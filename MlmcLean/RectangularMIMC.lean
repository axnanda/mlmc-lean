import MlmcLean.Theorem2

/-!
# Giles §2.4: Multi-Index Monte Carlo on a rectangular index set

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.4, p. 15:
"It might seem natural that the summation region `𝓛` should be rectangular, ... so that
`∑_{ℓ ∈ 𝓛} Y_ℓ = P_L` where `L` is the outermost point on the rectangle.  However, Haji-Ali et
al. (2014a) prove that this gives the optimal order of complexity only when `η < 0`, and under the
additional condition that `∑_d γ_d/α_d ≤ 2`."

* `rectSet L` is the rectangle `{ℓ : ℓ_d ≤ L_d for all d}`; `sum_rectSet_crossDiff` is the
  telescoping identity `∑_{ℓ ∈ rectSet L} ΔP_ℓ = P_L` quoted above.
* `sum_sdiff_rectSet_le`: the bias tail outside a rectangle,
  `∑_{ℓ ∉ rect} 2^{−α·ℓ} ≤ (∑_d 2^{−α_d(L_d+1)}) ∏_d (1 − 2^{−α_d})⁻¹`.
* `mimc_rect_core`: with `η < 0` (every `γ_d < β_d`) and `∑_d γ_d/α_d ≤ 2`, a rectangle and
  rounded-up optimal sample sizes give bias `≤ ε/2`, variance `≤ ε²/2` and cost `≤ c₄ ε⁻²`.
* `giles_mimc_rectangular`: the sufficiency direction of the statement quoted above — the MIMC
  estimator on a rectangular index set has `MSE < ε²` at expected cost `O(ε⁻²)`, the optimal order.
  (The "only when" direction needs lower bounds on the bias, variance and cost that the paper does
  not state; it is not formalised.)
-/

open MeasureTheory ProbabilityTheory Finset Real

namespace MLMC

variable {D : ℕ}

/-- The rectangular index set `{ℓ ∈ ℕ^D : ℓ_d ≤ L_d for all d}` (Giles 2015, §2.4, p. 15). -/
def rectSet (L : Fin D → ℕ) : Finset (Fin D → ℕ) := Fintype.piFinset fun d => range (L d + 1)

lemma mem_rectSet {L ℓ : Fin D → ℕ} : ℓ ∈ rectSet L ↔ ∀ d, ℓ d ≤ L d := by
  simp only [rectSet, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_add_one_iff]

/-- **On a rectangle the MIMC corrections telescope to the outermost point** (Giles 2015, §2.4,
p. 15: with a rectangular summation region, "`∑_{ℓ ∈ 𝓛} Y_ℓ = P_L` where `L` is the outermost point
on the rectangle", for `Y_ℓ = ΔP_ℓ`): `∑_{ℓ ∈ rect L} ΔP_ℓ = P_L` for every function `P` of the
multi-index, in particular pointwise for random variables. -/
theorem sum_rectSet_crossDiff (p : (Fin D → ℕ) → ℝ) (L : Fin D → ℕ) :
    ∑ ℓ ∈ rectSet L, crossDiff p ℓ = p L :=
  sum_crossDiff p L

/-- The tail of a geometric series: `∑_{k < n, k > L} r^k ≤ r^{L+1} (1 − r)⁻¹` for `0 ≤ r < 1`. -/
lemma geom_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (L n : ℕ) :
    ∑ k ∈ (range n).filter (fun k => L < k), r ^ k ≤ r ^ (L + 1) * (1 - r)⁻¹ := by
  have hset : (range n).filter (fun k => L < k) = Ico (L + 1) n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range,
    Finset.sum_congr rfl fun k _ => pow_add r (L + 1) k, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (geom_sum_le_of_lt_one hr0 hr1 _) (pow_nonneg hr0 _)

/-- `2^{−α·ℓ} = ∏_d (2^{−α_d})^{ℓ_d}`. -/
lemma two_rpow_neg_dot (α : Fin D → ℝ) (ℓ : Fin D → ℕ) :
    (2 : ℝ) ^ (-dot α ℓ) = ∏ d, ((2 : ℝ) ^ (-α d)) ^ ℓ d := by
  have h : -dot α ℓ = ∑ d, -α d * (ℓ d : ℝ) := by
    simp only [dot, ← Finset.sum_neg_distrib, neg_mul]
  rw [h, Real.rpow_sum_of_pos two_pos]
  exact Finset.prod_congr rfl fun d _ => two_rpow_mul_nat (-α d) (ℓ d)

/-- The part of a box beyond `L_d` in direction `d`:
`∑_{ℓ ∈ box n, ℓ_d > L_d} 2^{−α·ℓ} ≤ 2^{−α_d(L_d+1)} ∏_{d'} (1 − 2^{−α_{d'}})⁻¹` for `α > 0`. -/
lemma sum_filter_box_lt_le {α : Fin D → ℝ} (hα : ∀ d, 0 < α d) (L : Fin D → ℕ) (d : Fin D)
    (n : ℕ) :
    ∑ ℓ ∈ (box D n).filter (fun ℓ => L d < ℓ d), (2 : ℝ) ^ (-dot α ℓ) ≤
      ((2 : ℝ) ^ (-α d)) ^ (L d + 1) * ∏ d', (1 - (2 : ℝ) ^ (-α d'))⁻¹ := by
  classical
  have hr0 : ∀ d', 0 ≤ (2 : ℝ) ^ (-α d') := fun d' => (Real.rpow_pos_of_pos two_pos _).le
  have hr1 : ∀ d', (2 : ℝ) ^ (-α d') < 1 := fun d' =>
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith [hα d'])
  set t : Fin D → Finset ℕ := fun d' =>
    if d' = d then (range n).filter (fun k => L d < k) else range n with ht
  have hset : (box D n).filter (fun ℓ => L d < ℓ d) = Fintype.piFinset t := by
    ext ℓ
    simp only [Finset.mem_filter, box, Fintype.mem_piFinset, ht]
    constructor
    · rintro ⟨h1, h2⟩ d'
      by_cases h : d' = d
      · rw [if_pos h]
        refine Finset.mem_filter.2 ⟨h1 d', ?_⟩
        rw [h]
        exact h2
      · rw [if_neg h]
        exact h1 d'
    · intro h
      refine ⟨fun d' => ?_, ?_⟩
      · have h' := h d'
        by_cases hd : d' = d
        · rw [if_pos hd] at h'
          exact (Finset.mem_filter.1 h').1
        · rw [if_neg hd] at h'
          exact h'
      · have h' := h d
        rw [if_pos rfl] at h'
        exact (Finset.mem_filter.1 h').2
  have hfac : ∀ d', ∑ k ∈ t d', ((2 : ℝ) ^ (-α d')) ^ k ≤
      (if d' = d then ((2 : ℝ) ^ (-α d)) ^ (L d + 1) else 1) * (1 - (2 : ℝ) ^ (-α d'))⁻¹ := by
    intro d'
    by_cases hd : d' = d
    · have htd : t d' = (range n).filter (fun k => L d < k) := by simp only [ht, if_pos hd]
      rw [htd, if_pos hd, hd]
      exact geom_tail_le (hr0 d) (hr1 d) (L d) n
    · have htd : t d' = range n := by simp only [ht, if_neg hd]
      rw [htd, if_neg hd, one_mul]
      exact geom_sum_le_of_lt_one (hr0 d') (hr1 d') n
  rw [hset, Finset.sum_congr rfl fun ℓ _ => two_rpow_neg_dot α ℓ, ← Finset.prod_univ_sum]
  calc ∏ d', ∑ k ∈ t d', ((2 : ℝ) ^ (-α d')) ^ k
      ≤ ∏ d', ((if d' = d then ((2 : ℝ) ^ (-α d)) ^ (L d + 1) else 1) *
          (1 - (2 : ℝ) ^ (-α d'))⁻¹) :=
        Finset.prod_le_prod (fun d' _ => Finset.sum_nonneg fun k _ => pow_nonneg (hr0 d') k)
          (fun d' _ => hfac d')
    _ = ((2 : ℝ) ^ (-α d)) ^ (L d + 1) * ∏ d', (1 - (2 : ℝ) ^ (-α d'))⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ d,
          if_pos (Finset.mem_univ d)]

/-- **The bias tail outside a rectangle** (a step of the rectangular-set analysis of Giles 2015,
§2.4, p. 15): for `α > 0` and every finite set `s` of multi-indices,
`∑_{ℓ ∈ s ∖ rect L} 2^{−α·ℓ} ≤ (∑_d 2^{−α_d(L_d+1)}) ∏_d (1 − 2^{−α_d})⁻¹`. -/
theorem sum_sdiff_rectSet_le {α : Fin D → ℝ} (hα : ∀ d, 0 < α d) (L : Fin D → ℕ)
    (s : Finset (Fin D → ℕ)) :
    ∑ ℓ ∈ s \ rectSet L, (2 : ℝ) ^ (-dot α ℓ) ≤
      (∑ d, ((2 : ℝ) ^ (-α d)) ^ (L d + 1)) * ∏ d', (1 - (2 : ℝ) ^ (-α d'))⁻¹ := by
  classical
  obtain ⟨n, hn⟩ := exists_subset_box s
  have hf0 : ∀ ℓ, 0 ≤ (2 : ℝ) ^ (-dot α ℓ) := fun ℓ => (Real.rpow_pos_of_pos two_pos _).le
  calc ∑ ℓ ∈ s \ rectSet L, (2 : ℝ) ^ (-dot α ℓ)
      ≤ ∑ ℓ ∈ s \ rectSet L, ∑ d, (if L d < ℓ d then (2 : ℝ) ^ (-dot α ℓ) else 0) := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        have hnot : ¬ ∀ d, ℓ d ≤ L d := fun h => (Finset.mem_sdiff.1 hℓ).2 (mem_rectSet.2 h)
        obtain ⟨d, hd⟩ := not_forall.1 hnot
        calc (2 : ℝ) ^ (-dot α ℓ) = if L d < ℓ d then (2 : ℝ) ^ (-dot α ℓ) else 0 := by
              rw [if_pos (not_le.1 hd)]
          _ ≤ ∑ d', (if L d' < ℓ d' then (2 : ℝ) ^ (-dot α ℓ) else 0) :=
              Finset.single_le_sum (f := fun d' => if L d' < ℓ d' then (2 : ℝ) ^ (-dot α ℓ) else 0)
                (fun d' _ => by
                  show (0 : ℝ) ≤ if L d' < ℓ d' then (2 : ℝ) ^ (-dot α ℓ) else 0
                  split_ifs
                  · exact hf0 ℓ
                  · exact le_rfl) (Finset.mem_univ d)
    _ = ∑ d, ∑ ℓ ∈ s \ rectSet L, (if L d < ℓ d then (2 : ℝ) ^ (-dot α ℓ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ d, ∑ ℓ ∈ (box D n).filter (fun ℓ => L d < ℓ d), (2 : ℝ) ^ (-dot α ℓ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ℓ hℓ
          rw [Finset.mem_filter] at hℓ ⊢
          exact ⟨hn (Finset.mem_sdiff.1 hℓ.1).1, hℓ.2⟩
        · intro ℓ _ _
          exact hf0 ℓ
    _ ≤ ∑ d, ((2 : ℝ) ^ (-α d)) ^ (L d + 1) * ∏ d', (1 - (2 : ℝ) ^ (-α d'))⁻¹ :=
        Finset.sum_le_sum fun d _ => sum_filter_box_lt_le hα L d n
    _ = (∑ d, ((2 : ℝ) ^ (-α d)) ^ (L d + 1)) * ∏ d', (1 - (2 : ℝ) ^ (-α d'))⁻¹ := by
        rw [Finset.sum_mul]

/-- `∑_{ℓ ∈ rect L} 2^{γ·ℓ} ≤ ∏_d (2^{γ_d})^{L_d} q_d` with `q_d = 2^{γ_d}/(2^{γ_d} − 1)`, for
`γ > 0` (the rounding overhead of the rectangular set, Giles 2015, §2.4). -/
lemma sum_rectSet_two_rpow_le {γ : Fin D → ℝ} (hγ : ∀ d, 0 < γ d) (L : Fin D → ℕ) :
    ∑ ℓ ∈ rectSet L, (2 : ℝ) ^ dot γ ℓ ≤
      ∏ d, (((2 : ℝ) ^ γ d) ^ L d * ((2 : ℝ) ^ γ d / ((2 : ℝ) ^ γ d - 1))) := by
  have h : ∀ ℓ : Fin D → ℕ, (2 : ℝ) ^ dot γ ℓ = ∏ d, ((2 : ℝ) ^ γ d) ^ ℓ d := by
    intro ℓ
    rw [dot, Real.rpow_sum_of_pos two_pos]
    exact Finset.prod_congr rfl fun d _ => two_rpow_mul_nat (γ d) (ℓ d)
  rw [Finset.sum_congr rfl fun ℓ _ => h ℓ, rectSet, ← Finset.prod_univ_sum]
  apply Finset.prod_le_prod
  · intro d _
    exact Finset.sum_nonneg fun k _ => pow_nonneg (Real.rpow_pos_of_pos two_pos _).le _
  · intro d _
    exact geom_sum_le_of_one_lt (Real.one_lt_rpow one_lt_two (hγ d)) (L d)

/-- **The rectangular MIMC construction** (the deterministic part of the rectangular-set statement
of Giles 2015, §2.4, p. 15, after Haji-Ali et al. 2014a).  Let `α_d, γ_d > 0`, `η < 0` (that is,
`γ_d < β_d` for every `d`), `∑_d γ_d/α_d ≤ 2` and `c₁, c₂, c₃ > 0`.  Then there is `c₄ > 0` such
that for every `0 < ε < 1` there are a rectangle `rectSet L` and sample sizes `N_ℓ ≥ 1` with bias
tail `c₁ ∑_{ℓ ∉ rect} 2^{−α·ℓ} ≤ ε/2` (over every finite set), variance
`∑_{ℓ ∈ rect} c₂ 2^{−β·ℓ}/N_ℓ ≤ ε²/2` and cost `∑_{ℓ ∈ rect} N_ℓ c₃ 2^{γ·ℓ} ≤ c₄ ε⁻²`. -/
theorem mimc_rect_core {α β γ : Fin D → ℝ} {c₁ c₂ c₃ : ℝ} (hα : ∀ d, 0 < α d)
    (hγ : ∀ d, 0 < γ d) (hβγ : ∀ d, γ d < β d) (hsum : ∑ d, γ d / α d ≤ 2)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (L : Fin D → ℕ) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (∀ s : Finset (Fin D → ℕ), c₁ * ∑ ℓ ∈ s \ rectSet L, (2 : ℝ) ^ (-dot α ℓ) ≤ ε / 2) ∧
        ∑ ℓ ∈ rectSet L, c₂ * (2 : ℝ) ^ (-dot β ℓ) / N ℓ ≤ ε ^ 2 / 2 ∧
        ∑ ℓ ∈ rectSet L, (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ dot γ ℓ) ≤ c₄ * ε ^ (-2 : ℝ) := by
  -- constants
  set A : ℝ := ∏ d, (1 - (2 : ℝ) ^ (-α d))⁻¹
  have hA : 0 < A := Finset.prod_pos fun d _ => by
    have h := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith [hα d] : -α d < 0)
    exact inv_pos.2 (by linarith)
  set g : Fin D → ℝ := fun d => (1 / 2) * γ d + (-1 / 2) * β d with hg_def
  have hg : ∀ d, g d < 0 := fun d => by simp only [hg_def]; linarith [hβγ d]
  set G : ℝ := ∏ d, (1 - (2 : ℝ) ^ g d)⁻¹
  set Q : ℝ := ∏ d, ((2 : ℝ) ^ γ d * ((2 : ℝ) ^ γ d / ((2 : ℝ) ^ γ d - 1))) with hQ_def
  have hQ : 0 < Q := Finset.prod_pos fun d _ => by
    have h1 : 1 < (2 : ℝ) ^ γ d := Real.one_lt_rpow one_lt_two (hγ d)
    exact mul_pos (by linarith) (div_pos (by linarith) (by linarith))
  set K₀ : ℝ := 2 * c₁ * A * ((D : ℝ) + 1) with hK₀_def
  have hK₀ : 0 < K₀ := by rw [hK₀_def]; positivity
  set K : ℝ := max 1 K₀
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  set c₄ : ℝ := 2 * (c₂ * c₃) * G ^ 2 + c₃ * Q * K ^ 2 with hc₄_def
  have hc₄ : 0 < c₄ := by rw [hc₄_def]; positivity
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  set δ : ℝ := ε / K₀ with hδ_def
  have hδ : 0 < δ := div_pos hε hK₀
  -- the rectangle: `L_d` is the least level with `2^{−α_d L_d} ≤ δ`
  set L : Fin D → ℕ := fun d => levelL (α d) 1 δ
  have hLbias : ∀ d, ((2 : ℝ) ^ (-α d)) ^ (L d + 1) ≤ δ := fun d => by
    have h1 := levelL_bias (hα d) one_pos hδ
    rw [one_mul] at h1
    calc ((2 : ℝ) ^ (-α d)) ^ (L d + 1) = (2 : ℝ) ^ (-α d * ((L d + 1 : ℕ) : ℝ)) :=
          (two_rpow_mul_nat _ _).symm
      _ ≤ (2 : ℝ) ^ (-(α d * (L d : ℝ))) := by
          apply Real.rpow_le_rpow_of_exponent_le one_le_two
          push_cast
          nlinarith [hα d]
      _ ≤ δ := h1
  -- the sample sizes
  set V : (Fin D → ℕ) → ℝ := fun ℓ => c₂ * (2 : ℝ) ^ (-dot β ℓ) with hV
  set C : (Fin D → ℕ) → ℝ := fun ℓ => c₃ * (2 : ℝ) ^ dot γ ℓ with hC
  have hVpos : ∀ ℓ, 0 < V ℓ := fun ℓ => mul_pos hc₂ (Real.rpow_pos_of_pos two_pos _)
  have hCpos : ∀ ℓ, 0 < C ℓ := fun ℓ => mul_pos hc₃ (Real.rpow_pos_of_pos two_pos _)
  have hτ : 0 < ε ^ 2 / 2 := by positivity
  have hs : (rectSet L).Nonempty := ⟨0, mem_rectSet.2 fun d => Nat.zero_le _⟩
  refine ⟨L, optimalN (rectSet L) V C (ε ^ 2 / 2), fun ℓ => optimalN_pos hs hVpos hCpos hτ ℓ,
    fun s => ?_, optimalN_variance hs (fun ℓ _ => hVpos ℓ) (fun ℓ _ => hCpos ℓ) hτ, ?_⟩
  · -- bias
    have hsumL : ∑ d, ((2 : ℝ) ^ (-α d)) ^ (L d + 1) ≤ (D : ℝ) * δ := by
      calc ∑ d, ((2 : ℝ) ^ (-α d)) ^ (L d + 1) ≤ ∑ _d : Fin D, δ :=
            Finset.sum_le_sum fun d _ => hLbias d
        _ = (D : ℝ) * δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc c₁ * ∑ ℓ ∈ s \ rectSet L, (2 : ℝ) ^ (-dot α ℓ)
        ≤ c₁ * ((∑ d, ((2 : ℝ) ^ (-α d)) ^ (L d + 1)) * A) :=
          mul_le_mul_of_nonneg_left (sum_sdiff_rectSet_le hα L s) hc₁.le
      _ ≤ c₁ * (((D : ℝ) * δ) * A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumL hA.le) hc₁.le
      _ = (D : ℝ) * δ * c₁ * A * ((2 * ((D : ℝ) + 1)) / (2 * ((D : ℝ) + 1))) := by
          rw [div_self (by positivity : (2 : ℝ) * ((D : ℝ) + 1) ≠ 0), mul_one]
          ring
      _ = (D : ℝ) / (2 * ((D : ℝ) + 1)) * (δ * K₀) := by
          rw [hK₀_def]
          ring
      _ = (D : ℝ) / (2 * ((D : ℝ) + 1)) * ε := by
          rw [hδ_def, div_mul_cancel₀ ε hK₀.ne']
      _ ≤ 1 / 2 * ε := by
          refine mul_le_mul_of_nonneg_right ?_ hε.le
          rw [div_le_iff₀ (by positivity)]
          linarith
      _ = ε / 2 := by ring
  · -- cost
    have hc := optimalN_cost hs (fun ℓ _ => hVpos ℓ) (fun ℓ _ => hCpos ℓ) hτ
    -- `∑ √(V_ℓ C_ℓ) ≤ √(c₂c₃) G`
    have hsq : ∀ ℓ, Real.sqrt (V ℓ * C ℓ) = Real.sqrt (c₂ * c₃) * (2 : ℝ) ^ dot g ℓ := by
      intro ℓ
      have e : ((2 : ℝ) ^ dot g ℓ) ^ 2 = (2 : ℝ) ^ dot γ ℓ * (2 : ℝ) ^ (-dot β ℓ) := by
        rw [sq, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        congr 1
        rw [dot_linear (fun d => rfl : ∀ d, g d = (1 / 2) * γ d + (-1 / 2) * β d) ℓ]
        ring
      have h1 : V ℓ * C ℓ = (c₂ * c₃) * ((2 : ℝ) ^ dot g ℓ) ^ 2 := by
        rw [e]
        simp only [hV, hC]
        ring
      rw [h1, Real.sqrt_mul (mul_pos hc₂ hc₃).le,
        Real.sqrt_sq (Real.rpow_pos_of_pos two_pos _).le]
    obtain ⟨n, hn⟩ := exists_subset_box (rectSet L)
    have hS : ∑ ℓ ∈ rectSet L, Real.sqrt (V ℓ * C ℓ) ≤ Real.sqrt (c₂ * c₃) * G := by
      rw [Finset.sum_congr rfl fun ℓ _ => hsq ℓ, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      calc ∑ ℓ ∈ rectSet L, (2 : ℝ) ^ dot g ℓ ≤ ∑ ℓ ∈ box D n, (2 : ℝ) ^ dot g ℓ :=
            Finset.sum_le_sum_of_subset_of_nonneg hn fun ℓ _ _ =>
              (Real.rpow_pos_of_pos two_pos _).le
        _ ≤ G := sum_box_two_rpow_le_prod hg n
    have hS0 : 0 ≤ ∑ ℓ ∈ rectSet L, Real.sqrt (V ℓ * C ℓ) :=
      Finset.sum_nonneg fun ℓ _ => Real.sqrt_nonneg _
    -- `(2^{γ_d})^{L_d} ≤ 2^{γ_d} (K/ε)^{γ_d/α_d}`
    have hKε : 1 ≤ K / ε := by
      rw [le_div_iff₀ hε]
      linarith
    have hmax : max 1 (1 / δ) ≤ K / ε := by
      refine max_le hKε ?_
      rw [hδ_def, one_div_div]
      exact div_le_div_of_nonneg_right (le_max_right _ _) hε.le
    have hpow : ∀ d, ((2 : ℝ) ^ γ d) ^ L d ≤ (2 : ℝ) ^ γ d * (K / ε) ^ (γ d / α d) := fun d => by
      have h2 := two_rpow_levelL_le (hα d) one_pos hδ
      have e1 : ((2 : ℝ) ^ γ d) ^ L d =
          ((2 : ℝ) ^ (α d * (L d : ℝ))) ^ (γ d / α d) := by
        rw [← two_rpow_mul_nat, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        rw [mul_comm (α d), mul_assoc, mul_div_cancel₀ (γ d) (hα d).ne', mul_comm]
      have e2 : ((2 : ℝ) ^ α d * max 1 (1 / δ)) ^ (γ d / α d) =
          (2 : ℝ) ^ γ d * (max 1 (1 / δ)) ^ (γ d / α d) := by
        rw [Real.mul_rpow (Real.rpow_pos_of_pos two_pos _).le
          (le_trans zero_le_one (le_max_left _ _)),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_div_cancel₀ _ (hα d).ne']
      have hq : 0 ≤ γ d / α d := div_nonneg (hγ d).le (hα d).le
      rw [e1]
      calc ((2 : ℝ) ^ (α d * (L d : ℝ))) ^ (γ d / α d)
          ≤ ((2 : ℝ) ^ α d * max 1 (1 / δ)) ^ (γ d / α d) :=
            Real.rpow_le_rpow (Real.rpow_pos_of_pos two_pos _).le h2 hq
        _ = (2 : ℝ) ^ γ d * (max 1 (1 / δ)) ^ (γ d / α d) := e2
        _ ≤ (2 : ℝ) ^ γ d * (K / ε) ^ (γ d / α d) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) hmax hq)
              (Real.rpow_pos_of_pos two_pos _).le
    -- `∏_d (K/ε)^{γ_d/α_d} ≤ (K/ε)²`
    have hprodK : ∏ d, (K / ε) ^ (γ d / α d) ≤ (K / ε) ^ (2 : ℝ) := by
      rw [← Real.rpow_sum_of_pos (lt_of_lt_of_le one_pos hKε)]
      exact Real.rpow_le_rpow_of_exponent_le hKε hsum
    have hCsum : ∑ ℓ ∈ rectSet L, C ℓ ≤ c₃ * Q * K ^ 2 * ε ^ (-2 : ℝ) := by
      have h1 : ∑ ℓ ∈ rectSet L, C ℓ = c₃ * ∑ ℓ ∈ rectSet L, (2 : ℝ) ^ dot γ ℓ := by
        simp only [hC, Finset.mul_sum]
      have h2 : ∏ d, (((2 : ℝ) ^ γ d) ^ L d * ((2 : ℝ) ^ γ d / ((2 : ℝ) ^ γ d - 1))) ≤
          ∏ d, (((2 : ℝ) ^ γ d * (K / ε) ^ (γ d / α d)) *
            ((2 : ℝ) ^ γ d / ((2 : ℝ) ^ γ d - 1))) := by
        apply Finset.prod_le_prod
        · intro d _
          have h1 : 1 < (2 : ℝ) ^ γ d := Real.one_lt_rpow one_lt_two (hγ d)
          exact mul_nonneg (pow_nonneg (by linarith) _) (div_nonneg (by linarith) (by linarith))
        · intro d _
          have h1 : 1 < (2 : ℝ) ^ γ d := Real.one_lt_rpow one_lt_two (hγ d)
          exact mul_le_mul_of_nonneg_right (hpow d) (div_nonneg (by linarith) (by linarith))
      have h3 : ∏ d, (((2 : ℝ) ^ γ d * (K / ε) ^ (γ d / α d)) *
          ((2 : ℝ) ^ γ d / ((2 : ℝ) ^ γ d - 1))) = Q * ∏ d, (K / ε) ^ (γ d / α d) := by
        rw [hQ_def, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun d _ => by ring
      have h4 : (K / ε) ^ (2 : ℝ) = K ^ 2 * ε ^ (-2 : ℝ) := by
        rw [Real.rpow_two, div_pow, ← eps_inv_sq_eq hε, div_eq_mul_inv, inv_pow]
      rw [h1]
      calc c₃ * ∑ ℓ ∈ rectSet L, (2 : ℝ) ^ dot γ ℓ
          ≤ c₃ * (Q * ∏ d, (K / ε) ^ (γ d / α d)) :=
            mul_le_mul_of_nonneg_left ((sum_rectSet_two_rpow_le hγ L).trans (h2.trans h3.le))
              hc₃.le
        _ ≤ c₃ * (Q * (K / ε) ^ (2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprodK hQ.le) hc₃.le
        _ = c₃ * Q * K ^ 2 * ε ^ (-2 : ℝ) := by rw [h4]; ring
    have hτinv : (ε ^ 2 / 2)⁻¹ = 2 * ε ^ (-2 : ℝ) := by
      rw [inv_div, ← eps_inv_sq_eq hε, inv_pow, div_eq_mul_inv]
    calc ∑ ℓ ∈ rectSet L, (optimalN (rectSet L) V C (ε ^ 2 / 2) ℓ : ℝ) * (c₃ * (2 : ℝ) ^ dot γ ℓ)
        = ∑ ℓ ∈ rectSet L, (optimalN (rectSet L) V C (ε ^ 2 / 2) ℓ : ℝ) * C ℓ := rfl
      _ ≤ (ε ^ 2 / 2)⁻¹ * (∑ ℓ ∈ rectSet L, Real.sqrt (V ℓ * C ℓ)) ^ 2 +
          ∑ ℓ ∈ rectSet L, C ℓ := hc
      _ ≤ 2 * ε ^ (-2 : ℝ) * (Real.sqrt (c₂ * c₃) * G) ^ 2 + c₃ * Q * K ^ 2 * ε ^ (-2 : ℝ) := by
          rw [hτinv]
          have hε2 : 0 ≤ 2 * ε ^ (-2 : ℝ) := mul_nonneg zero_le_two (Real.rpow_nonneg hε.le _)
          exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hS 2) hε2) hCsum
      _ = c₄ * ε ^ (-2 : ℝ) := by
          rw [mul_pow, Real.sq_sqrt (mul_pos hc₂ hc₃).le, hc₄_def]
          ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **MIMC on a rectangular index set has the optimal order `ε⁻²` when `η < 0` and
`∑_d γ_d/α_d ≤ 2`** (Giles 2015, §2.4, p. 15: "Haji-Ali et al. (2014a) prove that this gives the
optimal order of complexity only when `η < 0`, and under the additional condition that
`∑_d γ_d/α_d ≤ 2`"; this is the sufficiency direction).  Under the hypotheses of Theorem 2 —
integrable `P` and `P_ℓ`, square-integrable estimators `Y ℓ n` that are pairwise independent
across multi-indices, with `V[Y ℓ n] = V_ℓ/n`, integrable random costs with `E[Cost ℓ n] = n C_ℓ`,
and conditions i)–v) — with positive `α, γ`, `η < 0` (every `γ_d < β_d`) and
`∑_d γ_d/α_d ≤ 2`, there is `c₄ > 0` such that for every `0 < ε < 1` there are a rectangle
`𝓛 = rectSet L` and sample sizes `N_ℓ ≥ 1` for which `Y = ∑_{ℓ ∈ 𝓛} Y ℓ (N ℓ)` has
`E[(Y − E[P])²] < ε²` and the cost `C = ∑_{ℓ ∈ 𝓛} Cost ℓ (N ℓ)` has `E[C] ≤ c₄ ε⁻²`. -/
theorem giles_mimc_rectangular (P : Ω → ℝ) (Pℓ : (Fin D → ℕ) → Ω → ℝ)
    (Y : (Fin D → ℕ) → ℕ → Ω → ℝ) (Cost : (Fin D → ℕ) → ℕ → Ω → ℝ) (V C : (Fin D → ℕ) → ℝ)
    {α β γ : Fin D → ℝ} {c₁ c₂ c₃ : ℝ} (hα : ∀ d, 0 < α d) (hγ : ∀ d, 0 < γ d)
    (hβγ : ∀ d, γ d < β d) (hsum : ∑ d, γ d / α d ≤ 2)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : (Fin D → ℕ) → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost_int : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (hCost_mean : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_i : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ ℓ : Fin D → ℕ, (∀ d, n₀ ≤ ℓ d) →
      |μ[fun ω => Pℓ ℓ ω - P ω]| < δ)
    (h_iii : ∀ ℓ n, 0 < n → μ[Y ℓ n] = μ[fun ω => crossDiff (fun m => Pℓ m ω) ℓ])
    (h_ii : ∀ ℓ n, 0 < n → |μ[Y ℓ n]| ≤ c₁ * (2 : ℝ) ^ (-dot α ℓ))
    (h_iv : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-dot β ℓ))
    (h_v : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ dot γ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (L : Fin D → ℕ) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ rectSet L, Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ rectSet L, Cost ℓ (N ℓ) ω] ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨c₄, hc₄, hcore⟩ := mimc_rect_core hα hγ hβγ hsum hc₁ hc₂ hc₃
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hbias, hvar, hcost⟩ := hcore ε hε hε1
  exact ⟨L, N, hN, mimc_mse_cost_of P Pℓ Y Cost V C hε (rectSet L) N hN hbias hvar hcost hP hPℓ
    hY hind hCost_int hCost_mean h_var h_i h_iii h_ii h_iv h_v⟩

end MLMC
