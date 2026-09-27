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
* `mimc_rect_lower_bounds`, `mimc_rect_necessary`: the "only when" direction.  The paper states no
  hypotheses for it; under attained rates (`|E[P_ℓ − P]| ≥ a₁ 2^{−α_d ℓ_d}` in each direction,
  `V_ℓ ≥ a₂ 2^{−β·ℓ}`, `C_ℓ ≥ a₃ 2^{γ·ℓ}`) a rectangle with `MSE < ε²` costs at least
  `a₃ (a₁/ε)^{∑ γ_d/α_d}`, and at least `a₂ a₃ (L_d + 1)² ε⁻²` in every direction with
  `β_d ≤ γ_d`; so cost `O(ε⁻²)` forces `η < 0` and `∑_d γ_d/α_d ≤ 2`.
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

/-! ### The converse under attained rates -/

/-- `a·(k e_d) = a_d k`, where `k e_d = Pi.single d k` is the multi-index with `k` in direction `d`
and `0` elsewhere. -/
lemma dot_single (a : Fin D → ℝ) (d : Fin D) (k : ℕ) : dot a (Pi.single d k) = a d * k := by
  rw [dot, Finset.sum_eq_single d
    (fun b _ hb => by rw [Pi.single_eq_of_ne hb, Nat.cast_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ d) h), Pi.single_eq_same]

/-- The multi-indices `k e_d` with `k ≤ L_d` lie in the rectangle, so for nonnegative `f`,
`∑_{k ≤ L_d} f(k e_d) ≤ ∑_{ℓ ∈ rect L} f ℓ`. -/
lemma sum_axis_le_sum_rectSet {f : (Fin D → ℕ) → ℝ} (hf : ∀ ℓ, 0 ≤ f ℓ) (L : Fin D → ℕ)
    (d : Fin D) : ∑ k ∈ range (L d + 1), f (Pi.single d k) ≤ ∑ ℓ ∈ rectSet L, f ℓ := by
  have himg : ∑ ℓ ∈ (range (L d + 1)).image (fun k => (Pi.single d k : Fin D → ℕ)), f ℓ =
      ∑ k ∈ range (L d + 1), f (Pi.single d k) :=
    Finset.sum_image fun x _ y _ h => Pi.single_injective d h
  rw [← himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => ?_) fun ℓ _ _ => hf ℓ
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hℓ
  have hk' : k ≤ L d := Nat.lt_add_one_iff.1 (Finset.mem_range.1 hk)
  refine mem_rectSet.2 fun d' => ?_
  show (Pi.single d k : Fin D → ℕ) d' ≤ L d'
  by_cases h : d' = d
  · rw [h, Pi.single_eq_same]
    exact hk'
  · rw [Pi.single_eq_of_ne h]
    exact Nat.zero_le _

/-- **Lower bounds for the MIMC estimator on a rectangle** (for the converse of the statement of
Giles 2015, §2.4, p. 15: a rectangle "gives the optimal order of complexity only when `η < 0`, and
under the additional condition that `∑_d γ_d/α_d ≤ 2`").  The paper states no hypotheses for the
converse; here the rates are *attained*: `|E[P_ℓ − P]| ≥ a₁ 2^{−α_d ℓ_d}` in every direction `d`,
`V_ℓ ≥ a₂ 2^{−β·ℓ}` and `C_ℓ ≥ a₃ 2^{γ·ℓ}`, with `α_d > 0` and `γ_d ≥ 0`.  If the estimator
`∑_{ℓ ∈ rect L} Y ℓ (N ℓ)` has `MSE < ε²`, then `2^{α_d L_d} > a₁/ε` in every direction, its
expected cost is at least `a₃ (a₁/ε)^{∑_d γ_d/α_d}` (the cost of the outermost point `L`), and at
least `a₂ a₃ (L_d + 1)² ε⁻²` in every direction with `β_d ≤ γ_d` (Cauchy–Schwarz,
`cost_lower_bound`, along the axis `{k e_d : k ≤ L_d}`). -/
theorem mimc_rect_lower_bounds (P : Ω → ℝ) (Pℓ : (Fin D → ℕ) → Ω → ℝ)
    (Y : (Fin D → ℕ) → ℕ → Ω → ℝ) (Cost : (Fin D → ℕ) → ℕ → Ω → ℝ) (V C : (Fin D → ℕ) → ℝ)
    {α β γ : Fin D → ℝ} {a₁ a₂ a₃ ε : ℝ} (hα : ∀ d, 0 < α d) (hγ : ∀ d, 0 ≤ γ d)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (hε : 0 < ε)
    (L : Fin D → ℕ) (N : (Fin D → ℕ) → ℕ) (hN : ∀ ℓ, 0 < N ℓ)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost_int : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (hCost_mean : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ n, 0 < n → μ[Y ℓ n] = μ[fun ω => crossDiff (fun m => Pℓ m ω) ℓ])
    (hbias : ∀ (ℓ : Fin D → ℕ) (d : Fin D),
      a₁ * (2 : ℝ) ^ (-(α d * ℓ d)) ≤ |μ[fun ω => Pℓ ℓ ω - P ω]|)
    (hV : ∀ ℓ, a₂ * (2 : ℝ) ^ (-dot β ℓ) ≤ V ℓ) (hC : ∀ ℓ, a₃ * (2 : ℝ) ^ dot γ ℓ ≤ C ℓ)
    (hmse : μ[fun ω => (∑ ℓ ∈ rectSet L, Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2) :
    (∀ d, a₁ / ε < (2 : ℝ) ^ (α d * L d)) ∧
      a₃ * (a₁ / ε) ^ (∑ d, γ d / α d) ≤ μ[fun ω => ∑ ℓ ∈ rectSet L, Cost ℓ (N ℓ) ω] ∧
      ∀ d, β d ≤ γ d → a₂ * a₃ * ((L d : ℝ) + 1) ^ 2 * ε ^ (-2 : ℝ) ≤
        μ[fun ω => ∑ ℓ ∈ rectSet L, Cost ℓ (N ℓ) ω] := by
  have hVpos : ∀ ℓ, 0 < V ℓ := fun ℓ =>
    lt_of_lt_of_le (mul_pos ha₂ (Real.rpow_pos_of_pos two_pos _)) (hV ℓ)
  have hCpos : ∀ ℓ, 0 < C ℓ := fun ℓ =>
    lt_of_lt_of_le (mul_pos ha₃ (Real.rpow_pos_of_pos two_pos _)) (hC ℓ)
  -- the mean-square error is `∑_{ℓ ∈ rect} V_ℓ/N_ℓ + E[P_L − P]²` (rectangle telescoping)
  set p : (Fin D → ℕ) → ℝ := fun m => μ[Pℓ m]
  have hEΔ : ∀ ℓ, μ[fun ω => crossDiff (fun m => Pℓ m ω) ℓ] = crossDiff p ℓ := fun ℓ =>
    (integrable_integral_crossDiff Pℓ hPℓ ℓ).2
  have hmean : μ[fun ω => ∑ ℓ ∈ rectSet L, Y ℓ (N ℓ) ω] = ∑ ℓ ∈ rectSet L, crossDiff p ℓ := by
    rw [integral_finsetSum _ fun ℓ _ => (hY ℓ (N ℓ) (hN ℓ)).integrable one_le_two]
    exact Finset.sum_congr rfl fun ℓ _ => by rw [h_iii ℓ (N ℓ) (hN ℓ), hEΔ]
  have hmean' : μ[∑ ℓ ∈ rectSet L, Y ℓ (N ℓ)] - μ[P] = μ[fun ω => Pℓ L ω - P ω] := by
    have h1 : μ[∑ ℓ ∈ rectSet L, Y ℓ (N ℓ)] = μ[fun ω => ∑ ℓ ∈ rectSet L, Y ℓ (N ℓ) ω] := by
      congr 1
      ext ω
      simp [Finset.sum_apply]
    rw [h1, hmean, sum_rectSet_crossDiff p L, integral_sub (hPℓ L) hP] <;> rfl
  have hsum : MemLp (∑ ℓ ∈ rectSet L, Y ℓ (N ℓ)) 2 μ :=
    memLp_finsetSum' _ fun ℓ _ => hY ℓ (N ℓ) (hN ℓ)
  have hind' : Set.Pairwise ↑(rectSet L) fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ :=
    fun i _ j _ hij => hind hij
  have hdec := mse_eq_variance_add_sq_bias hsum (μ[P])
  rw [IndepFun.variance_sum (fun ℓ _ => hY ℓ (N ℓ) (hN ℓ)) hind', hmean'] at hdec
  have hfun : (fun ω => (∑ ℓ ∈ rectSet L, Y ℓ (N ℓ) ω - μ[P]) ^ 2) =
      fun ω => ((∑ ℓ ∈ rectSet L, Y ℓ (N ℓ)) ω - μ[P]) ^ 2 := by
    ext ω
    simp [Finset.sum_apply]
  have hvar : ∑ ℓ ∈ rectSet L, variance (Y ℓ (N ℓ)) μ = ∑ ℓ ∈ rectSet L, V ℓ / N ℓ :=
    Finset.sum_congr rfl fun ℓ _ => h_var ℓ (N ℓ) (hN ℓ)
  rw [hfun, hdec, hvar] at hmse
  have hS0 : 0 ≤ ∑ ℓ ∈ rectSet L, V ℓ / N ℓ :=
    Finset.sum_nonneg fun ℓ _ => div_nonneg (hVpos ℓ).le (Nat.cast_nonneg _)
  have hB : |μ[fun ω => Pℓ L ω - P ω]| < ε :=
    abs_lt_of_sq_lt_sq (by linarith) hε.le
  have hS : ∑ ℓ ∈ rectSet L, V ℓ / N ℓ ≤ ε ^ 2 := by
    linarith [sq_nonneg (μ[fun ω => Pℓ L ω - P ω])]
  -- the finest levels: `2^{α_d L_d} > a₁/ε`
  have hpart1 : ∀ d, a₁ / ε < (2 : ℝ) ^ (α d * L d) := fun d => by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (α d * L d) := Real.rpow_pos_of_pos two_pos _
    have h1 := lt_of_le_of_lt (hbias L d) hB
    rw [Real.rpow_neg zero_le_two, ← div_eq_mul_inv, div_lt_iff₀ h2] at h1
    rw [div_lt_iff₀ hε, mul_comm]
    exact h1
  -- the expected cost is `∑ N_ℓ C_ℓ`, at least the cost `C_L` of the outermost point
  have hcost : μ[fun ω => ∑ ℓ ∈ rectSet L, Cost ℓ (N ℓ) ω] =
      ∑ ℓ ∈ rectSet L, (N ℓ : ℝ) * C ℓ := by
    rw [integral_finsetSum _ fun ℓ _ => hCost_int ℓ (N ℓ) (hN ℓ)]
    exact Finset.sum_congr rfl fun ℓ _ => hCost_mean ℓ (N ℓ) (hN ℓ)
  have hcorner : C L ≤ ∑ ℓ ∈ rectSet L, (N ℓ : ℝ) * C ℓ :=
    calc C L ≤ (N L : ℝ) * C L := le_mul_of_one_le_left (hCpos L).le (Nat.one_le_cast.2 (hN L))
      _ ≤ ∑ ℓ ∈ rectSet L, (N ℓ : ℝ) * C ℓ :=
          Finset.single_le_sum (f := fun ℓ => (N ℓ : ℝ) * C ℓ)
            (fun ℓ _ => mul_nonneg (Nat.cast_nonneg _) (hCpos ℓ).le)
            (mem_rectSet.2 fun _ => le_rfl)
  have hγL : (a₁ / ε) ^ (∑ d, γ d / α d) ≤ (2 : ℝ) ^ dot γ L := by
    have hq : 0 < a₁ / ε := div_pos ha₁ hε
    rw [Real.rpow_sum_of_pos hq, dot, Real.rpow_sum_of_pos two_pos]
    refine Finset.prod_le_prod (fun d _ => (Real.rpow_pos_of_pos hq _).le) fun d _ => ?_
    calc (a₁ / ε) ^ (γ d / α d) ≤ ((2 : ℝ) ^ (α d * L d)) ^ (γ d / α d) :=
          Real.rpow_le_rpow hq.le (hpart1 d).le (div_nonneg (hγ d) (hα d).le)
      _ = (2 : ℝ) ^ (γ d * L d) := by
          rw [← Real.rpow_mul zero_le_two]
          congr 1
          rw [mul_comm (α d), mul_assoc, mul_div_cancel₀ (γ d) (hα d).ne', mul_comm]
  have hpart2 : a₃ * (a₁ / ε) ^ (∑ d, γ d / α d) ≤
      μ[fun ω => ∑ ℓ ∈ rectSet L, Cost ℓ (N ℓ) ω] := by
    rw [hcost]
    calc a₃ * (a₁ / ε) ^ (∑ d, γ d / α d) ≤ a₃ * (2 : ℝ) ^ dot γ L :=
          mul_le_mul_of_nonneg_left hγL ha₃.le
      _ ≤ C L := hC L
      _ ≤ ∑ ℓ ∈ rectSet L, (N ℓ : ℝ) * C ℓ := hcorner
  -- directions with `β_d ≤ γ_d`: `∑_{rect} √(V_ℓ C_ℓ) ≥ (L_d + 1) √(a₂ a₃)` along the axis
  have hpart3 : ∀ d, β d ≤ γ d → a₂ * a₃ * ((L d : ℝ) + 1) ^ 2 * ε ^ (-2 : ℝ) ≤
      μ[fun ω => ∑ ℓ ∈ rectSet L, Cost ℓ (N ℓ) ω] := by
    intro d hd
    have hcs := cost_lower_bound (rectSet L) V C (fun ℓ => (N ℓ : ℝ)) (pow_pos hε 2)
      (fun ℓ _ => (hVpos ℓ).le) (fun ℓ _ => (hCpos ℓ).le) (fun ℓ _ => Nat.cast_pos.2 (hN ℓ)) hS
    have hVC : ∀ k : ℕ, a₂ * a₃ ≤ V (Pi.single d k) * C (Pi.single d k) := fun k => by
      have h1 : a₂ * (2 : ℝ) ^ (-dot β (Pi.single d k)) * (a₃ * (2 : ℝ) ^ dot γ (Pi.single d k)) ≤
          V (Pi.single d k) * C (Pi.single d k) :=
        mul_le_mul (hV _) (hC _) (mul_pos ha₃ (Real.rpow_pos_of_pos two_pos _)).le (hVpos _).le
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (-dot β (Pi.single d k)) * (2 : ℝ) ^ dot γ (Pi.single d k) := by
        rw [← Real.rpow_add two_pos, dot_single, dot_single]
        apply Real.one_le_rpow one_le_two
        rw [show -(β d * (k : ℝ)) + γ d * k = (γ d - β d) * k by ring]
        exact mul_nonneg (sub_nonneg.2 hd) (Nat.cast_nonneg k)
      calc a₂ * a₃ = a₂ * a₃ * 1 := (mul_one _).symm
        _ ≤ a₂ * a₃ * ((2 : ℝ) ^ (-dot β (Pi.single d k)) * (2 : ℝ) ^ dot γ (Pi.single d k)) :=
            mul_le_mul_of_nonneg_left h2 (mul_pos ha₂ ha₃).le
        _ = a₂ * (2 : ℝ) ^ (-dot β (Pi.single d k)) * (a₃ * (2 : ℝ) ^ dot γ (Pi.single d k)) := by
            ring
        _ ≤ V (Pi.single d k) * C (Pi.single d k) := h1
    have hax : ((L d : ℝ) + 1) * Real.sqrt (a₂ * a₃) ≤
        ∑ ℓ ∈ rectSet L, Real.sqrt (V ℓ * C ℓ) :=
      calc ((L d : ℝ) + 1) * Real.sqrt (a₂ * a₃)
          = ∑ k ∈ range (L d + 1), Real.sqrt (a₂ * a₃) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        _ ≤ ∑ k ∈ range (L d + 1), Real.sqrt (V (Pi.single d k) * C (Pi.single d k)) :=
            Finset.sum_le_sum fun k _ => Real.sqrt_le_sqrt (hVC k)
        _ ≤ ∑ ℓ ∈ rectSet L, Real.sqrt (V ℓ * C ℓ) :=
            sum_axis_le_sum_rectSet (f := fun ℓ => Real.sqrt (V ℓ * C ℓ))
              (fun ℓ => Real.sqrt_nonneg _) L d
    have hsq : ((L d : ℝ) + 1) ^ 2 * (a₂ * a₃) ≤ (∑ ℓ ∈ rectSet L, Real.sqrt (V ℓ * C ℓ)) ^ 2 := by
      have h0 : 0 ≤ ((L d : ℝ) + 1) * Real.sqrt (a₂ * a₃) := by positivity
      calc ((L d : ℝ) + 1) ^ 2 * (a₂ * a₃) = (((L d : ℝ) + 1) * Real.sqrt (a₂ * a₃)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (mul_pos ha₂ ha₃).le]
        _ ≤ (∑ ℓ ∈ rectSet L, Real.sqrt (V ℓ * C ℓ)) ^ 2 := pow_le_pow_left₀ h0 hax 2
    rw [hcost]
    calc a₂ * a₃ * ((L d : ℝ) + 1) ^ 2 * ε ^ (-2 : ℝ)
        = (ε ^ 2)⁻¹ * (((L d : ℝ) + 1) ^ 2 * (a₂ * a₃)) := by
          rw [← eps_inv_sq_eq hε, inv_pow]
          ring
      _ ≤ (ε ^ 2)⁻¹ * (∑ ℓ ∈ rectSet L, Real.sqrt (V ℓ * C ℓ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 (pow_nonneg hε.le 2))
      _ ≤ ∑ ℓ ∈ rectSet L, (N ℓ : ℝ) * C ℓ := hcs
  exact ⟨hpart1, hpart2, hpart3⟩

/-- **A rectangle attains the order `ε⁻²` only when `η < 0` and `∑_d γ_d/α_d ≤ 2`** (the converse
direction of Giles 2015, §2.4, p. 15: "Haji-Ali et al. (2014a) prove that this gives the optimal
order of complexity only when `η < 0`, and under the additional condition that
`∑_d γ_d/α_d ≤ 2`"), under the attained rates of `mimc_rect_lower_bounds`.  If for some `c₄` and
`ε₀ > 0` every `0 < ε < ε₀` admits a rectangle `rect L` and sample sizes `N_ℓ ≥ 1` with
`MSE < ε²` and expected cost `≤ c₄ ε⁻²`, then `γ_d < β_d` for every `d` (that is, `η < 0`) and
`∑_d γ_d/α_d ≤ 2`.  Together with `giles_mimc_rectangular` this is the statement quoted above. -/
theorem mimc_rect_necessary (P : Ω → ℝ) (Pℓ : (Fin D → ℕ) → Ω → ℝ)
    (Y : (Fin D → ℕ) → ℕ → Ω → ℝ) (Cost : (Fin D → ℕ) → ℕ → Ω → ℝ) (V C : (Fin D → ℕ) → ℝ)
    {α β γ : Fin D → ℝ} {a₁ a₂ a₃ : ℝ} (hα : ∀ d, 0 < α d) (hγ : ∀ d, 0 ≤ γ d)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : (Fin D → ℕ) → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost_int : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (hCost_mean : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ n, 0 < n → μ[Y ℓ n] = μ[fun ω => crossDiff (fun m => Pℓ m ω) ℓ])
    (hbias : ∀ (ℓ : Fin D → ℕ) (d : Fin D),
      a₁ * (2 : ℝ) ^ (-(α d * ℓ d)) ≤ |μ[fun ω => Pℓ ℓ ω - P ω]|)
    (hV : ∀ ℓ, a₂ * (2 : ℝ) ^ (-dot β ℓ) ≤ V ℓ) (hC : ∀ ℓ, a₃ * (2 : ℝ) ^ dot γ ℓ ≤ C ℓ)
    (hopt : ∃ c₄ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (L : Fin D → ℕ) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ rectSet L, Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ rectSet L, Cost ℓ (N ℓ) ω] ≤ c₄ * ε ^ (-2 : ℝ)) :
    (∀ d, γ d < β d) ∧ ∑ d, γ d / α d ≤ 2 := by
  obtain ⟨c₄, ε₀, hε₀, hopt⟩ := hopt
  have key : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ L : Fin D → ℕ,
      (∀ d, a₁ / ε < (2 : ℝ) ^ (α d * L d)) ∧
      a₃ * (a₁ / ε) ^ (∑ d, γ d / α d) ≤ c₄ * ε ^ (-2 : ℝ) ∧
      ∀ d, β d ≤ γ d → a₂ * a₃ * ((L d : ℝ) + 1) ^ 2 * ε ^ (-2 : ℝ) ≤ c₄ * ε ^ (-2 : ℝ) := by
    intro ε hε hεε₀
    obtain ⟨L, N, hN, hmse, hcost⟩ := hopt ε hε hεε₀
    obtain ⟨h1, h2, h3⟩ := mimc_rect_lower_bounds P Pℓ Y Cost V C hα hγ ha₁ ha₂ ha₃ hε L N hN
      hP hPℓ hY (hind N hN) hCost_int hCost_mean h_var h_iii hbias hV hC hmse
    exact ⟨L, h1, h2.trans hcost, fun d hd => (h3 d hd).trans hcost⟩
  refine ⟨fun d => ?_, ?_⟩
  · -- `γ_d < β_d`: otherwise `L_d` stays bounded while `2^{α_d L_d} > a₁/ε` is unbounded
    by_contra hlt
    rw [not_lt] at hlt
    have hK : 0 < a₂ * a₃ := mul_pos ha₂ ha₃
    set B : ℝ := (2 : ℝ) ^ (α d * (c₄ / (a₂ * a₃)))
    have hB : 0 < B := Real.rpow_pos_of_pos two_pos _
    set ε : ℝ := min (ε₀ / 2) (a₁ / B)
    have hε : 0 < ε := lt_min (half_pos hε₀) (div_pos ha₁ hB)
    have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀)
    obtain ⟨L, h1, -, h3⟩ := key ε hε hεε₀
    have hc : a₂ * a₃ * ((L d : ℝ) + 1) ^ 2 ≤ c₄ :=
      le_of_mul_le_mul_right (h3 d hlt) (Real.rpow_pos_of_pos hε _)
    have hLsq : (L d : ℝ) ≤ ((L d : ℝ) + 1) ^ 2 := by
      nlinarith [sq_nonneg (L d : ℝ), (Nat.cast_nonneg (L d) : (0 : ℝ) ≤ L d)]
    have hLd : (L d : ℝ) ≤ c₄ / (a₂ * a₃) := by
      rw [le_div_iff₀ hK]
      calc (L d : ℝ) * (a₂ * a₃) = a₂ * a₃ * (L d : ℝ) := mul_comm _ _
        _ ≤ a₂ * a₃ * ((L d : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_left hLsq hK.le
        _ ≤ c₄ := hc
    have hle : (2 : ℝ) ^ (α d * L d) ≤ B :=
      Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hLd (hα d).le)
    have hεB : ε ≤ a₁ / B := min_le_right _ _
    rw [le_div_iff₀ hB] at hεB
    have hBε : B ≤ a₁ / ε := by
      rw [le_div_iff₀ hε, mul_comm]
      exact hεB
    linarith [h1 d]
  · -- `∑_d γ_d/α_d ≤ 2`: otherwise `a₃ a₁^s ≤ c₄ ε^{s−2}` for all small `ε`, with `s − 2 > 0`
    by_contra hlt
    rw [not_le] at hlt
    set s : ℝ := ∑ d, γ d / α d
    have hs2 : 0 < s - 2 := by linarith
    have hA : 0 < a₃ * a₁ ^ s := mul_pos ha₃ (Real.rpow_pos_of_pos ha₁ _)
    set c : ℝ := max c₄ 1
    have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
    set X : ℝ := a₃ * a₁ ^ s / (2 * c) with hX_def
    have hX : 0 < X := div_pos hA (mul_pos two_pos hc)
    set ε : ℝ := min (ε₀ / 2) (X ^ (1 / (s - 2)))
    have hε : 0 < ε := lt_min (half_pos hε₀) (Real.rpow_pos_of_pos hX _)
    have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀)
    obtain ⟨L, -, h2, -⟩ := key ε hε hεε₀
    have hεs : 0 < ε ^ s := Real.rpow_pos_of_pos hε s
    rw [Real.div_rpow ha₁.le hε.le] at h2
    have h3 : a₃ * (a₁ ^ s / ε ^ s) * ε ^ s = a₃ * a₁ ^ s := by
      rw [mul_assoc, div_mul_cancel₀ _ hεs.ne']
    have h4 : c₄ * ε ^ (-2 : ℝ) * ε ^ s = c₄ * ε ^ (s - 2) := by
      rw [mul_assoc, ← Real.rpow_add hε, show (-2 : ℝ) + s = s - 2 by ring]
    have h5 : a₃ * a₁ ^ s ≤ c₄ * ε ^ (s - 2) := by
      rw [← h3, ← h4]
      exact mul_le_mul_of_nonneg_right h2 hεs.le
    have h6 : ε ^ (s - 2) ≤ X :=
      calc ε ^ (s - 2) ≤ (X ^ (1 / (s - 2))) ^ (s - 2) :=
            Real.rpow_le_rpow hε.le (min_le_right _ _) hs2.le
        _ = X := by rw [← Real.rpow_mul hX.le, one_div_mul_cancel hs2.ne', Real.rpow_one]
    have h7 : c₄ * ε ^ (s - 2) ≤ c * X :=
      mul_le_mul (le_max_left _ _) h6 (Real.rpow_nonneg hε.le _) hc.le
    have h8 : c * X = a₃ * a₁ ^ s / 2 := by
      rw [hX_def, ← mul_div_assoc, mul_comm c, mul_div_mul_right _ _ hc.ne']
    linarith

end MLMC
