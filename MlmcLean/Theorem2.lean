import MlmcLean.Lattice
import MlmcLean.Estimator
import Mathlib.Algebra.Order.Group.DenselyOrdered

/-!
# Giles' Theorem 2: Multi-Index Monte Carlo

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.4,
Theorem 2 (p. 13–14), Giles' formulation of the MIMC theorem of Haji-Ali, Nobile & Tempone (2014a).

**Theorem 2 (Giles).** If there exist independent estimators `Y_ℓ` based on `N_ℓ` Monte Carlo
samples, each with expected cost `C_ℓ` and variance `V_ℓ`, and positive `D`-dimensional vectors
`α, β, γ` with `α_d ≥ ½β_d`, and positive constants `c₁, c₂, c₃` such that

  i)   `|E[P_ℓ − P]| → 0` as `min_d ℓ_d → ∞`,
  iii) `E[Y_ℓ] = E[ΔP_ℓ]`,
  ii)  `|E[Y_ℓ]| ≤ c₁ 2^{−α·ℓ}`,
  iv)  `V_ℓ ≤ c₂ 2^{−β·ℓ}`,
  v)   `C_ℓ ≤ c₃ 2^{γ·ℓ}`,

then there is `c₄ > 0` such that for any `ε < e⁻¹` there is a set of levels `𝓛` and integers `N_ℓ`
for which `Y = ∑_{ℓ∈𝓛} Y_ℓ` has `MSE < ε²` and expected cost
`E[C] ≤ c₄ ε⁻²` if `η < 0`, `c₄ ε⁻² |log ε|^{e₁}` if `η = 0`, `c₄ ε^{−2−η} |log ε|^{e₂}` if `η > 0`,
where `η = max_d (γ_d − β_d)/α_d`.  When `α_d > ½β_d` for all `d`, `e₁ = 2D₂` and
`e₂ = (D₂ − 1)(2 + η)`, with `D₂` the number of directions attaining `η`; "the form of the
exponents is more complicated when `α_d = ½β_d` for some `d`".

(Giles lists the conditions in the order i), iii), ii), iv), v); we keep his labels.)

**Results.**
* `giles_theorem2` — the theorem for `α_d > ½β_d`, with the paper's `e₁ = 2D₂`,
  `e₂ = (D₂ − 1)(2 + η)`;
* `giles_theorem2_boundary` — the theorem for `α_d ≥ ½β_d`; the paper leaves the exponents
  unspecified, and we prove `e₁ = 2D₂ + D`, `e₂ = (D₂ − 1)(2 + η) + D`;
* `mimc_complexity`, `mimc_complexity_boundary` — the deterministic statements behind them.

**Proof.** The summation region is a simplex `𝓛 = {ℓ : θ·ℓ ≤ L}` ("of the form `ℓ·n ≤ L`",
Giles p. 15), here with `θ_d = α_d + (γ_d − β_d)/2`, whose level sets are those of the ratio
`2^{−α·ℓ} / 2^{(γ−β)·ℓ/2}` of the bias bound to `√(V_ℓ C_ℓ)`.  With `a = 2/(2 + η)`,
`α = aθ + δ` and `(γ − β)/2 = (1 − a)θ − δ` where `δ_d = α_d (η − (γ_d−β_d)/α_d)/(2 + η) ≥ 0`
vanishes exactly in the `D₂` directions attaining `η`.  The lattice sums of
`MlmcLean/Lattice.lean` then bound the bias by `(1+L)^{D₂−1} 2^{−aL}` and `∑_{𝓛} √(V_ℓ C_ℓ)` by
`1`, `(1+L)^{D₂}`, `(1+L)^{D₂−1} 2^{(1−a)L}` in the three regimes.  `L` is the least level with
bias `≤ ε/2`, and `N_ℓ` is the rounded-up optimal allocation of `MlmcLean/Allocation.lean`.
-/

open MeasureTheory ProbabilityTheory Finset Real

namespace MLMC

variable {D : ℕ}

/-! ### The pairing `a·ℓ` -/

lemma dot_linear {a b e : Fin D → ℝ} {u v : ℝ} (h : ∀ d, a d = u * b d + v * e d)
    (ℓ : Fin D → ℕ) : dot a ℓ = u * dot b ℓ + v * dot e ℓ := by
  simp only [dot, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by rw [h d]; ring

lemma dot_le_dot {a b : Fin D → ℝ} (h : ∀ d, a d ≤ b d) (ℓ : Fin D → ℕ) :
    dot a ℓ ≤ dot b ℓ :=
  Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (h d) (Nat.cast_nonneg _)

/-! ### The exponents of Theorem 2 -/

section Exponents

variable [NeZero D]

/-- `η = max_d (γ_d − β_d)/α_d` (Giles 2015, Theorem 2). -/
noncomputable def mimcEta (α β γ : Fin D → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun d => (γ d - β d) / α d

/-- `D₂ = #{d : (γ_d − β_d)/α_d = η}`, the number of directions attaining `η`
(Giles 2015, Theorem 2). -/
noncomputable def mimcD2 (α β γ : Fin D → ℝ) : ℕ :=
  (univ.filter fun d => (γ d - β d) / α d = mimcEta α β γ).card

lemma le_mimcEta (α β γ : Fin D → ℝ) (d : Fin D) : (γ d - β d) / α d ≤ mimcEta α β γ :=
  Finset.le_sup' (fun d => (γ d - β d) / α d) (Finset.mem_univ d)

lemma exists_eq_mimcEta (α β γ : Fin D → ℝ) : ∃ d, (γ d - β d) / α d = mimcEta α β γ := by
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_sup' univ_nonempty fun d => (γ d - β d) / α d
  exact ⟨d, hd.symm⟩

lemma one_le_mimcD2 (α β γ : Fin D → ℝ) : 1 ≤ mimcD2 α β γ := by
  obtain ⟨d, hd⟩ := exists_eq_mimcEta α β γ
  exact Finset.card_pos.2 ⟨d, Finset.mem_filter.2 ⟨Finset.mem_univ d, hd⟩⟩

end Exponents

/-- The three regimes of Theorem 2: `ε⁻²` if `η < 0`, `ε⁻² |log ε|^{e₁}` if `η = 0` and
`ε^{−2−η} |log ε|^{e₂}` if `η > 0`. -/
noncomputable def mimcBound (η e₁ e₂ ε : ℝ) : ℝ :=
  if η < 0 then ε ^ (-2 : ℝ)
  else if η = 0 then ε ^ (-2 : ℝ) * |Real.log ε| ^ e₁
  else ε ^ (-2 - η) * |Real.log ε| ^ e₂

lemma mimcBound_of_neg {η e₁ e₂ ε : ℝ} (h : η < 0) : mimcBound η e₁ e₂ ε = ε ^ (-2 : ℝ) := by
  simp [mimcBound, h]

lemma mimcBound_of_eq {η e₁ e₂ ε : ℝ} (h : η = 0) :
    mimcBound η e₁ e₂ ε = ε ^ (-2 : ℝ) * |Real.log ε| ^ e₁ := by
  simp [mimcBound, h]

lemma mimcBound_of_pos {η e₁ e₂ ε : ℝ} (h : 0 < η) :
    mimcBound η e₁ e₂ ε = ε ^ (-2 - η) * |Real.log ε| ^ e₂ := by
  simp [mimcBound, h.ne', not_lt.2 h.le]

lemma mimcBound_nonneg {η e₁ e₂ ε : ℝ} (hε : 0 < ε) : 0 ≤ mimcBound η e₁ e₂ ε := by
  unfold mimcBound
  split_ifs <;> positivity

lemma abs_log_eq_neg_log {ε : ℝ} (hε : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    |Real.log ε| = -Real.log ε :=
  abs_of_neg (Real.log_neg hε (eps_lt_one hε1))

/-- Larger log exponents give a larger bound (for `ε < e⁻¹`, where `|log ε| ≥ 1`). -/
lemma mimcBound_mono {η e₁ e₂ e₁' e₂' ε : ℝ} (hε : 0 < ε) (hε1 : ε < Real.exp (-1))
    (h1 : e₁ ≤ e₁') (h2 : e₂ ≤ e₂') : mimcBound η e₁ e₂ ε ≤ mimcBound η e₁' e₂' ε := by
  have ht : 1 ≤ |Real.log ε| := by
    rw [abs_log_eq_neg_log hε hε1]
    exact one_le_neg_log hε hε1
  unfold mimcBound
  split_ifs
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht h1)
      (Real.rpow_pos_of_pos hε _).le
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht h2)
      (Real.rpow_pos_of_pos hε _).le

/-! ### Step 1 — the level `L` -/

/-- **Choice of the level `L`** (proof of Giles 2015, Theorem 2).  With the tail constant of
`tail_bound`, take the least `L` for which the bias bound `c₁ K (1+L)^{m−1} 2^{−aL}` is at most
`ε/2`.  Minimality gives `2^{aL} ≤ K_P (1+L)^{m−1}/ε`, and hence `1 + L ≤ K_L |log ε|`. -/
lemma mimc_exists_level {θ δ : Fin D → ℝ} (hθ : ∀ d, 0 < θ d) (hδ : ∀ d, 0 ≤ δ d) {a c₁ : ℝ}
    (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ K_P K_L : ℝ, 0 < K_P ∧ 0 < K_L ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) → ∃ L : ℕ,
      (∀ n : ℕ, c₁ * ∑ ℓ ∈ box D n,
          (if (L : ℝ) < dot θ ℓ then (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) else 0) ≤ ε / 2) ∧
      (2 : ℝ) ^ (a * L) ≤ K_P * (1 + (L : ℝ)) ^ (crit δ - 1) / ε ∧
      1 + (L : ℝ) ≤ K_L * (-Real.log ε) := by
  classical
  obtain ⟨K_T, hK_T, htail⟩ := tail_bound hθ hδ ha
  obtain ⟨K_A, hK_A, hA⟩ := one_add_rpow_le_two_rpow
    (Nat.cast_nonneg (crit δ - 1) : (0 : ℝ) ≤ ((crit δ - 1 : ℕ) : ℝ)) (half_pos ha)
  have hA' : ∀ x : ℝ, 0 ≤ x → (1 + x) ^ (crit δ - 1) ≤ K_A * (2 : ℝ) ^ (a / 2 * x) := by
    intro x hx
    rw [← Real.rpow_natCast]
    exact hA x hx
  have h2a : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos two_pos a
  have hK0 : 0 ≤ 2 * 2 ^ a * c₁ * K_T :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two h2a.le) hc₁.le) hK_T
  obtain ⟨K_P, hK_P_def⟩ : ∃ K : ℝ, K = 1 + 2 * 2 ^ a * c₁ * K_T := ⟨_, rfl⟩
  have hK_P : 0 < K_P := by rw [hK_P_def]; linarith
  have hKPA : 0 < K_P * K_A := mul_pos hK_P hK_A
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc' : 0 < 2 / (a * Real.log 2) := div_pos two_pos (mul_pos ha hlog2)
  obtain ⟨K_L, hK_L_def⟩ : ∃ K : ℝ,
      K = 1 + 2 / (a * Real.log 2) * (|Real.log (K_P * K_A)| + 1) := ⟨_, rfl⟩
  have hK_L : 0 < K_L := by
    rw [hK_L_def]
    have := mul_nonneg hc'.le (add_nonneg (abs_nonneg (Real.log (K_P * K_A))) zero_le_one)
    linarith
  refine ⟨K_P, K_L, hK_P, hK_L, fun ε hε hε1 => ?_⟩
  have hε1' : ε < 1 := eps_lt_one hε1
  have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
  -- the bias bound `c₁ K_T (1+L)^{m−1} 2^{−aL}` eventually drops below `ε/2`
  have hq0 : 0 < (2 : ℝ) ^ (-(a / 2)) := Real.rpow_pos_of_pos two_pos _
  have hq1 : (2 : ℝ) ^ (-(a / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hK1 : 0 < c₁ * K_T * K_A + 1 := by
    have := mul_nonneg (mul_nonneg hc₁.le hK_T) hK_A.le
    linarith
  have hbound : ∀ L : ℕ, c₁ * (K_T * (1 + (L : ℝ)) ^ (crit δ - 1) * (2 : ℝ) ^ (-(a * L))) ≤
      (c₁ * K_T * K_A + 1) * ((2 : ℝ) ^ (-(a / 2))) ^ L := by
    intro L
    have h1 := hA' L (Nat.cast_nonneg L)
    have h2 : (2 : ℝ) ^ (a / 2 * L) * (2 : ℝ) ^ (-(a * L)) = ((2 : ℝ) ^ (-(a / 2))) ^ L := by
      rw [← Real.rpow_add two_pos, ← two_rpow_mul_nat]
      congr 1
      ring
    calc c₁ * (K_T * (1 + (L : ℝ)) ^ (crit δ - 1) * (2 : ℝ) ^ (-(a * L)))
        ≤ c₁ * (K_T * (K_A * (2 : ℝ) ^ (a / 2 * L)) * (2 : ℝ) ^ (-(a * L))) := by
          apply mul_le_mul_of_nonneg_left _ hc₁.le
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos two_pos _).le
          exact mul_le_mul_of_nonneg_left h1 hK_T
      _ = c₁ * K_T * K_A * ((2 : ℝ) ^ (a / 2 * L) * (2 : ℝ) ^ (-(a * L))) := by ring
      _ = c₁ * K_T * K_A * ((2 : ℝ) ^ (-(a / 2))) ^ L := by rw [h2]
      _ ≤ (c₁ * K_T * K_A + 1) * ((2 : ℝ) ^ (-(a / 2))) ^ L :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le L)
  obtain ⟨L₀, hL₀⟩ := exists_pow_lt_of_lt_one (div_pos hε (mul_pos two_pos hK1)) hq1
  have hex : ∃ L : ℕ,
      c₁ * (K_T * (1 + (L : ℝ)) ^ (crit δ - 1) * (2 : ℝ) ^ (-(a * L))) ≤ ε / 2 := by
    refine ⟨L₀, (hbound L₀).trans ?_⟩
    have e : (c₁ * K_T * K_A + 1) * (ε / (2 * (c₁ * K_T * K_A + 1))) = ε / 2 := by
      rw [mul_div_assoc', mul_comm 2 (c₁ * K_T * K_A + 1), mul_div_mul_left ε 2 hK1.ne']
    have := mul_lt_mul_of_pos_left hL₀ hK1
    linarith
  obtain ⟨L, hLspec, hLmin⟩ : ∃ L : ℕ,
      c₁ * (K_T * (1 + (L : ℝ)) ^ (crit δ - 1) * (2 : ℝ) ^ (-(a * L))) ≤ ε / 2 ∧
      ∀ L' < L, ¬ c₁ * (K_T * (1 + (L' : ℝ)) ^ (crit δ - 1) * (2 : ℝ) ^ (-(a * L'))) ≤ ε / 2 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun L' h => Nat.find_min hex h⟩
  have hW : 0 ≤ (1 + (L : ℝ)) ^ (crit δ - 1) := pow_nonneg (by positivity) _
  -- by minimality, `2^{aL} ≤ K_P (1+L)^{m−1}/ε`
  have hA2 : (2 : ℝ) ^ (a * L) ≤ K_P * (1 + (L : ℝ)) ^ (crit δ - 1) / ε := by
    rw [le_div_iff₀ hε]
    rcases Nat.eq_zero_or_pos L with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, add_zero, one_pow, mul_one, one_mul]
      rw [hK_P_def]
      linarith
    · have hnot := hLmin (L - 1) (by omega)
      have hL1 : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
      rw [hL1, not_le] at hnot
      have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hpos
      have e1 : (2 : ℝ) ^ (-(a * ((L : ℝ) - 1))) = 2 ^ a * (2 : ℝ) ^ (-(a * L)) := by
        rw [← Real.rpow_add two_pos]
        congr 1
        ring
      have e2 : (1 + ((L : ℝ) - 1)) ^ (crit δ - 1) ≤ (1 + (L : ℝ)) ^ (crit δ - 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      have hXY : (2 : ℝ) ^ (a * L) * (2 : ℝ) ^ (-(a * L)) = 1 := by
        rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
      have hX : 0 < (2 : ℝ) ^ (a * L) := Real.rpow_pos_of_pos two_pos _
      have hY : 0 < (2 : ℝ) ^ (-(a * L)) := Real.rpow_pos_of_pos two_pos _
      have h3 : ε / 2 <
          c₁ * (K_T * (1 + (L : ℝ)) ^ (crit δ - 1) * (2 ^ a * (2 : ℝ) ^ (-(a * L)))) := by
        calc ε / 2 < c₁ * (K_T * (1 + ((L : ℝ) - 1)) ^ (crit δ - 1) *
              (2 : ℝ) ^ (-(a * ((L : ℝ) - 1)))) := hnot
          _ ≤ c₁ * (K_T * (1 + (L : ℝ)) ^ (crit δ - 1) * (2 ^ a * (2 : ℝ) ^ (-(a * L)))) := by
              rw [e1]
              apply mul_le_mul_of_nonneg_left _ hc₁.le
              apply mul_le_mul_of_nonneg_right _ (mul_pos h2a hY).le
              exact mul_le_mul_of_nonneg_left e2 hK_T
      have h4 := mul_lt_mul_of_pos_left h3 hX
      have e3 : (2 : ℝ) ^ (a * L) *
            (c₁ * (K_T * (1 + (L : ℝ)) ^ (crit δ - 1) * (2 ^ a * (2 : ℝ) ^ (-(a * L))))) =
          c₁ * K_T * (1 + (L : ℝ)) ^ (crit δ - 1) * 2 ^ a *
            ((2 : ℝ) ^ (a * L) * (2 : ℝ) ^ (-(a * L))) := by ring
      rw [e3, hXY, mul_one] at h4
      have e4 : K_P * (1 + (L : ℝ)) ^ (crit δ - 1) = (1 + (L : ℝ)) ^ (crit δ - 1) +
          2 * (c₁ * K_T * (1 + (L : ℝ)) ^ (crit δ - 1) * 2 ^ a) := by
        rw [hK_P_def]
        ring
      rw [e4]
      linarith
  refine ⟨L, fun n => (mul_le_mul_of_nonneg_left (htail n L (Nat.cast_nonneg L)) hc₁.le).trans
    hLspec, hA2, ?_⟩
  -- and then `1 + L ≤ K_L |log ε|`
  have h5 : (2 : ℝ) ^ (a * L) ≤ K_P * (K_A * (2 : ℝ) ^ (a / 2 * L)) / ε := by
    refine hA2.trans (div_le_div_of_nonneg_right ?_ hε.le)
    exact mul_le_mul_of_nonneg_left (hA' L (Nat.cast_nonneg L)) hK_P.le
  have hpos' : 0 < (2 : ℝ) ^ (a / 2 * L) := Real.rpow_pos_of_pos two_pos _
  have h6 : (2 : ℝ) ^ (a / 2 * L) ≤ K_P * K_A / ε := by
    have e : (2 : ℝ) ^ (a * L) = (2 : ℝ) ^ (a / 2 * L) * (2 : ℝ) ^ (a / 2 * L) := by
      rw [← Real.rpow_add two_pos]
      congr 1
      ring
    rw [e, le_div_iff₀ hε] at h5
    rw [le_div_iff₀ hε]
    apply le_of_mul_le_mul_left _ hpos'
    calc (2 : ℝ) ^ (a / 2 * L) * ((2 : ℝ) ^ (a / 2 * L) * ε)
        = (2 : ℝ) ^ (a / 2 * L) * (2 : ℝ) ^ (a / 2 * L) * ε := by ring
      _ ≤ K_P * (K_A * (2 : ℝ) ^ (a / 2 * L)) := h5
      _ = (2 : ℝ) ^ (a / 2 * L) * (K_P * K_A) := by ring
  have h7 : a / 2 * L * Real.log 2 ≤ Real.log (K_P * K_A) + -Real.log ε := by
    have := Real.log_le_log hpos' h6
    rw [Real.log_rpow two_pos, Real.log_div hKPA.ne' hε.ne'] at this
    linarith
  have h8 : (L : ℝ) ≤ 2 / (a * Real.log 2) * (|Real.log (K_P * K_A)| + -Real.log ε) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos ha hlog2)]
    linarith [le_abs_self (Real.log (K_P * K_A))]
  have h9 : 2 / (a * Real.log 2) * (|Real.log (K_P * K_A)| + -Real.log ε) ≤
      2 / (a * Real.log 2) * (|Real.log (K_P * K_A)| + 1) * (-Real.log ε) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hc'.le
    nlinarith [abs_nonneg (Real.log (K_P * K_A))]
  rw [hK_L_def]
  linarith

/-! ### Step 2 — the index set and the sample sizes -/

/-- **Giles' construction for MIMC**: the index set `𝓛 = {θ·ℓ ≤ L}` with `L` from
`mimc_exists_level`, and the rounded-up optimal sample sizes `N_ℓ` (Giles 2015, §1.3) for
`V_ℓ = c₂ 2^{−β·ℓ}`, `C_ℓ = c₃ 2^{γ·ℓ}` and the variance target `ε²/2`. -/
lemma mimc_construction {α β γ θ δ g : Fin D → ℝ} {a c₁ c₂ c₃ : ℝ}
    (hθ : ∀ d, 0 < θ d) (hδ : ∀ d, 0 ≤ δ d) (ha : 0 < a)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hα : ∀ d, α d = a * θ d + 1 * δ d) (hg : ∀ d, g d = (1 / 2) * γ d + (-1 / 2) * β d) :
    ∃ K_P K_L : ℝ, 0 < K_P ∧ 0 < K_L ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (∀ s : Finset (Fin D → ℕ),
          c₁ * ∑ ℓ ∈ s \ indexSet θ L, (2 : ℝ) ^ (-dot α ℓ) ≤ ε / 2) ∧
        ∑ ℓ ∈ indexSet θ L, c₂ * (2 : ℝ) ^ (-dot β ℓ) / N ℓ ≤ ε ^ 2 / 2 ∧
        ∑ ℓ ∈ indexSet θ L, (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ dot γ ℓ) ≤
          2 * (c₂ * c₃) * ε⁻¹ ^ 2 * (∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ) ^ 2 +
            c₃ * ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot γ ℓ ∧
        (2 : ℝ) ^ (a * L) ≤ K_P * (1 + (L : ℝ)) ^ (crit δ - 1) / ε ∧
        1 + (L : ℝ) ≤ K_L * (-Real.log ε) := by
  obtain ⟨K_P, K_L, hK_P, hK_L, hlev⟩ := mimc_exists_level hθ hδ ha hc₁
  refine ⟨K_P, K_L, hK_P, hK_L, fun ε hε hε1 => ?_⟩
  obtain ⟨L, hbias, hP, hLlog⟩ := hlev ε hε hε1
  set V : (Fin D → ℕ) → ℝ := fun ℓ => c₂ * (2 : ℝ) ^ (-dot β ℓ) with hV
  set C : (Fin D → ℕ) → ℝ := fun ℓ => c₃ * (2 : ℝ) ^ dot γ ℓ with hC
  have hVpos : ∀ ℓ, 0 < V ℓ := fun ℓ => mul_pos hc₂ (Real.rpow_pos_of_pos two_pos _)
  have hCpos : ∀ ℓ, 0 < C ℓ := fun ℓ => mul_pos hc₃ (Real.rpow_pos_of_pos two_pos _)
  have hτ : 0 < ε ^ 2 / 2 := by positivity
  have hs : (indexSet θ L).Nonempty := ⟨0, (mem_indexSet hθ).2 (by simp [dot])⟩
  refine ⟨L, optimalN (indexSet θ L) V C (ε ^ 2 / 2), fun ℓ => optimalN_pos hs hVpos hCpos hτ ℓ,
    ?_, optimalN_variance hs hVpos hCpos hτ, ?_, hP, hLlog⟩
  · -- bias: the levels outside `𝓛` are the tail `θ·ℓ > L`
    intro s
    obtain ⟨n, hn⟩ := exists_subset_box s
    have hdα : ∀ ℓ, (2 : ℝ) ^ (-dot α ℓ) = (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) := by
      intro ℓ
      rw [dot_linear hα ℓ]
      congr 1
      ring
    calc c₁ * ∑ ℓ ∈ s \ indexSet θ L, (2 : ℝ) ^ (-dot α ℓ)
        = c₁ * ∑ ℓ ∈ s \ indexSet θ L, (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) := by
          rw [Finset.sum_congr rfl fun ℓ _ => hdα ℓ]
      _ ≤ c₁ * ∑ ℓ ∈ (box D n).filter (fun ℓ => (L : ℝ) < dot θ ℓ),
            (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) := by
          apply mul_le_mul_of_nonneg_left _ hc₁.le
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ℓ hℓ
            rw [Finset.mem_sdiff, mem_indexSet hθ] at hℓ
            exact Finset.mem_filter.2 ⟨hn hℓ.1, not_le.1 hℓ.2⟩
          · intro ℓ _ _
            exact (Real.rpow_pos_of_pos two_pos _).le
      _ = c₁ * ∑ ℓ ∈ box D n,
            (if (L : ℝ) < dot θ ℓ then (2 : ℝ) ^ (-(a * dot θ ℓ) - dot δ ℓ) else 0) := by
          rw [Finset.sum_filter]
      _ ≤ ε / 2 := hbias n
  · -- cost: `∑ N_ℓ C_ℓ ≤ (ε²/2)⁻¹ (∑ √(V_ℓ C_ℓ))² + ∑ C_ℓ` and `√(V_ℓ C_ℓ) = √(c₂c₃) 2^{g·ℓ}`
    have hc := optimalN_cost hs hVpos hCpos hτ
    have hS : S (indexSet θ L) V C =
        Real.sqrt (c₂ * c₃) * ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ := by
      unfold S
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      have hg2 : dot γ ℓ - dot β ℓ = 2 * dot g ℓ := by
        rw [dot_linear hg ℓ]
        ring
      have e : ((2 : ℝ) ^ dot g ℓ) ^ 2 = (2 : ℝ) ^ dot γ ℓ * (2 : ℝ) ^ (-dot β ℓ) := by
        rw [sq, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        congr 1
        linarith
      have h1 : V ℓ * C ℓ = (c₂ * c₃) * ((2 : ℝ) ^ dot g ℓ) ^ 2 := by
        rw [e]
        simp only [hV, hC]
        ring
      rw [h1, Real.sqrt_mul (mul_pos hc₂ hc₃).le,
        Real.sqrt_sq (Real.rpow_pos_of_pos two_pos _).le]
    have hτinv : (ε ^ 2 / 2)⁻¹ = 2 * ε⁻¹ ^ 2 := by
      rw [inv_div, inv_pow]
      ring
    have hCsum : ∑ ℓ ∈ indexSet θ L, C ℓ = c₃ * ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot γ ℓ := by
      rw [Finset.mul_sum]
    rw [hS, hτinv, hCsum, mul_pow, Real.sq_sqrt (mul_pos hc₂ hc₃).le] at hc
    calc _ ≤ _ := hc
      _ = _ := by ring

/-! ### Step 3 — powers of the level -/

/-- From `2^{aL} ≤ K (1+L)^p / ε` and `1 + L ≤ K_L t`:
`(1+L)^q 2^{bL} ≤ K^{b/a} K_L^{q + pb/a} t^{q + pb/a} ε^{−b/a}`. -/
lemma mimc_level_power {a b K K_L ε t q : ℝ} {p L : ℕ} (ha : 0 < a) (hb : 0 ≤ b) (hK : 0 < K)
    (hK_L : 0 < K_L) (hε : 0 < ε) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hP : (2 : ℝ) ^ (a * L) ≤ K * (1 + (L : ℝ)) ^ p / ε) (hL : 1 + (L : ℝ) ≤ K_L * t) :
    (1 + (L : ℝ)) ^ q * (2 : ℝ) ^ (b * L) ≤
      K ^ (b / a) * K_L ^ (q + p * (b / a)) * t ^ (q + p * (b / a)) * ε ^ (-(b / a)) := by
  have hu : (0 : ℝ) < 1 + L := by positivity
  have h2 := two_rpow_L_le ha hb (mul_pos hK (pow_pos hu p)) hε hP
  have e1 : (K * (1 + (L : ℝ)) ^ p) ^ (b / a) =
      K ^ (b / a) * (1 + (L : ℝ)) ^ ((p : ℝ) * (b / a)) := by
    rw [Real.mul_rpow hK.le (pow_nonneg hu.le p), ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  have hexp : 0 ≤ q + p * (b / a) :=
    add_nonneg hq (mul_nonneg (Nat.cast_nonneg p) (div_nonneg hb ha.le))
  have e2 : (1 + (L : ℝ)) ^ (q + p * (b / a)) ≤ K_L ^ (q + p * (b / a)) * t ^ (q + p * (b / a)) := by
    rw [← Real.mul_rpow hK_L.le ht]
    exact Real.rpow_le_rpow hu.le hL hexp
  calc (1 + (L : ℝ)) ^ q * (2 : ℝ) ^ (b * L)
      ≤ (1 + (L : ℝ)) ^ q * (K ^ (b / a) * (1 + (L : ℝ)) ^ ((p : ℝ) * (b / a)) *
          ε ^ (-(b / a))) := by
        rw [← e1]
        exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hu.le _)
    _ = K ^ (b / a) * (1 + (L : ℝ)) ^ (q + p * (b / a)) * ε ^ (-(b / a)) := by
        rw [Real.rpow_add hu]
        ring
    _ ≤ K ^ (b / a) * (K_L ^ (q + p * (b / a)) * t ^ (q + p * (b / a))) * ε ^ (-(b / a)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hε _).le
        exact mul_le_mul_of_nonneg_left e2 (Real.rpow_nonneg hK.le _)
    _ = _ := by ring

/-- The rounding-up overhead `c₃ ∑_{θ·ℓ ≤ L} 2^{γ·ℓ}` when `γ ≤ cθ` componentwise. -/
lemma mimc_extra_term {θ γ : Fin D → ℝ} {a c c₃ K_P K_L ε : ℝ} {p L : ℕ}
    (hθ : ∀ d, 0 < θ d) (ha : 0 < a) (hc : 0 ≤ c) (hc₃ : 0 < c₃) (hK_P : 0 < K_P)
    (hK_L : 0 < K_L) (hε : 0 < ε) (hγ : ∀ d, γ d ≤ c * θ d)
    (hP : (2 : ℝ) ^ (a * L) ≤ K_P * (1 + (L : ℝ)) ^ p / ε)
    (hL : 1 + (L : ℝ) ≤ K_L * (-Real.log ε)) :
    c₃ * ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot γ ℓ ≤
      c₃ * (∏ d, (1 / θ d + 1)) * (K_P ^ (c / a) * K_L ^ ((D : ℝ) + p * (c / a))) *
        (-Real.log ε) ^ ((D : ℝ) + p * (c / a)) * ε ^ (-(c / a)) := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have ht : 0 ≤ -Real.log ε := by
    by_contra h
    push_neg at h
    nlinarith
  have hK0 : 0 ≤ ∏ d, (1 / θ d + 1) := Finset.prod_nonneg fun d _ => by
    have := div_nonneg zero_le_one (hθ d).le
    linarith
  -- every term is at most `2^{cL}`
  have h1 : ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot γ ℓ ≤
      (indexSet θ L).card * (2 : ℝ) ^ (c * L) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun ℓ hℓ => Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have h2 := (mem_indexSet hθ).1 hℓ
    calc dot γ ℓ ≤ dot (fun d => c * θ d) ℓ := dot_le_dot hγ ℓ
      _ = c * dot θ ℓ := by simp only [dot, Finset.mul_sum, mul_assoc]
      _ ≤ c * L := mul_le_mul_of_nonneg_left h2 hc
  have hcard : ((indexSet θ L).card : ℝ) ≤ (1 + (L : ℝ)) ^ (D : ℝ) * ∏ d, (1 / θ d + 1) := by
    rw [Real.rpow_natCast]
    exact card_indexSet_le hθ hL0
  have hpow := mimc_level_power (q := (D : ℝ)) ha hc hK_P hK_L hε ht (Nat.cast_nonneg D) hP hL
  calc c₃ * ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot γ ℓ
      ≤ c₃ * ((indexSet θ L).card * (2 : ℝ) ^ (c * L)) := mul_le_mul_of_nonneg_left h1 hc₃.le
    _ ≤ c₃ * (((1 + (L : ℝ)) ^ (D : ℝ) * ∏ d, (1 / θ d + 1)) * (2 : ℝ) ^ (c * L)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcard (Real.rpow_pos_of_pos two_pos _).le) hc₃.le
    _ = c₃ * (∏ d, (1 / θ d + 1)) * ((1 + (L : ℝ)) ^ (D : ℝ) * (2 : ℝ) ^ (c * L)) := by ring
    _ ≤ c₃ * (∏ d, (1 / θ d + 1)) * (K_P ^ (c / a) * K_L ^ ((D : ℝ) + p * (c / a)) *
          (-Real.log ε) ^ ((D : ℝ) + p * (c / a)) * ε ^ (-(c / a))) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hc₃.le hK0)
    _ = _ := by ring

/-! ### The deterministic core -/

/-- **Giles' Theorem 2 — deterministic core.**  Let `θ_d = α_d + (γ_d − β_d)/2` and let `c ≥ 0`
with `γ_d ≤ c θ_d` for all `d`.  With `V_ℓ = c₂ 2^{−β·ℓ}` and `C_ℓ = c₃ 2^{γ·ℓ}` there are, for
every `0 < ε < e⁻¹`, a finite set of levels `𝓛` and `N_ℓ ≥ 1` such that the bias of every finite
part of the complement of `𝓛` is at most `ε/2`, `∑_{𝓛} V_ℓ/N_ℓ ≤ ε²/2`, and the cost is at most
the main term `K_M · (ε⁻², ε⁻²|log ε|^{2D₂}, ε^{−2−η}|log ε|^{(D₂−1)(2+η)})` plus the
rounding-up overhead `K_X |log ε|^{D + (D₂−1)s} ε^{−s}` with `s = c(2 + η)/2`. -/
theorem mimc_complexity_core [NeZero D] {α β γ : Fin D → ℝ} {c₁ c₂ c₃ c : ℝ}
    (hα : ∀ d, 0 < α d) (hγ : ∀ d, 0 < γ d) (hαβ : ∀ d, β d / 2 ≤ α d)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc : 0 ≤ c)
    (hcγ : ∀ d, γ d ≤ c * (α d + (γ d - β d) / 2)) :
    ∃ K_M K_X : ℝ, 0 ≤ K_M ∧ 0 ≤ K_X ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (𝓛 : Finset (Fin D → ℕ)) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (∀ s : Finset (Fin D → ℕ), c₁ * ∑ ℓ ∈ s \ 𝓛, (2 : ℝ) ^ (-dot α ℓ) ≤ ε / 2) ∧
        ∑ ℓ ∈ 𝓛, c₂ * (2 : ℝ) ^ (-dot β ℓ) / N ℓ ≤ ε ^ 2 / 2 ∧
        ∑ ℓ ∈ 𝓛, (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ dot γ ℓ) ≤
          K_M * mimcBound (mimcEta α β γ) (2 * mimcD2 α β γ)
              ((mimcD2 α β γ - 1) * (2 + mimcEta α β γ)) ε +
            K_X * (-Real.log ε) ^ ((D : ℝ) + (mimcD2 α β γ - 1) * (c * (2 + mimcEta α β γ) / 2)) *
              ε ^ (-(c * (2 + mimcEta α β γ) / 2)) := by
  have hr := le_mimcEta α β γ
  obtain ⟨d₀, hd₀⟩ := exists_eq_mimcEta α β γ
  have hm1 := one_le_mimcD2 α β γ
  generalize hm_def : mimcD2 α β γ = m at hm1 ⊢
  generalize hη_def : mimcEta α β γ = η at hr hd₀ ⊢
  -- `η > −2`
  have hη2 : 0 < 2 + η := by
    have h1 : -2 < (γ d₀ - β d₀) / α d₀ := by
      rw [lt_div_iff₀ (hα d₀)]
      linarith [hγ d₀, hαβ d₀]
    linarith [hr d₀]
  -- the direction `θ`, the rate `a` and the defect `δ`
  set θ : Fin D → ℝ := fun d => α d + (γ d - β d) / 2 with hθ_def
  have hθ : ∀ d, 0 < θ d := fun d => by
    simp only [hθ_def]
    linarith [hγ d, hαβ d]
  set a : ℝ := 2 / (2 + η) with ha_def
  have ha : 0 < a := div_pos two_pos hη2
  set δ : Fin D → ℝ := fun d => α d - a * θ d with hδ_def
  have hδ_eq : ∀ d, δ d = α d * (η - (γ d - β d) / α d) / (2 + η) := by
    intro d
    have h1 := (hα d).ne'
    have h2 := hη2.ne'
    simp only [hδ_def, hθ_def, ha_def]
    field_simp
    ring
  have hδ : ∀ d, 0 ≤ δ d := fun d => by
    rw [hδ_eq]
    exact div_nonneg (mul_nonneg (hα d).le (by linarith [hr d])) hη2.le
  have hcrit : crit δ = m := by
    rw [← hm_def]
    unfold crit mimcD2
    rw [hη_def]
    congr 1
    apply Finset.filter_congr
    intro d _
    rw [hδ_eq d, div_eq_zero_iff, mul_eq_zero, sub_eq_zero]
    constructor
    · rintro ((h | h) | h)
      · exact absurd h (hα d).ne'
      · exact h.symm
      · exact absurd h hη2.ne'
    · intro h
      exact Or.inl (Or.inr h.symm)
  have hαθ : ∀ d, α d = a * θ d + 1 * δ d := fun d => by
    simp only [hδ_def]
    ring
  set g : Fin D → ℝ := fun d => (γ d - β d) / 2 with hg_def
  have hg : ∀ d, g d = (1 / 2) * γ d + (-1 / 2) * β d := fun d => by
    simp only [hg_def]
    ring
  have hgθ : ∀ d, g d = (1 - a) * θ d + (-1) * δ d := fun d => by
    simp only [hg_def, hδ_def, hθ_def]
    ring
  have hγθ : ∀ d, γ d ≤ c * θ d := fun d => hcγ d
  have hc23 : 0 ≤ 2 * (c₂ * c₃) := mul_nonneg zero_le_two (mul_pos hc₂ hc₃).le
  -- exponent bookkeeping
  have hmR : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm1, Nat.cast_one]
  have hca : c / a = c * (2 + η) / 2 := by
    rw [ha_def, div_div_eq_mul_div]
  have heta : 2 * (1 - a) / a = η := by
    have h2 := hη2.ne'
    rw [ha_def]
    field_simp
    ring
  -- the construction and the overhead constant
  obtain ⟨K_P, K_L, hK_P, hK_L, hcons⟩ :=
    mimc_construction (α := α) (β := β) (γ := γ) (g := g) hθ hδ ha hc₁ hc₂ hc₃ hαθ hg
  rw [hcrit] at hcons
  set K_X : ℝ := c₃ * (∏ d, (1 / θ d + 1)) * (K_P ^ (c / a) *
    K_L ^ ((D : ℝ) + ((m - 1 : ℕ) : ℝ) * (c / a))) with hK_X_def
  have hK_X : 0 ≤ K_X := by
    have hK0 : 0 ≤ ∏ d, (1 / θ d + 1) := Finset.prod_nonneg fun d _ => by
      have := div_nonneg zero_le_one (hθ d).le
      linarith
    exact mul_nonneg (mul_nonneg hc₃.le hK0)
      (mul_nonneg (Real.rpow_nonneg hK_P.le _) (Real.rpow_nonneg hK_L.le _))
  have hX : ∀ ε : ℝ, 0 < ε → ∀ L : ℕ,
      (2 : ℝ) ^ (a * L) ≤ K_P * (1 + (L : ℝ)) ^ (m - 1) / ε →
      1 + (L : ℝ) ≤ K_L * (-Real.log ε) →
      c₃ * ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot γ ℓ ≤
        K_X * (-Real.log ε) ^ ((D : ℝ) + (m - 1) * (c * (2 + η) / 2)) *
          ε ^ (-(c * (2 + η) / 2)) := by
    intro ε hε L hP hL
    have h := mimc_extra_term hθ ha hc hc₃ hK_P hK_L hε hγθ hP hL
    rw [hmR, hca] at h
    rw [hK_X_def, hmR, hca]
    exact h
  -- the three regimes of the main term
  rcases lt_trichotomy η 0 with hneg | hzero | hpos
  · -- `η < 0`: `∑ √(V_ℓ C_ℓ)` is bounded by a product of geometric series
    have hgneg : ∀ d, g d < 0 := fun d => by
      have h1 : (γ d - β d) / α d < 0 := lt_of_le_of_lt (hr d) hneg
      have h2 : γ d - β d < 0 := by
        by_contra h
        push_neg at h
        exact absurd h1 (not_lt.2 (div_nonneg h (hα d).le))
      simp only [hg_def]
      linarith
    set Pg : ℝ := ∏ d, (1 - (2 : ℝ) ^ g d)⁻¹ with hPg
    have hPg0 : 0 ≤ Pg := Finset.prod_nonneg fun d _ => inv_nonneg.2 (by
      have := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (hgneg d)
      linarith)
    refine ⟨2 * (c₂ * c₃) * Pg ^ 2, K_X, mul_nonneg hc23 (sq_nonneg _), hK_X,
      fun ε hε hε1 => ?_⟩
    obtain ⟨L, N, hN, hbias, hvar, hcost, hP, hL⟩ := hcons ε hε hε1
    refine ⟨indexSet θ L, N, hN, hbias, hvar, ?_⟩
    have hS : ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ ≤ Pg := by
      rw [sum_indexSet_eq hθ]
      refine le_trans (Finset.sum_le_sum fun ℓ _ => ?_) (sum_box_two_rpow_le_prod hgneg _)
      split_ifs
      · exact le_rfl
      · exact (Real.rpow_pos_of_pos two_pos _).le
    have hS0 : 0 ≤ ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ :=
      Finset.sum_nonneg fun ℓ _ => (Real.rpow_pos_of_pos two_pos _).le
    rw [mimcBound_of_neg hneg, ← eps_inv_sq_eq hε]
    refine hcost.trans (add_le_add ?_ (hX ε hε L hP hL))
    calc 2 * (c₂ * c₃) * ε⁻¹ ^ 2 * (∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ) ^ 2
        ≤ 2 * (c₂ * c₃) * ε⁻¹ ^ 2 * Pg ^ 2 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hS 2)
            (mul_nonneg hc23 (sq_nonneg _))
      _ = 2 * (c₂ * c₃) * Pg ^ 2 * ε⁻¹ ^ 2 := by ring
  · -- `η = 0`: `∑ √(V_ℓ C_ℓ) ≲ (1+L)^{D₂}`
    have ha1 : a = 1 := by
      rw [ha_def, hzero]
      norm_num
    have hdotg : ∀ ℓ, dot g ℓ = 0 * dot θ ℓ - dot δ ℓ := fun ℓ => by
      rw [dot_linear hgθ ℓ, ha1]
      ring
    obtain ⟨K_I, hK_I, hinner⟩ := inner_bound hθ hδ (le_refl (0 : ℝ))
    rw [hcrit] at hinner
    refine ⟨2 * (c₂ * c₃) * (K_I ^ 2 * K_L ^ (2 * (m : ℝ))), K_X,
      mul_nonneg hc23 (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hK_L.le _)), hK_X,
      fun ε hε hε1 => ?_⟩
    obtain ⟨L, N, hN, hbias, hvar, hcost, hP, hL⟩ := hcons ε hε hε1
    refine ⟨indexSet θ L, N, hN, hbias, hvar, ?_⟩
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
    have hS : ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ ≤ K_I * (1 + (L : ℝ)) ^ m := by
      rw [sum_indexSet_eq hθ]
      calc ∑ ℓ ∈ box D (boxSize θ L), (if dot θ ℓ ≤ L then (2 : ℝ) ^ dot g ℓ else 0)
          = ∑ ℓ ∈ box D (boxSize θ L),
              (if dot θ ℓ ≤ L then (2 : ℝ) ^ (0 * dot θ ℓ - dot δ ℓ) else 0) := by
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            rw [hdotg]
        _ ≤ K_I * (1 + (L : ℝ)) ^ (m - 1) *
              ∑ j ∈ range (⌊(L : ℝ)⌋₊ + 1), (2 : ℝ) ^ ((0 : ℝ) * ((L : ℝ) - j)) :=
            hinner _ L hL0
        _ ≤ K_I * (1 + (L : ℝ)) ^ (m - 1) * (1 + L) :=
            mul_le_mul_of_nonneg_left (sum_two_rpow_zero_le hL0)
              (mul_nonneg hK_I (pow_nonneg (by linarith) _))
        _ = K_I * (1 + (L : ℝ)) ^ m := by
            rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hm1]
    have hS0 : 0 ≤ ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ :=
      Finset.sum_nonneg fun ℓ _ => (Real.rpow_pos_of_pos two_pos _).le
    have hu : (1 + (L : ℝ)) ^ (2 * (m : ℝ)) ≤ K_L ^ (2 * (m : ℝ)) * (-Real.log ε) ^ (2 * (m : ℝ)) := by
      rw [← Real.mul_rpow hK_L.le (by linarith)]
      exact Real.rpow_le_rpow (by linarith) hL (by positivity)
    have hS2 : (∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ) ^ 2 ≤
        K_I ^ 2 * (K_L ^ (2 * (m : ℝ)) * (-Real.log ε) ^ (2 * (m : ℝ))) := by
      calc (∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ) ^ 2 ≤ (K_I * (1 + (L : ℝ)) ^ m) ^ 2 :=
            pow_le_pow_left₀ hS0 hS 2
        _ = K_I ^ 2 * (1 + (L : ℝ)) ^ (2 * (m : ℝ)) := by
            rw [show (2 * (m : ℝ)) = ((m * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
              mul_pow, ← pow_mul]
        _ ≤ K_I ^ 2 * (K_L ^ (2 * (m : ℝ)) * (-Real.log ε) ^ (2 * (m : ℝ))) :=
            mul_le_mul_of_nonneg_left hu (by positivity)
    rw [mimcBound_of_eq hzero, abs_log_eq_neg_log hε hε1, ← eps_inv_sq_eq hε]
    refine hcost.trans (add_le_add ?_ (hX ε hε L hP hL))
    calc 2 * (c₂ * c₃) * ε⁻¹ ^ 2 * (∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ) ^ 2
        ≤ 2 * (c₂ * c₃) * ε⁻¹ ^ 2 *
            (K_I ^ 2 * (K_L ^ (2 * (m : ℝ)) * (-Real.log ε) ^ (2 * (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left hS2 (mul_nonneg hc23 (sq_nonneg _))
      _ = 2 * (c₂ * c₃) * (K_I ^ 2 * K_L ^ (2 * (m : ℝ))) *
            (ε⁻¹ ^ 2 * (-Real.log ε) ^ (2 * (m : ℝ))) := by ring
  · -- `η > 0`: `∑ √(V_ℓ C_ℓ) ≲ (1+L)^{D₂−1} 2^{(1−a)L}`
    have ha1 : a < 1 := by
      rw [ha_def, div_lt_one hη2]
      linarith
    have h1a : 0 < 1 - a := by linarith
    have hdotg : ∀ ℓ, dot g ℓ = (1 - a) * dot θ ℓ - dot δ ℓ := fun ℓ => by
      rw [dot_linear hgθ ℓ]
      ring
    obtain ⟨K_I, hK_I, hinner⟩ := inner_bound hθ hδ h1a.le
    rw [hcrit] at hinner
    set G : ℝ := (1 - (2 : ℝ) ^ (-(1 - a)))⁻¹ with hG
    have hG0 : 0 ≤ G := inv_nonneg.2 (by
      have := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith : -(1 - a) < 0)
      linarith)
    refine ⟨2 * (c₂ * c₃) * ((K_I * G) ^ 2 * (K_P ^ η *
      K_L ^ ((2 * ((m - 1 : ℕ) : ℝ)) + (m - 1 : ℕ) * η))), K_X, ?_, hK_X,
      fun ε hε hε1 => ?_⟩
    · exact mul_nonneg hc23
        (mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hK_P.le _)
          (Real.rpow_nonneg hK_L.le _)))
    obtain ⟨L, N, hN, hbias, hvar, hcost, hP, hL⟩ := hcons ε hε hε1
    refine ⟨indexSet θ L, N, hN, hbias, hvar, ?_⟩
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
    have hS : ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ ≤
        K_I * G * ((1 + (L : ℝ)) ^ (m - 1) * (2 : ℝ) ^ ((1 - a) * L)) := by
      rw [sum_indexSet_eq hθ]
      calc ∑ ℓ ∈ box D (boxSize θ L), (if dot θ ℓ ≤ L then (2 : ℝ) ^ dot g ℓ else 0)
          = ∑ ℓ ∈ box D (boxSize θ L),
              (if dot θ ℓ ≤ L then (2 : ℝ) ^ ((1 - a) * dot θ ℓ - dot δ ℓ) else 0) := by
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            rw [hdotg]
        _ ≤ K_I * (1 + (L : ℝ)) ^ (m - 1) *
              ∑ j ∈ range (⌊(L : ℝ)⌋₊ + 1), (2 : ℝ) ^ ((1 - a) * ((L : ℝ) - j)) :=
            hinner _ L hL0
        _ ≤ K_I * (1 + (L : ℝ)) ^ (m - 1) * ((2 : ℝ) ^ ((1 - a) * L) * G) :=
            mul_le_mul_of_nonneg_left (sum_two_rpow_sub_le h1a _)
              (mul_nonneg hK_I (pow_nonneg (by linarith) _))
        _ = K_I * G * ((1 + (L : ℝ)) ^ (m - 1) * (2 : ℝ) ^ ((1 - a) * L)) := by ring
    have hS0 : 0 ≤ ∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ :=
      Finset.sum_nonneg fun ℓ _ => (Real.rpow_pos_of_pos two_pos _).le
    -- `((1+L)^{m−1} 2^{(1−a)L})² = (1+L)^{2(m−1)} 2^{2(1−a)L}`, then use the level bound
    have hsq : ((1 + (L : ℝ)) ^ (m - 1) * (2 : ℝ) ^ ((1 - a) * L)) ^ 2 =
        (1 + (L : ℝ)) ^ (2 * ((m - 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (2 * (1 - a) * L) := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_natCast (1 + (L : ℝ)) ((m - 1) * 2), sq,
        ← Real.rpow_add two_pos]
      push_cast
      congr 1
      · ring_nf
      · ring_nf
    have hpow := mimc_level_power (q := 2 * ((m - 1 : ℕ) : ℝ)) (b := 2 * (1 - a)) ha
      (by linarith) hK_P hK_L hε (by linarith) (by positivity) hP hL
    rw [heta] at hpow
    have hS2 : (∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ) ^ 2 ≤
        (K_I * G) ^ 2 * (K_P ^ η * K_L ^ (2 * ((m - 1 : ℕ) : ℝ) + (m - 1 : ℕ) * η) *
          (-Real.log ε) ^ (2 * ((m - 1 : ℕ) : ℝ) + (m - 1 : ℕ) * η) * ε ^ (-η)) := by
      calc (∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ) ^ 2
          ≤ (K_I * G * ((1 + (L : ℝ)) ^ (m - 1) * (2 : ℝ) ^ ((1 - a) * L))) ^ 2 :=
            pow_le_pow_left₀ hS0 hS 2
        _ = (K_I * G) ^ 2 * ((1 + (L : ℝ)) ^ (2 * ((m - 1 : ℕ) : ℝ)) *
              (2 : ℝ) ^ (2 * (1 - a) * L)) := by
            rw [mul_pow, hsq]
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
    have hexp : 2 * ((m - 1 : ℕ) : ℝ) + (m - 1 : ℕ) * η = ((m : ℝ) - 1) * (2 + η) := by
      rw [hmR]
      ring
    rw [hexp] at hS2
    rw [mimcBound_of_pos hpos, abs_log_eq_neg_log hε hε1]
    refine hcost.trans (add_le_add ?_ (hX ε hε L hP hL))
    have hε2 : ε⁻¹ ^ 2 * ε ^ (-η) = ε ^ (-2 - η) := by
      rw [eps_inv_sq_eq hε, ← Real.rpow_add hε]
      congr 1
      ring
    rw [hexp]
    calc 2 * (c₂ * c₃) * ε⁻¹ ^ 2 * (∑ ℓ ∈ indexSet θ L, (2 : ℝ) ^ dot g ℓ) ^ 2
        ≤ 2 * (c₂ * c₃) * ε⁻¹ ^ 2 * ((K_I * G) ^ 2 * (K_P ^ η * K_L ^ (((m : ℝ) - 1) * (2 + η)) *
            (-Real.log ε) ^ (((m : ℝ) - 1) * (2 + η)) * ε ^ (-η))) :=
          mul_le_mul_of_nonneg_left hS2 (mul_nonneg hc23 (sq_nonneg _))
      _ = 2 * (c₂ * c₃) * ((K_I * G) ^ 2 * (K_P ^ η * K_L ^ (((m : ℝ) - 1) * (2 + η)))) *
            ((ε⁻¹ ^ 2 * ε ^ (-η)) * (-Real.log ε) ^ (((m : ℝ) - 1) * (2 + η))) := by ring
      _ = _ := by rw [hε2]

/-! ### Theorem 2, deterministic form -/

/-- **Giles' Theorem 2, deterministic form, for `α_d > ½β_d`** (Giles 2015, Theorem 2, with the
paper's exponents `e₁ = 2D₂`, `e₂ = (D₂ − 1)(2 + η)`). -/
theorem mimc_complexity [NeZero D] {α β γ : Fin D → ℝ} {c₁ c₂ c₃ : ℝ}
    (hα : ∀ d, 0 < α d) (hγ : ∀ d, 0 < γ d) (hαβ : ∀ d, β d / 2 < α d)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (𝓛 : Finset (Fin D → ℕ)) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (∀ s : Finset (Fin D → ℕ), c₁ * ∑ ℓ ∈ s \ 𝓛, (2 : ℝ) ^ (-dot α ℓ) ≤ ε / 2) ∧
        ∑ ℓ ∈ 𝓛, c₂ * (2 : ℝ) ^ (-dot β ℓ) / N ℓ ≤ ε ^ 2 / 2 ∧
        ∑ ℓ ∈ 𝓛, (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ dot γ ℓ) ≤
          c₄ * mimcBound (mimcEta α β γ) (2 * mimcD2 α β γ)
            ((mimcD2 α β γ - 1) * (2 + mimcEta α β γ)) ε := by
  -- `c = max_d γ_d/θ_d < 2`
  set θ : Fin D → ℝ := fun d => α d + (γ d - β d) / 2 with hθ_def
  have hθ : ∀ d, 0 < θ d := fun d => by
    simp only [hθ_def]
    linarith [hγ d, hαβ d]
  set c : ℝ := univ.sup' univ_nonempty fun d => γ d / θ d with hc_def
  have hcγ : ∀ d, γ d ≤ c * θ d := fun d => by
    have := Finset.le_sup' (fun d => γ d / θ d) (Finset.mem_univ d)
    rw [div_le_iff₀ (hθ d)] at this
    exact this
  have hc2 : c < 2 := by
    obtain ⟨d, -, hd⟩ := Finset.exists_mem_eq_sup' univ_nonempty fun d => γ d / θ d
    rw [hc_def, hd, div_lt_iff₀ (hθ d)]
    simp only [hθ_def]
    linarith [hαβ d]
  have hc0 : 0 ≤ c := le_trans (div_nonneg (hγ 0).le (hθ 0).le)
    (Finset.le_sup' (fun d => γ d / θ d) (Finset.mem_univ 0))
  obtain ⟨K_M, K_X, hK_M, hK_X, hcore⟩ := mimc_complexity_core hα hγ (fun d => (hαβ d).le)
    hc₁ hc₂ hc₃ hc0 hcγ
  -- the rounding-up overhead is of lower order: `s = c(2+η)/2 < 2 + max η 0`
  have hr := le_mimcEta α β γ
  obtain ⟨d₀, hd₀⟩ := exists_eq_mimcEta α β γ
  have hm1 := one_le_mimcD2 α β γ
  generalize hm_def : mimcD2 α β γ = m at hm1 hcore ⊢
  generalize hη_def : mimcEta α β γ = η at hr hd₀ hcore ⊢
  have hη2 : 0 < 2 + η := by
    have h1 : -2 < (γ d₀ - β d₀) / α d₀ := by
      rw [lt_div_iff₀ (hα d₀)]
      linarith [hγ d₀, hαβ d₀]
    linarith [hr d₀]
  set s : ℝ := c * (2 + η) / 2 with hs_def
  set q : ℝ := 2 + max η 0 with hq_def
  have hsq : s < q := by
    rcases le_or_gt η 0 with h | h
    · rw [hq_def, max_eq_right h, hs_def]
      nlinarith
    · rw [hq_def, max_eq_left h.le, hs_def]
      nlinarith
  have hp : 0 ≤ (D : ℝ) + ((m : ℝ) - 1) * s := by
    have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have h2 : 0 ≤ s := by
      rw [hs_def]
      exact div_nonneg (mul_nonneg hc0 hη2.le) zero_le_two
    exact add_nonneg (Nat.cast_nonneg D) (mul_nonneg (by linarith) h2)
  obtain ⟨K_abs, hK_abs, habs⟩ := neg_log_rpow_mul_rpow_le hp (sub_pos.2 hsq)
  have hKX0 : 0 ≤ K_X * K_abs := mul_nonneg hK_X hK_abs.le
  refine ⟨K_M + K_X * K_abs + 1, by linarith, fun ε hε hε1 => ?_⟩
  obtain ⟨𝓛, N, hN, hbias, hvar, hcost⟩ := hcore ε hε hε1
  refine ⟨𝓛, N, hN, hbias, hvar, hcost.trans ?_⟩
  have hε1' : ε < 1 := eps_lt_one hε1
  have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
  -- `|log ε|^p ε^{−s} ≤ K_abs ε^{−q}`
  have hX : (-Real.log ε) ^ ((D : ℝ) + ((m : ℝ) - 1) * s) * ε ^ (-s) ≤ K_abs * ε ^ (-q) := by
    have h := habs ε hε hε1'
    have e : ε ^ (-s) = ε ^ (q - s) * ε ^ (-q) := by
      rw [← Real.rpow_add hε]
      congr 1
      ring
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h (Real.rpow_pos_of_pos hε _).le
  -- and `ε^{−q} ≤ mimcBound`
  have hB : ε ^ (-q) ≤ mimcBound η (2 * m) ((m - 1) * (2 + η)) ε := by
    have hlog1 : 1 ≤ |Real.log ε| := by rw [abs_log_eq_neg_log hε hε1]; exact ht
    rcases lt_trichotomy η 0 with hneg | hzero | hpos
    · rw [mimcBound_of_neg hneg, hq_def, max_eq_right hneg.le, add_zero]
    · rw [mimcBound_of_eq hzero, hq_def, hzero, max_self, add_zero]
      exact le_mul_of_one_le_right (Real.rpow_pos_of_pos hε _).le
        (Real.one_le_rpow hlog1 (by positivity))
    · rw [mimcBound_of_pos hpos, hq_def, max_eq_left hpos.le, show -(2 + η) = -2 - η by ring]
      exact le_mul_of_one_le_right (Real.rpow_pos_of_pos hε _).le
        (Real.one_le_rpow hlog1 (mul_nonneg (by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          linarith) hη2.le))
  have hB0 := mimcBound_nonneg (η := η) (e₁ := 2 * m) (e₂ := (m - 1) * (2 + η)) hε
  calc K_M * mimcBound η (2 * m) ((m - 1) * (2 + η)) ε +
        K_X * (-Real.log ε) ^ ((D : ℝ) + ((m : ℝ) - 1) * s) * ε ^ (-s)
      ≤ K_M * mimcBound η (2 * m) ((m - 1) * (2 + η)) ε +
        K_X * (K_abs * mimcBound η (2 * m) ((m - 1) * (2 + η)) ε) := by
        rw [mul_assoc K_X]
        exact add_le_add_left (mul_le_mul_of_nonneg_left (hX.trans
          (mul_le_mul_of_nonneg_left hB hK_abs.le)) hK_X) _
    _ ≤ (K_M + K_X * K_abs + 1) * mimcBound η (2 * m) ((m - 1) * (2 + η)) ε := by
        nlinarith [hB0]

/-- **Giles' Theorem 2, deterministic form, for `α_d ≥ ½β_d`** (Giles 2015, Theorem 2).  The paper
does not specify the log exponents when some `α_d = ½β_d`; here `e₁ = 2D₂ + D` and
`e₂ = (D₂ − 1)(2 + η) + D`. -/
theorem mimc_complexity_boundary [NeZero D] {α β γ : Fin D → ℝ} {c₁ c₂ c₃ : ℝ}
    (hα : ∀ d, 0 < α d) (hγ : ∀ d, 0 < γ d) (hαβ : ∀ d, β d / 2 ≤ α d)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (𝓛 : Finset (Fin D → ℕ)) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (∀ s : Finset (Fin D → ℕ), c₁ * ∑ ℓ ∈ s \ 𝓛, (2 : ℝ) ^ (-dot α ℓ) ≤ ε / 2) ∧
        ∑ ℓ ∈ 𝓛, c₂ * (2 : ℝ) ^ (-dot β ℓ) / N ℓ ≤ ε ^ 2 / 2 ∧
        ∑ ℓ ∈ 𝓛, (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ dot γ ℓ) ≤
          c₄ * mimcBound (mimcEta α β γ) (2 * mimcD2 α β γ + D)
            ((mimcD2 α β γ - 1) * (2 + mimcEta α β γ) + D) ε := by
  -- with `c = 2`: `γ_d ≤ 2θ_d` is `β_d ≤ 2α_d`
  have hcγ : ∀ d, γ d ≤ 2 * (α d + (γ d - β d) / 2) := fun d => by linarith [hαβ d]
  obtain ⟨K_M, K_X, hK_M, hK_X, hcore⟩ := mimc_complexity_core hα hγ hαβ hc₁ hc₂ hc₃
    zero_le_two hcγ
  have hr := le_mimcEta α β γ
  obtain ⟨d₀, hd₀⟩ := exists_eq_mimcEta α β γ
  have hm1 := one_le_mimcD2 α β γ
  generalize hm_def : mimcD2 α β γ = m at hm1 hcore ⊢
  generalize hη_def : mimcEta α β γ = η at hr hd₀ hcore ⊢
  have hη2 : 0 < 2 + η := by
    have h1 : -2 < (γ d₀ - β d₀) / α d₀ := by
      rw [lt_div_iff₀ (hα d₀)]
      linarith [hγ d₀, hαβ d₀]
    linarith [hr d₀]
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hs : (2 : ℝ) * (2 + η) / 2 = 2 + η := by ring
  simp only [hs] at hcore
  -- for `η < 0` the overhead `|log ε|^p ε^{−(2+η)}` is `O(ε⁻²)`
  have hp : 0 ≤ (D : ℝ) + ((m : ℝ) - 1) * (2 + η) :=
    add_nonneg (Nat.cast_nonneg D) (mul_nonneg (sub_nonneg.2 hm1') hη2.le)
  obtain ⟨K_abs, hK_abs, habs⟩ := neg_log_rpow_mul_rpow_le (κ := if η < 0 then -η else 1) hp
    (by split_ifs with h <;> linarith)
  have hKX0 : 0 ≤ K_X * K_abs := mul_nonneg hK_X hK_abs.le
  refine ⟨K_M + K_X * K_abs + K_X + 1, by linarith, fun ε hε hε1 => ?_⟩
  obtain ⟨𝓛, N, hN, hbias, hvar, hcost⟩ := hcore ε hε hε1
  refine ⟨𝓛, N, hN, hbias, hvar, hcost.trans ?_⟩
  have hε1' : ε < 1 := eps_lt_one hε1
  have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
  have hlog : |Real.log ε| = -Real.log ε := abs_log_eq_neg_log hε hε1
  have hBmono := mimcBound_mono (η := η) hε hε1 (le_add_of_nonneg_right (Nat.cast_nonneg D))
    (le_add_of_nonneg_right (Nat.cast_nonneg D)) (e₁ := 2 * m) (e₂ := (m - 1) * (2 + η))
  set B := mimcBound η (2 * m + D) ((m - 1) * (2 + η) + D) ε with hB_def
  have hB0 : 0 ≤ B := mimcBound_nonneg hε
  -- the overhead is at most `(K_abs + 1) B`
  have hX : (-Real.log ε) ^ ((D : ℝ) + ((m : ℝ) - 1) * (2 + η)) * ε ^ (-(2 + η)) ≤
      (K_abs + 1) * B := by
    rcases lt_trichotomy η 0 with hneg | hzero | hpos
    · have h := habs ε hε hε1'
      rw [if_pos hneg] at h
      have e : ε ^ (-(2 + η)) = ε ^ (-η) * ε ^ (-2 : ℝ) := by
        rw [← Real.rpow_add hε]
        congr 1
        ring
      rw [hB_def, mimcBound_of_neg hneg, e, ← mul_assoc]
      calc (-Real.log ε) ^ ((D : ℝ) + ((m : ℝ) - 1) * (2 + η)) * ε ^ (-η) * ε ^ (-2 : ℝ)
          ≤ K_abs * ε ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right h (Real.rpow_pos_of_pos hε _).le
        _ ≤ (K_abs + 1) * ε ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_pos_of_pos hε _).le
    · rw [hB_def, mimcBound_of_eq hzero, hlog, hzero]
      have h1 : (-Real.log ε) ^ ((D : ℝ) + ((m : ℝ) - 1) * (2 + 0)) ≤
          (-Real.log ε) ^ (2 * (m : ℝ) + D) :=
        Real.rpow_le_rpow_of_exponent_le ht (by linarith)
      have e : ε ^ (-(2 + (0 : ℝ))) = ε ^ (-2 : ℝ) := by norm_num
      rw [e]
      calc (-Real.log ε) ^ ((D : ℝ) + ((m : ℝ) - 1) * (2 + 0)) * ε ^ (-2 : ℝ)
          ≤ (-Real.log ε) ^ (2 * (m : ℝ) + D) * ε ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos hε _).le
        _ = 1 * (ε ^ (-2 : ℝ) * (-Real.log ε) ^ (2 * (m : ℝ) + D)) := by ring
        _ ≤ (K_abs + 1) * (ε ^ (-2 : ℝ) * (-Real.log ε) ^ (2 * (m : ℝ) + D)) :=
            mul_le_mul_of_nonneg_right (by linarith)
              (mul_nonneg (Real.rpow_pos_of_pos hε _).le (Real.rpow_nonneg (by linarith) _))
    · rw [hB_def, mimcBound_of_pos hpos, hlog]
      have e : ε ^ (-(2 + η)) = ε ^ (-2 - η) := by
        congr 1
        ring
      rw [e]
      calc (-Real.log ε) ^ ((D : ℝ) + ((m : ℝ) - 1) * (2 + η)) * ε ^ (-2 - η)
          = 1 * (ε ^ (-2 - η) * (-Real.log ε) ^ (((m : ℝ) - 1) * (2 + η) + D)) := by
            rw [add_comm (D : ℝ)]
            ring
        _ ≤ (K_abs + 1) * (ε ^ (-2 - η) * (-Real.log ε) ^ (((m : ℝ) - 1) * (2 + η) + D)) :=
            mul_le_mul_of_nonneg_right (by linarith)
              (mul_nonneg (Real.rpow_pos_of_pos hε _).le (Real.rpow_nonneg (by linarith) _))
  calc K_M * mimcBound η (2 * m) ((m - 1) * (2 + η)) ε +
        K_X * (-Real.log ε) ^ ((D : ℝ) + ((m : ℝ) - 1) * (2 + η)) * ε ^ (-(2 + η))
      ≤ K_M * B + K_X * ((K_abs + 1) * B) := by
        rw [mul_assoc K_X]
        exact add_le_add (mul_le_mul_of_nonneg_left hBmono hK_M)
          (mul_le_mul_of_nonneg_left hX hK_X)
    _ ≤ (K_M + K_X * K_abs + K_X + 1) * B := by nlinarith [hB0]

/-! ### Theorem 2 on a probability space -/

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Linearity of expectation for cross-differences: `E[ΔP_ℓ] = Δ(E[P_·])_ℓ`. -/
theorem integrable_integral_crossDiff : ∀ {D : ℕ} (P : (Fin D → ℕ) → Ω → ℝ),
    (∀ ℓ, Integrable (P ℓ) μ) → ∀ ℓ : Fin D → ℕ,
      Integrable (fun ω => crossDiff (fun m => P m ω) ℓ) μ ∧
        μ[fun ω => crossDiff (fun m => P m ω) ℓ] = crossDiff (fun m => μ[P m]) ℓ
  | 0, P, hP, ℓ => ⟨hP ℓ, rfl⟩
  | D + 1, P, hP, ℓ => by
    have h1 : Integrable (fun ω => crossDiff (fun m => P (Fin.cons (ℓ 0) m) ω) (Fin.tail ℓ)) μ ∧
        μ[fun ω => crossDiff (fun m => P (Fin.cons (ℓ 0) m) ω) (Fin.tail ℓ)] =
          crossDiff (fun m => μ[P (Fin.cons (ℓ 0) m)]) (Fin.tail ℓ) :=
      integrable_integral_crossDiff (fun m => P (Fin.cons (ℓ 0) m)) (fun m => hP _) (Fin.tail ℓ)
    have h2 : Integrable
          (fun ω => crossDiff (fun m => P (Fin.cons (ℓ 0 - 1) m) ω) (Fin.tail ℓ)) μ ∧
        μ[fun ω => crossDiff (fun m => P (Fin.cons (ℓ 0 - 1) m) ω) (Fin.tail ℓ)] =
          crossDiff (fun m => μ[P (Fin.cons (ℓ 0 - 1) m)]) (Fin.tail ℓ) :=
      integrable_integral_crossDiff (fun m => P (Fin.cons (ℓ 0 - 1) m)) (fun m => hP _)
        (Fin.tail ℓ)
    by_cases h0 : ℓ 0 = 0
    · have e : ∀ q : (Fin (D + 1) → ℕ) → ℝ,
          crossDiff q ℓ = crossDiff (fun m => q (Fin.cons (ℓ 0) m)) (Fin.tail ℓ) := by
        intro q
        rw [crossDiff_succ, if_pos h0, sub_zero]
      simp only [e]
      exact h1
    · have e : ∀ q : (Fin (D + 1) → ℕ) → ℝ,
          crossDiff q ℓ = crossDiff (fun m => q (Fin.cons (ℓ 0) m)) (Fin.tail ℓ) -
            crossDiff (fun m => q (Fin.cons (ℓ 0 - 1) m)) (Fin.tail ℓ) := by
        intro q
        rw [crossDiff_succ, if_neg h0]
      simp only [e]
      refine ⟨h1.1.sub h2.1, ?_⟩
      rw [integral_sub h1.1 h2.1, h1.2, h2.2]

variable [IsProbabilityMeasure μ]

/-- From the deterministic form to the probability space (proof of Giles 2015, Theorem 2):
condition i) and the box telescoping `sum_crossDiff` identify the bias with the tail
`∑_{ℓ ∉ 𝓛} E[ΔP_ℓ]`, and `MSE = V[Y] + bias²` with `V[Y] = ∑ V_ℓ/N_ℓ`. -/
theorem mimc_mse_cost [NeZero D] (P : Ω → ℝ) (Pℓ : (Fin D → ℕ) → Ω → ℝ)
    (Y : (Fin D → ℕ) → ℕ → Ω → ℝ) (Cost : (Fin D → ℕ) → ℕ → Ω → ℝ) (V C : (Fin D → ℕ) → ℝ)
    {α β γ : Fin D → ℝ} {c₁ c₂ c₃ : ℝ} (B : ℝ → ℝ)
    (hdet : ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (𝓛 : Finset (Fin D → ℕ)) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (∀ s : Finset (Fin D → ℕ), c₁ * ∑ ℓ ∈ s \ 𝓛, (2 : ℝ) ^ (-dot α ℓ) ≤ ε / 2) ∧
        ∑ ℓ ∈ 𝓛, c₂ * (2 : ℝ) ^ (-dot β ℓ) / N ℓ ≤ ε ^ 2 / 2 ∧
        ∑ ℓ ∈ 𝓛, (N ℓ : ℝ) * (c₃ * (2 : ℝ) ^ dot γ ℓ) ≤ c₄ * B ε)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : (Fin D → ℕ) → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (h_cost : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_i : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ ℓ : Fin D → ℕ, (∀ d, n₀ ≤ ℓ d) →
      |μ[fun ω => Pℓ ℓ ω - P ω]| < δ)
    (h_iii : ∀ ℓ n, 0 < n → μ[Y ℓ n] = μ[fun ω => crossDiff (fun m => Pℓ m ω) ℓ])
    (h_ii : ∀ ℓ n, 0 < n → |μ[Y ℓ n]| ≤ c₁ * (2 : ℝ) ^ (-dot α ℓ))
    (h_iv : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-dot β ℓ))
    (h_v : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ dot γ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (𝓛 : Finset (Fin D → ℕ)) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ 𝓛, Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ 𝓛, Cost ℓ (N ℓ) ω] ≤ c₄ * B ε := by
  obtain ⟨c₄, hc₄, hdet⟩ := hdet
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨𝓛, N, hN, hbias, hvar, hcost⟩ := hdet ε hε hε1
  refine ⟨𝓛, N, hN, ?_, ?_⟩
  · -- the mean-square error
    set p : (Fin D → ℕ) → ℝ := fun m => μ[Pℓ m] with hp
    have hEΔ : ∀ ℓ, μ[fun ω => crossDiff (fun m => Pℓ m ω) ℓ] = crossDiff p ℓ := fun ℓ =>
      (integrable_integral_crossDiff Pℓ hPℓ ℓ).2
    have hΔbound : ∀ ℓ, |crossDiff p ℓ| ≤ c₁ * (2 : ℝ) ^ (-dot α ℓ) := fun ℓ => by
      rw [← hEΔ, ← h_iii ℓ 1 one_pos]
      exact h_ii ℓ 1 one_pos
    have hmean : μ[fun ω => ∑ ℓ ∈ 𝓛, Y ℓ (N ℓ) ω] = ∑ ℓ ∈ 𝓛, crossDiff p ℓ := by
      rw [integral_finsetSum _ fun ℓ _ => (hY ℓ (N ℓ)).integrable one_le_two]
      exact Finset.sum_congr rfl fun ℓ _ => by rw [h_iii ℓ (N ℓ) (hN ℓ), hEΔ]
    -- the bias: `|∑_{𝓛} ΔE[P] − E[P]| ≤ ε/2`, from condition i) and box telescoping
    have hbias' : |∑ ℓ ∈ 𝓛, crossDiff p ℓ - μ[P]| ≤ ε / 2 := by
      refine le_of_forall_pos_le_add fun η hη => ?_
      obtain ⟨n₀, hn₀⟩ := h_i η hη
      obtain ⟨n₁, hn₁⟩ := exists_subset_box 𝓛
      set n := max n₀ n₁ with hn
      have hsub : 𝓛 ⊆ box D (n + 1) := hn₁.trans (box_mono (by omega))
      have htel : ∑ ℓ ∈ box D (n + 1), crossDiff p ℓ = p fun _ => n :=
        sum_crossDiff p fun _ => n
      have hsplit : ∑ ℓ ∈ box D (n + 1), crossDiff p ℓ =
          ∑ ℓ ∈ box D (n + 1) \ 𝓛, crossDiff p ℓ + ∑ ℓ ∈ 𝓛, crossDiff p ℓ :=
        (Finset.sum_sdiff hsub).symm
      have htail : |∑ ℓ ∈ box D (n + 1) \ 𝓛, crossDiff p ℓ| ≤ ε / 2 :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          ((Finset.sum_le_sum fun ℓ _ => hΔbound ℓ).trans (by
            rw [← Finset.mul_sum]
            exact hbias _))
      have hlim : |p (fun _ => n) - μ[P]| < η := by
        have h := hn₀ (fun _ => n) fun d => le_max_left n₀ n₁
        rwa [integral_sub (hPℓ _) hP] at h
      have hsum_eq : ∑ ℓ ∈ 𝓛, crossDiff p ℓ =
          p (fun _ => n) - ∑ ℓ ∈ box D (n + 1) \ 𝓛, crossDiff p ℓ := by
        rw [← htel, hsplit]
        ring
      have h1 := abs_lt.1 hlim
      have h2 := abs_le.1 htail
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hsum_eq]
    -- the variance
    have hind' : Set.Pairwise ↑𝓛 fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ :=
      fun i _ j _ hij => hind N hN hij
    have hsum : MemLp (∑ ℓ ∈ 𝓛, Y ℓ (N ℓ)) 2 μ := memLp_finsetSum' _ fun ℓ _ => hY ℓ (N ℓ)
    have hmse := mse_eq_variance_add_sq_bias hsum (μ[P])
    rw [IndepFun.variance_sum (fun ℓ _ => hY ℓ (N ℓ)) hind'] at hmse
    have hfun : (fun ω => (∑ ℓ ∈ 𝓛, Y ℓ (N ℓ) ω - μ[P]) ^ 2) =
        fun ω => ((∑ ℓ ∈ 𝓛, Y ℓ (N ℓ)) ω - μ[P]) ^ 2 := by
      ext ω
      simp [Finset.sum_apply]
    have hmean' : μ[∑ ℓ ∈ 𝓛, Y ℓ (N ℓ)] = ∑ ℓ ∈ 𝓛, crossDiff p ℓ := by
      rw [← hmean]
      congr 1
      ext ω
      simp [Finset.sum_apply]
    rw [hfun, hmse, hmean']
    have hv : ∑ ℓ ∈ 𝓛, variance (Y ℓ (N ℓ)) μ ≤ ∑ ℓ ∈ 𝓛, c₂ * (2 : ℝ) ^ (-dot β ℓ) / N ℓ := by
      apply Finset.sum_le_sum
      intro ℓ _
      rw [h_var ℓ (N ℓ) (hN ℓ)]
      exact div_le_div_of_nonneg_right (h_iv ℓ) (Nat.cast_nonneg _)
    have hb2 : (∑ ℓ ∈ 𝓛, crossDiff p ℓ - μ[P]) ^ 2 ≤ (ε / 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hbias' 2
    have h4 := pow_pos hε 2
    linarith
  · -- the expected cost
    have hE : μ[fun ω => ∑ ℓ ∈ 𝓛, Cost ℓ (N ℓ) ω] = ∑ ℓ ∈ 𝓛, (N ℓ : ℝ) * C ℓ := by
      rw [integral_finsetSum _ fun ℓ _ => hCost ℓ (N ℓ) (hN ℓ)]
      exact Finset.sum_congr rfl fun ℓ _ => h_cost ℓ (N ℓ) (hN ℓ)
    rw [hE]
    refine le_trans (Finset.sum_le_sum fun ℓ _ => ?_) hcost
    exact mul_le_mul_of_nonneg_left (h_v ℓ) (Nat.cast_nonneg _)

-- `hβ : ∀ d, 0 < β d` is one of Giles' hypotheses; the proof only uses `α_d > ½β_d`.
set_option linter.unusedVariables false in
/-- **Giles' Theorem 2** (Giles 2015, §2.4, Theorem 2; Haji-Ali, Nobile & Tempone 2014a), for
`α_d > ½β_d`.  Let `P` be a random variable, `Pℓ ℓ` its approximation at the multi-index
`ℓ ∈ ℕ^D`, and `ΔP_ℓ = crossDiff (P_·) ℓ` the cross-difference.  Suppose there are estimators
`Y ℓ n` based on `n` Monte Carlo samples, independent across levels, whose samples at level `ℓ`
have variance `V ℓ` and expected cost `C ℓ`, and positive vectors `α, β, γ` with `α_d > ½β_d`
and constants `c₁, c₂, c₃ > 0` with

  i)   `|E[P_ℓ − P]| → 0` as `min_d ℓ_d → ∞`,
  iii) `E[Y_ℓ] = E[ΔP_ℓ]`,
  ii)  `|E[Y_ℓ]| ≤ c₁ 2^{−α·ℓ}`,
  iv)  `V_ℓ ≤ c₂ 2^{−β·ℓ}`,
  v)   `C_ℓ ≤ c₃ 2^{γ·ℓ}`.

Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are a finite set of levels `𝓛` and
`N_ℓ ≥ 1` for which `Y = ∑_{ℓ∈𝓛} Y ℓ (N ℓ)` has `MSE < ε²` and the expected cost satisfies
`E[C] ≤ c₄ ε⁻²` (`η < 0`), `c₄ ε⁻² |log ε|^{2D₂}` (`η = 0`),
`c₄ ε^{−2−η} |log ε|^{(D₂−1)(2+η)}` (`η > 0`), where `η = max_d (γ_d − β_d)/α_d` and `D₂` is the
number of directions attaining it. -/
theorem giles_theorem2 [NeZero D] (P : Ω → ℝ) (Pℓ : (Fin D → ℕ) → Ω → ℝ)
    (Y : (Fin D → ℕ) → ℕ → Ω → ℝ) (Cost : (Fin D → ℕ) → ℕ → Ω → ℝ) (V C : (Fin D → ℕ) → ℝ)
    {α β γ : Fin D → ℝ} {c₁ c₂ c₃ : ℝ}
    (hα : ∀ d, 0 < α d) (hβ : ∀ d, 0 < β d) (hγ : ∀ d, 0 < γ d) (hαβ : ∀ d, β d / 2 < α d)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : (Fin D → ℕ) → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (h_cost : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_i : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ ℓ : Fin D → ℕ, (∀ d, n₀ ≤ ℓ d) →
      |μ[fun ω => Pℓ ℓ ω - P ω]| < δ)
    (h_iii : ∀ ℓ n, 0 < n → μ[Y ℓ n] = μ[fun ω => crossDiff (fun m => Pℓ m ω) ℓ])
    (h_ii : ∀ ℓ n, 0 < n → |μ[Y ℓ n]| ≤ c₁ * (2 : ℝ) ^ (-dot α ℓ))
    (h_iv : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-dot β ℓ))
    (h_v : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ dot γ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (𝓛 : Finset (Fin D → ℕ)) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ 𝓛, Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ 𝓛, Cost ℓ (N ℓ) ω] ≤
          c₄ * mimcBound (mimcEta α β γ) (2 * mimcD2 α β γ)
            ((mimcD2 α β γ - 1) * (2 + mimcEta α β γ)) ε :=
  mimc_mse_cost P Pℓ Y Cost V C _ (mimc_complexity hα hγ hαβ hc₁ hc₂ hc₃) hP hPℓ hY hind
    hCost h_cost h_var h_i h_iii h_ii h_iv h_v

-- `hβ : ∀ d, 0 < β d` is one of Giles' hypotheses; the proof only uses `α_d ≥ ½β_d`.
set_option linter.unusedVariables false in
/-- **Giles' Theorem 2 when some `α_d = ½β_d`** (Giles 2015, §2.4, Theorem 2, for `α_d ≥ ½β_d`).
Hypotheses as in `giles_theorem2` but with `α_d ≥ ½β_d`.  The paper notes that "the form of the
exponents is more complicated" in this case and does not state them; we prove the bound with
`e₁ = 2D₂ + D` and `e₂ = (D₂ − 1)(2 + η) + D`. -/
theorem giles_theorem2_boundary [NeZero D] (P : Ω → ℝ) (Pℓ : (Fin D → ℕ) → Ω → ℝ)
    (Y : (Fin D → ℕ) → ℕ → Ω → ℝ) (Cost : (Fin D → ℕ) → ℕ → Ω → ℝ) (V C : (Fin D → ℕ) → ℝ)
    {α β γ : Fin D → ℝ} {c₁ c₂ c₃ : ℝ}
    (hα : ∀ d, 0 < α d) (hβ : ∀ d, 0 < β d) (hγ : ∀ d, 0 < γ d) (hαβ : ∀ d, β d / 2 ≤ α d)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : (Fin D → ℕ) → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (h_cost : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_i : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ ℓ : Fin D → ℕ, (∀ d, n₀ ≤ ℓ d) →
      |μ[fun ω => Pℓ ℓ ω - P ω]| < δ)
    (h_iii : ∀ ℓ n, 0 < n → μ[Y ℓ n] = μ[fun ω => crossDiff (fun m => Pℓ m ω) ℓ])
    (h_ii : ∀ ℓ n, 0 < n → |μ[Y ℓ n]| ≤ c₁ * (2 : ℝ) ^ (-dot α ℓ))
    (h_iv : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-dot β ℓ))
    (h_v : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ dot γ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (𝓛 : Finset (Fin D → ℕ)) (N : (Fin D → ℕ) → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ 𝓛, Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ 𝓛, Cost ℓ (N ℓ) ω] ≤
          c₄ * mimcBound (mimcEta α β γ) (2 * mimcD2 α β γ + D)
            ((mimcD2 α β γ - 1) * (2 + mimcEta α β γ) + D) ε :=
  mimc_mse_cost P Pℓ Y Cost V C _ (mimc_complexity_boundary hα hγ hαβ hc₁ hc₂ hc₃) hP hPℓ hY
    hind hCost h_cost h_var h_i h_iii h_ii h_iv h_v

end Probability

end MLMC
