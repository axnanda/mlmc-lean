import MlmcLean.ControlVariate
import MlmcLean.Randomised

/-!
# Cost comparisons (Giles 2015, §1.3, §2.1–§2.2; Haas–Giles 2025, §2.1)

References: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §1.3 (p. 4),
§2.1 (pp. 7–8) and §2.2 (pp. 10–11) of the author's version; I.-B. Haas and M.B. Giles, *A nested
MLMC framework for efficient simulations on FPGAs*, arXiv:2502.07123 (2025), §2.1 (p. 3).

* **Standard Monte Carlo** (Giles §1.3: "the standard MC cost of approximately `ε⁻² V₀ C_L`";
  Haas–Giles p. 3: "the overall cost would be `ε⁻² V C`").  The mean of `N` samples has r.m.s.
  error at most `ε` iff `N ≥ ε⁻² V[P]` (`mc_estimate`), so it costs at least `ε⁻² V[P] C`
  (`mc_cost_lower`), and the least such `N` costs at most one sample more (`mc_cost`).  Under the
  bias condition i) and `C_L ≤ c₃ 2^{γL}` the complexity is `O(ε^{−2−γ/α})` (`mc_complexity`).
* **The MLMC saving** (Giles §1.3: "in the first case the MLMC cost is reduced by factor
  `V_L/V₀` … in the second case it is reduced by factor `C₀/C_L`"): up to constant factors the
  cost (1.1) is `V_L/V[P_L]` times, or `(V₀/V[P_L])(C₀/C_L)` times, the standard cost
  `ε⁻² V[P_L] C_L` (`mlmc_vs_mc_increasing`, `mlmc_vs_mc_decreasing`).
* **The remarks after Theorem 1** (Giles §2.1, p. 7): for `β > γ` the coarsest level needs
  `Θ(ε⁻²)` samples and carries a fixed fraction of the cost (`coarsest_level_dominant`); for
  `β < γ`, `C_L = O(ε^{−γ/α})` at the finest level of the proof (`finest_cost_le`); for `β = γ` the
  cost and the variance are spread evenly over the levels (`equal_cost_per_level`).
* **The split of the MSE** (Giles §2.1, p. 8: "the equal split … is definitely not optimal …
  This can give up to a factor 2× improvement"): with the variance budget `(1 − θ)ε²` the cost is
  `(1 − θ)⁻¹ ε⁻² S_L²`, `S_L = ∑_{ℓ≤L} √(V_ℓ C_ℓ)` (`split_cost`); the equal split costs at most
  `2(1 − θ)` times a split that uses at least as many levels (`equal_split_cost_le`); and when
  `∑ √(V_ℓ C_ℓ)` converges (`β > γ`: `summable_sqrt_Vb_mul_Cb`) the equal-split cost tends to
  twice the limit `ε⁻² S_∞²` of the splits with `θ → 0`, `L → ∞` (`tendsto_equal_split_cost`,
  `tendsto_split_cost`).
* **The randomised estimator costs half** (Giles §2.2, p. 11: "which is the same as the total cost
  in Eq. (1.1), and half the cost of the standard MLMC algorithm in which only half of the MSE
  “budget” of `ε²` is allocated to the variance"): `randomised_half_cost`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

/-! ### Standard Monte Carlo -/

/-- **The cost of standard Monte Carlo** (Giles 2015, §1.3, p. 4: "the standard MC cost of
approximately `ε⁻² V₀ C_L`"; Haas–Giles 2025, §2.1, p. 3: "the overall cost would be `ε⁻² V C`").
For `V ≥ 0`, `C ≥ 0` and `ε > 0`: every `N ≥ 1` with `V/N ≤ ε²` costs `N C ≥ ε⁻² V C`; and
`N* = max(1, ⌈ε⁻² V⌉)` has `V/N* ≤ ε²` and costs `N* C ≤ ε⁻² V C + C`. -/
theorem mc_cost {V C ε : ℝ} (hV : 0 ≤ V) (hC : 0 ≤ C) (hε : 0 < ε) :
    (∀ N : ℕ, 0 < N → V / N ≤ ε ^ 2 → ε⁻¹ ^ 2 * V * C ≤ N * C) ∧
      0 < max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ ∧ V / (max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ : ℕ) ≤ ε ^ 2 ∧
      ((max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ : ℕ) : ℝ) * C ≤ ε⁻¹ ^ 2 * V * C + C := by
  have hε2 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hε.ne', one_pow]
  have hx : 0 ≤ ε⁻¹ ^ 2 * V := mul_nonneg (by positivity) hV
  refine ⟨fun N hN h => ?_, lt_of_lt_of_le Nat.one_pos (le_max_left _ _), ?_, ?_⟩
  · have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
    rw [div_le_iff₀ hN'] at h
    have h1 : ε⁻¹ ^ 2 * V ≤ N :=
      calc ε⁻¹ ^ 2 * V ≤ ε⁻¹ ^ 2 * (ε ^ 2 * N) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = N := by rw [← mul_assoc, mul_comm (ε⁻¹ ^ 2), hε2, one_mul]
    exact mul_le_mul_of_nonneg_right h1 hC
  · have hN1 : (1 : ℝ) ≤ ((max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ : ℕ) : ℝ) := by
      have h : 1 ≤ max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ := le_max_left _ _
      exact_mod_cast h
    have hNc : ε⁻¹ ^ 2 * V ≤ ((max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ : ℕ) : ℝ) := by
      have h : ⌈ε⁻¹ ^ 2 * V⌉₊ ≤ max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ := le_max_right _ _
      exact (Nat.le_ceil _).trans (by exact_mod_cast h)
    rw [div_le_iff₀ (by linarith)]
    calc V = ε ^ 2 * ε⁻¹ ^ 2 * V := by rw [hε2, one_mul]
      _ = ε ^ 2 * (ε⁻¹ ^ 2 * V) := mul_assoc _ _ _
      _ ≤ ε ^ 2 * ((max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hNc (by positivity)
  · have hN : ((max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ : ℕ) : ℝ) ≤ ε⁻¹ ^ 2 * V + 1 := by
      rw [Nat.cast_max, Nat.cast_one]
      exact max_le (by linarith) (Nat.ceil_lt_add_one hx).le
    calc ((max 1 ⌈ε⁻¹ ^ 2 * V⌉₊ : ℕ) : ℝ) * C ≤ (ε⁻¹ ^ 2 * V + 1) * C :=
          mul_le_mul_of_nonneg_right hN hC
      _ = ε⁻¹ ^ 2 * V * C + C := by ring

section Probability

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω}

/-- **Standard Monte Carlo costs at least `ε⁻² V[P] C`** (Giles 2015, §1.3, p. 4, the standard MC
cost `ε⁻² V₀ C_L`; Haas–Giles 2025, §2.1, p. 3).  With `N ≥ 1` independent inputs of law `ν` and a
square-integrable `P`, if the mean `N⁻¹ ∑_{n<N} P(ω⁽ⁿ⁾)` has r.m.s. error at most `ε > 0`, then
its cost `N C` (`C ≥ 0` per sample) is at least `ε⁻² V[P] C`. -/
theorem mc_cost_lower [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {P : Ω₀ → ℝ}
    (hPm : Measurable P) (hP : MemLp P 2 ν) {N : ℕ} (hN : 0 < N) {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C)
    (hrms : Real.sqrt (μ[fun x => ((N : ℝ)⁻¹ * ∑ n ∈ range N, P (ω n x) - ∫ y, P y ∂ν) ^ 2])
      ≤ ε) :
    ε⁻¹ ^ 2 * variance P ν * C ≤ N * C := by
  have h := ((mc_estimate ω hω hind hPm hP hN).2.2.2 ε hε).1 hrms
  have e : variance P ν / ε ^ 2 = ε⁻¹ ^ 2 * variance P ν := by rw [div_eq_inv_mul, inv_pow]
  rw [e] at h
  exact mul_le_mul_of_nonneg_right h hC

end Probability

/-- **The complexity of standard Monte Carlo** (Giles 2015, §1.3, p. 4, the standard MC cost
`ε⁻² V₀ C_L`; §2.1, p. 7: "Because of condition i), we have `2^{−αL} = O(ε)`, and hence
`C_L = O(ε^{−γ/α})`").  The plain Monte Carlo mean of `N` samples of `P_L` has
`MSE = V[P_L]/N + (E[P_L − P])²`.  If `|E[P_L − P]| ≤ c₁ 2^{−αL}`, `V[P_L] ≤ V̄` and
`C_L ≤ c₃ 2^{γL}` (`α, γ, c₁, c₃ > 0`, `V̄ ≥ 0`), there is `c₄ > 0` such that for every
`0 < ε < 1` there are `L` and `N ≥ 1` with `(c₁ 2^{−αL})² + V̄/N ≤ ε²` and
`N c₃ 2^{γL} ≤ c₄ ε^{−2−γ/α}`. -/
theorem mc_complexity {α γ c₁ c₃ Vbar : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hc₁ : 0 < c₁)
    (hc₃ : 0 < c₃) (hV : 0 ≤ Vbar) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ L N : ℕ, 0 < N ∧
      (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 + Vbar / N ≤ ε ^ 2 ∧
      (N : ℝ) * (c₃ * (2 : ℝ) ^ (γ * (L : ℝ))) ≤ c₄ * ε ^ (-2 - γ / α) := by
  set K : ℝ := (2 : ℝ) ^ α * (1 + Real.sqrt 2 * c₁) with hK_def
  have hK : 0 < K := by rw [hK_def]; positivity
  refine ⟨(2 * Vbar + 1) * c₃ * K ^ (γ / α), by positivity, fun ε hε hε1 => ?_⟩
  have hδ : 0 < ε / Real.sqrt 2 := div_pos hε (Real.sqrt_pos.2 two_pos)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsc : 0 ≤ Real.sqrt 2 * c₁ := mul_nonneg (Real.sqrt_nonneg 2) hc₁.le
  -- the finest level: the least `L` with `c₁ 2^{−αL} ≤ ε/√2`
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = levelL α c₁ (ε / Real.sqrt 2) := ⟨_, rfl⟩
  have hb : c₁ * (2 : ℝ) ^ (-(α * (L : ℝ))) ≤ ε / Real.sqrt 2 := by
    rw [hL]
    exact levelL_bias hα hc₁ hδ
  have hb0 : 0 ≤ c₁ * (2 : ℝ) ^ (-(α * (L : ℝ))) := by positivity
  have hmax : max 1 (c₁ / (ε / Real.sqrt 2)) ≤ (1 + Real.sqrt 2 * c₁) / ε := by
    apply max_le
    · rw [le_div_iff₀ hε]
      linarith
    · rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hε, mul_comm c₁]
      linarith
  have hLK : (2 : ℝ) ^ (α * (L : ℝ)) ≤ K / ε :=
    calc (2 : ℝ) ^ (α * (L : ℝ)) ≤ 2 ^ α * max 1 (c₁ / (ε / Real.sqrt 2)) := by
          rw [hL]
          exact two_rpow_levelL_le hα hc₁ hδ
      _ ≤ 2 ^ α * ((1 + Real.sqrt 2 * c₁) / ε) :=
          mul_le_mul_of_nonneg_left hmax (Real.rpow_pos_of_pos two_pos _).le
      _ = K / ε := by rw [hK_def]; ring
  have hγL := two_rpow_L_le hα hγ.le hK hε hLK
  -- the number of samples: `2 V̄ ε⁻²` rounded up, and at least one
  obtain ⟨-, hNpos, hNvar, hNcost⟩ :=
    mc_cost (C := 1) (by linarith : (0 : ℝ) ≤ 2 * Vbar) zero_le_one hε
  set N : ℕ := max 1 ⌈ε⁻¹ ^ 2 * (2 * Vbar)⌉₊ with hN_def
  refine ⟨L, N, hNpos, ?_, ?_⟩
  · have h1 : (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 ≤ (ε / Real.sqrt 2) ^ 2 :=
      pow_le_pow_left₀ hb0 hb 2
    have h2 : (ε / Real.sqrt 2) ^ 2 = ε ^ 2 / 2 := by rw [div_pow, hs2]
    rw [mul_div_assoc] at hNvar
    linarith
  · have hεinv : (1 : ℝ) ≤ ε⁻¹ ^ 2 := one_le_pow₀ ((one_le_inv₀ hε).2 hε1.le)
    have hNle : (N : ℝ) ≤ (2 * Vbar + 1) * ε⁻¹ ^ 2 := by
      have h := hNcost
      rw [mul_one, mul_one] at h
      nlinarith
    have hc3 : 0 ≤ c₃ * (2 : ℝ) ^ (γ * (L : ℝ)) := by positivity
    calc (N : ℝ) * (c₃ * (2 : ℝ) ^ (γ * (L : ℝ)))
        ≤ (2 * Vbar + 1) * ε⁻¹ ^ 2 * (c₃ * (K ^ (γ / α) * ε ^ (-(γ / α)))) :=
          mul_le_mul hNle (mul_le_mul_of_nonneg_left hγL hc₃.le) hc3 (by positivity)
      _ = (2 * Vbar + 1) * c₃ * K ^ (γ / α) * ε ^ (-2 - γ / α) := by
          rw [eps_inv_sq_eq hε, show (-2 : ℝ) - γ / α = -2 + -(γ / α) by ring,
            Real.rpow_add hε]
          ring

/-! ### The saving of MLMC over standard Monte Carlo -/

/-- **The MLMC saving when `V_ℓ C_ℓ` increases** (Giles 2015, §1.3, p. 4: "in the first case the
MLMC cost is reduced by factor `V_L/V₀`, corresponding to the ratio of the variances
`V[P_L − P_{L−1}]` and `V[P_L]`"; Haas–Giles 2025, §2.1, p. 3).  If `√(V_ℓ C_ℓ)` grows at least
geometrically with ratio `r > 1`, the cost (1.1), `τ⁻¹ (∑_{ℓ≤L} √(V_ℓ C_ℓ))²` (`τ = ε²`), is at
least `V_L/V_P` and at most `(r/(r−1))² V_L/V_P` times the standard Monte Carlo cost
`τ⁻¹ V_P C_L`, where `V_P = V[P_L] > 0`. -/
theorem mlmc_vs_mc_increasing {V C : ℕ → ℝ} {r τ VP : ℝ} (hr : 1 < r) (hτ : 0 < τ)
    (hVP : 0 < VP) (hV : ∀ ℓ, 0 ≤ V ℓ) (hC : ∀ ℓ, 0 ≤ C ℓ)
    (hgrow : ∀ ℓ, r * Real.sqrt (V ℓ * C ℓ) ≤ Real.sqrt (V (ℓ + 1) * C (ℓ + 1))) (L : ℕ) :
    V L / VP * (τ⁻¹ * VP * C L) ≤ τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 ∧
      τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 ≤
        (r / (r - 1)) ^ 2 * (V L / VP) * (τ⁻¹ * VP * C L) := by
  have hVP1 : VP / VP = 1 := div_self hVP.ne'
  have e : V L / VP * (τ⁻¹ * VP * C L) = τ⁻¹ * (V L * C L) :=
    calc V L / VP * (τ⁻¹ * VP * C L) = τ⁻¹ * (V L * C L) * (VP / VP) := by ring
      _ = τ⁻¹ * (V L * C L) := by rw [hVP1, mul_one]
  obtain ⟨h1, h2⟩ := optimal_cost_increasing hr hτ hV hC hgrow L
  refine ⟨by rw [e]; exact h1, ?_⟩
  calc τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2
      ≤ (r / (r - 1)) ^ 2 * (τ⁻¹ * (V L * C L)) := h2
    _ = (r / (r - 1)) ^ 2 * (V L / VP) * (τ⁻¹ * VP * C L) := by rw [mul_assoc, e]

/-- **The MLMC saving when `V_ℓ C_ℓ` decreases** (Giles 2015, §1.3, p. 4: "whereas in the second
case it is reduced by factor `C₀/C_L`, the ratio of the costs of computing `P₀` and
`P_L − P_{L−1}`"; Haas–Giles 2025, §2.1, p. 3).  If `√(V_ℓ C_ℓ)` decays at least geometrically
with ratio `0 ≤ r < 1`, the cost (1.1) is at least `(V₀/V_P)(C₀/C_L)` and at most
`(1 − r)⁻² (V₀/V_P)(C₀/C_L)` times the standard Monte Carlo cost `τ⁻¹ V_P C_L`, where
`V_P = V[P_L] > 0` (`≈ V₀` in the paper) and `C_L > 0`. -/
theorem mlmc_vs_mc_decreasing {V C : ℕ → ℝ} {r τ VP : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hτ : 0 < τ) (hVP : 0 < VP) (hV : ∀ ℓ, 0 ≤ V ℓ) (hC : ∀ ℓ, 0 ≤ C ℓ)
    (hdecay : ∀ ℓ, Real.sqrt (V (ℓ + 1) * C (ℓ + 1)) ≤ r * Real.sqrt (V ℓ * C ℓ)) {L : ℕ}
    (hCL : 0 < C L) :
    V 0 / VP * (C 0 / C L) * (τ⁻¹ * VP * C L) ≤
        τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 ∧
      τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 ≤
        ((1 - r)⁻¹) ^ 2 * (V 0 / VP * (C 0 / C L)) * (τ⁻¹ * VP * C L) := by
  have hVP1 : VP / VP = 1 := div_self hVP.ne'
  have hCL1 : C L / C L = 1 := div_self hCL.ne'
  have e : V 0 / VP * (C 0 / C L) * (τ⁻¹ * VP * C L) = τ⁻¹ * (V 0 * C 0) :=
    calc V 0 / VP * (C 0 / C L) * (τ⁻¹ * VP * C L) =
          τ⁻¹ * (V 0 * C 0) * (VP / VP) * (C L / C L) := by ring
      _ = τ⁻¹ * (V 0 * C 0) := by rw [hVP1, hCL1, mul_one, mul_one]
  obtain ⟨h1, h2⟩ := optimal_cost_decreasing hr0 hr hτ hV hC hdecay L
  refine ⟨by rw [e]; exact h1, ?_⟩
  calc τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2
      ≤ ((1 - r)⁻¹) ^ 2 * (τ⁻¹ * (V 0 * C 0)) := h2
    _ = ((1 - r)⁻¹) ^ 2 * (V 0 / VP * (C 0 / C L)) * (τ⁻¹ * VP * C L) := by
        rw [mul_assoc, e]

/-! ### The remarks after Theorem 1 -/

/-- **`β > γ`: the coarsest level dominates** (Giles 2015, §2.1, p. 7: "In the case `β > γ`, the
dominant computational cost is on the coarsest levels where `C_ℓ = O(1)` and `O(ε⁻²)` samples are
required").  Let `V_ℓ, C_ℓ > 0` with `S_∞ = ∑_ℓ √(V_ℓ C_ℓ) < ∞` (for `β > γ`, see
`summable_sqrt_Vb_mul_Cb`), and let `N_ℓ` be the allocation (1.1) with variance target `τ`
(`τ = ε²/2` in Theorem 1) on the levels `0, …, L`.  Then, uniformly in `L`,
`τ⁻¹ V₀ ≤ N₀ ≤ τ⁻¹ √(V₀/C₀) S_∞` (`Θ(ε⁻²)` samples), and level `0` carries at least the fraction
`√(V₀ C₀)/S_∞` of the total cost `∑_ℓ N_ℓ C_ℓ`. -/
theorem coarsest_level_dominant {V C : ℕ → ℝ} (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ)
    (hS : Summable fun ℓ => Real.sqrt (V ℓ * C ℓ)) {τ : ℝ} (hτ : 0 < τ) (L : ℕ) :
    τ⁻¹ * V 0 ≤ lagrangeN (range (L + 1)) V C τ 0 ∧
      lagrangeN (range (L + 1)) V C τ 0 ≤
        τ⁻¹ * Real.sqrt (V 0 / C 0) * ∑' ℓ, Real.sqrt (V ℓ * C ℓ) ∧
      Real.sqrt (V 0 * C 0) / (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) *
          ∑ ℓ ∈ range (L + 1), lagrangeN (range (L + 1)) V C τ ℓ * C ℓ ≤
        lagrangeN (range (L + 1)) V C τ 0 * C 0 := by
  have hs0 : ∀ ℓ, 0 ≤ Real.sqrt (V ℓ * C ℓ) := fun ℓ => Real.sqrt_nonneg _
  have hq0 : 0 < Real.sqrt (V 0 * C 0) := Real.sqrt_pos.2 (mul_pos (hV 0) (hC 0))
  have hmem : 0 ∈ range (L + 1) := Finset.mem_range.2 (Nat.succ_pos L)
  have hSlow : Real.sqrt (V 0 * C 0) ≤ ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) :=
    Finset.single_le_sum (fun ℓ _ => hs0 ℓ) hmem
  have hSup : ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) ≤ ∑' ℓ, Real.sqrt (V ℓ * C ℓ) :=
    hS.sum_le_tsum _ fun ℓ _ => hs0 ℓ
  have htot := (lagrangeN_variance_cost ⟨0, hmem⟩ (fun ℓ _ => hV ℓ) (fun ℓ _ => hC ℓ) hτ).2
  set S := ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) with hS_def
  set S' := ∑' ℓ, Real.sqrt (V ℓ * C ℓ) with hS'_def
  have hS0 : 0 ≤ S := hq0.le.trans hSlow
  have hS'pos : 0 < S' := (hq0.trans_le hSlow).trans_le hSup
  have hN0 : lagrangeN (range (L + 1)) V C τ 0 = τ⁻¹ * Real.sqrt (V 0 / C 0) * S := rfl
  have hr0 : 0 ≤ Real.sqrt (V 0 / C 0) := Real.sqrt_nonneg _
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  refine ⟨?_, ?_, ?_⟩
  · rw [hN0]
    calc τ⁻¹ * V 0 = τ⁻¹ * (Real.sqrt (V 0 / C 0) * Real.sqrt (V 0 * C 0)) := by
          rw [sqrt_div_mul_sqrt_mul (hV 0).le (hC 0)]
      _ ≤ τ⁻¹ * (Real.sqrt (V 0 / C 0) * S) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSlow hr0) hτi.le
      _ = τ⁻¹ * Real.sqrt (V 0 / C 0) * S := by ring
  · rw [hN0]
    exact mul_le_mul_of_nonneg_left hSup (mul_nonneg hτi.le hr0)
  · rw [htot]
    have hc0 : lagrangeN (range (L + 1)) V C τ 0 * C 0 = τ⁻¹ * S * Real.sqrt (V 0 * C 0) := by
      rw [hN0, ← sqrt_div_mul (hV 0).le (hC 0)]
      ring
    rw [hc0]
    have hSS : S / S' ≤ 1 := (div_le_one hS'pos).2 hSup
    calc Real.sqrt (V 0 * C 0) / S' * (τ⁻¹ * S ^ 2) =
          τ⁻¹ * S * Real.sqrt (V 0 * C 0) * (S / S') := by ring
      _ ≤ τ⁻¹ * S * Real.sqrt (V 0 * C 0) * 1 :=
          mul_le_mul_of_nonneg_left hSS (mul_nonneg (mul_nonneg hτi.le hS0) hq0.le)
      _ = τ⁻¹ * S * Real.sqrt (V 0 * C 0) := mul_one _

/-- **`β < γ`: the cost of a finest-level sample** (Giles 2015, §2.1, p. 7: "In the case `β < γ`
… Because of condition i), we have `2^{−αL} = O(ε)`, and hence `C_L = O(ε^{−γ/α})`").  At the
finest level of the proof of Theorem 1, `L = levelL α c₁ δ`, the least `L` with
`c₁ 2^{−αL} ≤ δ` (`δ = ε/2`), the bound `C_L ≤ c₃ 2^{γL}` gives
`C_L ≤ c₃ 2^γ max(1, c₁/δ)^{γ/α}`, which is `O(ε^{−γ/α})` for `δ` proportional to `ε`. -/
theorem finest_cost_le {α γ c₁ c₃ δ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) (hc₁ : 0 < c₁)
    (hc₃ : 0 ≤ c₃) (hδ : 0 < δ) :
    c₃ * (2 : ℝ) ^ (γ * (levelL α c₁ δ : ℝ)) ≤ c₃ * (2 ^ γ * max 1 (c₁ / δ) ^ (γ / α)) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hL := two_rpow_levelL_le hα hc₁ hδ
  have e : (2 : ℝ) ^ (γ * (levelL α c₁ δ : ℝ)) =
      ((2 : ℝ) ^ (α * (levelL α c₁ δ : ℝ))) ^ (γ / α) := by
    rw [← Real.rpow_mul h2]
    congr 1
    calc γ * (levelL α c₁ δ : ℝ) = γ / α * (α * (levelL α c₁ δ : ℝ)) := by
          rw [← mul_assoc, div_mul_cancel₀ γ hα.ne']
      _ = α * (levelL α c₁ δ : ℝ) * (γ / α) := mul_comm _ _
  have e2 : ((2 : ℝ) ^ α * max 1 (c₁ / δ)) ^ (γ / α) = 2 ^ γ * max 1 (c₁ / δ) ^ (γ / α) := by
    rw [Real.mul_rpow (Real.rpow_nonneg h2 _) (zero_le_one.trans (le_max_left _ _)),
      ← Real.rpow_mul h2, mul_div_cancel₀ γ hα.ne']
  rw [e, ← e2]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Real.rpow_nonneg h2 _) hL (div_nonneg hγ hα.le)) hc₃

/-- **`β = γ`: the cost and the variance are spread evenly over the levels** (Giles 2015, §2.1,
p. 7: "The dividing case `β = γ` is the one for which both the computational effort, and the
contributions to the overall variance, are spread approximately evenly across all of the levels;
the `(log ε)²` term corresponds to the `L²` factor in the corresponding discussion at the end of
Section 1.3"; §1.3, p. 4: "If the product `V_ℓ C_ℓ` does not vary with level, then the total cost
is `ε⁻² L² V₀ C₀ = ε⁻² L² V_L C_L`").  If `√(V_ℓ C_ℓ) = s` on the levels `0, …, L` (for
`V_ℓ = c₂ 2^{−βℓ}`, `C_ℓ = c₃ 2^{βℓ}`, `s = √(c₂ c₃)`), the allocation (1.1) with variance target
`τ` gives every level the variance `τ/(L+1)` and the cost `τ⁻¹ (L+1) s²`, and costs
`τ⁻¹ (L+1)² s²` in total (`L + 1` levels, the paper's `L²`). -/
theorem equal_cost_per_level {V C : ℕ → ℝ} (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ) {τ s : ℝ}
    (hτ : 0 < τ) {L : ℕ} (hs : ∀ ℓ ≤ L, Real.sqrt (V ℓ * C ℓ) = s) :
    (∀ ℓ ≤ L, V ℓ / lagrangeN (range (L + 1)) V C τ ℓ = τ / (L + 1)) ∧
      (∀ ℓ ≤ L, lagrangeN (range (L + 1)) V C τ ℓ * C ℓ = τ⁻¹ * (L + 1) * s ^ 2) ∧
      ∑ ℓ ∈ range (L + 1), lagrangeN (range (L + 1)) V C τ ℓ * C ℓ =
        τ⁻¹ * (L + 1) ^ 2 * s ^ 2 := by
  have hmem : 0 ∈ range (L + 1) := Finset.mem_range.2 (Nat.succ_pos L)
  have hsum : ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) = (L + 1) * s := by
    rw [Finset.sum_congr rfl fun ℓ hℓ => hs ℓ (Nat.lt_add_one_iff.1 (Finset.mem_range.1 hℓ)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add_one]
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, ?_⟩
  · have hVl : 0 < V ℓ := hV ℓ
    have hL0 : (0 : ℝ) < L + 1 := by positivity
    have e : lagrangeN (range (L + 1)) V C τ ℓ = τ⁻¹ * (L + 1) * V ℓ := by
      show τ⁻¹ * Real.sqrt (V ℓ / C ℓ) * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) = _
      rw [hsum, ← hs ℓ hℓ]
      calc τ⁻¹ * Real.sqrt (V ℓ / C ℓ) * ((L + 1) * Real.sqrt (V ℓ * C ℓ))
          = τ⁻¹ * (L + 1) * (Real.sqrt (V ℓ / C ℓ) * Real.sqrt (V ℓ * C ℓ)) := by ring
        _ = τ⁻¹ * (L + 1) * V ℓ := by rw [sqrt_div_mul_sqrt_mul hVl.le (hC ℓ)]
    have hττ : τ * τ⁻¹ = 1 := mul_inv_cancel₀ hτ.ne'
    have hN : 0 < τ⁻¹ * (L + 1) * V ℓ := by positivity
    rw [e, div_eq_div_iff hN.ne' hL0.ne']
    calc V ℓ * ((L : ℝ) + 1) = V ℓ * (L + 1) * (τ * τ⁻¹) := by rw [hττ, mul_one]
      _ = τ * (τ⁻¹ * (L + 1) * V ℓ) := by ring
  · have e : lagrangeN (range (L + 1)) V C τ ℓ * C ℓ =
        τ⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) * Real.sqrt (V ℓ * C ℓ) := by
      show τ⁻¹ * Real.sqrt (V ℓ / C ℓ) * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) * C ℓ = _
      rw [← sqrt_div_mul (hV ℓ).le (hC ℓ)]
      ring
    rw [e, hsum, hs ℓ hℓ]
    ring
  · rw [(lagrangeN_variance_cost ⟨0, hmem⟩ (fun ℓ _ => hV ℓ) (fun ℓ _ => hC ℓ) hτ).2, hsum]
    ring

/-! ### The split of the mean-square error, and the randomised estimator -/

/-- **The cost of a split `θ ε²` / `(1 − θ) ε²` of the MSE** (Giles 2015, §2.1, p. 8: "the equal
split between the error due to `E[P_ℓ − P_{ℓ−1}]` and the error due to the variance `V[Y]` is
definitely not optimal").  With bias budget `θ ε²` and variance budget `(1 − θ) ε²` (`θ < 1`,
`ε > 0`), the allocation (1.1) on the levels `0, …, L` meets the variance budget exactly and costs
`(1 − θ)⁻¹ ε⁻² (∑_{ℓ≤L} √(V_ℓ C_ℓ))²`. -/
theorem split_cost {V C : ℕ → ℝ} (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ) {θ ε : ℝ}
    (hθ1 : θ < 1) (hε : 0 < ε) (L : ℕ) :
    ∑ ℓ ∈ range (L + 1), V ℓ / lagrangeN (range (L + 1)) V C ((1 - θ) * ε ^ 2) ℓ =
        (1 - θ) * ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), lagrangeN (range (L + 1)) V C ((1 - θ) * ε ^ 2) ℓ * C ℓ =
        (1 - θ)⁻¹ * ((ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) := by
  have hτ : 0 < (1 - θ) * ε ^ 2 := mul_pos (by linarith) (by positivity)
  obtain ⟨h1, h2⟩ := lagrangeN_variance_cost ⟨0, Finset.mem_range.2 (Nat.succ_pos L)⟩
    (fun ℓ _ => hV ℓ) (fun ℓ _ => hC ℓ) hτ
  refine ⟨h1, ?_⟩
  rw [h2, mul_inv]
  ring

/-- **The equal split costs less than twice any split with at least as many levels** (Giles 2015,
§2.1, p. 8: allocating most of the error to the variance "can give up to a factor 2×
improvement in computational cost compared to the equal split").  For `θ < 1` and `L ≤ L'`, the
cost `(ε²/2)⁻¹ S_L²` of the equal split on the levels `0, …, L` is at most `2(1 − θ)` times the
cost `((1 − θ) ε²)⁻¹ S_{L'}²` of the split `θ` on the levels `0, …, L'`
(`S_L = ∑_{ℓ≤L} √(V_ℓ C_ℓ)`); a smaller bias budget `θ ε² < ε²/2` needs `L' ≥ L`. -/
theorem equal_split_cost_le {V C : ℕ → ℝ} {θ ε : ℝ} (hθ1 : θ < 1) (hε : 0 < ε) {L L' : ℕ}
    (hLL' : L ≤ L') :
    (ε ^ 2 / 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 ≤
      2 * (1 - θ) * (((1 - θ) * ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L' + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) := by
  have hS0 : 0 ≤ ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hmono : ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) ≤
      ∑ ℓ ∈ range (L' + 1), Real.sqrt (V ℓ * C ℓ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      fun _ _ _ => Real.sqrt_nonneg _
  have h1θ : (1 - θ) * (1 - θ)⁻¹ = 1 := mul_inv_cancel₀ (sub_pos.2 hθ1).ne'
  set X := (∑ ℓ ∈ range (L' + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 with hX
  have e : 2 * (1 - θ) * (((1 - θ) * ε ^ 2)⁻¹ * X) = (ε ^ 2 / 2)⁻¹ * X := by
    rw [mul_inv, inv_div]
    calc 2 * (1 - θ) * ((1 - θ)⁻¹ * (ε ^ 2)⁻¹ * X) =
          2 * ((1 - θ) * (1 - θ)⁻¹) * ((ε ^ 2)⁻¹ * X) := by ring
      _ = 2 / ε ^ 2 * X := by rw [h1θ]; ring
  rw [e, hX]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hmono 2) (by positivity)

/-- `∑_ℓ √(V_ℓ C_ℓ)` converges for `V_ℓ = c₂ 2^{−βℓ}`, `C_ℓ = c₃ 2^{γℓ}` with `β > γ` (Giles 2015,
§2.1, p. 7, and §2.2, p. 10: "`p_ℓ ∝ 2^{−(γ+β)ℓ/2}` … is not possible when `β ≤ γ`"): its terms
are `√(c₂ c₃) 2^{−(β−γ)ℓ/2}`. -/
theorem summable_sqrt_Vb_mul_Cb {β γ c₂ c₃ : ℝ} (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hγβ : γ < β) :
    Summable fun ℓ : ℕ => Real.sqrt (Vb β c₂ ℓ * Cb γ c₃ ℓ) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ ((γ - β) / 2) := Real.rpow_nonneg zero_le_two _
  have hr1 : (2 : ℝ) ^ ((γ - β) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  exact ((summable_geometric_of_lt_one hr0 hr1).mul_left (Real.sqrt (c₂ * c₃))).congr
    fun ℓ => (sqrt_Vb_mul_Cb hc₂ hc₃ ℓ).symm

/-- **The equal split tends to twice the cost** (Giles 2015, §2.1, p. 8, and §2.2, p. 11: for
`β > γ` "one can increase the value of `L` substantially at negligible cost").  If
`S_∞ = ∑_ℓ √(V_ℓ C_ℓ)` converges, the cost `(ε²/2)⁻¹ S_L²` of the equal split tends to
`2 ε⁻² S_∞²` as `L → ∞`. -/
theorem tendsto_equal_split_cost {V C : ℕ → ℝ} (hS : Summable fun ℓ => Real.sqrt (V ℓ * C ℓ))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun L : ℕ => (ε ^ 2 / 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2)
      atTop (𝓝 (2 * ((ε ^ 2)⁻¹ * (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2))) := by
  have h1 : Tendsto (fun L : ℕ => ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) atTop
      (𝓝 (∑' ℓ, Real.sqrt (V ℓ * C ℓ))) :=
    (hS.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have e : 2 * ((ε ^ 2)⁻¹ * (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2) =
      (ε ^ 2 / 2)⁻¹ * (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2 := by
    rw [inv_div]
    ring
  rw [e]
  exact (h1.pow 2).const_mul _

/-- **Allocating almost all of the MSE to the variance** (Giles 2015, §2.1, p. 8, and §2.2, p. 11:
"and at the same time allocate almost all of the Mean Square Error budget of `ε²` to the variance
term in (2.1), leading to approximately the same total cost").  If `S_∞ = ∑_ℓ √(V_ℓ C_ℓ)`
converges, `θ_k → 0` and `L_k → ∞`, the costs `((1 − θ_k) ε²)⁻¹ S_{L_k}²` of the splits `θ_k`
tend to `ε⁻² S_∞²`: half the limit of the equal split (`tendsto_equal_split_cost`), the "factor 2×
improvement". -/
theorem tendsto_split_cost {V C : ℕ → ℝ} (hS : Summable fun ℓ => Real.sqrt (V ℓ * C ℓ)) {ε : ℝ}
    (hε : 0 < ε) {θ : ℕ → ℝ} (hθ : Tendsto θ atTop (𝓝 0)) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun k => ((1 - θ k) * ε ^ 2)⁻¹ *
        (∑ ℓ ∈ range (L k + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) atTop
      (𝓝 ((ε ^ 2)⁻¹ * (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2)) := by
  have h1 : Tendsto (fun k => ∑ ℓ ∈ range (L k + 1), Real.sqrt (V ℓ * C ℓ)) atTop
      (𝓝 (∑' ℓ, Real.sqrt (V ℓ * C ℓ))) :=
    ((hS.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)).comp hL
  have h3 : Tendsto (fun k => (1 - θ k) * ε ^ 2) atTop (𝓝 ((1 - 0) * ε ^ 2)) :=
    (tendsto_const_nhds.sub hθ).mul_const _
  rw [sub_zero, one_mul] at h3
  exact (h3.inv₀ (by positivity)).mul (h1.pow 2)

/-- **The randomised estimator costs half the standard MLMC algorithm** (Giles 2015, §2.2,
pp. 10–11: the optimal randomised cost is "`C ≈ ε⁻² (∑_ℓ √(V_ℓ C_ℓ))²`, which is the same as the
total cost in Eq. (1.1), and half the cost of the standard MLMC algorithm in which only half of the
MSE “budget” of `ε²` is allocated to the variance").  Let `V_ℓ, C_ℓ > 0` with `∑ √(V_ℓ C_ℓ)` and
`∑ √(V_ℓ/C_ℓ)` convergent (`β > γ`).  The least value of the randomised cost
`ε⁻² (∑ p_ℓ⁻¹ V_ℓ)(∑ p_ℓ C_ℓ)` over the level distributions `p` is `ε⁻² S_∞²`
(`randomised_optimal_p_isLeast`), and the cost of the standard algorithm with the equal split tends
to twice this value as `L → ∞`. -/
theorem randomised_half_cost {V C : ℕ → ℝ} (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ)
    (hS : Summable fun ℓ => Real.sqrt (V ℓ * C ℓ))
    (hZ : Summable fun ℓ => Real.sqrt (V ℓ / C ℓ)) {ε : ℝ} (hε : 0 < ε) :
    IsLeast {x | ∃ p : ℕ → ℝ, (∀ ℓ, 0 < p ℓ) ∧ HasSum p 1 ∧
        Summable (fun ℓ => V ℓ / p ℓ) ∧ Summable (fun ℓ => p ℓ * C ℓ) ∧
        x = (ε ^ 2)⁻¹ * ((∑' ℓ, V ℓ / p ℓ) * ∑' ℓ, p ℓ * C ℓ)}
      ((ε ^ 2)⁻¹ * (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2) ∧
    Tendsto (fun L : ℕ => (ε ^ 2 / 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2)
      atTop (𝓝 (2 * ((ε ^ 2)⁻¹ * (∑' ℓ, Real.sqrt (V ℓ * C ℓ)) ^ 2))) := by
  obtain ⟨⟨hmem, hlow⟩, -⟩ := randomised_optimal_p_isLeast hV hC hS hZ
  have hc : 0 ≤ (ε ^ 2)⁻¹ := by positivity
  refine ⟨⟨?_, ?_⟩, tendsto_equal_split_cost hS hε⟩
  · obtain ⟨p, hp, h1, h2, h3, hx⟩ := hmem
    exact ⟨p, hp, h1, h2, h3, by rw [hx]⟩
  · rintro x ⟨p, hp, h1, h2, h3, rfl⟩
    exact mul_le_mul_of_nonneg_left (hlow ⟨p, hp, h1, h2, h3, rfl⟩) hc

end MLMC
