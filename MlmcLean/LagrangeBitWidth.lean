import MlmcLean.BitWidth
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Haas–Giles §4.3 and §6: the level cost (34), the Lagrange conditions (35) and (37), the trends

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §2 (p. 3), §4.3 (p. 10), §6.1 (pp. 11–12), §6.2 (p. 13) and §6.3
(pp. 13–14).  `MlmcLean.BitWidth` proves that (35) is a set of uncoupled scalar equations, each
with exactly one solution, and the derivative identity (36); this file completes §6.

* **(34) approximates (33)** (§6.1, p. 11).  With `Ṽ_ℓ = V_ℓ` and `C^Δ_ℓ = C_ℓ + C̃_ℓ`, the level
  cost (33) lies between (34) and `√(1 + C̃_ℓ/C_ℓ)` times (34), so the relative error of (34) is
  at most `C̃_ℓ/(2 C_ℓ)`: "using the fact that `C_ℓ ≫ C̃_ℓ`" (`levelCost34_le_levelCost33`,
  `levelCost33_le_sqrt_mul`, `levelCost33_le_add_mul`); summed over the levels, the total cost
  (32) lies between `ε⁻² (∑_ℓ (34))²` and `(1 + r)` times it when every `C̃_ℓ ≤ r C_ℓ`
  (`totalCost32_bounds`).
* **(35) is sufficient** (§6.1, pp. 11–12: "minimising `V^Δ_ℓ(d)` subject to a fixed `C̃_ℓ(d)`
  leads to the equation (35)").  The bound (26) and the cost (31) are convex and separable, so
  bit-widths solving (35) for some `λ ≥ 0` minimise the Lagrangian `V_indep + λ C̃`
  (`lagrangian_le_of_eq35`), hence minimise `V_indep` among all bit-widths of no greater cost
  (`vIndepR_le_of_eq35`), and, for `λ > 0`, minimise the cost among all bit-widths of no greater
  variance (`sepCost_le_of_eq35`).  For every `λ > 0` such bit-widths exist
  (`exists_eq35_isMin`).
* **(35) is necessary** (Lagrange multipliers): at a local minimum of `V_indep` on a level set of
  the cost `C̃` where `∇C̃ ≠ 0`, (35) holds for some `λ` (`eq35_of_isLocalMinOn`); so the marginal
  ratios `(−∂V_indep/∂d_i)/(∂C̃/∂d_i)` are all equal (`marginalRatio_eq_of_isLocalMinOn`, §6.3,
  p. 14: "if an error was 'disproportionately' small, there would be potential for cost
  savings").
* **(37)** (§6.1, p. 12): at uniform bit-widths, (37) determines `λ` uniquely
  (`eq37_iff`), `λ > 0` (`lambda37_pos`), and (37) is the sum over `i` of (35)
  (`eq37_of_eq35`).
* **(38) is uncoupled** (§6.2, p. 13): adding one bit to `d_i` lowers `V_indep` by
  `E[x̄_i²] 4^{e_i − d_i}/16` and raises `C̃` by `M_i (d_i + ½) + M'_i`, so the ratio (38) depends
  on `d_i` only (`vIndepR_sub_update_add_one`, `sepCost_update_add_one_sub`).
* **The trend of §6.3** (p. 13): one more bit divides the squared rounding error by 4
  (`rpow_four_sub_add_one`); if the variance factors `(1/12) E[x̄²] 4^{e_ℓ}` double from level to
  level and `d_{ℓ+1} = d_ℓ + 1`, the error bounds halve at every level (`errorBound_succ`,
  `errorBound_eq_div_pow`) and the share of each variable in the total is the same on all
  levels (`errorShare_succ`).
* **The size of the LUT** (§4.3, p. 10): if the LUT is chosen so that the MSE term of (28) is at
  most `V_indep`, the variance of the error is at most `2 V_indep`
  (`variance_extended_le_two_mul`).
-/

open Finset MeasureTheory ProbabilityTheory

namespace MLMC

/-! ### (34) as an approximation of (33) -/

section levelCost

/-- **Haas–Giles (2025), §6.1, p. 11: (34) is a lower bound for (33).**  With `Ṽ_ℓ = V_ℓ` (§6,
p. 11: "We make the assumption that the variance `Ṽ_ℓ` of the FPGA sample is approximately equal
to `V_ℓ`") and `C^Δ_ℓ = C_ℓ + C̃_ℓ` (§2, p. 3: "The cost of computing a sample of the correction
term is `C^Δ_ℓ = C_ℓ + C̃_ℓ`"), the level cost (33), `√(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ)`, is at least
its approximation (34), `√(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ)`. -/
theorem levelCost34_le_levelCost33 {V Vd C Ct : ℝ} (hVd : 0 ≤ Vd) (hCt : 0 ≤ Ct) :
    Real.sqrt (V * Ct) + Real.sqrt (Vd * C) ≤ Real.sqrt (V * Ct) + Real.sqrt (Vd * (C + Ct)) := by
  have h : Vd * C ≤ Vd * (C + Ct) := mul_le_mul_of_nonneg_left (by linarith) hVd
  linarith [Real.sqrt_le_sqrt h]

/-- **Haas–Giles (2025), §6.1, p. 11: (33) is at most `√(1 + C̃_ℓ/C_ℓ)` times (34).**  The level
cost (33) is "approximated as (34) using the fact that `C_ℓ ≫ C̃_ℓ`": with `Ṽ_ℓ = V_ℓ` and
`C^Δ_ℓ = C_ℓ + C̃_ℓ`, the ratio of (33) to (34) lies between `1` (`levelCost34_le_levelCost33`)
and `√(1 + C̃_ℓ/C_ℓ)`. -/
theorem levelCost33_le_sqrt_mul {V Vd C Ct : ℝ} (hC : 0 < C) (hCt : 0 ≤ Ct) :
    Real.sqrt (V * Ct) + Real.sqrt (Vd * (C + Ct)) ≤
      Real.sqrt (1 + Ct / C) * (Real.sqrt (V * Ct) + Real.sqrt (Vd * C)) := by
  have hq : 0 ≤ Ct / C := div_nonneg hCt hC.le
  have h1 : 1 ≤ Real.sqrt (1 + Ct / C) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + Ct / C by linarith)
    rwa [Real.sqrt_one] at this
  have h2 : Real.sqrt (Vd * (C + Ct)) = Real.sqrt (1 + Ct / C) * Real.sqrt (Vd * C) := by
    rw [← Real.sqrt_mul (by linarith)]
    congr 1
    rw [show (1 + Ct / C) * (Vd * C) = Vd * (C + Ct / C * C) by ring, div_mul_cancel₀ Ct hC.ne']
  have h3 : Real.sqrt (V * Ct) ≤ Real.sqrt (1 + Ct / C) * Real.sqrt (V * Ct) :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) h1
  rw [h2, mul_add]
  linarith

/-- **Haas–Giles (2025), §6.1, p. 11: the relative error of (34).**  With `Ṽ_ℓ = V_ℓ` and
`C^Δ_ℓ = C_ℓ + C̃_ℓ`, (33) exceeds (34) by at most the fraction `C̃_ℓ/(2 C_ℓ)` of (34), which is
small "using the fact that `C_ℓ ≫ C̃_ℓ`". -/
theorem levelCost33_le_add_mul {V Vd C Ct : ℝ} (hC : 0 < C) (hCt : 0 ≤ Ct) :
    Real.sqrt (V * Ct) + Real.sqrt (Vd * (C + Ct)) ≤
      (1 + Ct / (2 * C)) * (Real.sqrt (V * Ct) + Real.sqrt (Vd * C)) := by
  have hq : 0 ≤ Ct / C := div_nonneg hCt hC.le
  have h2C : Ct / (2 * C) = Ct / C / 2 := by ring
  have hs : Real.sqrt (1 + Ct / C) ≤ 1 + Ct / (2 * C) := by
    rw [h2C]
    calc Real.sqrt (1 + Ct / C) ≤ Real.sqrt ((1 + Ct / C / 2) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Ct / C)])
      _ = 1 + Ct / C / 2 := Real.sqrt_sq (by linarith)
  have h0 : 0 ≤ Real.sqrt (V * Ct) + Real.sqrt (Vd * C) := by positivity
  exact (levelCost33_le_sqrt_mul hC hCt).trans (mul_le_mul_of_nonneg_right hs h0)

/-- **Haas–Giles (2025), §6, p. 11, the total cost (32) and the approximation (34).**  With
`Ṽ_ℓ = V_ℓ` and `C^Δ_ℓ = C_ℓ + C̃_ℓ`, the total cost (32),
`ε⁻² (∑_ℓ √(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ))²`, is at least `ε⁻² (∑_ℓ (34))²`, and, if `C̃_ℓ ≤ r C_ℓ`
on every level, at most `(1 + r)` times it. -/
theorem totalCost32_bounds (L : ℕ) {V Vd C Ct : ℕ → ℝ} {ε r : ℝ} (hVd : ∀ ℓ, 0 ≤ Vd ℓ)
    (hC : ∀ ℓ, 0 < C ℓ) (hCt : ∀ ℓ, 0 ≤ Ct ℓ) (hr : ∀ ℓ ∈ range (L + 1), Ct ℓ / C ℓ ≤ r) :
    (ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ))) ^ 2 ≤
        (ε ^ 2)⁻¹ *
          (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ)))) ^ 2 ∧
      (ε ^ 2)⁻¹ *
          (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ)))) ^ 2 ≤
        (1 + r) * ((ε ^ 2)⁻¹ *
          (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ))) ^ 2) := by
  have hA0 : 0 ≤ ∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ)) :=
    Finset.sum_nonneg fun ℓ _ => by positivity
  have hAB : ∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ)) ≤
      ∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ))) :=
    Finset.sum_le_sum fun ℓ _ => levelCost34_le_levelCost33 (hVd ℓ) (hCt ℓ)
  have hr0 : 0 ≤ r :=
    le_trans (div_nonneg (hCt 0) (hC 0).le) (hr 0 (Finset.mem_range.2 (Nat.succ_pos L)))
  have hBA : ∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ))) ≤
      Real.sqrt (1 + r) *
        ∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ℓ hℓ => ?_
    refine (levelCost33_le_sqrt_mul (hC ℓ) (hCt ℓ)).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hr ℓ hℓ])) (by positivity)
  generalize ∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ)) = A
    at hA0 hAB hBA ⊢
  generalize ∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ))) = B
    at hAB hBA ⊢
  have hε : 0 ≤ (ε ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg ε)
  have hB2 : B ^ 2 ≤ (1 + r) * A ^ 2 :=
    calc B ^ 2 ≤ (Real.sqrt (1 + r) * A) ^ 2 := pow_le_pow_left₀ (hA0.trans hAB) hBA 2
      _ = (1 + r) * A ^ 2 := by rw [mul_pow, Real.sq_sqrt (by linarith)]
  refine ⟨mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hAB 2) hε, ?_⟩
  calc (ε ^ 2)⁻¹ * B ^ 2 ≤ (ε ^ 2)⁻¹ * ((1 + r) * A ^ 2) := mul_le_mul_of_nonneg_left hB2 hε
    _ = (1 + r) * ((ε ^ 2)⁻¹ * A ^ 2) := by ring

end levelCost

/-! ### (35) is sufficient: convexity -/

section sufficiency

variable {ι : Type*}

/-- The one-variable inequality behind the sufficiency of (35): for `E, M, λ ≥ 0` the function
`t ↦ E 4^{e − t}/12 + λ (M t²/2 + M' t)` is convex, so it is minimised at any `s` where its
derivative `−(log 4) E 4^{e − s}/12 + λ (M s + M')` vanishes (Haas–Giles 2025, §6.1, (35)). -/
lemma bitWidthLagrangian_le {E M M' lam e s : ℝ} (hE : 0 ≤ E) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (h35 : -(Real.log 4 * E * (4 : ℝ) ^ (e - s) / 12) + lam * (M * s + M') = 0) (t : ℝ) :
    E * (4 : ℝ) ^ (e - s) / 12 + lam * (M * s ^ 2 / 2 + M' * s) ≤
      E * (4 : ℝ) ^ (e - t) / 12 + lam * (M * t ^ 2 / 2 + M' * t) := by
  have hx : (4 : ℝ) ^ (e - t) = (4 : ℝ) ^ (e - s) * (4 : ℝ) ^ (s - t) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
    congr 1
    ring
  have hexp : 1 + Real.log 4 * (s - t) ≤ (4 : ℝ) ^ (s - t) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith [Real.add_one_le_exp (Real.log 4 * (s - t))]
  have key : (E * (4 : ℝ) ^ (e - t) / 12 + lam * (M * t ^ 2 / 2 + M' * t)) -
      (E * (4 : ℝ) ^ (e - s) / 12 + lam * (M * s ^ 2 / 2 + M' * s)) =
      E * (4 : ℝ) ^ (e - s) * ((4 : ℝ) ^ (s - t) - (1 + Real.log 4 * (s - t))) / 12 +
        lam * M * (t - s) ^ 2 / 2 +
        (t - s) * (-(Real.log 4 * E * (4 : ℝ) ^ (e - s) / 12) + lam * (M * s + M')) := by
    rw [hx]
    ring
  rw [h35, mul_zero, add_zero] at key
  have h1 : 0 ≤ E * (4 : ℝ) ^ (e - s) * ((4 : ℝ) ^ (s - t) - (1 + Real.log 4 * (s - t))) / 12 :=
    div_nonneg (mul_nonneg (mul_nonneg hE (Real.rpow_nonneg (by norm_num) _)) (by linarith))
      (by norm_num)
  have h2 : 0 ≤ lam * M * (t - s) ^ 2 / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hlam hM) (sq_nonneg _)) (by norm_num)
  linarith

/-- The Lagrangian `V_indep + λ C̃` of (35), with the bound (26) and the cost (31), as one sum over
the variables (Haas–Giles 2025, §6.1). -/
lemma vIndepR_add_mul_sepCost (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ) (lam : ℝ)
    (x : ι → ℝ) :
    vIndepR s E e x + lam * sepCost s M M' x =
      ∑ i ∈ s, (E i * (4 : ℝ) ^ ((e i : ℝ) - x i) / 12 +
        lam * (M i * x i ^ 2 / 2 + M' i * x i)) := by
  simp only [vIndepR, sepCost, Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Haas–Giles (2025), §6.1, pp. 11–12: bit-widths solving (35) minimise the Lagrangian.**  If
the bit-widths `d*` solve (35), `∂V_indep/∂d_i + λ ∂C̃/∂d_i = 0` for every variable `i`, with the
partial derivatives `−(log 4) E[x̄_i²] 4^{e_i − d_i}/12` of the bound (26) and `M_i d_i + M'_i` of
the cost (31) (`hasDerivAt_vIndepR_update`, `hasDerivAt_sepCost_update`), for some `λ ≥ 0`, and
`E[x̄_i²], M_i ≥ 0`, then `d*` minimises `V_indep + λ C̃` over all real bit-widths: both functions
are convex and separable. -/
theorem lagrangian_le_of_eq35 (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ)
    (hE : ∀ i ∈ s, 0 ≤ E i) (hM : ∀ i ∈ s, 0 ≤ M i) {lam : ℝ} (hlam : 0 ≤ lam)
    {dstar : ι → ℝ}
    (h35 : ∀ i ∈ s, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
      lam * (M i * dstar i + M' i) = 0) (d : ι → ℝ) :
    vIndepR s E e dstar + lam * sepCost s M M' dstar ≤
      vIndepR s E e d + lam * sepCost s M M' d := by
  rw [vIndepR_add_mul_sepCost, vIndepR_add_mul_sepCost]
  exact Finset.sum_le_sum fun i hi =>
    bitWidthLagrangian_le (hE i hi) (hM i hi) hlam (h35 i hi) (d i)

/-- **Haas–Giles (2025), §6.1, pp. 11–12: (35) is sufficient for "minimising `V^Δ_ℓ(d)` subject to
a fixed `C̃_ℓ(d)`".**  Bit-widths `d*` solving (35) for some `λ ≥ 0` (with `E[x̄_i²], M_i ≥ 0`)
have the least variance bound `V_indep` among all real bit-widths `d` whose cost `C̃(d)` is at most
`C̃(d*)`. -/
theorem vIndepR_le_of_eq35 (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ)
    (hE : ∀ i ∈ s, 0 ≤ E i) (hM : ∀ i ∈ s, 0 ≤ M i) {lam : ℝ} (hlam : 0 ≤ lam)
    {dstar : ι → ℝ}
    (h35 : ∀ i ∈ s, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
      lam * (M i * dstar i + M' i) = 0) {d : ι → ℝ}
    (hd : sepCost s M M' d ≤ sepCost s M M' dstar) :
    vIndepR s E e dstar ≤ vIndepR s E e d := by
  have h := lagrangian_le_of_eq35 s E e M M' hE hM hlam h35 d
  have h' := mul_le_mul_of_nonneg_left hd hlam
  linarith

/-- **Haas–Giles (2025), §6.1, pp. 11–12: the dual form of (35).**  Bit-widths `d*` solving (35)
for some `λ > 0` (with `E[x̄_i²], M_i ≥ 0`) have the least cost `C̃` among all real bit-widths `d`
whose variance bound `V_indep(d)` is at most `V_indep(d*)`: "the Lagrange multiplier `λ` controls
the trade-off between cost and variance". -/
theorem sepCost_le_of_eq35 (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ)
    (hE : ∀ i ∈ s, 0 ≤ E i) (hM : ∀ i ∈ s, 0 ≤ M i) {lam : ℝ} (hlam : 0 < lam)
    {dstar : ι → ℝ}
    (h35 : ∀ i ∈ s, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
      lam * (M i * dstar i + M' i) = 0) {d : ι → ℝ}
    (hd : vIndepR s E e d ≤ vIndepR s E e dstar) :
    sepCost s M M' dstar ≤ sepCost s M M' d := by
  have h := lagrangian_le_of_eq35 s E e M M' hE hM hlam.le h35 d
  exact le_of_mul_le_mul_left (by linarith) hlam

/-- **Haas–Giles (2025), §6.1, pp. 11–12: the Lagrange multiplier approach.**  For every `λ > 0`
(and `E[x̄_i²] > 0`, `M_i, M'_i ≥ 0` not both zero), the uncoupled equations (35) have a solution
`d*` (one per variable, `exists_unique_bitWidth`), and `d*` has the least variance bound
`V_indep` among all real bit-widths of no greater cost (31): "minimising `V^Δ_ℓ(d)` subject to a
fixed `C̃_ℓ(d)` leads to the equation (35) for a value of the Lagrange multiplier `λ` which gives
the desired `C̃_ℓ(d)`". -/
theorem exists_eq35_isMin (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ)
    (hE : ∀ i ∈ s, 0 < E i) (hM : ∀ i ∈ s, 0 ≤ M i) (hM' : ∀ i ∈ s, 0 ≤ M' i)
    (hMM : ∀ i ∈ s, 0 < M i + M' i) {lam : ℝ} (hlam : 0 < lam) :
    ∃ dstar : ι → ℝ,
      (∀ i ∈ s, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
        lam * (M i * dstar i + M' i) = 0) ∧
      ∀ d : ι → ℝ, sepCost s M M' d ≤ sepCost s M M' dstar →
        vIndepR s E e dstar ≤ vIndepR s E e d := by
  have h : ∀ i ∈ s, ∃ t : ℝ, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - t) / 12) +
      lam * (M i * t + M' i) = 0 := fun i hi =>
    (exists_unique_bitWidth (e i) hlam (hE i hi) (hM i hi) (hM' i hi) (hMM i hi)).exists
  choose! dstar hdstar using h
  exact ⟨dstar, hdstar, fun d hd =>
    vIndepR_le_of_eq35 s E e M M' (fun i hi => (hE i hi).le) hM hlam.le hdstar hd⟩

end sufficiency

/-! ### (35) is necessary: Lagrange multipliers -/

section necessity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The variance bound (26) is strictly differentiable in the bit-widths. -/
lemma exists_hasStrictFDerivAt_vIndepR (E : ι → ℝ) (e : ι → ℤ) (d : ι → ℝ) :
    ∃ V' : StrongDual ℝ (ι → ℝ), HasStrictFDerivAt (vIndepR univ E e) V' d := by
  have hterm : ∀ i, ∃ A' : StrongDual ℝ (ι → ℝ),
      HasStrictFDerivAt (fun x : ι → ℝ => E i * (4 : ℝ) ^ ((e i : ℝ) - x i)) A' d := by
    intro i
    have h1 : HasStrictDerivAt (fun t : ℝ => (e i : ℝ) - t) (-1) (d i) :=
      (hasStrictDerivAt_id (d i)).const_sub _
    have h2 := ((Real.hasStrictDerivAt_const_rpow (by norm_num : (0 : ℝ) < 4)
      ((e i : ℝ) - d i)).comp (d i) h1).const_mul (E i)
    exact ⟨_, HasStrictDerivAt.comp_hasStrictFDerivAt (f := fun x : ι → ℝ => x i) d h2
      (hasStrictFDerivAt_apply (𝕜 := ℝ) i d)⟩
  choose A' hA' using hterm
  exact ⟨_, (HasStrictFDerivAt.fun_sum (u := univ) fun i _ => hA' i).const_mul (1 / 12)⟩

omit [DecidableEq ι] in
/-- The cost (31) is strictly differentiable in the bit-widths. -/
lemma exists_hasStrictFDerivAt_sepCost (M M' : ι → ℝ) (d : ι → ℝ) :
    ∃ C' : StrongDual ℝ (ι → ℝ), HasStrictFDerivAt (sepCost univ M M') C' d := by
  have hsq : ∀ i, ∃ A' : StrongDual ℝ (ι → ℝ),
      HasStrictFDerivAt (fun x : ι → ℝ => M i * x i ^ 2) A' d := by
    intro i
    have h := (hasStrictDerivAt_pow 2 (d i)).const_mul (M i)
    exact ⟨_, HasStrictDerivAt.comp_hasStrictFDerivAt (f := fun x : ι → ℝ => x i) d h
      (hasStrictFDerivAt_apply (𝕜 := ℝ) i d)⟩
  have hlin : ∀ i, ∃ A' : StrongDual ℝ (ι → ℝ),
      HasStrictFDerivAt (fun x : ι → ℝ => M' i * x i) A' d :=
    fun i => ⟨_, (hasStrictFDerivAt_apply (𝕜 := ℝ) i d).const_mul (M' i)⟩
  choose A hA using hsq
  choose B hB using hlin
  exact ⟨_, ((HasStrictFDerivAt.fun_sum (u := univ) fun i _ => hA i).const_mul (1 / 2)).add
    (HasStrictFDerivAt.fun_sum (u := univ) fun i _ => hB i)⟩

/-- **Haas–Giles (2025), §6.1, pp. 11–12: (35) is necessary (Lagrange multipliers).**  "Minimising
`V^Δ_ℓ(d)` subject to a fixed `C̃_ℓ(d)` leads to the equation
`∂V^Δ_ℓ/∂d_{i,ℓ} + λ ∂C̃_ℓ/∂d_{i,ℓ} = 0` (35)": if the bit-widths `d*` are a local minimum of
the variance bound (26) among the bit-widths with the same cost (31), and the gradient of the cost
at `d*` is not zero, then there is a `λ` with
`−(log 4) E[x̄_i²] 4^{e_i − d*_i}/12 + λ (M_i d*_i + M'_i) = 0` for every variable `i`.  The proof
uses Mathlib's Lagrange multiplier theorem. -/
theorem eq35_of_isLocalMinOn (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ) {dstar : ι → ℝ}
    (hmin : IsLocalMinOn (vIndepR univ E e)
      {d | sepCost univ M M' d = sepCost univ M M' dstar} dstar)
    (hC : ∃ i, M i * dstar i + M' i ≠ 0) :
    ∃ lam : ℝ, ∀ i, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) +
      lam * (M i * dstar i + M' i) = 0 := by
  obtain ⟨V', hV'⟩ := exists_hasStrictFDerivAt_vIndepR E e dstar
  obtain ⟨C', hC'⟩ := exists_hasStrictFDerivAt_sepCost M M' dstar
  obtain ⟨a, b, hab, habeq⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d
      (show IsLocalExtrOn (vIndepR univ E e)
        {d | sepCost univ M M' d = sepCost univ M M' dstar} dstar from Or.inl hmin) hC' hV'
  -- the partial derivatives of `V_indep` and `C̃` are those of `MlmcLean.BitWidth`
  have hVi : ∀ i, V' (Pi.single i 1) =
      -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) := by
    intro i
    have h1 : HasDerivAt (fun t => vIndepR univ E e (Function.update dstar i t))
        (V' (Pi.single i 1)) (dstar i) :=
      hV'.hasFDerivAt.comp_hasDerivAt_of_eq (dstar i) (hasDerivAt_update dstar i (dstar i))
        (Function.update_eq_self i dstar).symm
    exact h1.unique (hasDerivAt_vIndepR_update univ E e dstar (Finset.mem_univ i) (dstar i))
  have hCi : ∀ i, C' (Pi.single i 1) = M i * dstar i + M' i := by
    intro i
    have h1 : HasDerivAt (fun t => sepCost univ M M' (Function.update dstar i t))
        (C' (Pi.single i 1)) (dstar i) :=
      hC'.hasFDerivAt.comp_hasDerivAt_of_eq (dstar i) (hasDerivAt_update dstar i (dstar i))
        (Function.update_eq_self i dstar).symm
    exact h1.unique (hasDerivAt_sepCost_update univ M M' dstar (Finset.mem_univ i) (dstar i))
  have hlin : ∀ i, a * (M i * dstar i + M' i) +
      b * -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) = 0 := by
    intro i
    rw [← hVi i, ← hCi i]
    have h := congrArg (fun L : StrongDual ℝ (ι → ℝ) => L (Pi.single i 1)) habeq
    simpa using h
  have hb : b ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hC
    have ha : a ≠ 0 := fun ha => hab (Prod.mk_eq_zero.2 ⟨ha, rfl⟩)
    have h0 := hlin i
    rw [zero_mul, add_zero] at h0
    exact hi ((mul_eq_zero.1 h0).resolve_left ha)
  refine ⟨a / b, fun i => ?_⟩
  have hl := hlin i
  generalize -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12) = v at hl ⊢
  generalize M i * dstar i + M' i = c at hl ⊢
  have h2 : b * (v + a / b * c) = a * c + b * v := by
    rw [show b * (v + a / b * c) = a / b * b * c + b * v by ring, div_mul_cancel₀ a hb]
  rw [hl] at h2
  exact (mul_eq_zero.1 h2).resolve_left hb

/-- **Haas–Giles (2025), §6.3, p. 14: equal marginal ratios at the optimum.**  "If an error was
'disproportionately' small, there would be potential for cost savings with a small increase in
the error": at a local minimum of the variance bound (26) among the bit-widths of the same cost
(31) (with a non-zero cost gradient), the marginal ratio
`(−∂V_indep/∂d_i) / (∂C̃/∂d_i)` of variance reduction to added cost is the same number `λ` for
every variable `i` with `∂C̃/∂d_i ≠ 0`. -/
theorem marginalRatio_eq_of_isLocalMinOn (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ)
    {dstar : ι → ℝ}
    (hmin : IsLocalMinOn (vIndepR univ E e)
      {d | sepCost univ M M' d = sepCost univ M M' dstar} dstar)
    (hC : ∃ i, M i * dstar i + M' i ≠ 0) :
    ∃ lam : ℝ, ∀ i, M i * dstar i + M' i ≠ 0 →
      Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - dstar i) / 12 / (M i * dstar i + M' i) = lam := by
  obtain ⟨lam, hlam⟩ := eq35_of_isLocalMinOn E e M M' hmin hC
  refine ⟨lam, fun i hi => ?_⟩
  rw [div_eq_iff hi]
  linarith [hlam i]

end necessity

/-! ### (37) and (38) -/

section eq37

variable {ι : Type*}

/-- **Haas–Giles (2025), §6.1, p. 12, (37).**  "For each uniform bit-width from 4 to 16, it
computes `λ` based on `∑_i ∂V^Δ_ℓ/∂d_{i,ℓ} + λ ∑_i ∂C̃_ℓ/∂d_{i,ℓ} = 0` (37)": at the uniform
bit-width `d_i = w`, with the partial derivatives of the bound (26) and of the cost (31), (37)
holds exactly for `λ = (∑_i (log 4) E[x̄_i²] 4^{e_i − w}/12) / ∑_i (M_i w + M'_i)`, when the
denominator is not zero. -/
theorem eq37_iff (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ) (w : ℝ)
    (hc : ∑ i ∈ s, (M i * w + M' i) ≠ 0) (lam : ℝ) :
    ∑ i ∈ s, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - w) / 12) +
        lam * ∑ i ∈ s, (M i * w + M' i) = 0 ↔
      lam = (∑ i ∈ s, Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - w) / 12) /
        ∑ i ∈ s, (M i * w + M' i) := by
  rw [Finset.sum_neg_distrib, eq_div_iff hc]
  constructor <;> intro h <;> linarith

/-- **Haas–Giles (2025), §6.1, p. 12: the multiplier of (37) is positive** when the second moments
`E[x̄_i²]` are non-negative, one of them positive, and the cost increases with the bit-widths. -/
theorem lambda37_pos (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ) (w : ℝ)
    (hE : ∀ i ∈ s, 0 ≤ E i) (hE' : ∃ i ∈ s, 0 < E i) (hc : 0 < ∑ i ∈ s, (M i * w + M' i)) :
    0 < (∑ i ∈ s, Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - w) / 12) /
      ∑ i ∈ s, (M i * w + M' i) := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine div_pos (Finset.sum_pos' (fun i hi => ?_) ?_) hc
  · exact div_nonneg (mul_nonneg (mul_nonneg hlog.le (hE i hi))
      (Real.rpow_nonneg (by norm_num) _)) (by norm_num)
  · obtain ⟨i, hi, hEi⟩ := hE'
    exact ⟨i, hi, div_pos (mul_pos (mul_pos hlog hEi)
      (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)⟩

/-- **Haas–Giles (2025), §6.1, p. 12: (37) is the sum of (35).**  If (35) holds for every variable
`i` with the same `λ`, then so does its sum over `i`, (37). -/
theorem eq37_of_eq35 (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ) (M M' : ι → ℝ) {lam : ℝ}
    {d : ι → ℝ}
    (h35 : ∀ i ∈ s, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - d i) / 12) +
      lam * (M i * d i + M' i) = 0) :
    ∑ i ∈ s, -(Real.log 4 * E i * (4 : ℝ) ^ ((e i : ℝ) - d i) / 12) +
      lam * ∑ i ∈ s, (M i * d i + M' i) = 0 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero h35

/-- Changing one coordinate of the argument of a separable sum changes the sum by the change of
that term. -/
lemma sum_update_sub_sum [DecidableEq ι] (s : Finset ι) (g : ι → ℝ → ℝ) (d : ι → ℝ) {i : ι}
    (hi : i ∈ s) (t : ℝ) :
    ∑ j ∈ s, g j (Function.update d i t j) - ∑ j ∈ s, g j (d j) = g i t - g i (d i) := by
  rw [← Finset.sum_sub_distrib,
    ← Finset.add_sum_erase s (fun j => g j (Function.update d i t j) - g j (d j)) hi,
    Function.update_self, Finset.sum_eq_zero, add_zero]
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), sub_self]

/-- **Haas–Giles (2025), §6.3, p. 13: one more bit divides the squared rounding error by 4.**
"`d_{S,ℓ+1} = d_{S,ℓ} + 1` is equivalent to division by 4 in the corresponding squared rounding
error": `4^{e − (d + 1)} = 4^{e − d}/4`. -/
theorem rpow_four_sub_add_one (e d : ℝ) :
    (4 : ℝ) ^ (e - (d + 1)) = (4 : ℝ) ^ (e - d) / 4 := by
  rw [show e - (d + 1) = (e - d) - 1 by ring, Real.rpow_sub (by norm_num : (0 : ℝ) < 4),
    Real.rpow_one]

/-- **Haas–Giles (2025), §6.2, p. 13, (38): the numerator.**  Adding one bit to the variable `x_i`
lowers the bound (26) by `E[x̄_i²] 4^{e_i − d_i}/16`, which depends on `d_i` only. -/
theorem vIndepR_sub_update_add_one [DecidableEq ι] (s : Finset ι) (E : ι → ℝ) (e : ι → ℤ)
    (d : ι → ℝ) {i : ι} (hi : i ∈ s) :
    vIndepR s E e d - vIndepR s E e (Function.update d i (d i + 1)) =
      E i * (4 : ℝ) ^ ((e i : ℝ) - d i) / 16 := by
  have h := sum_update_sub_sum s (fun j x => E j * (4 : ℝ) ^ ((e j : ℝ) - x)) d hi (d i + 1)
  rw [rpow_four_sub_add_one,
    show E i * ((4 : ℝ) ^ ((e i : ℝ) - d i) / 4) - E i * (4 : ℝ) ^ ((e i : ℝ) - d i) =
      -(3 / 4) * (E i * (4 : ℝ) ^ ((e i : ℝ) - d i)) by ring] at h
  unfold vIndepR
  linarith

/-- **Haas–Giles (2025), §6.2, p. 13, (38): the denominator.**  Adding one bit to the variable
`x_i` raises the cost (31) by `M_i (d_i + ½) + M'_i`, which depends on `d_i` only; so the ratio
(38) of the two is uncoupled. -/
theorem sepCost_update_add_one_sub [DecidableEq ι] (s : Finset ι) (M M' : ι → ℝ) (d : ι → ℝ)
    {i : ι} (hi : i ∈ s) :
    sepCost s M M' (Function.update d i (d i + 1)) - sepCost s M M' d =
      M i * (d i + 1 / 2) + M' i := by
  have h := sum_update_sub_sum s (fun j x => M j * x ^ 2) d hi (d i + 1)
  have h' := sum_update_sub_sum s (fun j x => M' j * x) d hi (d i + 1)
  rw [show M i * (d i + 1) ^ 2 - M i * d i ^ 2 = 2 * (M i * (d i + 1 / 2)) by ring] at h
  rw [show M' i * (d i + 1) - M' i * d i = M' i by ring] at h'
  unfold sepCost
  linarith

/-- The bound `(1/12) E[x̄²] 4^{e − d}` on the expected squared rounding error of a variable is its
variance factor `(1/12) E[x̄²] 4^e` (Haas–Giles 2025, §6.3, Figures 6 and 7) times `4^{−d}`. -/
lemma errorBound_eq_factor_mul (E e d : ℝ) :
    (1 / 12) * E * (4 : ℝ) ^ (e - d) = ((1 / 12) * E * (4 : ℝ) ^ e) * (4 : ℝ) ^ (-d) := by
  rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
  ring

/-- **Haas–Giles (2025), §6.3, p. 13: the error bounds halve at every level.**  "Looking at the
variance factors `(1/12) E[x̄_i²] 4^{e_{i,ℓ}}` in Figure 6, for variables `S` and `mul2` we notice
that the factors are approximately multiplied by 2 at every level.  Therefore, using the fact that
`d_{S,ℓ+1} = d_{S,ℓ} + 1` is equivalent to division by 4 in the corresponding squared rounding
error, the bound on the average error `E[S̄_i² δS_i²]` is divided by 2 at every level."  If the
factors `F_ℓ` double and `d_{ℓ+1} = d_ℓ + 1`, the bounds `F_ℓ 4^{−d_ℓ}` halve
(`errorBound_eq_factor_mul`). -/
theorem errorBound_succ {F d : ℕ → ℝ} (hF : ∀ ℓ, F (ℓ + 1) = 2 * F ℓ)
    (hd : ∀ ℓ, d (ℓ + 1) = d ℓ + 1) (ℓ : ℕ) :
    F (ℓ + 1) * (4 : ℝ) ^ (-d (ℓ + 1)) = F ℓ * (4 : ℝ) ^ (-d ℓ) / 2 := by
  rw [hF, hd, show -(d ℓ + 1) = -d ℓ - 1 by ring, Real.rpow_sub (by norm_num : (0 : ℝ) < 4),
    Real.rpow_one]
  ring

/-- **Haas–Giles (2025), §6.3, pp. 13–14: the error bounds decay like the time step.**  Under the
hypotheses of `errorBound_succ`, the bound on level `ℓ` is `2^{−ℓ}` times the bound on level 0,
i.e. proportional to the time step `h_ℓ = 2^{−ℓ} h_0`: "the precision evolves with level such that
the net error evolves like the time step `h`". -/
theorem errorBound_eq_div_pow {F d : ℕ → ℝ} (hF : ∀ ℓ, F (ℓ + 1) = 2 * F ℓ)
    (hd : ∀ ℓ, d (ℓ + 1) = d ℓ + 1) (ℓ : ℕ) :
    F ℓ * (4 : ℝ) ^ (-d ℓ) = F 0 * (4 : ℝ) ^ (-d 0) / 2 ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ n ih => rw [errorBound_succ hF hd, ih, div_div, ← pow_succ]

/-- **Haas–Giles (2025), §6.3, p. 14: the share of each variable is constant over levels.**  "The
portion of the overall error due to a certain variable is constant over levels": if the bounds
`B_ℓ(i)` of all variables halve from level `ℓ` to level `ℓ + 1`, the share
`B_ℓ(i) / ∑_j B_ℓ(j)` of each variable does not change. -/
theorem errorShare_succ {s : Finset ι} {B : ℕ → ι → ℝ}
    (hB : ∀ ℓ, ∀ i ∈ s, B (ℓ + 1) i = B ℓ i / 2) (ℓ : ℕ) {i : ι} (hi : i ∈ s) :
    B (ℓ + 1) i / ∑ j ∈ s, B (ℓ + 1) j = B ℓ i / ∑ j ∈ s, B ℓ j := by
  rw [hB ℓ i hi, Finset.sum_congr rfl (hB ℓ), ← Finset.sum_div]
  ring

end eq37

/-! ### §4.3: the size of the look-up table -/

section lut

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Haas–Giles (2025), §4.3, p. 10: the size of the LUT.**  "To integrate both approximate
random variables and fixed-point arithmetic, in practice at each level after the bit-widths for
all variables (including `Z`) are optimised we can for instance choose the size of the LUT such
that the term containing the MSE in (28) is smaller or equal to `V_indep`."  With that choice, the
variance of the linearised error is at most `2 V_indep` (from the corrected (28),
`variance_extended_indep`). -/
theorem variance_extended_le_two_mul {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (xbar δ : ι → Ω → ℝ) (zbar δZ : κ → Ω → ℝ) (e : ι → ℤ) (d : ι → ℕ) (mse : ℝ)
    (hxbar : ∀ i ∈ s, MemLp (xbar i) 2 μ)
    (hδ : ∀ i ∈ s, pdf.IsUniform (δ i)
      (Set.Icc (-(2 : ℝ) ^ (e i - d i - 1)) ((2 : ℝ) ^ (e i - d i - 1))) μ)
    (hzbar : ∀ j ∈ t, AEStronglyMeasurable (zbar j) μ)
    (hδZ : ∀ j ∈ t, AEStronglyMeasurable (δZ j) μ)
    (hZ : ∀ j ∈ t, MemLp (fun ω => zbar j ω * δZ j ω) 2 μ)
    (hmse : ∀ j ∈ t, ∫ ω, δZ j ω ^ 2 ∂μ = mse)
    (hind_x : ∀ i ∈ s, IndepFun (xbar i) (δ i) μ)
    (hind_z : ∀ j ∈ t, IndepFun (zbar j) (δZ j) μ)
    (hind : Set.Pairwise ↑(s.disjSum t) fun a b =>
      IndepFun (fun ω => Sum.elim xbar zbar a ω * Sum.elim δ δZ a ω)
        (fun ω => Sum.elim xbar zbar b ω * Sum.elim δ δZ b ω) μ)
    (hLUT : (∑ j ∈ t, ∫ ω, zbar j ω ^ 2 ∂μ) * mse ≤
      vIndep s (fun i => ∫ ω, xbar i ω ^ 2 ∂μ) e d) :
    variance (fun ω => ∑ i ∈ s, xbar i ω * δ i ω + ∑ j ∈ t, zbar j ω * δZ j ω) μ ≤
      2 * vIndep s (fun i => ∫ ω, xbar i ω ^ 2 ∂μ) e d := by
  have h := variance_extended_indep s t xbar δ zbar δZ e d mse hxbar hδ hzbar hδZ hZ hmse
    hind_x hind_z hind
  linarith

end lut

end MLMC
