import MlmcLean.LagrangeBitWidth
import MlmcLean.GBMEulerMaruyama

/-!
# Haas–Giles §6: the cost factor, the size of the variables and fixed precision

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §6.1 (pp. 11–13, (32)–(34), Figures 3 and 5) and §6.3
(pp. 13–14, (39)–(41)), with the rounding-error model of §4 (pp. 8–9, (22) and (26)).  This file
completes three remarks of §6 that `MlmcLean.LagrangeBitWidth` and `MlmcLean.FixedPointPath` prove
only in part.

* **The cost factor of Figures 3 and 5** (§6.1, p. 12: "the cost factor for both uniform and
  optimised bit-widths is smaller than 1 which means that the nested framework is cheaper than the
  standard Multilevel Monte Carlo").  The plotted factor is (34) divided by the standard level
  cost `√(V_ℓ C_ℓ)`, i.e. `√(C̃_ℓ/C_ℓ) + √(V^Δ_ℓ/V_ℓ)` (`levelCost34_eq_mul_costFactor`); the
  captions of Figures 3 and 5 print `√(Ṽ/V)` for `√(V^Δ/V)`.  If the factor is at most `ρ` on
  every level, the cost `ε⁻² (∑_ℓ (34))²` is at most `ρ²` times the standard cost (8), and the
  nested cost (32) (with `Ṽ_ℓ = V_ℓ`, `C^Δ_ℓ = C_ℓ + C̃_ℓ`) at most `ρ² (1 + ρ²)` times (8)
  (`nestedCost_le_of_costFactor_le`); so (34)'s cost is smaller than (8) when `ρ < 1`, and (32)
  is smaller than (8) when `ρ² (1 + ρ²) < 1` (`nestedCost_lt_of_costFactor_le`).  A factor
  below 1 alone does not make (32) smaller than (8): with `C̃_ℓ/C_ℓ = 9/16`,
  `V^Δ_ℓ/V_ℓ = 36/625` the factor is `99/100` and (32) is `(21/20)²` times (8)
  (`exists_costFactor_lt_one_nestedCost_gt`).
* **The size of the variables, (39)–(41)** (§6.3, p. 13: "`con2, mul1, sum1, mul2 ∼ √h`,
  `con1 ∼ h`, `S ∼ 1`.  The takeaway is that the variables `S_i` are the largest").  With
  independent centred increments `Z̃_i`: the exact second moments `E[mul1_i²] = σ² h E[Z̃_i²]`,
  `E[sum1_i²] = r² h² + σ² h E[Z̃_i²]` (`integral_sq_mul1_sum1_eq`),
  `E[S_n] = S_0 (1 + rh)ⁿ` (`integral_gbmPath_eq`), `E[S_i²] = S_0² ((1 + rh)² + σ² h v)^i` and
  `E[mul2_i²] = S_0² ((1 + rh)² + σ² h v)^i (r² h² + σ² h v)` when `E[Z̃_i²] = v`
  (`integral_sq_gbmPath_mul2_eq_pow`); the two-sided bounds that make "`∼`" precise over a time
  horizon `nh ≤ T` (`integral_sq_mul1_sum1_bounds`, `gbmPath_size_bounds`,
  `integral_sq_mul2_bounds`); and the comparison: for small `h` the mean squares of `con1, con2,
  mul1_i, sum1_i, mul2_i` are all smaller than that of `S_n` (`gbmPath_sq_largest`).
* **Fixed precision** (§6.3, p. 14: "if the bit-widths in the low precision path generation were
  fixed, starting at a certain level, the accuracy would decrease … for small time steps the
  rounding errors due to the finite precision are relatively large").  Under the model (22) with
  independent errors, the bound (26) is an equality (`variance_linearised_indep_eq`), so `N`
  rounding errors of fixed precision with sensitivities `E[x̄_i²] ≥ c` have variance at least
  `N c 4^{e−d}/12` (`variance_linearised_indep_ge`).  For the path of Algorithm 1 with `S` rounded
  after every step and rounding errors `ρ_k` uniform on `[−2^{e−d−1}, 2^{e−d−1}]`, the error
  `S̃_n − S_n` has mean 0 and variance exactly `V_indep`, with the sensitivities
  `x̄_k = ∂S_n/∂S_{k+1}` (`perturbed_path_sub_mean_variance`); its mean square lies between
  `n (4^{e−d}/12) e^{−4|r|T}` and `n (4^{e−d}/12) e^{(2|r| + r² + σ²)T}`
  (`integral_sq_perturbed_path_sub_bounds`), i.e. it is of order `h⁻¹ 4^{e−d}` for `n = T/h`; and
  once `h` is small it exceeds the mean-square discretisation error `E[(S_T − S_n)²] ≤ C(T) h`
  of `gbm_em_strong_error` (`strongError_lt_integral_sq_perturbed_path_sub`).
-/

open Finset MeasureTheory ProbabilityTheory

namespace MLMC

/-! ### §6.1: the cost factor of Figures 3 and 5 -/

section costFactor

/-- **Haas–Giles (2025), §6.1, pp. 12–13: the cost factor of Figures 3 and 5.**  "Figure 3 shows
the level cost (34) versus `λ`" (p. 12), where (34) is `√(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ)`; divided by the
standard level cost `√(V_ℓ C_ℓ)` of (8) it is the factor `√(C̃_ℓ/C_ℓ) + √(V^Δ_ℓ/V_ℓ)` plotted in
Figures 3 and 5 (for `V_ℓ, C_ℓ > 0`).  The captions of Figures 3 and 5 print
"`√(C̃/C) + √(Ṽ/V)`": this is a typo for `√(C̃/C) + √(V^Δ/V)`, since with the paper's assumption
`Ṽ_ℓ ≈ V_ℓ` (§6, p. 11) the printed expression would be at least about 1, while the plotted values
lie between 0.1 and 0.4 (Figure 5). -/
theorem levelCost34_eq_mul_costFactor {V Vd C Ct : ℝ} (hV : 0 < V) (hC : 0 < C) :
    Real.sqrt (V * Ct) + Real.sqrt (Vd * C) =
      Real.sqrt (V * C) * (Real.sqrt (Ct / C) + Real.sqrt (Vd / V)) := by
  have h1 : Real.sqrt (V * Ct) = Real.sqrt (V * C) * Real.sqrt (Ct / C) := by
    rw [← Real.sqrt_mul (mul_pos hV hC).le]
    congr 1
    field_simp
  have h2 : Real.sqrt (Vd * C) = Real.sqrt (V * C) * Real.sqrt (Vd / V) := by
    rw [← Real.sqrt_mul (mul_pos hV hC).le]
    congr 1
    field_simp
  rw [h1, h2, mul_add]

/-- **Haas–Giles (2025), §6.1, p. 12: a cost factor `ρ` on every level saves the factor `ρ²`.**
"The numerical results in Figure 5 show that the cost factor for both uniform and optimised
bit-widths is smaller than 1 which means that the nested framework is cheaper than the standard
Multilevel Monte Carlo."  Let `V_ℓ, C_ℓ > 0`, `C̃_ℓ ≥ 0` and let the cost factor
`√(C̃_ℓ/C_ℓ) + √(V^Δ_ℓ/V_ℓ)` of Figures 3 and 5 be at most `ρ` on every level `ℓ ≤ L`
(`levelCost34_eq_mul_costFactor`).  Then

* the cost `ε⁻² (∑_ℓ √(V_ℓ C̃_ℓ) + √(V^Δ_ℓ C_ℓ))²` built from the approximation (34) is at most
  `ρ²` times the standard MLMC cost (8), `ε⁻² (∑_ℓ √(V_ℓ C_ℓ))²`;
* the nested cost (32), `ε⁻² (∑_ℓ √(Ṽ_ℓ C̃_ℓ) + √(V^Δ_ℓ C^Δ_ℓ))²` with `Ṽ_ℓ = V_ℓ` and
  `C^Δ_ℓ = C_ℓ + C̃_ℓ` (§6, p. 11 and §2.2, p. 4), is at most `ρ² (1 + ρ²)` times (8).

The second bound is the first one times the factor `1 + r` of `totalCost32_bounds` with `r = ρ²`,
since `C̃_ℓ/C_ℓ ≤ ρ²`; unlike `totalCost32_bounds`, all hypotheses are only required on the levels
`ℓ ≤ L`.  The total saving
is thus the square of the level factor: the paper's "factor 7 in computational cost savings at
level 0" (for a level factor about `1/7`) is the saving in the level's contribution
`√(V_ℓ C_ℓ)` to the square root of the cost (8). -/
theorem nestedCost_le_of_costFactor_le (L : ℕ) {V Vd C Ct : ℕ → ℝ} {ε ρ : ℝ}
    (hV : ∀ ℓ ∈ range (L + 1), 0 < V ℓ) (hC : ∀ ℓ ∈ range (L + 1), 0 < C ℓ)
    (hCt : ∀ ℓ ∈ range (L + 1), 0 ≤ Ct ℓ)
    (hρ : ∀ ℓ ∈ range (L + 1), Real.sqrt (Ct ℓ / C ℓ) + Real.sqrt (Vd ℓ / V ℓ) ≤ ρ) :
    (ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ))) ^ 2 ≤
        ρ ^ 2 * ((ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) ∧
      (ε ^ 2)⁻¹ *
          (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ)))) ^ 2 ≤
        ρ ^ 2 * (1 + ρ ^ 2) * ((ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) := by
  have hL : 0 ∈ range (L + 1) := Finset.mem_range.2 (Nat.succ_pos L)
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) (hρ 0 hL)
  -- (34) is at most `ρ √(V_ℓ C_ℓ)` on every level
  have h34 : ∀ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ) ≤
      ρ * Real.sqrt (V ℓ * C ℓ) := fun ℓ hℓ => by
    rw [levelCost34_eq_mul_costFactor (hV ℓ hℓ) (hC ℓ hℓ), mul_comm ρ]
    exact mul_le_mul_of_nonneg_left (hρ ℓ hℓ) (Real.sqrt_nonneg _)
  -- `C̃_ℓ/C_ℓ ≤ ρ²` on every level
  have hr : ∀ ℓ ∈ range (L + 1), Ct ℓ / C ℓ ≤ ρ ^ 2 := fun ℓ hℓ => by
    have h1 : Real.sqrt (Ct ℓ / C ℓ) ≤ ρ :=
      le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (hρ ℓ hℓ)
    calc Ct ℓ / C ℓ = Real.sqrt (Ct ℓ / C ℓ) ^ 2 :=
          (Real.sq_sqrt (div_nonneg (hCt ℓ hℓ) (hC ℓ hℓ).le)).symm
      _ ≤ ρ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  -- (33) is at most `√(1 + ρ²) ρ √(V_ℓ C_ℓ)` on every level
  have h33 : ∀ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ)) ≤
      Real.sqrt (1 + ρ ^ 2) * ρ * Real.sqrt (V ℓ * C ℓ) := fun ℓ hℓ => by
    rw [mul_assoc]
    exact (levelCost33_le_sqrt_mul (hC ℓ hℓ) (hCt ℓ hℓ)).trans
      (mul_le_mul (Real.sqrt_le_sqrt (by linarith [hr ℓ hℓ])) (h34 ℓ hℓ) (by positivity)
        (Real.sqrt_nonneg _))
  have hA0 : 0 ≤ ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) :=
    Finset.sum_nonneg fun ℓ _ => Real.sqrt_nonneg _
  have hs34 : ∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ)) ≤
      ρ * ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum h34
  have hs33 : ∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ))) ≤
      Real.sqrt (1 + ρ ^ 2) * ρ * ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum h33
  have hε : 0 ≤ (ε ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg ε)
  generalize ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) = A at hA0 hs34 hs33 ⊢
  constructor
  · calc (ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ))) ^ 2
        ≤ (ε ^ 2)⁻¹ * (ρ * A) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Finset.sum_nonneg fun ℓ _ => by positivity) hs34 2) hε
      _ = ρ ^ 2 * ((ε ^ 2)⁻¹ * A ^ 2) := by ring
  · calc (ε ^ 2)⁻¹ *
          (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ)))) ^ 2
        ≤ (ε ^ 2)⁻¹ * (Real.sqrt (1 + ρ ^ 2) * ρ * A) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Finset.sum_nonneg fun ℓ _ => by positivity) hs33 2) hε
      _ = ρ ^ 2 * (1 + ρ ^ 2) * ((ε ^ 2)⁻¹ * A ^ 2) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          ring

/-- **Haas–Giles (2025), §6.1, p. 12: "the nested framework is cheaper than the standard
Multilevel Monte Carlo".**  Under the hypotheses of `nestedCost_le_of_costFactor_le` and for
`ε ≠ 0`: if the cost factor `√(C̃_ℓ/C_ℓ) + √(V^Δ_ℓ/V_ℓ)` of every level is at most `ρ < 1`, the
cost `ε⁻² (∑_ℓ (34))²` is strictly smaller than the standard cost (8); and if
`ρ² (1 + ρ²) < 1` (e.g. `ρ ≤ 3/4`; the values of Figure 5 are below `0.4`), so is the nested cost
(32) with `Ṽ_ℓ = V_ℓ` and `C^Δ_ℓ = C_ℓ + C̃_ℓ`.  The paper's inference from "smaller than 1"
holds for (34) but needs the extra margin for (32): see
`exists_costFactor_lt_one_nestedCost_gt`. -/
theorem nestedCost_lt_of_costFactor_le (L : ℕ) {V Vd C Ct : ℕ → ℝ} {ε ρ : ℝ} (hε : ε ≠ 0)
    (hV : ∀ ℓ ∈ range (L + 1), 0 < V ℓ) (hC : ∀ ℓ ∈ range (L + 1), 0 < C ℓ)
    (hCt : ∀ ℓ ∈ range (L + 1), 0 ≤ Ct ℓ)
    (hρ : ∀ ℓ ∈ range (L + 1), Real.sqrt (Ct ℓ / C ℓ) + Real.sqrt (Vd ℓ / V ℓ) ≤ ρ) :
    (ρ < 1 →
      (ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * C ℓ))) ^ 2 <
        (ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) ∧
    (ρ ^ 2 * (1 + ρ ^ 2) < 1 →
      (ε ^ 2)⁻¹ *
          (∑ ℓ ∈ range (L + 1), (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ)))) ^ 2 <
        (ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) := by
  obtain ⟨h1, h2⟩ := nestedCost_le_of_costFactor_le (ε := ε) L hV hC hCt hρ
  have hL : 0 ∈ range (L + 1) := Finset.mem_range.2 (Nat.succ_pos L)
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) (hρ 0 hL)
  -- the standard cost (8) is positive
  have hA : 0 < ∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ) :=
    Finset.sum_pos (fun ℓ hℓ => Real.sqrt_pos.2 (mul_pos (hV ℓ hℓ) (hC ℓ hℓ))) ⟨0, hL⟩
  have hB : 0 < (ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 := by positivity
  refine ⟨fun hρ1 => ?_, fun hρ1 => ?_⟩
  · have hρ2 : ρ ^ 2 < 1 := by nlinarith
    calc _ ≤ ρ ^ 2 * ((ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) := h1
      _ < _ := by nlinarith
  · calc _ ≤ ρ ^ 2 * (1 + ρ ^ 2) *
          ((ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2) := h2
      _ < _ := by nlinarith

/-- **Haas–Giles (2025), §6.1, p. 12: a cost factor below 1 does not by itself make (32) cheaper
than (8).**  The inference "the cost factor … is smaller than 1 which means that the nested
framework is cheaper" is exact for the approximation (34) (`nestedCost_lt_of_costFactor_le`) but
not for the nested cost (32) with `Ṽ_ℓ = V_ℓ`, `C^Δ_ℓ = C_ℓ + C̃_ℓ`: with `V_ℓ = C_ℓ = 1`,
`C̃_ℓ = 9/16` and `V^Δ_ℓ = 36/625` on every level the factor is `3/4 + 6/25 = 99/100 < 1`, but
the level cost (33) is `3/4 + 3/10 = 21/20 > 1 = √(V_ℓ C_ℓ)`, so for every `L` and `ε ≠ 0` the
nested cost (32) exceeds the standard cost (8) by the factor `(21/20)²`.  This is the regime of
the paper's own caveat (p. 12): "the assumption `C̃_ℓ ≪ C_ℓ` might not be relevant for all levels
as the cost of the fixed-point operations becomes comparable to the cost of the path generation
on the CPU". -/
theorem exists_costFactor_lt_one_nestedCost_gt :
    ∃ V Vd C Ct : ℕ → ℝ, (∀ ℓ, 0 < V ℓ ∧ 0 < C ℓ ∧ 0 ≤ Vd ℓ ∧ 0 ≤ Ct ℓ ∧
        Real.sqrt (Ct ℓ / C ℓ) + Real.sqrt (Vd ℓ / V ℓ) < 1) ∧
      ∀ (L : ℕ) {ε : ℝ}, ε ≠ 0 →
        (ε ^ 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (V ℓ * C ℓ)) ^ 2 <
          (ε ^ 2)⁻¹ *
            (∑ ℓ ∈ range (L + 1),
              (Real.sqrt (V ℓ * Ct ℓ) + Real.sqrt (Vd ℓ * (C ℓ + Ct ℓ)))) ^ 2 := by
  have e1 : Real.sqrt ((9 / 16 : ℝ) / 1) = 3 / 4 := by
    rw [div_one, show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e2 : Real.sqrt ((36 / 625 : ℝ) / 1) = 6 / 25 := by
    rw [div_one, show (36 / 625 : ℝ) = (6 / 25) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e3 : Real.sqrt ((1 : ℝ) * 1) = 1 := by rw [mul_one, Real.sqrt_one]
  have e4 : Real.sqrt ((1 : ℝ) * (9 / 16)) = 3 / 4 := by
    rw [one_mul, show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e5 : Real.sqrt ((36 / 625 : ℝ) * (1 + 9 / 16)) = 3 / 10 := by
    rw [show (36 / 625 : ℝ) * (1 + 9 / 16) = (3 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨fun _ => 1, fun _ => 36 / 625, fun _ => 1, fun _ => 9 / 16,
    fun ℓ => ⟨one_pos, one_pos, by norm_num, by norm_num, ?_⟩, fun L ε hε => ?_⟩
  · rw [e1, e2]
    norm_num
  · simp only [e3, e4, e5, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hε2 : 0 < (ε ^ 2)⁻¹ := by positivity
    have hL : (0 : ℝ) < L + 1 := by positivity
    refine mul_lt_mul_of_pos_left ?_ hε2
    push_cast
    nlinarith

end costFactor

/-! ### §6.3: the size of the variables, (39)–(41) -/

/-- `e^{−2|x|} ≤ 1 + x` for `|x| ≤ 1/2`. -/
lemma exp_neg_two_mul_abs_le_one_add {x : ℝ} (hx : |x| ≤ 1 / 2) :
    Real.exp (-(2 * |x|)) ≤ 1 + x := by
  rcases le_or_gt 0 x with h0 | h0
  · have : Real.exp (-(2 * |x|)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [abs_nonneg x])
    linarith
  · rw [abs_of_neg h0] at hx ⊢
    have h1 : 1 - 2 * x ≤ Real.exp (-(2 * x)) := by linarith [Real.add_one_le_exp (-(2 * x))]
    have h2 : Real.exp (2 * x) * Real.exp (-(2 * x)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : 0 ≤ -x * (1 + 2 * x) := mul_nonneg (by linarith) (by linarith)
    have hpos := Real.exp_pos (2 * x)
    have hx2 : 0 < 1 - 2 * x := by linarith
    rw [show -(2 * -x) = 2 * x by ring]
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]

/-- The mean of `k` Euler factors stays of order 1: `e^{−2|r|T} ≤ (1 + rh)^k` when
`|r| h ≤ 1/2`, `h ≥ 0` and `kh ≤ T`. -/
lemma exp_neg_le_one_add_pow {r h T : ℝ} (hh : 0 ≤ h) (hrh : |r| * h ≤ 1 / 2) {k : ℕ}
    (hk : k * h ≤ T) : Real.exp (-(2 * |r| * T)) ≤ (1 + r * h) ^ k := by
  have habs : |r * h| = |r| * h := by rw [abs_mul, abs_of_nonneg hh]
  have h1 : Real.exp (-(2 * (|r| * h))) ≤ 1 + r * h := by
    rw [← habs]
    exact exp_neg_two_mul_abs_le_one_add (by rw [habs]; exact hrh)
  calc Real.exp (-(2 * |r| * T)) ≤ Real.exp (k * -(2 * (|r| * h))) := by
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 2 * |r|)
        nlinarith
    _ = Real.exp (-(2 * (|r| * h))) ^ k := Real.exp_nat_mul _ k
    _ ≤ (1 + r * h) ^ k := pow_le_pow_left₀ (Real.exp_pos _).le h1 k

/-- `e^{−4|r|T} ≤ ∏_{j ∈ s} M_j` when every `M_j ≥ (1 + rh)²`, `|r| h ≤ 1/2`, `h ≥ 0` and
`|s| h ≤ T`. -/
lemma exp_neg_le_prod {M : ℕ → ℝ} {r h T : ℝ} (hh : 0 ≤ h) (hrh : |r| * h ≤ 1 / 2)
    (hM : ∀ j, (1 + r * h) ^ 2 ≤ M j) (s : Finset ℕ) (hs : s.card * h ≤ T) :
    Real.exp (-(4 * |r| * T)) ≤ ∏ j ∈ s, M j := by
  have h1 := exp_neg_le_one_add_pow hh hrh hs
  calc Real.exp (-(4 * |r| * T)) = Real.exp (-(2 * |r| * T)) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ ≤ ((1 + r * h) ^ s.card) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le h1 2
    _ = ∏ _j ∈ s, (1 + r * h) ^ 2 := by
        rw [Finset.prod_const, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ ∏ j ∈ s, M j := Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun j _ => hM j

section size

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `E[(a + bY)²] = a² + b² E[Y²]` for a centred square-integrable `Y`. -/
lemma integral_sq_affine_eq {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (a b : ℝ) : ∫ ω, (a + b * Y ω) ^ 2 ∂μ = a ^ 2 + b ^ 2 * ∫ ω, Y ω ^ 2 ∂μ := by
  have hint : Integrable Y μ := hY.integrable one_le_two
  have hi1 : Integrable (fun ω => 2 * a * b * Y ω) μ := hint.const_mul _
  have hi2 : Integrable (fun ω => b ^ 2 * Y ω ^ 2) μ := hY.integrable_sq.const_mul _
  have hi12 : Integrable (fun ω => 2 * a * b * Y ω + b ^ 2 * Y ω ^ 2) μ := hi1.add hi2
  have hexp : (fun ω => (a + b * Y ω) ^ 2) =
      fun ω => a ^ 2 + (2 * a * b * Y ω + b ^ 2 * Y ω ^ 2) := by
    funext ω
    ring
  rw [hexp, integral_add (integrable_const _) hi12, integral_add hi1 hi2,
    integral_const, integral_const_mul, integral_const_mul, hmean]
  simp

/-- The second moment of one factor `1 + sum1_i` of the path of Algorithm 1:
`E[(1 + rh + √h σ Z̃)²] = (1 + rh)² + σ² h E[Z̃²]` for a centred increment `Z̃`. -/
lemma integral_sq_factor_eq {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ ω, (1 + r * h + Real.sqrt h * σ * Y ω) ^ 2 ∂μ =
      (1 + r * h) ^ 2 + σ ^ 2 * h * ∫ ω, Y ω ^ 2 ∂μ := by
  rw [integral_sq_affine_eq hY hmean (1 + r * h) (Real.sqrt h * σ), mul_pow, Real.sq_sqrt hh]
  ring

/-- **Haas–Giles (2025), §6.3, p. 13, (39) for `mul1` and `sum1`, exactly.**  "Assume that
`h ≪ √h` and `σ, r, S_0, Z_i = O(1)`, then we obtain `con2, mul1, sum1, mul2 ∼ √h` (39)."  For a
centred square-integrable increment `Y = Z̃_i` and `h ≥ 0`, the variables `mul1_i = con2 × Z̃_i =
√h σ Z̃_i` and `sum1_i = con1 + mul1_i = rh + √h σ Z̃_i` of Algorithm 1 have the exact second
moments `E[mul1_i²] = σ² h E[Z̃_i²]` and `E[sum1_i²] = r² h² + σ² h E[Z̃_i²]`. -/
theorem integral_sq_mul1_sum1_eq {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ ω, (Real.sqrt h * σ * Y ω) ^ 2 ∂μ = σ ^ 2 * h * ∫ ω, Y ω ^ 2 ∂μ ∧
      ∫ ω, (r * h + Real.sqrt h * σ * Y ω) ^ 2 ∂μ =
        r ^ 2 * h ^ 2 + σ ^ 2 * h * ∫ ω, Y ω ^ 2 ∂μ := by
  have hs : (Real.sqrt h * σ) ^ 2 = σ ^ 2 * h := by
    rw [mul_pow, Real.sq_sqrt hh]
    ring
  refine ⟨?_, ?_⟩
  · have e : ∀ ω, (Real.sqrt h * σ * Y ω) ^ 2 = σ ^ 2 * h * Y ω ^ 2 := fun ω => by
      rw [mul_pow, hs]
    simp_rw [e]
    exact integral_const_mul _ _
  · rw [integral_sq_affine_eq hY hmean, hs, mul_pow]

/-- **Haas–Giles (2025), §6.3, p. 13, (39) for `mul1` and `sum1`: "`mul1, sum1 ∼ √h`",
two-sided.**  If the increment `Y = Z̃_i` is centred with `m ≤ E[Z̃_i²] ≤ 1` (`m = 1` for normal
increments) and `0 ≤ h ≤ 1`, then `m σ² h ≤ E[mul1_i²] ≤ σ² h` and
`m σ² h ≤ E[sum1_i²] ≤ (r² + σ²) h`: both have mean square of exact order `h` when `σ ≠ 0` and
`m > 0` (the upper bounds are `integral_sq_mul1_le` and `integral_sq_sum1_le`). -/
theorem integral_sq_mul1_sum1_bounds {Y : Ω → ℝ} (hY : MemLp Y 2 μ)
    (hmean : ∫ ω, Y ω ∂μ = 0) {m : ℝ} (hm : m ≤ ∫ ω, Y ω ^ 2 ∂μ) (hvar : ∫ ω, Y ω ^ 2 ∂μ ≤ 1)
    (r σ : ℝ) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    m * σ ^ 2 * h ≤ ∫ ω, (Real.sqrt h * σ * Y ω) ^ 2 ∂μ ∧
      ∫ ω, (Real.sqrt h * σ * Y ω) ^ 2 ∂μ ≤ σ ^ 2 * h ∧
      m * σ ^ 2 * h ≤ ∫ ω, (r * h + Real.sqrt h * σ * Y ω) ^ 2 ∂μ ∧
      ∫ ω, (r * h + Real.sqrt h * σ * Y ω) ^ 2 ∂μ ≤ (r ^ 2 + σ ^ 2) * h := by
  obtain ⟨h1, h2⟩ := integral_sq_mul1_sum1_eq hY hmean r σ hh0
  have hσh : 0 ≤ σ ^ 2 * h := mul_nonneg (sq_nonneg σ) hh0
  have hlow : m * σ ^ 2 * h ≤ σ ^ 2 * h * ∫ ω, Y ω ^ 2 ∂μ :=
    calc m * σ ^ 2 * h = σ ^ 2 * h * m := by ring
      _ ≤ σ ^ 2 * h * ∫ ω, Y ω ^ 2 ∂μ := mul_le_mul_of_nonneg_left hm hσh
  refine ⟨h1 ▸ hlow, integral_sq_mul1_le hvar hh0, ?_, integral_sq_sum1_le hY hmean hvar hh0 hh1⟩
  rw [h2]
  nlinarith [sq_nonneg (r * h)]

variable {Z : ℕ → Ω → ℝ}

/-- **Haas–Giles (2025), §6.3, p. 13, (41): the mean of `S`.**  With independent centred
integrable increments `Z̃_i`, the path of Algorithm 1 has mean `E[S_n] = S_0 (1 + rh)ⁿ` (the
mean of the Euler–Maruyama approximation of geometric Brownian motion). -/
theorem integral_gbmPath_eq (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (hZ1 : ∀ i, Integrable (Z i) μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0) (r σ h s₀ : ℝ) (n : ℕ) :
    ∫ ω, gbmPath r σ h s₀ (fun i => Z i ω) n ∂μ = s₀ * (1 + r * h) ^ n := by
  have hg : Measurable fun z : ℝ => 1 + r * h + Real.sqrt h * σ * z := by fun_prop
  have hWind : iIndepFun (fun i ω => 1 + r * h + Real.sqrt h * σ * Z i ω) μ :=
    hZ.comp _ fun _ => hg
  have hWm : ∀ i, Measurable fun ω => 1 + r * h + Real.sqrt h * σ * Z i ω :=
    fun i => hg.comp (hm i)
  have hfac : ∀ i, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z i ω) ∂μ = 1 + r * h := fun i => by
    rw [integral_add (integrable_const _) ((hZ1 i).const_mul _), integral_const,
      integral_const_mul, hmean i]
    simp
  simp_rw [gbmPath_eq_prod]
  rw [integral_const_mul, integral_prod_of_iIndepFun hWind hWm]
  simp only [hfac, Finset.prod_const, Finset.card_range]

/-- The second moment of `mul2_i = S_i × sum1_i` as a product (Haas–Giles 2025, §6.3): with
independent increments, `E[mul2_i²] = S_0² ∏_{j<i} E[(1 + sum1_j)²] · E[sum1_i²]`. -/
lemma integral_sq_mul2_eq_prod (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (r σ h s₀ : ℝ) (i : ℕ) :
    ∫ ω, (gbmPath r σ h s₀ (fun j => Z j ω) i * (r * h + Real.sqrt h * σ * Z i ω)) ^ 2 ∂μ =
      s₀ ^ 2 * ((∏ j ∈ range i, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ) *
        ∫ ω, (r * h + Real.sqrt h * σ * Z i ω) ^ 2 ∂μ) := by
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ → ℝ → ℝ, g = fun j z =>
      if j < i then (1 + r * h + Real.sqrt h * σ * z) ^ 2 else (r * h + Real.sqrt h * σ * z) ^ 2 :=
    ⟨_, rfl⟩
  have hgm : ∀ j, Measurable (g j) := by
    intro j
    rw [hg_def]
    by_cases hj : j < i
    · simp only [hj, ↓reduceIte]
      fun_prop
    · simp only [hj, ↓reduceIte]
      fun_prop
  have hGind : iIndepFun (fun j ω => g j (Z j ω)) μ := hZ.comp g hgm
  have hGm : ∀ j, Measurable fun ω => g j (Z j ω) := fun j => (hgm j).comp (hm j)
  have hlt : ∀ j ∈ range i, ∀ z, g j z = (1 + r * h + Real.sqrt h * σ * z) ^ 2 := by
    intro j hj z
    rw [hg_def]
    exact if_pos (Finset.mem_range.1 hj)
  have hself : ∀ z, g i z = (r * h + Real.sqrt h * σ * z) ^ 2 := by
    intro z
    rw [hg_def]
    exact if_neg (lt_irrefl i)
  have hprod : ∀ ω,
      (gbmPath r σ h s₀ (fun j => Z j ω) i * (r * h + Real.sqrt h * σ * Z i ω)) ^ 2 =
        s₀ ^ 2 * ∏ j ∈ range (i + 1), g j (Z j ω) := by
    intro ω
    rw [Finset.prod_range_succ, hself, Finset.prod_congr rfl fun j hj => hlt j hj (Z j ω),
      Finset.prod_pow, gbmPath_eq_prod]
    ring
  simp_rw [hprod]
  rw [integral_const_mul, integral_prod_of_iIndepFun hGind hGm, Finset.prod_range_succ,
    Finset.prod_congr rfl fun j hj =>
      integral_congr_ae (Filter.Eventually.of_forall fun ω => hlt j hj (Z j ω)),
    integral_congr_ae (Filter.Eventually.of_forall fun ω => hself (Z i ω))]

/-- **Haas–Giles (2025), §6.3, p. 13, (41) and (39) for `S` and `mul2`, exactly.**  With
independent centred square-integrable increments of the same second moment `E[Z̃_i²] = v`
(`v = 1` for normal increments) and `h ≥ 0`, the path of Algorithm 1 has
`E[S_i²] = S_0² ((1 + rh)² + σ² h v)^i` and `mul2_i = S_i × sum1_i` has
`E[mul2_i²] = S_0² ((1 + rh)² + σ² h v)^i (r² h² + σ² h v)`. -/
theorem integral_sq_gbmPath_mul2_eq_pow (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0) {v : ℝ}
    (hv : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ = v) (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (s₀ : ℝ) (i : ℕ) :
    ∫ ω, gbmPath r σ h s₀ (fun j => Z j ω) i ^ 2 ∂μ =
        s₀ ^ 2 * ((1 + r * h) ^ 2 + σ ^ 2 * h * v) ^ i ∧
      ∫ ω, (gbmPath r σ h s₀ (fun j => Z j ω) i * (r * h + Real.sqrt h * σ * Z i ω)) ^ 2 ∂μ =
        s₀ ^ 2 * ((1 + r * h) ^ 2 + σ ^ 2 * h * v) ^ i * (r ^ 2 * h ^ 2 + σ ^ 2 * h * v) := by
  have hfac : ∀ j, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ =
      (1 + r * h) ^ 2 + σ ^ 2 * h * v := fun j => by
    rw [integral_sq_factor_eq (hZ2 j) (hmean j) r σ hh, hv j]
  refine ⟨?_, ?_⟩
  · rw [integral_sq_gbmPath_eq hZ hm]
    simp only [hfac, Finset.prod_const, Finset.card_range]
  · rw [integral_sq_mul2_eq_prod hZ hm, (integral_sq_mul1_sum1_eq (hZ2 i) (hmean i) r σ hh).2,
      hv i]
    simp only [hfac, Finset.prod_const, Finset.card_range]
    ring

/-- **Haas–Giles (2025), §6.3, p. 13, (41): "`S ∼ 1`", two-sided.**  With independent centred
increments `Z̃_i` of second moment at most 1, `0 ≤ h ≤ 1`, `|r| h ≤ 1/2` and a time horizon
`nh ≤ T`, the path of Algorithm 1 satisfies
`|S_0| e^{−2|r|T} ≤ |E[S_n]| ≤ |S_0| e^{|r|T}` and
`S_0² e^{−4|r|T} ≤ E[S_n²] ≤ S_0² e^{(2|r| + r² + σ²)T}`:
the size of `S_n` is bounded above and below independently of `h`.  (The upper bound on `E[S_n²]`
is `integral_sq_gbmPath_le`; the paper's "size" is the exponent `e_i` of the largest value over
`10⁶` paths, and the mean and the mean square are its analogues here.) -/
theorem gbmPath_size_bounds (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ 1) {r σ h T : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hrh : |r| * h ≤ 1 / 2) (s₀ : ℝ) {n : ℕ} (hn : n * h ≤ T) :
    |s₀| * Real.exp (-(2 * |r| * T)) ≤ |∫ ω, gbmPath r σ h s₀ (fun i => Z i ω) n ∂μ| ∧
      |∫ ω, gbmPath r σ h s₀ (fun i => Z i ω) n ∂μ| ≤ |s₀| * Real.exp (|r| * T) ∧
      s₀ ^ 2 * Real.exp (-(4 * |r| * T)) ≤ ∫ ω, gbmPath r σ h s₀ (fun i => Z i ω) n ^ 2 ∂μ ∧
      ∫ ω, gbmPath r σ h s₀ (fun i => Z i ω) n ^ 2 ∂μ ≤
        s₀ ^ 2 * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * T) := by
  have hrh' : -(1 / 2) ≤ r * h := by
    have := neg_abs_le r
    nlinarith
  have hpos : 0 ≤ 1 + r * h := by linarith
  have hmeanS :=
    integral_gbmPath_eq hZ hm (fun i => (hZ2 i).integrable one_le_two) hmean r σ h s₀ n
  have habs : |∫ ω, gbmPath r σ h s₀ (fun i => Z i ω) n ∂μ| = |s₀| * (1 + r * h) ^ n := by
    rw [hmeanS, abs_mul, abs_pow, abs_of_nonneg hpos]
  have hn0 : (0 : ℝ) ≤ n * h := mul_nonneg (Nat.cast_nonneg n) hh0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [habs]
    exact mul_le_mul_of_nonneg_left (exp_neg_le_one_add_pow hh0 hrh hn) (abs_nonneg s₀)
  · rw [habs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s₀)
    calc (1 + r * h) ^ n ≤ Real.exp (r * h) ^ n :=
          pow_le_pow_left₀ hpos (by linarith [Real.add_one_le_exp (r * h)]) n
      _ = Real.exp (n * (r * h)) := (Real.exp_nat_mul _ n).symm
      _ ≤ Real.exp (|r| * T) := by
          refine Real.exp_le_exp.2 ?_
          have h1 : n * (r * h) ≤ |r| * (n * h) := by
            rw [show (n : ℝ) * (r * h) = r * (n * h) by ring]
            exact mul_le_mul_of_nonneg_right (le_abs_self r) hn0
          nlinarith [mul_le_mul_of_nonneg_left hn (abs_nonneg r)]
  · rw [integral_sq_gbmPath_eq hZ hm]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg s₀)
    refine exp_neg_le_prod hh0 hrh (fun j => ?_) (range n) (by rw [Finset.card_range]; exact hn)
    rw [integral_sq_factor_eq (hZ2 j) (hmean j) r σ hh0]
    have : 0 ≤ ∫ ω, Z j ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg σ) hh0) this]
  · refine (integral_sq_gbmPath_le hZ hm hZ2 hmean hvar hh0 hh1 s₀ n).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (sq_nonneg s₀)
    exact mul_le_mul_of_nonneg_left hn (by positivity)

/-- **Haas–Giles (2025), §6.3, p. 13, (39) for `mul2`: "`mul2 ∼ √h`", two-sided.**  With
independent centred increments `Z̃_i` with `m ≤ E[Z̃_i²] ≤ 1`, `0 ≤ h ≤ 1`, `|r| h ≤ 1/2` and
`ih ≤ T`, the variable `mul2_i = S_i × sum1_i` of Algorithm 1 satisfies
`S_0² e^{−4|r|T} m σ² h ≤ E[mul2_i²] ≤ S_0² e^{(2|r| + r² + σ²)T} (r² + σ²) h`: its mean square
is of exact order `h` when `S_0 σ ≠ 0` and `m > 0` (the upper bound is `integral_sq_mul2_le`). -/
theorem integral_sq_mul2_bounds (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0) {m : ℝ}
    (hvar' : ∀ i, m ≤ ∫ ω, Z i ω ^ 2 ∂μ) (hvar : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ 1) {r σ h T : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hrh : |r| * h ≤ 1 / 2) (s₀ : ℝ) {i : ℕ} (hi : i * h ≤ T) :
    s₀ ^ 2 * Real.exp (-(4 * |r| * T)) * (m * σ ^ 2 * h) ≤
        ∫ ω, (gbmPath r σ h s₀ (fun j => Z j ω) i * (r * h + Real.sqrt h * σ * Z i ω)) ^ 2 ∂μ ∧
      ∫ ω, (gbmPath r σ h s₀ (fun j => Z j ω) i * (r * h + Real.sqrt h * σ * Z i ω)) ^ 2 ∂μ ≤
        s₀ ^ 2 * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * T) * ((r ^ 2 + σ ^ 2) * h) := by
  refine ⟨?_, ?_⟩
  · rw [integral_sq_mul2_eq_prod hZ hm]
    have hP : Real.exp (-(4 * |r| * T)) ≤
        ∏ j ∈ range i, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ := by
      refine exp_neg_le_prod hh0 hrh (fun j => ?_) (range i) (by rw [Finset.card_range]; exact hi)
      rw [integral_sq_factor_eq (hZ2 j) (hmean j) r σ hh0]
      have : 0 ≤ ∫ ω, Z j ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg σ) hh0) this]
    have hG :=
      (integral_sq_mul1_sum1_bounds (hZ2 i) (hmean i) (hvar' i) (hvar i) r σ hh0 hh1).2.2.1
    have hG0 : 0 ≤ ∫ ω, (r * h + Real.sqrt h * σ * Z i ω) ^ 2 ∂μ :=
      integral_nonneg fun ω => sq_nonneg _
    calc s₀ ^ 2 * Real.exp (-(4 * |r| * T)) * (m * σ ^ 2 * h)
        ≤ s₀ ^ 2 * Real.exp (-(4 * |r| * T)) * ∫ ω, (r * h + Real.sqrt h * σ * Z i ω) ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_left hG (by positivity)
      _ ≤ s₀ ^ 2 * ((∏ j ∈ range i, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ) *
          ∫ ω, (r * h + Real.sqrt h * σ * Z i ω) ^ 2 ∂μ) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP hG0) (sq_nonneg s₀)
  · refine (integral_sq_mul2_le hZ hm hZ2 hmean hvar hh0 hh1 s₀ i).trans ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (sq_nonneg s₀)) (by positivity)
    exact mul_le_mul_of_nonneg_left hi (by positivity)

/-- **Haas–Giles (2025), §6.3, p. 13: "The takeaway is that the variables `S_i` are the
largest."**  With independent centred increments `Z̃_i` of second moment at most 1,
`0 ≤ h ≤ 1`, `|r| h ≤ 1/2` and time indices `i, n` in the horizon (`ih, nh ≤ T`), if the time
step is small, `(r² + σ²)(1 + S_0² e^{(2|r| + r² + σ²)T}) h < S_0² e^{−4|r|T}` (which holds for all
small `h` when `S_0 ≠ 0`), then the mean squares of `con1 = rh`, `con2 = √h σ`, `mul1_i`,
`sum1_i` and `mul2_i` are all smaller than that of `S_n`: the former are `O(h)`
(`integral_sq_mul1_le`, `integral_sq_sum1_le`, `integral_sq_mul2_bounds`), the latter is at least
`S_0² e^{−4|r|T}` (`gbmPath_size_bounds`). -/
theorem gbmPath_sq_largest (hZ : iIndepFun Z μ) (hm : ∀ i, Measurable (Z i))
    (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ 1) {r σ h T : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hrh : |r| * h ≤ 1 / 2) (s₀ : ℝ) {i n : ℕ} (hi : i * h ≤ T) (hn : n * h ≤ T)
    (hsmall : (r ^ 2 + σ ^ 2) * (1 + s₀ ^ 2 * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * T)) * h <
      s₀ ^ 2 * Real.exp (-(4 * |r| * T))) :
    (r * h) ^ 2 < ∫ ω, gbmPath r σ h s₀ (fun j => Z j ω) n ^ 2 ∂μ ∧
      (Real.sqrt h * σ) ^ 2 < ∫ ω, gbmPath r σ h s₀ (fun j => Z j ω) n ^ 2 ∂μ ∧
      ∫ ω, (Real.sqrt h * σ * Z i ω) ^ 2 ∂μ <
        ∫ ω, gbmPath r σ h s₀ (fun j => Z j ω) n ^ 2 ∂μ ∧
      ∫ ω, (r * h + Real.sqrt h * σ * Z i ω) ^ 2 ∂μ <
        ∫ ω, gbmPath r σ h s₀ (fun j => Z j ω) n ^ 2 ∂μ ∧
      ∫ ω, (gbmPath r σ h s₀ (fun j => Z j ω) i * (r * h + Real.sqrt h * σ * Z i ω)) ^ 2 ∂μ <
        ∫ ω, gbmPath r σ h s₀ (fun j => Z j ω) n ^ 2 ∂μ := by
  -- the lower bound `S_0² e^{−4|r|T}` for the mean square of `S_n`
  have hS := (gbmPath_size_bounds hZ hm hZ2 hmean hvar hh0 hh1 hrh s₀ hn (σ := σ)).2.2.1
  set E := Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * T) with hE
  have hE0 : 0 ≤ s₀ ^ 2 * E := by positivity
  have hK : (r ^ 2 + σ ^ 2) * h ≤ (r ^ 2 + σ ^ 2) * (1 + s₀ ^ 2 * E) * h := by
    have : 0 ≤ (r ^ 2 + σ ^ 2) * h := by positivity
    nlinarith
  have hK' : s₀ ^ 2 * E * ((r ^ 2 + σ ^ 2) * h) ≤
      (r ^ 2 + σ ^ 2) * (1 + s₀ ^ 2 * E) * h := by
    have : 0 ≤ (r ^ 2 + σ ^ 2) * h := by positivity
    nlinarith
  have hsum1 := integral_sq_sum1_le (hZ2 i) (hmean i) (hvar i) hh0 hh1 (r := r) (σ := σ)
  have hmul1 := integral_sq_mul1_le (μ := μ) (hvar i) hh0 (σ := σ)
  have hmul2 := (integral_sq_mul2_bounds hZ hm hZ2 hmean (m := 0) (fun j => integral_nonneg
    fun ω => sq_nonneg (Z j ω)) hvar hh0 hh1 hrh s₀ hi (σ := σ)).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (r * h) ^ 2 ≤ (r ^ 2 + σ ^ 2) * h := by
      have h1 : r ^ 2 * h ^ 2 ≤ r ^ 2 * h :=
        mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg r)
      nlinarith [mul_nonneg (sq_nonneg σ) hh0]
    linarith
  · have : (Real.sqrt h * σ) ^ 2 ≤ (r ^ 2 + σ ^ 2) * h := by
      rw [mul_pow, Real.sq_sqrt hh0]
      nlinarith [mul_nonneg (sq_nonneg r) hh0]
    linarith
  · have : σ ^ 2 * h ≤ (r ^ 2 + σ ^ 2) * h := by nlinarith [mul_nonneg (sq_nonneg r) hh0]
    linarith
  · linarith
  · linarith

end size

/-! ### §6.3: fixed precision and the independent uniform rounding model -/

section recursion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A quantity computed by a recursion `D_{k+1} = F_k(D_k, W_k)` from a constant `D_0` and
independent step inputs `W_0, W_1, …` is independent of the next input: `D_n ⊥ W_n`.  (`D_n` is
measurable with respect to the σ-algebra generated by `W_0, …, W_{n−1}`.) -/
lemma indepFun_of_recursion {β : Type*} [MeasurableSpace β] {W : ℕ → Ω → β}
    (hW : iIndepFun W μ) (hWm : ∀ k, Measurable (W k)) {D : ℕ → Ω → ℝ} {c : ℝ}
    (h0 : ∀ ω, D 0 ω = c) {F : ℕ → ℝ → β → ℝ} (hF : ∀ k, Measurable (Function.uncurry (F k)))
    (hD : ∀ k ω, D (k + 1) ω = F k (D k ω) (W k ω)) (n : ℕ) :
    IndepFun (D n) (W n) μ := by
  -- `D n` is measurable with respect to the σ-algebra generated by `W 0, …, W (n − 1)`
  have hmeas : ∀ n, Measurable[⨆ k ∈ Set.Iio n, MeasurableSpace.comap (W k) inferInstance]
      (D n) := by
    intro n
    induction n with
    | zero =>
      rw [show D 0 = fun _ => c from funext h0]
      exact measurable_const
    | succ k ih =>
      have hle : (⨆ j ∈ Set.Iio k, MeasurableSpace.comap (W j) inferInstance) ≤
          ⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (W j) inferInstance :=
        biSup_mono fun j hj => lt_trans hj (Nat.lt_succ_self k)
      have hWk : Measurable[⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (W j) inferInstance]
          (W k) :=
        (comap_measurable (W k)).mono
          (le_iSup₂ (f := fun j (_ : j ∈ Set.Iio (k + 1)) =>
            MeasurableSpace.comap (W j) inferInstance) k (Nat.lt_succ_self k)) le_rfl
      rw [show D (k + 1) = fun ω => F k (D k ω) (W k ω) from funext (hD k)]
      exact (hF k).comp ((ih.mono hle le_rfl).prodMk hWk)
  have hind := indep_iSup_of_disjoint (fun k => (hWm k).comap_le) hW.iIndep
    (S := Set.Iio n) (T := {n}) (Set.disjoint_singleton_right.2 (lt_irrefl n))
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at hind
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left hind (hmeas n).comap_le

/-- A uniform variable on a symmetric interval `[−a, a]` has mean `0` (Haas–Giles 2025, §4.1,
the model (22) of the rounding errors). -/
lemma integral_of_isUniform_Icc_neg {δ : Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (hδ : pdf.IsUniform δ (Set.Icc (-a) a) μ) : ∫ ω, δ ω ∂μ = 0 := by
  rw [hδ.integral_eq, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), integral_id]
  ring

end recursion

section rounding

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Haas–Giles (2025), §4.2, p. 9, (26) is an equality under its assumptions.**  "If we assume
that the individual errors `x̄_i δx_i` are independent and use (22) we get the optimistic upper
bound on the path error variance (25): `V[P − P̃] ≤ (1/12) ∑_i E[x̄_i²] 4^{e_i−d_i} ≜ V_indep`
(26)."  Under exactly the hypotheses of `variance_linearised_indep` (sensitivities `x̄_i`
independent of the errors `δx_i`, the terms `x̄_i δx_i` pairwise independent, each `δx_i` uniform
on `[−2^{e_i−d_i−1}, 2^{e_i−d_i−1}]` (22)) the variance of the linearised error is exactly
`V_indep`: `E[δx_i] = 0`, so `V[x̄_i δx_i] = E[x̄_i²] E[δx_i²]`. -/
theorem variance_linearised_indep_eq {ι : Type*} (s : Finset ι) (xbar δ : ι → Ω → ℝ)
    (e : ι → ℤ) (d : ι → ℕ) (hxbar : ∀ i ∈ s, MemLp (xbar i) 2 μ)
    (hδ : ∀ i ∈ s, pdf.IsUniform (δ i)
      (Set.Icc (-(2 : ℝ) ^ (e i - d i - 1)) ((2 : ℝ) ^ (e i - d i - 1))) μ)
    (hind_i : ∀ i ∈ s, IndepFun (xbar i) (δ i) μ)
    (hind : Set.Pairwise ↑s fun i j =>
      IndepFun (fun ω => xbar i ω * δ i ω) (fun ω => xbar j ω * δ j ω) μ) :
    variance (fun ω => ∑ i ∈ s, xbar i ω * δ i ω) μ =
      vIndep s (fun i => ∫ ω, xbar i ω ^ 2 ∂μ) e d := by
  have hfacts : ∀ i ∈ s, AEStronglyMeasurable (δ i) μ ∧
      ∀ᵐ ω ∂μ, |δ i ω| ≤ (2 : ℝ) ^ (e i - d i - 1) :=
    fun i hi => isUniform_Icc_facts (zpow_pos two_pos _) (hδ i hi)
  have hY : ∀ i ∈ s, MemLp (fun ω => xbar i ω * δ i ω) 2 μ := fun i hi =>
    memLp_mul_of_bound (hxbar i hi) (hfacts i hi).1 (hfacts i hi).2
  have hsum : (fun ω => ∑ i ∈ s, xbar i ω * δ i ω) = ∑ i ∈ s, fun ω => xbar i ω * δ i ω := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hsum, IndepFun.variance_sum hY hind, vIndep, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hmean : ∫ ω, δ i ω ∂μ = 0 :=
    integral_of_isUniform_Icc_neg (zpow_pos two_pos _) (hδ i hi)
  have h1 : ∫ ω, xbar i ω * δ i ω ∂μ = 0 := by
    rw [(hind_i i hi).integral_fun_mul_eq_mul_integral (hxbar i hi).1 (hfacts i hi).1, hmean,
      mul_zero]
  have hind2 : IndepFun (fun ω => xbar i ω ^ 2) (fun ω => δ i ω ^ 2) μ :=
    (hind_i i hi).comp (continuous_pow 2).measurable (continuous_pow 2).measurable
  have h2 : ∫ ω, (xbar i ω * δ i ω) ^ 2 ∂μ =
      (∫ ω, xbar i ω ^ 2 ∂μ) * ∫ ω, δ i ω ^ 2 ∂μ := by
    simp_rw [mul_pow]
    exact hind2.integral_fun_mul_eq_mul_integral ((hxbar i hi).1.pow 2) ((hfacts i hi).1.pow 2)
  rw [variance_eq_sub (hY i hi)]
  simp only [Pi.pow_apply]
  rw [h2, h1, integral_sq_uniform_roundError (e i) (d i) (hδ i hi)]
  ring

/-- **Haas–Giles (2025), §6.3, p. 14, with (22) and (26): `N` independent rounding errors of fixed
precision.**  "If the bit-widths in the low precision path generation were fixed, starting at a
certain level, the accuracy would decrease."  If all `N = |s|` variables are rounded with the same
exponent `e` and bit-width `d`, under the model of (26) (`variance_linearised_indep_eq`) and with
mean-square sensitivities `E[x̄_i²] ≥ c`, the variance of the linearised error is at least
`N c 4^{e−d}/12`: it grows linearly in the number of rounded operations, hence like `h⁻¹` for
the `N = T/h` time steps of a path. -/
theorem variance_linearised_indep_ge {ι : Type*} (s : Finset ι) (xbar δ : ι → Ω → ℝ)
    (e : ℤ) (d : ℕ) {c : ℝ} (hxbar : ∀ i ∈ s, MemLp (xbar i) 2 μ)
    (hc : ∀ i ∈ s, c ≤ ∫ ω, xbar i ω ^ 2 ∂μ)
    (hδ : ∀ i ∈ s, pdf.IsUniform (δ i)
      (Set.Icc (-(2 : ℝ) ^ (e - d - 1)) ((2 : ℝ) ^ (e - d - 1))) μ)
    (hind_i : ∀ i ∈ s, IndepFun (xbar i) (δ i) μ)
    (hind : Set.Pairwise ↑s fun i j =>
      IndepFun (fun ω => xbar i ω * δ i ω) (fun ω => xbar j ω * δ j ω) μ) :
    s.card * c * (4 : ℝ) ^ (e - d) / 12 ≤ variance (fun ω => ∑ i ∈ s, xbar i ω * δ i ω) μ := by
  have heq :=
    variance_linearised_indep_eq s xbar δ (fun _ => e) (fun _ => d) hxbar hδ hind_i hind
  rw [heq, vIndep]
  have h : ∑ _i ∈ s, c * (4 : ℝ) ^ (e - d) ≤
      ∑ i ∈ s, (∫ ω, xbar i ω ^ 2 ∂μ) * (4 : ℝ) ^ (e - d) :=
    Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hc i hi) (zpow_pos (by norm_num) _).le
  rw [Finset.sum_const, nsmul_eq_mul] at h
  linarith

variable {Z ρ : ℕ → Ω → ℝ}

/-- One step of the error recursion `D_{n+1} = D_n (1 + sum1_n) + ρ_n` of the path of
Algorithm 1 with `S` rounded after every step, in the independent uniform model (Haas–Giles 2025,
§4.1, (22)): if the step inputs `(Z̃_k, ρ_k)` are independent and each `ρ_k` is uniform on
`[−2^{e−d−1}, 2^{e−d−1}]`, then `D_n ∈ L²`, `E[D_n] = 0` and
`E[D_{n+1}²] = E[D_n²] E[(1 + sum1_n)²] + 4^{e−d}/12`. -/
lemma roundError_step (hW : iIndepFun (fun k ω => (Z k ω, ρ k ω)) μ)
    (hZm : ∀ k, Measurable (Z k)) (hρm : ∀ k, Measurable (ρ k)) (hZ2 : ∀ k, MemLp (Z k) 2 μ)
    {e : ℤ} {d : ℕ}
    (hρ : ∀ k, pdf.IsUniform (ρ k) (Set.Icc (-(2 : ℝ) ^ (e - d - 1)) ((2 : ℝ) ^ (e - d - 1))) μ)
    (r σ h : ℝ) {D : ℕ → Ω → ℝ} (hD0 : ∀ ω, D 0 ω = 0)
    (hDs : ∀ k ω, D (k + 1) ω = D k ω * (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω)
    (n : ℕ) :
    MemLp (D n) 2 μ ∧ ∫ ω, D n ω ∂μ = 0 ∧
      ∫ ω, D (n + 1) ω ^ 2 ∂μ = (∫ ω, D n ω ^ 2 ∂μ) *
        (∫ ω, (1 + r * h + Real.sqrt h * σ * Z n ω) ^ 2 ∂μ) + (4 : ℝ) ^ (e - d) / 12 := by
  -- the error is independent of the next step input `(Z̃_n, ρ_n)`
  have hWm : ∀ k, Measurable fun ω => (Z k ω, ρ k ω) := fun k => (hZm k).prodMk (hρm k)
  have hF : ∀ _k : ℕ, Measurable (Function.uncurry
      fun (x : ℝ) (w : ℝ × ℝ) => x * (1 + r * h + Real.sqrt h * σ * w.1) + w.2) := fun _ => by
    show Measurable fun p : ℝ × (ℝ × ℝ) => p.1 * (1 + r * h + Real.sqrt h * σ * p.2.1) + p.2.2
    fun_prop
  have hDW : ∀ n, IndepFun (D n) (fun ω => (Z n ω, ρ n ω)) μ :=
    indepFun_of_recursion hW hWm hD0 hF hDs
  -- the rounding errors: bounded, centred, with `E[ρ²] = 4^{e−d}/12` (22)
  have ha : (0 : ℝ) < 2 ^ (e - d - 1) := zpow_pos two_pos _
  have hρf : ∀ k, AEStronglyMeasurable (ρ k) μ ∧ ∀ᵐ ω ∂μ, |ρ k ω| ≤ 2 ^ (e - d - 1) :=
    fun k => isUniform_Icc_facts ha (hρ k)
  have hρ0 : ∀ k, ∫ ω, ρ k ω ∂μ = 0 := fun k => integral_of_isUniform_Icc_neg ha (hρ k)
  have hρ2 : ∀ k, ∫ ω, ρ k ω ^ 2 ∂μ = (4 : ℝ) ^ (e - d) / 12 := fun k =>
    integral_sq_uniform_roundError e d (hρ k)
  have hρL2 : ∀ k, MemLp (ρ k) 2 μ := fun k =>
    MemLp.of_bound (hρf k).1 _ ((hρf k).2.mono fun ω hω => by rwa [Real.norm_eq_abs])
  have hmL2 : ∀ k, MemLp (fun ω => 1 + r * h + Real.sqrt h * σ * Z k ω) 2 μ := fun k =>
    (memLp_const (1 + r * h)).add ((hZ2 k).const_mul (Real.sqrt h * σ))
  -- one step, given the moments of `D n`
  have hstep : ∀ n, MemLp (D n) 2 μ → ∫ ω, D n ω ∂μ = 0 →
      MemLp (D (n + 1)) 2 μ ∧ ∫ ω, D (n + 1) ω ∂μ = 0 ∧
        ∫ ω, D (n + 1) ω ^ 2 ∂μ = (∫ ω, D n ω ^ 2 ∂μ) *
          (∫ ω, (1 + r * h + Real.sqrt h * σ * Z n ω) ^ 2 ∂μ) + (4 : ℝ) ^ (e - d) / 12 := by
    intro n hDL2 hDmean
    have hDm : IndepFun (D n) (fun ω => 1 + r * h + Real.sqrt h * σ * Z n ω) μ :=
      (hDW n).comp measurable_id
        (by fun_prop : Measurable fun w : ℝ × ℝ => 1 + r * h + Real.sqrt h * σ * w.1)
    have hD2m2 : IndepFun (fun ω => D n ω ^ 2)
        (fun ω => (1 + r * h + Real.sqrt h * σ * Z n ω) ^ 2) μ :=
      (hDW n).comp (continuous_pow 2).measurable
        (by fun_prop : Measurable fun w : ℝ × ℝ => (1 + r * h + Real.sqrt h * σ * w.1) ^ 2)
    have hDmρ : IndepFun (D n) (fun ω => (1 + r * h + Real.sqrt h * σ * Z n ω) * ρ n ω) μ :=
      (hDW n).comp measurable_id
        (by fun_prop : Measurable fun w : ℝ × ℝ => (1 + r * h + Real.sqrt h * σ * w.1) * w.2)
    have hint2 : Integrable
        (fun ω => D n ω ^ 2 * (1 + r * h + Real.sqrt h * σ * Z n ω) ^ 2) μ :=
      hD2m2.integrable_mul hDL2.integrable_sq (hmL2 n).integrable_sq
    have hDmL2 : MemLp (fun ω => D n ω * (1 + r * h + Real.sqrt h * σ * Z n ω)) 2 μ := by
      refine (memLp_two_iff_integrable_sq (hDL2.1.mul (hmL2 n).1)).2 ?_
      simpa [mul_pow] using hint2
    have hDmρL2 : MemLp (fun ω => D n ω * (1 + r * h + Real.sqrt h * σ * Z n ω) * ρ n ω) 2 μ :=
      memLp_mul_of_bound hDmL2 (hρf n).1 (hρf n).2
    have heq : D (n + 1) = fun ω => D n ω * (1 + r * h + Real.sqrt h * σ * Z n ω) + ρ n ω :=
      funext (hDs n)
    refine ⟨?_, ?_, ?_⟩
    · rw [heq]
      exact hDmL2.add (hρL2 n)
    · rw [heq, integral_add (hDmL2.integrable one_le_two) ((hρL2 n).integrable one_le_two),
        hDm.integral_fun_mul_eq_mul_integral hDL2.1 (hmL2 n).1, hDmean, hρ0 n]
      ring
    · have hexp : (fun ω => D (n + 1) ω ^ 2) =
          fun ω => D n ω ^ 2 * (1 + r * h + Real.sqrt h * σ * Z n ω) ^ 2 +
            (2 * (D n ω * ((1 + r * h + Real.sqrt h * σ * Z n ω) * ρ n ω)) + ρ n ω ^ 2) := by
        funext ω
        rw [hDs n ω]
        ring
      have hi1 : Integrable
          (fun ω => 2 * (D n ω * ((1 + r * h + Real.sqrt h * σ * Z n ω) * ρ n ω))) μ := by
        refine ((hDmρL2.integrable one_le_two).const_mul 2).congr ?_
        filter_upwards with ω
        ring
      have hi2 : Integrable (fun ω => ρ n ω ^ 2) μ := (hρL2 n).integrable_sq
      have hi12 : Integrable (fun ω => 2 * (D n ω * ((1 + r * h + Real.sqrt h * σ * Z n ω) *
          ρ n ω)) + ρ n ω ^ 2) μ := hi1.add hi2
      rw [hexp, integral_add hint2 hi12, integral_add hi1 hi2, integral_const_mul,
        hD2m2.integral_fun_mul_eq_mul_integral (hDL2.1.pow 2) ((hmL2 n).1.pow 2),
        hDmρ.integral_fun_mul_eq_mul_integral hDL2.1 ((hmL2 n).1.mul (hρf n).1), hDmean, hρ2 n]
      ring
  -- the moments of `D n` by induction
  have hmom : ∀ n, MemLp (D n) 2 μ ∧ ∫ ω, D n ω ∂μ = 0 := by
    intro n
    induction n with
    | zero =>
      rw [show D 0 = fun _ => 0 from funext hD0]
      exact ⟨memLp_const 0, by simp⟩
    | succ k ih => exact ⟨(hstep k ih.1 ih.2).1, (hstep k ih.1 ih.2).2.1⟩
  exact ⟨(hmom n).1, (hmom n).2, (hstep n (hmom n).1 (hmom n).2).2.2⟩

/-- The closed form of the recursion of `roundError_step`:
`E[D_n²] = ∑_{k<n} (4^{e−d}/12) ∏_{k<j<n} E[(1 + sum1_j)²]` (Haas–Giles 2025, §6.3). -/
lemma integral_sq_roundError_eq_sum (hW : iIndepFun (fun k ω => (Z k ω, ρ k ω)) μ)
    (hZm : ∀ k, Measurable (Z k)) (hρm : ∀ k, Measurable (ρ k)) (hZ2 : ∀ k, MemLp (Z k) 2 μ)
    {e : ℤ} {d : ℕ}
    (hρ : ∀ k, pdf.IsUniform (ρ k) (Set.Icc (-(2 : ℝ) ^ (e - d - 1)) ((2 : ℝ) ^ (e - d - 1))) μ)
    (r σ h : ℝ) {D : ℕ → Ω → ℝ} (hD0 : ∀ ω, D 0 ω = 0)
    (hDs : ∀ k ω, D (k + 1) ω = D k ω * (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω)
    (n : ℕ) :
    ∫ ω, D n ω ^ 2 ∂μ = ∑ k ∈ range n, (4 : ℝ) ^ (e - d) / 12 *
      ∏ j ∈ Ico (k + 1) n, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ := by
  have h := perturbed_sub_eq (fun j => ∫ ω, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ)
    (fun _ => (4 : ℝ) ^ (e - d) / 12) (fun _ => 0) (fun n => ∫ ω, D n ω ^ 2 ∂μ)
    (fun _ => by simp) (fun k => (roundError_step hW hZm hρm hZ2 hρ r σ h hD0 hDs k).2.2)
    (by simp [hD0]) n
  simpa using h

/-- The lower bound `E[D_n²] ≥ n (4^{e−d}/12) e^{−4|r|T}` for the error recursion of
`roundError_step`, when the increments are centred, `h ≥ 0`, `|r| h ≤ 1/2` and `nh ≤ T`. -/
lemma integral_sq_roundError_ge (hW : iIndepFun (fun k ω => (Z k ω, ρ k ω)) μ)
    (hZm : ∀ k, Measurable (Z k)) (hρm : ∀ k, Measurable (ρ k)) (hZ2 : ∀ k, MemLp (Z k) 2 μ)
    (hmean : ∀ k, ∫ ω, Z k ω ∂μ = 0) {e : ℤ} {d : ℕ}
    (hρ : ∀ k, pdf.IsUniform (ρ k) (Set.Icc (-(2 : ℝ) ^ (e - d - 1)) ((2 : ℝ) ^ (e - d - 1))) μ)
    {r σ h T : ℝ} (hh0 : 0 ≤ h) (hrh : |r| * h ≤ 1 / 2) {D : ℕ → Ω → ℝ} (hD0 : ∀ ω, D 0 ω = 0)
    (hDs : ∀ k ω, D (k + 1) ω = D k ω * (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω)
    {n : ℕ} (hn : n * h ≤ T) :
    n * ((4 : ℝ) ^ (e - d) / 12) * Real.exp (-(4 * |r| * T)) ≤ ∫ ω, D n ω ^ 2 ∂μ := by
  rw [integral_sq_roundError_eq_sum hW hZm hρm hZ2 hρ r σ h hD0 hDs n]
  have hc : (0 : ℝ) ≤ (4 : ℝ) ^ (e - d) / 12 := by positivity
  have hterm : ∀ k ∈ range n, (4 : ℝ) ^ (e - d) / 12 * Real.exp (-(4 * |r| * T)) ≤
      (4 : ℝ) ^ (e - d) / 12 *
        ∏ j ∈ Ico (k + 1) n, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ := by
    intro k _
    refine mul_le_mul_of_nonneg_left (exp_neg_le_prod hh0 hrh (fun j => ?_) _ ?_) hc
    · rw [integral_sq_factor_eq (hZ2 j) (hmean j) r σ hh0]
      have : 0 ≤ ∫ ω, Z j ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg σ) hh0) this]
    · rw [Nat.card_Ico]
      have hle : ((n - (k + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n (k + 1)
      nlinarith
  calc (n : ℝ) * ((4 : ℝ) ^ (e - d) / 12) * Real.exp (-(4 * |r| * T))
      = ∑ _k ∈ range n, (4 : ℝ) ^ (e - d) / 12 * Real.exp (-(4 * |r| * T)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum hterm

/-- **Haas–Giles (2025), §6.3, p. 14, with (22) and (26): the rounding error of the path, exactly.**
Model the path of Algorithm 1 in which `S` is rounded after every step, as in
`integral_abs_roundFixed_path_sub_le`, by `S̃_0 = S_0`,
`S̃_{k+1} = S̃_k (1 + rh + √h σ Z̃_k) + ρ_k`, where, as in the model (22) and (26), the rounding
errors `ρ_k` are uniform on `[−2^{e−d−1}, 2^{e−d−1}]` and the step inputs `(Z̃_k, ρ_k)` are
independent (the increments `Z̃_k` square-integrable).  Then the error `S̃_n − S_n` has mean 0 and
its variance is exactly `V_indep` of (26) for the `n` roundings of `S`, with the sensitivities
`x̄_k = ∂S_n/∂S_{k+1} = ∏_{k<j<n} (1 + sum1_j)`:
`V[S̃_n − S_n] = (1/12) ∑_{k<n} E[x̄_k²] 4^{e−d}`.  The terms `x̄_k ρ_k` are not independent, as
(26) assumes, but they are uncorrelated, which is all that (26) needs. -/
theorem perturbed_path_sub_mean_variance (hW : iIndepFun (fun k ω => (Z k ω, ρ k ω)) μ)
    (hZm : ∀ k, Measurable (Z k)) (hρm : ∀ k, Measurable (ρ k)) (hZ2 : ∀ k, MemLp (Z k) 2 μ)
    {e : ℤ} {d : ℕ}
    (hρ : ∀ k, pdf.IsUniform (ρ k) (Set.Icc (-(2 : ℝ) ^ (e - d - 1)) ((2 : ℝ) ^ (e - d - 1))) μ)
    (r σ h s₀ : ℝ) (St : ℕ → Ω → ℝ) (hSt0 : ∀ ω, St 0 ω = s₀)
    (hSt : ∀ k ω, St (k + 1) ω = St k ω * (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω)
    (n : ℕ) :
    ∫ ω, (St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) ∂μ = 0 ∧
      variance (fun ω => St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) μ =
        vIndep (range n)
          (fun k => ∫ ω, (∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω)) ^ 2 ∂μ)
          (fun _ => e) (fun _ => d) := by
  have hD0 : ∀ ω, St 0 ω - gbmPath r σ h s₀ (fun j => Z j ω) 0 = 0 := fun ω => by
    simp [hSt0, gbmPath]
  have hDs : ∀ k ω, St (k + 1) ω - gbmPath r σ h s₀ (fun j => Z j ω) (k + 1) =
      (St k ω - gbmPath r σ h s₀ (fun j => Z j ω) k) *
        (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω := fun k ω => by
    rw [hSt, gbmPath_succ]
    ring
  obtain ⟨hL2, hmean0, -⟩ := roundError_step hW hZm hρm hZ2 hρ r σ h
    (D := fun n ω => St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) hD0 hDs n
  refine ⟨hmean0, ?_⟩
  rw [variance_of_integral_eq_zero hL2.aemeasurable hmean0,
    integral_sq_roundError_eq_sum hW hZm hρm hZ2 hρ r σ h
      (D := fun n ω => St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) hD0 hDs n,
    vIndep, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- `E[(∏_j (1 + sum1_j))²] = ∏_j E[(1 + sum1_j)²]` by independence
  have hg : Measurable fun w : ℝ × ℝ => (1 + r * h + Real.sqrt h * σ * w.1) ^ 2 := by fun_prop
  have hind : iIndepFun (fun j ω => (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2) μ :=
    hW.comp _ fun _ => hg
  have hm : ∀ j, Measurable fun ω => (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 := fun j =>
    (measurable_const.add (measurable_const.mul (hZm j))).pow_const 2
  have hprod : ∫ ω, (∏ j ∈ Ico (k + 1) n, (1 + r * h + Real.sqrt h * σ * Z j ω)) ^ 2 ∂μ =
      ∏ j ∈ Ico (k + 1) n, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ := by
    simp_rw [← Finset.prod_pow]
    exact integral_prod_of_iIndepFun hind hm _
  simp only [hprod]
  ring

/-- **Haas–Giles (2025), §6.3, p. 14: with fixed precision the rounding error grows like `h⁻¹`.**
"In the fixed precision case the rounding error at each time step of the Euler-Maruyama scheme is
of order `O(h⁻¹ 2^{e_{S,ℓ}−d_{S,ℓ}})`."  In the model of `perturbed_path_sub_mean_variance`, with
centred increments of second moment at most 1, `0 ≤ h ≤ 1`, `|r| h ≤ 1/2` and `nh ≤ T`,
`n (4^{e−d}/12) e^{−4|r|T} ≤ E[(S̃_n − S_n)²] ≤ n (4^{e−d}/12) e^{(2|r| + r² + σ²)T}`.
With `n = T/h` steps the mean-square rounding error is of exact order `h⁻¹ 4^{e−d}`: for a fixed
bit-width `d` it grows without bound as `h → 0`.  Its root mean square is of order
`h^{−1/2} 2^{e−d}`: the independent errors partly cancel, and the paper's `O(h⁻¹ 2^{e−d})` is the
worst-case bound (`integral_abs_roundFixed_path_sub_le`), which this model does not attain. -/
theorem integral_sq_perturbed_path_sub_bounds (hW : iIndepFun (fun k ω => (Z k ω, ρ k ω)) μ)
    (hZm : ∀ k, Measurable (Z k)) (hρm : ∀ k, Measurable (ρ k)) (hZ2 : ∀ k, MemLp (Z k) 2 μ)
    (hmean : ∀ k, ∫ ω, Z k ω ∂μ = 0) (hvar : ∀ k, ∫ ω, Z k ω ^ 2 ∂μ ≤ 1) {e : ℤ} {d : ℕ}
    (hρ : ∀ k, pdf.IsUniform (ρ k) (Set.Icc (-(2 : ℝ) ^ (e - d - 1)) ((2 : ℝ) ^ (e - d - 1))) μ)
    {r σ h T : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hrh : |r| * h ≤ 1 / 2) (s₀ : ℝ)
    (St : ℕ → Ω → ℝ) (hSt0 : ∀ ω, St 0 ω = s₀)
    (hSt : ∀ k ω, St (k + 1) ω = St k ω * (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω)
    {n : ℕ} (hn : n * h ≤ T) :
    n * ((4 : ℝ) ^ (e - d) / 12) * Real.exp (-(4 * |r| * T)) ≤
        ∫ ω, (St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) ^ 2 ∂μ ∧
      ∫ ω, (St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) ^ 2 ∂μ ≤
        n * ((4 : ℝ) ^ (e - d) / 12) * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * T) := by
  have hD0 : ∀ ω, St 0 ω - gbmPath r σ h s₀ (fun j => Z j ω) 0 = 0 := fun ω => by
    simp [hSt0, gbmPath]
  have hDs : ∀ k ω, St (k + 1) ω - gbmPath r σ h s₀ (fun j => Z j ω) (k + 1) =
      (St k ω - gbmPath r σ h s₀ (fun j => Z j ω) k) *
        (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω := fun k ω => by
    rw [hSt, gbmPath_succ]
    ring
  refine ⟨integral_sq_roundError_ge hW hZm hρm hZ2 hmean hρ hh0 hrh
    (D := fun n ω => St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) hD0 hDs hn, ?_⟩
  rw [integral_sq_roundError_eq_sum hW hZm hρm hZ2 hρ r σ h
    (D := fun n ω => St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) hD0 hDs n]
  have hc : (0 : ℝ) ≤ (4 : ℝ) ^ (e - d) / 12 := by positivity
  have hterm : ∀ k ∈ range n, (4 : ℝ) ^ (e - d) / 12 *
      ∏ j ∈ Ico (k + 1) n, ∫ ω, (1 + r * h + Real.sqrt h * σ * Z j ω) ^ 2 ∂μ ≤
        (4 : ℝ) ^ (e - d) / 12 * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * T) := by
    intro k _
    refine mul_le_mul_of_nonneg_left ((prod_integral_sq_factor_le hZ2 hmean hvar hh0 hh1 _).trans
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by positivity)))) hc
    rw [Nat.card_Ico]
    have hle : ((n - (k + 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n (k + 1)
    nlinarith
  calc _ ≤ ∑ _k ∈ range n, (4 : ℝ) ^ (e - d) / 12 * Real.exp ((2 * |r| + r ^ 2 + σ ^ 2) * T) :=
        Finset.sum_le_sum hterm
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- **Haas–Giles (2025), §6.3, p. 14: "for small time steps the rounding errors due to the finite
precision are relatively large".**  "Indeed in the fixed precision case the rounding error … is
of order `O(h⁻¹ 2^{e_{S,ℓ}−d_{S,ℓ}})` … so for large time steps the net error in `S_N` is dominated
by the time step, however for small time steps the rounding errors due to the finite precision
are relatively large."  Let `n` steps of size `h > 0` cover the horizon, `nh = T`, with
`|r| h ≤ 1/2`, and let the rounded path `S̃` follow the independent uniform model of
`perturbed_path_sub_mean_variance` with centred increments.  If
`C(T) h² < T (4^{e−d}/12) e^{−4|r|T}`, where `C(T) = gbmStrongConst r σ T S_0` — true for all
small `h`, since the right side does not depend on `h` — then the mean-square discretisation
error of Algorithm 1 in exact arithmetic, `E[(S_T − S_n)²] ≤ C(T) h` for normal increments
(`gbm_em_strong_error`, with the exact solution `S_T = S_0 e^{(r − σ²/2)T + σ W_T}` driven by the
same increments), is smaller than the mean-square rounding error `E[(S̃_n − S_n)²]`
(`integral_sq_perturbed_path_sub_bounds`); the increments of the model need only be centred, so
they may be the normal increments themselves.  So with `h_ℓ = T 2^{−ℓ}` and a fixed bit-width
`d`, from some level on the rounding error dominates. -/
theorem strongError_lt_integral_sq_perturbed_path_sub
    (hW : iIndepFun (fun k ω => (Z k ω, ρ k ω)) μ)
    (hZm : ∀ k, Measurable (Z k)) (hρm : ∀ k, Measurable (ρ k)) (hZ2 : ∀ k, MemLp (Z k) 2 μ)
    (hmean : ∀ k, ∫ ω, Z k ω ∂μ = 0) {e : ℤ} {d : ℕ}
    (hρ : ∀ k, pdf.IsUniform (ρ k) (Set.Icc (-(2 : ℝ) ^ (e - d - 1)) ((2 : ℝ) ^ (e - d - 1))) μ)
    {r σ h T : ℝ} (hh : 0 < h) (hrh : |r| * h ≤ 1 / 2) (s₀ : ℝ) (St : ℕ → Ω → ℝ)
    (hSt0 : ∀ ω, St 0 ω = s₀)
    (hSt : ∀ k ω, St (k + 1) ω = St k ω * (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω)
    {n : ℕ} (hT : n * h = T)
    (hsmall : gbmStrongConst r σ T s₀ * h ^ 2 <
      T * ((4 : ℝ) ^ (e - d) / 12) * Real.exp (-(4 * |r| * T))) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
        gbmPath r σ h s₀ z n) ^ 2 ∂stdNormalSeq <
      ∫ ω, (St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) ^ 2 ∂μ := by
  -- the discretisation error: `E[(S_T − S_n)²] ≤ C(T) h` (`gbm_em_strong_error`)
  have hpath : ∀ z : ℕ → ℝ, emPath (gbmDrift r) (gbmVol σ) h s₀ z n = gbmPath r σ h s₀ z n :=
    fun z => by
      rw [emPath_gbm, gbmPath_eq_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      unfold gbmEMFactor
      ring
  have hdisc := gbm_em_strong_error r σ s₀ hh.le n
  simp_rw [hpath, hT] at hdisc
  -- the rounding error: `E[(S̃_n − S_n)²] ≥ n (4^{e−d}/12) e^{−4|r|T}`
  have hD0 : ∀ ω, St 0 ω - gbmPath r σ h s₀ (fun j => Z j ω) 0 = 0 := fun ω => by
    simp [hSt0, gbmPath]
  have hDs : ∀ k ω, St (k + 1) ω - gbmPath r σ h s₀ (fun j => Z j ω) (k + 1) =
      (St k ω - gbmPath r σ h s₀ (fun j => Z j ω) k) *
        (1 + r * h + Real.sqrt h * σ * Z k ω) + ρ k ω := fun k ω => by
    rw [hSt, gbmPath_succ]
    ring
  have hround := integral_sq_roundError_ge hW hZm hρm hZ2 hmean hρ hh.le hrh
    (D := fun n ω => St n ω - gbmPath r σ h s₀ (fun j => Z j ω) n) hD0 hDs hT.le
  -- `C(T) h < n (4^{e−d}/12) e^{−4|r|T}` because `nh = T`
  have hlt : gbmStrongConst r σ T s₀ * h <
      n * ((4 : ℝ) ^ (e - d) / 12) * Real.exp (-(4 * |r| * T)) := by
    refine lt_of_mul_lt_mul_right ?_ hh.le
    calc gbmStrongConst r σ T s₀ * h * h = gbmStrongConst r σ T s₀ * h ^ 2 := by ring
      _ < T * ((4 : ℝ) ^ (e - d) / 12) * Real.exp (-(4 * |r| * T)) := hsmall
      _ = n * ((4 : ℝ) ^ (e - d) / 12) * Real.exp (-(4 * |r| * T)) * h := by
          rw [← hT]
          ring
  linarith

end rounding

end MLMC
