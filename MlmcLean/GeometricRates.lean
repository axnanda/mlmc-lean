import MlmcLean.Complexity

/-!
# Giles §2.1: the optimal allocation under geometric rates, and the case `β = 2α`

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1, p. 7 (the
proof sketch of Theorem 1 and the remark after it).

* **The allocation of the proof sketch.**  "If `V_ℓ = O(2^{−βℓ})` and `C_ℓ = O(2^{γℓ})` then the
  optimal number of samples `N_ℓ` on level `ℓ` is proportional to `2^{−(β+γ)ℓ/2}`, and so the total
  cost on level `ℓ` is proportional to `2^{(γ−β)ℓ/2}`" (`lagrangeN_geometric`, for the rates
  `V_ℓ = c₂ 2^{−βℓ}`, `C_ℓ = c₃ 2^{γℓ}` and the Lagrange allocation of §1.3).
* **The case `β = 2α`.**  "If `β = 2α`, which is usually the best that can be achieved ..., then
  the total cost is `O(C_L)`, corresponding to `O(1)` samples on the finest level"
  (`complexityBound_of_two_mul`: the bound `ε^{−2−(γ−β)/α}` of Theorem 1 is then `ε^{−γ/α}`, the
  order of `C_L`; `cost_of_beta_eq_two_alpha`: when `2^{−αL} ≤ K ε`, the optimal allocation for
  the variance `ε²/2` has `N_L` bounded by a constant and total cost bounded by a constant times
  `C_L`, both constants independent of `ε` and `L`).
-/

open Finset

namespace MLMC

/-- **The optimal allocation under geometric rates** (Giles 2015, §2.1, p. 7, proof sketch of
Theorem 1: "the optimal number of samples `N_ℓ` on level `ℓ` is proportional to `2^{−(β+γ)ℓ/2}`,
and therefore the cost on level `ℓ` is proportional to `2^{(γ−β)ℓ/2}`").  For the rates
`V_ℓ = c₂ 2^{−βℓ}`, `C_ℓ = c₃ 2^{γℓ}` (`c₂, c₃ > 0`), the Lagrange allocation
`N_ℓ = τ⁻¹ √(V_ℓ/C_ℓ) ∑_j √(V_j C_j)` of §1.3 over any finite set of levels is
`N_ℓ = K √(c₂/c₃) (2^{−(β+γ)/2})^ℓ` and costs `N_ℓ C_ℓ = K √(c₂ c₃) (2^{(γ−β)/2})^ℓ` on level
`ℓ`, with the same factor `K = τ⁻¹ ∑_j √(V_j C_j)` for all levels. -/
theorem lagrangeN_geometric {β γ c₂ c₃ : ℝ} (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (s : Finset ℕ)
    (τ : ℝ) (ℓ : ℕ) :
    lagrangeN s (Vb β c₂) (Cb γ c₃) τ ℓ =
        τ⁻¹ * sumSqrtVC s (Vb β c₂) (Cb γ c₃) * Real.sqrt (c₂ / c₃) *
          ((2 : ℝ) ^ (-(β + γ) / 2)) ^ ℓ ∧
      lagrangeN s (Vb β c₂) (Cb γ c₃) τ ℓ * Cb γ c₃ ℓ =
        τ⁻¹ * sumSqrtVC s (Vb β c₂) (Cb γ c₃) * Real.sqrt (c₂ * c₃) *
          ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ := by
  have hr : ((2 : ℝ) ^ (-(β + γ) / 2)) ^ (2 * ℓ) =
      (2 : ℝ) ^ (-(β * (ℓ : ℝ))) / (2 : ℝ) ^ (γ * (ℓ : ℝ)) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_sub two_pos]
    congr 1
    push_cast
    ring
  have hsq : Vb β c₂ ℓ / Cb γ c₃ ℓ =
      (Real.sqrt (c₂ / c₃) * ((2 : ℝ) ^ (-(β + γ) / 2)) ^ ℓ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (div_pos hc₂ hc₃).le, ← pow_mul', hr]
    unfold Vb Cb
    rw [mul_div_mul_comm]
  have hsqrt : Real.sqrt (Vb β c₂ ℓ / Cb γ c₃ ℓ) =
      Real.sqrt (c₂ / c₃) * ((2 : ℝ) ^ (-(β + γ) / 2)) ^ ℓ := by
    rw [hsq, Real.sqrt_sq (by positivity)]
  refine ⟨?_, ?_⟩
  · unfold lagrangeN
    rw [hsqrt]
    ring
  · have h2 : lagrangeN s (Vb β c₂) (Cb γ c₃) τ ℓ * Cb γ c₃ ℓ =
        τ⁻¹ * sumSqrtVC s (Vb β c₂) (Cb γ c₃) * Real.sqrt (Vb β c₂ ℓ * Cb γ c₃ ℓ) := by
      unfold lagrangeN
      rw [← sqrt_div_mul (Vb_pos hc₂ ℓ).le (Cb_pos hc₃ ℓ)]
      ring
    rw [h2, sqrt_Vb_mul_Cb hc₂ hc₃ ℓ]
    ring

/-- **The exponent when `β = 2α`** (Giles 2015, §2.1, p. 7): if `β = 2α < γ`, the bound
`ε^{−2−(γ−β)/α}` of Theorem 1 is `ε^{−γ/α}`, which is the order of the cost `C_L` of one sample on
the finest level (`2^{−αL} = O(ε)` and `C_L = O(2^{γL})`). -/
theorem complexityBound_of_two_mul {α β γ : ℝ} (hα : 0 < α) (hβ : β = 2 * α) (hβγ : β < γ)
    (ε : ℝ) : complexityBound α β γ ε = ε ^ (-(γ / α)) := by
  rw [complexityBound_of_gt hβγ]
  have h : -2 - (γ - β) / α = -(γ / α) := by
    rw [hβ, sub_div, mul_div_assoc, div_self hα.ne']
    ring
  rw [h]

/-- **`β = 2α`: `O(1)` samples on the finest level and total cost `O(C_L)`** (Giles 2015, §2.1,
p. 7: "If `β = 2α` ... then the total cost is `O(C_L)`, corresponding to `O(1)` samples on the
finest level").  Let `γ > 2α`, `c₂, c₃ > 0`, `ε > 0`, and let the finest level `L` satisfy
the bias condition `2^{−αL} ≤ K ε`.  For the rates `V_ℓ = c₂ 2^{−2αℓ}`, `C_ℓ = c₃ 2^{γℓ}`, the
optimal (Lagrange) allocation over the levels `0, …, L` for the variance target `ε²/2` has
`N_L ≤ 2 c₂ K² q` samples on the finest level and total cost `∑_ℓ N_ℓ C_ℓ ≤ 2 c₂ K² q² C_L`,
where `q = r/(r − 1)` with `r = 2^{(γ−2α)/2}`: both bounds are independent of `ε` and `L`. -/
theorem cost_of_beta_eq_two_alpha {α γ c₂ c₃ K ε : ℝ} (hαγ : 2 * α < γ)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hε : 0 < ε) {L : ℕ}
    (hL : (2 : ℝ) ^ (-(α * (L : ℝ))) ≤ K * ε) :
    lagrangeN (range (L + 1)) (Vb (2 * α) c₂) (Cb γ c₃) (ε ^ 2 / 2) L ≤
        2 * c₂ * K ^ 2 * ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) ∧
      ∑ ℓ ∈ range (L + 1),
          lagrangeN (range (L + 1)) (Vb (2 * α) c₂) (Cb γ c₃) (ε ^ 2 / 2) ℓ * Cb γ c₃ ℓ ≤
        2 * c₂ * K ^ 2 *
          ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) ^ 2 * Cb γ c₃ L := by
  have hr : 1 < (2 : ℝ) ^ ((γ - 2 * α) / 2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hq : 0 < (2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1) :=
    div_pos (by linarith) (by linarith)
  have hx0 : 0 < (2 : ℝ) ^ (-(α * (L : ℝ))) := Real.rpow_pos_of_pos two_pos _
  have hsq : ((2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 ≤ (K * ε) ^ 2 := pow_le_pow_left₀ hx0.le hL 2
  have hτ : (ε ^ 2 / 2)⁻¹ = 2 / ε ^ 2 := by rw [inv_div]
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε.ne'
  have hA : 0 ≤ 2 / ε ^ 2 * c₂ := mul_nonneg (div_pos two_pos (pow_pos hε 2)).le hc₂.le
  -- the sum `∑_{ℓ ≤ L} √(V_ℓ C_ℓ) = √(c₂ c₃) ∑_{ℓ ≤ L} r^ℓ ≤ √(c₂ c₃) r^L q`
  have hS : ∑ ℓ ∈ range (L + 1), Real.sqrt (Vb (2 * α) c₂ ℓ * Cb γ c₃ ℓ) ≤
      Real.sqrt (c₂ * c₃) * (((2 : ℝ) ^ ((γ - 2 * α) / 2)) ^ L *
        ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1))) := by
    rw [Finset.sum_congr rfl fun ℓ _ => sqrt_Vb_mul_Cb hc₂ hc₃ ℓ, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (geom_sum_le_of_one_lt hr L) (Real.sqrt_nonneg _)
  have hS0 : 0 ≤ ∑ ℓ ∈ range (L + 1), Real.sqrt (Vb (2 * α) c₂ ℓ * Cb γ c₃ ℓ) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  -- `2^{−(2α+γ)L/2} r^L = (2^{−αL})²` and `(r^L)² = (2^{−αL})² 2^{γL}`
  have e1 : ((2 : ℝ) ^ (-(2 * α + γ) / 2)) ^ L * ((2 : ℝ) ^ ((γ - 2 * α) / 2)) ^ L =
      ((2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := by
    rw [← mul_pow, ← Real.rpow_add two_pos, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      sq, ← Real.rpow_add two_pos]
    congr 1
    ring
  have e2 : (((2 : ℝ) ^ ((γ - 2 * α) / 2)) ^ L) ^ 2 =
      ((2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 * (2 : ℝ) ^ (γ * (L : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), sq,
      ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    congr 1
    push_cast
    ring
  constructor
  · -- samples on the finest level
    rw [(lagrangeN_geometric (β := 2 * α) (γ := γ) hc₂ hc₃ (range (L + 1)) (ε ^ 2 / 2) L).1]
    have hτ0 : 0 ≤ (ε ^ 2 / 2)⁻¹ := by positivity
    calc (ε ^ 2 / 2)⁻¹ * sumSqrtVC (range (L + 1)) (Vb (2 * α) c₂) (Cb γ c₃) *
          Real.sqrt (c₂ / c₃) * ((2 : ℝ) ^ (-(2 * α + γ) / 2)) ^ L
        ≤ (ε ^ 2 / 2)⁻¹ * (Real.sqrt (c₂ * c₃) * (((2 : ℝ) ^ ((γ - 2 * α) / 2)) ^ L *
            ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)))) *
          Real.sqrt (c₂ / c₃) * ((2 : ℝ) ^ (-(2 * α + γ) / 2)) ^ L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hS hτ0) (Real.sqrt_nonneg _)) (by positivity)
      _ = (ε ^ 2 / 2)⁻¹ * (Real.sqrt (c₂ / c₃) * Real.sqrt (c₂ * c₃)) *
          (((2 : ℝ) ^ (-(2 * α + γ) / 2)) ^ L * ((2 : ℝ) ^ ((γ - 2 * α) / 2)) ^ L) *
          ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) := by ring
      _ = 2 / ε ^ 2 * c₂ * ((2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 *
          ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) := by
          rw [sqrt_div_mul_sqrt_mul hc₂.le hc₃, e1, hτ]
      _ ≤ 2 / ε ^ 2 * c₂ * (K * ε) ^ 2 *
          ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hA) hq.le
      _ = 2 * c₂ * K ^ 2 *
          ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) * (ε ^ 2 / ε ^ 2) := by
          ring
      _ = 2 * c₂ * K ^ 2 *
          ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) := by
          rw [div_self hε2, mul_one]
  · -- the total cost
    have hs : (range (L + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos L)⟩
    rw [(lagrangeN_variance_cost hs (fun ℓ _ => Vb_pos (β := 2 * α) hc₂ ℓ)
      (fun ℓ _ => Cb_pos (γ := γ) hc₃ ℓ)
      (by positivity : (0 : ℝ) < ε ^ 2 / 2)).2]
    have hB : 0 ≤ ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) ^ 2 *
        Cb γ c₃ L := mul_nonneg (sq_nonneg _) (Cb_pos hc₃ L).le
    calc (ε ^ 2 / 2)⁻¹ * (∑ ℓ ∈ range (L + 1), Real.sqrt (Vb (2 * α) c₂ ℓ * Cb γ c₃ ℓ)) ^ 2
        ≤ (ε ^ 2 / 2)⁻¹ * (Real.sqrt (c₂ * c₃) * (((2 : ℝ) ^ ((γ - 2 * α) / 2)) ^ L *
            ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)))) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hS 2) (by positivity)
      _ = 2 / ε ^ 2 * c₂ * c₃ * (((2 : ℝ) ^ ((γ - 2 * α) / 2)) ^ L) ^ 2 *
          ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) ^ 2 := by
          rw [hτ, mul_pow, Real.sq_sqrt (mul_pos hc₂ hc₃).le]
          ring
      _ = 2 / ε ^ 2 * c₂ * ((2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 *
          (((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) ^ 2 *
            Cb γ c₃ L) := by
          rw [e2]
          unfold Cb
          ring
      _ ≤ 2 / ε ^ 2 * c₂ * (K * ε) ^ 2 *
          (((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) ^ 2 *
            Cb γ c₃ L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hA) hB
      _ = 2 * c₂ * K ^ 2 *
          ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) ^ 2 * Cb γ c₃ L *
          (ε ^ 2 / ε ^ 2) := by ring
      _ = 2 * c₂ * K ^ 2 *
          ((2 : ℝ) ^ ((γ - 2 * α) / 2) / ((2 : ℝ) ^ ((γ - 2 * α) / 2) - 1)) ^ 2 *
            Cb γ c₃ L := by
          rw [div_self hε2, mul_one]

end MLMC
