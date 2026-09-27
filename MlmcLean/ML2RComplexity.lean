import MlmcLean.Richardson
import MlmcLean.Complexity

/-!
# The complexity of multilevel Richardson–Romberg extrapolation (Giles 2015, §2.3)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.3 (p. 12 of
the author's version), after Lemaire and Pagès (2013).

"Because the remaining error is `O(2^{−αL²})`, rather than the usual `O(2^{−αL})`, it is possible
to obtain the usual `O(ε)` weak error with a value of `L` which is the square root of the usual
value.  Hence, in the case `β = γ` they prove that the overall cost is reduced to `O(ε⁻² |log ε|)`,
while for `β < γ` the cost is reduced much more to `O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`."

`MlmcLean.Richardson` shows that the remaining error is `(−1)^L a_{L+1} 2^{−αL(L+1)/2}`
(`ml2r_bias`), i.e. of order `2^{−αL(L+1)/2}` rather than the printed `2^{−αL²}`.  This file proves
the complexity statements with this rate.

* **The weights are bounded uniformly in `L`** (`abs_ml2rWeight_le`, `sum_abs_ml2rWeight_le`,
  `abs_ml2r_coeff_le`): with `r = 2^{−α}`, `|w_ℓ| ≤ B² r^{L−ℓ}` with `B = e^{r/(1−r)²}`, so
  `∑_ℓ |w_ℓ| ≤ B²/(1 − r)` and the coefficients `v_ℓ = ∑_{ℓ' ≥ ℓ} w_ℓ'` of the ML2R estimator
  are bounded by the same constant, whatever `L`.
* **The number of levels is the square root of the usual value** (`ml2rLevel_bias`,
  `ml2rLevel_le`): `L = ⌈√(2 log₂(√2 c₁/ε)/α)⌉` levels make the remaining error
  `c₁ 2^{−αL(L+1)/2} ≤ ε/√2`, whereas `2^{−αL}` needs `L ≈ log₂(1/ε)/α`.
* **The cost** (`ml2r_complexity_eq`, `ml2r_complexity_lt`): with `V_ℓ ≤ c₂ 2^{−βℓ}`,
  `C_ℓ ≤ c₃ 2^{γℓ}`, there are `L` and `N_ℓ` with mean square error `< ε²` and cost
  `O(ε⁻² |log ε|)` when `β = γ`, and `O(ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)})` when `β < γ` (the
  printed exponent `√(|log₂ ε|/α)` comes from the printed rate `2^{−αL²}`; with the rate
  `2^{−αL(L+1)/2}` it is `√(2|log₂ ε|/α)`).
-/

open Finset

namespace MLMC

/-! ### A uniform bound on the ML2R weights -/

section weights

/-- `|x_k/(x_k − x_ℓ)|` for nodes `x_k = r^k` with `k < ℓ`. -/
lemma abs_ml2r_factor_of_lt {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {k ℓ : ℕ} (hk : k < ℓ) :
    |r ^ k / (r ^ k - r ^ ℓ)| = (1 - r ^ (ℓ - k))⁻¹ := by
  have hq : r ^ (ℓ - k) < 1 := pow_lt_one₀ hr0.le hr1 (Nat.sub_ne_zero_of_lt hk)
  have hℓ : r ^ ℓ = r ^ k * r ^ (ℓ - k) := by rw [← pow_add, Nat.add_sub_of_le hk.le]
  rw [hℓ, show r ^ k - r ^ k * r ^ (ℓ - k) = r ^ k * (1 - r ^ (ℓ - k)) by ring,
    div_mul_cancel_left₀ (pow_pos hr0 k).ne', abs_inv, abs_of_pos (by linarith)]

/-- `|x_k/(x_k − x_ℓ)|` for nodes `x_k = r^k` with `ℓ < k`. -/
lemma abs_ml2r_factor_of_gt {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {k ℓ : ℕ} (hk : ℓ < k) :
    |r ^ k / (r ^ k - r ^ ℓ)| = r ^ (k - ℓ) * (1 - r ^ (k - ℓ))⁻¹ := by
  have hq : r ^ (k - ℓ) < 1 := pow_lt_one₀ hr0.le hr1 (Nat.sub_ne_zero_of_lt hk)
  have hk' : r ^ k = r ^ ℓ * r ^ (k - ℓ) := by rw [← pow_add, Nat.add_sub_of_le hk.le]
  have hden : r ^ k - r ^ ℓ = -(r ^ ℓ * (1 - r ^ (k - ℓ))) := by rw [hk']; ring
  have heq : r ^ k / (r ^ k - r ^ ℓ) = -(r ^ (k - ℓ) * (1 - r ^ (k - ℓ))⁻¹) := by
    rw [hden, hk', div_neg, mul_div_mul_left _ _ (pow_pos hr0 ℓ).ne', div_eq_mul_inv]
  rw [heq, abs_neg, abs_mul, abs_of_pos (pow_pos hr0 _), abs_inv, abs_of_pos (by linarith)]

/-- `(1 − q)⁻¹ ≤ e^{q/(1−r)}` for `0 ≤ q ≤ r < 1`. -/
lemma inv_one_sub_le_exp {q r : ℝ} (hq0 : 0 ≤ q) (hqr : q ≤ r) (hr1 : r < 1) :
    (1 - q)⁻¹ ≤ Real.exp (q / (1 - r)) := by
  have h1 : 0 < 1 - r := by linarith
  have h2 : (1 - q) ≠ 0 := by linarith
  have h3 : 1 + q / (1 - q) = (1 - q)⁻¹ := by
    rw [← one_div, eq_div_iff h2, add_mul, div_mul_cancel₀ q h2]
    ring
  have h4 : q / (1 - q) ≤ q / (1 - r) := div_le_div_of_nonneg_left hq0 h1 (by linarith)
  rw [← h3]
  linarith [Real.add_one_le_exp (q / (1 - r))]

/-- `∑_{j=1}^{n} r^j ≤ r/(1 − r)` for `0 ≤ r < 1`, written as `∑_{j<n} r^{j+1}`. -/
lemma sum_pow_succ_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ range n, r ^ (j + 1) ≤ r / (1 - r) := by
  have h := geom_sum_le_of_lt_one hr0 hr1 n
  rw [show ∑ j ∈ range n, r ^ (j + 1) = r * ∑ j ∈ range n, r ^ j by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h hr0

/-- The factors of the weight `w_ℓ` from the nodes `x_k = r^k`, `k < ℓ`, multiply to at most
`e^{r/(1−r)²}`. -/
lemma prod_ml2r_factor_lt_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ℓ : ℕ) :
    ∏ k ∈ range ℓ, |r ^ k / (r ^ k - r ^ ℓ)| ≤ Real.exp (r / (1 - r) ^ 2) := by
  have h1 : 0 < 1 - r := by linarith
  calc ∏ k ∈ range ℓ, |r ^ k / (r ^ k - r ^ ℓ)|
      = ∏ k ∈ range ℓ, (1 - r ^ (ℓ - k))⁻¹ :=
        Finset.prod_congr rfl fun k hk => abs_ml2r_factor_of_lt hr0 hr1 (Finset.mem_range.1 hk)
    _ ≤ ∏ k ∈ range ℓ, Real.exp (r ^ (ℓ - k) / (1 - r)) := by
        refine Finset.prod_le_prod (fun k hk => ?_) fun k hk => ?_
        · have := pow_lt_one₀ hr0.le hr1 (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk))
          exact inv_nonneg.2 (by linarith)
        · exact inv_one_sub_le_exp (pow_nonneg hr0.le _)
            (pow_le_of_le_one hr0.le hr1.le (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk))) hr1
    _ = Real.exp (∑ k ∈ range ℓ, r ^ (ℓ - k) / (1 - r)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (r / (1 - r) ^ 2) := by
        refine Real.exp_le_exp.2 ?_
        have hre : ∑ k ∈ range ℓ, r ^ (ℓ - k) = ∑ j ∈ range ℓ, r ^ (j + 1) := by
          rw [← Finset.sum_range_reflect (fun j => r ^ (j + 1)) ℓ]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := Finset.mem_range.1 hk
          congr 1
          omega
        rw [← Finset.sum_div, hre, sq, ← div_div]
        exact div_le_div_of_nonneg_right (sum_pow_succ_le hr0.le hr1 ℓ) h1.le

/-- The factors of the weight `w_ℓ` from the nodes `x_k = r^k`, `ℓ < k ≤ L`, multiply to at most
`e^{r/(1−r)²} r^{L−ℓ}`. -/
lemma prod_ml2r_factor_gt_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ℓ L : ℕ) :
    ∏ k ∈ Ico (ℓ + 1) (L + 1), |r ^ k / (r ^ k - r ^ ℓ)| ≤
      Real.exp (r / (1 - r) ^ 2) * r ^ (L - ℓ) := by
  have h1 : 0 < 1 - r := by linarith
  have hkℓ : ∀ k ∈ Ico (ℓ + 1) (L + 1), ℓ < k := fun k hk => by
    have := (Finset.mem_Ico.1 hk).1
    omega
  have hq : ∀ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) < 1 := fun k hk =>
    pow_lt_one₀ hr0.le hr1 (Nat.sub_ne_zero_of_lt (hkℓ k hk))
  calc ∏ k ∈ Ico (ℓ + 1) (L + 1), |r ^ k / (r ^ k - r ^ ℓ)|
      = (∏ k ∈ Ico (ℓ + 1) (L + 1), (1 - r ^ (k - ℓ))⁻¹) *
          ∏ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun k hk => by
          rw [abs_ml2r_factor_of_gt hr0 hr1 (hkℓ k hk), mul_comm]
    _ ≤ Real.exp (r / (1 - r) ^ 2) * r ^ (L - ℓ) := by
        refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun k _ => pow_nonneg hr0.le _)
          (Real.exp_pos _).le
        · calc ∏ k ∈ Ico (ℓ + 1) (L + 1), (1 - r ^ (k - ℓ))⁻¹
              ≤ ∏ k ∈ Ico (ℓ + 1) (L + 1), Real.exp (r ^ (k - ℓ) / (1 - r)) := by
                refine Finset.prod_le_prod (fun k hk => ?_) fun k hk => ?_
                · exact inv_nonneg.2 (by linarith [hq k hk])
                · exact inv_one_sub_le_exp (pow_nonneg hr0.le _)
                    (pow_le_of_le_one hr0.le hr1.le (Nat.sub_ne_zero_of_lt (hkℓ k hk))) hr1
            _ = Real.exp (∑ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) / (1 - r)) :=
                (Real.exp_sum _ _).symm
            _ ≤ Real.exp (r / (1 - r) ^ 2) := by
                refine Real.exp_le_exp.2 ?_
                have hre : ∑ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) =
                    ∑ j ∈ range (L + 1 - (ℓ + 1)), r ^ (j + 1) := by
                  rw [Finset.sum_Ico_eq_sum_range]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  congr 1
                  omega
                rw [← Finset.sum_div, hre, sq, ← div_div]
                exact div_le_div_of_nonneg_right (sum_pow_succ_le hr0.le hr1 _) h1.le
        · calc ∏ k ∈ Ico (ℓ + 1) (L + 1), r ^ (k - ℓ) ≤ ∏ _k ∈ Ico (ℓ + 1) (L + 1), r :=
                Finset.prod_le_prod (fun k _ => pow_nonneg hr0.le _) fun k hk =>
                  pow_le_of_le_one hr0.le hr1.le (Nat.sub_ne_zero_of_lt (hkℓ k hk))
            _ = r ^ (L - ℓ) := by
                rw [Finset.prod_const, Nat.card_Ico]
                congr 1
                omega

/-- The product defining an ML2R weight, for the nodes `x_k = r^k`, `0 < r < 1`: for `ℓ ≤ L`,
`|∏_{k ≤ L, k ≠ ℓ} x_k/(x_k − x_ℓ)| ≤ e^{2r/(1−r)²} r^{L−ℓ}`. -/
lemma abs_prod_ml2r_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {L ℓ : ℕ} (hℓ : ℓ ≤ L) :
    |∏ k ∈ (range (L + 1)).erase ℓ, r ^ k / (r ^ k - r ^ ℓ)| ≤
      Real.exp (r / (1 - r) ^ 2) ^ 2 * r ^ (L - ℓ) := by
  have hsplit : (range (L + 1)).erase ℓ = range ℓ ∪ Ico (ℓ + 1) (L + 1) := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (range ℓ) (Ico (ℓ + 1) (L + 1)) := by
    refine Finset.disjoint_left.2 fun k h1 h2 => ?_
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2
    omega
  rw [Finset.abs_prod, hsplit, Finset.prod_union hdisj]
  calc (∏ k ∈ range ℓ, |r ^ k / (r ^ k - r ^ ℓ)|) *
        ∏ k ∈ Ico (ℓ + 1) (L + 1), |r ^ k / (r ^ k - r ^ ℓ)|
      ≤ Real.exp (r / (1 - r) ^ 2) * (Real.exp (r / (1 - r) ^ 2) * r ^ (L - ℓ)) :=
        mul_le_mul (prod_ml2r_factor_lt_le hr0 hr1 ℓ) (prod_ml2r_factor_gt_le hr0 hr1 ℓ L)
          (Finset.prod_nonneg fun k _ => abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (r / (1 - r) ^ 2) ^ 2 * r ^ (L - ℓ) := by ring

/-- The sum over `ℓ ≤ L` of the bounds of `abs_prod_ml2r_le`: at most `e^{2r/(1−r)²}/(1 − r)`,
whatever `L`. -/
lemma sum_abs_prod_ml2r_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (L : ℕ) :
    ∑ ℓ ∈ range (L + 1), |∏ k ∈ (range (L + 1)).erase ℓ, r ^ k / (r ^ k - r ^ ℓ)| ≤
      Real.exp (r / (1 - r) ^ 2) ^ 2 * (1 - r)⁻¹ := by
  calc ∑ ℓ ∈ range (L + 1), |∏ k ∈ (range (L + 1)).erase ℓ, r ^ k / (r ^ k - r ^ ℓ)|
      ≤ ∑ ℓ ∈ range (L + 1), Real.exp (r / (1 - r) ^ 2) ^ 2 * r ^ (L - ℓ) :=
        Finset.sum_le_sum fun ℓ hℓ =>
          abs_prod_ml2r_le hr0 hr1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ))
    _ = Real.exp (r / (1 - r) ^ 2) ^ 2 * ∑ j ∈ range (L + 1), r ^ j := by
        rw [← Finset.mul_sum, ← Finset.sum_range_reflect (fun j => r ^ j) (L + 1)]
        congr 1
    _ ≤ Real.exp (r / (1 - r) ^ 2) ^ 2 * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_left (geom_sum_le_of_lt_one hr0.le hr1 _)
          (pow_nonneg (Real.exp_pos _).le 2)

/-- The ML2R weight as a product over the nodes `x_k = r^k`, `r = 2^{−α}`. -/
lemma ml2rWeight_eq_prod (α : ℝ) (L ℓ : ℕ) :
    ml2rWeight α L ℓ = ∏ k ∈ (range (L + 1)).erase ℓ,
      ((2 : ℝ) ^ (-α)) ^ k / (((2 : ℝ) ^ (-α)) ^ k - ((2 : ℝ) ^ (-α)) ^ ℓ) := by
  simp only [ml2rWeight, ml2rNode_eq]

/-- **The ML2R weights decay away from the finest level** (Giles 2015, §2.3): with
`r = 2^{−α}` (`α > 0`) and `B = e^{r/(1−r)²}`, the weight of level `ℓ ≤ L` satisfies
`|w_ℓ| ≤ B² r^{L−ℓ}`, uniformly in `L`. -/
theorem abs_ml2rWeight_le {α : ℝ} (hα : 0 < α) {L ℓ : ℕ} (hℓ : ℓ ≤ L) :
    |ml2rWeight α L ℓ| ≤
      Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 * ((2 : ℝ) ^ (-α)) ^ (L - ℓ) := by
  rw [ml2rWeight_eq_prod]
  exact abs_prod_ml2r_le (Real.rpow_pos_of_pos two_pos _)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)) hℓ

/-- The constant `B²/(1 − r)` bounding the ML2R weights, with `r = 2^{−α}` and
`B = e^{r/(1−r)²}` (Giles 2015, §2.3). -/
noncomputable def ml2rWeightBound (α : ℝ) : ℝ :=
  Real.exp ((2 : ℝ) ^ (-α) / (1 - (2 : ℝ) ^ (-α)) ^ 2) ^ 2 / (1 - (2 : ℝ) ^ (-α))

lemma ml2rWeightBound_pos {α : ℝ} (hα : 0 < α) : 0 < ml2rWeightBound α := by
  have hr1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  exact div_pos (pow_pos (Real.exp_pos _) 2) (by linarith)

/-- **The ML2R weights are bounded uniformly in `L`** (Giles 2015, §2.3): for `α > 0`,
`∑_{ℓ=0}^{L} |w_ℓ| ≤ ml2rWeightBound α` for every `L`. -/
theorem sum_abs_ml2rWeight_le {α : ℝ} (hα : 0 < α) (L : ℕ) :
    ∑ ℓ ∈ range (L + 1), |ml2rWeight α L ℓ| ≤ ml2rWeightBound α := by
  simp only [ml2rWeight_eq_prod]
  rw [ml2rWeightBound, div_eq_mul_inv]
  exact sum_abs_prod_ml2r_le (Real.rpow_pos_of_pos two_pos _)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)) L

/-- **The coefficients of the ML2R estimator are bounded uniformly in `L`** (Giles 2015, §2.3):
`|v_ℓ| = |∑_{ℓ'=ℓ}^{L} w_ℓ'| ≤ ml2rWeightBound α`. -/
theorem abs_ml2r_coeff_le {α : ℝ} (hα : 0 < α) (L ℓ : ℕ) :
    |∑ k ∈ Ico ℓ (L + 1), ml2rWeight α L k| ≤ ml2rWeightBound α := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum_of_subset_of_nonneg ?_
    fun k _ _ => abs_nonneg _).trans (sum_abs_ml2rWeight_le hα L))
  intro k hk
  simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
  omega

end weights

/-! ### The number of levels -/

section levels

/-- **The number of levels of ML2R** (Giles 2015, §2.3): `L = ⌈√(2 log₂⁺(2c₁/ε)/α)⌉`, with
`log₂⁺ = max 0 log₂`, the least `L` whose remaining error `c₁ 2^{−αL(L+1)/2}` is guaranteed to be
at most `ε/2` by `ml2rLevel_bias`. -/
noncomputable def ml2rLevel (α c₁ ε : ℝ) : ℕ :=
  ⌈Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α)⌉₊

/-- **ML2R reaches the weak error `ε/2`** (Giles 2015, §2.3): with `L = ml2rLevel α c₁ ε`, the
remaining error bound of `ml2r_bias`, `c₁ 2^{−αL(L+1)/2}`, is at most `ε/2`. -/
theorem ml2rLevel_bias {α c₁ ε : ℝ} (hα : 0 < α) (hc₁ : 0 < c₁) (hε : 0 < ε) :
    c₁ * (2 : ℝ) ^ (-(α * ((ml2rLevel α c₁ ε : ℝ) * (ml2rLevel α c₁ ε + 1) / 2))) ≤ ε / 2 := by
  have hL : Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α) ≤ (ml2rLevel α c₁ ε : ℝ) :=
    Nat.le_ceil _
  generalize ml2rLevel α c₁ ε = L at hL ⊢
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hy0 : 0 ≤ 2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α :=
    div_nonneg (mul_nonneg zero_le_two (le_max_left _ _)) hα.le
  have hsq : 2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α ≤ (L : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL 2
    rwa [Real.sq_sqrt hy0] at this
  have h2 : 2 * max 0 (Real.logb 2 (2 * c₁ / ε)) ≤ α * (L : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hα.le
    rwa [alpha_mul_div hα] at this
  have hexp : Real.logb 2 (2 * c₁ / ε) ≤ α * ((L : ℝ) * (L + 1) / 2) := by
    have h1 := le_max_right 0 (Real.logb 2 (2 * c₁ / ε))
    nlinarith [mul_nonneg hα.le hL0]
  have hpos : 0 < 2 * c₁ / ε := div_pos (by linarith) hε
  have h3 : 2 * c₁ / ε ≤ (2 : ℝ) ^ (α * ((L : ℝ) * (L + 1) / 2)) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hpos).1 hexp
  have hp : 0 < (2 : ℝ) ^ (α * ((L : ℝ) * (L + 1) / 2)) := Real.rpow_pos_of_pos two_pos _
  rw [div_le_iff₀ hε] at h3
  rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, div_le_iff₀ hp]
  linarith

/-- `L < √(2 log₂⁺(2c₁/ε)/α) + 1` for `L = ml2rLevel α c₁ ε`. -/
lemma ml2rLevel_lt (α c₁ ε : ℝ) :
    (ml2rLevel α c₁ ε : ℝ) < Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α) + 1 :=
  Nat.ceil_lt_add_one (Real.sqrt_nonneg _)

/-- **The number of levels is the square root of the usual value** (Giles 2015, §2.3: "it is
possible to obtain the usual `O(ε)` weak error with a value of `L` which is the square root of the
usual value").  Standard MLMC needs `levelL α c₁ (ε/2) = ⌈log₂(2c₁/ε)/α⌉` levels for the bias
`c₁ 2^{−αL} ≤ ε/2` (`levelL_bias`); ML2R needs at most `√(2 · levelL α c₁ (ε/2)) + 1`. -/
theorem ml2rLevel_lt_sqrt_levelL {α : ℝ} (hα : 0 < α) (c₁ ε : ℝ) :
    (ml2rLevel α c₁ ε : ℝ) < Real.sqrt (2 * levelL α c₁ (ε / 2)) + 1 := by
  refine (ml2rLevel_lt α c₁ ε).trans_le (add_le_add (Real.sqrt_le_sqrt ?_) le_rfl)
  have h1 : Real.logb 2 (c₁ / (ε / 2)) / α ≤ levelL α c₁ (ε / 2) := Nat.le_ceil _
  rw [show c₁ / (ε / 2) = 2 * c₁ / ε by ring] at h1
  have h0 : (0 : ℝ) ≤ levelL α c₁ (ε / 2) := Nat.cast_nonneg _
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  rcases le_total 0 (Real.logb 2 (2 * c₁ / ε)) with h | h
  · rw [max_eq_right h]
    exact h1
  · rw [max_eq_left h, zero_div]
    exact h0

/-- `t √(2y/α) ≤ y + t²/(2α)` (the arithmetic–geometric mean inequality). -/
lemma mul_sqrt_le {α y : ℝ} (hα : 0 < α) (hy : 0 ≤ y) (t : ℝ) :
    t * Real.sqrt (2 * y / α) ≤ y + t ^ 2 / (2 * α) := by
  have hs : Real.sqrt (2 * y / α) ^ 2 = 2 * y / α :=
    Real.sq_sqrt (div_nonneg (mul_nonneg zero_le_two hy) hα.le)
  generalize Real.sqrt (2 * y / α) = s at hs ⊢
  have hy2 : α * s ^ 2 = 2 * y := by rw [hs, alpha_mul_div hα]
  have hy3 : α ^ 2 * s ^ 2 = 2 * α * y := by linear_combination α * hy2
  have key : 0 ≤ (α * s - t) ^ 2 := sq_nonneg _
  have h2α : 0 < 2 * α := by linarith
  have h1 : 2 * α * (t * s) ≤ 2 * α * (y + t ^ 2 / (2 * α)) := by
    rw [mul_add, alpha_mul_div h2α]
    nlinarith
  exact le_of_mul_le_mul_left h1 h2α

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
lemma sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt a + Real.sqrt b :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))

/-- `2^{max 0 (log₂ x)} ≤ max 1 x` for `x > 0`. -/
lemma two_rpow_max_logb {x : ℝ} (hx : 0 < x) :
    (2 : ℝ) ^ max 0 (Real.logb 2 x) = max 1 x := by
  rcases le_total 0 (Real.logb 2 x) with h | h
  · rw [max_eq_right h, Real.rpow_logb (by norm_num) (by norm_num) hx,
      max_eq_right ((Real.logb_nonneg_iff (by norm_num) hx).1 h)]
  · have hx1 : x ≤ 1 := by
      by_contra hgt
      have : 0 < Real.logb 2 x := Real.logb_pos (by norm_num) (not_le.1 hgt)
      linarith
    rw [max_eq_left h, Real.rpow_zero, max_eq_left hx1]

/-- `2^{tL} ≤ 2^{t + t²/(2α)} (1 + 2c₁)/ε` for `L = ml2rLevel α c₁ ε`, `t ≥ 0` and `0 < ε ≤ 1`: the
number of levels grows so slowly that `2^{tL}` is `O(ε⁻¹)` for every `t`. -/
lemma two_rpow_mul_ml2rLevel_le {α c₁ ε t : ℝ} (hα : 0 < α) (hc₁ : 0 < c₁) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    (2 : ℝ) ^ (t * ml2rLevel α c₁ ε) ≤ 2 ^ (t + t ^ 2 / (2 * α)) * ((1 + 2 * c₁) / ε) := by
  have hL := ml2rLevel_lt α c₁ ε
  have hx0 : 0 ≤ max 0 (Real.logb 2 (2 * c₁ / ε)) := le_max_left _ _
  have hpos : 0 < 2 * c₁ / ε := div_pos (by linarith) hε
  have hexp : t * (ml2rLevel α c₁ ε : ℝ) ≤
      max 0 (Real.logb 2 (2 * c₁ / ε)) + (t + t ^ 2 / (2 * α)) := by
    have h1 := mul_le_mul_of_nonneg_left hL.le ht
    have h2 := mul_sqrt_le hα hx0 t
    nlinarith
  have hmax : max 1 (2 * c₁ / ε) ≤ (1 + 2 * c₁) / ε := by
    refine max_le ?_ ?_
    · rw [le_div_iff₀ hε]
      nlinarith
    · exact div_le_div_of_nonneg_right (by linarith) hε.le
  calc (2 : ℝ) ^ (t * ml2rLevel α c₁ ε)
      ≤ 2 ^ (max 0 (Real.logb 2 (2 * c₁ / ε)) + (t + t ^ 2 / (2 * α))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 2 ^ (t + t ^ 2 / (2 * α)) * max 1 (2 * c₁ / ε) := by
        rw [Real.rpow_add two_pos, two_rpow_max_logb hpos]
        ring
    _ ≤ 2 ^ (t + t ^ 2 / (2 * α)) * ((1 + 2 * c₁) / ε) :=
        mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by norm_num) _)

/-- `log₂⁺(2c₁/ε) ≤ A |log ε|` with `A = (|log(2c₁)| + 1)/log 2`, for `0 < ε < e⁻¹`. -/
lemma max_logb_le {c₁ ε : ℝ} (hc₁ : 0 < c₁) (hε : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    max 0 (Real.logb 2 (2 * c₁ / ε)) ≤
      (|Real.log (2 * c₁)| + 1) / Real.log 2 * (-Real.log ε) := by
  have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA : 0 ≤ (|Real.log (2 * c₁)| + 1) / Real.log 2 * (-Real.log ε) :=
    mul_nonneg (div_nonneg (by positivity) hl2.le) (by linarith)
  refine max_le hA ?_
  rw [Real.logb, Real.log_div (mul_pos two_pos hc₁).ne' hε.ne', div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hl2]
  have h3 : Real.log (2 * c₁) ≤ |Real.log (2 * c₁)| * (-Real.log ε) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) ht)
  nlinarith

/-- `(L + 1)² ≤ K |log ε|` for `L = ml2rLevel α c₁ ε` and `0 < ε < e⁻¹`, with
`K = 4(|log(2c₁)| + 1)/(α log 2) + 8`: the square of the number of levels is `O(|log ε|)`. -/
lemma sq_ml2rLevel_add_one_le {α c₁ ε : ℝ} (hα : 0 < α) (hc₁ : 0 < c₁) (hε : 0 < ε)
    (hε1 : ε < Real.exp (-1)) :
    ((ml2rLevel α c₁ ε : ℝ) + 1) ^ 2 ≤
      (4 * ((|Real.log (2 * c₁)| + 1) / Real.log 2) / α + 8) * (-Real.log ε) := by
  have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
  have hL := ml2rLevel_lt α c₁ ε
  have hL0 : (0 : ℝ) ≤ ml2rLevel α c₁ ε := Nat.cast_nonneg _
  have hx := max_logb_le hc₁ hε hε1
  have hx0 : 0 ≤ max 0 (Real.logb 2 (2 * c₁ / ε)) := le_max_left _ _
  have hs0 : 0 ≤ Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α) ^ 2 =
      2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α :=
    Real.sq_sqrt (div_nonneg (mul_nonneg zero_le_two hx0) hα.le)
  generalize Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α) = s at hL hs0 hs2
  have h1 : ((ml2rLevel α c₁ ε : ℝ) + 1) ^ 2 ≤ (s + 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : (s + 2) ^ 2 ≤ 2 * s ^ 2 + 8 := by nlinarith [sq_nonneg (s - 2)]
  have h3 : 2 * s ^ 2 ≤ 4 * ((|Real.log (2 * c₁)| + 1) / Real.log 2) / α * (-Real.log ε) := by
    rw [hs2, show 2 * (2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α) =
      4 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α by ring, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hα]
    nlinarith
  nlinarith

end levels

/-! ### Mean square error and cost -/

section cost

/-- **The mean square error and the cost of the ML2R estimator for a given number of levels**
(Giles 2015, §2.3).  Let `α > 0`, `V_ℓ = c₂ 2^{−βℓ}`, `C_ℓ = c₃ 2^{γℓ}` (`Vb`, `Cb`), and let `L`
make the remaining error bound at most `ε/2`: `c₁ 2^{−αL(L+1)/2} ≤ ε/2` (`ml2r_bias`,
`ml2rLevel_bias`).  With `W = ml2rWeightBound α` and the rounded-up optimal allocation for the
variances `W² V_ℓ` and the target `ε²/2`, the estimator of `ml2r_estimator_mean_variance`, whose
variance is `∑_ℓ v_ℓ² V_ℓ/N_ℓ`, has mean square error bound `< ε²`, and its cost is at most
`2 ε⁻² W² c₂ c₃ (∑_{ℓ≤L} r^ℓ)² + ∑_{ℓ≤L} C_ℓ` with `r = 2^{(γ−β)/2}`. -/
theorem ml2r_mse_cost {α β γ c₁ c₂ c₃ ε : ℝ} (hα : 0 < α) (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂)
    (hc₃ : 0 < c₃) (hε : 0 < ε) (L : ℕ)
    (hbias : c₁ * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2))) ≤ ε / 2) :
    ∃ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) ∧
      (c₁ * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2)))) ^ 2 +
          ∑ ℓ ∈ range (L + 1),
            (∑ k ∈ Ico ℓ (L + 1), ml2rWeight α L k) ^ 2 * Vb β c₂ ℓ / (N ℓ : ℝ) < ε ^ 2 ∧
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ ≤
        2 * (ε ^ 2)⁻¹ * (ml2rWeightBound α ^ 2 * (c₂ * c₃)) *
            (∑ ℓ ∈ range (L + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2 +
          ∑ ℓ ∈ range (L + 1), Cb γ c₃ ℓ := by
  have hW := ml2rWeightBound_pos hα
  have hs : (range (L + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos L)⟩
  have hτ : 0 < ε ^ 2 / 2 := by positivity
  have hV : ∀ ℓ, 0 < ml2rWeightBound α ^ 2 * Vb β c₂ ℓ := fun ℓ =>
    mul_pos (pow_pos hW 2) (Vb_pos hc₂ ℓ)
  have hC : ∀ ℓ, 0 < Cb γ c₃ ℓ := fun ℓ => Cb_pos hc₃ ℓ
  refine ⟨optimalN (range (L + 1)) (fun ℓ => ml2rWeightBound α ^ 2 * Vb β c₂ ℓ) (Cb γ c₃)
    (ε ^ 2 / 2), fun ℓ => optimalN_pos hs hV hC hτ ℓ, ?_, ?_⟩
  · have hvar := optimalN_variance hs (fun ℓ _ => hV ℓ) (fun ℓ _ => hC ℓ) hτ
    have hterm : ∀ ℓ ∈ range (L + 1),
        (∑ k ∈ Ico ℓ (L + 1), ml2rWeight α L k) ^ 2 * Vb β c₂ ℓ /
            (optimalN (range (L + 1)) (fun ℓ => ml2rWeightBound α ^ 2 * Vb β c₂ ℓ) (Cb γ c₃)
              (ε ^ 2 / 2) ℓ : ℝ) ≤
          ml2rWeightBound α ^ 2 * Vb β c₂ ℓ /
            (optimalN (range (L + 1)) (fun ℓ => ml2rWeightBound α ^ 2 * Vb β c₂ ℓ) (Cb γ c₃)
              (ε ^ 2 / 2) ℓ : ℝ) := by
      intro ℓ _
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Vb_pos hc₂ ℓ).le)
        (Nat.cast_nonneg _)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_ml2r_coeff_le hα L ℓ) 2
    have hb2 : (c₁ * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2)))) ^ 2 ≤ (ε / 2) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hc₁ (Real.rpow_nonneg (by norm_num) _)) hbias 2
    have hsum := (Finset.sum_le_sum hterm).trans hvar
    have hε2 : 0 < ε ^ 2 := by positivity
    nlinarith
  · refine (optimalN_cost hs (fun ℓ _ => hV ℓ) (fun ℓ _ => hC ℓ) hτ).trans (le_of_eq ?_)
    have hsqrt : ∀ ℓ, Real.sqrt (ml2rWeightBound α ^ 2 * Vb β c₂ ℓ * Cb γ c₃ ℓ) =
        ml2rWeightBound α * (Real.sqrt (c₂ * c₃) * ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) := by
      intro ℓ
      rw [mul_assoc, Real.sqrt_mul (pow_nonneg hW.le 2), Real.sqrt_sq hW.le,
        sqrt_Vb_mul_Cb hc₂ hc₃ ℓ]
    simp only [hsqrt]
    rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow, mul_pow,
      Real.sq_sqrt (mul_pos hc₂ hc₃).le, inv_div]
    ring

/-- The rounding-up overhead of ML2R: `∑_{ℓ≤L} C_ℓ ≤ K ε⁻¹` for `L = ml2rLevel α c₁ ε`,
`0 < ε ≤ 1`, with `K = c₃ (2^γ/(2^γ − 1)) 2^{γ + γ²/(2α)} (1 + 2c₁)`. -/
lemma ml2r_tail_cost {α γ c₁ c₃ ε : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hc₁ : 0 < c₁) (hc₃ : 0 < c₃)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), Cb γ c₃ ℓ ≤
      c₃ * (2 ^ γ / (2 ^ γ - 1)) * ((2 : ℝ) ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁)) * ε⁻¹ := by
  have hKt : 0 < (2 : ℝ) ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁) :=
    mul_pos (Real.rpow_pos_of_pos two_pos _) (by linarith)
  have h2L := two_rpow_mul_ml2rLevel_le hα hc₁ hε hε1 hγ.le
  have hL' : (2 : ℝ) ^ (γ * (ml2rLevel α c₁ ε : ℝ)) ≤
      (2 ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁)) / ε := by
    rwa [mul_div_assoc]
  have htc := tail_cost_bound hγ hγ hc₃ hKt hε (ml2rLevel α c₁ ε) hL'
  have hCb : ∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), Cb γ c₃ ℓ =
      c₃ * ∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), ((2 : ℝ) ^ γ) ^ ℓ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by rw [Cb, two_rpow_mul_nat]
  rw [hCb]
  refine htc.trans (le_of_eq ?_)
  rw [div_self hγ.ne', Real.rpow_one, Real.rpow_neg_one]
  ring

/-- **ML2R in the case `β = γ`** (Giles 2015, §2.3: "Hence, in the case `β = γ` they prove that the
overall cost is reduced to `O(ε⁻² |log ε|)`", after Lemaire and Pagès).  Let `α, γ > 0`, `β = γ`
and `c₁, c₂, c₃ > 0`, with the remaining error bound `c₁ 2^{−αL(L+1)/2}` of `ml2r_bias`,
`V_ℓ = c₂ 2^{−βℓ}` and `C_ℓ = c₃ 2^{γℓ}`.  There is `c₄ > 0` such that for every `0 < ε < e⁻¹`
there are `L` and `N_ℓ ≥ 1` for which the ML2R estimator has mean square error bound `< ε²` and
cost at most `c₄ ε⁻² |log ε|`; standard MLMC costs `ε⁻² (log ε)²` in this case
(`giles_theorem1`). -/
theorem ml2r_complexity_eq {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hβγ : β = γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (c₁ * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2)))) ^ 2 +
            ∑ ℓ ∈ range (L + 1),
              (∑ k ∈ Ico ℓ (L + 1), ml2rWeight α L k) ^ 2 * Vb β c₂ ℓ / (N ℓ : ℝ) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ ≤
          c₄ * (ε ^ (-2 : ℝ) * |Real.log ε|) := by
  have hW := ml2rWeightBound_pos hα
  have hg : 1 < (2 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hK₁0 : 0 ≤ 4 * ((|Real.log (2 * c₁)| + 1) / Real.log 2) / α :=
    div_nonneg (mul_nonneg (by norm_num) (div_nonneg (by positivity) hl2.le)) hα.le
  have hK₂0 : 0 < c₃ * (2 ^ γ / (2 ^ γ - 1)) *
      ((2 : ℝ) ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁)) :=
    mul_pos (mul_pos hc₃ (div_pos (by linarith) (by linarith)))
      (mul_pos (Real.rpow_pos_of_pos two_pos _) (by linarith))
  have hX : 0 < ml2rWeightBound α ^ 2 * (c₂ * c₃) := mul_pos (pow_pos hW 2) (mul_pos hc₂ hc₃)
  refine ⟨2 * (ml2rWeightBound α ^ 2 * (c₂ * c₃)) *
      (4 * ((|Real.log (2 * c₁)| + 1) / Real.log 2) / α + 8) +
      c₃ * (2 ^ γ / (2 ^ γ - 1)) * ((2 : ℝ) ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁)),
    ?_, fun ε hε hε1 => ?_⟩
  · have h1 : 0 < 2 * (ml2rWeightBound α ^ 2 * (c₂ * c₃)) *
        (4 * ((|Real.log (2 * c₁)| + 1) / Real.log 2) / α + 8) :=
      mul_pos (mul_pos two_pos hX) (by linarith)
    have h2 : 0 < c₃ * (2 ^ γ / (2 ^ γ - 1)) *
        ((2 : ℝ) ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁)) :=
      mul_pos (mul_pos hc₃ (div_pos (by linarith) (by linarith)))
        (mul_pos (Real.rpow_pos_of_pos two_pos _) (by linarith))
    linarith
  have hε1' : ε < 1 := eps_lt_one hε1
  have ht : 1 ≤ -Real.log ε := one_le_neg_log hε hε1
  have habs : |Real.log ε| = -Real.log ε := abs_of_neg (by linarith)
  have hepow : ε ^ (-2 : ℝ) = (ε ^ 2)⁻¹ := by rw [← eps_inv_sq_eq hε, inv_pow]
  have hε2 : 0 < (ε ^ 2)⁻¹ := by positivity
  obtain ⟨N, hN, hmse, hcost⟩ := ml2r_mse_cost (β := β) (γ := γ) hα hc₁.le hc₂ hc₃ hε
    (ml2rLevel α c₁ ε) (ml2rLevel_bias hα hc₁ hε)
  refine ⟨ml2rLevel α c₁ ε, N, hN, hmse, hcost.trans ?_⟩
  have hsum : ∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ =
      (ml2rLevel α c₁ ε : ℝ) + 1 := by
    rw [hβγ, sub_self, zero_div, Real.rpow_zero]
    simp
  have hsq := sq_ml2rLevel_add_one_le hα hc₁ hε hε1
  have htail := ml2r_tail_cost hα hγ hc₁ hc₃ hε hε1'.le
  have hinv : ε⁻¹ ≤ (ε ^ 2)⁻¹ * (-Real.log ε) := by
    have h1 : ε⁻¹ ≤ (ε ^ 2)⁻¹ := by
      rw [inv_le_inv₀ hε (by positivity)]
      nlinarith
    calc ε⁻¹ ≤ (ε ^ 2)⁻¹ := h1
      _ = (ε ^ 2)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (ε ^ 2)⁻¹ * (-Real.log ε) := mul_le_mul_of_nonneg_left ht hε2.le
  rw [hsum, hepow, habs]
  generalize c₃ * (2 ^ γ / (2 ^ γ - 1)) * ((2 : ℝ) ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁)) = K₂
    at htail hK₂0 ⊢
  generalize 4 * ((|Real.log (2 * c₁)| + 1) / Real.log 2) / α + 8 = K₁ at hsq ⊢
  generalize ml2rWeightBound α ^ 2 * (c₂ * c₃) = X at hX ⊢
  generalize ((ml2rLevel α c₁ ε : ℝ) + 1) ^ 2 = Q at hsq ⊢
  have hfirst : 2 * (ε ^ 2)⁻¹ * X * Q ≤ 2 * X * K₁ * ((ε ^ 2)⁻¹ * (-Real.log ε)) := by
    have h0 : 0 ≤ 2 * (ε ^ 2)⁻¹ * X := mul_nonneg (mul_nonneg zero_le_two hε2.le) hX.le
    calc 2 * (ε ^ 2)⁻¹ * X * Q ≤ 2 * (ε ^ 2)⁻¹ * X * (K₁ * (-Real.log ε)) :=
          mul_le_mul_of_nonneg_left hsq h0
      _ = 2 * X * K₁ * ((ε ^ 2)⁻¹ * (-Real.log ε)) := by ring
  have hK₂inv : K₂ * ε⁻¹ ≤ K₂ * ((ε ^ 2)⁻¹ * (-Real.log ε)) :=
    mul_le_mul_of_nonneg_left hinv hK₂0.le
  calc 2 * (ε ^ 2)⁻¹ * X * Q + ∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), Cb γ c₃ ℓ
      ≤ 2 * X * K₁ * ((ε ^ 2)⁻¹ * (-Real.log ε)) + K₂ * ((ε ^ 2)⁻¹ * (-Real.log ε)) := by
        linarith
    _ = (2 * X * K₁ + K₂) * ((ε ^ 2)⁻¹ * (-Real.log ε)) := by ring

/-- **ML2R in the case `β < γ`** (Giles 2015, §2.3: "while for `β < γ` the cost is reduced much
more to `O(ε⁻² 2^{(γ−β)√(|log₂ ε|/α)})`", after Lemaire and Pagès).  Let `0 < α`, `β < γ`,
`0 < γ` and `c₁, c₂, c₃ > 0`, with the remaining error bound `c₁ 2^{−αL(L+1)/2}` of `ml2r_bias`,
`V_ℓ = c₂ 2^{−βℓ}` and `C_ℓ = c₃ 2^{γℓ}`.  There is `c₄ > 0` such that for every `0 < ε < e⁻¹`
there are `L` and `N_ℓ ≥ 1` for which the ML2R estimator has mean square error bound `< ε²` and
cost at most `c₄ ε⁻² 2^{(γ−β)√(2 log₂(1/ε)/α)}`.  The exponent is `√2` times the printed one
because the remaining error is `2^{−αL(L+1)/2}` (`ml2r_bias`), not the printed `2^{−αL²}`; it is
`o(log(1/ε))`, so the cost is `ε^{−2−δ}` for every `δ > 0`, against `ε^{−2−(γ−β)/α}` for standard
MLMC (`giles_theorem1`). -/
theorem ml2r_complexity_lt {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hβγ : β < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        (c₁ * (2 : ℝ) ^ (-(α * ((L : ℝ) * (L + 1) / 2)))) ^ 2 +
            ∑ ℓ ∈ range (L + 1),
              (∑ k ∈ Ico ℓ (L + 1), ml2rWeight α L k) ^ 2 * Vb β c₂ ℓ / (N ℓ : ℝ) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ ≤
          c₄ * (ε ^ (-2 : ℝ) * (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α))) := by
  have hW := ml2rWeightBound_pos hα
  have hg : 1 < (2 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  have hδ : 0 < γ - β := by linarith
  have hq : 1 < (2 : ℝ) ^ ((γ - β) / 2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hm0 : 0 ≤ max 0 (Real.logb 2 (2 * c₁)) := le_max_left _ _
  -- the constant of the first term
  have hC₁ : 0 < 2 * (ml2rWeightBound α ^ 2 * (c₂ * c₃)) *
      ((2 : ℝ) ^ ((γ - β) / 2) / ((2 : ℝ) ^ ((γ - β) / 2) - 1)) ^ 2 * 2 ^ (γ - β) *
        2 ^ ((γ - β) * Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁)) / α)) := by
    have : 0 < (2 : ℝ) ^ ((γ - β) / 2) / ((2 : ℝ) ^ ((γ - β) / 2) - 1) :=
      div_pos (by linarith) (by linarith)
    have h2 : 0 < (2 : ℝ) ^ (γ - β) := Real.rpow_pos_of_pos two_pos _
    have h3 : 0 < (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁)) / α)) :=
      Real.rpow_pos_of_pos two_pos _
    have h4 : 0 < ml2rWeightBound α ^ 2 * (c₂ * c₃) := mul_pos (pow_pos hW 2) (mul_pos hc₂ hc₃)
    exact mul_pos (mul_pos (mul_pos (mul_pos two_pos h4) (pow_pos this 2)) h2) h3
  have hK₂0 : 0 < c₃ * (2 ^ γ / (2 ^ γ - 1)) *
      ((2 : ℝ) ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁)) :=
    mul_pos (mul_pos hc₃ (div_pos (by linarith) (by linarith)))
      (mul_pos (Real.rpow_pos_of_pos two_pos _) (by linarith))
  refine ⟨2 * (ml2rWeightBound α ^ 2 * (c₂ * c₃)) *
      ((2 : ℝ) ^ ((γ - β) / 2) / ((2 : ℝ) ^ ((γ - β) / 2) - 1)) ^ 2 * 2 ^ (γ - β) *
        2 ^ ((γ - β) * Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁)) / α)) +
      c₃ * (2 ^ γ / (2 ^ γ - 1)) * ((2 : ℝ) ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁)),
    by linarith, fun ε hε hε1 => ?_⟩
  have hε1' : ε < 1 := eps_lt_one hε1
  have hepow : ε ^ (-2 : ℝ) = (ε ^ 2)⁻¹ := by rw [← eps_inv_sq_eq hε, inv_pow]
  have hε2 : 0 < (ε ^ 2)⁻¹ := by positivity
  obtain ⟨N, hN, hmse, hcost⟩ := ml2r_mse_cost (β := β) (γ := γ) hα hc₁.le hc₂ hc₃ hε
    (ml2rLevel α c₁ ε) (ml2rLevel_bias hα hc₁ hε)
  refine ⟨ml2rLevel α c₁ ε, N, hN, hmse, hcost.trans ?_⟩
  -- `log₂⁺(2c₁/ε) ≤ log₂(1/ε) + log₂⁺(2c₁)`
  have hlinv : 0 ≤ Real.logb 2 ε⁻¹ := by
    rw [Real.logb_inv]
    have := Real.logb_neg (by norm_num : (1 : ℝ) < 2) hε hε1'
    linarith
  have hx : max 0 (Real.logb 2 (2 * c₁ / ε)) ≤
      Real.logb 2 ε⁻¹ + max 0 (Real.logb 2 (2 * c₁)) := by
    refine max_le (by linarith) ?_
    rw [div_eq_mul_inv, Real.logb_mul (mul_pos two_pos hc₁).ne' (inv_pos.2 hε).ne']
    linarith [le_max_right 0 (Real.logb 2 (2 * c₁))]
  -- `√(2 log₂⁺(2c₁/ε)/α) ≤ √(2 log₂(1/ε)/α) + √(2 log₂⁺(2c₁)/α)`
  have hs : Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α) ≤
      Real.sqrt (2 * Real.logb 2 ε⁻¹ / α) +
        Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁)) / α) := by
    calc Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁ / ε)) / α)
        ≤ Real.sqrt (2 * Real.logb 2 ε⁻¹ / α + 2 * max 0 (Real.logb 2 (2 * c₁)) / α) := by
          refine Real.sqrt_le_sqrt ?_
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by linarith) hα.le
      _ ≤ _ := sqrt_add_le_sqrt_add_sqrt (div_nonneg (by linarith) hα.le)
          (div_nonneg (by linarith) hα.le)
  -- `(∑_{ℓ≤L} r^ℓ)² ≤ (r/(r−1))² 2^{(γ−β)L}` with `r = 2^{(γ−β)/2}`
  have hgeo := geom_sum_le_of_one_lt hq (ml2rLevel α c₁ ε)
  have hr2L : (((2 : ℝ) ^ ((γ - β) / 2)) ^ (ml2rLevel α c₁ ε)) ^ 2 =
      (2 : ℝ) ^ ((γ - β) * (ml2rLevel α c₁ ε : ℝ)) := by
    rw [← pow_mul, ← two_rpow_mul_nat]
    congr 1
    push_cast
    ring
  have hL := ml2rLevel_lt α c₁ ε
  have h2L : (2 : ℝ) ^ ((γ - β) * (ml2rLevel α c₁ ε : ℝ)) ≤
      2 ^ (γ - β) * 2 ^ ((γ - β) * Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁)) / α)) *
        2 ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α)) := by
    rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith [mul_lt_mul_of_pos_left hL hδ, mul_le_mul_of_nonneg_left hs hδ.le]
  have hsum_sq : (∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2 ≤
      ((2 : ℝ) ^ ((γ - β) / 2) / ((2 : ℝ) ^ ((γ - β) / 2) - 1)) ^ 2 *
        (2 ^ (γ - β) * 2 ^ ((γ - β) * Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁)) / α)) *
          2 ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α))) := by
    have h0 : 0 ≤ ∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ :=
      Finset.sum_nonneg fun ℓ _ => pow_nonneg (by linarith) _
    calc (∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2
        ≤ (((2 : ℝ) ^ ((γ - β) / 2)) ^ (ml2rLevel α c₁ ε) *
            ((2 : ℝ) ^ ((γ - β) / 2) / ((2 : ℝ) ^ ((γ - β) / 2) - 1))) ^ 2 :=
          pow_le_pow_left₀ h0 hgeo 2
      _ = ((2 : ℝ) ^ ((γ - β) / 2) / ((2 : ℝ) ^ ((γ - β) / 2) - 1)) ^ 2 *
            (2 : ℝ) ^ ((γ - β) * (ml2rLevel α c₁ ε : ℝ)) := by
          rw [mul_pow, hr2L]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2L (sq_nonneg _)
  have htail := ml2r_tail_cost hα hγ hc₁ hc₃ hε hε1'.le
  have hE : 1 ≤ (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hδ.le (Real.sqrt_nonneg _))
  have hinv : ε⁻¹ ≤ (ε ^ 2)⁻¹ *
      (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α)) := by
    have h1 : ε⁻¹ ≤ (ε ^ 2)⁻¹ := by
      rw [inv_le_inv₀ hε (by positivity)]
      nlinarith
    calc ε⁻¹ ≤ (ε ^ 2)⁻¹ := h1
      _ = (ε ^ 2)⁻¹ * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hE hε2.le
  have hXpos : 0 < ml2rWeightBound α ^ 2 * (c₂ * c₃) := mul_pos (pow_pos hW 2) (mul_pos hc₂ hc₃)
  rw [hepow]
  generalize (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * Real.logb 2 ε⁻¹ / α)) = E at hsum_sq hinv hE ⊢
  generalize c₃ * (2 ^ γ / (2 ^ γ - 1)) * ((2 : ℝ) ^ (γ + γ ^ 2 / (2 * α)) * (1 + 2 * c₁)) = K₂
    at htail hK₂0 ⊢
  generalize ((2 : ℝ) ^ ((γ - β) / 2) / ((2 : ℝ) ^ ((γ - β) / 2) - 1)) ^ 2 = R at hsum_sq hC₁ ⊢
  generalize (2 : ℝ) ^ ((γ - β) * Real.sqrt (2 * max 0 (Real.logb 2 (2 * c₁)) / α)) = M
    at hsum_sq hC₁ ⊢
  generalize ml2rWeightBound α ^ 2 * (c₂ * c₃) = X at hC₁ hXpos ⊢
  generalize (∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), ((2 : ℝ) ^ ((γ - β) / 2)) ^ ℓ) ^ 2 = Q
    at hsum_sq ⊢
  have hX : 0 ≤ 2 * (ε ^ 2)⁻¹ * X := mul_nonneg (mul_nonneg zero_le_two hε2.le) hXpos.le
  have hfirst : 2 * (ε ^ 2)⁻¹ * X * Q ≤
      2 * X * R * 2 ^ (γ - β) * M * ((ε ^ 2)⁻¹ * E) := by
    calc 2 * (ε ^ 2)⁻¹ * X * Q ≤ 2 * (ε ^ 2)⁻¹ * X * (R * (2 ^ (γ - β) * M * E)) :=
          mul_le_mul_of_nonneg_left hsum_sq hX
      _ = 2 * X * R * 2 ^ (γ - β) * M * ((ε ^ 2)⁻¹ * E) := by ring
  have hK₂inv : K₂ * ε⁻¹ ≤ K₂ * ((ε ^ 2)⁻¹ * E) := mul_le_mul_of_nonneg_left hinv hK₂0.le
  calc 2 * (ε ^ 2)⁻¹ * X * Q + ∑ ℓ ∈ range (ml2rLevel α c₁ ε + 1), Cb γ c₃ ℓ
      ≤ 2 * X * R * 2 ^ (γ - β) * M * ((ε ^ 2)⁻¹ * E) + K₂ * ((ε ^ 2)⁻¹ * E) := by
        linarith
    _ = (2 * X * R * 2 ^ (γ - β) * M + K₂) * ((ε ^ 2)⁻¹ * E) := by ring

end cost

end MLMC
