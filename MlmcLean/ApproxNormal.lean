import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Approximate normal random numbers (Haas–Giles 2025, §3)

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §3 "Approximate random normally distributed numbers", pp. 4–8,
equations (14)–(19).

The three inversion methods of §3 approximate the inverse normal CDF `Φ⁻¹` on `[0, 1]` by a
function that is constant on each uniform interval `I_j = [u_j, u_{j+1}]`, `u_j = 2^{−d} j`
(methods 1 and 3; method 2 after its permutation).  Nothing below uses a property of `Φ⁻¹` other
than square-integrability (and, for the sign bit, the symmetry `Φ⁻¹(1 − u) = −Φ⁻¹(u)`), so the
results are stated for any `f : ℝ → ℝ` with `f` and `f²` interval-integrable on `[0, 1]`.

* **The mean-square error of a constant** (`integral_sq_sub_eq`): on `[a, b]` with `a < b`,
  `∫ (z − f)² = (b − a)(z − z̄)² + ∫ (z̄ − f)²`, `z̄` the mean of `f`.  Hence **(14)–(15)**: the LUT
  value `Z_j = 2^d ∫_{I_j} f` is the unique minimiser of the MSE (14) on `I_j`
  (`lutValue_isLeast`); **(18)** is the identity on `I_j` (`integral_sq_sub_lutValue`); **(19)**
  follows by summing (`sum_integral_sq_sub_lutValue`), so minimising the MSE of method 3 is
  minimising (19) (`sum_integral_sq_le_iff`).
* **Methods 2 and 3 cannot beat method 1** (§3.3–§3.4; `method1_le`, `method1_le_perm`).
* **The symmetry of `Φ⁻¹`** (§3, §3.1): if `f(1 − u) = −f(u)` then `Z_{2^d−1−j} = −Z_j`
  (`lutValue_mirror`), so a LUT of size `2^{d−1}` and a sign bit give every value
  (`lutValue_upper_half`).
* **The coupled uniform variable (17)** (§3.1–§3.2): the two forms of (17) agree
  (`coupledUniform_eq`); `U` lies in the interval `I_{π(j)}` that `Z̃_j` approximates
  (`coupledUniform_mem`; `midpoint_mem_cell` for method 1); and for a permutation `π` the index of
  `U` is uniform whenever `J` is (`sum_coupledIndex`).
* **Method 2** (§3.2): the table sizes (`card_signed_sums`), the number of distinct sums
  (`card_image_add_le`, `choose_two_pow_add_one`), the sorting step of the least-squares
  iteration (16) (`sorting_minimises`), and the behaviour of the iteration: the objective does not
  increase (`alternating_min_antitone`) and is eventually constant
  (`alternating_min_eventually_const`), the iteration is eventually periodic
  (`alternating_eventually_periodic`), and it is stationary once the permutation repeats
  (`alternating_stationary`).
* **Method 3** (§3.3–§3.4): the dyadic interval of `j` and the LUT of size `d − 1`
  (`dyadic_index`), and exact fits on intervals with two points (`affine_fit_exact`).
-/

open MeasureTheory Finset

namespace MLMC

/-! ### The mean-square error of a constant on an interval -/

section Projection

variable {f : ℝ → ℝ} {a b : ℝ}

/-- The mean `(b − a)⁻¹ ∫ₐᵇ f` of `f` over `[a, b]` (Haas–Giles 2025, §3.1: "`Z_j` is the mean of
`Φ⁻¹` over the interval"). -/
noncomputable def intervalMean (f : ℝ → ℝ) (a b : ℝ) : ℝ := (b - a)⁻¹ * ∫ u in a..b, f u

/-- Expanding the square in the mean-square error (14) of a constant `z` (Haas–Giles 2025, §3.1):
`∫ₐᵇ (z − f)² = (b − a) z² − 2z ∫ₐᵇ f + ∫ₐᵇ f²`. -/
lemma integral_sq_sub_const (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume a b) (z : ℝ) :
    ∫ u in a..b, (z - f u) ^ 2 =
      (b - a) * z ^ 2 - 2 * z * (∫ u in a..b, f u) + ∫ u in a..b, f u ^ 2 := by
  have e : ∫ u in a..b, (z - f u) ^ 2 = ∫ u in a..b, ((z ^ 2 - 2 * z * f u) + f u ^ 2) := by
    congr 1
    funext u
    ring
  have i1 : IntervalIntegrable (fun u => z ^ 2 - 2 * z * f u) volume a b :=
    intervalIntegrable_const.sub (hf.const_mul (2 * z))
  have e1 : ∫ u in a..b, ((z ^ 2 - 2 * z * f u) + f u ^ 2) =
      (∫ u in a..b, (z ^ 2 - 2 * z * f u)) + ∫ u in a..b, f u ^ 2 :=
    intervalIntegral.integral_add i1 hf2
  have e2 : ∫ u in a..b, (z ^ 2 - 2 * z * f u) =
      (∫ _ in a..b, z ^ 2) - ∫ u in a..b, 2 * z * f u :=
    intervalIntegral.integral_sub intervalIntegrable_const (hf.const_mul (2 * z))
  have e3 : ∫ u in a..b, 2 * z * f u = 2 * z * ∫ u in a..b, f u :=
    intervalIntegral.integral_const_mul (2 * z) f
  have e4 : ∫ _ in a..b, z ^ 2 = (b - a) * z ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [e, e1, e2, e3, e4]

/-- **The mean-square error of a constant** (Haas–Giles 2025, §3.1, (14), and §3.3, (18)): for
`a < b`, with `z̄` the mean of `f` over `[a, b]`, every constant `z` has
`∫ₐᵇ (z − f)² = (b − a)(z − z̄)² + ∫ₐᵇ (z̄ − f)²`. -/
theorem integral_sq_sub_eq (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume a b) (z : ℝ) :
    ∫ u in a..b, (z - f u) ^ 2 =
      (b - a) * (z - intervalMean f a b) ^ 2 + ∫ u in a..b, (intervalMean f a b - f u) ^ 2 := by
  rw [integral_sq_sub_const hf hf2 z, integral_sq_sub_const hf hf2 (intervalMean f a b)]
  have e : (b - a) * intervalMean f a b = ∫ u in a..b, f u := by
    rw [intervalMean, ← mul_assoc, mul_inv_cancel₀ (sub_pos.2 hab).ne', one_mul]
  linear_combination (2 * z - 2 * intervalMean f a b) * e

/-- **(14)–(15): the mean minimises the mean-square error** (Haas–Giles 2025, §3.1: minimising
(14) "gives that `Z_j` is the mean of `Φ⁻¹` over the interval"): for `a < b`,
`∫ₐᵇ (z̄ − f)² ≤ ∫ₐᵇ (z − f)²` for every constant `z`, where `z̄` is the mean of `f`. -/
theorem integral_sq_sub_intervalMean_le (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume a b) (z : ℝ) :
    ∫ u in a..b, (intervalMean f a b - f u) ^ 2 ≤ ∫ u in a..b, (z - f u) ^ 2 := by
  rw [integral_sq_sub_eq hab hf hf2 z]
  have := mul_nonneg (sub_pos.2 hab).le (sq_nonneg (z - intervalMean f a b))
  linarith

/-- **The mean is the only minimiser of (14)** (Haas–Giles 2025, §3.1): for `a < b`, if
`∫ₐᵇ (z − f)² ≤ ∫ₐᵇ (z̄ − f)²` then `z = z̄`, the mean of `f`. -/
theorem eq_intervalMean_of_integral_sq_sub_le (hab : a < b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume a b) {z : ℝ}
    (hz : ∫ u in a..b, (z - f u) ^ 2 ≤ ∫ u in a..b, (intervalMean f a b - f u) ^ 2) :
    z = intervalMean f a b := by
  rw [integral_sq_sub_eq hab hf hf2 z] at hz
  have hba : 0 < b - a := sub_pos.2 hab
  have h1 : (z - intervalMean f a b) ^ 2 ≤ 0 := by
    by_contra hcon
    have := mul_pos hba (not_le.1 hcon)
    linarith
  have h2 : (z - intervalMean f a b) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  have h3 : z - intervalMean f a b = 0 := (pow_eq_zero_iff two_ne_zero).1 h2
  linarith

/-- **(14)–(15) as a least value** (Haas–Giles 2025, §3.1): for `a < b` the least value of
`z ↦ ∫ₐᵇ (z − f)²` is attained at the mean of `f`. -/
theorem intervalMean_isLeast (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume a b) :
    IsLeast (Set.range fun z => ∫ u in a..b, (z - f u) ^ 2)
      (∫ u in a..b, (intervalMean f a b - f u) ^ 2) :=
  ⟨⟨intervalMean f a b, rfl⟩, by
    rintro _ ⟨z, rfl⟩
    exact integral_sq_sub_intervalMean_le hab hf hf2 z⟩

end Projection

/-! ### Uniform intervals and the LUT of method 1 -/

section Grid

variable {f : ℝ → ℝ}

/-- The grid point `u_j = 2^{−d} j` of the uniform intervals `I_j = [u_j, u_{j+1}]` of methods 1
and 3 (Haas–Giles 2025, §3.1). -/
noncomputable def gridPt (d j : ℕ) : ℝ := (j : ℝ) / 2 ^ d

lemma gridPt_succ_sub (d j : ℕ) : gridPt d (j + 1) - gridPt d j = (2 ^ d)⁻¹ := by
  unfold gridPt
  push_cast
  ring

lemma gridPt_lt (d j : ℕ) : gridPt d j < gridPt d (j + 1) := by
  have h := gridPt_succ_sub d j
  have h2 : (0 : ℝ) < (2 ^ d)⁻¹ := by positivity
  linarith

lemma gridPt_nonneg (d j : ℕ) : 0 ≤ gridPt d j := by
  unfold gridPt
  positivity

lemma gridPt_le_one {d j : ℕ} (hj : j ≤ 2 ^ d) : gridPt d j ≤ 1 := by
  unfold gridPt
  rw [div_le_one (by positivity)]
  exact_mod_cast hj

/-- A function interval-integrable on `[0, 1]` is interval-integrable on each `I_j`, `j < 2^d`. -/
lemma intervalIntegrable_cell {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) {d j : ℕ}
    (hj : j < 2 ^ d) : IntervalIntegrable g volume (gridPt d j) (gridPt d (j + 1)) :=
  hg.mono_set (Set.uIcc_subset_uIcc
    (Set.mem_uIcc.2 (Or.inl ⟨gridPt_nonneg d j, gridPt_le_one hj.le⟩))
    (Set.mem_uIcc.2 (Or.inl ⟨gridPt_nonneg d (j + 1), gridPt_le_one (Nat.lt_iff_add_one_le.1 hj)⟩)))

/-- **The LUT value (15)** of method 1 (Haas–Giles 2025, §3.1): the mean of `f` over `I_j`,
`Z_j = 2^d ∫_{u_j}^{u_{j+1}} f(u) du`. -/
noncomputable def lutValue (f : ℝ → ℝ) (d j : ℕ) : ℝ :=
  2 ^ d * ∫ u in gridPt d j..gridPt d (j + 1), f u

lemma lutValue_eq_intervalMean (f : ℝ → ℝ) (d j : ℕ) :
    lutValue f d j = intervalMean f (gridPt d j) (gridPt d (j + 1)) := by
  rw [lutValue, intervalMean, gridPt_succ_sub, inv_inv]

/-- **(14)–(15)** (Haas–Giles 2025, §3.1: the MSE (14) "is minimised with respect to the LUT values
`Z_j`. This gives that `Z_j` is the mean of `Φ⁻¹` over the interval `I_j`", (15)): on `I_j` the
LUT value `Z_j` attains the least value of `z ↦ ∫_{I_j} (z − f)²`, and it is the only value that
does. -/
theorem lutValue_isLeast {d j : ℕ}
    (hf : IntervalIntegrable f volume (gridPt d j) (gridPt d (j + 1)))
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume (gridPt d j) (gridPt d (j + 1))) :
    IsLeast (Set.range fun z => ∫ u in gridPt d j..gridPt d (j + 1), (z - f u) ^ 2)
        (∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2) ∧
      ∀ z, ∫ u in gridPt d j..gridPt d (j + 1), (z - f u) ^ 2 ≤
          ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 →
        z = lutValue f d j := by
  rw [lutValue_eq_intervalMean]
  exact ⟨intervalMean_isLeast (gridPt_lt d j) hf hf2,
    fun z hz => eq_intervalMean_of_integral_sq_sub_le (gridPt_lt d j) hf hf2 hz⟩

/-- **(18)** (Haas–Giles 2025, §3.3: "A simple calculation shows that
`∫_{u_j}^{u_{j+1}} (Z̄_j − Φ⁻¹(u))² du = 2^{−d}(Z̄_j − Z_j)² +
∫_{u_j}^{u_{j+1}} (Z_j − Φ⁻¹(u))² du`"), for any value `z̄` in place of `Z̄_j = a + b j`. -/
theorem integral_sq_sub_lutValue {d j : ℕ}
    (hf : IntervalIntegrable f volume (gridPt d j) (gridPt d (j + 1)))
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume (gridPt d j) (gridPt d (j + 1)))
    (z : ℝ) :
    ∫ u in gridPt d j..gridPt d (j + 1), (z - f u) ^ 2 =
      (2 ^ d)⁻¹ * (z - lutValue f d j) ^ 2 +
        ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 := by
  rw [lutValue_eq_intervalMean, integral_sq_sub_eq (gridPt_lt d j) hf hf2 z, gridPt_succ_sub]

/-- **(19)** (Haas–Giles 2025, §3.3): summing (18) over the intervals `I_j`, `j < n ≤ 2^d`, the
mean-square error of the approximation that takes the value `w_j` on `I_j` (method 3:
`w_j = Z̄_j = a + b j`) is
`∑_j ∫_{I_j} (w_j − f)² = 2^{−d} ∑_j (w_j − Z_j)² + ∑_j ∫_{I_j} (Z_j − f)²`, the last sum being
the mean-square error of method 1. -/
theorem sum_integral_sq_sub_lutValue {d n : ℕ} (hn : n ≤ 2 ^ d)
    (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (w : ℕ → ℝ) :
    ∑ j ∈ range n, ∫ u in gridPt d j..gridPt d (j + 1), (w j - f u) ^ 2 =
      (2 ^ d)⁻¹ * ∑ j ∈ range n, (w j - lutValue f d j) ^ 2 +
        ∑ j ∈ range n, ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < 2 ^ d := lt_of_lt_of_le (Finset.mem_range.1 hj) hn
  exact integral_sq_sub_lutValue (intervalIntegrable_cell hf hj')
    (intervalIntegrable_cell hf2 hj') (w j)

/-- **Minimising (19) minimises the mean-square error** (Haas–Giles 2025, §3.3: "Therefore to
calculate the pairs `(a, b)` we only need to minimise (19)"): for two families of interval values
`w, w'`, the mean-square error of `w` is at most that of `w'` if and only if
`∑_j (w_j − Z_j)² ≤ ∑_j (w'_j − Z_j)²`. -/
theorem sum_integral_sq_le_iff {d n : ℕ} (hn : n ≤ 2 ^ d)
    (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (w w' : ℕ → ℝ) :
    ∑ j ∈ range n, ∫ u in gridPt d j..gridPt d (j + 1), (w j - f u) ^ 2 ≤
        ∑ j ∈ range n, ∫ u in gridPt d j..gridPt d (j + 1), (w' j - f u) ^ 2 ↔
      ∑ j ∈ range n, (w j - lutValue f d j) ^ 2 ≤ ∑ j ∈ range n, (w' j - lutValue f d j) ^ 2 := by
  rw [sum_integral_sq_sub_lutValue hn hf hf2 w, sum_integral_sq_sub_lutValue hn hf hf2 w',
    add_le_add_iff_right]
  have hc : (0 : ℝ) < (2 ^ d)⁻¹ := by positivity
  exact ⟨fun h => le_of_mul_le_mul_left h hc, fun h => mul_le_mul_of_nonneg_left h hc.le⟩

/-- **Methods 2 and 3 cannot beat method 1** (Haas–Giles 2025, §3.3: "(18) also shows that for the
same value of `d` this approximation cannot be as good as the method 1"; §3.4: "the MSE obtained in
methods 2 and 3 are necessarily larger than in method 1"): an approximation that takes the value
`w_j` on each interval `I_j` has mean-square error at least that of the LUT values `Z_j`, with
equality only if `w_j = Z_j` on every interval. -/
theorem method1_le {d n : ℕ} (hn : n ≤ 2 ^ d) (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (w : ℕ → ℝ) :
    ∑ j ∈ range n, ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 ≤
        ∑ j ∈ range n, ∫ u in gridPt d j..gridPt d (j + 1), (w j - f u) ^ 2 ∧
      (∑ j ∈ range n, ∫ u in gridPt d j..gridPt d (j + 1), (w j - f u) ^ 2 =
          ∑ j ∈ range n, ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 →
        ∀ j < n, w j = lutValue f d j) := by
  rw [sum_integral_sq_sub_lutValue hn hf hf2 w]
  have hS : 0 ≤ ∑ j ∈ range n, (w j - lutValue f d j) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hc : (0 : ℝ) < (2 ^ d)⁻¹ := by positivity
  have hcS := mul_nonneg hc.le hS
  refine ⟨by linarith, fun h j hj => ?_⟩
  have h0 : (2 ^ d : ℝ)⁻¹ * ∑ j ∈ range n, (w j - lutValue f d j) ^ 2 = 0 := by linarith
  have h1 : ∑ j ∈ range n, (w j - lutValue f d j) ^ 2 = 0 :=
    (mul_eq_zero.1 h0).resolve_left hc.ne'
  have h2 : (w j - lutValue f d j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (w i - lutValue f d i)).1 h1 j
      (Finset.mem_range.2 hj)
  have h3 : w j - lutValue f d j = 0 := (pow_eq_zero_iff two_ne_zero).1 h2
  linarith

/-- **Method 2 cannot beat method 1** (Haas–Giles 2025, §3.2: "the output is the value `Z̃_j`, which
is an approximate of `Φ⁻¹(2^{−d}π(j))`", so method 2 uses `Z̃_j` on the interval `I_{π(j)}`; §3.4):
for every permutation `π` of the `2^d` intervals and all values `Z̃`, its mean-square error is at
least that of method 1. -/
theorem method1_le_perm {d : ℕ} (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (π : Equiv.Perm (Fin (2 ^ d)))
    (Zt : Fin (2 ^ d) → ℝ) :
    ∑ j ∈ range (2 ^ d), ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 ≤
      ∑ j : Fin (2 ^ d), ∫ u in gridPt d (π j)..gridPt d ((π j : ℕ) + 1), (Zt j - f u) ^ 2 := by
  set w : ℕ → ℝ := fun k => if h : k < 2 ^ d then Zt (π.symm ⟨k, h⟩) else 0 with hw
  have e1 : ∑ j : Fin (2 ^ d), ∫ u in gridPt d (π j)..gridPt d ((π j : ℕ) + 1), (Zt j - f u) ^ 2 =
      ∑ k : Fin (2 ^ d), ∫ u in gridPt d k..gridPt d ((k : ℕ) + 1), (w k - f u) ^ 2 := by
    refine Fintype.sum_equiv π _ _ fun j => ?_
    have hwj : w (π j) = Zt j := by simp [hw]
    rw [hwj]
  rw [e1, Fin.sum_univ_eq_sum_range (fun k => ∫ u in gridPt d k..gridPt d (k + 1), (w k - f u) ^ 2)]
  exact (method1_le le_rfl hf hf2 w).1

/-- **The symmetry of `Φ⁻¹`** (Haas–Giles 2025, §3: "we exploit the symmetry of `Φ⁻¹` so we only
need to approximate it on `[0, 1/2]`"): if `f(1 − u) = −f(u)` for every `u` (as for `Φ⁻¹`), the LUT
values of mirrored intervals are opposite: `Z_{2^d−1−j} = −Z_j` for `j < 2^d`. -/
theorem lutValue_mirror (hf : ∀ u, f (1 - u) = -f u) {d j : ℕ} (hj : j < 2 ^ d) :
    lutValue f d (2 ^ d - 1 - j) = -lutValue f d j := by
  have h2 : (0 : ℝ) < 2 ^ d := by positivity
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ d - 1 - j = m := ⟨_, rfl⟩
  have hmj : m + j + 1 = 2 ^ d := by omega
  have hmR : (m : ℝ) + j + 1 = 2 ^ d := by exact_mod_cast hmj
  rw [hm]
  have hlo : gridPt d m = 1 - gridPt d (j + 1) := by
    unfold gridPt
    rw [div_eq_iff h2.ne', sub_mul, div_mul_cancel₀ _ h2.ne', one_mul]
    push_cast
    linarith
  have hhi : gridPt d (m + 1) = 1 - gridPt d j := by
    unfold gridPt
    rw [div_eq_iff h2.ne', sub_mul, div_mul_cancel₀ _ h2.ne', one_mul]
    push_cast
    linarith
  unfold lutValue
  rw [hlo, hhi, ← intervalIntegral.integral_comp_sub_left f 1]
  simp only [hf, intervalIntegral.integral_neg, mul_neg]

/-- **A LUT on `[0, 1/2]` and a sign bit suffice** (Haas–Giles 2025, §3.1: "a Look-Up-Table (LUT)
of size `2^{d−1}` ... The leading bit of `j` gives the sign of the normal increment, which allows us
to extend the approximation of `Φ⁻¹` on the interval `[1/2, 1]`"): if `f(1 − u) = −f(u)`, every
`j` in the upper half, `2^{d−1} ≤ j < 2^d`, has its mirror `2^d − 1 − j` in the LUT range
`[0, 2^{d−1})` and `Z_j = −Z_{2^d−1−j}`. -/
theorem lutValue_upper_half (hf : ∀ u, f (1 - u) = -f u) {d j : ℕ} (hd : 1 ≤ d)
    (hj1 : 2 ^ (d - 1) ≤ j) (hj : j < 2 ^ d) :
    2 ^ d - 1 - j < 2 ^ (d - 1) ∧ lutValue f d j = -lutValue f d (2 ^ d - 1 - j) := by
  have h2 : 2 ^ d = 2 * 2 ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  refine ⟨by omega, ?_⟩
  have h := lutValue_mirror hf (d := d) (j := 2 ^ d - 1 - j) (by omega)
  rw [show 2 ^ d - 1 - (2 ^ d - 1 - j) = j by omega] at h
  exact h

end Grid

/-! ### The coupled full-precision uniform variable (17) -/

section Coupling

/-- The identity (17) for real numbers (Haas–Giles 2025, §3.2): for `d ≤ D`,
`p/2^d + ((J − 2^{D−d} q) + ½)/2^D = (p − q)/2^d + (J + ½)/2^D`. -/
lemma coupled_identity {d D : ℕ} (hdD : d ≤ D) (p q J : ℝ) :
    p / 2 ^ d + (J - 2 ^ (D - d) * q + 1 / 2) / 2 ^ D =
      (p - q) / 2 ^ d + (J + 1 / 2) / 2 ^ D := by
  have hD : (2 : ℝ) ^ D = 2 ^ (D - d) * 2 ^ d := by rw [← pow_add, Nat.sub_add_cancel hdD]
  have h1 : (2 : ℝ) ^ (D - d) ≠ 0 := by positivity
  have key : (2 : ℝ) ^ (D - d) * q / (2 ^ (D - d) * 2 ^ d) = q / 2 ^ d :=
    mul_div_mul_left q _ h1
  have e : (J - 2 ^ (D - d) * q + 1 / 2) / (2 ^ (D - d) * 2 ^ d) =
      (J + 1 / 2) / (2 ^ (D - d) * 2 ^ d) - 2 ^ (D - d) * q / (2 ^ (D - d) * 2 ^ d) := by
    ring
  rw [hD, e, key]
  ring

/-- **The coupled full-precision uniform variable (17)** of method 2 (Haas–Giles 2025, §3.2), for a
`D`-bit integer `J` whose leading `d` bits form `j = ⌊J/2^{D−d}⌋`:
`U = 2^{−d} π(j) + 2^{−D}((J − 2^{D−d} j) + ½)`.  With `π = id` it is the method-1 variable
`U = 2^{−D}(J + ½)` of §3.1 (`coupledUniform_eq`). -/
noncomputable def coupledUniform (π : ℕ → ℕ) (d D J : ℕ) : ℝ :=
  (π (J / 2 ^ (D - d)) : ℝ) / 2 ^ d +
    ((J : ℝ) - 2 ^ (D - d) * ((J / 2 ^ (D - d) : ℕ) : ℝ) + 1 / 2) / 2 ^ D

/-- **(17)** (Haas–Giles 2025, §3.2): for `d ≤ D` and `j = ⌊J/2^{D−d}⌋`,
`U = 2^{−d} π(j) + 2^{−D}((J − 2^{D−d} j) + ½) = 2^{−d}(π(j) − j) + 2^{−D}(J + ½)`. -/
theorem coupledUniform_eq {d D : ℕ} (hdD : d ≤ D) (π : ℕ → ℕ) (J : ℕ) :
    coupledUniform π d D J =
      ((π (J / 2 ^ (D - d)) : ℝ) - ((J / 2 ^ (D - d) : ℕ) : ℝ)) / 2 ^ d +
        ((J : ℝ) + 1 / 2) / 2 ^ D := by
  rw [coupledUniform]
  exact coupled_identity hdD _ _ _

/-- `J − 2^{D−d}⌊J/2^{D−d}⌋` is the remainder `J mod 2^{D−d}` (Haas–Giles 2025, §3.2). -/
lemma sub_mul_div_eq_mod (m J : ℕ) :
    (J : ℝ) - (m : ℝ) * ((J / m : ℕ) : ℝ) = ((J % m : ℕ) : ℝ) := by
  have h := Nat.div_add_mod J m
  have h' : ((m * (J / m) + J % m : ℕ) : ℝ) = (J : ℝ) := by rw [h]
  push_cast at h'
  linarith

/-- **The coupled variable lies in the interval that `Z̃_j` approximates** (Haas–Giles 2025, §3.2:
"the output is the value `Z̃_j`, which is an approximate of `Φ⁻¹(2^{−d}π(j))`. Therefore the
corresponding uniform variable used on the CPU is (17)"): for `d ≤ D` and `j = ⌊J/2^{D−d}⌋`,
`u_{π(j)} < U < u_{π(j)+1}`. -/
theorem coupledUniform_mem {d D : ℕ} (hdD : d ≤ D) (π : ℕ → ℕ) (J : ℕ) :
    gridPt d (π (J / 2 ^ (D - d))) < coupledUniform π d D J ∧
      coupledUniform π d D J < gridPt d (π (J / 2 ^ (D - d)) + 1) := by
  have hm0 : 0 < 2 ^ (D - d) := by positivity
  have hr : J % 2 ^ (D - d) + 1 ≤ 2 ^ (D - d) := Nat.mod_lt _ hm0
  have hJ : (J : ℝ) - 2 ^ (D - d) * ((J / 2 ^ (D - d) : ℕ) : ℝ) =
      ((J % 2 ^ (D - d) : ℕ) : ℝ) := by
    have h := sub_mul_div_eq_mod (2 ^ (D - d)) J
    push_cast at h
    exact h
  have hr' : ((J % 2 ^ (D - d) : ℕ) : ℝ) + 1 / 2 < (2 : ℝ) ^ (D - d) := by
    have h : ((J % 2 ^ (D - d) : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (D - d) := by exact_mod_cast hr
    linarith
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hD : (2 : ℝ) ^ D = 2 ^ (D - d) * 2 ^ d := by rw [← pow_add, Nat.sub_add_cancel hdD]
  unfold coupledUniform gridPt
  rw [hJ, hD, Nat.cast_add_one]
  set r : ℝ := ((J % 2 ^ (D - d) : ℕ) : ℝ)
  set p : ℝ := ((π (J / 2 ^ (D - d)) : ℕ) : ℝ)
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hpos : 0 < (r + 1 / 2) / (2 ^ (D - d) * 2 ^ d) := by positivity
  have hlt : (r + 1 / 2) / (2 ^ (D - d) * 2 ^ d) < 1 / 2 ^ d := by
    rw [div_lt_div_iff₀ (by positivity) h2d]
    have := mul_lt_mul_of_pos_right hr' h2d
    linarith
  have e : (p + 1) / 2 ^ d = p / 2 ^ d + 1 / 2 ^ d := add_div p 1 _
  constructor
  · linarith
  · linarith

/-- **Method 1: the interval of `U` is given by the leading bits of `J`** (Haas–Giles 2025, §3.1:
"the corresponding full precision uniform variable is defined as `U = 2^{−D}(J + ½)`"; "Locating the
interval corresponding to the input uniform variable `U` is trivial since the integer `j` maps to
the index of the interval"): for `d ≤ D`, `U = 2^{−D}(J + ½)` lies in `I_j`, `j = ⌊J/2^{D−d}⌋`. -/
theorem midpoint_mem_cell {d D : ℕ} (hdD : d ≤ D) (J : ℕ) :
    gridPt d (J / 2 ^ (D - d)) < ((J : ℝ) + 1 / 2) / 2 ^ D ∧
      ((J : ℝ) + 1 / 2) / 2 ^ D < gridPt d (J / 2 ^ (D - d) + 1) := by
  have h := coupledUniform_mem hdD id J
  rw [coupledUniform_eq hdD] at h
  simpa using h

/-- The integer index `K = 2^{D−d} π(j) + (J − 2^{D−d} j)`, `j = ⌊J/2^{D−d}⌋`, of the coupled
variable (17) (Haas–Giles 2025, §3.2): `U = 2^{−D}(K + ½)` (`coupledUniform_eq_index`). -/
def coupledIndex (π : ℕ → ℕ) (d D J : ℕ) : ℕ :=
  2 ^ (D - d) * π (J / 2 ^ (D - d)) + J % 2 ^ (D - d)

/-- The coupled variable (17) is the midpoint `2^{−D}(K + ½)` of the `K`-th of the `2^D` fine
intervals (Haas–Giles 2025, §3.2). -/
lemma coupledUniform_eq_index {d D : ℕ} (hdD : d ≤ D) (π : ℕ → ℕ) (J : ℕ) :
    coupledUniform π d D J = ((coupledIndex π d D J : ℝ) + 1 / 2) / 2 ^ D := by
  have hD : (2 : ℝ) ^ D = 2 ^ (D - d) * 2 ^ d := by rw [← pow_add, Nat.sub_add_cancel hdD]
  have h1 : (2 : ℝ) ^ (D - d) ≠ 0 := by positivity
  have hJ : (J : ℝ) - 2 ^ (D - d) * ((J / 2 ^ (D - d) : ℕ) : ℝ) =
      ((J % 2 ^ (D - d) : ℕ) : ℝ) := by
    have h := sub_mul_div_eq_mod (2 ^ (D - d)) J
    push_cast at h
    exact h
  unfold coupledUniform coupledIndex
  rw [hJ]
  push_cast
  rw [hD]
  set p : ℝ := ((π (J / 2 ^ (D - d)) : ℕ) : ℝ)
  have key : (2 : ℝ) ^ (D - d) * p / (2 ^ (D - d) * 2 ^ d) = p / 2 ^ d :=
    mul_div_mul_left p _ h1
  rw [← key]
  ring

/-- **The coupled uniform variable is uniformly distributed** (Haas–Giles 2025, §3.2: the CPU
variable (17) must be a valid full-precision uniform variable coupled with `Z̃_j`): if `π` permutes
the `2^d` intervals, with inverse `ρ`, then the index map `J ↦ K` of (17) permutes the `2^D`
integers `J < 2^D`.  So `∑_{J < 2^D} g(K(J)) = ∑_{J < 2^D} g(J)` for every `g`: if `J` is uniform
on its `2^D` values, so is `K`, and `U = 2^{−D}(K + ½)` has the law of `2^{−D}(J + ½)`. -/
theorem sum_coupledIndex {d D : ℕ} (hdD : d ≤ D) {π ρ : ℕ → ℕ}
    (hπ : ∀ j < 2 ^ d, π j < 2 ^ d) (hρ : ∀ j < 2 ^ d, ρ j < 2 ^ d)
    (hρπ : ∀ j < 2 ^ d, ρ (π j) = j) (hπρ : ∀ j < 2 ^ d, π (ρ j) = j) {M : Type*}
    [AddCommMonoid M] (g : ℕ → M) :
    ∑ J ∈ range (2 ^ D), g (coupledIndex π d D J) = ∑ J ∈ range (2 ^ D), g J := by
  have hm0 : 0 < 2 ^ (D - d) := by positivity
  have hD : 2 ^ D = 2 ^ (D - d) * 2 ^ d := by rw [← pow_add, Nat.sub_add_cancel hdD]
  have hD' : 2 ^ D = 2 ^ d * 2 ^ (D - d) := by rw [hD, Nat.mul_comm]
  -- the leading `d` bits of `J < 2^D`
  have hq : ∀ J < 2 ^ D, J / 2 ^ (D - d) < 2 ^ d := fun J hJ => by
    rw [Nat.div_lt_iff_lt_mul hm0, ← hD']
    exact hJ
  -- the index stays below `2^D`
  have hK : ∀ σ : ℕ → ℕ, (∀ j < 2 ^ d, σ j < 2 ^ d) → ∀ J < 2 ^ D,
      coupledIndex σ d D J < 2 ^ D := by
    intro σ hσ J hJ
    have h2 : J % 2 ^ (D - d) < 2 ^ (D - d) := Nat.mod_lt _ hm0
    have h3 : 2 ^ (D - d) * (σ (J / 2 ^ (D - d)) + 1) ≤ 2 ^ (D - d) * 2 ^ d :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (hσ _ (hq J hJ)))
    unfold coupledIndex
    rw [hD]
    calc 2 ^ (D - d) * σ (J / 2 ^ (D - d)) + J % 2 ^ (D - d)
        < 2 ^ (D - d) * σ (J / 2 ^ (D - d)) + 2 ^ (D - d) := Nat.add_lt_add_left h2 _
      _ = 2 ^ (D - d) * (σ (J / 2 ^ (D - d)) + 1) := by ring
      _ ≤ 2 ^ (D - d) * 2 ^ d := h3
  -- the index maps of `π` and `ρ` are inverse to each other
  have hinv : ∀ σ τ : ℕ → ℕ, (∀ j < 2 ^ d, τ (σ j) = j) → ∀ J < 2 ^ D,
      coupledIndex τ d D (coupledIndex σ d D J) = J := by
    intro σ τ hστ J hJ
    have h2 : J % 2 ^ (D - d) < 2 ^ (D - d) := Nat.mod_lt _ hm0
    have hdiv : (2 ^ (D - d) * σ (J / 2 ^ (D - d)) + J % 2 ^ (D - d)) / 2 ^ (D - d) =
        σ (J / 2 ^ (D - d)) := by
      rw [Nat.mul_add_div hm0, Nat.div_eq_of_lt h2, Nat.add_zero]
    have hmod : (2 ^ (D - d) * σ (J / 2 ^ (D - d)) + J % 2 ^ (D - d)) % 2 ^ (D - d) =
        J % 2 ^ (D - d) := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
    unfold coupledIndex
    rw [hdiv, hmod, hστ _ (hq J hJ)]
    exact Nat.div_add_mod J _
  exact Finset.sum_nbij' (coupledIndex π d D) (coupledIndex ρ d D)
    (fun J hJ => Finset.mem_range.2 (hK π hπ J (Finset.mem_range.1 hJ)))
    (fun J hJ => Finset.mem_range.2 (hK ρ hρ J (Finset.mem_range.1 hJ)))
    (fun J hJ => hinv π ρ hρπ J (Finset.mem_range.1 hJ))
    (fun J hJ => hinv ρ π hπρ J (Finset.mem_range.1 hJ))
    (fun J _ => rfl)

end Coupling

/-! ### Method 2: sums of low-precision variables -/

section Method2

/-- `(2 · 2^{e−1})^n = 2^{ne}` for `e ≥ 1` (Haas–Giles 2025, §3.2). -/
lemma two_mul_two_pow_pred_pow {e : ℕ} (he : 1 ≤ e) (n : ℕ) :
    (2 * 2 ^ (e - 1)) ^ n = 2 ^ (n * e) := by
  rw [← pow_succ', Nat.sub_add_cancel he, ← pow_mul, Nat.mul_comm]

/-- **The table sizes of method 2** (Haas–Giles 2025, §3.2: with two streams, "Both streams of
lower precision variables `X^{(1)}, X^{(2)}` are computed with the same LUT of size `2^{d/2−1}`",
and "we form a larger LUT of size `2^d` by computing all possible sums `±X_k ± X_l`"; with `n`
streams "`n` low precision variables are summed"): if each of the `n` streams has `e` bits, a sign
bit and `e − 1` bits indexing a LUT of size `2^{e−1}`, the signed sums are indexed by
`(Bool × Fin 2^{e−1})^n`, a set of `2^{ne}` elements (`2^d` for `d = ne`). -/
theorem card_signed_sums {e : ℕ} (he : 1 ≤ e) (n : ℕ) :
    Fintype.card (Fin n → Bool × Fin (2 ^ (e - 1))) = 2 ^ (n * e) := by
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  exact two_mul_two_pow_pred_pow he n

/-- **Most method-2 values occur in pairs** (Haas–Giles 2025, §3.4: "most of the values in method
2 occur in pairs (`X_i + X_j` and `X_j + X_i`)", with "the extra values of the form `X_i + X_i`"):
the sums `x_k + x_l` over the ordered pairs from a set of `N` signed table values take at most
`N(N + 1)/2 = (N+1 choose 2)` distinct values. -/
theorem card_image_add_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) :
    ((s ×ˢ s).image fun p => x p.1 + x p.2).card ≤ Nat.choose (s.card + 1) 2 := by
  have h : ((s ×ˢ s).image fun p => x p.1 + x p.2) =
      s.sym2.image (Sym2.lift ⟨fun a b => x a + x b, fun a b => add_comm (x a) (x b)⟩) := by
    rw [Finset.sym2_eq_image, Finset.image_image]
    rfl
  rw [h, ← Finset.card_sym2]
  exact Finset.card_image_le

/-- **Method 2 with `d` bits against method 1 with `d − 1` bits** (Haas–Giles 2025, §3.4: "it is
also interesting to compare methods 2 with `d` bits against the method 1 with `d − 1` bits"): with
two streams of `d/2 = k + 1` bits there are `N = 2^{k+1}` signed table values, and the bound of
`card_image_add_le` is `(N+1 choose 2) = 2^{2k+1} + 2^k = 2^{d−1} + 2^{d/2−1}`, the size `2^{d−1}`
of a method-1 LUT with `d − 1` bits plus `2^{d/2−1}`: the `N(N − 1)/2` sums of two different
entries (each occurring twice) and the `N` sums `X_i + X_i`. -/
theorem choose_two_pow_add_one (k : ℕ) :
    Nat.choose (2 ^ (k + 1) + 1) 2 = 2 ^ (2 * k + 1) + 2 ^ k := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have h : (2 ^ (k + 1) + 1) * 2 ^ (k + 1) = 2 * (2 ^ (2 * k + 1) + 2 ^ k) := by ring
  rw [h, Nat.mul_div_cancel_left _ two_pos]

/-- **The sorting step of the method-2 optimisation minimises (16)** (Haas–Giles 2025, §3.2:
"ordering the outputs `Z̃_j` in ascending order. This step defines a permutation `π` such that
`π(j)` gives the position of the random number `Z̃_j` in the ordered list", with the least-squares
objective (16) `∑_j (Z_{π(j)} − Z̃_j)²`): if the targets `Z` are nondecreasing along the positions
and `π` ranks the `Z̃_j` (`Z̃_i < Z̃_j → π(i) < π(j)`), then `π` minimises (16) over all
permutations (the rearrangement inequality). -/
theorem sorting_minimises {n : ℕ} {Z : Fin n → ℝ} (hZ : Monotone Z) (Zt : Fin n → ℝ)
    {π : Equiv.Perm (Fin n)} (hπ : ∀ i j, Zt i < Zt j → π i < π j) (σ : Equiv.Perm (Fin n)) :
    ∑ j, (Z (π j) - Zt j) ^ 2 ≤ ∑ j, (Z (σ j) - Zt j) ^ 2 := by
  have hmono : Monovary (Z ∘ π) Zt := fun i j hij => hZ (hπ i j hij).le
  have hsq : ∀ τ : Equiv.Perm (Fin n), ∑ j, (Z (τ j) - Zt j) ^ 2 =
      ∑ j, Z j ^ 2 - 2 * ∑ j, Z (τ j) * Zt j + ∑ j, Zt j ^ 2 := by
    intro τ
    have e : ∑ j, Z (τ j) ^ 2 = ∑ j, Z j ^ 2 := Equiv.sum_comp τ (fun k => Z k ^ 2)
    rw [← e, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hre : ∑ j, Z (σ j) * Zt j ≤ ∑ j, Z (π j) * Zt j := by
    have h := hmono.sum_comp_perm_mul_le_sum_mul (σ := σ.trans π.symm)
    simpa [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply] using h
  rw [hsq π, hsq σ]
  linarith

/-- **The method-2 iteration does not increase the objective (16)** (Haas–Giles 2025, §3.2: a
least-squares minimisation over the table values for the current permutation, then "update the
permutation `π` by ordering the resulting `Z̃_j` and repeat the least-squares optimisation"): for an
objective `F(π, x)`, if each `x_k` minimises `F(π_k, ·)` and each `π_{k+1}` minimises `F(·, x_k)`,
the values `F(π_k, x_k)` are nonincreasing. -/
theorem alternating_min_antitone {P X : Type*} (F : P → X → ℝ) {π : ℕ → P} {x : ℕ → X}
    (hx : ∀ k y, F (π k) (x k) ≤ F (π k) y) (hπ : ∀ k p, F (π (k + 1)) (x k) ≤ F p (x k)) :
    Antitone fun k => F (π k) (x k) :=
  antitone_nat_of_succ_le fun k => (hx (k + 1) (x k)).trans (hπ k (π k))

/-- **The objective of the method-2 iteration is eventually constant** (Haas–Giles 2025, §3.2:
"The algorithm stops when the permutation has converged"): under the hypotheses of
`alternating_min_antitone`, with finitely many permutations, `F(π_k, x_k)` is constant from some
iteration on. -/
theorem alternating_min_eventually_const {P X : Type*} [Finite P] (F : P → X → ℝ) {π : ℕ → P}
    {x : ℕ → X} (hx : ∀ k y, F (π k) (x k) ≤ F (π k) y)
    (hπ : ∀ k p, F (π (k + 1)) (x k) ≤ F p (x k)) :
    ∃ K, ∀ k, K ≤ k → F (π k) (x k) = F (π K) (x K) := by
  classical
  set v : ℕ → ℝ := fun k => F (π k) (x k)
  -- `v k` depends only on `π k`
  have hdep : ∀ k k', π k = π k' → v k = v k' := fun k k' h => by
    apply le_antisymm
    · show F (π k) (x k) ≤ F (π k') (x k')
      have := hx k (x k')
      rw [h] at this ⊢
      exact this
    · show F (π k') (x k') ≤ F (π k) (x k)
      have := hx k' (x k)
      rw [← h] at this ⊢
      exact this
  -- so `v` has finitely many values
  let g : P → ℝ := fun p => if hp : ∃ k, π k = p then v (Nat.find hp) else 0
  have hg : ∀ k, v k = g (π k) := fun k => by
    have hp : ∃ k', π k' = π k := ⟨k, rfl⟩
    simp only [g, dif_pos hp]
    exact hdep k _ (Nat.find_spec hp).symm
  have hfin : (Set.range v).Finite :=
    (Set.finite_range g).subset (by
      rintro _ ⟨k, rfl⟩
      exact ⟨π k, (hg k).symm⟩)
  -- the least value is attained, and the antitone sequence stays there
  have hne : hfin.toFinset.Nonempty := ⟨v 0, by simp⟩
  obtain ⟨K, hKv⟩ : hfin.toFinset.min' hne ∈ Set.range v := by
    simpa using hfin.toFinset.min'_mem hne
  have hanti : Antitone v := alternating_min_antitone F hx hπ
  refine ⟨K, fun k hk => le_antisymm (hanti hk) ?_⟩
  show v K ≤ v k
  rw [hKv]
  exact hfin.toFinset.min'_le _ (by simp)

/-- **The method-2 iteration is eventually periodic** (Haas–Giles 2025, §3.2): if the least-squares
step `T` and the sorting step `S` are deterministic, `π_{k+1} = S(T(π_k))`, and there are finitely
many permutations, then some permutation recurs and from then on the iteration cycles with some
period `p > 0` (the permutation "has converged" when the period is `1`). -/
theorem alternating_eventually_periodic {P X : Type*} [Finite P] (S : X → P) (T : P → X)
    {π : ℕ → P} (hπ : ∀ k, π (k + 1) = S (T (π k))) :
    ∃ K p, 0 < p ∧ ∀ k, K ≤ k → π (k + p) = π k := by
  have key : ∀ a b, a < b → π a = π b → ∃ K p, 0 < p ∧ ∀ k, K ≤ k → π (k + p) = π k := by
    intro a b hab he
    refine ⟨a, b - a, Nat.sub_pos_of_lt hab, fun k hk => ?_⟩
    induction k, hk using Nat.le_induction with
    | base => rw [Nat.add_sub_cancel' hab.le]; exact he.symm
    | succ k hk ih =>
      rw [show k + 1 + (b - a) = k + (b - a) + 1 by omega, hπ, ih, ← hπ]
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite π
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h heq
  · exact key j i h heq.symm

/-- **The stopping rule of the method-2 iteration** (Haas–Giles 2025, §3.2: "The algorithm stops
when the permutation has converged"): with deterministic steps, `π_{k+1} = S(T(π_k))`, once the
permutation repeats, `π_{K+1} = π_K`, the iteration is stationary: `π_k = π_K` for all `k ≥ K`. -/
theorem alternating_stationary {P X : Type*} (S : X → P) (T : P → X) {π : ℕ → P}
    (hπ : ∀ k, π (k + 1) = S (T (π k))) {K : ℕ} (hK : π (K + 1) = π K) :
    ∀ k, K ≤ k → π k = π K := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [hπ, ih, ← hπ, hK]

end Method2

/-! ### Method 3: piecewise linear approximation on dyadic intervals -/

section Method3

/-- **The dyadic intervals of method 3** (Haas–Giles 2025, §3.3: "a separate pair `(a, b)` for
each interval `I'_i = [[2^{i−1}, 2^i − 1]]`, where `i` is the leading non-zero bit of the integer
`j`. The coefficients are stored in a LUT of size `d − 1`"): for `0 < j < 2^{d−1}`, the position
`i = ⌊log₂ j⌋ + 1` of the leading bit of `j` has `2^{i−1} ≤ j < 2^i` and `1 ≤ i ≤ d − 1`. -/
theorem dyadic_index {d j : ℕ} (hj0 : j ≠ 0) (hj : j < 2 ^ (d - 1)) :
    2 ^ Nat.log 2 j ≤ j ∧ j < 2 ^ (Nat.log 2 j + 1) ∧ 1 ≤ Nat.log 2 j + 1 ∧
      Nat.log 2 j + 1 ≤ d - 1 :=
  ⟨Nat.pow_log_le_self 2 hj0, Nat.lt_pow_succ_log_self one_lt_two j, Nat.le_add_left 1 _,
    Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow hj0 hj)⟩

/-- **Two points determine a line** (Haas–Giles 2025, §3.4: "for the first two dyadic intervals
there are only two points in each so `Z̄_j` will exactly match `Z_j`"): if `(a, b)` minimises the
least-squares objective (19) `∑_j (a + b j − Z_j)²` over an interval of two points `j₁ ≠ j₂`, the
fit is exact: `a + b j₁ = Z_{j₁}` and `a + b j₂ = Z_{j₂}`. -/
theorem affine_fit_exact {j₁ j₂ : ℝ} (h : j₁ ≠ j₂) (Z₁ Z₂ : ℝ) {a b : ℝ}
    (hmin : ∀ a' b' : ℝ, (a + b * j₁ - Z₁) ^ 2 + (a + b * j₂ - Z₂) ^ 2 ≤
      (a' + b' * j₁ - Z₁) ^ 2 + (a' + b' * j₂ - Z₂) ^ 2) :
    a + b * j₁ = Z₁ ∧ a + b * j₂ = Z₂ := by
  have hd : j₂ - j₁ ≠ 0 := sub_ne_zero.2 h.symm
  have h1 : (Z₁ - (Z₂ - Z₁) / (j₂ - j₁) * j₁ + (Z₂ - Z₁) / (j₂ - j₁) * j₁ - Z₁) ^ 2 = 0 := by
    ring
  have h2 : (Z₁ - (Z₂ - Z₁) / (j₂ - j₁) * j₁ + (Z₂ - Z₁) / (j₂ - j₁) * j₂ - Z₂) ^ 2 = 0 := by
    have e : (Z₂ - Z₁) / (j₂ - j₁) * (j₂ - j₁) = Z₂ - Z₁ := div_mul_cancel₀ _ hd
    have e' : Z₁ - (Z₂ - Z₁) / (j₂ - j₁) * j₁ + (Z₂ - Z₁) / (j₂ - j₁) * j₂ - Z₂ = 0 := by
      linear_combination e
    rw [e']
    ring
  have hs := hmin (Z₁ - (Z₂ - Z₁) / (j₂ - j₁) * j₁) ((Z₂ - Z₁) / (j₂ - j₁))
  rw [h1, h2] at hs
  have q1 := sq_nonneg (a + b * j₁ - Z₁)
  have q2 := sq_nonneg (a + b * j₂ - Z₂)
  have r1 : (a + b * j₁ - Z₁) ^ 2 = 0 := le_antisymm (by linarith) q1
  have r2 : (a + b * j₂ - Z₂) ^ 2 = 0 := le_antisymm (by linarith) q2
  have s1 : a + b * j₁ - Z₁ = 0 := (pow_eq_zero_iff two_ne_zero).1 r1
  have s2 : a + b * j₂ - Z₂ = 0 := (pow_eq_zero_iff two_ne_zero).1 r2
  exact ⟨by linarith, by linarith⟩

end Method3

end MLMC
