import MlmcLean.ApproxNormal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The mean-square error of the lookup tables as `d → ∞` (Haas–Giles 2025, §3.4)

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §3.4 "Comparison of the three inversion methods", pp. 7–8: "as
`d` tends to infinity, the uniform intervals give `MSE → 0` and the dyadic intervals give
`MSE → C`, for some positive constant `C`.  The latter is because with our simple dyadic
segmentation, when `d` increases by 1 the MSE is reduced only in the interval closest to 0, so the
error due to the other intervals remains the same", and "with dyadic intervals, the MSE value
cannot be arbitrarily small".

As in `MlmcLean/ApproxNormal.lean`, `f : ℝ → ℝ` stands for `Φ⁻¹`, with `f` and `f²`
interval-integrable on `[0, 1]`; `I_j = [u_j, u_{j+1}]`, `u_j = 2^{−d} j`, `j < 2^d`, are the
uniform intervals and `Z_j` is the LUT value (15), the mean of `f` over `I_j`.

* **Uniform intervals** (`tendsto_method1MSE`): if `f` is monotone on `(0, 1)`, as `Φ⁻¹` is, the
  mean-square error `∑_j ∫_{I_j} (Z_j − f)²` of method 1 tends to `0` as `d → ∞`.  On an interior
  interval both `Z_j` and `f` lie between the values of `f` at its ends
  (`lutValue_mem_of_monotoneOn`), so the interior intervals contribute at most
  `2^{−d}(f(1 − 2^{−d}) − f(2^{−d}))²`, and each end interval at most `∫ f²` over it
  (`method1MSE_le`); by monotonicity `2^{−d} f(2^{−d})² ≤ ∫₀^{2^{−d}} f² + 2^{−d} f(1/2)²`
  (`mul_sq_le_left`, `mul_sq_le_right`).  All of these tend to `0`.
* **Dyadic intervals** (`dyadic_mse_ge`, `method3_mse_ge`, `method3_mse_not_tendsto_zero`):
  method 3 takes the values `a + b j` on the intervals `I_j` of a dyadic interval
  `[2^{−(k+1)}, 2^{−k}]` (those with `2^{d−k−1} ≤ j < 2^{d−k}`).  If `f` is strongly concave there,
  `2f(u + s) − f(u) − f(u + 2s) ≥ μ s²` with `μ > 0` (as `Φ⁻¹` is on `[2^{−(k+1)}, 2^{−k}]` for
  `k ≥ 2`, where `(Φ⁻¹)'' = Φ⁻¹/φ(Φ⁻¹)² ≤ 2π Φ⁻¹(1/4) < 0`), then for every `d ≥ k + 3` and all
  `a`, `b` the mean-square error on these intervals is at least `c = μ² 2^{−5(k+3)}/6`: an affine
  sequence has zero second differences, while by (18) and concavity the second differences
  `2Z_{j+m} − Z_j − Z_{j+2m}` of the LUT values at the spacing `m = 2^{d−k−3}` are at least
  `μ 4^{−(k+3)}`.  So the MSE of method 3 stays above `c` and does not tend to `0`.  The limit `C`
  of the paper (its existence and value) is not formalised; the lower bound is the claim of p. 8.
-/

open MeasureTheory Finset Filter Topology

namespace MLMC

variable {f : ℝ → ℝ}

/-! ### Uniform intervals: the mean-square error of method 1 tends to `0` -/

section Uniform

/-- The mean-square error of method 1 with `2^d` uniform intervals (Haas–Giles 2025, §3.1, (14)
summed over the intervals, and §3.4): `∑_{j<2^d} ∫_{I_j} (Z_j − f)²`. -/
noncomputable def method1MSE (f : ℝ → ℝ) (d : ℕ) : ℝ :=
  ∑ j ∈ range (2 ^ d), ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2

/-- `(z − f)²` is interval-integrable when `f` and `f²` are. -/
lemma intervalIntegrable_sq_sub {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume a b) (z : ℝ) :
    IntervalIntegrable (fun u => (z - f u) ^ 2) volume a b := by
  have e : (fun u => (z - f u) ^ 2) = fun u => (z ^ 2 - 2 * z * f u) + f u ^ 2 :=
    funext fun u => by ring
  rw [e]
  exact (intervalIntegrable_const.sub (hf.const_mul (2 * z))).add hf2

/-- On an interval `I_j` where `f` is monotone, the LUT value (15) lies between the values of `f`
at the ends: `f(u_j) ≤ Z_j ≤ f(u_{j+1})` (Haas–Giles 2025, §3.1). -/
lemma lutValue_mem_of_monotoneOn {d j : ℕ}
    (hmono : MonotoneOn f (Set.Icc (gridPt d j) (gridPt d (j + 1))))
    (hf : IntervalIntegrable f volume (gridPt d j) (gridPt d (j + 1))) :
    f (gridPt d j) ≤ lutValue f d j ∧ lutValue f d j ≤ f (gridPt d (j + 1)) := by
  have hab : gridPt d j ≤ gridPt d (j + 1) := (gridPt_lt d j).le
  have hpos : (0 : ℝ) < 2 ^ d := by positivity
  have h1 : ∫ _ in gridPt d j..gridPt d (j + 1), f (gridPt d j) ≤
      ∫ u in gridPt d j..gridPt d (j + 1), f u :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const hf fun u hu =>
      hmono (Set.left_mem_Icc.2 hab) hu hu.1
  have h2 : ∫ u in gridPt d j..gridPt d (j + 1), f u ≤
      ∫ _ in gridPt d j..gridPt d (j + 1), f (gridPt d (j + 1)) :=
    intervalIntegral.integral_mono_on hab hf intervalIntegrable_const fun u hu =>
      hmono hu (Set.right_mem_Icc.2 hab) hu.2
  rw [intervalIntegral.integral_const, smul_eq_mul, gridPt_succ_sub] at h1 h2
  constructor
  · calc f (gridPt d j) = 2 ^ d * ((2 ^ d)⁻¹ * f (gridPt d j)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
      _ ≤ 2 ^ d * ∫ u in gridPt d j..gridPt d (j + 1), f u :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = lutValue f d j := rfl
  · calc lutValue f d j = 2 ^ d * ∫ u in gridPt d j..gridPt d (j + 1), f u := rfl
      _ ≤ 2 ^ d * ((2 ^ d)⁻¹ * f (gridPt d (j + 1))) := mul_le_mul_of_nonneg_left h2 hpos.le
      _ = f (gridPt d (j + 1)) := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

/-- On an interval `I_j` where `f` is monotone, `∫_{I_j} (Z_j − f)² ≤ 2^{−d}(f(u_{j+1}) − f(u_j))²`
(Haas–Giles 2025, §3.4). -/
lemma integral_sq_sub_lutValue_le {d j : ℕ}
    (hmono : MonotoneOn f (Set.Icc (gridPt d j) (gridPt d (j + 1))))
    (hf : IntervalIntegrable f volume (gridPt d j) (gridPt d (j + 1)))
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume (gridPt d j) (gridPt d (j + 1))) :
    ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 ≤
      (2 ^ d)⁻¹ * (f (gridPt d (j + 1)) - f (gridPt d j)) ^ 2 := by
  have hab : gridPt d j ≤ gridPt d (j + 1) := (gridPt_lt d j).le
  obtain ⟨hZ1, hZ2⟩ := lutValue_mem_of_monotoneOn hmono hf
  calc ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2
      ≤ ∫ _ in gridPt d j..gridPt d (j + 1), (f (gridPt d (j + 1)) - f (gridPt d j)) ^ 2 := by
        refine intervalIntegral.integral_mono_on hab (intervalIntegrable_sq_sub hf hf2 _)
          intervalIntegrable_const fun u hu => ?_
        have h1 := hmono (Set.left_mem_Icc.2 hab) hu hu.1
        have h2 := hmono hu (Set.right_mem_Icc.2 hab) hu.2
        exact sq_le_sq' (by linarith) (by linarith)
    _ = (2 ^ d)⁻¹ * (f (gridPt d (j + 1)) - f (gridPt d j)) ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul, gridPt_succ_sub]

/-- The mean-square error on `I_j` is at most `∫_{I_j} f²`: the LUT value does at least as well
as the constant `0` ((14)–(15), Haas–Giles 2025, §3.1). -/
lemma integral_sq_sub_lutValue_le_sq {d j : ℕ}
    (hf : IntervalIntegrable f volume (gridPt d j) (gridPt d (j + 1)))
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume (gridPt d j) (gridPt d (j + 1))) :
    ∫ u in gridPt d j..gridPt d (j + 1), (lutValue f d j - f u) ^ 2 ≤
      ∫ u in gridPt d j..gridPt d (j + 1), f u ^ 2 := by
  have e : ∫ u in gridPt d j..gridPt d (j + 1), (0 - f u) ^ 2 =
      ∫ u in gridPt d j..gridPt d (j + 1), f u ^ 2 := by
    congr 1
    funext u
    ring
  rw [lutValue_eq_intervalMean, ← e]
  exact integral_sq_sub_intervalMean_le (gridPt_lt d j) hf hf2 0

/-- Near `0`: for `0 < h ≤ 1/2` and `f` monotone on `(0, 1)`,
`h f(h)² ≤ ∫₀ʰ f² + h f(1/2)²` (used for Haas–Giles 2025, §3.4). -/
lemma mul_sq_le_left {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1 / 2) (hmono : MonotoneOn f (Set.Ioo 0 1))
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 h) :
    h * f h ^ 2 ≤ (∫ u in (0 : ℝ)..h, f u ^ 2) + h * f (1 / 2) ^ 2 := by
  have hmem : h ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, by linarith⟩
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hc : 0 ≤ h * f (1 / 2) ^ 2 := mul_nonneg h0.le (sq_nonneg _)
  rcases le_or_gt (f h) 0 with hneg | hpos
  · have hI : ∫ _ in (0 : ℝ)..h, f h ^ 2 ≤ ∫ u in (0 : ℝ)..h, f u ^ 2 :=
      intervalIntegral.integral_mono_on_of_le_Ioo h0.le intervalIntegrable_const hf2
        fun u hu => by
          have hfu : f u ≤ f h := hmono ⟨hu.1, by linarith [hu.2]⟩ hmem hu.2.le
          nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hI
    linarith
  · have hfh : f h ≤ f (1 / 2) := hmono hmem hhalf h1
    have hsq : f h ^ 2 ≤ f (1 / 2) ^ 2 := pow_le_pow_left₀ hpos.le hfh 2
    have hI : 0 ≤ ∫ u in (0 : ℝ)..h, f u ^ 2 :=
      intervalIntegral.integral_nonneg h0.le fun u _ => sq_nonneg _
    nlinarith

/-- Near `1`: for `0 < h ≤ 1/2` and `f` monotone on `(0, 1)`,
`h f(1 − h)² ≤ ∫_{1−h}^1 f² + h f(1/2)²` (used for Haas–Giles 2025, §3.4). -/
lemma mul_sq_le_right {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1 / 2) (hmono : MonotoneOn f (Set.Ioo 0 1))
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume (1 - h) 1) :
    h * f (1 - h) ^ 2 ≤ (∫ u in (1 - h)..1, f u ^ 2) + h * f (1 / 2) ^ 2 := by
  have hmem : 1 - h ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hc : 0 ≤ h * f (1 / 2) ^ 2 := mul_nonneg h0.le (sq_nonneg _)
  rcases le_or_gt 0 (f (1 - h)) with hpos | hneg
  · have hI : ∫ _ in (1 - h)..1, f (1 - h) ^ 2 ≤ ∫ u in (1 - h)..1, f u ^ 2 :=
      intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) intervalIntegrable_const hf2
        fun u hu => by
          have hfu : f (1 - h) ≤ f u := hmono hmem ⟨by linarith [hu.1], hu.2⟩ hu.1.le
          nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_sub_cancel] at hI
    linarith
  · have hfh : f (1 / 2) ≤ f (1 - h) := hmono hhalf hmem (by linarith)
    have hsq : f (1 - h) ^ 2 ≤ f (1 / 2) ^ 2 := by nlinarith
    have hI : 0 ≤ ∫ u in (1 - h)..1, f u ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun u _ => sq_nonneg _
    nlinarith

/-- **The bound behind `MSE → 0` for uniform intervals** (Haas–Giles 2025, §3.4).  For `d ≥ 1` and
`f` monotone on `(0, 1)`, the mean-square error of method 1 is at most the mean square `∫ f²` over
the two end intervals plus `2^{−d}(f(u_{2^d−1}) − f(u_1))²`. -/
lemma method1MSE_le {d : ℕ} (hd : 1 ≤ d) (hmono : MonotoneOn f (Set.Ioo 0 1))
    (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) :
    method1MSE f d ≤ (∫ u in gridPt d 0..gridPt d (0 + 1), f u ^ 2) +
      (∫ u in gridPt d (2 ^ d - 1)..gridPt d (2 ^ d - 1 + 1), f u ^ 2) +
      (2 ^ d)⁻¹ * (f (gridPt d (2 ^ d - 1)) - f (gridPt d (0 + 1))) ^ 2 := by
  obtain ⟨n, hn⟩ : ∃ n, 2 ^ d = n + 1 + 1 := ⟨2 ^ d - 2, by
    have : 2 ≤ 2 ^ d :=
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    omega⟩
  have hlast : 2 ^ d - 1 = n + 1 := by omega
  rw [hlast]
  have hsplit : method1MSE f d =
      (∫ u in gridPt d 0..gridPt d (0 + 1), (lutValue f d 0 - f u) ^ 2) +
        ∑ i ∈ range n, ∫ u in gridPt d (i + 1)..gridPt d (i + 1 + 1),
          (lutValue f d (i + 1) - f u) ^ 2 +
        ∫ u in gridPt d (n + 1)..gridPt d (n + 1 + 1), (lutValue f d (n + 1) - f u) ^ 2 := by
    rw [method1MSE, hn, Finset.sum_range_succ, Finset.sum_range_succ']
    ring
  have hcell : ∀ j, j < 2 ^ d → IntervalIntegrable f volume (gridPt d j) (gridPt d (j + 1)) ∧
      IntervalIntegrable (fun u => f u ^ 2) volume (gridPt d j) (gridPt d (j + 1)) :=
    fun j hj => ⟨intervalIntegrable_cell hf hj, intervalIntegrable_cell hf2 hj⟩
  -- the interior intervals lie in `(0, 1)`, where `f` is monotone
  have hmono_cell : ∀ i < n,
      MonotoneOn f (Set.Icc (gridPt d (i + 1)) (gridPt d (i + 1 + 1))) := by
    intro i hi
    refine hmono.mono fun u hu => ⟨?_, ?_⟩
    · have h0 : 0 < gridPt d (i + 1) := by
        unfold gridPt
        positivity
      linarith [hu.1]
    · have h1 : gridPt d (i + 1 + 1) < 1 := by
        unfold gridPt
        rw [div_lt_one (by positivity)]
        have h2 : i + 1 + 1 < 2 ^ d := by omega
        exact_mod_cast h2
      linarith [hu.2]
  have hmid : ∑ i ∈ range n, ∫ u in gridPt d (i + 1)..gridPt d (i + 1 + 1),
      (lutValue f d (i + 1) - f u) ^ 2 ≤
      (2 ^ d)⁻¹ * (f (gridPt d (n + 1)) - f (gridPt d (0 + 1))) ^ 2 := by
    have hΔ : ∀ i ∈ range n, 0 ≤ f (gridPt d (i + 1 + 1)) - f (gridPt d (i + 1)) := by
      intro i hi
      have hab : gridPt d (i + 1) ≤ gridPt d (i + 1 + 1) := (gridPt_lt d (i + 1)).le
      exact sub_nonneg.2 ((hmono_cell i (Finset.mem_range.1 hi)) (Set.left_mem_Icc.2 hab)
        (Set.right_mem_Icc.2 hab) hab)
    have htel : ∑ i ∈ range n, (f (gridPt d (i + 1 + 1)) - f (gridPt d (i + 1))) =
        f (gridPt d (n + 1)) - f (gridPt d (0 + 1)) :=
      Finset.sum_range_sub (fun i => f (gridPt d (i + 1))) n
    calc ∑ i ∈ range n, ∫ u in gridPt d (i + 1)..gridPt d (i + 1 + 1),
          (lutValue f d (i + 1) - f u) ^ 2
        ≤ ∑ i ∈ range n, (2 ^ d)⁻¹ * (f (gridPt d (i + 1 + 1)) - f (gridPt d (i + 1))) ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i + 1 < 2 ^ d := by
            have := Finset.mem_range.1 hi
            omega
          exact integral_sq_sub_lutValue_le (hmono_cell i (Finset.mem_range.1 hi))
            (hcell (i + 1) hi').1 (hcell (i + 1) hi').2
      _ = (2 ^ d)⁻¹ * ∑ i ∈ range n, (f (gridPt d (i + 1 + 1)) - f (gridPt d (i + 1))) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (2 ^ d)⁻¹ * (∑ i ∈ range n, (f (gridPt d (i + 1 + 1)) - f (gridPt d (i + 1)))) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [sq, Finset.sum_mul]
          refine Finset.sum_le_sum fun i hi => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hΔ hi) (hΔ i hi)
      _ = (2 ^ d)⁻¹ * (f (gridPt d (n + 1)) - f (gridPt d (0 + 1))) ^ 2 := by rw [htel]
  have h0 : 0 < 2 ^ d := by positivity
  have hn1 : n + 1 < 2 ^ d := by omega
  have hfirst := integral_sq_sub_lutValue_le_sq (hcell 0 h0).1 (hcell 0 h0).2
  have hlast' := integral_sq_sub_lutValue_le_sq (hcell (n + 1) hn1).1 (hcell (n + 1) hn1).2
  rw [hsplit]
  linarith

/-- **Uniform intervals give `MSE → 0`** (Haas–Giles 2025, §3.4, p. 7: "as `d` tends to infinity,
the uniform intervals give `MSE → 0`").  If `f` is monotone on `(0, 1)`, as `Φ⁻¹` is, and `f`, `f²`
are interval-integrable on `[0, 1]`, the mean-square error `∑_{j<2^d} ∫_{I_j} (Z_j − f)²` of
method 1 tends to `0` as `d → ∞`. -/
theorem tendsto_method1MSE (hmono : MonotoneOn f (Set.Ioo 0 1))
    (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) :
    Tendsto (method1MSE f) atTop (𝓝 0) := by
  have hG : ContinuousOn (fun x => ∫ u in (0 : ℝ)..x, f u ^ 2) (Set.uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval' hf2 Set.left_mem_uIcc
  have hh : Tendsto (fun d : ℕ => ((2 : ℝ) ^ d)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hmemI : ∀ d : ℕ, ((2 : ℝ) ^ d)⁻¹ ∈ Set.uIcc (0 : ℝ) 1 := fun d => by
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)⟩
  have hmemI' : ∀ d : ℕ, 1 - ((2 : ℝ) ^ d)⁻¹ ∈ Set.uIcc (0 : ℝ) 1 := fun d => by
    have h := hmemI d
    rw [Set.uIcc_of_le zero_le_one] at h ⊢
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  -- `∫₀^{2^{−d}} f² → 0`
  have hA : Tendsto (fun d : ℕ => ∫ u in (0 : ℝ)..((2 : ℝ) ^ d)⁻¹, f u ^ 2) atTop (𝓝 0) := by
    have h1 := (hG 0 Set.left_mem_uIcc).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hh, Eventually.of_forall hmemI⟩)
    rw [intervalIntegral.integral_same] at h1
    exact h1
  -- `∫_{1−2^{−d}}^1 f² → 0`
  have hB : Tendsto (fun d : ℕ => (∫ u in (0 : ℝ)..1, f u ^ 2) -
      ∫ u in (0 : ℝ)..(1 - ((2 : ℝ) ^ d)⁻¹), f u ^ 2) atTop (𝓝 0) := by
    have hh' : Tendsto (fun d : ℕ => 1 - ((2 : ℝ) ^ d)⁻¹) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hh
      rw [sub_zero] at h
      exact h
    have h1 := (hG 1 Set.right_mem_uIcc).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hh', Eventually.of_forall hmemI'⟩)
    have h2 := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ∫ u in (0 : ℝ)..1, f u ^ 2) atTop
        (𝓝 (∫ u in (0 : ℝ)..1, f u ^ 2))).sub h1
    rw [sub_self] at h2
    exact h2
  have hC : Tendsto (fun d : ℕ => ((2 : ℝ) ^ d)⁻¹ * f (1 / 2) ^ 2) atTop (𝓝 0) := by
    have h := hh.mul_const (f (1 / 2) ^ 2)
    rw [zero_mul] at h
    exact h
  have hbound : Tendsto (fun d : ℕ =>
      3 * (∫ u in (0 : ℝ)..((2 : ℝ) ^ d)⁻¹, f u ^ 2) +
        3 * ((∫ u in (0 : ℝ)..1, f u ^ 2) - ∫ u in (0 : ℝ)..(1 - ((2 : ℝ) ^ d)⁻¹), f u ^ 2) +
        4 * (((2 : ℝ) ^ d)⁻¹ * f (1 / 2) ^ 2)) atTop (𝓝 0) := by
    have h := ((hA.const_mul 3).add (hB.const_mul 3)).add (hC.const_mul 4)
    simp only [mul_zero, add_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
  · exact Eventually.of_forall fun d => show (0 : ℝ) ≤ method1MSE f d from
      Finset.sum_nonneg fun j _ =>
        intervalIntegral.integral_nonneg (gridPt_lt d j).le fun u _ => sq_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ d)⁻¹ := by positivity
    have hle : ((2 : ℝ) ^ d)⁻¹ ≤ 1 / 2 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num)
        (calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd)
    have e0 : gridPt d 0 = 0 := by simp [gridPt]
    have e1 : gridPt d (0 + 1) = ((2 : ℝ) ^ d)⁻¹ := by simp [gridPt]
    have e2 : gridPt d (2 ^ d - 1) = 1 - ((2 : ℝ) ^ d)⁻¹ := by
      rw [gridPt, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        sub_div, div_self (by positivity), one_div]
    have e3 : gridPt d (2 ^ d - 1 + 1) = 1 := by
      rw [Nat.sub_add_cancel Nat.one_le_two_pow, gridPt, Nat.cast_pow, Nat.cast_ofNat,
        div_self (by positivity)]
    have hbd := method1MSE_le hd hmono hf hf2
    rw [e0, e1, e2, e3] at hbd
    have hI1 : IntervalIntegrable (fun u => f u ^ 2) volume 0 ((2 : ℝ) ^ d)⁻¹ :=
      hf2.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (hmemI d))
    have hI0 : IntervalIntegrable (fun u => f u ^ 2) volume 0 (1 - ((2 : ℝ) ^ d)⁻¹) :=
      hf2.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (hmemI' d))
    have hI2 : IntervalIntegrable (fun u => f u ^ 2) volume (1 - ((2 : ℝ) ^ d)⁻¹) 1 :=
      hf2.mono_set (Set.uIcc_subset_uIcc (hmemI' d) Set.right_mem_uIcc)
    have hL := mul_sq_le_left hpos hle hmono hI1
    have hR := mul_sq_le_right hpos hle hmono hI2
    have hsplit : ∫ u in (1 - ((2 : ℝ) ^ d)⁻¹)..1, f u ^ 2 =
        (∫ u in (0 : ℝ)..1, f u ^ 2) - ∫ u in (0 : ℝ)..(1 - ((2 : ℝ) ^ d)⁻¹), f u ^ 2 :=
      (intervalIntegral.integral_interval_sub_left hf2 hI0).symm
    have hsq : ((2 : ℝ) ^ d)⁻¹ * (f (1 - ((2 : ℝ) ^ d)⁻¹) - f ((2 : ℝ) ^ d)⁻¹) ^ 2 ≤
        2 * (((2 : ℝ) ^ d)⁻¹ * f (1 - ((2 : ℝ) ^ d)⁻¹) ^ 2) +
          2 * (((2 : ℝ) ^ d)⁻¹ * f ((2 : ℝ) ^ d)⁻¹ ^ 2) := by
      nlinarith [mul_nonneg hpos.le (sq_nonneg (f (1 - ((2 : ℝ) ^ d)⁻¹) + f ((2 : ℝ) ^ d)⁻¹))]
    rw [hsplit] at hbd hR
    linarith

end Uniform

/-! ### Dyadic intervals: the mean-square error of method 3 stays away from `0` -/

section Dyadic

/-- The grid points add: `u_x + c u_y = u_{x + c y}`. -/
lemma gridPt_add_mul (d x y c : ℕ) : gridPt d x + c * gridPt d y = gridPt d (x + c * y) := by
  unfold gridPt
  push_cast
  ring

/-- `u_{2^e} = 2^{−k}` on the grid with `2^{k+e}` intervals. -/
lemma gridPt_two_pow {d e k : ℕ} (h : d = k + e) : gridPt d (2 ^ e) = ((2 : ℝ) ^ k)⁻¹ := by
  subst h
  rw [gridPt, Nat.cast_pow, Nat.cast_ofNat, pow_add,
    div_mul_cancel_right₀ (pow_ne_zero e (two_ne_zero : (2 : ℝ) ≠ 0))]

/-- `x² ≤ 6(a² + b² + c²)` for `x = a − 2b + c` (Cauchy–Schwarz). -/
lemma sq_sub_two_mul_add_le (a b c : ℝ) : (a - 2 * b + c) ^ 2 ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (2 * a + b), sq_nonneg (2 * c + b), sq_nonneg (a - c)]

/-- **The second differences of the LUT values of a strongly concave `f`** (Haas–Giles 2025, §3.1,
(15), and §3.4).  If `2f(u + s) − f(u) − f(u + 2s) ≥ μ s²` for `u ∈ I_j`, where `s = u_m`, and the
intervals `I_j`, `I_{j+m}`, `I_{j+2m}` lie in `[0, 1]`, then `2Z_{j+m} − Z_j − Z_{j+2m} ≥ μ s²`. -/
lemma lutValue_second_diff_ge (hf : IntervalIntegrable f volume 0 1) {d j m : ℕ}
    (hj : j + 2 * m < 2 ^ d) {μ : ℝ}
    (hconc : ∀ u ∈ Set.Icc (gridPt d j) (gridPt d (j + 1)),
      μ * gridPt d m ^ 2 ≤ 2 * f (u + gridPt d m) - f u - f (u + 2 * gridPt d m)) :
    μ * gridPt d m ^ 2 ≤
      2 * lutValue f d (j + m) - lutValue f d j - lutValue f d (j + 2 * m) := by
  have hab : gridPt d j ≤ gridPt d (j + 1) := (gridPt_lt d j).le
  have hpos : (0 : ℝ) < 2 ^ d := by positivity
  -- the intervals `I_{j+m}` and `I_{j+2m}` are the translates of `I_j` by `u_m` and `2u_m`
  have hA1 : gridPt d j + gridPt d m = gridPt d (j + m) := by
    unfold gridPt
    push_cast
    ring
  have hB1 : gridPt d (j + 1) + gridPt d m = gridPt d (j + m + 1) := by
    unfold gridPt
    push_cast
    ring
  have hA2 : gridPt d j + 2 * gridPt d m = gridPt d (j + 2 * m) := by
    unfold gridPt
    push_cast
    ring
  have hB2 : gridPt d (j + 1) + 2 * gridPt d m = gridPt d (j + 2 * m + 1) := by
    unfold gridPt
    push_cast
    ring
  have e1 : ∫ u in gridPt d j..gridPt d (j + 1), f (u + gridPt d m) =
      ∫ u in gridPt d (j + m)..gridPt d (j + m + 1), f u := by
    rw [intervalIntegral.integral_comp_add_right f (gridPt d m), hA1, hB1]
  have e2 : ∫ u in gridPt d j..gridPt d (j + 1), f (u + 2 * gridPt d m) =
      ∫ u in gridPt d (j + 2 * m)..gridPt d (j + 2 * m + 1), f u := by
    rw [intervalIntegral.integral_comp_add_right f (2 * gridPt d m), hA2, hB2]
  have hI0 : IntervalIntegrable f volume (gridPt d j) (gridPt d (j + 1)) :=
    intervalIntegrable_cell hf (by omega)
  have hI1 : IntervalIntegrable (fun u => f (u + gridPt d m)) volume (gridPt d j)
      (gridPt d (j + 1)) := by
    have h := (intervalIntegrable_cell hf (show j + m < 2 ^ d by omega)).comp_add_right
      (gridPt d m)
    rwa [← hA1, ← hB1, add_sub_cancel_right, add_sub_cancel_right] at h
  have hI2 : IntervalIntegrable (fun u => f (u + 2 * gridPt d m)) volume (gridPt d j)
      (gridPt d (j + 1)) := by
    have h := (intervalIntegrable_cell hf hj).comp_add_right (2 * gridPt d m)
    rwa [← hA2, ← hB2, add_sub_cancel_right, add_sub_cancel_right] at h
  have hmono : ∫ _ in gridPt d j..gridPt d (j + 1), μ * gridPt d m ^ 2 ≤
      ∫ u in gridPt d j..gridPt d (j + 1),
        (2 * f (u + gridPt d m) - f u - f (u + 2 * gridPt d m)) :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (((hI1.const_mul 2).sub hI0).sub hI2) hconc
  rw [intervalIntegral.integral_const, smul_eq_mul, gridPt_succ_sub,
    intervalIntegral.integral_sub ((hI1.const_mul 2).sub hI0) hI2,
    intervalIntegral.integral_sub (hI1.const_mul 2) hI0, intervalIntegral.integral_const_mul,
    e1, e2] at hmono
  have key := mul_le_mul_of_nonneg_left hmono hpos.le
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at key
  unfold lutValue
  linarith

/-- **Dyadic intervals keep a positive mean-square error** (Haas–Giles 2025, §3.3–§3.4, p. 7: "the
dyadic intervals give `MSE → C`, for some positive constant `C`"; p. 8: "with dyadic intervals, the
MSE value cannot be arbitrarily small").  Method 3 takes the values `a + b j` on the intervals
`I_j`, `2^{d−k−1} ≤ j < 2^{d−k}`, of the dyadic interval `[2^{−(k+1)}, 2^{−k}]`.  If `f` is strongly
concave there, `2f(u + s) − f(u) − f(u + 2s) ≥ μ s²` with `μ > 0`, then there is `c > 0` such that
for every `d ≥ k + 3` and all `a`, `b` the mean-square error on these intervals is at least `c`
(namely `c = μ² 2^{−5(k+3)}/6`). -/
theorem dyadic_mse_ge (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {k : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (hconc : ∀ u s : ℝ, ((2 : ℝ) ^ (k + 1))⁻¹ ≤ u → 0 ≤ s → u + 2 * s ≤ ((2 : ℝ) ^ k)⁻¹ →
      μ * s ^ 2 ≤ 2 * f (u + s) - f u - f (u + 2 * s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, k + 3 ≤ d → ∀ a b : ℝ,
      c ≤ ∑ j ∈ Ico (2 ^ (d - k - 1)) (2 ^ (d - k)),
        ∫ u in gridPt d j..gridPt d (j + 1), (a + b * j - f u) ^ 2 := by
  refine ⟨μ ^ 2 * (((2 : ℝ) ^ (k + 3))⁻¹) ^ 5 / 6, by positivity, fun d hd a b => ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = k + 3 + e := ⟨d - (k + 3), by omega⟩
  have hlo : k + 3 + e - k - 1 = e + 2 := by omega
  have hhi : k + 3 + e - k = e + 3 := by omega
  rw [hlo, hhi]
  -- the spacing `m = 2^e`, `s = u_m = 2^{−(k+3)}`, and the ends of the dyadic interval
  have hs : gridPt (k + 3 + e) (2 ^ e) = ((2 : ℝ) ^ (k + 3))⁻¹ := gridPt_two_pow rfl
  have hp : gridPt (k + 3 + e) (2 ^ (e + 2)) = ((2 : ℝ) ^ (k + 1))⁻¹ :=
    gridPt_two_pow (by omega)
  have hq : gridPt (k + 3 + e) (2 ^ (e + 3)) = ((2 : ℝ) ^ k)⁻¹ := gridPt_two_pow (by omega)
  have h4 : 2 ^ (e + 2) = 4 * 2 ^ e := by ring
  have h8 : 2 ^ (e + 3) = 8 * 2 ^ e := by ring
  have hd8 : 2 ^ (e + 3) ≤ 2 ^ (k + 3 + e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsp : (0 : ℝ) < ((2 : ℝ) ^ (k + 3))⁻¹ := by positivity
  -- the residuals `r_j = a + b j − Z_j` of the LUT values
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, r = fun y => a + b * y - lutValue f (k + 3 + e) y := ⟨_, rfl⟩
  have hr' : ∀ y : ℕ, r y = a + b * y - lutValue f (k + 3 + e) y := fun y => by rw [hr]
  -- (18): the mean-square error on `I_j` is at least `2^{−d} r_j²`
  have hcell : ∀ j ∈ Ico (2 ^ (e + 2)) (2 ^ (e + 3)),
      ((2 : ℝ) ^ (k + 3 + e))⁻¹ * r j ^ 2 ≤
        ∫ u in gridPt (k + 3 + e) j..gridPt (k + 3 + e) (j + 1), (a + b * j - f u) ^ 2 := by
    intro j hj
    have hj' : j < 2 ^ (k + 3 + e) := lt_of_lt_of_le (Finset.mem_Ico.1 hj).2 hd8
    rw [integral_sq_sub_lutValue (intervalIntegrable_cell hf hj')
      (intervalIntegrable_cell hf2 hj'), hr' j]
    have h0 : 0 ≤ ∫ u in gridPt (k + 3 + e) j..gridPt (k + 3 + e) (j + 1),
        (lutValue f (k + 3 + e) j - f u) ^ 2 :=
      intervalIntegral.integral_nonneg (gridPt_lt _ j).le fun u _ => sq_nonneg _
    linarith
  -- each second difference of `r` at the spacing `2^e` is at least `μ s²`
  have hsecond : ∀ i < 2 ^ e,
      (μ * (((2 : ℝ) ^ (k + 3))⁻¹) ^ 2) ^ 2 ≤
        6 * (r (2 ^ (e + 2) + i) ^ 2 + r (2 ^ (e + 2) + i + 2 ^ e) ^ 2 +
          r (2 ^ (e + 2) + i + 2 * 2 ^ e) ^ 2) := by
    intro i hi
    have hj : 2 ^ (e + 2) + i + 2 * 2 ^ e < 2 ^ (k + 3 + e) := by omega
    have hconc' : ∀ u ∈ Set.Icc (gridPt (k + 3 + e) (2 ^ (e + 2) + i))
        (gridPt (k + 3 + e) (2 ^ (e + 2) + i + 1)),
        μ * gridPt (k + 3 + e) (2 ^ e) ^ 2 ≤ 2 * f (u + gridPt (k + 3 + e) (2 ^ e)) - f u -
          f (u + 2 * gridPt (k + 3 + e) (2 ^ e)) := by
      intro u hu
      have hlo' : ((2 : ℝ) ^ (k + 1))⁻¹ ≤ u := by
        rw [← hp]
        refine le_trans ?_ hu.1
        unfold gridPt
        gcongr
        exact_mod_cast Nat.le_add_right _ _
      have hhi' : u + 2 * gridPt (k + 3 + e) (2 ^ e) ≤ ((2 : ℝ) ^ k)⁻¹ := by
        rw [← hq]
        have h1 := gridPt_add_mul (k + 3 + e) (2 ^ (e + 2) + i + 1) (2 ^ e) 2
        push_cast at h1
        have h2 : gridPt (k + 3 + e) (2 ^ (e + 2) + i + 1 + 2 * 2 ^ e) ≤
            gridPt (k + 3 + e) (2 ^ (e + 3)) := by
          unfold gridPt
          gcongr
          have : 2 ^ (e + 2) + i + 1 + 2 * 2 ^ e ≤ 2 ^ (e + 3) := by omega
          exact_mod_cast this
        linarith [hu.2]
      rw [hs]
      exact hconc u _ hlo' hsp.le (by rwa [hs] at hhi')
    have hZ := lutValue_second_diff_ge hf hj hconc'
    rw [hs] at hZ
    have hX : μ * (((2 : ℝ) ^ (k + 3))⁻¹) ^ 2 ≤ r (2 ^ (e + 2) + i) -
        2 * r (2 ^ (e + 2) + i + 2 ^ e) + r (2 ^ (e + 2) + i + 2 * 2 ^ e) := by
      rw [hr' (2 ^ (e + 2) + i), hr' (2 ^ (e + 2) + i + 2 ^ e),
        hr' (2 ^ (e + 2) + i + 2 * 2 ^ e)]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      linarith
    have hX0 : 0 ≤ μ * (((2 : ℝ) ^ (k + 3))⁻¹) ^ 2 := by positivity
    calc (μ * (((2 : ℝ) ^ (k + 3))⁻¹) ^ 2) ^ 2
        ≤ (r (2 ^ (e + 2) + i) - 2 * r (2 ^ (e + 2) + i + 2 ^ e) +
            r (2 ^ (e + 2) + i + 2 * 2 ^ e)) ^ 2 := pow_le_pow_left₀ hX0 hX 2
      _ ≤ 6 * (r (2 ^ (e + 2) + i) ^ 2 + r (2 ^ (e + 2) + i + 2 ^ e) ^ 2 +
            r (2 ^ (e + 2) + i + 2 * 2 ^ e) ^ 2) := sq_sub_two_mul_add_le _ _ _
  -- sum over the first quarter of the dyadic interval
  have hsum : (2 ^ e : ℕ) * (μ * (((2 : ℝ) ^ (k + 3))⁻¹) ^ 2) ^ 2 ≤
      6 * ∑ j ∈ Ico (2 ^ (e + 2)) (2 ^ (e + 3)), r j ^ 2 := by
    have hIco : ∑ j ∈ Ico (2 ^ (e + 2)) (2 ^ (e + 3)), r j ^ 2 =
        ∑ i ∈ range (2 ^ e + 2 ^ e + 2 ^ e + 2 ^ e), r (2 ^ (e + 2) + i) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      congr 2
      omega
    have hsub : ∑ i ∈ range (2 ^ e + 2 ^ e + 2 ^ e), r (2 ^ (e + 2) + i) ^ 2 ≤
        ∑ i ∈ range (2 ^ e + 2 ^ e + 2 ^ e + 2 ^ e), r (2 ^ (e + 2) + i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        fun i _ _ => sq_nonneg _
    have hthree : ∑ i ∈ range (2 ^ e + 2 ^ e + 2 ^ e), r (2 ^ (e + 2) + i) ^ 2 =
        ∑ i ∈ range (2 ^ e), (r (2 ^ (e + 2) + i) ^ 2 + r (2 ^ (e + 2) + i + 2 ^ e) ^ 2 +
          r (2 ^ (e + 2) + i + 2 * 2 ^ e) ^ 2) := by
      rw [Finset.sum_range_add, Finset.sum_range_add, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show 2 ^ (e + 2) + (2 ^ e + i) = 2 ^ (e + 2) + i + 2 ^ e by ring,
        show 2 ^ (e + 2) + (2 ^ e + 2 ^ e + i) = 2 ^ (e + 2) + i + 2 * 2 ^ e by ring]
    have hle : ∑ i ∈ range (2 ^ e), (μ * (((2 : ℝ) ^ (k + 3))⁻¹) ^ 2) ^ 2 ≤
        ∑ i ∈ range (2 ^ e), 6 * (r (2 ^ (e + 2) + i) ^ 2 +
          r (2 ^ (e + 2) + i + 2 ^ e) ^ 2 + r (2 ^ (e + 2) + i + 2 * 2 ^ e) ^ 2) :=
      Finset.sum_le_sum fun i hi => hsecond i (Finset.mem_range.1 hi)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, ← hthree] at hle
    rw [hIco]
    linarith
  -- (18) summed, and `2^{−d} 2^e = s`
  have hsum_cell : ((2 : ℝ) ^ (k + 3 + e))⁻¹ * ∑ j ∈ Ico (2 ^ (e + 2)) (2 ^ (e + 3)), r j ^ 2 ≤
      ∑ j ∈ Ico (2 ^ (e + 2)) (2 ^ (e + 3)),
        ∫ u in gridPt (k + 3 + e) j..gridPt (k + 3 + e) (j + 1), (a + b * j - f u) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hcell
  have hscale : ((2 : ℝ) ^ (k + 3 + e))⁻¹ * (2 ^ e : ℕ) = ((2 : ℝ) ^ (k + 3))⁻¹ := by
    rw [← hs, gridPt]
    push_cast
    ring
  have hdpos : (0 : ℝ) < ((2 : ℝ) ^ (k + 3 + e))⁻¹ := by positivity
  have key := mul_le_mul_of_nonneg_left hsum hdpos.le
  rw [← mul_assoc, hscale] at key
  calc μ ^ 2 * (((2 : ℝ) ^ (k + 3))⁻¹) ^ 5 / 6
      = ((2 : ℝ) ^ (k + 3))⁻¹ * (μ * (((2 : ℝ) ^ (k + 3))⁻¹) ^ 2) ^ 2 / 6 := by ring
    _ ≤ ((2 : ℝ) ^ (k + 3 + e))⁻¹ * ∑ j ∈ Ico (2 ^ (e + 2)) (2 ^ (e + 3)), r j ^ 2 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
        linarith
    _ ≤ _ := hsum_cell

/-- **The mean-square error of method 3 stays above a positive constant** (Haas–Giles 2025, §3.4,
p. 8: "with dyadic intervals, the MSE value cannot be arbitrarily small").  Under the hypotheses of
`dyadic_mse_ge`, there is `c > 0` such that for every `d ≥ k + 3`, every approximation that takes
the values `w_j` on the intervals `I_j`, `j < 2^d`, with `w_j = a + b j` on the intervals of the
dyadic interval `[2^{−(k+1)}, 2^{−k}]` (as method 3 does), has mean-square error
`∑_{j<2^d} ∫_{I_j} (w_j − f)² ≥ c`. -/
theorem method3_mse_ge (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {k : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (hconc : ∀ u s : ℝ, ((2 : ℝ) ^ (k + 1))⁻¹ ≤ u → 0 ≤ s → u + 2 * s ≤ ((2 : ℝ) ^ k)⁻¹ →
      μ * s ^ 2 ≤ 2 * f (u + s) - f u - f (u + 2 * s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, k + 3 ≤ d → ∀ w : ℕ → ℝ,
      (∃ a b : ℝ, ∀ j ∈ Ico (2 ^ (d - k - 1)) (2 ^ (d - k)), w j = a + b * j) →
        c ≤ ∑ j ∈ range (2 ^ d), ∫ u in gridPt d j..gridPt d (j + 1), (w j - f u) ^ 2 := by
  obtain ⟨c, hc, hbd⟩ := dyadic_mse_ge hf hf2 hμ hconc
  refine ⟨c, hc, fun d hd w ⟨a, b, hw⟩ => ?_⟩
  have hsub : Ico (2 ^ (d - k - 1)) (2 ^ (d - k)) ⊆ range (2 ^ d) := by
    intro j hj
    rw [Finset.mem_range]
    exact lt_of_lt_of_le (Finset.mem_Ico.1 hj).2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  calc c ≤ ∑ j ∈ Ico (2 ^ (d - k - 1)) (2 ^ (d - k)),
        ∫ u in gridPt d j..gridPt d (j + 1), (a + b * j - f u) ^ 2 := hbd d hd a b
    _ = ∑ j ∈ Ico (2 ^ (d - k - 1)) (2 ^ (d - k)),
        ∫ u in gridPt d j..gridPt d (j + 1), (w j - f u) ^ 2 :=
        Finset.sum_congr rfl fun j hj => by rw [hw j hj]
    _ ≤ ∑ j ∈ range (2 ^ d), ∫ u in gridPt d j..gridPt d (j + 1), (w j - f u) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
          intervalIntegral.integral_nonneg (gridPt_lt d j).le fun u _ => sq_nonneg _

/-- **Method 3 cannot make the MSE arbitrarily small** (Haas–Giles 2025, §3.4, pp. 7–8: the dyadic
intervals give `MSE → C > 0`; "the MSE value cannot be arbitrarily small").  Under the hypotheses
of `dyadic_mse_ge`, for every choice of method-3 approximations `w d` (affine in `j` on the
dyadic interval `[2^{−(k+1)}, 2^{−k}]` for each `d`), the mean-square error does not tend to `0` as
`d → ∞`. -/
theorem method3_mse_not_tendsto_zero (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) {k : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (hconc : ∀ u s : ℝ, ((2 : ℝ) ^ (k + 1))⁻¹ ≤ u → 0 ≤ s → u + 2 * s ≤ ((2 : ℝ) ^ k)⁻¹ →
      μ * s ^ 2 ≤ 2 * f (u + s) - f u - f (u + 2 * s))
    (w : ℕ → ℕ → ℝ)
    (hw : ∀ d, ∃ a b : ℝ, ∀ j ∈ Ico (2 ^ (d - k - 1)) (2 ^ (d - k)), w d j = a + b * j) :
    ¬ Tendsto (fun d => ∑ j ∈ range (2 ^ d),
      ∫ u in gridPt d j..gridPt d (j + 1), (w d j - f u) ^ 2) atTop (𝓝 0) := by
  intro htend
  obtain ⟨c, hc, hbd⟩ := method3_mse_ge hf hf2 hμ hconc
  obtain ⟨d, hd1, hd2⟩ := ((htend.eventually (gt_mem_nhds hc)).and
    (eventually_ge_atTop (k + 3))).exists
  exact absurd (hbd d hd2 (w d) (hw d)) (not_le.2 hd1)

end Dyadic

end MLMC
