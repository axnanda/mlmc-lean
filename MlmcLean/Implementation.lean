import MlmcLean.Algorithm
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Tactic.LinearCombination

/-!
# Implementation details of the MLMC algorithm (Giles 2015, §3.3–§3.5)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §3.3 (pp. 22–23),
§3.4 (the driver routine `mlmc.m`, pp. 23–26) and §3.5 (pp. 26–27) of the author's version.

**The driver `mlmc.m` (§3.4).**
* The level routine returns the sums `∑_n (P_ℓ^{(n)} − P_{ℓ−1}^{(n)})^p` for `p = 1, 2`, and the
  driver sets `ml = abs( suml(1,:)./Nl)`, `Vl = max(0, suml(2,:)./Nl - ml.^2)`.  With `s₁ = ∑ x_n`,
  `s₂ = ∑ x_n²`, `s₂/N − (s₁/N)² = N⁻¹ ∑ (x_n − s₁/N)² ≥ 0` (`powerSum_variance_eq`,
  `powerSum_variance_nonneg`), and for independent samples its mean is `(1 − N⁻¹) V`
  (`powerSum_variance_mean`).
* The floors `ml(l) = max(ml(l), 0.5*ml(l-1)/2^alpha)` and `Vl(l) = max(Vl(l), 0.5*Vl(l-1)/2^beta)`
  for `l = 3:L+1` (`floorEst`): "the estimates for `m_ℓ` and `V_ℓ` are not allowed to decrease by
  more than factor ½ relative to this anticipated value" (`le_floorEst`,
  `floorEst_ge_extrapolation`), and they are the smallest such estimates (`floorEst_le`).
* "If the user has not supplied the values for `α` and/or `β`, they are now estimated by linear
  regression" (`x = [(1:L)' ones(L,1)] \ log2(ml(2:end))'; alpha = max(0.5,-x(1));`): the
  least-squares line minimises the sum of squared residuals (`lsFit_le`), it recovers the slope of
  exactly affine data (`lsSlope_affine`), hence the rate `α` of exactly geometric corrections
  `c 2^{−αℓ}` from `log₂` of their means (`lsSlope_log_geometric`).

**The consistency check (§3.3).**  "The probability of this ratio being greater than unity is less
than 0.3%", for the ratio `|a − b + c|/(3(√V_a + √V_b + √V_c))`.  The bound `0.3%` presumes normal
estimates: for `N(0, 1)`, `P(|Z| > 3) < 0.003` (`gaussian_tail_three`, via the Mills-ratio bound
`∫_3^∞ φ ≤ φ(3)/3`), so under a normal model with the mean `0` of `consistency_mean` the check
fails with probability `< 0.003` (`consistency_check_gaussian`).  Without normality Chebyshev's
inequality still gives `≤ 1/9` (`consistency_check_chebyshev`).

**The kurtosis (§3.3).**  "Hence `O(κ)` samples are required to obtain a reasonable estimate for the
variance": the relative standard deviation `√((κ − 1)/N)` is at most `r` iff `N ≥ (κ − 1)/r²`
(`sampleVariance_relative_sd_le_iff`).  For `X ∈ {1, −1, 0}` with probabilities `p, q, 1 − p − q`:
`E[X] = p − q` (`integral_ternary`), and "we may get all `X^{(n)} = 0`, which will give an
estimated variance of zero", with probability `(1 − p − q)^N` for `N` independent samples
(`measureReal_ternary_zero`, `prob_all_zero`, `powerSum_variance_of_zero`).

**MLQMC (§3.5, (3.3)).**  "Doubling `N_ℓ` will usually eliminate a large fraction of the variance,
so the greatest reduction in total variance relative to the additional computational effort is
achieved by doubling `N_ℓ` on the level `ℓ* = argmax_ℓ V_ℓ/(N_ℓ C_ℓ)`": if doubling removes the
same fraction of `V_ℓ` on every level, the reduction per unit of added cost `N_ℓ C_ℓ` is largest
exactly on the levels that maximise `V_ℓ/(N_ℓ C_ℓ)` (`mlqmc_doubling_level`).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal

namespace MLMC

/-! ### §3.4: the variance estimate from power sums -/

/-- **The variance estimate of the driver** (Giles 2015, §3.4, p. 25: "`% compute absolute average
and variance` … `ml = abs( suml(1,:)./Nl); Vl = max(0, suml(2,:)./Nl - ml.^2);`", from the sums
`suml(1,:)`, `suml(2,:)` of the corrections and of their squares).  For `N ≥ 1` values `x_n`, with
`s₁ = ∑ x_n` and `s₂ = ∑ x_n²`, the estimate `s₂/N − (s₁/N)²` is the mean squared deviation from
the sample mean, `N⁻¹ ∑ (x_n − s₁/N)²`. -/
theorem powerSum_variance_eq (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ range N, x n ^ 2) / N - ((∑ n ∈ range N, x n) / N) ^ 2 =
      (∑ n ∈ range N, (x n - (∑ k ∈ range N, x k) / N) ^ 2) / N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨s, hs⟩ : ∃ s, s = ∑ k ∈ range N, x k := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = s / N := ⟨_, rfl⟩
  have hNm : (N : ℝ) * m = s := by rw [hm, mul_div_cancel₀ s hN']
  rw [← hs, ← hm]
  have e : ∑ n ∈ range N, (x n - m) ^ 2 = ∑ n ∈ range N, x n ^ 2 - 2 * m * s + N * m ^ 2 := by
    have h1 : ∀ n ∈ range N, (x n - m) ^ 2 = x n ^ 2 - 2 * m * x n + m ^ 2 := fun n _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [e, ← hNm]
  linear_combination m ^ 2 * mul_inv_cancel₀ hN'

/-- The variance estimate of the driver is never negative (Giles 2015, §3.4, p. 25): the
`max(0, ·)` in `Vl = max(0, suml(2,:)./Nl - ml.^2)` only guards against rounding errors. -/
theorem powerSum_variance_nonneg (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    0 ≤ (∑ n ∈ range N, x n ^ 2) / N - ((∑ n ∈ range N, x n) / N) ^ 2 := by
  rw [powerSum_variance_eq x hN]
  exact div_nonneg (Finset.sum_nonneg fun n _ => sq_nonneg _) (Nat.cast_nonneg N)

section PowerSumMean

variable {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {μ : Measure Ω} {ν : Measure Ω₀}

/-- **The mean of the variance estimate** (Giles 2015, §3.4, p. 25).  For `N ≥ 1` independent
samples `X(ω⁽ⁿ⁾)` of a square-integrable `X`, the estimate `s₂/N − (s₁/N)²` of the driver has mean
`(1 − N⁻¹) V[X]`: it is consistent, with bias `−V[X]/N`. -/
theorem powerSum_variance_mean [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {X : Ω₀ → ℝ}
    (hXm : Measurable X) (hX : MemLp X 2 ν) {N : ℕ} (hN : 0 < N) :
    μ[fun x => (∑ n ∈ range N, X (ω n x) ^ 2) / N - ((∑ n ∈ range N, X (ω n x)) / N) ^ 2] =
      (1 - (N : ℝ)⁻¹) * variance X ν := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω 0).map_eq]
    exact Measure.isProbabilityMeasure_map (hω 0).measurable.aemeasurable
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨hmean, hvar, -, -⟩ := mc_estimate ω hω hind hXm hX hN
  have hXn : ∀ n, MemLp (fun x => X (ω n x)) 2 μ := fun n => hX.comp_measurePreserving (hω n)
  have hY : MemLp (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, X (ω n x)) 2 μ :=
    (memLp_finsetSum (range N) fun n _ => hXn n).const_mul _
  have hsq : ∀ n, Integrable (fun x => X (ω n x) ^ 2) μ := fun n => (hXn n).integrable_sq
  have hY2 := variance_eq_sub hY
  have hX2 := variance_eq_sub hX
  simp only [Pi.pow_apply] at hY2 hX2
  rw [hvar, hmean] at hY2
  have hs2 : ∫ x, ∑ n ∈ range N, X (ω n x) ^ 2 ∂μ = N * ∫ y, X y ^ 2 ∂ν := by
    rw [integral_finsetSum _ fun n _ => hsq n]
    have h1 : ∀ n ∈ range N, ∫ x, X (ω n x) ^ 2 ∂μ = ∫ y, X y ^ 2 ∂ν := fun n _ =>
      integral_comp_of_measurePreserving (hω n) (hXm.pow_const 2).aestronglyMeasurable
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e : ∀ x, (∑ n ∈ range N, X (ω n x) ^ 2) / N - ((∑ n ∈ range N, X (ω n x)) / N) ^ 2 =
      (N : ℝ)⁻¹ * ∑ n ∈ range N, X (ω n x) ^ 2 - ((N : ℝ)⁻¹ * ∑ n ∈ range N, X (ω n x)) ^ 2 :=
    fun x => by ring
  simp_rw [e]
  rw [integral_sub ((integrable_finsetSum _ fun n _ => hsq n).const_mul _) hY.integrable_sq,
    integral_const_mul, hs2]
  linear_combination hY2 - hX2 + (∫ y, X y ^ 2 ∂ν) * inv_mul_cancel₀ hN'

end PowerSumMean

/-! ### §3.4: the floors of the estimates -/

/-- **The floored estimates of the driver** (Giles 2015, §3.4, pp. 24–25: "If the mean and variance
are decaying as expected, one would expect `m_ℓ = 2^{−α} m_{ℓ−1}`, `V_ℓ = 2^{−β} V_{ℓ−1}`. … the
estimates for `m_ℓ` and `V_ℓ` are not allowed to decrease by more than factor ½ relative to this
anticipated value"; the code sets `ml(l) = max(ml(l), 0.5*ml(l-1)/2^alpha)` and
`Vl(l) = max(Vl(l), 0.5*Vl(l-1)/2^beta)` for `l = 3:L+1`, i.e. for the levels `ℓ ≥ 2`).  With
`r = ½ 2^{−α}` (resp. `½ 2^{−β}`), the estimate on each level `ℓ ≥ 2` is raised to `r` times the
floored estimate on the level below; levels `0` and `1` are unchanged. -/
noncomputable def floorEst (x : ℕ → ℝ) (r : ℝ) : ℕ → ℝ
  | 0 => x 0
  | 1 => x 1
  | ℓ + 2 => max (x (ℓ + 2)) (r * floorEst x r (ℓ + 1))

/-- The floors never lower an estimate (Giles 2015, §3.4, p. 25). -/
theorem le_floorEst (x : ℕ → ℝ) (r : ℝ) : ∀ ℓ, x ℓ ≤ floorEst x r ℓ
  | 0 => le_refl _
  | 1 => le_refl _
  | _ + 2 => le_max_left _ _

/-- **At least half of the anticipated value** (Giles 2015, §3.4, p. 25): with `r = ½ 2^{−α}`, the
floored estimate on level `ℓ + 2` is at least half of the value `2^{−α} m̂_{ℓ+1}` anticipated from
the level below. -/
theorem floorEst_ge_extrapolation (x : ℕ → ℝ) (r : ℝ) (ℓ : ℕ) :
    r * floorEst x r (ℓ + 1) ≤ floorEst x r (ℓ + 2) :=
  le_max_right _ _

/-- The floored estimates are the smallest ones with these two properties (Giles 2015, §3.4): any
`y ≥ x` with `r y_{ℓ+1} ≤ y_{ℓ+2}` for all `ℓ` (and `r ≥ 0`) lies above `floorEst x r`. -/
theorem floorEst_le {x y : ℕ → ℝ} {r : ℝ} (hr : 0 ≤ r) (hxy : ∀ ℓ, x ℓ ≤ y ℓ)
    (hy : ∀ ℓ, r * y (ℓ + 1) ≤ y (ℓ + 2)) : ∀ ℓ, floorEst x r ℓ ≤ y ℓ
  | 0 => hxy 0
  | 1 => hxy 1
  | ℓ + 2 => max_le (hxy (ℓ + 2))
      ((mul_le_mul_of_nonneg_left (floorEst_le hr hxy hy (ℓ + 1)) hr).trans (hy ℓ))

/-! ### §3.4: the rates by linear regression -/

/-- The least-squares slope of the points `(t_i, y_i)`, `i ∈ s` (Giles 2015, §3.4: `α` and `β` are
"estimated by linear regression"): `∑ (t_i − t̄)(y_i − ȳ) / ∑ (t_i − t̄)²` with `t̄, ȳ` the
means. -/
noncomputable def lsSlope {ι : Type*} (s : Finset ι) (t y : ι → ℝ) : ℝ :=
  (∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) * (y i - (∑ j ∈ s, y j) / s.card)) /
    ∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) ^ 2

/-- The least-squares intercept `ȳ − slope · t̄` (Giles 2015, §3.4). -/
noncomputable def lsIntercept {ι : Type*} (s : Finset ι) (t y : ι → ℝ) : ℝ :=
  (∑ j ∈ s, y j) / s.card - lsSlope s t y * ((∑ j ∈ s, t j) / s.card)

/-- The points are not all on one vertical line: `∑ (t_i − t̄)² ≠ 0` as soon as two abscissae
differ (Giles 2015, §3.4: the regression uses the levels `1, …, L`). -/
lemma lsSxx_ne_zero {ι : Type*} {s : Finset ι} {t : ι → ℝ} {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hij : t i ≠ t j) : ∑ k ∈ s, (t k - (∑ l ∈ s, t l) / s.card) ^ 2 ≠ 0 := by
  intro h
  rw [Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _] at h
  have h1 := h i hi
  have h2 := h j hj
  rw [sq_eq_zero_iff, sub_eq_zero] at h1 h2
  exact hij (h1.trans h2.symm)

/-- **Linear regression is least squares** (Giles 2015, §3.4: "estimated by linear regression").
The line `y = lsSlope · t + lsIntercept` minimises the sum of squared residuals
`∑ (y_i − (a t_i + b))²` over all lines. -/
theorem lsFit_le {ι : Type*} (s : Finset ι) (t y : ι → ℝ)
    (hS : ∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) ^ 2 ≠ 0) (a b : ℝ) :
    ∑ i ∈ s, (y i - (lsSlope s t y * t i + lsIntercept s t y)) ^ 2 ≤
      ∑ i ∈ s, (y i - (a * t i + b)) ^ 2 := by
  obtain ⟨T, hT⟩ : ∃ T, T = (∑ j ∈ s, t j) / s.card := ⟨_, rfl⟩
  obtain ⟨Yb, hYb⟩ : ∃ Yb, Yb = (∑ j ∈ s, y j) / s.card := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = lsSlope s t y := ⟨_, rfl⟩
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hS (by simp)
  have hn : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hs)
  have hS' : ∑ i ∈ s, (t i - T) ^ 2 ≠ 0 := by rwa [← hT] at hS
  have hsumT : ∑ i ∈ s, (t i - T) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hT, mul_div_cancel₀ _ hn,
      sub_self]
  have hsumY : ∑ i ∈ s, (y i - Yb) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hYb, mul_div_cancel₀ _ hn,
      sub_self]
  have hA' : A * ∑ i ∈ s, (t i - T) ^ 2 = ∑ i ∈ s, (t i - T) * (y i - Yb) := by
    rw [hA, lsSlope, ← hT, ← hYb, div_mul_cancel₀ _ hS']
  have hB : lsIntercept s t y = Yb - A * T := by rw [lsIntercept, ← hT, ← hYb, ← hA]
  -- the normal equations
  have hu : ∑ i ∈ s, ((t i - T) * (y i - Yb) - A * (t i - T) ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hA', sub_self]
  have hv : ∑ i ∈ s, ((y i - Yb) - A * (t i - T)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumY, hsumT, mul_zero, sub_zero]
  have hsplit : ∑ i ∈ s, (y i - (a * t i + b)) ^ 2 =
      ∑ i ∈ s, (y i - (A * t i + (Yb - A * T))) ^ 2 +
        2 * (A - a) * ∑ i ∈ s, ((t i - T) * (y i - Yb) - A * (t i - T) ^ 2) +
        2 * ((A - a) * T + (Yb - A * T) - b) * ∑ i ∈ s, ((y i - Yb) - A * (t i - T)) +
        ∑ i ∈ s, ((A - a) * (t i - T) + ((A - a) * T + (Yb - A * T) - b)) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hd : 0 ≤ ∑ i ∈ s, ((A - a) * (t i - T) + ((A - a) * T + (Yb - A * T) - b)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← hA, hB, hsplit, hu, hv]
  linarith

/-- **Regression recovers the slope of affine data** (Giles 2015, §3.4): if `y_i = c + a t_i` on
`s` and the `t_i` are not all equal, the least-squares slope is `a`. -/
theorem lsSlope_affine {ι : Type*} (s : Finset ι) (t : ι → ℝ) (c a : ℝ)
    (hS : ∑ i ∈ s, (t i - (∑ j ∈ s, t j) / s.card) ^ 2 ≠ 0) :
    lsSlope s t (fun i => c + a * t i) = a := by
  obtain ⟨T, hT⟩ : ∃ T, T = (∑ j ∈ s, t j) / s.card := ⟨_, rfl⟩
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hS (by simp)
  have hn : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hs)
  have hS' : ∑ i ∈ s, (t i - T) ^ 2 ≠ 0 := by rwa [← hT] at hS
  have hY : (∑ j ∈ s, (c + a * t j)) / s.card = c + a * T := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, add_div,
      mul_div_cancel_left₀ c hn, mul_div_assoc, hT]
  have hnum : ∑ i ∈ s, (t i - T) * (c + a * t i - (c + a * T)) =
      a * ∑ i ∈ s, (t i - T) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [lsSlope]
  rw [← hT, hY, hnum, mul_div_assoc, div_self hS', mul_one]

/-- **The rate `α` by regression** (Giles 2015, §3.4, p. 25: `α` and `β` "are now estimated by
linear regression"; `x = [(1:L)' ones(L,1)] \ log2(ml(2:end))'; alpha = max(0.5,-x(1));`, a
least-squares fit of `log₂ m_ℓ` against `ℓ = 1, …, L` with an intercept).  If the corrections are
exactly geometric, `|E[P_ℓ − P_{ℓ−1}]| = c 2^{−αℓ}` with `c > 0`, on levels that are not all equal,
the least-squares slope of `log₂` of the means is `−α`, so the driver's estimate is `max(½, α)`. -/
theorem lsSlope_log_geometric (s : Finset ℕ) {i j : ℕ} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    {c α : ℝ} (hc : 0 < c) :
    lsSlope s (fun ℓ => (ℓ : ℝ)) (fun ℓ => Real.logb 2 (c * (2 : ℝ) ^ (-(α * ℓ)))) = -α := by
  have e : (fun ℓ : ℕ => Real.logb 2 (c * (2 : ℝ) ^ (-(α * ℓ)))) =
      fun ℓ : ℕ => Real.logb 2 c + (-α) * (ℓ : ℝ) := by
    funext ℓ
    rw [Real.logb_mul hc.ne' (by positivity), Real.logb_rpow (by norm_num) (by norm_num)]
    ring
  rw [e]
  exact lsSlope_affine s _ _ _ (lsSxx_ne_zero hi hj (by exact_mod_cast hij))

/-! ### §3.3: the probability that the consistency check fails -/

/-- **The three-sigma bound for a standard normal variable** (Giles 2015, §3.3, p. 22: the
probability of the consistency ratio exceeding unity "is less than 0.3%"): if `Z ~ N(0, 1)` then
`P(|Z| > 3) < 0.003` (the exact value is `2(1 − Φ(3)) ≈ 0.0027`).  The proof uses the Mills-ratio
bound `∫_3^∞ φ(x) dx ≤ ∫_3^∞ (x/3) φ(x) dx = φ(3)/3` and the symmetry of `φ`. -/
theorem gaussian_tail_three : (gaussianReal 0 1).real {x : ℝ | 3 < |x|} < 0.003 := by
  -- the density `φ(x) = (2π)^{−1/2} e^{−x²/2}` of `N(0, 1)`
  have hφ : ∀ x, gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hφi : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have hP : ∀ s : Set ℝ, (gaussianReal 0 1).real s = ∫ x in s, gaussianPDFReal 0 1 x := by
    intro s
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero s,
      ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x)]
  -- `∫_3^∞ x e^{−x²/2} dx = e^{−9/2}`
  have hderiv : ∀ x ∈ Set.Ici (3 : ℝ), HasDerivAt (fun x : ℝ => -Real.exp (-x ^ 2 / 2))
      (x * Real.exp (-x ^ 2 / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    exact ((h1.neg.div_const 2).exp.neg).congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-x ^ 2 / 2)) (Set.Ioi 3) := by
    have h := integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    have e : (fun x : ℝ => x * Real.exp (-(1 / 2) * x ^ 2)) =
        fun x => x * Real.exp (-x ^ 2 / 2) := by
      funext x
      rw [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
    rw [e] at h
    exact h.integrableOn
  have hlim : Tendsto (fun x : ℝ => -Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    have h2 : Tendsto (fun x : ℝ => Real.exp (-(x ^ 2 / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := h2.neg
    rw [neg_zero] at h3
    exact h3.congr fun x => by rw [neg_div]
  have hI : ∫ x in Set.Ioi (3 : ℝ), x * Real.exp (-x ^ 2 / 2) =
      0 - -Real.exp (-(3 : ℝ) ^ 2 / 2) :=
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  -- the right tail
  have hright : ∫ x in Set.Ioi (3 : ℝ), gaussianPDFReal 0 1 x ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(3 : ℝ) ^ 2 / 2) / 3 := by
    calc ∫ x in Set.Ioi (3 : ℝ), gaussianPDFReal 0 1 x
        ≤ ∫ x in Set.Ioi (3 : ℝ),
            (Real.sqrt (2 * Real.pi))⁻¹ / 3 * (x * Real.exp (-x ^ 2 / 2)) := by
          refine setIntegral_mono_on hφi.integrableOn (Integrable.const_mul hint _)
            measurableSet_Ioi fun x hx => ?_
          have hx3 : (3 : ℝ) < x := hx
          have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by positivity
          rw [hφ]
          nlinarith [mul_nonneg hc (sub_nonneg.2 hx3.le)]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ / 3 * ∫ x in Set.Ioi (3 : ℝ), x * Real.exp (-x ^ 2 / 2) :=
          integral_const_mul _ _
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(3 : ℝ) ^ 2 / 2) / 3 := by
          rw [hI]
          ring
  -- the left tail, by symmetry
  have hleft : ∫ x in Set.Iic (-3 : ℝ), gaussianPDFReal 0 1 x =
      ∫ x in Set.Ioi (3 : ℝ), gaussianPDFReal 0 1 x := by
    have e : (fun x => gaussianPDFReal 0 1 (-x)) = gaussianPDFReal 0 1 := funext fun x => by
      rw [hφ, hφ, neg_sq]
    rw [← integral_comp_neg_Ioi, e]
  have hsub : {x : ℝ | 3 < |x|} ⊆ Set.Iic (-3) ∪ Set.Ioi 3 := by
    intro x hx
    have hx' : (3 : ℝ) < |x| := hx
    rcases lt_abs.1 hx' with h | h
    · exact Or.inr h
    · exact Or.inl (show x ≤ -3 by linarith)
  -- the numerical bound `2 e^{−9/2}/(3 √(2π)) < 0.003`
  have hsqrt : (2.505 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith [Real.pi_gt_d2]
  have hexp : (90 : ℝ) ≤ Real.exp (9 / 2) := by
    have h9 : Real.exp (9 / 2) ^ 2 = Real.exp 1 ^ 9 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    have h3 : (90 : ℝ) ^ 2 ≤ Real.exp 1 ^ 9 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 9)
    rw [← h9] at h3
    exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le two_ne_zero).1 h3
  have e1 : Real.exp (-(3 : ℝ) ^ 2 / 2) = (Real.exp (9 / 2))⁻¹ := by
    rw [show -(3 : ℝ) ^ 2 / 2 = -(9 / 2) by norm_num, Real.exp_neg]
  have hi1 : (Real.sqrt (2 * Real.pi))⁻¹ ≤ (2.505 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hsqrt
  have hi2 : (Real.exp (9 / 2))⁻¹ ≤ (90 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hexp
  calc (gaussianReal 0 1).real {x : ℝ | 3 < |x|}
      ≤ (gaussianReal 0 1).real (Set.Iic (-3) ∪ Set.Ioi 3) := measureReal_mono hsub
    _ ≤ (gaussianReal 0 1).real (Set.Iic (-3)) + (gaussianReal 0 1).real (Set.Ioi 3) :=
        measureReal_union_le _ _
    _ = 2 * ∫ x in Set.Ioi (3 : ℝ), gaussianPDFReal 0 1 x := by
        rw [hP, hP, hleft]
        ring
    _ ≤ 2 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(3 : ℝ) ^ 2 / 2) / 3) :=
        mul_le_mul_of_nonneg_left hright (by norm_num)
    _ = 2 * ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (9 / 2))⁻¹ / 3) := by rw [e1]
    _ ≤ 2 * ((2.505 : ℝ)⁻¹ * (90 : ℝ)⁻¹ / 3) := by gcongr
    _ < 0.003 := by norm_num

section Consistency

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The consistency check under a normal model** (Giles 2015, §3.3, p. 22: for estimates `a, b, c`
of `E[P^f_{ℓ−1}]`, `E[P^f_ℓ]`, `E[Y_ℓ]`, "The probability of this ratio being greater than unity is
less than 0.3%", the ratio being `|a − b + c|/(3(√V_a + √V_b + √V_c))`).  If `a − b + c` is
normally distributed with mean zero (its mean is zero under (2.4), `consistency_mean`; normality
is the paper's implicit assumption), then
`P(|a − b + c| > 3(√V_a + √V_b + √V_c)) < 0.003`, because
`√V[a − b + c] ≤ √V_a + √V_b + √V_c` (`consistency_sd`) and `gaussian_tail_three`.  Here
`V_a, V_b, V_c` are the true variances; with the paper's empirical estimates the bound holds
asymptotically (`consistency_check_empirical` in `MlmcLean/ConsistencyCheck.lean`). -/
theorem consistency_check_gaussian {a b c : Ω → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hc : MemLp c 2 μ) {v : ℝ≥0} (hv : v ≠ 0)
    (hlaw : HasLaw (fun ω => a ω - b ω + c ω) (gaussianReal 0 v) μ) :
    μ.real {ω | 3 * (Real.sqrt (variance a μ) + Real.sqrt (variance b μ) +
      Real.sqrt (variance c μ)) < |a ω - b ω + c ω|} < 0.003 := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (variance a μ) + Real.sqrt (variance b μ) +
      Real.sqrt (variance c μ) := ⟨_, rfl⟩
  rw [← hs]
  have hsd := consistency_sd ha hb hc
  rw [← hs, hlaw.variance_eq, variance_id_gaussianReal] at hsd
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.coe_nonneg (NNReal.coe_ne_zero.2 hv).symm
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  -- the standardised variable has law `N(0, 1)`
  have hZ : HasLaw (fun ω => (a ω - b ω + c ω) / Real.sqrt v) (gaussianReal 0 1) μ := by
    have h := gaussianReal_div_const hlaw (Real.sqrt v)
    convert h using 2
    · simp
    · apply NNReal.eq
      simp only [NNReal.coe_one, NNReal.coe_div, NNReal.coe_mk]
      rw [Real.sq_sqrt v.coe_nonneg, div_self hv0.ne']
  have hmeas : MeasurableSet {z : ℝ | 3 < |z|} :=
    measurableSet_lt measurable_const measurable_abs
  calc μ.real {ω | 3 * s < |a ω - b ω + c ω|}
      ≤ μ.real {ω | 3 < |(a ω - b ω + c ω) / Real.sqrt v|} := by
        refine measureReal_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [abs_div, abs_of_pos hsv, lt_div_iff₀ hsv]
        nlinarith
    _ = (gaussianReal 0 1).real {z : ℝ | 3 < |z|} := hZ.measureReal_eq hmeas
    _ < 0.003 := gaussian_tail_three

/-- **The consistency check, without normality** (Giles 2015, §3.3, p. 22).  If `E[a − b + c] = 0`
(which holds under (2.4), `consistency_mean`), Chebyshev's inequality bounds the probability that
the ratio `|a − b + c|/(3(√V_a + √V_b + √V_c))` reaches unity by `1/9`, whatever the distribution;
the paper's `0.3%` needs normality (`consistency_check_gaussian`). -/
theorem consistency_check_chebyshev {a b c : Ω → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hc : MemLp c 2 μ) (hmean : ∫ ω, a ω - b ω + c ω ∂μ = 0)
    (hpos : 0 < Real.sqrt (variance a μ) + Real.sqrt (variance b μ) + Real.sqrt (variance c μ)) :
    μ.real {ω | 3 * (Real.sqrt (variance a μ) + Real.sqrt (variance b μ) +
      Real.sqrt (variance c μ)) ≤ |a ω - b ω + c ω|} ≤ 1 / 9 := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (variance a μ) + Real.sqrt (variance b μ) +
      Real.sqrt (variance c μ) := ⟨_, rfl⟩
  rw [← hs] at hpos ⊢
  have hY : MemLp (fun ω => a ω - b ω + c ω) 2 μ := (ha.sub hb).add hc
  have hsd := consistency_sd ha hb hc
  rw [← hs] at hsd
  have h0 := variance_nonneg (fun ω => a ω - b ω + c ω) μ
  have hV : variance (fun ω => a ω - b ω + c ω) μ ≤ s ^ 2 := by
    calc variance (fun ω => a ω - b ω + c ω) μ
        = Real.sqrt (variance (fun ω => a ω - b ω + c ω) μ) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ s ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsd 2
  have h3 : (0 : ℝ) < 3 * s := by positivity
  have hcheb := meas_ge_le_variance_div_sq hY h3
  rw [hmean] at hcheb
  simp only [sub_zero] at hcheb
  have hle : variance (fun ω => a ω - b ω + c ω) μ / (3 * s) ^ 2 ≤ 1 / 9 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc μ.real {ω | 3 * s ≤ |a ω - b ω + c ω|}
      ≤ variance (fun ω => a ω - b ω + c ω) μ / (3 * s) ^ 2 :=
        ENNReal.toReal_le_of_le_ofReal (div_nonneg h0 (sq_nonneg _)) hcheb
    _ ≤ 1 / 9 := hle

end Consistency

/-! ### §3.3: the kurtosis and rare non-zero corrections -/

/-- **`O(κ)` samples** (Giles 2015, §3.3, p. 23: "Hence `O(κ)` samples are required to obtain a
reasonable estimate for the variance").  The standard deviation of the sample variance is
`√((κ − 1)/N) E[X²]` (`sampleVariance_sd`), so its relative standard deviation is at most `r > 0`
exactly when `N ≥ (κ − 1)/r²`. -/
theorem sampleVariance_relative_sd_le_iff {κ r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 0 < N) :
    Real.sqrt ((κ - 1) / N) ≤ r ↔ (κ - 1) / r ^ 2 ≤ N := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [Real.sqrt_le_left hr.le, div_le_iff₀ hN', div_le_iff₀ (by positivity : (0 : ℝ) < r ^ 2),
    mul_comm (r ^ 2) (N : ℝ)]

section Ternary

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The mean of a ternary correction** (Giles 2015, §3.3, p. 23: "`X ≡ P_ℓ − P_{ℓ−1}` = `1`,
probability `p`; `−1`, probability `q`; `0`, probability `1 − p − q`.  If `p, q ≪ 1`, then
`E[X] ≈ 0`"): exactly, `E[X] = p − q`. -/
theorem integral_ternary {X : Ω → ℝ} (hXm : Measurable X) (hX : ∀ ω, X ω = -1 ∨ X ω = 0 ∨ X ω = 1) :
    ∫ ω, X ω ∂μ = μ.real {ω | X ω = 1} - μ.real {ω | X ω = -1} := by
  have h1 : MeasurableSet {ω | X ω = 1} := hXm (measurableSet_singleton 1)
  have h2 : MeasurableSet {ω | X ω = -1} := hXm (measurableSet_singleton (-1))
  have e : ∀ ω, X ω = Set.indicator {ω | X ω = 1} (fun _ => (1 : ℝ)) ω -
      Set.indicator {ω | X ω = -1} (fun _ => (1 : ℝ)) ω := by
    intro ω
    rcases hX ω with h | h | h <;> norm_num [Set.indicator, h]
  rw [integral_congr_ae (Filter.Eventually.of_forall e),
    integral_sub ((integrable_const (1 : ℝ)).indicator h1)
      ((integrable_const (1 : ℝ)).indicator h2),
    integral_indicator_const _ h1, integral_indicator_const _ h2, smul_eq_mul, smul_eq_mul, mul_one,
    mul_one]

/-- The probability that a ternary correction vanishes is `1 − p − q` (Giles 2015, §3.3, p. 23). -/
theorem measureReal_ternary_zero {X : Ω → ℝ} (hXm : Measurable X)
    (hX : ∀ ω, X ω = -1 ∨ X ω = 0 ∨ X ω = 1) :
    μ.real {ω | X ω = 0} = 1 - μ.real {ω | X ω = 1} - μ.real {ω | X ω = -1} := by
  have h1 : MeasurableSet {ω | X ω = 1} := hXm (measurableSet_singleton 1)
  have h2 : MeasurableSet {ω | X ω = -1} := hXm (measurableSet_singleton (-1))
  have hd : Disjoint {ω | X ω = 1} {ω | X ω = -1} := by
    rw [Set.disjoint_left]
    intro ω h h'
    simp only [Set.mem_ofPred_eq] at h h'
    rw [h] at h'
    norm_num at h'
  have hc : {ω | X ω = 0} = ({ω | X ω = 1} ∪ {ω | X ω = -1})ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union]
    rcases hX ω with h | h | h <;> rw [h] <;> norm_num
  rw [hc, measureReal_compl (h1.union h2), measureReal_union hd h2, probReal_univ]
  ring

end Ternary

section AllZero

variable {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {μ : Measure Ω} {ν : Measure Ω₀}

/-- **All samples may vanish** (Giles 2015, §3.3, p. 23: "many samples are required for a good
estimate of `V_ℓ`; otherwise, we may get all `X^{(n)} = 0`, which will give an estimated variance
of zero"): for `N`
independent samples `X(ω⁽ⁿ⁾)` with law `ν`, the probability that all of them are zero is
`P(X = 0)^N`; for a ternary `X` this is `(1 − p − q)^N` (`measureReal_ternary_zero`). -/
theorem prob_all_zero (ω : ℕ → Ω → Ω₀) (hω : ∀ n, MeasurePreserving (ω n) μ ν)
    (hind : iIndepFun ω μ) {X : Ω₀ → ℝ} (hXm : Measurable X) (N : ℕ) :
    μ.real {x | ∀ n ∈ range N, X (ω n x) = 0} = ν.real {y | X y = 0} ^ N := by
  have hA : MeasurableSet {y | X y = 0} := hXm (measurableSet_singleton 0)
  have hset : {x | ∀ n ∈ range N, X (ω n x) = 0} = ⋂ n ∈ range N, ω n ⁻¹' {y | X y = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  have hmeas : μ (⋂ n ∈ range N, ω n ⁻¹' {y | X y = 0}) =
      ∏ n ∈ range N, μ (ω n ⁻¹' {y | X y = 0}) :=
    hind.meas_biInter fun n _ => MeasurableSpace.measurableSet_comap.2 ⟨_, hA, rfl⟩
  have hpre : ∀ n ∈ range N, μ (ω n ⁻¹' {y | X y = 0}) = ν {y | X y = 0} := fun n _ =>
    (hω n).measure_preimage hA.nullMeasurableSet
  rw [measureReal_def, hset, hmeas, Finset.prod_congr rfl hpre, Finset.prod_const,
    Finset.card_range, ENNReal.toReal_pow, ← measureReal_def]

/-- "… which will give an estimated variance of zero" (Giles 2015, §3.3, p. 23): if all `N ≥ 1`
samples vanish, the variance estimate `s₂/N − (s₁/N)²` of the driver is zero. -/
theorem powerSum_variance_of_zero {x : ℕ → ℝ} {N : ℕ} (h : ∀ n ∈ range N, x n = 0) :
    (∑ n ∈ range N, x n ^ 2) / N - ((∑ n ∈ range N, x n) / N) ^ 2 = 0 := by
  have h1 : ∑ n ∈ range N, x n ^ 2 = 0 := Finset.sum_eq_zero fun n hn => by simp [h n hn]
  have h2 : ∑ n ∈ range N, x n = 0 := Finset.sum_eq_zero h
  simp [h1, h2]

end AllZero

/-! ### §3.5: MLQMC -/

/-- **The level on which to double the samples in MLQMC** (Giles 2015, §3.5, p. 27, (3.3): "Doubling
`N_ℓ` will usually eliminate a large fraction of the variance, so the greatest reduction in total
variance relative to the additional computational effort is achieved by doubling `N_ℓ` on the
level `ℓ*` given by `ℓ* = argmax_ℓ V_ℓ/(N_ℓ C_ℓ)`").  If doubling `N_ℓ` removes the same
fraction `f > 0` of `V_ℓ` on every level, at the additional cost `N_ℓ C_ℓ`, the reduction per unit
cost `f V_ℓ/(N_ℓ C_ℓ)` is largest exactly on the levels that maximise `V_ℓ/(N_ℓ C_ℓ)`, and such a
level exists. -/
theorem mlqmc_doubling_level {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (V N C : ι → ℝ) {f : ℝ}
    (hf : 0 < f) :
    (∃ ℓ ∈ s, ∀ k ∈ s, V k / (N k * C k) ≤ V ℓ / (N ℓ * C ℓ)) ∧
      ∀ ℓ ∈ s, ((∀ k ∈ s, f * V k / (N k * C k) ≤ f * V ℓ / (N ℓ * C ℓ)) ↔
        ∀ k ∈ s, V k / (N k * C k) ≤ V ℓ / (N ℓ * C ℓ)) := by
  refine ⟨s.exists_max_image (fun k => V k / (N k * C k)) hs, fun ℓ _ => ?_⟩
  simp only [mul_div_assoc, mul_le_mul_iff_right₀ hf]

end MLMC
