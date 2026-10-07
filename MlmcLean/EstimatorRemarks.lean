import MlmcLean.ConsistencyCheck
import MlmcLean.NestedSimulation
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Remarks on estimators: a counterexample to "therefore so is `Y`", the consistency check with one
or two samples, and the variance of the sample variance

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1 (p. 8,
l. 346–351 of `docs/giles2015.txt`) and §3.3 (pp. 22–23, l. 1012–1045).  Three claims that the
other modules state only in docstrings (`notes/coverage/round17_spot_check.md`, "Docstring-only
claims").

**1. With a growing number of levels, "therefore so is `Y`" needs a hypothesis** (§2.1, p. 8,
l. 346–351: "Collier, Haji-Ali, Nobile, von Schwerin and Tempone (2014) … prefer to use the
Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence. This exploits the fact that the multilevel correction `Y_ℓ` on each
level is asymptotically Normally-distributed, and therefore so is `Y`.").  The counterexample of
the docstring of `MlmcLean/MLMCCentralLimit.lean`: the input `u` is uniform on `[0, 1]`, the
corrections are `ΔP_ℓ = ±a_ℓ` with probability `p_ℓ/2` each and `0` otherwise, `p_ℓ = 2^{−ℓ}`,
`a_ℓ² p_ℓ = 1` (`cltCexDiff`, `cltCexP`), the finest level of row `k` is `L_k = k`, and
`N_{k,k} = k + 1`, `N_{k,ℓ} = (k + 1)³` for `ℓ < k` (`cltCexN`).
* `cltCex_moments`: `E[ΔP_ℓ] = 0`, `V_ℓ = 1`, `P(ΔP_ℓ ≠ 0) = 2^{−ℓ}`, `E[ΔP_ℓ⁴] = 2^ℓ` (the
  kurtosis is `2^ℓ`), `min_{ℓ ≤ k} N_{k,ℓ} → ∞`, and `σ_k² = k/(k + 1)³ + 1/(k + 1)`;
* `mlmc_clt_counterexample`: every level estimator is asymptotically normal as `k → ∞`, but the
  normalised estimator `(Y_k − E[P_{L_k}])/σ_k` tends to `0` in probability, hence not to
  `N(0, 1)`: the levels `ℓ < k` carry only `k/(k + (k + 1)²)` of `σ_k²`, and with probability
  `(1 − 2^{−k})^{k+1} → 1` all `k + 1` finest samples vanish;
* `mlmc_clt_counterexample_conditions`: the hypotheses that fail.  Lindeberg's condition fails in
  the strongest way: for every `ε > 0` the Lindeberg sum of the triangular array of normalised
  samples (the hypothesis of `tendstoInDistribution_lindeberg`) tends to `1`, not `0`; Lyapunov's
  ratio (the hypothesis of `tendstoInDistribution_mlmcEstimator_lyapunov`) does not tend to `0`
  for any `δ ≥ 0`; and the standardised moments `E|ΔP_ℓ − E ΔP_ℓ|^{2+δ}/V_ℓ^{1+δ/2}` are
  unbounded for every `δ > 0` (the hypothesis of
  `tendstoInDistribution_mlmcEstimator_of_moment_le`);
* `exists_mlmc_clt_counterexample`: such a setting exists (independent uniform inputs on the
  infinite product space).

**2. The consistency check with one or two samples per level** (§3.3, p. 22, l. 1012–1031: "If
`a, b, c` are estimates for `E[P^f_{ℓ−1}], E[P^f_ℓ], E[Y_ℓ]`, respectively, then it should be
true that `a − b + c ≈ 0`. … it computes and plots the ratio `|a − b + c| / (3(√V_a + √V_b +
√V_c))` where `V_a, V_b, V_c` are empirical estimates for the variances of `a, b, c`. The
probability of this ratio being greater than unity is less than 0.3%.").  The setting and the
notation are those of `MlmcLean/ConsistencyCheck.lean` (levels `ℓ, ℓ + 1` for the paper's
`ℓ − 1, ℓ`; `V = s²/N` with the empirical variance `s² = N⁻¹ ∑ (x_n − x̄)²`, `empVar`; the event
written without division).
* `consistency_check_one_sample`: with one sample per level every empirical variance is `0`, so
  the ratio is `0/0` or `+∞`: the check fails exactly when `a − b + c ≠ 0`, i.e. when the two
  samples `P^f_ℓ(ω^{(ℓ,0)})` and `P^c_ℓ(ω^{(ℓ+1,0)})` differ, and if the law of `P^c_ℓ` has no
  atoms it fails with probability `1`.  (The unbiased variance `S² = ∑ (x_n − x̄)²/(N − 1)` is
  undefined for `N = 1`.)
* `consistency_check_two_samples`: the Gaussian example of `ConsistencyCheck.lean`
  (`P^f_ℓ = P^f_{ℓ+1} = 0`, `P^c_ℓ = −Y`, `Y ∼ N(0, 1)`, so (2.4) holds) with two samples per
  level fails with probability exactly `(2/π) arctan(√2/3) ≈ 0.2804 > 1/4` with the empirical
  variances, and `(2/π) arctan(1/3) ≈ 0.2048 > 1/8` with the unbiased ones (`sampleVar`).  The
  ratio `(y₀ − y₁)/(y₀ + y₁)` of two independent standard normals is standard Cauchy:
  `P(|U − V| < t|U + V|) = (2/π) arctan t` (`gaussian_prod_cone`, by polar coordinates,
  `lintegral_comp_polarCoord_symm`).

**3. The standard deviation of the sample variance** (§3.3, pp. 22–23, l. 1038–1042: "When the
number of samples `N` is large, the standard deviation of the sample variance for a random
variable `X` with zero mean is approximately `√((κ − 1)/N) E[X²]` where the kurtosis `κ` is
defined as `κ = E[X⁴]/(E[X²])²`.").  `MlmcLean/ErrorAnalysis.lean` proves this exactly for the
sample variance with known mean (`sampleVariance_sd`).  For the usual unbiased sample variance
`S_N² = (N − 1)⁻¹ ∑_{n<N} (X_n − X̄_N)²` of `N ≥ 2` i.i.d. samples with `E[X⁴] < ∞`, `σ² = V[X]`,
`μ₄ = E[(X − E X)⁴]` and the central kurtosis `κ = μ₄/σ⁴`:
* `sampleVar_mean_variance`: `E[S_N²] = σ²` and `V[S_N²] = (μ₄ − (N − 3)/(N − 1) σ⁴)/N`;
* `sampleVar_sd`: `√V[S_N²] = √((κ − 1)/N + 2/(N(N − 1))) σ²`, so if `κ > 1`,
  `√((κ − 1)/N) σ² ≤ √V[S_N²] ≤ √((κ − 1)/N) σ² (1 + 1/((κ − 1)(N − 1)))`, the paper's
  approximation with relative error `O(1/N)`;
* `tendsto_sampleVar_sd_div`: `√V[S_N²]/(√((κ − 1)/N) σ²) → 1` as `N → ∞`.
The moments behind it: `E[T⁴] = Nμ₄ + 3N(N − 1)σ⁴`, `E[QT²] = E[Q²] = Nμ₄ + N(N − 1)σ⁴` for
`T = ∑ Y_n`, `Q = ∑ Y_n²` and centred i.i.d. `Y_n` (`moments_finsetSum_indep`,
`integral_sumSq_mul_sq`, `integral_sumSq_sq`).

**Deviations from the paper.**
* Item 1 refutes an inference, not a theorem: the paper states no hypotheses for "therefore so is
  `Y`" (it cites Collier et al.); the example shows that the asymptotic normality of every level
  estimator is not enough when the number of levels grows (for a fixed number of levels it is,
  `tendstoInDistribution_mlmcEstimator`).  It holds on every probability space carrying
  independent uniform inputs.
* Item 2 makes precise "less than 0.3%" for small samples, where it fails; the paper's claim is
  the asymptotic statement `consistency_check_empirical_lt`.
* Item 3 uses the central kurtosis `κ = E[(X − E X)⁴]/V[X]²` (the paper's `κ` for zero-mean
  `X`) and assumes `κ > 1`: for `κ = 1` (`X − E X = ±c`) the standard deviation is
  `√(2/(N(N − 1))) σ²`, not approximately `√((κ − 1)/N) σ² = 0`.  For the biased estimator
  `s_N² = (N − 1) S_N²/N` (`empVar`) the standard deviation is `(N − 1)/N` times as large, which
  changes only the `O(1/N)` term.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real

namespace MLMC

/-! ### §2.1: the counterexample to "and therefore so is `Y`" -/

/-- The correction `ΔP_ℓ` of the counterexample to Giles 2015, §2.1, p. 8 ("the multilevel
correction `Y_ℓ` on each level is asymptotically Normally-distributed, and therefore so is `Y`"),
as a function of an input `u` that is uniform on `[0, 1]`: `ΔP_ℓ(u) = 2^{ℓ/2}` for
`u < 2^{−ℓ}/2`, `−2^{ℓ/2}` for `2^{−ℓ}/2 ≤ u < 2^{−ℓ}`, and `0` otherwise.  So `ΔP_ℓ = ±a_ℓ`
with probability `p_ℓ/2` each, `p_ℓ = 2^{−ℓ}`, `a_ℓ = 2^{ℓ/2}`, `a_ℓ² p_ℓ = 1` (the example in
the docstring of `MlmcLean/MLMCCentralLimit.lean`). -/
noncomputable def cltCexDiff (ℓ : ℕ) (u : ℝ) : ℝ :=
  if u < ((2 : ℝ) ^ ℓ)⁻¹ / 2 then √((2 : ℝ) ^ ℓ)
  else if u < ((2 : ℝ) ^ ℓ)⁻¹ then -√((2 : ℝ) ^ ℓ) else 0

/-- The level outputs of the counterexample (Giles 2015, §2.1, p. 8): `P_ℓ = ∑_{j ≤ ℓ} ΔP_j`, so
that the correction `P_ℓ − P_{ℓ−1}` of the estimator (2.2) is `ΔP_ℓ` (`levelDiff_cltCexP`). -/
noncomputable def cltCexP (ℓ : ℕ) (u : ℝ) : ℝ := ∑ j ∈ range (ℓ + 1), cltCexDiff j u

/-- The sample sizes of the counterexample (Giles 2015, §2.1, p. 8): row `k` uses the levels
`ℓ ≤ L_k = k`, with `N_{k,k} = k + 1` samples on the finest level and `N_{k,ℓ} = (k + 1)³` on the
others. -/
def cltCexN (k ℓ : ℕ) : ℕ := if ℓ = k then k + 1 else (k + 1) ^ 3

/-- The correction of the counterexample is measurable. -/
lemma measurable_cltCexDiff (ℓ : ℕ) : Measurable (cltCexDiff ℓ) :=
  Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

/-- The correction of the counterexample is bounded by `a_ℓ = 2^{ℓ/2}`. -/
lemma abs_cltCexDiff_le (ℓ : ℕ) (u : ℝ) : |cltCexDiff ℓ u| ≤ √((2 : ℝ) ^ ℓ) := by
  unfold cltCexDiff
  split_ifs <;> simp [abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The correction of the counterexample takes the values `0` and `±a_ℓ`. -/
lemma cltCexDiff_eq_zero_or (ℓ : ℕ) (u : ℝ) :
    cltCexDiff ℓ u = 0 ∨ |cltCexDiff ℓ u| = √((2 : ℝ) ^ ℓ) := by
  unfold cltCexDiff
  split_ifs <;> simp [abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The correction of the counterexample as a difference of two indicators,
`a_ℓ 1_{u < p_ℓ/2} − a_ℓ 1_{p_ℓ/2 ≤ u < p_ℓ}`. -/
lemma cltCexDiff_eq_indicator (ℓ : ℕ) (u : ℝ) :
    cltCexDiff ℓ u = (Set.Iio (((2 : ℝ) ^ ℓ)⁻¹ / 2)).indicator (fun _ => √((2 : ℝ) ^ ℓ)) u -
      (Set.Ico (((2 : ℝ) ^ ℓ)⁻¹ / 2) ((2 : ℝ) ^ ℓ)⁻¹).indicator (fun _ => √((2 : ℝ) ^ ℓ)) u := by
  unfold cltCexDiff
  split_ifs with h1 h2
  · rw [Set.indicator_of_mem (show u ∈ Set.Iio _ from h1),
      Set.indicator_of_notMem (show u ∉ Set.Ico _ _ from fun h => absurd h.1 (not_le.2 h1))]
    ring
  · rw [Set.indicator_of_notMem (show u ∉ Set.Iio _ from h1),
      Set.indicator_of_mem (show u ∈ Set.Ico _ _ from ⟨not_lt.1 h1, h2⟩)]
    ring
  · rw [Set.indicator_of_notMem (show u ∉ Set.Iio _ from h1),
      Set.indicator_of_notMem (show u ∉ Set.Ico _ _ from fun h => h2 h.2)]
    ring

/-- The square of the correction of the counterexample is `2^ℓ 1_{u < 2^{−ℓ}}`. -/
lemma cltCexDiff_sq (ℓ : ℕ) (u : ℝ) :
    cltCexDiff ℓ u ^ 2 = (Set.Iio ((2 : ℝ) ^ ℓ)⁻¹).indicator (fun _ => (2 : ℝ) ^ ℓ) u := by
  have hp : (0 : ℝ) < ((2 : ℝ) ^ ℓ)⁻¹ := by positivity
  have hs : √((2 : ℝ) ^ ℓ) ^ 2 = (2 : ℝ) ^ ℓ := Real.sq_sqrt (by positivity)
  unfold cltCexDiff
  split_ifs with h1 h2
  · rw [Set.indicator_of_mem (show u ∈ Set.Iio _ from by
      simp only [Set.mem_Iio]; linarith), hs]
  · rw [Set.indicator_of_mem (show u ∈ Set.Iio _ from h2), neg_sq, hs]
  · rw [Set.indicator_of_notMem (show u ∉ Set.Iio _ from h2)]
    ring

/-- The fourth power of the correction of the counterexample is `4^ℓ 1_{u < 2^{−ℓ}}`. -/
lemma cltCexDiff_pow_four (ℓ : ℕ) (u : ℝ) :
    cltCexDiff ℓ u ^ 4 = (Set.Iio ((2 : ℝ) ^ ℓ)⁻¹).indicator (fun _ => ((2 : ℝ) ^ ℓ) ^ 2) u := by
  rw [show cltCexDiff ℓ u ^ 4 = (cltCexDiff ℓ u ^ 2) ^ 2 by ring, cltCexDiff_sq]
  by_cases h : u < ((2 : ℝ) ^ ℓ)⁻¹
  · rw [Set.indicator_of_mem (show u ∈ Set.Iio _ from h),
      Set.indicator_of_mem (show u ∈ Set.Iio _ from h)]
  · rw [Set.indicator_of_notMem (show u ∉ Set.Iio _ from h),
      Set.indicator_of_notMem (show u ∉ Set.Iio _ from h)]
    ring

/-- The uniform law on `[0, 1]`, the law of the input of the counterexample, is a probability
measure. -/
lemma isProbabilityMeasure_restrict_Icc_zero_one :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- The uniform law on `[0, 1]` gives `(−∞, x)` the mass `x` for `0 ≤ x ≤ 1`. -/
lemma measureReal_unitIcc_Iio {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iio x) = x := by
  rw [measureReal_def, Measure.restrict_apply measurableSet_Iio]
  have e : Set.Iio x ∩ Set.Icc 0 1 = Set.Ico 0 x := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨h, h', _⟩
      exact ⟨h', h⟩
    · rintro ⟨h, h'⟩
      exact ⟨h', h, by linarith⟩
  rw [e, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal h0]

/-- The uniform law on `[0, 1]` gives `[a, b)` the mass `b − a` for `0 ≤ a ≤ b ≤ 1`. -/
lemma measureReal_unitIcc_Ico {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Ico a b) = b - a := by
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ico]
  have e : Set.Ico a b ∩ Set.Icc 0 1 = Set.Ico a b := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h, _⟩
      exact h
    · rintro ⟨h, h'⟩
      exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
  rw [e, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]

/-- The correction of the counterexample has mean `0` (Giles 2015, §2.1, p. 8). -/
lemma integral_cltCexDiff (ℓ : ℕ) :
    ∫ u, cltCexDiff ℓ u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
  have hp : (0 : ℝ) < ((2 : ℝ) ^ ℓ)⁻¹ := by positivity
  have hp1 : ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have := isProbabilityMeasure_restrict_Icc_zero_one
  simp_rw [cltCexDiff_eq_indicator]
  rw [integral_sub ((integrable_const _).indicator measurableSet_Iio)
      ((integrable_const _).indicator measurableSet_Ico),
    integral_indicator_const _ measurableSet_Iio, integral_indicator_const _ measurableSet_Ico,
    measureReal_unitIcc_Iio (by positivity) (by linarith),
    measureReal_unitIcc_Ico (by positivity) (by linarith) hp1]
  simp only [smul_eq_mul]
  ring

/-- The correction of the counterexample has second moment `a_ℓ² p_ℓ = 1` (Giles 2015, §2.1,
p. 8). -/
lemma integral_cltCexDiff_sq (ℓ : ℕ) :
    ∫ u, cltCexDiff ℓ u ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 1 := by
  have hp1 : ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  simp_rw [cltCexDiff_sq]
  rw [integral_indicator_const _ measurableSet_Iio, measureReal_unitIcc_Iio (by positivity) hp1,
    smul_eq_mul, inv_mul_cancel₀ (by positivity)]

/-- The correction of the counterexample has fourth moment `a_ℓ⁴ p_ℓ = 2^ℓ`, so its kurtosis is
`2^ℓ` (Giles 2015, §2.1, p. 8; §3.3, p. 23). -/
lemma integral_cltCexDiff_pow_four (ℓ : ℕ) :
    ∫ u, cltCexDiff ℓ u ^ 4 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 2 ^ ℓ := by
  have hp1 : ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  simp_rw [cltCexDiff_pow_four]
  rw [integral_indicator_const _ measurableSet_Iio, measureReal_unitIcc_Iio (by positivity) hp1,
    smul_eq_mul, sq, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- The correction of the counterexample has variance `1` (Giles 2015, §2.1, p. 8). -/
lemma variance_cltCexDiff (ℓ : ℕ) :
    variance (cltCexDiff ℓ) (volume.restrict (Set.Icc (0 : ℝ) 1)) = 1 := by
  rw [variance_of_integral_eq_zero (measurable_cltCexDiff ℓ).aemeasurable
    (integral_cltCexDiff ℓ), integral_cltCexDiff_sq]

/-- The correction of the counterexample is in every `L^p` (it is bounded). -/
lemma memLp_cltCexDiff (ℓ : ℕ) (p : ENNReal) :
    MemLp (cltCexDiff ℓ) p (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have := isProbabilityMeasure_restrict_Icc_zero_one
  exact MemLp.of_bound (measurable_cltCexDiff ℓ).aestronglyMeasurable _
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact abs_cltCexDiff_le ℓ u)

/-- The correction of the counterexample vanishes except with probability `p_ℓ = 2^{−ℓ}`
(Giles 2015, §2.1, p. 8). -/
lemma measureReal_cltCexDiff_ne_zero (ℓ : ℕ) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real {u | cltCexDiff ℓ u ≠ 0} = ((2 : ℝ) ^ ℓ)⁻¹ := by
  have hp1 : ((2 : ℝ) ^ ℓ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have e : {u | cltCexDiff ℓ u ≠ 0} = Set.Iio ((2 : ℝ) ^ ℓ)⁻¹ := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Iio]
    rw [← pow_ne_zero_iff two_ne_zero, cltCexDiff_sq]
    by_cases h : u < ((2 : ℝ) ^ ℓ)⁻¹
    · rw [Set.indicator_of_mem (show u ∈ Set.Iio _ from h)]
      exact ⟨fun _ => h, fun _ => by positivity⟩
    · rw [Set.indicator_of_notMem (show u ∉ Set.Iio _ from h)]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩
  rw [e, measureReal_unitIcc_Iio (by positivity) hp1]

/-- The corrections `P_ℓ − P_{ℓ−1}` of the level outputs of the counterexample are the
`ΔP_ℓ` of `cltCexDiff` (Giles 2015, (2.2)). -/
lemma levelDiff_cltCexP (ℓ : ℕ) : levelDiff cltCexP ℓ = cltCexDiff ℓ := by
  cases ℓ with
  | zero =>
    funext u
    simp [cltCexP]
  | succ ℓ =>
    funext u
    simp only [levelDiff_succ, cltCexP, Finset.sum_range_succ]
    ring

/-- The level outputs of the counterexample are measurable. -/
lemma measurable_cltCexP (k : ℕ) : Measurable (cltCexP k) :=
  Finset.measurable_sum _ fun j _ => measurable_cltCexDiff j

/-- The level outputs of the counterexample are in every `L^p`. -/
lemma memLp_cltCexP (k : ℕ) (p : ENNReal) :
    MemLp (cltCexP k) p (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have h := memLp_finsetSum (range (k + 1)) fun j _ => memLp_cltCexDiff j p
  convert h using 1
  funext u
  simp [cltCexP]

/-- The level outputs of the counterexample have mean `0`, so `E[P_{L_k}] = 0`. -/
lemma integral_cltCexP (k : ℕ) :
    ∫ u, cltCexP k u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
  unfold cltCexP
  rw [integral_finsetSum _ fun j _ => (memLp_cltCexDiff j 1).integrable le_rfl]
  simp [integral_cltCexDiff]

/-- The finest level of row `k` of the counterexample has `N_{k,k} = k + 1` samples. -/
lemma cltCexN_self (k : ℕ) : cltCexN k k = k + 1 := if_pos rfl

/-- The other levels of row `k` of the counterexample have `N_{k,ℓ} = (k + 1)³` samples. -/
lemma cltCexN_of_ne {k ℓ : ℕ} (h : ℓ ≠ k) : cltCexN k ℓ = (k + 1) ^ 3 := if_neg h

/-- Every level of row `k` of the counterexample has at least `k + 1` samples. -/
lemma le_cltCexN (k ℓ : ℕ) : k + 1 ≤ cltCexN k ℓ := by
  unfold cltCexN
  split_ifs
  · exact le_rfl
  · exact Nat.le_self_pow (by norm_num) _

/-- Every level of the counterexample has at least one sample. -/
lemma cltCexN_pos (k ℓ : ℕ) : 0 < cltCexN k ℓ := (Nat.succ_pos k).trans_le (le_cltCexN k ℓ)

/-- The variance of row `k` of the counterexample:
`σ_k² = ∑_{ℓ ≤ k} V_ℓ/N_{k,ℓ} = k/(k + 1)³ + 1/(k + 1)` (Giles 2015, (2.3)). -/
lemma sum_variance_div_cltCexN (k : ℕ) :
    ∑ ℓ ∈ range (k + 1), variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc (0 : ℝ) 1)) /
      (cltCexN k ℓ : ℝ) = k / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1) := by
  simp only [levelDiff_cltCexP, variance_cltCexDiff]
  rw [Finset.sum_range_succ, cltCexN_self,
    Finset.sum_congr rfl fun ℓ hℓ => by rw [cltCexN_of_ne (Finset.mem_range.1 hℓ).ne],
    Finset.sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **The counterexample: rare large corrections** (Giles 2015, §2.1, p. 8, l. 350–351: "This
exploits the fact that the multilevel correction `Y_ℓ` on each level is asymptotically
Normally-distributed, and therefore so is `Y`."; the example in the docstring of
`MlmcLean/MLMCCentralLimit.lean`). With the input `u` uniform on `[0, 1]`, the corrections
`ΔP_ℓ = P_ℓ − P_{ℓ−1}` of `cltCexP` satisfy `E[ΔP_ℓ] = 0`, `V_ℓ = 1`, `P(ΔP_ℓ ≠ 0) = 2^{−ℓ}` and
`E[ΔP_ℓ⁴] = 2^ℓ` (so the kurtosis `2^ℓ` is unbounded); the sample sizes `N_{k,ℓ}` of `cltCexN`
satisfy `min_{ℓ ≤ k} N_{k,ℓ} → ∞`; and the variance of the estimator of row `k` is
`σ_k² = ∑_{ℓ ≤ k} V_ℓ/N_{k,ℓ} = k/(k + 1)³ + 1/(k + 1)`, of which the finest level carries
`1/(k + 1)`. -/
theorem cltCex_moments :
    (∀ ℓ, ∫ y, levelDiff cltCexP ℓ y ∂(volume.restrict (Set.Icc 0 1)) = 0 ∧
      variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) = 1 ∧
      (volume.restrict (Set.Icc (0 : ℝ) 1)).real {y | levelDiff cltCexP ℓ y ≠ 0} =
        ((2 : ℝ) ^ ℓ)⁻¹ ∧
      ∫ y, levelDiff cltCexP ℓ y ^ 4 ∂(volume.restrict (Set.Icc 0 1)) = 2 ^ ℓ) ∧
    (∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ k, n₀ ≤ cltCexN k ℓ) ∧
    ∀ k : ℕ, ∑ ℓ ∈ range (k + 1),
        variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ =
      k / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1) := by
  refine ⟨fun ℓ => ?_, fun n₀ => ?_, sum_variance_div_cltCexN⟩
  · rw [levelDiff_cltCexP]
    exact ⟨integral_cltCexDiff ℓ, variance_cltCexDiff ℓ, measureReal_cltCexDiff_ne_zero ℓ,
      integral_cltCexDiff_pow_four ℓ⟩
  · filter_upwards [eventually_ge_atTop n₀] with k hk ℓ _
    exact hk.trans ((Nat.le_succ k).trans (le_cltCexN k ℓ))

section Cex

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ω : ℕ × ℕ → Ω → ℝ}

/-- The coarse levels `ℓ < k` of row `k` of the counterexample: their part
`A_k = ∑_{ℓ<k} Y_{k,ℓ}` of the estimator (2.2) is square integrable, centred, and has variance
`k/(k + 1)³` (Giles 2015, (2.3)). -/
lemma coarse_cltCex [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ (volume.restrict (Set.Icc 0 1)))
    (hind : iIndepFun ω μ) (k : ℕ) :
    MemLp (fun x => ∑ ℓ ∈ range k, levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x) 2 μ ∧
      μ[fun x => ∑ ℓ ∈ range k, levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x] = 0 ∧
      variance (fun x => ∑ ℓ ∈ range k, levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x) μ =
        k / ((k : ℝ) + 1) ^ 3 := by
  have hPl : ∀ ℓ, MemLp (cltCexP ℓ) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    fun ℓ => memLp_cltCexP ℓ 2
  have hfun : (fun x => ∑ ℓ ∈ range k, levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x) =
      ∑ ℓ ∈ range k, levelEstimator cltCexP ω ℓ (cltCexN k ℓ) := by
    funext x
    simp only [Finset.sum_apply]
  have hmem : ∀ ℓ ∈ range k, MemLp (levelEstimator cltCexP ω ℓ (cltCexN k ℓ)) 2 μ :=
    fun ℓ _ => memLp_levelEstimator hω hPl ℓ _
  refine ⟨memLp_finsetSum _ hmem, ?_, ?_⟩
  · rw [integral_finsetSum _ fun ℓ hℓ => (hmem ℓ hℓ).integrable one_le_two]
    refine Finset.sum_eq_zero fun ℓ _ => ?_
    rw [integral_levelEstimator hω (fun j => (hPl j).integrable one_le_two) ℓ
      (cltCexN_pos k ℓ), levelDiff_cltCexP, integral_cltCexDiff]
  · rw [hfun, IndepFun.variance_sum hmem (fun i _ j _ hij => indepFun_levelEstimator
      (fun p => (hω p).measurable) hind measurable_cltCexP hij _ _)]
    rw [Finset.sum_congr rfl fun ℓ hℓ => by
      rw [variance_levelEstimator hω hind measurable_cltCexP hPl ℓ (cltCexN_pos k ℓ),
        levelDiff_cltCexP, variance_cltCexDiff, cltCexN_of_ne (Finset.mem_range.1 hℓ).ne]]
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
    push_cast
    ring

/-- The tail bound behind the counterexample (Giles 2015, §2.1, p. 8): for `ε > 0`, the
normalised estimator `S_k = Y_k/σ_k` of row `k` satisfies
`P(|S_k| ≥ ε) ≤ 1/(ε²(k + 1)) + (k + 1)/2^k`.  The coarse levels contribute at most
`V[A_k]/(εσ_k)² ≤ 1/(ε²(k + 1))` (Chebyshev), and the finest level is `0` unless one of its
`k + 1` samples is nonzero, which has probability at most `(k + 1) 2^{−k}` (union bound). -/
lemma measureReal_cltCex_le [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ (volume.restrict (Set.Icc 0 1)))
    (hind : iIndepFun ω μ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    μ.real {x | ε ≤ |mlmcEstimator cltCexP ω k (cltCexN k) x /
        √(k / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1))|} ≤
      1 / (ε ^ 2 * ((k : ℝ) + 1)) + ((k : ℝ) + 1) / 2 ^ k := by
  obtain ⟨hAmem, hAmean, hAvar⟩ := coarse_cltCex hω hind k
  set A := fun x => ∑ ℓ ∈ range k, levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x
  set s : ℝ := k / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1) with hs
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hs1 : 1 / ((k : ℝ) + 1) ≤ s := by
    rw [hs]
    have : (0 : ℝ) ≤ k / ((k : ℝ) + 1) ^ 3 := by positivity
    linarith
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs1
  have hsq : 0 < √s := Real.sqrt_pos.2 hspos
  -- the event is covered by a large coarse part or a nonzero finest-level sample
  have hsub : {x | ε ≤ |mlmcEstimator cltCexP ω k (cltCexN k) x / √s|} ⊆
      {x | ε * √s ≤ |A x - μ[A]|} ∪
        ⋃ n ∈ range (k + 1), {x | cltCexDiff k (ω (k, n) x) ≠ 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    by_cases hall : ∀ n ∈ range (k + 1), cltCexDiff k (ω (k, n) x) = 0
    · left
      have hB : levelEstimator cltCexP ω k (cltCexN k k) x = 0 := by
        rw [levelEstimator, levelDiff_cltCexP, Finset.sum_eq_zero, mul_zero]
        intro n hn
        rw [cltCexN_self] at hn
        exact hall n hn
      have hY : mlmcEstimator cltCexP ω k (cltCexN k) x = A x := by
        rw [mlmcEstimator, Finset.sum_range_succ, hB, add_zero]
      rw [hY, abs_div, abs_of_pos hsq, le_div_iff₀ hsq] at hx
      simp only [Set.mem_ofPred_eq, hAmean, sub_zero]
      exact hx
    · right
      push Not at hall
      obtain ⟨n, hn, hne⟩ := hall
      exact Set.mem_biUnion hn hne
  have hcheb : μ.real {x | ε * √s ≤ |A x - μ[A]|} ≤ k / ((k : ℝ) + 1) ^ 3 / (ε * √s) ^ 2 := by
    rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have h := meas_ge_le_variance_div_sq hAmem (c := ε * √s) (by positivity)
    rwa [hAvar] at h
  have hunion : μ.real (⋃ n ∈ range (k + 1), {x | cltCexDiff k (ω (k, n) x) ≠ 0}) ≤
      ((k : ℝ) + 1) / 2 ^ k := by
    refine (measureReal_biUnion_finset_le _ _).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun n _ => by
      rw [show {x | cltCexDiff k (ω (k, n) x) ≠ 0} =
          ω (k, n) ⁻¹' {u | cltCexDiff k u ≠ 0} from rfl,
        (hω (k, n)).measureReal_preimage (show MeasurableSet {u | cltCexDiff k u ≠ 0} from
          (measurable_cltCexDiff k) (measurableSet_singleton 0).compl).nullMeasurableSet,
        measureReal_cltCexDiff_ne_zero]]
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
    push_cast
    ring
  have hfrac : k / ((k : ℝ) + 1) ^ 3 / (ε * √s) ^ 2 ≤ 1 / (ε ^ 2 * ((k : ℝ) + 1)) := by
    rw [mul_pow, Real.sq_sqrt hspos.le, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk : (k : ℝ) / ((k : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) ≤ s := by
      refine le_trans ?_ hs1
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hk1]
      nlinarith
    calc (k : ℝ) / ((k : ℝ) + 1) ^ 3 * (ε ^ 2 * ((k : ℝ) + 1))
        = ε ^ 2 * ((k : ℝ) / ((k : ℝ) + 1) ^ 3 * ((k : ℝ) + 1)) := by ring
      _ ≤ ε ^ 2 * s := by gcongr
      _ = 1 * (ε ^ 2 * s) := by ring
  calc μ.real {x | ε ≤ |mlmcEstimator cltCexP ω k (cltCexN k) x / √s|}
      ≤ μ.real ({x | ε * √s ≤ |A x - μ[A]|} ∪
        ⋃ n ∈ range (k + 1), {x | cltCexDiff k (ω (k, n) x) ≠ 0}) := measureReal_mono hsub
    _ ≤ μ.real {x | ε * √s ≤ |A x - μ[A]|} +
        μ.real (⋃ n ∈ range (k + 1), {x | cltCexDiff k (ω (k, n) x) ≠ 0}) :=
        measureReal_union_le _ _
    _ ≤ 1 / (ε ^ 2 * ((k : ℝ) + 1)) + ((k : ℝ) + 1) / 2 ^ k := by linarith

/-- `(k + 1)/2^k → 0`: the probability bound for a nonzero finest-level sample in the
counterexample (Giles 2015, §2.1, p. 8). -/
lemma tendsto_succ_div_two_pow :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) / 2 ^ k) atTop (𝓝 0) := by
  have h := (tendsto_self_mul_const_pow_of_lt_one (r := 1 / 2) (by norm_num)
    (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have h2 := h.const_mul 2
  rw [mul_zero] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp_apply]
  push_cast
  rw [pow_succ, one_div, inv_pow]
  field_simp

/-- The normalised estimator of the counterexample tends to `0` in probability (Giles 2015,
§2.1, p. 8), by `measureReal_cltCex_le`. -/
lemma tendstoInMeasure_cltCex [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ (volume.restrict (Set.Icc 0 1)))
    (hind : iIndepFun ω μ) :
    TendstoInMeasure μ (fun k x => (mlmcEstimator cltCexP ω k (cltCexN k) x -
        ∫ y, cltCexP k y ∂(volume.restrict (Set.Icc 0 1))) /
        √(∑ ℓ ∈ range (k + 1),
          variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  simp only [integral_cltCexP, sub_zero, sum_variance_div_cltCexN, Real.norm_eq_abs]
  have hlim : Tendsto (fun k : ℕ => 1 / (ε ^ 2 * ((k : ℝ) + 1)) + ((k : ℝ) + 1) / 2 ^ k) atTop
      (𝓝 0) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / ε ^ 2)
    rw [mul_zero] at h1
    have h := h1.add tendsto_succ_div_two_pow
    rw [add_zero] at h
    refine h.congr fun k => ?_
    rw [one_div_mul_one_div]
  exact squeeze_zero (fun k => measureReal_nonneg) (fun k => measureReal_cltCex_le hω hind hε k)
    hlim

/-- **Every level estimator is asymptotically normal, but the multilevel estimator is not**
(Giles 2015, §2.1, p. 8, l. 347–351: "Instead of bounding the Mean Square Error, they prefer to use
the Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence. This exploits the fact that the multilevel correction `Y_ℓ` on each
level is asymptotically Normally-distributed, and therefore so is `Y`.").  Let the inputs
`ω^{(ℓ,n)}` be independent and uniform on `[0, 1]`, and take the level outputs `cltCexP`, the
finest level `L_k = k` and the sample sizes `N_{k,ℓ}` of `cltCexN` (`cltCex_moments`:
`E[ΔP_ℓ] = 0`, `V_ℓ = 1`, `min_{ℓ ≤ k} N_{k,ℓ} → ∞`).  Then
* for every level `ℓ`, the standardised level estimator `(Y_{k,ℓ} − E[ΔP_ℓ])/√(V_ℓ/N_{k,ℓ})`
  tends to `N(0, 1)` in distribution as `k → ∞` (Mathlib's central limit theorem, via
  `tendstoInDistribution_levelEstimator`);
* the normalised multilevel estimator `S_k = (Y_k − E[P_{L_k}])/σ_k`,
  `σ_k² = ∑_{ℓ ≤ k} V_ℓ/N_{k,ℓ} = V[Y_k]`, tends to `0` in probability
  (`measureReal_cltCex_le`);
* hence `S_k` does not tend to `N(0, 1)` in distribution: its limit law is the point mass at
  `0` (`tendstoInDistribution_unique`).
So the paper's "therefore" needs a hypothesis when the number of levels grows; Lyapunov's
condition, or a uniform bound on the standardised moments, is such a hypothesis
(`tendstoInDistribution_mlmcEstimator_lyapunov`, `tendstoInDistribution_mlmcEstimator_of_moment_le`;
the conditions this example violates: `mlmc_clt_counterexample_conditions`).  For a fixed
number of levels the inference is valid (`tendstoInDistribution_mlmcEstimator`). -/
theorem mlmc_clt_counterexample {Ω Ω' : Type*} [MeasurableSpace Ω]
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} [IsProbabilityMeasure μ] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {ω : ℕ × ℕ → Ω → ℝ}
    (hω : ∀ p, MeasurePreserving (ω p) μ (volume.restrict (Set.Icc 0 1)))
    (hind : iIndepFun ω μ) {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    (∀ ℓ, TendstoInDistribution (fun k x =>
        (levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x -
          ∫ y, levelDiff cltCexP ℓ y ∂(volume.restrict (Set.Icc 0 1))) /
        √(variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ))
      atTop Z (fun _ => μ) P') ∧
    TendstoInMeasure μ (fun k x => (mlmcEstimator cltCexP ω k (cltCexN k) x -
        ∫ y, cltCexP k y ∂(volume.restrict (Set.Icc 0 1))) /
        √(∑ ℓ ∈ range (k + 1),
          variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ))
      atTop (fun _ => 0) ∧
    ¬ TendstoInDistribution (fun k x => (mlmcEstimator cltCexP ω k (cltCexN k) x -
        ∫ y, cltCexP k y ∂(volume.restrict (Set.Icc 0 1))) /
        √(∑ ℓ ∈ range (k + 1),
          variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ))
      atTop Z (fun _ => μ) P' := by
  have hm := tendstoInMeasure_cltCex hω hind
  refine ⟨fun ℓ => ?_, hm, fun hd => ?_⟩
  · -- the level CLT along `N = N_{k,ℓ} → ∞`
    have hD := levelDiff_cltCexP ℓ
    have h := tendstoInDistribution_levelEstimator (Pl := cltCexP) hω hind (ℓ := ℓ)
      (by rw [hD]; exact memLp_cltCexDiff ℓ 2) (Z := Z)
      (by rw [hD, variance_cltCexDiff, Real.toNNReal_one]; exact hZ)
    have hN : Tendsto (fun k => cltCexN k ℓ) atTop atTop :=
      tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (le_cltCexN k ℓ)) tendsto_id
    have h' : TendstoInDistribution (fun k x => √(cltCexN k ℓ : ℝ) *
        (levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x -
          ∫ y, levelDiff cltCexP ℓ y ∂(volume.restrict (Set.Icc 0 1)))) atTop Z (fun _ => μ) P' :=
      ⟨fun k => h.forall_aemeasurable _, h.aemeasurable_limit, h.tendsto.comp hN⟩
    have e : (fun k x => (levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x -
          ∫ y, levelDiff cltCexP ℓ y ∂(volume.restrict (Set.Icc 0 1))) /
        √(variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ)) =
        fun k x => √(cltCexN k ℓ : ℝ) * (levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x -
          ∫ y, levelDiff cltCexP ℓ y ∂(volume.restrict (Set.Icc 0 1))) := by
      funext k x
      rw [hD, variance_cltCexDiff, one_div, Real.sqrt_inv, div_inv_eq_mul, mul_comm]
    rw [e]
    exact h'
  · -- the limit law would be both `δ₀` and `N(0, 1)`
    have h0 := hm.tendstoInDistribution_of_aemeasurable
      (fun k => aemeasurable_mlmcEstimator_sub_div hω (fun ℓ _ => memLp_cltCexP ℓ 2) _ _ _)
      aemeasurable_const
    have huniq := tendstoInDistribution_unique _ h0 hd
    rw [hZ.map_eq, Measure.map_const, measure_univ, one_smul] at huniq
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    have h1 : (Measure.dirac (0 : ℝ)) {0} = 1 := by simp
    have h2 : (gaussianReal 0 1) {(0 : ℝ)} = 0 := measure_singleton 0
    rw [huniq, h2] at h1
    exact zero_ne_one h1

/-- The Lindeberg integrand is at most the square: `x² 𝟙{|x| > ε} ≤ x²`. -/
lemma lindebergIntegrand_le_sq (ε x : ℝ) :
    {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) x ≤ x ^ 2 := by
  by_cases h : ε < |x|
  · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | ε < |y|} from h)]
  · rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | ε < |y|} from h)]
    positivity

/-- A Lindeberg term of the counterexample is at most the variance:
`E[(cΔP_ℓ)²; |cΔP_ℓ| > ε] ≤ c² V_ℓ = c²`. -/
lemma integral_lindeberg_cltCex_le (ℓ : ℕ) (c ε : ℝ) :
    ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (c * cltCexDiff ℓ y)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ c ^ 2 := by
  have := isProbabilityMeasure_restrict_Icc_zero_one
  have hint : Integrable (fun y => (c * cltCexDiff ℓ y) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ((memLp_cltCexDiff ℓ 2).const_mul c).integrable_sq
  calc ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (c * cltCexDiff ℓ y)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ ∫ y, (c * cltCexDiff ℓ y) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        integral_mono_of_nonneg (ae_of_all _ fun y =>
          Set.indicator_nonneg (fun z _ => sq_nonneg z) _) hint
          (ae_of_all _ fun y => lindebergIntegrand_le_sq ε _)
    _ = c ^ 2 := by
        simp_rw [mul_pow]
        rw [integral_const_mul, integral_cltCexDiff_sq, mul_one]

/-- A Lindeberg term of the counterexample when the jumps are large: if `ε c < a_ℓ = 2^{ℓ/2}`,
every nonzero value of `c⁻¹ΔP_ℓ` exceeds `ε`, so `E[(c⁻¹ΔP_ℓ)²; |c⁻¹ΔP_ℓ| > ε] = c⁻²`. -/
lemma integral_lindeberg_cltCex_eq (ℓ : ℕ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hεc : ε * c < √((2 : ℝ) ^ ℓ)) :
    ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (c⁻¹ * cltCexDiff ℓ y)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = c⁻¹ ^ 2 := by
  have hpt : ∀ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (c⁻¹ * cltCexDiff ℓ y) =
      (c⁻¹ * cltCexDiff ℓ y) ^ 2 := by
    intro y
    rcases cltCexDiff_eq_zero_or ℓ y with h | h
    · rw [h, mul_zero, Set.indicator_of_notMem (show (0 : ℝ) ∉ {z : ℝ | ε < |z|} by
        simp only [Set.mem_ofPred_eq, abs_zero, not_lt]; exact hε.le)]
      ring
    · refine Set.indicator_of_mem ?_ _
      show ε < |c⁻¹ * cltCexDiff ℓ y|
      rw [abs_mul, abs_inv, abs_of_pos hc, h, ← div_eq_inv_mul, lt_div_iff₀ hc]
      exact hεc
  simp_rw [hpt, mul_pow]
  rw [integral_const_mul, integral_cltCexDiff_sq, mul_one]

/-- The centred `(2 + δ)`-th moments of the corrections of the counterexample are finite. -/
lemma integrable_cltCex_rpow (ℓ : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun y => |levelDiff cltCexP ℓ y -
      ∫ z, levelDiff cltCexP ℓ z ∂(volume.restrict (Set.Icc (0 : ℝ) 1))| ^ (2 + δ))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have := isProbabilityMeasure_restrict_Icc_zero_one
  rw [levelDiff_cltCexP, integral_cltCexDiff]
  simp only [sub_zero]
  refine Integrable.of_bound (((measurable_cltCexDiff ℓ).abs).pow_const _).aestronglyMeasurable
    (√((2 : ℝ) ^ ℓ) ^ (2 + δ)) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_cltCexDiff_le ℓ y) (by linarith)

/-- A Lindeberg term of the triangular array of the counterexample, transported to the input
law: `E[(cΔP_ℓ(ω^{(ℓ,n)}))²; |cΔP_ℓ(ω^{(ℓ,n)})| > ε] = E_ν[(cΔP_ℓ)²; |cΔP_ℓ| > ε]`. -/
lemma setIntegral_lindeberg_cltCex
    (hω : ∀ p, MeasurePreserving (ω p) μ (volume.restrict (Set.Icc 0 1))) (ℓ n : ℕ) (c ε : ℝ) :
    ∫ x in {x | ε < |c * cltCexDiff ℓ (ω (ℓ, n) x)|}, (c * cltCexDiff ℓ (ω (ℓ, n) x)) ^ 2 ∂μ =
      ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (c * cltCexDiff ℓ y)
        ∂(volume.restrict (Set.Icc 0 1)) := by
  rw [← integral_lindebergIntegrand (X := fun x => c * cltCexDiff ℓ (ω (ℓ, n) x))
    (((measurable_cltCexDiff ℓ).comp (hω (ℓ, n)).measurable).const_mul c).aemeasurable]
  exact integral_comp_of_measurePreserving (hω (ℓ, n))
    (f := fun y => {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (c * cltCexDiff ℓ y))
    ((measurable_lindebergIntegrand ε).comp
      ((measurable_cltCexDiff ℓ).const_mul c)).aestronglyMeasurable

/-- **The conditions of the triangular-array central limit theorems fail in the counterexample**
(Giles 2015, §2.1, p. 8, l. 350–351: "This exploits the fact that the multilevel correction `Y_ℓ` on
each level is asymptotically Normally-distributed, and therefore so is `Y`.").  In the setting of
`mlmc_clt_counterexample` (independent uniform inputs, `cltCexP`, `L_k = k`, `cltCexN`), write
`X_{k,(ℓ,n)} = (ΔP_ℓ(ω^{(ℓ,n)}) − E[ΔP_ℓ])/(N_{k,ℓ} σ_k)`, `ℓ ≤ k`, `n < N_{k,ℓ}`, for the
triangular array whose row sums are the normalised estimators `(Y_k − E[P_{L_k}])/σ_k`
(`mlmcEstimator_sub_div_eq_sum`), and `M_ℓ = E|ΔP_ℓ − E[ΔP_ℓ]|^{2+δ}`.  Then
* **Lindeberg's condition fails**: for every `ε > 0`,
  `∑_{ℓ ≤ k} ∑_{n < N_{k,ℓ}} E[X_{k,(ℓ,n)}²; |X_{k,(ℓ,n)}| > ε] → 1`, whereas
  `tendstoInDistribution_lindeberg` needs the limit `0`: once `ε (k + 1) σ_k < 2^{k/2}`, every
  nonzero finest-level sample is large, and the finest level carries the fraction
  `1/((k + 1)σ_k²) → 1` of the variance;
* **Lyapunov's condition fails**: for every `δ ≥ 0` the ratio
  `∑_{ℓ ≤ k} M_ℓ N_{k,ℓ}^{−1−δ}/σ_k^{2+δ}` of `tendstoInDistribution_mlmcEstimator_lyapunov`
  does not tend to `0` (it is `1` for `δ = 0`; for `δ > 0` the finest level alone gives at least
  `(4/5)^{1+δ/2} 2^{kδ/2} (k + 1)^{−δ/2} → ∞`, a value not formalised here);
* **the standardised moments are unbounded**: for every `δ > 0` there is no `K` with
  `M_ℓ ≤ K V_ℓ^{1+δ/2}` for all `ℓ` (the hypothesis of
  `tendstoInDistribution_mlmcEstimator_of_moment_le`; by a direct computation, not formalised
  here, `M_ℓ = 2^{ℓδ/2}` and `V_ℓ = 1`).
The last two follow from `mlmc_clt_counterexample`, as these conditions would give the central
limit theorem; the first is computed directly.  Feller's condition
`max V[X_{k,(ℓ,n)}] = 1/((k + 1)²σ_k²) → 0` holds as well (not formalised), so by Feller's
converse Lindeberg's condition is exactly the one that breaks. -/
theorem mlmc_clt_counterexample_conditions {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ω : ℕ × ℕ → Ω → ℝ}
    (hω : ∀ p, MeasurePreserving (ω p) μ (volume.restrict (Set.Icc 0 1)))
    (hind : iIndepFun ω μ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun k => ∑ q ∈ (range (k + 1)).sigma (fun ℓ => range (cltCexN k ℓ)),
        ∫ x in {x | ε < |((cltCexN k q.1 : ℝ) * √(∑ ℓ ∈ range (k + 1),
            variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ))⁻¹ *
          (levelDiff cltCexP q.1 (ω (q.1, q.2) x) -
            ∫ y, levelDiff cltCexP q.1 y ∂(volume.restrict (Set.Icc 0 1)))|},
          (((cltCexN k q.1 : ℝ) * √(∑ ℓ ∈ range (k + 1),
            variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ))⁻¹ *
          (levelDiff cltCexP q.1 (ω (q.1, q.2) x) -
            ∫ y, levelDiff cltCexP q.1 y ∂(volume.restrict (Set.Icc 0 1)))) ^ 2 ∂μ)
      atTop (𝓝 1)) ∧
    (∀ δ : ℝ, 0 ≤ δ → ¬ Tendsto (fun k => (∑ ℓ ∈ range (k + 1),
        (∫ y, |levelDiff cltCexP ℓ y -
          ∫ z, levelDiff cltCexP ℓ z ∂(volume.restrict (Set.Icc 0 1))| ^ (2 + δ)
            ∂(volume.restrict (Set.Icc 0 1))) * (cltCexN k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (k + 1),
          variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ) ^ (2 + δ))
      atTop (𝓝 0)) ∧
    (∀ δ : ℝ, 0 < δ → ¬ ∃ K : ℝ, ∀ ℓ, ∫ y, |levelDiff cltCexP ℓ y -
        ∫ z, levelDiff cltCexP ℓ z ∂(volume.restrict (Set.Icc 0 1))| ^ (2 + δ)
          ∂(volume.restrict (Set.Icc 0 1)) ≤
        K * variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) ^ (1 + δ / 2)) := by
  have hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (k + 1),
      variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc (0 : ℝ) 1)) / cltCexN k ℓ :=
    Eventually.of_forall fun k => by rw [sum_variance_div_cltCexN]; positivity
  have hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ k, n₀ ≤ cltCexN k ℓ := fun n₀ => by
    filter_upwards [eventually_ge_atTop n₀] with k hk ℓ _
    exact hk.trans ((Nat.le_succ k).trans (le_cltCexN k ℓ))
  have hnot := (mlmc_clt_counterexample (P' := gaussianReal 0 1) hω hind HasLaw.id).2.2
  refine ⟨fun ε hε => ?_, fun δ hδ hlyap => ?_, fun δ hδ ⟨K, hK⟩ => ?_⟩
  · have hs : ∀ k : ℕ, 0 < (k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1) := fun k => by
      positivity
    have hsum : ∀ k : ℕ, ∑ ℓ ∈ range (k + 1), (1 : ℝ) / (cltCexN k ℓ : ℝ) =
        (k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1) := fun k => by
      have h := sum_variance_div_cltCexN k
      simp only [levelDiff_cltCexP, variance_cltCexDiff] at h
      exact h
    simp only [levelDiff_cltCexP, integral_cltCexDiff, sub_zero, variance_cltCexDiff, hsum]
    -- the Lindeberg sum of row `k` is `∑_ℓ N_{k,ℓ} E_ν[g_{k,ℓ}²; |g_{k,ℓ}| > ε]`
    have hrow : ∀ k : ℕ, ∑ q ∈ (range (k + 1)).sigma (fun ℓ => range (cltCexN k ℓ)),
        ∫ x in {x | ε < |((cltCexN k q.1 : ℝ) *
          √((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1)))⁻¹ *
            cltCexDiff q.1 (ω (q.1, q.2) x)|},
          (((cltCexN k q.1 : ℝ) * √((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1)))⁻¹ *
            cltCexDiff q.1 (ω (q.1, q.2) x)) ^ 2 ∂μ =
        ∑ ℓ ∈ range (k + 1), (cltCexN k ℓ : ℝ) *
          ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2)
            (((cltCexN k ℓ : ℝ) * √((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1)))⁻¹ *
              cltCexDiff ℓ y) ∂(volume.restrict (Set.Icc 0 1)) := by
      intro k
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      simp only [setIntegral_lindeberg_cltCex hω, Finset.sum_const, card_range, nsmul_eq_mul]
    simp only [hrow]
    -- upper bound: the Lindeberg sum is at most the total variance `1`
    have hup : ∀ k : ℕ, ∑ ℓ ∈ range (k + 1), (cltCexN k ℓ : ℝ) *
          ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2)
            (((cltCexN k ℓ : ℝ) * √((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1)))⁻¹ *
              cltCexDiff ℓ y) ∂(volume.restrict (Set.Icc 0 1)) ≤ 1 := by
      intro k
      have hsk := hs k
      calc _ ≤ ∑ ℓ ∈ range (k + 1), (cltCexN k ℓ : ℝ) *
            (((cltCexN k ℓ : ℝ) *
              √((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1)))⁻¹) ^ 2 :=
            Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left
              (integral_lindeberg_cltCex_le ℓ _ ε) (Nat.cast_nonneg _)
        _ = (∑ ℓ ∈ range (k + 1), (1 : ℝ) / (cltCexN k ℓ : ℝ)) /
            ((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1)) := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            rw [inv_pow, mul_pow, Real.sq_sqrt hsk.le]
            field_simp
        _ = 1 := by rw [hsum k, div_self hsk.ne']
    -- lower bound: eventually the finest level alone contributes `1/((k + 1) σ_k²)`
    have hev : ∀ᶠ k : ℕ in atTop, ((k : ℝ) + 1) / 2 ^ k < 1 / (2 * ε ^ 2) :=
      tendsto_succ_div_two_pow.eventually_lt_const (by positivity)
    have hlow : ∀ᶠ k : ℕ in atTop, 1 / (((k : ℝ) + 1) *
        ((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1))) ≤
        ∑ ℓ ∈ range (k + 1), (cltCexN k ℓ : ℝ) *
          ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2)
            (((cltCexN k ℓ : ℝ) * √((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1)))⁻¹ *
              cltCexDiff ℓ y) ∂(volume.restrict (Set.Icc 0 1)) := by
      filter_upwards [hev] with k hk
      have hsk := hs k
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      set s := (k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1) with hsdef
      have hcpos : 0 < ((k : ℝ) + 1) * √s := mul_pos hk1 (Real.sqrt_pos.2 hsk)
      -- `ε (k + 1) σ_k < 2^{k/2}`
      have hcond : ε * (((k : ℝ) + 1) * √s) < √((2 : ℝ) ^ k) := by
        refine Real.lt_sqrt_of_sq_lt ?_
        have hks : ((k : ℝ) + 1) ^ 2 * s ≤ 2 * ((k : ℝ) + 1) := by
          rw [hsdef]
          have e : ((k : ℝ) + 1) ^ 2 * ((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1)) =
              (k : ℝ) / ((k : ℝ) + 1) + ((k : ℝ) + 1) := by
            field_simp
          rw [e]
          have : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
            rw [div_le_one hk1]
            linarith
          linarith
        rw [div_lt_iff₀ h2k, one_div, inv_mul_eq_div, lt_div_iff₀ (by positivity)] at hk
        calc (ε * (((k : ℝ) + 1) * √s)) ^ 2 = ε ^ 2 * (((k : ℝ) + 1) ^ 2 * s) := by
              rw [mul_pow, mul_pow, Real.sq_sqrt hsk.le]
          _ ≤ ε ^ 2 * (2 * ((k : ℝ) + 1)) := by gcongr
          _ < 2 ^ k := by linarith
      have hterm := integral_lindeberg_cltCex_eq k hcpos hε hcond
      have hle := Finset.single_le_sum (f := fun ℓ => (cltCexN k ℓ : ℝ) *
          ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2)
            (((cltCexN k ℓ : ℝ) * √s)⁻¹ * cltCexDiff ℓ y) ∂(volume.restrict (Set.Icc 0 1)))
        (fun ℓ _ => mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun y =>
          Set.indicator_nonneg (fun z _ => sq_nonneg z) _)) (Finset.self_mem_range_succ k)
      rw [cltCexN_self] at hle
      push_cast at hle
      rw [hterm] at hle
      refine le_trans (le_of_eq ?_) hle
      rw [inv_pow, mul_pow, Real.sq_sqrt hsk.le]
      field_simp
    -- `1/((k + 1) σ_k²) → 1`
    have hlim : Tendsto (fun k : ℕ => 1 / (((k : ℝ) + 1) *
        ((k : ℝ) / ((k : ℝ) + 1) ^ 3 + 1 / ((k : ℝ) + 1)))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
        refine squeeze_zero (fun k => by positivity) (fun k => ?_)
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        rw [div_le_div_iff₀ (by positivity) hk1]
        nlinarith
      have h1 := (h0.add_const 1).inv₀ (by norm_num)
      rw [zero_add, inv_one] at h1
      refine h1.congr fun k => ?_
      rw [one_div]
      congr 1
      field_simp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow
      (Eventually.of_forall hup)
  · exact hnot (tendstoInDistribution_mlmcEstimator_lyapunov hω hind (L := fun k => k)
      (fun k ℓ _ => memLp_cltCexP ℓ 2) hδ (fun k ℓ _ => integrable_cltCex_rpow ℓ hδ)
      (Eventually.of_forall fun k ℓ _ => cltCexN_pos k ℓ) hσ hlyap HasLaw.id)
  · exact hnot (tendstoInDistribution_mlmcEstimator_of_moment_le hω hind (L := fun k => k)
      (fun k ℓ _ => memLp_cltCexP ℓ 2) hδ (fun k ℓ _ => integrable_cltCex_rpow ℓ hδ.le)
      (fun k ℓ _ => hK ℓ) hNtop hσ HasLaw.id)

end Cex

/-- **The counterexample exists** (Giles 2015, §2.1, p. 8, l. 350–351: "the multilevel correction
`Y_ℓ` on each level is asymptotically Normally-distributed, and therefore so is `Y`").  There are a
probability space and independent inputs `ω^{(ℓ,n)}`, uniform on `[0, 1]`, such that, with the
level outputs `cltCexP`, the finest levels `L_k = k` and the sample sizes `cltCexN`, every
standardised level estimator tends to `N(0, 1)` in distribution while the normalised multilevel
estimator `(Y_k − E[P_{L_k}])/σ_k` does not.  The space is the infinite product
`[0, 1]^{ℕ×ℕ}` with the coordinates as inputs (`exists_iid_inputs`), and the rest is
`mlmc_clt_counterexample`. -/
theorem exists_mlmc_clt_counterexample :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ω : ℕ × ℕ → Ω → ℝ), iIndepFun ω μ ∧
      (∀ p, MeasurePreserving (ω p) μ (volume.restrict (Set.Icc 0 1))) ∧
      (∀ ℓ, TendstoInDistribution (fun k x =>
          (levelEstimator cltCexP ω ℓ (cltCexN k ℓ) x -
            ∫ y, levelDiff cltCexP ℓ y ∂(volume.restrict (Set.Icc 0 1))) /
          √(variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ))
        atTop id (fun _ => μ) (gaussianReal 0 1)) ∧
      ¬ TendstoInDistribution (fun k x => (mlmcEstimator cltCexP ω k (cltCexN k) x -
          ∫ y, cltCexP k y ∂(volume.restrict (Set.Icc 0 1))) /
          √(∑ ℓ ∈ range (k + 1),
            variance (levelDiff cltCexP ℓ) (volume.restrict (Set.Icc 0 1)) / cltCexN k ℓ))
        atTop id (fun _ => μ) (gaussianReal 0 1) := by
  have := isProbabilityMeasure_restrict_Icc_zero_one
  obtain ⟨hP, hind, hω⟩ := exists_iid_inputs (volume.restrict (Set.Icc (0 : ℝ) 1))
  obtain ⟨hlev, -, hnot⟩ := mlmc_clt_counterexample (P' := gaussianReal 0 1) hω hind HasLaw.id
  exact ⟨ℕ × ℕ → ℝ, inferInstance, _, hP, _, hind, hω, hlev, hnot⟩

/-! ### §3.3: the consistency check with one or two samples per level -/

/-- The unbiased sample variance `S_N² = (N − 1)⁻¹ ∑_{n<N} (x_n − x̄_N)²` of the first `N` terms
of a sequence (Giles 2015, §3.3, p. 23: "the sample variance").  `S_N² = N s_N²/(N − 1)` with
the biased empirical variance `s_N²` of `empVar`.  For `N = 1` it is `0/0`, Lean's junk value
`0`: the theorems assume `N ≥ 2`. -/
noncomputable def sampleVar (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, (x n - empMean x N) ^ 2) / ((N : ℝ) - 1)

/-- The empirical variance of one value is `0` (Giles 2015, §3.3, p. 22). -/
lemma empVar_one (x : ℕ → ℝ) : empVar x 1 = 0 := by
  simp [empVar, empMean]

/-- The empirical mean of one value is that value (Giles 2015, §3.3, p. 22). -/
lemma empMean_one (x : ℕ → ℝ) : empMean x 1 = x 0 := by
  simp [empMean]

/-- The empirical mean of two values (Giles 2015, §3.3, p. 22). -/
lemma empMean_two (x : ℕ → ℝ) : empMean x 2 = (x 0 + x 1) / 2 := by
  simp [empMean, Finset.sum_range_succ]

/-- The empirical variance of two values, `((x₀ − x₁)/2)²` (Giles 2015, §3.3, p. 22). -/
lemma empVar_two (x : ℕ → ℝ) : empVar x 2 = ((x 0 - x 1) / 2) ^ 2 := by
  simp only [empVar, empMean_two, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  push_cast
  ring

/-- The unbiased sample variance of two values, `(x₀ − x₁)²/2` (Giles 2015, §3.3, p. 23). -/
lemma sampleVar_two (x : ℕ → ℝ) : sampleVar x 2 = (x 0 - x 1) ^ 2 / 2 := by
  simp only [sampleVar, empMean_two, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  push_cast
  ring

section CheckOne

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω} {ω : ℕ × ℕ → Ω → Ω₀}

/-- **The consistency check with one sample per level** (Giles 2015, §3.3, p. 22, l. 1024–1029: "it
computes and plots the ratio `|a − b + c| / (3(√V_a + √V_b + √V_c))` where `V_a, V_b, V_c` are
empirical estimates for the variances of `a, b, c`. The probability of this ratio being greater than
unity is less than 0.3%.").  In the setting of `consistency_check_empirical` (levels `ℓ, ℓ + 1` for
the paper's `ℓ − 1, ℓ`; independent inputs `ω^{(p)}` of law `ν`; `a`, `b`, `c` the means of
`P^f_ℓ(ω^{(ℓ,n)})`, `P^f_{ℓ+1}(ω^{(ℓ+1,n)})` and `P^f_{ℓ+1} − P^c_ℓ` at the same inputs;
`V = s²/N` with the empirical variances `s²` of `empVar`), take `N_a = N_b = 1`.  Then
* every empirical variance is `0`, so the ratio is `0/0` or `+∞`, and the check fails (the event
  `3(√V_a + √V_b + √V_c) < |a − b + c|`) exactly when the two samples
  `P^f_ℓ(ω^{(ℓ,0)})` and `P^c_ℓ(ω^{(ℓ+1,0)})` differ (`P^f_{ℓ+1}` cancels);
* if `P^f_ℓ`, `P^c_ℓ` are measurable and the law of `P^c_ℓ` under `ν` has no atoms
  (`ν{P^c_ℓ = t} = 0` for every `t`), the check fails with probability `1`.
No other hypothesis is needed: not even (2.4).  The unbiased variance estimate
`S² = ∑ (x_n − x̄)²/(N − 1)` is undefined (`0/0`) for `N = 1`. -/
theorem consistency_check_one_sample [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {Pf Pc : ℕ → Ω₀ → ℝ}
    {ℓ : ℕ} (hPf : Measurable (Pf ℓ)) (hPc : Measurable (Pc ℓ))
    (hatom : ∀ t, ν {y | Pc ℓ y = t} = 0) :
    (∀ x, empVar (fun n => Pf ℓ (ω (ℓ, n) x)) 1 = 0 ∧
      empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 1 = 0 ∧
      empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 1 = 0 ∧
      (3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) 1 / 1) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 1 / 1) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 1 / 1)) <
        |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) 1 -
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 1 +
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 1| ↔
        Pf ℓ (ω (ℓ, 0) x) ≠ Pc ℓ (ω (ℓ + 1, 0) x))) ∧
    μ.real {x | 3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) 1 / 1) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 1 / 1) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 1 / 1)) <
      |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) 1 -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 1 +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 1|} = 1 := by
  have hpt : ∀ x, (3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) 1 / 1) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 1 / 1) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 1 / 1)) <
        |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) 1 -
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 1 +
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 1| ↔
        Pf ℓ (ω (ℓ, 0) x) ≠ Pc ℓ (ω (ℓ + 1, 0) x)) := by
    intro x
    simp only [empVar_one, empMean_one, zero_div, Real.sqrt_zero, add_zero, mul_zero,
      abs_pos]
    constructor
    · intro h he
      apply h
      rw [he]
      ring
    · intro h he
      apply h
      linarith
  refine ⟨fun x => ⟨empVar_one _, empVar_one _, empVar_one _, hpt x⟩, ?_⟩
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  -- the two samples are independent with law `ν ⊗ ν`
  have hne : ((ℓ, 0) : ℕ × ℕ) ≠ (ℓ + 1, 0) := by simp
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map (hω (ℓ, 0)).aemeasurable
    (hω (ℓ + 1, 0)).aemeasurable).1 (hind.indepFun hne)
  rw [(hω (ℓ, 0)).map_eq, (hω (ℓ + 1, 0)).map_eq] at hlaw
  set S : Set (Ω₀ × Ω₀) := {p | Pf ℓ p.1 = Pc ℓ p.2} with hSdef
  have hS : MeasurableSet S := measurableSet_eq_fun (hPf.comp measurable_fst)
    (hPc.comp measurable_snd)
  have hS0 : (ν.prod ν) S = 0 := by
    rw [Measure.prod_apply hS]
    have h0 : ∀ y, ν (Prod.mk y ⁻¹' S) = 0 := fun y => by
      have e : Prod.mk y ⁻¹' S = {y' | Pc ℓ y' = Pf ℓ y} := by
        ext y'
        simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq]
        exact eq_comm
      rw [e]
      exact hatom _
    simp [h0]
  have hg : Measurable fun x => (ω (ℓ, 0) x, ω (ℓ + 1, 0) x) :=
    (hω (ℓ, 0)).measurable.prodMk (hω (ℓ + 1, 0)).measurable
  have hset : {x | 3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) 1 / 1) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 1 / 1) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 1 / 1)) <
      |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) 1 -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 1 +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 1|} =
      (fun x => (ω (ℓ, 0) x, ω (ℓ + 1, 0) x)) ⁻¹' Sᶜ := by
    ext x
    rw [Set.mem_ofPred_eq, hpt x]
    simp [hSdef]
  rw [hset, measureReal_def, ← Measure.map_apply hg hS.compl, hlaw, prob_compl_eq_one_sub hS,
    hS0, tsub_zero, ENNReal.toReal_one]

end CheckOne

/-- The tangent criterion on `(−π/2, π/2)`: `|sin ψ| < t |cos ψ| ↔ |ψ| < arctan t` (for the
Cauchy probabilities of the consistency check, Giles 2015, §3.3, p. 22). -/
lemma abs_sin_lt_mul_abs_cos_iff {ψ : ℝ} (t : ℝ) (hψ : |ψ| < π / 2) :
    |sin ψ| < t * |cos ψ| ↔ |ψ| < arctan t := by
  have hψ' := abs_lt.1 hψ
  have hcos : 0 < cos ψ := cos_pos_of_mem_Ioo ⟨hψ'.1, hψ'.2⟩
  have htan : arctan (tan ψ) = ψ := arctan_tan hψ'.1 hψ'.2
  have h1 : |sin ψ| < t * |cos ψ| ↔ |tan ψ| < t := by
    rw [tan_eq_sin_div_cos, abs_div, abs_of_pos hcos, div_lt_iff₀ hcos]
  have e1 : -t < tan ψ ↔ -arctan t < ψ := by
    rw [← arctan_strictMono.lt_iff_lt, arctan_neg, htan]
  have e2 : tan ψ < t ↔ ψ < arctan t := by
    rw [← arctan_strictMono.lt_iff_lt, htan]
  rw [h1, abs_lt, abs_lt, e1, e2]

/-- `cos(ψ + π/4) − sin(ψ + π/4) = −√2 sin ψ`. -/
lemma cos_add_pi_div_four_sub_sin (ψ : ℝ) :
    cos (ψ + π / 4) - sin (ψ + π / 4) = -(√2 * sin ψ) := by
  rw [cos_add, sin_add, cos_pi_div_four, sin_pi_div_four]
  ring

/-- `cos(ψ + π/4) + sin(ψ + π/4) = √2 cos ψ`. -/
lemma cos_add_pi_div_four_add_sin (ψ : ℝ) :
    cos (ψ + π / 4) + sin (ψ + π / 4) = √2 * cos ψ := by
  rw [cos_add, sin_add, cos_pi_div_four, sin_pi_div_four]
  ring

/-- The cone `|u − v| < t |u + v|` in polar coordinates, rotated by `π/4`:
`|cos θ − sin θ| < t |cos θ + sin θ| ↔ |sin ψ| < t |cos ψ|` for `θ = ψ + π/4`. -/
lemma cone_angle_iff (t ψ : ℝ) :
    |cos (ψ + π / 4) - sin (ψ + π / 4)| < t * |cos (ψ + π / 4) + sin (ψ + π / 4)| ↔
      |sin ψ| < t * |cos ψ| := by
  have hs : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  rw [cos_add_pi_div_four_sub_sin, cos_add_pi_div_four_add_sin, abs_neg, abs_mul, abs_mul,
    abs_of_pos hs, mul_left_comm, mul_lt_mul_iff_right₀ hs]

/-- The angles of the cone `|u − v| < t |u + v|`, `0 < t < 1`: in `(−π, π)` they form the two
intervals of length `2 arctan t` centred at `π/4` and `−3π/4` (for the consistency check of
Giles 2015, §3.3, p. 22). -/
lemma cone_angle_set {t : ℝ} (ht1 : t < 1) :
    {θ : ℝ | |cos θ - sin θ| < t * |cos θ + sin θ|} ∩ Set.Ioo (-π) π =
      Set.Ioo (π / 4 - arctan t) (π / 4 + arctan t) ∪
        Set.Ioo (-(3 * π / 4) - arctan t) (-(3 * π / 4) + arctan t) := by
  have hc1 : arctan t < π / 4 := by
    rw [← arctan_one]
    exact arctan_strictMono ht1
  have hshift : ∀ φ, |sin (φ + π)| < t * |cos (φ + π)| ↔ |sin φ| < t * |cos φ| :=
    fun φ => by rw [sin_add_pi, cos_add_pi, abs_neg, abs_neg]
  have hzero : ∀ φ, cos φ = 0 → ¬ |sin φ| < t * |cos φ| := fun φ h => by
    rw [h, abs_zero, mul_zero]
    exact not_lt.2 (abs_nonneg _)
  ext θ
  have hθ : θ = (θ - π / 4) + π / 4 := by ring
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, Set.mem_union]
  rw [hθ, cone_angle_iff]
  set ψ := θ - π / 4
  constructor
  · rintro ⟨hcnd, h1, h2⟩
    by_cases hlt : |ψ| < π / 2
    · rw [abs_sin_lt_mul_abs_cos_iff _ hlt, abs_lt] at hcnd
      left
      constructor <;> linarith
    · rcases le_or_gt ψ 0 with hneg | hpos
      · -- `ψ ≤ −π/2`
        have hle : ψ ≤ -(π / 2) := by
          rw [abs_of_nonpos hneg] at hlt
          linarith
        rcases hle.lt_or_eq with hlt' | heq
        · have hb : |ψ + π| < π / 2 := by
            rw [abs_lt]
            constructor <;> linarith
          rw [← hshift, abs_sin_lt_mul_abs_cos_iff _ hb, abs_lt] at hcnd
          right
          constructor <;> linarith
        · exact absurd hcnd (hzero ψ (by rw [heq, cos_neg, cos_pi_div_two]))
      · -- `ψ ≥ π/2`
        have hge : π / 2 ≤ ψ := by
          rw [abs_of_pos hpos] at hlt
          linarith
        rcases hge.lt_or_eq with hlt' | heq
        · have hb : |ψ - π| < π / 2 := by
            rw [abs_lt]
            constructor <;> linarith
          have hcnd' : |sin (ψ - π + π)| < t * |cos (ψ - π + π)| := by
            rwa [sub_add_cancel]
          rw [hshift, abs_sin_lt_mul_abs_cos_iff _ hb, abs_lt] at hcnd'
          linarith [hcnd'.1]
        · exact absurd hcnd (hzero ψ (by rw [← heq, cos_pi_div_two]))
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hb : |ψ| < π / 2 := by
        rw [abs_lt]
        constructor <;> linarith
      refine ⟨(abs_sin_lt_mul_abs_cos_iff _ hb).2 ?_, by linarith, by linarith⟩
      rw [abs_lt]
      constructor <;> linarith
    · have hb : |ψ + π| < π / 2 := by
        rw [abs_lt]
        constructor <;> linarith
      refine ⟨(hshift ψ).1 ((abs_sin_lt_mul_abs_cos_iff _ hb).2 ?_), by linarith, by linarith⟩
      rw [abs_lt]
      constructor <;> linarith

/-- `∫_0^∞ r e^{−r²/2} dr = 1`, the radial integral of the standard normal density in the plane. -/
lemma integral_Ioi_mul_exp_neg_sq_div_two :
    ∫ r in Set.Ioi (0 : ℝ), r * exp (-r ^ 2 / 2) = 1 := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -exp (-x ^ 2 / 2))
      (x * exp (-x ^ 2 / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    exact ((h1.neg.div_const 2).exp.neg).congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hint : IntegrableOn (fun x : ℝ => x * exp (-x ^ 2 / 2)) (Set.Ioi 0) := by
    have h := integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    have e : (fun x : ℝ => x * exp (-(1 / 2) * x ^ 2)) = fun x => x * exp (-x ^ 2 / 2) := by
      funext x
      rw [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
    rw [e] at h
    exact h.integrableOn
  have hlim : Tendsto (fun x : ℝ => -exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    have h2 : Tendsto (fun x : ℝ => exp (-(x ^ 2 / 2))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := h2.neg
    rw [neg_zero] at h3
    exact h3.congr fun x => by rw [neg_div]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp

/-- The product of two standard normal densities in polar coordinates:
`φ(r cos θ) φ(r sin θ) = (2π)⁻¹ e^{−r²/2}`. -/
lemma gaussianPDF_mul_polar (r θ : ℝ) :
    gaussianPDF 0 1 (r * cos θ) * gaussianPDF 0 1 (r * sin θ) =
      ENNReal.ofReal ((2 * π)⁻¹ * exp (-r ^ 2 / 2)) := by
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hs : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt h2π]
  have he : exp (-(r * cos θ) ^ 2 / 2) * exp (-(r * sin θ) ^ 2 / 2) = exp (-r ^ 2 / 2) := by
    rw [← exp_add]
    congr 1
    linear_combination (-(r ^ 2) / 2) * sin_sq_add_cos_sq θ
  calc (√(2 * π))⁻¹ * exp (-(r * cos θ) ^ 2 / 2) * ((√(2 * π))⁻¹ * exp (-(r * sin θ) ^ 2 / 2))
      = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) *
        (exp (-(r * cos θ) ^ 2 / 2) * exp (-(r * sin θ) ^ 2 / 2)) := by ring
    _ = (2 * π)⁻¹ * exp (-r ^ 2 / 2) := by rw [hs, he]

/-- **A Cauchy probability of two independent standard normals** (for the consistency check of
Giles 2015, §3.3, p. 22).  For `0 < t < 1`, the standard normal law of the plane gives the cone
`|u − v| < t |u + v|` the mass `(2/π) arctan t`; equivalently, for independent `U, V ∼ N(0, 1)`
the ratio `(U − V)/(U + V)` is standard Cauchy, `P(|U − V| < t |U + V|) = (2/π) arctan t`.  Proof
in polar coordinates (`lintegral_comp_polarCoord_symm`): the radial integral
`∫_0^∞ r e^{−r²/2}/(2π) dr = 1/(2π)` and the angles of the cone have measure `4 arctan t`
(`cone_angle_set`). -/
lemma gaussian_prod_cone {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) {p : ℝ × ℝ | |p.1 - p.2| < t * |p.1 + p.2|} =
      ENNReal.ofReal (2 / π * arctan t) := by
  set C := {p : ℝ × ℝ | |p.1 - p.2| < t * |p.1 + p.2|} with hCdef
  have hC : MeasurableSet C := measurableSet_lt (by fun_prop) (by fun_prop)
  set A := {θ : ℝ | |cos θ - sin θ| < t * |cos θ + sin θ|} with hAdef
  have hA : MeasurableSet A := measurableSet_lt (by fun_prop) (by fun_prop)
  have hG : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  rw [hG, prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    ← Measure.volume_eq_prod, withDensity_apply _ hC, ← lintegral_indicator hC,
    ← lintegral_comp_polarCoord_symm]
  have hcongr : Set.EqOn (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
      C.indicator (fun z : ℝ × ℝ => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2)
        (polarCoord.symm p))
      (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((2 * π)⁻¹ * exp (-p.1 ^ 2 / 2))) *
        A.indicator 1 p.2) polarCoord.target := by
    intro p hp
    rw [polarCoord_target] at hp
    have hr : 0 < p.1 := hp.1
    simp only [polarCoord_symm_apply]
    have hmem : (p.1 * cos p.2, p.1 * sin p.2) ∈ C ↔ p.2 ∈ A := by
      simp only [hCdef, hAdef, Set.mem_ofPred_eq]
      rw [← mul_sub, ← mul_add, abs_mul, abs_mul, abs_of_pos hr, mul_left_comm,
        mul_lt_mul_iff_right₀ hr]
    by_cases hθ : p.2 ∈ A
    · rw [Set.indicator_of_mem (hmem.2 hθ), Set.indicator_of_mem hθ, gaussianPDF_mul_polar,
        smul_eq_mul, ← ENNReal.ofReal_mul hr.le, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (fun h => hθ (hmem.1 h)), Set.indicator_of_notMem hθ,
        smul_zero, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hcongr, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((2 * π)⁻¹ * exp (-r ^ 2 / 2))))
      (g := A.indicator 1) (by fun_prop) ((measurable_one.indicator hA).aemeasurable)]
  -- the radial integral
  have hrad : ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * ((2 * π)⁻¹ * exp (-r ^ 2 / 2))) =
      ENNReal.ofReal ((2 * π)⁻¹) := by
    have hint : IntegrableOn (fun r : ℝ => r * exp (-r ^ 2 / 2)) (Set.Ioi 0) := by
      have h := integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      have e : (fun x : ℝ => x * exp (-(1 / 2) * x ^ 2)) = fun x => x * exp (-x ^ 2 / 2) := by
        funext x
        rw [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
      rw [e] at h
      exact h.integrableOn
    have e2 : (fun r : ℝ => r * ((2 * π)⁻¹ * exp (-r ^ 2 / 2))) =
        fun r => (2 * π)⁻¹ * (r * exp (-r ^ 2 / 2)) := by
      funext r
      ring
    rw [← ofReal_integral_eq_lintegral_ofReal, e2, integral_const_mul,
      integral_Ioi_mul_exp_neg_sq_div_two, mul_one]
    · rw [e2]
      exact hint.const_mul _
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
      have hr' : 0 < r := hr
      positivity
  -- the angular integral
  have hang : ∫⁻ θ in Set.Ioo (-π) π, A.indicator 1 θ = ENNReal.ofReal (4 * arctan t) := by
    have hc0 : 0 < arctan t := arctan_pos.2 ht0
    rw [lintegral_indicator_one hA, Measure.restrict_apply hA, hAdef, cone_angle_set ht1,
      measure_union _ measurableSet_Ioo, Real.volume_Ioo, Real.volume_Ioo,
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    · congr 1
      ring
    · rw [Set.disjoint_left]
      intro θ h1 h2
      simp only [Set.mem_Ioo] at h1 h2
      have hc1 : arctan t < π / 4 := by
        rw [← arctan_one]
        exact arctan_strictMono ht1
      linarith [h1.1, h2.2]
  rw [hrad, hang, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- `(2/π) arctan(√2/3) > 1/4`, as `2 arctan(√2/3) = arctan(6√2/7) > arctan 1 = π/4`. -/
lemma quarter_lt_two_div_pi_mul_arctan : 1 / 4 < 2 / π * arctan (√2 / 3) := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := Real.sqrt_pos.2 two_pos
  have hxy : √2 / 3 * (√2 / 3) < 1 := by nlinarith
  have hadd := arctan_add hxy
  have h67 : 1 < (√2 / 3 + √2 / 3) / (1 - √2 / 3 * (√2 / 3)) := by
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have h := arctan_strictMono h67
  rw [arctan_one, ← hadd] at h
  have hπ := pi_pos
  rw [div_mul_eq_mul_div, lt_div_iff₀ hπ]
  linarith

/-- `(2/π) arctan(1/3) > 1/8`, as `4 arctan(1/3) = arctan(24/7) > arctan 1 = π/4`. -/
lemma eighth_lt_two_div_pi_mul_arctan : 1 / 8 < 2 / π * arctan (1 / 3) := by
  have h1 := arctan_add (x := 1 / 3) (y := 1 / 3) (by norm_num)
  have h2 := arctan_add (x := 3 / 4) (y := 3 / 4) (by norm_num)
  have e1 : (1 / 3 + 1 / 3 : ℝ) / (1 - 1 / 3 * (1 / 3)) = 3 / 4 := by norm_num
  have e2 : (3 / 4 + 3 / 4 : ℝ) / (1 - 3 / 4 * (3 / 4)) = 24 / 7 := by norm_num
  rw [e1] at h1
  rw [e2] at h2
  have h3 : arctan 1 < arctan (24 / 7) := arctan_strictMono (by norm_num)
  rw [arctan_one, ← h2, ← h1] at h3
  have hπ := pi_pos
  rw [div_mul_eq_mul_div, lt_div_iff₀ hπ]
  linarith

section CheckTwo

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ω : ℕ × ℕ → Ω → ℝ}

/-- The law of the cone event of two independent standard normal inputs (for the consistency
check of Giles 2015, §3.3, p. 22): `P(|y₀ − y₁| < t |y₀ + y₁|) = (2/π) arctan t` for
`y_n = ω^{(ℓ+1,n)}`, by independence and `gaussian_prod_cone`. -/
lemma measureReal_cone_inputs [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ (gaussianReal 0 1)) (hind : iIndepFun ω μ)
    (ℓ : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    μ.real {x | |ω (ℓ + 1, 0) x - ω (ℓ + 1, 1) x| < t * |ω (ℓ + 1, 0) x + ω (ℓ + 1, 1) x|} =
      2 / π * arctan t := by
  have hC : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| < t * |p.1 + p.2|} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  have hne : ((ℓ + 1, 0) : ℕ × ℕ) ≠ (ℓ + 1, 1) := by simp
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map (hω (ℓ + 1, 0)).aemeasurable
    (hω (ℓ + 1, 1)).aemeasurable).1 (hind.indepFun hne)
  rw [(hω (ℓ + 1, 0)).map_eq, (hω (ℓ + 1, 1)).map_eq] at hlaw
  have hg : Measurable fun x => (ω (ℓ + 1, 0) x, ω (ℓ + 1, 1) x) :=
    (hω (ℓ + 1, 0)).measurable.prodMk (hω (ℓ + 1, 1)).measurable
  have hset : {x | |ω (ℓ + 1, 0) x - ω (ℓ + 1, 1) x| < t * |ω (ℓ + 1, 0) x + ω (ℓ + 1, 1) x|} =
      (fun x => (ω (ℓ + 1, 0) x, ω (ℓ + 1, 1) x)) ⁻¹'
        {p : ℝ × ℝ | |p.1 - p.2| < t * |p.1 + p.2|} := rfl
  rw [hset, measureReal_def, ← Measure.map_apply hg hC, hlaw, gaussian_prod_cone ht0 ht1,
    ENNReal.toReal_ofReal (by positivity)]

/-- **The consistency check with two samples per level fails with probability about 28%**
(Giles 2015, §3.3, p. 22, l. 1024–1029: "it computes and plots the ratio
`|a − b + c| / (3(√V_a + √V_b + √V_c))` where `V_a, V_b, V_c` are empirical estimates for the
variances of `a, b, c`. The probability of this ratio being greater than unity is less than 0.3%.").
The example of `MlmcLean/ConsistencyCheck.lean`: the inputs `ω^{(p)}` are independent standard
normals, `P^f_ℓ = P^f_{ℓ+1} = 0` and `P^c_ℓ(y) = −y`, so (2.4) holds (`E[P^f_ℓ] = E[P^c_ℓ] = 0`) and
`a − b + c` is the mean of the `y_n = ω^{(ℓ+1,n)}`.  With `N_a = N_b = 2` samples:
* with the empirical variances `V = s²/N` (`empVar`, as in `consistency_check_empirical`), the
  check fails iff `3|y₀ − y₁| < √2 |y₀ + y₁|`, which has probability exactly
  `(2/π) arctan(√2/3) ≈ 0.2804`, more than `1/4`;
* with the unbiased variances `V = S²/N` (`sampleVar`), it fails iff `3|y₀ − y₁| < |y₀ + y₁|`,
  with probability exactly `(2/π) arctan(1/3) ≈ 0.2048`, more than `1/8`.
Both are far above the paper's `0.3%`, which holds only in the limit of large samples
(`consistency_check_empirical_lt`).  The ratio `(y₀ − y₁)/(y₀ + y₁)` is standard Cauchy
(`gaussian_prod_cone`). -/
theorem consistency_check_two_samples [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ (gaussianReal 0 1)) (hind : iIndepFun ω μ)
    {Pf Pc : ℕ → ℝ → ℝ} {ℓ : ℕ} (hf₀ : ∀ y, Pf ℓ y = 0) (hf₁ : ∀ y, Pf (ℓ + 1) y = 0)
    (hc : ∀ y, Pc ℓ y = -y) :
    μ.real {x | 3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) 2 / 2) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 2 / 2) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 2 / 2)) <
      |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) 2 -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 2 +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 2|} =
      2 / π * arctan (√2 / 3) ∧ 1 / 4 < 2 / π * arctan (√2 / 3) ∧
    μ.real {x | 3 * (√(sampleVar (fun n => Pf ℓ (ω (ℓ, n) x)) 2 / 2) +
        √(sampleVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 2 / 2) +
        √(sampleVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 2 / 2)) <
      |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) 2 -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) 2 +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) 2|} =
      2 / π * arctan (1 / 3) ∧ 1 / 8 < 2 / π * arctan (1 / 3) := by
  have hs3 : √2 / 3 < 1 := by
    have h : √2 < 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  refine ⟨?_, quarter_lt_two_div_pi_mul_arctan, ?_, eighth_lt_two_div_pi_mul_arctan⟩
  · rw [← measureReal_cone_inputs hω hind ℓ (by positivity) hs3]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, hf₀, hf₁, hc, sub_neg_eq_add, zero_add, empVar_two,
      empMean_two]
    norm_num
    rw [Real.sqrt_sq_eq_abs, abs_div, abs_div, abs_two]
    have h1 : 3 * (|ω (ℓ + 1, 0) x - ω (ℓ + 1, 1) x| / 2 / √2) =
        3 / (2 * √2) * |ω (ℓ + 1, 0) x - ω (ℓ + 1, 1) x| := by
      field_simp
    have h2 : √2 / 3 * |ω (ℓ + 1, 0) x + ω (ℓ + 1, 1) x| =
        (2 * √2 / 3) * (|ω (ℓ + 1, 0) x + ω (ℓ + 1, 1) x| / 2) := by
      field_simp
    rw [h1, h2]
    constructor
    · intro h
      have h' := mul_lt_mul_of_pos_left h (show (0 : ℝ) < 2 * √2 / 3 by positivity)
      have e : 2 * √2 / 3 * (3 / (2 * √2) * |ω (ℓ + 1, 0) x - ω (ℓ + 1, 1) x|) =
          |ω (ℓ + 1, 0) x - ω (ℓ + 1, 1) x| := by
        field_simp
      linarith
    · intro h
      have h' := mul_lt_mul_of_pos_left h (show (0 : ℝ) < 3 / (2 * √2) by positivity)
      have e : 3 / (2 * √2) * (2 * √2 / 3 * (|ω (ℓ + 1, 0) x + ω (ℓ + 1, 1) x| / 2)) =
          |ω (ℓ + 1, 0) x + ω (ℓ + 1, 1) x| / 2 := by
        field_simp
      linarith
  · rw [← measureReal_cone_inputs hω hind ℓ (by norm_num) (by norm_num)]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, hf₀, hf₁, hc, sub_neg_eq_add, zero_add, sampleVar_two,
      empMean_two]
    norm_num
    rw [Real.sqrt_sq_eq_abs, abs_div, abs_two, div_div, Real.mul_self_sqrt (by norm_num)]
    constructor <;> intro h <;> linarith

end CheckTwo

/-! ### §3.3: the standard deviation of the sample variance -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Second and fourth moments of a sum of independent centred variables** (behind Giles 2015,
§3.3, p. 23: "the standard deviation of the sample variance"): for mutually independent
measurable `Y_i` with `E[Y_i] = 0`, `E[Y_i²] = v` and `E[Y_i⁴] = q < ∞`, and every finite set
`s`, `E[(∑_{i ∈ s} Y_i)²] = |s| v` and `E[(∑_{i ∈ s} Y_i)⁴] = |s| q + 3|s|(|s| − 1) v²`
(`moments_add_indep` and induction on `s`; `moments_sum_indep` has the inequality
`≤ n q + 3n² v²` for `s = {0, …, n − 1}`). -/
lemma moments_finsetSum_indep [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y μ)
    (hYm : ∀ i, Measurable (Y i)) (hY4 : ∀ i, Integrable (fun ω => Y i ω ^ 4) μ)
    (hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0) {v q : ℝ} (hv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = v)
    (hq : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ = q) (s : Finset ℕ) :
    Integrable (fun ω => (∑ i ∈ s, Y i ω) ^ 4) μ ∧
      ∫ ω, (∑ i ∈ s, Y i ω) ^ 2 ∂μ = s.card * v ∧
      ∫ ω, (∑ i ∈ s, Y i ω) ^ 4 ∂μ =
        s.card * q + 3 * (s.card : ℝ) * ((s.card : ℝ) - 1) * v ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h4, h2, h4e⟩ := ih
    have hSm : Measurable fun ω => ∑ i ∈ s, Y i ω := Finset.measurable_sum _ fun i _ => hYm i
    have hSX : IndepFun (fun ω => ∑ i ∈ s, Y i ω) (Y a) μ := by
      have h := hind.indepFun_finsetSum_of_notMem hYm ha
      convert h using 1
      funext ω
      simp only [Finset.sum_apply]
    have hY1 : ∀ i, Integrable (Y i) μ := fun i => by
      simpa using integrable_pow_of_pow_four (hYm i) (hY4 i) (k := 1) (by norm_num)
    have hS0 : ∫ ω, ∑ i ∈ s, Y i ω ∂μ = 0 := by
      rw [integral_finsetSum _ fun i _ => hY1 i]
      simp [hY0]
    obtain ⟨i4, e2, e4⟩ := moments_add_indep hSX hSm (hYm a) h4 (hY4 a) hS0 (hY0 a)
    have hsum : ∀ ω, ∑ i ∈ insert a s, Y i ω = (∑ i ∈ s, Y i ω) + Y a ω := fun ω => by
      rw [Finset.sum_insert ha, add_comm]
    simp only [hsum, Finset.card_insert_of_notMem ha]
    refine ⟨i4, ?_, ?_⟩
    · rw [e2, h2, hv a]
      push_cast
      ring
    · rw [e4, h2, h4e, hv a, hq a]
      push_cast
      ring

/-- One step of the mixed moment: for independent `R` and `X` with finite fourth moments and
`E[R] = 0`, `E[X²(X + R)²] = E[X⁴] + E[X²] E[R²]` (behind Giles 2015, §3.3, p. 23). -/
lemma integral_sq_mul_add_sq_indep [IsProbabilityMeasure μ] {R X : Ω → ℝ}
    (hRX : IndepFun R X μ) (hRm : Measurable R) (hXm : Measurable X)
    (hR4 : Integrable (fun ω => R ω ^ 4) μ) (hX4 : Integrable (fun ω => X ω ^ 4) μ)
    (hR0 : ∫ ω, R ω ∂μ = 0) :
    Integrable (fun ω => X ω ^ 2 * (X ω + R ω) ^ 2) μ ∧
      ∫ ω, X ω ^ 2 * (X ω + R ω) ^ 2 ∂μ =
        ∫ ω, X ω ^ 4 ∂μ + (∫ ω, X ω ^ 2 ∂μ) * ∫ ω, R ω ^ 2 ∂μ := by
  have p2 : Measurable fun x : ℝ => x ^ 2 := (continuous_pow 2).measurable
  have p3 : Measurable fun x : ℝ => x ^ 3 := (continuous_pow 3).measurable
  have hR1 : Integrable R μ := by
    simpa using integrable_pow_of_pow_four hRm hR4 (k := 1) (by norm_num)
  have hR2 : Integrable (fun ω => R ω ^ 2) μ := integrable_pow_of_pow_four hRm hR4 (by norm_num)
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := integrable_pow_of_pow_four hXm hX4 (by norm_num)
  have hX3 : Integrable (fun ω => X ω ^ 3) μ := integrable_pow_of_pow_four hXm hX4 (by norm_num)
  have i31 : Integrable (fun ω => X ω ^ 3 * R ω) μ :=
    (hRX.symm.comp p3 measurable_id).integrable_mul hX3 hR1
  have i22 : Integrable (fun ω => X ω ^ 2 * R ω ^ 2) μ :=
    (hRX.symm.comp p2 p2).integrable_mul hX2 hR2
  have e31 : ∫ ω, X ω ^ 3 * R ω ∂μ = (∫ ω, X ω ^ 3 ∂μ) * ∫ ω, R ω ∂μ :=
    (hRX.symm.comp p3 measurable_id).integral_fun_mul_eq_mul_integral
      hX3.aestronglyMeasurable hR1.aestronglyMeasurable
  have e22 : ∫ ω, X ω ^ 2 * R ω ^ 2 ∂μ = (∫ ω, X ω ^ 2 ∂μ) * ∫ ω, R ω ^ 2 ∂μ :=
    (hRX.symm.comp p2 p2).integral_fun_mul_eq_mul_integral hX2.aestronglyMeasurable
      hR2.aestronglyMeasurable
  have h : ∀ ω, X ω ^ 2 * (X ω + R ω) ^ 2 =
      X ω ^ 4 + 2 * (X ω ^ 3 * R ω) + X ω ^ 2 * R ω ^ 2 := fun ω => by ring
  have j1 : Integrable (fun ω => X ω ^ 4 + 2 * (X ω ^ 3 * R ω)) μ := hX4.add (i31.const_mul 2)
  simp_rw [h]
  refine ⟨j1.add i22, ?_⟩
  rw [integral_add j1 i22, integral_add hX4 (i31.const_mul 2), integral_const_mul, e31, e22,
    hR0]
  ring

/-- **The mixed moment `E[Q T²]`** (behind Giles 2015, §3.3, p. 23): in the setting of
`moments_finsetSum_indep`, with `Q = ∑_{i ∈ s} Y_i²` and `T = ∑_{i ∈ s} Y_i`,
`E[Q T²] = |s| q + |s|(|s| − 1) v²`: write `Q T² = ∑_i Y_i² (Y_i + ∑_{j ≠ i} Y_j)²`
(`integral_sq_mul_add_sq_indep`). -/
lemma integral_sumSq_mul_sq [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y μ)
    (hYm : ∀ i, Measurable (Y i)) (hY4 : ∀ i, Integrable (fun ω => Y i ω ^ 4) μ)
    (hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0) {v q : ℝ} (hv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = v)
    (hq : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ = q) (s : Finset ℕ) :
    Integrable (fun ω => (∑ i ∈ s, Y i ω ^ 2) * (∑ i ∈ s, Y i ω) ^ 2) μ ∧
      ∫ ω, (∑ i ∈ s, Y i ω ^ 2) * (∑ i ∈ s, Y i ω) ^ 2 ∂μ =
        s.card * q + (s.card : ℝ) * ((s.card : ℝ) - 1) * v ^ 2 := by
  have hY1 : ∀ i, Integrable (Y i) μ := fun i => by
    simpa using integrable_pow_of_pow_four (hYm i) (hY4 i) (k := 1) (by norm_num)
  have hterm : ∀ i ∈ s, Integrable (fun ω => Y i ω ^ 2 * (∑ j ∈ s, Y j ω) ^ 2) μ ∧
      ∫ ω, Y i ω ^ 2 * (∑ j ∈ s, Y j ω) ^ 2 ∂μ = q + v * (((s.card : ℝ) - 1) * v) := by
    intro i hi
    have hsplit : ∀ ω, ∑ j ∈ s, Y j ω = Y i ω + ∑ j ∈ s.erase i, Y j ω := fun ω =>
      (Finset.add_sum_erase s (fun j => Y j ω) hi).symm
    have hRm : Measurable fun ω => ∑ j ∈ s.erase i, Y j ω :=
      Finset.measurable_sum _ fun j _ => hYm j
    have hRX : IndepFun (fun ω => ∑ j ∈ s.erase i, Y j ω) (Y i) μ := by
      have h := hind.indepFun_finsetSum_of_notMem hYm (Finset.notMem_erase i s)
      convert h using 1
      funext ω
      simp only [Finset.sum_apply]
    obtain ⟨hR4, hR2, -⟩ := moments_finsetSum_indep hind hYm hY4 hY0 hv hq (s.erase i)
    have hR0 : ∫ ω, ∑ j ∈ s.erase i, Y j ω ∂μ = 0 := by
      rw [integral_finsetSum _ fun j _ => hY1 j]
      simp [hY0]
    obtain ⟨hint, he⟩ := integral_sq_mul_add_sq_indep hRX hRm (hYm i) hR4 (hY4 i) hR0
    simp only [hsplit]
    refine ⟨hint, ?_⟩
    have hc : ((s.erase i).card : ℝ) = (s.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hi, Nat.cast_sub (Finset.card_pos.2 ⟨i, hi⟩)]
      push_cast
      ring
    rw [he, hq i, hv i, hR2, hc]
  have hfun : (fun ω => (∑ i ∈ s, Y i ω ^ 2) * (∑ i ∈ s, Y i ω) ^ 2) =
      fun ω => ∑ i ∈ s, Y i ω ^ 2 * (∑ j ∈ s, Y j ω) ^ 2 := by
    funext ω
    rw [Finset.sum_mul]
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i hi => (hterm i hi).1, ?_⟩
  rw [integral_finsetSum _ fun i hi => (hterm i hi).1,
    Finset.sum_congr rfl fun i hi => (hterm i hi).2, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The moment `E[Q²]`** (behind Giles 2015, §3.3, p. 23): for mutually independent measurable
`Y_i` with `E[Y_i²] = v` and `E[Y_i⁴] = q < ∞` and `Q = ∑_{i ∈ s} Y_i²`,
`E[Q²] = |s| q + |s|(|s| − 1) v²`: write `Q² = ∑_i Y_i² (Y_i² + ∑_{j ≠ i} Y_j²)`. -/
lemma integral_sumSq_sq [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (hind : iIndepFun Y μ)
    (hYm : ∀ i, Measurable (Y i)) (hY4 : ∀ i, Integrable (fun ω => Y i ω ^ 4) μ)
    {v q : ℝ} (hv : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = v) (hq : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ = q)
    (s : Finset ℕ) :
    Integrable (fun ω => (∑ i ∈ s, Y i ω ^ 2) ^ 2) μ ∧
      ∫ ω, (∑ i ∈ s, Y i ω ^ 2) ^ 2 ∂μ =
        s.card * q + (s.card : ℝ) * ((s.card : ℝ) - 1) * v ^ 2 := by
  have p2 : Measurable fun x : ℝ => x ^ 2 := (continuous_pow 2).measurable
  have hW : iIndepFun (fun i ω => Y i ω ^ 2) μ :=
    hind.comp (fun _ x => x ^ 2) (fun _ => p2)
  have hWm : ∀ i, Measurable fun ω => Y i ω ^ 2 := fun i => (hYm i).pow_const 2
  have hY2 : ∀ i, Integrable (fun ω => Y i ω ^ 2) μ := fun i =>
    integrable_pow_of_pow_four (hYm i) (hY4 i) (by norm_num)
  have hterm : ∀ i ∈ s, Integrable (fun ω => Y i ω ^ 2 * ∑ j ∈ s, Y j ω ^ 2) μ ∧
      ∫ ω, Y i ω ^ 2 * ∑ j ∈ s, Y j ω ^ 2 ∂μ = q + v * (((s.card : ℝ) - 1) * v) := by
    intro i hi
    have hsplit : ∀ ω, ∑ j ∈ s, Y j ω ^ 2 = Y i ω ^ 2 + ∑ j ∈ s.erase i, Y j ω ^ 2 := fun ω =>
      (Finset.add_sum_erase s (fun j => Y j ω ^ 2) hi).symm
    have hUW : IndepFun (fun ω => ∑ j ∈ s.erase i, Y j ω ^ 2) (fun ω => Y i ω ^ 2) μ := by
      have h := hW.indepFun_finsetSum_of_notMem hWm (Finset.notMem_erase i s)
      convert h using 1
      funext ω
      simp only [Finset.sum_apply]
    have hU : Integrable (fun ω => ∑ j ∈ s.erase i, Y j ω ^ 2) μ :=
      integrable_finsetSum _ fun j _ => hY2 j
    have i1 : Integrable (fun ω => Y i ω ^ 2 * ∑ j ∈ s.erase i, Y j ω ^ 2) μ :=
      hUW.symm.integrable_mul (hY2 i) hU
    have e1 : ∫ ω, Y i ω ^ 2 * ∑ j ∈ s.erase i, Y j ω ^ 2 ∂μ =
        (∫ ω, Y i ω ^ 2 ∂μ) * ∫ ω, ∑ j ∈ s.erase i, Y j ω ^ 2 ∂μ :=
      hUW.symm.integral_fun_mul_eq_mul_integral (hY2 i).aestronglyMeasurable
        hU.aestronglyMeasurable
    have h4 : ∀ ω, Y i ω ^ 2 * (Y i ω ^ 2 + ∑ j ∈ s.erase i, Y j ω ^ 2) =
        Y i ω ^ 4 + Y i ω ^ 2 * ∑ j ∈ s.erase i, Y j ω ^ 2 := fun ω => by ring
    simp only [hsplit, h4]
    refine ⟨(hY4 i).add i1, ?_⟩
    have hc : ((s.erase i).card : ℝ) = (s.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hi, Nat.cast_sub (Finset.card_pos.2 ⟨i, hi⟩)]
      push_cast
      ring
    rw [integral_add (hY4 i) i1, e1, integral_finsetSum _ fun j _ => hY2 j, hq i, hv i]
    simp only [hv, Finset.sum_const, nsmul_eq_mul, hc]
  have hfun : (fun ω => (∑ i ∈ s, Y i ω ^ 2) ^ 2) =
      fun ω => ∑ i ∈ s, Y i ω ^ 2 * ∑ j ∈ s, Y j ω ^ 2 := by
    funext ω
    rw [sq, Finset.sum_mul]
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i hi => (hterm i hi).1, ?_⟩
  rw [integral_finsetSum _ fun i hi => (hterm i hi).1,
    Finset.sum_congr rfl fun i hi => (hterm i hi).2, Finset.sum_const, nsmul_eq_mul]
  ring

end Moments

/-- The sum of squared deviations from the empirical mean in terms of any centre `c`:
`∑_{n<N} (x_n − x̄_N)² = ∑ (x_n − c)² − (∑ (x_n − c))²/N` for `N ≥ 1` (Giles 2015, §3.3, p. 23;
with `c` the true mean this is the decomposition `Q − T²/N` of the sample variance). -/
lemma sum_sub_empMean_sq (x : ℕ → ℝ) (c : ℝ) {N : ℕ} (hN : 0 < N) :
    ∑ n ∈ range N, (x n - empMean x N) ^ 2 =
      ∑ n ∈ range N, (x n - c) ^ 2 - (∑ n ∈ range N, (x n - c)) ^ 2 / N := by
  have hm : empMean x N = (∑ n ∈ range N, (x n - c)) / N + c := by
    rw [empMean, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
    field_simp
    ring
  have hx : ∀ n, x n - empMean x N = (x n - c) - (∑ k ∈ range N, (x k - c)) / N := fun n => by
    rw [hm]
    ring
  simp only [hx]
  have h := powerSum_variance_eq (fun n => x n - c) hN
  simp only at h
  field_simp at h ⊢
  linarith

section SampleVarMoments

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω}

/-- **The variance of the sample variance** (Giles 2015, §3.3, pp. 22–23, l. 1038–1042: "When the
number of samples `N` is large, the standard deviation of the sample variance for a random variable
`X` with zero mean is approximately `√((κ − 1)/N) E[X²]` where the kurtosis `κ` is defined as
`κ = E[X⁴]/(E[X²])²`.").  Let the inputs `ω⁽ⁿ⁾` be independent with law `ν` and let `X` be
measurable with `E[X⁴] < ∞`; write `σ² = V[X]` and `μ₄ = E[(X − E X)⁴]`.  For `N ≥ 2` samples
the unbiased sample variance `S_N² = (N − 1)⁻¹ ∑_{n<N} (X(ω⁽ⁿ⁾) − X̄_N)²` (`sampleVar`) satisfies
`E[S_N²] = σ²` and `V[S_N²] = (μ₄ − (N − 3)/(N − 1) σ⁴)/N`.  Proof: with `Y_n = X(ω⁽ⁿ⁾) − E X`,
`Q = ∑ Y_n²`, `T = ∑ Y_n`, `(N − 1) S_N² = Q − T²/N` (`sum_sub_empMean_sq`), and
`E[Q²] = E[QT²] = Nμ₄ + N(N − 1)σ⁴`, `E[T⁴] = Nμ₄ + 3N(N − 1)σ⁴` (`integral_sumSq_sq`,
`integral_sumSq_mul_sq`, `moments_finsetSum_indep`).  For the known-mean estimator
`N⁻¹ ∑ Y_n²` the variance is `(μ₄ − σ⁴)/N` (`sampleVariance_sd`); the extra term is
`2σ⁴/(N(N − 1))`. -/
theorem sampleVar_mean_variance [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {X : Ω₀ → ℝ}
    (hXm : Measurable X) (hX4 : Integrable (fun y => X y ^ 4) ν) {N : ℕ} (hN : 2 ≤ N) :
    μ[fun x => sampleVar (fun n => X (ω n x)) N] = variance X ν ∧
      variance (fun x => sampleVar (fun n => X (ω n x)) N) μ =
        (∫ y, (X y - ∫ z, X z ∂ν) ^ 4 ∂ν -
          ((N : ℝ) - 3) / ((N : ℝ) - 1) * variance X ν ^ 2) / N := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω 0).map_eq]
    exact Measure.isProbabilityMeasure_map (hω 0).measurable.aemeasurable
  set m := ∫ z, X z ∂ν with hm
  set q := ∫ y, (X y - m) ^ 4 ∂ν
  set v := variance X ν with hv
  -- the centred samples
  set Y : ℕ → Ω → ℝ := fun n x => X (ω n x) - m with hY
  have hXc4 : Integrable (fun y => (X y - m) ^ 4) ν := by
    refine Integrable.mono' ((hX4.add (integrable_const (m ^ 4))).const_mul 8)
      ((hXm.sub_const m).pow_const 4).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    show (X y - m) ^ 4 ≤ 8 * (X y ^ 4 + m ^ 4)
    nlinarith [sq_nonneg ((X y + m) ^ 2), sq_nonneg (X y ^ 2 - m ^ 2)]
  have hX1 : Integrable X ν := by
    simpa using integrable_pow_of_pow_four hXm hX4 (k := 1) (by norm_num)
  have hYind : iIndepFun Y μ := hind.comp (fun _ y => X y - m) (fun _ => hXm.sub_const m)
  have hYm : ∀ n, Measurable (Y n) := fun n => (hXm.sub_const m).comp (hω n).measurable
  have hY4 : ∀ n, Integrable (fun x => Y n x ^ 4) μ := fun n =>
    (hω n).integrable_comp_of_integrable hXc4
  have hY0 : ∀ n, ∫ x, Y n x ∂μ = 0 := fun n => by
    rw [hY, integral_comp_of_measurePreserving (hω n) (hXm.sub_const m).aestronglyMeasurable,
      integral_sub hX1 (integrable_const m), integral_const, probReal_univ, one_smul, hm,
      sub_self]
  have hYv : ∀ n, ∫ x, Y n x ^ 2 ∂μ = v := fun n => by
    rw [hY, integral_comp_of_measurePreserving (hω n)
      ((hXm.sub_const m).pow_const 2).aestronglyMeasurable, hv,
      variance_eq_integral hXm.aemeasurable]
  have hYq : ∀ n, ∫ x, Y n x ^ 4 ∂μ = q := fun n => by
    rw [hY, integral_comp_of_measurePreserving (hω n)
      ((hXm.sub_const m).pow_const 4).aestronglyMeasurable]
  -- the sample variance in terms of `Q = ∑ Y_n²` and `T = ∑ Y_n`
  have hN0 : 0 < N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hpt : (fun x => sampleVar (fun n => X (ω n x)) N) = fun x =>
      ((∑ n ∈ range N, Y n x ^ 2) - (∑ n ∈ range N, Y n x) ^ 2 / N) / ((N : ℝ) - 1) := by
    funext x
    rw [sampleVar, sum_sub_empMean_sq _ m hN0]
  obtain ⟨hT4, hT2, hT4e⟩ := moments_finsetSum_indep hYind hYm hY4 hY0 hYv hYq (range N)
  obtain ⟨hQT, hQTe⟩ := integral_sumSq_mul_sq hYind hYm hY4 hY0 hYv hYq (range N)
  obtain ⟨hQQ, hQQe⟩ := integral_sumSq_sq hYind hYm hY4 hYv hYq (range N)
  simp only [card_range] at hT2 hT4e hQTe hQQe
  have hTm : Measurable fun x => ∑ n ∈ range N, Y n x := Finset.measurable_sum _ fun n _ => hYm n
  have hQm : Measurable fun x => ∑ n ∈ range N, Y n x ^ 2 :=
    Finset.measurable_sum _ fun n _ => (hYm n).pow_const 2
  have hY2 : ∀ n, Integrable (fun x => Y n x ^ 2) μ := fun n =>
    integrable_pow_of_pow_four (hYm n) (hY4 n) (by norm_num)
  have hQ : Integrable (fun x => ∑ n ∈ range N, Y n x ^ 2) μ :=
    integrable_finsetSum _ fun n _ => hY2 n
  have hQe : ∫ x, ∑ n ∈ range N, Y n x ^ 2 ∂μ = N * v := by
    rw [integral_finsetSum _ fun n _ => hY2 n]
    simp [hYv]
  have hT2i : Integrable (fun x => (∑ n ∈ range N, Y n x) ^ 2) μ :=
    integrable_pow_of_pow_four hTm hT4 (by norm_num)
  -- integrability of the square of the sample variance
  have hsq : ∀ x, (((∑ n ∈ range N, Y n x ^ 2) - (∑ n ∈ range N, Y n x) ^ 2 / N) /
      ((N : ℝ) - 1)) ^ 2 = ((N : ℝ) - 1)⁻¹ ^ 2 * ((∑ n ∈ range N, Y n x ^ 2) ^ 2 -
        2 / N * ((∑ n ∈ range N, Y n x ^ 2) * (∑ n ∈ range N, Y n x) ^ 2) +
        1 / (N : ℝ) ^ 2 * (∑ n ∈ range N, Y n x) ^ 4) := fun x => by
    field_simp
    ring
  have hi1 : Integrable (fun x => (∑ n ∈ range N, Y n x ^ 2) ^ 2 -
      2 / N * ((∑ n ∈ range N, Y n x ^ 2) * (∑ n ∈ range N, Y n x) ^ 2)) μ :=
    hQQ.sub (hQT.const_mul _)
  have hi2 : Integrable (fun x => (∑ n ∈ range N, Y n x ^ 2) ^ 2 -
      2 / N * ((∑ n ∈ range N, Y n x ^ 2) * (∑ n ∈ range N, Y n x) ^ 2) +
      1 / (N : ℝ) ^ 2 * (∑ n ∈ range N, Y n x) ^ 4) μ := hi1.add (hT4.const_mul _)
  have hS2 : MemLp (fun x => ((∑ n ∈ range N, Y n x ^ 2) -
      (∑ n ∈ range N, Y n x) ^ 2 / N) / ((N : ℝ) - 1)) 2 μ := by
    refine (memLp_two_iff_integrable_sq ((hQm.sub (hTm.pow_const 2 |>.div_const _)).div_const
      _).aestronglyMeasurable).2 ?_
    exact (hi2.const_mul (((N : ℝ) - 1)⁻¹ ^ 2)).congr (ae_of_all _ fun x => (hsq x).symm)
  have hmean : ∫ x, ((∑ n ∈ range N, Y n x ^ 2) - (∑ n ∈ range N, Y n x) ^ 2 / N) /
      ((N : ℝ) - 1) ∂μ = v := by
    rw [integral_div, integral_sub hQ (hT2i.div_const _), integral_div, hQe, hT2]
    field_simp
  have hsecond : ∫ x, (((∑ n ∈ range N, Y n x ^ 2) - (∑ n ∈ range N, Y n x) ^ 2 / N) /
      ((N : ℝ) - 1)) ^ 2 ∂μ = ((N : ℝ) - 1)⁻¹ ^ 2 * ((N * q + N * (N - 1) * v ^ 2) -
        2 / N * (N * q + N * (N - 1) * v ^ 2) + 1 / (N : ℝ) ^ 2 *
          (N * q + 3 * N * (N - 1) * v ^ 2)) := by
    simp only [hsq]
    rw [integral_const_mul, integral_add hi1 (hT4.const_mul _), integral_sub hQQ (hQT.const_mul _),
      integral_const_mul, integral_const_mul, hQQe, hQTe, hT4e]
  rw [hpt]
  refine ⟨hmean, ?_⟩
  rw [variance_eq_sub hS2]
  simp only [Pi.pow_apply]
  rw [hsecond, hmean]
  field_simp
  ring

/-- **The standard deviation of the sample variance is `√((κ − 1)/N) σ² (1 + O(1/N))`** (Giles
2015, §3.3, pp. 22–23, l. 1038–1042: "When the number of samples `N` is large, the standard
deviation of the sample variance for a random variable `X` with zero mean is approximately
`√((κ − 1)/N) E[X²]` where the kurtosis `κ` is defined as `κ = E[X⁴]/(E[X²])²`.").  In the setting
of `sampleVar_mean_variance` (`N ≥ 2` independent samples of a measurable `X` with `E[X⁴] < ∞`, the
unbiased sample variance `S_N²`), let `κ = E[(X − E X)⁴]/V[X]²` be the central kurtosis
(`kurtosis` of `X − E X`; the paper's `κ` when `E[X] = 0`, and then `V[X] = E[X²]`), and assume
`κ > 1` (which forces `V[X] > 0`).  Then
`√V[S_N²] = √((κ − 1)/N + 2/(N(N − 1))) V[X]`, hence
`√((κ − 1)/N) V[X] ≤ √V[S_N²] ≤ √((κ − 1)/N) V[X] (1 + 1/((κ − 1)(N − 1)))`: the paper's
approximation with relative error at most `1/((κ − 1)(N − 1)) = O(1/N)`.  For `κ = 1`
(`X − E X = ±c`) the paper's approximation `0` is wrong in relative terms: the standard
deviation is `√(2/(N(N − 1))) V[X]`. -/
theorem sampleVar_sd [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {X : Ω₀ → ℝ}
    (hXm : Measurable X) (hX4 : Integrable (fun y => X y ^ 4) ν) {N : ℕ} (hN : 2 ≤ N)
    (hκ : 1 < kurtosis (fun y => X y - ∫ z, X z ∂ν) ν) :
    √(variance (fun x => sampleVar (fun n => X (ω n x)) N) μ) =
        √((kurtosis (fun y => X y - ∫ z, X z ∂ν) ν - 1) / N + 2 / (N * ((N : ℝ) - 1))) *
          variance X ν ∧
      √((kurtosis (fun y => X y - ∫ z, X z ∂ν) ν - 1) / N) * variance X ν ≤
        √(variance (fun x => sampleVar (fun n => X (ω n x)) N) μ) ∧
      √(variance (fun x => sampleVar (fun n => X (ω n x)) N) μ) ≤
        √((kurtosis (fun y => X y - ∫ z, X z ∂ν) ν - 1) / N) * variance X ν *
          (1 + 1 / ((kurtosis (fun y => X y - ∫ z, X z ∂ν) ν - 1) * ((N : ℝ) - 1))) := by
  have hvar := (sampleVar_mean_variance ω hω hind hXm hX4 hN).2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set κ := kurtosis (fun y => X y - ∫ z, X z ∂ν) ν with hκdef
  set v := variance X ν with hv
  set q := ∫ y, (X y - ∫ z, X z ∂ν) ^ 4 ∂ν
  have hκq : κ = q / v ^ 2 := by
    rw [hκdef, kurtosis, hv, variance_eq_integral hXm.aemeasurable]
  have hv0 : v ≠ 0 := by
    intro h
    rw [hκq, h] at hκ
    norm_num at hκ
  have hvpos : 0 < v := lt_of_le_of_ne (variance_nonneg X ν) (Ne.symm hv0)
  have hqκ : q = κ * v ^ 2 := by
    rw [hκq]
    field_simp
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  have hVe : variance (fun x => sampleVar (fun n => X (ω n x)) N) μ =
      ((κ - 1) / N + 2 / (N * ((N : ℝ) - 1))) * v ^ 2 := by
    rw [hvar, hqκ]
    field_simp
    ring
  have hκ1 : 0 < κ - 1 := by linarith
  have hexact : √(variance (fun x => sampleVar (fun n => X (ω n x)) N) μ) =
      √((κ - 1) / N + 2 / (N * ((N : ℝ) - 1))) * v := by
    rw [hVe, Real.sqrt_mul (by positivity), Real.sqrt_sq hvpos.le]
  refine ⟨hexact, ?_, ?_⟩
  · rw [hexact]
    gcongr
    have : 0 ≤ 2 / ((N : ℝ) * ((N : ℝ) - 1)) := by positivity
    linarith
  · rw [hexact, mul_right_comm]
    gcongr
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + 1 / ((κ - 1) * ((N : ℝ) - 1))),
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have e : (κ - 1) / N * (1 + 1 / ((κ - 1) * ((N : ℝ) - 1))) ^ 2 =
        (κ - 1) / N + 2 / (N * ((N : ℝ) - 1)) + 1 / (N * (κ - 1) * ((N : ℝ) - 1) ^ 2) := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ 1 / ((N : ℝ) * (κ - 1) * ((N : ℝ) - 1) ^ 2) := by positivity
    linarith

/-- **"Approximately `√((κ − 1)/N) E[X²]`" as a limit** (Giles 2015, §3.3, pp. 22–23, l. 1038–1042:
"When the number of samples `N` is large, the standard deviation of the sample variance for a random
variable `X` with zero mean is approximately `√((κ − 1)/N) E[X²]`").  In the setting of
`sampleVar_sd` (independent samples of a measurable `X` with `E[X⁴] < ∞`, central kurtosis
`κ > 1`), the ratio of the standard deviation of the unbiased sample variance `S_N²` to
`√((κ − 1)/N) V[X]` tends to `1` as `N → ∞` (it lies between `1` and
`1 + 1/((κ − 1)(N − 1))` for `N ≥ 2`). -/
theorem tendsto_sampleVar_sd_div [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {X : Ω₀ → ℝ}
    (hXm : Measurable X) (hX4 : Integrable (fun y => X y ^ 4) ν)
    (hκ : 1 < kurtosis (fun y => X y - ∫ z, X z ∂ν) ν) :
    Tendsto (fun N : ℕ => √(variance (fun x => sampleVar (fun n => X (ω n x)) N) μ) /
      (√((kurtosis (fun y => X y - ∫ z, X z ∂ν) ν - 1) / N) * variance X ν)) atTop (𝓝 1) := by
  set κ := kurtosis (fun y => X y - ∫ z, X z ∂ν) ν with hκdef
  have hκ1 : 0 < κ - 1 := by linarith
  have hvpos : 0 < variance X ν := by
    rcases (variance_nonneg X ν).lt_or_eq with hv | hv
    · exact hv
    · exfalso
      have hκq : κ = (∫ y, (X y - ∫ z, X z ∂ν) ^ 4 ∂ν) / variance X ν ^ 2 := by
        rw [hκdef, kurtosis, variance_eq_integral hXm.aemeasurable]
      rw [hκq, ← hv] at hκ
      norm_num at hκ
  have hlim : Tendsto (fun N : ℕ => 1 + 1 / ((κ - 1) * ((N : ℝ) - 1))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => (κ - 1) * ((N : ℝ) - 1)) atTop atTop :=
      Tendsto.const_mul_atTop hκ1 (tendsto_atTop_add_const_right _ (-1)
        tendsto_natCast_atTop_atTop)
    have h2 := (tendsto_inv_atTop_zero.comp h1).const_add 1
    rw [add_zero] at h2
    refine h2.congr fun N => ?_
    simp only [Function.comp_apply, one_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    obtain ⟨-, hlow, -⟩ := sampleVar_sd ω hω hind hXm hX4 hN hκ
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hd : 0 < √((κ - 1) / N) * variance X ν :=
      mul_pos (Real.sqrt_pos.2 (div_pos hκ1 (by linarith))) hvpos
    rw [le_div_iff₀ hd, one_mul]
    exact hlow
  · filter_upwards [eventually_ge_atTop 2] with N hN
    obtain ⟨-, -, hup⟩ := sampleVar_sd ω hω hind hXm hX4 hN hκ
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hd : 0 < √((κ - 1) / N) * variance X ν :=
      mul_pos (Real.sqrt_pos.2 (div_pos hκ1 (by linarith))) hvpos
    rw [div_le_iff₀ hd, mul_comm]
    exact hup

end SampleVarMoments

end MLMC
