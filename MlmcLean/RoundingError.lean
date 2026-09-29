import MlmcLean.ErrorAnalysis
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The rounding-error model of Haas and Giles (2025, §4)

Reference: I.-B. Haas and M.B. Giles, *A nested MLMC framework for efficient simulations on
FPGAs*, arXiv:2502.07123 (2025), §4 (pp. 8–10).

In fixed-point arithmetic with exponent `e` and bit-width `d` a number is stored as
`x̃ = (−1)^s 2^{e−d} n` with `0 ≤ n < 2^d`; rounding to nearest gives the error `δx = x − x̃`.

* **(20)** `|δx| ≤ 2^{e−d−1}` (`abs_sub_roundFixed_le`; `roundFixed_mantissa` checks that the
  rounded value has the fixed-point format when there is no overflow).
* **(21)** "Without making any assumption on the distribution of the errors we then have that
  `E[δx²] = 4^{e−d−1}`": this must read `≤` (`integral_sq_roundError_le`).
* **(22)** If `δx` is uniform on `[−2^{e−d−1}, 2^{e−d−1}]` then `E[δx²] = 4^{e−d}/12`
  (`integral_sq_of_isUniform`, `integral_sq_uniform_roundError`).
* **(25)** `V[P − P̃] = ∑_i V[x̄_i δx_i] + 2 ∑_{i≠j} Cov(x̄_i δx_i, x̄_j δx_j)` for the
  linearised error `P − P̃ ≈ ∑_i x̄_i δx_i`: correct when `∑_{i≠j}` runs over unordered pairs
  `{i, j}` (the reading the paper's (27) uses); over ordered pairs the factor 2 must go
  (`variance_sum_eq` sums over ordered pairs `i ≠ j`, with no factor 2).
* "It always holds that `V[x̄_i δx_i] ≤ E[x̄_i² δx_i²]`" (`variance_le_integral_sq`).
* **(26)** With independent errors, sensitivities independent of the rounding errors and (22),
  `V[P − P̃] ≤ (1/12) ∑_i E[x̄_i²] 4^{e_i−d_i} ≜ V_indep` (`variance_linearised_indep`, from the
  general `variance_sum_mul_le_of_indep`).
* **(27)** `V[P − P̃] ≤ (∑_i √E[x̄_i²] 2^{e_i−d_i−1})² ≜ V_corr`; the paper derives it assuming
  perfect correlation, but it holds with no assumption on the joint law of the errors
  (`variance_linearised_corr`, from `variance_sum_le_sq_sum_sqrt`).
* "(26) … is tighter than (27)": `V_indep ≤ V_corr` (`vIndep_le_vCorr`).
* **(28), (29)** The extended bounds with approximate normal increments `Z̃_j` and
  `MSE = E[|Z_j − Z̃_j|²]`: (29) holds as printed (`variance_extended_corr`); in (28) the factor
  `1/12` on the MSE term does not follow — the bound is
  `V_indep + ∑_j E[Z̄_j²] · MSE` (`variance_extended_indep`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### Fixed-point rounding (§4.1) -/

/-- Round-to-nearest onto the fixed-point grid `2^{e−d} ℤ` (Haas–Giles 2025, §4.1): the number
`2^{e−d} n`, `n ∈ ℤ`, nearest to `x`, for the exponent `e` and the bit-width `d`.  The paper says
"round-to-nearest" without a tie rule; a tie (`x` halfway between two grid points) is rounded
upwards here, as Mathlib's `round` does. -/
noncomputable def roundFixed (e : ℤ) (d : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ (e - d) * round (x / (2 : ℝ) ^ (e - d))

lemma two_zpow_sq (k : ℤ) : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
  rw [sq, ← mul_zpow]
  norm_num

/-- **Haas–Giles (20)** (2025, §4.1, p. 8): rounding to nearest in fixed point with exponent `e`
and bit-width `d` makes an error `|δx| = |x − x̃| ≤ 2^{e−d−1}`. -/
theorem abs_sub_roundFixed_le (e : ℤ) (d : ℕ) (x : ℝ) :
    |x - roundFixed e d x| ≤ (2 : ℝ) ^ (e - d - 1) := by
  have hq : (0 : ℝ) < 2 ^ (e - d) := zpow_pos two_pos _
  have h := abs_sub_round (x / (2 : ℝ) ^ (e - d))
  have e1 : x - roundFixed e d x =
      2 ^ (e - d) * (x / 2 ^ (e - d) - round (x / (2 : ℝ) ^ (e - d))) := by
    rw [roundFixed, mul_sub, mul_div_cancel₀ x hq.ne']
  have e2 : (2 : ℝ) ^ (e - d - 1) = 2 ^ (e - d) * (1 / 2) := by
    rw [zpow_sub₀ two_ne_zero (e - d) 1, zpow_one, div_eq_mul_one_div]
  rw [e1, abs_mul, abs_of_pos hq, e2]
  exact mul_le_mul_of_nonneg_left h hq.le

/-- **The fixed-point format** (Haas–Giles 2025, §4.1, p. 8): "The fixed-point equivalent of
variable `x_i` is defined as `x̃_i = (−1)^s 2^{e_i−d_i} n`, where `n` is a non negative integer
smaller than `2^{d_i}`."  If `|x| < 2^e − 2^{e−d−1}` (no overflow), the rounded value is
`2^{e−d} k` with an integer `|k| < 2^d`. -/
theorem roundFixed_mantissa (e : ℤ) (d : ℕ) {x : ℝ}
    (hx : |x| < (2 : ℝ) ^ e - (2 : ℝ) ^ (e - d - 1)) :
    ∃ k : ℤ, |k| < 2 ^ d ∧ roundFixed e d x = (2 : ℝ) ^ (e - d) * k := by
  have hq : (0 : ℝ) < 2 ^ (e - d) := zpow_pos two_pos _
  refine ⟨round (x / (2 : ℝ) ^ (e - d)), ?_, rfl⟩
  have h1 := abs_sub_round (x / (2 : ℝ) ^ (e - d))
  have h2e : (2 : ℝ) ^ e = 2 ^ (e - d) * 2 ^ d := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, sub_add_cancel]
  have h2h : (2 : ℝ) ^ (e - d - 1) = 2 ^ (e - d) / 2 := by
    rw [zpow_sub₀ two_ne_zero (e - d) 1, zpow_one]
  rw [h2e, h2h] at hx
  have hxq : |x / (2 : ℝ) ^ (e - d)| < 2 ^ d - 1 / 2 := by
    rw [abs_div, abs_of_pos hq, div_lt_iff₀ hq]
    linarith
  have h3 := abs_sub_abs_le_abs_sub (round (x / (2 : ℝ) ^ (e - d)) : ℝ) (x / 2 ^ (e - d))
  rw [abs_sub_comm] at h3
  have h4 : |(round (x / (2 : ℝ) ^ (e - d)) : ℝ)| < 2 ^ d := by linarith
  exact_mod_cast h4

section moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A random variable bounded by `B` almost surely has second moment at most `B²`. -/
lemma integral_sq_le_of_abs_le [IsProbabilityMeasure μ] {δ : Ω → ℝ} {B : ℝ}
    (hδ : ∀ᵐ ω ∂μ, |δ ω| ≤ B) : ∫ ω, δ ω ^ 2 ∂μ ≤ B ^ 2 := by
  by_cases hint : Integrable (fun ω => δ ω ^ 2) μ
  · have hle : ∀ᵐ ω ∂μ, δ ω ^ 2 ≤ B ^ 2 := hδ.mono fun ω h => by
      rw [← sq_abs (δ ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc ∫ ω, δ ω ^ 2 ∂μ ≤ ∫ _, B ^ 2 ∂μ := integral_mono_ae hint (integrable_const _) hle
      _ = B ^ 2 := by simp
  · rw [integral_undef hint]
    positivity

/-- **Haas–Giles (21)**, corrected (2025, §4.1, p. 8): "Without making any assumption on the
distribution of the errors we then have that `E[δx_i²] = 4^{e_i−d_i−1}`."  The equality must read
`≤`: for any random input `X` the rounding error `δ = X − x̃` satisfies
`E[δ²] ≤ 4^{e−d−1}`, whatever the law of `X`. -/
theorem integral_sq_roundError_le [IsProbabilityMeasure μ] (e : ℤ) (d : ℕ) (X : Ω → ℝ) :
    ∫ ω, (X ω - roundFixed e d (X ω)) ^ 2 ∂μ ≤ (4 : ℝ) ^ (e - d - 1) := by
  have h := integral_sq_le_of_abs_le (μ := μ) (δ := fun ω => X ω - roundFixed e d (X ω))
    (B := (2 : ℝ) ^ (e - d - 1)) (Filter.Eventually.of_forall fun ω =>
      abs_sub_roundFixed_le e d (X ω))
  rw [two_zpow_sq] at h
  exact h

-- `[−a, a]` has Lebesgue measure `2a`, which is positive and finite
lemma volume_Icc_neg_facts {a : ℝ} (ha : 0 < a) :
    volume (Set.Icc (-a) a) = ENNReal.ofReal (2 * a) ∧ volume (Set.Icc (-a) a) ≠ 0 ∧
      volume (Set.Icc (-a) a) ≠ ⊤ := by
  have hvol : volume (Set.Icc (-a) a) = ENNReal.ofReal (2 * a) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  refine ⟨hvol, ?_, ?_⟩
  · rw [hvol]
    exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  · rw [hvol]
    exact ENNReal.ofReal_ne_top

/-- The second moment of a uniform distribution: if `X` is uniform on `[−a, a]` (`a > 0`), then
`E[X²] = a²/3` (the step behind Haas–Giles (22)). -/
theorem integral_sq_of_isUniform {X : Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (hX : pdf.IsUniform X (Set.Icc (-a) a) μ) : ∫ ω, X ω ^ 2 ∂μ = a ^ 2 / 3 := by
  obtain ⟨hvol, hns, hnt⟩ := volume_Icc_neg_facts ha
  have hXm : AEMeasurable X μ := hX.aemeasurable hns hnt
  have hX' : μ.map X = ProbabilityTheory.cond volume (Set.Icc (-a) a) := hX
  have hmap : ∫ ω, X ω ^ 2 ∂μ = ∫ x, x ^ 2 ∂(μ.map X) :=
    (integral_map hXm (continuous_pow 2).aestronglyMeasurable).symm
  have key : (2 * a)⁻¹ * ((a ^ (2 + 1) - (-a) ^ (2 + 1)) / ((2 : ℕ) + 1 : ℝ)) = a ^ 2 / 3 := by
    have h2a : (2 * a) ≠ 0 := by positivity
    have e3 : (a ^ (2 + 1) - (-a) ^ (2 + 1)) / ((2 : ℕ) + 1 : ℝ) = (2 * a) * (a ^ 2 / 3) := by
      push_cast
      ring
    rw [e3, ← mul_assoc, inv_mul_cancel₀ h2a, one_mul]
  rw [hmap, hX', ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, hvol,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith)]
  exact key

/-- **Haas–Giles (22)** (2025, §4.1, p. 8): "If additionally we assume that the rounding errors
`δx_i` are uniform variables over `[−2^{e_i−d_i−1}, 2^{e_i−d_i−1}]` we get the expected squared
rounding error `E[δx_i²] = 4^{e_i−d_i}/12`." -/
theorem integral_sq_uniform_roundError {δ : Ω → ℝ} (e : ℤ) (d : ℕ)
    (hδ : pdf.IsUniform δ (Set.Icc (-(2 : ℝ) ^ (e - d - 1)) ((2 : ℝ) ^ (e - d - 1))) μ) :
    ∫ ω, δ ω ^ 2 ∂μ = (4 : ℝ) ^ (e - d) / 12 := by
  rw [integral_sq_of_isUniform (zpow_pos two_pos _) hδ, two_zpow_sq,
    zpow_sub₀ (by norm_num : (4 : ℝ) ≠ 0) (e - d) 1, zpow_one]
  ring

-- a uniform variable on `[−a, a]` is a.e. strongly measurable and bounded by `a` almost surely
lemma isUniform_Icc_facts {δ : Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (hδ : pdf.IsUniform δ (Set.Icc (-a) a) μ) :
    AEStronglyMeasurable δ μ ∧ ∀ᵐ ω ∂μ, |δ ω| ≤ a := by
  obtain ⟨-, hns, hnt⟩ := volume_Icc_neg_facts ha
  have h0 : μ (δ ⁻¹' (Set.Icc (-a) a)ᶜ) = 0 := by
    rw [hδ.measure_preimage hns hnt measurableSet_Icc.compl, Set.inter_compl_self,
      measure_empty, ENNReal.zero_div]
  have hmem : ∀ᵐ ω ∂μ, δ ω ∈ Set.Icc (-a) a := ae_iff.2 h0
  exact ⟨(hδ.aemeasurable hns hnt).aestronglyMeasurable,
    hmem.mono fun ω hω => abs_le.2 ⟨hω.1, hω.2⟩⟩

-- a square-integrable variable times an a.s. bounded one is square-integrable
lemma memLp_mul_of_bound {X δ : Ω → ℝ} {B : ℝ} (hX : MemLp X 2 μ)
    (hδm : AEStronglyMeasurable δ μ) (hδ : ∀ᵐ ω ∂μ, |δ ω| ≤ B) :
    MemLp (fun ω => X ω * δ ω) 2 μ :=
  hX.of_le_mul (c := B) (hX.1.mul hδm) (hδ.mono fun ω h => by
    show |X ω * δ ω| ≤ B * |X ω|
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg _))

end moments

/-! ### The variance of the linearised rounding error (§4.2) -/

/-- `V_indep(d₁, …, d_m) = (1/12) ∑_i M_i 4^{e_i−d_i}` (Haas–Giles 2025, (26)), where
`M_i = E[x̄_i²]` is the mean-square sensitivity of the output to the variable `x_i`, `e_i` its
exponent and `d_i` its bit-width. -/
noncomputable def vIndep {ι : Type*} (s : Finset ι) (M : ι → ℝ) (e : ι → ℤ) (d : ι → ℕ) : ℝ :=
  (1 / 12) * ∑ i ∈ s, M i * (4 : ℝ) ^ (e i - d i)

/-- `V_corr(d₁, …, d_m) = (∑_i √M_i 2^{e_i−d_i−1})²` (Haas–Giles 2025, (27)), with
`M_i = E[x̄_i²]`. -/
noncomputable def vCorr {ι : Type*} (s : Finset ι) (M : ι → ℝ) (e : ι → ℤ) (d : ι → ℕ) : ℝ :=
  (∑ i ∈ s, Real.sqrt (M i) * (2 : ℝ) ^ (e i - d i - 1)) ^ 2

section variance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Haas–Giles (25)**, corrected (2025, §4.2, p. 9): the variance of the linearised error
`∑_i X_i` (with `X_i = x̄_i δx_i`) is `∑_i V[X_i] + ∑_{i ≠ j} Cov(X_i, X_j)`, the sum over
ordered pairs `i ≠ j`.  The printed (25) has `2 ∑_{i≠j}`: this is correct when the sum runs over
unordered pairs `{i, j}` (equivalently `2 ∑_{i<j}`), the reading behind the paper's (27), but
counts every covariance twice if the pairs are ordered; the notation is ambiguous. -/
theorem variance_sum_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) {X : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    variance (fun ω => ∑ i ∈ s, X i ω) μ =
      ∑ i ∈ s, variance (X i) μ + ∑ i ∈ s, ∑ j ∈ s.erase i, covariance (X i) (X j) μ := by
  rw [variance_fun_sum' hX, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.add_sum_erase s _ hi, covariance_self (hX i hi).aemeasurable]

/-- Haas–Giles (2025, §4.2, p. 9): "It always holds that `V[x̄_i δx_i] ≤ E[x̄_i² δx_i²]`." -/
theorem variance_le_integral_sq {xbar δ : Ω → ℝ} (hxbar : AEStronglyMeasurable xbar μ)
    (hδ : AEStronglyMeasurable δ μ) :
    variance (fun ω => xbar ω * δ ω) μ ≤ ∫ ω, xbar ω ^ 2 * δ ω ^ 2 ∂μ := by
  have h := variance_le_expectation_sq (hxbar.mul hδ)
  simp only [Pi.pow_apply, Pi.mul_apply, mul_pow] at h
  exact h

/-- **The independent-errors bound behind Haas–Giles (26) and (28)** (2025, §4.2–4.3): if the
terms `s_k ε_k` (sensitivity times error) are square-integrable and pairwise independent, and each
`s_k` is independent of `ε_k`, then `V[∑_k s_k ε_k] ≤ ∑_k E[s_k²] E[ε_k²]`. -/
theorem variance_sum_mul_le_of_indep {ι : Type*} (s : Finset ι) (sens err : ι → Ω → ℝ)
    (hY : ∀ i ∈ s, MemLp (fun ω => sens i ω * err i ω) 2 μ)
    (hsm : ∀ i ∈ s, AEStronglyMeasurable (sens i) μ)
    (hem : ∀ i ∈ s, AEStronglyMeasurable (err i) μ)
    (hind_i : ∀ i ∈ s, IndepFun (sens i) (err i) μ)
    (hind : Set.Pairwise ↑s fun i j =>
      IndepFun (fun ω => sens i ω * err i ω) (fun ω => sens j ω * err j ω) μ) :
    variance (fun ω => ∑ i ∈ s, sens i ω * err i ω) μ ≤
      ∑ i ∈ s, (∫ ω, sens i ω ^ 2 ∂μ) * ∫ ω, err i ω ^ 2 ∂μ := by
  have hsum : (fun ω => ∑ i ∈ s, sens i ω * err i ω) = ∑ i ∈ s, fun ω => sens i ω * err i ω := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hsum, IndepFun.variance_sum hY hind]
  refine Finset.sum_le_sum fun i hi => ?_
  have hind2 : IndepFun (fun ω => sens i ω ^ 2) (fun ω => err i ω ^ 2) μ :=
    (hind_i i hi).comp (continuous_pow 2).measurable (continuous_pow 2).measurable
  have hmul := hind2.integral_mul_eq_mul_integral ((hsm i hi).pow 2) ((hem i hi).pow 2)
  calc variance (fun ω => sens i ω * err i ω) μ
      ≤ ∫ ω, sens i ω ^ 2 * err i ω ^ 2 ∂μ := variance_le_integral_sq (hsm i hi) (hem i hi)
    _ = (∫ ω, sens i ω ^ 2 ∂μ) * ∫ ω, err i ω ^ 2 ∂μ := hmul

/-- **Haas–Giles (26)** (2025, §4.2, p. 9): if the sensitivities `x̄_i` and the rounding errors
`δx_i` are independent, the individual errors `x̄_i δx_i` are (pairwise) independent, and each
`δx_i` is uniform on `[−2^{e_i−d_i−1}, 2^{e_i−d_i−1}]` (22), then the variance of the linearised
error satisfies `V[∑_i x̄_i δx_i] ≤ (1/12) ∑_i E[x̄_i²] 4^{e_i−d_i} = V_indep`. -/
theorem variance_linearised_indep {ι : Type*} (s : Finset ι) (xbar δ : ι → Ω → ℝ)
    (e : ι → ℤ) (d : ι → ℕ) (hxbar : ∀ i ∈ s, MemLp (xbar i) 2 μ)
    (hδ : ∀ i ∈ s, pdf.IsUniform (δ i)
      (Set.Icc (-(2 : ℝ) ^ (e i - d i - 1)) ((2 : ℝ) ^ (e i - d i - 1))) μ)
    (hind_i : ∀ i ∈ s, IndepFun (xbar i) (δ i) μ)
    (hind : Set.Pairwise ↑s fun i j =>
      IndepFun (fun ω => xbar i ω * δ i ω) (fun ω => xbar j ω * δ j ω) μ) :
    variance (fun ω => ∑ i ∈ s, xbar i ω * δ i ω) μ ≤
      vIndep s (fun i => ∫ ω, xbar i ω ^ 2 ∂μ) e d := by
  have hfacts : ∀ i ∈ s, AEStronglyMeasurable (δ i) μ ∧
      ∀ᵐ ω ∂μ, |δ i ω| ≤ (2 : ℝ) ^ (e i - d i - 1) :=
    fun i hi => isUniform_Icc_facts (zpow_pos two_pos _) (hδ i hi)
  have hY : ∀ i ∈ s, MemLp (fun ω => xbar i ω * δ i ω) 2 μ := fun i hi =>
    memLp_mul_of_bound (hxbar i hi) (hfacts i hi).1 (hfacts i hi).2
  refine (variance_sum_mul_le_of_indep s xbar δ hY (fun i hi => (hxbar i hi).1)
    (fun i hi => (hfacts i hi).1) hind_i hind).trans (le_of_eq ?_)
  rw [vIndep, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_sq_uniform_roundError (e i) (d i) (hδ i hi)]
  ring

/-- **The variance of a sum is at most the square of the sum of the standard deviations**, with no
assumption on the joint law: `V[∑_i Y_i] ≤ (∑_i √V[Y_i])²` (the bound behind Haas–Giles (27) and
(29), which the paper derives by assuming perfectly correlated errors). -/
theorem variance_sum_le_sq_sum_sqrt {ι : Type*} (s : Finset ι) {Y : ι → Ω → ℝ}
    (hY : ∀ i ∈ s, MemLp (Y i) 2 μ) :
    variance (fun ω => ∑ i ∈ s, Y i ω) μ ≤ (∑ i ∈ s, Real.sqrt (variance (Y i) μ)) ^ 2 := by
  rw [variance_fun_sum' hY, sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
  rw [← Real.sqrt_mul (variance_nonneg _ _)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (covariance_sq_le (hY i hi) (hY j hj)))

/-- **The term bound behind Haas–Giles (27)** (2025, §4.2, p. 9): if `x̄` is square-integrable and
`|δ| ≤ B` almost surely, then `V[x̄ δ] ≤ E[x̄² δ²] ≤ E[x̄²] B²`, i.e. `√V[x̄ δ] ≤ √E[x̄²] · B`; with
`B = 2^{e−d−1}` from (20) this is the `i`-th term of `V_corr`. -/
theorem sqrt_variance_mul_le {xbar δ : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B) (hxbar : MemLp xbar 2 μ)
    (hδm : AEStronglyMeasurable δ μ) (hδ : ∀ᵐ ω ∂μ, |δ ω| ≤ B) :
    Real.sqrt (variance (fun ω => xbar ω * δ ω) μ) ≤ Real.sqrt (∫ ω, xbar ω ^ 2 ∂μ) * B := by
  have hY := memLp_mul_of_bound hxbar hδm hδ
  have h1 := variance_le_integral_sq (μ := μ) hxbar.1 hδm
  have h2 : ∫ ω, xbar ω ^ 2 * δ ω ^ 2 ∂μ ≤ (∫ ω, xbar ω ^ 2 ∂μ) * B ^ 2 := by
    rw [← integral_mul_const]
    have hint : Integrable (fun ω => xbar ω ^ 2 * δ ω ^ 2) μ := by
      have h := hY.integrable_sq
      simp only [mul_pow] at h
      exact h
    refine integral_mono_ae hint (hxbar.integrable_sq.mul_const _) ?_
    filter_upwards [hδ] with ω hω
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [← sq_abs (δ ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  calc Real.sqrt (variance (fun ω => xbar ω * δ ω) μ)
      ≤ Real.sqrt ((∫ ω, xbar ω ^ 2 ∂μ) * B ^ 2) := Real.sqrt_le_sqrt (h1.trans h2)
    _ = Real.sqrt (∫ ω, xbar ω ^ 2 ∂μ) * B := by
        rw [Real.sqrt_mul (integral_nonneg fun ω => sq_nonneg _), Real.sqrt_sq hB]

/-- **Haas–Giles (27)** (2025, §4.2, p. 9): if every rounding error satisfies (20),
`|δx_i| ≤ 2^{e_i−d_i−1}` almost surely, then the variance of the linearised error satisfies
`V[∑_i x̄_i δx_i] ≤ (∑_i √E[x̄_i²] 2^{e_i−d_i−1})² = V_corr`.  The paper derives this "pessimistic"
bound by assuming perfectly correlated errors; it holds without any assumption on the joint law
of the sensitivities and the errors. -/
theorem variance_linearised_corr {ι : Type*} (s : Finset ι) (xbar δ : ι → Ω → ℝ)
    (e : ι → ℤ) (d : ι → ℕ) (hxbar : ∀ i ∈ s, MemLp (xbar i) 2 μ)
    (hδm : ∀ i ∈ s, AEStronglyMeasurable (δ i) μ)
    (hδ : ∀ i ∈ s, ∀ᵐ ω ∂μ, |δ i ω| ≤ (2 : ℝ) ^ (e i - d i - 1)) :
    variance (fun ω => ∑ i ∈ s, xbar i ω * δ i ω) μ ≤
      vCorr s (fun i => ∫ ω, xbar i ω ^ 2 ∂μ) e d := by
  have hY : ∀ i ∈ s, MemLp (fun ω => xbar i ω * δ i ω) 2 μ := fun i hi =>
    memLp_mul_of_bound (hxbar i hi) (hδm i hi) (hδ i hi)
  refine (variance_sum_le_sq_sum_sqrt s hY).trans ?_
  rw [vCorr]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _)
    (Finset.sum_le_sum fun i hi => sqrt_variance_mul_le (zpow_pos two_pos _).le (hxbar i hi)
      (hδm i hi) (hδ i hi)) 2

/-- **"(26) … is tighter than (27)"** (Haas–Giles 2025, §4.4, p. 10): for nonnegative mean-square
sensitivities `M_i`, `V_indep ≤ V_corr`. -/
theorem vIndep_le_vCorr {ι : Type*} (s : Finset ι) {M : ι → ℝ} (hM : ∀ i ∈ s, 0 ≤ M i)
    (e : ι → ℤ) (d : ι → ℕ) : vIndep s M e d ≤ vCorr s M e d := by
  rw [vIndep, vCorr]
  have hb0 : ∀ i ∈ s, 0 ≤ Real.sqrt (M i) * (2 : ℝ) ^ (e i - d i - 1) :=
    fun i _ => mul_nonneg (Real.sqrt_nonneg _) (zpow_pos two_pos _).le
  have hterm : ∀ i ∈ s, M i * (4 : ℝ) ^ (e i - d i) =
      4 * (Real.sqrt (M i) * (2 : ℝ) ^ (e i - d i - 1)) ^ 2 := fun i hi => by
    rw [mul_pow, Real.sq_sqrt (hM i hi), two_zpow_sq,
      zpow_sub₀ (by norm_num : (4 : ℝ) ≠ 0) (e i - d i) 1, zpow_one]
    ring
  have hsq : ∑ i ∈ s, (Real.sqrt (M i) * (2 : ℝ) ^ (e i - d i - 1)) ^ 2 ≤
      (∑ i ∈ s, Real.sqrt (M i) * (2 : ℝ) ^ (e i - d i - 1)) ^ 2 := by
    rw [sq (∑ i ∈ s, Real.sqrt (M i) * (2 : ℝ) ^ (e i - d i - 1)), Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [sq]
    exact Finset.single_le_sum
      (f := fun j => Real.sqrt (M i) * (2 : ℝ) ^ (e i - d i - 1) *
        (Real.sqrt (M j) * (2 : ℝ) ^ (e j - d j - 1)))
      (fun j hj => mul_nonneg (hb0 i hi) (hb0 j hj)) hi
  have h0 : 0 ≤ ∑ i ∈ s, (Real.sqrt (M i) * (2 : ℝ) ^ (e i - d i - 1)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  linarith

/-! ### Approximate normal increments (§4.3) -/

/-- **Haas–Giles (28)**, corrected (2025, §4.3, p. 9): with rounding errors `δx_i` as in (26) and,
in addition, the errors `δZ_j = Z_j − Z̃_j` of approximate normal increments with sensitivities
`Z̄_j = ∂P/∂Z_j` and `MSE = E[|Z_j − Z̃_j|²]`, all terms `x̄_i δx_i`, `Z̄_j δZ_j` pairwise
independent and every sensitivity independent of its error,
`V[∑_i x̄_i δx_i + ∑_j Z̄_j δZ_j] ≤ V_indep + ∑_j E[Z̄_j²] · MSE`.  The paper's (28) has
`(1/12) ∑_j E[Z̄_j²] · MSE`; the `1/12` belongs to the uniform model (22) of the rounding errors
and does not apply to `MSE`. -/
theorem variance_extended_indep {ι κ : Type*} (s : Finset ι) (t : Finset κ)
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
        (fun ω => Sum.elim xbar zbar b ω * Sum.elim δ δZ b ω) μ) :
    variance (fun ω => ∑ i ∈ s, xbar i ω * δ i ω + ∑ j ∈ t, zbar j ω * δZ j ω) μ ≤
      vIndep s (fun i => ∫ ω, xbar i ω ^ 2 ∂μ) e d + (∑ j ∈ t, ∫ ω, zbar j ω ^ 2 ∂μ) * mse := by
  have hfacts : ∀ i ∈ s, AEStronglyMeasurable (δ i) μ ∧
      ∀ᵐ ω ∂μ, |δ i ω| ≤ (2 : ℝ) ^ (e i - d i - 1) :=
    fun i hi => isUniform_Icc_facts (zpow_pos two_pos _) (hδ i hi)
  have hfun : (fun ω => ∑ i ∈ s, xbar i ω * δ i ω + ∑ j ∈ t, zbar j ω * δZ j ω) =
      fun ω => ∑ k ∈ s.disjSum t, Sum.elim xbar zbar k ω * Sum.elim δ δZ k ω := by
    funext ω
    simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr]
  have hY : ∀ k ∈ s.disjSum t, MemLp (fun ω => Sum.elim xbar zbar k ω * Sum.elim δ δZ k ω) 2 μ := by
    rintro (i | j) hk
    · have hi : i ∈ s := Finset.inl_mem_disjSum.1 hk
      exact memLp_mul_of_bound (hxbar i hi) (hfacts i hi).1 (hfacts i hi).2
    · exact hZ j (Finset.inr_mem_disjSum.1 hk)
  have hsm : ∀ k ∈ s.disjSum t, AEStronglyMeasurable (Sum.elim xbar zbar k) μ := by
    rintro (i | j) hk
    · exact (hxbar i (Finset.inl_mem_disjSum.1 hk)).1
    · exact hzbar j (Finset.inr_mem_disjSum.1 hk)
  have hem : ∀ k ∈ s.disjSum t, AEStronglyMeasurable (Sum.elim δ δZ k) μ := by
    rintro (i | j) hk
    · exact (hfacts i (Finset.inl_mem_disjSum.1 hk)).1
    · exact hδZ j (Finset.inr_mem_disjSum.1 hk)
  have hind_k : ∀ k ∈ s.disjSum t, IndepFun (Sum.elim xbar zbar k) (Sum.elim δ δZ k) μ := by
    rintro (i | j) hk
    · exact hind_x i (Finset.inl_mem_disjSum.1 hk)
    · exact hind_z j (Finset.inr_mem_disjSum.1 hk)
  rw [hfun]
  refine (variance_sum_mul_le_of_indep (s.disjSum t) (Sum.elim xbar zbar) (Sum.elim δ δZ) hY hsm
    hem hind_k hind).trans (le_of_eq ?_)
  rw [Finset.sum_disjSum, vIndep, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    show (∫ ω, xbar i ω ^ 2 ∂μ) * ∫ ω, δ i ω ^ 2 ∂μ = _
    rw [integral_sq_uniform_roundError (e i) (d i) (hδ i hi)]
    ring
  · refine Finset.sum_congr rfl fun j hj => ?_
    show (∫ ω, zbar j ω ^ 2 ∂μ) * ∫ ω, δZ j ω ^ 2 ∂μ = _
    rw [hmse j hj]

/-- **Haas–Giles (29)** (2025, §4.3, p. 9): with rounding errors satisfying (20) and the errors
`δZ_j` of approximate normal increments independent of their sensitivities `Z̄_j`, with
`MSE = E[|Z_j − Z̃_j|²]`,
`V[∑_i x̄_i δx_i + ∑_j Z̄_j δZ_j] ≤ (∑_i √E[x̄_i²] 2^{e_i−d_i−1} + ∑_j √(E[Z̄_j²] · MSE))²`
(`= V'_corr`), with no assumption on the joint law of the different terms. -/
theorem variance_extended_corr {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (xbar δ : ι → Ω → ℝ) (zbar δZ : κ → Ω → ℝ) (e : ι → ℤ) (d : ι → ℕ) (mse : ℝ)
    (hxbar : ∀ i ∈ s, MemLp (xbar i) 2 μ) (hδm : ∀ i ∈ s, AEStronglyMeasurable (δ i) μ)
    (hδ : ∀ i ∈ s, ∀ᵐ ω ∂μ, |δ i ω| ≤ (2 : ℝ) ^ (e i - d i - 1))
    (hzbar : ∀ j ∈ t, AEStronglyMeasurable (zbar j) μ)
    (hδZ : ∀ j ∈ t, AEStronglyMeasurable (δZ j) μ)
    (hZ : ∀ j ∈ t, MemLp (fun ω => zbar j ω * δZ j ω) 2 μ)
    (hmse : ∀ j ∈ t, ∫ ω, δZ j ω ^ 2 ∂μ = mse)
    (hind_z : ∀ j ∈ t, IndepFun (zbar j) (δZ j) μ) :
    variance (fun ω => ∑ i ∈ s, xbar i ω * δ i ω + ∑ j ∈ t, zbar j ω * δZ j ω) μ ≤
      (∑ i ∈ s, Real.sqrt (∫ ω, xbar i ω ^ 2 ∂μ) * (2 : ℝ) ^ (e i - d i - 1) +
        ∑ j ∈ t, Real.sqrt ((∫ ω, zbar j ω ^ 2 ∂μ) * mse)) ^ 2 := by
  have hfun : (fun ω => ∑ i ∈ s, xbar i ω * δ i ω + ∑ j ∈ t, zbar j ω * δZ j ω) =
      fun ω => ∑ k ∈ s.disjSum t, Sum.elim xbar zbar k ω * Sum.elim δ δZ k ω := by
    funext ω
    simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr]
  have hY : ∀ k ∈ s.disjSum t, MemLp (fun ω => Sum.elim xbar zbar k ω * Sum.elim δ δZ k ω) 2 μ := by
    rintro (i | j) hk
    · have hi : i ∈ s := Finset.inl_mem_disjSum.1 hk
      exact memLp_mul_of_bound (hxbar i hi) (hδm i hi) (hδ i hi)
    · exact hZ j (Finset.inr_mem_disjSum.1 hk)
  rw [hfun]
  refine (variance_sum_le_sq_sum_sqrt (s.disjSum t) hY).trans ?_
  rw [Finset.sum_disjSum]
  refine pow_le_pow_left₀ (add_nonneg (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _)
    (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _))
    (add_le_add (Finset.sum_le_sum fun i hi => ?_) (Finset.sum_le_sum fun j hj => ?_)) 2
  · exact sqrt_variance_mul_le (zpow_pos two_pos _).le (hxbar i hi) (hδm i hi) (hδ i hi)
  · -- `V[Z̄ δZ] ≤ E[Z̄² δZ²] = E[Z̄²] E[δZ²]` by independence
    have hind2 : IndepFun (fun ω => zbar j ω ^ 2) (fun ω => δZ j ω ^ 2) μ :=
      (hind_z j hj).comp (continuous_pow 2).measurable (continuous_pow 2).measurable
    have hmul := hind2.integral_mul_eq_mul_integral ((hzbar j hj).pow 2) ((hδZ j hj).pow 2)
    have h1 := variance_le_integral_sq (μ := μ) (hzbar j hj) (hδZ j hj)
    have h2 : ∫ ω, zbar j ω ^ 2 * δZ j ω ^ 2 ∂μ = (∫ ω, zbar j ω ^ 2 ∂μ) * mse := by
      rw [← hmse j hj]
      exact hmul
    exact Real.sqrt_le_sqrt (h1.trans h2.le)

end variance

end MLMC
