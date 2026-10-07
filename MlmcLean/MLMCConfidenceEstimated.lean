import MlmcLean.ConsistencyCheck

/-!
# Confidence intervals for multilevel Monte Carlo with estimated variances

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1, p. 8 of
the author's version (and §3.3, p. 23, for the accuracy of variance estimates).

**Giles (2015), §2.1, p. 8.** "Collier, Haji-Ali, Nobile, von Schwerin and Tempone (2014) have
developed a modified version of the Theorem. Instead of bounding the Mean Square Error, they prefer
to use the Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence. This exploits the fact that the multilevel correction `Y_ℓ` on each
level is asymptotically Normally-distributed, and therefore so is `Y`."

`MlmcLean/MLMCCentralLimit.lean` proves the confidence intervals with the exact standard deviation
`σ_k`, `σ_k² = ∑_{ℓ ≤ L_k} V_ℓ/N_{k,ℓ} = V[Y_k]`.  In practice `σ_k` is unknown and is replaced
by the estimate `σ̂_k² = ∑_{ℓ ≤ L_k} s_{k,ℓ}²/N_{k,ℓ}` (`mlmcVarEst`), where `s_{k,ℓ}²` is the
empirical variance (`empVar`, `N⁻¹ ∑ (x_n − x̄)²`) of the `N_{k,ℓ}` samples of `ΔP_ℓ` used by the
estimator itself.  This file proves that the intervals `Y_k ± z σ̂_k` have the same asymptotic
confidence.  The paper only cites Collier et al.; it states neither a theorem nor hypotheses, and
all hypotheses below are this formalisation's.  Notation as in `MlmcLean/MLMCCentralLimit.lean`:
independent inputs `ω^{(ℓ,n)}` of law `ν`, `ΔP_ℓ = P_ℓ − P_{ℓ−1}`, `V_ℓ = V[ΔP_ℓ]`, `Y_k` the
estimator (2.2) with finest level `L_k` and `N_{k,ℓ}` samples on level `ℓ`, and
`Φ = cdf (gaussianReal 0 1)`.  Events are stated without division by `σ̂_k`, which may vanish.

**Results.**
* `tendsto_measureReal_abs_le_mul_of_rel` (Slutsky's lemma for intervals): if
  `P(|S_k| ≤ z' σ_k) → 2Φ(z') − 1` for every `z' ≥ 0` and `P(|σ̂_k − σ_k| > ε σ_k) → 0` for every
  `ε > 0`, then `P(|S_k| ≤ z σ̂_k) → 2Φ(z) − 1` (`Φ` is continuous: `continuous_cdf_gaussianReal`).
* `integral_abs_empVar_sub_le`, `integral_abs_empVar_sub_le_sqrt`: if the kurtosis of `g` is at
  most `K`, `E[(g − E g)⁴] ≤ K V[g]²`, the empirical variance of `N ≥ 1` independent samples has
  `E|s_N² − V[g]| ≤ (√((K − 1)/N) + 1/N) V[g] ≤ √(2K/N) V[g]` for every `N`: an `L¹` analogue of
  the paper's heuristic (§3.3, p. 23) "the standard deviation of the sample variance … is
  approximately `√((κ − 1)/N) E[X²]`".  Only the mean absolute error is bounded: with the same
  constant, the standard deviation of `s_N²` is not (for `g = ±1` it is `√(2(N − 1))/N^{3/2}`,
  above `1/N` for `N ≥ 3`).
* `integral_abs_mlmcVarEst_sub_le` (the key estimate): with kurtosis at most `K` on every level
  and `N_ℓ ≥ n₀ ≥ 1`, `E|σ̂² − σ²| ≤ √(2K/n₀) σ²`, however many levels there are.
* Fixed number of levels `L`, `N_{k,ℓ} → ∞` on every level at arbitrary rates, second moments
  only: `tendsto_measureReal_mlmcVarEst_rel_fixed` and `tendstoInMeasure_sqrt_mlmcVarEst_div_fixed`
  (`σ̂_k/σ_k → 1` in probability, the strong law on every level);
  `tendstoInDistribution_mlmcEstimator_fixed` (`(Y_k − E[P_L])/σ_k → N(0, 1)`, Lindeberg's
  theorem; this generalises the non-degenerate case of `tendstoInDistribution_mlmcEstimator`,
  `N_ℓ = m_ℓ n` with some `V_ℓ > 0`, to arbitrary rates);
  `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_fixed`
  (`P(|Y_k − E[P_L]| ≤ z σ̂_k) → 2Φ(z) − 1`).
* Growing number of levels, kurtosis at most `K` on the levels used,
  `min_{ℓ ≤ L_k} N_{k,ℓ} → ∞` (the setting of `tendstoInDistribution_mlmcEstimator_of_moment_le`
  with `δ = 2`): `tendsto_measureReal_mlmcVarEst_rel` and `tendstoInMeasure_mlmcVarEst_div`
  (`σ̂_k²/σ_k² → 1` in probability); `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd`
  (`P(|Y_k − E[P_{L_k}]| ≤ z σ̂_k) → 2Φ(z) − 1`), with no condition on the growth of `L_k`.
* Around `E[P]`: `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_of_bias` (bias `o(σ_k)`);
  `eventually_lt_measureReal_abs_mlmcEstimator_sub_le_estSd_add` (the computable interval
  `Y_k ± (z σ̂_k + b_k)` with a bias bound `b_k` covers `E[P]` with asymptotic confidence at least
  `2Φ(z) − 1`); and the tolerance split of Collier et al., where the statistical condition
  `z σ̂_k ≤ θ TOL_k` is now a random test: `eventually_measureReal_test_and_tol_lt_abs_lt` (the
  test accepts while the error exceeds `TOL_k` with asymptotic probability at most `2(1 − Φ(z))`,
  given only `|E[P_{L_k}] − E[P]| ≤ (1 − θ) TOL_k`) and
  `eventually_lt_measureReal_test_and_abs_sub_le_tol` (the test accepts and the error is at most
  `TOL_k` with asymptotic probability at least `2Φ(z) − 1` when moreover `z σ_k ≤ θ' TOL_k`,
  `0 ≤ θ' < θ`).

**Deviations and remarks.**
* *The statements are asymptotic.*  For small samples the coverage with estimated variances is
  below the nominal level.  In a simulation with three levels,
  `ΔP_ℓ = 2^{−ℓ/2}(E_ℓ − 1) + 2^{−ℓ}/10` with `E_ℓ` exponential with mean `1`, the interval
  `Y ± 1.96 σ̂` covered `E[P_L]` in `86.50% ± 0.05%` of `4·10⁵` replications for `N = (10, 5, 3)`
  (`95.33% ± 0.03%` with the exact `σ`), and in `94.69% ± 0.04%` of `3·10⁵` replications for
  `N = (1000, 400, 100)` (`95.04% ± 0.04%` with the exact `σ`; nominal `95.00%`), where `±` is one
  Monte Carlo standard error.
* *Fixed sample sizes, not the adaptive algorithm.*  The levels `L_k` and sample sizes `N_{k,ℓ}`
  are deterministic, and the tolerance test `z σ̂_k ≤ θ TOL_k` is studied at a fixed index `k`.
  The estimator at a random stopping index, or with sample sizes chosen from estimated variances
  (as in Collier et al. or the driver of §3.4), is not formalised.
* *Hypotheses.*  For a fixed number of levels only `P_ℓ ∈ L²` and `V_ℓ > 0` for some `ℓ ≤ L` are
  assumed (if every `V_ℓ = 0`, then `Y_k = E[P_L]` and `σ̂_k = 0` almost surely, and the coverage
  is `1`).  For a growing number of levels the central limit theorem needs a condition beyond
  `min_ℓ N_{k,ℓ} → ∞` (counterexample in `MlmcLean/MLMCCentralLimit.lean`), e.g. Lyapunov's
  condition (`tendstoInDistribution_mlmcEstimator_lyapunov`) or a uniform moment bound; here the
  bound on the kurtosis, `E[(ΔP_ℓ − E ΔP_ℓ)⁴] ≤ K V_ℓ²` (Giles §3.3 defines `κ`), serves both the
  central limit theorem (`δ = 2`) and the consistency of `σ̂_k` with an explicit rate.  The biased
  empirical variance is the driver's `Vl` (§3.4); any other estimate that is relatively consistent
  can be used in `tendsto_measureReal_abs_le_mul_of_rel`.
* *`E[P]`* is written `∫ P dν` without assuming `P` integrable, as in
  `MlmcLean/MLMCCentralLimit.lean`.  The statements around `E[P]` hold for every real number in
  its place; for a non-integrable `P`, Lean's `∫ P dν` is `0` and they are statements about `0`.
* *Around `E[P]` for a fixed number of levels* nothing new holds: `σ_k → 0`, so a bias `o(σ_k)`
  means `E[P_L] = E[P]`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

/-! ### Empirical variances: algebra -/

/-- Shifting a sequence shifts its empirical mean: `(x − c)‾_N = x̄_N − c` for `N ≥ 1`. -/
lemma empMean_sub_const (x : ℕ → ℝ) (c : ℝ) {N : ℕ} (hN : 0 < N) :
    empMean (fun n => x n - c) N = empMean x N - c := by
  have h := empMean_sub x (fun _ => c) N
  rw [empMean_const c hN] at h
  exact h

/-- The empirical variance is invariant under shifts: `s_N²[x − c] = s_N²[x]`. -/
lemma empVar_sub_const (x : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    empVar (fun n => x n - c) N = empVar x N := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [empVar]
  · simp only [empVar, empMean_sub_const x c hN, sub_sub_sub_cancel_right]

/-- The empirical variance is nonnegative. -/
lemma empVar_nonneg (x : ℕ → ℝ) (N : ℕ) : 0 ≤ empVar x N :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- The empirical variance around an arbitrary centre `c`, for `N ≥ 1`:
`s_N² = N⁻¹ ∑_{n<N} (x_n − c)² − (x̄_N − c)²`. -/
lemma empVar_eq_sub_sq (x : ℕ → ℝ) (c : ℝ) {N : ℕ} (hN : 0 < N) :
    empVar x N = (N : ℝ)⁻¹ * ∑ n ∈ range N, (x n - c) ^ 2 -
      ((N : ℝ)⁻¹ * ∑ n ∈ range N, (x n - c)) ^ 2 := by
  rw [← empVar_sub_const x c, empVar_eq_powerSum _ hN, div_eq_inv_mul, div_eq_inv_mul]

/-! ### Slutsky's lemma for confidence intervals -/

/-- The standard normal distribution function `Φ = cdf (gaussianReal 0 1)` is continuous: it is
a Stieltjes function, hence right-continuous, and its jump `Φ(x) − Φ(x−)` at `x` is the mass of
`{x}`, which is `0` (`StieltjesFunction.measure_singleton`, `ProbabilityTheory.measure_cdf`). -/
lemma continuous_cdf_gaussianReal : Continuous (cdf (gaussianReal 0 1)) := by
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [(cdf (gaussianReal 0 1)).mono.continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  have h := (cdf (gaussianReal 0 1)).measure_singleton x
  rw [measure_cdf, measure_singleton] at h
  have h1 := ENNReal.ofReal_eq_zero.1 h.symm
  have h2 := (cdf (gaussianReal 0 1)).mono.leftLim_le (le_refl x)
  linarith

/-- `2Φ(0) − 1 = 0` for the standard normal distribution function `Φ` (no atom at `0`). -/
lemma two_mul_cdf_gaussianReal_zero_sub_one : 2 * cdf (gaussianReal 0 1) 0 - 1 = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  rw [← measureReal_gaussianReal_Icc_neg le_rfl, neg_zero, Set.Icc_self, measureReal_def,
    measure_singleton, ENNReal.toReal_zero]

/-- `2Φ(z) − 1 ≤ 0` for `z ≤ 0`, `Φ` the standard normal distribution function (`Φ` is monotone
and `2Φ(0) − 1 = 0`): for `z ≤ 0` the asymptotic bounds below are trivial. -/
lemma two_mul_cdf_gaussianReal_sub_one_nonpos {z : ℝ} (hz : z ≤ 0) :
    2 * cdf (gaussianReal 0 1) z - 1 ≤ 0 := by
  have h := (cdf (gaussianReal 0 1)).mono hz
  have h0 := two_mul_cdf_gaussianReal_zero_sub_one
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Slutsky's lemma for confidence intervals** (for the estimated variances of Collier et al.
cited in Giles 2015, §2.1, p. 8: "they prefer to use the Central Limit Theorem to construct a
confidence interval which bounds `E[P]` with a user-prescribed confidence").  Let `S_k` be random
errors and `σ_k` numbers such that `P(|S_k| ≤ z' σ_k) → 2Φ(z') − 1` for every `z' ≥ 0` (as for
`S_k = Y_k − E[P_{L_k}]` and the exact standard deviation `σ_k`), and let `σ̂_k` be random
estimates of `σ_k` that are consistent in the relative sense, `P(|σ̂_k − σ_k| > ε σ_k) → 0` for
every `ε > 0`.  Then `P(|S_k| ≤ z σ̂_k) → 2Φ(z) − 1` for every `z ≥ 0`.  No division by `σ̂_k`
occurs, so `σ̂_k = 0` needs no special treatment, and the `S_k`, `σ̂_k` need not be measurable.
Proof: for `0 < ε ≤ 1`, `{|S_k| ≤ z(1 − ε) σ_k} ⊆ {|S_k| ≤ z σ̂_k} ∪ B_k` and
`{|S_k| ≤ z σ̂_k} ⊆ {|S_k| ≤ z(1 + ε) σ_k} ∪ B_k` with `B_k = {|σ̂_k − σ_k| > ε σ_k}`, and `Φ` is
continuous (`continuous_cdf_gaussianReal`).  The hypotheses are this formalisation's; the paper
only cites Collier et al. -/
theorem tendsto_measureReal_abs_le_mul_of_rel {S σh : ℕ → Ω → ℝ} {σ : ℕ → ℝ}
    (hS : ∀ z' : ℝ, 0 ≤ z' → Tendsto (fun k => μ.real {x | |S k x| ≤ z' * σ k}) atTop
      (𝓝 (2 * cdf (gaussianReal 0 1) z' - 1)))
    (hσh : ∀ ε : ℝ, 0 < ε → Tendsto (fun k => μ.real {x | ε * σ k < |σh k x - σ k|}) atTop
      (𝓝 0))
    {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun k => μ.real {x | |S k x| ≤ z * σh k x}) atTop
      (𝓝 (2 * cdf (gaussianReal 0 1) z - 1)) := by
  set G : ℝ → ℝ := fun z' => 2 * cdf (gaussianReal 0 1) z' - 1 with hG
  have hGc : Continuous G := (continuous_const.mul continuous_cdf_gaussianReal).sub
    continuous_const
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- the lower bound, with `z(1 − ε)`
    have hlim : Tendsto (fun n : ℕ => G (z * (1 - 1 / ((n : ℝ) + 1)))) atTop (𝓝 (G z)) := by
      have h1 := ((tendsto_const_nhds (x := z)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat))
      rw [sub_zero, mul_one] at h1
      exact (hGc.tendsto z).comp h1
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds ha)).exists
    set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
    have hε0 : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have hz' : 0 ≤ z * (1 - ε) := mul_nonneg hz (by linarith)
    have hc : 0 < (G (z * (1 - ε)) - a) / 2 := by linarith
    filter_upwards [(hS _ hz').eventually (lt_mem_nhds (show G (z * (1 - ε)) - (G (z * (1 - ε))
      - a) / 2 < G (z * (1 - ε)) by linarith)), (hσh ε hε0).eventually_lt_const hc] with k hk1 hk2
    have hsub : {x | |S k x| ≤ z * (1 - ε) * σ k} ⊆
        {x | |S k x| ≤ z * σh k x} ∪ {x | ε * σ k < |σh k x - σ k|} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
      by_cases hb : ε * σ k < |σh k x - σ k|
      · exact Or.inr hb
      left
      have h1 := neg_abs_le (σh k x - σ k)
      have h2 : (1 - ε) * σ k ≤ σh k x := by linarith [not_lt.1 hb]
      calc |S k x| ≤ z * (1 - ε) * σ k := hx
        _ = z * ((1 - ε) * σ k) := by ring
        _ ≤ z * σh k x := mul_le_mul_of_nonneg_left h2 hz
    have hu := measureReal_union_le (μ := μ) {x | |S k x| ≤ z * σh k x}
      {x | ε * σ k < |σh k x - σ k|}
    have hm := measureReal_mono (μ := μ) hsub
    linarith
  · -- the upper bound, with `z(1 + ε)`
    have hlim : Tendsto (fun n : ℕ => G (z * (1 + 1 / ((n : ℝ) + 1)))) atTop (𝓝 (G z)) := by
      have h1 := ((tendsto_const_nhds (x := z)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat))
      rw [add_zero, mul_one] at h1
      exact (hGc.tendsto z).comp h1
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hb)).exists
    set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
    have hε0 : 0 < ε := by positivity
    have hz' : 0 ≤ z * (1 + ε) := mul_nonneg hz (by linarith)
    have hc : 0 < (b - G (z * (1 + ε))) / 2 := by linarith
    filter_upwards [(hS _ hz').eventually (gt_mem_nhds (show G (z * (1 + ε)) < G (z * (1 + ε)) +
      (b - G (z * (1 + ε))) / 2 by linarith)), (hσh ε hε0).eventually_lt_const hc] with k hk1 hk2
    have hsub : {x | |S k x| ≤ z * σh k x} ⊆
        {x | |S k x| ≤ z * (1 + ε) * σ k} ∪ {x | ε * σ k < |σh k x - σ k|} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
      by_cases hb : ε * σ k < |σh k x - σ k|
      · exact Or.inr hb
      left
      have h1 := le_abs_self (σh k x - σ k)
      have h2 : σh k x ≤ (1 + ε) * σ k := by linarith [not_lt.1 hb]
      calc |S k x| ≤ z * σh k x := hx
        _ ≤ z * ((1 + ε) * σ k) := mul_le_mul_of_nonneg_left h2 hz
        _ = z * (1 + ε) * σ k := by ring
    have hu := measureReal_union_le (μ := μ) {x | |S k x| ≤ z * (1 + ε) * σ k}
      {x | ε * σ k < |σh k x - σ k|}
    have hm := measureReal_mono (μ := μ) hsub
    linarith

/-! ### The empirical variance on one level: an `L¹` bound from the kurtosis -/

/-- `E|X| ≤ √(E[X²])` for a square-integrable `X` on a probability space (the variance of `|X|`
is nonnegative). -/
lemma integral_abs_le_sqrt_integral_sq {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫ x, |X x| ∂μ ≤ √(∫ x, X x ^ 2 ∂μ) := by
  have hA : MemLp (fun x => |X x|) 2 μ := by simpa [Real.norm_eq_abs] using hX.norm
  have hv := variance_nonneg (fun x => |X x|) μ
  rw [variance_eq_sub hA] at hv
  have e : μ[(fun x => |X x|) ^ 2] = ∫ x, X x ^ 2 ∂μ := by
    congr 1
    funext x
    simp [sq_abs]
  rw [e] at hv
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

section Level

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀} {ω : ℕ × ℕ → Ω → Ω₀}

omit [IsProbabilityMeasure μ] in
/-- The empirical variance of `N` samples `g(ω^{(i,n)})` of a square-integrable `g` is
integrable. -/
lemma integrable_empVar_input (hω : ∀ p, MeasurePreserving (ω p) μ ν) {g : Ω₀ → ℝ}
    (hg : MemLp g 2 ν) (i N : ℕ) :
    Integrable (fun x => empVar (fun n => g (ω (i, n) x)) N) μ := by
  have hs : ∀ n, MemLp (fun x => g (ω (i, n) x)) 2 μ := fun n =>
    hg.comp_measurePreserving (hω (i, n))
  have hm : MemLp (fun x => empMean (fun n => g (ω (i, n) x)) N) 2 μ := by
    have h := (memLp_finsetSum (range N) fun n _ => hs n).mul_const ((N : ℝ)⁻¹)
    simpa only [empMean, div_eq_mul_inv] using h
  unfold empVar
  exact (integrable_finsetSum _ fun n _ => ((hs n).sub hm).integrable_sq).div_const _

/-- The centred fourth moment bounds the squared variance: `V[g]² ≤ E[(g − E g)⁴]` (the variance
of `(g − E g)²` is nonnegative), so a bound `E[(g − E g)⁴] ≤ K V[g]²` with `V[g] > 0` forces
`K ≥ 1`: the kurtosis `κ = E[X⁴]/(E[X²])²` defined in Giles 2015, §3.3, p. 23, is at least `1`. -/
lemma sq_variance_le_integral_pow_four [IsProbabilityMeasure ν] {g : Ω₀ → ℝ} (hg : MemLp g 2 ν)
    (h4 : Integrable (fun y => (g y - ∫ z, g z ∂ν) ^ 4) ν) :
    variance g ν ^ 2 ≤ ∫ y, (g y - ∫ z, g z ∂ν) ^ 4 ∂ν := by
  set m := ∫ z, g z ∂ν
  have hcm : AEStronglyMeasurable (fun y => g y - m) ν :=
    (hg.sub (memLp_const m)).aestronglyMeasurable
  have hcm2 : AEStronglyMeasurable (fun y => (g y - m) ^ 2) ν := hcm.pow 2
  have hsq : MemLp (fun y => (g y - m) ^ 2) 2 ν :=
    (memLp_two_iff_integrable_sq hcm2).2 (h4.congr (ae_of_all _ fun y => by ring))
  have hv := variance_nonneg (fun y => (g y - m) ^ 2) ν
  rw [variance_eq_sub hsq] at hv
  have e1 : ν[(fun y => (g y - m) ^ 2) ^ 2] = ∫ y, (g y - m) ^ 4 ∂ν := by
    congr 1
    funext y
    simp only [Pi.pow_apply]
    ring
  have e2 : ν[fun y => (g y - m) ^ 2] = variance g ν :=
    (variance_eq_integral hg.aestronglyMeasurable.aemeasurable).symm
  rw [e1, e2] at hv
  linarith

/-- **The accuracy of the empirical variance under a kurtosis bound** (Giles 2015, §3.3, p. 23:
"When the number of samples `N` is large, the standard deviation of the sample variance for a
random variable `X` with zero mean is approximately `√((κ − 1)/N) E[X²]` where the kurtosis `κ` is
defined as `κ = E[X⁴]/(E[X²])²`"; used for the estimated variances of Collier et al., §2.1, p. 8).
Let the inputs `ω^{(p)}` be independent with law `ν`, let `g` be square integrable with
`E[(g − E g)⁴] ≤ K V[g]²` (the kurtosis of `g` is at most `K`; no division, so `V[g] = 0` is
allowed), and let `s_N²` be the empirical variance (`empVar`, the biased form `N⁻¹ ∑ (x_n − x̄)²`)
of the `N ≥ 1` samples `g(ω^{(i,n)})`, `n < N`.  Then
`E|s_N² − V[g]| ≤ (√((K − 1)/N) + 1/N) V[g]`.  This is an `L¹` analogue of the paper's
heuristic, valid for every `N`: the first term is the paper's approximate standard deviation
`√((κ − 1)/N) E[X²]` with `κ ≤ K`, the second accounts for the bias of the biased form.  Only the
mean absolute error `E|s_N² − V|` (at most the root-mean-square error) is bounded; the standard
deviation of `s_N²` is not bounded by the same constant.  For the symmetric two-point law
`g = ±1` (`K = V = 1`), `s_N² − V = −ḡ_N²` with `ḡ_N` the sample mean, so the standard deviation
of `s_N²` is `√(2(N − 1))/N^{3/2} > 1/N` for `N ≥ 3`, and the root-mean-square error is
`√(3N − 2)/N^{3/2} ≈ √3/N`: an `L²` version needs a larger `O(V/N)` term.  The bound is attained
for every `N` by that law: `E|s_N² − V| = E[ḡ_N²] = 1/N`.  The paper states only the
approximation for large `N`; the kurtosis hypothesis and the bound are this formalisation's.
Proof: with `X_n = g(ω^{(i,n)}) − E g`, `s_N² − V = N⁻¹ ∑ (X_n² − V) − X̄²`,
`E|N⁻¹ ∑ (X_n² − V)| ≤ √(V[X²]/N)` with `V[X²] = E[X⁴] − V² ≤ (K − 1) V²`, and
`E[X̄²] = V/N`. -/
theorem integral_abs_empVar_sub_le (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {g : Ω₀ → ℝ} (hg : MemLp g 2 ν)
    (h4 : Integrable (fun y => (g y - ∫ z, g z ∂ν) ^ 4) ν) {K : ℝ}
    (hK : ∫ y, (g y - ∫ z, g z ∂ν) ^ 4 ∂ν ≤ K * variance g ν ^ 2) (i : ℕ) {N : ℕ}
    (hN : 0 < N) :
    ∫ x, |empVar (fun n => g (ω (i, n) x)) N - variance g ν| ∂μ ≤
      (√((K - 1) / N) + 1 / N) * variance g ν := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  obtain ⟨m, hm⟩ : ∃ m, ∫ z, g z ∂ν = m := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, variance g ν = V := ⟨_, rfl⟩
  rw [hm] at h4 hK
  rw [hV] at hK ⊢
  have hgm : AEMeasurable g ν := hg.aestronglyMeasurable.aemeasurable
  have hV0 : 0 ≤ V := hV ▸ variance_nonneg _ _
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  -- the centred samples `X_n` and the centred squares `X_n² − V`
  have hcL2 : MemLp (fun y => g y - m) 2 ν := hg.sub (memLp_const m)
  have hcm : AEStronglyMeasurable (fun y => g y - m) ν := hcL2.aestronglyMeasurable
  have hcm2 : AEStronglyMeasurable (fun y => (g y - m) ^ 2) ν := hcm.pow 2
  have hsq : MemLp (fun y => (g y - m) ^ 2) 2 ν :=
    (memLp_two_iff_integrable_sq hcm2).2 (h4.congr (ae_of_all _ fun y => by ring))
  have hdL2 : MemLp (fun y => (g y - m) ^ 2 - V) 2 ν := hsq.sub (memLp_const V)
  have hc0 : ∫ y, (g y - m) ∂ν = 0 := by
    rw [integral_sub (hg.integrable one_le_two) (integrable_const m), hm]
    simp
  have hc2 : ∫ y, (g y - m) ^ 2 ∂ν = V := by
    rw [← hV, variance_eq_integral hgm, hm]
  have hd0 : ∫ y, ((g y - m) ^ 2 - V) ∂ν = 0 := by
    rw [integral_sub (hsq.integrable one_le_two) (integrable_const V), hc2]
    simp
  have hcvar : variance (fun y => g y - m) ν = V := by
    rw [variance_sub_const hg.aestronglyMeasurable, hV]
  have hdvar : variance (fun y => (g y - m) ^ 2 - V) ν ≤ (K - 1) * V ^ 2 := by
    rw [variance_sub_const hsq.aestronglyMeasurable, variance_eq_sub hsq]
    have e1 : ν[(fun y => (g y - m) ^ 2) ^ 2] = ∫ y, (g y - m) ^ 4 ∂ν := by
      congr 1
      funext y
      simp only [Pi.pow_apply]
      ring
    have e2 : ν[fun y => (g y - m) ^ 2] = V := hc2
    rw [e1, e2]
    linarith
  -- transport to the samples
  have he : Function.Injective fun n : ℕ => (i, n) := fun a b h => by simpa using h
  have hYind := iIndepFun_comp_inputs hω hind he (g := fun _ => fun y => g y - m)
    fun _ => hcm.aemeasurable
  have hZind := iIndepFun_comp_inputs hω hind he (g := fun _ => fun y => (g y - m) ^ 2 - V)
    fun _ => hdL2.aestronglyMeasurable.aemeasurable
  have hYL2 : ∀ n, MemLp (fun x => g (ω (i, n) x) - m) 2 μ := fun n =>
    hcL2.comp_measurePreserving (hω (i, n))
  have hZL2 : ∀ n, MemLp (fun x => (g (ω (i, n) x) - m) ^ 2 - V) 2 μ := fun n =>
    hdL2.comp_measurePreserving (hω (i, n))
  have hY0 : ∀ n, ∫ x, (g (ω (i, n) x) - m) ∂μ = 0 := fun n => by
    rw [integral_comp_of_measurePreserving (hω (i, n)) (f := fun y => g y - m) hcm, hc0]
  have hZ0 : ∀ n, ∫ x, ((g (ω (i, n) x) - m) ^ 2 - V) ∂μ = 0 := fun n => by
    rw [integral_comp_of_measurePreserving (hω (i, n)) (f := fun y => (g y - m) ^ 2 - V)
      hdL2.aestronglyMeasurable, hd0]
  -- the two means and their second moments
  set Ybar : Ω → ℝ := fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, (g (ω (i, n) x) - m) with hYbar
  set Zbar : Ω → ℝ := fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, ((g (ω (i, n) x) - m) ^ 2 - V)
    with hZbar
  have hYbarL2 : MemLp Ybar 2 μ := (memLp_finsetSum _ fun n _ => hYL2 n).const_mul _
  have hZbarL2 : MemLp Zbar 2 μ := (memLp_finsetSum _ fun n _ => hZL2 n).const_mul _
  have hYbar0 : ∫ x, Ybar x ∂μ = 0 := by
    simp only [hYbar]
    rw [integral_const_mul, integral_finsetSum _ fun n _ => (hYL2 n).integrable one_le_two]
    simp [hY0]
  have hZbar0 : ∫ x, Zbar x ∂μ = 0 := by
    simp only [hZbar]
    rw [integral_const_mul, integral_finsetSum _ fun n _ => (hZL2 n).integrable one_le_two]
    simp [hZ0]
  have hYbar2 : ∫ x, Ybar x ^ 2 ∂μ = V / N := by
    rw [← variance_of_integral_eq_zero hYbarL2.aestronglyMeasurable.aemeasurable hYbar0]
    refine variance_sample_mean (fun n x => g (ω (i, n) x) - m) N hN V hYL2 (fun n => ?_)
      fun a _ b _ hab => hYind.indepFun hab
    rw [(hω (i, n)).variance_fun_comp (f := fun y => g y - m) hcm.aemeasurable, hcvar]
  have hZbar2 : ∫ x, Zbar x ^ 2 ∂μ = variance (fun y => (g y - m) ^ 2 - V) ν / N := by
    rw [← variance_of_integral_eq_zero hZbarL2.aestronglyMeasurable.aemeasurable hZbar0]
    exact variance_sample_mean (fun n x => (g (ω (i, n) x) - m) ^ 2 - V) N hN _ hZL2
      (fun n => (hω (i, n)).variance_fun_comp (f := fun y => (g y - m) ^ 2 - V)
        hdL2.aestronglyMeasurable.aemeasurable) fun a _ b _ hab => hZind.indepFun hab
  -- `E|Z̄| ≤ √(E[Z̄²]) ≤ √((K − 1)/N) V`
  have hZabs : ∫ x, |Zbar x| ∂μ ≤ √((K - 1) / N) * V := by
    refine (integral_abs_le_sqrt_integral_sq hZbarL2).trans ?_
    have e : √((K - 1) / N) * V = √((K - 1) / N * V ^ 2) := by
      rw [Real.sqrt_mul' _ (sq_nonneg V), Real.sqrt_sq hV0]
    rw [hZbar2, e]
    refine Real.sqrt_le_sqrt ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hdvar hN0.le
  -- the pointwise decomposition `s_N² − V = Z̄ − Ȳ²`
  have hpt : ∀ x, |empVar (fun n => g (ω (i, n) x)) N - V| ≤ |Zbar x| + Ybar x ^ 2 := by
    intro x
    have e1 : ∑ n ∈ range N, ((g (ω (i, n) x) - m) ^ 2 - V) =
        ∑ n ∈ range N, (g (ω (i, n) x) - m) ^ 2 - N * V := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
    have e : empVar (fun n => g (ω (i, n) x)) N - V = Zbar x - Ybar x ^ 2 := by
      rw [empVar_eq_sub_sq _ m hN]
      simp only [hZbar, hYbar]
      rw [e1, mul_sub, ← mul_assoc, inv_mul_cancel₀ hN0.ne', one_mul]
      ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (sq_nonneg (Ybar x))]
  have hint : Integrable (fun x => |Zbar x| + Ybar x ^ 2) μ :=
    (hZbarL2.integrable one_le_two).abs.add hYbarL2.integrable_sq
  calc ∫ x, |empVar (fun n => g (ω (i, n) x)) N - V| ∂μ
      ≤ ∫ x, (|Zbar x| + Ybar x ^ 2) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hint (ae_of_all _ hpt)
    _ = ∫ x, |Zbar x| ∂μ + ∫ x, Ybar x ^ 2 ∂μ :=
        integral_add (hZbarL2.integrable one_le_two).abs hYbarL2.integrable_sq
    _ ≤ √((K - 1) / N) * V + V / N := by rw [hYbar2]; linarith
    _ = (√((K - 1) / N) + 1 / N) * V := by ring

/-- **The `L¹` error of the empirical variance is `O(√(K/N)) V`** (Giles 2015, §3.3, p. 23:
"the standard deviation of the sample variance … is approximately `√((κ − 1)/N) E[X²]`"; for the
estimated variances of Collier et al., §2.1, p. 8).  Under the hypotheses of
`integral_abs_empVar_sub_le` (independent samples, `g ∈ L²`, `E[(g − E g)⁴] ≤ K V[g]²`, `N ≥ 1`),
`E|s_N² − V[g]| ≤ √(2K/N) V[g]`, i.e. `E|s_N² − V| ≤ C √K V/√N` with `C = √2`.  Proof:
`(√((K − 1)/N) + 1/N)² ≤ 2(K − 1)/N + 2/N² ≤ 2K/N`, where `K ≥ 1` if `V[g] > 0`
(`sq_variance_le_integral_pow_four`).  As for `integral_abs_empVar_sub_le`, this bounds the mean
absolute error only, not the standard deviation of `s_N²`; the paper states only the
approximation for large `N`, and the kurtosis hypothesis and the bound are this formalisation's. -/
theorem integral_abs_empVar_sub_le_sqrt (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {g : Ω₀ → ℝ} (hg : MemLp g 2 ν)
    (h4 : Integrable (fun y => (g y - ∫ z, g z ∂ν) ^ 4) ν) {K : ℝ}
    (hK : ∫ y, (g y - ∫ z, g z ∂ν) ^ 4 ∂ν ≤ K * variance g ν ^ 2) (i : ℕ) {N : ℕ}
    (hN : 0 < N) :
    ∫ x, |empVar (fun n => g (ω (i, n) x)) N - variance g ν| ∂μ ≤
      √(2 * K / N) * variance g ν := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  refine (integral_abs_empVar_sub_le hω hind hg h4 hK i hN).trans ?_
  rcases (variance_nonneg g ν).eq_or_lt with hV0 | hVpos
  · rw [← hV0, mul_zero, mul_zero]
  refine mul_le_mul_of_nonneg_right ?_ hVpos.le
  have hK1 : 1 ≤ K := by
    have h := (sq_variance_le_integral_pow_four hg h4).trans hK
    have hV2 : 0 < variance g ν ^ 2 := pow_pos hVpos 2
    nlinarith
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
  have ha : √((K - 1) / N) ^ 2 = (K - 1) / N := Real.sq_sqrt (div_nonneg (by linarith) hN0.le)
  have hb : (1 / (N : ℝ)) ^ 2 ≤ 1 / N := by
    rw [one_div, inv_pow, sq]
    exact inv_anti₀ hN0 (by nlinarith)
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have h2 : 2 * K / N = 2 * ((K - 1) / N) + 2 * (1 / N) := by
    field_simp
    ring
  rw [h2]
  nlinarith [sq_nonneg (√((K - 1) / N) - 1 / N)]

end Level

/-! ### Relative consistency: from squares to square roots, ratios, Markov -/

/-- Relative errors of square roots are controlled by those of the squares: for `a, b ≥ 0`, if
`ε √a < |√b − √a|` then `ε a < |b − a|` (as `|b − a| = |√b − √a| (√b + √a)`). -/
lemma lt_abs_sub_of_lt_abs_sqrt_sub {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ε * √a < |√b - √a|) : ε * a < |b - a| := by
  have e : b - a = (√b - √a) * (√b + √a) := by
    linear_combination (Real.sq_sqrt ha) - (Real.sq_sqrt hb)
  have hsa := Real.sqrt_nonneg a
  have hsb := Real.sqrt_nonneg b
  rw [e, abs_mul, abs_of_nonneg (add_nonneg hsb hsa)]
  rcases hsa.eq_or_lt with h0 | hpos
  · have ha0 : a = 0 := by rw [← Real.sq_sqrt ha, ← h0]; ring
    subst ha0
    simp only [Real.sqrt_zero, mul_zero, sub_zero, add_zero, abs_of_nonneg hsb] at h ⊢
    exact mul_pos h h
  · have h1 : ε * √a * √a < |√b - √a| * √a := mul_lt_mul_of_pos_right h hpos
    have h2 : ε * a = ε * √a * √a := by rw [mul_assoc, Real.mul_self_sqrt ha]
    have h3 : |√b - √a| * √a ≤ |√b - √a| * (√b + √a) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith

/-- The square-root form of relative consistency: if `σ_k² ≥ 0` and the random `σ̂_k² ≥ 0`
satisfy `P(|σ̂_k² − σ_k²| > ε σ_k²) → 0` for every `ε > 0`, then
`P(|σ̂_k − σ_k| > ε σ_k) → 0` for every `ε > 0` (`lt_abs_sub_of_lt_abs_sqrt_sub`). -/
lemma tendsto_measureReal_sqrt_rel {f : ℕ → Ω → ℝ} {s : ℕ → ℝ} (hf : ∀ k x, 0 ≤ f k x)
    (hs : ∀ k, 0 ≤ s k)
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun k => μ.real {x | ε * s k < |f k x - s k|}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => μ.real {x | ε * √(s k) < |√(f k x) - √(s k)|}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun k => measureReal_nonneg) fun k =>
      measureReal_mono fun x hx => lt_abs_sub_of_lt_abs_sqrt_sub (hs k) (hf k x) hx

/-- Relative consistency gives convergence of the ratio in probability: if `s_k > 0` for large `k`
and `P(|f_k − s_k| > ε s_k) → 0` for every `ε > 0`, then `f_k / s_k → 1` in probability. -/
lemma tendstoInMeasure_div_of_rel {f : ℕ → Ω → ℝ} {s : ℕ → ℝ} (hs : ∀ᶠ k in atTop, 0 < s k)
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun k => μ.real {x | ε * s k < |f k x - s k|}) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun k x => f k x / s k) atTop (fun _ => 1) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h (ε / 2) (by positivity))
    (Eventually.of_forall fun k => measureReal_nonneg) ?_
  filter_upwards [hs] with k hk
  refine measureReal_mono fun x hx => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hx ⊢
  rw [div_sub_one hk.ne', abs_div, abs_of_pos hk, le_div_iff₀ hk] at hx
  have : ε / 2 * s k < ε * s k := by nlinarith
  linarith

/-- Markov's inequality in the form used for the variance estimates: if `f ≥ 0` is integrable,
`c ≥ 0`, `B ≥ 0`, `ε > 0` and `E[f] ≤ B c`, then `P(f > ε c) ≤ B/ε` (for `c = 0`, `f = 0` almost
surely). -/
lemma measureReal_lt_le_of_integral_le {f : Ω → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μ)
    {c B ε : ℝ} (hc : 0 ≤ c) (hB0 : 0 ≤ B) (hε : 0 < ε) (hB : ∫ x, f x ∂μ ≤ B * c) :
    μ.real {x | ε * c < f x} ≤ B / ε := by
  have hint0 : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hf0
  rcases hc.eq_or_lt with hc0 | hcpos
  · -- `E[f] ≤ 0` forces `f = 0` almost surely
    rw [← hc0, mul_zero] at hB
    have hf : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hf0 hfi).1 (le_antisymm hB hint0)
    have hnull : μ {x | ¬ f x = (0 : Ω → ℝ) x} = 0 := ae_iff.1 hf
    have hle : μ.real {x | ε * c < f x} ≤ μ.real {x | ¬ f x = (0 : Ω → ℝ) x} :=
      measureReal_mono fun x hx => by
        simp only [Set.mem_ofPred_eq, ← hc0, mul_zero, Pi.zero_apply] at hx ⊢
        exact hx.ne'
    rw [measureReal_def μ {x | ¬ f x = (0 : Ω → ℝ) x}, hnull, ENNReal.toReal_zero] at hle
    exact hle.trans (div_nonneg hB0 hε.le)
  · have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hf0) hfi (ε * c)
    have hsub := measureReal_mono (μ := μ) (show {x | ε * c < f x} ⊆ {x | ε * c ≤ f x} from
      fun x (hx : ε * c < f x) => (le_of_lt hx : ε * c ≤ f x))
    have hεc : 0 < ε * c := mul_pos hε hcpos
    rw [le_div_iff₀ hε]
    nlinarith

/-! ### The estimated variance of the multilevel estimator -/

/-- The estimated variance of the multilevel estimator (2.2) (the variance estimate behind the
confidence intervals of Collier et al., Giles 2015, §2.1, p. 8; the level variances are estimated
as in the driver of §3.4, p. 25, `Vl = max(0, suml(2,:)./Nl - ml.^2)`):
`σ̂² = ∑_{ℓ ≤ L} s_ℓ²/N_ℓ`, where `s_ℓ²` is the empirical variance (`empVar`, the biased form
`N_ℓ⁻¹ ∑_n (x_n − x̄)²`) of the `N_ℓ` samples `ΔP_ℓ(ω^{(ℓ,n)})`, `n < N_ℓ`, used by the estimator
(`mlmcEstimator`).  It estimates `σ² = V[Y] = ∑_{ℓ ≤ L} V_ℓ/N_ℓ` (2.3).  A level with `N_ℓ = 0`
contributes `0`; every theorem assumes `N_ℓ ≥ 1` eventually. -/
noncomputable def mlmcVarEst {Ω₀ Ω : Type*} (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (L : ℕ)
    (N : ℕ → ℕ) (x : Ω) : ℝ :=
  ∑ ℓ ∈ range (L + 1), empVar (fun n => levelDiff Pl ℓ (ω (ℓ, n) x)) (N ℓ) / N ℓ

/-- The estimated variance `σ̂²` is nonnegative. -/
lemma mlmcVarEst_nonneg {Ω₀ Ω : Type*} (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (L : ℕ)
    (N : ℕ → ℕ) (x : Ω) : 0 ≤ mlmcVarEst Pl ω L N x :=
  Finset.sum_nonneg fun _ _ => div_nonneg (empVar_nonneg _ _) (Nat.cast_nonneg _)

/-- The error of `σ̂²` is at most the sum of the level errors: for any numbers `V_ℓ`,
`|σ̂² − ∑_ℓ V_ℓ/N_ℓ| ≤ ∑_ℓ |s_ℓ² − V_ℓ|/N_ℓ`. -/
lemma abs_mlmcVarEst_sub_le {Ω₀ Ω : Type*} (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (L : ℕ)
    (N : ℕ → ℕ) (V : ℕ → ℝ) (x : Ω) :
    |mlmcVarEst Pl ω L N x - ∑ ℓ ∈ range (L + 1), V ℓ / N ℓ| ≤
      ∑ ℓ ∈ range (L + 1), |empVar (fun n => levelDiff Pl ℓ (ω (ℓ, n) x)) (N ℓ) - V ℓ| / N ℓ := by
  rw [mlmcVarEst, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun ℓ _ => ?_))
  rw [← sub_div, abs_div, Nat.abs_cast]

section Estimator

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀} {ω : ℕ × ℕ → Ω → Ω₀}
  {Pl : ℕ → Ω₀ → ℝ}

omit [IsProbabilityMeasure μ] in
/-- The estimated variance `σ̂²` is integrable when the corrections `ΔP_ℓ`, `ℓ ≤ L`, are square
integrable. -/
lemma integrable_mlmcVarEst (hω : ∀ p, MeasurePreserving (ω p) μ ν) {L : ℕ}
    (hD : ∀ ℓ ≤ L, MemLp (levelDiff Pl ℓ) 2 ν) (N : ℕ → ℕ) :
    Integrable (mlmcVarEst Pl ω L N) μ :=
  integrable_finsetSum _ fun ℓ hℓ => (integrable_empVar_input hω
    (hD ℓ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ))) ℓ (N ℓ)).div_const _

/-- **The key estimate for the estimated variance** (for the confidence intervals of Collier et
al. with estimated variances, Giles 2015, §2.1, p. 8: "they prefer to use the Central Limit
Theorem to construct a confidence interval which bounds `E[P]` with a user-prescribed
confidence").  Let the inputs `ω^{(ℓ,n)}` be independent with law `ν`, let `ΔP_ℓ ∈ L²(ν)` with
kurtosis at most `K`, `E[(ΔP_ℓ − E ΔP_ℓ)⁴] ≤ K V_ℓ²`, for `ℓ ≤ L`, and let `N_ℓ ≥ n₀ ≥ 1` for
`ℓ ≤ L`.  Then `E|σ̂² − σ²| ≤ √(2K/n₀) σ²`, where `σ̂² = ∑_ℓ s_ℓ²/N_ℓ` (`mlmcVarEst`) and
`σ² = ∑_ℓ V_ℓ/N_ℓ = V[Y]`: the relative `L¹` error of `σ̂²` is at most `√(2K/min_ℓ N_ℓ)`, however
many levels there are.  Proof: `|σ̂² − σ²| ≤ ∑_ℓ |s_ℓ² − V_ℓ|/N_ℓ` and
`E|s_ℓ² − V_ℓ| ≤ √(2K/N_ℓ) V_ℓ` (`integral_abs_empVar_sub_le_sqrt`).  The hypotheses are this
formalisation's; the paper only cites Collier et al. -/
theorem integral_abs_mlmcVarEst_sub_le (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {L : ℕ} (hD : ∀ ℓ ≤ L, MemLp (levelDiff Pl ℓ) 2 ν)
    (h4 : ∀ ℓ ≤ L, Integrable (fun y => (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4) ν)
    {K : ℝ} (hK : ∀ ℓ ≤ L, ∫ y, (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4 ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ 2)
    {N : ℕ → ℕ} {n₀ : ℕ} (hn₀ : 0 < n₀) (hN : ∀ ℓ ≤ L, n₀ ≤ N ℓ) :
    ∫ x, |mlmcVarEst Pl ω L N x - ∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N ℓ| ∂μ ≤
      √(2 * K / n₀) * ∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N ℓ := by
  have hle : ∀ ℓ ∈ range (L + 1), ℓ ≤ L := fun ℓ hℓ => Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
  have hint : ∀ ℓ ∈ range (L + 1), Integrable (fun x =>
      |empVar (fun n => levelDiff Pl ℓ (ω (ℓ, n) x)) (N ℓ) - variance (levelDiff Pl ℓ) ν| /
        N ℓ) μ := fun ℓ hℓ =>
    ((integrable_empVar_input hω (hD ℓ (hle ℓ hℓ)) ℓ (N ℓ)).sub
      (integrable_const _)).abs.div_const _
  calc ∫ x, |mlmcVarEst Pl ω L N x - ∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N ℓ| ∂μ
      ≤ ∫ x, ∑ ℓ ∈ range (L + 1),
          |empVar (fun n => levelDiff Pl ℓ (ω (ℓ, n) x)) (N ℓ) - variance (levelDiff Pl ℓ) ν| /
            N ℓ ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_finsetSum _ hint)
          (ae_of_all _ fun x => abs_mlmcVarEst_sub_le Pl ω L N _ x)
    _ = ∑ ℓ ∈ range (L + 1), (∫ x,
          |empVar (fun n => levelDiff Pl ℓ (ω (ℓ, n) x)) (N ℓ) - variance (levelDiff Pl ℓ) ν| ∂μ) /
            N ℓ := by
        rw [integral_finsetSum _ hint]
        exact Finset.sum_congr rfl fun ℓ _ => integral_div _ _
    _ ≤ ∑ ℓ ∈ range (L + 1), √(2 * K / n₀) * (variance (levelDiff Pl ℓ) ν / N ℓ) := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        have hNℓ : 0 < N ℓ := hn₀.trans_le (hN ℓ (hle ℓ hℓ))
        have h1 := integral_abs_empVar_sub_le_sqrt hω hind (hD ℓ (hle ℓ hℓ)) (h4 ℓ (hle ℓ hℓ))
          (hK ℓ (hle ℓ hℓ)) ℓ hNℓ
        have h2 : √(2 * K / N ℓ) ≤ √(2 * K / n₀) := by
          rcases le_or_gt K 0 with hK0 | hKpos
          · rw [Real.sqrt_eq_zero'.2 (div_nonpos_of_nonpos_of_nonneg (by linarith)
              (Nat.cast_nonneg _))]
            exact Real.sqrt_nonneg _
          · exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity)
              (Nat.cast_pos.2 hn₀) (Nat.cast_le.2 (hN ℓ (hle ℓ hℓ))))
        have hV := variance_nonneg (levelDiff Pl ℓ) ν
        calc (∫ x, |empVar (fun n => levelDiff Pl ℓ (ω (ℓ, n) x)) (N ℓ) -
              variance (levelDiff Pl ℓ) ν| ∂μ) / N ℓ
            ≤ √(2 * K / N ℓ) * variance (levelDiff Pl ℓ) ν / N ℓ :=
              div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
          _ ≤ √(2 * K / n₀) * variance (levelDiff Pl ℓ) ν / N ℓ := by gcongr
          _ = √(2 * K / n₀) * (variance (levelDiff Pl ℓ) ν / N ℓ) := mul_div_assoc _ _ _
    _ = √(2 * K / n₀) * ∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N ℓ := by
        rw [Finset.mul_sum]

/-- **The estimated variance is consistent as the number of levels grows** (for the confidence
intervals of Collier et al. with estimated variances, Giles 2015, §2.1, p. 8: "they prefer to use
the Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence").  Let the inputs be independent with law `ν`, and for `k ∈ ℕ` let
`ΔP_ℓ ∈ L²(ν)` with kurtosis at most `K`, `E[(ΔP_ℓ − E ΔP_ℓ)⁴] ≤ K V_ℓ²`, on the levels `ℓ ≤ L_k`
used, and `min_{ℓ ≤ L_k} N_{k,ℓ} → ∞`.  Then `σ̂_k²` is relatively consistent:
`P(|σ̂_k² − σ_k²| > ε σ_k²) → 0` for every `ε > 0`, where `σ̂_k² = ∑_{ℓ ≤ L_k} s_{k,ℓ}²/N_{k,ℓ}`
(`mlmcVarEst`) and `σ_k² = ∑_{ℓ ≤ L_k} V_ℓ/N_{k,ℓ}`, with no condition on the growth of `L_k` and no
positivity of `σ_k²` (the event has no division).  Proof: Markov's inequality and
`E|σ̂_k² − σ_k²| ≤ √(2K/n₀) σ_k²` once `N_{k,ℓ} ≥ n₀` on all levels
(`integral_abs_mlmcVarEst_sub_le`).  The hypotheses are this formalisation's; the paper only cites
Collier et al. -/
theorem tendsto_measureReal_mlmcVarEst_rel (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {L : ℕ → ℕ} (hD : ∀ k, ∀ ℓ ≤ L k, MemLp (levelDiff Pl ℓ) 2 ν)
    (h4 : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k, ∫ y, (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4 ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ 2)
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k => μ.real {x | ε * ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ <
      |mlmcVarEst Pl ω (L k) (N k) x -
        ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ|}) atTop (𝓝 0) := by
  have htend : Tendsto (fun n : ℕ => √(2 * K / n) / ε) atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (2 * K))).div_const ε
    rwa [Real.sqrt_zero, zero_div] at h
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨n₁, hn₁⟩ := Metric.tendsto_atTop.1 htend η hη
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hNtop (n₁ + 1))
  refine ⟨k₀, fun k hk => ?_⟩
  have hb := integral_abs_mlmcVarEst_sub_le hω hind (hD k) (h4 k) (hK k) n₁.succ_pos (hk₀ k hk)
  have hM := measureReal_lt_le_of_integral_le (μ := μ) (fun x => abs_nonneg _)
    ((integrable_mlmcVarEst hω (hD k) (N k)).sub (integrable_const _)).abs
    (Finset.sum_nonneg fun ℓ _ => div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _))
    (Real.sqrt_nonneg _) hε hb
  have hc := hn₁ (n₁ + 1) (Nat.le_succ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hε.le)] at hc
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  exact hM.trans_lt hc

/-- **The estimated variance converges in ratio, for a growing number of levels** (for the
confidence intervals of Collier et al. with estimated variances, Giles 2015, §2.1, p. 8: "they
prefer to use the Central Limit Theorem to construct a confidence interval which bounds `E[P]` with
a user-prescribed confidence").  Under the hypotheses of `tendsto_measureReal_mlmcVarEst_rel`
(independent samples; `ΔP_ℓ ∈ L²` with kurtosis at most `K` on the levels `ℓ ≤ L_k` used;
`min_{ℓ ≤ L_k} N_{k,ℓ} → ∞`), and `σ_k² > 0` for large `k`, `σ̂_k²/σ_k² → 1` in probability, with no
condition on the growth of `L_k`.  The hypotheses are this formalisation's; the paper only cites
Collier et al. -/
theorem tendstoInMeasure_mlmcVarEst_div (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {L : ℕ → ℕ} (hD : ∀ k, ∀ ℓ ≤ L k, MemLp (levelDiff Pl ℓ) 2 ν)
    (h4 : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k, ∫ y, (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4 ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ 2)
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) :
    TendstoInMeasure μ (fun k x => mlmcVarEst Pl ω (L k) (N k) x /
        ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) atTop (fun _ => 1) :=
  tendstoInMeasure_div_of_rel hσ fun _ hε =>
    tendsto_measureReal_mlmcVarEst_rel hω hind hD h4 hK hNtop hε

/-- The relative consistency of the estimated standard deviation `σ̂_k = √(σ̂_k²)` for a growing
number of levels: under the hypotheses of `tendsto_measureReal_mlmcVarEst_rel`,
`P(|σ̂_k − σ_k| > ε σ_k) → 0` for every `ε > 0` (`tendsto_measureReal_sqrt_rel`). -/
lemma tendsto_measureReal_sqrt_mlmcVarEst_rel (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {L : ℕ → ℕ} (hD : ∀ k, ∀ ℓ ≤ L k, MemLp (levelDiff Pl ℓ) 2 ν)
    (h4 : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k, ∫ y, (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4 ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ 2)
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k => μ.real {x |
      ε * √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) <
      |√(mlmcVarEst Pl ω (L k) (N k) x) -
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)|}) atTop (𝓝 0) :=
  tendsto_measureReal_sqrt_rel (f := fun k x => mlmcVarEst Pl ω (L k) (N k) x)
    (fun _ x => mlmcVarEst_nonneg _ _ _ _ x)
    (fun _ => Finset.sum_nonneg fun _ _ => div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _))
    (fun _ hε => tendsto_measureReal_mlmcVarEst_rel hω hind hD h4 hK hNtop hε) hε

/-- The empirical variance of one level is relatively consistent (strong law of large numbers):
if `g ∈ L²(ν)` and `N_k → ∞`, then `P(|s_{N_k}² − V[g]| > ε V[g]) → 0` for every `ε > 0`.  For
`V[g] = 0` the samples are almost surely constant and the event is null. -/
lemma tendsto_measureReal_empVar_rel (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {g : Ω₀ → ℝ} (hg : MemLp g 2 ν) (i : ℕ) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => μ.real {x | ε * variance g ν <
      |empVar (fun n => g (ω (i, n) x)) (N k) - variance g ν|}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  rcases (variance_nonneg g ν).eq_or_lt with hV0 | hVpos
  · -- `V[g] = 0`: the samples are almost surely constant
    have hga := ae_eq_integral_of_variance_eq_zero hg hV0.symm
    have hae : ∀ᵐ x ∂μ, ∀ n, g (ω (i, n) x) = ∫ y, g y ∂ν := by
      rw [ae_all_iff]
      exact fun n => (hω (i, n)).quasiMeasurePreserving.ae hga
    have hnull : μ {x | ¬ ∀ n, g (ω (i, n) x) = ∫ y, g y ∂ν} = 0 := ae_iff.1 hae
    refine tendsto_const_nhds.congr fun k => ?_
    symm
    refine le_antisymm ?_ measureReal_nonneg
    have hle : μ.real {x | ε * variance g ν <
        |empVar (fun n => g (ω (i, n) x)) (N k) - variance g ν|} ≤
        μ.real {x | ¬ ∀ n, g (ω (i, n) x) = ∫ y, g y ∂ν} := by
      refine measureReal_mono fun x hx => ?_
      simp only [Set.mem_ofPred_eq] at hx ⊢
      intro hall
      rw [show (fun n => g (ω (i, n) x)) = fun _ => ∫ y, g y ∂ν from funext hall,
        empVar_const, ← hV0, mul_zero, sub_zero, abs_zero] at hx
      exact lt_irrefl _ hx
    rwa [measureReal_def μ {x | ¬ ∀ n, g (ω (i, n) x) = ∫ y, g y ∂ν}, hnull,
      ENNReal.toReal_zero] at hle
  · have hm := tendstoInMeasure_empVar_input hω hind hg i
    rw [tendstoInMeasure_iff_measureReal_dist] at hm
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((hm (ε * variance g ν) (mul_pos hε hVpos)).comp hN) (fun k => measureReal_nonneg)
      fun k => measureReal_mono fun x hx => ?_
    simp only [Set.mem_ofPred_eq, Real.dist_eq] at hx ⊢
    exact hx.le

/-- **The estimated variance is consistent for a fixed number of levels** (for the confidence
intervals of Collier et al. with estimated variances, Giles 2015, §2.1, p. 8: "they prefer to use
the Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence").  Let the inputs be independent with law `ν`, let `L` be fixed,
`ΔP_ℓ ∈ L²(ν)` for `ℓ ≤ L`, and let `N_{k,ℓ} → ∞` for every `ℓ ≤ L` (at arbitrary rates).  Then
`P(|σ̂_k² − σ_k²| > ε σ_k²) → 0` for every `ε > 0`, where `σ̂_k² = ∑_{ℓ ≤ L} s_{k,ℓ}²/N_{k,ℓ}`
(`mlmcVarEst`) and `σ_k² = ∑_{ℓ ≤ L} V_ℓ/N_{k,ℓ}`.  Only second moments are needed: each `s_{k,ℓ}²`
is relatively consistent by the strong law of large numbers (`tendsto_measureReal_empVar_rel`), and
if `|s_{k,ℓ}² − V_ℓ| ≤ ε V_ℓ` on every level then `|σ̂_k² − σ_k²| ≤ ε σ_k²`.  The hypotheses are
this formalisation's; the paper only cites Collier et al. -/
theorem tendsto_measureReal_mlmcVarEst_rel_fixed (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {L : ℕ} (hD : ∀ ℓ ≤ L, MemLp (levelDiff Pl ℓ) 2 ν)
    {N : ℕ → ℕ → ℕ} (hN : ∀ ℓ ≤ L, Tendsto (fun k => N k ℓ) atTop atTop) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k => μ.real {x | ε * ∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ <
      |mlmcVarEst Pl ω L (N k) x -
        ∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ|}) atTop (𝓝 0) := by
  have hle : ∀ ℓ ∈ range (L + 1), ℓ ≤ L := fun ℓ hℓ => Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
  have hsum : Tendsto (fun k => ∑ ℓ ∈ range (L + 1), μ.real {x | ε * variance (levelDiff Pl ℓ) ν <
      |empVar (fun n => levelDiff Pl ℓ (ω (ℓ, n) x)) (N k ℓ) - variance (levelDiff Pl ℓ) ν|})
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (range (L + 1)) fun ℓ hℓ =>
      tendsto_measureReal_empVar_rel hω hind (hD ℓ (hle ℓ hℓ)) ℓ (hN ℓ (hle ℓ hℓ)) hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun k => measureReal_nonneg) fun k => ?_
  refine (measureReal_mono (fun x hx => ?_) (measure_ne_top μ _)).trans
    (measureReal_biUnion_finset_le (range (L + 1))
    fun ℓ => {x | ε * variance (levelDiff Pl ℓ) ν <
      |empVar (fun n => levelDiff Pl ℓ (ω (ℓ, n) x)) (N k ℓ) - variance (levelDiff Pl ℓ) ν|})
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] at hx ⊢
  by_contra hno
  push Not at hno
  have h1 := abs_mlmcVarEst_sub_le Pl ω L (N k) (fun ℓ => variance (levelDiff Pl ℓ) ν) x
  have h2 : ∑ ℓ ∈ range (L + 1),
      |empVar (fun n => levelDiff Pl ℓ (ω (ℓ, n) x)) (N k ℓ) - variance (levelDiff Pl ℓ) ν| /
        N k ℓ ≤ ∑ ℓ ∈ range (L + 1), ε * (variance (levelDiff Pl ℓ) ν / N k ℓ) :=
    Finset.sum_le_sum fun ℓ hℓ => by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hno ℓ hℓ) (Nat.cast_nonneg _)
  rw [← Finset.mul_sum] at h2
  linarith

/-- For a fixed number of levels with `N_{k,ℓ} → ∞` on every level and some `V_ℓ > 0`, `ℓ ≤ L`,
eventually `σ_k² = ∑_{ℓ ≤ L} V_ℓ/N_{k,ℓ} > 0`. -/
lemma eventually_pos_sum_variance_div (Pl : ℕ → Ω₀ → ℝ) (ν : Measure Ω₀) {L : ℕ}
    (hV : ∃ ℓ ≤ L, 0 < variance (levelDiff Pl ℓ) ν) {N : ℕ → ℕ → ℕ}
    (hN : ∀ ℓ ≤ L, Tendsto (fun k => N k ℓ) atTop atTop) :
    ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ := by
  obtain ⟨ℓ₀, hℓ₀, hV0⟩ := hV
  filter_upwards [(hN ℓ₀ hℓ₀).eventually_gt_atTop 0] with k hk
  exact (div_pos hV0 (Nat.cast_pos.2 hk)).trans_le (Finset.single_le_sum
    (f := fun ℓ => variance (levelDiff Pl ℓ) ν / N k ℓ)
    (fun ℓ _ => div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hℓ₀)))

/-- **The estimated standard deviation converges in ratio, for a fixed number of levels** (for the
confidence intervals of Collier et al. with estimated variances, Giles 2015, §2.1, p. 8: "they
prefer to use the Central Limit Theorem to construct a confidence interval which bounds `E[P]` with
a user-prescribed confidence").  Let the inputs be independent with law `ν`, `L` fixed,
`ΔP_ℓ ∈ L²(ν)` for `ℓ ≤ L` with `V_ℓ > 0` for some `ℓ ≤ L`, and `N_{k,ℓ} → ∞` for every `ℓ ≤ L`.
Then `σ̂_k/σ_k → 1` in probability, where `σ̂_k = √(∑_ℓ s_{k,ℓ}²/N_{k,ℓ})` and
`σ_k = √(∑_ℓ V_ℓ/N_{k,ℓ})` (strong law on every level, `tendsto_measureReal_mlmcVarEst_rel_fixed`).
Only second moments are needed.  The hypotheses are this formalisation's; the paper only cites
Collier et al. -/
theorem tendstoInMeasure_sqrt_mlmcVarEst_div_fixed (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {L : ℕ} (hD : ∀ ℓ ≤ L, MemLp (levelDiff Pl ℓ) 2 ν)
    (hV : ∃ ℓ ≤ L, 0 < variance (levelDiff Pl ℓ) ν) {N : ℕ → ℕ → ℕ}
    (hN : ∀ ℓ ≤ L, Tendsto (fun k => N k ℓ) atTop atTop) :
    TendstoInMeasure μ (fun k x => √(mlmcVarEst Pl ω L (N k) x) /
        √(∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)) atTop (fun _ => 1) :=
  tendstoInMeasure_div_of_rel ((eventually_pos_sum_variance_div Pl ν hV hN).mono
      fun _ hk => Real.sqrt_pos.2 hk) fun _ hε =>
    tendsto_measureReal_sqrt_rel (f := fun k x => mlmcVarEst Pl ω L (N k) x)
      (fun _ x => mlmcVarEst_nonneg _ _ _ _ x)
      (fun _ => Finset.sum_nonneg fun _ _ => div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _))
      (fun _ hε' => tendsto_measureReal_mlmcVarEst_rel_fixed hω hind hD hN hε') hε

/-! ### The central limit theorem for a fixed number of levels and arbitrary sample sizes -/

/-- The fixed-level central limit theorem when `N_{k,ℓ} ≥ 1` and `σ_k > 0` for every `k` (the core
of `tendstoInDistribution_mlmcEstimator_fixed`). -/
lemma tendstoInDistribution_mlmcEstimator_fixed_of_forall {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {L : ℕ}
    (hPl : ∀ ℓ ≤ L, MemLp (Pl ℓ) 2 ν) {N : ℕ → ℕ → ℕ}
    (hN : ∀ ℓ ≤ L, Tendsto (fun k => N k ℓ) atTop atTop) (hN1 : ∀ k, ∀ ℓ ≤ L, 0 < N k ℓ)
    (hσ : ∀ k, 0 < ∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k x => (mlmcEstimator Pl ω L (N k) x - ∫ y, Pl L y ∂ν) /
        √(∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)) atTop Z (fun _ => μ) P' := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℝ, ∀ ℓ, ∫ y, levelDiff Pl ℓ y ∂ν = m ℓ := ⟨_, fun _ => rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → ℝ, ∀ k,
      √(∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) = σ k := ⟨_, fun _ => rfl⟩
  have hσpos : ∀ k, 0 < σ k := fun k => hσdef k ▸ Real.sqrt_pos.2 (hσ k)
  have hσsq : ∀ k, σ k ^ 2 = ∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ :=
    fun k => by rw [← hσdef k, Real.sq_sqrt (hσ k).le]
  simp only [hσdef]
  have hD : ∀ ℓ ≤ L, MemLp (levelDiff Pl ℓ) 2 ν := memLp_levelDiff_of_le hPl
  -- the triangular array of normalised samples `g_{k,ℓ}(ω^{(ℓ,n)})`
  set g : ℕ → ℕ → Ω₀ → ℝ := fun k ℓ y => ((N k ℓ : ℝ) * σ k)⁻¹ * (levelDiff Pl ℓ y - m ℓ)
    with hg
  have hgL2 : ∀ k, ∀ ℓ ≤ L, MemLp (g k ℓ) 2 ν := fun k ℓ hℓ =>
    ((hD ℓ hℓ).sub (memLp_const _)).const_mul _
  have hgm : ∀ k, ∀ ℓ ≤ L, AEMeasurable (g k ℓ) ν := fun k ℓ hℓ =>
    (hgL2 k ℓ hℓ).aestronglyMeasurable.aemeasurable
  have hg0 : ∀ k, ∀ ℓ ≤ L, ∫ y, g k ℓ y ∂ν = 0 := by
    intro k ℓ hℓ
    simp only [hg]
    rw [integral_const_mul, integral_sub ((hD ℓ hℓ).integrable one_le_two)
      (integrable_const _), integral_const, hm]
    simp
  have hgvar : ∀ k, ∀ ℓ ≤ L, Var[g k ℓ; ν] =
      ((N k ℓ : ℝ) * σ k)⁻¹ ^ 2 * variance (levelDiff Pl ℓ) ν := by
    intro k ℓ hℓ
    simp only [hg]
    rw [variance_const_mul, variance_sub_const (hD ℓ hℓ).aestronglyMeasurable]
  have hfun : (fun k x => (mlmcEstimator Pl ω L (N k) x - ∫ y, Pl L y ∂ν) / σ k) =
      fun k x => ∑ q ∈ (range (L + 1)).sigma (fun ℓ => range (N k ℓ)),
        g k q.1 (ω (q.1, q.2) x) := by
    funext k x
    rw [← sum_integral_levelDiff_of_le fun ℓ hℓ => (hPl ℓ hℓ).integrable one_le_two]
    simp only [hm]
    exact mlmcEstimator_sub_div_eq_sum Pl ω L (hN1 k) m (σ k) x
  rw [hfun]
  have hle : ∀ k, ∀ q ∈ (range (L + 1)).sigma (fun ℓ => range (N k ℓ)), q.1 ≤ L :=
    fun k q hq => Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_sigma.1 hq).1)
  refine tendstoInDistribution_lindeberg (Ω := fun _ => Ω) (P := fun _ => μ)
    (s := fun k => (range (L + 1)).sigma fun ℓ => range (N k ℓ))
    (X := fun k q x => g k q.1 (ω (q.1, q.2) x)) (fun k => ?_)
    (fun k q hq => (hgL2 k q.1 (hle k q hq)).comp_measurePreserving (hω (q.1, q.2)))
    (fun k q hq => ?_) (fun k => ?_) (fun ε hε => ?_) hZ
  · -- independence: distinct samples use distinct inputs
    refine iIndepFun_comp_inputs hω hind
      (e := fun q : ((range (L + 1)).sigma fun ℓ => range (N k ℓ)) => (q.1.1, q.1.2)) ?_
      (g := fun q => g k q.1.1) fun q => hgm k q.1.1 (hle k q.1 q.2)
    rintro ⟨⟨a, b⟩, _⟩ ⟨⟨c, d⟩, _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · -- centring
    rw [integral_comp_of_measurePreserving (hω _)
      (hgL2 k q.1 (hle k q hq)).aestronglyMeasurable, hg0 k q.1 (hle k q hq)]
  · -- the variances sum to one
    rw [Finset.sum_congr rfl fun q hq =>
        (hω (q.1, q.2)).variance_fun_comp (hgm k q.1 (hle k q hq)), Finset.sum_sigma,
      ← div_self (pow_pos (hσpos k) 2).ne', hσsq k, Finset.sum_div]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓL : ℓ ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    have hNℓ : (N k ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hN1 k ℓ hℓL).ne'
    have hσk : σ k ≠ 0 := (hσpos k).ne'
    simp only [hgvar k ℓ hℓL, Finset.sum_const, card_range, nsmul_eq_mul]
    rw [← hσsq k]
    field_simp
  · -- Lindeberg's condition, level by level (`tendsto_lindebergTail_div`)
    have hterm : ∀ k, ∀ q ∈ (range (L + 1)).sigma (fun ℓ => range (N k ℓ)),
        ∫ x in {x | ε < |g k q.1 (ω (q.1, q.2) x)|}, g k q.1 (ω (q.1, q.2) x) ^ 2 ∂μ =
          ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (g k q.1 y) ∂ν := by
      intro k q hq
      rw [← integral_lindebergIntegrand
        (aemeasurable_comp_input hω (hgm k q.1 (hle k q hq)) (q.1, q.2)) ε]
      exact integral_comp_of_measurePreserving (hω (q.1, q.2))
        (f := fun y => {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (g k q.1 y))
        ((measurable_lindebergIntegrand ε).comp_aemeasurable
          (hgm k q.1 (hle k q hq))).aestronglyMeasurable
    have hgt : ∀ k, ∀ ℓ ≤ L, ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (g k ℓ y) ∂ν =
        ((N k ℓ : ℝ) * σ k)⁻¹ ^ 2 * ∫ y, {z : ℝ | ε * (N k ℓ * σ k) < |z|}.indicator
          (fun z => z ^ 2) (levelDiff Pl ℓ y - m ℓ) ∂ν := by
      intro k ℓ hℓ
      have hNpos : (0 : ℝ) < N k ℓ := Nat.cast_pos.2 (hN1 k ℓ hℓ)
      simp only [hg]
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [lindebergIntegrand_const_mul (inv_pos.2 (mul_pos hNpos (hσpos k))), div_inv_eq_mul]
    have hle2 : ∀ ℓ ≤ L, ∀ k, ∫ y, (levelDiff Pl ℓ y - m ℓ) ^ 2 ∂ν ≤ N k ℓ * σ k ^ 2 := by
      intro ℓ hℓ k
      have hNpos : (0 : ℝ) < N k ℓ := Nat.cast_pos.2 (hN1 k ℓ hℓ)
      have hV : ∫ y, (levelDiff Pl ℓ y - m ℓ) ^ 2 ∂ν = variance (levelDiff Pl ℓ) ν := by
        rw [variance_eq_integral (hD ℓ hℓ).aestronglyMeasurable.aemeasurable, hm]
      have hsingle : variance (levelDiff Pl ℓ) ν / N k ℓ ≤ σ k ^ 2 := by
        rw [hσsq k]
        exact Finset.single_le_sum (f := fun ℓ => variance (levelDiff Pl ℓ) ν / N k ℓ)
          (fun ℓ _ => div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _))
          (Finset.mem_range.2 (Nat.lt_succ_of_le hℓ))
      rw [hV]
      rw [div_le_iff₀ hNpos] at hsingle
      linarith
    have hlim := tendsto_finsetSum (range (L + 1)) fun ℓ hℓ =>
      tendsto_lindebergTail_div (g := fun y => levelDiff Pl ℓ y - m ℓ)
        ((hD ℓ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ))).sub (memLp_const _))
        (hN ℓ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ))) hσpos
        (hle2 ℓ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ))) hε
    simp only [Finset.sum_const_zero] at hlim
    refine hlim.congr fun k => ?_
    rw [Finset.sum_congr rfl (hterm k), Finset.sum_sigma]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓL : ℓ ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    have hNpos : (0 : ℝ) < N k ℓ := Nat.cast_pos.2 (hN1 k ℓ hℓL)
    have hσk := hσpos k
    simp only [hgt k ℓ hℓL, Finset.sum_const, card_range, nsmul_eq_mul]
    field_simp

/-- **The multilevel central limit theorem for a fixed number of levels and arbitrary sample
sizes** (Giles 2015, §2.1, p. 8: "This exploits the fact that the multilevel correction `Y_ℓ` on
each level is asymptotically Normally-distributed, and therefore so is `Y`.").  Let the inputs
`ω^{(ℓ,n)}` be independent with law `ν`, `L` fixed, `P_0, …, P_L ∈ L²(ν)` with `V_ℓ > 0` for some
`ℓ ≤ L`, and let `N_{k,ℓ} → ∞` for every `ℓ ≤ L`, at arbitrary, unrelated rates.  Then
`(Y_k − E[P_L])/σ_k → N(0, 1)` in distribution, where `Y_k` is the estimator (2.2) with `N_{k,ℓ}`
samples on level `ℓ` and `σ_k² = ∑_{ℓ ≤ L} V_ℓ/N_{k,ℓ}`.  Only second moments are needed: the
normalised samples form a triangular array satisfying Lindeberg's condition
(`tendsto_lindebergTail_div` on every level, `tendstoInDistribution_lindeberg`).  This
generalises the non-degenerate case of `tendstoInDistribution_mlmcEstimator` (`N_ℓ = m_ℓ n` with
some `V_ℓ > 0`, normalised by `√n` instead of `σ_k`) to arbitrary rates; that theorem also covers
the degenerate case of all `V_ℓ = 0` (limit `N(0, 0)`).  The hypotheses are this formalisation's;
the paper only cites Collier et al. -/
theorem tendstoInDistribution_mlmcEstimator_fixed {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    (hind : iIndepFun ω μ) {L : ℕ} (hPl : ∀ ℓ ≤ L, MemLp (Pl ℓ) 2 ν)
    (hV : ∃ ℓ ≤ L, 0 < variance (levelDiff Pl ℓ) ν) {N : ℕ → ℕ → ℕ}
    (hN : ∀ ℓ ≤ L, Tendsto (fun k => N k ℓ) atTop atTop) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k x => (mlmcEstimator Pl ω L (N k) x - ∫ y, Pl L y ∂ν) /
        √(∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)) atTop Z (fun _ => μ) P' := by
  have hN1 : ∀ᶠ k in atTop, ∀ ℓ ∈ range (L + 1), 0 < N k ℓ :=
    (eventually_all_finset _).2 fun ℓ hℓ =>
      (hN ℓ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ))).eventually_gt_atTop 0
  obtain ⟨k₀, hk₀⟩ := (hN1.and (eventually_pos_sum_variance_div Pl ν hV hN)).exists_forall_of_atTop
  exact tendstoInDistribution_of_comp_add k₀
    (fun k => aemeasurable_mlmcEstimator_sub_div hω hPl _ _ _)
    (tendstoInDistribution_mlmcEstimator_fixed_of_forall (N := fun k => N (k + k₀)) hω hind hPl
      (fun ℓ hℓ => (hN ℓ hℓ).comp (tendsto_add_atTop_nat k₀))
      (fun k ℓ hℓ => (hk₀ (k + k₀) (Nat.le_add_left _ _)).1 ℓ
        (Finset.mem_range.2 (Nat.lt_succ_of_le hℓ)))
      (fun k => (hk₀ (k + k₀) (Nat.le_add_left _ _)).2) hZ)

/-! ### Confidence intervals with the estimated standard deviation -/

/-- **The confidence interval with estimated variances, for a fixed number of levels** (Giles 2015,
§2.1, p. 8: "Instead of bounding the Mean Square Error, they prefer to use the Central Limit
Theorem to construct a confidence interval which bounds `E[P]` with a user-prescribed
confidence.").  Let the inputs be independent with law `ν`, `L` fixed, `P_0, …, P_L ∈ L²(ν)` with
`V_ℓ > 0` for some `ℓ ≤ L`, and `N_{k,ℓ} → ∞` for every `ℓ ≤ L` (at arbitrary rates).  Then for
every `z ≥ 0`, `P(|Y_k − E[P_L]| ≤ z σ̂_k) → 2Φ(z) − 1`, where `σ̂_k² = ∑_{ℓ ≤ L} s_{k,ℓ}²/N_{k,ℓ}`
(`mlmcVarEst`) is computed from the same samples as `Y_k`, and `Φ = cdf (gaussianReal 0 1)`: the
practical interval `Y_k ± z σ̂_k` covers `E[P_L]` with asymptotic confidence `2Φ(z) − 1`.  The
event is stated without division by `σ̂_k`.  Proof: Slutsky's lemma
(`tendsto_measureReal_abs_le_mul_of_rel`) from the central limit theorem
`tendstoInDistribution_mlmcEstimator_fixed` and `σ̂_k/σ_k → 1`
(`tendsto_measureReal_mlmcVarEst_rel_fixed`, the strong law).  Only second moments are needed.
The hypotheses are this formalisation's; the paper only cites Collier et al. -/
theorem tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_fixed
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {L : ℕ}
    (hPl : ∀ ℓ ≤ L, MemLp (Pl ℓ) 2 ν) (hV : ∃ ℓ ≤ L, 0 < variance (levelDiff Pl ℓ) ν)
    {N : ℕ → ℕ → ℕ} (hN : ∀ ℓ ≤ L, Tendsto (fun k => N k ℓ) atTop atTop) {z : ℝ}
    (hz : 0 ≤ z) :
    Tendsto (fun k => μ.real {x | |mlmcEstimator Pl ω L (N k) x - ∫ y, Pl L y ∂ν| ≤
        z * √(mlmcVarEst Pl ω L (N k) x)}) atTop (𝓝 (2 * cdf (gaussianReal 0 1) z - 1)) := by
  have hD : ∀ ℓ ≤ L, MemLp (levelDiff Pl ℓ) 2 ν := memLp_levelDiff_of_le hPl
  refine tendsto_measureReal_abs_le_mul_of_rel
    (S := fun k x => mlmcEstimator Pl ω L (N k) x - ∫ y, Pl L y ∂ν)
    (σ := fun k => √(∑ ℓ ∈ range (L + 1), variance (levelDiff Pl ℓ) ν / N k ℓ))
    (fun z' hz' => ?_) (fun ε hε => ?_) hz
  · have h := tendsto_measureReal_abs_le_of_tendstoInDistribution
      (tendstoInDistribution_mlmcEstimator_fixed (P' := gaussianReal 0 1) (Z := id) hω hind hPl
        hV hN HasLaw.id) HasLaw.id hz'
    refine h.congr' ((eventually_pos_sum_variance_div Pl ν hV hN).mono fun k hk => ?_)
    show μ.real _ = μ.real _
    congr 1
    ext x
    have hs := Real.sqrt_pos.2 hk
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hs, div_le_iff₀ hs]
  · exact tendsto_measureReal_sqrt_rel (f := fun k x => mlmcVarEst Pl ω L (N k) x)
      (fun _ x => mlmcVarEst_nonneg _ _ _ _ x)
      (fun _ => Finset.sum_nonneg fun _ _ => div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _))
      (fun _ hε' => tendsto_measureReal_mlmcVarEst_rel_fixed hω hind hD hN hε') hε

/-- `|x|^{2+2} = x⁴`: the moment `M_ℓ = E|ΔP_ℓ − E ΔP_ℓ|^{2+δ}` of `MlmcLean/MLMCCentralLimit.lean`
for `δ = 2` is the centred fourth moment. -/
lemma abs_rpow_two_add_two (x : ℝ) : |x| ^ ((2 : ℝ) + 2) = x ^ 4 := by
  rw [show (2 : ℝ) + 2 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← abs_pow,
    abs_of_nonneg (by positivity)]

/-- `V^{1+2/2} = V²`: the bound `M_ℓ ≤ K V_ℓ^{1+δ/2}` of `MlmcLean/MLMCCentralLimit.lean` for
`δ = 2` is the kurtosis bound `E[(ΔP_ℓ − E ΔP_ℓ)⁴] ≤ K V_ℓ²`. -/
lemma rpow_one_add_two_div_two (V : ℝ) : V ^ ((1 : ℝ) + 2 / 2) = V ^ 2 := by
  rw [show (1 : ℝ) + 2 / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The confidence interval with estimated variances, for a growing number of levels** (Giles
2015, §2.1, p. 8: "Instead of bounding the Mean Square Error, they prefer to use the Central Limit
Theorem to construct a confidence interval which bounds `E[P]` with a user-prescribed
confidence. This exploits the fact that the multilevel correction `Y_ℓ` on each level is
asymptotically Normally-distributed, and therefore so is `Y`.").  Let the inputs be independent
with law `ν`, and for `k ∈ ℕ` let `P_0, …, P_{L_k} ∈ L²(ν)` and let the corrections used have
bounded kurtosis, `E[(ΔP_ℓ − E ΔP_ℓ)⁴] ≤ K V_ℓ² < ∞` for `ℓ ≤ L_k` (the setting of
`tendstoInDistribution_mlmcEstimator_of_moment_le` with `δ = 2`); let
`min_{ℓ ≤ L_k} N_{k,ℓ} → ∞` and `σ_k² = ∑_{ℓ ≤ L_k} V_ℓ/N_{k,ℓ} > 0` for large `k`.  Then for
every `z ≥ 0`, `P(|Y_k − E[P_{L_k}]| ≤ z σ̂_k) → 2Φ(z) − 1`, where
`σ̂_k² = ∑_{ℓ ≤ L_k} s_{k,ℓ}²/N_{k,ℓ}` (`mlmcVarEst`) uses the samples of `Y_k`; there is no
condition on the growth of `L_k`.  Proof: Slutsky's lemma
(`tendsto_measureReal_abs_le_mul_of_rel`) from the interval with the exact `σ_k`
(`tendsto_measureReal_abs_mlmcEstimator_sub_le_of_moment_le`) and the relative consistency of
`σ̂_k` (`tendsto_measureReal_mlmcVarEst_rel`, from `E|σ̂_k² − σ_k²| ≤ √(2K/min_ℓ N_{k,ℓ}) σ_k²`).
The hypotheses are this formalisation's; the paper only cites Collier et al. -/
theorem tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {L : ℕ → ℕ}
    (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν)
    (h4 : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k, ∫ y, (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4 ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ 2)
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun k => μ.real {x | |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν| ≤
        z * √(mlmcVarEst Pl ω (L k) (N k) x)}) atTop
      (𝓝 (2 * cdf (gaussianReal 0 1) z - 1)) := by
  have hD : ∀ k, ∀ ℓ ≤ L k, MemLp (levelDiff Pl ℓ) 2 ν := fun k => memLp_levelDiff_of_le (hPl k)
  have hM : ∀ k, ∀ ℓ ≤ L k, Integrable
      (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ ((2 : ℝ) + 2)) ν := by
    simpa only [abs_rpow_two_add_two] using h4
  have hK' : ∀ k, ∀ ℓ ≤ L k,
      ∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ ((2 : ℝ) + 2) ∂ν ≤
        K * variance (levelDiff Pl ℓ) ν ^ ((1 : ℝ) + 2 / 2) := by
    simpa only [abs_rpow_two_add_two, rpow_one_add_two_div_two] using hK
  exact tendsto_measureReal_abs_le_mul_of_rel
    (fun z' hz' => tendsto_measureReal_abs_mlmcEstimator_sub_le_of_moment_le hω hind hPl two_pos
      hM hK' hNtop hσ hz')
    (fun _ hε => tendsto_measureReal_sqrt_mlmcVarEst_rel hω hind hD h4 hK hNtop hε) hz

/-- **The confidence interval around `E[P]` with estimated variances** (Giles 2015, §2.1, p. 8:
"they prefer to use the Central Limit Theorem to construct a confidence interval which bounds
`E[P]` with a user-prescribed confidence").  Under the hypotheses of
`tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd` (independent samples; `P_ℓ ∈ L²` and kurtosis
of `ΔP_ℓ` at most `K` on the levels `ℓ ≤ L_k` used; `min_ℓ N_{k,ℓ} → ∞`; `σ_k > 0` for large
`k`), if the bias is small against the standard deviation, `(E[P_{L_k}] − E[P])/σ_k → 0`, then for
every `z ≥ 0`, `P(|Y_k − E[P]| ≤ z σ̂_k) → 2Φ(z) − 1`: the practical interval `Y_k ± z σ̂_k`
covers `E[P]` itself with asymptotic confidence `2Φ(z) − 1`.  Proof: Slutsky's lemma
(`tendsto_measureReal_abs_le_mul_of_rel`) from
`tendsto_measureReal_abs_mlmcEstimator_sub_le_of_bias` with `δ = 2`.  Only the number
`E[P] = ∫ P dν` enters, so no integrability of `P` is assumed (the statement holds for every real
number in place of `∫ P dν`).  The hypotheses are this formalisation's; the paper only cites
Collier et al. -/
theorem tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd_of_bias
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {L : ℕ → ℕ}
    (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν)
    (h4 : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k, ∫ y, (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4 ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ 2)
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    {P : Ω₀ → ℝ}
    (hbias : Tendsto (fun k => (∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν) /
      √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)) atTop (𝓝 0))
    {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun k => μ.real {x | |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν| ≤
        z * √(mlmcVarEst Pl ω (L k) (N k) x)}) atTop
      (𝓝 (2 * cdf (gaussianReal 0 1) z - 1)) := by
  have hD : ∀ k, ∀ ℓ ≤ L k, MemLp (levelDiff Pl ℓ) 2 ν := fun k => memLp_levelDiff_of_le (hPl k)
  have hM : ∀ k, ∀ ℓ ≤ L k, Integrable
      (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ ((2 : ℝ) + 2)) ν := by
    simpa only [abs_rpow_two_add_two] using h4
  have hK' : ∀ k, ∀ ℓ ≤ L k,
      ∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ ((2 : ℝ) + 2) ∂ν ≤
        K * variance (levelDiff Pl ℓ) ν ^ ((1 : ℝ) + 2 / 2) := by
    simpa only [abs_rpow_two_add_two, rpow_one_add_two_div_two] using hK
  exact tendsto_measureReal_abs_le_mul_of_rel
    (fun z' hz' => tendsto_measureReal_abs_mlmcEstimator_sub_le_of_bias hω hind hPl
      (zero_le_two) hM ((hNtop 1).mono fun _ hk ℓ hℓ => hk ℓ hℓ) hσ
      (tendsto_mlmcLyapunovRatio_of_moment_le two_pos hK' hNtop hσ) hbias hz')
    (fun _ hε => tendsto_measureReal_sqrt_mlmcVarEst_rel hω hind hD h4 hK hNtop hε) hz

/-- **The interval of Collier et al. with estimated variances and a bias bound** (Giles 2015,
§2.1, p. 8: "Instead of bounding the Mean Square Error, they prefer to use the Central Limit
Theorem to construct a confidence interval which bounds `E[P]` with a user-prescribed
confidence.").  Under the hypotheses of `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd`, let
`b_k` bound the bias, `|E[P_{L_k}] − E[P]| ≤ b_k` for large `k` (Collier et al. take
`b_k = (1 − θ) TOL_k`).  Then the computable interval `Y_k ± (z σ̂_k + b_k)` covers `E[P]` with
asymptotic confidence at least `2Φ(z) − 1`: for every real `z` and every `η > 0`, eventually
`P(|Y_k − E[P]| ≤ z σ̂_k + b_k) > 2Φ(z) − 1 − η`.  No relation between the bias and `σ_k` is
needed, and `E[P] = ∫ P dν` may be replaced by any real number.  The hypotheses are this
formalisation's; the paper only cites Collier et al.  Proof: for `z ≤ 0`, `2Φ(z) − 1 ≤ 0`
(`two_mul_cdf_gaussianReal_sub_one_nonpos`) and the bound is trivial; for `z ≥ 0`,
`{|Y_k − E[P_{L_k}]| ≤ z σ̂_k} ⊆ {|Y_k − E[P]| ≤ z σ̂_k + b_k}` and
`tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd` applies. -/
theorem eventually_lt_measureReal_abs_mlmcEstimator_sub_le_estSd_add
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {L : ℕ → ℕ}
    (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν)
    (h4 : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k, ∫ y, (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4 ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ 2)
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    {P : Ω₀ → ℝ} {b : ℕ → ℝ} (hb : ∀ᶠ k in atTop, |∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν| ≤ b k)
    (z : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, 2 * cdf (gaussianReal 0 1) z - 1 - η <
      μ.real {x | |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν| ≤
        z * √(mlmcVarEst Pl ω (L k) (N k) x) + b k} := by
  rcases lt_or_ge z 0 with hneg | hz
  · -- `z < 0`: `2Φ(z) − 1 ≤ 0`
    exact Eventually.of_forall fun k =>
      (sub_neg.2 ((two_mul_cdf_gaussianReal_sub_one_nonpos hneg.le).trans_lt hη)).trans_le
        measureReal_nonneg
  have h := tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd hω hind hPl h4 hK hNtop hσ hz
  filter_upwards [h.eventually (lt_mem_nhds (sub_lt_self _ hη)), hb] with k hk hbk
  refine hk.trans_le (measureReal_mono fun x hx => ?_)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  calc |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν|
      = |(mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν) +
          (∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν)| := by rw [sub_add_sub_cancel]
    _ ≤ |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν| +
          |∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν| := abs_add_le _ _
    _ ≤ z * √(mlmcVarEst Pl ω (L k) (N k) x) + b k := add_le_add hx hbk

omit [IsProbabilityMeasure μ] in
/-- The interval `Y ± z σ̂` is a null-measurable event (the estimator and `σ̂` are a.e.
measurable when `P_0, …, P_L` are square integrable). -/
lemma nullMeasurableSet_abs_mlmcEstimator_sub_le (hω : ∀ p, MeasurePreserving (ω p) μ ν)
    {L : ℕ} (hPl : ∀ ℓ ≤ L, MemLp (Pl ℓ) 2 ν) (N : ℕ → ℕ) (c z : ℝ) :
    NullMeasurableSet {x | |mlmcEstimator Pl ω L N x - c| ≤ z * √(mlmcVarEst Pl ω L N x)} μ := by
  have h1 : AEMeasurable (fun x => mlmcEstimator Pl ω L N x - c) μ := by
    simpa using aemeasurable_mlmcEstimator_sub_div hω hPl N c 1
  have h2 : AEMeasurable (fun x => z * √(mlmcVarEst Pl ω L N x)) μ :=
    ((integrable_mlmcVarEst hω (memLp_levelDiff_of_le hPl) N).aemeasurable.sqrt).const_mul z
  exact nullMeasurableSet_le h1.abs h2

/-- **False acceptance in the tolerance test of Collier et al., at a fixed index** (Giles 2015,
§2.1, p. 8: "Instead of bounding the Mean Square Error, they prefer to use the Central Limit
Theorem to construct a confidence interval which bounds `E[P]` with a user-prescribed
confidence.").  Collier et al. split a tolerance `TOL_k` into a bias part `(1 − θ) TOL_k` and a
statistical part `θ TOL_k`, and accept when the estimated statistical error is small,
`z σ̂_k ≤ θ TOL_k`: a random test.  Under the hypotheses of
`tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd`, if `|E[P_{L_k}] − E[P]| ≤ (1 − θ) TOL_k` for
large `k`, then the probability that the test accepts although the error exceeds the tolerance is
asymptotically at most `2(1 − Φ(z))`: for every real `z` and every `η > 0`, eventually
`P(z σ̂_k ≤ θ TOL_k and |Y_k − E[P]| > TOL_k) < 2(1 − Φ(z)) + η`.  No condition on the size of
`σ_k` against `TOL_k` is needed, and `E[P] = ∫ P dν` may be replaced by any real number.  Here
`L_k` and `N_{k,ℓ}` are deterministic and the test is evaluated at a fixed index `k`; the
estimator at a random stopping index, or with sample sizes chosen from the estimated variances
(as in the adaptive algorithm of Collier et al. or the driver of §3.4), is not formalised.  The
hypotheses are this formalisation's; the paper only cites Collier et al.  Proof: for `z ≤ 0`,
`2(1 − Φ(z)) ≥ 1` (`two_mul_cdf_gaussianReal_sub_one_nonpos`) and the bound is trivial; for
`z ≥ 0` the event is contained in `{|Y_k − E[P_{L_k}]| > z σ̂_k}`, whose probability tends to
`1 − (2Φ(z) − 1)`. -/
theorem eventually_measureReal_test_and_tol_lt_abs_lt
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {L : ℕ → ℕ}
    (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν)
    (h4 : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k, ∫ y, (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4 ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ 2)
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    {P : Ω₀ → ℝ} {θ : ℝ} {TOL : ℕ → ℝ}
    (hbias : ∀ᶠ k in atTop, |∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν| ≤ (1 - θ) * TOL k)
    (z : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, μ.real {x | z * √(mlmcVarEst Pl ω (L k) (N k) x) ≤ θ * TOL k ∧
      TOL k < |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν|} <
      2 * (1 - cdf (gaussianReal 0 1) z) + η := by
  rcases lt_or_ge z 0 with hneg | hz
  · -- `z < 0`: `2(1 − Φ(z)) ≥ 1 ≥ P(·)`
    have h0 := two_mul_cdf_gaussianReal_sub_one_nonpos hneg.le
    exact Eventually.of_forall fun k => by
      have h1 := measureReal_le_one (μ := μ) (s := {x | z * √(mlmcVarEst Pl ω (L k) (N k) x) ≤
        θ * TOL k ∧ TOL k < |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν|})
      linarith
  have h := tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd hω hind hPl h4 hK hNtop hσ hz
  filter_upwards [h.eventually (lt_mem_nhds (sub_lt_self _ hη)), hbias] with k hk hb
  have hc := probReal_compl_eq_one_sub₀ (μ := μ)
    (nullMeasurableSet_abs_mlmcEstimator_sub_le hω (hPl k) (N k) (∫ y, Pl (L k) y ∂ν) z)
  have hsub : {x | z * √(mlmcVarEst Pl ω (L k) (N k) x) ≤ θ * TOL k ∧
      TOL k < |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν|} ⊆
      {x | |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν| ≤
        z * √(mlmcVarEst Pl ω (L k) (N k) x)}ᶜ := by
    rintro x ⟨h1, h2⟩
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    have htri : |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν| ≤
        |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν| +
          |∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν| := by
      rw [← sub_add_sub_cancel (mlmcEstimator Pl ω (L k) (N k) x) (∫ y, Pl (L k) y ∂ν)
        (∫ y, P y ∂ν)]
      exact abs_add_le _ _
    linarith
  have hm := measureReal_mono (μ := μ) hsub
  linarith

/-- **The tolerance split of Collier et al. with estimated variances, at a fixed index** (Giles
2015, §2.1, p. 8:
"Instead of bounding the Mean Square Error, they prefer to use the Central Limit Theorem to
construct a confidence interval which bounds `E[P]` with a user-prescribed confidence.").  Under
the hypotheses of `tendsto_measureReal_abs_mlmcEstimator_sub_le_estSd`, let
`|E[P_{L_k}] − E[P]| ≤ (1 − θ) TOL_k` and `z σ_k ≤ θ' TOL_k` for large `k`, with
`0 ≤ θ' < θ`.  Then the random test `z σ̂_k ≤ θ TOL_k` of Collier et al. passes and the error is
within the tolerance with asymptotic probability at least `2Φ(z) − 1`: for every `η > 0`,
eventually `P(z σ̂_k ≤ θ TOL_k and |Y_k − E[P]| ≤ TOL_k) > 2Φ(z) − 1 − η` (for every real `z`;
for `z ≤ 0` this is trivial).  The margin `θ' < θ` is what makes the test pass with probability
tending to one: if `z σ_k = θ TOL_k`, the test passes only when `σ̂_k ≤ σ_k`, an event whose
probability need not tend to one; `θ' ≥ 0` cannot be dropped (`θ' = −1`, `θ = 2`, `TOL_k = −1`
satisfy the other hypotheses, and the test never passes).  `E[P] = ∫ P dν` may be replaced by any
real number.  Here `L_k` and `N_{k,ℓ}` are deterministic and the test is evaluated at a fixed
index `k`; the estimator at a random stopping index, or with sample sizes chosen from the
estimated variances (as in the adaptive algorithm of Collier et al. or the driver of §3.4), is not
formalised.  The hypotheses are this formalisation's; the paper only cites Collier et al.  Proof:
for `z > 0`, with `1 + δ = θ/θ'`,
`{|Y_k − E[P_{L_k}]| ≤ z σ_k} ⊆ {test passes, |Y_k − E[P]| ≤ TOL_k} ∪ {|σ̂_k − σ_k| > δ σ_k}`,
and the interval with the exact `σ_k`
(`tendsto_measureReal_abs_mlmcEstimator_sub_le_of_moment_le`) and the consistency of `σ̂_k`
(`tendsto_measureReal_sqrt_mlmcVarEst_rel`) apply; for `z ≤ 0` the bound `2Φ(z) − 1 − η < 0` is
trivial (`two_mul_cdf_gaussianReal_sub_one_nonpos`). -/
theorem eventually_lt_measureReal_test_and_abs_sub_le_tol
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {L : ℕ → ℕ}
    (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν)
    (h4 : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k, ∫ y, (levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν) ^ 4 ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ 2)
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    {P : Ω₀ → ℝ} {θ θ' z : ℝ} {TOL : ℕ → ℝ} (hθ' : 0 ≤ θ') (hθθ' : θ' < θ)
    (hbias : ∀ᶠ k in atTop, |∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν| ≤ (1 - θ) * TOL k)
    (hstat : ∀ᶠ k in atTop,
      z * √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ≤ θ' * TOL k)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, 2 * cdf (gaussianReal 0 1) z - 1 - η <
      μ.real {x | z * √(mlmcVarEst Pl ω (L k) (N k) x) ≤ θ * TOL k ∧
        |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν| ≤ TOL k} := by
  rcases le_or_gt z 0 with hz0 | hzpos
  · -- `z ≤ 0`: `2Φ(z) − 1 ≤ 0`
    exact Eventually.of_forall fun k =>
      (sub_neg.2 ((two_mul_cdf_gaussianReal_sub_one_nonpos hz0).trans_lt hη)).trans_le
        measureReal_nonneg
  -- `θ' > 0`, since `z σ_k > 0` for large `k`
  obtain ⟨k₁, hk₁σ, hk₁s⟩ := (hσ.and hstat).exists
  have hθ'pos : 0 < θ' := by
    rcases hθ'.eq_or_lt with h | h
    · rw [← h, zero_mul] at hk₁s
      have := mul_pos hzpos (Real.sqrt_pos.2 hk₁σ)
      linarith
    · exact h
  set δ := (θ - θ') / θ' with hδ
  have hδpos : 0 < δ := div_pos (by linarith) hθ'pos
  have hδθ : (1 + δ) * θ' = θ := by
    rw [hδ]
    field_simp
    ring
  have hD : ∀ k, ∀ ℓ ≤ L k, MemLp (levelDiff Pl ℓ) 2 ν := fun k => memLp_levelDiff_of_le (hPl k)
  have hM : ∀ k, ∀ ℓ ≤ L k, Integrable
      (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ ((2 : ℝ) + 2)) ν := by
    simpa only [abs_rpow_two_add_two] using h4
  have hK' : ∀ k, ∀ ℓ ≤ L k,
      ∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ ((2 : ℝ) + 2) ∂ν ≤
        K * variance (levelDiff Pl ℓ) ν ^ ((1 : ℝ) + 2 / 2) := by
    simpa only [abs_rpow_two_add_two, rpow_one_add_two_div_two] using hK
  have h1 := tendsto_measureReal_abs_mlmcEstimator_sub_le_of_moment_le hω hind hPl two_pos hM hK'
    hNtop hσ hzpos.le
  have h2 := tendsto_measureReal_sqrt_mlmcVarEst_rel hω hind hD h4 hK hNtop hδpos
  filter_upwards [h1.eventually (lt_mem_nhds (sub_lt_self _ (half_pos hη))),
    h2.eventually_lt_const (half_pos hη), hbias, hstat, hσ] with k hk1 hk2 hb hs hσk
  set σk := √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) with hσkdef
  have hσpos : 0 < σk := Real.sqrt_pos.2 hσk
  have hTOL : 0 < TOL k := by
    have := mul_pos hzpos hσpos
    by_contra hneg
    have : θ' * TOL k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ'pos.le (not_lt.1 hneg)
    linarith
  have hsub : {x | |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν| ≤ z * σk} ⊆
      {x | z * √(mlmcVarEst Pl ω (L k) (N k) x) ≤ θ * TOL k ∧
        |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν| ≤ TOL k} ∪
      {x | δ * σk < |√(mlmcVarEst Pl ω (L k) (N k) x) - σk|} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    by_cases hbad : δ * σk < |√(mlmcVarEst Pl ω (L k) (N k) x) - σk|
    · exact Or.inr hbad
    left
    have hup : √(mlmcVarEst Pl ω (L k) (N k) x) ≤ (1 + δ) * σk := by
      have := le_abs_self (√(mlmcVarEst Pl ω (L k) (N k) x) - σk)
      linarith [not_lt.1 hbad]
    constructor
    · calc z * √(mlmcVarEst Pl ω (L k) (N k) x) ≤ z * ((1 + δ) * σk) :=
            mul_le_mul_of_nonneg_left hup hzpos.le
        _ = (1 + δ) * (z * σk) := by ring
        _ ≤ (1 + δ) * (θ' * TOL k) := mul_le_mul_of_nonneg_left hs (by linarith)
        _ = θ * TOL k := by rw [← mul_assoc, hδθ]
    · have htri : |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν| ≤
          |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν| +
            |∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν| := by
        rw [← sub_add_sub_cancel (mlmcEstimator Pl ω (L k) (N k) x) (∫ y, Pl (L k) y ∂ν)
          (∫ y, P y ∂ν)]
        exact abs_add_le _ _
      have : θ' * TOL k ≤ θ * TOL k := mul_le_mul_of_nonneg_right hθθ'.le hTOL.le
      linarith
  have hu := measureReal_union_le (μ := μ)
    {x | z * √(mlmcVarEst Pl ω (L k) (N k) x) ≤ θ * TOL k ∧
      |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν| ≤ TOL k}
    {x | δ * σk < |√(mlmcVarEst Pl ω (L k) (N k) x) - σk|}
  have hm := measureReal_mono (μ := μ) hsub
  linarith

end Estimator

end MLMC
