import MlmcLean.Corrections
import MlmcLean.KarhunenLoeve
import MlmcLean.MLMCConfidenceEstimated
import MlmcLean.PoissonGrids
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Truncated Lévy processes: simulating the large jumps on each level (Giles 2015, §6.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §6.2 "More
general processes", p. 47 (`docs/giles2015.txt`, l. 2037–2051; coverage rows G6-06, l. 2038–2043,
and G6-07, l. 2044–2051).  "With infinite activity Lévy processes it is impossible to simulate each
jump.  One approach is to simulate the large jumps and either neglect the small jumps or
approximate their effect by adding a Brownian diffusion term …  the cutoff `δ_ℓ` for the jumps
which are simulated varies with level, and `δ_ℓ → 0` as `ℓ → ∞` to ensure that the bias converges
to zero.  In the multilevel treatment, when simulating `P_ℓ − P_{ℓ−1}` the jumps fall into three
categories.  The ones which are larger than `δ_{ℓ−1}` get simulated in both the fine and coarse
paths.  The ones which are smaller than `δ_ℓ` are either neglected for both paths, or approximated
by the same Brownian increment.  The difficulty is in the intermediate range `[δ_ℓ, δ_{ℓ−1}]` in
which the jumps are simulated for the fine path, but neglected or approximated for the coarse
path.  This is what leads to the difference in path simulations, and contributes to a non-zero
value for `P_ℓ − P_{ℓ−1}`."

**Setting.**  The terminal value `X_T` of a pure-jump Lévy process (no drift, no Brownian part)
with Lévy measure `ν` on `ℝ`, `∫ min(1, z²) dν < ∞` (possibly `ν(ℝ) = ∞`), and the truncation
`1_{|z|<1}`.  Its jumps of size `|z| ≥ δ > 0` over `[0, T]` form a compound Poisson variable: a
count `N ∼ P(r)` and i.i.d. sizes `Z_i ∼ μ` with `r • μ = T • ν|_{|z| ≥ δ}` (intensity
`r = Tν(|z| ≥ δ)`, jump law `ν(· | |z| ≥ δ)`); `cpInputLaw r μ` is the law of `(N, Z)` and
`cpSum f (N, Z) = ∑_{i<N} f(Z_i)`.  The level-`δ` approximation is
`levyFine ν T δ = ∑_{i<N} 1_{|Z_i| ≥ δ} Z_i − T ∫_{δ ≤ |z| < 1} z dν` (the small jumps neglected,
the simulated ones compensated).

**Compound Poisson tools.**  `charFun_cpSum`: the characteristic function
`exp (r ∫ (e^{itf} − 1) dμ)`.  `cp_thinning`: keeping the jumps in `A` gives the compound Poisson
variable with `r' • μ' = r • μ|_A`; `cp_thinning_indep`: the kept and the discarded jumps are
independent.  `cpSum_moments`: `E[∑_{i<N} g(Z_i)] = r ∫ g dμ` and
`E[(∑_{i<N} g(Z_i) − r ∫ g dμ)²] = r ∫ g² dμ`, with `MemLp 2`.

**G6-07: the coupled levels.**  The jumps `|z| ≥ δ_ℓ` are simulated once; the fine value uses all
of them (`levyFine ν T δ_ℓ`), the coarse value only those with `|z| ≥ δ_{ℓ−1}`
(`levyFine ν T δ_{ℓ−1}` on the same input).
* `levy_coarse_map_eq`, `levy_truncation_2_4`: the coarse value has exactly the law of the level
  `ℓ − 1` approximation simulated on its own, hence (2.4).
* `levy_correction_moments`: `X^{δ_ℓ} − X^{δ_{ℓ−1}}` is exactly the compensated sum of the jumps in
  `[δ_ℓ, δ_{ℓ−1})`, has mean `0` and
  `E[(X^{δ_ℓ} − X^{δ_{ℓ−1}})²] = T ∫_{δ_ℓ ≤ |z| < δ_{ℓ−1}} z² dν`.
* `levy_correction_variance_le`: for a `K`-Lipschitz payoff,
  `V_ℓ ≤ K² T ∫_{δ_ℓ ≤ |z| < δ_{ℓ−1}} z² dν`.

**G6-06: all levels on one space, convergence and bias.**  The bands `levyBand δ 0 = {|z| ≥ δ_0}`,
`levyBand δ (k + 1) = [δ_{k+1}, δ_k)` get independent compound Poisson inputs
(`bandInputLaw Λ M`, `Λ_k • M_k = T • ν|_{band k}`; such laws exist, `exists_levy_bandLaws`), and
`bandApprox ν T δ ℓ` adds the jumps of the bands `0, …, ℓ` and subtracts the compensator: the
level-`ℓ` correction uses the bands `0, …, ℓ − 1` (jumps `≥ δ_{ℓ−1}`) on both paths and band `ℓ`
on the fine path only, the "three categories".
* `bandApprox_map_eq` (superposition): `bandApprox ν T δ ℓ` has the law of `levyFine ν T δ_ℓ`.
* `bandApprox_sq_sub`: `E[(X^{δ_{ℓ'}} − X^{δ_ℓ})²] = T ∫_{δ_{ℓ'} ≤ |z| < δ_ℓ} z² dν`, `ℓ ≤ ℓ'`.
* `levy_truncation_limit`: for `0 < δ_ℓ ≤ δ_0 ≤ 1`, `δ_ℓ ↓ 0`, an `L²` limit `X` exists with
  `E[(X − X^{δ_ℓ})²] = T ∫_{|z| < δ_ℓ} z² dν → 0`, and the bias of a `K`-Lipschitz payoff is
  `|E[Φ(X^{δ_ℓ}) − Φ(X)]| ≤ K (T ∫_{|z| < δ_ℓ} z² dν)^{1/2} → 0` (the argument of
  `exists_klField_limit`, `exists_L2_limit_of_tail`).
* `integral_band_count`: the expected number of simulated jumps is `T ν(|z| ≥ δ_ℓ)`.
* `levy_expected_cost`: the random cost of the estimator (one plus the number of simulated jumps
  per sample, `∑_ℓ ∑_{n<N_ℓ} (1 + ∑_{k≤ℓ} N_k^{(ℓ,n)})`) is integrable with expectation
  `∑_ℓ N_ℓ (1 + T ν(|z| ≥ δ_ℓ))`.

**Theorem 1.**  `levy_truncation_theorem1`: with `δ_ℓ = 2^{−ℓ}`, `∫_{|z| ≥ 1} z² dν < ∞`, a
`K`-Lipschitz payoff and the rates `T ∫_{|z| < δ_ℓ} z² dν ≤ a δ_ℓ^{2−Y}`,
`T ν(|z| ≥ δ_ℓ) ≤ b δ_ℓ^{−Y}` (`0 < Y < 2`), Theorem 1 holds for the estimator of `E[Φ(X)]` with
`α = (2 − Y)/2`, `β = 2 − Y`, `γ = Y` and the cost "one plus the number of simulated jumps", whose
expectation `∑_ℓ N_ℓ (1 + T ν(|z| ≥ δ_ℓ))` is bounded (`giles_theorem1_fineCoarse`,
`levy_expected_cost`).  `levy_stableLike_theorem1`: the one-sided example
`ν(dz) = c z^{−1−Y} dz` on `(0, 1]` (`stableLikeLevy`), for which
`T ∫_{|z| < 2^{−ℓ}} z² dν = T c 2^{−(2−Y)ℓ}/(2 − Y)` and `T ν(|z| ≥ 2^{−ℓ}) = T c (2^{Yℓ} − 1)/Y`
(`stableLike_small_sq`, `stableLike_count`); the complexity `complexityBound α β γ ε` is `ε⁻²` for
`Y < 1`, `ε⁻² (log ε)²` for `Y = 1` and `ε^{−2−(γ−β)/α} = ε^{−2−4(Y−1)/(2−Y)} = ε^{−2Y/(2−Y)}` for
`1 < Y < 2` (e.g. `ε^{−6}` at `Y = 3/2`).

**Deviations.**  Only the terminal value `X_T` is modelled (payoffs `Φ(X_T)`; jump times and paths
are not simulated); no drift or Brownian component.  The simulated jumps are summed as
`∑_{i<N} 1_{|Z_i| ≥ δ} Z_i`; under the jump law `ν(· | |z| ≥ δ)` the indicator is `1` almost
surely when `r > 0`.  The jump laws enter through `r • μ = T • ν|_B` (any such `r`, `μ`).  The
intermediate range is the half-open `[δ_ℓ, δ_{ℓ−1})` (a jump of size exactly `δ_{ℓ−1}` is simulated
on both paths), not the paper's closed interval.  Two realisations of the coupling are used: per
level (simulate `|z| ≥ δ_ℓ` once, the coarse path keeps `|z| ≥ δ_{ℓ−1}`) for (2.4) and the
correction variance; and all levels on one product space of independent bands for the limit and
Theorem 1, where the coarse value of level `ℓ` is the level-`(ℓ − 1)` value on the same input
(their laws agree by `bandApprox_map_eq`).  The limit `X` is an `L²` limit (a representative), not
identified as the terminal value of a càdlàg Lévy process.  Theorem 1 fixes the cutoffs
`δ_ℓ = 2^{−ℓ}` (the paper only requires `δ_ℓ → 0`).  The cost of a sample is random (one plus
the number of simulated jumps); Theorem 1 bounds the expected total cost, which equals
`∑_ℓ N_ℓ (1 + T ν(|z| ≥ δ_ℓ))` (`levy_expected_cost`), not the cost of every realisation.  The bias
rate `α = β/2` is the mean-square one for Lipschitz payoffs; the large jumps are assumed square
integrable so that the payoffs are in `L²`; the rates are hypotheses, verified for the one-sided
example.  In the example `ν` lives on `(0, 1]`, so band `0 = {|z| ≥ 1}` has `ν`-mass `0`
(`Λ_0 = 0`): level `0` is almost surely the deterministic `Φ(0)` and all jumps are simulated in the
correction levels.

**Not proved here.**  The alternative of approximating the effect of the small jumps by a
Brownian diffusion term (l. 2039–2041, citing Dereich 2011, Dereich and Heidenreich 2011 and
Marxen 2010; l. 2047–2048, "approximated by the same Brownian increment") is in
`MlmcLean.LevyExtras`, with the same rates (Dereich's improved bias is not proved).  The
Lévy–Khintchine law of the limit `X`, `E[e^{itX}] = exp (T ∫ (e^{itz} − 1 − itz 1_{|z|<1}) dν)`,
is in `MlmcLean.LevyKhintchineLimit` (`levy_truncation_limit_charFun`, `levy_limit_charFun`; the
law of the terminal value only, no process).  Not proved: path-dependent payoffs for truncated
levels and the rates of Table 6.3 (p. 48; the Asian row with exactly simulated increments is in
`MlmcLean.JumpProcesses` and `MlmcLean.LevyExtras`), two-sided or non-Lipschitz examples, and
bounds on the realised (rather than expected) cost.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal ENNReal

namespace MLMC

/-! ### Compound Poisson variables -/

/-- The law of the input of a compound Poisson variable (Giles 2015, §6.2, p. 47, l. 2038–2041:
"simulate the large jumps"): a Poisson number `N ∼ P(r)` of jumps and the independent jump sizes
`Z_0, Z_1, …`, i.i.d. with the probability law `μ`, on `ℕ × (ℕ → ℝ)`. -/
noncomputable def cpInputLaw (r : ℝ≥0) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measure (ℕ × (ℕ → ℝ)) :=
  (poissonMeasure r).prod (Measure.infinitePi fun _ : ℕ => μ)

/-- The sum `∑_{i<N} f(Z_i)` of a function of the jumps of a compound Poisson input `(N, Z)`
(Giles 2015, §6.2, p. 47, l. 2038–2051). -/
def cpSum (f : ℝ → ℝ) (ω : ℕ × (ℕ → ℝ)) : ℝ := ∑ i ∈ range ω.1, f (ω.2 i)

/-- The input law of a compound Poisson variable is a probability measure (Giles 2015, §6.2). -/
lemma isProbabilityMeasure_cpInputLaw (r : ℝ≥0) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (cpInputLaw r μ) := by
  unfold cpInputLaw
  infer_instance

/-- `∑_{i<N} f(Z_i)` is measurable (Giles 2015, §6.2). -/
lemma measurable_cpSum {f : ℝ → ℝ} (hf : Measurable f) : Measurable (cpSum f) :=
  measurable_from_prod_countable_right fun n => by
    change Measurable fun y : ℕ → ℝ => ∑ i ∈ range n, f (y i)
    exact Finset.measurable_fun_sum _ fun i _ => hf.comp (measurable_pi_apply i)

/-- Products of functions of finitely many coordinates of a product measure (Giles 2015, §6.2):
`∫ ∏_{k∈s} F_k(ω_k) d(⊗_k P_k) = ∏_{k∈s} ∫ F_k dP_k`. -/
lemma integral_prod_infinitePi {X : ℕ → Type*} [∀ k, MeasurableSpace (X k)]
    (P : ∀ k, Measure (X k)) [∀ k, IsProbabilityMeasure (P k)] (s : Finset ℕ)
    {F : ∀ k, X k → ℂ} (hF : ∀ k, Measurable (F k)) :
    ∫ ω, ∏ k ∈ s, F k (ω k) ∂(Measure.infinitePi P) = ∏ k ∈ s, ∫ x, F k x ∂(P k) := by
  have h := integral_restrict_infinitePi (μ := P) (s := s)
    (f := fun y : (∀ k : s, X k) => ∏ k : s, F k (y k)) ?_
  · rw [integral_fintype_prod_eq_prod (fun k : s => F k)] at h
    rw [← Finset.prod_coe_sort s fun k => ∫ x, F k x ∂(P k), ← h]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact (Finset.prod_coe_sort s fun k => F k (ω k)).symm
  · exact (Finset.measurable_fun_prod (Finset.univ : Finset s) fun k _ =>
      (hF k).comp (measurable_pi_apply k)).aestronglyMeasurable

/-- The characteristic function of a sum of `n` i.i.d. jumps (Giles 2015, §6.2):
`E[e^{it ∑_{i<n} f(Z_i)}] = (E[e^{it f(Z_0)}])^n`. -/
lemma integral_cexp_sum_infinitePi (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) (t : ℝ) (n : ℕ) :
    ∫ z : ℕ → ℝ, Complex.exp (t * ((∑ i ∈ range n, f (z i) : ℝ) : ℂ) * Complex.I)
        ∂(Measure.infinitePi fun _ : ℕ => μ) =
      (∫ x, Complex.exp (t * f x * Complex.I) ∂μ) ^ n := by
  have h := integral_prod_infinitePi (fun _ : ℕ => μ) (range n)
    (F := fun _ x => Complex.exp (t * f x * Complex.I)) (fun _ => by fun_prop)
  rw [Finset.prod_const, card_range] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  dsimp only
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The exponential series of a Poisson variate (Giles 2015, §6.2): `E[w^N] = e^{r(w − 1)}` for
`N ∼ P(r)` and every complex `w`. -/
lemma integral_pow_poissonMeasure (r : ℝ≥0) (w : ℂ) :
    ∫ n, w ^ n ∂(poissonMeasure r) = Complex.exp (r * (w - 1)) := by
  rw [integral_poissonMeasure r]
  calc ∑' a, (Real.exp (-r) * r ^ a / (a.factorial) : ℝ) • w ^ a
      = ∑' a, (Real.exp (-r) : ℂ) * (((r : ℂ) * w) ^ a / a.factorial) := by
        congr with a
        rw [Complex.real_smul]
        push_cast
        rw [mul_pow]
        ring
    _ = (Real.exp (-r) : ℂ) * ∑' a, (((r : ℂ) * w) ^ a / a.factorial) := tsum_mul_left
    _ = (Real.exp (-r) : ℂ) * Complex.exp (r * w) := by
        rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * w)).tsum_eq, Complex.exp_eq_exp_ℂ]
    _ = Complex.exp (r * (w - 1)) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        push_cast
        ring_nf

/-- **The characteristic function of a compound Poisson variable** (Giles 2015, §6.2, p. 47,
l. 2038–2039: "With infinite activity Lévy processes it is impossible to simulate each jump.  One
approach is to simulate the large jumps"; the large jumps form a compound Poisson variable): for
`N ∼ P(r)` and i.i.d. jumps `Z_i ∼ μ`, the law of `∑_{i<N} f(Z_i)` has the characteristic
function `t ↦ exp (r ∫ (e^{itf(z)} − 1) dμ(z))`. -/
theorem charFun_cpSum (r : ℝ≥0) (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) (t : ℝ) :
    charFun ((cpInputLaw r μ).map (cpSum f)) t =
      Complex.exp (r * ∫ x, (Complex.exp (t * f x * Complex.I) - 1) ∂μ) := by
  have := isProbabilityMeasure_cpInputLaw r μ
  have hS := measurable_cpSum hf
  have hm : Measurable fun ω => Complex.exp (t * cpSum f ω * Complex.I) := by fun_prop
  have hint : Integrable (fun ω => Complex.exp (t * cpSum f ω * Complex.I))
      (cpInputLaw r μ) := by
    refine Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  have hφ : Integrable (fun x => Complex.exp (t * f x * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  rw [charFun_apply_real, integral_map hS.aemeasurable (by fun_prop)]
  rw [cpInputLaw] at hint ⊢
  rw [integral_prod _ hint]
  unfold cpSum
  simp_rw [integral_cexp_sum_infinitePi μ hf t]
  rw [integral_pow_poissonMeasure, integral_sub hφ (integrable_const 1), integral_const,
    probReal_univ, one_smul]

/-- Two compound Poisson variables have the same law when their exponents agree (Giles 2015, §6.2):
if `r ∫ (e^{itf} − 1) dμ = r' ∫ (e^{itf'} − 1) dμ'` for all `t`, then `∑_{i<N} f(Z_i)` and
`∑_{i<N'} f'(Z'_i)` have the same law (uniqueness of characteristic functions). -/
lemma cpSum_map_eq_of_exponent {r r' : ℝ≥0} {μ μ' : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {f f' : ℝ → ℝ} (hf : Measurable f) (hf' : Measurable f')
    (h : ∀ t : ℝ, (r : ℂ) * ∫ x, (Complex.exp (t * f x * Complex.I) - 1) ∂μ =
      (r' : ℂ) * ∫ x, (Complex.exp (t * f' x * Complex.I) - 1) ∂μ') :
    (cpInputLaw r μ).map (cpSum f) = (cpInputLaw r' μ').map (cpSum f') := by
  have := isProbabilityMeasure_cpInputLaw r μ
  have := isProbabilityMeasure_cpInputLaw r' μ'
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_cpSum r μ hf, charFun_cpSum r' μ' hf', h t]

/-- The exponent of a compound Poisson variable as an integral against its Lévy measure
`r • μ` (Giles 2015, §6.2): `r ∫ φ dμ = ∫ φ d(r • μ)`. -/
lemma nnreal_mul_integral_eq (r : ℝ≥0) (μ : Measure ℝ) (φ : ℝ → ℂ) :
    (r : ℂ) * ∫ x, φ x ∂μ = ∫ x, φ x ∂(r • μ) := by
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/-- Keeping the jumps in `A`: `e^{it 1_A(x) x} − 1 = 1_A(x) (e^{itx} − 1)` (Giles 2015, §6.2). -/
lemma cexp_indicator_sub_one (A : Set ℝ) (t x : ℝ) :
    Complex.exp (t * (A.indicator id x : ℝ) * Complex.I) - 1 =
      A.indicator (fun y : ℝ => Complex.exp (t * y * Complex.I) - 1) x := by
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, id]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- **Thinning a compound Poisson variable by its marks** (Giles 2015, §6.2, p. 47, l. 2045–2048:
"The ones which are larger than `δ_{ℓ−1}` get simulated in both the fine and coarse paths", the
coarse path keeping only those jumps of the fine simulation).  Let `N ∼ P(r)` and `Z_i ∼ μ` i.i.d.
and keep the jumps in a measurable set `A`.  If `r' • μ' = r • μ|_A` (intensity `r' = rμ(A)` and
jump law `μ' = μ(· | A)`), the sum `∑_{i<N} 1_A(Z_i) Z_i` of the kept jumps has the law of the
compound Poisson sum `∑_{i<N'} Z'_i` with `N' ∼ P(r')` and `Z'_i ∼ μ'` i.i.d. -/
theorem cp_thinning {r r' : ℝ≥0} {μ μ' : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {A : Set ℝ} (hA : MeasurableSet A)
    (h : r' • μ' = r • μ.restrict A) :
    (cpInputLaw r μ).map (cpSum (A.indicator id)) = (cpInputLaw r' μ').map (cpSum id) := by
  refine cpSum_map_eq_of_exponent (measurable_id.indicator hA) measurable_id fun t => ?_
  rw [nnreal_mul_integral_eq, nnreal_mul_integral_eq, h]
  simp_rw [cexp_indicator_sub_one A t]
  rw [integral_indicator hA, Measure.restrict_smul]
  rfl

/-- `|e^{iθ} − 1| ≤ 2`: the exponent integrands are integrable (Giles 2015, §6.2). -/
lemma integrable_cexp_sub_one (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Measurable f) (t : ℝ) :
    Integrable (fun x => Complex.exp (t * f x * Complex.I) - 1) μ := by
  refine Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun x => ?_)
  calc ‖Complex.exp (t * f x * Complex.I) - 1‖ ≤
        ‖Complex.exp (t * f x * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
        rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, norm_one]
        norm_num

/-- **The kept and the discarded jumps are independent** (Giles 2015, §6.2, p. 47, l. 2044–2050:
the jumps "fall into three categories"; the marking theorem for compound Poisson sums): for a
measurable `A`, `∑_{i<N} 1_A(Z_i) Z_i` and `∑_{i<N} 1_{Aᶜ}(Z_i) Z_i` are independent (the joint
characteristic function factorises). -/
theorem cp_thinning_indep (r : ℝ≥0) (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ}
    (hA : MeasurableSet A) :
    IndepFun (cpSum (A.indicator id)) (cpSum (Aᶜ.indicator id)) (cpInputLaw r μ) := by
  have := isProbabilityMeasure_cpInputLaw r μ
  have hf : Measurable (A.indicator (id : ℝ → ℝ)) := measurable_id.indicator hA
  have hg : Measurable (Aᶜ.indicator (id : ℝ → ℝ)) := measurable_id.indicator hA.compl
  have hSf := measurable_cpSum hf
  have hSg := measurable_cpSum hg
  rw [indepFun_iff_charFun_prod hSf.aemeasurable hSg.aemeasurable]
  intro t
  set s := (WithLp.ofLp t).1 with hs
  set u := (WithLp.ofLp t).2 with hu
  set F : ℝ → ℝ := fun z => s * A.indicator id z + u * Aᶜ.indicator id z with hFdef
  have hF : Measurable F := (measurable_const.mul hf).add (measurable_const.mul hg)
  have hjoint : charFun ((cpInputLaw r μ).map
      (fun ω => WithLp.toLp 2 (cpSum (A.indicator id) ω, cpSum (Aᶜ.indicator id) ω))) t =
      charFun ((cpInputLaw r μ).map (cpSum F)) 1 := by
    rw [charFun_apply, charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
      integral_map (measurable_cpSum hF).aemeasurable (by fun_prop)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    dsimp only
    rw [WithLp.prod_inner_apply, WithLp.ofLp_toLp, Real.inner_apply, Real.inner_apply]
    congr 1
    unfold cpSum
    simp only [hFdef, Finset.sum_add_distrib, ← Finset.mul_sum]
    push_cast
    ring
  rw [hjoint, charFun_cpSum r μ hF 1, charFun_cpSum r μ hf s, charFun_cpSum r μ hg u,
    ← Complex.exp_add, ← mul_add,
    ← integral_add (integrable_cexp_sub_one μ hf s) (integrable_cexp_sub_one μ hg u)]
  congr 3
  funext z
  by_cases hz : z ∈ A
  · have hz' : z ∉ Aᶜ := fun h => h hz
    simp only [hFdef, Set.indicator_of_mem hz, Set.indicator_of_notMem hz', id, mul_zero,
      add_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, Complex.ofReal_one,
      one_mul, Complex.ofReal_mul]
  · have hz' : z ∈ Aᶜ := hz
    simp only [hFdef, Set.indicator_of_mem hz', Set.indicator_of_notMem hz, id, mul_zero,
      zero_add, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, Complex.ofReal_one,
      one_mul, Complex.ofReal_mul]

/-- The moments of a sum of `n` i.i.d. jumps (Giles 2015, §6.2): `S_n = ∑_{i<n} g(Z_i)` is square
integrable, `E[S_n] = n m` and `E[(S_n − c)²] = n (s − m²) + (n m − c)²`, where `m = ∫ g dμ`,
`s = ∫ g² dμ`. -/
lemma cp_inner_moments (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 μ) (n : ℕ) (c : ℝ) :
    MemLp (fun z : ℕ → ℝ => ∑ i ∈ range n, g (z i)) 2 (Measure.infinitePi fun _ : ℕ => μ) ∧
      ∫ z, ∑ i ∈ range n, g (z i) ∂(Measure.infinitePi fun _ : ℕ => μ) = n * ∫ x, g x ∂μ ∧
      ∫ z, (∑ i ∈ range n, g (z i) - c) ^ 2 ∂(Measure.infinitePi fun _ : ℕ => μ) =
        n * (∫ x, g x ^ 2 ∂μ - (∫ x, g x ∂μ) ^ 2) + (n * ∫ x, g x ∂μ - c) ^ 2 := by
  set M := Measure.infinitePi fun _ : ℕ => μ with hM
  have hev : ∀ i, MeasurePreserving (fun z : ℕ → ℝ => z i) M μ := fun i =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i
  have hgi : ∀ i, MemLp (fun z : ℕ → ℝ => g (z i)) 2 M := fun i =>
    hg2.comp_measurePreserving (hev i)
  have hint : ∀ i, ∫ z, g (z i) ∂M = ∫ x, g x ∂μ := fun i => by
    have h := integral_map (μ := M) (hev i).measurable.aemeasurable (f := g)
      (by rw [(hev i).map_eq]; exact hg.aestronglyMeasurable)
    rw [(hev i).map_eq] at h
    exact h.symm
  have hS : MemLp (fun z : ℕ → ℝ => ∑ i ∈ range n, g (z i)) 2 M :=
    memLp_finsetSum (range n) fun i _ => hgi i
  have hmean : ∫ z, ∑ i ∈ range n, g (z i) ∂M = n * ∫ x, g x ∂μ := by
    rw [integral_finsetSum _ fun i _ => (hgi i).integrable one_le_two]
    simp_rw [hint]
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
  have e : (fun z : ℕ → ℝ => ∑ i ∈ range n, g (z i)) =
      ∑ i ∈ range n, (fun z : ℕ → ℝ => g (z i)) := by
    funext z
    rw [Finset.sum_apply]
  have hvar : variance (fun z : ℕ → ℝ => ∑ i ∈ range n, g (z i)) M =
      n * (∫ x, g x ^ 2 ∂μ - (∫ x, g x ∂μ) ^ 2) := by
    rw [e, IndepFun.variance_sum (fun i _ => hgi i) fun i _ j _ hij =>
      (iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ => g) fun _ => hg).indepFun hij]
    simp_rw [(hev _).variance_fun_comp hg.aemeasurable, variance_eq_sub hg2]
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
    rfl
  refine ⟨hS, hmean, ?_⟩
  have hSc : MemLp (fun z : ℕ → ℝ => ∑ i ∈ range n, g (z i) - c) 2 M := hS.sub (memLp_const c)
  have h1 := variance_eq_sub hSc
  rw [variance_sub_const hS.aestronglyMeasurable c, hvar,
    integral_sub (hS.integrable one_le_two) (integrable_const c), hmean, integral_const,
    probReal_univ, one_smul] at h1
  simp only [Pi.pow_apply] at h1
  linarith

/-- `n` and `n²` are integrable under the Poisson law (Giles 2015, §6.2). -/
lemma integrable_poissonMeasure_id_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) ∧
      Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) := by
  have hs2 : HasSum (fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2)
      ((r : ℝ) + (r : ℝ) ^ 2) := by
    convert (hasSum_poissonWeight_mul_id r).add (hasSum_poissonWeight_mul_descFactorial r) using 1
    funext n
    ring
  exact ⟨integrable_poissonMeasure_iff.2 ((hasSum_poissonWeight_mul_id r).summable.congr
      fun n => by rw [Real.norm_natCast]),
    integrable_poissonMeasure_iff.2 (hs2.summable.congr fun n => by
      rw [norm_pow, Real.norm_natCast])⟩

/-- **The first two moments of a compound Poisson sum** (Giles 2015, §6.2, p. 47, l. 2048–2051:
the jumps of the intermediate range "contribute to a non-zero value for `P_ℓ − P_{ℓ−1}`"; this is
the size of that contribution): for `N ∼ P(r)`, `Z_i ∼ μ` i.i.d. and `g ∈ L²(μ)`,
`S = ∑_{i<N} g(Z_i)` is square integrable with `E[S] = r ∫ g dμ` and
`E[(S − r ∫ g dμ)²] = r ∫ g² dμ`. -/
theorem cpSum_moments (r : ℝ≥0) (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 μ) :
    MemLp (cpSum g) 2 (cpInputLaw r μ) ∧
      ∫ ω, cpSum g ω ∂(cpInputLaw r μ) = r * ∫ x, g x ∂μ ∧
      ∫ ω, (cpSum g ω - r * ∫ x, g x ∂μ) ^ 2 ∂(cpInputLaw r μ) = r * ∫ x, g x ^ 2 ∂μ := by
  have := isProbabilityMeasure_cpInputLaw r μ
  set m := ∫ x, g x ∂μ with hm
  set s := ∫ x, g x ^ 2 ∂μ with hs
  have hSm := measurable_cpSum hg
  obtain ⟨hi1, hi2⟩ := integrable_poissonMeasure_id_sq r
  have hpoly : ∀ c : ℝ, Integrable (fun n : ℕ => (n : ℝ) * (s - m ^ 2) + ((n : ℝ) * m - c) ^ 2)
      (poissonMeasure r) := fun c => by
    have e : (fun n : ℕ => (n : ℝ) * (s - m ^ 2) + ((n : ℝ) * m - c) ^ 2) =
        fun n : ℕ => (n : ℝ) ^ 2 * m ^ 2 + (n : ℝ) * (s - m ^ 2 - 2 * m * c) + c ^ 2 := by
      funext n
      ring
    rw [e]
    exact ((hi2.mul_const _).add (hi1.mul_const _)).add (integrable_const _)
  have hsq : ∀ c : ℝ, Integrable (fun ω => (cpSum g ω - c) ^ 2) (cpInputLaw r μ) := by
    intro c
    rw [cpInputLaw, integrable_prod_iff ((hSm.sub_const c).pow_const 2).aestronglyMeasurable]
    refine ⟨ae_of_all _ fun n => ?_, ?_⟩
    · exact ((cp_inner_moments μ hg hg2 n 0).1.sub (memLp_const c)).integrable_sq
    · refine (hpoly c).congr (ae_of_all _ fun n => ?_)
      simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact ((cp_inner_moments μ hg hg2 n c).2.2).symm
  have hL2 : MemLp (cpSum g) 2 (cpInputLaw r μ) :=
    (memLp_two_iff_integrable_sq hSm.aestronglyMeasurable).2 (by simpa using hsq 0)
  have hmean : ∫ ω, cpSum g ω ∂(cpInputLaw r μ) = r * m := by
    have hint := hL2.integrable one_le_two
    rw [cpInputLaw] at hint ⊢
    rw [integral_prod _ hint]
    unfold cpSum
    simp_rw [(cp_inner_moments μ hg hg2 _ 0).2.1]
    rw [integral_mul_const, integral_poissonMeasure_id]
  refine ⟨hL2, hmean, ?_⟩
  have hint := hsq (r * m)
  rw [cpInputLaw] at hint ⊢
  rw [integral_prod _ hint]
  unfold cpSum
  simp_rw [(cp_inner_moments μ hg hg2 _ (r * m)).2.2]
  have e : (fun n : ℕ => (n : ℝ) * (s - m ^ 2) + ((n : ℝ) * m - r * m) ^ 2) =
      fun n : ℕ => (n : ℝ) ^ 2 * m ^ 2 + (n : ℝ) * (s - m ^ 2 - 2 * m * (r * m)) +
        (r * m) ^ 2 := by
    funext n
    ring
  have hA : Integrable (fun n : ℕ => (n : ℝ) ^ 2 * m ^ 2 + (n : ℝ) * (s - m ^ 2 -
      2 * m * (r * m))) (poissonMeasure r) := (hi2.mul_const _).add (hi1.mul_const _)
  rw [e, integral_add hA (integrable_const _),
    integral_add (hi2.mul_const _) (hi1.mul_const _), integral_mul_const, integral_mul_const,
    integral_poissonMeasure_id, integral_sq_poissonMeasure, integral_const, probReal_univ,
    one_smul]
  ring

/-! ### The level-`δ` approximation of a Lévy process and the coupled levels -/

/-- The jumps of size at least `δ`, `{z : δ ≤ |z|}` (Giles 2015, §6.2, p. 47, l. 2039:
"simulate the large jumps"). -/
def levySet (δ : ℝ) : Set ℝ := {z | δ ≤ |z|}

/-- The compensator `T ∫_{δ ≤ |z| < 1} z dν` of the simulated small-to-medium jumps of a Lévy
process with Lévy measure `ν` over `[0, T]` (Giles 2015, §6.2, p. 47, l. 2039–2041; the usual
truncation `1_{|z|<1}` of the Lévy–Khintchine formula). -/
noncomputable def levyComp (ν : Measure ℝ) (T : ℝ≥0) (δ : ℝ) : ℝ :=
  T * ∫ z in {z : ℝ | δ ≤ |z| ∧ |z| < 1}, z ∂ν

/-- **The level-`δ` approximation of `X_T`** (Giles 2015, §6.2, p. 47, l. 2038–2043: "simulate the
large jumps and … neglect the small jumps"; "the cutoff `δ_ℓ` for the jumps which are simulated
varies with level"): from a compound Poisson input `(N, Z)`, the sum of the simulated jumps of size
`|Z_i| ≥ δ` minus the compensator, `∑_{i<N} 1_{|Z_i| ≥ δ} Z_i − T ∫_{δ ≤ |z| < 1} z dν`. -/
noncomputable def levyFine (ν : Measure ℝ) (T : ℝ≥0) (δ : ℝ) (ω : ℕ × (ℕ → ℝ)) : ℝ :=
  cpSum ((levySet δ).indicator id) ω - levyComp ν T δ

/-- `{z : δ ≤ |z|}` is measurable (Giles 2015, §6.2). -/
lemma measurableSet_levySet (δ : ℝ) : MeasurableSet (levySet δ) :=
  measurableSet_le measurable_const continuous_abs.measurable

/-- The level-`δ` approximation is measurable (Giles 2015, §6.2). -/
lemma measurable_levyFine (ν : Measure ℝ) (T : ℝ≥0) (δ : ℝ) : Measurable (levyFine ν T δ) :=
  (measurable_cpSum (measurable_id.indicator (measurableSet_levySet δ))).sub_const _

/-- Integrals against the jump law of the level-`δ` simulation (Giles 2015, §6.2): if
`r • μ = T • ν|_{|z| ≥ δ}` (intensity `r = Tν(|z| ≥ δ)` and jump law `ν(· | |z| ≥ δ)`), then
`r ∫ φ dμ = T ∫_{|z| ≥ δ} φ dν` for every `φ`. -/
lemma nnreal_mul_integral_of_smul_eq {r T : ℝ≥0} {μ ν : Measure ℝ} {S : Set ℝ}
    (h : r • μ = T • ν.restrict S) (φ : ℝ → ℝ) :
    (r : ℝ) * ∫ x, φ x ∂μ = T * ∫ x in S, φ x ∂ν := by
  calc (r : ℝ) * ∫ x, φ x ∂μ = ∫ x, φ x ∂(r • μ) := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    _ = ∫ x, φ x ∂(T • ν.restrict S) := by rw [h]
    _ = T * ∫ x in S, φ x ∂ν := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

/-- The exponent of the coarse sum (Giles 2015, §6.2): if `r • μ = T • ν|_{|z| ≥ δ}` and
`δ ≤ δ'`, keeping the jumps with `|z| ≥ δ'` gives the exponent
`∫ (e^{itz} − 1) d(T • ν|_{|z| ≥ δ'})` (the jumps of the level-`δ'` simulation). -/
lemma exponent_levySet {ν : Measure ℝ} {T r : ℝ≥0} {μ : Measure ℝ} {δ δ' : ℝ} (hδ : δ ≤ δ')
    (h : r • μ = T • ν.restrict (levySet δ)) (t : ℝ) :
    (r : ℂ) * ∫ x, (Complex.exp (t * ((levySet δ').indicator id x : ℝ) * Complex.I) - 1) ∂μ =
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂(T • ν.restrict (levySet δ')) := by
  have hA := measurableSet_levySet δ'
  have hsub : levySet δ' ⊆ levySet δ := fun z hz => le_trans hδ hz
  rw [nnreal_mul_integral_eq, h]
  simp_rw [cexp_indicator_sub_one (levySet δ') t]
  rw [integral_indicator hA, Measure.restrict_smul, Measure.restrict_restrict hA,
    Set.inter_eq_left.2 hsub]

/-- **The coarse value of the level-`ℓ` simulation has the law of the level-`(ℓ − 1)`
approximation** (Giles 2015, §6.2, p. 47, l. 2044–2051: "In the multilevel treatment, when
simulating `P_ℓ − P_{ℓ−1}` the jumps fall into three categories.  The ones which are larger than
`δ_{ℓ−1}` get simulated in both the fine and coarse paths. … The difficulty is in the intermediate
range `[δ_ℓ, δ_{ℓ−1}]` in which the jumps are simulated for the fine path, but neglected … for the
coarse path"; this gives (2.4), §2.1, p. 8).  The jumps of size `|z| ≥ δ` (`δ = δ_ℓ`) are
simulated once, `N ∼ P(r)`, `Z_i ∼ μ` with `r • μ = T • ν|_{|z| ≥ δ}`; the fine value is
`levyFine ν T δ` and the coarse value `levyFine ν T δ'` (`δ' = δ_{ℓ−1} ≥ δ`) keeps only the jumps
with `|Z_i| ≥ δ'`.  Then the coarse value has exactly the law of the level-`δ'` approximation
computed from its own simulation `N' ∼ P(r')`, `Z'_i ∼ μ'` with `r' • μ' = T • ν|_{|z| ≥ δ'}`
(compound Poisson thinning by marks). -/
theorem levy_coarse_map_eq {ν : Measure ℝ} {T : ℝ≥0} {δ δ' : ℝ} (hδ : δ ≤ δ') {r r' : ℝ≥0}
    {μ μ' : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (h : r • μ = T • ν.restrict (levySet δ)) (h' : r' • μ' = T • ν.restrict (levySet δ')) :
    (cpInputLaw r μ).map (levyFine ν T δ') = (cpInputLaw r' μ').map (levyFine ν T δ') := by
  have hf := measurable_id.indicator (measurableSet_levySet δ')
  have e : ∀ ρ : Measure (ℕ × (ℕ → ℝ)), ρ.map (levyFine ν T δ') =
      (ρ.map (cpSum ((levySet δ').indicator id))).map (fun x => x - levyComp ν T δ') :=
    fun ρ => by
      rw [Measure.map_map (measurable_sub_const _) (measurable_cpSum hf)]
      rfl
  rw [e, e, cpSum_map_eq_of_exponent hf hf fun t =>
    (exponent_levySet hδ h t).trans (exponent_levySet le_rfl h' t).symm]

/-- **The identity (2.4) for the truncated Lévy levels** (Giles 2015, §6.2, p. 47, l. 2045–2046:
"The ones which are larger than `δ_{ℓ−1}` get simulated in both the fine and coarse paths"; and
§2.1, p. 8, (2.4): `E[P^f_ℓ] = E[P^c_ℓ]`).  With the hypotheses of `levy_coarse_map_eq`, for
every measurable payoff `Φ`, the expectation of `Φ` of the coarse value of the level-`ℓ`
simulation (cutoff `δ ≤ δ'`, jumps `|z| ≥ δ` simulated, coarse value keeping those with
`|z| ≥ δ'`) equals the expectation of `Φ` of the fine value of the level-`(ℓ − 1)` simulation
(cutoff `δ'`). -/
theorem levy_truncation_2_4 {ν : Measure ℝ} {T : ℝ≥0} {δ δ' : ℝ} (hδ : δ ≤ δ') {r r' : ℝ≥0}
    {μ μ' : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (h : r • μ = T • ν.restrict (levySet δ)) (h' : r' • μ' = T • ν.restrict (levySet δ'))
    {Φ : ℝ → ℝ} (hΦ : Measurable Φ) :
    ∫ ω, Φ (levyFine ν T δ' ω) ∂(cpInputLaw r μ) =
      ∫ ω, Φ (levyFine ν T δ' ω) ∂(cpInputLaw r' μ') := by
  have hm := measurable_levyFine ν T δ'
  rw [← integral_map hm.aemeasurable hΦ.aestronglyMeasurable, levy_coarse_map_eq hδ h h',
    integral_map hm.aemeasurable hΦ.aestronglyMeasurable]

/-- The intermediate range `[δ, δ')` of jump sizes (Giles 2015, §6.2, p. 47, l. 2048–2050). -/
def levyMid (δ δ' : ℝ) : Set ℝ := {z | δ ≤ |z| ∧ |z| < δ'}

/-- `[δ, δ')` is measurable (Giles 2015, §6.2). -/
lemma measurableSet_levyMid (δ δ' : ℝ) : MeasurableSet (levyMid δ δ') :=
  (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)

/-- The fine minus the coarse value keeps exactly the jumps in `[δ, δ')` (Giles 2015, §6.2). -/
lemma indicator_levySet_sub {δ δ' : ℝ} (hδ : δ ≤ δ') (z : ℝ) :
    (levySet δ).indicator id z - (levySet δ').indicator id z = (levyMid δ δ').indicator id z := by
  by_cases h1 : δ' ≤ |z|
  · have h0 : δ ≤ |z| := hδ.trans h1
    have h2 : z ∉ levyMid δ δ' := fun h => absurd h.2 (not_lt.2 h1)
    rw [Set.indicator_of_mem (show z ∈ levySet δ from h0),
      Set.indicator_of_mem (show z ∈ levySet δ' from h1), Set.indicator_of_notMem h2, sub_self]
  · have h1' : z ∉ levySet δ' := h1
    rw [Set.indicator_of_notMem h1', sub_zero]
    by_cases h0 : δ ≤ |z|
    · rw [Set.indicator_of_mem (show z ∈ levySet δ from h0),
        Set.indicator_of_mem (show z ∈ levyMid δ δ' from ⟨h0, not_le.1 h1⟩)]
    · have h2 : z ∉ levyMid δ δ' := fun h => h0 h.1
      rw [Set.indicator_of_notMem (show z ∉ levySet δ from h0), Set.indicator_of_notMem h2]

/-- The compensator over `{δ ≤ |z| < 1}` as an integral against the jump law (Giles 2015, §6.2). -/
lemma levyComp_eq {ν : Measure ℝ} {T r : ℝ≥0} {μ : Measure ℝ} {δ δ' : ℝ} (hδ : δ ≤ δ')
    (h : r • μ = T • ν.restrict (levySet δ)) :
    levyComp ν T δ' = r * ∫ x, {z : ℝ | δ' ≤ |z| ∧ |z| < 1}.indicator id x ∂μ := by
  have hm : MeasurableSet {z : ℝ | δ' ≤ |z| ∧ |z| < 1} :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  rw [nnreal_mul_integral_of_smul_eq h, setIntegral_indicator hm,
    Set.inter_eq_right.2 (show {z : ℝ | δ' ≤ |z| ∧ |z| < 1} ⊆ levySet δ from
      fun z hz => le_trans hδ hz.1), levyComp]
  rfl

/-- The compensators of two cutoffs differ by the jumps in `[δ, δ')` (Giles 2015, §6.2), for
`δ ≤ δ' ≤ 1`. -/
lemma indicator_levySmall_sub {δ δ' : ℝ} (hδ : δ ≤ δ') (hδ1 : δ' ≤ 1) (z : ℝ) :
    {z : ℝ | δ ≤ |z| ∧ |z| < 1}.indicator id z - {z : ℝ | δ' ≤ |z| ∧ |z| < 1}.indicator id z =
      (levyMid δ δ').indicator id z := by
  by_cases h1 : |z| < 1
  · by_cases h2 : δ' ≤ |z|
    · rw [Set.indicator_of_mem (show z ∈ {z : ℝ | δ ≤ |z| ∧ |z| < 1} from ⟨hδ.trans h2, h1⟩),
        Set.indicator_of_mem (show z ∈ {z : ℝ | δ' ≤ |z| ∧ |z| < 1} from ⟨h2, h1⟩),
        Set.indicator_of_notMem (show z ∉ levyMid δ δ' from fun h => absurd h.2 (not_lt.2 h2)),
        sub_self]
    · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | δ' ≤ |z| ∧ |z| < 1} from fun h => h2 h.1),
        sub_zero]
      by_cases h0 : δ ≤ |z|
      · rw [Set.indicator_of_mem (show z ∈ {z : ℝ | δ ≤ |z| ∧ |z| < 1} from ⟨h0, h1⟩),
          Set.indicator_of_mem (show z ∈ levyMid δ δ' from ⟨h0, not_le.1 h2⟩)]
      · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | δ ≤ |z| ∧ |z| < 1} from fun h => h0 h.1),
          Set.indicator_of_notMem (show z ∉ levyMid δ δ' from fun h => h0 h.1)]
  · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | δ ≤ |z| ∧ |z| < 1} from fun h => h1 h.2),
      Set.indicator_of_notMem (show z ∉ {z : ℝ | δ' ≤ |z| ∧ |z| < 1} from fun h => h1 h.2),
      Set.indicator_of_notMem (show z ∉ levyMid δ δ' from fun h => h1 (h.2.trans_le hδ1)),
      sub_zero]

/-- **The multilevel correction of the truncated Lévy levels** (Giles 2015, §6.2, p. 47,
l. 2048–2051: "The difficulty is in the intermediate range `[δ_ℓ, δ_{ℓ−1}]` in which the jumps are
simulated for the fine path, but neglected … for the coarse path.  This is what leads to the
difference in path simulations, and contributes to a non-zero value for `P_ℓ − P_{ℓ−1}`").  With
the level-`ℓ` simulation of the jumps `|z| ≥ δ` (`r • μ = T • ν|_{|z| ≥ δ}`) and
`δ ≤ δ' ≤ 1`, the difference of the fine value (cutoff `δ`) and the coarse value (cutoff `δ'`) is
exactly the compensated sum of the jumps in `[δ, δ')`,
`∑_{i<N} 1_{δ ≤ |Z_i| < δ'} Z_i − T ∫_{δ ≤ |z| < δ'} z dν`; it is square integrable, its mean is
`0`, and `E[(X^δ − X^{δ'})²] = T ∫_{δ ≤ |z| < δ'} z² dν` exactly. -/
theorem levy_correction_moments {ν : Measure ℝ} {T : ℝ≥0} {δ δ' : ℝ} (hδ : δ ≤ δ')
    (hδ1 : δ' ≤ 1) {r : ℝ≥0} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : r • μ = T • ν.restrict (levySet δ)) :
    (∀ ω, levyFine ν T δ ω - levyFine ν T δ' ω =
        cpSum ((levyMid δ δ').indicator id) ω - T * ∫ z in levyMid δ δ', z ∂ν) ∧
      MemLp (fun ω => levyFine ν T δ ω - levyFine ν T δ' ω) 2 (cpInputLaw r μ) ∧
      ∫ ω, (levyFine ν T δ ω - levyFine ν T δ' ω) ∂(cpInputLaw r μ) = 0 ∧
      ∫ ω, (levyFine ν T δ ω - levyFine ν T δ' ω) ^ 2 ∂(cpInputLaw r μ) =
        T * ∫ z in levyMid δ δ', z ^ 2 ∂ν := by
  have := isProbabilityMeasure_cpInputLaw r μ
  set g : ℝ → ℝ := (levyMid δ δ').indicator id with hg
  have hmid := measurableSet_levyMid δ δ'
  have hsub : levyMid δ δ' ⊆ levySet δ := fun z hz => hz.1
  have hgm : Measurable g := measurable_id.indicator hmid
  have hgb : ∀ x, ‖g x‖ ≤ 1 := fun x => by
    by_cases hx : x ∈ levyMid δ δ'
    · rw [hg, Set.indicator_of_mem hx, id, Real.norm_eq_abs]
      exact (hx.2.trans_le hδ1).le
    · rw [hg, Set.indicator_of_notMem hx, norm_zero]
      exact zero_le_one
  have hg2 : MemLp g 2 μ := MemLp.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ hgb)
  obtain ⟨hL2, hmean, hsq⟩ := cpSum_moments r μ hgm hg2
  -- the mean of the kept jumps is the difference of the compensators
  have hmeanT : (r : ℝ) * ∫ x, g x ∂μ = T * ∫ z in levyMid δ δ', z ∂ν := by
    rw [nnreal_mul_integral_of_smul_eq h, hg, setIntegral_indicator hmid,
      Set.inter_eq_right.2 hsub]
    rfl
  have hcomp : levyComp ν T δ - levyComp ν T δ' = r * ∫ x, g x ∂μ := by
    have hb : ∀ a : ℝ, Integrable (fun x => {z : ℝ | a ≤ |z| ∧ |z| < 1}.indicator id x) μ :=
      fun a => by
        refine Integrable.of_bound ((measurable_id.indicator
          ((measurableSet_le measurable_const continuous_abs.measurable).inter
            (measurableSet_lt continuous_abs.measurable measurable_const))).aestronglyMeasurable)
          1 (ae_of_all _ fun x => ?_)
        by_cases hx : x ∈ {z : ℝ | a ≤ |z| ∧ |z| < 1}
        · rw [Set.indicator_of_mem hx, id, Real.norm_eq_abs]
          exact hx.2.le
        · rw [Set.indicator_of_notMem hx, norm_zero]
          exact zero_le_one
    rw [levyComp_eq le_rfl h, levyComp_eq hδ h, ← mul_sub, ← integral_sub (hb δ) (hb δ')]
    congr 2
    funext x
    exact indicator_levySmall_sub hδ hδ1 x
  have hid : ∀ ω, levyFine ν T δ ω - levyFine ν T δ' ω = cpSum g ω - r * ∫ x, g x ∂μ := by
    intro ω
    rw [← hcomp]
    have : cpSum ((levySet δ).indicator id) ω - cpSum ((levySet δ').indicator id) ω =
        cpSum g ω := by
      unfold cpSum
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => indicator_levySet_sub hδ _
    unfold levyFine
    linarith
  simp_rw [hid]
  refine ⟨fun ω => by rw [hmeanT], hL2.sub (memLp_const _), ?_, ?_⟩
  · rw [integral_sub (hL2.integrable one_le_two) (integrable_const _), hmean, integral_const,
      probReal_univ, one_smul, sub_self]
  · rw [hsq, nnreal_mul_integral_of_smul_eq h]
    have e : (fun x => g x ^ 2) = (levyMid δ δ').indicator fun z => z ^ 2 := by
      funext x
      by_cases hx : x ∈ levyMid δ δ'
      · rw [hg, Set.indicator_of_mem hx, Set.indicator_of_mem hx, id]
      · rw [hg, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        ring
    rw [e, setIntegral_indicator hmid, Set.inter_eq_right.2 hsub]

/-- `(Φ(a) − Φ(b))² ≤ K² (a − b)²` for a `K`-Lipschitz payoff `Φ` (Giles 2015, §6.2). -/
lemma sq_sub_le_of_lipschitz {Φ : ℝ → ℝ} {K : ℝ≥0} (hΦ : LipschitzWith K Φ) (a b : ℝ) :
    (Φ a - Φ b) ^ 2 ≤ (K : ℝ) ^ 2 * (a - b) ^ 2 := by
  have h1 := hΦ.dist_le_mul a b
  rw [Real.dist_eq, Real.dist_eq] at h1
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rwa [mul_pow, sq_abs, sq_abs] at h2

/-- **The variance of the multilevel correction of a Lipschitz payoff** (Giles 2015, §6.2, p. 47,
l. 2048–2051, the intermediate range `[δ_ℓ, δ_{ℓ−1}]` "contributes to a non-zero value for
`P_ℓ − P_{ℓ−1}`"; §2.1, Theorem 1, condition iii)).  With the level-`ℓ` simulation of the jumps
`|z| ≥ δ` (`r • μ = T • ν|_{|z| ≥ δ}`), `δ ≤ δ' ≤ 1` and a `K`-Lipschitz payoff `Φ`, the correction
`Φ(X^δ) − Φ(X^{δ'})` is square integrable and
`V_ℓ = V[Φ(X^δ) − Φ(X^{δ'})] ≤ K² T ∫_{δ ≤ |z| < δ'} z² dν`. -/
theorem levy_correction_variance_le {ν : Measure ℝ} {T : ℝ≥0} {δ δ' : ℝ} (hδ : δ ≤ δ')
    (hδ1 : δ' ≤ 1) {r : ℝ≥0} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : r • μ = T • ν.restrict (levySet δ)) {Φ : ℝ → ℝ} {K : ℝ≥0} (hΦ : LipschitzWith K Φ) :
    MemLp (fun ω => Φ (levyFine ν T δ ω) - Φ (levyFine ν T δ' ω)) 2 (cpInputLaw r μ) ∧
      variance (fun ω => Φ (levyFine ν T δ ω) - Φ (levyFine ν T δ' ω)) (cpInputLaw r μ) ≤
        K ^ 2 * (T * ∫ z in levyMid δ δ', z ^ 2 ∂ν) := by
  have := isProbabilityMeasure_cpInputLaw r μ
  obtain ⟨-, hL2, -, hsq⟩ := levy_correction_moments hδ hδ1 h
  have hm : Measurable fun ω => Φ (levyFine ν T δ ω) - Φ (levyFine ν T δ' ω) :=
    (hΦ.continuous.measurable.comp (measurable_levyFine ν T δ)).sub
      (hΦ.continuous.measurable.comp (measurable_levyFine ν T δ'))
  have hL2' : MemLp (fun ω => Φ (levyFine ν T δ ω) - Φ (levyFine ν T δ' ω)) 2
      (cpInputLaw r μ) :=
    (hL2.const_mul (K : ℝ)).of_le hm.aestronglyMeasurable (ae_of_all _ fun ω => by
      have h1 := hΦ.dist_le_mul (levyFine ν T δ ω) (levyFine ν T δ' ω)
      rw [Real.dist_eq, Real.dist_eq] at h1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, NNReal.abs_eq]
      exact h1)
  refine ⟨hL2', (variance_le_expectation_sq hm.aestronglyMeasurable).trans ?_⟩
  rw [← hsq, ← integral_const_mul]
  refine integral_mono hL2'.integrable_sq (hL2.integrable_sq.const_mul _) fun ω => ?_
  exact sq_sub_le_of_lipschitz hΦ _ _

/-! ### All levels on one probability space: the bands of jump sizes -/

/-- The bands of jump sizes (Giles 2015, §6.2, p. 47, l. 2045–2050, the "three categories" of
jumps): band `0` is `{|z| ≥ δ_0}` and band `k + 1` is `[δ_{k+1}, δ_k)`, the jumps simulated on the
fine path of level `k + 1` but not on its coarse path. -/
def levyBand (δ : ℕ → ℝ) : ℕ → Set ℝ
  | 0 => levySet (δ 0)
  | k + 1 => levyMid (δ (k + 1)) (δ k)

/-- The bands are measurable (Giles 2015, §6.2). -/
lemma measurableSet_levyBand (δ : ℕ → ℝ) : ∀ k, MeasurableSet (levyBand δ k)
  | 0 => measurableSet_levySet _
  | _ + 1 => measurableSet_levyMid _ _

/-- The law of the inputs of all levels at once (Giles 2015, §6.2, p. 47, l. 2045–2050): for each
band `k` an independent compound Poisson input, `N_k ∼ P(Λ_k)` and jumps `∼ M_k` i.i.d.; with
`Λ_k • M_k = T • ν|_{band k}` these are the jumps of the Lévy process in the band. -/
noncomputable def bandInputLaw (Λ : ℕ → ℝ≥0) (M : ℕ → Measure ℝ)
    [∀ k, IsProbabilityMeasure (M k)] : Measure (ℕ → ℕ × (ℕ → ℝ)) :=
  Measure.infinitePi fun k => (poissonMeasure (Λ k)).prod (Measure.infinitePi fun _ : ℕ => M k)

/-- **The level-`ℓ` approximation on the common space** (Giles 2015, §6.2, p. 47, l. 2038–2050):
the jumps of the bands `0, …, ℓ` (all jumps `|z| ≥ δ_ℓ`) minus the compensator
`T ∫_{δ_ℓ ≤ |z| < 1} z dν`.  The level-`ℓ` correction uses the bands `0, …, ℓ` on the fine path and
`0, …, ℓ − 1` on the coarse path. -/
noncomputable def bandApprox (ν : Measure ℝ) (T : ℝ≥0) (δ : ℕ → ℝ) (ℓ : ℕ)
    (ω : ℕ → ℕ × (ℕ → ℝ)) : ℝ :=
  ∑ k ∈ range (ℓ + 1), cpSum ((levyBand δ k).indicator id) (ω k) - levyComp ν T (δ ℓ)

/-- The compensated sum of the jumps of band `k` (Giles 2015, §6.2, p. 47, l. 2048–2051):
`∑_{i<N_k} 1_{band k}(Z_{k,i}) Z_{k,i} − T ∫_{band k} z dν`. -/
noncomputable def bandTerm (ν : Measure ℝ) (T : ℝ≥0) (δ : ℕ → ℝ) (k : ℕ)
    (x : ℕ × (ℕ → ℝ)) : ℝ :=
  cpSum ((levyBand δ k).indicator id) x - T * ∫ z in levyBand δ k, z ∂ν

/-- The input law of all levels is a probability measure (Giles 2015, §6.2). -/
lemma isProbabilityMeasure_bandInputLaw (Λ : ℕ → ℝ≥0) (M : ℕ → Measure ℝ)
    [∀ k, IsProbabilityMeasure (M k)] : IsProbabilityMeasure (bandInputLaw Λ M) := by
  unfold bandInputLaw
  infer_instance

/-- A Lévy measure gives finite mass to `{|z| ≥ δ}`, `δ > 0` (Giles 2015, §6.2, p. 47, l. 2038:
only finitely many jumps of size `≥ δ` occur). -/
lemma levy_measure_levySet_lt_top {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    {δ : ℝ} (hδ : 0 < δ) : ν (levySet δ) < ∞ := by
  have h := hν.measure_norm_ge_lt_top (ε := min 1 (δ ^ 2)) (by positivity)
  refine lt_of_le_of_lt (measure_mono fun z hz => ?_) h
  have hz' : δ ≤ |z| := hz
  show min 1 (δ ^ 2) ≤ ‖min 1 (z ^ 2)‖
  rw [Real.norm_of_nonneg (by positivity)]
  refine min_le_min le_rfl ?_
  have := pow_le_pow_left₀ hδ.le hz' 2
  rwa [sq_abs] at this

/-- Bounded functions are integrable on `[a, c)`, `0 < a`, `c ≤ 1` (Giles 2015, §6.2). -/
lemma integrableOn_levyMid {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    {a c : ℝ} (ha : 0 < a) (hc : c ≤ 1) {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hb : ∀ z, |z| < 1 → |φ z| ≤ 1) : IntegrableOn φ (levyMid a c) ν := by
  have hfin : ν (levyMid a c) ≠ ∞ :=
    ((measure_mono fun z hz => hz.1 : ν (levyMid a c) ≤ ν (levySet a)).trans_lt
      (levy_measure_levySet_lt_top hν ha)).ne
  have := isFiniteMeasure_restrict.2 hfin
  exact Integrable.of_bound hφ.aestronglyMeasurable 1
    (ae_restrict_of_forall_mem (measurableSet_levyMid a c) fun z hz => by
      rw [Real.norm_eq_abs]
      exact hb z (hz.2.trans_le hc))

/-- Splitting `[a, c)` at `b` (Giles 2015, §6.2): `∫_{[a,c)} = ∫_{[b,c)} + ∫_{[a,b)}`. -/
lemma setIntegral_levyMid_split {ν : Measure ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {φ : ℝ → ℝ} (hφ : IntegrableOn φ (levyMid a c) ν) :
    ∫ z in levyMid a c, φ z ∂ν = ∫ z in levyMid b c, φ z ∂ν + ∫ z in levyMid a b, φ z ∂ν := by
  have e : levyMid a c = levyMid b c ∪ levyMid a b := by
    ext z
    rw [Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : b ≤ |z|
      · exact Or.inl ⟨h3, h2⟩
      · exact Or.inr ⟨h1, not_le.1 h3⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨hab.trans h1, h2⟩
      · exact ⟨h1, h2.trans_le hbc⟩
  have hd : Disjoint (levyMid b c) (levyMid a b) :=
    Set.disjoint_left.2 fun z h1 h2 => absurd h1.1 (not_le.2 h2.2)
  rw [e] at hφ ⊢
  exact setIntegral_union hd (measurableSet_levyMid a b) (hφ.mono_set Set.subset_union_left)
    (hφ.mono_set Set.subset_union_right)

/-- The compensators of two cutoffs `0 < δ' ≤ δ ≤ 1` differ by the jumps in `[δ', δ)`
(Giles 2015, §6.2): `levyComp δ' − levyComp δ = T ∫_{[δ', δ)} z dν`. -/
lemma levyComp_sub {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν) (T : ℝ≥0)
    {δ δ' : ℝ} (hδ' : 0 < δ') (hδδ : δ' ≤ δ) (hδ1 : δ ≤ 1) :
    levyComp ν T δ' - levyComp ν T δ = T * ∫ z in levyMid δ' δ, z ∂ν := by
  have h := setIntegral_levyMid_split (ν := ν) hδδ hδ1 (φ := id)
    (integrableOn_levyMid hν hδ' le_rfl measurable_id fun z hz => hz.le)
  have e : ∀ a, levyComp ν T a = T * ∫ z in levyMid a 1, z ∂ν := fun a => rfl
  rw [e, e]
  change (T : ℝ) * ∫ z in levyMid δ' 1, id z ∂ν - T * ∫ z in levyMid δ 1, id z ∂ν =
    T * ∫ z in levyMid δ' δ, id z ∂ν
  rw [h]
  ring

/-- One more band (Giles 2015, §6.2, p. 47, l. 2048–2051): the level-`(ℓ + 1)` approximation minus
the level-`ℓ` one is the compensated sum of the jumps of band `ℓ + 1`, `[δ_{ℓ+1}, δ_ℓ)`. -/
lemma bandApprox_succ_sub {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1)
    (ℓ : ℕ) (ω : ℕ → ℕ × (ℕ → ℝ)) :
    bandApprox ν T δ (ℓ + 1) ω - bandApprox ν T δ ℓ ω = bandTerm ν T δ (ℓ + 1) (ω (ℓ + 1)) := by
  have h := levyComp_sub hν T (hδpos (ℓ + 1)) (hδanti (Nat.le_succ ℓ))
    ((hδanti (Nat.zero_le ℓ)).trans hδ1)
  unfold bandApprox bandTerm
  rw [Finset.sum_range_succ]
  change _ - _ - (_ - _) = _ - (T : ℝ) * ∫ z in levyMid (δ (ℓ + 1)) (δ ℓ), z ∂ν
  linarith

/-- The level-`ℓ'` approximation minus the level-`ℓ` one, `ℓ ≤ ℓ'`, is the sum of the compensated
band sums of the bands `ℓ + 1, …, ℓ'` (Giles 2015, §6.2). -/
lemma bandApprox_sub {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1)
    {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ') (ω : ℕ → ℕ × (ℕ → ℝ)) :
    bandApprox ν T δ ℓ' ω - bandApprox ν T δ ℓ ω =
      ∑ k ∈ Ico (ℓ + 1) (ℓ' + 1), bandTerm ν T δ k (ω k) := by
  induction ℓ', hℓ using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ← ih,
        ← bandApprox_succ_sub hν T hδpos hδanti hδ1 n ω]
      ring

/-- Integrals over the bands `ℓ + 1, …, ℓ'` add up to the integral over `[δ_{ℓ'}, δ_ℓ)`
(Giles 2015, §6.2). -/
lemma sum_setIntegral_levyBand {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1) {φ : ℝ → ℝ}
    (hφ : Measurable φ) (hb : ∀ z, |z| < 1 → |φ z| ≤ 1) {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ') :
    ∑ k ∈ Ico (ℓ + 1) (ℓ' + 1), ∫ z in levyBand δ k, φ z ∂ν =
      ∫ z in levyMid (δ ℓ') (δ ℓ), φ z ∂ν := by
  induction ℓ', hℓ using Nat.le_induction with
  | base =>
      have e : levyMid (δ ℓ) (δ ℓ) = ∅ :=
        Set.eq_empty_of_forall_notMem fun z hz => absurd hz.2 (not_lt.2 hz.1)
      rw [Finset.Ico_self, Finset.sum_empty, e, Measure.restrict_empty, integral_zero_measure]
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih,
        setIntegral_levyMid_split (hδanti (Nat.le_succ n)) (hδanti hn)
          (integrableOn_levyMid hν (hδpos (n + 1)) ((hδanti (Nat.zero_le ℓ)).trans hδ1) hφ hb)]
      rfl

/-- The compensated band sum is measurable (Giles 2015, §6.2). -/
lemma measurable_bandTerm (ν : Measure ℝ) (T : ℝ≥0) (δ : ℕ → ℝ) (k : ℕ) :
    Measurable (bandTerm ν T δ k) :=
  (measurable_cpSum (measurable_id.indicator (measurableSet_levyBand δ k))).sub_const _

/-- The compensated sum of the jumps of band `j + 1`, `[δ_{j+1}, δ_j)`, is square integrable, has
mean `0` and second moment `T ∫_{band} z² dν` (Giles 2015, §6.2, p. 47, l. 2048–2051). -/
lemma bandTerm_moments {ν : Measure ℝ} (T : ℝ≥0) {δ : ℕ → ℝ} (hδanti : Antitone δ)
    (hδ1 : δ 0 ≤ 1) {r : ℝ≥0} {μ : Measure ℝ} [IsProbabilityMeasure μ] (j : ℕ)
    (h : r • μ = T • ν.restrict (levyBand δ (j + 1))) :
    MemLp (bandTerm ν T δ (j + 1)) 2 (cpInputLaw r μ) ∧
      ∫ x, bandTerm ν T δ (j + 1) x ∂(cpInputLaw r μ) = 0 ∧
      ∫ x, bandTerm ν T δ (j + 1) x ^ 2 ∂(cpInputLaw r μ) =
        T * ∫ z in levyBand δ (j + 1), z ^ 2 ∂ν := by
  have := isProbabilityMeasure_cpInputLaw r μ
  have hB := measurableSet_levyBand δ (j + 1)
  set g : ℝ → ℝ := (levyBand δ (j + 1)).indicator id with hg
  have hgm : Measurable g := measurable_id.indicator hB
  have hgb : ∀ x, ‖g x‖ ≤ 1 := fun x => by
    by_cases hx : x ∈ levyBand δ (j + 1)
    · rw [hg, Set.indicator_of_mem hx, id, Real.norm_eq_abs]
      exact (hx.2.trans_le ((hδanti (Nat.zero_le j)).trans hδ1)).le
    · rw [hg, Set.indicator_of_notMem hx, norm_zero]
      exact zero_le_one
  have hg2 : MemLp g 2 μ := MemLp.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ hgb)
  obtain ⟨hL2, hmean, hsq⟩ := cpSum_moments r μ hgm hg2
  have hm : (r : ℝ) * ∫ x, g x ∂μ = T * ∫ z in levyBand δ (j + 1), z ∂ν := by
    rw [nnreal_mul_integral_of_smul_eq h, hg, setIntegral_indicator hB, Set.inter_self]
    rfl
  have e : bandTerm ν T δ (j + 1) = fun x => cpSum g x - r * ∫ x, g x ∂μ := by
    funext x
    rw [hm]
    rfl
  rw [e]
  refine ⟨hL2.sub (memLp_const _), ?_, ?_⟩
  · rw [integral_sub (hL2.integrable one_le_two) (integrable_const _), hmean, integral_const,
      probReal_univ, one_smul, sub_self]
  · rw [hsq, nnreal_mul_integral_of_smul_eq h]
    have e2 : (fun x => g x ^ 2) = (levyBand δ (j + 1)).indicator fun z => z ^ 2 := by
      funext x
      by_cases hx : x ∈ levyBand δ (j + 1)
      · rw [hg, Set.indicator_of_mem hx, Set.indicator_of_mem hx, id]
      · rw [hg, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        ring
    rw [e2, setIntegral_indicator hB, Set.inter_self]

/-- Sums of independent centred square-integrable coordinates (Giles 2015, §6.2): under a product
of probability measures, `E[(∑_{k∈s} F_k(ω_k))²] = ∑_{k∈s} E[F_k²]` when each `F_k` has mean `0`. -/
lemma integral_sq_sum_infinitePi {X : ℕ → Type*} [∀ k, MeasurableSpace (X k)]
    (P : ∀ k, Measure (X k)) [∀ k, IsProbabilityMeasure (P k)] (s : Finset ℕ)
    {F : ∀ k, X k → ℝ} (hFm : ∀ k, Measurable (F k)) (hF : ∀ k ∈ s, MemLp (F k) 2 (P k))
    (h0 : ∀ k ∈ s, ∫ x, F k x ∂(P k) = 0) :
    MemLp (fun ω => ∑ k ∈ s, F k (ω k)) 2 (Measure.infinitePi P) ∧
      ∫ ω, (∑ k ∈ s, F k (ω k)) ^ 2 ∂(Measure.infinitePi P) =
        ∑ k ∈ s, ∫ x, F k x ^ 2 ∂(P k) := by
  set Q := Measure.infinitePi P with hQ
  have hev : ∀ k, MeasurePreserving (fun ω : (∀ k, X k) => ω k) Q (P k) := fun k =>
    measurePreserving_eval_infinitePi P k
  have hFk : ∀ k ∈ s, MemLp (fun ω : (∀ k, X k) => F k (ω k)) 2 Q := fun k hk =>
    (hF k hk).comp_measurePreserving (hev k)
  have hS : MemLp (fun ω => ∑ k ∈ s, F k (ω k)) 2 Q := memLp_finsetSum s hFk
  have hint : ∀ k, ∫ ω, F k (ω k) ∂Q = ∫ x, F k x ∂(P k) := fun k => by
    have h := integral_map (μ := Q) (hev k).measurable.aemeasurable (f := F k)
      (by rw [(hev k).map_eq]; exact (hFm k).aestronglyMeasurable)
    rw [(hev k).map_eq] at h
    exact h.symm
  have hmean : ∫ ω, ∑ k ∈ s, F k (ω k) ∂Q = 0 := by
    rw [integral_finsetSum _ fun k hk => (hFk k hk).integrable one_le_two]
    exact Finset.sum_eq_zero fun k hk => by rw [hint k, h0 k hk]
  have e : (fun ω => ∑ k ∈ s, F k (ω k)) = ∑ k ∈ s, fun ω : (∀ k, X k) => F k (ω k) := by
    funext ω
    rw [Finset.sum_apply]
  have hvar := IndepFun.variance_sum (μ := Q) (X := fun k ω => F k (ω k)) (s := s) hFk
    fun i _ j _ hij => (iIndepFun_infinitePi (P := P) (X := F) hFm).indepFun hij
  rw [← e, variance_eq_sub hS, hmean] at hvar
  refine ⟨hS, ?_⟩
  simp only [Pi.pow_apply] at hvar
  have h00 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [h00, sub_zero] at hvar
  rw [hvar]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [(hev k).variance_fun_comp (hFm k).aemeasurable, variance_eq_sub (hF k hk), h0 k hk]
  simp

/-- **The truncation levels converge in mean square** (Giles 2015, §6.2, p. 47, l. 2042–2043:
"the cutoff `δ_ℓ` for the jumps which are simulated varies with level"): on the common space of
all bands, for `ℓ ≤ ℓ'` the difference of the level-`ℓ'` and the level-`ℓ`
approximations is square integrable with
`E[(X^{δ_{ℓ'}} − X^{δ_ℓ})²] = T ∫_{δ_{ℓ'} ≤ |z| < δ_ℓ} z² dν`. -/
theorem bandApprox_sq_sub {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1)
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ') :
    MemLp (fun ω => bandApprox ν T δ ℓ' ω - bandApprox ν T δ ℓ ω) 2 (bandInputLaw Λ M) ∧
      ∫ ω, (bandApprox ν T δ ℓ' ω - bandApprox ν T δ ℓ ω) ^ 2 ∂(bandInputLaw Λ M) =
        T * ∫ z in levyMid (δ ℓ') (δ ℓ), z ^ 2 ∂ν := by
  have hP : ∀ k, IsProbabilityMeasure (cpInputLaw (Λ k) (M k)) := fun k =>
    isProbabilityMeasure_cpInputLaw _ _
  simp_rw [bandApprox_sub hν T hδpos hδanti hδ1 hℓ]
  have hk1 : ∀ k ∈ Ico (ℓ + 1) (ℓ' + 1), k = (k - 1) + 1 := fun k hk => by
    have := (Finset.mem_Ico.1 hk).1
    omega
  have hmom : ∀ k ∈ Ico (ℓ + 1) (ℓ' + 1),
      MemLp (bandTerm ν T δ k) 2 (cpInputLaw (Λ k) (M k)) ∧
        ∫ x, bandTerm ν T δ k x ∂(cpInputLaw (Λ k) (M k)) = 0 ∧
        ∫ x, bandTerm ν T δ k x ^ 2 ∂(cpInputLaw (Λ k) (M k)) =
          T * ∫ z in levyBand δ k, z ^ 2 ∂ν := fun k hk => by
    rw [hk1 k hk]
    exact bandTerm_moments T hδanti hδ1 (k - 1) (hband _)
  obtain ⟨hL2, hsq⟩ := integral_sq_sum_infinitePi (fun k => cpInputLaw (Λ k) (M k))
    (Ico (ℓ + 1) (ℓ' + 1)) (measurable_bandTerm ν T δ) (fun k hk => (hmom k hk).1)
    (fun k hk => (hmom k hk).2.1)
  refine ⟨hL2, ?_⟩
  change ∫ ω, (∑ k ∈ Ico (ℓ + 1) (ℓ' + 1), bandTerm ν T δ k (ω k)) ^ 2
    ∂(Measure.infinitePi fun k => cpInputLaw (Λ k) (M k)) = _
  rw [hsq, Finset.sum_congr rfl fun k hk => (hmom k hk).2.2, ← Finset.mul_sum,
    sum_setIntegral_levyBand hν hδpos hδanti hδ1 (φ := fun z => z ^ 2) (by fun_prop) (fun z hz => by
      rw [abs_of_nonneg (sq_nonneg z)]
      nlinarith [abs_nonneg z, sq_abs z]) hℓ]

/-- A mean-square limit with a known tail (Giles 2015, §6.2; the argument of
`exists_klField_limit`): if `F_ℓ ∈ L²`, `E[(F_{ℓ'} − F_ℓ)²] ≤ τ_ℓ` for `ℓ ≤ ℓ'`,
`E[(F_{ℓ'} − F_ℓ)²] → τ_ℓ` as `ℓ' → ∞` and `τ_ℓ → 0`, then `F_ℓ` converges in `L²` to some `G`
with `E[(G − F_ℓ)²] = τ_ℓ`. -/
lemma exists_L2_limit_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F : ℕ → Ω → ℝ} (hF : ∀ ℓ, MemLp (F ℓ) 2 P) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝 0))
    (hle : ∀ ℓ ℓ', ℓ ≤ ℓ' → ∫ ω, (F ℓ' ω - F ℓ ω) ^ 2 ∂P ≤ τ ℓ)
    (hlim : ∀ ℓ, Tendsto (fun ℓ' => ∫ ω, (F ℓ' ω - F ℓ ω) ^ 2 ∂P) atTop (𝓝 (τ ℓ))) :
    ∃ G : Ω → ℝ, MemLp G 2 P ∧ ∀ ℓ, ∫ ω, (G ω - F ℓ ω) ^ 2 ∂P = τ ℓ := by
  set Fl : ℕ → Lp ℝ 2 P := fun ℓ => (hF ℓ).toLp _ with hFl
  have hnorm : ∀ ℓ ℓ', ‖Fl ℓ' - Fl ℓ‖ ^ 2 = ∫ ω, (F ℓ' ω - F ℓ ω) ^ 2 ∂P := by
    intro ℓ ℓ'
    rw [hFl, ← MemLp.toLp_sub, klNorm_toLp_sq]
    rfl
  have hcauchy : CauchySeq Fl := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := ((tendsto_order.1 hτ).2 (ε ^ 2) (by positivity)).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
    rw [hnorm]
    exact (hle N n hn).trans_lt (hN N le_rfl)
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨G, Lp.memLp G, fun ℓ => ?_⟩
  have h1 : Tendsto (fun ℓ' => ‖Fl ℓ' - Fl ℓ‖ ^ 2) atTop (𝓝 (‖G - Fl ℓ‖ ^ 2)) :=
    ((hG.sub_const (Fl ℓ)).norm).pow 2
  simp_rw [hnorm] at h1
  have hGl : G - Fl ℓ = ((Lp.memLp G).sub (hF ℓ)).toLp _ := by
    rw [MemLp.toLp_sub (Lp.memLp G) (hF ℓ), Lp.toLp_coeFn]
  rw [← tendsto_nhds_unique h1 (hlim ℓ), hGl, klNorm_toLp_sq]
  rfl

/-- `∫_{δ_n ≤ |z| < c} z² dν → ∫_{|z| < c} z² dν` as `δ_n → 0`, `c ≤ 1` (Giles 2015, §6.2,
dominated convergence). -/
lemma tendsto_setIntegral_levyMid_sq {ν : Measure ℝ}
    (hν : Integrable (fun z => min 1 (z ^ 2)) ν) {δ : ℕ → ℝ} (hδlim : Tendsto δ atTop (𝓝 0))
    {c : ℝ} (hc : c ≤ 1) :
    Tendsto (fun n => ∫ z in levyMid (δ n) c, z ^ 2 ∂ν) atTop
      (𝓝 (∫ z in {z : ℝ | |z| < c}, z ^ 2 ∂ν)) := by
  have hc' : MeasurableSet {z : ℝ | |z| < c} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  simp_rw [← integral_indicator (measurableSet_levyMid _ c), ← integral_indicator hc']
  refine tendsto_integral_of_dominated_convergence (fun z => min 1 (z ^ 2))
    (fun n => ((measurable_id.pow_const 2).indicator
      (measurableSet_levyMid _ c)).aestronglyMeasurable) hν
    (fun n => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
  · by_cases hz : z ∈ levyMid (δ n) c
    · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (sq_nonneg z)]
      have h1 : |z| < 1 := hz.2.trans_le hc
      have h2 : z ^ 2 ≤ 1 := by nlinarith [abs_nonneg z, sq_abs z]
      rw [min_eq_right h2]
    · rw [Set.indicator_of_notMem hz, norm_zero]
      positivity
  · by_cases hz0 : z = 0
    · subst hz0
      have h0 : ∀ s : Set ℝ, s.indicator (fun z : ℝ => z ^ 2) 0 = 0 := fun s =>
        Set.indicator_apply_eq_zero.2 fun _ => by norm_num
      simp only [h0]
      exact tendsto_const_nhds
    · have hpos : 0 < |z| := abs_pos.2 hz0
      have hev : ∀ᶠ n in atTop, δ n ≤ |z| :=
        ((tendsto_order.1 hδlim).2 _ hpos).mono fun n h => h.le
      refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
      dsimp only
      by_cases hzc : |z| < c
      · rw [Set.indicator_of_mem (show z ∈ {z : ℝ | |z| < c} from hzc),
          Set.indicator_of_mem (show z ∈ levyMid (δ n) c from ⟨hn, hzc⟩)]
      · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | |z| < c} from hzc),
          Set.indicator_of_notMem (show z ∉ levyMid (δ n) c from fun h => hzc h.2)]

/-- The small-jump second moment tends to `0`: `∫_{|z| < δ_n} z² dν → 0` as `δ_n → 0`
(Giles 2015, §6.2, p. 47, l. 2042–2043: "`δ_ℓ → 0` as `ℓ → ∞` to ensure that the bias converges to
zero"; dominated convergence). -/
lemma tendsto_setIntegral_small_sq {ν : Measure ℝ}
    (hν : Integrable (fun z => min 1 (z ^ 2)) ν) {δ : ℕ → ℝ} (hδanti : Antitone δ)
    (hδ1 : δ 0 ≤ 1) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z in {z : ℝ | |z| < δ n}, z ^ 2 ∂ν) atTop (𝓝 0) := by
  have hm : ∀ n, MeasurableSet {z : ℝ | |z| < δ n} := fun n =>
    measurableSet_lt continuous_abs.measurable measurable_const
  simp_rw [← integral_indicator (hm _)]
  have h := tendsto_integral_of_dominated_convergence (μ := ν) (f := fun _ : ℝ => (0 : ℝ))
    (F := fun n => {z : ℝ | |z| < δ n}.indicator fun z => z ^ 2) (fun z => min 1 (z ^ 2))
    (fun n => ((measurable_id.pow_const 2).indicator (hm n)).aestronglyMeasurable) hν
    (fun n => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
  · simpa using h
  · by_cases hz : z ∈ {z : ℝ | |z| < δ n}
    · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (sq_nonneg z)]
      have h1 : |z| < 1 := (show |z| < δ n from hz).trans_le ((hδanti (Nat.zero_le n)).trans hδ1)
      have h2 : z ^ 2 ≤ 1 := by nlinarith [abs_nonneg z, sq_abs z]
      rw [min_eq_right h2]
    · rw [Set.indicator_of_notMem hz, norm_zero]
      positivity
  · by_cases hz0 : z = 0
    · subst hz0
      have h0 : ∀ s : Set ℝ, s.indicator (fun z : ℝ => z ^ 2) 0 = 0 := fun s =>
        Set.indicator_apply_eq_zero.2 fun _ => by norm_num
      simp only [h0]
      exact tendsto_const_nhds
    · have hpos : 0 < |z| := abs_pos.2 hz0
      have hev : ∀ᶠ n in atTop, δ n ≤ |z| :=
        ((tendsto_order.1 hδlim).2 _ hpos).mono fun n h => h.le
      refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
      dsimp only
      rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | |z| < δ n} from not_lt.2 hn)]

/-- The level-`ℓ` approximation on the common space is measurable (Giles 2015, §6.2). -/
lemma measurable_bandApprox (ν : Measure ℝ) (T : ℝ≥0) (δ : ℕ → ℝ) (ℓ : ℕ) :
    Measurable (bandApprox ν T δ ℓ) :=
  (Finset.measurable_fun_sum _ fun k _ => (measurable_cpSum (measurable_id.indicator
    (measurableSet_levyBand δ k))).comp (measurable_pi_apply k)).sub_const _

/-- **The truncated levels converge and the bias tends to zero** (Giles 2015, §6.2, p. 47,
l. 2038–2043: "simulate the large jumps and … neglect the small jumps …  the cutoff `δ_ℓ` for the
jumps which are simulated varies with level, and `δ_ℓ → 0` as `ℓ → ∞` to ensure that the bias
converges to zero").  Let `ν` be a Lévy measure (`∫ min(1, z²) dν < ∞`, possibly of infinite total
mass), `T ≥ 0`, and let the cutoffs `0 < δ_ℓ ≤ δ_0 ≤ 1` decrease to `0`.  All levels are built on
one probability space from independent compound Poisson inputs for the bands `{|z| ≥ δ_0}` and
`[δ_{k+1}, δ_k)` (`Λ_k • M_k = T • ν|_{band k}`).  Then there is a limit `X`, an `L²` limit (its
Lévy–Khintchine law is not derived here; it is `levy_truncation_limit_charFun` in
`MlmcLean.LevyKhintchineLimit`), with `X − X^{δ_0} ∈ L²` and, for every level `ℓ`,
`E[(X − X^{δ_ℓ})²] = T ∫_{|z| < δ_ℓ} z² dν`, which tends to `0`.  For every `K`-Lipschitz payoff
`Φ` the bias satisfies `|E[Φ(X^{δ_ℓ}) − Φ(X)]| ≤ K (T ∫_{|z| < δ_ℓ} z² dν)^{1/2} → 0`. -/
theorem levy_truncation_limit {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1)
    (hδlim : Tendsto δ atTop (𝓝 0)) {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ}
    [∀ k, IsProbabilityMeasure (M k)] (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) :
    ∃ X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ,
      MemLp (fun ω => X ω - bandApprox ν T δ 0 ω) 2 (bandInputLaw Λ M) ∧
      (∀ ℓ, Integrable (fun ω => (X ω - bandApprox ν T δ ℓ ω) ^ 2) (bandInputLaw Λ M) ∧
        ∫ ω, (X ω - bandApprox ν T δ ℓ ω) ^ 2 ∂(bandInputLaw Λ M) =
          T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) ∧
      Tendsto (fun ℓ => (T : ℝ) * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) atTop (𝓝 0) ∧
      ∀ (Φ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K Φ → ∀ ℓ,
        Integrable (fun ω => Φ (bandApprox ν T δ ℓ ω) - Φ (X ω)) (bandInputLaw Λ M) ∧
        |∫ ω, Φ (bandApprox ν T δ ℓ ω) - Φ (X ω) ∂(bandInputLaw Λ M)| ≤
          K * Real.sqrt (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) := by
  have := isProbabilityMeasure_bandInputLaw Λ M
  set P := bandInputLaw Λ M with hP
  set F : ℕ → (ℕ → ℕ × (ℕ → ℝ)) → ℝ :=
    fun ℓ ω => bandApprox ν T δ ℓ ω - bandApprox ν T δ 0 ω with hFdef
  have hF : ∀ ℓ, MemLp (F ℓ) 2 P := fun ℓ =>
    (bandApprox_sq_sub hν T hδpos hδanti hδ1 hband (Nat.zero_le ℓ)).1
  have hdiff : ∀ ℓ ℓ' ω, F ℓ' ω - F ℓ ω = bandApprox ν T δ ℓ' ω - bandApprox ν T δ ℓ ω :=
    fun ℓ ℓ' ω => by
      rw [hFdef]
      ring
  set τ : ℕ → ℝ := fun ℓ => T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν with hτdef
  have hδ1' : ∀ ℓ, δ ℓ ≤ 1 := fun ℓ => (hδanti (Nat.zero_le ℓ)).trans hδ1
  have hint : ∀ ℓ, IntegrableOn (fun z : ℝ => z ^ 2) {z : ℝ | |z| < δ ℓ} ν := fun ℓ =>
    hν.integrableOn.congr_fun (fun z hz => by
      have h1 : |z| < 1 := (show |z| < δ ℓ from hz).trans_le (hδ1' ℓ)
      have h2 : z ^ 2 ≤ 1 := by nlinarith [abs_nonneg z, sq_abs z]
      exact min_eq_right h2) (measurableSet_lt continuous_abs.measurable measurable_const)
  have hle : ∀ ℓ ℓ', ℓ ≤ ℓ' → ∫ ω, (F ℓ' ω - F ℓ ω) ^ 2 ∂P ≤ τ ℓ := by
    intro ℓ ℓ' hℓ
    simp_rw [hdiff]
    rw [(bandApprox_sq_sub hν T hδpos hδanti hδ1 hband hℓ).2]
    refine mul_le_mul_of_nonneg_left (setIntegral_mono_set (hint ℓ)
      (ae_of_all _ fun z => sq_nonneg z) (Eventually.of_forall fun z hz => ?_)) T.2
    exact hz.2
  have hlim : ∀ ℓ, Tendsto (fun ℓ' => ∫ ω, (F ℓ' ω - F ℓ ω) ^ 2 ∂P) atTop (𝓝 (τ ℓ)) := by
    intro ℓ
    refine ((tendsto_setIntegral_levyMid_sq hν hδlim (hδ1' ℓ)).const_mul (T : ℝ)).congr'
      ((eventually_ge_atTop ℓ).mono fun ℓ' hℓ' => ?_)
    simp_rw [hdiff]
    rw [(bandApprox_sq_sub hν T hδpos hδanti hδ1 hband hℓ').2]
  have hτ : Tendsto τ atTop (𝓝 0) := by
    have h := (tendsto_setIntegral_small_sq hν hδanti hδ1 hδlim).const_mul (T : ℝ)
    rwa [mul_zero] at h
  obtain ⟨G, hG, hGτ⟩ := exists_L2_limit_of_tail hF hτ hle hlim
  set X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ := fun ω => G ω + bandApprox ν T δ 0 ω with hX
  have hXF : ∀ ℓ, (fun ω => X ω - bandApprox ν T δ ℓ ω) = fun ω => G ω - F ℓ ω := fun ℓ => by
    funext ω
    rw [hX, hFdef]
    ring
  have hXF' : ∀ ℓ ω, X ω - bandApprox ν T δ ℓ ω = G ω - F ℓ ω := fun ℓ ω => by
    rw [hX, hFdef]
    ring
  have hD : ∀ ℓ, MemLp (fun ω => X ω - bandApprox ν T δ ℓ ω) 2 P := fun ℓ => by
    rw [hXF]
    exact hG.sub (hF ℓ)
  refine ⟨X, ?_, fun ℓ => ⟨(hD ℓ).integrable_sq, ?_⟩, hτ, ?_⟩
  · have e : (fun ω => X ω - bandApprox ν T δ 0 ω) = G := by
      funext ω
      rw [hX]
      ring
    rw [e]
    exact hG
  · simp_rw [hXF']
    exact hGτ ℓ
  · intro Φ K hΦ ℓ
    have hXm : AEStronglyMeasurable X P :=
      hG.1.add (measurable_bandApprox ν T δ 0).aestronglyMeasurable
    have hm : AEStronglyMeasurable (fun ω => Φ (bandApprox ν T δ ℓ ω) - Φ (X ω)) P :=
      (hΦ.continuous.measurable.comp (measurable_bandApprox ν T δ ℓ)).aestronglyMeasurable.sub
        (hΦ.continuous.comp_aestronglyMeasurable hXm)
    have hpt : ∀ ω, |Φ (bandApprox ν T δ ℓ ω) - Φ (X ω)| ≤
        K * |X ω - bandApprox ν T δ ℓ ω| := fun ω => by
      have h1 := hΦ.dist_le_mul (bandApprox ν T δ ℓ ω) (X ω)
      rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (bandApprox ν T δ ℓ ω)] at h1
      exact h1
    have hI1 := ((hD ℓ).integrable one_le_two).abs.const_mul (K : ℝ)
    have hI : Integrable (fun ω => Φ (bandApprox ν T δ ℓ ω) - Φ (X ω)) P :=
      hI1.mono' hm (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hpt ω)
    refine ⟨hI, ?_⟩
    calc |∫ ω, Φ (bandApprox ν T δ ℓ ω) - Φ (X ω) ∂P|
        ≤ ∫ ω, |Φ (bandApprox ν T δ ℓ ω) - Φ (X ω)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, K * |X ω - bandApprox ν T δ ℓ ω| ∂P := integral_mono hI.abs hI1 hpt
      _ = K * ∫ ω, |X ω - bandApprox ν T δ ℓ ω| ∂P := integral_const_mul _ _
      _ ≤ K * Real.sqrt (∫ ω, (X ω - bandApprox ν T δ ℓ ω) ^ 2 ∂P) :=
          mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq (hD ℓ)) K.2
      _ = K * Real.sqrt (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) := by
          simp_rw [hXF']
          rw [hGτ ℓ]

/-! ### Superposition: the bands make up the level-`δ_ℓ` simulation -/

/-- The jumps `|z| ≥ δ_ℓ` are the disjoint union of the bands `0, …, ℓ` (Giles 2015, §6.2,
p. 47, l. 2045–2050): `ν|_{|z| ≥ δ_ℓ} = ∑_{k ≤ ℓ} ν|_{band k}`. -/
lemma restrict_levySet_eq_sum (ν : Measure ℝ) {δ : ℕ → ℝ} (hδanti : Antitone δ) :
    ∀ ℓ, ν.restrict (levySet (δ ℓ)) = ∑ k ∈ range (ℓ + 1), ν.restrict (levyBand δ k)
  | 0 => by rw [Finset.sum_range_one]; rfl
  | ℓ + 1 => by
      have e : levySet (δ (ℓ + 1)) = levySet (δ ℓ) ∪ levyMid (δ (ℓ + 1)) (δ ℓ) := by
        ext z
        rw [Set.mem_union]
        constructor
        · intro hz
          by_cases h : δ ℓ ≤ |z|
          · exact Or.inl h
          · exact Or.inr ⟨hz, not_le.1 h⟩
        · rintro (h | h)
          · exact (hδanti (Nat.le_succ ℓ)).trans h
          · exact h.1
      have hd : Disjoint (levySet (δ ℓ)) (levyMid (δ (ℓ + 1)) (δ ℓ)) :=
        Set.disjoint_left.2 fun z h1 h2 => absurd h1 (not_le.2 h2.2)
      rw [e, Measure.restrict_union hd (measurableSet_levyMid _ _),
        restrict_levySet_eq_sum ν hδanti ℓ, Finset.sum_range_succ (n := ℓ + 1)]
      rfl

/-- The exponent of the compound Poisson sum of one band (Giles 2015, §6.2): with
`Λ • M = T • ν|_B`, `Λ ∫ (e^{it 1_B(x) x} − 1) dM = ∫ (e^{itx} − 1) d(T • ν|_B)`. -/
lemma exponent_band {ν : Measure ℝ} {T r : ℝ≥0} {μ : Measure ℝ} {B : Set ℝ}
    (hB : MeasurableSet B) (h : r • μ = T • ν.restrict B) (t : ℝ) :
    (r : ℂ) * ∫ x, (Complex.exp (t * (B.indicator id x : ℝ) * Complex.I) - 1) ∂μ =
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂(T • ν.restrict B) := by
  rw [nnreal_mul_integral_eq, h]
  simp_rw [cexp_indicator_sub_one B t]
  rw [integral_indicator hB, Measure.restrict_smul, Measure.restrict_restrict hB, Set.inter_self]

/-- **Superposition: the band simulation of level `ℓ` has the law of the level-`δ_ℓ`
approximation** (Giles 2015, §6.2, p. 47, l. 2038–2050: "simulate the large jumps", which "fall
into three categories").  Simulating the bands `0, …, ℓ` independently
(`Λ_k • M_k = T • ν|_{band k}`) and adding their jumps gives the same law of `X^{δ_ℓ}` as
simulating all jumps `|z| ≥ δ_ℓ` at once (`N ∼ P(r)`, `Z_i ∼ μ`, `r • μ = T • ν|_{|z| ≥ δ_ℓ}`). -/
theorem bandApprox_map_eq {ν : Measure ℝ} (T : ℝ≥0) {δ : ℕ → ℝ} (hδanti : Antitone δ)
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) (ℓ : ℕ) {r : ℝ≥0}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : r • μ = T • ν.restrict (levySet (δ ℓ))) :
    (bandInputLaw Λ M).map (bandApprox ν T δ ℓ) = (cpInputLaw r μ).map (levyFine ν T (δ ℓ)) := by
  have hPk : ∀ k, IsProbabilityMeasure (cpInputLaw (Λ k) (M k)) := fun k =>
    isProbabilityMeasure_cpInputLaw _ _
  have := isProbabilityMeasure_bandInputLaw Λ M
  have := isProbabilityMeasure_cpInputLaw r μ
  have hfk : ∀ k, Measurable ((levyBand δ k).indicator (id : ℝ → ℝ)) := fun k =>
    measurable_id.indicator (measurableSet_levyBand δ k)
  have hf := measurable_id.indicator (measurableSet_levySet (δ ℓ))
  set S : (ℕ → ℕ × (ℕ → ℝ)) → ℝ :=
    fun ω => ∑ k ∈ range (ℓ + 1), cpSum ((levyBand δ k).indicator id) (ω k) with hS
  have hSm : Measurable S := Finset.measurable_fun_sum _ fun k _ =>
    (measurable_cpSum (hfk k)).comp (measurable_pi_apply k)
  have e1 : (bandInputLaw Λ M).map (bandApprox ν T δ ℓ) =
      ((bandInputLaw Λ M).map S).map (fun x => x - levyComp ν T (δ ℓ)) := by
    rw [Measure.map_map (measurable_sub_const _) hSm]
    rfl
  have e2 : (cpInputLaw r μ).map (levyFine ν T (δ ℓ)) =
      ((cpInputLaw r μ).map (cpSum ((levySet (δ ℓ)).indicator id))).map
        (fun x => x - levyComp ν T (δ ℓ)) := by
    rw [Measure.map_map (measurable_sub_const _) (measurable_cpSum hf)]
    rfl
  rw [e1, e2]
  congr 1
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_cpSum r μ hf, exponent_levySet le_rfl h t, charFun_apply_real,
    integral_map hSm.aemeasurable (by fun_prop)]
  -- the characteristic function of the sum of independent bands
  have hprod : ∀ ω : ℕ → ℕ × (ℕ → ℝ), Complex.exp (t * (S ω : ℂ) * Complex.I) =
      ∏ k ∈ range (ℓ + 1),
        Complex.exp (t * (cpSum ((levyBand δ k).indicator id) (ω k) : ℂ) * Complex.I) := by
    intro ω
    rw [← Complex.exp_sum, hS]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [hprod]
  have hB : bandInputLaw Λ M = Measure.infinitePi fun k => cpInputLaw (Λ k) (M k) := rfl
  rw [hB, integral_prod_infinitePi (fun k => cpInputLaw (Λ k) (M k)) (range (ℓ + 1))
    (F := fun k x => Complex.exp (t * (cpSum ((levyBand δ k).indicator id) x : ℂ) * Complex.I))
    (fun k => by have := measurable_cpSum (hfk k); fun_prop)]
  have hk : ∀ k, ∫ x, Complex.exp (t * (cpSum ((levyBand δ k).indicator id) x : ℂ) *
      Complex.I) ∂(cpInputLaw (Λ k) (M k)) =
      Complex.exp (∫ x, (Complex.exp (t * x * Complex.I) - 1)
        ∂(T • ν.restrict (levyBand δ k))) := fun k => by
    have h1 := charFun_cpSum (Λ k) (M k) (hfk k) t
    rw [charFun_apply_real, integral_map (measurable_cpSum (hfk k)).aemeasurable
      (by fun_prop), exponent_band (measurableSet_levyBand δ k) (hband k) t] at h1
    exact h1
  have hint : ∀ k ∈ range (ℓ + 1), Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I) - 1)
      (T • ν.restrict (levyBand δ k)) := fun k _ => by
    rw [← hband k]
    exact integrable_cexp_sub_one _ measurable_id t
  simp_rw [hk]
  rw [← Complex.exp_sum, ← integral_finsetSum_measure hint, ← Finset.smul_sum,
    ← restrict_levySet_eq_sum ν hδanti ℓ]

/-- **The expected number of simulated jumps** (Giles 2015, §6.2, p. 47, l. 2038–2039: "it is
impossible to simulate each jump.  One approach is to simulate the large jumps"; this is the cost
of a level-`ℓ` sample): the bands `0, …, ℓ` contain
`E[∑_{k ≤ ℓ} N_k] = T ν(|z| ≥ δ_ℓ)` jumps on average. -/
theorem integral_band_count {ν : Measure ℝ} (T : ℝ≥0) {δ : ℕ → ℝ} (hδanti : Antitone δ)
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) (ℓ : ℕ) :
    ∫ ω, ∑ k ∈ range (ℓ + 1), ((ω k).1 : ℝ) ∂(bandInputLaw Λ M) =
      T * (ν (levySet (δ ℓ))).toReal := by
  have hPk : ∀ k, IsProbabilityMeasure (cpInputLaw (Λ k) (M k)) := fun k =>
    isProbabilityMeasure_cpInputLaw _ _
  have hB : bandInputLaw Λ M = Measure.infinitePi fun k => cpInputLaw (Λ k) (M k) := rfl
  have hev : ∀ k, MeasurePreserving (fun ω : ℕ → ℕ × (ℕ → ℝ) => ω k) (bandInputLaw Λ M)
      (cpInputLaw (Λ k) (M k)) := fun k => by
    rw [hB]
    exact measurePreserving_eval_infinitePi (fun k => cpInputLaw (Λ k) (M k)) k
  have hfst : Measurable fun x : ℕ × (ℕ → ℝ) => (x.1 : ℝ) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp measurable_fst
  have hint1 : ∀ k, Integrable (fun x : ℕ × (ℕ → ℝ) => (x.1 : ℝ)) (cpInputLaw (Λ k) (M k)) :=
    fun k => (integrable_poissonMeasure_id_sq (Λ k)).1.comp_fst _
  have hint : ∀ k, Integrable (fun ω : ℕ → ℕ × (ℕ → ℝ) => ((ω k).1 : ℝ)) (bandInputLaw Λ M) :=
    fun k => ((hev k).integrable_comp hfst.aestronglyMeasurable).2 (hint1 k)
  have hmean : ∀ k, ∫ ω, ((ω k).1 : ℝ) ∂(bandInputLaw Λ M) = Λ k := fun k => by
    rw [integral_comp_of_measurePreserving (hev k) (f := fun x : ℕ × (ℕ → ℝ) => (x.1 : ℝ))
      hfst.aestronglyMeasurable, cpInputLaw, integral_fun_fst, probReal_univ, one_smul,
      integral_poissonMeasure_id]
  rw [integral_finsetSum _ fun k _ => hint k]
  simp_rw [hmean]
  have hΛ : ∀ k, (Λ k : ℝ≥0∞) = T * ν (levyBand δ k) := fun k => by
    have h := congrArg (fun m : Measure ℝ => m Set.univ) (hband k)
    simp only [Measure.coe_nnreal_smul_apply, measure_univ, mul_one,
      Measure.restrict_apply_univ] at h
    exact h
  have hsum : ν (levySet (δ ℓ)) = ∑ k ∈ range (ℓ + 1), ν (levyBand δ k) := by
    have h := congrArg (fun m : Measure ℝ => m Set.univ) (restrict_levySet_eq_sum ν hδanti ℓ)
    simp only [Measure.restrict_apply_univ, Measure.finsetSum_apply] at h
    exact h
  have e : ∑ k ∈ range (ℓ + 1), (Λ k : ℝ) =
      (∑ k ∈ range (ℓ + 1), (Λ k : ℝ≥0∞)).toReal := by
    rw [ENNReal.toReal_sum fun k _ => ENNReal.coe_ne_top]
    rfl
  rw [e]
  simp_rw [hΛ]
  rw [← Finset.mul_sum, ← hsum, ENNReal.toReal_mul, ENNReal.coe_toReal]

/-- **The expected cost of the multilevel estimator** (Giles 2015, §2.1, Theorem 1, p. 6–7,
l. 273–274 and l. 295: "independent estimators `Y_ℓ` based on `N_ℓ` Monte Carlo samples, each with
expected cost `C_ℓ`", "`E[C] ≤ …`"; l. 302–304: "expected costs to allow for applications in which
the simulation cost of individual samples is itself random"; with §6.2, p. 47, l. 2038–2039: "it is
impossible to simulate each jump.  One approach is to simulate the large jumps").  Sample `n` of
level `ℓ` uses its own input `x(ℓ, n)` of all bands, with i.i.d. inputs `x(ℓ, n) ∼ bandInputLaw Λ M`
(`Λ_k • M_k = T • ν|_{band k}`, `δ` antitone), and costs one plus the number of jumps it simulates,
`1 + ∑_{k ≤ ℓ} N_k^{(ℓ,n)}` (the bands `0, …, ℓ`, i.e. all jumps `|z| ≥ δ_ℓ`; the coarse path
reuses the bands `0, …, ℓ − 1`).  For every `L` and `N_0, …, N_L`, the random total cost
`∑_{ℓ ≤ L} ∑_{n < N_ℓ} (1 + ∑_{k ≤ ℓ} N_k^{(ℓ,n)})` is integrable and its expectation is
`∑_{ℓ ≤ L} N_ℓ (1 + T ν(|z| ≥ δ_ℓ))`. -/
theorem levy_expected_cost {ν : Measure ℝ} (T : ℝ≥0) {δ : ℕ → ℝ} (hδanti : Antitone δ)
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) (L : ℕ) (N : ℕ → ℕ) :
    Integrable (fun x : ℕ × ℕ → ℕ → ℕ × (ℕ → ℝ) => ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ),
        (1 + ∑ k ∈ range (ℓ + 1), ((x (ℓ, n) k).1 : ℝ)))
      (Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) ∧
    ∫ x, ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ), (1 + ∑ k ∈ range (ℓ + 1), ((x (ℓ, n) k).1 : ℝ))
        ∂(Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) =
      ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * (ν (levySet (δ ℓ))).toReal) := by
  have := isProbabilityMeasure_bandInputLaw Λ M
  obtain ⟨-, -, hω⟩ := exists_iid_inputs (bandInputLaw Λ M)
  have hPk : ∀ k, IsProbabilityMeasure (cpInputLaw (Λ k) (M k)) := fun k =>
    isProbabilityMeasure_cpInputLaw _ _
  have hfst : ∀ ℓ, Measurable fun ω : ℕ → ℕ × (ℕ → ℝ) =>
      (1 + ∑ k ∈ range (ℓ + 1), ((ω k).1 : ℝ)) := fun ℓ =>
    measurable_const.add (Finset.measurable_fun_sum _ fun k _ =>
      (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp
        (measurable_fst.comp (measurable_pi_apply k)))
  have hint1 : ∀ ℓ, Integrable (fun ω : ℕ → ℕ × (ℕ → ℝ) =>
      (1 + ∑ k ∈ range (ℓ + 1), ((ω k).1 : ℝ))) (bandInputLaw Λ M) := fun ℓ => by
    refine (integrable_const 1).add (integrable_finsetSum _ fun k _ => ?_)
    have hev : MeasurePreserving (fun ω : ℕ → ℕ × (ℕ → ℝ) => ω k) (bandInputLaw Λ M)
        (cpInputLaw (Λ k) (M k)) :=
      measurePreserving_eval_infinitePi (fun k => cpInputLaw (Λ k) (M k)) k
    exact (hev.integrable_comp ((Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp
      measurable_fst).aestronglyMeasurable).2
      ((integrable_poissonMeasure_id_sq (Λ k)).1.comp_fst _)
  have hmean : ∀ ℓ, ∫ ω, (1 + ∑ k ∈ range (ℓ + 1), ((ω k).1 : ℝ)) ∂(bandInputLaw Λ M) =
      1 + T * (ν (levySet (δ ℓ))).toReal := fun ℓ => by
    rw [integral_add (integrable_const 1) ((hint1 ℓ).sub (integrable_const 1) |>.congr
      (ae_of_all _ fun ω => by simp)), integral_const, probReal_univ, one_smul,
      integral_band_count T hδanti hband ℓ]
  have hI : ∀ ℓ n, Integrable (fun x : ℕ × ℕ → ℕ → ℕ × (ℕ → ℝ) =>
      1 + ∑ k ∈ range (ℓ + 1), ((x (ℓ, n) k).1 : ℝ))
      (Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) := fun ℓ n =>
    ((hω (ℓ, n)).integrable_comp (hfst ℓ).aestronglyMeasurable).2 (hint1 ℓ)
  refine ⟨integrable_finsetSum _ fun ℓ _ => integrable_finsetSum _ fun n _ => hI ℓ n, ?_⟩
  rw [integral_finsetSum _ fun ℓ _ => integrable_finsetSum _ fun n _ => hI ℓ n]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [integral_finsetSum _ fun n _ => hI ℓ n]
  have hn : ∀ n, ∫ x : ℕ × ℕ → ℕ → ℕ × (ℕ → ℝ), 1 + ∑ k ∈ range (ℓ + 1), ((x (ℓ, n) k).1 : ℝ)
      ∂(Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) =
      1 + T * (ν (levySet (δ ℓ))).toReal := fun n => by
    rw [← hmean ℓ]
    exact integral_comp_of_measurePreserving (hω (ℓ, n)) (hfst ℓ).aestronglyMeasurable
      (f := fun ω : ℕ → ℕ × (ℕ → ℝ) => 1 + ∑ k ∈ range (ℓ + 1), ((ω k).1 : ℝ))
  rw [Finset.sum_congr rfl fun n _ => hn n, Finset.sum_const, card_range, nsmul_eq_mul]

/-! ### Theorem 1 end to end -/

/-- `z²` is integrable on `{|z| < c}`, `c ≤ 1`, for a Lévy measure (Giles 2015, §6.2). -/
lemma integrableOn_sq_small {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    {c : ℝ} (hc : c ≤ 1) : IntegrableOn (fun z : ℝ => z ^ 2) {z : ℝ | |z| < c} ν :=
  hν.integrableOn.congr_fun (fun z hz => by
    have h1 : |z| < 1 := (show |z| < c from hz).trans_le hc
    have h2 : z ^ 2 ≤ 1 := by nlinarith [abs_nonneg z, sq_abs z]
    exact min_eq_right h2) (measurableSet_lt continuous_abs.measurable measurable_const)

/-- The jumps of a set `B` with `∫_B z² dν < ∞` give a square-integrable compound Poisson sum
(Giles 2015, §6.2): if `r • μ = T • ν|_B`, then `∑_{i<N} 1_B(Z_i) Z_i ∈ L²`. -/
lemma memLp_cpSum_indicator {ν : Measure ℝ} {T r : ℝ≥0} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {B : Set ℝ} (hB : MeasurableSet B) (h : r • μ = T • ν.restrict B)
    (hB2 : IntegrableOn (fun z => z ^ 2) B ν) :
    MemLp (cpSum (B.indicator id)) 2 (cpInputLaw r μ) := by
  have hgm : Measurable (B.indicator (id : ℝ → ℝ)) := measurable_id.indicator hB
  by_cases hr : r = 0
  · subst hr
    have e : cpInputLaw 0 μ = (Measure.infinitePi fun _ : ℕ => μ).map (Prod.mk 0) := by
      rw [cpInputLaw, poissonMeasure_zero, Measure.dirac_prod]
    rw [e, memLp_map_measure_iff (measurable_cpSum hgm).aestronglyMeasurable
      measurable_prodMk_left.aemeasurable]
    have e2 : (cpSum (B.indicator id) ∘ Prod.mk 0) = fun _ : ℕ → ℝ => (0 : ℝ) := by
      funext z
      unfold cpSum
      simp
    rw [e2]
    exact memLp_const 0
  · have hg2 : MemLp (B.indicator (id : ℝ → ℝ)) 2 μ := by
      refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 ?_
      have h1 : Integrable (fun z => B.indicator id z ^ 2) (ν.restrict B) :=
        hB2.congr_fun (fun z hz => by rw [Set.indicator_of_mem hz, id]) hB
      have h2 := h1.smul_measure_nnreal (c := T)
      rw [← h, ← Measure.coe_nnreal_smul] at h2
      exact (integrable_smul_measure (by simpa using hr) ENNReal.coe_ne_top).1 h2
    exact (cpSum_moments r μ hgm hg2).1

/-- A Lipschitz function of a square-integrable variable is square integrable (Giles 2015, §6.2,
the Lipschitz payoffs). -/
lemma memLp_comp_lipschitz {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Φ : ℝ → ℝ} {K : ℝ≥0} (hΦ : LipschitzWith K Φ) {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    MemLp (fun ω => Φ (Y ω)) 2 P := by
  refine ((memLp_const |Φ 0|).add (hY.norm.const_mul (K : ℝ))).of_le
    (hΦ.continuous.comp_aestronglyMeasurable hY.1) (ae_of_all _ fun ω => ?_)
  have h1 := hΦ.dist_le_mul (Y ω) 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at h1
  have h2 : |Φ (Y ω)| ≤ |Φ 0| + K * ‖Y ω‖ := by
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (Φ (Y ω)) (Φ 0)
    linarith
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |Φ 0| + K * |Y ω|)]
  rwa [Real.norm_eq_abs] at h2

/-- `√(a 2^{−(2−Y)ℓ}) = √a 2^{−((2−Y)/2) ℓ}` (Giles 2015, §6.2, the rate `α = β/2`). -/
lemma sqrt_mul_two_rpow {a : ℝ} (ha : 0 ≤ a) (β x : ℝ) :
    Real.sqrt (a * (2 : ℝ) ^ (-(β * x))) = Real.sqrt a * (2 : ℝ) ^ (-(β / 2 * x)) := by
  rw [Real.sqrt_mul ha, Real.sqrt_eq_rpow ((2 : ℝ) ^ (-(β * x))),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2
  ring

/-- **Theorem 1 for the truncated Lévy levels** (Giles 2015, §6.2, p. 47, l. 2038–2051: "the
cutoff `δ_ℓ` for the jumps which are simulated varies with level, and `δ_ℓ → 0` as `ℓ → ∞` to
ensure that the bias converges to zero", with §2.1, Theorem 1).  A pure-jump Lévy process with
Lévy measure `ν` (`∫ min(1, z²) dν < ∞`) whose large jumps have a finite second moment
(`∫_{|z| ≥ 1} z² dν < ∞`), observed at `T`; the cutoffs are
`δ_ℓ = 2^{−ℓ}`, all levels are built from independent compound Poisson simulations of the bands
of jump sizes (`Λ_k • M_k = T • ν|_{band k}`; the level-`ℓ` correction uses the jumps `≥ δ_{ℓ−1}`
on both paths and those in `[δ_ℓ, δ_{ℓ−1})` on the fine path only), and `Φ` is a `K`-Lipschitz
payoff.  Assume the Blumenthal–Getoor-type rates, for some `0 < Y < 2`,
`T ∫_{|z| < δ_ℓ} z² dν ≤ a δ_ℓ^{2−Y}` and `T ν(|z| ≥ δ_ℓ) ≤ b δ_ℓ^{−Y}`.  Sample `n` of level `ℓ`
has its own input `x(ℓ, n)` and costs one plus the number `∑_{k ≤ ℓ} N_k^{(ℓ,n)}` of jumps it
simulates, a random cost with expectation `1 + T ν(|z| ≥ δ_ℓ)`.  Then the levels converge to a
limit `X` (`E[(X − X^{δ_ℓ})²] = T ∫_{|z| < δ_ℓ} z² dν`), and the multilevel estimator of `E[Φ(X)]`
satisfies Theorem 1 with `α = (2 − Y)/2`, `β = 2 − Y` (the variance bound of the intermediate
range) and `γ = Y`: for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with square-integrable
error, mean square error `< ε²` and an integrable random total cost whose expectation
`∑_ℓ N_ℓ (1 + T ν(|z| ≥ δ_ℓ))` is `≤ c₄ · complexityBound α β γ ε`, which is `ε⁻²` for `Y < 1`,
`ε⁻² (log ε)²` for `Y = 1` and `ε^{−2−(γ−β)/α} = ε^{−2−4(Y−1)/(2−Y)} = ε^{−2Y/(2−Y)}` for `Y > 1`
(e.g. `ε^{−6}` at `Y = 3/2`). -/
theorem levy_truncation_theorem1 {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (hlarge : IntegrableOn (fun z => z ^ 2) (levySet 1) ν) (T : ℝ≥0) {Y a b : ℝ}
    (hY0 : 0 < Y) (hY2 : Y < 2)
    (hsmall : ∀ ℓ : ℕ, (T : ℝ) * ∫ z in {z : ℝ | |z| < (2 : ℝ)⁻¹ ^ ℓ}, z ^ 2 ∂ν ≤
      a * (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))))
    (hcount : ∀ ℓ : ℕ, (T : ℝ) * (ν (levySet ((2 : ℝ)⁻¹ ^ ℓ))).toReal ≤
      b * (2 : ℝ) ^ (Y * (ℓ : ℝ)))
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) k))
    {Φ : ℝ → ℝ} {K : ℝ≥0} (hΦ : LipschitzWith K Φ) :
    ∃ X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ,
      (∀ ℓ, Integrable (fun ω => (X ω - bandApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω) ^ 2)
          (bandInputLaw Λ M) ∧
        ∫ ω, (X ω - bandApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω) ^ 2 ∂(bandInputLaw Λ M) =
          T * ∫ z in {z : ℝ | |z| < (2 : ℝ)⁻¹ ^ ℓ}, z ^ 2 ∂ν) ∧
      Integrable (fun ω => Φ (X ω)) (bandInputLaw Λ M) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ ω => Φ (bandApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω))
              (fun ℓ ω => Φ (bandApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω)))
              (fun p x => x p) ℓ (N ℓ) x - ∫ ω, Φ (X ω) ∂(bandInputLaw Λ M)) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ ω => Φ (bandApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω))
              (fun ℓ ω => Φ (bandApprox ν T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω)))
              (fun p x => x p) ℓ (N ℓ) x - ∫ ω, Φ (X ω) ∂(bandInputLaw Λ M)) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) < ε ^ 2 ∧
          Integrable (fun x : ℕ × ℕ → ℕ → ℕ × (ℕ → ℝ) => ∑ ℓ ∈ range (L + 1),
              ∑ n ∈ range (N ℓ), (1 + ∑ k ∈ range (ℓ + 1), ((x (ℓ, n) k).1 : ℝ)))
            (Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) ∧
          ∫ x, ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ),
              (1 + ∑ k ∈ range (ℓ + 1), ((x (ℓ, n) k).1 : ℝ))
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) =
            ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * (ν (levySet ((2 : ℝ)⁻¹ ^ ℓ))).toReal) ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * (ν (levySet ((2 : ℝ)⁻¹ ^ ℓ))).toReal) ≤
            c₄ * complexityBound ((2 - Y) / 2) (2 - Y) Y ε := by
  set δ : ℕ → ℝ := fun ℓ => (2 : ℝ)⁻¹ ^ ℓ with hδdef
  have hδpos : ∀ k, 0 < δ k := fun k => by positivity
  have hδanti : Antitone δ := fun m n hmn =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hδ1 : δ 0 ≤ 1 := le_of_eq (pow_zero _)
  have hδ1' : ∀ ℓ, δ ℓ ≤ 1 := fun ℓ => (hδanti (Nat.zero_le ℓ)).trans hδ1
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨X, hX0, hXℓ, -, hbias⟩ := levy_truncation_limit hν T hδpos hδanti hδ1 hδlim hband
  have := isProbabilityMeasure_bandInputLaw Λ M
  set P := bandInputLaw Λ M with hP
  -- the level approximations are square integrable
  have hPk : ∀ k, IsProbabilityMeasure (cpInputLaw (Λ k) (M k)) := fun k =>
    isProbabilityMeasure_cpInputLaw _ _
  have hA0 : MemLp (bandApprox ν T δ 0) 2 P := by
    have hev0 : MeasurePreserving (fun ω : ℕ → ℕ × (ℕ → ℝ) => ω 0) P
        (cpInputLaw (Λ 0) (M 0)) :=
      measurePreserving_eval_infinitePi (fun k => cpInputLaw (Λ k) (M k)) 0
    have hB : levyBand δ 0 = levySet 1 := by
      change levySet ((2 : ℝ)⁻¹ ^ 0) = levySet 1
      rw [pow_zero]
    have h1 := memLp_cpSum_indicator (measurableSet_levyBand δ 0) (hband 0)
      (by rw [hB]; exact hlarge)
    have h2 := (h1.comp_measurePreserving hev0).sub (memLp_const (levyComp ν T (δ 0)))
    have e : bandApprox ν T δ 0 =
        fun ω => cpSum ((levyBand δ 0).indicator id) (ω 0) - levyComp ν T (δ 0) := by
      funext ω
      rw [bandApprox, Finset.sum_range_one]
    rw [e]
    exact h2
  have hA : ∀ ℓ, MemLp (bandApprox ν T δ ℓ) 2 P := fun ℓ => by
    have h := (bandApprox_sq_sub hν T hδpos hδanti hδ1 hband (Nat.zero_le ℓ)).1.add hA0
    have e : bandApprox ν T δ ℓ =
        (fun ω => bandApprox ν T δ ℓ ω - bandApprox ν T δ 0 ω) + bandApprox ν T δ 0 := by
      funext ω
      simp
    rw [e]
    exact h
  have hXL2 : MemLp X 2 P := by
    have h := hX0.add hA0
    have e : X = (fun ω => X ω - bandApprox ν T δ 0 ω) + bandApprox ν T δ 0 := by
      funext ω
      simp
    rw [e]
    exact h
  have hPf : ∀ ℓ, MemLp (fun ω => Φ (bandApprox ν T δ ℓ ω)) 2 P := fun ℓ =>
    memLp_comp_lipschitz hΦ (hA ℓ)
  have hPfm : ∀ ℓ, Measurable (fun ω => Φ (bandApprox ν T δ ℓ ω)) := fun ℓ =>
    hΦ.continuous.measurable.comp (measurable_bandApprox ν T δ ℓ)
  have hPX : Integrable (fun ω => Φ (X ω)) P :=
    (memLp_comp_lipschitz hΦ hXL2).integrable one_le_two
  refine ⟨X, hXℓ, hPX, ?_⟩
  -- the constants
  have ha : 0 ≤ a := by
    have h0 := hsmall 0
    have hnn : 0 ≤ (T : ℝ) * ∫ z in {z : ℝ | |z| < (2 : ℝ)⁻¹ ^ 0}, z ^ 2 ∂ν :=
      mul_nonneg T.2 (setIntegral_nonneg (measurableSet_lt continuous_abs.measurable
        measurable_const) fun z _ => sq_nonneg z)
    rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one] at h0
    linarith
  -- (i): `α = (2 − Y)/2`
  have hc₁ : 0 < K * Real.sqrt a + 1 := by positivity
  have h_i : ∀ ℓ : ℕ, |∫ ω, Φ (bandApprox ν T δ ℓ ω) - Φ (X ω) ∂P| ≤
      (K * Real.sqrt a + 1) * (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ))) := by
    intro ℓ
    have h1 := (hbias Φ K hΦ ℓ).2
    have h2 : Real.sqrt (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) ≤
        Real.sqrt a * (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ))) := by
      rw [← sqrt_mul_two_rpow ha]
      exact Real.sqrt_le_sqrt (hsmall ℓ)
    have h3 : 0 ≤ (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ))) := by positivity
    calc _ ≤ K * Real.sqrt (T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) := h1
      _ ≤ K * (Real.sqrt a * (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_left h2 K.2
      _ ≤ (K * Real.sqrt a + 1) * (2 : ℝ) ^ (-((2 - Y) / 2 * (ℓ : ℝ))) := by nlinarith
  -- (iii): `β = 2 − Y`
  set V₀ := variance (fun ω => Φ (bandApprox ν T δ 0 ω)) P with hV₀
  have hV₀0 : 0 ≤ V₀ := variance_nonneg _ _
  have hc₂ : 0 < V₀ + (K : ℝ) ^ 2 * a * (2 : ℝ) ^ (2 - Y) + 1 := by positivity
  have h_iii : ∀ ℓ, variance (fineCoarseDiff (fun ℓ ω => Φ (bandApprox ν T δ ℓ ω))
      (fun ℓ ω => Φ (bandApprox ν T δ ℓ ω)) ℓ) P ≤
      (V₀ + (K : ℝ) ^ 2 * a * (2 : ℝ) ^ (2 - Y) + 1) * (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) := by
    intro ℓ
    cases ℓ with
    | zero =>
      rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one]
      change V₀ ≤ _
      have : 0 ≤ (K : ℝ) ^ 2 * a * (2 : ℝ) ^ (2 - Y) := by positivity
      linarith
    | succ ℓ =>
      have hm := (measurable_fineCoarseDiff hPfm hPfm (ℓ + 1)).aestronglyMeasurable (μ := P)
      refine (variance_le_expectation_sq hm).trans ?_
      have hD := bandApprox_sq_sub hν T hδpos hδanti hδ1 hband (Nat.le_succ ℓ)
      have h1 : ∫ ω, (fineCoarseDiff (fun ℓ ω => Φ (bandApprox ν T δ ℓ ω))
          (fun ℓ ω => Φ (bandApprox ν T δ ℓ ω)) (ℓ + 1) ^ 2) ω ∂P ≤
          (K : ℝ) ^ 2 * ∫ ω, (bandApprox ν T δ (ℓ + 1) ω - bandApprox ν T δ ℓ ω) ^ 2 ∂P := by
        rw [← integral_const_mul]
        refine integral_mono ((hPf (ℓ + 1)).sub (hPf ℓ)).integrable_sq
          (hD.1.integrable_sq.const_mul _) fun ω => ?_
        exact sq_sub_le_of_lipschitz hΦ _ _
      have h2 : (T : ℝ) * ∫ z in levyMid (δ (ℓ + 1)) (δ ℓ), z ^ 2 ∂ν ≤
          a * (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) := by
        refine le_trans (mul_le_mul_of_nonneg_left (setIntegral_mono_set
          (integrableOn_sq_small hν (hδ1' ℓ)) (ae_of_all _ fun z => sq_nonneg z)
          (Eventually.of_forall fun z hz => hz.2)) T.2) (hsmall ℓ)
      rw [hD.2] at h1
      have e : (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) =
          (2 : ℝ) ^ (2 - Y) * (2 : ℝ) ^ (-((2 - Y) * ((ℓ + 1 : ℕ) : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        push_cast
        ring
      rw [e] at h2
      have hK2 : 0 ≤ (K : ℝ) ^ 2 := by positivity
      have h4 : 0 ≤ (2 : ℝ) ^ (-((2 - Y) * ((ℓ + 1 : ℕ) : ℝ))) := by positivity
      calc _ ≤ (K : ℝ) ^ 2 * ((T : ℝ) * ∫ z in levyMid (δ (ℓ + 1)) (δ ℓ), z ^ 2 ∂ν) := h1
        _ ≤ (K : ℝ) ^ 2 * (a * ((2 : ℝ) ^ (2 - Y) *
            (2 : ℝ) ^ (-((2 - Y) * ((ℓ + 1 : ℕ) : ℝ))))) := mul_le_mul_of_nonneg_left h2 hK2
        _ ≤ _ := by nlinarith
  -- (iv): `γ = Y`, cost = expected number of simulated jumps plus one
  have hc₃ : 0 < 1 + |b| := by positivity
  have h_iv : ∀ ℓ : ℕ, 1 + (T : ℝ) * (ν (levySet (δ ℓ))).toReal ≤
      (1 + |b|) * (2 : ℝ) ^ (Y * (ℓ : ℝ)) := by
    intro ℓ
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Y * (ℓ : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have h2 : (T : ℝ) * (ν (levySet (δ ℓ))).toReal ≤ b * (2 : ℝ) ^ (Y * (ℓ : ℝ)) := hcount ℓ
    have h3 : b * (2 : ℝ) ^ (Y * (ℓ : ℝ)) ≤ |b| * (2 : ℝ) ^ (Y * (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_abs_self b) (by positivity)
    nlinarith
  have hαβγ : min (2 - Y) Y / 2 ≤ (2 - Y) / 2 := by
    have := min_le_left (2 - Y) Y
    linarith
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs P
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => P)
    (fun ω => Φ (X ω)) (fun ℓ ω => Φ (bandApprox ν T δ ℓ ω))
    (fun ℓ ω => Φ (bandApprox ν T δ ℓ ω)) (fun p x => x p)
    (fun ℓ _ _ => 1 + (T : ℝ) * (ν (levySet (δ ℓ))).toReal)
    (fun ℓ => 1 + (T : ℝ) * (ν (levySet (δ ℓ))).toReal)
    (α := (2 - Y) / 2) (β := 2 - Y) (γ := Y) (by linarith) (by linarith) hY0 hc₁ hc₂ hc₃ hαβγ
    hω hind hPX hPfm hPfm hPf hPf (fun _ => rfl) (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul])
    (fun ℓ => by
      rw [integral_sub ((hPf ℓ).integrable one_le_two) hPX]
      rw [← integral_sub ((hPf ℓ).integrable one_le_two) hPX]
      exact h_i ℓ) h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  obtain ⟨hcI, hcE⟩ := levy_expected_cost T hδanti hband L N
  refine ⟨L, N, hN, ?_, hmse, hcI, hcE, ?_⟩
  · exact ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω (memLp_fineCoarseDiff hPf hPf) ℓ
      (N ℓ)).sub (memLp_const _)).integrable_sq
  · unfold totalCost at hcost
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul] at hcost
    exact hcost

/-! ### The band laws exist -/

/-- A finite measure on `S` is an intensity times a probability law (Giles 2015, §6.2): if
`ν(S) < ∞` there are `r ≥ 0` and a probability measure `μ` with `r • μ = T • ν|_S`
(`r = Tν(S)`, `μ = ν(· | S)`, or `μ = δ_0` when `ν(S) = 0`). -/
lemma exists_smul_eq_restrict {ν : Measure ℝ} (T : ℝ≥0) {S : Set ℝ} (hS : ν S ≠ ∞) :
    ∃ (r : ℝ≥0) (μ : Measure ℝ), IsProbabilityMeasure μ ∧ r • μ = T • ν.restrict S := by
  by_cases h0 : ν S = 0
  · refine ⟨0, Measure.dirac 0, inferInstance, ?_⟩
    rw [zero_smul, Measure.restrict_eq_zero.2 h0, smul_zero]
  · refine ⟨T * (ν S).toNNReal, (ν S)⁻¹ • ν.restrict S, ⟨?_⟩, ?_⟩
    · rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
        ENNReal.inv_mul_cancel h0 hS]
    · rw [← Measure.coe_nnreal_smul, ← Measure.coe_nnreal_smul, smul_smul]
      congr 1
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hS, mul_assoc, ENNReal.mul_inv_cancel h0 hS,
        mul_one]

/-- **The band laws exist** (Giles 2015, §6.2, p. 47, l. 2039: "simulate the large jumps"): for a
Lévy measure `ν`, `T ≥ 0` and positive cutoffs, every band has an intensity `Λ_k = Tν(band k)` and
a jump law `M_k` with `Λ_k • M_k = T • ν|_{band k}`, so the hypotheses of
`levy_truncation_limit` and `levy_truncation_theorem1` are satisfiable. -/
theorem exists_levy_bandLaws {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) :
    ∃ (Λ : ℕ → ℝ≥0) (M : ℕ → Measure ℝ), (∀ k, IsProbabilityMeasure (M k)) ∧
      ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k) := by
  have hfin : ∀ k, ν (levyBand δ k) ≠ ∞ := fun k => by
    have hsub : levyBand δ k ⊆ levySet (δ k) := by
      cases k with
      | zero => exact subset_rfl
      | succ k => exact fun z hz => hz.1
    exact ((measure_mono hsub).trans_lt (levy_measure_levySet_lt_top hν (hδpos k))).ne
  choose Λ M hM hΛ using fun k => exists_smul_eq_restrict (ν := ν) T (hfin k)
  exact ⟨Λ, M, hM, hΛ⟩

/-! ### A concrete example: a one-sided stable-like Lévy measure -/

/-- The density `c z^{−1−Y}` of the example (Giles 2015, §6.2, p. 47, l. 2038: an infinite
activity Lévy process; the jump intensity of an `Y`-stable-like process), as an `ℝ≥0`-valued
function. -/
noncomputable def stableLikeDensity (c Y : ℝ) (z : ℝ) : ℝ≥0 := (c * z ^ (-1 - Y)).toNNReal

/-- **The one-sided stable-like Lévy measure** `ν(dz) = c z^{−1−Y} dz` on `0 < z ≤ 1` (Giles 2015,
§6.2, p. 47, l. 2038: "infinite activity Lévy processes"); for `c > 0`, `0 < Y < 2` it has infinite
total mass (`ν(z ≥ δ) = c (δ^{−Y} − 1)/Y → ∞` as `δ → 0`) and `∫ z² dν < ∞`. -/
noncomputable def stableLikeLevy (c Y : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity fun z => (stableLikeDensity c Y z : ℝ≥0∞)

/-- The density is measurable (Giles 2015, §6.2). -/
lemma measurable_stableLikeDensity (c Y : ℝ) : Measurable (stableLikeDensity c Y) :=
  (measurable_const.mul (measurable_id.pow_const _)).real_toNNReal

/-- Set integrals against the example measure (Giles 2015, §6.2):
`∫_S f dν = ∫_{S ∩ (0,1]} c z^{−1−Y} f(z) dz`. -/
lemma setIntegral_stableLikeLevy (c Y : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (f : ℝ → ℝ) :
    ∫ z in S, f z ∂(stableLikeLevy c Y) =
      ∫ z in S ∩ Set.Ioc 0 1, (stableLikeDensity c Y z : ℝ) * f z := by
  rw [stableLikeLevy, restrict_withDensity hS,
    integral_withDensity_eq_integral_smul (measurable_stableLikeDensity c Y),
    Measure.restrict_restrict hS]
  rfl

/-- The density on `(0, ∞)`: `c z^{−1−Y} · z^p = c z^{p−1−Y}` (Giles 2015, §6.2). -/
lemma stableLikeDensity_mul_rpow {c Y : ℝ} (hc : 0 < c) {z : ℝ} (hz : 0 < z) (p : ℝ) :
    (stableLikeDensity c Y z : ℝ) * z ^ p = c * z ^ (p - 1 - Y) := by
  rw [stableLikeDensity, Real.coe_toNNReal _ (by positivity), mul_assoc,
    ← Real.rpow_add hz]
  congr 2
  ring

/-- The example has a finite second moment, `∫ z² dν < ∞` (Giles 2015, §6.2). -/
lemma integrable_sq_stableLikeLevy {c Y : ℝ} (hc : 0 < c) (hY2 : Y < 2) :
    Integrable (fun z : ℝ => z ^ 2) (stableLikeLevy c Y) := by
  rw [stableLikeLevy, integrable_withDensity_iff_integrable_smul
    (measurable_stableLikeDensity c Y)]
  have h1 : IntegrableOn (fun z : ℝ => c * z ^ (1 - Y)) (Set.Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 1 - Y)).const_mul c)
  refine h1.congr_fun (fun z hz => ?_) measurableSet_Ioc
  have e := stableLikeDensity_mul_rpow (Y := Y) hc hz.1 2
  rw [Real.rpow_two] at e
  rw [NNReal.smul_def, smul_eq_mul, e, show (2 : ℝ) - 1 - Y = 1 - Y by ring]

/-- `(2^{−ℓ})^x = 2^{−xℓ}` (Giles 2015, §6.2, the cutoffs `δ_ℓ = 2^{−ℓ}`). -/
lemma inv_two_pow_rpow (ℓ : ℕ) (x : ℝ) : ((2 : ℝ)⁻¹ ^ ℓ) ^ x = (2 : ℝ) ^ (-(x * ℓ)) := by
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num),
    ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- The small-jump second moment of the example: `∫_{|z| < δ} z² dν = c δ^{2−Y}/(2 − Y)` for
`0 < δ ≤ 1` (Giles 2015, §6.2: `∫_{δ_ℓ}^{δ_{ℓ−1}} z² ν(dz) ≍ δ^{2−Y}`). -/
lemma setIntegral_sq_stableLikeLevy {c Y : ℝ} (hc : 0 < c) (hY2 : Y < 2) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∫ z in {z : ℝ | |z| < δ}, z ^ 2 ∂(stableLikeLevy c Y) = c * δ ^ (2 - Y) / (2 - Y) := by
  have hm : MeasurableSet {z : ℝ | |z| < δ} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have e : {z : ℝ | |z| < δ} ∩ Set.Ioc 0 1 = Set.Ioo 0 δ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, (le_abs_self z).trans_lt h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨show |z| < δ by rw [abs_of_pos h1]; exact h2, h1, (h2.trans_le hδ1).le⟩
  rw [setIntegral_stableLikeLevy c Y hm, e]
  have e2 : ∫ z in Set.Ioo 0 δ, (stableLikeDensity c Y z : ℝ) * z ^ 2 =
      ∫ z in Set.Ioo 0 δ, c * z ^ (1 - Y) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
    have e3 := stableLikeDensity_mul_rpow (Y := Y) hc hz.1 2
    rw [Real.rpow_two] at e3
    rw [e3, show (2 : ℝ) - 1 - Y = 1 - Y by ring]
  rw [e2, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hδ.le,
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 1 - Y)),
    Real.zero_rpow (by linarith : (1 - Y + 1 : ℝ) ≠ 0)]
  have e4 : (1 - Y + 1 : ℝ) = 2 - Y := by ring
  rw [e4, sub_zero, mul_div_assoc]

/-- The mass of the simulated jumps of the example: `ν(|z| ≥ δ) = c (δ^{−Y} − 1)/Y` for
`0 < δ ≤ 1` (Giles 2015, §6.2: the expected number of simulated jumps `≍ δ^{−Y}`). -/
lemma measureReal_levySet_stableLikeLevy {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((stableLikeLevy c Y) (levySet δ)).toReal = c * (δ ^ (-Y) - 1) / Y := by
  have hm := measurableSet_levySet δ
  have h1 := setIntegral_const (μ := stableLikeLevy c Y) (s := levySet δ) (1 : ℝ)
  rw [smul_eq_mul, mul_one, measureReal_def] at h1
  rw [← h1, setIntegral_stableLikeLevy c Y hm]
  have e : levySet δ ∩ Set.Ioc 0 1 = Set.Icc δ 1 := by
    ext z
    unfold levySet
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by rwa [abs_of_pos h2] at h1, h3⟩
    · rintro ⟨h1, h2⟩
      have hz : 0 < z := hδ.trans_le h1
      exact ⟨by rw [abs_of_pos hz]; exact h1, hz, h2⟩
  rw [e]
  have e2 : ∫ z in Set.Icc δ 1, (stableLikeDensity c Y z : ℝ) * 1 =
      ∫ z in Set.Icc δ 1, c * z ^ (-1 - Y) := by
    refine setIntegral_congr_fun measurableSet_Icc fun z hz => ?_
    have e3 := stableLikeDensity_mul_rpow (Y := Y) hc (hδ.trans_le hz.1) 0
    rw [Real.rpow_zero] at e3
    rw [e3, show (0 : ℝ) - 1 - Y = -1 - Y by ring]
  have h0 : (0 : ℝ) ∉ Set.uIcc δ 1 := by
    rw [Set.mem_uIcc]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · linarith
    · linarith
  rw [e2, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hδ1,
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by linarith, h0⟩), Real.one_rpow]
  have e4 : (-1 - Y + 1 : ℝ) = -Y := by ring
  rw [e4]
  field_simp
  ring

/-- The small-jump second moment of the example at `δ_ℓ = 2^{−ℓ}`:
`∫_{|z| < 2^{−ℓ}} z² dν = c 2^{−(2−Y)ℓ}/(2 − Y)` (Giles 2015, §6.2). -/
lemma stableLike_small_sq {c Y : ℝ} (hc : 0 < c) (hY2 : Y < 2) (ℓ : ℕ) :
    ∫ z in {z : ℝ | |z| < (2 : ℝ)⁻¹ ^ ℓ}, z ^ 2 ∂(stableLikeLevy c Y) =
      c * (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) / (2 - Y) := by
  rw [setIntegral_sq_stableLikeLevy hc hY2 (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)), inv_two_pow_rpow]

/-- The expected number of simulated jumps of the example at `δ_ℓ = 2^{−ℓ}`, per unit time:
`ν(|z| ≥ 2^{−ℓ}) = c (2^{Yℓ} − 1)/Y` (Giles 2015, §6.2). -/
lemma stableLike_count {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y) (ℓ : ℕ) :
    ((stableLikeLevy c Y) (levySet ((2 : ℝ)⁻¹ ^ ℓ))).toReal =
      c * ((2 : ℝ) ^ (Y * (ℓ : ℝ)) - 1) / Y := by
  rw [measureReal_levySet_stableLikeLevy hc hY0 (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)), inv_two_pow_rpow, neg_mul, neg_neg]

/-- **Theorem 1 end to end for the one-sided stable-like example** (Giles 2015, §6.2, p. 47,
l. 2038–2051: "With infinite activity Lévy processes it is impossible to simulate each jump", with
§2.1, Theorem 1).  The pure-jump Lévy process with Lévy measure
`ν(dz) = c z^{−1−Y} dz` on `0 < z ≤ 1` (`c > 0`, `0 < Y < 2`, infinite activity) at time `T`,
cutoffs `δ_ℓ = 2^{−ℓ}`, levels built from independent compound Poisson simulations of the bands
of jump sizes (any band laws with `Λ_k • M_k = T • ν|_{band k}`, which exist by
`exists_levy_bandLaws`) and a `K`-Lipschitz payoff `Φ`.  The truncation error is
`E[(X − X^{δ_ℓ})²] = T c 2^{−(2−Y)ℓ}/(2 − Y)` for an `L²` limit `X`, a level-`ℓ` sample costs one
plus the number of jumps it simulates, a random cost with expectation `1 + T c (2^{Yℓ} − 1)/Y`,
and the multilevel estimator of `E[Φ(X)]` satisfies Theorem 1 with `α = (2 − Y)/2`, `β = 2 − Y`,
`γ = Y`: mean square error `< ε²` with an integrable random total cost whose expectation
`∑_ℓ N_ℓ (1 + T c (2^{Yℓ} − 1)/Y)` is `O(ε⁻²)` for `Y < 1`, `O(ε⁻² (log ε)²)` for `Y = 1` and
`O(ε^{−2−(γ−β)/α}) = O(ε^{−2−4(Y−1)/(2−Y)}) = O(ε^{−2Y/(2−Y)})` for `1 < Y < 2` (e.g. `O(ε^{−6})`
at `Y = 3/2`).  Since `ν` lives on `(0, 1]`, band `0 = {|z| ≥ 1}` has `ν`-mass `0`, so level `0`
is almost surely the deterministic `Φ(0)`. -/
theorem levy_stableLike_theorem1 {c Y : ℝ} (hc : 0 < c) (hY0 : 0 < Y) (hY2 : Y < 2) (T : ℝ≥0)
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k =
      T • (stableLikeLevy c Y).restrict (levyBand (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) k))
    {Φ : ℝ → ℝ} {K : ℝ≥0} (hΦ : LipschitzWith K Φ) :
    ∃ X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ,
      (∀ ℓ : ℕ, Integrable (fun ω => (X ω -
          bandApprox (stableLikeLevy c Y) T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω) ^ 2)
          (bandInputLaw Λ M) ∧
        ∫ ω, (X ω - bandApprox (stableLikeLevy c Y) T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω) ^ 2
          ∂(bandInputLaw Λ M) = T * c * (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) / (2 - Y)) ∧
      Integrable (fun ω => Φ (X ω)) (bandInputLaw Λ M) ∧
      ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
        ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
          Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ ω => Φ (bandApprox (stableLikeLevy c Y) T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω))
              (fun ℓ ω => Φ (bandApprox (stableLikeLevy c Y) T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω)))
              (fun p x => x p) ℓ (N ℓ) x - ∫ ω, Φ (X ω) ∂(bandInputLaw Λ M)) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) ∧
          ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff
              (fun ℓ ω => Φ (bandApprox (stableLikeLevy c Y) T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω))
              (fun ℓ ω => Φ (bandApprox (stableLikeLevy c Y) T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω)))
              (fun p x => x p) ℓ (N ℓ) x - ∫ ω, Φ (X ω) ∂(bandInputLaw Λ M)) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) < ε ^ 2 ∧
          Integrable (fun x : ℕ × ℕ → ℕ → ℕ × (ℕ → ℝ) => ∑ ℓ ∈ range (L + 1),
              ∑ n ∈ range (N ℓ), (1 + ∑ k ∈ range (ℓ + 1), ((x (ℓ, n) k).1 : ℝ)))
            (Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) ∧
          ∫ x, ∑ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ),
              (1 + ∑ k ∈ range (ℓ + 1), ((x (ℓ, n) k).1 : ℝ))
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => bandInputLaw Λ M) =
            ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * c * ((2 : ℝ) ^ (Y * (ℓ : ℝ)) - 1) / Y) ∧
          ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * c * ((2 : ℝ) ^ (Y * (ℓ : ℝ)) - 1) / Y) ≤
            c₄ * complexityBound ((2 - Y) / 2) (2 - Y) Y ε := by
  have hsq := integrable_sq_stableLikeLevy hc hY2
  have hν : Integrable (fun z => min 1 (z ^ 2)) (stableLikeLevy c Y) :=
    hsq.mono' (by fun_prop) (ae_of_all _ fun z => by
      rw [Real.norm_of_nonneg (le_min zero_le_one (sq_nonneg z))]
      exact min_le_right _ _)
  have hT : (0 : ℝ) ≤ T := T.2
  obtain ⟨X, hXℓ, hPX, c₄, hc₄, h⟩ := levy_truncation_theorem1 hν hsq.integrableOn T hY0 hY2
    (a := T * c / (2 - Y)) (b := T * c / Y)
    (fun ℓ => by
      rw [stableLike_small_sq hc hY2 ℓ]
      exact le_of_eq (by ring))
    (fun ℓ => by
      rw [stableLike_count hc hY0 ℓ]
      have h2 : (0 : ℝ) ≤ T * c / Y := by positivity
      have e : (T : ℝ) * (c * ((2 : ℝ) ^ (Y * (ℓ : ℝ)) - 1) / Y) =
          T * c / Y * (2 : ℝ) ^ (Y * (ℓ : ℝ)) - T * c / Y := by
        field_simp
      rw [e]
      linarith) hband hΦ
  refine ⟨X, fun ℓ => ⟨(hXℓ ℓ).1, ?_⟩, hPX, c₄, hc₄, fun ε hε hε1 => ?_⟩
  · rw [(hXℓ ℓ).2, stableLike_small_sq hc hY2 ℓ]
    ring
  · obtain ⟨L, N, hN, hint, hmse, hcI, hcE, hcost⟩ := h ε hε hε1
    have e : ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) *
        (1 + T * ((stableLikeLevy c Y) (levySet ((2 : ℝ)⁻¹ ^ ℓ))).toReal) =
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (1 + T * c * ((2 : ℝ) ^ (Y * (ℓ : ℝ)) - 1) / Y) := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [stableLike_count hc hY0 ℓ]
      ring
    exact ⟨L, N, hN, hint, hmse, hcI, hcE.trans e, e.symm.le.trans hcost⟩

end MLMC
