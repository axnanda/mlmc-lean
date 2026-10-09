import MlmcLean.MarkovNoWeakLimit
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# A logarithmic moment suffices for the half-step chain (Giles 2015, §10.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §10.1 "Markov
chains and limiting distributions", p. 61, l. 2707–2717: "In their application, the Markov chain
`{X_n}` in a metric space with metric `d` is defined by `X_0 = x`, `X_{n+1} = φ_n(X_n)`, `n ≥ 0`,
where `{φ_n}` is a sequence of iid random functions.  Furthermore, it is assumed that the `φ`'s are
contracting on average in the sense that `sup_{x≠y} E[(d(φ_n(x), φ_n(y))/d(x, y))^{2γ}] < 1` for
some `γ ∈ (0, 1)`.  Under these conditions, it is known that the distribution of `X_n` converges
weakly to that of a limit random variable `X_∞`"; and l. 2720–2722: "An example they offer of a
chain satisfying the required conditions is `X_0 = 0`, `X_{n+1} = ½ X_n + ξ_n`, `n ≥ 0`".

**Context.**  `tendstoInDistribution_fwdIter` (`MlmcLean/MarkovLimit.lean`) proves the weak
convergence under the extra moment hypothesis `hc : E[d(x₀, φ(x₀, ξ))^p] < ∞`, and
`MlmcLean/MarkovNoWeakLimit.lean` shows that some moment condition is needed: the half-step chain
`X_{n+1} = X_n/2 + ξ_n` driven by noise with `P(ξ > t) = 1/log t` has no weak limit.  This file
proves the claim made there that for the half-step chain a logarithmic moment already suffices,
and that this condition is strictly weaker than `hc`.

**What is proved.**  Let the noises `ξ_0, ξ_1, …` be real, independent, with common law `ν`, and let
`E[log(1 + |ξ|)] = ∫ log(1 + |e|) dν(e) < ∞` (stated as a finite Lebesgue integral of the
nonnegative function `log(1 + |e|)`; it is equivalent to `E[log⁺ |ξ|] < ∞` for a finite law, since
`log⁺ x ≤ log(1 + x) ≤ log⁺ x + log 2` for `x ≥ 0`, `lintegral_log_one_add_abs_ne_top_iff`). Let
`|c| < 1` (for the step `x ↦ c x + e` the contraction on average of `tendstoInDistribution_fwdIter`
holds with `ρ = |c|^p`, and only for `|c| < 1`).  Then the series `∑_j c^j ξ_j` converges absolutely
almost surely; for every start `x₀` the chain started `n` steps in the past,
`Z_n = c^n x₀ + ∑_{j<n} c^j ξ_j`, converges almost surely to its sum `X_∞`; and the chain
`X_0 = x₀`, `X_{n+1} = c X_n + ξ_n` converges to `X_∞` in distribution (the notion
`TendstoInDistribution` of `tendstoInDistribution_fwdIter`).  For `c = ½` this is Giles' example
with general noise (`halfStep`), and `X_∞ = ∑_j 2^{−j} ξ_j`.

The proof: for `r = 2/(1 + |c|) > 1`, `∑_j P(|ξ_j| > r^j) ≤ E[log(1 + |ξ|)]/log r + 1 < ∞`
(`|e|` exceeds at most `log(1 + |e|)/log r + 1` of the thresholds `r^j`), so by the first
Borel–Cantelli lemma almost surely `|ξ_j| ≤ r^j` for all large `j`, and then
`|c^j ξ_j| ≤ (|c| r)^j` with `|c| r = 2|c|/(1 + |c|) < 1`.  The almost sure convergence uses only
that the `ξ_j` have law `ν`, not their independence; independence enters through
`map_backIter_eq_map_fwdIter` (the forward chain has the law of the chain started in the past).

## Main results

* `tendstoInDistribution_fwdIter_affine`: the step `x ↦ c x + e` with `|c| < 1` and a finite
  logarithmic moment: almost sure convergence of `∑_j c^j ξ_j` and of the chains started in the
  past, and convergence in distribution of `X_n` to the sum, from every start `x₀`.
* `tendstoInDistribution_fwdIter_halfStep_of_log`: the same for `halfStep`, `X_∞ = ∑_j ξ_j/2^j`.
* `lintegral_log_one_add_abs_ne_top_iff`: `E[log(1 + |ξ|)] < ∞` iff `E[log⁺ |ξ|] < ∞`.
* `lintegral_log_ne_top_of_hc`: for `halfStep` the hypothesis `hc` of
  `tendstoInDistribution_fwdIter`, for any `p > 0` and `x₀`, implies the logarithmic moment.
* `logSqTailLaw`, `logSqTailLaw_Ioi`: the law of `ξ = exp(1/√U)`, `U` uniform on `(0, 1)`, with
  `P(ξ > t) = 1/(log t)²` for `t ≥ e`.
* `lintegral_log_logSqTailLaw_ne_top`, `lintegral_logSqTailLaw_eq_top`: this law has a finite
  logarithmic moment, but `hc` fails for it for every `p > 0` and every `x₀`.
* `exists_iid_logSqTailLaw`, `tendstoInDistribution_fwdIter_logSqTailLaw`: independent noises of
  this law exist, and the half-step chain driven by them converges in distribution.
* `halfStep_log_moment_strictly_weaker`: the logarithmic moment is strictly weaker than `hc` for the
  half-step chain, and the new theorem covers chains that `tendstoInDistribution_fwdIter` does
  not.

## Not covered

General metric spaces and general random maps `φ` (the proof uses the explicit series of the
affine step); random coefficients `c`; the converse, that for nonnegative noises
`E[log⁺ ξ] = ∞` prevents weak convergence (`MlmcLean/MarkovNoWeakLimit.lean` proves this only for
the particular law with `P(ξ > t) = 1/log t`); and the identification of the limit law as the
unique invariant law (`MlmcLean/MarkovLimitLaw.lean` does this under `hc`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MLMC

/-! ### Few noises exceed a geometric threshold -/

/-- For `r > 1`, `|e|` exceeds at most `log(1 + |e|)/log r + 1` of the thresholds `r^j`,
`j ∈ ℕ` (a counting fact used for the Borel–Cantelli step below). -/
lemma tsum_indicator_pow_lt_abs_le {r : ℝ} (hr : 1 < r) (e : ℝ) :
    ∑' j : ℕ, {x : ℝ | r ^ j < |x|}.indicator (1 : ℝ → ℝ≥0∞) e ≤
      ENNReal.ofReal (Real.log (1 + |e|) / Real.log r) + 1 := by
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have he1 : 0 < 1 + |e| := by positivity
  have ht0 : 0 ≤ Real.log (1 + |e|) / Real.log r :=
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg e])) hlogr.le
  have hvanish : ∀ j ∉ Finset.range (⌊Real.log (1 + |e|) / Real.log r⌋₊ + 1),
      {x : ℝ | r ^ j < |x|}.indicator (1 : ℝ → ℝ≥0∞) e = 0 := by
    intro j hj
    rw [Finset.mem_range, not_lt] at hj
    refine Set.indicator_of_notMem (fun hej => ?_) _
    have h1 : Real.log (1 + |e|) / Real.log r < j :=
      (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hj)
    rw [div_lt_iff₀ hlogr] at h1
    have h2 : 1 + |e| < r ^ j := by
      rw [← Real.exp_log he1, ← Real.exp_log (pow_pos (zero_lt_one.trans hr) j), Real.log_pow]
      exact Real.exp_lt_exp.2 h1
    have h3 : r ^ j < |e| := hej
    linarith
  rw [tsum_eq_sum hvanish]
  calc ∑ j ∈ Finset.range (⌊Real.log (1 + |e|) / Real.log r⌋₊ + 1),
        {x : ℝ | r ^ j < |x|}.indicator (1 : ℝ → ℝ≥0∞) e
      ≤ ∑ _j ∈ Finset.range (⌊Real.log (1 + |e|) / Real.log r⌋₊ + 1), (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun j _ => Set.indicator_le_self _ _ e
    _ = ((⌊Real.log (1 + |e|) / Real.log r⌋₊ : ℕ) : ℝ≥0∞) + 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_one]
        push_cast
        rfl
    _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (Nat.floor_le ht0)

/-- The function `e ↦ log(1 + |e|)`, as an extended nonnegative real, is measurable. -/
lemma measurable_ofReal_log_one_add_abs :
    Measurable fun e : ℝ => ENNReal.ofReal (Real.log (1 + |e|)) := by
  fun_prop

/-- **The expected number of large noises** (Giles 2015, §10.1, p. 61, l. 2716–2717): for `r > 1`,
`∑_j ν(|e| > r^j) ≤ E_ν[log(1 + |e|)]/log r + ν(ℝ)`. -/
lemma tsum_measure_pow_lt_abs_le (ν : Measure ℝ) {r : ℝ} (hr : 1 < r) :
    ∑' j : ℕ, ν {e | r ^ j < |e|} ≤
      ENNReal.ofReal (Real.log r)⁻¹ * ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν +
        ν univ := by
  have hs : ∀ j : ℕ, MeasurableSet {e : ℝ | r ^ j < |e|} := fun j =>
    measurableSet_lt measurable_const continuous_abs.measurable
  calc ∑' j : ℕ, ν {e | r ^ j < |e|}
      = ∑' j : ℕ, ∫⁻ e, {x : ℝ | r ^ j < |x|}.indicator (1 : ℝ → ℝ≥0∞) e ∂ν :=
        tsum_congr fun j => (lintegral_indicator_one (hs j)).symm
    _ = ∫⁻ e, ∑' j : ℕ, {x : ℝ | r ^ j < |x|}.indicator (1 : ℝ → ℝ≥0∞) e ∂ν :=
        (lintegral_tsum fun j => (measurable_one.indicator (hs j)).aemeasurable).symm
    _ ≤ ∫⁻ e, (ENNReal.ofReal (Real.log r)⁻¹ * ENNReal.ofReal (Real.log (1 + |e|)) + 1) ∂ν := by
        refine lintegral_mono fun e => (tsum_indicator_pow_lt_abs_le hr e).trans_eq ?_
        rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 (Real.log_pos hr).le)]
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, one_mul,
          lintegral_const_mul _ measurable_ofReal_log_one_add_abs]

/-- **Borel–Cantelli for the noises** (Giles 2015, §10.1, p. 61, l. 2716–2717): if the `ξ_j` have
law `ν` with `E_ν[log(1 + |e|)] < ∞` and `r > 1`, then almost surely `|ξ_j| ≤ r^j` for all large
`j`.  Independence is not needed. -/
lemma ae_eventually_abs_le_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ν : Measure ℝ}
    [IsFiniteMeasure ν] {ξ : ℕ → Ω → ℝ} (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = ν) (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν ≠ ∞)
    {r : ℝ} (hr : 1 < r) : ∀ᵐ ω ∂μ, ∀ᶠ j in atTop, |ξ j ω| ≤ r ^ j := by
  have hs : ∀ j : ℕ, MeasurableSet {e : ℝ | r ^ j < |e|} := fun j =>
    measurableSet_lt measurable_const continuous_abs.measurable
  have hj : ∀ j : ℕ, μ (ξ j ⁻¹' {e | r ^ j < |e|}) = ν {e | r ^ j < |e|} := fun j => by
    rw [← hlaw j, Measure.map_apply (hξm j) (hs j)]
  have hsum : ∑' j, μ (ξ j ⁻¹' {e | r ^ j < |e|}) ≠ ∞ := by
    rw [tsum_congr hj]
    refine ne_top_of_le_ne_top ?_ (tsum_measure_pow_lt_abs_le ν hr)
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlog, measure_ne_top ν _⟩
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with j hj
  exact not_lt.1 hj

/-- **The series `∑_j c^j ξ_j` converges almost surely** (Giles 2015, §10.1, p. 61,
l. 2716–2717) when `|c| < 1` and the `ξ_j` have a law with a finite logarithmic moment: with
`r = 2/(1 + |c|) > 1`, eventually `|c^j ξ_j| ≤ (|c| r)^j` and `|c| r < 1`. -/
lemma ae_summable_pow_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ν : Measure ℝ}
    [IsFiniteMeasure ν] {ξ : ℕ → Ω → ℝ} (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = ν) (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν ≠ ∞)
    {c : ℝ} (hc1 : |c| < 1) : ∀ᵐ ω ∂μ, Summable fun j => c ^ j * ξ j ω := by
  have hc0 := abs_nonneg c
  have hr1 : 1 < 2 / (1 + |c|) := by
    rw [one_lt_div (by positivity)]
    linarith
  have hcr0 : 0 ≤ |c| * (2 / (1 + |c|)) := by positivity
  have hcr1 : |c| * (2 / (1 + |c|)) < 1 := by
    rw [mul_div_assoc', div_lt_one (by positivity)]
    linarith
  filter_upwards [ae_eventually_abs_le_pow hξm hlaw hlog hr1] with ω hω
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hcr0 hcr1) ?_
  filter_upwards [hω] with j hj
  rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left hj (pow_nonneg hc0 j)

/-! ### The affine chain and the half-step chain -/

/-- The chain of the affine step `x ↦ c x + e` started `n` steps in the past at `x`:
`Z_n = c^n x + ∑_{j<n} c^j e_j`. -/
lemma backIter_affine (c : ℝ) (n : ℕ) (e : ℕ → ℝ) (x : ℝ) :
    backIter (fun y a => c * y + a) n e x = c ^ n * x + ∑ j ∈ Finset.range n, c ^ j * e j := by
  induction n generalizing e with
  | zero => rw [backIter_zero, pow_zero, one_mul, Finset.sum_range_zero, add_zero]
  | succ n ih =>
    rw [backIter_succ, ih, Finset.sum_range_succ', pow_zero, one_mul, mul_add, Finset.mul_sum]
    have h : ∑ j ∈ Finset.range n, c * (c ^ j * e (j + 1)) =
        ∑ j ∈ Finset.range n, c ^ (j + 1) * e (j + 1) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [h]
    ring

section main

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure ℝ}
  {ξ : ℕ → Ω → ℝ}

/-- **A logarithmic moment suffices for the affine chain** (Giles 2015, §10.1, p. 61,
l. 2716–2717: "it is known that the distribution of `X_n` converges weakly to that of a limit
random variable `X_∞`").  Let `|c| < 1`, and let the noises `ξ_j` be independent with law `ν`,
where `E_ν[log(1 + |e|)] < ∞`.  Then `∑_j c^j ξ_j` converges almost surely to some `X_∞`, and for
every start `x₀` the chains `c^n x₀ + ∑_{j<n} c^j ξ_j` started `n` steps in the past converge to
`X_∞` almost surely, and the chain `X_0 = x₀`, `X_{n+1} = c X_n + ξ_n` converges to `X_∞` in
distribution.  No moment `E[|ξ|^p]`, `p > 0`, is assumed. -/
theorem tendstoInDistribution_fwdIter_affine {c : ℝ} (hc1 : |c| < 1) (hξ : iIndepFun ξ μ)
    (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν ≠ ∞) :
    ∃ X : Ω → ℝ, AEMeasurable X μ ∧ (∀ᵐ ω ∂μ, HasSum (fun j => c ^ j * ξ j ω) (X ω)) ∧
      ∀ x₀ : ℝ,
        (∀ᵐ ω ∂μ, Tendsto (fun n => backIter (fun x e => c * x + e) n (fun k => ξ k ω) x₀)
          atTop (𝓝 (X ω))) ∧
        TendstoInDistribution (fun n ω => fwdIter (fun x e => c * x + e) n (fun k => ξ k ω) x₀)
          atTop X (fun _ => μ) μ := by
  have : IsProbabilityMeasure ν := hlaw 0 ▸ Measure.isProbabilityMeasure_map (hξm 0).aemeasurable
  have hφm : Measurable fun q : ℝ × ℝ => (fun x e => c * x + e) q.1 q.2 := by
    show Measurable fun q : ℝ × ℝ => c * q.1 + q.2
    fun_prop
  have hX : ∀ᵐ ω ∂μ, HasSum (fun j => c ^ j * ξ j ω) (∑' j, c ^ j * ξ j ω) :=
    (ae_summable_pow_mul hξm hlaw hlog hc1).mono fun ω h => h.hasSum
  have hSm : ∀ n, Measurable fun ω => ∑ j ∈ Finset.range n, c ^ j * ξ j ω := fun n =>
    Finset.measurable_sum _ fun j _ => (hξm j).const_mul _
  have hXm : AEMeasurable (fun ω => ∑' j, c ^ j * ξ j ω) μ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hSm n).aemeasurable)
      (hX.mono fun ω h => h.tendsto_sum_nat)
  refine ⟨fun ω => ∑' j, c ^ j * ξ j ω, hXm, hX, fun x₀ => ?_⟩
  have hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun n => backIter (fun x e => c * x + e) n (fun k => ξ k ω) x₀) atTop
      (𝓝 (∑' j, c ^ j * ξ j ω)) := by
    filter_upwards [hX] with ω h
    have h0 := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc1).mul_const x₀
    rw [zero_mul] at h0
    have h1 := h0.add h.tendsto_sum_nat
    rw [zero_add] at h1
    exact h1.congr fun n => (backIter_affine c n _ x₀).symm
  have hZm : ∀ n, Measurable fun ω =>
      backIter (fun x e => c * x + e) n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_backIter_shift hφm ξ n 0 (U := fun _ => x₀) measurable_const).mono
      (noiseFrom_le hξm _) le_rfl
  have hFm : ∀ n, Measurable fun ω =>
      fwdIter (fun x e => c * x + e) n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_fwdIter hφm n x₀).comp (measurable_pi_lambda (fun ω (k : ℕ) => ξ k ω) hξm)
  refine ⟨hlim, ?_⟩
  have hZ := tendstoInDistribution_of_ae_tendsto (fun n => (hZm n).aemeasurable) hXm hlim
  refine ⟨fun n => (hFm n).aemeasurable, hXm, ?_⟩
  refine hZ.tendsto.congr fun n => ?_
  exact Subtype.ext (map_backIter_eq_map_fwdIter hφm hξ hξm hlaw n x₀)

/-- **A logarithmic moment suffices for the half-step chain** (Giles 2015, §10.1, p. 61,
l. 2716–2722: "it is known that the distribution of `X_n` converges weakly to that of a limit
random variable `X_∞` … An example they offer … is `X_0 = 0`, `X_{n+1} = ½ X_n + ξ_n`"), for
general noise.  Let the noises `ξ_j` be independent with law `ν`, where
`E_ν[log(1 + |e|)] < ∞`.  Then `∑_j 2^{−j} ξ_j` converges almost surely to some `X_∞`, and for
every start `x₀` the chains started `n` steps in the past converge to `X_∞` almost surely, and
the chain `X_0 = x₀`, `X_{n+1} = X_n/2 + ξ_n` converges to `X_∞` in distribution. -/
theorem tendstoInDistribution_fwdIter_halfStep_of_log (hξ : iIndepFun ξ μ)
    (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν ≠ ∞) :
    ∃ X : Ω → ℝ, AEMeasurable X μ ∧ (∀ᵐ ω ∂μ, HasSum (fun j => ξ j ω / 2 ^ j) (X ω)) ∧
      ∀ x₀ : ℝ,
        (∀ᵐ ω ∂μ, Tendsto (fun n => backIter halfStep n (fun k => ξ k ω) x₀) atTop
          (𝓝 (X ω))) ∧
        TendstoInDistribution (fun n ω => fwdIter halfStep n (fun k => ξ k ω) x₀) atTop X
          (fun _ => μ) μ := by
  have hφ : halfStep = fun x e => (2 : ℝ)⁻¹ * x + e := by
    funext x e
    rw [halfStep, div_eq_inv_mul]
  have hc : |(2 : ℝ)⁻¹| < 1 := by
    rw [abs_of_pos (by norm_num)]
    norm_num
  obtain ⟨X, hXm, hX, hconv⟩ := tendstoInDistribution_fwdIter_affine hc hξ hξm hlaw hlog
  refine ⟨X, hXm, hX.mono fun ω h => ?_, fun x₀ => ?_⟩
  · have e : (fun j => ξ j ω / 2 ^ j) = fun j => (2 : ℝ)⁻¹ ^ j * ξ j ω :=
      funext fun j => by rw [inv_pow, inv_mul_eq_div]
    rw [e]
    exact h
  · rw [hφ]
    exact hconv x₀

end main

/-! ### The logarithmic moment is weaker than the first-step moment -/

/-- `log(1 + |e|) ≤ log(1 + |x₀|) + 2^p/p + 2^p/p · |x₀ − φ(x₀, e)|^p` for the half step
`φ(x, e) = x/2 + e` and `p > 0`. -/
lemma log_one_add_abs_le {p : ℝ} (hp : 0 < p) (x₀ e : ℝ) :
    Real.log (1 + |e|) ≤
      (Real.log (1 + |x₀|) + 2 ^ p / p) + 2 ^ p / p * dist x₀ (halfStep x₀ e) ^ p := by
  have hb0 : 0 ≤ dist x₀ (halfStep x₀ e) := dist_nonneg
  have he : |e| ≤ |x₀| + dist x₀ (halfStep x₀ e) := by
    rw [Real.dist_eq, halfStep]
    have h1 := le_abs_self x₀
    have h2 := neg_abs_le x₀
    have h3 := le_abs_self (x₀ - (x₀ / 2 + e))
    have h4 := neg_abs_le (x₀ - (x₀ / 2 + e))
    rw [abs_le]
    constructor <;> linarith
  have h1 : Real.log (1 + |e|) ≤
      Real.log (1 + |x₀|) + Real.log (1 + dist x₀ (halfStep x₀ e)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    nlinarith [abs_nonneg x₀, abs_nonneg e, mul_nonneg (abs_nonneg x₀) hb0]
  have h2 : Real.log (1 + dist x₀ (halfStep x₀ e)) ≤ (1 + dist x₀ (halfStep x₀ e)) ^ p / p :=
    Real.log_le_rpow_div (by positivity) hp
  have h3 : (1 + dist x₀ (halfStep x₀ e)) ^ p ≤ 2 ^ p * (1 + dist x₀ (halfStep x₀ e) ^ p) := by
    have hbp := Real.rpow_nonneg hb0 p
    rcases le_total (dist x₀ (halfStep x₀ e)) 1 with hb1 | hb1
    · calc (1 + dist x₀ (halfStep x₀ e)) ^ p ≤ 2 ^ p :=
            Real.rpow_le_rpow (by positivity) (by linarith) hp.le
        _ ≤ 2 ^ p * (1 + dist x₀ (halfStep x₀ e) ^ p) :=
            le_mul_of_one_le_right (by positivity) (by linarith)
    · calc (1 + dist x₀ (halfStep x₀ e)) ^ p ≤ (2 * dist x₀ (halfStep x₀ e)) ^ p :=
            Real.rpow_le_rpow (by positivity) (by linarith) hp.le
        _ = 2 ^ p * dist x₀ (halfStep x₀ e) ^ p := Real.mul_rpow zero_le_two hb0
        _ ≤ 2 ^ p * (1 + dist x₀ (halfStep x₀ e) ^ p) := by
            gcongr
            linarith
  have h4 : (1 + dist x₀ (halfStep x₀ e)) ^ p / p ≤
      2 ^ p / p + 2 ^ p / p * dist x₀ (halfStep x₀ e) ^ p :=
    calc (1 + dist x₀ (halfStep x₀ e)) ^ p / p
        ≤ 2 ^ p * (1 + dist x₀ (halfStep x₀ e) ^ p) / p := div_le_div_of_nonneg_right h3 hp.le
      _ = _ := by ring
  linarith

/-- **`log(1 + |ξ|)` and `log⁺ |ξ|` have finite means together** (the logarithmic moment of
Giles 2015, §10.1, p. 61, l. 2716–2717: "it is known that the distribution of `X_n` converges
weakly to that of a limit random variable `X_∞`", here under a logarithmic moment): for a finite
noise law `ν`, `E_ν[log(1 + |e|)] < ∞` iff `E_ν[log⁺ |e|] < ∞`, where
`ENNReal.ofReal (log |e|) = max(0, log |e|) = log⁺ |e|` (`ENNReal.ofReal` sends negative numbers,
and `Real.log 0 = 0`, to `0`), since `log⁺ x ≤ log(1 + x) ≤ log 2 + log⁺ x` for `x ≥ 0`. -/
theorem lintegral_log_one_add_abs_ne_top_iff (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν ≠ ∞ ↔
      ∫⁻ e, ENNReal.ofReal (Real.log |e|) ∂ν ≠ ∞ := by
  have h1 : ∀ e : ℝ, ENNReal.ofReal (Real.log |e|) ≤ ENNReal.ofReal (Real.log (1 + |e|)) := by
    intro e
    rcases (abs_nonneg e).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero, ENNReal.ofReal_zero]
      exact zero_le
    · exact ENNReal.ofReal_le_ofReal (Real.log_le_log h0 (by linarith))
  have h2 : ∀ e : ℝ, ENNReal.ofReal (Real.log (1 + |e|)) ≤
      ENNReal.ofReal (Real.log 2) + ENNReal.ofReal (Real.log |e|) := by
    intro e
    rcases le_total |e| 1 with he | he
    · exact (ENNReal.ofReal_le_ofReal (Real.log_le_log (by positivity) (by linarith))).trans
        le_self_add
    · rw [← ENNReal.ofReal_add (Real.log_nonneg one_le_two) (Real.log_nonneg he),
        ← Real.log_mul two_ne_zero (by linarith)]
      exact ENNReal.ofReal_le_ofReal (Real.log_le_log (by positivity) (by linarith))
  constructor
  · exact fun h => ne_top_of_le_ne_top h (lintegral_mono h1)
  · intro h
    refine ne_top_of_le_ne_top ?_ (lintegral_mono h2)
    rw [lintegral_add_left measurable_const, lintegral_const]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _), h⟩

/-- **The first-step moment implies the logarithmic moment** (Giles 2015, §10.1, p. 61,
l. 2716–2717: "it is known that the distribution of `X_n` converges weakly to that of a limit
random variable `X_∞`"; l. 2720–2722, for the example `X_{n+1} = ½ X_n + ξ_n` with general
noise): for a finite noise law
`ν`, `p > 0` and a start `x₀`, if the hypothesis `hc` of `tendstoInDistribution_fwdIter` holds,
`E_ν[|x₀ − φ(x₀, e)|^p] < ∞` with `φ(x, e) = x/2 + e`, then `E_ν[log(1 + |e|)] < ∞`.  So
`tendstoInDistribution_fwdIter_halfStep_of_log` applies whenever `tendstoInDistribution_fwdIter`
does for the half-step chain. -/
theorem lintegral_log_ne_top_of_hc (ν : Measure ℝ) [IsFiniteMeasure ν] {p : ℝ} (hp : 0 < p)
    (x₀ : ℝ) (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (halfStep x₀ e) ^ p) ∂ν ≠ ∞) :
    ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν ≠ ∞ := by
  have hB : 0 ≤ (2 : ℝ) ^ p / p := by positivity
  have hle : ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν ≤
      ∫⁻ e, (ENNReal.ofReal (Real.log (1 + |x₀|) + 2 ^ p / p) +
        ENNReal.ofReal (2 ^ p / p) * ENNReal.ofReal (dist x₀ (halfStep x₀ e) ^ p)) ∂ν := by
    refine lintegral_mono fun e => ?_
    rw [← ENNReal.ofReal_mul hB]
    exact (ENNReal.ofReal_le_ofReal (log_one_add_abs_le hp x₀ e)).trans ENNReal.ofReal_add_le
  rw [lintegral_add_left (measurable_const (a := ENNReal.ofReal (Real.log (1 + |x₀|) + 2 ^ p / p))),
    lintegral_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hle
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩) hle
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc

/-! ### A noise law with a logarithmic moment but no moment of positive order -/

/-- The map `u ↦ exp(1/√u)` is measurable; the noise is `ξ = exp(1/√U)` with `U` uniform on
`(0, 1)`. -/
lemma measurable_exp_one_div_sqrt : Measurable fun u : ℝ => Real.exp (1 / Real.sqrt u) := by
  fun_prop

/-- **A noise law with a logarithmic moment but no moment of positive order** (for the example of
Giles 2015, §10.1, p. 61, l. 2720–2722, `X_{n+1} = ½ X_n + ξ_n`): the law of `ξ = exp(1/√U)` with
`U` uniform on `(0, 1)`, so that `P(ξ > t) = 1/(log t)²` for `t ≥ e`. -/
noncomputable def logSqTailLaw : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).map fun u => Real.exp (1 / Real.sqrt u)

/-- `logSqTailLaw` is a probability measure. -/
lemma isProbabilityMeasure_logSqTailLaw : IsProbabilityMeasure logSqTailLaw :=
  haveI := isProbabilityMeasure_restrict_Ioo
  Measure.isProbabilityMeasure_map measurable_exp_one_div_sqrt.aemeasurable

/-- `logSqTailLaw s` is the Lebesgue measure of `{u ∈ (0, 1) : exp(1/√u) ∈ s}`. -/
lemma logSqTailLaw_apply {s : Set ℝ} (hs : MeasurableSet s) :
    logSqTailLaw s = volume ((fun u : ℝ => Real.exp (1 / Real.sqrt u)) ⁻¹' s ∩ Ioo 0 1) := by
  rw [logSqTailLaw, Measure.map_apply measurable_exp_one_div_sqrt hs,
    Measure.restrict_apply (measurable_exp_one_div_sqrt hs)]

/-- **The tail of the noise law** (for the example of Giles 2015, §10.1, p. 61, l. 2720–2722: "An
example they offer of a chain satisfying the required conditions is `X_0 = 0`,
`X_{n+1} = ½ X_n + ξ_n`, `n ≥ 0`"): under `logSqTailLaw`, `P(ξ > t) = 1/(log t)²` for `t ≥ e`.  So
`log ξ` has a finite mean, but the tail of `ξ` decays more slowly than any power of `t`. -/
theorem logSqTailLaw_Ioi {t : ℝ} (ht : Real.exp 1 ≤ t) :
    logSqTailLaw (Ioi t) = ENNReal.ofReal (1 / Real.log t ^ 2) := by
  have ht0 : 0 < t := (Real.exp_pos 1).trans_le ht
  have hlog : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).2 ht
  have hlog0 : 0 < Real.log t := zero_lt_one.trans_le hlog
  have hset : (fun u : ℝ => Real.exp (1 / Real.sqrt u)) ⁻¹' Ioi t ∩ Ioo 0 1 =
      Ioo 0 (1 / Real.log t ^ 2) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h, hu0, -⟩
      have hs : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
      have h1 : Real.log t < 1 / Real.sqrt u := (Real.log_lt_iff_lt_exp ht0).2 h
      have h2 : Real.sqrt u < 1 / Real.log t := (lt_one_div hlog0 hs).1 h1
      rw [Real.sqrt_lt' (by positivity), one_div_pow] at h2
      exact ⟨hu0, h2⟩
    · rintro ⟨hu0, hu⟩
      have hs : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
      have h2 : Real.sqrt u < 1 / Real.log t := by
        rw [Real.sqrt_lt' (by positivity), one_div_pow]
        exact hu
      refine ⟨(Real.log_lt_iff_lt_exp ht0).1 ((lt_one_div hs hlog0).1 h2), hu0, ?_⟩
      refine hu.trans_le ?_
      rw [div_le_one (by positivity)]
      nlinarith
  rw [logSqTailLaw_apply measurableSet_Ioi, hset, Real.volume_Ioo, sub_zero]

/-- **The noise law has a logarithmic moment** (the hypothesis of
`tendstoInDistribution_fwdIter_halfStep_of_log`, for the example of Giles 2015, §10.1, p. 61,
l. 2720–2722: "An example they offer of a chain satisfying the required conditions is `X_0 = 0`,
`X_{n+1} = ½ X_n + ξ_n`, `n ≥ 0`"): `E[log(1 + |ξ|)] < ∞` under `logSqTailLaw`, since
`log(1 + exp(1/√u)) ≤ 1 + u^{−1/2}`, which is integrable on `(0, 1)`. -/
theorem lintegral_log_logSqTailLaw_ne_top :
    ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂logSqTailLaw ≠ ∞ := by
  rw [logSqTailLaw, lintegral_map measurable_ofReal_log_one_add_abs measurable_exp_one_div_sqrt]
  have hint : IntegrableOn (fun u : ℝ => 1 + u ^ (-(1 / 2 : ℝ))) (Ioo 0 1) :=
    (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).add
      ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num))
  refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioo).mono fun u hu => ?_)
  apply ENNReal.ofReal_le_ofReal
  have hu0 : 0 < u := hu.1
  have hy : 1 / Real.sqrt u = u ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hu0.le, one_div]
  rw [abs_of_pos (Real.exp_pos _), ← hy]
  have hy0 : 0 ≤ 1 / Real.sqrt u := by positivity
  rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add]
  have h1 : 1 ≤ Real.exp (1 / Real.sqrt u) := Real.one_le_exp hy0
  have h2 : 2 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (1 / Real.sqrt u)).le
  linarith

/-- **The first step has no moment of positive order** (the hypothesis `hc` of
`tendstoInDistribution_fwdIter` fails, for the example of Giles 2015, §10.1, p. 61, l. 2720–2722:
"An example they offer of a chain satisfying the required conditions is `X_0 = 0`,
`X_{n+1} = ½ X_n + ξ_n`, `n ≥ 0`"): for the noise law `logSqTailLaw`, every start `x₀` and every
`p > 0`, `E[|x₀ − φ(x₀, ξ)|^p] = ∞` with `φ(x, e) = x/2 + e`: for `s ≥ max(1, |x₀|)` and `ξ > e^s`,
`|x₀ − φ(x₀, ξ)| = ξ − x₀/2 ≥ e^s/2`, so by Markov's inequality the moment is at least
`e^{ps}/(2^p s²) → ∞`. -/
theorem lintegral_logSqTailLaw_eq_top (x₀ : ℝ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ e, ENNReal.ofReal (dist x₀ (halfStep x₀ e) ^ p) ∂logSqTailLaw = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨s, hsr, hs1, hsx⟩ := ((tendsto_exp_mul_div_rpow_atTop 2 p hp).eventually_ge_atTop
    (2 ^ p * r : ℝ) |>.and ((eventually_ge_atTop 1).and (eventually_ge_atTop |x₀|))).exists
  rw [Real.rpow_two] at hsr
  have h2p : 0 < (2 : ℝ) ^ p := by positivity
  have hm : AEMeasurable (fun e => ENNReal.ofReal (dist x₀ (halfStep x₀ e) ^ p))
      logSqTailLaw := by
    unfold halfStep
    fun_prop
  calc (r : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (p * s) / 2 ^ p / s ^ 2) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        rw [div_right_comm, le_div_iff₀ h2p]
        linarith
    _ = ENNReal.ofReal (Real.exp (p * s) / 2 ^ p) * logSqTailLaw (Ioi (Real.exp s)) := by
        rw [logSqTailLaw_Ioi (Real.exp_le_exp.2 hs1), Real.log_exp,
          ← ENNReal.ofReal_mul (by positivity), mul_one_div]
    _ ≤ ENNReal.ofReal (Real.exp (p * s) / 2 ^ p) *
          logSqTailLaw {e | ENNReal.ofReal (Real.exp (p * s) / 2 ^ p) ≤
            ENNReal.ofReal (dist x₀ (halfStep x₀ e) ^ p)} := by
        gcongr
        intro e he
        simp only [mem_Ioi] at he
        show ENNReal.ofReal _ ≤ ENNReal.ofReal _
        apply ENNReal.ofReal_le_ofReal
        have hes : s < Real.exp s := by
          have := Real.add_one_le_exp s
          linarith
        have hd : Real.exp s / 2 ≤ dist x₀ (halfStep x₀ e) := by
          have h1 := le_abs_self x₀
          rw [Real.dist_eq, halfStep, abs_of_neg (by linarith)]
          linarith
        calc Real.exp (p * s) / 2 ^ p = (Real.exp s / 2) ^ p := by
              rw [Real.div_rpow (Real.exp_pos s).le zero_le_two, ← Real.exp_mul, mul_comm s p]
          _ ≤ _ := Real.rpow_le_rpow (by positivity) hd hp.le
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hm _

/-- **Independent noises of law `logSqTailLaw` exist** (so the hypotheses of
`tendstoInDistribution_fwdIter_logSqTailLaw` are satisfiable; for the example of Giles 2015, §10.1,
p. 61, l. 2720–2722: "An example they offer of a chain satisfying the required conditions is
`X_0 = 0`, `X_{n+1} = ½ X_n + ξ_n`, `n ≥ 0`"): the coordinates of the product space
`(ℝ^ℕ, logSqTailLaw^⊗ℕ)`. -/
theorem exists_iid_logSqTailLaw :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ξ : ℕ → Ω → ℝ), iIndepFun ξ μ ∧ (∀ i, Measurable (ξ i)) ∧
        ∀ i, μ.map (ξ i) = logSqTailLaw := by
  have := isProbabilityMeasure_logSqTailLaw
  exact ⟨ℕ → ℝ, inferInstance, Measure.infinitePi fun _ => logSqTailLaw, inferInstance,
    fun k ω => ω k, iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id,
    fun i => measurable_pi_apply i, fun i => Measure.infinitePi_map_eval _ i⟩

/-- **The half-step chain with noise law `logSqTailLaw` converges in distribution** (Giles 2015,
§10.1, p. 61, l. 2716–2722: "it is known that the distribution of `X_n` converges weakly to that
of a limit random variable `X_∞` … `X_{n+1} = ½ X_n + ξ_n`"), although the moment hypothesis of
`tendstoInDistribution_fwdIter` fails (`lintegral_logSqTailLaw_eq_top`): with independent noises
of law `logSqTailLaw`, the series `X_∞ = ∑_j ξ_j/2^j` converges almost surely and, for every
start `x₀`, the chain `X_0 = x₀`, `X_{n+1} = X_n/2 + ξ_n` converges to `X_∞` in distribution. -/
theorem tendstoInDistribution_fwdIter_logSqTailLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : ℕ → Ω → ℝ} (hξ : iIndepFun ξ μ)
    (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = logSqTailLaw) :
    ∃ X : Ω → ℝ, (∀ᵐ ω ∂μ, HasSum (fun j => ξ j ω / 2 ^ j) (X ω)) ∧
      ∀ x₀ : ℝ, TendstoInDistribution (fun n ω => fwdIter halfStep n (fun k => ξ k ω) x₀) atTop X
        (fun _ => μ) μ := by
  obtain ⟨X, -, hX, hconv⟩ :=
    tendstoInDistribution_fwdIter_halfStep_of_log hξ hξm hlaw lintegral_log_logSqTailLaw_ne_top
  exact ⟨X, hX, fun x₀ => (hconv x₀).2⟩

/-- **The logarithmic moment is strictly weaker than the first-step moment** (Giles 2015, §10.1,
p. 61, l. 2716–2722: "it is known that the distribution of `X_n` converges weakly to that of a
limit random variable `X_∞` … An example they offer … is `X_0 = 0`, `X_{n+1} = ½ X_n + ξ_n`").
For the half step `φ(x, e) = x/2 + e`:
(1) for every finite noise law, every `p > 0` and every `x₀`, the hypothesis
`E[|x₀ − φ(x₀, ξ)|^p] < ∞` of `tendstoInDistribution_fwdIter` implies `E[log(1 + |ξ|)] < ∞`, the
hypothesis of `tendstoInDistribution_fwdIter_halfStep_of_log`;
(2) there is a noise law with `E[log(1 + |ξ|)] < ∞` for which `E[|x₀ − φ(x₀, ξ)|^p] = ∞` for
every `p > 0` and every `x₀`, and independent noises of this law exist and drive a chain that
converges in distribution, to one limit for every start: a chain that
`tendstoInDistribution_fwdIter` does not cover. -/
theorem halfStep_log_moment_strictly_weaker :
    (∀ (ν : Measure ℝ) [IsFiniteMeasure ν] (p x₀ : ℝ), 0 < p →
      ∫⁻ e, ENNReal.ofReal (dist x₀ (halfStep x₀ e) ^ p) ∂ν ≠ ∞ →
        ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν ≠ ∞) ∧
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∫⁻ e, ENNReal.ofReal (Real.log (1 + |e|)) ∂ν ≠ ∞ ∧
      (∀ x₀ p : ℝ, 0 < p → ∫⁻ e, ENNReal.ofReal (dist x₀ (halfStep x₀ e) ^ p) ∂ν = ∞) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (ξ : ℕ → Ω → ℝ), iIndepFun ξ μ ∧ (∀ i, Measurable (ξ i)) ∧
          (∀ i, μ.map (ξ i) = ν) ∧
          ∃ X : Ω → ℝ, ∀ x₀ : ℝ,
            TendstoInDistribution (fun n ω => fwdIter halfStep n (fun k => ξ k ω) x₀) atTop X
              (fun _ => μ) μ := by
  refine ⟨fun ν _ p x₀ hp hc => lintegral_log_ne_top_of_hc ν hp x₀ hc, logSqTailLaw,
    isProbabilityMeasure_logSqTailLaw, lintegral_log_logSqTailLaw_ne_top,
    fun x₀ p hp => lintegral_logSqTailLaw_eq_top x₀ hp, ?_⟩
  obtain ⟨Ω, _, μ, _, ξ, hξ, hξm, hlaw⟩ := exists_iid_logSqTailLaw
  refine ⟨Ω, inferInstance, μ, inferInstance, ξ, hξ, hξm, hlaw, ?_⟩
  obtain ⟨X, -, hX⟩ := tendstoInDistribution_fwdIter_logSqTailLaw hξ hξm hlaw
  exact ⟨X, hX⟩

end MLMC
