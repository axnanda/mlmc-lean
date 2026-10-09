import MlmcLean.MarkovLimit
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Without a first-step moment a contracting chain need not converge weakly (Giles 2015, §10.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §10.1 "Markov
chains and limiting distributions", p. 61, l. 2707–2717: "In their application, the Markov chain
`{X_n}` in a metric space with metric `d` is defined by `X_0 = x`, `X_{n+1} = φ_n(X_n)`, `n ≥ 0`,
where `{φ_n}` is a sequence of iid random functions.  Furthermore, it is assumed that the `φ`'s are
contracting on average in the sense that `sup_{x≠y} E[(d(φ_n(x), φ_n(y))/d(x, y))^{2γ}] < 1` for
some `γ ∈ (0, 1)`.  Under these conditions, it is known that the distribution of `X_n` converges
weakly to that of a limit random variable `X_∞`".

**The slip.**  Contraction on average alone does not give weak convergence: a moment condition on
a single step is needed as well.  `tendstoInDistribution_fwdIter` (`MlmcLean/MarkovLimit.lean`)
proves the weak convergence under the extra hypothesis
`hc : E[d(x₀, φ(x₀, ξ))^p] < ∞`; this file shows that `hc` cannot be dropped.  (The sentence
paraphrases Glynn and Rhee (2014), whose paper is not in `docs/`; their "required conditions",
l. 2720, may include more than the paraphrase lists.  `hc` is sufficient, not necessary: for the
chain below a logarithmic moment `E[log⁺ ξ] < ∞` would already do; this is not formalised.
Completeness of the space is also needed: on `(0, ∞)` the deterministic map `x ↦ x/2` satisfies
`hc`, but `δ_{2^{−n}x₀}` has no weak limit in the space; `tendstoInDistribution_fwdIter` assumes
`CompleteSpace`, and `completeSpace_cannot_be_dropped` (`MlmcLean.LimitLawExtras`) proves that
this hypothesis cannot be dropped.)

**The counterexample.**  On `ℝ` take the step `φ(x, e) = x/2 + e` of the example quoted by Giles
(`halfStep`; "An example they offer", l. 2720–2722), but drive it by heavy-tailed noise:
`ξ = exp(1/U)` with `U` uniform on `(0, 1)` (`logTailLaw`), so that `P(ξ > t) = 1/log t` for
`t ≥ e`.  Since `|φ(x, e) − φ(y, e)| = |x − y|/2` for every `e`, the step contracts on average with
`ρ = 2^{−p}` for every `p > 0` (in Giles' notation the supremum is `2^{−2γ} < 1` for every `γ`), but
`E[ξ^p] = ∞` for every `p > 0`.  The chain started at `0` is `X_n = ∑_{j<n} 2^{−(n−1−j)} ξ_j`; it
has the law of the chain started in the past, `Z_n = ∑_{j<n} 2^{−j} ξ_j ≥ max_{j<n} 2^{−j} ξ_j` (the
noises are positive), so for an integer `m ≥ 2` and `M ≤ e^m`,
`P(X_n ≤ M) ≤ ∏_{j<n} P(ξ_j ≤ e^{j+m}) = (m − 1)/(n + m − 1) → 0`.  The mass escapes to `+∞`, the
laws of the `X_n` are not tight, and by the portmanteau theorem they have no weak limit.

## Main results

* `logTailLaw_Ioi`: `P(ξ > t) = 1/log t` for `t ≥ e`.
* `halfStep_contracting`: the hypothesis `hφ` of `tendstoInDistribution_fwdIter` holds for
  `φ(x, e) = x/2 + e`, every noise law and every `p > 0`, with `ρ = 2^{−p}`.
* `lintegral_logTailLaw_eq_top`: the hypothesis `hc` fails for `logTailLaw`, `x₀ = 0` and every
  `p > 0`; `logTailLaw_counterexample` collects the two.
* `tendsto_measure_fwdIter_halfStep_le`, `tendsto_measure_lt_fwdIter_halfStep`: with independent
  noises of law `logTailLaw`, `P(X_n ≤ M) → 0` and `P(X_n > M) → 1` for every `M`.
* `markov_no_weak_limit`: no probability measure on `ℝ` is the weak limit of the laws of `X_n`.
* `not_tendstoInDistribution_fwdIter_halfStep`: `X_n` has no limit in distribution.
* `exists_iid_logTailLaw`: independent noises of law `logTailLaw` exist (the coordinates of the
  product space), so the hypotheses of the results above are satisfiable.
* `hc_cannot_be_dropped`: the statement of `tendstoInDistribution_fwdIter` without `hc` is false.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MLMC

/-! ### The noise law and the step -/

/-- The map `u ↦ exp(1/u)` is measurable; the noise is `ξ = exp(1/U)` with `U` uniform on
`(0, 1)`. -/
lemma measurable_exp_one_div : Measurable fun u : ℝ => Real.exp (1 / u) := by fun_prop

/-- **The heavy-tailed noise law** of the counterexample to Giles 2015, §10.1, p. 61: the law of
`ξ = exp(1/U)` with `U` uniform on `(0, 1)`, so that `P(ξ > t) = 1/log t` for `t ≥ e`. -/
noncomputable def logTailLaw : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).map fun u => Real.exp (1 / u)

/-- Lebesgue measure restricted to `(0, 1)`, the law of `U`, is a probability measure. -/
lemma isProbabilityMeasure_restrict_Ioo :
    IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]⟩

/-- `logTailLaw` is a probability measure. -/
lemma isProbabilityMeasure_logTailLaw : IsProbabilityMeasure logTailLaw :=
  haveI := isProbabilityMeasure_restrict_Ioo
  Measure.isProbabilityMeasure_map measurable_exp_one_div.aemeasurable

/-- `logTailLaw s` is the Lebesgue measure of `{u ∈ (0, 1) : exp(1/u) ∈ s}`. -/
lemma logTailLaw_apply {s : Set ℝ} (hs : MeasurableSet s) :
    logTailLaw s = volume ((fun u : ℝ => Real.exp (1 / u)) ⁻¹' s ∩ Ioo 0 1) := by
  rw [logTailLaw, Measure.map_apply measurable_exp_one_div hs,
    Measure.restrict_apply (measurable_exp_one_div hs)]

/-- **The tail of the noise law** (Giles 2015, §10.1, p. 61, counterexample to l. 2716–2717: "it is
known that the distribution of `X_n` converges weakly to that of a limit random variable `X_∞`"):
under `logTailLaw`, `P(ξ > t) = 1/log t` for `t ≥ e`.  This decays more slowly than any power of
`t`, so `ξ` has no moment of positive order. -/
theorem logTailLaw_Ioi {t : ℝ} (ht : Real.exp 1 ≤ t) :
    logTailLaw (Ioi t) = ENNReal.ofReal (1 / Real.log t) := by
  have ht0 : 0 < t := (Real.exp_pos 1).trans_le ht
  have hlog : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).2 ht
  have hlog0 : 0 < Real.log t := zero_lt_one.trans_le hlog
  have hset : (fun u : ℝ => Real.exp (1 / u)) ⁻¹' Ioi t ∩ Ioo 0 1 = Ioo 0 (1 / Real.log t) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h, hu0, -⟩
      exact ⟨hu0, (lt_one_div hlog0 hu0).1 ((Real.log_lt_iff_lt_exp ht0).2 h)⟩
    · rintro ⟨hu0, hu⟩
      refine ⟨(Real.log_lt_iff_lt_exp ht0).1 ((lt_one_div hu0 hlog0).1 hu), hu0, ?_⟩
      exact hu.trans_le ((div_le_one hlog0).2 hlog)
  rw [logTailLaw_apply measurableSet_Ioi, hset, Real.volume_Ioo, sub_zero]

/-- The distribution function of the noise law at `e^s`: `P(ξ ≤ e^s) = 1 − 1/s` for `s ≥ 1`. -/
lemma logTailLaw_Iic_exp {s : ℝ} (hs : 1 ≤ s) :
    logTailLaw (Iic (Real.exp s)) = ENNReal.ofReal (1 - 1 / s) := by
  have := isProbabilityMeasure_logTailLaw
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    logTailLaw_Ioi (Real.exp_le_exp.2 hs), Real.log_exp,
    ENNReal.ofReal_sub _ (one_div_nonneg.2 (zero_le_one.trans hs)), ENNReal.ofReal_one]

/-- The noise is positive: `ξ = exp(1/U) > 0`. -/
lemma ae_pos_logTailLaw : ∀ᵐ e ∂logTailLaw, 0 < e := by
  rw [logTailLaw, ae_map_iff measurable_exp_one_div.aemeasurable measurableSet_Ioi]
  exact Eventually.of_forall fun u => Real.exp_pos _

/-- **The step contracts on average** (the hypothesis `hφ` of `tendstoInDistribution_fwdIter`, Giles
2015, §10.1, p. 61, l. 2711–2716: "it is assumed that the `φ`'s are contracting on average in the
sense that `sup_{x≠y} E[(d(φ_n(x), φ_n(y))/d(x, y))^{2γ}] < 1` for some `γ ∈ (0, 1)`"): for every
noise law `ν` and every `p > 0`, `E[|φ(x, ξ) − φ(y, ξ)|^p] ≤ 2^{−p} |x − y|^p` with
`0 ≤ 2^{−p} < 1`, since `|φ(x, e) − φ(y, e)| = |x − y|/2` for every `e`. -/
theorem halfStep_contracting (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ} (hp : 0 < p) :
    0 ≤ (2 : ℝ) ^ (-p) ∧ (2 : ℝ) ^ (-p) < 1 ∧
      ∀ x y : ℝ, ∫⁻ e, ENNReal.ofReal (dist (halfStep x e) (halfStep y e) ^ p) ∂ν ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-p)) * ENNReal.ofReal (dist x y ^ p) := by
  refine ⟨Real.rpow_nonneg zero_le_two _,
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hp), fun x y => le_of_eq ?_⟩
  have h : ∀ e, dist (halfStep x e) (halfStep y e) ^ p = (2 : ℝ) ^ (-p) * dist x y ^ p := by
    intro e
    rw [Real.dist_eq, Real.dist_eq, halfStep, halfStep,
      show x / 2 + e - (y / 2 + e) = (x - y) / 2 by ring, abs_div, abs_two,
      Real.div_rpow (abs_nonneg _) zero_le_two, Real.rpow_neg zero_le_two, div_eq_inv_mul]
  simp_rw [h]
  rw [lintegral_const, measure_univ, mul_one,
    ENNReal.ofReal_mul (Real.rpow_nonneg zero_le_two _)]

/-- **The first step has no moment** (the hypothesis `hc` of `tendstoInDistribution_fwdIter` fails,
Giles 2015, §10.1, p. 61, counterexample to l. 2716–2717: "it is known that the distribution of
`X_n` converges weakly to that of a limit random variable `X_∞`"): for the noise law `logTailLaw`
and every `p > 0`, `E[|x₀ − φ(x₀, ξ)|^p] = E[ξ^p] = ∞` at `x₀ = 0`, because `P(ξ > t) = 1/log t`
decays more slowly than `t^{−p}` (Markov's inequality at `t = e^s`: `E[ξ^p] ≥ e^{ps}/s → ∞`). -/
theorem lintegral_logTailLaw_eq_top {p : ℝ} (hp : 0 < p) :
    ∫⁻ e, ENNReal.ofReal (dist 0 (halfStep 0 e) ^ p) ∂logTailLaw = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨s, hsr, hs1⟩ := ((tendsto_exp_mul_div_rpow_atTop 1 p hp).eventually_ge_atTop
    (r : ℝ) |>.and (eventually_ge_atTop 1)).exists
  rw [Real.rpow_one] at hsr
  have hm : AEMeasurable (fun e => ENNReal.ofReal (dist 0 (halfStep 0 e) ^ p)) logTailLaw := by
    unfold halfStep
    fun_prop
  calc (r : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (p * s) / s) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hsr
    _ = ENNReal.ofReal (Real.exp (p * s)) * logTailLaw (Ioi (Real.exp s)) := by
        rw [logTailLaw_Ioi (Real.exp_le_exp.2 hs1), Real.log_exp,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_one_div]
    _ ≤ ENNReal.ofReal (Real.exp (p * s)) * logTailLaw {e | ENNReal.ofReal (Real.exp (p * s)) ≤
          ENNReal.ofReal (dist 0 (halfStep 0 e) ^ p)} := by
        gcongr
        intro e he
        simp only [mem_Ioi] at he
        have he0 : 0 < e := (Real.exp_pos s).trans he
        show ENNReal.ofReal _ ≤ ENNReal.ofReal _
        apply ENNReal.ofReal_le_ofReal
        rw [Real.dist_eq, halfStep, zero_div, zero_add, zero_sub, abs_neg, abs_of_pos he0,
          mul_comm, Real.exp_mul]
        exact Real.rpow_le_rpow (Real.exp_pos s).le he.le hp.le
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hm _

/-- **The counterexample's step and noise** (Giles 2015, §10.1, p. 61, l. 2711–2716: "it is assumed
that the `φ`'s are contracting on average in the sense that
`sup_{x≠y} E[(d(φ_n(x), φ_n(y))/d(x, y))^{2γ}] < 1` for some `γ ∈ (0, 1)`"): for `φ(x, e) = x/2 + e`
and the noise law `logTailLaw`, for every `p > 0` the hypotheses `hp`, `hρ0`, `hρ1` and `hφ` of
`tendstoInDistribution_fwdIter` hold with `ρ = 2^{−p}`, and its hypothesis `hc` fails at
`x₀ = 0`. -/
theorem logTailLaw_counterexample {p : ℝ} (hp : 0 < p) :
    0 ≤ (2 : ℝ) ^ (-p) ∧ (2 : ℝ) ^ (-p) < 1 ∧
      (∀ x y : ℝ, ∫⁻ e, ENNReal.ofReal (dist (halfStep x e) (halfStep y e) ^ p) ∂logTailLaw ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-p)) * ENNReal.ofReal (dist x y ^ p)) ∧
      ¬ ∫⁻ e, ENNReal.ofReal (dist 0 (halfStep 0 e) ^ p) ∂logTailLaw ≠ ∞ := by
  have := isProbabilityMeasure_logTailLaw
  obtain ⟨h0, h1, h2⟩ := halfStep_contracting logTailLaw hp
  exact ⟨h0, h1, h2, not_not.2 (lintegral_logTailLaw_eq_top hp)⟩

/-! ### The chain escapes to infinity -/

/-- The chain started `n` steps in the past at `0`: `Z_n = ∑_{j<n} 2^{−j} e_j`. -/
lemma backIter_halfStep (n : ℕ) (e : ℕ → ℝ) :
    backIter halfStep n e 0 = ∑ j ∈ Finset.range n, e j / 2 ^ j := by
  induction n generalizing e with
  | zero => rw [backIter_zero, Finset.sum_range_zero]
  | succ n ih =>
    rw [backIter_succ, ih, Finset.sum_range_succ', halfStep, Finset.sum_div, pow_zero, div_one]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ, div_div]

/-- The telescoping product `∏_{j<n} (1 − 1/(j + m)) = (m − 1)/(n + m − 1)`. -/
lemma prod_one_sub_one_div (m : ℕ) (hm : 2 ≤ m) (n : ℕ) :
    ∏ j ∈ Finset.range n, (1 - 1 / ((j : ℝ) + m)) = ((m : ℝ) - 1) / (n + m - 1) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  induction n with
  | zero =>
    rw [Finset.prod_range_zero, Nat.cast_zero, zero_add, div_self (by linarith)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (n : ℝ) + m - 1 ≠ 0 := by linarith
    have h2 : (n : ℝ) + m ≠ 0 := by linarith
    rw [show (1 : ℝ) - 1 / (n + m) = (n + m - 1) / (n + m) by field_simp, div_mul_div_comm,
      mul_comm ((m : ℝ) - 1), mul_div_mul_left _ _ h1]
    push_cast
    ring_nf

section escape

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- **The chain started in the past escapes to infinity** (Giles 2015, §10.1, p. 61, counterexample
to l. 2716–2717: "it is known that the distribution of `X_n` converges weakly to that of a limit
random variable `X_∞`"): with independent noises of law `logTailLaw`, `P(Z_n ≤ M) → 0` for every
`M`, where `Z_n = ∑_{j<n} 2^{−j} ξ_j` is the chain started `n` steps in the past at `0`.  Indeed
`Z_n ≥ 2^{−j} ξ_j` for `j < n`, so with an integer `m ≥ 2` and `M ≤ e^m`,
`P(Z_n ≤ M) ≤ ∏_{j<n} P(ξ_j ≤ e^{j+m}) = ∏_{j<n} (1 − 1/(j + m)) = (m − 1)/(n + m − 1)`. -/
theorem tendsto_measure_backIter_halfStep_le (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = logTailLaw) (M : ℝ) :
    Tendsto (fun n => μ {ω | backIter halfStep n (fun k => ξ k ω) 0 ≤ M}) atTop (𝓝 0) := by
  obtain ⟨m, hm2, hMm⟩ : ∃ m : ℕ, 2 ≤ m ∧ M ≤ Real.exp m := by
    refine ⟨⌈M⌉₊ + 2, by omega, ?_⟩
    have h1 := Nat.le_ceil M
    have h2 := Real.add_one_le_exp ((⌈M⌉₊ + 2 : ℕ) : ℝ)
    push_cast at h2 ⊢
    linarith
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < ξ k ω :=
    ae_all_iff.2 fun k => ae_of_ae_map (hξm k).aemeasurable ((hlaw k).symm ▸ ae_pos_logTailLaw)
  have hbound : ∀ n : ℕ, μ {ω | backIter halfStep n (fun k => ξ k ω) 0 ≤ M} ≤
      ENNReal.ofReal (((m : ℝ) - 1) / (n + m - 1)) := by
    intro n
    calc μ {ω | backIter halfStep n (fun k => ξ k ω) 0 ≤ M}
        ≤ μ (⋂ j ∈ Finset.range n, ξ j ⁻¹' Iic (Real.exp (j + m))) := by
          refine measure_mono_ae (hpos.mono fun ω hω hZ => ?_)
          change backIter halfStep n (fun k => ξ k ω) 0 ≤ M at hZ
          change ω ∈ ⋂ j ∈ Finset.range n, ξ j ⁻¹' Iic (Real.exp (j + m))
          simp only [mem_iInter, mem_preimage, mem_Iic]
          intro j hj
          rw [backIter_halfStep] at hZ
          have h1 : ξ j ω / 2 ^ j ≤ M := (Finset.single_le_sum
            (f := fun i => ξ i ω / 2 ^ i) (fun i _ => div_nonneg (hω i).le (by positivity))
            hj).trans hZ
          have h2 : ξ j ω ≤ 2 ^ j * M := by
            rwa [div_le_iff₀ (by positivity), mul_comm] at h1
          have h3 : (2 : ℝ) ^ j ≤ Real.exp j := by
            rw [← Real.exp_one_pow]
            have := Real.add_one_le_exp 1
            exact pow_le_pow_left₀ zero_le_two (by linarith) j
          calc ξ j ω ≤ 2 ^ j * M := h2
            _ ≤ Real.exp j * Real.exp m := mul_le_mul h3 hMm (le_trans ?_ h1)
              (Real.exp_pos _).le
            _ = Real.exp (j + m) := (Real.exp_add _ _).symm
          exact div_nonneg (hω j).le (by positivity)
      _ = ∏ j ∈ Finset.range n, μ (ξ j ⁻¹' Iic (Real.exp (j + m))) :=
          hξ.measure_inter_preimage_eq_mul _ (sets := fun j => Iic (Real.exp (j + m)))
            fun _ _ => measurableSet_Iic
      _ = ∏ j ∈ Finset.range n, ENNReal.ofReal (1 - 1 / ((j : ℝ) + m)) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          have hj : (1 : ℝ) ≤ j + m := by
            have := Nat.cast_nonneg (α := ℝ) j
            linarith
          rw [← Measure.map_apply (hξm j) measurableSet_Iic, hlaw, logTailLaw_Iic_exp hj]
      _ = ENNReal.ofReal (∏ j ∈ Finset.range n, (1 - 1 / ((j : ℝ) + m))) := by
          refine (ENNReal.ofReal_prod_of_nonneg fun j _ => ?_).symm
          have := Nat.cast_nonneg (α := ℝ) j
          rw [sub_nonneg, div_le_one (by linarith)]
          linarith
      _ = ENNReal.ofReal (((m : ℝ) - 1) / (n + m - 1)) := by rw [prod_one_sub_one_div m hm2]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (((m : ℝ) - 1) / (n + m - 1))) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
    refine tendsto_atTop_add_const_right _ _ ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    hbound

/-- The chain `X_n = fwdIter halfStep n ξ 0` is measurable. -/
lemma measurable_fwdIter_halfStep (hξm : ∀ i, Measurable (ξ i)) (n : ℕ) :
    Measurable fun ω => fwdIter halfStep n (fun k => ξ k ω) 0 :=
  (measurable_fwdIter measurable_halfStep n 0).comp
    (measurable_pi_lambda (fun ω (k : ℕ) => ξ k ω) hξm)

/-- **The forward chain escapes to infinity** (Giles 2015, §10.1, p. 61, counterexample to
l. 2716–2717: "it is known that the distribution of `X_n` converges weakly to that of a limit
random variable `X_∞`"): for the
chain `X_0 = 0`, `X_{n+1} = X_n/2 + ξ_n` with independent noises of law `logTailLaw`,
`P(X_n ≤ M) → 0` for every `M`: `X_n` has the law of the chain started `n` steps in the past
(`map_backIter_eq_map_fwdIter`), which escapes by `tendsto_measure_backIter_halfStep_le`. -/
theorem tendsto_measure_fwdIter_halfStep_le (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = logTailLaw) (M : ℝ) :
    Tendsto (fun n => μ {ω | fwdIter halfStep n (fun k => ξ k ω) 0 ≤ M}) atTop (𝓝 0) := by
  refine (tendsto_measure_backIter_halfStep_le hξ hξm hlaw M).congr fun n => ?_
  have hB : Measurable fun ω => backIter halfStep n (fun k => ξ k ω) 0 :=
    (measurable_backIter_shift measurable_halfStep ξ n 0 (U := fun _ => (0 : ℝ))
      measurable_const).mono (noiseFrom_le hξm _) le_rfl
  change μ ((fun ω => backIter halfStep n (fun k => ξ k ω) 0) ⁻¹' Iic M) =
    μ ((fun ω => fwdIter halfStep n (fun k => ξ k ω) 0) ⁻¹' Iic M)
  rw [← Measure.map_apply hB measurableSet_Iic,
    ← Measure.map_apply (measurable_fwdIter_halfStep hξm n) measurableSet_Iic,
    map_backIter_eq_map_fwdIter measurable_halfStep hξ hξm hlaw n 0]

/-- **The laws of the chain are not tight** (Giles 2015, §10.1, p. 61, counterexample to
l. 2716–2717: "it is known that the distribution of `X_n` converges weakly to that of a limit
random variable `X_∞`"): for the
chain `X_0 = 0`, `X_{n+1} = X_n/2 + ξ_n` with independent noises of law `logTailLaw`,
`P(X_n > M) → 1` for every `M`, although the step contracts on average
(`halfStep_contracting`). -/
theorem tendsto_measure_lt_fwdIter_halfStep (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = logTailLaw) (M : ℝ) :
    Tendsto (fun n => μ {ω | M < fwdIter halfStep n (fun k => ξ k ω) 0}) atTop (𝓝 1) := by
  have h := ENNReal.Tendsto.sub tendsto_const_nhds
    (tendsto_measure_fwdIter_halfStep_le hξ hξm hlaw M) (Or.inl ENNReal.one_ne_top)
  rw [tsub_zero] at h
  refine h.congr fun n => ?_
  have hm : MeasurableSet {ω | fwdIter halfStep n (fun k => ξ k ω) 0 ≤ M} :=
    measurableSet_le (measurable_fwdIter_halfStep hξm n) measurable_const
  rw [← prob_compl_eq_one_sub hm]
  congr 1
  ext ω
  simp only [mem_compl_iff, Set.mem_ofPred_eq, not_le]

/-- **The distribution of `X_n` does not converge weakly** (Giles 2015, §10.1, p. 61,
l. 2716–2717: "it is known
that the distribution of `X_n` converges weakly to that of a limit random variable `X_∞`" fails
without a moment condition on the first step).  For the chain `X_0 = 0`, `X_{n+1} = X_n/2 + ξ_n`
with independent noises of law `logTailLaw`, which contracts on average for every exponent
(`halfStep_contracting`), no sequence of probability measures equal to the laws of the `X_n`
converges weakly: the mass escapes to `+∞` (`tendsto_measure_fwdIter_halfStep_le`), while by the
portmanteau theorem a weak limit `π` would satisfy `π((−∞, M)) ≤ liminf P(X_n < M) = 0` for every
`M`. -/
theorem markov_no_weak_limit (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = logTailLaw) (π : ProbabilityMeasure ℝ)
    (P : ℕ → ProbabilityMeasure ℝ)
    (hP : ∀ n, (P n : Measure ℝ) = μ.map fun ω => fwdIter halfStep n (fun k => ξ k ω) 0) :
    ¬ Tendsto P atTop (𝓝 π) := by
  intro hlim
  have hzero : ∀ M : ℝ, (π : Measure ℝ) (Iio M) = 0 := by
    intro M
    have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (isOpen_Iio (a := M))
    have hP0 : Tendsto (fun n => (P n : Measure ℝ) (Iio M)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_measure_fwdIter_halfStep_le hξ hξm hlaw M) (fun _ => zero_le) fun n => ?_
      rw [hP n, Measure.map_apply (measurable_fwdIter_halfStep hξm n) measurableSet_Iio]
      exact measure_mono fun ω (hω : _ < M) => le_of_lt hω
    rw [hP0.liminf_eq] at hle
    exact le_antisymm hle zero_le
  have huniv : (univ : Set ℝ) = ⋃ k : ℕ, Iio (k : ℝ) := by
    refine (eq_univ_of_forall fun x => ?_).symm
    obtain ⟨k, hk⟩ := exists_nat_gt x
    exact mem_iUnion.2 ⟨k, hk⟩
  have h1 : (π : Measure ℝ) univ = 0 := by
    rw [huniv]
    exact measure_iUnion_null fun k => hzero k
  simp only [measure_univ, one_ne_zero] at h1

/-- **No limit in distribution** (Giles 2015, §10.1, p. 61, counterexample to l. 2716–2717: "it is
known that the distribution of `X_n` converges weakly to that of a limit random variable `X_∞`"), in
the form of the conclusion of `tendstoInDistribution_fwdIter`: for the chain `X_0 = 0`,
`X_{n+1} = X_n/2 + ξ_n` with independent noises of law `logTailLaw`, there is no random variable
`X_∞`, on any probability space, such that `X_n` converges to `X_∞` in distribution. -/
theorem not_tendstoInDistribution_fwdIter_halfStep (hξ : iIndepFun ξ μ)
    (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = logTailLaw) {Ω' : Type*}
    [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ'] (X : Ω' → ℝ) :
    ¬ TendstoInDistribution (fun n ω => fwdIter halfStep n (fun k => ξ k ω) 0) atTop X
      (fun _ => μ) μ' := fun h =>
  markov_no_weak_limit hξ hξm hlaw _ _ (fun _ => rfl) h.tendsto

end escape

/-! ### The hypotheses are satisfiable, and `hc` cannot be dropped -/

/-- **Independent noises of law `logTailLaw` exist** (so the hypotheses of
`markov_no_weak_limit` are satisfiable; Giles 2015, §10.1, p. 61, counterexample to
l. 2716–2717: "it is known that the distribution of `X_n` converges weakly to that of a limit
random variable `X_∞`"): the coordinates of the product
space `(ℝ^ℕ, logTailLaw^⊗ℕ)`. -/
theorem exists_iid_logTailLaw :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ξ : ℕ → Ω → ℝ), iIndepFun ξ μ ∧ (∀ i, Measurable (ξ i)) ∧
        ∀ i, μ.map (ξ i) = logTailLaw := by
  have := isProbabilityMeasure_logTailLaw
  exact ⟨ℕ → ℝ, inferInstance, Measure.infinitePi fun _ => logTailLaw, inferInstance,
    fun k ω => ω k, iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id,
    fun i => measurable_pi_apply i, fun i => Measure.infinitePi_map_eval _ i⟩

/-- **The moment hypothesis `hc` of `tendstoInDistribution_fwdIter` cannot be dropped** (Giles 2015,
§10.1, p. 61, l. 2716–2717: "it is known that the distribution of `X_n` converges weakly" under the
contraction on average alone).  The statement of `tendstoInDistribution_fwdIter` without
`hc : E[d(x₀, φ(x₀, ξ))^p] < ∞`, even on `α = E = ℝ` and with the weaker conclusion that some `X_∞`
is a limit in distribution, is false: the chain `X_{n+1} = X_n/2 + ξ_n`, `X_0 = 0`, with noises of
law `logTailLaw` contracts on average with `p = 1`, `ρ = 1/2` (`γ = ½`), but has no limit in
distribution. -/
theorem hc_cannot_be_dropped :
    ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ν : Measure ℝ) (φ : ℝ → ℝ → ℝ) (ξ : ℕ → Ω → ℝ),
        (Measurable fun q : ℝ × ℝ => φ q.1 q.2) → ∀ p ρ : ℝ, 0 < p → 0 ≤ ρ → ρ < 1 →
        (∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ p) ∂ν ≤
          ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p)) →
        iIndepFun ξ μ → (∀ i, Measurable (ξ i)) → (∀ i, μ.map (ξ i) = ν) → ∀ x₀ : ℝ,
        ∃ X : Ω → ℝ, TendstoInDistribution (fun n ω => fwdIter φ n (fun k => ξ k ω) x₀) atTop X
          (fun _ => μ) μ := by
  intro h
  obtain ⟨Ω, _, μ, _, ξ, hξ, hξm, hlaw⟩ := exists_iid_logTailLaw
  have := isProbabilityMeasure_logTailLaw
  obtain ⟨hρ0, hρ1, hφ⟩ := halfStep_contracting logTailLaw one_pos
  obtain ⟨X, hX⟩ := h Ω μ logTailLaw halfStep ξ measurable_halfStep 1 _ one_pos hρ0 hρ1 hφ hξ
    hξm hlaw 0
  exact not_tendstoInDistribution_fwdIter_halfStep hξ hξm hlaw μ X hX

end MLMC
