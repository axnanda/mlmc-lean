import MlmcLean.KarhunenLoeveLimit
import MlmcLean.MarkovNoWeakLimit
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The joint law of the Karhunen–Loève field, and completeness in §10.1 (Giles 2015, §7.2, §10.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015)
(`docs/giles2015.txt`; the line numbers below refer to it).

**§7.2 "Elliptic SPDE", pp. 51–53, row G7.2-02.**  The paper models the diffusivity as "a
lognormal random field, i.e. `log κ` is a Gaussian field with a uniform mean (which we will take
to be zero for simplicity) and a covariance function of the general form `R(x, y) = r(x − y)`"
(l. 2219–2220, 2254–2255), sampled by "a Karhunen-Loève expansion:
`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`, where `θ_n` are the eigenvalues of `R(x, y)` …, `f_n`
are the corresponding eigenfunctions, and `ξ_n` are independent unit Normal random variables"
(l. 2255–2262).  `MlmcLean.KarhunenLoeveLimit` defines the full series `klLimit θ f z x` (with
`ξ_n = z n` under `stdNormalSeq = N(0, 1)^{⊗ℕ}`) and proves, with Mercer's expansion
`R(x_i, x_j) = ∑ θ_n f_n(x_i) f_n(x_j)` as `HasSum` hypotheses, that `(Y(x_1), …, Y(x_m))` is
jointly Gaussian with mean `0` and covariance `R(x_i, x_j)`.  Here the law is identified with
Mathlib's `multivariateGaussian`:

* `posSemidef_klCov`: the matrix `(R(x_i, x_j))_{ij}` is positive semidefinite (it is symmetric
  and `∑_{i,j} a_i a_j R(x_i, x_j) = ∑_n θ_n (∑_i a_i f_n(x_i))² ≥ 0`).
* `map_klLimit_eq_multivariateGaussian`: the law of `(Y(x_i))_i` in `EuclideanSpace ℝ ι` is
  `multivariateGaussian 0 (R(x_i, x_j))_{ij}` (equal characteristic functions);
  `map_klLimit_pi_eq_multivariateGaussian` is the same statement on `ι → ℝ`.
* `klLimit_multivariateGaussian_satisfiable`: the hypotheses are satisfiable (the witness of
  `kl_hypotheses_satisfiable`, for which the covariance matrix is `diag(θ_{x_i})` on distinct
  points).

**§10.1 "Markov chains and limiting distributions", p. 61, row G10.1-04.**  "the Markov chain
`{X_n}` in a metric space with metric `d` is defined by `X_0 = x`, `X_{n+1} = φ_n(X_n)`, `n ≥ 0`,
where `{φ_n}` is a sequence of iid random functions.  Furthermore, it is assumed that the `φ`'s are
contracting on average in the sense that `sup_{x≠y} E[(d(φ_n(x), φ_n(y))/d(x, y))^{2γ}] < 1` for
some `γ ∈ (0, 1)`.  Under these conditions, it is known that the distribution of `X_n` converges
weakly to that of a limit random variable `X_∞`" (l. 2707–2717).
`tendstoInDistribution_fwdIter` (`MlmcLean.MarkovLimit`) proves this in a complete separable
metric space with a moment hypothesis on one step, and `hc_cannot_be_dropped`
(`MlmcLean.MarkovNoWeakLimit`) shows the moment hypothesis is needed.  Here completeness is shown
to be needed too.  On the incomplete space `α = (0, ∞)` (`Set.Ioi 0` with the induced metric and
the Borel σ-algebra) the deterministic step `φ(x, e) = x/2` (`posHalfStep`) contracts on average
with `ρ = 2^{−p}` for every `p > 0` and has every moment `E[d(x₀, φ(x₀, ξ))^p] = (x₀/2)^p < ∞`,
but `X_n = x₀/2ⁿ` has the laws `δ_{x₀/2ⁿ}`, whose only candidate limit `δ_0` lives outside `α`:

* `posHalfStep_contracting`, `lintegral_posHalfStep_ne_top`: the hypotheses `hφ` and `hc` of
  `tendstoInDistribution_fwdIter` hold, for every noise law and every `p > 0`.
* `coe_fwdIter_posHalfStep`, `map_fwdIter_posHalfStep`: `X_n = x₀/2ⁿ`, with law `δ_{x₀/2ⁿ}`.
* `posHalfStep_no_weak_limit`, `not_tendstoInDistribution_fwdIter_posHalfStep`: no probability
  measure on `α` is the weak limit of the laws of `X_n` (portmanteau: a limit `π` would give
  `π({y > 1/(k+1)}) ≤ liminf P(X_n > 1/(k+1)) = 0` for every `k`), so `X_n` has no limit in
  distribution.
* `not_completeSpace_Ioi_zero`: `(0, ∞)` is not complete.
* `completeSpace_cannot_be_dropped`: the statement of `tendstoInDistribution_fwdIter` without
  `CompleteSpace α` (keeping `hc`, and with the weaker conclusion that some `X_∞` is a limit in
  distribution) is false.

**Deviations.**  As in `MlmcLean.KarhunenLoeveLimit`, Mercer's theorem stays a hypothesis and a
general covariance `R` replaces the stationary `r(x − y)`.  The noise law in
`completeSpace_cannot_be_dropped` is `δ_0` (the step ignores the noise).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MLMC

/-! ### The joint law of the Karhunen–Loève limit field -/

section KarhunenLoeve

variable {D : Type*}

/-- **The quadratic form of the covariance as a series** (Giles 2015, §7.2, p. 53, l. 2255–2262:
"`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`, where `θ_n` are the eigenvalues of `R(x, y)`"): under
Mercer's expansion `R(x_i, x_j) = ∑ θ_n f_n(x_i) f_n(x_j)` at finitely many points,
`∑_{i,j} a_i a_j R(x_i, x_j) = ∑_n θ_n (∑_i a_i f_n(x_i))²`. -/
lemma kl_hasSum_quadForm {ι : Type*} [Fintype ι] {θ : ℕ → ℝ} {f : ℕ → D → ℝ} {R : D → D → ℝ}
    (x : ι → D) (hR : ∀ i j, HasSum (fun n => θ n * f n (x i) * f n (x j)) (R (x i) (x j)))
    (a : ι → ℝ) :
    HasSum (fun n => θ n * (∑ i, a i * f n (x i)) ^ 2)
      (∑ i, ∑ j, a i * a j * R (x i) (x j)) := by
  have h := hasSum_sum fun i (_ : i ∈ Finset.univ) =>
    hasSum_sum fun j (_ : j ∈ Finset.univ) => (hR i j).mul_left (a i * a j)
  refine h.congr_fun fun n => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `a ⬝ᵥ S a = ∑_{i,j} a_i a_j S_{ij}` for `S = (R(x_i, x_j))_{ij}` (Giles 2015, §7.2, p. 53,
l. 2254–2255: "a covariance function of the general form `R(x, y)`"). -/
lemma kl_dotProduct_mulVec {ι : Type*} [Fintype ι] {R : D → D → ℝ} (x : ι → D) (a : ι → ℝ) :
    a ⬝ᵥ (Matrix.of fun i j => R (x i) (x j)).mulVec a =
      ∑ i, ∑ j, a i * a j * R (x i) (x j) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The covariance matrix of the field is positive semidefinite** (Giles 2015, §7.2, pp. 51–53,
l. 2219–2220, 2254–2255: "`log κ` is a Gaussian field with a uniform mean (which we will take to
be zero for simplicity) and a covariance function of the general form `R(x, y) = r(x − y)`").  For
`θ_n ≥ 0` and finitely many points `x_i` where Mercer's expansion
`R(x_i, x_j) = ∑ θ_n f_n(x_i) f_n(x_j)` holds, the matrix `(R(x_i, x_j))_{ij}` is symmetric and
`∑_{i,j} a_i a_j R(x_i, x_j) = ∑_n θ_n (∑_i a_i f_n(x_i))² ≥ 0`. -/
theorem posSemidef_klCov {ι : Type*} [Fintype ι] {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n)
    {f : ℕ → D → ℝ} {R : D → D → ℝ} (x : ι → D)
    (hR : ∀ i j, HasSum (fun n => θ n * f n (x i) * f n (x j)) (R (x i) (x j))) :
    (Matrix.of fun i j => R (x i) (x j)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun a => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply, star_trivial]
    exact (hR j i).unique ((hR i j).congr_fun fun n => by ring)
  · rw [star_trivial, kl_dotProduct_mulVec]
    exact (kl_hasSum_quadForm x hR a).nonneg fun n => mul_nonneg (hθ n) (sq_nonneg _)

/-- **The joint law of the untruncated field is `multivariateGaussian 0 (R(x_i, x_j))`** (Giles
2015, §7.2, pp. 51–53, l. 2219–2220, 2254–2255: "`log κ` is a Gaussian field with a uniform mean
(which we will take to be zero for simplicity) and a covariance function of the general form
`R(x, y) = r(x − y)`", and l. 2255–2262: "`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`, where `θ_n`
are the eigenvalues of `R(x, y)` …, `f_n` are the corresponding eigenfunctions, and `ξ_n` are
independent unit Normal random variables").  For `θ_n ≥ 0` and finitely many points `x_i`
(indexed by a finite type `ι`, e.g. `Fin m`) where Mercer's expansion
`R(x_i, x_j) = ∑ θ_n f_n(x_i) f_n(x_j)` holds, the law of the vector `(Y(x_i))_i` of values of the
full Karhunen–Loève series, as an element of `EuclideanSpace ℝ ι`, is the multivariate Gaussian
with mean `0` and covariance matrix `(R(x_i, x_j))_{ij}` (which is positive semidefinite,
`posSemidef_klCov`).  Both characteristic functions are `t ↦ exp(−∑_{i,j} t_i t_j R(x_i, x_j)/2)`:
`⟪Y, t⟫ = ∑ t_i Y(x_i) ∼ N(0, ∑_{i,j} t_i t_j R(x_i, x_j))`. -/
theorem map_klLimit_eq_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ} {R : D → D → ℝ} (x : ι → D)
    (hR : ∀ i j, HasSum (fun n => θ n * f n (x i) * f n (x j)) (R (x i) (x j))) :
    stdNormalSeq.map (fun z => WithLp.toLp 2 fun k => klLimit θ f z (x k)) =
      multivariateGaussian 0 (Matrix.of fun i j => R (x i) (x j)) := by
  have hS := posSemidef_klCov hθ x hR
  have hsx : ∀ i, Summable fun n => θ n * f n (x i) ^ 2 := fun i =>
    (hR i i).summable.congr fun n => by ring
  have hYi : ∀ i, AEMeasurable (fun z => klLimit θ f z (x i)) stdNormalSeq := fun i =>
    (klLimit_tendsto hθ (hsx i)).2.1.aestronglyMeasurable.aemeasurable
  have hV : AEMeasurable (fun z => WithLp.toLp 2 fun k => klLimit θ f z (x k)) stdNormalSeq :=
    (WithLp.measurable_toLp 2 _).comp_aemeasurable (aemeasurable_pi_lambda _ hYi)
  have := Measure.isProbabilityMeasure_map hV
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_multivariateGaussian hS, charFun_eq_charFunDual_toDualMap,
    charFunDual_eq_charFun_map_one, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hV]
  have hL : (⇑(InnerProductSpace.toDualMap ℝ _ t) ∘
      fun z => WithLp.toLp 2 fun k => klLimit θ f z (x k)) =
      fun z => ∑ i, t i * klLimit θ f z (x i) := by
    funext z
    simp [PiLp.inner_apply, mul_comm]
  rw [hL, map_sum_klLimit_eq_gaussianReal hθ x hR, charFun_gaussianReal]
  have hq := (kl_hasSum_quadForm x hR t.ofLp).nonneg fun n => mul_nonneg (hθ n) (sq_nonneg _)
  rw [kl_dotProduct_mulVec, Real.coe_toNNReal _ hq, inner_zero_right]
  congr 1
  push_cast
  ring

/-- **The joint law on `ι → ℝ`** (Giles 2015, §7.2, pp. 51–53, l. 2220: "`log κ` is a Gaussian
field", and l. 2257–2259: "`log κ(x, ω) = ∑_{n≥0} √θ_n ξ_n(ω) f_n(x)`"): with the hypotheses of
`map_klLimit_eq_multivariateGaussian`, the law of `(Y(x_i))_i` on the plain product `ι → ℝ` is the
image of `multivariateGaussian 0 (R(x_i, x_j))_{ij}` under the identification
`EuclideanSpace ℝ ι → (ι → ℝ)`. -/
theorem map_klLimit_pi_eq_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ℕ → ℝ} (hθ : ∀ n, 0 ≤ θ n) {f : ℕ → D → ℝ} {R : D → D → ℝ} (x : ι → D)
    (hR : ∀ i j, HasSum (fun n => θ n * f n (x i) * f n (x j)) (R (x i) (x j))) :
    stdNormalSeq.map (fun z k => klLimit θ f z (x k)) =
      (multivariateGaussian 0 (Matrix.of fun i j => R (x i) (x j))).map WithLp.ofLp := by
  have hsx : ∀ i, Summable fun n => θ n * f n (x i) ^ 2 := fun i =>
    (hR i i).summable.congr fun n => by ring
  have hV : AEMeasurable (fun z => WithLp.toLp 2 fun k => klLimit θ f z (x k)) stdNormalSeq :=
    (WithLp.measurable_toLp 2 _).comp_aemeasurable (aemeasurable_pi_lambda _ fun i =>
      (klLimit_tendsto hθ (hsx i)).2.1.aestronglyMeasurable.aemeasurable)
  rw [← map_klLimit_eq_multivariateGaussian hθ x hR,
    AEMeasurable.map_map_of_aemeasurable (WithLp.measurable_ofLp 2 _).aemeasurable hV]
  rfl

/-- **The hypotheses of `map_klLimit_eq_multivariateGaussian` are satisfiable** (Giles 2015,
§7.2, p. 53, l. 2255–2262: "`θ_n` are the eigenvalues of `R(x, y)` …, `f_n` are the corresponding
eigenfunctions, and `ξ_n` are independent unit Normal random variables").  On `D = ℕ`, with the
eigenfunctions `f_n = 1_{{n}}` of `kl_hypotheses_satisfiable` and the diagonal kernel
`R(x, y) = θ_x δ_{xy}`, Mercer's expansion holds at all points for every `θ ≥ 0`, and the law of
`(Y(x_i))_i` is `multivariateGaussian 0 (θ_{x_i} δ_{x_i x_j})_{ij}`. -/
theorem klLimit_multivariateGaussian_satisfiable {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ f : ℕ → ℕ → ℝ, ∀ θ : ℕ → ℝ, (∀ n, 0 ≤ θ n) → ∀ x : ι → ℕ,
      (∀ i j, HasSum (fun n => θ n * f n (x i) * f n (x j))
        (if x i = x j then θ (x i) else 0)) ∧
      stdNormalSeq.map (fun z => WithLp.toLp 2 fun k => klLimit θ f z (x k)) =
        multivariateGaussian 0 (Matrix.of fun i j => if x i = x j then θ (x i) else 0) := by
  obtain ⟨-, f, -, -, -, hf⟩ := kl_hypotheses_satisfiable
  exact ⟨f, fun θ hθ x => ⟨fun i j => hf θ (x i) (x j),
    map_klLimit_eq_multivariateGaussian hθ (R := fun a b => if a = b then θ a else 0) x
      fun i j => hf θ (x i) (x j)⟩⟩

end KarhunenLoeve

/-! ### Completeness is needed for the weak limit of a contracting chain -/

/-- **The halving step on `(0, ∞)`** (for the counterexample to Giles 2015, §10.1, p. 61,
l. 2707–2717, with an incomplete state space): `φ(x, e) = x/2`, the same for every noise `e`. -/
noncomputable def posHalfStep {E : Type*} (x : Ioi (0 : ℝ)) (_e : E) : Ioi (0 : ℝ) :=
  ⟨(x : ℝ) / 2, show (0 : ℝ) < (x : ℝ) / 2 from half_pos x.2⟩

/-- The value of the halving step is `x/2` (Giles 2015, §10.1, p. 61, l. 2707–2709:
"`X_0 = x`, `X_{n+1} = φ_n(X_n)`, `n ≥ 0`"). -/
lemma coe_posHalfStep {E : Type*} (x : Ioi (0 : ℝ)) (e : E) :
    (posHalfStep x e : ℝ) = x / 2 := rfl

/-- The halving step is jointly measurable (the hypothesis `hφm` of
`tendstoInDistribution_fwdIter`; Giles 2015, §10.1, p. 61, l. 2709–2710: "`{φ_n}` is a sequence
of iid random functions"). -/
lemma measurable_posHalfStep {E : Type*} [MeasurableSpace E] :
    Measurable fun q : Ioi (0 : ℝ) × E => posHalfStep q.1 q.2 :=
  ((measurable_subtype_coe.comp measurable_fst).div_const 2).subtype_mk

/-- The halving step halves distances, whatever the noises (Giles 2015, §10.1, p. 61,
l. 2711–2716: "the `φ`'s are contracting on average"). -/
lemma dist_posHalfStep {E : Type*} (x y : Ioi (0 : ℝ)) (e e' : E) :
    dist (posHalfStep x e) (posHalfStep y e') = dist x y / 2 := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq, coe_posHalfStep,
    coe_posHalfStep, show (x : ℝ) / 2 - (y : ℝ) / 2 = ((x : ℝ) - y) / 2 by ring, abs_div,
    abs_two]

/-- One halving step moves `x` by `x/2` (Giles 2015, §10.1, p. 61, l. 2707–2709:
"`X_{n+1} = φ_n(X_n)`"). -/
lemma dist_self_posHalfStep {E : Type*} (x : Ioi (0 : ℝ)) (e : E) :
    dist x (posHalfStep x e) = x / 2 := by
  have hx : (0 : ℝ) < x := x.2
  rw [Subtype.dist_eq, Real.dist_eq, coe_posHalfStep, show (x : ℝ) - x / 2 = x / 2 by ring,
    abs_of_pos (half_pos hx)]

/-- **The halving step contracts on average** (the hypothesis `hφ` of
`tendstoInDistribution_fwdIter`; Giles 2015, §10.1, p. 61, l. 2711–2716: "it is assumed that the
`φ`'s are contracting on average in the sense that
`sup_{x≠y} E[(d(φ_n(x), φ_n(y))/d(x, y))^{2γ}] < 1` for some `γ ∈ (0, 1)`"): on `(0, ∞)`, for every
noise law `ν` and every `p > 0`, `E[d(φ(x, ξ), φ(y, ξ))^p] = 2^{−p} d(x, y)^p` with
`0 ≤ 2^{−p} < 1`. -/
theorem posHalfStep_contracting {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] {p : ℝ} (hp : 0 < p) :
    0 ≤ (2 : ℝ) ^ (-p) ∧ (2 : ℝ) ^ (-p) < 1 ∧
      ∀ x y : Ioi (0 : ℝ),
        ∫⁻ e, ENNReal.ofReal (dist (posHalfStep x e) (posHalfStep y e) ^ p) ∂ν ≤
          ENNReal.ofReal ((2 : ℝ) ^ (-p)) * ENNReal.ofReal (dist x y ^ p) := by
  refine ⟨Real.rpow_nonneg zero_le_two _,
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hp), fun x y => le_of_eq ?_⟩
  have h : ∀ e : E, dist (posHalfStep x e) (posHalfStep y e) ^ p =
      (2 : ℝ) ^ (-p) * dist x y ^ p := by
    intro e
    rw [dist_posHalfStep, Real.div_rpow dist_nonneg zero_le_two, Real.rpow_neg zero_le_two,
      div_eq_inv_mul]
  simp_rw [h]
  rw [lintegral_const, measure_univ, mul_one,
    ENNReal.ofReal_mul (Real.rpow_nonneg zero_le_two _)]

/-- **The first step has every moment** (the hypothesis `hc` of `tendstoInDistribution_fwdIter`
holds; Giles 2015, §10.1, p. 61, l. 2716–2717: "Under these conditions, it is known that the
distribution of `X_n` converges weakly to that of a limit random variable `X_∞`"): for every noise
law `ν`, every `x₀ ∈ (0, ∞)` and every `p`, `E[d(x₀, φ(x₀, ξ))^p] = (x₀/2)^p < ∞` (a hypothesis
the paper does not state). -/
theorem lintegral_posHalfStep_ne_top {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (x₀ : Ioi (0 : ℝ)) (p : ℝ) :
    ∫⁻ e, ENNReal.ofReal (dist x₀ (posHalfStep x₀ e) ^ p) ∂ν ≠ ∞ := by
  simp_rw [dist_self_posHalfStep]
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_ne_top

/-- **The chain is `X_n = x₀/2ⁿ`** (Giles 2015, §10.1, p. 61, l. 2707–2709: "`X_0 = x`,
`X_{n+1} = φ_n(X_n)`, `n ≥ 0`"), for every noise sequence. -/
theorem coe_fwdIter_posHalfStep {E : Type*} (n : ℕ) (e : ℕ → E) (x₀ : Ioi (0 : ℝ)) :
    ((fwdIter posHalfStep n e x₀ : Ioi (0 : ℝ)) : ℝ) = x₀ / 2 ^ n := by
  induction n with
  | zero => rw [fwdIter_zero, pow_zero, div_one]
  | succ n ih => rw [fwdIter_succ, coe_posHalfStep, ih, pow_succ, div_div]

/-- The chain of the halving step does not depend on the noises (Giles 2015, §10.1, p. 61,
l. 2707–2710: "`X_0 = x`, `X_{n+1} = φ_n(X_n)`, `n ≥ 0` where `{φ_n}` is a sequence of iid random
functions"). -/
lemma fwdIter_posHalfStep_congr {E : Type*} (n : ℕ) (e e' : ℕ → E) (x₀ : Ioi (0 : ℝ)) :
    fwdIter posHalfStep n e x₀ = fwdIter posHalfStep n e' x₀ :=
  Subtype.ext (by rw [coe_fwdIter_posHalfStep, coe_fwdIter_posHalfStep])

section noLimit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {E : Type*}

/-- **The law of `X_n` is `δ_{x₀/2ⁿ}`** (Giles 2015, §10.1, p. 61, l. 2716–2717: "the
distribution of `X_n`"): for any noises `ξ_k`, the chain of the halving step is deterministic, and
its law is the Dirac mass at `fwdIter posHalfStep n e x₀ = x₀/2ⁿ` (any noise sequence `e`). -/
theorem map_fwdIter_posHalfStep (ξ : ℕ → Ω → E) (x₀ : Ioi (0 : ℝ)) (n : ℕ) (e : ℕ → E) :
    μ.map (fun ω => fwdIter posHalfStep n (fun k => ξ k ω) x₀) =
      Measure.dirac (fwdIter posHalfStep n e x₀) := by
  have h : (fun ω => fwdIter posHalfStep n (fun k => ξ k ω) x₀) =
      fun _ => fwdIter posHalfStep n e x₀ :=
    funext fun ω => fwdIter_posHalfStep_congr n _ e x₀
  rw [h, Measure.map_const, measure_univ, one_smul]

omit [IsProbabilityMeasure μ] in
/-- **The distribution of `X_n` does not converge weakly in the incomplete space `(0, ∞)`**
(Giles 2015, §10.1, p. 61, l. 2707–2717: "the Markov chain `{X_n}` in a metric space with metric
`d` … it is known that the distribution of `X_n` converges weakly to that of a limit random
variable `X_∞`" fails without completeness).  For the chain `X_0 = x₀`, `X_{n+1} = X_n/2` on
`(0, ∞)`, which contracts on average (`posHalfStep_contracting`) and whose first step has every
moment (`lintegral_posHalfStep_ne_top`), no sequence of probability measures equal to the laws
`δ_{x₀/2ⁿ}` of the `X_n` converges weakly to a probability measure on `(0, ∞)`: by the
portmanteau theorem a limit `π` would satisfy `π({y > 1/(k+1)}) ≤ liminf P(X_n > 1/(k+1)) = 0`
for every `k`, so `π((0, ∞)) = 0`. -/
theorem posHalfStep_no_weak_limit (ξ : ℕ → Ω → E) (x₀ : Ioi (0 : ℝ))
    (π : ProbabilityMeasure (Ioi (0 : ℝ))) (P : ℕ → ProbabilityMeasure (Ioi (0 : ℝ)))
    (hP : ∀ n, (P n : Measure (Ioi (0 : ℝ))) =
      μ.map fun ω => fwdIter posHalfStep n (fun k => ξ k ω) x₀) :
    ¬ Tendsto P atTop (𝓝 π) := by
  intro hlim
  have hseq : Tendsto (fun n : ℕ => (x₀ : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hzero : ∀ k : ℕ, (π : Measure (Ioi (0 : ℝ))) {y | 1 / ((k : ℝ) + 1) < y} = 0 := by
    intro k
    have hU : IsOpen {y : Ioi (0 : ℝ) | 1 / ((k : ℝ) + 1) < y} :=
      isOpen_lt continuous_const continuous_subtype_val
    have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hU
    have hev : ∀ᶠ n in atTop,
        (P n : Measure (Ioi (0 : ℝ))) {y | 1 / ((k : ℝ) + 1) < y} = 0 := by
      filter_upwards [hseq.eventually
        (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))] with n hn
      have hm : Measurable fun ω => fwdIter posHalfStep n (fun k => ξ k ω) x₀ :=
        measurable_const' fun ω ω' => fwdIter_posHalfStep_congr n _ _ x₀
      rw [hP n, Measure.map_apply hm hU.measurableSet]
      convert measure_empty (μ := μ)
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, coe_fwdIter_posHalfStep, mem_empty_iff_false,
        iff_false, not_lt]
      exact hn.le
    have hP0 : Tendsto (fun n => (P n : Measure (Ioi (0 : ℝ))) {y | 1 / ((k : ℝ) + 1) < y})
        atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
    rw [hP0.liminf_eq] at hle
    exact le_antisymm hle zero_le
  have huniv : (univ : Set (Ioi (0 : ℝ))) =
      ⋃ k : ℕ, {y : Ioi (0 : ℝ) | 1 / ((k : ℝ) + 1) < y} := by
    refine (eq_univ_of_forall fun y => ?_).symm
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < y from y.2)
    exact mem_iUnion.2 ⟨k, hk⟩
  have h1 : (π : Measure (Ioi (0 : ℝ))) univ = 0 := by
    rw [huniv]
    exact measure_iUnion_null hzero
  simp only [measure_univ, one_ne_zero] at h1

/-- **No limit in distribution in `(0, ∞)`** (Giles 2015, §10.1, p. 61, l. 2707–2717: "the Markov
chain `{X_n}` in a metric space with metric `d` … it is known that the distribution of `X_n`
converges weakly to that of a limit random variable `X_∞`"), in the form of the conclusion of
`tendstoInDistribution_fwdIter`: for the chain `X_0 = x₀`, `X_{n+1} = X_n/2` on `(0, ∞)`, driven
by any noises, there is no `(0, ∞)`-valued random variable `X_∞`, on any probability space, such
that `X_n` converges to `X_∞` in distribution. -/
theorem not_tendstoInDistribution_fwdIter_posHalfStep (ξ : ℕ → Ω → E) (x₀ : Ioi (0 : ℝ))
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (X : Ω' → Ioi (0 : ℝ)) :
    ¬ TendstoInDistribution (fun n ω => fwdIter posHalfStep n (fun k => ξ k ω) x₀) atTop X
      (fun _ => μ) μ' := fun h =>
  posHalfStep_no_weak_limit ξ x₀ _ _ (fun _ => rfl) h.tendsto

end noLimit

/-- **The state space of the counterexample is not complete** (Giles 2015, §10.1, p. 61,
l. 2707–2708: "the Markov chain `{X_n}` in a metric space with metric `d`"): `(0, ∞)` with the
metric of `ℝ` is not a complete space, since it is not closed in `ℝ`. -/
theorem not_completeSpace_Ioi_zero : ¬ CompleteSpace (Ioi (0 : ℝ)) := by
  intro h
  have hc : IsClosed (Ioi (0 : ℝ)) := (completeSpace_coe_iff_isComplete.1 h).isClosed
  have h0 : (0 : ℝ) ∈ Ioi (0 : ℝ) := by
    rw [← hc.closure_eq, closure_Ioi]
    exact mem_Ici.2 le_rfl
  exact lt_irrefl _ (mem_Ioi.1 h0)

/-- **Completeness cannot be dropped from `tendstoInDistribution_fwdIter`** (Giles 2015, §10.1,
p. 61, l. 2707–2717: "the Markov chain `{X_n}` in a metric space with metric `d` … contracting on
average … Under these conditions, it is known that the distribution of `X_n` converges weakly to
that of a limit random variable `X_∞`").  The statement of `tendstoInDistribution_fwdIter` without
`CompleteSpace α`, keeping all its other hypotheses (a separable metric space with its Borel
σ-algebra, a jointly measurable step contracting on average, i.i.d. noises, and the moment
hypothesis `hc : E[d(x₀, φ(x₀, ξ))^p] < ∞`), and with the weaker conclusion that some `X_∞` is a
limit in distribution, is false: on `α = (0, ∞)` the chain `X_{n+1} = X_n/2`, `X_0 = 1`, with
noises of law `δ_0`, contracts on average with `p = 1` (`γ = ½`), `ρ = 1/2` and satisfies `hc`,
but has no limit in distribution, even with the noise space `E = ℝ`. -/
theorem completeSpace_cannot_be_dropped :
    ¬ ∀ (α : Type) [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
        (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ν : Measure ℝ) (φ : α → ℝ → α) (ξ : ℕ → Ω → ℝ),
        (Measurable fun q : α × ℝ => φ q.1 q.2) → ∀ p ρ : ℝ, 0 < p → 0 ≤ ρ → ρ < 1 →
        (∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ p) ∂ν ≤
          ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p)) →
        iIndepFun ξ μ → (∀ i, Measurable (ξ i)) → (∀ i, μ.map (ξ i) = ν) → ∀ x₀ : α,
        ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν ≠ ∞ →
        ∃ X : Ω → α, TendstoInDistribution (fun n ω => fwdIter φ n (fun k => ξ k ω) x₀) atTop X
          (fun _ => μ) μ := by
  intro h
  obtain ⟨hρ0, hρ1, hφ⟩ := posHalfStep_contracting (Measure.dirac (0 : ℝ)) one_pos
  obtain ⟨X, hX⟩ := h (Ioi (0 : ℝ)) (ℕ → ℝ) (Measure.infinitePi fun _ => Measure.dirac 0)
    (Measure.dirac 0) posHalfStep (fun k ω => ω k) measurable_posHalfStep 1 _ one_pos hρ0 hρ1
    hφ (iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id)
    (fun i => measurable_pi_apply i) (fun i => Measure.infinitePi_map_eval _ i)
    ⟨1, mem_Ioi.2 one_pos⟩ (lintegral_posHalfStep_ne_top _ _ 1)
  exact not_tendstoInDistribution_fwdIter_posHalfStep _ _ _ X hX

end MLMC
