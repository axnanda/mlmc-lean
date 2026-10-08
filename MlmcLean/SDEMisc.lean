import MlmcLean.SDEExtras

/-!
# Giles 2015, §5: antithetic MLMC in `d` dimensions, the call option, taming, CDF smoothing

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.3
"Multi-dimensional SDEs" (pp. 39–42), §5.6 "Stiff and highly nonlinear SDEs" (pp. 43–44) and §5.7
"CDF and density estimation" (p. 46).  As in `MlmcLean/SDEExtras.lean`, SDE theory is not
formalised (the strong convergence of the discretisations, the path analysis of the antithetic
estimator of Giles and Szpruch, the moment bounds of Hutzenthaler, Jentzen and Kloeden); what is
proved is every step that follows from it by analysis or probability, with the SDE rates as
explicit hypotheses.

* **§5.3, smooth payoffs of a `d`-dimensional path** (p. 42: "Lengthy analysis proves that the
  average of the fine and antithetic paths is within `O(h)` of the coarse path, and hence the
  multilevel variance is `O(h²)` for smooth payoffs").  The payoff is `f : E → ℝ` on a real normed
  space `E` (for instance `ℝ^d`), with a `K`-Lipschitz derivative `f′`.
  `abs_midpoint_sub_avg_le_fderiv`: `|f(½(a + b)) − ½f(a) − ½f(b)| ≤ (K/8)‖a − b‖²`;
  `abs_antithetic_le_fderiv`, `abs_antithetic_le_midpoint`: two pathwise bounds on
  `½(f(a) + f(b)) − f(c)`; `variance_antithetic_le_fderiv`, `variance_antithetic_le_midpoint`: the
  variance is `O(h²)` when `E‖½(A + B) − C‖² = O(h²)` and the fine–coarse differences `A − C`,
  `B − C` (respectively the fine–antithetic difference `A − B`) have fourth moments `O(h²)`.  These
  extend the scalar `abs_antithetic_le` and `variance_antithetic_le` of `SDEExtras`.
* **§5.3, the European call** (p. 42: "and `O(h^{3/2})` for the standard European call option").
  `abs_call_antithetic_le`: for `g(x) = max(x − K, 0)`,
  `|½(g(a) + g(b)) − g(c)| ≤ |½(a + b) − c| + ¼|a − b| 1{K strictly between a and b}` (the constant
  `¼` is sharp); `variance_call_antithetic_le`: the variance is `O(h^{3/2})` if, given `|A − B|`,
  the average `½(A + B)` has a density bounded by `ρ₀`; `variance_call_antithetic_le_holder`: the
  bound in terms of `P(K between A and B)`, which gives `O(h^{3/2 − 1/(2p)})` from `p`-th moments
  alone.  Such marginal information cannot give `O(h^{3/2})` (counterexample in the docstring).
* **§5.6, super-linear drift** (p. 44: "SDEs such as `dS_t = −S_t³ dt + dW_t`, which have a
  super-linear growth in the drift … This again leads to numerical instability if a uniform
  timestep is used").  For the explicit Euler step `S ↦ S − hS³` (`eulerDriftStep`) the orbit of
  `S` stays within `|S|` if `hS² ≤ 2` (`eulerCubic_bounded`) and grows at least geometrically to
  `∞` if `hS² > 2` (`eulerCubic_growth`, `eulerCubic_tendsto_atTop`): whatever the timestep, large
  values explode, while the solutions of `S′ = −S³` decay.  The tamed step
  `S ↦ S + h b(S)/(1 + h|b(S)|)` (`tamedDriftStep`) "limits the size of the drift term"
  (`abs_tamedDrift_lt`), is a "slight modification" of the explicit step
  (`abs_tamedDriftStep_sub_eulerDriftStep_le`), and keeps every orbit within `max(|S|, 1)`
  (`tamedDriftStep_iterate_bounded`, `tamedCubic_bounded`).  The stochastic statements are in
  `MlmcLean.EulerSuperlinear` (divergence of the Euler–Maruyama moments,
  `emCubic_moment_tendsto_atTop`; moment bounds for the tamed scheme, `tamedPath_integral_abs_le`,
  `tamedCubic_second_moment_le`), `MlmcLean.EulerSuperlinearGeneral` (HJK's general divergence
  theorem) and `MlmcLean.EndToEndInstances` (`tamedCubic_fourth_moment_le`).
* **§5.7, smoothing functions of either sign** (p. 46: "`g(x)` is a continuous function with
  `g(x) = 0` for `x < −1`, and `g(x) = 1` for `x > 1`").  `abs_smoothCDF_sub_le_of_bounded`,
  `tendsto_smoothCDF_of_bounded`, `tendsto_smoothCDF_of_continuous` remove the hypothesis
  `0 ≤ g ≤ 1` of `abs_smoothCDF_sub_le` and `tendsto_smoothCDF` (`SDEExtras`), which the paper does
  not make.
* **§5.7, multi-dimensional outputs** (p. 46: "can also be generalised to multi-dimensional
  outputs").  `tendsto_density_multidim`, `tendsto_density_euclidean`:
  `E[δ^{−d} g((x − P)/δ)] → ρ(x)` as `δ → 0⁺` for a `d`-dimensional output `P` whose density `ρ` is
  continuous at `x`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MLMC

/-! ### §5.3: smooth payoffs of a multi-dimensional path -/

section antithetic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
  {f' : E → E →L[ℝ] ℝ} {K : ℝ}

/-- Restricted to the line `t ↦ x + t(y − x)`, a differentiable `f` with a `K`-Lipschitz derivative
has the derivative `t ↦ f′(x + t(y − x))(y − x)`, which is `K‖y − x‖²`-Lipschitz. -/
lemma hasDerivAt_lineRestrict (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hf' : ∀ x y, ‖f' y - f' x‖ ≤ K * ‖y - x‖) (x y : E) :
    (∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • (y - x))) (f' (x + t • (y - x)) (y - x)) t) ∧
      ∀ s t : ℝ, s ≤ t → |f' (x + t • (y - x)) (y - x) - f' (x + s • (y - x)) (y - x)| ≤
        K * ‖y - x‖ ^ 2 * (t - s) := by
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · have hl : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact (hf (x + t • (y - x))).comp_hasDerivAt t hl
  · rw [← sub_apply]
    calc |(f' (x + t • (y - x)) - f' (x + s • (y - x))) (y - x)|
        ≤ ‖f' (x + t • (y - x)) - f' (x + s • (y - x))‖ * ‖y - x‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖x + t • (y - x) - (x + s • (y - x))‖ * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right (hf' _ _) (norm_nonneg _)
      _ = K * ‖y - x‖ ^ 2 * (t - s) := by
          rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.2 hst)]
          ring

/-- **First-order Taylor bound in a normed space** (the multi-dimensional form of
`abs_taylor_first_le`): if `f` is differentiable with a `K`-Lipschitz derivative, then
`|f(y) − f(x) − f′(x)(y − x)| ≤ (K/2)‖y − x‖²`. -/
lemma abs_taylor_fderiv_le (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hf' : ∀ x y, ‖f' y - f' x‖ ≤ K * ‖y - x‖) (x y : E) :
    |f y - f x - f' x (y - x)| ≤ K / 2 * ‖y - x‖ ^ 2 := by
  obtain ⟨hd, hL⟩ := hasDerivAt_lineRestrict hf hf' x y
  have h := abs_taylor_first_le hd hL 0 1
  simp only [zero_smul, add_zero, one_smul, add_sub_cancel, sub_zero, mul_one, one_pow] at h
  linarith

/-- **The antithetic second difference of a smooth payoff of a `d`-dimensional value** (Giles
2015, §5.3, p. 42: "the average of the fine and antithetic paths is within `O(h)` of the coarse
path, and hence the multilevel variance is `O(h²)` for smooth payoffs").  If `f : E → ℝ` is
differentiable and its derivative is `K`-Lipschitz, `‖f′(y) − f′(x)‖ ≤ K‖y − x‖` (for `E = ℝ^d`:
`∇f` is `K`-Lipschitz), then `|f(½(a + b)) − ½f(a) − ½f(b)| ≤ (K/8)‖a − b‖²`, i.e.
`|f(a) + f(b) − 2f(½(a + b))| ≤ (K/4)‖a − b‖²`: the first-order terms cancel.  This is the
multi-dimensional form of `abs_midpoint_sub_avg_le`. -/
theorem abs_midpoint_sub_avg_le_fderiv (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hf' : ∀ x y, ‖f' y - f' x‖ ≤ K * ‖y - x‖) (a b : E) :
    |f (midpoint ℝ a b) - f a / 2 - f b / 2| ≤ K / 8 * ‖a - b‖ ^ 2 := by
  obtain ⟨hd, hL⟩ := hasDerivAt_lineRestrict hf hf' a b
  have h := abs_midpoint_sub_avg_le hd hL 0 1
  have hm : a + ((0 + 1) / 2 : ℝ) • (b - a) = midpoint ℝ a b := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    module
  rw [hm, zero_smul, add_zero, one_smul, add_sub_cancel] at h
  rw [norm_sub_rev]
  linarith

/-- **Giles 2015, §5.3, pointwise, in `d` dimensions** (p. 42: "the average of the fine and
antithetic paths is within `O(h)` of the coarse path, and hence the multilevel variance is `O(h²)`
for smooth payoffs").  For `f : E → ℝ` with a `K`-Lipschitz derivative, the antithetic correction
`½(f(a) + f(b)) − f(c)` of the fine value `a`, the antithetic value `b` and the coarse value `c` is
at most `‖f′(c)‖ ‖½(a + b) − c‖ + (K/4)(‖a − c‖² + ‖b − c‖²)`.  The scalar `abs_antithetic_le` is
the case `E = ℝ`. -/
theorem abs_antithetic_le_fderiv (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hf' : ∀ x y, ‖f' y - f' x‖ ≤ K * ‖y - x‖) (a b c : E) :
    |(f a + f b) / 2 - f c| ≤
      ‖f' c‖ * ‖midpoint ℝ a b - c‖ + K / 4 * (‖a - c‖ ^ 2 + ‖b - c‖ ^ 2) := by
  have ha := abs_taylor_fderiv_le hf hf' c a
  have hb := abs_taylor_fderiv_le hf hf' c b
  have hmc : midpoint ℝ a b - c = (2⁻¹ : ℝ) • ((a - c) + (b - c)) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    module
  have hlin : f' c (midpoint ℝ a b - c) = (f' c (a - c) + f' c (b - c)) / 2 := by
    rw [hmc, map_smul, map_add, smul_eq_mul]
    ring
  have hop : |f' c (midpoint ℝ a b - c)| ≤ ‖f' c‖ * ‖midpoint ℝ a b - c‖ := by
    rw [← Real.norm_eq_abs]
    exact ContinuousLinearMap.le_opNorm _ _
  have e : (f a + f b) / 2 - f c = (f a - f c - f' c (a - c)) / 2 +
      (f b - f c - f' c (b - c)) / 2 + f' c (midpoint ℝ a b - c) := by
    rw [hlin]
    ring
  rw [e]
  calc |(f a - f c - f' c (a - c)) / 2 + (f b - f c - f' c (b - c)) / 2 +
        f' c (midpoint ℝ a b - c)|
      ≤ |(f a - f c - f' c (a - c)) / 2| + |(f b - f c - f' c (b - c)) / 2| +
          |f' c (midpoint ℝ a b - c)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |f a - f c - f' c (a - c)| / 2 + |f b - f c - f' c (b - c)| / 2 +
          |f' c (midpoint ℝ a b - c)| := by
        rw [abs_div, abs_div, abs_two]
    _ ≤ K / 2 * ‖a - c‖ ^ 2 / 2 + K / 2 * ‖b - c‖ ^ 2 / 2 +
          ‖f' c‖ * ‖midpoint ℝ a b - c‖ :=
        add_le_add (add_le_add (div_le_div_of_nonneg_right ha zero_le_two)
          (div_le_div_of_nonneg_right hb zero_le_two)) hop
    _ = ‖f' c‖ * ‖midpoint ℝ a b - c‖ + K / 4 * (‖a - c‖ ^ 2 + ‖b - c‖ ^ 2) := by ring

/-- **Giles 2015, §5.3, pointwise, in terms of the fine–antithetic difference** (p. 42: "the
average of the fine and antithetic paths is within `O(h)` of the coarse path, and hence the
multilevel variance is `O(h²)` for smooth payoffs").  For `f : E → ℝ` with a `K`-Lipschitz
derivative and `‖f′‖ ≤ L`,
`|½(f(a) + f(b)) − f(c)| ≤ L‖½(a + b) − c‖ + (K/8)‖a − b‖²`: the correction is of the order of the
distance of the average from the coarse value plus the square of the fine–antithetic difference
(`abs_midpoint_sub_avg_le_fderiv` and the mean value inequality). -/
theorem abs_antithetic_le_midpoint {L : ℝ} (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hf' : ∀ x y, ‖f' y - f' x‖ ≤ K * ‖y - x‖) (hL : ∀ x, ‖f' x‖ ≤ L) (a b c : E) :
    |(f a + f b) / 2 - f c| ≤ L * ‖midpoint ℝ a b - c‖ + K / 8 * ‖a - b‖ ^ 2 := by
  have hmid := abs_midpoint_sub_avg_le_fderiv hf hf' a b
  have hlip : |f (midpoint ℝ a b) - f c| ≤ L * ‖midpoint ℝ a b - c‖ := by
    have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ => (hf x).hasFDerivWithinAt) (fun x _ => hL x) convex_univ (Set.mem_univ c)
      (Set.mem_univ (midpoint ℝ a b))
    rwa [Real.norm_eq_abs] at h
  have e : (f a + f b) / 2 - f c =
      -(f (midpoint ℝ a b) - f a / 2 - f b / 2) + (f (midpoint ℝ a b) - f c) := by ring
  rw [e]
  calc |-(f (midpoint ℝ a b) - f a / 2 - f b / 2) + (f (midpoint ℝ a b) - f c)|
      ≤ |f (midpoint ℝ a b) - f a / 2 - f b / 2| + |f (midpoint ℝ a b) - f c| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ K / 8 * ‖a - b‖ ^ 2 + L * ‖midpoint ℝ a b - c‖ := add_le_add hmid hlip
    _ = L * ‖midpoint ℝ a b - c‖ + K / 8 * ‖a - b‖ ^ 2 := by ring

/-- **Giles 2015, §5.3, the variance for a multi-dimensional SDE** (p. 42: "the average of the fine
and antithetic paths is within `O(h)` of the coarse path, and hence the multilevel variance is
`O(h²)` for smooth payoffs").  Let `A`, `B` be the fine and antithetic terminal values and `C` the
coarse one, with values in a real normed space `E` (for instance `ℝ^d`), and let `f : E → ℝ` have
`‖f′‖ ≤ L` and a `K`-Lipschitz derivative.  If `E‖½(A + B) − C‖² ≤ D₁ h²` and
`E‖A − C‖⁴, E‖B − C‖⁴ ≤ D₂ h²` (the fourth moments of an `O(h^{1/2})` strong error), then
`V[½(f(A) + f(B)) − f(C)] ≤ (2L²D₁ + K²D₂/2) h²`, the constant of the scalar
`variance_antithetic_le`.  The rates of the paths are hypotheses: the SDE analysis behind them
(the paper's "Lengthy analysis", due to Giles and Szpruch) is not formalised. -/
theorem variance_antithetic_le_fderiv {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [MeasurableSpace E] [OpensMeasurableSpace E] {L D₁ D₂ h : ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : ∀ x y, ‖f' y - f' x‖ ≤ K * ‖y - x‖)
    (hL : ∀ x, ‖f' x‖ ≤ L) {A B C : Ω → E} (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (hi1 : Integrable (fun ω => ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2) μ)
    (hi2 : Integrable (fun ω => ‖A ω - C ω‖ ^ 4) μ)
    (hi3 : Integrable (fun ω => ‖B ω - C ω‖ ^ 4) μ)
    (h1 : ∫ ω, ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 ∂μ ≤ D₁ * h ^ 2)
    (h2 : ∫ ω, ‖A ω - C ω‖ ^ 4 ∂μ ≤ D₂ * h ^ 2) (h3 : ∫ ω, ‖B ω - C ω‖ ^ 4 ∂μ ≤ D₂ * h ^ 2) :
    variance (fun ω => (f (A ω) + f (B ω)) / 2 - f (C ω)) μ ≤
      (2 * L ^ 2 * D₁ + K ^ 2 * D₂ / 2) * h ^ 2 := by
  have hfm : Measurable f :=
    (continuous_iff_continuousAt.2 fun x => (hf x).continuousAt).measurable
  have hYm : Measurable fun ω => (f (A ω) + f (B ω)) / 2 - f (C ω) :=
    (((hfm.comp hA).add (hfm.comp hB)).div_const 2).sub (hfm.comp hC)
  -- the pointwise bound on the square
  have hpt : ∀ ω, ((f (A ω) + f (B ω)) / 2 - f (C ω)) ^ 2 ≤
      2 * L ^ 2 * ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 +
        K ^ 2 / 4 * (‖A ω - C ω‖ ^ 4 + ‖B ω - C ω‖ ^ 4) := by
    intro ω
    have h := abs_antithetic_le_fderiv hf hf' (A ω) (B ω) (C ω)
    have hb : |(f (A ω) + f (B ω)) / 2 - f (C ω)| ≤ L * ‖midpoint ℝ (A ω) (B ω) - C ω‖ +
        |K| / 4 * (‖A ω - C ω‖ ^ 2 + ‖B ω - C ω‖ ^ 2) := by
      refine h.trans (add_le_add (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _)) ?_)
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (by positivity)
    refine (sq_le_of_abs_le_add hb).trans_eq ?_
    rw [mul_pow, div_pow, sq_abs]
    ring
  have hi23 : Integrable (fun ω => ‖A ω - C ω‖ ^ 4 + ‖B ω - C ω‖ ^ 4) μ := hi2.add hi3
  have hbound : Integrable (fun ω => 2 * L ^ 2 * ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 +
      K ^ 2 / 4 * (‖A ω - C ω‖ ^ 4 + ‖B ω - C ω‖ ^ 4)) μ :=
    (hi1.const_mul (2 * L ^ 2)).add (hi23.const_mul (K ^ 2 / 4))
  calc variance (fun ω => (f (A ω) + f (B ω)) / 2 - f (C ω)) μ
      ≤ ∫ ω, ((f (A ω) + f (B ω)) / 2 - f (C ω)) ^ 2 ∂μ :=
        variance_le_expectation_sq hYm.aestronglyMeasurable
    _ ≤ ∫ ω, (2 * L ^ 2 * ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 +
          K ^ 2 / 4 * (‖A ω - C ω‖ ^ 4 + ‖B ω - C ω‖ ^ 4)) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) hbound
          (Eventually.of_forall hpt)
    _ = 2 * L ^ 2 * ∫ ω, ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 ∂μ +
          K ^ 2 / 4 * (∫ ω, ‖A ω - C ω‖ ^ 4 ∂μ + ∫ ω, ‖B ω - C ω‖ ^ 4 ∂μ) := by
        rw [integral_add (hi1.const_mul (2 * L ^ 2)) (hi23.const_mul (K ^ 2 / 4)),
          integral_const_mul, integral_const_mul, integral_add hi2 hi3]
    _ ≤ 2 * L ^ 2 * (D₁ * h ^ 2) + K ^ 2 / 4 * (D₂ * h ^ 2 + D₂ * h ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity))
    _ = (2 * L ^ 2 * D₁ + K ^ 2 * D₂ / 2) * h ^ 2 := by ring

/-- **Giles 2015, §5.3, the variance in terms of the fine–antithetic difference** (p. 42: "the
average of the fine and antithetic paths is within `O(h)` of the coarse path, and hence the
multilevel variance is `O(h²)` for smooth payoffs"; p. 39: "a very low variance despite the
`O(h^{1/2})` strong convergence").  With `A`, `B`, `C`, `f`, `L`, `K` as in
`variance_antithetic_le_fderiv`: if `E‖½(A + B) − C‖² ≤ D₁ h²` (the average within `O(h)` of the
coarse path) and `E‖A − B‖⁴ ≤ D₂ h²` (fine and antithetic paths `O(h^{1/2})` apart), then
`V[½(f(A) + f(B)) − f(C)] ≤ (2L²D₁ + K²D₂/32) h²`.  Since
`‖A − B‖⁴ ≤ 8(‖A − C‖⁴ + ‖B − C‖⁴)`, the moment bounds of `variance_antithetic_le_fderiv` give
`E‖A − B‖⁴ ≤ 16D₂ h²`, and with `16D₂` in place of `D₂` this bound is the same
`(2L²D₁ + K²D₂/2) h²`: these hypotheses are weaker. -/
theorem variance_antithetic_le_midpoint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [MeasurableSpace E] [OpensMeasurableSpace E] {L D₁ D₂ h : ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : ∀ x y, ‖f' y - f' x‖ ≤ K * ‖y - x‖)
    (hL : ∀ x, ‖f' x‖ ≤ L) {A B C : Ω → E} (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (hi1 : Integrable (fun ω => ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2) μ)
    (hi2 : Integrable (fun ω => ‖A ω - B ω‖ ^ 4) μ)
    (h1 : ∫ ω, ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 ∂μ ≤ D₁ * h ^ 2)
    (h2 : ∫ ω, ‖A ω - B ω‖ ^ 4 ∂μ ≤ D₂ * h ^ 2) :
    variance (fun ω => (f (A ω) + f (B ω)) / 2 - f (C ω)) μ ≤
      (2 * L ^ 2 * D₁ + K ^ 2 * D₂ / 32) * h ^ 2 := by
  have hfm : Measurable f :=
    (continuous_iff_continuousAt.2 fun x => (hf x).continuousAt).measurable
  have hYm : Measurable fun ω => (f (A ω) + f (B ω)) / 2 - f (C ω) :=
    (((hfm.comp hA).add (hfm.comp hB)).div_const 2).sub (hfm.comp hC)
  -- the pointwise bound on the square
  have hpt : ∀ ω, ((f (A ω) + f (B ω)) / 2 - f (C ω)) ^ 2 ≤
      2 * L ^ 2 * ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 + K ^ 2 / 32 * ‖A ω - B ω‖ ^ 4 := by
    intro ω
    have hb := abs_antithetic_le_midpoint hf hf' hL (A ω) (B ω) (C ω)
    have hsq : ((f (A ω) + f (B ω)) / 2 - f (C ω)) ^ 2 ≤
        (L * ‖midpoint ℝ (A ω) (B ω) - C ω‖ + K / 8 * ‖A ω - B ω‖ ^ 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    nlinarith [sq_nonneg (L * ‖midpoint ℝ (A ω) (B ω) - C ω‖ - K / 8 * ‖A ω - B ω‖ ^ 2)]
  have hbound : Integrable (fun ω => 2 * L ^ 2 * ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 +
      K ^ 2 / 32 * ‖A ω - B ω‖ ^ 4) μ :=
    (hi1.const_mul (2 * L ^ 2)).add (hi2.const_mul (K ^ 2 / 32))
  calc variance (fun ω => (f (A ω) + f (B ω)) / 2 - f (C ω)) μ
      ≤ ∫ ω, ((f (A ω) + f (B ω)) / 2 - f (C ω)) ^ 2 ∂μ :=
        variance_le_expectation_sq hYm.aestronglyMeasurable
    _ ≤ ∫ ω, (2 * L ^ 2 * ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 +
          K ^ 2 / 32 * ‖A ω - B ω‖ ^ 4) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) hbound
          (Eventually.of_forall hpt)
    _ = 2 * L ^ 2 * ∫ ω, ‖midpoint ℝ (A ω) (B ω) - C ω‖ ^ 2 ∂μ +
          K ^ 2 / 32 * ∫ ω, ‖A ω - B ω‖ ^ 4 ∂μ := by
        rw [integral_add (hi1.const_mul (2 * L ^ 2)) (hi2.const_mul (K ^ 2 / 32)),
          integral_const_mul, integral_const_mul]
    _ ≤ 2 * L ^ 2 * (D₁ * h ^ 2) + K ^ 2 / 32 * (D₂ * h ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = (2 * L ^ 2 * D₁ + K ^ 2 * D₂ / 32) * h ^ 2 := by ring

end antithetic

/-! ### §5.3: the European call option -/

section call

/-- The convexity defect of the call payoff `g(x) = max(x − K, 0)` at the midpoint:
`0 ≤ ½(g(a) + g(b)) − g(½(a + b)) ≤ ¼|a − b|`, and it vanishes unless the strike `K` lies strictly
between `a` and `b` (then it is `½ min(|a − K|, |b − K|)`). -/
lemma call_midpoint_defect (K a b : ℝ) :
    0 ≤ (max (a - K) 0 + max (b - K) 0) / 2 - max ((a + b) / 2 - K) 0 ∧
      (max (a - K) 0 + max (b - K) 0) / 2 - max ((a + b) / 2 - K) 0 ≤
        if min a b < K ∧ K < max a b then |a - b| / 4 else 0 := by
  -- the case `a ≤ b`
  have key : ∀ a b : ℝ, a ≤ b →
      0 ≤ (max (a - K) 0 + max (b - K) 0) / 2 - max ((a + b) / 2 - K) 0 ∧
        (max (a - K) 0 + max (b - K) 0) / 2 - max ((a + b) / 2 - K) 0 ≤
          if min a b < K ∧ K < max a b then |a - b| / 4 else 0 := by
    intro a b hab
    rw [min_eq_left hab, max_eq_right hab, abs_of_nonpos (sub_nonpos.2 hab)]
    split_ifs with hK
    · obtain ⟨h1, h2⟩ := hK
      rw [max_eq_right (by linarith : a - K ≤ 0), max_eq_left (by linarith : 0 ≤ b - K)]
      rcases le_total ((a + b) / 2) K with hm | hm
      · rw [max_eq_right (by linarith : (a + b) / 2 - K ≤ 0)]
        constructor <;> linarith
      · rw [max_eq_left (by linarith : 0 ≤ (a + b) / 2 - K)]
        constructor <;> linarith
    · rw [not_and_or, not_lt, not_lt] at hK
      rcases hK with hK | hK
      · rw [max_eq_left (by linarith : 0 ≤ a - K), max_eq_left (by linarith : 0 ≤ b - K),
          max_eq_left (by linarith : 0 ≤ (a + b) / 2 - K)]
        constructor <;> linarith
      · rw [max_eq_right (by linarith : a - K ≤ 0), max_eq_right (by linarith : b - K ≤ 0),
          max_eq_right (by linarith : (a + b) / 2 - K ≤ 0)]
        constructor <;> linarith
  rcases le_total a b with hab | hab
  · exact key a b hab
  · have h := key b a hab
    rwa [min_comm b a, max_comm b a, abs_sub_comm b a, add_comm b a,
      add_comm (max (b - K) 0)] at h

/-- **Giles 2015, §5.3, the antithetic correction of a call option, pointwise** (p. 42: "the
average of the fine and antithetic paths is within `O(h)` of the coarse path, and hence the
multilevel variance is … `O(h^{3/2})` for the standard European call option").  For the call
payoff `g(x) = max(x − K, 0)`, the fine, antithetic and coarse values `a`, `b`, `c` satisfy
`|½(g(a) + g(b)) − g(c)| ≤ |½(a + b) − c| + ¼|a − b| 1{K strictly between a and b}`: away from the
kink the fine and antithetic errors cancel as for a smooth payoff (`g` is affine between `a` and
`b`), and the defect `¼|a − b|` appears only when the kink separates them.  The constant `¼` is
attained for `a = K − t`, `b = K + t`, `c = K`. -/
theorem abs_call_antithetic_le (K a b c : ℝ) :
    |(max (a - K) 0 + max (b - K) 0) / 2 - max (c - K) 0| ≤
      |(a + b) / 2 - c| + if min a b < K ∧ K < max a b then |a - b| / 4 else 0 := by
  obtain ⟨h0, h1⟩ := call_midpoint_defect K a b
  have hlip : |max ((a + b) / 2 - K) 0 - max (c - K) 0| ≤ |(a + b) / 2 - c| := by
    have h := abs_max_sub_max_le_abs ((a + b) / 2 - K) (c - K) 0
    rwa [sub_sub_sub_cancel_right] at h
  have e : (max (a - K) 0 + max (b - K) 0) / 2 - max (c - K) 0 =
      ((max (a - K) 0 + max (b - K) 0) / 2 - max ((a + b) / 2 - K) 0) +
        (max ((a + b) / 2 - K) 0 - max (c - K) 0) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg h0]
  linarith

/-- The strike `K` lies strictly between `a` and `b` iff `|½(a + b) − K| < ½|a − b|`. -/
lemma between_iff_abs_lt (K a b : ℝ) :
    (min a b < K ∧ K < max a b) ↔ |(a + b) / 2 - K| < |a - b| / 2 := by
  rw [abs_sub_lt_iff]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab, abs_of_nonpos (sub_nonpos.2 hab)]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · rw [min_eq_right hab, max_eq_left hab, abs_of_nonneg (sub_nonneg.2 hab)]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- If, given `D ≥ 0`, `M` has a density at most `ρ₀` (the joint law of `(D, M)` is dominated by
`law(D) ⊗ ρ₀ Lebesgue`), then `E[D² 1{|M − K| < D/2}] ≤ ρ₀ E[D³]`: the window
`|M − K| < D/2` has conditional probability at most `ρ₀ D`. -/
lemma integral_sq_ite_le_of_density {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D M : Ω → ℝ} (hD : Measurable D) (hM : Measurable M) (hD0 : ∀ ω, 0 ≤ D ω) {K : ℝ}
    {ρ₀ : ℝ≥0} (hdens : μ.map (fun ω => (D ω, M ω)) ≤ (μ.map D).prod ((ρ₀ : ℝ≥0∞) • volume))
    (hi : Integrable (fun ω => D ω ^ 3) μ) :
    ∫ ω, (if |M ω - K| < D ω / 2 then D ω ^ 2 else 0) ∂μ ≤ ρ₀ * ∫ ω, D ω ^ 3 ∂μ := by
  have hS : MeasurableSet {p : ℝ × ℝ | |p.2 - K| < p.1 / 2} :=
    measurableSet_lt (measurable_snd.sub_const K).abs (measurable_fst.div_const 2)
  set F : ℝ × ℝ → ℝ≥0∞ :=
    {p : ℝ × ℝ | |p.2 - K| < p.1 / 2}.indicator fun p => ENNReal.ofReal (p.1 ^ 2) with hF_def
  have hF : Measurable F :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const 2)).indicator hS
  have hG0 : ∀ ω, 0 ≤ (if |M ω - K| < D ω / 2 then D ω ^ 2 else 0) := fun ω => by
    split_ifs <;> positivity
  have hGm : Measurable fun ω => (if |M ω - K| < D ω / 2 then D ω ^ 2 else 0) :=
    Measurable.ite (measurableSet_lt ((hM.sub_const K).abs) (hD.div_const 2)) (hD.pow_const 2)
      measurable_const
  have hGF : ∀ ω, ENNReal.ofReal (if |M ω - K| < D ω / 2 then D ω ^ 2 else 0) =
      F (D ω, M ω) := by
    intro ω
    simp only [hF_def, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  -- the inner integral over `M` given `D = d`
  have hinner : ∀ d : ℝ, ∫⁻ m, F (d, m) ∂((ρ₀ : ℝ≥0∞) • volume) =
      ρ₀ * ENNReal.ofReal (d ^ 3) := by
    intro d
    have hset : {m : ℝ | |m - K| < d / 2} = Set.Ioo (K - d / 2) (K + d / 2) := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_Ioo, abs_sub_lt_iff]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have hFd : (fun m => F (d, m)) =
        Set.indicator (Set.Ioo (K - d / 2) (K + d / 2)) fun _ => ENNReal.ofReal (d ^ 2) := by
      funext m
      rw [← hset]
      simp only [hF_def, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hFd, lintegral_smul_measure, lintegral_indicator_const measurableSet_Ioo,
      Real.volume_Ioo, ← ENNReal.ofReal_mul (sq_nonneg d), smul_eq_mul]
    congr 2
    ring
  have hlhs : ∫ ω, (if |M ω - K| < D ω / 2 then D ω ^ 2 else 0) ∂μ =
      (∫⁻ ω, F (D ω, M ω) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hG0) hGm.aestronglyMeasurable]
    congr 1
    exact lintegral_congr fun ω => hGF ω
  have hcube : Measurable fun d : ℝ => ENNReal.ofReal (d ^ 3) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const 3)
  have hbound : ∫⁻ ω, F (D ω, M ω) ∂μ ≤ ρ₀ * ENNReal.ofReal (∫ ω, D ω ^ 3 ∂μ) := by
    calc ∫⁻ ω, F (D ω, M ω) ∂μ = ∫⁻ p, F p ∂(μ.map fun ω => (D ω, M ω)) :=
          (lintegral_map hF (hD.prodMk hM)).symm
      _ ≤ ∫⁻ p, F p ∂((μ.map D).prod ((ρ₀ : ℝ≥0∞) • volume)) := lintegral_mono' hdens le_rfl
      _ = ∫⁻ d, ∫⁻ m, F (d, m) ∂((ρ₀ : ℝ≥0∞) • volume) ∂(μ.map D) :=
          lintegral_prod F hF.aemeasurable
      _ = ∫⁻ d, ρ₀ * ENNReal.ofReal (d ^ 3) ∂(μ.map D) := lintegral_congr fun d => hinner d
      _ = ρ₀ * ∫⁻ ω, ENNReal.ofReal (D ω ^ 3) ∂μ := by
          rw [lintegral_const_mul _ hcube, lintegral_map hcube hD]
      _ = ρ₀ * ENNReal.ofReal (∫ ω, D ω ^ 3 ∂μ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hi
            (Eventually.of_forall fun ω => pow_nonneg (hD0 ω) 3)]
  rw [hlhs]
  calc (∫⁻ ω, F (D ω, M ω) ∂μ).toReal ≤ (ρ₀ * ENNReal.ofReal (∫ ω, D ω ^ 3 ∂μ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hbound
    _ = ρ₀ * ∫ ω, D ω ^ 3 ∂μ := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
          ENNReal.toReal_ofReal (integral_nonneg fun ω => pow_nonneg (hD0 ω) 3)]

/-- **Giles 2015, §5.3: the antithetic multilevel variance is `O(h^{3/2})` for the European call**
(p. 42: "Lengthy analysis proves that the average of the fine and antithetic paths is within
`O(h)` of the coarse path, and hence the multilevel variance is `O(h²)` for smooth payoffs, and
`O(h^{3/2})` for the standard European call option").  Let `A`, `B` be the fine and antithetic
terminal values, `C` the coarse one, and `g(x) = max(x − K, 0)`.  Suppose that
`E[(½(A + B) − C)²] ≤ D₁ h²` (the average within `O(h)` of the coarse path),
`E|A − B|³ ≤ D₂ h^{3/2}` (the third moment of an `O(h^{1/2})` fine–antithetic difference), and that,
given `|A − B|`, the average `½(A + B)` has a density at most `ρ₀`: the joint law of
`(|A − B|, ½(A + B))` is dominated by `law(|A − B|) ⊗ ρ₀ · Lebesgue` (for instance `|A − B|`
independent of `½(A + B)`, whose density is at most `ρ₀`).  Then
`V[½(g(A) + g(B)) − g(C)] ≤ 2D₁ h² + (ρ₀D₂/8) h^{3/2}`.  By `abs_call_antithetic_le` the square
of the correction is at most `2(½(A + B) − C)² + ⅛|A − B|² 1{|½(A + B) − K| < ½|A − B|}`, and the
window has conditional probability at most `ρ₀|A − B|` (`integral_sq_ite_le_of_density`).
The joint hypothesis replaces the SDE analysis; bounds from marginal information only are weaker,
see `variance_call_antithetic_le_holder`. -/
theorem variance_call_antithetic_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B C : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) {K : ℝ} {ρ₀ : ℝ≥0}
    (hdens : μ.map (fun ω => (|A ω - B ω|, (A ω + B ω) / 2)) ≤
      (μ.map fun ω => |A ω - B ω|).prod ((ρ₀ : ℝ≥0∞) • volume))
    {D₁ D₂ h : ℝ} (hi1 : Integrable (fun ω => ((A ω + B ω) / 2 - C ω) ^ 2) μ)
    (hi2 : Integrable (fun ω => |A ω - B ω| ^ 3) μ)
    (h1 : ∫ ω, ((A ω + B ω) / 2 - C ω) ^ 2 ∂μ ≤ D₁ * h ^ 2)
    (h2 : ∫ ω, |A ω - B ω| ^ 3 ∂μ ≤ D₂ * h ^ (3 / 2 : ℝ)) :
    variance (fun ω => (max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0) μ ≤
      2 * D₁ * h ^ 2 + ρ₀ * D₂ / 8 * h ^ (3 / 2 : ℝ) := by
  set G : Ω → ℝ := fun ω =>
    if |(A ω + B ω) / 2 - K| < |A ω - B ω| / 2 then |A ω - B ω| ^ 2 else 0 with hG
  have hDm : Measurable fun ω => |A ω - B ω| := (hA.sub hB).abs
  have hMm : Measurable fun ω => (A ω + B ω) / 2 := (hA.add hB).div_const 2
  have hGm : Measurable G :=
    Measurable.ite (measurableSet_lt ((hMm.sub_const K).abs) (hDm.div_const 2))
      (hDm.pow_const 2) measurable_const
  have hGint : Integrable G μ := by
    refine ((integrable_const (1 : ℝ)).add hi2).mono' hGm.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have ht := abs_nonneg (A ω - B ω)
    show |G ω| ≤ 1 + |A ω - B ω| ^ 3
    rw [hG]
    dsimp only
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg (|A ω - B ω| - 1)) (by linarith : 0 ≤ |A ω - B ω| + 1)]
    · rw [abs_zero]
      positivity
  have hGle : ∫ ω, G ω ∂μ ≤ ρ₀ * ∫ ω, |A ω - B ω| ^ 3 ∂μ :=
    integral_sq_ite_le_of_density hDm hMm (fun ω => abs_nonneg _) hdens hi2
  have hYm : Measurable fun ω => (max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0 :=
    ((((hA.sub_const K).max measurable_const).add
      ((hB.sub_const K).max measurable_const)).div_const 2).sub
      ((hC.sub_const K).max measurable_const)
  -- the pointwise bound on the square
  have hpt : ∀ ω, ((max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0) ^ 2 ≤
      2 * ((A ω + B ω) / 2 - C ω) ^ 2 + G ω / 8 := by
    intro ω
    have hb := abs_call_antithetic_le K (A ω) (B ω) (C ω)
    by_cases hS : min (A ω) (B ω) < K ∧ K < max (A ω) (B ω)
    · rw [if_pos hS] at hb
      have hG' : G ω = |A ω - B ω| ^ 2 := by
        rw [hG]
        exact if_pos ((between_iff_abs_lt K (A ω) (B ω)).1 hS)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [sq_abs] at hsq
      rw [hG', ← sq_abs ((A ω + B ω) / 2 - C ω)]
      nlinarith [sq_nonneg (|(A ω + B ω) / 2 - C ω| - |A ω - B ω| / 4)]
    · rw [if_neg hS, add_zero] at hb
      have hG' : G ω = 0 := by
        rw [hG]
        exact if_neg fun h => hS ((between_iff_abs_lt K (A ω) (B ω)).2 h)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [sq_abs, sq_abs] at hsq
      rw [hG']
      nlinarith [sq_nonneg ((A ω + B ω) / 2 - C ω)]
  have hbound : Integrable (fun ω => 2 * ((A ω + B ω) / 2 - C ω) ^ 2 + G ω / 8) μ :=
    (hi1.const_mul 2).add (hGint.div_const 8)
  calc variance (fun ω => (max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0) μ
      ≤ ∫ ω, ((max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0) ^ 2 ∂μ :=
        variance_le_expectation_sq hYm.aestronglyMeasurable
    _ ≤ ∫ ω, (2 * ((A ω + B ω) / 2 - C ω) ^ 2 + G ω / 8) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) hbound
          (Eventually.of_forall hpt)
    _ = 2 * ∫ ω, ((A ω + B ω) / 2 - C ω) ^ 2 ∂μ + (∫ ω, G ω ∂μ) / 8 := by
        rw [integral_add (hi1.const_mul 2) (hGint.div_const 8), integral_const_mul,
          integral_div]
    _ ≤ 2 * (D₁ * h ^ 2) + ρ₀ * (D₂ * h ^ (3 / 2 : ℝ)) / 8 := by
        gcongr
        exact hGle.trans (mul_le_mul_of_nonneg_left h2 ρ₀.coe_nonneg)
    _ = 2 * D₁ * h ^ 2 + ρ₀ * D₂ / 8 * h ^ (3 / 2 : ℝ) := by ring

/-- **Giles 2015, §5.3: the call variance in terms of the probability that the strike separates the
fine and antithetic values** (p. 42: "and `O(h^{3/2})` for the standard European call option").
For `g(x) = max(x − K, 0)`, Hölder conjugate exponents `p`, `q` and `S` the event that `K` lies
strictly between `A` and `B`,
`V[½(g(A) + g(B)) − g(C)] ≤ 2E[(½(A + B) − C)²] + ⅛ (E|A − B|^{2p})^{1/p} P(S)^{1/q}`
(`abs_call_antithetic_le` and Hölder's inequality).  With `E[(½(A + B) − C)²] = O(h²)`,
`E|A − B|^{2p} = O(h^p)` and `P(S) = O(h^{1/2})` this is `O(h^{3/2 − 1/(2p)})`, arbitrarily close
to the paper's `O(h^{3/2})` for large `p`.  The exponent `3/2` itself does not follow from such
marginal information: for `h < e^{−2}`, let `½(A + B) = C = K + V` with `V` uniform on `(−1, 1)`,
and `|A − B| = h^{1/2} log(1/h)` if `|V| < h^{1/2}`, `|A − B| = h^{1/2}` otherwise.  Then
`P(S) = h^{1/2}` and `E|A − B|^r = O(h^{r/2})` for every `r`, but the variance is at least
`(h^{3/2}/16)((log(1/h) − 2)² − h^{1/2} log²(1/h))`, which is not `O(h^{3/2})`.
`variance_call_antithetic_le` obtains `O(h^{3/2})` from a joint (conditional density) hypothesis. -/
theorem variance_call_antithetic_le_holder {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B C : Ω → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (K : ℝ) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hi1 : Integrable (fun ω => ((A ω + B ω) / 2 - C ω) ^ 2) μ)
    (hi2 : Integrable (fun ω => |A ω - B ω| ^ (2 * p)) μ) :
    variance (fun ω => (max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0) μ ≤
      2 * ∫ ω, ((A ω + B ω) / 2 - C ω) ^ 2 ∂μ +
        (∫ ω, |A ω - B ω| ^ (2 * p) ∂μ) ^ (1 / p) *
          μ.real {ω | min (A ω) (B ω) < K ∧ K < max (A ω) (B ω)} ^ (1 / q) / 8 := by
  set S := {ω | min (A ω) (B ω) < K ∧ K < max (A ω) (B ω)}
  have hSm : MeasurableSet S :=
    (measurableSet_lt (hA.min hB) measurable_const).inter
      (measurableSet_lt measurable_const (hA.max hB))
  have hp1 : 1 ≤ p := hpq.lt.le
  -- `|A − B|²` is in `L^p`, and `1_S` in `L^q`
  have hfm : Measurable fun ω => |A ω - B ω| ^ 2 := ((hA.sub hB).abs).pow_const 2
  have hfp : ∀ ω, (|A ω - B ω| ^ 2) ^ p = |A ω - B ω| ^ (2 * p) := by
    intro ω
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hfLp : MemLp (fun ω => |A ω - B ω| ^ 2) (ENNReal.ofReal p) μ := by
    rw [← integrable_norm_rpow_iff hfm.aestronglyMeasurable (by simp [hpq.pos])
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hpq.pos.le]
    refine hi2.congr (Eventually.of_forall fun ω => ?_)
    show |A ω - B ω| ^ (2 * p) = ‖|A ω - B ω| ^ 2‖ ^ p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |A ω - B ω| ^ 2), hfp]
  have hfint : Integrable (fun ω => |A ω - B ω| ^ 2) μ :=
    hfLp.integrable (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1)
  have hgm : Measurable (S.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hSm
  have hgLq : MemLp (S.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal q) μ := by
    refine MemLp.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, norm_one]
    · rw [Set.indicator_of_notMem hω, norm_zero]
      exact zero_le_one
  have hgq : ∀ ω, (S.indicator fun _ => (1 : ℝ)) ω ^ q = (S.indicator fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Real.one_rpow]
    · rw [Set.indicator_of_notMem hω, Real.zero_rpow hpq.symm.pos.ne']
  -- Hölder's inequality for `|A − B|² 1_S`
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun ω => by positivity)
    (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω) hfLp hgLq
  rw [integral_congr_ae (Eventually.of_forall hfp), integral_congr_ae (Eventually.of_forall hgq),
    integral_indicator_const _ hSm, smul_eq_mul, mul_one] at hholder
  have hG : ∀ ω, |A ω - B ω| ^ 2 * (S.indicator fun _ => (1 : ℝ)) ω =
      S.indicator (fun ω => |A ω - B ω| ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, mul_one]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
  rw [integral_congr_ae (Eventually.of_forall hG)] at hholder
  have hGint : Integrable (S.indicator fun ω => |A ω - B ω| ^ 2) μ := hfint.indicator hSm
  have hYm : Measurable fun ω => (max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0 :=
    ((((hA.sub_const K).max measurable_const).add
      ((hB.sub_const K).max measurable_const)).div_const 2).sub
      ((hC.sub_const K).max measurable_const)
  -- the pointwise bound on the square
  have hpt : ∀ ω, ((max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0) ^ 2 ≤
      2 * ((A ω + B ω) / 2 - C ω) ^ 2 + S.indicator (fun ω => |A ω - B ω| ^ 2) ω / 8 := by
    intro ω
    have hb := abs_call_antithetic_le K (A ω) (B ω) (C ω)
    by_cases hS : min (A ω) (B ω) < K ∧ K < max (A ω) (B ω)
    · rw [if_pos hS] at hb
      rw [Set.indicator_of_mem (show ω ∈ S from hS)]
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [sq_abs] at hsq
      rw [← sq_abs ((A ω + B ω) / 2 - C ω)]
      nlinarith [sq_nonneg (|(A ω + B ω) / 2 - C ω| - |A ω - B ω| / 4)]
    · rw [if_neg hS, add_zero] at hb
      rw [Set.indicator_of_notMem (show ω ∉ S from hS)]
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [sq_abs, sq_abs] at hsq
      nlinarith [sq_nonneg ((A ω + B ω) / 2 - C ω)]
  have hbound : Integrable (fun ω => 2 * ((A ω + B ω) / 2 - C ω) ^ 2 +
      S.indicator (fun ω => |A ω - B ω| ^ 2) ω / 8) μ :=
    (hi1.const_mul 2).add (hGint.div_const 8)
  calc variance (fun ω => (max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0) μ
      ≤ ∫ ω, ((max (A ω - K) 0 + max (B ω - K) 0) / 2 - max (C ω - K) 0) ^ 2 ∂μ :=
        variance_le_expectation_sq hYm.aestronglyMeasurable
    _ ≤ ∫ ω, (2 * ((A ω + B ω) / 2 - C ω) ^ 2 +
          S.indicator (fun ω => |A ω - B ω| ^ 2) ω / 8) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) hbound
          (Eventually.of_forall hpt)
    _ = 2 * ∫ ω, ((A ω + B ω) / 2 - C ω) ^ 2 ∂μ +
          (∫ ω, S.indicator (fun ω => |A ω - B ω| ^ 2) ω ∂μ) / 8 := by
        rw [integral_add (hi1.const_mul 2) (hGint.div_const 8), integral_const_mul,
          integral_div]
    _ ≤ 2 * ∫ ω, ((A ω + B ω) / 2 - C ω) ^ 2 ∂μ +
          (∫ ω, |A ω - B ω| ^ (2 * p) ∂μ) ^ (1 / p) * μ.real S ^ (1 / q) / 8 := by
        gcongr

end call

/-! ### §5.6: super-linear drift and taming -/

section taming

/-- The explicit Euler step `S ↦ S + h b(S)` for the drift `b` (the drift part of the
Euler–Maruyama step of Giles 2015, §5.6). -/
def eulerDriftStep (b : ℝ → ℝ) (h S : ℝ) : ℝ := S + h * b S

/-- The tamed Euler step `S ↦ S + h b(S)/(1 + h|b(S)|)`: the explicit step with the drift increment
`h b(S)` replaced by `h b(S)/(1 + h|b(S)|)`, "a slight modification to the Euler-Maruyama
discretisation which limits the size of the drift term … when `S_t` is large" (Giles 2015, §5.6,
p. 44; the survey gives no formula, this is the taming of Hutzenthaler, Jentzen and Kloeden). -/
noncomputable def tamedDriftStep (b : ℝ → ℝ) (h S : ℝ) : ℝ := S + h * b S / (1 + h * |b S|)

/-- The explicit step for the drift `−S³` is `S ↦ S(1 − hS²)`. -/
lemma eulerDriftStep_cubic (h S : ℝ) :
    eulerDriftStep (fun S => -S ^ 3) h S = S * (1 - h * S ^ 2) := by
  unfold eulerDriftStep
  ring

/-- **The explicit Euler step for a super-linear drift explodes** (Giles 2015, §5.6, p. 44: SDEs
"such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the
volatility.  This again leads to numerical instability if a uniform timestep is used").  For the
drift `−S³` and `hS² ≥ 2`, the `n`-th explicit Euler iterate is at least `(hS² − 1)ⁿ|S|` in
absolute value (at least `2ⁿ|S|` when `hS² ≥ 3`), whereas the solutions of `S′ = −S³` decay
monotonically to `0`.  The noise-free (drift) part of the scheme only: that the moments of the
Euler–Maruyama approximations diverge (Hutzenthaler, Jentzen and Kloeden) is
`emCubic_moment_tendsto_atTop` in `MlmcLean/EulerSuperlinear.lean`. -/
theorem eulerCubic_growth {h S : ℝ} (hS : 2 ≤ h * S ^ 2) (n : ℕ) :
    (h * S ^ 2 - 1) ^ n * |S| ≤ |(eulerDriftStep (fun S => -S ^ 3) h)^[n] S| := by
  have key : ∀ n : ℕ, h * S ^ 2 ≤ h * ((eulerDriftStep (fun S => -S ^ 3) h)^[n] S) ^ 2 ∧
      (h * S ^ 2 - 1) ^ n * |S| ≤ |(eulerDriftStep (fun S => -S ^ 3) h)^[n] S| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [Function.iterate_succ_apply', eulerDriftStep_cubic]
      set x := (eulerDriftStep (fun S => -S ^ 3) h)^[n] S
      have hx2 : 2 ≤ h * x ^ 2 := le_trans hS h1
      constructor
      · have e : h * (x * (1 - h * x ^ 2)) ^ 2 = h * x ^ 2 * (1 - h * x ^ 2) ^ 2 := by ring
        rw [e]
        have hsq : 1 ≤ (1 - h * x ^ 2) ^ 2 := by nlinarith
        nlinarith
      · rw [abs_mul, abs_of_nonpos (by linarith : 1 - h * x ^ 2 ≤ 0), pow_succ]
        calc (h * S ^ 2 - 1) ^ n * (h * S ^ 2 - 1) * |S| =
            (h * S ^ 2 - 1) ^ n * |S| * (h * S ^ 2 - 1) := by ring
          _ ≤ |x| * -(1 - h * x ^ 2) :=
            mul_le_mul h2 (by linarith) (by linarith) (abs_nonneg _)
  exact (key n).2

/-- **Numerical instability for every uniform timestep** (Giles 2015, §5.6, p. 44: "This again
leads to numerical instability if a uniform timestep is used").  For the drift `−S³`, every
timestep `h > 0` and every starting value with `hS² > 2`, i.e. `|S| > √(2/h)`, the explicit Euler
iterates tend to `∞` in absolute value (`eulerCubic_growth`).  The threshold is sharp:
`eulerCubic_bounded`. -/
theorem eulerCubic_tendsto_atTop {h S : ℝ} (hS : 2 < h * S ^ 2) :
    Tendsto (fun n : ℕ => |(eulerDriftStep (fun S => -S ^ 3) h)^[n] S|) atTop atTop := by
  have hr : 1 < h * S ^ 2 - 1 := by linarith
  have hS0 : 0 < |S| := by
    rw [abs_pos]
    rintro rfl
    norm_num at hS
  exact tendsto_atTop_mono (eulerCubic_growth hS.le)
    ((tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const hS0)

/-- **The explicit step is stable for small values** (Giles 2015, §5.6): for the drift `−S³`,
`h ≥ 0` and `hS² ≤ 2`, i.e. `|S| ≤ √(2/h)`, the explicit Euler iterates stay within `|S|`.  With
`eulerCubic_tendsto_atTop` this makes `√(2/h)` the exact stability threshold (at `hS² = 2` the orbit
is the 2-cycle `S, −S`): a fixed timestep `h` is stable only for `|S| ≤ √(2/h)`, so no uniform
timestep is stable for all starting values. -/
theorem eulerCubic_bounded {h S : ℝ} (hh : 0 ≤ h) (hS : h * S ^ 2 ≤ 2) (n : ℕ) :
    |(eulerDriftStep (fun S => -S ^ 3) h)^[n] S| ≤ |S| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', eulerDriftStep_cubic, abs_mul]
    set x := (eulerDriftStep (fun S => -S ^ 3) h)^[n] S
    have hx2 : h * x ^ 2 ≤ 2 := by
      have : x ^ 2 ≤ S ^ 2 := by
        rw [← sq_abs x, ← sq_abs S]
        exact pow_le_pow_left₀ (abs_nonneg _) ih 2
      nlinarith
    have hx0 : 0 ≤ h * x ^ 2 := by positivity
    have h1 : |1 - h * x ^ 2| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc |x| * |1 - h * x ^ 2| ≤ |x| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |x| := mul_one _
      _ ≤ |S| := ih

/-- **Taming limits the drift term** (Giles 2015, §5.6, p. 44: "Their solution is to introduce a
slight modification to the Euler-Maruyama discretisation which limits the size of the drift term
on each level of approximation when `S_t` is large, to avoid this instability").  For every drift
`b`, timestep `h ≥ 0` and value `S`, the tamed drift increment `h b(S)/(1 + h|b(S)|)` is less than
`1` in absolute value. -/
theorem abs_tamedDrift_lt (b : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h) (S : ℝ) :
    |h * b S / (1 + h * |b S|)| < 1 := by
  have hpos : 0 < 1 + h * |b S| := by positivity
  rw [abs_div, abs_of_pos hpos, abs_mul, abs_of_nonneg hh, div_lt_one hpos]
  linarith

/-- **Taming is a slight modification** (Giles 2015, §5.6, p. 44: "a slight modification to the
Euler-Maruyama discretisation"): the tamed and explicit steps differ by at most `h² b(S)²`, which is
`O(h²)` for bounded `S`, so taming does not change the consistency of the scheme. -/
theorem abs_tamedDriftStep_sub_eulerDriftStep_le (b : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h) (S : ℝ) :
    |tamedDriftStep b h S - eulerDriftStep b h S| ≤ h ^ 2 * b S ^ 2 := by
  unfold tamedDriftStep eulerDriftStep
  have hpos : 0 < 1 + h * |b S| := by positivity
  have e : S + h * b S / (1 + h * |b S|) - (S + h * b S) =
      -(h * b S * (h * |b S|)) / (1 + h * |b S|) := by
    field_simp
    ring
  rw [e, abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hh, abs_abs]
  have hb2 : |b S| * |b S| = b S ^ 2 := by rw [← sq, sq_abs]
  have h0 : 0 ≤ h * |b S| := by positivity
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg h) (sq_nonneg (b S))) h0]

/-- One tamed step for an inward drift (`S b(S) ≤ 0`) does not leave `[−max(|S|, 1), max(|S|, 1)]`:
the increment points towards `0` and is less than `1` in absolute value. -/
lemma abs_tamedDriftStep_le {b : ℝ → ℝ} (hb : ∀ S, S * b S ≤ 0) {h : ℝ} (hh : 0 ≤ h) (S : ℝ) :
    |tamedDriftStep b h S| ≤ max |S| 1 := by
  have hu1 := abs_lt.1 (abs_tamedDrift_lt b hh S)
  have hpos : 0 < 1 + h * |b S| := by positivity
  have hSu : S * (h * b S / (1 + h * |b S|)) ≤ 0 := by
    have e : S * (h * b S / (1 + h * |b S|)) = h * (S * b S) / (1 + h * |b S|) := by ring
    rw [e]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hh (hb S)) hpos.le
  unfold tamedDriftStep
  set u := h * b S / (1 + h * |b S|)
  have hm1 := le_max_left |S| 1
  have hm2 := le_max_right |S| 1
  have hS1 := le_abs_self S
  have hS2 := neg_abs_le S
  rw [abs_le]
  rcases le_or_gt u 0 with hu0 | hu0
  · constructor
    · rcases le_or_gt 0 S with hS | hS
      · linarith [hu1.1]
      · have : 0 ≤ u := by nlinarith
        linarith
    · linarith
  · have hS0 : S ≤ 0 := by nlinarith
    constructor <;> linarith [hu1.2]

/-- **The tamed scheme is stable for every timestep** (Giles 2015, §5.6, p. 44: "limits the size of
the drift term on each level of approximation when `S_t` is large, to avoid this instability").
For any drift pointing towards `0`, `S b(S) ≤ 0` (as `b(S) = −S³` of the paper's example), and
every timestep `h ≥ 0`, the tamed Euler iterates of `S` stay within `max(|S|, 1)`.  Deterministic
analogue only: for the cubic drift the second moment of the tamed Euler–Maruyama scheme is bounded
uniformly in the timestep (`tamedCubic_second_moment_le` in `MlmcLean/EulerSuperlinear.lean`); the
general uniform moment bounds of Hutzenthaler, Jentzen and Kloeden are not formalised. -/
theorem tamedDriftStep_iterate_bounded {b : ℝ → ℝ} (hb : ∀ S, S * b S ≤ 0) {h : ℝ}
    (hh : 0 ≤ h) (S : ℝ) (n : ℕ) : |(tamedDriftStep b h)^[n] S| ≤ max |S| 1 := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (abs_tamedDriftStep_le hb hh _).trans (max_le ih (le_max_right _ _))

/-- **Taming removes the instability of `dS_t = −S_t³ dt + dW_t`** (Giles 2015, §5.6, p. 44).  For
the drift `−S³` and every timestep `h ≥ 0`, the tamed Euler iterates of every `S` stay within
`max(|S|, 1)`, while the explicit iterates explode as soon as `hS² > 2`
(`eulerCubic_tendsto_atTop`). -/
theorem tamedCubic_bounded {h : ℝ} (hh : 0 ≤ h) (S : ℝ) (n : ℕ) :
    |(tamedDriftStep (fun S => -S ^ 3) h)^[n] S| ≤ max |S| 1 :=
  tamedDriftStep_iterate_bounded (fun S => by nlinarith [sq_nonneg (S ^ 2)]) hh S n

end taming

/-! ### §5.7: smoothing functions of either sign -/

section cdfBounded

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The smoothing error of the CDF for a smoothing function of either sign** (Giles 2015, §5.7,
p. 46: "`C_δ(x) = E[g((x − P)/δ)]`, where `g(x)` is a continuous function with `g(x) = 0` for
`x < −1`, and `g(x) = 1` for `x > 1`").  The paper does not ask for `0 ≤ g ≤ 1`, which
`abs_smoothCDF_sub_le` assumes.  If `|g| ≤ B`, `g = 0` on `(−∞, −1)` and `g = 1` on `(1, ∞)`, then
for `δ > 0` the smoothed CDF differs from the CDF `C(x) = P(P < x)` by at most
`(1 + B) P(|P − x| ≤ δ)`.  The constant is the supremum of `|g − H|` for `H` the Heaviside function,
which can be `1 + B` (`g = −B` just right of `0`); it is `1` when `0 ≤ g ≤ 1`. -/
theorem abs_smoothCDF_sub_le_of_bounded {P : Ω → ℝ} (hP : Measurable P) {g : ℝ → ℝ}
    (hgm : Measurable g) (hg0 : ∀ y < -1, g y = 0) (hg1 : ∀ y > 1, g y = 1) {B : ℝ}
    (hgB : ∀ y, |g y| ≤ B) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |smoothCDF μ P g δ x - μ.real {ω | P ω < x}| ≤ (1 + B) * μ.real {ω | |P ω - x| ≤ δ} := by
  have hA : MeasurableSet {ω | P ω < x} := measurableSet_lt hP measurable_const
  have hB : MeasurableSet {ω | |P ω - x| ≤ δ} :=
    measurableSet_le ((hP.sub measurable_const).abs) measurable_const
  have hgP : Measurable fun ω => g ((x - P ω) / δ) :=
    hgm.comp ((measurable_const.sub hP).div_const δ)
  have hgi : Integrable (fun ω => g ((x - P ω) / δ)) μ :=
    (integrable_const B).mono' hgP.aestronglyMeasurable
      (Eventually.of_forall fun ω => (Real.norm_eq_abs _).trans_le (hgB _))
  -- pointwise, the integrands differ only where `|P − x| ≤ δ`, and there by at most `1 + B`
  have hpt : ∀ ω, |g ((x - P ω) / δ) - Set.indicator {ω | P ω < x} (fun _ => (1 : ℝ)) ω| ≤
      Set.indicator {ω | |P ω - x| ≤ δ} (fun _ => 1 + B) ω := by
    intro ω
    have hb := hgB ((x - P ω) / δ)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases hω : |P ω - x| ≤ δ
    · rw [if_pos hω]
      by_cases hlt : P ω < x
      · rw [if_pos hlt]
        calc |g ((x - P ω) / δ) - 1| ≤ |g ((x - P ω) / δ)| + |1| := abs_sub _ _
          _ ≤ 1 + B := by rw [abs_one]; linarith
      · rw [if_neg hlt, sub_zero]
        linarith [abs_nonneg (g ((x - P ω) / δ))]
    · rw [if_neg hω]
      rw [not_le] at hω
      by_cases hlt : P ω < x
      · rw [if_pos hlt]
        rw [abs_of_neg (sub_neg.2 hlt)] at hω
        rw [hg1 _ (by rw [gt_iff_lt, lt_div_iff₀ hδ]; linarith), sub_self, abs_zero]
      · rw [if_neg hlt]
        rw [not_lt] at hlt
        rw [abs_of_nonneg (sub_nonneg.2 hlt)] at hω
        rw [hg0 _ (by rw [div_lt_iff₀ hδ]; linarith), sub_self, abs_zero]
  have hIA : ∫ ω, Set.indicator {ω | P ω < x} (fun _ => (1 : ℝ)) ω ∂μ =
      μ.real {ω | P ω < x} := by
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_one]
  have hIB : ∫ ω, Set.indicator {ω | |P ω - x| ≤ δ} (fun _ => 1 + B) ω ∂μ =
      (1 + B) * μ.real {ω | |P ω - x| ≤ δ} := by
    rw [integral_indicator_const _ hB, smul_eq_mul, mul_comm]
  rw [smoothCDF, ← hIA, ← hIB, ← integral_sub hgi ((integrable_const 1).indicator hA)]
  exact (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun ω => abs_nonneg _) ((integrable_const _).indicator hB)
    (Eventually.of_forall hpt))

/-- `P(|P − x| ≤ δ) → P(P = x) = 0` as `δ → 0⁺` when `P` has no atom at `x`. -/
lemma tendsto_measureReal_abs_sub_le {P : Ω → ℝ} (hP : Measurable P) (x : ℝ)
    (hx : μ {ω | P ω = x} = 0) :
    Tendsto (fun δ : ℝ => μ.real {ω | |P ω - x| ≤ δ}) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_measure_biInter_gt (μ := μ) (s := fun δ : ℝ => {ω | |P ω - x| ≤ δ})
    (a := 0) (fun r _ => (measurableSet_le ((hP.sub measurable_const).abs)
      measurable_const).nullMeasurableSet)
    (fun i j _ hij ω hω => le_trans hω hij) ⟨1, one_pos, measure_ne_top μ _⟩
  have hinter : (⋂ r > (0 : ℝ), {ω | |P ω - x| ≤ r}) = {ω | P ω = x} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h
      by_contra hne
      have hpos : 0 < |P ω - x| := abs_pos.2 (sub_ne_zero.2 hne)
      have := h (|P ω - x| / 2) (half_pos hpos)
      linarith
    · intro h r hr
      rw [h, sub_self, abs_zero]
      exact hr.le
  rw [hinter, hx] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def, measureReal_def] using this

/-- **"As `δ → 0` … the accuracy improves", for a bounded smoothing function of either sign**
(Giles 2015, §5.7, p. 46: "`g(x)` is a continuous function with `g(x) = 0` for `x < −1`, and
`g(x) = 1` for `x > 1` … As `δ → 0`, `g(x/δ) → H(x)`, and the accuracy improves").  With the
hypotheses of `abs_smoothCDF_sub_le_of_bounded` (`|g| ≤ B` in place of the `0 ≤ g ≤ 1` of
`tendsto_smoothCDF`), if `P` has no atom at `x`, then `C_δ(x) → C(x) = P(P < x)` as `δ → 0⁺`. -/
theorem tendsto_smoothCDF_of_bounded {P : Ω → ℝ} (hP : Measurable P) {g : ℝ → ℝ}
    (hgm : Measurable g) (hg0 : ∀ y < -1, g y = 0) (hg1 : ∀ y > 1, g y = 1) {B : ℝ}
    (hgB : ∀ y, |g y| ≤ B) (x : ℝ) (hx : μ {ω | P ω = x} = 0) :
    Tendsto (fun δ => smoothCDF μ P g δ x) (𝓝[>] 0) (𝓝 (μ.real {ω | P ω < x})) := by
  have h := (tendsto_measureReal_abs_sub_le hP x hx).const_mul (1 + B)
  rw [mul_zero] at h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun δ => norm_nonneg _) ?_ h
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [Real.norm_eq_abs]
  exact abs_smoothCDF_sub_le_of_bounded hP hgm hg0 hg1 hgB hδ x

/-- **"As `δ → 0` … the accuracy improves", with exactly the paper's smoothing functions** (Giles
2015, §5.7, p. 46: "`C_δ(x) = E[g((x − P)/δ)]`, where `g(x)` is a continuous function with
`g(x) = 0` for `x < −1`, and `g(x) = 1` for `x > 1` … As `δ → 0`, `g(x/δ) → H(x)`, and the accuracy
improves").  For every continuous `g` with `g = 0` on `(−∞, −1)` and `g = 1` on `(1, ∞)` (of either
sign: `g` is bounded by compactness of `[−1, 1]`), if `P` has no atom at `x` then
`C_δ(x) → C(x) = P(P < x)` as `δ → 0⁺`. -/
theorem tendsto_smoothCDF_of_continuous {P : Ω → ℝ} (hP : Measurable P) {g : ℝ → ℝ}
    (hg : Continuous g) (hg0 : ∀ y < -1, g y = 0) (hg1 : ∀ y > 1, g y = 1) (x : ℝ)
    (hx : μ {ω | P ω = x} = 0) :
    Tendsto (fun δ => smoothCDF μ P g δ x) (𝓝[>] 0) (𝓝 (μ.real {ω | P ω < x})) := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hg.continuousOn
  refine tendsto_smoothCDF_of_bounded hP hg.measurable hg0 hg1 (B := max M 1) (fun y => ?_) x hx
  by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
  · exact ((Real.norm_eq_abs _).symm.trans_le (hM y hy)).trans (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with hy | hy
    · rw [hg0 y hy, abs_zero]
      exact zero_le_one.trans (le_max_right _ _)
    · rw [hg1 y hy, abs_one]
      exact le_max_right _ _

end cdfBounded

/-! ### §5.7: the density of a multi-dimensional output -/

section densityMultidim

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {ν : Measure F} [ν.IsAddHaarMeasure]

omit [MeasurableSpace F] [BorelSpace F] in
/-- A function on a finite-dimensional space that vanishes outside the closed unit ball has compact
support. -/
lemma hasCompactSupport_of_norm_gt {g : F → ℝ} (hg0 : ∀ y, 1 < ‖y‖ → g y = 0) :
    HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_closedBall (0 : F) 1) fun y hy => hg0 y (by
    rwa [Metric.mem_closedBall, dist_zero_right, not_le] at hy)

omit [FiniteDimensional ℝ F] [ν.IsAddHaarMeasure] in
/-- `y ↦ c^d φ(c(x − y)) r(y)` is integrable for continuous `φ` with compact support and
integrable `r` (`d = dim F`). -/
lemma integrable_kernel_mul_multidim {φ : F → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {r : F → ℝ} (hr : Integrable r ν) (c : ℝ) (x : F) :
    Integrable (fun y => c ^ Module.finrank ℝ F * φ (c • (x - y)) * r y) ν := by
  obtain ⟨B, hB⟩ := hφs.exists_bound_of_continuous hφc
  refine hr.bdd_mul (c := |c| ^ Module.finrank ℝ F * B) ?_ (Eventually.of_forall fun y => ?_)
  · exact (continuous_const.mul (hφc.comp (continuous_const.smul
      (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · show ‖c ^ Module.finrank ℝ F * φ (c • (x - y))‖ ≤ |c| ^ Module.finrank ℝ F * B
    rw [norm_mul, norm_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

/-- The rescaled kernels `c^d φ(c(x − ·))` of a nonnegative `φ` with integral `1` vanishing outside
the unit ball are peak functions at `x`: `∫ c^d φ(c(x − y)) r(y) dy → r(x)` as `c → ∞` for
integrable `r` continuous at `x` (Mathlib's `tendsto_integral_comp_smul_smul_of_integrable'`, for
any additive Haar measure on a finite-dimensional space). -/
lemma tendsto_kernel_integral_multidim {φ : F → ℝ} (hφ0 : ∀ y, 0 ≤ φ y)
    (hφs : ∀ y, 1 < ‖y‖ → φ y = 0) (hφ1 : ∫ y, φ y ∂ν = 1) {r : F → ℝ} (hr : Integrable r ν)
    {x : F} (hrx : ContinuousAt r x) :
    Tendsto (fun c : ℝ => ∫ y, c ^ Module.finrank ℝ F * φ (c • (x - y)) * r y ∂ν) atTop
      (𝓝 (r x)) := by
  have hdecay : Tendsto (fun y : F => ‖y‖ ^ Module.finrank ℝ F * φ y) (Bornology.cobounded F)
      (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 1] with y hy
    show (0 : ℝ) = ‖y‖ ^ Module.finrank ℝ F * φ y
    rw [hφs y hy, mul_zero]
  have h := tendsto_integral_comp_smul_smul_of_integrable' hφ0 hφ1 hdecay hr hrx
  simp only [smul_eq_mul] at h
  exact h

/-- The same for a kernel `g` of either sign: `g` continuous, `g = 0` outside the unit ball and
`∫ g = 1`.  With `A = ∫ |g| ≥ 1`, `g = ((2A + 1) φ₁ − (2A − 1) φ₂)/2` for the nonnegative kernels
`φ₁ = (2|g| + g)/(2A + 1)` and `φ₂ = (2|g| − g)/(2A − 1)`, each of integral `1` (as in
`tendsto_kernel_integral_signed`). -/
lemma tendsto_kernel_integral_signed_multidim {g : F → ℝ} (hg : Continuous g)
    (hg0 : ∀ y, 1 < ‖y‖ → g y = 0) (hg1 : ∫ y, g y ∂ν = 1) {r : F → ℝ} (hr : Integrable r ν)
    {x : F} (hrx : ContinuousAt r x) :
    Tendsto (fun c : ℝ => ∫ y, c ^ Module.finrank ℝ F * g (c • (x - y)) * r y ∂ν) atTop
      (𝓝 (r x)) := by
  have hgi : Integrable g ν :=
    hg.integrable_of_hasCompactSupport (hasCompactSupport_of_norm_gt hg0)
  obtain ⟨A, hA_def⟩ : ∃ A, A = ∫ t, |g t| ∂ν := ⟨_, rfl⟩
  have hA : 1 ≤ A := by
    have h := (le_abs_self (∫ t, g t ∂ν)).trans (abs_integral_le_integral_abs (f := g))
    rwa [hg1, ← hA_def] at h
  have hp : (0 : ℝ) < 2 * A + 1 := by linarith
  have hm : (0 : ℝ) < 2 * A - 1 := by linarith
  have hc₁ : Continuous fun y => (2 * |g y| + g y) / (2 * A + 1) :=
    ((continuous_const.mul hg.abs).add hg).div_const _
  have hc₂ : Continuous fun y => (2 * |g y| - g y) / (2 * A - 1) :=
    ((continuous_const.mul hg.abs).sub hg).div_const _
  have hs₁ : ∀ y, 1 < ‖y‖ → (2 * |g y| + g y) / (2 * A + 1) = 0 := fun y hy => by
    rw [hg0 y hy, abs_zero, mul_zero, add_zero, zero_div]
  have hs₂ : ∀ y, 1 < ‖y‖ → (2 * |g y| - g y) / (2 * A - 1) = 0 := fun y hy => by
    rw [hg0 y hy, abs_zero, mul_zero, sub_zero, zero_div]
  have h₁ := tendsto_kernel_integral_multidim (φ := fun y => (2 * |g y| + g y) / (2 * A + 1))
    (fun y => div_nonneg (by linarith [abs_nonneg (g y), neg_abs_le (g y)]) hp.le) hs₁
    (by
      show ∫ y, (2 * |g y| + g y) / (2 * A + 1) ∂ν = 1
      rw [integral_div, integral_add (hgi.abs.const_mul 2) hgi, integral_const_mul, hg1,
        ← hA_def]
      exact div_self hp.ne')
    hr hrx
  have h₂ := tendsto_kernel_integral_multidim (φ := fun y => (2 * |g y| - g y) / (2 * A - 1))
    (fun y => div_nonneg (by linarith [abs_nonneg (g y), le_abs_self (g y)]) hm.le) hs₂
    (by
      show ∫ y, (2 * |g y| - g y) / (2 * A - 1) ∂ν = 1
      rw [integral_div, integral_sub (hgi.abs.const_mul 2) hgi, integral_const_mul, hg1,
        ← hA_def]
      exact div_self hm.ne')
    hr hrx
  have hlim := ((h₁.const_mul (2 * A + 1)).sub (h₂.const_mul (2 * A - 1))).div_const 2
  have e : ((2 * A + 1) * r x - (2 * A - 1) * r x) / 2 = r x := by ring
  rw [e] at hlim
  refine hlim.congr fun c => ?_
  have hi₁ := integrable_kernel_mul_multidim hc₁ (hasCompactSupport_of_norm_gt hs₁) hr c x
  have hi₂ := integrable_kernel_mul_multidim hc₂ (hasCompactSupport_of_norm_gt hs₂) hr c x
  try dsimp only
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hi₁.const_mul _) (hi₂.const_mul _), ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e₁ : (2 * A + 1) * (2 * A + 1)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have e₂ : (2 * A - 1) * (2 * A - 1)⁻¹ = 1 := mul_inv_cancel₀ hm.ne'
  show ((2 * A + 1) * (c ^ Module.finrank ℝ F *
      ((2 * |g (c • (x - y))| + g (c • (x - y))) / (2 * A + 1)) * r y) -
      (2 * A - 1) * (c ^ Module.finrank ℝ F *
      ((2 * |g (c • (x - y))| - g (c • (x - y))) / (2 * A - 1)) * r y)) / 2 =
    c ^ Module.finrank ℝ F * g (c • (x - y)) * r y
  linear_combination
    (c ^ Module.finrank ℝ F * (2 * |g (c • (x - y))| + g (c • (x - y))) * r y / 2) * e₁ -
    (c ^ Module.finrank ℝ F * (2 * |g (c • (x - y))| - g (c • (x - y))) * r y / 2) * e₂

/-- **The density of a multi-dimensional output as a limit** (Giles 2015, §5.7, p. 46: "the density
`ρ(x)` of the scalar output `P` is given by `ρ(x) = lim_{δ→0} E[δ⁻¹ g((x − P)/δ)]`, where `g(x)` is
a continuous function with `g(x) = 0` for `|x| > 1`, and `∫_{−1}^{1} g(x) dx = 1`.  This has
similarities with kernel density estimation (Silverman 1986), and can also be generalised to
multi-dimensional outputs").  Let `P` take values in a finite-dimensional real normed space `F` of
dimension `d`, with an additive Haar measure `ν` (Lebesgue measure on `ℝ^d`), and let the law of
`P` have a density `ρ` with respect to `ν` that is continuous at `x`.  If `g : F → ℝ` is continuous,
vanishes for `‖y‖ > 1` and has `∫ g dν = 1`, then `E[δ^{−d} g((x − P)/δ)] → ρ(x)` as `δ → 0⁺`.
The paper states no formula for `d > 1`; the normalisation `δ^{−d}` is the one that makes the
limit the density.  For `d = 1` this is `tendsto_density`. -/
theorem tendsto_density_multidim {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {P : Ω → F} (hP : Measurable P) {ρ : F → ℝ≥0} (hρm : Measurable ρ)
    (hlaw : μ.map P = ν.withDensity fun y => (ρ y : ℝ≥0∞)) {x : F}
    (hρx : ContinuousAt (fun y => (ρ y : ℝ)) x) {g : F → ℝ} (hg : Continuous g)
    (hg0 : ∀ y, 1 < ‖y‖ → g y = 0) (hg1 : ∫ y, g y ∂ν = 1) :
    Tendsto (fun δ : ℝ => ∫ ω, δ⁻¹ ^ Module.finrank ℝ F * g (δ⁻¹ • (x - P ω)) ∂μ) (𝓝[>] 0)
      (𝓝 (ρ x : ℝ)) := by
  -- the density has total mass one, so it is integrable
  have hmass : ∫⁻ y, (ρ y : ℝ≥0∞) ∂ν = 1 := by
    have h := congrArg (fun m : Measure F => m Set.univ) hlaw
    simp only [Measure.map_apply hP MeasurableSet.univ, Set.preimage_univ, measure_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h.symm
  have hr : Integrable (fun y => (ρ y : ℝ)) ν :=
    (integrable_toReal_of_lintegral_ne_top hρm.coe_nnreal_ennreal.aemeasurable
      (by rw [hmass]; exact ENNReal.one_ne_top)).congr (Eventually.of_forall fun _ => rfl)
  -- the expectation is an integral against the density
  have hE : ∀ δ : ℝ, ∫ ω, δ⁻¹ ^ Module.finrank ℝ F * g (δ⁻¹ • (x - P ω)) ∂μ =
      ∫ y, δ⁻¹ ^ Module.finrank ℝ F * g (δ⁻¹ • (x - y)) * (ρ y : ℝ) ∂ν := by
    intro δ
    have hmeas : Measurable fun y : F => δ⁻¹ ^ Module.finrank ℝ F * g (δ⁻¹ • (x - y)) :=
      (continuous_const.mul (hg.comp (continuous_const.smul
        (continuous_const.sub continuous_id)))).measurable
    rw [← integral_map hP.aemeasurable hmeas.aestronglyMeasurable, hlaw,
      integral_withDensity_eq_integral_smul hρm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, smul_eq_mul]
    ring
  exact ((tendsto_kernel_integral_signed_multidim hg hg0 hg1 hr hρx).comp
    tendsto_inv_nhdsGT_zero).congr fun δ => (hE δ).symm

/-- **The density of an `ℝ^d`-valued output as a limit** (Giles 2015, §5.7, p. 46: "`ρ(x) =
lim_{δ→0} E[δ⁻¹ g((x − P)/δ)]` … can also be generalised to multi-dimensional outputs"): for
`P : Ω → ℝ^d` (`EuclideanSpace ℝ (Fin d)`, with Lebesgue measure) whose law has a density `ρ`
continuous at `x`, and `g` continuous with `g(y) = 0` for `‖y‖ > 1` and `∫ g = 1`,
`E[δ^{−d} g((x − P)/δ)] → ρ(x)` as `δ → 0⁺` (`tendsto_density_multidim`). -/
theorem tendsto_density_euclidean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} {P : Ω → EuclideanSpace ℝ (Fin d)} (hP : Measurable P)
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ≥0} (hρm : Measurable ρ)
    (hlaw : μ.map P = volume.withDensity fun y => (ρ y : ℝ≥0∞)) {x : EuclideanSpace ℝ (Fin d)}
    (hρx : ContinuousAt (fun y => (ρ y : ℝ)) x) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : Continuous g) (hg0 : ∀ y, 1 < ‖y‖ → g y = 0) (hg1 : ∫ y, g y = 1) :
    Tendsto (fun δ : ℝ => ∫ ω, δ⁻¹ ^ d * g (δ⁻¹ • (x - P ω)) ∂μ) (𝓝[>] 0) (𝓝 (ρ x : ℝ)) := by
  have h := tendsto_density_multidim hP hρm hlaw hρx hg hg0 hg1
  rwa [finrank_euclideanSpace_fin] at h

end densityMultidim

end MLMC
