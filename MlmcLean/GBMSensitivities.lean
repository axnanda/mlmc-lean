import MlmcLean.GBMDigitalCondExp
import MlmcLean.InverseNormal

/-!
# Sensitivities: the delta of the call and of the digital option for GBM (Giles 2015, §5.4)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.4
"Computing sensitivities", p. 42, l. 1819–1835 of `docs/giles2015.txt`.  Geometric Brownian
motion `dS = rS dt + σS dW`, `S_0 = s₀`; the level-`ℓ` Euler–Maruyama and Milstein values
`gbmEM`, `gbmMil` (`2^ℓ` steps of size `h_ℓ = T 2^{−ℓ}`) and the exact solution `gbmExact`, all
driven by the same increments `Z_i ∼ N(0,1)` (`stdNormalSeq`), the coarse path of a sample driven
by the summed increments (`pairAvg`).  The sensitivity is the delta `∂/∂s₀`.  For GBM every path
is linear in `s₀`, `Ŝ(s₀) = s₀ Ŝ(1)` (`gbmEM_eq_mul_one`, `gbmMil_eq_mul_one`,
`gbmExact_eq_mul_one`), so the "linearised perturbation to the underlying path evolution"
(l. 1824–1825), the tangent process, is `∂Ŝ/∂s₀ = Ŝ(1) = Ŝ/s₀`.

**What is proved.**
* **Pathwise sensitivities (G5.4-01, l. 1820–1825).**  `gbm_em_call_pathwise_delta`,
  `gbm_mil_call_pathwise_delta`: for `σ ≠ 0`, `T > 0` and `s₀ ≠ 0` or `K ≠ 0`, the call payoff
  `(Ŝ_N(s) − K)⁺` of the discretised path is a.s. differentiable at `s₀` with pathwise delta
  `1_{Ŝ_N(s₀) > K} Ŝ_N(1)`, both are integrable, and
  `d/ds₀ E[(Ŝ_N − K)⁺] = E[1_{Ŝ_N > K} Ŝ_N(1)]` (differentiation under the integral,
  `hasDerivAt_integral_call_mul`; `Ŝ_N(1)` has no atoms, `stdNormalSeq_prod_eq_null`);
  `gbm_call_delta`: the same for the exact solution, so `E[1_{S_T(s₀) > K} S_T(1)]` (`S_T(1)` the
  path from the initial value `1`) is the true delta when `s₀ ≠ 0 ∨ K ≠ 0`.
* **The derivative of the call payoff is discontinuous (G5.4-02, l. 1826–1827)**:
  `hasDerivAt_call_payoff` (`MlmcLean.SDEDigital`); so the pathwise delta is a digital payoff
  times the tangent, `1_{x > K} x = (x − K)⁺ + K 1_{x > K}` (`indicator_mul_self_eq`).
* **"Similar difficulties to … a digital option" (G5.4-03, l. 1828–1829).**  The correction
  `D_ℓ = 1_{Ŝ^f > K} Ŝ^f(1) − 1_{Ŝ^c > K} Ŝ^c(1)` (`= (1_{Ŝ^f > K} Ŝ^f − 1_{Ŝ^c > K} Ŝ^c)/s₀`)
  is square integrable with `V[D_ℓ] ≤ C h_{ℓ+1}^q` for every `q < ½` (Euler–Maruyama,
  `gbm_em_call_delta_rate`) and every `q < 1` (Milstein, `gbm_mil_call_delta_rate`): the bounds
  proved are those of the digital option (`gbm_em_digital_rate`, `gbm_mil_digital_rate`); the
  call's rates (`O(h)`, `O(h²)`) are not claimed for the delta; the weak errors are `O(h^q)`
  (`gbm_em_call_delta_weak_rate`, `gbm_mil_call_delta_weak_rate`); Theorem 1 end to end for the
  multilevel estimator of the delta: cost `O(ε^{−3−η})` (`gbm_em_call_delta_theorem1`) and
  `O(ε^{−2−η})` with the natural Milstein estimator (`gbm_mil_call_delta_theorem1`), for every
  `η > 0`, as for the digital option (`gbm_em_digital_theorem1`, `gbm_mil_digital_theorem1`).
* **Digital sensitivities via the conditional expectation (G5.4-04, l. 1829–1832).**  The pathwise
  sensitivities `∂P^f_ℓ/∂s₀ = φ((m_f − K)/s_f) K/(s₀ s_f)` (`gbmDigitalCondFineDelta`) and
  `∂P^c_ℓ/∂s₀` (`gbmDigitalCondCoarseDelta`) of the conditional-expectation payoffs `P^f_ℓ`,
  `P^c_ℓ` of §5.2 (`gbmDigitalCondFine`, `gbmDigitalCondCoarse`).  `gbm_digital_condExp_delta`:
  for `s₀ ≠ 0`, `σ ≠ 0`, `T > 0` they are a.s. the derivatives, square integrable, unbiased
  (`d/ds₀ E[P^f_ℓ] = E[∂P^f_ℓ/∂s₀]`, the same for `P^c_ℓ`), and satisfy (2.4):
  `E[∂P^f_ℓ/∂s₀] = E[∂P^c_ℓ/∂s₀]`; `gbm_digital_condExp_delta_telescope`: the means of the level
  corrections sum to `d/ds₀ P(Ŝ^f_N > K)`, the delta of the digital price of the finest level.  The
  key bound is `abs_pdf_mul_div_le`: `|φ(u) K/(s₀ s_f)| ≤ (|m_f(1)|/s_f(1) + 1)/|s₀|`, the
  Gaussian factor compensating `1/s_f`, which gives a domination on a neighbourhood of `s₀`
  (`hasDerivAt_integral_cdf_mul_div`).

**Deviations.**
* GBM only, and the delta only: the paper (and Burgos and Giles 2012, which it cites for the
  details, l. 1833–1835) treats general SDEs and Greeks; for GBM the tangent process is `Ŝ/s₀`.
  It is written `Ŝ(1)` (the path from the initial value `1`), which avoids a division by `s₀`.
* The rates are those of the digital option up to an arbitrarily small loss in the exponent
  (`q < ½`, `q < 1`, not the endpoints), and the costs carry the loss `η > 0`; the constants depend
  on `s₀` and `K`.  "Similar difficulties" is formalised by these upper bounds; that the call delta
  is not better than the digital option (a lower bound on `V_ℓ`) is not proved.
* The payoffs are undiscounted (the factor `e^{−rT}` is omitted).  The hypotheses: `T > 0`
  throughout; `σ ≠ 0` for the derivatives (otherwise the paths are deterministic and the payoff
  is not differentiable at the `s₀` with `Ŝ(s₀) = K`), the weak rates and Theorem 1 (for `σ = 0`,
  `s₀ = −1`, `r = T = 1`, `K = −e` the pathwise delta of the scheme tends to `e`, while the
  integral formula gives `0`; the price `max(s e + e, 0)` is not differentiable there, with
  one-sided derivatives `0` and `e`; for `σ = 0` the statements can fail only at the kink
  `s₀ e^{rT} = K`), but not for the variance rates (`V_ℓ = 0` for `σ = 0`); `s₀ ≠ 0` or `K ≠ 0` for
  the call (for `s₀ = K = 0` the call price is not differentiable at `0`); `s₀ ≠ 0` for the
  conditional-expectation payoffs (which jump at `s₀ = 0`).

**What is not proved.**  The variance of the digital-delta corrections `∂P^f_ℓ/∂s₀ −
∂P^c_{ℓ−1}/∂s₀` (the paper gives no rate: it defers to Burgos 2014, l. 1834–1835; heuristically
and numerically `V_ℓ ≈ O(h^{1/2})`) and Theorem 1 for them; the convergence of
`d/ds₀ P(Ŝ^f_N > K)` to the true digital delta as `L → ∞` (a convergence of densities at the
strike).
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### Atomless products of independent factors -/

/-- **A product of independent atomless factors is atomless** (the tool behind the a.e.
differentiability of the pathwise sensitivities, Giles 2015, §5.4, p. 42, l. 1820–1825).  If
`F(Z)` has no atoms for `Z ∼ N(0,1)`, then `P(∏_{i ≤ n} F(Z_i) = c) = 0` for every `c` and `n`
under `N(0,1)^{⊗ℕ}`: for `c = 0` some factor vanishes; for `c ≠ 0` the last factor is independent
of the others and `P(x F(Z_n) = c) = 0` for every `x`. -/
lemma stdNormalSeq_prod_eq_null {F : ℝ → ℝ} (hF : Measurable F)
    (hFa : ∀ c, gaussianReal 0 1 (F ⁻¹' {c}) = 0) (n : ℕ) (c : ℝ) :
    stdNormalSeq {z | ∏ i ∈ range (n + 1), F (z i) = c} = 0 := by
  have hev : ∀ i, MeasurePreserving (fun z : ℕ → ℝ => z i) stdNormalSeq (gaussianReal 0 1) :=
    fun i => measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i
  have hfac : ∀ i c, stdNormalSeq {z : ℕ → ℝ | F (z i) = c} = 0 := fun i c => by
    have e : {z : ℕ → ℝ | F (z i) = c} = (fun z : ℕ → ℝ => z i) ⁻¹' (F ⁻¹' {c}) := rfl
    rw [e, (hev i).measure_preimage (hF (measurableSet_singleton c)).nullMeasurableSet]
    exact hFa c
  rcases eq_or_ne c 0 with rfl | hc
  · refine measure_mono_null (fun z hz => ?_)
      ((measure_biUnion_null_iff (Finset.countable_toSet (range (n + 1)))).2
        fun i _ => hfac i 0)
    obtain ⟨i, hi, h0⟩ := Finset.prod_eq_zero_iff.1 hz
    exact Set.mem_biUnion (Finset.mem_coe.2 hi) h0
  · set X : (ℕ → ℝ) → ℝ := fun z => ∏ i ∈ range n, F (z i) with hXdef
    have hXm : Measurable X :=
      Finset.measurable_prod _ fun i _ => hF.comp (measurable_pi_apply i)
    have hind : IndepFun X (fun z => z n) stdNormalSeq :=
      indepFun_incr_of_eq_lt hXm fun z z' h =>
        Finset.prod_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable
      (measurable_pi_apply n).aemeasurable).1 hind
    set S : Set (ℝ × ℝ) := {p | p.1 * F p.2 = c} with hSdef
    have hS : MeasurableSet S :=
      measurableSet_eq_fun (measurable_fst.mul (hF.comp measurable_snd)) measurable_const
    have e : {z : ℕ → ℝ | ∏ i ∈ range (n + 1), F (z i) = c} =
        (fun z => (X z, z n)) ⁻¹' S := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, hSdef, hXdef, Finset.prod_range_succ]
    have h0 : ∀ x : ℝ, gaussianReal 0 1 (Prod.mk x ⁻¹' S) = 0 := fun x => by
      rcases eq_or_ne x 0 with rfl | hx
      · have he : Prod.mk (0 : ℝ) ⁻¹' S = ∅ := by
          ext y
          simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, zero_mul,
            Set.mem_empty_iff_false, iff_false]
          exact fun h => hc h.symm
        rw [he, measure_empty]
      · have he : Prod.mk x ⁻¹' S = F ⁻¹' {c / x} := by
          ext y
          simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, Set.mem_singleton_iff]
          rw [eq_div_iff hx, mul_comm]
        rw [he]
        exact hFa _
    rw [e, ← Measure.map_apply (hXm.prodMk (measurable_pi_apply n)) hS, hmap,
      Measure.prod_apply hS, (hev n).map_eq]
    simp only [h0, lintegral_zero]

/-- The Euler–Maruyama step `1 + rh + σ√h Z` of GBM has no atoms for `σ ≠ 0`, `h > 0` (Giles 2015,
§5.1): it is a non-constant affine function of `Z ∼ N(0,1)`. -/
lemma gaussianReal_gbmEMFactor_preimage (r σ : ℝ) {h : ℝ} (hσ : σ ≠ 0) (hh : 0 < h) (c : ℝ) :
    gaussianReal 0 1 ((fun x => gbmEMFactor r σ h x) ⁻¹' {c}) = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hs : σ * Real.sqrt h ≠ 0 := mul_ne_zero hσ (Real.sqrt_pos.2 hh).ne'
  refine measure_mono_null (t := {(c - 1 - r * h) / (σ * Real.sqrt h)}) (fun x hx => ?_)
    (measure_singleton _)
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
  unfold gbmEMFactor at hx
  rw [Set.mem_singleton_iff, eq_div_iff hs]
  linarith

/-- The Milstein step `1 + rh + σ√h Z + ½σ²h(Z² − 1)` of GBM has no atoms for `σ ≠ 0`, `h > 0`
(Giles 2015, §5.2): it is a quadratic in `Z ∼ N(0,1)` with leading coefficient `σ²h/2 ≠ 0`. -/
lemma gaussianReal_gbmMilFactor_preimage (r σ : ℝ) {h : ℝ} (hσ : σ ≠ 0) (hh : 0 < h) (c : ℝ) :
    gaussianReal 0 1 ((fun x => gbmMilFactor r σ h x) ⁻¹' {c}) = 0 := by
  have hc : σ ^ 2 / 2 * Real.sqrt h ^ 2 ≠ 0 := by
    have : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
    positivity
  have hae := ae_gaussian_quadratic_ne_zero (c₁ := σ * Real.sqrt h)
    (c₀ := 1 + r * h - σ ^ 2 * h / 2 - c) hc
  refine measure_mono_null (fun x hx => ?_) (measure_eq_zero_iff_ae_notMem.2 hae)
  rw [Set.mem_preimage, Set.mem_singleton_iff, gbmMilFactor_eq_quadratic] at hx
  show _ = _
  linear_combination hx

/-- `P(s₀ Y = K) = 0` for `Y = ∏_{i ≤ n} F(Z_i)` with atomless `F(Z)`, provided `s₀ ≠ 0` or
`K ≠ 0` (for `s₀ = 0 = K` the event is everything) (Giles 2015, §5.4, p. 42, l. 1820–1825). -/
lemma stdNormalSeq_mul_eq_null {F : ℝ → ℝ} (hF : Measurable F)
    (hFa : ∀ c, gaussianReal 0 1 (F ⁻¹' {c}) = 0) {n : ℕ} {Y : (ℕ → ℝ) → ℝ}
    (hY : ∀ z, Y z = ∏ i ∈ range (n + 1), F (z i)) {s₀ K : ℝ} (hsK : s₀ ≠ 0 ∨ K ≠ 0) :
    stdNormalSeq {z | s₀ * Y z = K} = 0 := by
  rcases eq_or_ne s₀ 0 with rfl | hs₀
  · have hK : K ≠ 0 := hsK.resolve_left (not_not.2 rfl)
    have he : {z : ℕ → ℝ | 0 * Y z = K} = ∅ := by
      ext z
      simp only [zero_mul, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hK h.symm
    rw [he, measure_empty]
  · refine measure_mono_null (fun z hz => ?_) (stdNormalSeq_prod_eq_null hF hFa n (K / s₀))
    have hz' : s₀ * Y z = K := hz
    show ∏ i ∈ range (n + 1), F (z i) = K / s₀
    rw [← hY z, eq_div_iff hs₀, mul_comm]
    exact hz'

/-! ### The pathwise sensitivity of the call: differentiation under the integral -/

/-- **The pathwise derivative of the call payoff along a path linear in `s₀`** (Giles 2015, §5.4,
p. 42, l. 1820–1825; `hasDerivAt_call_payoff`): if `s₀ y ≠ K`, then
`d/ds (s y − K)⁺ = 1_{s₀ y > K} y` at `s = s₀`. -/
lemma hasDerivAt_call_mul (K y s₀ : ℝ) (h : s₀ * y ≠ K) :
    HasDerivAt (fun s => max (s * y - K) 0) ((Set.Ioi K).indicator 1 (s₀ * y) * y) s₀ := by
  have h1 := (hasDerivAt_call_payoff K).1 (s₀ * y) h
  have h2 : HasDerivAt (fun s => s * y) y s₀ := by
    simpa using (hasDerivAt_id s₀).mul_const y
  exact h1.comp s₀ h2

/-- **Pathwise sensitivity analysis for the call with a path linear in `s₀`** (Giles 2015, §5.4,
p. 42, l. 1820–1825: "pathwise sensitivity analysis … which considers linearised perturbations to
the underlying path evolution, and the consequential perturbation to the payoff").  On a finite
measure space let `Y` be integrable and the path be `S(s) = s Y` (so `∂S/∂s = Y`).  If
`μ(s₀ Y = K) = 0`, then the call payoff `(s Y − K)⁺` is a.e. differentiable at `s₀` with
derivative `1_{s₀ Y > K} Y`, it is integrable for every `s`, the derivative is integrable, and
`d/ds E[(s Y − K)⁺] = E[1_{s₀ Y > K} Y]` at `s₀` (dominated differentiation, the payoff being
`|Y|`-Lipschitz in `s`). -/
lemma hasDerivAt_integral_call_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y : Ω → ℝ} (hYm : Measurable Y) (hY : Integrable Y μ) {s₀ K : ℝ}
    (hnull : μ {ω | s₀ * Y ω = K} = 0) :
    (∀ᵐ ω ∂μ, HasDerivAt (fun s => max (s * Y ω - K) 0)
      ((Set.Ioi K).indicator 1 (s₀ * Y ω) * Y ω) s₀) ∧
    (∀ s, Integrable (fun ω => max (s * Y ω - K) 0) μ) ∧
    Integrable (fun ω => (Set.Ioi K).indicator 1 (s₀ * Y ω) * Y ω) μ ∧
    HasDerivAt (fun s => ∫ ω, max (s * Y ω - K) 0 ∂μ)
      (∫ ω, (Set.Ioi K).indicator 1 (s₀ * Y ω) * Y ω ∂μ) s₀ := by
  have hdiff : ∀ᵐ ω ∂μ, HasDerivAt (fun s => max (s * Y ω - K) 0)
      ((Set.Ioi K).indicator 1 (s₀ * Y ω) * Y ω) s₀ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω
    exact hasDerivAt_call_mul K (Y ω) s₀ hω
  have hFm : ∀ s, Measurable fun ω => max (s * Y ω - K) 0 := fun s => by fun_prop
  have hint : ∀ s, Integrable (fun ω => max (s * Y ω - K) 0) μ := fun s => by
    refine ((hY.abs.const_mul |s|).add (integrable_const |K|)).mono'
      (hFm s).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    show max (s * Y ω - K) 0 ≤ |s| * |Y ω| + |K|
    refine max_le ?_ (by positivity)
    have h1 : s * Y ω ≤ |s| * |Y ω| := by rw [← abs_mul]; exact le_abs_self _
    have h2 : -K ≤ |K| := neg_le_abs K
    linarith
  have hF'm : Measurable fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (s₀ * Y ω) * Y ω :=
    ((measurable_one.indicator measurableSet_Ioi).comp (hYm.const_mul s₀)).mul hYm
  have hlip : ∀ ω, LipschitzOnWith (Real.nnabs |Y ω|) (fun s => max (s * Y ω - K) 0)
      Set.univ := fun ω => by
    refine (LipschitzWith.of_dist_le_mul fun s t => ?_).lipschitzOnWith
    rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_abs]
    calc |max (s * Y ω - K) 0 - max (t * Y ω - K) 0| ≤ |(s * Y ω - K) - (t * Y ω - K)| :=
          abs_max_sub_max_le_abs _ _ _
      _ = |Y ω| * |s - t| := by rw [← abs_mul]; congr 1; ring
  obtain ⟨hI, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (F := fun s ω => max (s * Y ω - K) 0) (x₀ := s₀) (bound := fun ω => |Y ω|)
    Filter.univ_mem (Eventually.of_forall fun s => (hFm s).aestronglyMeasurable) (hint s₀)
    hF'm.aestronglyMeasurable (Eventually.of_forall hlip) hY.abs hdiff
  exact ⟨hdiff, hint, hI, hD⟩

/-- The Euler–Maruyama path of GBM is linear in the initial value: `Ŝ_N(s) = s Ŝ_N(1)`, so its
tangent process `∂Ŝ_N/∂s₀` is `Ŝ_N(1)` (`= Ŝ_N/s₀` for `s₀ ≠ 0`) (Giles 2015, §5.4, p. 42,
l. 1820–1825). -/
lemma gbmEM_eq_mul_one (r σ T s : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmEM r σ T s ℓ z = s * gbmEM r σ T 1 ℓ z := by
  rw [gbmEM_eq_prod, gbmEM_eq_prod, one_mul]

/-- The Milstein path of GBM is linear in the initial value: `Ŝ_N(s) = s Ŝ_N(1)` (Giles 2015,
§5.4, p. 42, l. 1820–1825). -/
lemma gbmMil_eq_mul_one (r σ T s : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmMil r σ T s ℓ z = s * gbmMil r σ T 1 ℓ z := by
  rw [gbmMil_eq_prod, gbmMil_eq_prod, one_mul]

/-- **The pathwise delta of the call for the Euler–Maruyama discretisation of GBM** (Giles 2015,
§5.4, p. 42, l. 1820–1829: "When the option payoff is continuous, the standard Monte Carlo
approach is pathwise sensitivity analysis … which considers linearised perturbations to the
underlying path evolution, and the consequential perturbation to the payoff. … the derivative of
a call option payoff function is discontinuous").  For `dS = rS dt + σS dW`, `σ ≠ 0`, `T > 0`, the
level-`ℓ` Euler–Maruyama value `Ŝ_N(s₀)` (`N = 2^ℓ` steps of size `T 2^{−ℓ}`) is
`s₀ Ŝ_N(1)`, so the linearised perturbation of the path is `∂Ŝ_N/∂s₀ = Ŝ_N(1)` (`= Ŝ_N/s₀` for
`s₀ ≠ 0`).  If `s₀ ≠ 0` or `K ≠ 0`:
* for almost every path, `s ↦ (Ŝ_N(s) − K)⁺` is differentiable at `s₀` with derivative
  `1_{Ŝ_N(s₀) > K} Ŝ_N(1)`: the pathwise delta is a digital payoff times the tangent `Ŝ_N(1)`;
* the payoff and the pathwise delta are integrable, and
  `d/ds₀ E[(Ŝ_N(s₀) − K)⁺] = E[1_{Ŝ_N(s₀) > K} Ŝ_N(1)]`: the pathwise estimator is unbiased.
The a.e. differentiability uses that `Ŝ_N(1)` is a product of independent non-degenerate affine
functions of normals, hence has no atoms (`stdNormalSeq_prod_eq_null`).  For `s₀ = K = 0` the
expected payoff `E[(s Ŝ_N(1))⁺]` has the one-sided derivatives `E[Ŝ_N(1)⁺]` and `−E[Ŝ_N(1)⁻]` at
`0`, which differ as `Ŝ_N(1) ≠ 0` a.s., whence the hypothesis; `σ ≠ 0`, `T > 0` exclude
deterministic paths, for which differentiability fails at `s₀ = K/Ŝ_N(1)`. -/
theorem gbm_em_call_pathwise_delta (r σ K : ℝ) {T s₀ : ℝ} (hσ : σ ≠ 0) (hT : 0 < T)
    (hsK : s₀ ≠ 0 ∨ K ≠ 0) (ℓ : ℕ) :
    (∀ s z, gbmEM r σ T s ℓ z = s * gbmEM r σ T 1 ℓ z) ∧
    (∀ᵐ z ∂stdNormalSeq, HasDerivAt (fun s => max (gbmEM r σ T s ℓ z - K) 0)
      ((Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z) * gbmEM r σ T 1 ℓ z) s₀) ∧
    (∀ s, Integrable (fun z => max (gbmEM r σ T s ℓ z - K) 0) stdNormalSeq) ∧
    Integrable (fun z => (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z) * gbmEM r σ T 1 ℓ z)
      stdNormalSeq ∧
    HasDerivAt (fun s => ∫ z, max (gbmEM r σ T s ℓ z - K) 0 ∂stdNormalSeq)
      (∫ z, (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z) * gbmEM r σ T 1 ℓ z ∂stdNormalSeq)
      s₀ := by
  have hh : 0 < T / 2 ^ ℓ := by positivity
  have hnull : stdNormalSeq {z | s₀ * gbmEM r σ T 1 ℓ z = K} = 0 :=
    stdNormalSeq_mul_eq_null (measurable_gbmEMFactor r σ (T / 2 ^ ℓ))
      (gaussianReal_gbmEMFactor_preimage r σ hσ hh) (n := 2 ^ ℓ - 1)
      (fun z => by rw [gbmEM_eq_prod, one_mul, ← two_pow_eq_sub_one_add_one]) hsK
  obtain ⟨h1, h2, h3, h4⟩ := hasDerivAt_integral_call_mul (measurable_gbmEM r σ T 1 ℓ)
    ((memLp_gbmEM r σ T 1 ℓ).integrable one_le_two) hnull
  refine ⟨fun s z => gbmEM_eq_mul_one r σ T s ℓ z, ?_⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = gbmEM r σ T 1 ℓ := ⟨_, rfl⟩
  have hS : ∀ s z, gbmEM r σ T s ℓ z = s * Y z := fun s z => by
    rw [hYdef]
    exact gbmEM_eq_mul_one r σ T s ℓ z
  rw [← hYdef] at h1 h2 h3 h4
  simp only [hS, one_mul]
  exact ⟨h1, h2, h3, h4⟩

/-- **The pathwise delta of the call for the Milstein discretisation of GBM** (Giles 2015, §5.4,
p. 42, l. 1820–1829: pathwise sensitivity analysis "considers linearised perturbations to the
underlying path evolution, and the consequential perturbation to the payoff. … the derivative of
a call option payoff function is discontinuous"), as `gbm_em_call_pathwise_delta` with the
level-`ℓ` Milstein value `Ŝ_N(s₀) = s₀ Ŝ_N(1)`: if `s₀ ≠ 0` or `K ≠ 0`, then a.e.
`d/ds (Ŝ_N(s) − K)⁺ = 1_{Ŝ_N(s₀) > K} Ŝ_N(1)` at `s₀`, both are integrable and
`d/ds₀ E[(Ŝ_N(s₀) − K)⁺] = E[1_{Ŝ_N(s₀) > K} Ŝ_N(1)]`.  The Milstein step is a non-degenerate
quadratic in the normal increment, so `Ŝ_N(1)` has no atoms
(`gaussianReal_gbmMilFactor_preimage`, `stdNormalSeq_prod_eq_null`). -/
theorem gbm_mil_call_pathwise_delta (r σ K : ℝ) {T s₀ : ℝ} (hσ : σ ≠ 0) (hT : 0 < T)
    (hsK : s₀ ≠ 0 ∨ K ≠ 0) (ℓ : ℕ) :
    (∀ s z, gbmMil r σ T s ℓ z = s * gbmMil r σ T 1 ℓ z) ∧
    (∀ᵐ z ∂stdNormalSeq, HasDerivAt (fun s => max (gbmMil r σ T s ℓ z - K) 0)
      ((Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ z) * gbmMil r σ T 1 ℓ z) s₀) ∧
    (∀ s, Integrable (fun z => max (gbmMil r σ T s ℓ z - K) 0) stdNormalSeq) ∧
    Integrable (fun z => (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ z) * gbmMil r σ T 1 ℓ z)
      stdNormalSeq ∧
    HasDerivAt (fun s => ∫ z, max (gbmMil r σ T s ℓ z - K) 0 ∂stdNormalSeq)
      (∫ z, (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ z) * gbmMil r σ T 1 ℓ z ∂stdNormalSeq)
      s₀ := by
  have hh : 0 < T / 2 ^ ℓ := by positivity
  have hnull : stdNormalSeq {z | s₀ * gbmMil r σ T 1 ℓ z = K} = 0 :=
    stdNormalSeq_mul_eq_null (measurable_gbmMilFactor r σ (T / 2 ^ ℓ))
      (gaussianReal_gbmMilFactor_preimage r σ hσ hh) (n := 2 ^ ℓ - 1)
      (fun z => by rw [gbmMil_eq_prod, one_mul, ← two_pow_eq_sub_one_add_one]) hsK
  obtain ⟨h1, h2, h3, h4⟩ := hasDerivAt_integral_call_mul (measurable_gbmMil r σ T 1 ℓ)
    ((memLp_gbmMil r σ T 1 ℓ).integrable one_le_two) hnull
  refine ⟨fun s z => gbmMil_eq_mul_one r σ T s ℓ z, ?_⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = gbmMil r σ T 1 ℓ := ⟨_, rfl⟩
  have hS : ∀ s z, gbmMil r σ T s ℓ z = s * Y z := fun s z => by
    rw [hYdef]
    exact gbmMil_eq_mul_one r σ T s ℓ z
  rw [← hYdef] at h1 h2 h3 h4
  simp only [hS, one_mul]
  exact ⟨h1, h2, h3, h4⟩

/-- **The true delta of the call for GBM** (Giles 2015, §5.4, p. 42, l. 1820–1825: "When the option
payoff is continuous, the standard Monte Carlo approach is pathwise sensitivity analysis …
which considers linearised perturbations to the underlying path evolution, and the consequential
perturbation to the payoff"; here for the exact solution `S_T(s₀) = s₀ e^{(r−σ²/2)T + σ√T Z}`,
`Z ∼ N(0,1)`).  For `σ ≠ 0`, `T > 0` and `s₀ ≠ 0` or `K ≠ 0`: for a.e. `Z`,
`d/ds (S_T(s) − K)⁺ = 1_{S_T(s₀) > K} S_T(1)` at `s₀` (`S_T(1)` the path from the initial value
`1`, the tangent process), the payoff and this pathwise delta are integrable, and
`d/ds₀ E[(S_T(s₀) − K)⁺] = E[1_{S_T(s₀) > K} S_T(1)]`. -/
theorem gbm_call_delta (r σ K : ℝ) {T s₀ : ℝ} (hσ : σ ≠ 0) (hT : 0 < T)
    (hsK : s₀ ≠ 0 ∨ K ≠ 0) :
    (∀ᵐ w ∂gaussianReal 0 1, HasDerivAt
      (fun s => max (s * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) - K) 0)
      ((Set.Ioi K).indicator 1 (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
        Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) s₀) ∧
    (∀ s, Integrable (fun w =>
      max (s * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) - K) 0)
      (gaussianReal 0 1)) ∧
    Integrable (fun w =>
      (Set.Ioi K).indicator 1 (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
        Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) (gaussianReal 0 1) ∧
    HasDerivAt (fun s => ∫ w,
      max (s * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) - K) 0 ∂gaussianReal 0 1)
      (∫ w, (Set.Ioi K).indicator 1
          (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
        Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) ∂gaussianReal 0 1) s₀ := by
  set E : ℝ → ℝ := fun w => Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) with hE
  have hEm : Measurable E := by fun_prop
  have hEi : Integrable E (gaussianReal 0 1) := by
    have e : E = fun w => Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp (σ * Real.sqrt T * w) := by
      funext w
      rw [hE, ← Real.exp_add, mul_assoc]
    rw [e]
    exact (integrable_exp_mul_gaussianReal _).const_mul _
  have hsT : σ * Real.sqrt T ≠ 0 := mul_ne_zero hσ (Real.sqrt_pos.2 hT).ne'
  have hnull : gaussianReal 0 1 {w | s₀ * E w = K} = 0 := by
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    refine Set.Subsingleton.measure_zero (fun w₁ hw₁ w₂ hw₂ => ?_) _
    have h1 : s₀ * E w₁ = K := hw₁
    have h2 : s₀ * E w₂ = K := hw₂
    have hs₀ : s₀ ≠ 0 := by
      rintro rfl
      rw [zero_mul] at h1
      exact hsK.elim (fun h => h rfl) fun h => h h1.symm
    have h3 : E w₁ = E w₂ := mul_left_cancel₀ hs₀ (h1.trans h2.symm)
    rw [hE] at h3
    have h4 := Real.exp_injective h3
    have h5 : σ * Real.sqrt T * (w₁ - w₂) = 0 := by linear_combination h4
    exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left hsT)
  exact hasDerivAt_integral_call_mul hEm hEi hnull

/-! ### The call delta has the difficulties of the digital option -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `V[X + Y] ≤ 2 V[X] + 2 V[Y]` for square-integrable `X`, `Y` (Giles 2015, §5.1, p. 29,
l. 1310–1311: "`V_ℓ ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`"). -/
lemma variance_add_le_two_mul [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) :
    variance (fun ω => X ω + Y ω) μ ≤ 2 * variance X μ + 2 * variance Y μ := by
  rw [variance_fun_add hX hY]
  have h1 := covariance_sq_le hX hY
  have h2 := variance_nonneg X μ
  have h3 := variance_nonneg Y μ
  nlinarith [sq_nonneg (variance X μ - variance Y μ),
    sq_nonneg (2 * covariance X Y μ - variance X μ - variance Y μ)]

/-- **The pathwise delta of the call splits into a call and a digital part**:
`1_{x > K} x = (x − K)⁺ + K 1_{x > K}` (Giles 2015, §5.4, p. 42, l. 1826–1829: "the derivative of
a call option payoff function is discontinuous. Hence, computing first order sensitivities for a
call option has similar difficulties to computing the option price for a digital option"). -/
lemma indicator_mul_self_eq (K x : ℝ) :
    (Set.Ioi K).indicator 1 x * x = max (x - K) 0 + K * (Set.Ioi K).indicator 1 x := by
  by_cases hx : x ∈ Set.Ioi K
  · have hKx : K < x := hx
    rw [Set.indicator_of_mem hx, Pi.one_apply, max_eq_left (by linarith)]
    ring
  · have hKx : x ≤ K := not_lt.1 hx
    rw [Set.indicator_of_notMem hx, max_eq_right (by linarith)]
    ring

/-- The pathwise delta `1_{F > K} f` of the call with `F = s₀ f`, `s₀ ≠ 0`, is
`s₀⁻¹ ((F − K)⁺ + K 1_{F > K})` (Giles 2015, §5.4, p. 42, l. 1826–1829). -/
lemma indicator_mul_eq_inv_mul {F f s₀ : ℝ} (hs₀ : s₀ ≠ 0) (hF : F = s₀ * f) (K : ℝ) :
    (Set.Ioi K).indicator 1 F * f =
      s₀⁻¹ * (max (F - K) 0 + K * (Set.Ioi K).indicator 1 F) := by
  rw [← indicator_mul_self_eq, hF]
  field_simp

/-- `1_{F > K} f` is square integrable if `f` is and `F` is measurable (Giles 2015, §5.4). -/
lemma memLp_indicator_mul {F f : Ω → ℝ} (hFm : Measurable F) (hf : MemLp f 2 μ) (K : ℝ) :
    MemLp (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (F ω) * f ω) 2 μ := by
  refine hf.of_le (((measurable_one.indicator measurableSet_Ioi).comp hFm).aestronglyMeasurable.mul
    hf.aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  rcases digital_eq_zero_or_one K (F ω) with h | h <;> simp [h]

/-- The call payoff `(F − K)⁺` is square integrable if `F` is (Giles 2015, §5.1). -/
lemma memLp_call [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) (K : ℝ) :
    MemLp (fun ω => max (F ω - K) 0) 2 μ :=
  memLp_two_comp_of_abs_sub_le (g := fun x => max (x - K) 0) (K := 1)
    (fun x y => by
      rw [one_mul]
      calc |max (x - K) 0 - max (y - K) 0| ≤ |(x - K) - (y - K)| := abs_max_sub_max_le_abs _ _ _
        _ = |x - y| := by rw [sub_sub_sub_cancel_right]) hF

/-- **The variance of the call-delta correction is controlled by the call and the digital
corrections** (Giles 2015, §5.4, p. 42, l. 1826–1829: "computing first order sensitivities for a
call option has similar difficulties to computing the option price for a digital option").  With
fine and coarse tangent paths `f`, `c` (square integrable) and paths `F = s₀ f`, `C = s₀ c`,
`s₀ ≠ 0`, the correction `D = 1_{F > K} f − 1_{C > K} c` of the pathwise delta satisfies
`V[D] ≤ 2 s₀⁻² V[(F − K)⁺ − (C − K)⁺] + 2 (K/s₀)² V[1_{F > K} − 1_{C > K}]`. -/
lemma variance_callDelta_le [IsProbabilityMeasure μ] {f c F C : Ω → ℝ} (hfm : Measurable f)
    (hcm : Measurable c) (hf : MemLp f 2 μ) (hc : MemLp c 2 μ) {s₀ : ℝ} (hs₀ : s₀ ≠ 0)
    (hF : ∀ ω, F ω = s₀ * f ω) (hC : ∀ ω, C ω = s₀ * c ω) (K : ℝ) :
    variance (fun ω => (Set.Ioi K).indicator 1 (F ω) * f ω -
        (Set.Ioi K).indicator 1 (C ω) * c ω) μ ≤
      2 * (s₀⁻¹) ^ 2 * variance (fun ω => max (F ω - K) 0 - max (C ω - K) 0) μ +
        2 * (K / s₀) ^ 2 * variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (F ω) -
          (Set.Ioi K).indicator 1 (C ω)) μ := by
  have eF : F = fun ω => s₀ * f ω := funext hF
  have eC : C = fun ω => s₀ * c ω := funext hC
  have hFm : Measurable F := by rw [eF]; exact hfm.const_mul s₀
  have hCm : Measurable C := by rw [eC]; exact hcm.const_mul s₀
  have hFL : MemLp F 2 μ := by rw [eF]; exact hf.const_mul s₀
  have hCL : MemLp C 2 μ := by rw [eC]; exact hc.const_mul s₀
  have hA : MemLp (fun ω => max (F ω - K) 0 - max (C ω - K) 0) 2 μ :=
    (memLp_call hFL K).sub (memLp_call hCL K)
  have hB : MemLp (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (F ω) -
      (Set.Ioi K).indicator 1 (C ω)) 2 μ :=
    (memLp_digital hFm K).sub (memLp_digital hCm K)
  have e : (fun ω => (Set.Ioi K).indicator 1 (F ω) * f ω -
      (Set.Ioi K).indicator 1 (C ω) * c ω) = fun ω =>
      s₀⁻¹ * (max (F ω - K) 0 - max (C ω - K) 0) +
        K / s₀ * ((Set.Ioi K).indicator (1 : ℝ → ℝ) (F ω) - (Set.Ioi K).indicator 1 (C ω)) := by
    funext ω
    rw [indicator_mul_eq_inv_mul hs₀ (hF ω), indicator_mul_eq_inv_mul hs₀ (hC ω)]
    ring
  rw [e]
  refine (variance_add_le_two_mul (hA.const_mul _) (hB.const_mul _)).trans (le_of_eq ?_)
  rw [variance_const_mul, variance_const_mul]
  ring

end Generic

/-- `T 2^{−ℓ} ≤ T^{1−q} h_ℓ^q` for `h_ℓ = T 2^{−ℓ}`, `T > 0`, `q ≤ 1` (Giles 2015, §5.1). -/
lemma mul_inv_two_pow_le {T : ℝ} (hT : 0 < T) {q : ℝ} (hq : q ≤ 1) (ℓ : ℕ) :
    T * ((2 : ℝ) ^ ℓ)⁻¹ ≤ T ^ (1 - q) * (T / 2 ^ ℓ) ^ q := by
  have h := rpow_le_rpow_sub_mul_rpow (h := T / 2 ^ ℓ) (by positivity)
    (div_le_self hT.le (one_le_pow₀ (by norm_num))) hq
  rwa [Real.rpow_one, div_eq_mul_inv] at h

/-- `T² 4^{−ℓ} ≤ T^{2−q} h_ℓ^q` for `h_ℓ = T 2^{−ℓ}`, `T > 0`, `q ≤ 2` (Giles 2015, §5.2). -/
lemma sq_mul_inv_four_pow_le {T : ℝ} (hT : 0 < T) {q : ℝ} (hq : q ≤ 2) (ℓ : ℕ) :
    T ^ 2 * ((4 : ℝ) ^ ℓ)⁻¹ ≤ T ^ (2 - q) * (T / 2 ^ ℓ) ^ q := by
  have h := rpow_le_rpow_sub_mul_rpow (h := T / 2 ^ ℓ) (by positivity)
    (div_le_self hT.le (one_le_pow₀ (by norm_num))) hq
  have e : (T / 2 ^ ℓ) ^ (2 : ℝ) = T ^ 2 * ((4 : ℝ) ^ ℓ)⁻¹ := by
    rw [Real.rpow_two, div_pow, ← pow_mul, mul_comm ℓ 2, pow_mul, div_eq_mul_inv]
    norm_num
  rwa [e] at h

/-- The correction `1_{Y s₀ (ℓ+1) > K} Y 1 (ℓ+1) − 1_{Y s₀ ℓ > K} Y 1 ℓ ∘ pairAvg` of the pathwise
call delta is square integrable if the paths are measurable and square integrable (Giles 2015,
§5.4). -/
lemma memLp_callDelta_diff {Y : ℝ → ℕ → (ℕ → ℝ) → ℝ} (hYm : ∀ s ℓ, Measurable (Y s ℓ))
    (hYL : ∀ s ℓ, MemLp (Y s ℓ) 2 stdNormalSeq) (s₀ K : ℝ) (ℓ : ℕ) :
    MemLp (fun z => (Set.Ioi K).indicator 1 (Y s₀ (ℓ + 1) z) * Y 1 (ℓ + 1) z -
      (Set.Ioi K).indicator 1 (Y s₀ ℓ (pairAvg z)) * Y 1 ℓ (pairAvg z)) 2 stdNormalSeq :=
  (memLp_indicator_mul (hYm s₀ (ℓ + 1)) (hYL 1 (ℓ + 1)) K).sub
    (memLp_indicator_mul ((hYm s₀ ℓ).comp measurable_pairAvg)
      ((hYL 1 ℓ).comp_measurePreserving measurePreserving_pairAvg) K)

/-- A constant function has variance `0`. -/
lemma variance_eq_zero_of_forall_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ} (h : ∀ ω, X ω = c) : variance X μ = 0 := by
  have e : X = fun _ => c := funext h
  rw [e, variance_eq_integral measurable_const.aemeasurable]
  simp

/-- For `σ = 0` the Euler–Maruyama path of GBM is deterministic:
`Ŝ_N = s (1 + r h_ℓ)^{2^ℓ}` (Giles 2015, §5.1). -/
lemma gbmEM_vol_zero (r T s : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmEM r 0 T s ℓ z = s * (1 + r * (T / 2 ^ ℓ)) ^ (2 ^ ℓ) := by
  rw [gbmEM_eq_prod]
  congr 1
  rw [← Finset.card_range (2 ^ ℓ), ← Finset.prod_const]
  refine Finset.prod_congr (by rw [Finset.card_range]) fun i _ => ?_
  unfold gbmEMFactor
  ring

/-- For `σ = 0` the Milstein path of GBM is deterministic:
`Ŝ_N = s (1 + r h_ℓ)^{2^ℓ}` (Giles 2015, §5.2). -/
lemma gbmMil_vol_zero (r T s : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmMil r 0 T s ℓ z = s * (1 + r * (T / 2 ^ ℓ)) ^ (2 ^ ℓ) := by
  rw [gbmMil_eq_prod]
  congr 1
  rw [← Finset.card_range (2 ^ ℓ), ← Finset.prod_const]
  refine Finset.prod_congr (by rw [Finset.card_range]) fun i _ => ?_
  unfold gbmMilFactor
  ring

/-- **The variance rate of the call-delta correction from the call and the digital rates**
(Giles 2015, §5.4, p. 42, l. 1826–1829).  Let `Y s ℓ` be level-`ℓ` approximations of `S_T` with
initial value `s`, linear in `s` (`Y s = s Y 1`), measurable and square integrable, and let the
coarse path be `Y s ℓ ∘ pairAvg`.  If the call corrections `(Y s₀ (ℓ+1) − K)⁺ − (Y s₀ ℓ − K)⁺`,
the tangent corrections `Y 1 (ℓ+1) − Y 1 ℓ` and the digital corrections
`1_{Y s₀ (ℓ+1) > K} − 1_{Y s₀ ℓ > K}` have variances `O(ρ_ℓ)`, then so has the correction
`1_{Y s₀ (ℓ+1) > K} Y 1 (ℓ+1) − 1_{Y s₀ ℓ > K} Y 1 ℓ` of the pathwise delta, which is square
integrable (`variance_callDelta_le`; for `s₀ = 0` it is `1_{0 > K}` times the tangent
correction). -/
lemma callDelta_rate_of {Y : ℝ → ℕ → (ℕ → ℝ) → ℝ} (hlin : ∀ s ℓ z, Y s ℓ z = s * Y 1 ℓ z)
    (hYm : ∀ s ℓ, Measurable (Y s ℓ)) (hYL : ∀ s ℓ, MemLp (Y s ℓ) 2 stdNormalSeq)
    {ρ : ℕ → ℝ} (s₀ K : ℝ)
    (hcall : ∃ A, 0 ≤ A ∧ ∀ ℓ, variance (fun z => max (Y s₀ (ℓ + 1) z - K) 0 -
      max (Y s₀ ℓ (pairAvg z) - K) 0) stdNormalSeq ≤ A * ρ ℓ)
    (hid : ∃ A, 0 ≤ A ∧ ∀ ℓ, variance (fun z => Y 1 (ℓ + 1) z - Y 1 ℓ (pairAvg z))
      stdNormalSeq ≤ A * ρ ℓ)
    (hdig : ∃ B, 0 ≤ B ∧ ∀ ℓ, variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (Y s₀ (ℓ + 1) z) - (Set.Ioi K).indicator 1 (Y s₀ ℓ (pairAvg z))) stdNormalSeq ≤ B * ρ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fun z => (Set.Ioi K).indicator 1 (Y s₀ (ℓ + 1) z) * Y 1 (ℓ + 1) z -
        (Set.Ioi K).indicator 1 (Y s₀ ℓ (pairAvg z)) * Y 1 ℓ (pairAvg z)) 2 stdNormalSeq ∧
      variance (fun z => (Set.Ioi K).indicator 1 (Y s₀ (ℓ + 1) z) * Y 1 (ℓ + 1) z -
        (Set.Ioi K).indicator 1 (Y s₀ ℓ (pairAvg z)) * Y 1 ℓ (pairAvg z)) stdNormalSeq ≤
        C * ρ ℓ := by
  have hL := memLp_callDelta_diff hYm hYL s₀ K
  rcases eq_or_ne s₀ 0 with rfl | hs₀
  · obtain ⟨A, hA0, hA⟩ := hid
    refine ⟨A, hA0, fun ℓ => ⟨hL ℓ, ?_⟩⟩
    have e : (fun z => (Set.Ioi K).indicator 1 (Y 0 (ℓ + 1) z) * Y 1 (ℓ + 1) z -
        (Set.Ioi K).indicator 1 (Y 0 ℓ (pairAvg z)) * Y 1 ℓ (pairAvg z)) =
        fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) 0 * (Y 1 (ℓ + 1) z - Y 1 ℓ (pairAvg z)) := by
      funext z
      rw [hlin 0, hlin 0 ℓ, zero_mul, zero_mul]
      ring
    rw [e, variance_const_mul]
    have h01 : (Set.Ioi K).indicator (1 : ℝ → ℝ) 0 ^ 2 ≤ 1 := by
      rcases digital_eq_zero_or_one K 0 with h | h <;> simp [h]
    calc _ ≤ 1 * variance (fun z => Y 1 (ℓ + 1) z - Y 1 ℓ (pairAvg z)) stdNormalSeq :=
          mul_le_mul_of_nonneg_right h01 (variance_nonneg _ _)
      _ ≤ A * ρ ℓ := by rw [one_mul]; exact hA ℓ
  · obtain ⟨A, hA0, hA⟩ := hcall
    obtain ⟨B, hB0, hB⟩ := hdig
    refine ⟨2 * (s₀⁻¹) ^ 2 * A + 2 * (K / s₀) ^ 2 * B, by positivity, fun ℓ => ⟨hL ℓ, ?_⟩⟩
    have h := variance_callDelta_le (μ := stdNormalSeq) (hYm 1 (ℓ + 1))
      ((hYm 1 ℓ).comp measurable_pairAvg) (hYL 1 (ℓ + 1))
      ((hYL 1 ℓ).comp_measurePreserving measurePreserving_pairAvg) hs₀
      (F := Y s₀ (ℓ + 1)) (C := fun z => Y s₀ ℓ (pairAvg z)) (fun z => hlin s₀ (ℓ + 1) z)
      (fun z => hlin s₀ ℓ (pairAvg z)) K
    refine h.trans ?_
    have h1 := mul_le_mul_of_nonneg_left (hA ℓ) (by positivity : (0 : ℝ) ≤ 2 * (s₀⁻¹) ^ 2)
    have h2 := mul_le_mul_of_nonneg_left (hB ℓ) (by positivity : (0 : ℝ) ≤ 2 * (K / s₀) ^ 2)
    calc _ ≤ 2 * (s₀⁻¹) ^ 2 * (A * ρ ℓ) + 2 * (K / s₀) ^ 2 * (B * ρ ℓ) := add_le_add h1 h2
      _ = _ := by ring

/-- The call payoff `x ↦ (x − K)⁺` is `1`-Lipschitz, in the form of the hypotheses of
`gbm_correction_variance_le` (Giles 2015, §5.1). -/
lemma abs_call_sub_le (K x y : ℝ) : |max (x - K) 0 - max (y - K) 0| ≤ 1 * |x - y| := by
  rw [one_mul]
  calc |max (x - K) 0 - max (y - K) 0| ≤ |(x - K) - (y - K)| := abs_max_sub_max_le_abs _ _ _
    _ = |x - y| := by rw [sub_sub_sub_cancel_right]

/-- **The call delta with Euler–Maruyama has the variance rate of the digital option: `V_ℓ = O(h^q)`
for every `q < ½`** (Giles 2015, §5.4, p. 42, l. 1826–1829: "the derivative of a call option
payoff function is discontinuous. Hence, computing first order sensitivities for a call option has
similar difficulties to computing the option price for a digital option"; for the digital option
with Euler–Maruyama, §5.1, p. 33, l. 1436–1441: "`V_ℓ = O(h^{1/2})`").  For `T > 0`, `q < ½`,
any `σ`, `s₀` and `K`, the correction of the pathwise delta of the call on level `ℓ + 1`,
`D_ℓ = 1_{Ŝ^f > K} Ŝ^f(1) − 1_{Ŝ^c > K} Ŝ^c(1)` (`Ŝ^f = Ŝ_{ℓ+1}(s₀)` the fine, `Ŝ^c = Ŝ_ℓ(s₀)` the
coarse Euler–Maruyama value driven by the summed increments, `Ŝ(1) = Ŝ/s₀` the tangent paths,
so `D_ℓ = (1_{Ŝ^f > K} Ŝ^f − 1_{Ŝ^c > K} Ŝ^c)/s₀` for `s₀ ≠ 0`), is square integrable and
`V[D_ℓ] ≤ C h_{ℓ+1}^q`.  Proof: `1_{x > K} x = (x − K)⁺ + K 1_{x > K}`, so `D_ℓ` is `s₀⁻¹` times a
call correction (`V = O(h)`, `gbm_correction_variance_le`) plus `K/s₀` times a digital correction
(`V = O(h^q)`, `gbm_em_digital_rate`, for `σ ≠ 0`); for `σ = 0` the paths are deterministic and
`V[D_ℓ] = 0`.  The endpoint `q = ½` is not proved (as for the digital option).  `C` depends on
`s₀` and `K` (through `K/s₀`). -/
theorem gbm_em_call_delta_rate (r σ : ℝ) {T : ℝ} (hT : 0 < T) {q : ℝ}
    (hq : q < 1 / 2) (s₀ K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fun z => (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ (ℓ + 1) z) *
          gbmEM r σ T 1 (ℓ + 1) z -
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z)) * gbmEM r σ T 1 ℓ (pairAvg z))
        2 stdNormalSeq ∧
      variance (fun z => (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ (ℓ + 1) z) *
          gbmEM r σ T 1 (ℓ + 1) z -
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z)) * gbmEM r σ T 1 ℓ (pairAvg z))
        stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ q := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · -- `σ = 0`: deterministic paths, the correction is a constant
    refine ⟨0, le_rfl, fun ℓ => ⟨memLp_callDelta_diff (Y := fun s ℓ z => gbmEM r 0 T s ℓ z)
      (measurable_gbmEM r 0 T) (memLp_gbmEM r 0 T) s₀ K ℓ, ?_⟩⟩
    rw [variance_eq_zero_of_forall_eq (fun z => by simp only [gbmEM_vol_zero]; rfl), zero_mul]
  have hq1 : q ≤ 1 := by linarith
  have hlev : ∀ s ℓ, 6 * 1 ^ 2 * (gbmStrongConst r σ T s * T) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ ≤
      6 * gbmStrongConst r σ T s * T ^ (1 - q) * (T / 2 ^ (ℓ + 1)) ^ q := fun s ℓ => by
    have h := mul_inv_two_pow_le hT hq1 (ℓ + 1)
    have hC := gbmStrongConst_nonneg r σ s hT.le
    calc _ = 6 * gbmStrongConst r σ T s * (T * ((2 : ℝ) ^ (ℓ + 1))⁻¹) := by ring
      _ ≤ 6 * gbmStrongConst r σ T s * (T ^ (1 - q) * (T / 2 ^ (ℓ + 1)) ^ q) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  obtain ⟨Cd, hCd, hd⟩ := gbm_em_digital_rate r σ hσ hT hq
  exact callDelta_rate_of (Y := fun s ℓ z => gbmEM r σ T s ℓ z) (gbmEM_eq_mul_one r σ T)
    (measurable_gbmEM r σ T) (memLp_gbmEM r σ T) s₀ K
    ⟨6 * gbmStrongConst r σ T s₀ * T ^ (1 - q),
      by have := gbmStrongConst_nonneg r σ s₀ hT.le; positivity,
      fun ℓ => ((gbm_correction_variance_le r σ s₀ hT.le (abs_call_sub_le K) ℓ).2).trans
        (hlev s₀ ℓ)⟩
    ⟨6 * gbmStrongConst r σ T 1 * T ^ (1 - q),
      by have := gbmStrongConst_nonneg r σ 1 hT.le; positivity,
      fun ℓ => ((gbm_correction_variance_le r σ 1 hT.le (g := fun x => x) (K := 1)
        (fun x y => by rw [one_mul]) ℓ).2).trans (hlev 1 ℓ)⟩
    ⟨Cd, hCd, fun ℓ => (hd s₀ K ℓ).1⟩

/-- **The call delta with the natural Milstein estimator has the variance rate of the digital
option: `V_ℓ = O(h^q)` for every `q < 1`** (Giles 2015, §5.4, p. 42, l. 1826–1829: "computing
first order sensitivities for a call option has similar difficulties to computing the option price
for a digital option"; for the digital option with the natural Milstein estimator, §5.2, p. 35,
l. 1529–1531: "`V_ℓ = O(h_ℓ)`").  As `gbm_em_call_delta_rate` with the Milstein paths: for
`T > 0`, `q < 1`, any `σ`, `s₀`, `K`, the correction
`D_ℓ = 1_{Ŝ^f > K} Ŝ^f(1) − 1_{Ŝ^c > K} Ŝ^c(1)` of the pathwise delta is square integrable and
`V[D_ℓ] ≤ C h_{ℓ+1}^q` (the call part is `O(h²)`, `gbm_mil_correction_variance_le`; the digital
part `O(h^q)`, `gbm_mil_digital_rate`, for `σ ≠ 0`; for `σ = 0`, `V[D_ℓ] = 0`).  The bound
proved is the digital rate (every `q < 1`), not the `O(h²)` of the call price (§5.2, p. 35,
l. 1508–1509); that the `O(h²)` is actually lost (a lower bound on `V_ℓ`) is not proved, nor the
endpoint `q = 1`.  Numerically (`r = 0.05`, `σ = 0.2`, `s₀ = K = T = 1`) the variance slopes per
level are about `½` (Euler–Maruyama) and `1` (Milstein, approached on the finer levels), against
`1` and `2` for the call. -/
theorem gbm_mil_call_delta_rate (r σ : ℝ) {T : ℝ} (hT : 0 < T) {q : ℝ}
    (hq : q < 1) (s₀ K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fun z => (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ (ℓ + 1) z) *
          gbmMil r σ T 1 (ℓ + 1) z -
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z)) * gbmMil r σ T 1 ℓ (pairAvg z))
        2 stdNormalSeq ∧
      variance (fun z => (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ (ℓ + 1) z) *
          gbmMil r σ T 1 (ℓ + 1) z -
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z)) * gbmMil r σ T 1 ℓ (pairAvg z))
        stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ q := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · -- `σ = 0`: deterministic paths, the correction is a constant
    refine ⟨0, le_rfl, fun ℓ => ⟨memLp_callDelta_diff (Y := fun s ℓ z => gbmMil r 0 T s ℓ z)
      (measurable_gbmMil r 0 T) (memLp_gbmMil r 0 T) s₀ K ℓ, ?_⟩⟩
    rw [variance_eq_zero_of_forall_eq (fun z => by simp only [gbmMil_vol_zero]; rfl), zero_mul]
  have hq2 : q ≤ 2 := by linarith
  have hlev : ∀ s ℓ, 10 * 1 ^ 2 * (gbmMilStrongConst r σ T s * T ^ 2) * ((4 : ℝ) ^ (ℓ + 1))⁻¹ ≤
      10 * gbmMilStrongConst r σ T s * T ^ (2 - q) * (T / 2 ^ (ℓ + 1)) ^ q := fun s ℓ => by
    have h := sq_mul_inv_four_pow_le hT hq2 (ℓ + 1)
    have hC := gbmMilStrongConst_nonneg r σ s hT.le
    calc _ = 10 * gbmMilStrongConst r σ T s * (T ^ 2 * ((4 : ℝ) ^ (ℓ + 1))⁻¹) := by ring
      _ ≤ 10 * gbmMilStrongConst r σ T s * (T ^ (2 - q) * (T / 2 ^ (ℓ + 1)) ^ q) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  obtain ⟨Cd, hCd, hd⟩ := gbm_mil_digital_rate r σ hσ hT hq
  exact callDelta_rate_of (Y := fun s ℓ z => gbmMil r σ T s ℓ z) (gbmMil_eq_mul_one r σ T)
    (measurable_gbmMil r σ T) (memLp_gbmMil r σ T) s₀ K
    ⟨10 * gbmMilStrongConst r σ T s₀ * T ^ (2 - q),
      by have := gbmMilStrongConst_nonneg r σ s₀ hT.le; positivity,
      fun ℓ => (gbm_mil_correction_variance_le r σ s₀ hT.le (abs_call_sub_le K) ℓ).trans
        (hlev s₀ ℓ)⟩
    ⟨10 * gbmMilStrongConst r σ T 1 * T ^ (2 - q),
      by have := gbmMilStrongConst_nonneg r σ 1 hT.le; positivity,
      fun ℓ => (gbm_mil_correction_variance_le r σ 1 hT.le (g := fun x => x) (K := 1)
        (fun x y => by rw [one_mul]) ℓ).trans (hlev 1 ℓ)⟩
    ⟨Cd, hCd, fun ℓ => (hd s₀ K ℓ).1⟩

/-- **The weak rate of the pathwise call delta from the call and the digital weak rates** (Giles
2015, §5.4, p. 42, l. 1826–1829, with condition (i) of Theorem 1, §2.1, p. 6).  In the setting of
`callDelta_rate_of`, with `X s` (linear in `s`, square integrable) the exact solution: if the
weak errors of the call payoff `(· − K)⁺` at `s₀`, of the tangent `Y 1 ℓ` and of the digital
payoff at `s₀` are `O(ρ_ℓ)`, then so is the weak error of the pathwise delta
`1_{Y s₀ ℓ > K} Y 1 ℓ`. -/
lemma callDelta_weak_rate_of {Y : ℝ → ℕ → (ℕ → ℝ) → ℝ} {X : ℝ → (ℕ → ℝ) → ℝ}
    (hlin : ∀ s ℓ z, Y s ℓ z = s * Y 1 ℓ z) (hXlin : ∀ s z, X s z = s * X 1 z)
    (hYm : ∀ s ℓ, Measurable (Y s ℓ)) (hYL : ∀ s ℓ, MemLp (Y s ℓ) 2 stdNormalSeq)
    (hXm : ∀ s, Measurable (X s)) (hXL : ∀ s, MemLp (X s) 2 stdNormalSeq)
    {ρ : ℕ → ℝ} (s₀ K : ℝ)
    (hcall : ∃ A, 0 ≤ A ∧ ∀ ℓ, |∫ z, max (Y s₀ ℓ z - K) 0 - max (X s₀ z - K) 0 ∂stdNormalSeq| ≤
      A * ρ ℓ)
    (hid : ∃ A, 0 ≤ A ∧ ∀ ℓ, |∫ z, Y 1 ℓ z - X 1 z ∂stdNormalSeq| ≤ A * ρ ℓ)
    (hdig : ∃ B, 0 ≤ B ∧ ∀ ℓ, |∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (Y s₀ ℓ z) ∂stdNormalSeq -
      ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (X s₀ z) ∂stdNormalSeq| ≤ B * ρ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      |∫ z, (Set.Ioi K).indicator 1 (Y s₀ ℓ z) * Y 1 ℓ z ∂stdNormalSeq -
        ∫ z, (Set.Ioi K).indicator 1 (X s₀ z) * X 1 z ∂stdNormalSeq| ≤ C * ρ ℓ := by
  rcases eq_or_ne s₀ 0 with rfl | hs₀
  · obtain ⟨A, hA0, hA⟩ := hid
    refine ⟨A, hA0, fun ℓ => ?_⟩
    have e1 : ∀ z, (Set.Ioi K).indicator 1 (Y 0 ℓ z) * Y 1 ℓ z =
        (Set.Ioi K).indicator (1 : ℝ → ℝ) 0 * Y 1 ℓ z := fun z => by rw [hlin, zero_mul]
    have e2 : ∀ z, (Set.Ioi K).indicator 1 (X 0 z) * X 1 z =
        (Set.Ioi K).indicator (1 : ℝ → ℝ) 0 * X 1 z := fun z => by rw [hXlin, zero_mul]
    simp_rw [e1, e2]
    rw [integral_const_mul, integral_const_mul, ← mul_sub,
      ← integral_sub ((hYL 1 ℓ).integrable one_le_two) ((hXL 1).integrable one_le_two), abs_mul]
    have h01 : |(Set.Ioi K).indicator (1 : ℝ → ℝ) 0| ≤ 1 := by
      rcases digital_eq_zero_or_one K 0 with h | h <;> simp [h]
    calc _ ≤ 1 * |∫ z, Y 1 ℓ z - X 1 z ∂stdNormalSeq| :=
          mul_le_mul_of_nonneg_right h01 (abs_nonneg _)
      _ ≤ A * ρ ℓ := by rw [one_mul]; exact hA ℓ
  · obtain ⟨A, hA0, hA⟩ := hcall
    obtain ⟨B, hB0, hB⟩ := hdig
    refine ⟨|s₀|⁻¹ * (A + |K| * B), by positivity, fun ℓ => ?_⟩
    have hYc := (memLp_call (hYL s₀ ℓ) K).integrable one_le_two
    have hXc := (memLp_call (hXL s₀) K).integrable one_le_two
    have hYd := integrable_digital (μ := stdNormalSeq) (hYm s₀ ℓ) K
    have hXd := integrable_digital (μ := stdNormalSeq) (hXm s₀) K
    have e1 : ∀ z, (Set.Ioi K).indicator 1 (Y s₀ ℓ z) * Y 1 ℓ z =
        s₀⁻¹ * (max (Y s₀ ℓ z - K) 0 + K * (Set.Ioi K).indicator 1 (Y s₀ ℓ z)) := fun z =>
      indicator_mul_eq_inv_mul hs₀ (hlin s₀ ℓ z) K
    have e2 : ∀ z, (Set.Ioi K).indicator 1 (X s₀ z) * X 1 z =
        s₀⁻¹ * (max (X s₀ z - K) 0 + K * (Set.Ioi K).indicator 1 (X s₀ z)) := fun z =>
      indicator_mul_eq_inv_mul hs₀ (hXlin s₀ z) K
    simp_rw [e1, e2]
    rw [integral_const_mul, integral_const_mul, integral_add hYc (hYd.const_mul K),
      integral_add hXc (hXd.const_mul K), integral_const_mul, integral_const_mul]
    have e3 : s₀⁻¹ * (∫ z, max (Y s₀ ℓ z - K) 0 ∂stdNormalSeq +
          K * ∫ z, (Set.Ioi K).indicator 1 (Y s₀ ℓ z) ∂stdNormalSeq) -
        s₀⁻¹ * (∫ z, max (X s₀ z - K) 0 ∂stdNormalSeq +
          K * ∫ z, (Set.Ioi K).indicator 1 (X s₀ z) ∂stdNormalSeq) =
        s₀⁻¹ * ((∫ z, max (Y s₀ ℓ z - K) 0 - max (X s₀ z - K) 0 ∂stdNormalSeq) +
          K * (∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (Y s₀ ℓ z) ∂stdNormalSeq -
            ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (X s₀ z) ∂stdNormalSeq)) := by
      rw [integral_sub hYc hXc]
      ring
    rw [e3, abs_mul, abs_inv]
    have h1 := hA ℓ
    have h2 := mul_le_mul_of_nonneg_left (hB ℓ) (abs_nonneg K)
    have h3 := abs_add_le (∫ z, max (Y s₀ ℓ z - K) 0 - max (X s₀ z - K) 0 ∂stdNormalSeq)
      (K * (∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (Y s₀ ℓ z) ∂stdNormalSeq -
        ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (X s₀ z) ∂stdNormalSeq))
    rw [abs_mul K] at h3
    calc _ ≤ |s₀|⁻¹ * (A * ρ ℓ + |K| * (B * ρ ℓ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring

/-- The exact solution of GBM is linear in the initial value: `S_T(s) = s S_T(1)` (Giles 2015,
§5.4, p. 42, l. 1820–1825). -/
lemma gbmExact_eq_mul_one (r σ T s : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmExact r σ T s ℓ z = s * gbmExact r σ T 1 ℓ z := by
  unfold gbmExact
  ring

/-- The expectation `E[1_{S_T(s₀) > K} S_T(1)]` (`S_T(1)` the path from the initial value `1`; the
true delta when `s₀ ≠ 0 ∨ K ≠ 0`, `gbm_call_delta`), computed from the exact solution at level
`0`, is the Gaussian integral
`∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} e^{(r−σ²/2)T + σ√T w} dN(0,1)(w)` (Giles 2015, §5.4). -/
lemma integral_callDelta_gbmExact (r σ T s₀ K : ℝ) :
    ∫ z, (Set.Ioi K).indicator 1 (gbmExact r σ T s₀ 0 z) * gbmExact r σ T 1 0 z ∂stdNormalSeq =
      ∫ w, (Set.Ioi K).indicator 1
          (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
        Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) ∂gaussianReal 0 1 := by
  simp_rw [gbmExact_zero, one_mul]
  have hF : Measurable fun w : ℝ => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
        Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) :=
    ((measurable_one.indicator measurableSet_Ioi).comp (by fun_prop)).mul (by fun_prop)
  exact integral_comp_of_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0) hF.aestronglyMeasurable

/-- `2^{−ℓ} ≤ T⁻¹ T^{1−q} h_ℓ^q` for `h_ℓ = T 2^{−ℓ}`, `T > 0`, `q ≤ 1` (Giles 2015, §5.2). -/
lemma inv_two_pow_le {T : ℝ} (hT : 0 < T) {q : ℝ} (hq : q ≤ 1) (ℓ : ℕ) :
    ((2 : ℝ) ^ ℓ)⁻¹ ≤ T⁻¹ * T ^ (1 - q) * (T / 2 ^ ℓ) ^ q := by
  have h := mul_le_mul_of_nonneg_left (mul_inv_two_pow_le hT hq ℓ) (inv_nonneg.2 hT.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hT.ne', one_mul, ← mul_assoc] at h

/-- `2^{−ℓ/2} ≤ (T^{1/2})⁻¹ T^{1/2−q} h_ℓ^q` for `h_ℓ = T 2^{−ℓ}`, `T > 0`, `q ≤ ½` (Giles 2015,
§5.1). -/
lemma two_rpow_neg_half_le {T : ℝ} (hT : 0 < T) {q : ℝ} (hq : q ≤ 1 / 2) (ℓ : ℕ) :
    (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) ≤
      (T ^ (1 / 2 : ℝ))⁻¹ * T ^ (1 / 2 - q) * (T / 2 ^ ℓ) ^ q := by
  have hT2 : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT _
  have h := rpow_le_rpow_sub_mul_rpow (h := T / 2 ^ ℓ) (by positivity)
    (div_le_self hT.le (one_le_pow₀ (by norm_num))) hq
  rw [div_two_pow_rpow hT.le] at h
  have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hT2.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hT2.ne', one_mul, ← mul_assoc] at h'

/-- **The weak error of the pathwise call delta with Euler–Maruyama: `O(h^q)` for every `q < ½`**
(Giles 2015, §5.4, p. 42, l. 1820–1829: "the derivative of a call option payoff function is
discontinuous. Hence, computing first order sensitivities for a call option has similar
difficulties to computing the option price for a digital option"; with condition (i) of
Theorem 1, §2.1, p. 6).  For `σ ≠ 0`, `T > 0`, `q < ½` and any `s₀`, `K` there is `C ≥ 0` with
`|E[1_{Ŝ_ℓ(s₀) > K} Ŝ_ℓ(1)] − E[1_{S_T(s₀) > K} S_T(1)]| ≤ C h_ℓ^q` on every level, where
`S_T(1)` is the exact path from the initial value `1` and the second expectation, written as a
Gaussian integral, is the true delta `d/ds₀ E[(S_T − K)⁺]` when `s₀ ≠ 0 ∨ K ≠ 0`
(`gbm_call_delta`).  Proof: the call part has weak error `O(h^{1/2})` (`gbm_weak_error_le`), the
digital part `O(h^q)` (`gbm_em_digital_weak_rate`), `callDelta_weak_rate_of`.  The paper gives
the weak order `α = 1` only for the Euler–Maruyama digital option (§5.1, p. 33, l. 1447–1449),
not for the delta; order `1` is not proved here (the bounds used give only `O(h^q)`).  `σ ≠ 0`
is needed: for `σ = 0`, `s₀ = −1`, `r = T = 1`, `K = −e`, `Ŝ_ℓ = −(1 + 2^{−ℓ})^{2^ℓ} > K`, so the
pathwise delta is `(1 + 2^{−ℓ})^{2^ℓ} → e`, while the integral formula gives `0` (the price
`max(s e + e, 0)` is not differentiable at `s = −1`); for `σ = 0` the statement can fail only at
the kink `s₀ e^{rT} = K`. -/
theorem gbm_em_call_delta_weak_rate (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {q : ℝ}
    (hq : q < 1 / 2) (s₀ K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      |∫ z, (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z) * gbmEM r σ T 1 ℓ z ∂stdNormalSeq -
        ∫ w, (Set.Ioi K).indicator 1
            (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
          Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) ∂gaussianReal 0 1| ≤
        C * (T / 2 ^ ℓ) ^ q := by
  have hlev : ∀ (s : ℝ) (ℓ : ℕ),
      1 * Real.sqrt (gbmStrongConst r σ T s * T) * (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ)))
      ≤ Real.sqrt (gbmStrongConst r σ T s * T) * ((T ^ (1 / 2 : ℝ))⁻¹ * T ^ (1 / 2 - q)) *
        (T / 2 ^ ℓ) ^ q := fun s ℓ => by
    have h := mul_le_mul_of_nonneg_left (two_rpow_neg_half_le hT hq.le ℓ)
      (Real.sqrt_nonneg (gbmStrongConst r σ T s * T))
    rw [one_mul, mul_assoc]
    exact h.trans_eq (by ring)
  obtain ⟨Cw, hCw, hw⟩ := gbm_em_digital_weak_rate r σ hσ hT hq
  obtain ⟨C, hC, h⟩ := callDelta_weak_rate_of (Y := fun s ℓ z => gbmEM r σ T s ℓ z)
    (X := fun s z => gbmExact r σ T s 0 z) (gbmEM_eq_mul_one r σ T)
    (fun s z => gbmExact_eq_mul_one r σ T s 0 z) (measurable_gbmEM r σ T) (memLp_gbmEM r σ T)
    (fun s => measurable_gbmExact r σ T s 0) (fun s => memLp_gbmExact r σ T s 0)
    (ρ := fun ℓ => (T / 2 ^ ℓ) ^ q) s₀ K
    ⟨Real.sqrt (gbmStrongConst r σ T s₀ * T) * ((T ^ (1 / 2 : ℝ))⁻¹ * T ^ (1 / 2 - q)),
      by positivity, fun ℓ => (gbm_weak_error_le r σ s₀ hT.le (abs_call_sub_le K) ℓ).trans
      (hlev s₀ ℓ)⟩
    ⟨Real.sqrt (gbmStrongConst r σ T 1 * T) * ((T ^ (1 / 2 : ℝ))⁻¹ * T ^ (1 / 2 - q)),
      by positivity, fun ℓ => (gbm_weak_error_le r σ 1 hT.le (g := fun x => x) (K := 1)
      (fun x y => by rw [one_mul]) ℓ).trans (hlev 1 ℓ)⟩
    ⟨Cw, hCw, fun ℓ => by rw [integral_digital_gbmExact r σ T s₀ K 0]; exact (hw s₀ K ℓ).2⟩
  refine ⟨C, hC, fun ℓ => ?_⟩
  rw [← integral_callDelta_gbmExact]
  exact h ℓ

/-- **The weak error of the pathwise call delta with Milstein: `O(h^q)` for every `q < 1`**
(Giles 2015, §5.4, p. 42, l. 1820–1829: "computing first order sensitivities for a call option
has similar difficulties to computing the option price for a digital option"; with condition (i)
of Theorem 1, §2.1, p. 6).  As `gbm_em_call_delta_weak_rate` with the Milstein paths: for
`σ ≠ 0`, `T > 0`, `q < 1` and any `s₀`, `K` there is `C ≥ 0` with
`|E[1_{Ŝ_ℓ(s₀) > K} Ŝ_ℓ(1)] − E[1_{S_T(s₀) > K} S_T(1)]| ≤ C h_ℓ^q`, where `S_T(1)` is the exact
path from the initial value `1` and the second expectation is the delta when `s₀ ≠ 0 ∨ K ≠ 0`
(`gbm_call_delta`).  The call part is `O(h)` (`gbm_mil_weak_error_le`), the digital part
`O(h^q)` (`gbm_mil_digital_weak_rate`).  `σ ≠ 0` is needed (for `σ = 0` the Milstein path is
the Euler–Maruyama one, see `gbm_em_call_delta_weak_rate`: the statement can fail only at the
kink `s₀ e^{rT} = K`, where the integral formula gives `0` and the price is not
differentiable). -/
theorem gbm_mil_call_delta_weak_rate (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {q : ℝ}
    (hq : q < 1) (s₀ K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      |∫ z, (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ z) * gbmMil r σ T 1 ℓ z ∂stdNormalSeq -
        ∫ w, (Set.Ioi K).indicator 1
            (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
          Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) ∂gaussianReal 0 1| ≤
        C * (T / 2 ^ ℓ) ^ q := by
  have hlev : ∀ (s : ℝ) (ℓ : ℕ), 1 * Real.sqrt (gbmMilStrongConst r σ T s * T ^ 2) * ((2 : ℝ) ^ ℓ)⁻¹
      ≤ Real.sqrt (gbmMilStrongConst r σ T s * T ^ 2) * (T⁻¹ * T ^ (1 - q)) *
        (T / 2 ^ ℓ) ^ q := fun s ℓ => by
    have h := mul_le_mul_of_nonneg_left (inv_two_pow_le hT hq.le ℓ)
      (Real.sqrt_nonneg (gbmMilStrongConst r σ T s * T ^ 2))
    rw [one_mul, mul_assoc]
    exact h.trans_eq (by ring)
  obtain ⟨Cw, hCw, hw⟩ := gbm_mil_digital_weak_rate r σ hσ hT hq
  obtain ⟨C, hC, h⟩ := callDelta_weak_rate_of (Y := fun s ℓ z => gbmMil r σ T s ℓ z)
    (X := fun s z => gbmExact r σ T s 0 z) (gbmMil_eq_mul_one r σ T)
    (fun s z => gbmExact_eq_mul_one r σ T s 0 z) (measurable_gbmMil r σ T) (memLp_gbmMil r σ T)
    (fun s => measurable_gbmExact r σ T s 0) (fun s => memLp_gbmExact r σ T s 0)
    (ρ := fun ℓ => (T / 2 ^ ℓ) ^ q) s₀ K
    ⟨Real.sqrt (gbmMilStrongConst r σ T s₀ * T ^ 2) * (T⁻¹ * T ^ (1 - q)), by positivity,
      fun ℓ => (gbm_mil_weak_error_le r σ s₀ hT.le (abs_call_sub_le K) ℓ).trans (hlev s₀ ℓ)⟩
    ⟨Real.sqrt (gbmMilStrongConst r σ T 1 * T ^ 2) * (T⁻¹ * T ^ (1 - q)), by positivity,
      fun ℓ => (gbm_mil_weak_error_le r σ 1 hT.le (g := fun x => x) (K := 1)
      (fun x y => by rw [one_mul]) ℓ).trans (hlev 1 ℓ)⟩
    ⟨Cw, hCw, fun ℓ => by rw [integral_digital_gbmExact r σ T s₀ K 0]; exact (hw s₀ K ℓ).2⟩
  refine ⟨C, hC, fun ℓ => ?_⟩
  rw [← integral_callDelta_gbmExact]
  exact h ℓ

/-- **Theorem 1 end to end for the pathwise delta of the call with Euler–Maruyama: MSE `< ε²` at
cost `O(ε^{−3−η})` for every `η > 0`** (Giles 2015, §5.4, p. 42, l. 1820–1829: pathwise
sensitivity analysis for the call "has similar difficulties to computing the option price for a
digital option", with Theorem 1, §2.1, p. 6, and (2.4)).  For `dS = rS dt + σS dW`, `σ ≠ 0`,
`T > 0`, any `s₀`, `K` and `η > 0`: level `ℓ` uses `2^ℓ` Euler–Maruyama steps, the level-`ℓ`
payoff is the pathwise delta `1_{Ŝ_ℓ(s₀) > K} Ŝ_ℓ(1)` (`Ŝ_ℓ(1)` the path from the initial value
`1`, the tangent path), the coarse path is driven by the summed increments, the samples are
independent and a level-`ℓ` sample costs `2^ℓ`.  Then there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel estimator of
`E[1_{S_T(s₀) > K} S_T(1)] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} e^{(r−σ²/2)T + σ√T w} dN(0,1)(w)`
(`S_T(1)` the exact path from the initial value `1`; this is the delta `d/ds₀ E[(S_T − K)⁺]` when
`s₀ ≠ 0 ∨ K ≠ 0`, `gbm_call_delta`) has a square-integrable error with mean square `< ε²`, at
cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε^{−3−η}`.  The bound proved is that of the digital option
(`gbm_em_digital_theorem1`); the `O(ε⁻²(log ε)²)` of the call price is not claimed for the delta.
Theorem 1 with `α = β = q = 1/(2 + η)`, `γ = 1` (`theorem1_pairAvg_of_rate`,
`gbm_em_call_delta_weak_rate`, `gbm_em_call_delta_rate`).  The rates proved are `α = β = q` for
every `q < ½`; Theorem 1 with `α = 1`, `β = ½` (the paper's rates for the Euler–Maruyama digital
option, §5.1, p. 33, l. 1447–1449) would give `O(ε^{−2.5})`, and the gap to `ε^{−3−η}` is `½`
(from `α = q < ½` instead of `1`) plus `η` (from the excluded endpoint `q = ½`).  The paper
states no complexity for the delta.  `σ ≠ 0` is needed (see `gbm_em_call_delta_weak_rate`: for
`σ = 0`, `s₀ = −1`, `r = T = 1`, `K = −e` the mean of the estimator tends to `e` while the
integral formula gives `0`, at the kink `s₀ e^{rT} = K` where the price is not differentiable;
for `σ = 0` the statement can fail only at that kink). -/
theorem gbm_em_call_delta_theorem1 (r σ s₀ K : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {η : ℝ}
    (hη : 0 < η) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z) * gbmEM r σ T 1 ℓ z)
              (fun ℓ z => (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z)) *
                gbmEM r σ T 1 ℓ (pairAvg z)))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator 1
                (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
              Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) ∂gaussianReal 0 1) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z) * gbmEM r σ T 1 ℓ z)
              (fun ℓ z => (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z)) *
                gbmEM r σ T 1 ℓ (pairAvg z)))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator 1
                (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
              Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) ∂gaussianReal 0 1) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-3 - η) := by
  set q := 1 / (2 + η) with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q < 1 / 2 := by
    rw [hqdef, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨C₁, -, hC₁⟩ := gbm_em_call_delta_weak_rate r σ hσ hT hq s₀ K
  obtain ⟨C₂, -, hC₂⟩ := gbm_em_call_delta_rate r σ hT hq s₀ K
  obtain ⟨c₄, hc₄, h⟩ := theorem1_pairAvg_of_rate hT hq0 (by linarith)
    (Pf := fun ℓ z => (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z) * gbmEM r σ T 1 ℓ z)
    (P := fun z => (Set.Ioi K).indicator 1 (gbmExact r σ T s₀ 0 z) * gbmExact r σ T 1 0 z)
    (fun ℓ => ((measurable_one.indicator measurableSet_Ioi).comp
      (measurable_gbmEM r σ T s₀ ℓ)).mul (measurable_gbmEM r σ T 1 ℓ))
    (fun ℓ => memLp_indicator_mul (measurable_gbmEM r σ T s₀ ℓ) (memLp_gbmEM r σ T 1 ℓ) K)
    ((memLp_indicator_mul (measurable_gbmExact r σ T s₀ 0) (memLp_gbmExact r σ T 1 0)
      K).integrable one_le_two) (c₁ := C₁) (c₂ := C₂)
    (fun ℓ => by rw [integral_callDelta_gbmExact]; exact hC₁ ℓ)
    (fun ℓ => (hC₂ ℓ).2)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  rw [integral_callDelta_gbmExact] at hint hmse
  have hexp : -2 - (1 - q) / q = -3 - η := by
    rw [hqdef]
    field_simp
    ring
  rw [hexp] at hcost
  exact ⟨L, N, hN, hint, hmse, hcost⟩

/-- **Theorem 1 end to end for the pathwise delta of the call with the natural Milstein
estimator: MSE `< ε²` at cost `O(ε^{−2−η})` for every `η > 0`** (Giles 2015, §5.4, p. 42,
l. 1820–1829: "computing first order sensitivities for a call option has similar difficulties to
computing the option price for a digital option", with Theorem 1, §2.1, p. 6, and (2.4)).  As
`gbm_em_call_delta_theorem1` with `2^ℓ` Milstein steps on level `ℓ`: for `σ ≠ 0`, `T > 0`, any
`s₀`, `K` and `η > 0` there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` for which the natural multilevel estimator of `E[1_{S_T(s₀) > K} S_T(1)]` (`S_T(1)` the
exact path from the initial value `1`; the delta `d/ds₀ E[(S_T − K)⁺]` when `s₀ ≠ 0 ∨ K ≠ 0`,
`gbm_call_delta`) built from the pathwise deltas `1_{Ŝ_ℓ(s₀) > K} Ŝ_ℓ(1)` has a square-integrable
error with mean square `< ε²`, at cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε^{−2−η}`.  The bound proved is that
of the digital option (`gbm_mil_digital_theorem1`); the `O(ε⁻²)` that `β = 2 > γ` gives for the
call price is not claimed for the delta.  Theorem 1 with `α = β = q = 1/(1 + η) < 1`, `γ = 1`
(`gbm_mil_call_delta_weak_rate`, `gbm_mil_call_delta_rate`); `β = 1` itself is not proved, and
the paper states no complexity for the delta.  `σ ≠ 0` is needed, as in
`gbm_em_call_delta_theorem1`. -/
theorem gbm_mil_call_delta_theorem1 (r σ s₀ K : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {η : ℝ}
    (hη : 0 < η) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ z) * gbmMil r σ T 1 ℓ z)
              (fun ℓ z => (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z)) *
                gbmMil r σ T 1 ℓ (pairAvg z)))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator 1
                (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
              Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) ∂gaussianReal 0 1) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ z) * gbmMil r σ T 1 ℓ z)
              (fun ℓ z => (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z)) *
                gbmMil r σ T 1 ℓ (pairAvg z)))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator 1
                (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) *
              Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) ∂gaussianReal 0 1) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 - η) := by
  set q := 1 / (1 + η) with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q < 1 := by
    rw [hqdef, div_lt_one (by positivity)]
    linarith
  obtain ⟨C₁, -, hC₁⟩ := gbm_mil_call_delta_weak_rate r σ hσ hT hq s₀ K
  obtain ⟨C₂, -, hC₂⟩ := gbm_mil_call_delta_rate r σ hT hq s₀ K
  obtain ⟨c₄, hc₄, h⟩ := theorem1_pairAvg_of_rate hT hq0 (by linarith)
    (Pf := fun ℓ z => (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ z) * gbmMil r σ T 1 ℓ z)
    (P := fun z => (Set.Ioi K).indicator 1 (gbmExact r σ T s₀ 0 z) * gbmExact r σ T 1 0 z)
    (fun ℓ => ((measurable_one.indicator measurableSet_Ioi).comp
      (measurable_gbmMil r σ T s₀ ℓ)).mul (measurable_gbmMil r σ T 1 ℓ))
    (fun ℓ => memLp_indicator_mul (measurable_gbmMil r σ T s₀ ℓ) (memLp_gbmMil r σ T 1 ℓ) K)
    ((memLp_indicator_mul (measurable_gbmExact r σ T s₀ 0) (memLp_gbmExact r σ T 1 0)
      K).integrable one_le_two) (c₁ := C₁) (c₂ := C₂)
    (fun ℓ => by rw [integral_callDelta_gbmExact]; exact hC₁ ℓ)
    (fun ℓ => (hC₂ ℓ).2)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  rw [integral_callDelta_gbmExact] at hint hmse
  have hexp : -2 - (1 - q) / q = -2 - η := by
    rw [hqdef]
    field_simp
    ring
  rw [hexp] at hcost
  exact ⟨L, N, hN, hint, hmse, hcost⟩

/-! ### The digital delta via the conditional expectation -/

/-- `φ ≤ 1` for the standard normal density (`φ ≤ 1/√(2π)`). -/
lemma gaussianPDFReal_std_le_one (u : ℝ) : gaussianPDFReal 0 1 u ≤ 1 := by
  refine (gaussianPDFReal_std_le u).trans (inv_le_one_of_one_le₀ ?_)
  exact Real.one_le_sqrt.2 (by nlinarith [Real.two_le_pi])

/-- `|u| φ(u) ≤ 1` for the standard normal density (`|u| ≤ 1 + u²/2 ≤ e^{u²/2}`). -/
lemma abs_mul_gaussianPDFReal_std_le_one (u : ℝ) : |u| * gaussianPDFReal 0 1 u ≤ 1 := by
  rw [gaussianPDFReal_std]
  have h1 : (√(2 * Real.pi))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by nlinarith [Real.two_le_pi]))
  have h2 : |u| ≤ Real.exp (u ^ 2 / 2) := by
    have := Real.add_one_le_exp (u ^ 2 / 2)
    nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have h3 : |u| * Real.exp (-u ^ 2 / 2) ≤ 1 := by
    have e : Real.exp (u ^ 2 / 2) * Real.exp (-u ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    nlinarith [Real.exp_pos (-u ^ 2 / 2)]
  have h4 : 0 ≤ |u| * Real.exp (-u ^ 2 / 2) := by positivity
  calc |u| * ((√(2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2)) =
        (√(2 * Real.pi))⁻¹ * (|u| * Real.exp (-u ^ 2 / 2)) := by ring
    _ ≤ 1 * 1 := mul_le_mul h1 h3 h4 zero_le_one
    _ = 1 := one_mul 1

/-- **The pathwise derivative of a conditional-expectation digital payoff** (Giles 2015, §5.4,
p. 42, l. 1829–1832: "Sensitivities for digital options can be obtained by first using the
conditional expectation approach described previously, and then applying pathwise sensitivity
analysis to this").  For a conditional mean `m = s a` and standard deviation `σ_c = |s| b`
linear in the initial value `s` (`b > 0`), the payoff `Φ((m − K)/σ_c)` has at `s₀ ≠ 0` the
derivative `φ((m − K)/σ_c) K/(s₀ σ_c)` (the tangents `∂m/∂s₀ = m/s₀`, `∂σ_c/∂s₀ = σ_c/s₀` give
`∂/∂s₀ (m − K)/σ_c = K/(s₀ σ_c)`). -/
lemma hasDerivAt_cdf_mul_div (a K : ℝ) {b : ℝ} (hb : 0 < b) {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    HasDerivAt (fun s => cdf (gaussianReal 0 1) ((s * a - K) / (|s| * b)))
      (gaussianPDFReal 0 1 ((s₀ * a - K) / (|s₀| * b)) * (K / (s₀ * (|s₀| * b)))) s₀ := by
  have hnum : HasDerivAt (fun s => s * a - K) a s₀ := by
    simpa using ((hasDerivAt_id s₀).mul_const a).sub_const K
  have hd0 : |s₀| * b ≠ 0 := mul_ne_zero (abs_ne_zero.2 hs₀) hb.ne'
  have hu : HasDerivAt (fun s => (s * a - K) / (|s| * b)) (K / (s₀ * (|s₀| * b))) s₀ := by
    rcases lt_or_gt_of_ne hs₀ with hneg | hpos
    · have heq : (fun s => (s * a - K) / (|s| * b)) =ᶠ[nhds s₀]
          fun s => (s * a - K) / (-s * b) := by
        filter_upwards [Iio_mem_nhds hneg] with s hs
        rw [abs_of_neg (Set.mem_Iio.1 hs)]
      have hden : HasDerivAt (fun s => -s * b) (-1 * b) s₀ := (hasDerivAt_neg s₀).mul_const b
      have hd : -s₀ * b ≠ 0 := by rw [← abs_of_neg hneg]; exact hd0
      refine ((hnum.div hden hd).congr_of_eventuallyEq heq).congr_deriv ?_
      rw [abs_of_neg hneg]
      field_simp
      ring
    · have heq : (fun s => (s * a - K) / (|s| * b)) =ᶠ[nhds s₀]
          fun s => (s * a - K) / (s * b) := by
        filter_upwards [Ioi_mem_nhds hpos] with s hs
        rw [abs_of_pos (Set.mem_Ioi.1 hs)]
      have hden : HasDerivAt (fun s => s * b) (1 * b) s₀ := (hasDerivAt_id s₀).mul_const b
      have hd : s₀ * b ≠ 0 := by rw [← abs_of_pos hpos]; exact hd0
      refine ((hnum.div hden hd).congr_of_eventuallyEq heq).congr_deriv ?_
      rw [abs_of_pos hpos]
      field_simp
      ring
  exact (hasDerivAt_normCDF _).comp s₀ hu

/-- **The pathwise derivative of the conditional-expectation payoff is controlled by `|a|/b`**
(Giles 2015, §5.4, p. 42, l. 1829–1832): for `b ≥ 0`, `s ≠ 0`,
`|φ((s a − K)/(|s| b)) K/(s |s| b)| ≤ (|a|/b + 1)/|s|`.  Near the strike the factor `1/σ_c` is
compensated by the Gaussian factor: with `u = (s a − K)/(|s| b)`,
`K/(|s| b) = s a/(|s| b) − u`, and `φ ≤ 1`, `|u| φ(u) ≤ 1`. -/
lemma abs_pdf_mul_div_le (a K : ℝ) {b : ℝ} (hb : 0 ≤ b) {s : ℝ} (hs : s ≠ 0) :
    |gaussianPDFReal 0 1 ((s * a - K) / (|s| * b)) * (K / (s * (|s| * b)))| ≤
      (|a| / b + 1) / |s| := by
  have hs' : 0 < |s| := abs_pos.2 hs
  rcases hb.eq_or_lt with rfl | hb'
  · simp only [mul_zero, div_zero, abs_zero, zero_add]
    positivity
  · set u := (s * a - K) / (|s| * b) with hu
    have hK : K / (s * (|s| * b)) = (s * a / (|s| * b) - u) / s := by
      rw [hu]
      field_simp
      ring
    have habs : |s * a / (|s| * b)| = |a| / b := by
      rw [abs_div, abs_mul, abs_mul, abs_abs, abs_of_pos hb']
      field_simp
    have hφ := gaussianPDFReal_nonneg 0 1 u
    rw [hK, abs_mul, abs_div, abs_of_nonneg hφ]
    have h1 : |s * a / (|s| * b) - u| ≤ |a| / b + |u| := by
      rw [← habs]
      exact abs_sub _ _
    have h2 := gaussianPDFReal_std_le_one u
    have h3 := abs_mul_gaussianPDFReal_std_le_one u
    have h4 : gaussianPDFReal 0 1 u * |s * a / (|s| * b) - u| ≤ |a| / b + 1 := by
      calc gaussianPDFReal 0 1 u * |s * a / (|s| * b) - u| ≤
            gaussianPDFReal 0 1 u * (|a| / b + |u|) := mul_le_mul_of_nonneg_left h1 hφ
        _ = gaussianPDFReal 0 1 u * (|a| / b) + |u| * gaussianPDFReal 0 1 u := by ring
        _ ≤ 1 * (|a| / b) + 1 := add_le_add (mul_le_mul_of_nonneg_right h2 (by positivity)) h3
        _ = |a| / b + 1 := by ring
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h4 hs'.le

section GenericCond

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Unbiasedness of the pathwise sensitivity of a conditional-expectation payoff** (Giles 2015,
§5.4, p. 42, l. 1829–1832: "Sensitivities for digital options can be obtained by first using the
conditional expectation approach described previously, and then applying pathwise sensitivity
analysis to this").  On a probability space let `a`, `b` be measurable, `b ≥ 0`, `b ≠ 0` a.s., and
`|a|/b` square integrable.  Then for `s₀ ≠ 0`: a.s. `s ↦ Φ((s a − K)/(|s| b))` is differentiable
at `s₀` with derivative `φ((s₀ a − K)/(|s₀| b)) K/(s₀ |s₀| b)`, this derivative is square
integrable, and it is the derivative of the expected payoff:
`d/ds₀ E[Φ((s₀ a − K)/(|s₀| b))] = E[φ(…) K/(s₀ |s₀| b)]` (dominated differentiation on the ball
of radius `|s₀|/2`, where the derivative is at most `2(|a|/b + 1)/|s₀|`, `abs_pdf_mul_div_le`). -/
lemma hasDerivAt_integral_cdf_mul_div [IsProbabilityMeasure μ] {a b : Ω → ℝ}
    (ham : Measurable a) (hbm : Measurable b) (hb0 : ∀ ω, 0 ≤ b ω) (hb : ∀ᵐ ω ∂μ, b ω ≠ 0)
    (hab : MemLp (fun ω => |a ω| / b ω) 2 μ) (K : ℝ) {s₀ : ℝ} (hs₀ : s₀ ≠ 0) :
    (∀ᵐ ω ∂μ, HasDerivAt (fun s => cdf (gaussianReal 0 1) ((s * a ω - K) / (|s| * b ω)))
      (gaussianPDFReal 0 1 ((s₀ * a ω - K) / (|s₀| * b ω)) * (K / (s₀ * (|s₀| * b ω)))) s₀) ∧
    MemLp (fun ω => gaussianPDFReal 0 1 ((s₀ * a ω - K) / (|s₀| * b ω)) *
      (K / (s₀ * (|s₀| * b ω)))) 2 μ ∧
    HasDerivAt (fun s => ∫ ω, cdf (gaussianReal 0 1) ((s * a ω - K) / (|s| * b ω)) ∂μ)
      (∫ ω, gaussianPDFReal 0 1 ((s₀ * a ω - K) / (|s₀| * b ω)) * (K / (s₀ * (|s₀| * b ω)))
        ∂μ) s₀ := by
  have hs₀' : 0 < |s₀| := abs_pos.2 hs₀
  have hcdf : Measurable (cdf (gaussianReal 0 1)) := (monotone_cdf _).measurable
  have hF'm : ∀ s, Measurable fun ω => gaussianPDFReal 0 1 ((s * a ω - K) / (|s| * b ω)) *
      (K / (s * (|s| * b ω))) := fun s =>
    ((measurable_gaussianPDFReal 0 1).comp (by fun_prop)).mul (by fun_prop)
  have hball : ∀ s ∈ Metric.ball s₀ (|s₀| / 2), |s₀| / 2 ≤ |s| := fun s hs => by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have := abs_sub_abs_le_abs_sub s₀ s
    rw [abs_sub_comm] at hs
    linarith
  have hbound : ∀ s ∈ Metric.ball s₀ (|s₀| / 2), ∀ ω,
      ‖gaussianPDFReal 0 1 ((s * a ω - K) / (|s| * b ω)) * (K / (s * (|s| * b ω)))‖ ≤
        2 / |s₀| * (|a ω| / b ω + 1) := fun s hs ω => by
    have hs1 := hball s hs
    have hsne : s ≠ 0 := abs_pos.1 (by linarith)
    rw [Real.norm_eq_abs]
    refine (abs_pdf_mul_div_le (a ω) K (hb0 ω) hsne).trans ?_
    have hA : 0 ≤ |a ω| / b ω + 1 := by have := hb0 ω; positivity
    rw [div_le_iff₀ (by linarith), mul_comm, ← mul_assoc]
    calc |a ω| / b ω + 1 = 1 * (|a ω| / b ω + 1) := (one_mul _).symm
      _ ≤ |s| * (2 / |s₀|) * (|a ω| / b ω + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hA
        rw [mul_div_assoc', le_div_iff₀ hs₀']
        linarith
  have hbL : MemLp (fun ω => 2 / |s₀| * (|a ω| / b ω + 1)) 2 μ :=
    (hab.add (memLp_const 1)).const_mul _
  have hmem : ∀ s ∈ Metric.ball s₀ (|s₀| / 2),
      MemLp (fun ω => gaussianPDFReal 0 1 ((s * a ω - K) / (|s| * b ω)) *
        (K / (s * (|s| * b ω)))) 2 μ := fun s hs =>
    hbL.of_le (hF'm s).aestronglyMeasurable (Eventually.of_forall fun ω =>
      (hbound s hs ω).trans (le_abs_self _))
  have hdiff : ∀ᵐ ω ∂μ, ∀ s ∈ Metric.ball s₀ (|s₀| / 2),
      HasDerivAt (fun s => cdf (gaussianReal 0 1) ((s * a ω - K) / (|s| * b ω)))
        (gaussianPDFReal 0 1 ((s * a ω - K) / (|s| * b ω)) * (K / (s * (|s| * b ω)))) s := by
    filter_upwards [hb] with ω hω s hs
    have hs1 := hball s hs
    exact hasDerivAt_cdf_mul_div (a ω) K (lt_of_le_of_ne (hb0 ω) (Ne.symm hω))
      (abs_pos.1 (by linarith))
  have hs₀b : s₀ ∈ Metric.ball s₀ (|s₀| / 2) := Metric.mem_ball_self (by positivity)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s ω => cdf (gaussianReal 0 1) ((s * a ω - K) / (|s| * b ω)))
    (F' := fun s ω => gaussianPDFReal 0 1 ((s * a ω - K) / (|s| * b ω)) *
      (K / (s * (|s| * b ω))))
    (Metric.ball_mem_nhds s₀ (by positivity))
    (Eventually.of_forall fun s => (hcdf.comp (by fun_prop)).aestronglyMeasurable)
    (Integrable.of_bound (hcdf.comp (by fun_prop)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg _ _)]
        exact cdf_le_one _ _))
    (hF'm s₀).aestronglyMeasurable
    (Eventually.of_forall fun ω s hs => hbound s hs ω) (hbL.integrable one_le_two) hdiff
  exact ⟨hdiff.mono fun ω hω => hω s₀ hs₀b, hmem s₀ hs₀b, hD⟩

end GenericCond

/-- **The pathwise delta of the fine conditional-expectation payoff** (Giles 2015, §5.4, p. 42,
l. 1829–1832: "Sensitivities for digital options can be obtained by first using the conditional
expectation approach described previously, and then applying pathwise sensitivity analysis to
this"; the payoff of §5.2, p. 36, l. 1551–1558): with the conditional mean `m_f` and standard
deviation `s_f` of `gbmCondMeanFine`, `gbmCondStdFine` at the initial value `s₀`,
`∂P^f_ℓ/∂s₀ = φ((m_f − K)/s_f) K/(s₀ s_f)`, `φ` the standard normal density (the tangents of
`m_f`, `s_f` are `m_f/s₀`, `s_f/s₀`).  For `σ ≠ 0`, `T > 0` the value `0` that Lean gives to
`K/0` is only taken on the null set `s_f = 0` or at `s₀ = 0` (where the payoff is not
differentiable); for `σ = 0` or `T ≤ 0`, `s_f = 0` and the formula gives `0`, not a derivative. -/
noncomputable def gbmDigitalCondFineDelta (r σ T s₀ K : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  gaussianPDFReal 0 1 ((gbmCondMeanFine r σ T s₀ ℓ z - K) / gbmCondStdFine r σ T s₀ ℓ z) *
    (K / (s₀ * gbmCondStdFine r σ T s₀ ℓ z))

/-- **The pathwise delta of the coarse conditional-expectation payoff, used on level `ℓ + 1`**
(Giles 2015, §5.4, p. 42, l. 1829–1832; the payoff of §5.2, p. 36, l. 1566–1574): with `m_c`,
`s_c` of `gbmCondMeanCoarse`, `gbmCondStdCoarse` at `s₀`, `∂P^c_ℓ/∂s₀ = φ((m_c − K)/s_c)
K/(s₀ s_c)` (for `σ ≠ 0`, `T > 0` the value `0` of `K/0` is only taken on a null set or at
`s₀ = 0`; for `σ = 0` or `T ≤ 0`, `s_c = 0` and the formula gives `0`, not a derivative). -/
noncomputable def gbmDigitalCondCoarseDelta (r σ T s₀ K : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  gaussianPDFReal 0 1 ((gbmCondMeanCoarse r σ T s₀ ℓ z - K) / gbmCondStdCoarse r σ T s₀ ℓ z) *
    (K / (s₀ * gbmCondStdCoarse r σ T s₀ ℓ z))

/-- The fine conditional mean is linear in the initial value: `m_f(s) = s m_f(1)` (Giles 2015,
§5.4). -/
lemma gbmCondMeanFine_eq_mul (r σ T s : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmCondMeanFine r σ T s ℓ z = s * gbmCondMeanFine r σ T 1 ℓ z := by
  unfold gbmCondMeanFine
  rw [milsteinPath_gbm, milsteinPath_gbm]
  ring

/-- The fine conditional standard deviation is `|s|`-homogeneous: `s_f(s) = |s| s_f(1)` (Giles
2015, §5.4). -/
lemma gbmCondStdFine_eq_mul (r σ T s : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmCondStdFine r σ T s ℓ z = |s| * gbmCondStdFine r σ T 1 ℓ z := by
  unfold gbmCondStdFine
  rw [milsteinPath_gbm, milsteinPath_gbm, one_mul, mul_left_comm σ s, abs_mul]
  ring

/-- The coarse conditional mean is linear in the initial value (Giles 2015, §5.4). -/
lemma gbmCondMeanCoarse_eq_mul (r σ T s : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmCondMeanCoarse r σ T s ℓ z = s * gbmCondMeanCoarse r σ T 1 ℓ z := by
  unfold gbmCondMeanCoarse
  rw [milsteinPath_gbm, milsteinPath_gbm]
  ring

/-- The coarse conditional standard deviation is `|s|`-homogeneous (Giles 2015, §5.4). -/
lemma gbmCondStdCoarse_eq_mul (r σ T s : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmCondStdCoarse r σ T s ℓ z = |s| * gbmCondStdCoarse r σ T 1 ℓ z := by
  unfold gbmCondStdCoarse
  rw [milsteinPath_gbm, milsteinPath_gbm, one_mul, mul_left_comm σ s, abs_mul]
  ring

/-- `|X c|/(|X| d) ≤ |c|/d` for `d ≥ 0` (for `X = 0` the left side is `0`). -/
lemma abs_mul_div_abs_mul_le (X c : ℝ) {d : ℝ} (hd : 0 ≤ d) : |X * c| / (|X| * d) ≤ |c| / d := by
  rcases eq_or_ne X 0 with rfl | hX
  · simp only [zero_mul, abs_zero, zero_div]
    positivity
  · rw [abs_mul, mul_div_mul_left _ _ (abs_ne_zero.2 hX)]

/-- **The pathwise delta of the fine conditional-expectation payoff is a.s. the derivative,
square integrable and unbiased** (Giles 2015, §5.4, p. 42, l. 1829–1832), from
`hasDerivAt_integral_cdf_mul_div` with `a = m_f(1)`, `b = s_f(1)`: `|a|/b ≤ |1 + rh|/(|σ|√h)`. -/
lemma gbmDigitalCondFine_delta (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) (ℓ : ℕ) :
    (∀ᵐ z ∂stdNormalSeq, HasDerivAt (fun s => gbmDigitalCondFine r σ T s K ℓ z)
      (gbmDigitalCondFineDelta r σ T s₀ K ℓ z) s₀) ∧
    MemLp (gbmDigitalCondFineDelta r σ T s₀ K ℓ) 2 stdNormalSeq ∧
    HasDerivAt (fun s => ∫ z, gbmDigitalCondFine r σ T s K ℓ z ∂stdNormalSeq)
      (∫ z, gbmDigitalCondFineDelta r σ T s₀ K ℓ z ∂stdNormalSeq) s₀ := by
  have hh : 0 < T / 2 ^ ℓ := by positivity
  have hsh : 0 < Real.sqrt (T / 2 ^ ℓ) := Real.sqrt_pos.2 hh
  have hX : Measurable fun z : ℕ → ℝ =>
      milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) 1 z (2 ^ ℓ - 1) :=
    measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _
  obtain ⟨a, ha⟩ : ∃ a, a = gbmCondMeanFine r σ T 1 ℓ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = gbmCondStdFine r σ T 1 ℓ := ⟨_, rfl⟩
  have ham : Measurable a := by rw [ha]; unfold gbmCondMeanFine; fun_prop
  have hbm : Measurable b := by rw [hb]; unfold gbmCondStdFine; fun_prop
  have hb0 : ∀ z, 0 ≤ b z := fun z => by rw [hb]; unfold gbmCondStdFine; positivity
  have hbne : ∀ᵐ z ∂stdNormalSeq, b z ≠ 0 := by
    filter_upwards [ae_gbm_milsteinPath_ne_zero r σ one_ne_zero hσ hh (2 ^ ℓ - 1)] with z hz
    rw [hb]
    unfold gbmCondStdFine
    exact mul_ne_zero (abs_ne_zero.2 hz) hsh.ne'
  have key : ∀ X : ℝ, |X + r * X * (T / 2 ^ ℓ)| / (|σ * X| * Real.sqrt (T / 2 ^ ℓ)) ≤
      |1 + r * (T / 2 ^ ℓ)| / (|σ| * Real.sqrt (T / 2 ^ ℓ)) := fun X => by
    rw [show X + r * X * (T / 2 ^ ℓ) = X * (1 + r * (T / 2 ^ ℓ)) by ring,
      show |σ * X| * Real.sqrt (T / 2 ^ ℓ) = |X| * (|σ| * Real.sqrt (T / 2 ^ ℓ)) by
        rw [abs_mul]; ring]
    exact abs_mul_div_abs_mul_le _ _ (by positivity)
  have hab : MemLp (fun z => |a z| / b z) 2 stdNormalSeq := by
    refine (memLp_const (|1 + r * (T / 2 ^ ℓ)| / (|σ| * Real.sqrt (T / 2 ^ ℓ)))).of_le
      ((continuous_abs.measurable.comp ham).div hbm).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) (hb0 z))]
    refine le_trans ?_ (le_abs_self _)
    rw [ha, hb]
    unfold gbmCondMeanFine gbmCondStdFine
    exact key _
  obtain ⟨h1, h2, h3⟩ := hasDerivAt_integral_cdf_mul_div ham hbm hb0 hbne hab K hs₀
  have eP : ∀ s z, gbmDigitalCondFine r σ T s K ℓ z =
      cdf (gaussianReal 0 1) ((s * a z - K) / (|s| * b z)) := fun s z => by
    unfold gbmDigitalCondFine
    rw [gbmCondMeanFine_eq_mul, gbmCondStdFine_eq_mul, ha, hb]
  have eD : ∀ z, gbmDigitalCondFineDelta r σ T s₀ K ℓ z =
      gaussianPDFReal 0 1 ((s₀ * a z - K) / (|s₀| * b z)) * (K / (s₀ * (|s₀| * b z))) :=
    fun z => by
    unfold gbmDigitalCondFineDelta
    rw [gbmCondMeanFine_eq_mul, gbmCondStdFine_eq_mul, ha, hb]
  have eD' : gbmDigitalCondFineDelta r σ T s₀ K ℓ = fun z =>
      gaussianPDFReal 0 1 ((s₀ * a z - K) / (|s₀| * b z)) * (K / (s₀ * (|s₀| * b z))) :=
    funext eD
  simp only [eP, eD]
  rw [eD']
  exact ⟨h1, h2, h3⟩

/-- **The pathwise delta of the coarse conditional-expectation payoff is a.s. the derivative,
square integrable and unbiased** (Giles 2015, §5.4, p. 42, l. 1829–1832), from
`hasDerivAt_integral_cdf_mul_div` with `a = m_c(1)`, `b = s_c(1)`:
`|a|/b ≤ |1 + rh_ℓ + σ√h_{ℓ+1} Z_{N−2}|/(|σ|√h_{ℓ+1})`, square integrable. -/
lemma gbmDigitalCondCoarse_delta (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) (ℓ : ℕ) :
    (∀ᵐ z ∂stdNormalSeq, HasDerivAt (fun s => gbmDigitalCondCoarse r σ T s K ℓ z)
      (gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z) s₀) ∧
    MemLp (gbmDigitalCondCoarseDelta r σ T s₀ K ℓ) 2 stdNormalSeq ∧
    HasDerivAt (fun s => ∫ z, gbmDigitalCondCoarse r σ T s K ℓ z ∂stdNormalSeq)
      (∫ z, gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z ∂stdNormalSeq) s₀ := by
  have hh : 0 < T / 2 ^ ℓ := by positivity
  have hh' : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have hsh : 0 < Real.sqrt (T / 2 ^ (ℓ + 1)) := Real.sqrt_pos.2 hh'
  have hY : Measurable fun z : ℕ → ℝ =>
      milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) 1 (pairAvg z) (2 ^ ℓ - 1) :=
    (measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _).comp measurable_pairAvg
  have hzN : Measurable fun z : ℕ → ℝ => z (2 ^ (ℓ + 1) - 2) := measurable_pi_apply _
  obtain ⟨a, ha⟩ : ∃ a, a = gbmCondMeanCoarse r σ T 1 ℓ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = gbmCondStdCoarse r σ T 1 ℓ := ⟨_, rfl⟩
  have ham : Measurable a := by rw [ha]; unfold gbmCondMeanCoarse; fun_prop
  have hbm : Measurable b := by rw [hb]; unfold gbmCondStdCoarse; fun_prop
  have hb0 : ∀ z, 0 ≤ b z := fun z => by rw [hb]; unfold gbmCondStdCoarse; positivity
  have hbne : ∀ᵐ z ∂stdNormalSeq, b z ≠ 0 := by
    filter_upwards [measurePreserving_pairAvg.quasiMeasurePreserving.ae
      (ae_gbm_milsteinPath_ne_zero r σ one_ne_zero hσ hh (2 ^ ℓ - 1))] with z hz
    rw [hb]
    unfold gbmCondStdCoarse
    exact mul_ne_zero (abs_ne_zero.2 hz) hsh.ne'
  have hg : MemLp (fun z : ℕ → ℝ => ‖1 + r * (T / 2 ^ ℓ) +
      σ * (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2))‖ *
        (|σ| * Real.sqrt (T / 2 ^ (ℓ + 1)))⁻¹) 2 stdNormalSeq := by
    have hz : MemLp (fun z : ℕ → ℝ => z (2 ^ (ℓ + 1) - 2)) 2 stdNormalSeq :=
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
        (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) _)
    exact (((memLp_const (1 + r * (T / 2 ^ ℓ))).add
      ((hz.const_mul (Real.sqrt (T / 2 ^ (ℓ + 1)))).const_mul σ)).norm.mul_const _)
  have key : ∀ (X w : ℝ), |X + r * X * (T / 2 ^ ℓ) + σ * X * (Real.sqrt (T / 2 ^ (ℓ + 1)) * w)| /
      (|σ * X| * Real.sqrt (T / 2 ^ (ℓ + 1))) ≤
      ‖1 + r * (T / 2 ^ ℓ) + σ * (Real.sqrt (T / 2 ^ (ℓ + 1)) * w)‖ *
        (|σ| * Real.sqrt (T / 2 ^ (ℓ + 1)))⁻¹ := fun X w => by
    rw [show X + r * X * (T / 2 ^ ℓ) + σ * X * (Real.sqrt (T / 2 ^ (ℓ + 1)) * w) =
        X * (1 + r * (T / 2 ^ ℓ) + σ * (Real.sqrt (T / 2 ^ (ℓ + 1)) * w)) by ring,
      show |σ * X| * Real.sqrt (T / 2 ^ (ℓ + 1)) = |X| * (|σ| * Real.sqrt (T / 2 ^ (ℓ + 1))) by
        rw [abs_mul]; ring, Real.norm_eq_abs, ← div_eq_mul_inv]
    exact abs_mul_div_abs_mul_le _ _ (by positivity)
  have hab : MemLp (fun z => |a z| / b z) 2 stdNormalSeq := by
    refine hg.of_le ((continuous_abs.measurable.comp ham).div hbm).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) (hb0 z))]
    refine le_trans ?_ (le_abs_self _)
    rw [ha, hb]
    unfold gbmCondMeanCoarse gbmCondStdCoarse
    exact key _ _
  obtain ⟨h1, h2, h3⟩ := hasDerivAt_integral_cdf_mul_div ham hbm hb0 hbne hab K hs₀
  have eP : ∀ s z, gbmDigitalCondCoarse r σ T s K ℓ z =
      cdf (gaussianReal 0 1) ((s * a z - K) / (|s| * b z)) := fun s z => by
    unfold gbmDigitalCondCoarse
    rw [gbmCondMeanCoarse_eq_mul, gbmCondStdCoarse_eq_mul, ha, hb]
  have eD : ∀ z, gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z =
      gaussianPDFReal 0 1 ((s₀ * a z - K) / (|s₀| * b z)) * (K / (s₀ * (|s₀| * b z))) :=
    fun z => by
    unfold gbmDigitalCondCoarseDelta
    rw [gbmCondMeanCoarse_eq_mul, gbmCondStdCoarse_eq_mul, ha, hb]
  have eD' : gbmDigitalCondCoarseDelta r σ T s₀ K ℓ = fun z =>
      gaussianPDFReal 0 1 ((s₀ * a z - K) / (|s₀| * b z)) * (K / (s₀ * (|s₀| * b z))) :=
    funext eD
  simp only [eP, eD]
  rw [eD']
  exact ⟨h1, h2, h3⟩

/-- **The digital delta via the conditional expectation: pathwise sensitivities of the smoothed
payoffs, their unbiasedness and (2.4)** (Giles 2015, §5.4, p. 42, l. 1829–1832: "Sensitivities for
digital options can be obtained by first using the conditional expectation approach described
previously, and then applying pathwise sensitivity analysis to this"; the conditional-expectation
payoffs of §5.2, p. 36, l. 1551–1574, and (2.4), l. 1584–1590).  For GBM with `s₀ ≠ 0`, `σ ≠ 0`,
`T > 0`, any strike `K` and level `ℓ`, the fine payoff `P^f_ℓ(s) = Φ((m_f − K)/s_f)`
(`gbmDigitalCondFine`) and the coarse payoff `P^c_ℓ(s) = Φ((m_c − K)/s_c)` used on level `ℓ + 1`
(`gbmDigitalCondCoarse`), as functions of the initial value `s`:
* are a.s. differentiable at `s₀`, with pathwise sensitivities
  `∂P^f_ℓ/∂s₀ = φ((m_f − K)/s_f) K/(s₀ s_f)` (`gbmDigitalCondFineDelta`) and
  `∂P^c_ℓ/∂s₀ = φ((m_c − K)/s_c) K/(s₀ s_c)` (`gbmDigitalCondCoarseDelta`);
* these sensitivities are square integrable, with no lower bound on `s_f` needed: the Gaussian
  factor compensates `1/s_f` (`abs_pdf_mul_div_le`);
* they are unbiased: `d/ds₀ E[P^f_ℓ] = E[∂P^f_ℓ/∂s₀]`, `d/ds₀ E[P^c_ℓ] = E[∂P^c_ℓ/∂s₀]`;
* (2.4) holds for the sensitivities: `E[∂P^f_ℓ/∂s₀] = E[∂P^c_ℓ/∂s₀]` (differentiate the identity
  `E[P^f_ℓ(s)] = E[P^c_ℓ(s)]`, valid for every `s ≠ 0`, at `s₀`).

**Deviations.**  GBM and the delta (`∂/∂s₀`) only; the paper refers to Burgos and Giles (2012)
for the general estimators.  `s₀ ≠ 0` is needed: at `s₀ = 0` the payoffs jump. -/
theorem gbm_digital_condExp_delta (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (ℓ : ℕ) :
    (∀ᵐ z ∂stdNormalSeq, HasDerivAt (fun s => gbmDigitalCondFine r σ T s K ℓ z)
      (gbmDigitalCondFineDelta r σ T s₀ K ℓ z) s₀) ∧
    (∀ᵐ z ∂stdNormalSeq, HasDerivAt (fun s => gbmDigitalCondCoarse r σ T s K ℓ z)
      (gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z) s₀) ∧
    MemLp (gbmDigitalCondFineDelta r σ T s₀ K ℓ) 2 stdNormalSeq ∧
    MemLp (gbmDigitalCondCoarseDelta r σ T s₀ K ℓ) 2 stdNormalSeq ∧
    HasDerivAt (fun s => ∫ z, gbmDigitalCondFine r σ T s K ℓ z ∂stdNormalSeq)
      (∫ z, gbmDigitalCondFineDelta r σ T s₀ K ℓ z ∂stdNormalSeq) s₀ ∧
    HasDerivAt (fun s => ∫ z, gbmDigitalCondCoarse r σ T s K ℓ z ∂stdNormalSeq)
      (∫ z, gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z ∂stdNormalSeq) s₀ ∧
    ∫ z, gbmDigitalCondFineDelta r σ T s₀ K ℓ z ∂stdNormalSeq =
      ∫ z, gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z ∂stdNormalSeq := by
  obtain ⟨hf1, hf2, hf3⟩ := gbmDigitalCondFine_delta r σ hs₀ hσ hT K ℓ
  obtain ⟨hc1, hc2, hc3⟩ := gbmDigitalCondCoarse_delta r σ hs₀ hσ hT K ℓ
  have heq : (fun s => ∫ z, gbmDigitalCondCoarse r σ T s K ℓ z ∂stdNormalSeq) =ᶠ[nhds s₀]
      fun s => ∫ z, gbmDigitalCondFine r σ T s K ℓ z ∂stdNormalSeq := by
    filter_upwards [eventually_ne_nhds hs₀] with s hs
    exact (gbmDigitalCond_integral_eq r σ hs hσ hT K ℓ).symm
  exact ⟨hf1, hc1, hf2, hc2, hf3, hc3, (hf3.congr_of_eventuallyEq heq).unique hc3⟩

/-- **The telescoping sum of the digital-delta corrections is the delta of the discretised digital
price** (Giles 2015, §5.4, p. 42, l. 1829–1832, with (2.4), p. 8, and §5.2, p. 36, l. 1584–1590:
"This ensures that the identity in Equation (2.4) is respected so that the telescoping summation
remains valid").  For GBM with `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, any `K` and `L`, the level corrections
`∂P^f_ℓ/∂s₀ − ∂P^c_{ℓ−1}/∂s₀` (`fineCoarseDiff` of `gbmDigitalCondFineDelta` and
`gbmDigitalCondCoarseDelta`, `∂P^c_{−1}/∂s₀ = 0`) are square integrable, and the sum of their
means over `ℓ ≤ L` is `d/ds₀ P(Ŝ^f_N > K)`, the delta of the digital option for the level-`L`
fine path `Ŝ^f_N` (`gbmMilEM`: Milstein steps and an Euler–Maruyama last step,
`E[P^f_L] = P(Ŝ^f_N > K)`).  So the multilevel estimator of the digital delta built from the
pathwise sensitivities of the conditional-expectation payoffs is unbiased for the delta of the
finest-level digital price.

**Not proved.**  The convergence of `d/ds₀ P(Ŝ^f_N > K)` to the true delta `d/ds₀ P(S_T > K)` as
`L → ∞` (a convergence of densities at the strike, not implied by the weak convergence of the
prices); the variance of the corrections (the paper gives no rate: it defers to Burgos 2014,
l. 1834–1835; heuristically and numerically `V_ℓ ≈ O(h^{1/2})`). -/
theorem gbm_digital_condExp_delta_telescope (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (L : ℕ) :
    (∀ ℓ, MemLp (fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
      (gbmDigitalCondCoarseDelta r σ T s₀ K) ℓ) 2 stdNormalSeq) ∧
    HasDerivAt (fun s => ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s L z)
        ∂stdNormalSeq)
      (∑ ℓ ∈ range (L + 1), ∫ z, fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
        (gbmDigitalCondCoarseDelta r σ T s₀ K) ℓ z ∂stdNormalSeq) s₀ := by
  have hD := fun ℓ => gbm_digital_condExp_delta r σ hs₀ hσ hT K ℓ
  have hPf : ∀ ℓ, MemLp (gbmDigitalCondFineDelta r σ T s₀ K ℓ) 2 stdNormalSeq :=
    fun ℓ => (hD ℓ).2.2.1
  have hPc : ∀ ℓ, MemLp (gbmDigitalCondCoarseDelta r σ T s₀ K ℓ) 2 stdNormalSeq :=
    fun ℓ => (hD ℓ).2.2.2.1
  refine ⟨memLp_fineCoarseDiff hPf hPc, ?_⟩
  have hsum : ∀ L : ℕ, ∑ ℓ ∈ range (L + 1), ∫ z, fineCoarseDiff
      (gbmDigitalCondFineDelta r σ T s₀ K) (gbmDigitalCondCoarseDelta r σ T s₀ K) ℓ z
        ∂stdNormalSeq = ∫ z, gbmDigitalCondFineDelta r σ T s₀ K L z ∂stdNormalSeq := by
    intro L
    induction L with
    | zero => rw [Finset.sum_range_one]; rfl
    | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      have e : ∫ z, fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
          (gbmDigitalCondCoarseDelta r σ T s₀ K) (L + 1) z ∂stdNormalSeq =
          ∫ z, gbmDigitalCondFineDelta r σ T s₀ K (L + 1) z ∂stdNormalSeq -
            ∫ z, gbmDigitalCondCoarseDelta r σ T s₀ K L z ∂stdNormalSeq :=
        integral_sub ((hPf (L + 1)).integrable one_le_two) ((hPc L).integrable one_le_two)
      rw [e, ← (hD L).2.2.2.2.2.2]
      ring
  rw [hsum L]
  have heq : (fun s => ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMilEM r σ T s L z)
      ∂stdNormalSeq) =ᶠ[nhds s₀] fun s => ∫ z, gbmDigitalCondFine r σ T s K L z ∂stdNormalSeq := by
    filter_upwards [eventually_ne_nhds hs₀] with s hs
    exact ((gbmDigitalCondFine_condExp r σ hs hσ hT K L).2).symm
  exact (hD L).2.2.2.2.1.congr_of_eventuallyEq heq

end MLMC
