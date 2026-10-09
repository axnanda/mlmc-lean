import MlmcLean.LevyTruncation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Lévy–Khintchine law of the truncation limit (Giles 2015, §6.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §6.2 "More
general processes", p. 47 (`docs/giles2015.txt`, l. 2037–2051; coverage row G6-06,
l. 2038–2043).  "With infinite activity Lévy processes it is impossible to simulate each jump.
One approach is to simulate the large jumps and either neglect the small jumps or approximate
their effect by adding a Brownian diffusion term …  Following this approach, the cutoff `δ_ℓ` for
the jumps which are simulated varies with level, and `δ_ℓ → 0` as `ℓ → ∞` to ensure that the bias
converges to zero."

**Setting.**  `MlmcLean.LevyTruncation` builds all truncation levels of a pure-jump Lévy process
with Lévy measure `ν` (`∫ min(1, z²) dν < ∞`, possibly `ν(ℝ) = ∞`) over `[0, T]` on one space of
independent compound Poisson bands (`bandInputLaw Λ M`, `Λ_k • M_k = T • ν|_{band k}`): the
level-`ℓ` value `bandApprox ν T δ ℓ` is the sum of the simulated jumps `|z| ≥ δ_ℓ` minus the
compensator `levyComp ν T δ_ℓ = T ∫_{δ_ℓ ≤ |z| < 1} z dν`, and `levy_truncation_limit` gives an
`L²` limit `X` of the levels, `E[(X − X^{δ_ℓ})²] = T ∫_{|z| < δ_ℓ} z² dν → 0`, without identifying
its law.  Here the law of the limit is identified: it is the law of the terminal value `X_T` of
the Lévy process with characteristic triplet `(0, 0, ν)` for the truncation `1_{|z|<1}`,
`E[e^{itX}] = exp (T ∫ (e^{itz} − 1 − itz 1_{|z|<1}) ν(dz))` (the pure-jump Lévy–Khintchine
formula).

**Results.**
* `norm_levyKhintchine_le`, `integrable_levyKhintchine`:
  `|e^{itz} − 1 − itz 1_{|z|<1}| ≤ (2t² + 2) min(1, z²)`, so the exponent is finite for every Lévy
  measure.
* `charFun_bandApprox` (the levels): `E[e^{itX^{δ_ℓ}}] = exp (T ∫_{|z| ≥ δ_ℓ}
  (e^{itz} − 1 − itz 1_{|z|<1}) dν)`; the simulated jumps form a compound Poisson variable
  (superposition `bandApprox_map_eq` and `charFun_cpSum`) and the compensator contributes the
  phase `e^{−it T ∫_{δ_ℓ ≤ |z| < 1} z dν}`.
* `tendsto_levyKhintchine_exponent`: `∫_{|z| ≥ δ_ℓ} → ∫` by dominated convergence.
* `norm_charFun_map_sub_le`, `tendsto_charFun_of_L2`:
  `|E e^{itX} − E e^{itY}| ≤ |t| E|X − Y| ≤ |t| (E(X − Y)²)^{1/2}`, so `L²` convergence implies
  pointwise convergence of the characteristic functions.
* `levy_limit_charFun`: every `L²` limit `X` of the levels has the Lévy–Khintchine
  characteristic function; `levy_truncation_limit_charFun`: so does the limit of
  `levy_truncation_limit`.
* `levy_limit_map_eq`: the law of the limit depends only on `ν` and `T`, not on the cutoffs
  `δ_ℓ`, the band laws or the choice of the `L²` limit.
* `exists_unique_levyKhintchine_law`: for every Lévy measure `ν` and `T ≥ 0` there is a unique
  finite measure with this characteristic function, and it is a probability measure.
* `stableLike_limit_charFun`: for the one-sided stable-like example `ν(dz) = c z^{−1−Y} dz` on
  `(0, 1]` and `δ_ℓ = 2^{−ℓ}`, `E[e^{itX}] = exp (T ∫_0^1 c z^{−1−Y} (e^{itz} − 1 − itz) dz)`.

**Deviations.**  Only the law of the terminal value `X_T` is identified (through its
characteristic function); the limit is not constructed as a process with independent stationary
increments, and there is no drift or Brownian component (the triplet is `(0, 0, Tν)` at time
`T`).  The quadratic bound `|e^{ix} − 1 − ix| ≤ 2x²` is used instead of the sharp `x²/2` (any
quadratic bound suffices for dominated convergence).  The law is that of any `L²` limit of the
levels (all of them agree almost surely).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal ENNReal

namespace MLMC

/-! ### The Lévy–Khintchine integrand -/

/-- The second-order bound `|e^{ix} − 1 − ix| ≤ 2x²` for real `x` (Giles 2015, §6.2, p. 47,
l. 2038–2041: "it is impossible to simulate each jump.  One approach is to simulate the large jumps
and … neglect the small jumps"; the neglected small jumps contribute `O(x²)` to the exponent). -/
lemma norm_cexp_mul_I_sub_one_sub_le (x : ℝ) :
    ‖Complex.exp (x * Complex.I) - 1 - x * Complex.I‖ ≤ 2 * x ^ 2 := by
  have hn : ‖(x * Complex.I : ℂ)‖ = |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  by_cases hx : |x| ≤ 1
  · have h := Complex.norm_exp_sub_one_sub_id_le (x := x * Complex.I) (by rw [hn]; exact hx)
    rw [hn, sq_abs] at h
    nlinarith [sq_nonneg x]
  · replace hx := not_le.1 hx
    have h1 : ‖Complex.exp (x * Complex.I) - 1‖ ≤ |x| := by
      have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)
      rwa [mul_comm, Real.norm_eq_abs] at h
    calc ‖Complex.exp (x * Complex.I) - 1 - x * Complex.I‖
        ≤ ‖Complex.exp (x * Complex.I) - 1‖ + ‖(x * Complex.I : ℂ)‖ := norm_sub_le _ _
      _ ≤ |x| + |x| := by rw [hn]; linarith
      _ ≤ 2 * x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]

/-- The first-order bound `|e^{ia} − e^{ib}| ≤ |a − b|` for real `a`, `b` (Giles 2015, §6.2,
p. 47, l. 2042–2043: "`δ_ℓ → 0` as `ℓ → ∞` to ensure that the bias converges to zero"; nearby
values have nearby characteristic functions). -/
lemma norm_cexp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have e : Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I) =
      Complex.exp (b * Complex.I) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- The Lévy–Khintchine integrand is dominated by the Lévy integrand (Giles 2015, §6.2, p. 47,
l. 2038: "infinite activity Lévy processes"):
`|e^{itz} − 1 − itz 1_{|z|<1}| ≤ (2t² + 2) min(1, z²)`. -/
lemma norm_levyKhintchine_le (t z : ℝ) :
    ‖Complex.exp (t * z * Complex.I) - 1 -
        t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I‖ ≤
      (2 * t ^ 2 + 2) * min 1 (z ^ 2) := by
  by_cases hz : |z| < 1
  · rw [Set.indicator_of_mem (show z ∈ {z : ℝ | |z| < 1} from hz), id]
    have h2 : z ^ 2 ≤ 1 := by nlinarith [abs_nonneg z, sq_abs z]
    rw [min_eq_right h2]
    have h := norm_cexp_mul_I_sub_one_sub_le (t * z)
    push_cast at h
    calc _ ≤ 2 * (t * z) ^ 2 := h
      _ ≤ (2 * t ^ 2 + 2) * z ^ 2 := by nlinarith [sq_nonneg z, sq_nonneg t]
  · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | |z| < 1} from hz)]
    have h2 : 1 ≤ z ^ 2 := by nlinarith [abs_nonneg z, sq_abs z, not_lt.1 hz]
    rw [min_eq_left h2]
    have h := norm_sub_le (Complex.exp (t * z * Complex.I)) 1
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, norm_one] at h
    push_cast at h ⊢
    rw [mul_zero, zero_mul, sub_zero]
    nlinarith [sq_nonneg t]

/-- The Lévy–Khintchine integrand `z ↦ e^{itz} − 1 − itz 1_{|z|<1}` is measurable (Giles 2015,
§6.2, p. 47, l. 2038–2040: "simulate the large jumps and either neglect the small jumps or
approximate their effect"). -/
lemma measurable_levyKhintchine (t : ℝ) :
    Measurable fun z : ℝ => Complex.exp (t * z * Complex.I) - 1 -
      t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I := by
  have hm : Measurable fun z : ℝ => ({z : ℝ | |z| < 1}.indicator id z : ℝ) :=
    measurable_id.indicator (measurableSet_lt continuous_abs.measurable measurable_const)
  fun_prop

/-- **The Lévy–Khintchine exponent is finite** (Giles 2015, §6.2, p. 47, l. 2038: "With infinite
activity Lévy processes it is impossible to simulate each jump"; although `ν` may have infinite
mass, the compensated exponent converges): for a Lévy measure `ν` (`∫ min(1, z²) dν < ∞`) and
every `t`, `z ↦ e^{itz} − 1 − itz 1_{|z|<1}` is `ν`-integrable. -/
theorem integrable_levyKhintchine {ν : Measure ℝ}
    (hν : Integrable (fun z => min 1 (z ^ 2)) ν) (t : ℝ) :
    Integrable (fun z : ℝ => Complex.exp (t * z * Complex.I) - 1 -
      t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I) ν :=
  (hν.const_mul (2 * t ^ 2 + 2)).mono' (measurable_levyKhintchine t).aestronglyMeasurable
    (ae_of_all _ fun z => norm_levyKhintchine_le t z)

/-! ### (a) The characteristic function of a truncation level -/

/-- **The characteristic function of the level-`ℓ` approximation** (Giles 2015, §6.2, p. 47,
l. 2038–2043: "simulate the large jumps and … neglect the small jumps …  the cutoff `δ_ℓ` for the
jumps which are simulated varies with level").  For a Lévy measure `ν`, positive antitone cutoffs
and band laws `Λ_k • M_k = T • ν|_{band k}`, the level-`ℓ` value (the jumps `|z| ≥ δ_ℓ` of the
bands `0, …, ℓ` minus the compensator `T ∫_{δ_ℓ ≤ |z| < 1} z dν`) has the characteristic function
`exp (T ∫_{|z| ≥ δ_ℓ} (e^{itz} − 1 − itz 1_{|z|<1}) dν)`. -/
theorem charFun_bandApprox {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ)
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) (ℓ : ℕ) (t : ℝ) :
    charFun ((bandInputLaw Λ M).map (bandApprox ν T δ ℓ)) t =
      Complex.exp (T * ∫ z in levySet (δ ℓ), (Complex.exp (t * z * Complex.I) - 1 -
        t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I) ∂ν) := by
  have hfin := levy_measure_levySet_lt_top hν (hδpos ℓ)
  obtain ⟨r, μ, hμ, h⟩ := exists_smul_eq_restrict (ν := ν) T hfin.ne
  have := isProbabilityMeasure_cpInputLaw r μ
  rw [bandApprox_map_eq T hδanti hband ℓ h]
  set S := levySet (δ ℓ) with hS
  have hSm : MeasurableSet S := measurableSet_levySet (δ ℓ)
  have hf : Measurable (S.indicator (id : ℝ → ℝ)) := measurable_id.indicator hSm
  -- the compensator contributes a deterministic phase
  have key : charFun ((cpInputLaw r μ).map (levyFine ν T (δ ℓ))) t =
      charFun ((cpInputLaw r μ).map (cpSum (S.indicator id))) t *
        Complex.exp (-(t * levyComp ν T (δ ℓ)) * Complex.I) := by
    rw [charFun_apply_real, charFun_apply_real,
      integral_map (measurable_levyFine ν T (δ ℓ)).aemeasurable (by fun_prop),
      integral_map (measurable_cpSum hf).aemeasurable (by fun_prop), ← integral_mul_const]
    congr 1
    funext ω
    rw [levyFine, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [key, charFun_cpSum r μ hf, exponent_levySet le_rfl h t, ← Complex.exp_add]
  congr 1
  -- `∫ (e^{itz} − 1) d(T • ν|_S) − itT ∫_S z 1_{|z|<1} dν = T ∫_S (e^{itz} − 1 − itz 1_{|z|<1}) dν`
  have := isFiniteMeasure_restrict.2 hfin.ne
  set g : ℝ → ℝ := fun z => {z : ℝ | |z| < 1}.indicator id z with hg
  have hgm : Measurable g :=
    measurable_id.indicator (measurableSet_lt continuous_abs.measurable measurable_const)
  have hgI : Integrable g (ν.restrict S) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun z => ?_)
    by_cases hz : |z| < 1
    · rw [hg]
      dsimp only
      rw [Set.indicator_of_mem (show z ∈ {z : ℝ | |z| < 1} from hz), id, Real.norm_eq_abs]
      exact hz.le
    · rw [hg]
      dsimp only
      rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | |z| < 1} from hz), norm_zero]
      exact zero_le_one
  have hcomp : levyComp ν T (δ ℓ) = T * ∫ z in S, g z ∂ν := by
    rw [hg, setIntegral_indicator
      (measurableSet_lt continuous_abs.measurable measurable_const)]
    rfl
  have hI1 : Integrable (fun z : ℝ => Complex.exp (t * z * Complex.I) - 1) (ν.restrict S) :=
    integrable_cexp_sub_one (ν.restrict S) measurable_id t
  have hI2 : Integrable (fun z : ℝ => (t : ℂ) * (g z : ℂ) * Complex.I) (ν.restrict S) :=
    (hgI.ofReal.const_mul (t : ℂ)).mul_const Complex.I
  rw [← nnreal_mul_integral_eq, integral_sub hI1 hI2, integral_mul_const, integral_const_mul,
    integral_complex_ofReal, hcomp]
  push_cast
  ring

/-! ### (b) The limit of the exponents -/

/-- The exponents of the levels converge (Giles 2015, §6.2, p. 47, l. 2042–2043: "`δ_ℓ → 0` as
`ℓ → ∞`"; dominated convergence): if `δ_ℓ → 0`, then
`∫_{|z| ≥ δ_ℓ} (e^{itz} − 1 − itz 1_{|z|<1}) dν → ∫ (e^{itz} − 1 − itz 1_{|z|<1}) dν`. -/
lemma tendsto_levyKhintchine_exponent {ν : Measure ℝ}
    (hν : Integrable (fun z => min 1 (z ^ 2)) ν) {δ : ℕ → ℝ} (hδlim : Tendsto δ atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun ℓ => ∫ z in levySet (δ ℓ), (Complex.exp (t * z * Complex.I) - 1 -
        t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I) ∂ν) atTop
      (𝓝 (∫ z, (Complex.exp (t * z * Complex.I) - 1 -
        t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I) ∂ν)) := by
  set ψ : ℝ → ℂ := fun z => Complex.exp (t * z * Complex.I) - 1 -
    t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I with hψ
  have hψm : Measurable ψ := measurable_levyKhintchine t
  have hψI : Integrable ψ ν := integrable_levyKhintchine hν t
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  simp_rw [← integral_indicator (measurableSet_levySet _)]
  refine tendsto_integral_of_dominated_convergence (fun z => ‖ψ z‖)
    (fun n => (hψm.indicator (measurableSet_levySet _)).aestronglyMeasurable) hψI.norm
    (fun n => ae_of_all _ fun z => norm_indicator_le_norm_self _ _) (ae_of_all _ fun z => ?_)
  change Tendsto (fun n => (levySet (δ n)).indicator ψ z) atTop (𝓝 (ψ z))
  by_cases hz0 : z = 0
  · subst hz0
    have h0 : ∀ s : Set ℝ, s.indicator ψ 0 = 0 := fun s =>
      Set.indicator_apply_eq_zero.2 fun _ => hψ0
    simp only [h0, hψ0]
    exact tendsto_const_nhds
  · have hpos : 0 < |z| := abs_pos.2 hz0
    have hev : ∀ᶠ n in atTop, δ n ≤ |z| :=
      ((tendsto_order.1 hδlim).2 _ hpos).mono fun n h => h.le
    refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
    dsimp only
    rw [Set.indicator_of_mem (show z ∈ levySet (δ n) from hn)]

/-! ### (c) Mean-square convergence implies convergence of characteristic functions -/

/-- Characteristic functions are `L²`-Lipschitz (Giles 2015, §6.2, p. 47, l. 2042–2043: "`δ_ℓ → 0`
as `ℓ → ∞` to ensure that the bias converges to zero"; here the bias of the payoffs
`x ↦ e^{itx}`): on a probability space,
`|E e^{itX} − E e^{itY}| ≤ |t| E|X − Y| ≤ |t| (E(X − Y)²)^{1/2}`. -/
lemma norm_charFun_map_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXY : MemLp (fun ω => X ω - Y ω) 2 P) (t : ℝ) :
    ‖charFun (P.map X) t - charFun (P.map Y) t‖ ≤
      |t| * Real.sqrt (∫ ω, (X ω - Y ω) ^ 2 ∂P) := by
  have hb : ∀ Z : Ω → ℝ, AEMeasurable Z P →
      Integrable (fun ω => Complex.exp (t * Z ω * Complex.I)) P := fun Z hZ => by
    refine Integrable.of_bound ((by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (t * x * Complex.I)).comp_aestronglyMeasurable hZ.aestronglyMeasurable) 1
      (ae_of_all _ fun ω => ?_)
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  rw [charFun_apply_real, charFun_apply_real, integral_map hX (by fun_prop),
    integral_map hY (by fun_prop), ← integral_sub (hb X hX) (hb Y hY)]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ ω, ‖Complex.exp (t * X ω * Complex.I) - Complex.exp (t * Y ω * Complex.I)‖ ≤
      |t| * |X ω - Y ω| := fun ω => by
    have h := norm_cexp_mul_I_sub_le (t * X ω) (t * Y ω)
    rw [← mul_sub, abs_mul] at h
    push_cast at h
    exact h
  calc ∫ ω, ‖Complex.exp (t * X ω * Complex.I) - Complex.exp (t * Y ω * Complex.I)‖ ∂P
      ≤ ∫ ω, |t| * |X ω - Y ω| ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          ((hXY.integrable one_le_two).abs.const_mul |t|) (ae_of_all _ hpt)
    _ = |t| * ∫ ω, |X ω - Y ω| ∂P := integral_const_mul _ _
    _ ≤ |t| * Real.sqrt (∫ ω, (X ω - Y ω) ^ 2 ∂P) :=
        mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq hXY) (abs_nonneg t)

/-- Mean-square convergence implies convergence of the characteristic functions (Giles 2015,
§6.2, p. 47, l. 2042–2043: "`δ_ℓ → 0` as `ℓ → ∞` to ensure that the bias converges to zero"): if
`E[(X − Y_n)²] → 0`, then `E e^{itY_n} → E e^{itX}` for every `t`. -/
lemma tendsto_charFun_of_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {Y : ℕ → Ω → ℝ} (hX : AEMeasurable X P)
    (hY : ∀ n, AEMeasurable (Y n) P) (hXY : ∀ n, MemLp (fun ω => X ω - Y n ω) 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (X ω - Y n ω) ^ 2 ∂P) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => charFun (P.map (Y n)) t) atTop (𝓝 (charFun (P.map X) t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (hlim.sqrt).const_mul |t|
  rw [Real.sqrt_zero, mul_zero] at h
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
  rw [norm_sub_rev]
  exact norm_charFun_map_sub_le hX (hY n) (hXY n) t

/-! ### (d) The law of the limit -/

/-- A variable at finite `L²` distance from a measurable one is almost everywhere measurable
(Giles 2015, §6.2, p. 47, l. 2042–2043: the limit of the levels "as `ℓ → ∞`"). -/
lemma aemeasurable_of_memLp_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X A : Ω → ℝ} (hA : Measurable A) (hXA : MemLp (fun ω => X ω - A ω) 2 P) :
    AEMeasurable X P :=
  (hXA.1.aemeasurable.add hA.aemeasurable).congr (ae_of_all _ fun ω => by simp)

/-- **The limit of the truncation levels has the Lévy–Khintchine law** (Giles 2015, §6.2, p. 47,
l. 2038–2043: "With infinite activity Lévy processes it is impossible to simulate each jump.  One
approach is to simulate the large jumps and either neglect the small jumps …  the cutoff `δ_ℓ`
for the jumps which are simulated varies with level, and `δ_ℓ → 0` as `ℓ → ∞` to ensure that the
bias converges to zero").  Let `ν` be a Lévy measure (`∫ min(1, z²) dν < ∞`), `T ≥ 0`, the cutoffs
`0 < δ_ℓ ≤ δ_0 ≤ 1` decrease to `0`, and the levels be built from independent compound Poisson
bands (`Λ_k • M_k = T • ν|_{band k}`).  If `X` is a mean-square limit of the levels
(`X − X^{δ_0} ∈ L²` and `E[(X − X^{δ_ℓ})²] → 0`), then for every `t`
`E[e^{itX}] = exp (T ∫ (e^{itz} − 1 − itz 1_{|z|<1}) ν(dz))`: `X` has the law of the terminal value
`X_T` of the pure-jump Lévy process with Lévy measure `ν` (truncation `1_{|z|<1}`). -/
theorem levy_limit_charFun {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1)
    (hδlim : Tendsto δ atTop (𝓝 0)) {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ}
    [∀ k, IsProbabilityMeasure (M k)] (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k))
    {X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ}
    (hX0 : MemLp (fun ω => X ω - bandApprox ν T δ 0 ω) 2 (bandInputLaw Λ M))
    (hXlim : Tendsto (fun ℓ => ∫ ω, (X ω - bandApprox ν T δ ℓ ω) ^ 2 ∂(bandInputLaw Λ M))
      atTop (𝓝 0)) (t : ℝ) :
    charFun ((bandInputLaw Λ M).map X) t =
      Complex.exp (T * ∫ z, (Complex.exp (t * z * Complex.I) - 1 -
        t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I) ∂ν) := by
  have := isProbabilityMeasure_bandInputLaw Λ M
  have hAm : ∀ ℓ, Measurable (bandApprox ν T δ ℓ) := measurable_bandApprox ν T δ
  have hXA : ∀ ℓ, MemLp (fun ω => X ω - bandApprox ν T δ ℓ ω) 2 (bandInputLaw Λ M) := fun ℓ =>
    (hX0.sub (bandApprox_sq_sub hν T hδpos hδanti hδ1 hband (Nat.zero_le ℓ)).1).ae_eq
      (ae_of_all _ fun ω => by simp)
  have h1 := tendsto_charFun_of_L2 (aemeasurable_of_memLp_sub (hAm 0) hX0)
    (fun ℓ => (hAm ℓ).aemeasurable) hXA hXlim t
  have h2 := ((tendsto_levyKhintchine_exponent hν hδlim t).const_mul ((T : ℝ) : ℂ)).cexp
  simp_rw [← charFun_bandApprox hν T hδpos hδanti hband _ t] at h2
  exact tendsto_nhds_unique h1 h2

/-- **The truncation limit and its Lévy–Khintchine law** (Giles 2015, §6.2, p. 47, l. 2038–2043:
"simulate the large jumps and … neglect the small jumps …  `δ_ℓ → 0` as `ℓ → ∞` to ensure that the
bias converges to zero").  With the hypotheses of the mean-square construction (a Lévy measure
`ν`, cutoffs `0 < δ_ℓ ≤ δ_0 ≤ 1` decreasing to `0`, band laws `Λ_k • M_k = T • ν|_{band k}`), there
is a limit `X` of the levels with `X − X^{δ_0} ∈ L²` and
`E[(X − X^{δ_ℓ})²] = T ∫_{|z| < δ_ℓ} z² dν` for every `ℓ`, and its law has the characteristic
function `t ↦ exp (T ∫ (e^{itz} − 1 − itz 1_{|z|<1}) ν(dz))`. -/
theorem levy_truncation_limit_charFun {ν : Measure ℝ}
    (hν : Integrable (fun z => min 1 (z ^ 2)) ν) (T : ℝ≥0) {δ : ℕ → ℝ}
    (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1)
    (hδlim : Tendsto δ atTop (𝓝 0)) {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ}
    [∀ k, IsProbabilityMeasure (M k)] (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k)) :
    ∃ X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ,
      MemLp (fun ω => X ω - bandApprox ν T δ 0 ω) 2 (bandInputLaw Λ M) ∧
      (∀ ℓ, ∫ ω, (X ω - bandApprox ν T δ ℓ ω) ^ 2 ∂(bandInputLaw Λ M) =
          T * ∫ z in {z : ℝ | |z| < δ ℓ}, z ^ 2 ∂ν) ∧
      ∀ t : ℝ, charFun ((bandInputLaw Λ M).map X) t =
        Complex.exp (T * ∫ z, (Complex.exp (t * z * Complex.I) - 1 -
          t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I) ∂ν) := by
  obtain ⟨X, hX0, hXℓ, hτ, -⟩ := levy_truncation_limit hν T hδpos hδanti hδ1 hδlim hband
  have hXlim : Tendsto (fun ℓ => ∫ ω, (X ω - bandApprox ν T δ ℓ ω) ^ 2 ∂(bandInputLaw Λ M))
      atTop (𝓝 0) := hτ.congr fun ℓ => ((hXℓ ℓ).2).symm
  exact ⟨X, hX0, fun ℓ => (hXℓ ℓ).2,
    levy_limit_charFun hν T hδpos hδanti hδ1 hδlim hband hX0 hXlim⟩

/-- **The law of the limit does not depend on the truncation scheme** (Giles 2015, §6.2, p. 47,
l. 2042–2043: "the cutoff `δ_ℓ` for the jumps which are simulated varies with level, and
`δ_ℓ → 0` as `ℓ → ∞`").  For a Lévy measure `ν` and `T ≥ 0`, take two cutoff sequences
`0 < δ_ℓ ≤ δ_0 ≤ 1`, `0 < δ'_ℓ ≤ δ'_0 ≤ 1` decreasing to `0`, two families of band laws
(`Λ_k • M_k = T • ν|_{band_δ k}`, `Λ'_k • M'_k = T • ν|_{band_δ' k}`) and mean-square limits `X`,
`X'` of the respective levels.  Then `X` and `X'` have the same law (that of `X_T`). -/
theorem levy_limit_map_eq {ν : Measure ℝ} (hν : Integrable (fun z => min 1 (z ^ 2)) ν)
    (T : ℝ≥0) {δ δ' : ℕ → ℝ} (hδpos : ∀ k, 0 < δ k) (hδanti : Antitone δ) (hδ1 : δ 0 ≤ 1)
    (hδlim : Tendsto δ atTop (𝓝 0)) (hδpos' : ∀ k, 0 < δ' k) (hδanti' : Antitone δ')
    (hδ1' : δ' 0 ≤ 1) (hδlim' : Tendsto δ' atTop (𝓝 0)) {Λ Λ' : ℕ → ℝ≥0}
    {M M' : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)] [∀ k, IsProbabilityMeasure (M' k)]
    (hband : ∀ k, Λ k • M k = T • ν.restrict (levyBand δ k))
    (hband' : ∀ k, Λ' k • M' k = T • ν.restrict (levyBand δ' k))
    {X X' : (ℕ → ℕ × (ℕ → ℝ)) → ℝ}
    (hX0 : MemLp (fun ω => X ω - bandApprox ν T δ 0 ω) 2 (bandInputLaw Λ M))
    (hXlim : Tendsto (fun ℓ => ∫ ω, (X ω - bandApprox ν T δ ℓ ω) ^ 2 ∂(bandInputLaw Λ M))
      atTop (𝓝 0))
    (hX0' : MemLp (fun ω => X' ω - bandApprox ν T δ' 0 ω) 2 (bandInputLaw Λ' M'))
    (hXlim' : Tendsto (fun ℓ => ∫ ω, (X' ω - bandApprox ν T δ' ℓ ω) ^ 2 ∂(bandInputLaw Λ' M'))
      atTop (𝓝 0)) :
    (bandInputLaw Λ M).map X = (bandInputLaw Λ' M').map X' := by
  have := isProbabilityMeasure_bandInputLaw Λ M
  have := isProbabilityMeasure_bandInputLaw Λ' M'
  have := Measure.isProbabilityMeasure_map (μ := bandInputLaw Λ M)
    (aemeasurable_of_memLp_sub (measurable_bandApprox ν T δ 0) hX0)
  have := Measure.isProbabilityMeasure_map (μ := bandInputLaw Λ' M')
    (aemeasurable_of_memLp_sub (measurable_bandApprox ν T δ' 0) hX0')
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [levy_limit_charFun hν T hδpos hδanti hδ1 hδlim hband hX0 hXlim t,
    levy_limit_charFun hν T hδpos' hδanti' hδ1' hδlim' hband' hX0' hXlim' t]

/-- **The pure-jump Lévy–Khintchine law exists and is unique** (Giles 2015, §6.2, p. 47,
l. 2038: "infinite activity Lévy processes", whose terminal values are the limits of the truncated
simulations "as `ℓ → ∞`", l. 2043).  For every Lévy measure `ν` (`∫ min(1, z²) dν < ∞`) and
`T ≥ 0` there is a probability measure `ρ` on `ℝ` with
`∫ e^{itx} dρ(x) = exp (T ∫ (e^{itz} − 1 − itz 1_{|z|<1}) ν(dz))` for all `t` (the law of the
limit of the truncations with cutoffs `δ_ℓ = 2^{−ℓ}`), and every finite measure with this
characteristic function equals `ρ`. -/
theorem exists_unique_levyKhintchine_law {ν : Measure ℝ}
    (hν : Integrable (fun z => min 1 (z ^ 2)) ν) (T : ℝ≥0) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      (∀ t : ℝ, charFun ρ t = Complex.exp (T * ∫ z, (Complex.exp (t * z * Complex.I) - 1 -
          t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I) ∂ν)) ∧
      ∀ ρ' : Measure ℝ, IsFiniteMeasure ρ' →
        (∀ t : ℝ, charFun ρ' t = Complex.exp (T * ∫ z, (Complex.exp (t * z * Complex.I) - 1 -
          t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I) ∂ν)) → ρ' = ρ := by
  set δ : ℕ → ℝ := fun ℓ => (2 : ℝ)⁻¹ ^ ℓ with hδdef
  have hδpos : ∀ k, 0 < δ k := fun k => by positivity
  have hδanti : Antitone δ := fun m n hmn =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hδ1 : δ 0 ≤ 1 := le_of_eq (pow_zero _)
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨Λ, M, hM, hband⟩ := exists_levy_bandLaws hν T hδpos
  have := isProbabilityMeasure_bandInputLaw Λ M
  obtain ⟨X, hX0, -, hcf⟩ := levy_truncation_limit_charFun hν T hδpos hδanti hδ1 hδlim hband
  have hρ := Measure.isProbabilityMeasure_map (μ := bandInputLaw Λ M)
    (aemeasurable_of_memLp_sub (measurable_bandApprox ν T δ 0) hX0)
  refine ⟨(bandInputLaw Λ M).map X, hρ, hcf, fun ρ' hρ' h' => ?_⟩
  exact Measure.ext_of_charFun (funext fun t => (h' t).trans (hcf t).symm)

/-! ### The one-sided stable-like example -/

/-- The Lévy–Khintchine exponent of the one-sided stable-like example (Giles 2015, §6.2, p. 47,
l. 2038: "infinite activity Lévy processes"): for `ν(dz) = c z^{−1−Y} dz` on `(0, 1]`,
`∫ (e^{itz} − 1 − itz 1_{|z|<1}) dν = ∫_0^1 c z^{−1−Y} (e^{itz} − 1 − itz) dz`. -/
lemma integral_levyKhintchine_stableLikeLevy {c Y : ℝ} (hc : 0 < c) (t : ℝ) :
    ∫ z, (Complex.exp (t * z * Complex.I) - 1 -
        t * ({z : ℝ | |z| < 1}.indicator id z : ℝ) * Complex.I) ∂(stableLikeLevy c Y) =
      ∫ z in Set.Ioo (0 : ℝ) 1, (c * z ^ (-1 - Y) : ℝ) *
        (Complex.exp (t * z * Complex.I) - 1 - t * z * Complex.I) := by
  rw [stableLikeLevy, integral_withDensity_eq_integral_smul (measurable_stableLikeDensity c Y),
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun z hz => ?_
  have hz1 : |z| < 1 := by rw [abs_of_pos hz.1]; exact hz.2
  rw [Set.indicator_of_mem (show z ∈ {z : ℝ | |z| < 1} from hz1), id, NNReal.smul_def,
    Complex.real_smul, stableLikeDensity, Real.coe_toNNReal _ (by have := hz.1; positivity)]

/-- **The Lévy–Khintchine law of the limit for the one-sided stable-like example** (Giles 2015,
§6.2, p. 47, l. 2038–2043: "With infinite activity Lévy processes it is impossible to simulate
each jump.  One approach is to simulate the large jumps and either neglect the small jumps …
`δ_ℓ → 0` as `ℓ → ∞` to ensure that the bias converges to zero").  For the Lévy measure
`ν(dz) = c z^{−1−Y} dz` on `0 < z ≤ 1` (`c > 0`, `Y < 2`; infinite activity for `Y ≥ 0`), the
cutoffs `δ_ℓ = 2^{−ℓ}` and band laws `Λ_k • M_k = T • ν|_{band k}` (which exist), there is a
limit `X` of the levels with `E[(X − X^{δ_ℓ})²] = T c 2^{−(2−Y)ℓ}/(2 − Y)` and
`E[e^{itX}] = exp (T ∫_0^1 c z^{−1−Y} (e^{itz} − 1 − itz) dz)` for every `t`. -/
theorem stableLike_limit_charFun {c Y : ℝ} (hc : 0 < c) (hY2 : Y < 2) (T : ℝ≥0)
    {Λ : ℕ → ℝ≥0} {M : ℕ → Measure ℝ} [∀ k, IsProbabilityMeasure (M k)]
    (hband : ∀ k, Λ k • M k =
      T • (stableLikeLevy c Y).restrict (levyBand (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) k)) :
    ∃ X : (ℕ → ℕ × (ℕ → ℝ)) → ℝ,
      (∀ ℓ : ℕ, ∫ ω, (X ω - bandApprox (stableLikeLevy c Y) T (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) ℓ ω) ^ 2
          ∂(bandInputLaw Λ M) = T * c * (2 : ℝ) ^ (-((2 - Y) * (ℓ : ℝ))) / (2 - Y)) ∧
      ∀ t : ℝ, charFun ((bandInputLaw Λ M).map X) t =
        Complex.exp (T * ∫ z in Set.Ioo (0 : ℝ) 1, (c * z ^ (-1 - Y) : ℝ) *
          (Complex.exp (t * z * Complex.I) - 1 - t * z * Complex.I)) := by
  have hsq := integrable_sq_stableLikeLevy hc hY2
  have hν : Integrable (fun z => min 1 (z ^ 2)) (stableLikeLevy c Y) :=
    hsq.mono' (by fun_prop) (ae_of_all _ fun z => by
      rw [Real.norm_of_nonneg (le_min zero_le_one (sq_nonneg z))]
      exact min_le_right _ _)
  have hδpos : ∀ k, 0 < (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) k := fun k => by positivity
  have hδanti : Antitone fun ℓ => (2 : ℝ)⁻¹ ^ ℓ := fun m n hmn =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hδlim : Tendsto (fun ℓ => (2 : ℝ)⁻¹ ^ ℓ) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨X, -, hXℓ, hcf⟩ := levy_truncation_limit_charFun hν T hδpos hδanti
    (le_of_eq (pow_zero _)) hδlim hband
  refine ⟨X, fun ℓ => ?_, fun t => ?_⟩
  · rw [hXℓ ℓ, stableLike_small_sq hc hY2 ℓ]
    ring
  · rw [hcf t, integral_levyKhintchine_stableLikeLevy hc t]

end MLMC
