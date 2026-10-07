import MlmcLean.DriftImplicit
import MlmcLean.BrownianPaths
import MlmcLean.NestedKinkSde

/-!
# Multiplicative noise for drift-implicit Euler, continuous antithetic Brownian paths, and nested
simulation with several kinks (Giles 2015, §5.6, §5.3, §9.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.6 "Stiff and
highly nonlinear SDEs" (p. 44), §5.3 "Multi-dimensional SDEs" (p. 42) and §9.1 "MLMC treatment"
(p. 58).  Line numbers refer to the text `docs/giles2015.txt`.  Each part extends an earlier module.

**§5.6: the drift-implicit scheme with multiplicative noise** (lines 1893–1902, p. 44: "SDEs such
as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift and/or the volatility.
This again leads to numerical instability if a uniform timestep is used. … Other approaches to
these problems include the use of drift-implicit methods (Dereich, Neuenkirch and Szpruch 2012,
Higham, Mao and Stuart 2002)").  `MlmcLean/DriftImplicit.lean` treats additive noise.  Here the
noise is multiplicative, `X_{n+1} = X_n + h a(X_{n+1}) + b(X_n)√h Z_n` (`implicitPathMult`), with a
continuous, one-sided Lipschitz drift pointing towards `0` (`y a(y) ≤ 0`) and a volatility of
linear growth, `b(x)² ≤ c(1 + x²)`.
* `implicitPathMult_second_moment_le`: `X_N ∈ L²` and
  `E X_N² ≤ (x₀² + 1)(1 + ch)^N − 1 ≤ (x₀² + 1) e^{cNh} − 1`, from
  `|X_{n+1}| ≤ |X_n + b(X_n)√h Z_n|` (`abs_implicitStep_le`) and the independence of `X_n` and
  `Z_n` (`integral_add_mul_mul_sq`).
* `implicitPathMult_second_moment_le_uniform`: hence `E X_N² ≤ (x₀² + 1) e^{cT} − 1` for `h = T/N`
  and every `N`; for the paper's cubic drift with the noise `σS dW`:
  `implicitCubicMult_second_moment_le`.
* `implicitPathMult_second_moment_sharp`: the first bound is attained for the zero drift and
  `b(x) = √(c(1 + x²))`.

**§5.3: the antithetic Brownian path is continuous** (lines 1805–1809, p. 42: "`ω^a_i` is an
antithetic counterpart defined by a time-reversal of the Brownian path within each coarse
timestep").  `MlmcLean/BrownianPaths.lean` proves that the reversed path `antitheticBM H B` is
pre-Brownian (finite-dimensional laws only).
* `continuous_antitheticBM`: pathwise, `antitheticBM H B` is continuous wherever `B` is, for every
  `H`: on each closed coarse step `[kH, (k+1)H]` it is a reflection of `B` (`antitheticBM_eqOn`,
  which uses that the values agree at the coarse times), and these steps form a locally finite
  closed cover (`locallyFinite_Icc_natCast_mul`, `LocallyFinite.continuous`).
* `isBrownianReal_antitheticBM`: so for a Brownian motion `B` (Mathlib's `IsBrownianReal`:
  pre-Brownian with almost surely continuous paths) and `H ≠ 0`, `antitheticBM H B` is a Brownian
  motion; `iIndepFun_isBrownianReal_antitheticBM` for independent components, and
  `isBrownianReal_reverseFirstStep` for the reversal within the first coarse step only.
* `map_iSup_antitheticBM`: hence payoffs of a continuum of path values have the same law under
  `ω^a` as under `ω` (l. 1813–1814, p. 42: "This treatment has been extended to handle lookback and
  barrier options"): for continuous `F`, `(sup_{t ≤ T} F(t, B^a_t), B^a_T)` has the law of
  `(sup_{t ≤ T} F(t, B_t), B_T)` (`map_iSup_Icc_eq_of_isBrownianReal`: by continuity the supremum
  is one over countably many times, whose joint law is that of any pre-Brownian motion,
  `map_pi_eq_of_isPreBrownianReal`).

**§9.1: several kinks** (lines 2550–2554, p. 58: "In their case, the function `f` was piecewise
linear, not twice differentiable, and so the rate of variance convergence was slightly lower, with
`β = 1.5`. However, this is still sufficiently large to achieve an overall complexity which is
`O(ε⁻²)`").  `MlmcLean/NestedRates.lean` and `MlmcLean/NestedKinkSde.lean` treat one kink.  Here
`f = f₀ + ∑_{i ∈ ι} c_i max(· − k_i, 0)` with finitely many kinks and `f₀′` Lipschitz (every
continuous `f` that is `C^{1,1}` on each closed interval between consecutive kinks has this form,
`c_i` being the jump of `f′` at `k_i`; for a piecewise linear `f`, `f₀` is affine).  With bounded
conditional fourth moments and a small-ball bound for `E_W[g(Z, W)]` at each kink:
* `nested_kinks_variance_rate`: `β = 3/2`;
* `nested_kinks_bias_rate`: `α = 1`;
* `nested_kinks_mlmc_complexity`: cost `O(ε⁻²)`, Theorem 1 with `α = 1`, `β = 3/2`, `γ = 1`.
The corrections are linear in `f` (`nestedDelta_succ_kinks`, `nestedP_kinks`,
`nestedTarget_kinks`), so these follow from the smooth case (`nested_variance_rate`,
`nested_bias_rate`) and the one-kink case (`nested_kink_variance_rate`,
`nested_kink_bias_rate_one`) by the triangle and Cauchy–Schwarz inequalities (`sq_add_sum_le`).
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal

namespace MLMC

/-! ### §5.6: the drift-implicit scheme with multiplicative noise -/

/-- The drift-implicit Euler–Maruyama scheme with multiplicative noise (Giles 2015, §5.6, p. 44,
l. 1901–1902: "the use of drift-implicit methods (Dereich, Neuenkirch and Szpruch 2012, Higham, Mao
and Stuart 2002)") for the SDE `dX_t = a(X_t) dt + b(X_t) dW_t` with timestep `h`, driven by the
normal variables `z = (Z_0, Z_1, …)` (Brownian increments `ΔW_n = √h Z_n`): `X_0 = x₀` and
`X_{n+1} = implicitStep a h (X_n + b(X_n)√h Z_n)`, i.e.
`X_{n+1} = X_n + h a(X_{n+1}) + b(X_n)√h Z_n` whenever the implicit equation is solvable
(`implicitStep_eq`).  The drift is evaluated at the new point, the volatility at the old one.  For
a constant volatility `b ≡ σ` this is `implicitPath` (`implicitPathMult_const`). -/
noncomputable def implicitPathMult (a b : ℝ → ℝ) (h x₀ : ℝ) (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => implicitStep a h (implicitPathMult a b h x₀ z n +
      b (implicitPathMult a b h x₀ z n) * √h * z n)

/-- The drift-implicit path with multiplicative noise at step `n` depends only on
`z_0, …, z_{n−1}` (Giles 2015, §5.6: so `X_n` is independent of the next increment `Z_n`). -/
lemma implicitPathMult_congr (a b : ℝ → ℝ) (h x₀ : ℝ) {z z' : ℕ → ℝ} {n : ℕ}
    (hz : ∀ k < n, z k = z' k) :
    implicitPathMult a b h x₀ z n = implicitPathMult a b h x₀ z' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show implicitStep a h (implicitPathMult a b h x₀ z n +
        b (implicitPathMult a b h x₀ z n) * √h * z n) =
      implicitStep a h (implicitPathMult a b h x₀ z' n +
        b (implicitPathMult a b h x₀ z' n) * √h * z' n)
    rw [ih fun k hk => hz k (by omega), hz n (by omega)]

/-- For a measurable implicit step and a measurable volatility, the drift-implicit path with
multiplicative noise at step `n` is a measurable function of the normal variables (Giles 2015,
§5.6). -/
lemma measurable_implicitPathMult {a b : ℝ → ℝ} {h : ℝ} (hm : Measurable (implicitStep a h))
    (hb : Measurable b) (x₀ : ℝ) (n : ℕ) :
    Measurable fun z : ℕ → ℝ => implicitPathMult a b h x₀ z n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact hm.comp (ih.add (((hb.comp ih).mul measurable_const).mul (measurable_pi_apply n)))

/-- For a constant volatility `b ≡ σ` the scheme with multiplicative noise is the additive-noise
scheme `implicitPath` of `MlmcLean/DriftImplicit.lean` (Giles 2015, §5.6). -/
lemma implicitPathMult_const (a : ℝ → ℝ) (h σ x₀ : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    implicitPathMult a (fun _ => σ) h x₀ z n = implicitPath a h σ x₀ z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show implicitStep a h (implicitPathMult a (fun _ => σ) h x₀ z n + σ * √h * z n) =
      implicitStep a h (implicitPath a h σ x₀ z n + σ * √h * z n)
    rw [ih]

/-- One step of multiplicative noise in mean square (Giles 2015, §5.6): if `X ∈ L²` is independent
of `Y ∼ N(0, 1)`, `b` is measurable and `b(x)² ≤ c(1 + x²)`, then `X + b(X) s Y ∈ L²`,
`E b(X)² ≤ c(1 + E X²)` and `E[(X + b(X) s Y)²] = E X² + s² E b(X)²`: the cross term vanishes
because `X b(X)` is independent of `Y` and `E Y = 0`, and `E[b(X)² Y²] = E b(X)²` because
`E Y² = 1`. -/
lemma integral_add_mul_mul_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {b : ℝ → ℝ} (hb : Measurable b) {c : ℝ}
    (hbc : ∀ x, b x ^ 2 ≤ c * (1 + x ^ 2)) (hX : MemLp X 2 μ)
    (hY : μ.map Y = gaussianReal 0 1) (hXY : IndepFun X Y μ) (s : ℝ) :
    MemLp (fun ω => X ω + b (X ω) * s * Y ω) 2 μ ∧
      ∫ ω, b (X ω) ^ 2 ∂μ ≤ c * (1 + ∫ ω, X ω ^ 2 ∂μ) ∧
      ∫ ω, (X ω + b (X ω) * s * Y ω) ^ 2 ∂μ =
        ∫ ω, X ω ^ 2 ∂μ + s ^ 2 * ∫ ω, b (X ω) ^ 2 ∂μ := by
  have hYm := aemeasurable_of_map_eq_gaussianReal hY
  have hY2 : MemLp Y 2 μ := memLp_of_map_eq_gaussianReal hY 2 ENNReal.ofNat_ne_top
  have hEY : ∫ ω, Y ω ∂μ = 0 := by
    have h1 : ∫ y, y ∂(μ.map Y) = ∫ ω, Y ω ∂μ := integral_map hYm aestronglyMeasurable_id
    rw [← h1, hY, integral_id_gaussianReal]
  have hEY2 : ∫ ω, Y ω ^ 2 ∂μ = 1 := by
    rw [← integral_map hYm (continuous_pow 2).aestronglyMeasurable, hY, integral_sq_gaussian]
  have hBm : AEStronglyMeasurable (fun ω => b (X ω)) μ :=
    (hb.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
  have iX2 : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have iC : Integrable (fun ω => c * (1 + X ω ^ 2)) μ :=
    ((integrable_const (1 : ℝ)).add iX2).const_mul c
  have iB2 : Integrable (fun ω => b (X ω) ^ 2) μ :=
    iC.mono' (hBm.pow 2) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbc (X ω))
  have hBX : ∫ ω, b (X ω) ^ 2 ∂μ ≤ c * (1 + ∫ ω, X ω ^ 2 ∂μ) := by
    have h1 := integral_mono iB2 iC fun ω => hbc (X ω)
    rwa [integral_const_mul, integral_add (integrable_const _) iX2, integral_const,
      probReal_univ, one_smul] at h1
  have hB : MemLp (fun ω => b (X ω)) 2 μ := (memLp_two_iff_integrable_sq hBm).2 iB2
  have hXBY : IndepFun (fun ω => X ω * b (X ω)) Y μ :=
    hXY.comp (measurable_id.mul hb) measurable_id
  have hB2Y2 : IndepFun (fun ω => b (X ω) ^ 2) (fun ω => Y ω ^ 2) μ :=
    hXY.comp (hb.pow_const 2) (measurable_id.pow_const 2)
  have iXB : Integrable (fun ω => X ω * b (X ω)) μ := hX.integrable_mul hB
  have iY : Integrable Y μ := hY2.integrable one_le_two
  have iY2 : Integrable (fun ω => Y ω ^ 2) μ := hY2.integrable_sq
  have iXBY : Integrable (fun ω => X ω * b (X ω) * Y ω) μ := hXBY.integrable_mul iXB iY
  have iB2Y2 : Integrable (fun ω => b (X ω) ^ 2 * Y ω ^ 2) μ := hB2Y2.integrable_mul iB2 iY2
  have e0 : ∫ ω, X ω * b (X ω) * Y ω ∂μ = 0 := by
    rw [hXBY.integral_fun_mul_eq_mul_integral iXB.aestronglyMeasurable
      hYm.aestronglyMeasurable, hEY, mul_zero]
  have e1 : ∫ ω, b (X ω) ^ 2 * Y ω ^ 2 ∂μ = ∫ ω, b (X ω) ^ 2 ∂μ := by
    rw [hB2Y2.integral_fun_mul_eq_mul_integral iB2.aestronglyMeasurable
      iY2.aestronglyMeasurable, hEY2, mul_one]
  have hBY2 : MemLp (fun ω => b (X ω) * Y ω) 2 μ := by
    have hm : AEStronglyMeasurable (fun ω => b (X ω) * Y ω) μ :=
      hBm.mul hYm.aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hm).2 (iB2Y2.congr (ae_of_all _ fun ω => ?_))
    ring
  have hsum : MemLp (fun ω => X ω + b (X ω) * s * Y ω) 2 μ := by
    have h1 := hX.add (hBY2.const_mul s)
    convert h1 using 1
    funext ω
    simp only [Pi.add_apply]
    ring
  refine ⟨hsum, hBX, ?_⟩
  have e : (fun ω => (X ω + b (X ω) * s * Y ω) ^ 2) = fun ω =>
      X ω ^ 2 + 2 * s * (X ω * b (X ω) * Y ω) + s ^ 2 * (b (X ω) ^ 2 * Y ω ^ 2) := by
    funext ω
    ring
  have iA : Integrable (fun ω => X ω ^ 2 + 2 * s * (X ω * b (X ω) * Y ω)) μ :=
    iX2.add (iXBY.const_mul _)
  rw [e, integral_add iA (iB2Y2.const_mul _), integral_add iX2 (iXBY.const_mul _),
    integral_const_mul, integral_const_mul, e0, e1]
  ring

/-- **The drift-implicit scheme with multiplicative noise has second moments bounded uniformly in
the timestep** (Giles 2015, §5.6, p. 44, l. 1893–1902: "SDEs such as `dS_t = −S_t³ dt + dW_t`,
which have a super-linear growth in the drift and/or the volatility. This again leads to numerical
instability if a uniform timestep is used. … Other approaches to these problems include the use of
drift-implicit methods (Dereich, Neuenkirch and Szpruch 2012, Higham, Mao and Stuart 2002)").  The
survey states no theorem; this is the moment bound behind the remedy, for multiplicative noise
(`implicitPath_moments_le` treats additive noise).  Let `a` be continuous, one-sided Lipschitz with
constant `K` and pointing towards `0` (`y a(y) ≤ 0`; e.g. `a(y) = −y³`, `K = 0`), `h ≥ 0` with
`hK < 1`, `b` measurable with `b(x)² ≤ c(1 + x²)` for all `x`, and `Z_0, …, Z_{N−1}` independent
with law `N(0, 1)`.  Then the scheme `X_{n+1} = X_n + h a(X_{n+1}) + b(X_n)√h Z_n`, `X_0 = x₀`
(`implicitPathMult`), is square integrable and
`E X_N² ≤ (x₀² + 1)(1 + ch)^N − 1 ≤ (x₀² + 1) e^{cNh} − 1`,
so `E X_N² ≤ (x₀² + 1) e^{cT} − 1` whenever `Nh ≤ T`, whatever the timestep
(`implicitPathMult_second_moment_le_uniform`).  The first bound is attained for the zero drift and
`b(x) = √(c(1 + x²))` (`implicitPathMult_second_moment_sharp`).  Proof: `|X_{n+1}| ≤
|X_n + b(X_n)√h Z_n|` (`abs_implicitStep_le`) and `X_n` is independent of `Z_n`, so
`E X_{n+1}² ≤ E X_n² + h E b(X_n)² ≤ E X_n² + ch(1 + E X_n²)` (`integral_add_mul_mul_sq`).
Deviations: a volatility of super-linear growth, which the quotation also mentions, is not covered
(`b(x)² ≤ c(1 + x²)` is a linear growth bound; `c ≥ 0` follows from it at `x = 0`).  As in
`implicitPath_moments_le`, the one-sided Lipschitz condition is used only for the uniqueness and
the measurability of the step (`continuous_implicitStep`).  The strong convergence of the scheme
needs Itô calculus and is not formalised.  Neither the measurability of the `Z_n` nor that `μ` is a
probability measure is assumed: both follow from the laws and the independence. -/
theorem implicitPathMult_second_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a b : ℝ → ℝ} {K h c : ℝ} (ha : Continuous a)
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hdiss : ∀ y, y * a y ≤ 0)
    (hh : 0 ≤ h) (hhK : h * K < 1) (hb : Measurable b) (hbc : ∀ x, b x ^ 2 ≤ c * (1 + x ^ 2))
    (x₀ : ℝ) {N : ℕ} (Z : ℕ → Ω → ℝ) (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    MemLp (fun ω => implicitPathMult a b h x₀ (fun n => Z n ω) N) 2 μ ∧
      ∫ ω, implicitPathMult a b h x₀ (fun n => Z n ω) N ^ 2 ∂μ ≤
        (x₀ ^ 2 + 1) * (1 + c * h) ^ N - 1 ∧
      ∫ ω, implicitPathMult a b h x₀ (fun n => Z n ω) N ^ 2 ∂μ ≤
        (x₀ ^ 2 + 1) * Real.exp (c * (N * h)) - 1 := by
  have hprob : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hm : ∀ n < N, AEMeasurable (Z n) μ := fun n hn =>
    aemeasurable_of_map_eq_gaussianReal (hZ n hn)
  have hcont := continuous_implicitStep ha hK hh hhK
  have hstep : ∀ r, |implicitStep a h r| ≤ |r| := abs_implicitStep_le ha hdiss hh
  have hc : 0 ≤ c := by
    have h0 := hbc 0
    nlinarith [sq_nonneg (b 0)]
  have hch : 0 ≤ 1 + c * h := by positivity
  have key : ∀ n ≤ N, MemLp (fun ω => implicitPathMult a b h x₀ (fun k => Z k ω) n) 2 μ ∧
      ∫ ω, implicitPathMult a b h x₀ (fun k => Z k ω) n ^ 2 ∂μ + 1 ≤
        (x₀ ^ 2 + 1) * (1 + c * h) ^ n := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨memLp_const x₀, ?_⟩
      simp [implicitPathMult]
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      obtain ⟨hX2, hXb⟩ := ih hn'.le
      set X := fun ω => implicitPathMult a b h x₀ (fun k => Z k ω) n with hXdef
      have hXZ : IndepFun X (Z n) μ :=
        indepFun_of_forall_lt hn' (measurable_implicitPathMult hcont.measurable hb x₀ n)
          (fun z z' hz => implicitPathMult_congr a b h x₀ hz) hm hind
      obtain ⟨hY2, hBX, hE⟩ := integral_add_mul_mul_sq hb hbc hX2 (hZ n hn') hXZ (√h)
      have hle : ∀ ω, |implicitPathMult a b h x₀ (fun k => Z k ω) (n + 1)| ≤
          |X ω + b (X ω) * √h * Z n ω| := fun ω => hstep _
      have hXm : AEStronglyMeasurable
          (fun ω => implicitPathMult a b h x₀ (fun k => Z k ω) (n + 1)) μ :=
        hcont.comp_aestronglyMeasurable hY2.aestronglyMeasurable
      have hX2n : MemLp (fun ω => implicitPathMult a b h x₀ (fun k => Z k ω) (n + 1)) 2 μ :=
        hY2.of_le hXm (ae_of_all _ fun ω => by simp only [Real.norm_eq_abs]; exact hle ω)
      have b2 : ∫ ω, implicitPathMult a b h x₀ (fun k => Z k ω) (n + 1) ^ 2 ∂μ ≤
          ∫ ω, (X ω + b (X ω) * √h * Z n ω) ^ 2 ∂μ :=
        integral_mono hX2n.integrable_sq hY2.integrable_sq fun ω => sq_le_sq.mpr (hle ω)
      rw [hE, Real.sq_sqrt hh] at b2
      refine ⟨hX2n, ?_⟩
      have hXb' : ∫ ω, X ω ^ 2 ∂μ + 1 ≤ (x₀ ^ 2 + 1) * (1 + c * h) ^ n := hXb
      have h1 : h * ∫ ω, b (X ω) ^ 2 ∂μ ≤ h * (c * (1 + ∫ ω, X ω ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hBX hh
      have h2 := mul_le_mul_of_nonneg_left hXb' hch
      rw [pow_succ (1 + c * h) n]
      nlinarith
  obtain ⟨hmem, hbd⟩ := key N le_rfl
  have hexp : (1 + c * h) ^ N ≤ Real.exp (c * (N * h)) := by
    rw [show c * (N * h) = N * (c * h) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ hch (by linarith [Real.add_one_le_exp (c * h)]) N
  have hx : 0 ≤ x₀ ^ 2 + 1 := by positivity
  refine ⟨hmem, by linarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hexp hx]

/-- For the zero drift the implicit step is the identity, `implicitStep 0 h r = r` (Giles 2015,
§5.6: the equation `y = r + h · 0` has the unique solution `r`). -/
lemma implicitStep_zero (h r : ℝ) : implicitStep (fun _ => 0) h r = r := by
  have := implicitStep_eq_of_exists (a := fun _ => 0) (h := h) (r := r) ⟨r, by simp⟩
  rw [this, mul_zero, add_zero]

/-- **The second-moment bound for multiplicative noise is sharp** (Giles 2015, §5.6, p. 44,
l. 1901–1902: "the use of drift-implicit methods").  The zero drift is continuous, non-increasing
and points towards `0`, so it satisfies the hypotheses of `implicitPathMult_second_moment_le` with
`K = 0`; take the volatility `b(x) = √(c(1 + x²))`, `c ≥ 0`, for which `b(x)² = c(1 + x²)`.  For
`h ≥ 0` and independent `Z_0, …, Z_{N−1}` with law `N(0, 1)` the scheme (here the Euler–Maruyama
scheme for `dX = b(X) dW`) satisfies `E X_N² = (x₀² + 1)(1 + ch)^N − 1`: the bound of
`implicitPathMult_second_moment_le` holds with equality, so it cannot be improved under its
hypotheses.  Proof: `E X_{n+1}² = E X_n² + h E b(X_n)² = E X_n² + ch(1 + E X_n²)`
(`integral_add_mul_mul_sq`). -/
theorem implicitPathMult_second_moment_sharp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {h c : ℝ} (hh : 0 ≤ h) (hc : 0 ≤ c) (x₀ : ℝ) {N : ℕ} (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    ∫ ω, implicitPathMult (fun _ => 0) (fun x => √(c * (1 + x ^ 2))) h x₀
        (fun n => Z n ω) N ^ 2 ∂μ = (x₀ ^ 2 + 1) * (1 + c * h) ^ N - 1 := by
  have hprob : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hm : ∀ n < N, AEMeasurable (Z n) μ := fun n hn =>
    aemeasurable_of_map_eq_gaussianReal (hZ n hn)
  set b : ℝ → ℝ := fun x => √(c * (1 + x ^ 2)) with hbdef
  have hb2 : ∀ x, b x ^ 2 = c * (1 + x ^ 2) := fun x => Real.sq_sqrt (by positivity)
  have hb : Measurable b := by fun_prop
  have hcont : Continuous (implicitStep (fun _ : ℝ => (0 : ℝ)) h) := by
    have e : implicitStep (fun _ : ℝ => (0 : ℝ)) h = id := funext (implicitStep_zero h)
    rw [e]
    exact continuous_id
  have key : ∀ n ≤ N, MemLp (fun ω => implicitPathMult (fun _ => 0) b h x₀ (fun k => Z k ω) n)
      2 μ ∧ ∫ ω, implicitPathMult (fun _ => 0) b h x₀ (fun k => Z k ω) n ^ 2 ∂μ + 1 =
        (x₀ ^ 2 + 1) * (1 + c * h) ^ n := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨memLp_const x₀, ?_⟩
      simp [implicitPathMult]
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      obtain ⟨hX2, hXb⟩ := ih hn'.le
      have hXb' : ∫ ω, implicitPathMult (fun _ => 0) b h x₀ (fun k => Z k ω) n ^ 2 ∂μ =
          (x₀ ^ 2 + 1) * (1 + c * h) ^ n - 1 := by linarith
      have hXZ : IndepFun (fun ω => implicitPathMult (fun _ => 0) b h x₀ (fun k => Z k ω) n)
          (Z n) μ :=
        indepFun_of_forall_lt hn' (measurable_implicitPathMult hcont.measurable hb x₀ n)
          (fun z z' hz => implicitPathMult_congr _ b h x₀ hz) hm hind
      obtain ⟨hY2, -, hE⟩ := integral_add_mul_mul_sq hb (fun x => (hb2 x).le) hX2 (hZ n hn')
        hXZ (√h)
      have e : ∀ ω, implicitPathMult (fun _ => 0) b h x₀ (fun k => Z k ω) (n + 1) =
          implicitPathMult (fun _ => 0) b h x₀ (fun k => Z k ω) n +
            b (implicitPathMult (fun _ => 0) b h x₀ (fun k => Z k ω) n) * √h * Z n ω :=
        fun ω => implicitStep_zero h _
      have hB : ∫ ω, b (implicitPathMult (fun _ => 0) b h x₀ (fun k => Z k ω) n) ^ 2 ∂μ =
          c * (1 + ∫ ω, implicitPathMult (fun _ => 0) b h x₀ (fun k => Z k ω) n ^ 2 ∂μ) := by
        simp only [hb2]
        rw [integral_const_mul, integral_add (integrable_const _) hX2.integrable_sq,
          integral_const, probReal_univ, one_smul]
      simp_rw [e]
      refine ⟨hY2, ?_⟩
      rw [hE, hB, Real.sq_sqrt hh, hXb', pow_succ (1 + c * h) n]
      ring
  have := (key N le_rfl).2
  linarith

/-- **Moments bounded uniformly in the number of steps** (Giles 2015, §5.6, p. 44, l. 1893–1902:
"This again leads to numerical instability if a uniform timestep is used. … Other approaches to
these problems include the use of drift-implicit methods").  Under the hypotheses of
`implicitPathMult_second_moment_le`, with `T ≥ 0`, `TK < 1` (every `T` for a non-increasing drift,
`K = 0`) and the timestep `h = T/N`, the scheme is square integrable and
`E X_N² ≤ (x₀² + 1) e^{cT} − 1` for every number of steps `N`.  (`TK < 1` makes the implicit step
well defined for the largest timestep `h = T`, `N = 1`.) -/
theorem implicitPathMult_second_moment_le_uniform {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {a b : ℝ → ℝ} {K c T : ℝ} (ha : Continuous a)
    (hK : ∀ x y, (a x - a y) * (x - y) ≤ K * (x - y) ^ 2) (hdiss : ∀ y, y * a y ≤ 0)
    (hT : 0 ≤ T) (hTK : T * K < 1) (hb : Measurable b) (hbc : ∀ x, b x ^ 2 ≤ c * (1 + x ^ 2))
    (x₀ : ℝ) (N : ℕ) (Z : ℕ → Ω → ℝ) (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    MemLp (fun ω => implicitPathMult a b (T / N) x₀ (fun n => Z n ω) N) 2 μ ∧
      ∫ ω, implicitPathMult a b (T / N) x₀ (fun n => Z n ω) N ^ 2 ∂μ ≤
        (x₀ ^ 2 + 1) * Real.exp (c * T) - 1 := by
  have hh : 0 ≤ T / N := by positivity
  have hNT : (N : ℝ) * (T / N) ≤ T := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [h0, hT]
    · rw [mul_div_cancel₀ _ (by exact_mod_cast h0.ne')]
  have hTN : T / N ≤ T := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [h0, hT]
    · exact div_le_self hT (by exact_mod_cast h0)
  have hhK : T / N * K < 1 := by
    rcases le_or_gt K 0 with hK0 | hK0
    · nlinarith
    · nlinarith
  have hc : 0 ≤ c := by
    have h0 := hbc 0
    nlinarith [sq_nonneg (b 0)]
  obtain ⟨hmem, -, hexp⟩ := implicitPathMult_second_moment_le ha hK hdiss hh hhK hb hbc x₀ Z hZ
    hind
  refine ⟨hmem, hexp.trans ?_⟩
  have h1 : Real.exp (c * (N * (T / N))) ≤ Real.exp (c * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hNT hc)
  have hx : 0 ≤ x₀ ^ 2 + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hx]

/-- **The drift-implicit scheme for `dS = −S³ dt + σS dW`** (Giles 2015, §5.6, p. 44,
l. 1893–1902: "SDEs such as `dS_t = −S_t³ dt + dW_t`, which have a super-linear growth in the drift
and/or the volatility. … Other approaches to these problems include the use of drift-implicit
methods").  The paper's cubic drift with the multiplicative noise `σS dW` in place of the additive
`dW`: for `T ≥ 0`, every number of steps `N` and independent `Z_0, …, Z_{N−1}` with law `N(0, 1)`,
the scheme `X_{n+1} = X_n − h X_{n+1}³ + σ X_n √h Z_n`, `h = T/N` (`implicitPathMult`), is square
integrable and `E X_N² ≤ (x₀² + 1) e^{σ²T} − 1` (`implicitPathMult_second_moment_le_uniform` with
`K = 0` and `c = σ²`).  For the additive noise of the paper the moments of the explicit scheme
diverge (`emCubic_moment_tendsto_atTop`); the explicit scheme for this multiplicative noise is not
treated here. -/
theorem implicitCubicMult_second_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (σ x₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    MemLp (fun ω => implicitPathMult (fun y => -y ^ 3) (fun x => σ * x) (T / N) x₀
      (fun n => Z n ω) N) 2 μ ∧
      ∫ ω, implicitPathMult (fun y => -y ^ 3) (fun x => σ * x) (T / N) x₀
        (fun n => Z n ω) N ^ 2 ∂μ ≤ (x₀ ^ 2 + 1) * Real.exp (σ ^ 2 * T) - 1 :=
  implicitPathMult_second_moment_le_uniform continuous_cubicDrift cubic_oneSidedLipschitz
    cubic_dissipative hT (by simp) (by fun_prop) (fun x => by nlinarith [sq_nonneg σ])
    x₀ N Z hZ hind

/-! ### §5.3: the antithetic Brownian path is continuous -/

section Reversal

variable {Ω : Type*}

/-- On the closed coarse step `[kH, (k+1)H]` the antithetic path is the reflection
`t ↦ B(kH) + B((k+1)H) − B(kH + (k+1)H − t)` (Giles 2015, §5.3, p. 42, l. 1805–1809: "a
time-reversal of the Brownian path within each coarse timestep"), including the right end
`t = (k+1)H`, where the next step starts: there both equal `B((k+1)H)`
(`antitheticBM_natCast_mul`). -/
lemma antitheticBM_eqOn {H : ℝ≥0} (hH : H ≠ 0) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (k : ℕ) :
    Set.EqOn (fun t => antitheticBM H B t ω)
      (fun t => B (k * H) ω + B ((k + 1) * H) ω - B (k * H + (k + 1) * H - t) ω)
      (Set.Icc ((k : ℝ≥0) * H) ((k + 1) * H)) := by
  have hpos : 0 < H := pos_iff_ne_zero.2 hH
  rintro t ⟨ht1, ht2⟩
  rcases ht2.lt_or_eq with ht2 | rfl
  · have hk : ⌊t / H⌋₊ = k := by
      rw [Nat.floor_eq_iff zero_le]
      exact ⟨(le_div_iff₀ hpos).2 ht1, (div_lt_iff₀ hpos).2 ht2⟩
    simp only [antitheticBM, hk]
  · have e := antitheticBM_natCast_mul H B ω (k + 1)
    push_cast at e
    simp only
    rw [e, add_tsub_cancel_right]
    ring

/-- The closed coarse steps `[kH, (k+1)H]`, `k ∈ ℕ`, form a locally finite family for `H ≠ 0`
(Giles 2015, §5.3, the coarse timesteps): the neighbourhood `[0, t + H)` of `t` meets only the
steps with `k < ⌊t/H⌋ + 2`. -/
lemma locallyFinite_Icc_natCast_mul {H : ℝ≥0} (hH : H ≠ 0) :
    LocallyFinite fun k : ℕ => Set.Icc ((k : ℝ≥0) * H) ((k + 1) * H) := by
  have hpos : 0 < H := pos_iff_ne_zero.2 hH
  intro t
  refine ⟨Set.Iio (t + H), Iio_mem_nhds (lt_add_of_pos_right t hpos), ?_⟩
  refine (Set.finite_Iio (⌊t / H⌋₊ + 2)).subset ?_
  rintro k ⟨x, ⟨hx1, -⟩, hx3⟩
  have hx3' : x < t + H := hx3
  have h1 : (k : ℝ≥0) * H < (⌊t / H⌋₊ + 2) * H := by
    calc (k : ℝ≥0) * H ≤ x := hx1
      _ < t + H := hx3'
      _ = t / H * H + H := by rw [div_mul_cancel₀ t hH]
      _ ≤ (⌊t / H⌋₊ + 1) * H + H := by gcongr; exact (Nat.lt_floor_add_one _).le
      _ = (⌊t / H⌋₊ + 2) * H := by ring
  have h2 : (k : ℝ≥0) < ⌊t / H⌋₊ + 2 := lt_of_mul_lt_mul_right h1 zero_le
  show k < ⌊t / H⌋₊ + 2
  exact_mod_cast h2

/-- **The antithetic Brownian path is continuous** (Giles 2015, §5.3, p. 42, l. 1805–1809: "`ω^a_i`
is an antithetic counterpart defined by a time-reversal of the Brownian path within each coarse
timestep").  For every coarse timestep `H` and every `ω` for which `t ↦ B(t, ω)` is continuous,
`t ↦ B^a(t, ω)` (`antitheticBM`) is continuous.  On each closed coarse step `[kH, (k+1)H]` it is the
continuous reflection `B(kH) + B((k+1)H) − B((2k+1)H − t)`, also at the right end `(k+1)H`, where
the reversed path re-attached to the endpoints of the step takes the value `B((k+1)H)` with which
the next step starts (`antitheticBM_eqOn`); these closed steps form a locally finite closed cover
of `[0, ∞)` (`locallyFinite_Icc_natCast_mul`, `LocallyFinite.continuous`).  For `H = 0` the path is
the constant `B(0, ω)` (Lean's `t / 0 = 0`). -/
theorem continuous_antitheticBM (H : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hω : Continuous fun t => B t ω) : Continuous fun t => antitheticBM H B t ω := by
  rcases eq_or_ne H 0 with rfl | hH
  · have e : (fun t => antitheticBM 0 B t ω) = fun _ => B 0 ω := by
      funext t
      simp [antitheticBM]
    rw [e]
    exact continuous_const
  refine (locallyFinite_Icc_natCast_mul hH).continuous ?_ (fun k => isClosed_Icc) fun k => ?_
  · refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 ⟨⌊t / H⌋₊, ?_, ?_⟩
    · calc (⌊t / H⌋₊ : ℝ≥0) * H ≤ t / H * H := mul_le_mul_left (Nat.floor_le (by positivity)) H
        _ = t := div_mul_cancel₀ t hH
    · calc t = t / H * H := (div_mul_cancel₀ t hH).symm
        _ ≤ (⌊t / H⌋₊ + 1) * H := mul_le_mul_left (Nat.lt_floor_add_one _).le H
  · refine (Continuous.continuousOn ?_).congr (antitheticBM_eqOn hH B ω k)
    exact continuous_const.sub (hω.comp (continuous_const.sub continuous_id))

/-- **The antithetic path of a Brownian motion is a Brownian motion** (Giles 2015, §5.3, p. 42,
l. 1799–1809: the antithetic estimator `N_ℓ⁻¹ ∑_i (½(P_ℓ(ω_i) + P_ℓ(ω^a_i)) − P_{ℓ−1}(ω_i))`,
where "`ω^a_i` is an antithetic counterpart defined by a time-reversal of the Brownian path within
each coarse timestep").  If `B` is a Brownian motion (Mathlib's `IsBrownianReal`: a pre-Brownian
motion with almost surely continuous paths) and the coarse timestep is `H > 0`, then the reversed
path `antitheticBM H B` is again a Brownian motion: it is pre-Brownian
(`isPreBrownianReal_antitheticBM`, which gives the finite-dimensional laws only) and its paths are
continuous wherever those of `B` are (`continuous_antitheticBM`): the reflected path is continuous
at the coarse times because the values match there. -/
theorem isBrownianReal_antitheticBM [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {H : ℝ≥0} (hH : H ≠ 0) :
    IsBrownianReal (antitheticBM H B) P :=
  ⟨isPreBrownianReal_antitheticBM hB.toIsPreBrownianReal hH,
    hB.cont.mono fun ω hω => continuous_antitheticBM H B ω hω⟩

/-- **The antithetic path of a multi-dimensional Brownian motion** (Giles 2015, §5.3, pp. 39 and
42, l. 1728–1735 and 1799–1809: for "multi-dimensional SDEs which do not satisfy the commutativity
condition", the antithetic treatment uses "a time-reversal of the Brownian path within each coarse
timestep").  If the components `B_i` (`i ∈ ι`, any index type) are Brownian motions that are
independent as processes, then for `H > 0` the reversed components `antitheticBM H B_i` are again
independent Brownian motions (`isBrownianReal_antitheticBM`, `iIndepFun_antitheticBM`).  Correlated
Brownian components are not treated. -/
theorem iIndepFun_isBrownianReal_antitheticBM [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) {H : ℝ≥0} (hH : H ≠ 0) :
    (∀ i, IsBrownianReal (antitheticBM H (B i)) P) ∧
      iIndepFun (fun i ω t => antitheticBM H (B i) t ω) P :=
  ⟨fun i => isBrownianReal_antitheticBM (hB i) hH,
    (iIndepFun_antitheticBM (fun i => (hB i).toIsPreBrownianReal) hind hH).2⟩

/-- The reversal within the first coarse step only, `B^a(t) = B(H) − B(H − t)` for `t ≤ H` and
`B^a(t) = B(t)` for `t > H` (`reverseFirstStep`; Giles 2015, §5.3), is continuous when `t ↦ B(t, ω)`
is continuous and `B(0, ω) = 0`: at `t = H` both formulas give `B(H, ω)`. -/
lemma continuous_reverseFirstStep (H : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hω : Continuous fun t => B t ω) (h0 : B 0 ω = 0) :
    Continuous fun t => reverseFirstStep H B t ω := by
  refine Continuous.if_le (continuous_const.sub (hω.comp (continuous_const.sub continuous_id)))
    hω continuous_id continuous_const fun t ht => ?_
  simp only [ht, tsub_self, h0, sub_zero]

/-- **Reversing a Brownian motion within the first coarse step gives a Brownian motion** (Giles
2015, §5.3, p. 42, l. 1805–1809: "a time-reversal of the Brownian path within each coarse
timestep").  If `B` is a Brownian motion, so is `reverseFirstStep H B` for every `H ≥ 0`: it is
pre-Brownian (`isPreBrownianReal_reverseFirstStep`), and its paths are continuous wherever those of
`B` are continuous with `B(0) = 0` (`continuous_reverseFirstStep`), which holds almost surely. -/
theorem isBrownianReal_reverseFirstStep [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (H : ℝ≥0) :
    IsBrownianReal (reverseFirstStep H B) P :=
  ⟨isPreBrownianReal_reverseFirstStep hB.toIsPreBrownianReal H, by
    filter_upwards [hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω h0
    exact continuous_reverseFirstStep H B ω hω h0⟩

end Reversal

/-! ### §5.3: running maxima of the antithetic path -/

section RunningMax

/-- **A pre-Brownian motion has the same law at countably many times as any other** (Giles 2015,
§5.3, p. 42, l. 1805–1809: the antithetic path `ω^a` must have the law of the original path `ω`).
For pre-Brownian motions `X` on `(Ω, P)` and `Y` on `(Ω', P')` and times `τ_i`, `i ∈ ι` with `ι`
countable, the random sequences `(X(τ_i))_i` and `(Y(τ_i))_i` have the same law on `ℝ^ι`: their
finite-dimensional laws are images of Mathlib's `projectiveFamily`, and a measure on `ℝ^ι` is
determined by them (`IsProjectiveLimit.unique`).  (Countability makes the sequences a.e.
measurable; `IsPreBrownianReal` only gives each `X(t)` a.e. measurable.) -/
lemma map_pi_eq_of_isPreBrownianReal {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ι : Type*} [Countable ι] (τ : ι → ℝ≥0)
    {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ} (hX : IsPreBrownianReal X P)
    (hY : IsPreBrownianReal Y P') :
    P.map (fun ω i => X (τ i) ω) = P'.map (fun ω i => Y (τ i) ω) := by
  classical
  have hP : IsProbabilityMeasure P := hX.isGaussianProcess.isProbabilityMeasure
  have hXm : AEMeasurable (fun ω i => X (τ i) ω) P :=
    aemeasurable_pi_lambda _ fun i => hX.aemeasurable (τ i)
  have hYm : AEMeasurable (fun ω i => Y (τ i) ω) P' :=
    aemeasurable_pi_lambda _ fun i => hY.aemeasurable (τ i)
  have hfd : ∀ J : Finset ι, (P'.map (fun ω i => Y (τ i) ω)).map J.restrict =
      (P.map (fun ω i => X (τ i) ω)).map J.restrict := by
    intro J
    let I : Finset ℝ≥0 := J.image τ
    let r : (I → ℝ) → (J → ℝ) := fun x j => x ⟨τ j, Finset.mem_image_of_mem τ j.2⟩
    have hr : Measurable r := measurable_pi_lambda _ fun j => measurable_pi_apply _
    have hJ : Measurable (J.restrict : (ι → ℝ) → (J → ℝ)) := Finset.measurable_restrict J
    rw [AEMeasurable.map_map_of_aemeasurable hJ.aemeasurable hXm,
      AEMeasurable.map_map_of_aemeasurable hJ.aemeasurable hYm]
    have eX : (J.restrict ∘ fun ω i => X (τ i) ω) = r ∘ fun ω => I.restrict (X · ω) := rfl
    have eY : (J.restrict ∘ fun ω i => Y (τ i) ω) = r ∘ fun ω => I.restrict (Y · ω) := rfl
    rw [eX, eY,
      ← AEMeasurable.map_map_of_aemeasurable hr.aemeasurable (hX.hasLaw I).aemeasurable,
      ← AEMeasurable.map_map_of_aemeasurable hr.aemeasurable (hY.hasLaw I).aemeasurable,
      (hX.hasLaw I).map_eq, (hY.hasLaw I).map_eq]
  have hμ : IsProjectiveLimit (P.map (fun ω i => X (τ i) ω))
      (fun J => (P.map (fun ω i => X (τ i) ω)).map J.restrict) := fun J => rfl
  exact hμ.unique hfd

/-- For a Brownian motion the running supremum of `F(t, X_t)` over `[0, T]`, `F` continuous, is
almost surely the supremum over any dense subset of `[0, T]` (Giles 2015, §5.3, p. 42, l. 1813–1814:
lookback and barrier payoffs depend on the running maximum; `Dense.ciSup'` for the continuous
path). -/
lemma iSup_Icc_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsBrownianReal X P) {F : ℝ≥0 → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (T : ℝ≥0) {S : Set (Set.Icc (0 : ℝ≥0) T)} (hS : Dense S) :
    (fun ω => ⨆ t : Set.Icc 0 T, F t (X t ω)) =ᵐ[P] fun ω => ⨆ s : S, F s (X s ω) :=
  hX.cont.mono fun ω hω => (hS.ciSup' (f := fun t : Set.Icc 0 T => F t (X t ω))
    (hF.comp (continuous_subtype_val.prodMk (hω.comp continuous_subtype_val)))).symm

/-- **Brownian motions have the same running maxima in law** (Giles 2015, §5.3, p. 42, l. 1813–1814:
"This treatment has been extended to handle lookback and barrier options (Giles and Szpruch
2013)"; lookback and barrier payoffs depend on a continuum of path values).  Let `X` on `(Ω, P)`
and `Y` on `(Ω', P')` be Brownian motions (`IsBrownianReal`), `F : ℝ≥0 × ℝ → ℝ` continuous and
`T ≥ 0`.  Then `(sup_{t ≤ T} F(t, X_t), X_T)` is a random variable (a.e. measurable) with the same
law as `(sup_{t ≤ T} F(t, Y_t), Y_T)`.  For geometric Brownian motion `S_t = F(t, W_t)` with
`F(t, w) = s₀ e^{(r − σ²/2)t + σw}` this is the joint law of `(max_{t ≤ T} S_t, S_T)`, on which
lookback payoffs and barrier events depend (the minimum is the case `−F`).  Proof: by path
continuity both suprema are a.s. suprema over a countable dense set (`iSup_Icc_ae_eq`), hence
measurable functions of countably many path values, whose joint law is the same for all
pre-Brownian motions (`map_pi_eq_of_isPreBrownianReal`). -/
theorem map_iSup_Icc_eq_of_isBrownianReal {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} {X : ℝ≥0 → Ω → ℝ}
    {Y : ℝ≥0 → Ω' → ℝ} (hX : IsBrownianReal X P) (hY : IsBrownianReal Y P')
    {F : ℝ≥0 → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) (T : ℝ≥0) :
    AEMeasurable (fun ω => (⨆ t : Set.Icc 0 T, F t (X t ω), X T ω)) P ∧
      P.map (fun ω => (⨆ t : Set.Icc 0 T, F t (X t ω), X T ω)) =
        P'.map (fun ω => (⨆ t : Set.Icc 0 T, F t (Y t ω), Y T ω)) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ≥0) T)
  have : Countable S := hSc.to_subtype
  let τ : Option S → ℝ≥0 := fun o => Option.elim o T fun s => s.1.1
  let Φ : (Option S → ℝ) → ℝ × ℝ := fun x => (⨆ s : S, F s (x (some s)), x none)
  have hFs : ∀ s : ℝ≥0, Continuous (F s) := fun s =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hΦ : Measurable Φ :=
    (Measurable.iSup fun s => (hFs _).measurable.comp (measurable_pi_apply (some s))).prodMk
      (measurable_pi_apply none)
  have hXm : AEMeasurable (fun ω o => X (τ o) ω) P :=
    aemeasurable_pi_lambda _ fun o => hX.toIsPreBrownianReal.aemeasurable (τ o)
  have hYm : AEMeasurable (fun ω o => Y (τ o) ω) P' :=
    aemeasurable_pi_lambda _ fun o => hY.toIsPreBrownianReal.aemeasurable (τ o)
  have haeX : (fun ω => (⨆ t : Set.Icc 0 T, F t (X t ω), X T ω)) =ᵐ[P]
      Φ ∘ fun ω o => X (τ o) ω := by
    filter_upwards [iSup_Icc_ae_eq hX hF T hSd] with ω hω
    rw [hω]
    rfl
  have haeY : (fun ω => (⨆ t : Set.Icc 0 T, F t (Y t ω), Y T ω)) =ᵐ[P']
      Φ ∘ fun ω o => Y (τ o) ω := by
    filter_upwards [iSup_Icc_ae_eq hY hF T hSd] with ω hω
    rw [hω]
    rfl
  refine ⟨(hΦ.comp_aemeasurable hXm).congr haeX.symm, ?_⟩
  rw [Measure.map_congr haeX, Measure.map_congr haeY,
    ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hXm,
    ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hYm,
    map_pi_eq_of_isPreBrownianReal τ hX.toIsPreBrownianReal hY.toIsPreBrownianReal]

/-- **The antithetic path has the running maxima of the original path in law** (Giles 2015, §5.3,
p. 42, l. 1805–1814: "`ω^a_i` is an antithetic counterpart defined by a time-reversal of the
Brownian path within each coarse timestep. … This treatment has been extended to handle lookback
and barrier options (Giles and Szpruch 2013)").  For a Brownian motion `B`, a coarse timestep
`H > 0`, a continuous `F : ℝ≥0 × ℝ → ℝ` and `T ≥ 0`, the pair
`(sup_{t ≤ T} F(t, B^a_t), B^a_T)` for the antithetic path `B^a = antitheticBM H B` is a random
variable with the law of `(sup_{t ≤ T} F(t, B_t), B_T)` (`isBrownianReal_antitheticBM`,
`map_iSup_Icc_eq_of_isBrownianReal`): lookback and barrier payoffs of the exact path have the same
law under `ω^a` as under `ω`.  The paper applies these payoffs to discretised paths (with
Brownian-bridge interpolation within each step); Giles and Szpruch's analysis is not formalised. -/
theorem map_iSup_antitheticBM {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {H : ℝ≥0} (hH : H ≠ 0) {F : ℝ≥0 → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (T : ℝ≥0) :
    AEMeasurable (fun ω => (⨆ t : Set.Icc 0 T, F t (antitheticBM H B t ω),
      antitheticBM H B T ω)) P ∧
      P.map (fun ω => (⨆ t : Set.Icc 0 T, F t (antitheticBM H B t ω), antitheticBM H B T ω)) =
        P.map (fun ω => (⨆ t : Set.Icc 0 T, F t (B t ω), B T ω)) :=
  map_iSup_Icc_eq_of_isBrownianReal (isBrownianReal_antitheticBM hB hH) hB hF T

end RunningMax

/-! ### §9.1: nested simulation with several kinks -/

/-- The Cauchy–Schwarz inequality `(a + ∑_{i ∈ ι} b_i)² ≤ (|ι| + 1)(a² + ∑_i b_i²)` over a finite
index type (Giles 2015, §9.1: the correction for an `f` with several kinks is the sum of the
correction for the smooth part and one correction per kink). -/
lemma sq_add_sum_le {ι : Type*} [Fintype ι] (a : ℝ) (b : ι → ℝ) :
    (a + ∑ i, b i) ^ 2 ≤ (Fintype.card ι + 1) * (a ^ 2 + ∑ i, b i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Option ι))
    (fun o => Option.elim o a b) (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_option,
    nsmul_eq_mul, Fintype.sum_option, Option.elim] at h
  push_cast at h
  linarith

section Kinks

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲]

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
/-- **The antithetic correction is linear in `f`** (Giles 2015, §9.1, p. 57): if
`f = f₀ + ∑_i c_i max(· − k_i, 0)`, then
`Y_{ℓ+1}(f) = Y_{ℓ+1}(f₀) + ∑_i c_i Y_{ℓ+1}(max(· − k_i, 0))` pointwise (`nestedDelta`). -/
lemma nestedDelta_succ_kinks {ι : Type*} [Fintype ι] {f f₀ : ℝ → ℝ} {c k : ι → ℝ}
    (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0) (g : 𝒵 → 𝒲 → ℝ) (ℓ : ℕ)
    (p : 𝒵 × (ℕ → 𝒲)) :
    nestedDelta f g (ℓ + 1) p = nestedDelta f₀ g (ℓ + 1) p +
      ∑ i, c i * nestedDelta (fun x => max (x - k i) 0) g (ℓ + 1) p := by
  set A := innerMean g (2 ^ (ℓ + 1)) p.1 p.2
  set B := innerMean g (2 ^ ℓ) p.1 p.2
  set C := innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)
  have e : ∀ F : ℝ → ℝ, nestedDelta F g (ℓ + 1) p = F A - F B / 2 - F C / 2 := fun F => rfl
  have h1 : ∑ i, c i * (max (A - k i) 0 - max (B - k i) 0 / 2 - max (C - k i) 0 / 2) =
      ∑ i, c i * max (A - k i) 0 - (∑ i, c i * max (B - k i) 0) / 2 -
        (∑ i, c i * max (C - k i) 0) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, e, hf A, hf B, hf C]
  simp only [e]
  rw [h1]
  ring

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
/-- The level approximation `P_ℓ = f(A_{2^ℓ})` is linear in `f` (Giles 2015, §9.1): for
`f = f₀ + ∑_i c_i max(· − k_i, 0)`, `P_ℓ(f) = P_ℓ(f₀) + ∑_i c_i P_ℓ(max(· − k_i, 0))`. -/
lemma nestedP_kinks {ι : Type*} [Fintype ι] {f f₀ : ℝ → ℝ} {c k : ι → ℝ}
    (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0) (g : 𝒵 → 𝒲 → ℝ) (ℓ : ℕ)
    (p : 𝒵 × (ℕ → 𝒲)) :
    nestedP f g ℓ p = nestedP f₀ g ℓ p + ∑ i, c i * nestedP (fun x => max (x - k i) 0) g ℓ p :=
  hf _

omit [MeasurableSpace 𝒵] in
/-- The quantity of interest `f(E_W[g(z, W)])` is linear in `f` (Giles 2015, §9.1): for
`f = f₀ + ∑_i c_i max(· − k_i, 0)` it is the corresponding combination for `f₀` and the hinges. -/
lemma nestedTarget_kinks {ι : Type*} [Fintype ι] {f f₀ : ℝ → ℝ} {c k : ι → ℝ}
    (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0) (g : 𝒵 → 𝒲 → ℝ) (ρ : Measure 𝒲)
    (p : 𝒵 × (ℕ → 𝒲)) :
    nestedTarget f g ρ p = nestedTarget f₀ g ρ p +
      ∑ i, c i * nestedTarget (fun x => max (x - k i) 0) g ρ p :=
  hf _

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
/-- `f = f₀ + ∑_i c_i max(· − k_i, 0)` with `f₀` differentiable is continuous (Giles 2015, §9.1:
"the function `f` was piecewise linear"). -/
lemma continuous_kinks {ι : Type*} [Fintype ι] {f f₀ f₀' : ℝ → ℝ} {c k : ι → ℝ}
    (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0)
    (hf₀ : ∀ x, HasDerivAt f₀ (f₀' x) x) : Continuous f := by
  have e : f = fun x => f₀ x + ∑ i, c i * max (x - k i) 0 := funext hf
  have h0 : Continuous f₀ := continuous_iff_continuousAt.2 fun x => (hf₀ x).continuousAt
  rw [e]
  fun_prop

variable (ν : Measure 𝒵) [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- Bounded conditional fourth moments bound the joint one (Giles 2015, §9.1): if
`E_W[g(z, W)⁴] ≤ m₄` for `ν`-a.e. `z`, then `E[g(Z, W)⁴] ≤ m₄` (Fubini). -/
lemma integral_pow_four_le_of_fiber {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g))
    {m₄ : ℝ} (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧ ∫ v, g z v ^ 4 ∂ρ ≤ m₄) :
    ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄ := by
  have hg4 := integrable_pow_four_of_fiber ν ρ hg hfib
  rw [integral_prod _ hg4]
  calc ∫ z, ∫ v, g z v ^ 4 ∂ρ ∂ν ≤ ∫ _z, m₄ ∂ν :=
        integral_mono_ae hg4.integral_prod_left (integrable_const _) (hfib.mono fun z hz => hz.2)
    _ = m₄ := by simp

/-- The level approximations and the quantity of interest are square integrable for an `f` with
several kinks (Giles 2015, §9.1): for `f = f₀ + ∑_i c_i max(· − k_i, 0)` with `f₀′` Lipschitz and
`E[g(Z, W)⁴] < ∞`, `P_ℓ = f(A_{2^ℓ})` and `f(E_W[g(Z, W)])` are in `L²` (`memLp_nestedP`,
`memLp_nestedTarget` for the smooth part, `memLp_two_kink_comp` for the hinges). -/
lemma memLp_nestedP_kinks {ι : Type*} [Fintype ι] {f f₀ f₀' : ℝ → ℝ} {K : ℝ} {c k : ι → ℝ}
    (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0)
    (hf₀ : ∀ x, HasDerivAt f₀ (f₀' x) x) (hf₀' : ∀ x y, x ≤ y → |f₀' y - f₀' x| ≤ K * (y - x))
    {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) :
    (∀ ℓ, MemLp (nestedP f g ℓ) 2 (nestedLaw ν ρ)) ∧
      MemLp (nestedTarget f g ρ) 2 (nestedLaw ν ρ) := by
  obtain ⟨hGm, hG4⟩ := integrable_condMean_pow_four ν ρ hg hg4
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hhinge : ∀ i, ∀ x, (fun x => max (x - k i) 0) x = 0 + 0 * x + 1 * max (x - k i) 0 :=
    fun i x => by ring
  constructor
  · intro ℓ
    have hA : Measurable fun p : 𝒵 × (ℕ → 𝒲) => innerMean g (2 ^ ℓ) p.1 p.2 :=
      measurable_innerMean hg _ measurable_id
    have hA2 := integrable_pow_of_pow_four hA
      (integrable_innerMean_pow_four ν ρ hg hg4 (by positivity)) (k := 2) (by norm_num)
    have hi : ∀ i, MemLp (nestedP (fun x => max (x - k i) 0) g ℓ) 2 (nestedLaw ν ρ) := fun i =>
      memLp_two_kink_comp (hhinge i) hA hA2
    have hsum := (memLp_nestedP ν ρ hf₀ hf₀' hg hg4 ℓ).add
      (memLp_finsetSum Finset.univ fun i _ => (hi i).const_mul (c i))
    convert hsum using 1
    funext p
    exact nestedP_kinks hf g ℓ p
  · have hG2 := integrable_pow_of_pow_four hGm hG4 (k := 2) (by norm_num)
    have hi : ∀ i, MemLp (nestedTarget (fun x => max (x - k i) 0) g ρ) 2 (nestedLaw ν ρ) :=
      fun i => (memLp_two_kink_comp (hhinge i) hGm hG2).comp_measurePreserving hfst
    have hsum := (memLp_nestedTarget ν ρ hf₀ hf₀' hg hg4).add
      (memLp_finsetSum Finset.univ fun i _ => (hi i).const_mul (c i))
    convert hsum using 1
    funext p
    exact nestedTarget_kinks hf g ρ p

/-- **`β = 1.5` for an `f` with several kinks** (Giles 2015, §9.1, p. 58, l. 2551–2553: "In their
case, the function `f` was piecewise linear, not twice differentiable, and so the rate of variance
convergence was slightly lower, with `β = 1.5`").  Let `f = f₀ + ∑_{i ∈ ι} c_i max(· − k_i, 0)` with
finitely many kinks `k_i` and `f₀` differentiable with a `K`-Lipschitz derivative (every continuous
`f` that is `C^{1,1}` on each closed interval between consecutive kinks has this form, `c_i` being
the jump of `f′` at `k_i`; a piecewise linear `f` has `f₀` affine and `K = 0`).  Let the
conditional fourth moments be bounded, `E_W[g(z, W)⁴] ≤ m₄` for `ν`-a.e. `z`, and let the
conditional mean put little mass near each kink, `ν{|E_W[g(Z, W)] − k_i| ≤ t} ≤ c_{d,i} t` for all
`t > 0` (true if `E_W[g(Z, W)]` has a bounded density near `k_i`: `small_ball_of_density`).  Then
the §9.1 correction `Y_{ℓ+1}` (`2^ℓ` coarse inner samples) is square integrable and
`2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ (|ι| + 1)((K/8)² 224 m₄ + ∑_i c_i² 2 c_{d,i} √(8 m₄ (1 + 16 m₄)))`,
i.e. `V_ℓ = O(M_ℓ^{−3/2})`.  Proof: `Y_{ℓ+1}` is linear in `f` (`nestedDelta_succ_kinks`), its
smooth part is `O(2^{−2ℓ})` in mean square (`nested_variance_rate`), each hinge part
`O(2^{−3ℓ/2})` (`nested_kink_variance_rate`), and `(a + ∑_i b_i)² ≤ (|ι| + 1)(a² + ∑_i b_i²)`
(`sq_add_sum_le`).
The paper states no hypotheses; as for one kink (`nested_kink_variance_rate`), the small-ball bounds
and the bounded conditional fourth moments are this formalisation's.  Deviation: `f` is given
through the decomposition above rather than as a piecewise `C^{1,1}` function. -/
theorem nested_kinks_variance_rate {ι : Type*} [Fintype ι] {f f₀ f₀' : ℝ → ℝ} {K : ℝ}
    {c k c_d : ι → ℝ} (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0)
    (hf₀ : ∀ x, HasDerivAt f₀ (f₀' x) x) (hf₀' : ∀ x y, x ≤ y → |f₀' y - f₀' x| ≤ K * (y - x))
    {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g)) {m₄ : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧ ∫ v, g z v ^ 4 ∂ρ ≤ m₄)
    (hball : ∀ i, ∀ t : ℝ, 0 < t →
      ν {z | |∫ v, g z v ∂ρ - k i| ≤ t} ≤ ENNReal.ofReal (c_d i * t))
    (ℓ : ℕ) :
    MemLp (nestedDelta f g (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        (Fintype.card ι + 1) * ((K / 8) ^ 2 * (224 * m₄) +
          ∑ i, c i ^ 2 * (2 * c_d i * Real.sqrt (8 * m₄ * (1 + 16 * m₄)))) := by
  have hg4 := integrable_pow_four_of_fiber ν ρ hg hfib
  have hE4 := integral_pow_four_le_of_fiber ν ρ hg hfib
  have hhinge : ∀ i, ∀ x, (fun x => max (x - k i) 0) x = 0 + 0 * x + 1 * max (x - k i) 0 :=
    fun i x => by ring
  obtain ⟨h0m, h0b⟩ := nested_variance_rate ν ρ hf₀ hf₀' hg hg4 ℓ
  have hi := fun i => nested_kink_variance_rate ν ρ (hhinge i) hg hfib (hball i) ℓ
  set Y₀ := nestedDelta f₀ g (ℓ + 1)
  set Y : ι → 𝒵 × (ℕ → 𝒲) → ℝ := fun i => nestedDelta (fun x => max (x - k i) 0) g (ℓ + 1)
  have hY : ∀ p, nestedDelta f g (ℓ + 1) p = Y₀ p + ∑ i, c i * Y i p :=
    nestedDelta_succ_kinks hf g ℓ
  have hmem : MemLp (nestedDelta f g (ℓ + 1)) 2 (nestedLaw ν ρ) := by
    have hsum := h0m.add (memLp_finsetSum Finset.univ fun i _ => (hi i).1.const_mul (c i))
    convert hsum using 1
    funext p
    exact hY p
  refine ⟨hmem, ?_⟩
  -- pointwise Cauchy–Schwarz, integrated
  have i0 : Integrable (fun p => Y₀ p ^ 2) (nestedLaw ν ρ) := h0m.integrable_sq
  have ii : ∀ i, Integrable (fun p => Y i p ^ 2) (nestedLaw ν ρ) := fun i =>
    (hi i).1.integrable_sq
  have iS : Integrable (fun p => ∑ i, c i ^ 2 * Y i p ^ 2) (nestedLaw ν ρ) :=
    integrable_finsetSum _ fun i _ => (ii i).const_mul _
  have iF : Integrable (fun p => (Fintype.card ι + 1 : ℝ) * (Y₀ p ^ 2 +
      ∑ i, c i ^ 2 * Y i p ^ 2)) (nestedLaw ν ρ) := (i0.add iS).const_mul _
  have hpt : ∀ p, nestedDelta f g (ℓ + 1) p ^ 2 ≤
      (Fintype.card ι + 1 : ℝ) * (Y₀ p ^ 2 + ∑ i, c i ^ 2 * Y i p ^ 2) := fun p => by
    rw [hY p]
    have h := sq_add_sum_le (Y₀ p) fun i => c i * Y i p
    simp only [mul_pow] at h
    exact h
  have hint : ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
      (Fintype.card ι + 1 : ℝ) * (∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ) +
        ∑ i, c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ)) := by
    have h := integral_mono hmem.integrable_sq iF hpt
    rw [integral_const_mul, integral_add i0 iS,
      integral_finsetSum _ fun i _ => (ii i).const_mul _] at h
    simpa only [integral_const_mul] using h
  -- the rates of the two parts
  set r : ℝ := (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr4 : r ≤ ((2 : ℝ) ^ ℓ) ^ 2 := by
    rw [hr, ← pow_mul, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hb0 : r * ∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ) ≤ (K / 8) ^ 2 * (224 * m₄) := by
    have hY0 : 0 ≤ ∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ) := integral_nonneg fun p => sq_nonneg _
    calc r * ∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ)
        ≤ ((2 : ℝ) ^ ℓ) ^ 2 * ∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ) :=
          mul_le_mul_of_nonneg_right hr4 hY0
      _ ≤ (K / 8) ^ 2 * (224 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) := h0b
      _ ≤ (K / 8) ^ 2 * (224 * m₄) := by gcongr
  have hbi : ∀ i, r * (c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ)) ≤
      c i ^ 2 * (2 * c_d i * Real.sqrt (8 * m₄ * (1 + 16 * m₄))) := fun i => by
    have h := (hi i).2
    rw [one_pow, mul_one] at h
    calc r * (c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ))
        = c i ^ 2 * (r * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ)) := by ring
      _ ≤ c i ^ 2 * (2 * c_d i * Real.sqrt (8 * m₄ * (1 + 16 * m₄))) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
  have hcard : (0 : ℝ) ≤ Fintype.card ι + 1 := by positivity
  calc r * ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)
      ≤ r * ((Fintype.card ι + 1 : ℝ) * (∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ) +
        ∑ i, c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ))) := mul_le_mul_of_nonneg_left hint hr0
    _ = (Fintype.card ι + 1 : ℝ) * (r * ∫ p, Y₀ p ^ 2 ∂(nestedLaw ν ρ) +
        ∑ i, r * (c i ^ 2 * ∫ p, Y i p ^ 2 ∂(nestedLaw ν ρ))) := by
          rw [← Finset.mul_sum]
          ring
    _ ≤ (Fintype.card ι + 1 : ℝ) * ((K / 8) ^ 2 * (224 * m₄) +
        ∑ i, c i ^ 2 * (2 * c_d i * Real.sqrt (8 * m₄ * (1 + 16 * m₄)))) :=
          mul_le_mul_of_nonneg_left (add_le_add hb0 (Finset.sum_le_sum fun i _ => hbi i)) hcard

/-- **`α = 1` for an `f` with several kinks** (Giles 2015, §9.1, p. 58, l. 2550–2554, the setting
of Bujok et al.: "the function `f` was piecewise linear, not twice differentiable"; the paper does
not state `α` for it).  Under the hypotheses of `nested_kinks_variance_rate`, the bias integrand
`P_ℓ − f(E_W[g(Z, W)])` of the level-`ℓ` approximation `P_ℓ = f(A_{2^ℓ})` is integrable and
`2^ℓ |E[P_ℓ − f(E_W[g(Z, W)])]| ≤ (K/2)(1 + 16 m₄) + ∑_i |c_i| 3 c_{d,i} (1 + 1280 m₄)`.  Proof: the
bias is linear in `f` (`nestedP_kinks`, `nestedTarget_kinks`); the smooth part has bias
`O(2^{−ℓ})` (`nested_bias_rate`), and so has each hinge by its small-ball bound
(`nested_kink_bias_rate_one`, with centred conditional fourth moments `≤ 16 m₄` by
`centred_moments_le`).  (For Theorem 1 with `β = 3/2 > γ = 1`, `α = ½` would suffice.) -/
theorem nested_kinks_bias_rate {ι : Type*} [Fintype ι] {f f₀ f₀' : ℝ → ℝ} {K : ℝ}
    {c k c_d : ι → ℝ} (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0)
    (hf₀ : ∀ x, HasDerivAt f₀ (f₀' x) x) (hf₀' : ∀ x y, x ≤ y → |f₀' y - f₀' x| ≤ K * (y - x))
    {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g)) {m₄ : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧ ∫ v, g z v ^ 4 ∂ρ ≤ m₄)
    (hball : ∀ i, ∀ t : ℝ, 0 < t →
      ν {z | |∫ v, g z v ∂ρ - k i| ≤ t} ≤ ENNReal.ofReal (c_d i * t))
    (ℓ : ℕ) :
    Integrable (fun p => nestedP f g ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, (nestedP f g ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
        K / 2 * (1 + 16 * m₄) + ∑ i, |c i| * (3 * c_d i * (1 + 1280 * m₄)) := by
  have hg4 := integrable_pow_four_of_fiber ν ρ hg hfib
  have hE4 := integral_pow_four_le_of_fiber ν ρ hg hfib
  have hK := lipschitz_const_nonneg hf₀'
  have hhinge : ∀ i, ∀ x, (fun x => max (x - k i) 0) x = 0 + 0 * x + 1 * max (x - k i) 0 :=
    fun i x => by ring
  -- centred conditional fourth moments
  have hfibc : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧
      ∫ v, (g z v - ∫ u, g z u ∂ρ) ^ 4 ∂ρ ≤ 16 * m₄ :=
    hfib.mono fun z hz => ⟨hz.1, (centred_moments_le hg.of_uncurry_left hz.1).2.1.trans
      (by linarith [hz.2])⟩
  have hi := fun i => nested_kink_bias_rate_one ν ρ (hhinge i) hg hfibc (hball i) ℓ
  set D₀ : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => nestedP f₀ g ℓ p - nestedTarget f₀ g ρ p
  set D : ι → 𝒵 × (ℕ → 𝒲) → ℝ := fun i p =>
    nestedP (fun x => max (x - k i) 0) g ℓ p - nestedTarget (fun x => max (x - k i) 0) g ρ p
  have hi' : ∀ i, Integrable (D i) (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ℓ * |∫ p, D i p ∂(nestedLaw ν ρ)| ≤ 3 * c_d i * |1| * (1 + 80 * (16 * m₄)) :=
    hi
  have i0 : Integrable D₀ (nestedLaw ν ρ) :=
    ((memLp_nestedP ν ρ hf₀ hf₀' hg hg4 ℓ).integrable one_le_two).sub
      ((memLp_nestedTarget ν ρ hf₀ hf₀' hg hg4).integrable one_le_two)
  have hD : ∀ p, nestedP f g ℓ p - nestedTarget f g ρ p = D₀ p + ∑ i, c i * D i p := fun p => by
    rw [nestedP_kinks hf g ℓ p, nestedTarget_kinks hf g ρ p]
    simp only [D₀, D, mul_sub, Finset.sum_sub_distrib]
    ring
  have iS : Integrable (fun p => ∑ i, c i * D i p) (nestedLaw ν ρ) :=
    integrable_finsetSum _ fun i _ => (hi' i).1.const_mul _
  have hint : Integrable (fun p => nestedP f g ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) :=
    (i0.add iS).congr (ae_of_all _ fun p => (hD p).symm)
  refine ⟨hint, ?_⟩
  have hsplit : ∫ p, (nestedP f g ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ p, D₀ p ∂(nestedLaw ν ρ) + ∑ i, c i * ∫ p, D i p ∂(nestedLaw ν ρ) := by
    simp_rw [hD]
    rw [integral_add i0 iS, integral_finsetSum _ fun i _ => (hi' i).1.const_mul _]
    simp only [integral_const_mul]
  have hb0 : (2 : ℝ) ^ ℓ * |∫ p, D₀ p ∂(nestedLaw ν ρ)| ≤ K / 2 * (1 + 16 * m₄) := by
    have h := nested_bias_rate ν ρ hf₀ hf₀' hg hg4 ℓ
    have : K / 2 * (1 + 16 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ)) ≤ K / 2 * (1 + 16 * m₄) := by
      gcongr
    exact h.trans this
  have hbi : ∀ i, (2 : ℝ) ^ ℓ * |c i * ∫ p, D i p ∂(nestedLaw ν ρ)| ≤
      |c i| * (3 * c_d i * (1 + 1280 * m₄)) := fun i => by
    have h := (hi' i).2
    rw [abs_one, mul_one, show 1 + 80 * (16 * m₄) = 1 + 1280 * m₄ by ring] at h
    rw [abs_mul]
    calc (2 : ℝ) ^ ℓ * (|c i| * |∫ p, D i p ∂(nestedLaw ν ρ)|)
        = |c i| * ((2 : ℝ) ^ ℓ * |∫ p, D i p ∂(nestedLaw ν ρ)|) := by ring
      _ ≤ |c i| * (3 * c_d i * (1 + 1280 * m₄)) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  rw [hsplit]
  have h2 : (0 : ℝ) ≤ 2 ^ ℓ := by positivity
  calc (2 : ℝ) ^ ℓ * |∫ p, D₀ p ∂(nestedLaw ν ρ) + ∑ i, c i * ∫ p, D i p ∂(nestedLaw ν ρ)|
      ≤ (2 : ℝ) ^ ℓ * (|∫ p, D₀ p ∂(nestedLaw ν ρ)| +
          ∑ i, |c i * ∫ p, D i p ∂(nestedLaw ν ρ)|) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
          (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))) h2
    _ = (2 : ℝ) ^ ℓ * |∫ p, D₀ p ∂(nestedLaw ν ρ)| +
          ∑ i, (2 : ℝ) ^ ℓ * |c i * ∫ p, D i p ∂(nestedLaw ν ρ)| := by
        rw [mul_add, Finset.mul_sum]
    _ ≤ K / 2 * (1 + 16 * m₄) + ∑ i, |c i| * (3 * c_d i * (1 + 1280 * m₄)) :=
        add_le_add hb0 (Finset.sum_le_sum fun i _ => hbi i)

/-- **MLMC for nested simulation with several kinks has complexity `O(ε⁻²)`** (Giles 2015, §9.1,
p. 58, l. 2550–2554: "In their case, the function `f` was piecewise linear, not twice
differentiable, and so the rate of variance convergence was slightly lower, with `β = 1.5`.
However, this is still sufficiently large to achieve an overall complexity which is `O(ε⁻²)`").
Under the hypotheses of `nested_kinks_variance_rate` (`f = f₀ + ∑_i c_i max(· − k_i, 0)` with `f₀′`
Lipschitz, bounded conditional fourth moments, a small-ball bound at each kink), for independent
inputs `ω^{(ℓ,n)}` with law `ν ⊗ ρ^{⊗ℕ}` and level-`ℓ` costs with mean `C_ℓ ≤ c₃ 2^ℓ`
(`M_ℓ = 2^ℓ` inner samples), there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` for which the MLMC estimator `∑_{ℓ ≤ L} N_ℓ⁻¹ ∑_{n < N_ℓ} Y_ℓ(ω^{(ℓ,n)})` of
`E_Z[f(E_W[g(Z, W)])]` has mean square error `< ε²` and expected cost `≤ c₄ ε⁻²`: Theorem 1
(`giles_theorem1_corrections`) with `α = 1` (`nested_kinks_bias_rate`), `β = 3/2`
(`nested_kinks_variance_rate`) and `γ = 1`.  This extends `nested_kink_mlmc_complexity` (one kink,
`f` piecewise linear) to finitely many kinks and curved pieces. -/
theorem nested_kinks_mlmc_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] {f f₀ f₀' : ℝ → ℝ} {K : ℝ}
    {c k c_d : ι → ℝ} (hf : ∀ x, f x = f₀ x + ∑ i, c i * max (x - k i) 0)
    (hf₀ : ∀ x, HasDerivAt f₀ (f₀' x) x) (hf₀' : ∀ x y, x ≤ y → |f₀' y - f₀' x| ≤ K * (y - x))
    {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g)) {m₄ : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧ ∫ v, g z v ^ 4 ∂ρ ≤ m₄)
    (hball : ∀ i, ∀ t : ℝ, 0 < t →
      ν {z | |∫ v, g z v ∂ρ - k i| ≤ t} ≤ ENNReal.ofReal (c_d i * t))
    (ω : ℕ × ℕ → Ω → 𝒵 × (ℕ → 𝒲)) (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ))
    (hind : iIndepFun ω μ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * 2 ^ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedDelta f g) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * ε ^ (-2 : ℝ) := by
  have hg4 := integrable_pow_four_of_fiber ν ρ hg hfib
  have hfm : Measurable f := (continuous_kinks hf hf₀).measurable
  obtain ⟨hGm, -⟩ := integrable_condMean_pow_four ν ρ hg hg4
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  obtain ⟨hPl2, hP2⟩ := memLp_nestedP_kinks ν ρ hf hf₀ hf₀' hg hg4
  have hPl : ∀ ℓ, Integrable (nestedP f g ℓ) (nestedLaw ν ρ) := fun ℓ =>
    (hPl2 ℓ).integrable one_le_two
  have hP : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) := hP2.integrable one_le_two
  have hΔm : ∀ ℓ, Measurable (nestedDelta f g ℓ) := measurable_nestedDelta hfm hg
  have hΔ : ∀ ℓ, MemLp (nestedDelta f g ℓ) 2 (nestedLaw ν ρ) := fun ℓ => by
    cases ℓ with
    | zero => exact hPl2 0
    | succ ℓ => exact (nested_kinks_variance_rate ν ρ hf hf₀ hf₀' hg hfib hball ℓ).1
  -- (i) the bias, `α = 1`
  obtain ⟨B₁, hB₁⟩ : ∃ B, B = K / 2 * (1 + 16 * m₄) +
      ∑ i, |c i| * (3 * c_d i * (1 + 1280 * m₄)) := ⟨_, rfl⟩
  have h_i : ∀ ℓ : ℕ, |∫ y, nestedP f g ℓ y - nestedTarget f g ρ y ∂(nestedLaw ν ρ)| ≤
      (|B₁| + 1) * (2 : ℝ) ^ (-((1 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hb := (nested_kinks_bias_rate ν ρ hf hf₀ hf₀' hg hfib hball ℓ).2
    rw [← hB₁] at hb
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity), mul_comm]
    linarith [le_abs_self B₁]
  -- (iii) the variance, `β = 3/2`
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = (Fintype.card ι + 1 : ℝ) * ((K / 8) ^ 2 * (224 * m₄) +
      ∑ i, c i ^ 2 * (2 * c_d i * Real.sqrt (8 * m₄ * (1 + 16 * m₄)))) := ⟨_, rfl⟩
  have h_iii : ∀ ℓ : ℕ, variance (nestedDelta f g ℓ) (nestedLaw ν ρ) ≤
      (variance (nestedDelta f g 0) (nestedLaw ν ρ) + 3 * |B₂| + 1) *
        (2 : ℝ) ^ (-((3 / 2 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hv0 := variance_nonneg (nestedDelta f g 0) (nestedLaw ν ρ)
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← div_eq_mul_inv]
    cases ℓ with
    | zero =>
      rw [Nat.cast_zero, mul_zero, Real.rpow_zero, div_one]
      linarith [abs_nonneg B₂]
    | succ ℓ =>
      have hv : variance (nestedDelta f g (ℓ + 1)) (nestedLaw ν ρ) ≤
          ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) := by
        simpa only [Pi.pow_apply] using
          variance_le_expectation_sq (hΔm (ℓ + 1)).aestronglyMeasurable
      have hr := (nested_kinks_variance_rate ν ρ hf hf₀ hf₀' hg hfib hball ℓ).2
      rw [← hB₂] at hr
      -- `2^{3(ℓ+1)/2} = 2^{3/2} 2^{3ℓ/2} ≤ 3 · 2^{3ℓ/2}`
      have h32 : (2 : ℝ) ^ ((3 / 2 : ℝ) * ((ℓ + 1 : ℕ) : ℝ)) ≤
          3 * (2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ)) := by
        have e : (3 / 2 : ℝ) * ((ℓ + 1 : ℕ) : ℝ) = 3 / 2 + (3 / 2 : ℝ) * (ℓ : ℝ) := by
          push_cast
          ring
        rw [e, Real.rpow_add (by norm_num)]
        gcongr
        have h8 : (2 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt 8 := by
          rw [Real.sqrt_eq_rpow, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [h8, Real.sqrt_le_left (by norm_num)]
        norm_num
      rw [le_div_iff₀ (by positivity)]
      have hvnn : 0 ≤ variance (nestedDelta f g (ℓ + 1)) (nestedLaw ν ρ) := variance_nonneg _ _
      calc variance (nestedDelta f g (ℓ + 1)) (nestedLaw ν ρ) *
            (2 : ℝ) ^ ((3 / 2 : ℝ) * ((ℓ + 1 : ℕ) : ℝ))
          ≤ variance (nestedDelta f g (ℓ + 1)) (nestedLaw ν ρ) *
            (3 * (2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ))) := mul_le_mul_of_nonneg_left h32 hvnn
        _ = 3 * ((2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ)) *
            variance (nestedDelta f g (ℓ + 1)) (nestedLaw ν ρ)) := by ring
        _ ≤ 3 * ((2 : ℝ) ^ ((3 / 2 : ℝ) * (ℓ : ℝ)) *
            ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)) := by gcongr
        _ ≤ 3 * B₂ := by linarith
        _ ≤ variance (nestedDelta f g 0) (nestedLaw ν ρ) + 3 * |B₂| + 1 := by
            linarith [le_abs_self B₂]
  -- (iv) the cost, `γ = 1`
  have h_iv : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, Real.rpow_natCast 2 ℓ]
    exact hC ℓ
  have hc₁ : 0 < |B₁| + 1 := by positivity
  have hc₂ : 0 < variance (nestedDelta f g 0) (nestedLaw ν ρ) + 3 * |B₂| + 1 := by
    have := variance_nonneg (nestedDelta f g 0) (nestedLaw ν ρ)
    positivity
  have hαβγ : min (3 / 2 : ℝ) 1 / 2 ≤ 1 := by norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_corrections (nestedTarget f g ρ) (nestedP f g)
    (nestedDelta f g) ω cost C one_pos (by norm_num) one_pos hc₁ hc₂ hc₃ hαβγ hω hind hP
    hPl hΔm hΔ hcost hcostC h_i (integral_nestedDelta ν ρ f g hPl) h_iii h_iv
  have hPint : ∫ y, nestedTarget f g ρ y ∂(nestedLaw ν ρ) = ∫ z, f (∫ v, g z v ∂ρ) ∂ν :=
    integral_comp_of_measurePreserving hfst (hfm.comp hGm).aestronglyMeasurable
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := h ε hε hε1
  rw [hPint] at hmse
  rw [complexityBound_of_lt (by norm_num) ε] at hcost'
  exact ⟨L, N, hN, hmse, hcost'⟩

end Kinks

end MLMC
