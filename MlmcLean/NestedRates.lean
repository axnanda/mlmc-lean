import MlmcLean.NestedMLMC
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Nested simulation: the remaining claims of §9.1–§9.2 (Giles 2015)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §9.1 "MLMC
treatment" (pp. 57–58) and §9.2 "MIMC treatment" (pp. 59–60) of the author's version.
`MlmcLean/NestedSimulation.lean` and `MlmcLean/NestedMLMC.lean` treat §9.1 for an exactly
computable inner quantity `g` and a smooth `f`; this file proves the other claims of §9.1–§9.2,
reusing their model: the outer sample `Z ~ ν`, the inner samples `W⁽⁰⁾, W⁽¹⁾, … ~ ρ`, all
independent (`nestedLaw ν ρ`), and the inner means `innerMean`.

* **The §9.2 Taylor expansion** (p. 60): "`Y_ℓ ≈ −(1/(4N_ℓ)) ∑_n f″(E[g(Z⁽ⁿ⁾, W)])
  {(Δg_{1,ℓ₂} − Δg_{2,ℓ₂})² − (Δg_{1,ℓ₂−1} − Δg_{2,ℓ₂−1})²}`".  The MIMC correction is the
  difference of two §9.1 antithetic differences, so the coefficient has the factor-2 error of §9.1
  (`antithetic_quadratic`): it is `−1/8`, exactly so for quadratic `f`
  (`mimc_antithetic_quadratic`).  `abs_mimc_antithetic_taylor_le` is the expansion with an explicit
  remainder when `f″` is Lipschitz, `abs_mimc_antithetic_le` the crude bound when `f′` is.
* **MLMC with a discretised inner quantity** (p. 59): "on level `ℓ` we could use `2^ℓ` timesteps.
  When using the Milstein discretisation (giving first order weak and strong convergence) this
  would still give `α = 1, β = 2`. However, we would now have `γ = 2` … This then leads to an
  overall MLMC complexity which is `O(ε⁻²(log ε)⁻²)`".  Level `ℓ` uses `2^ℓ` inner samples of a
  level-`ℓ` approximation `g_ℓ` (`nestedSdeP`, `nestedSdeDelta`).  The weak and strong orders of the
  Milstein scheme are not formalised: they are hypotheses on `g_ℓ`.  From them:
  `nested_sde_bias_rate` (`α = 1`), `nested_sde_variance_rate` (`β = 2`), `nested_sde_mean_rate`,
  and `nested_sde_mlmc_complexity` (Theorem 1 with `γ = 2`: cost `O(ε⁻²(log ε)²)`, the exponent of
  `log ε` printed as `−2` should be `2`).
* **A piecewise linear `f`** (p. 58, Bujok, Hambly and Reisinger): "the function `f` was piecewise
  linear, not twice differentiable, and so the rate of variance convergence was slightly lower,
  with `β = 1.5`. However, this is still sufficiently large to achieve an overall complexity which
  is `O(ε⁻²)`".  `antithetic_kink`: for one kink at `k` the antithetic difference vanishes unless
  `k` lies between the two coarse inner means, and is at most `¼|c||A₁ − A₂|` (sharp).
  `nested_kink_variance_rate` (`β = 3/2`), `nested_kink_bias_rate` (`α = ½`) and
  `nested_kink_mlmc_complexity` (cost `O(ε⁻²)`) hold if the conditional fourth moments are bounded
  and `E_W[g(Z, W)]` puts little mass near `k` (a bounded density suffices:
  `small_ball_of_density`, `nested_kink_variance_rate_of_density`).
* **The MIMC rates** (p. 60): "`E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` and `V_ℓ = O(2^{−2ℓ₁−2ℓ₂})`" for
  `ℓ₁, ℓ₂ > 0` (`nestedMimcDelta`, `nested_mimc_mean_rate`, `nested_mimc_variance_rate`), from the
  pathwise bound `abs_mimc_antithetic_le_of_deriv2`.  They need `f″` Lipschitz (not only "twice
  differentiable"), strong convergence in `L⁴` and weak convergence of the level differences
  uniformly in `Z`; the paper's intermediate `O(·)` claims hold only after re-centring.
-/

open MeasureTheory ProbabilityTheory Finset Filter

namespace MLMC

/-! ### Elementary inequalities -/

/-- A point `x + t (y − x)`, `t ∈ [0, 1]`, of the segment from `x` to `y` is at most
`max(|x|, |y|)` in absolute value. -/
lemma abs_add_mul_sub_le_max {x y t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |x + t * (y - x)| ≤ max |x| |y| := by
  obtain ⟨h0, h1⟩ := ht
  have e : x + t * (y - x) = (1 - t) * x + t * y := by ring
  have h1' : 0 ≤ 1 - t := by linarith
  rw [e]
  calc |(1 - t) * x + t * y| ≤ |(1 - t) * x| + |t * y| := abs_add_le _ _
    _ = (1 - t) * |x| + t * |y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h1', abs_of_nonneg h0]
    _ ≤ (1 - t) * max |x| |y| + t * max |x| |y| := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max |x| |y| := by ring

/-- `|Y| ≤ a + b + c` gives `Y² ≤ 3(a² + b² + c²)`. -/
lemma sq_le_three_mul_of_abs_le {Y a b c : ℝ} (h : |Y| ≤ a + b + c) :
    Y ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h1 : Y ^ 2 ≤ (a + b + c) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- `X² Z² ≤ ½(X⁴/q² + q² Z⁴) ≤ ½(T/q² + q² Z⁴)` if `X⁴ ≤ T` and `q > 0`. -/
lemma sq_mul_sq_le_of_pow_four_le {X Z T q : ℝ} (hq : 0 < q) (hX4 : X ^ 4 ≤ T) :
    X ^ 2 * Z ^ 2 ≤ (T / q ^ 2 + q ^ 2 * Z ^ 4) / 2 := by
  have e : (X ^ 4 / q ^ 2 + q ^ 2 * Z ^ 4) / 2 - X ^ 2 * Z ^ 2 =
      (X ^ 2 - q ^ 2 * Z ^ 2) ^ 2 / (2 * q ^ 2) := by
    field_simp
    ring
  have h0 : 0 ≤ (X ^ 2 - q ^ 2 * Z ^ 2) ^ 2 / (2 * q ^ 2) := by positivity
  have h2 : X ^ 4 / q ^ 2 ≤ T / q ^ 2 := div_le_div_of_nonneg_right hX4 (by positivity)
  linarith

/-- `max(|a|, |b|)⁴ ≤ a⁴ + b⁴`. -/
lemma max_abs_pow_four_le (a b : ℝ) : max |a| |b| ^ 4 ≤ a ^ 4 + b ^ 4 := by
  have ea : |a| ^ 4 = a ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  have eb : |b| ^ 4 = b ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  have ha : 0 ≤ a ^ 4 := by positivity
  have hb : 0 ≤ b ^ 4 := by positivity
  rcases le_total |a| |b| with h | h
  · rw [max_eq_right h, eb]
    linarith
  · rw [max_eq_left h, ea]
    linarith

/-- A function `f′` with `|f′(y) − f′(x)| ≤ K (y − x)` for `x ≤ y` is continuous. -/
lemma continuous_of_lipschitz_deriv {f' : ℝ → ℝ} {K : ℝ}
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) : Continuous f' := by
  have hK := lipschitz_const_nonneg hf'
  refine (LipschitzWith.of_dist_le_mul (K := K.toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
  rcases le_total x y with h | h
  · rw [abs_sub_comm, abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 h)]
    exact hf' x y h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact hf' y x h

/-- **A difference of values of `f` with a Lipschitz derivative** (Giles 2015, §9.2): if `f′` is
`K`-Lipschitz, then `|f(A) − f(B)| ≤ (|f′(0)| + K|B|) |A − B| + (K/2)(A − B)²`. -/
lemma abs_sub_le_of_lipschitz_deriv {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (A B : ℝ) :
    |f A - f B| ≤ (|f' 0| + K * |B|) * |A - B| + K / 2 * (A - B) ^ 2 := by
  have h1 := abs_taylor_first_le hf hf' B A
  have h2 : |f' B| ≤ |f' 0| + K * |B| := by
    have : |f' B - f' 0| ≤ K * |B| := by
      rcases le_total 0 B with h | h
      · rw [abs_of_nonneg h]
        simpa using hf' 0 B h
      · rw [abs_sub_comm, abs_of_nonpos h]
        have := hf' B 0 h
        simpa using this
    calc |f' B| = |f' B - f' 0 + f' 0| := by ring_nf
      _ ≤ |f' B - f' 0| + |f' 0| := abs_add_le _ _
      _ ≤ |f' 0| + K * |B| := by linarith
  calc |f A - f B| = |f' B * (A - B) + (f A - f B - f' B * (A - B))| := by ring_nf
    _ ≤ |f' B * (A - B)| + |f A - f B - f' B * (A - B)| := abs_add_le _ _
    _ ≤ (|f' 0| + K * |B|) * |A - B| + K / 2 * (A - B) ^ 2 := by
        rw [abs_mul]
        gcongr

/-- **The square of a difference of values of `f`** (Giles 2015, §9.2): if `f′` is `K`-Lipschitz,
then for every `s > 0`, `(f(A) − f(B))² ≤ 8(|f′(0)|⁴ + K⁴B⁴)/s + (s + K²/2)(A − B)⁴`. -/
lemma sq_sub_le_of_lipschitz_deriv {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (A B : ℝ) {s : ℝ} (hs : 0 < s) :
    (f A - f B) ^ 2 ≤ 8 * (|f' 0| ^ 4 + K ^ 4 * B ^ 4) / s + (s + K ^ 2 / 2) * (A - B) ^ 4 := by
  have h := abs_sub_le_of_lipschitz_deriv hf hf' A B
  set X := |f' 0| + K * |B|
  have hY : |A - B| ^ 2 = (A - B) ^ 2 := sq_abs _
  -- `(X|A − B| + (K/2)(A − B)²)² ≤ 2 X² (A − B)² + (K²/2)(A − B)⁴`
  have h1 : (f A - f B) ^ 2 ≤ 2 * X ^ 2 * (A - B) ^ 2 + K ^ 2 / 2 * (A - B) ^ 4 := by
    calc (f A - f B) ^ 2 = |f A - f B| ^ 2 := (sq_abs _).symm
      _ ≤ (X * |A - B| + K / 2 * (A - B) ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ ≤ 2 * X ^ 2 * (A - B) ^ 2 + K ^ 2 / 2 * (A - B) ^ 4 := by
          nlinarith [sq_nonneg (X * |A - B| - K / 2 * (A - B) ^ 2), hY]
  -- `2 X² (A − B)² ≤ X⁴/s + s (A − B)⁴`
  have h2 : 2 * X ^ 2 * (A - B) ^ 2 ≤ X ^ 4 / s + s * (A - B) ^ 4 := by
    rw [div_add' _ _ _ hs.ne', le_div_iff₀ hs]
    nlinarith [sq_nonneg (X ^ 2 - s * (A - B) ^ 2)]
  -- `X⁴ ≤ 8(|f′(0)|⁴ + K⁴ B⁴)`
  have h3 : X ^ 4 ≤ 8 * (|f' 0| ^ 4 + K ^ 4 * B ^ 4) := by
    have := sub_pow_four_le (|f' 0|) (-(K * |B|))
    rw [sub_neg_eq_add] at this
    calc X ^ 4 ≤ 8 * (|f' 0| ^ 4 + (-(K * |B|)) ^ 4) := this
      _ = 8 * (|f' 0| ^ 4 + K ^ 4 * B ^ 4) := by
          have hB4 : |B| ^ 4 = B ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
          rw [neg_pow, mul_pow, hB4]
          ring
  have h4 : X ^ 4 / s ≤ 8 * (|f' 0| ^ 4 + K ^ 4 * B ^ 4) / s :=
    div_le_div_of_nonneg_right h3 hs.le
  nlinarith

/-- A mean from a second moment without square roots: for `Y ∈ L²` on a probability space and
`s > 0`, `s |E[Y]| ≤ (s² E[Y²] + 1)/2`, from `|y| ≤ ½(s y² + 1/s)`. -/
lemma mul_abs_integral_le_of_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : MemLp Y 2 μ) {s : ℝ} (hs : 0 < s) :
    s * |∫ x, Y x ∂μ| ≤ (s ^ 2 * ∫ x, Y x ^ 2 ∂μ + 1) / 2 := by
  have hamgm : ∀ y : ℝ, |y| ≤ (s * y ^ 2 + 1 / s) / 2 := fun y => by
    have e : (s * y ^ 2 + 1 / s) / 2 - |y| = (s * |y| - 1) ^ 2 / (2 * s) := by
      rw [← sq_abs y]
      field_simp
      ring
    have : 0 ≤ (s * |y| - 1) ^ 2 / (2 * s) := by positivity
    linarith
  have i1 : Integrable (fun x => s * Y x ^ 2) μ := hY.integrable_sq.const_mul s
  have i2 : Integrable (fun x => (s * Y x ^ 2 + 1 / s) / 2) μ :=
    (i1.add (integrable_const _)).div_const 2
  have h1 : |∫ x, Y x ∂μ| ≤ (s * ∫ x, Y x ^ 2 ∂μ + 1 / s) / 2 := by
    calc |∫ x, Y x ∂μ| ≤ ∫ x, |Y x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, (s * Y x ^ 2 + 1 / s) / 2 ∂μ :=
          integral_mono (hY.integrable one_le_two).abs i2 fun x => hamgm _
      _ = (s * ∫ x, Y x ^ 2 ∂μ + 1 / s) / 2 := by
          rw [integral_div, integral_add i1 (integrable_const _), integral_const_mul,
            integral_const, probReal_univ, one_smul]
  calc s * |∫ x, Y x ∂μ| ≤ s * ((s * ∫ x, Y x ^ 2 ∂μ + 1 / s) / 2) := by gcongr
    _ = (s ^ 2 * ∫ x, Y x ^ 2 ∂μ + 1) / 2 := by field_simp

/-! ### §9.2: the Taylor expansion of the MIMC correction, with the constant `−1/8` -/

/-- **The coefficient of the §9.2 Taylor expansion is `−1/8`** (Giles 2015, §9.2, p. 60: "Carrying
out the same analysis as before, performing the Taylor series expansion around `E[g(Z⁽ⁿ⁾, W)]`, we
obtain `Y_ℓ ≈ −(1/(4N_ℓ)) ∑_n f″(E[g(Z⁽ⁿ⁾, W)]) {(Δg⁽ⁿ⁾_{1,ℓ₂} − Δg⁽ⁿ⁾_{2,ℓ₂})² −
(Δg⁽ⁿ⁾_{1,ℓ₂−1} − Δg⁽ⁿ⁾_{2,ℓ₂−1})²}`").  One outer sample of the MIMC correction is the
difference of the §9.1 antithetic differences for the level-`ℓ₂` and level-`(ℓ₂ − 1)` inner
approximations: with `G = E[g(Z⁽ⁿ⁾, W)]`, `a₁ = Δg_{1,ℓ₂}`, `b₁ = Δg_{2,ℓ₂}`, `a₂ = Δg_{1,ℓ₂−1}`,
`b₂ = Δg_{2,ℓ₂−1}` it is
`[f(G + ½(a₁ + b₁)) − ½ f(G + a₁) − ½ f(G + b₁)] − [f(G + ½(a₂ + b₂)) − ½ f(G + a₂) − ½ f(G + b₂)]`.
For `f(x) = c₀ + c₁x + (K/2)x²` (`f″ ≡ K`, so the second-order expansion is exact) this equals
`−(K/8){(a₁ − b₁)² − (a₂ − b₂)²}`, and it differs from the paper's `−(K/4){…}` whenever `K ≠ 0` and
`(a₁ − b₁)² ≠ (a₂ − b₂)²`.  Example: `f(x) = x²`, `G = 0`, `a₁ = 1`, `b₁ = −1`, `a₂ = b₂ = 0`; the
correction is `−1`, the paper's expression `−2`.  So the coefficient should be `−1/8`, as in §9.1
(`antithetic_quadratic`); the orders of magnitude derived from it are unaffected. -/
theorem mimc_antithetic_quadratic {f : ℝ → ℝ} {c₀ c₁ K : ℝ}
    (hf : ∀ x, f x = c₀ + c₁ * x + K / 2 * x ^ 2) (G a₁ a₂ b₁ b₂ : ℝ) :
    (f (G + (a₁ + b₁) / 2) - f (G + a₁) / 2 - f (G + b₁) / 2) -
        (f (G + (a₂ + b₂) / 2) - f (G + a₂) / 2 - f (G + b₂) / 2) =
      -(K / 8) * ((a₁ - b₁) ^ 2 - (a₂ - b₂) ^ 2) ∧
    (K ≠ 0 → (a₁ - b₁) ^ 2 ≠ (a₂ - b₂) ^ 2 →
      (f (G + (a₁ + b₁) / 2) - f (G + a₁) / 2 - f (G + b₁) / 2) -
          (f (G + (a₂ + b₂) / 2) - f (G + a₂) / 2 - f (G + b₂) / 2) ≠
        -(K / 4) * ((a₁ - b₁) ^ 2 - (a₂ - b₂) ^ 2)) := by
  have e1 := (antithetic_quadratic hf (G + a₁) (G + b₁)).1
  have e2 := (antithetic_quadratic hf (G + a₂) (G + b₂)).1
  have h1 : G + (a₁ + b₁) / 2 = (G + a₁ + (G + b₁)) / 2 := by ring
  have h2 : G + (a₂ + b₂) / 2 = (G + a₂ + (G + b₂)) / 2 := by ring
  have e : (f (G + (a₁ + b₁) / 2) - f (G + a₁) / 2 - f (G + b₁) / 2) -
      (f (G + (a₂ + b₂) / 2) - f (G + a₂) / 2 - f (G + b₂) / 2) =
      -(K / 8) * ((a₁ - b₁) ^ 2 - (a₂ - b₂) ^ 2) := by
    rw [h1, h2, e1, e2]
    ring
  refine ⟨e, fun hK hab h => ?_⟩
  rw [e] at h
  have hd : (a₁ - b₁) ^ 2 - (a₂ - b₂) ^ 2 ≠ 0 := sub_ne_zero.2 hab
  exact mul_ne_zero hK hd (by linarith)

/-- **The crude bound for the §9.2 correction** (Giles 2015, §9.2, p. 60, the expansion of `Y_ℓ`):
if `f′` is `K`-Lipschitz (e.g. `|f″| ≤ K`), then
`|D(A₁, A₂) − D(B₁, B₂)| ≤ (K/8)((A₁ − A₂)² + (B₁ − B₂)²)`, with
`D(x, y) = f(½(x + y)) − ½ f(x) − ½ f(y)`: the `(K/8)`-bound (`abs_midpoint_sub_avg_le`) of each
§9.1 difference, with the corrected constant.  It gives only `O(2^{−ℓ₁})`; the order
`O(2^{−ℓ₁−ℓ₂})` needs the cancellation between the two differences
(`abs_mimc_antithetic_le_of_deriv2`). -/
theorem abs_mimc_antithetic_le {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) (A₁ A₂ B₁ B₂ : ℝ) :
    |(f ((A₁ + A₂) / 2) - f A₁ / 2 - f A₂ / 2) - (f ((B₁ + B₂) / 2) - f B₁ / 2 - f B₂ / 2)| ≤
      K / 8 * ((A₁ - A₂) ^ 2 + (B₁ - B₂) ^ 2) := by
  have h1 := abs_midpoint_sub_avg_le hf hf' A₁ A₂
  have h2 := abs_midpoint_sub_avg_le hf hf' B₁ B₂
  calc _ ≤ |f ((A₁ + A₂) / 2) - f A₁ / 2 - f A₂ / 2| + |f ((B₁ + B₂) / 2) - f B₁ / 2 - f B₂ / 2| :=
        abs_sub _ _
    _ ≤ K / 8 * (A₁ - A₂) ^ 2 + K / 8 * (B₁ - B₂) ^ 2 := add_le_add h1 h2
    _ = K / 8 * ((A₁ - A₂) ^ 2 + (B₁ - B₂) ^ 2) := by ring

/-- **The difference of two antithetic differences along a segment** (Giles 2015, §9.2: the MIMC
correction `Y = D(A₁, A₂) − D(B₁, B₂)`, `D(x, y) = f(½(x + y)) − ½ f(x) − ½ f(y)`).  For every `c`,
`Y + (c/8)((A₁ − A₂)² − (B₁ − B₂)²)` is the increment over `[0, 1]` of
`t ↦ D(x₁(t), x₂(t)) + (c/8)(x₁(t) − x₂(t))²`, `x(t) = B + t (A − B)`; so it is at most any bound
`C` of the derivative `½(f′(m) − f′(x₁)) e₁ + ½(f′(m) − f′(x₂)) e₂ + (c/4)(x₁ − x₂)(e₁ − e₂)` on the
segment, where `m = ½(x₁ + x₂)` and `e = A − B` (mean value inequality). -/
lemma abs_antithetic_sub_add_le {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {c C A₁ A₂ B₁ B₂ : ℝ}
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(f' ((B₁ + t * (A₁ - B₁) + (B₂ + t * (A₂ - B₂))) / 2) - f' (B₁ + t * (A₁ - B₁))) *
            (A₁ - B₁) / 2 +
          (f' ((B₁ + t * (A₁ - B₁) + (B₂ + t * (A₂ - B₂))) / 2) - f' (B₂ + t * (A₂ - B₂))) *
            (A₂ - B₂) / 2 +
          c * (B₁ + t * (A₁ - B₁) - (B₂ + t * (A₂ - B₂))) * (A₁ - B₁ - (A₂ - B₂)) / 4| ≤ C) :
    |(f ((A₁ + A₂) / 2) - f A₁ / 2 - f A₂ / 2) - (f ((B₁ + B₂) / 2) - f B₁ / 2 - f B₂ / 2) +
      c / 8 * ((A₁ - A₂) ^ 2 - (B₁ - B₂) ^ 2)| ≤ C := by
  -- the path and its derivative
  have hx : ∀ (u v t : ℝ), HasDerivAt (fun t => u + t * (v - u)) (v - u) t := fun u v t => by
    simpa using ((hasDerivAt_id t).mul_const (v - u)).const_add u
  have hm : ∀ t, HasDerivAt (fun t => (B₁ + t * (A₁ - B₁) + (B₂ + t * (A₂ - B₂))) / 2)
      ((A₁ - B₁ + (A₂ - B₂)) / 2) t := fun t =>
    ((hx B₁ A₁ t).add (hx B₂ A₂ t)).div_const 2
  have hψ : ∀ t, HasDerivAt (fun t =>
      f ((B₁ + t * (A₁ - B₁) + (B₂ + t * (A₂ - B₂))) / 2) - f (B₁ + t * (A₁ - B₁)) / 2 -
        f (B₂ + t * (A₂ - B₂)) / 2 +
        c / 8 * (B₁ + t * (A₁ - B₁) - (B₂ + t * (A₂ - B₂))) ^ 2)
      ((f' ((B₁ + t * (A₁ - B₁) + (B₂ + t * (A₂ - B₂))) / 2) - f' (B₁ + t * (A₁ - B₁))) *
            (A₁ - B₁) / 2 +
          (f' ((B₁ + t * (A₁ - B₁) + (B₂ + t * (A₂ - B₂))) / 2) - f' (B₂ + t * (A₂ - B₂))) *
            (A₂ - B₂) / 2 +
          c * (B₁ + t * (A₁ - B₁) - (B₂ + t * (A₂ - B₂))) * (A₁ - B₁ - (A₂ - B₂)) / 4) t := by
    intro t
    have h1 := (hf _).comp t (hm t)
    have h2 := (hf _).comp t (hx B₁ A₁ t)
    have h3 := (hf _).comp t (hx B₂ A₂ t)
    have h5 : HasDerivAt (fun t => B₁ + t * (A₁ - B₁) - (B₂ + t * (A₂ - B₂)))
        (A₁ - B₁ - (A₂ - B₂)) t := (hx B₁ A₁ t).sub (hx B₂ A₂ t)
    have h4 := (h5.pow 2).const_mul (c / 8)
    refine (((h1.sub (h2.div_const 2)).sub (h3.div_const 2)).add h4).congr_deriv ?_
    norm_num
    ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hψ t).hasDerivWithinAt) (fun t ht => hC t (Set.Ico_subset_Icc_self ht))
  simp only [Real.norm_eq_abs, one_mul, zero_mul, add_zero, add_sub_cancel] at key
  convert key using 2
  ring

/-- The derivative in `abs_antithetic_sub_add_le` in terms of the second difference
`P = f′(x₁) + f′(x₂) − 2 f′(m)` and of `Q = f′(x₁) − f′(x₂) − c (x₁ − x₂)`: it equals
`−(P (e₁ + e₂) + Q (e₁ − e₂))/4` (Giles 2015, §9.2, the re-arrangement of p. 60). -/
lemma antithetic_deriv_eq (p₁ p₂ q c x₁ x₂ e₁ e₂ : ℝ) :
    (q - p₁) * e₁ / 2 + (q - p₂) * e₂ / 2 + c * (x₁ - x₂) * (e₁ - e₂) / 4 =
      -((p₁ + p₂ - 2 * q) * (e₁ + e₂) + (p₁ - p₂ - c * (x₁ - x₂)) * (e₁ - e₂)) / 4 := by
  ring

/-- **Differences of a derivative with a Lipschitz derivative** (Giles 2015, §9.2): if `f′` has
derivative `f″` and `f″` is `L`-Lipschitz, then `|f′(x₁) + f′(x₂) − 2 f′(m)| ≤ L ((x₁ − x₂)/2)²` and
`|f′(x₁) − f′(x₂) − f″(G)(x₁ − x₂)| ≤ L ((x₁ − x₂)/2)² + L |m − G| |x₁ − x₂|`, `m = ½(x₁ + x₂)`. -/
lemma abs_deriv_second_diff_le {f' f'' : ℝ → ℝ} {L : ℝ} (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x y, x ≤ y → |f'' y - f'' x| ≤ L * (y - x)) (G x₁ x₂ : ℝ) :
    |f' x₁ + f' x₂ - 2 * f' ((x₁ + x₂) / 2)| ≤ L * ((x₁ - x₂) / 2) ^ 2 ∧
      |f' x₁ - f' x₂ - f'' G * (x₁ - x₂)| ≤
        L * ((x₁ - x₂) / 2) ^ 2 + L * |(x₁ + x₂) / 2 - G| * |x₁ - x₂| := by
  set m := (x₁ + x₂) / 2 with hm
  have t1 := abs_taylor_first_le hf' hf'' m x₁
  have t2 := abs_taylor_first_le hf' hf'' m x₂
  have e1 : (x₁ - m) ^ 2 = ((x₁ - x₂) / 2) ^ 2 := by rw [hm]; ring
  have e2 : (x₂ - m) ^ 2 = ((x₁ - x₂) / 2) ^ 2 := by rw [hm]; ring
  rw [e1] at t1
  rw [e2] at t2
  have hs : x₁ - m + (x₂ - m) = 0 := by rw [hm]; ring
  have hG : |f'' m - f'' G| ≤ L * |m - G| := by
    rcases le_total G m with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact hf'' G m h
    · rw [abs_sub_comm, abs_sub_comm m G, abs_of_nonneg (sub_nonneg.2 h)]
      exact hf'' m G h
  constructor
  · have e : f' x₁ + f' x₂ - 2 * f' m =
        (f' x₁ - f' m - f'' m * (x₁ - m)) + (f' x₂ - f' m - f'' m * (x₂ - m)) +
          f'' m * (x₁ - m + (x₂ - m)) := by ring
    rw [e, hs, mul_zero, add_zero]
    calc |f' x₁ - f' m - f'' m * (x₁ - m) + (f' x₂ - f' m - f'' m * (x₂ - m))|
        ≤ |f' x₁ - f' m - f'' m * (x₁ - m)| + |f' x₂ - f' m - f'' m * (x₂ - m)| :=
          abs_add_le _ _
      _ ≤ L / 2 * ((x₁ - x₂) / 2) ^ 2 + L / 2 * ((x₁ - x₂) / 2) ^ 2 := add_le_add t1 t2
      _ = L * ((x₁ - x₂) / 2) ^ 2 := by ring
  · have e : f' x₁ - f' x₂ - f'' G * (x₁ - x₂) =
        (f' x₁ - f' m - f'' m * (x₁ - m)) - (f' x₂ - f' m - f'' m * (x₂ - m)) +
          (f'' m - f'' G) * (x₁ - x₂) := by rw [hm]; ring
    rw [e]
    calc |f' x₁ - f' m - f'' m * (x₁ - m) - (f' x₂ - f' m - f'' m * (x₂ - m)) +
          (f'' m - f'' G) * (x₁ - x₂)|
        ≤ |f' x₁ - f' m - f'' m * (x₁ - m)| + |f' x₂ - f' m - f'' m * (x₂ - m)| +
          |f'' m - f'' G| * |x₁ - x₂| := by
          rw [← abs_mul]
          exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ L / 2 * ((x₁ - x₂) / 2) ^ 2 + L / 2 * ((x₁ - x₂) / 2) ^ 2 +
          L * |m - G| * |x₁ - x₂| := by
          gcongr
      _ = L * ((x₁ - x₂) / 2) ^ 2 + L * |m - G| * |x₁ - x₂| := by ring

/-- **The §9.2 Taylor expansion with the coefficient `−1/8` and a remainder** (Giles 2015, §9.2,
p. 60: "performing the Taylor series expansion around `E[g(Z⁽ⁿ⁾, W)]`, we obtain `Y_ℓ ≈
−(1/(4N_ℓ)) ∑_n f″(E[g(Z⁽ⁿ⁾, W)]) {(Δg_{1,ℓ₂} − Δg_{2,ℓ₂})² − (Δg_{1,ℓ₂−1} − Δg_{2,ℓ₂−1})²}`").
In the notation of `mimc_antithetic_quadratic`, let `f′` have derivative `f″` with `f″`
`L`-Lipschitz.  Then `|Y + (f″(G)/8){(a₁ − b₁)² − (a₂ − b₂)²}| ≤ (L/16) δ² (|e₊| + |e₋|) +
(L/8) σ δ |e₋|`, with `δ = max(|a₁ − b₁|, |a₂ − b₂|)`, `σ = max(|a₁ + b₁|, |a₂ + b₂|)`,
`e₊ = (a₁ − a₂) + (b₁ − b₂)` and `e₋ = (a₁ − a₂) − (b₁ − b₂)`.  So the expansion holds with the
coefficient `−1/8`, not `−1/4`, and is exact for quadratic `f` (`L = 0`).  Deviations from the
paper: its "twice differentiable" does not control the remainder, so `f″` is assumed Lipschitz;
and the remainder is of the same order `2^{−ℓ₁−ℓ₂}` as the leading term (the change of `f″`
between the level-`ℓ₂` and level-`(ℓ₂ − 1)` inner means, `δ² |e₊|`), so the "`≈`" holds only up
to terms of the same order, which is enough for the paper's `O(·)` conclusions
(`nested_mimc_variance_rate`). -/
theorem abs_mimc_antithetic_taylor_le {f f' f'' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x y, x ≤ y → |f'' y - f'' x| ≤ L * (y - x)) (G a₁ a₂ b₁ b₂ : ℝ) :
    |(f (G + (a₁ + b₁) / 2) - f (G + a₁) / 2 - f (G + b₁) / 2) -
        (f (G + (a₂ + b₂) / 2) - f (G + a₂) / 2 - f (G + b₂) / 2) +
        f'' G / 8 * ((a₁ - b₁) ^ 2 - (a₂ - b₂) ^ 2)| ≤
      L / 16 * max |a₁ - b₁| |a₂ - b₂| ^ 2 * (|a₁ - a₂ + (b₁ - b₂)| + |a₁ - a₂ - (b₁ - b₂)|) +
        L / 8 * max |a₁ + b₁| |a₂ + b₂| * max |a₁ - b₁| |a₂ - b₂| * |a₁ - a₂ - (b₁ - b₂)| := by
  have hL := lipschitz_const_nonneg hf''
  have e : (f (G + (a₁ + b₁) / 2) - f (G + a₁) / 2 - f (G + b₁) / 2) -
        (f (G + (a₂ + b₂) / 2) - f (G + a₂) / 2 - f (G + b₂) / 2) +
        f'' G / 8 * ((a₁ - b₁) ^ 2 - (a₂ - b₂) ^ 2) =
      (f ((G + a₁ + (G + b₁)) / 2) - f (G + a₁) / 2 - f (G + b₁) / 2) -
        (f ((G + a₂ + (G + b₂)) / 2) - f (G + a₂) / 2 - f (G + b₂) / 2) +
        f'' G / 8 * ((G + a₁ - (G + b₁)) ^ 2 - (G + a₂ - (G + b₂)) ^ 2) := by
    rw [show (G + a₁ + (G + b₁)) / 2 = G + (a₁ + b₁) / 2 by ring,
      show (G + a₂ + (G + b₂)) / 2 = G + (a₂ + b₂) / 2 by ring]
    ring
  rw [e]
  refine abs_antithetic_sub_add_le hf fun t ht => ?_
  set x₁ := G + a₂ + t * (G + a₁ - (G + a₂)) with hx₁
  set x₂ := G + b₂ + t * (G + b₁ - (G + b₂)) with hx₂
  obtain ⟨hP, hQ⟩ := abs_deriv_second_diff_le hf' hf'' G x₁ x₂
  rw [antithetic_deriv_eq]
  -- the path stays within the bounds of its end points
  have hd : |x₁ - x₂| ≤ max |a₁ - b₁| |a₂ - b₂| := by
    have h := abs_add_mul_sub_le_max (x := a₂ - b₂) (y := a₁ - b₁) ht
    rw [max_comm]
    convert h using 2
    rw [hx₁, hx₂]
    ring
  have hmG : |(x₁ + x₂) / 2 - G| ≤ max |a₁ + b₁| |a₂ + b₂| / 2 := by
    have h := abs_add_mul_sub_le_max (x := a₂ + b₂) (y := a₁ + b₁) ht
    rw [max_comm] at h
    have e2 : (x₁ + x₂) / 2 - G = (a₂ + b₂ + t * (a₁ + b₁ - (a₂ + b₂))) / 2 := by
      rw [hx₁, hx₂]
      ring
    rw [e2, abs_div, abs_two]
    linarith
  have hd0 : 0 ≤ |x₁ - x₂| := abs_nonneg _
  have hd2 : ((x₁ - x₂) / 2) ^ 2 ≤ max |a₁ - b₁| |a₂ - b₂| ^ 2 / 4 := by
    rw [div_pow, ← sq_abs (x₁ - x₂)]
    have := pow_le_pow_left₀ hd0 hd 2
    linarith
  have e1 : G + a₁ - (G + a₂) + (G + b₁ - (G + b₂)) = a₁ - a₂ + (b₁ - b₂) := by ring
  have e2 : G + a₁ - (G + a₂) - (G + b₁ - (G + b₂)) = a₁ - a₂ - (b₁ - b₂) := by ring
  rw [e1, e2, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hQ' : |f' x₁ - f' x₂ - f'' G * (x₁ - x₂)| ≤ L * (max |a₁ - b₁| |a₂ - b₂| ^ 2 / 4) +
      L * (max |a₁ + b₁| |a₂ + b₂| / 2) * max |a₁ - b₁| |a₂ - b₂| := by
    refine hQ.trans ?_
    gcongr
  have hP' : |f' x₁ + f' x₂ - 2 * f' ((x₁ + x₂) / 2)| ≤ L * (max |a₁ - b₁| |a₂ - b₂| ^ 2 / 4) :=
    hP.trans (by gcongr)
  calc |(f' x₁ + f' x₂ - 2 * f' ((x₁ + x₂) / 2)) * (a₁ - a₂ + (b₁ - b₂)) +
        (f' x₁ - f' x₂ - f'' G * (x₁ - x₂)) * (a₁ - a₂ - (b₁ - b₂))| / 4
      ≤ (|f' x₁ + f' x₂ - 2 * f' ((x₁ + x₂) / 2)| * |a₁ - a₂ + (b₁ - b₂)| +
          |f' x₁ - f' x₂ - f'' G * (x₁ - x₂)| * |a₁ - a₂ - (b₁ - b₂)|) / 4 := by
        gcongr
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ (L * (max |a₁ - b₁| |a₂ - b₂| ^ 2 / 4) * |a₁ - a₂ + (b₁ - b₂)| +
          (L * (max |a₁ - b₁| |a₂ - b₂| ^ 2 / 4) +
            L * (max |a₁ + b₁| |a₂ + b₂| / 2) * max |a₁ - b₁| |a₂ - b₂|) *
            |a₁ - a₂ - (b₁ - b₂)|) / 4 := by
        gcongr
    _ = _ := by ring

/-- **The pathwise bound behind the MIMC rates, re-centred** (Giles 2015, §9.2, p. 60: "Due to the
Central Limit Theorem, we have `Δg_{1,ℓ₂} + Δg_{1,ℓ₂−1} = O(2^{−ℓ₁/2})` … and assuming first order
strong convergence we also have `Δg_{1,ℓ₂} − Δg_{1,ℓ₂−1} = O(2^{−ℓ₁/2−ℓ₂})` … Combining these
results we obtain `(Δg_{1,ℓ₂} − Δg_{2,ℓ₂})² − (Δg_{1,ℓ₂−1} − Δg_{2,ℓ₂−1})² = O(2^{−ℓ₁−ℓ₂})`").  Let
`f′` (with derivative `f″`) be `K`-Lipschitz and `f″` be `L`-Lipschitz.  For the two coarse inner
means `A₁, A₂` of the fine-timestep and `B₁, B₂` of the coarse-timestep inner quantity, and every
`μ`, `|D(A₁, A₂) − D(B₁, B₂)| ≤ (L/8) δ² |μ| + (K/2) δ |½((A₁ − B₁) + (A₂ − B₂)) − μ| +
(K/4) δ |(A₁ − B₁) − (A₂ − B₂)|`, `δ = max(|A₁ − A₂|, |B₁ − B₂|)`.
Re-centring: `A₁ − B₁ = Δg_{1,ℓ₂} − Δg_{1,ℓ₂−1}` has the conditional mean
`μ = E[g_{ℓ₂} − g_{ℓ₂−1} | Z]`, of the order `2^{−ℓ₂}` of the weak error, so it is `O(2^{−ℓ₂})`, not
`O(2^{−ℓ₁/2−ℓ₂})` as printed (if `g_ℓ = g + c 2^{−ℓ}`, then `A₁ − B₁ = −c 2^{−ℓ₂}` whatever `ℓ₁`);
likewise `Δg_{1,ℓ₂} + Δg_{1,ℓ₂−1}` contains the bias `O(2^{−ℓ₂})`.  Only the fluctuation
`½((A₁ − B₁) + (A₂ − B₂)) − μ` and the antithetic difference `(A₁ − B₁) − (A₂ − B₂)` are
`O(2^{−ℓ₁/2−ℓ₂})`; the mean shift `μ` enters through the second difference of `f′`, which is where
`f″` Lipschitz is needed.  With `δ = O(2^{−ℓ₁/2})` every term is `O(2^{−ℓ₁−ℓ₂})`. -/
theorem abs_mimc_antithetic_le_of_deriv2 {f f' f'' : ℝ → ℝ} {K L : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hK : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x))
    (hf'' : ∀ x y, x ≤ y → |f'' y - f'' x| ≤ L * (y - x)) (A₁ A₂ B₁ B₂ μ : ℝ) :
    |(f ((A₁ + A₂) / 2) - f A₁ / 2 - f A₂ / 2) - (f ((B₁ + B₂) / 2) - f B₁ / 2 - f B₂ / 2)| ≤
      L / 8 * max |A₁ - A₂| |B₁ - B₂| ^ 2 * |μ| +
        K / 2 * max |A₁ - A₂| |B₁ - B₂| * |(A₁ - B₁ + (A₂ - B₂)) / 2 - μ| +
        K / 4 * max |A₁ - A₂| |B₁ - B₂| * |A₁ - B₁ - (A₂ - B₂)| := by
  have hL := lipschitz_const_nonneg hf''
  have hK0 := lipschitz_const_nonneg hK
  set D := max |A₁ - A₂| |B₁ - B₂| with hD
  have key := abs_antithetic_sub_add_le hf (c := 0)
    (C := L / 8 * D ^ 2 * |μ| + K / 2 * D * |(A₁ - B₁ + (A₂ - B₂)) / 2 - μ| +
        K / 4 * D * |A₁ - B₁ - (A₂ - B₂)|) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁)
    (B₂ := B₂) (fun t ht => ?_)
  · simpa using key
  set x₁ := B₁ + t * (A₁ - B₁) with hx₁
  set x₂ := B₂ + t * (A₂ - B₂) with hx₂
  have hP := (abs_deriv_second_diff_le hf' hf'' 0 x₁ x₂).1
  rw [antithetic_deriv_eq]
  have hd : |x₁ - x₂| ≤ D := by
    have h := abs_add_mul_sub_le_max (x := B₁ - B₂) (y := A₁ - A₂) ht
    rw [hD, max_comm]
    convert h using 2
    rw [hx₁, hx₂]
    ring
  have hd0 : 0 ≤ |x₁ - x₂| := abs_nonneg _
  have hd2 : ((x₁ - x₂) / 2) ^ 2 ≤ D ^ 2 / 4 := by
    rw [div_pow, ← sq_abs (x₁ - x₂)]
    have := pow_le_pow_left₀ hd0 hd 2
    linarith
  have hlip : ∀ a b, |f' a - f' b| ≤ K * |a - b| := fun a b => by
    rcases le_total b a with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact hK b a h
    · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.2 h)]
      exact hK a b h
  -- the second difference of `f′`: `|P| ≤ L d²` and `|P| ≤ 2K|d|`
  have hP' : |f' x₁ + f' x₂ - 2 * f' ((x₁ + x₂) / 2)| ≤ L * (D ^ 2 / 4) :=
    hP.trans (by gcongr)
  have hP'' : |f' x₁ + f' x₂ - 2 * f' ((x₁ + x₂) / 2)| ≤ K * D := by
    have e : f' x₁ + f' x₂ - 2 * f' ((x₁ + x₂) / 2) =
        (f' x₁ - f' ((x₁ + x₂) / 2)) + (f' x₂ - f' ((x₁ + x₂) / 2)) := by ring
    have h1 := hlip x₁ ((x₁ + x₂) / 2)
    have h2 := hlip x₂ ((x₁ + x₂) / 2)
    have e1 : |x₁ - (x₁ + x₂) / 2| = |x₁ - x₂| / 2 := by
      rw [show x₁ - (x₁ + x₂) / 2 = (x₁ - x₂) / 2 by ring, abs_div, abs_two]
    have e2 : |x₂ - (x₁ + x₂) / 2| = |x₁ - x₂| / 2 := by
      rw [show x₂ - (x₁ + x₂) / 2 = -((x₁ - x₂) / 2) by ring, abs_neg, abs_div, abs_two]
    rw [e1] at h1
    rw [e2] at h2
    rw [e]
    calc |(f' x₁ - f' ((x₁ + x₂) / 2)) + (f' x₂ - f' ((x₁ + x₂) / 2))|
        ≤ |f' x₁ - f' ((x₁ + x₂) / 2)| + |f' x₂ - f' ((x₁ + x₂) / 2)| := abs_add_le _ _
      _ ≤ K * (|x₁ - x₂| / 2) + K * (|x₁ - x₂| / 2) := add_le_add h1 h2
      _ = K * |x₁ - x₂| := by ring
      _ ≤ K * D := mul_le_mul_of_nonneg_left hd hK0
  have hQ : |f' x₁ - f' x₂ - 0 * (x₁ - x₂)| ≤ K * D := by
    rw [zero_mul, sub_zero]
    exact (hlip x₁ x₂).trans (mul_le_mul_of_nonneg_left hd hK0)
  rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  set P := f' x₁ + f' x₂ - 2 * f' ((x₁ + x₂) / 2)
  set Q := f' x₁ - f' x₂ - 0 * (x₁ - x₂)
  have e : P * (A₁ - B₁ + (A₂ - B₂)) + Q * (A₁ - B₁ - (A₂ - B₂)) =
      2 * P * μ + 2 * P * ((A₁ - B₁ + (A₂ - B₂)) / 2 - μ) + Q * (A₁ - B₁ - (A₂ - B₂)) := by
    ring
  rw [e]
  calc |2 * P * μ + 2 * P * ((A₁ - B₁ + (A₂ - B₂)) / 2 - μ) + Q * (A₁ - B₁ - (A₂ - B₂))| / 4
      ≤ (2 * |P| * |μ| + 2 * |P| * |(A₁ - B₁ + (A₂ - B₂)) / 2 - μ| +
          |Q| * |A₁ - B₁ - (A₂ - B₂)|) / 4 := by
        gcongr
        calc |2 * P * μ + 2 * P * ((A₁ - B₁ + (A₂ - B₂)) / 2 - μ) + Q * (A₁ - B₁ - (A₂ - B₂))|
            ≤ |2 * P * μ| + |2 * P * ((A₁ - B₁ + (A₂ - B₂)) / 2 - μ)| +
                |Q * (A₁ - B₁ - (A₂ - B₂))| := abs_add_three _ _ _
          _ = 2 * |P| * |μ| + 2 * |P| * |(A₁ - B₁ + (A₂ - B₂)) / 2 - μ| +
                |Q| * |A₁ - B₁ - (A₂ - B₂)| := by
              simp only [abs_mul, abs_two]
    _ ≤ (2 * (L * (D ^ 2 / 4)) * |μ| + 2 * (K * D) * |(A₁ - B₁ + (A₂ - B₂)) / 2 - μ| +
          K * D * |A₁ - B₁ - (A₂ - B₂)|) / 4 := by
        gcongr
    _ = L / 8 * D ^ 2 * |μ| + K / 2 * D * |(A₁ - B₁ + (A₂ - B₂)) / 2 - μ| +
          K / 4 * D * |A₁ - B₁ - (A₂ - B₂)| := by ring

/-! ### The nested model: inner means and their moments -/

section Model

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲]

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
/-- The inner mean is linear in the inner quantity (Giles 2015, §9.2: the level difference of the
inner means is the inner mean of the level difference `g_{ℓ+1} − g_ℓ`). -/
lemma innerMean_sub (g₁ g₂ : 𝒵 → 𝒲 → ℝ) (M : ℕ) (z : 𝒵) (w : ℕ → 𝒲) :
    innerMean g₁ M z w - innerMean g₂ M z w = innerMean (fun z v => g₁ z v - g₂ z v) M z w := by
  simp only [innerMean, Finset.sum_sub_distrib, mul_sub]

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
/-- The §9.1 correction as an antithetic difference of the two coarse inner means (Giles 2015,
§9.1, p. 57): `Y_{ℓ+1} = f(½(A + A′)) − ½ f(A) − ½ f(A′)`, where `A, A′` are the means of the two
halves of the `2^{ℓ+1}` inner samples. -/
lemma nestedDelta_succ_eq (f : ℝ → ℝ) (g : 𝒵 → 𝒲 → ℝ) (ℓ : ℕ) (p : 𝒵 × (ℕ → 𝒲)) :
    nestedDelta f g (ℓ + 1) p =
      f ((innerMean g (2 ^ ℓ) p.1 p.2 + innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2) -
        f (innerMean g (2 ^ ℓ) p.1 p.2) / 2 -
        f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2 := by
  have e : innerMean g (2 ^ (ℓ + 1)) p.1 p.2 = (innerMean g (2 ^ ℓ) p.1 p.2 +
      innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2 := by
    rw [show (2 : ℕ) ^ (ℓ + 1) = 2 * 2 ^ ℓ from pow_succ' 2 ℓ, innerMean_two_mul]
  show f (innerMean g (2 ^ (ℓ + 1)) p.1 p.2) - f (innerMean g (2 ^ ℓ) p.1 p.2) / 2 -
    f (innerMean g (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2 = _
  rw [e]

end Model

section ModelFiber

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ρ : Measure 𝒲)
  [IsProbabilityMeasure ρ]

omit [MeasurableSpace 𝒵] in
/-- **The centred fourth moment of the inner mean** (Giles 2015, §9.1: "By the Central Limit
Theorem, `Δg₁⁽ⁿ⁾, Δg₂⁽ⁿ⁾ = O(M_ℓ^{−1/2})`", in `L⁴`).  For a fixed outer sample `z` with
`E_W[g(z, W)⁴] < ∞`, `G = E_W[g(z, W)]` and `M ≥ 1`: `M² E[(A_M − G)⁴] ≤ 64 E_W[g(z, W)⁴]`. -/
lemma fiber_centred_fourth_moment (g : 𝒵 → 𝒲 → ℝ) (z : 𝒵) (hgz : Measurable (g z))
    (hgz4 : Integrable (fun v => g z v ^ 4) ρ) {M : ℕ} (hM : 0 < M) :
    Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 4) (innerLaw ρ) ∧
      (M : ℝ) ^ 2 * ∫ w, (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 4 ∂(innerLaw ρ) ≤
        64 * ∫ v, g z v ^ 4 ∂ρ := by
  have hM1 : (1 : ℝ) ≤ M := Nat.one_le_cast.2 hM
  obtain ⟨-, hk, hsk, -⟩ := centred_moments_le hgz hgz4
  obtain ⟨j4, -, -, e4⟩ :=
    fiber_sum_moments ρ hgz hgz4 (nestedSign M) (nestedSign_sq M) M
  obtain ⟨G, hG⟩ : ∃ G, G = ∫ v, g z v ∂ρ := ⟨_, rfl⟩
  rw [← hG] at hk hsk j4 e4 ⊢
  have hE : ∀ w, innerMean g M z w - G =
      (M : ℝ)⁻¹ * ∑ m ∈ range M, nestedSign M m * (g z (w m) - G) :=
    fun w => centred_sum_eq g hM z w G
  simp only [hE, mul_pow]
  refine ⟨j4.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hk0 : 0 ≤ ∫ v, (g z v - G) ^ 4 ∂ρ := integral_nonneg fun v => by positivity
  set κ := ∫ v, (g z v - G) ^ 4 ∂ρ
  set σ := ∫ v, (g z v - G) ^ 2 ∂ρ
  calc (M : ℝ) ^ 2 * ((M : ℝ)⁻¹ ^ 4 *
        ∫ w, (∑ m ∈ range M, nestedSign M m * (g z (w m) - G)) ^ 4 ∂(innerLaw ρ))
      ≤ (M : ℝ) ^ 2 * ((M : ℝ)⁻¹ ^ 4 * (M * κ + 3 * M ^ 2 * σ ^ 2)) := by gcongr
    _ = κ / M + 3 * σ ^ 2 := by field_simp
    _ ≤ κ + 3 * κ := by
        gcongr
        exact div_le_self hk0 hM1
    _ ≤ 64 * ∫ v, g z v ^ 4 ∂ρ := by linarith

end ModelFiber

section ModelProduct

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **Jensen's inequality for the inner mean** (Giles 2015, §9.1–§9.2): `A_M⁴ ≤ M⁻¹ ∑ h(Z, W⁽ᵐ⁾)⁴`
and each `(Z, W⁽ᵐ⁾)` has the law of `(Z, W)`, so `E[A_M⁴] ≤ E[h(Z, W)⁴]` (`M ≥ 1`); no independence
of the inner samples is used. -/
lemma integral_innerMean_pow_four_le {h : 𝒵 → 𝒲 → ℝ} (hh : Measurable (Function.uncurry h))
    (hh4 : Integrable (fun p : 𝒵 × 𝒲 => h p.1 p.2 ^ 4) (ν.prod ρ)) {M : ℕ} (hM : 0 < M) :
    ∫ p, innerMean h M p.1 p.2 ^ 4 ∂(nestedLaw ν ρ) ≤ ∫ p, h p.1 p.2 ^ 4 ∂(ν.prod ρ) := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hev : ∀ m, MeasurePreserving (Function.eval m) (innerLaw ρ) ρ := fun m =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) m
  have hcoord : ∀ m, MeasurePreserving (fun p : 𝒵 × (ℕ → 𝒲) => (p.1, p.2 m)) (nestedLaw ν ρ)
      (ν.prod ρ) := fun m => (MeasurePreserving.id ν).prod (hev m)
  have hgm : ∀ m, Integrable (fun p : 𝒵 × (ℕ → 𝒲) => h p.1 (p.2 m) ^ 4) (nestedLaw ν ρ) :=
    fun m => (hcoord m).integrable_comp_of_integrable hh4
  have hgi : ∀ m, ∫ p, h p.1 (p.2 m) ^ 4 ∂(nestedLaw ν ρ) = ∫ p, h p.1 p.2 ^ 4 ∂(ν.prod ρ) :=
    fun m => integral_comp_of_measurePreserving (hcoord m) hh4.aestronglyMeasurable
  have hJ : ∀ x : ℕ → ℝ, ((M : ℝ)⁻¹ * ∑ m ∈ range M, x m) ^ 4 ≤
      (M : ℝ)⁻¹ * ∑ m ∈ range M, x m ^ 4 := fun x => by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (n := 4) (by decide)).map_sum_le (t := range M)
      (w := fun _ => (M : ℝ)⁻¹) (p := x) (fun _ _ => inv_nonneg.2 (Nat.cast_nonneg M))
      (by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_inv_cancel₀ hM')
      (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul, ← Finset.mul_sum] at h
    exact h
  have hdom : Integrable (fun p : 𝒵 × (ℕ → 𝒲) => (M : ℝ)⁻¹ * ∑ m ∈ range M, h p.1 (p.2 m) ^ 4)
      (nestedLaw ν ρ) :=
    (integrable_finsetSum (range M) fun m _ => hgm m).const_mul _
  calc ∫ p, innerMean h M p.1 p.2 ^ 4 ∂(nestedLaw ν ρ)
      ≤ ∫ p, (M : ℝ)⁻¹ * ∑ m ∈ range M, h p.1 (p.2 m) ^ 4 ∂(nestedLaw ν ρ) :=
        integral_mono (integrable_innerMean_pow_four ν ρ hh hh4 hM) hdom
          fun p => hJ fun m => h p.1 (p.2 m)
    _ = ∫ p, h p.1 p.2 ^ 4 ∂(ν.prod ρ) := by
        rw [integral_const_mul, integral_finsetSum _ fun m _ => hgm m]
        simp only [hgi, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

/-- **The fourth moment of the antithetic difference of the inner means** (Giles 2015, §9.1:
"`Δg₁⁽ⁿ⁾, Δg₂⁽ⁿ⁾ = O(M_ℓ^{−1/2})`", in `L⁴` and averaged over the outer sample): if
`E[g(Z, W)⁴] < ∞` and `M ≥ 1`, then `M² E[(A_M − A′_M)⁴] ≤ 224 E[g(Z, W)⁴]`. -/
lemma integral_antithetic_pow_four_le {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) {M : ℕ} (hM : 0 < M) :
    Integrable (fun p : 𝒵 × (ℕ → 𝒲) =>
        (innerMean g M p.1 p.2 - innerMean g M p.1 (shiftSeq M p.2)) ^ 4) (nestedLaw ν ρ) ∧
      (M : ℝ) ^ 2 * ∫ p, (innerMean g M p.1 p.2 - innerMean g M p.1 (shiftSeq M p.2)) ^ 4
          ∂(nestedLaw ν ρ) ≤ 224 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ) := by
  obtain ⟨hfib4, hm4, hE4⟩ := fourth_moment_fibers ν ρ hg4
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  have hDm : Measurable fun p : 𝒵 × (ℕ → 𝒲) =>
      innerMean g M p.1 p.2 - innerMean g M p.1 (shiftSeq M p.2) :=
    (measurable_innerMean hg M measurable_id).sub
      (measurable_innerMean hg M (measurable_shiftSeq M))
  obtain ⟨hD4, hD4le⟩ := integrable_of_fiber_bound ν ρ
    (F := fun p => (innerMean g M p.1 p.2 - innerMean g M p.1 (shiftSeq M p.2)) ^ 4)
    (hDm.pow_const 4) (fun p => by positivity) ((hm4.const_mul 224).div_const ((M : ℝ) ^ 2))
    (hfib4.mono fun z hz => by
      obtain ⟨i4, -, h4, -⟩ := fiber_nested_moments ρ g z hg.of_uncurry_left hz hM
      refine ⟨i4, ?_⟩
      show ∫ w, (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 4 ∂(innerLaw ρ) ≤
        224 * (∫ v, g z v ^ 4 ∂ρ) / (M : ℝ) ^ 2
      rw [le_div_iff₀ hM2]
      linarith)
  refine ⟨hD4, ?_⟩
  rw [integral_div, integral_const_mul, hE4, le_div_iff₀ hM2] at hD4le
  linarith

/-- **The centred fourth moment of the inner mean, averaged over the outer sample** (Giles 2015,
§9.1): if `E[g(Z, W)⁴] < ∞` and `M ≥ 1`, then `M² E[(A_M − E_W[g(Z, W)])⁴] ≤ 64 E[g(Z, W)⁴]`. -/
lemma integral_centred_pow_four_le {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) {M : ℕ} (hM : 0 < M) :
    Integrable (fun p : 𝒵 × (ℕ → 𝒲) => (innerMean g M p.1 p.2 - ∫ v, g p.1 v ∂ρ) ^ 4)
        (nestedLaw ν ρ) ∧
      (M : ℝ) ^ 2 * ∫ p, (innerMean g M p.1 p.2 - ∫ v, g p.1 v ∂ρ) ^ 4 ∂(nestedLaw ν ρ) ≤
        64 * ∫ p, g p.1 p.2 ^ 4 ∂(ν.prod ρ) := by
  obtain ⟨hfib4, hm4, hE4⟩ := fourth_moment_fibers ν ρ hg4
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  have hGm : Measurable fun z => ∫ v, g z v ∂ρ := (integrable_condMean_pow_four ν ρ hg hg4).1
  have hDm : Measurable fun p : 𝒵 × (ℕ → 𝒲) => innerMean g M p.1 p.2 - ∫ v, g p.1 v ∂ρ :=
    (measurable_innerMean hg M measurable_id).sub (hGm.comp measurable_fst)
  obtain ⟨hD4, hD4le⟩ := integrable_of_fiber_bound ν ρ
    (F := fun p => (innerMean g M p.1 p.2 - ∫ v, g p.1 v ∂ρ) ^ 4)
    (hDm.pow_const 4) (fun p => by positivity) ((hm4.const_mul 64).div_const ((M : ℝ) ^ 2))
    (hfib4.mono fun z hz => by
      obtain ⟨i4, h4⟩ := fiber_centred_fourth_moment ρ g z hg.of_uncurry_left hz hM
      refine ⟨i4, ?_⟩
      show ∫ w, (innerMean g M z w - ∫ v, g z v ∂ρ) ^ 4 ∂(innerLaw ρ) ≤
        64 * (∫ v, g z v ^ 4 ∂ρ) / (M : ℝ) ^ 2
      rw [le_div_iff₀ hM2]
      linarith)
  refine ⟨hD4, ?_⟩
  rw [integral_div, integral_const_mul, hE4, le_div_iff₀ hM2] at hD4le
  linarith

end ModelProduct

/-! ### §9.2: MLMC with `2^ℓ` inner samples of a level-`ℓ` inner approximation -/

section Discretised

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲]

/-- The level-`ℓ` approximation with a discretised inner quantity (Giles 2015, §9.2, p. 59: "suppose
now that `W` represents a complete Brownian path, and so `g(Z, W)` can not be evaluated exactly; it
can only be approximated by using some finite number of timesteps. We could continue to use MLMC,
and on level `ℓ` we could use `2^ℓ` timesteps"): `P_ℓ = f(2^{−ℓ} ∑_{m<2^ℓ} g_ℓ(Z, W⁽ᵐ⁾))`, where
`g_ℓ` is the level-`ℓ` approximation of the inner quantity. -/
noncomputable def nestedSdeP (f : ℝ → ℝ) (gh : ℕ → 𝒵 → 𝒲 → ℝ) (ℓ : ℕ)
    (p : 𝒵 × (ℕ → 𝒲)) : ℝ :=
  f (innerMean (gh ℓ) (2 ^ ℓ) p.1 p.2)

/-- The antithetic level correction with a discretised inner quantity (Giles 2015, §9.1–§9.2):
`P₀` on level `0` and, on level `ℓ + 1` with `M = 2^ℓ`, `f(A_{2M}) − ½ f(B_M) − ½ f(B′_M)`, where
`A_{2M}` is the mean of `g_{ℓ+1}` over all `2M` inner samples and `B_M`, `B′_M` are the means of
`g_ℓ` over the first and the second `M` of them: the §9.1 antithetic estimator with the fine value
computed with the fine inner approximation.  Both use the same inner samples `W⁽ᵐ⁾`. -/
noncomputable def nestedSdeDelta (f : ℝ → ℝ) (gh : ℕ → 𝒵 → 𝒲 → ℝ) :
    ℕ → 𝒵 × (ℕ → 𝒲) → ℝ
  | 0 => nestedSdeP f gh 0
  | ℓ + 1 => fun p => f (innerMean (gh (ℓ + 1)) (2 ^ (ℓ + 1)) p.1 p.2) -
      f (innerMean (gh ℓ) (2 ^ ℓ) p.1 p.2) / 2 -
      f (innerMean (gh ℓ) (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2

omit [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] in
/-- **The discretised correction splits into the §9.1 correction and two level differences**
(Giles 2015, §9.2): with `M = 2^ℓ`, `A, A′` the two half means of `g_{ℓ+1}` and `B, B′` those of
`g_ℓ`, `Y_{ℓ+1} = [f(½(A + A′)) − ½ f(A) − ½ f(A′)] + ½(f(A) − f(B)) + ½(f(A′) − f(B′))`. -/
lemma nestedSdeDelta_succ_eq (f : ℝ → ℝ) (gh : ℕ → 𝒵 → 𝒲 → ℝ) (ℓ : ℕ) (p : 𝒵 × (ℕ → 𝒲)) :
    nestedSdeDelta f gh (ℓ + 1) p = nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p +
      (f (innerMean (gh (ℓ + 1)) (2 ^ ℓ) p.1 p.2) - f (innerMean (gh ℓ) (2 ^ ℓ) p.1 p.2)) / 2 +
      (f (innerMean (gh (ℓ + 1)) (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) -
        f (innerMean (gh ℓ) (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2))) / 2 := by
  simp only [nestedSdeDelta, nestedDelta]
  ring

/-- The discretised correction is measurable. -/
lemma measurable_nestedSdeDelta {f : ℝ → ℝ} (hfm : Measurable f) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hg : ∀ ℓ, Measurable (Function.uncurry (gh ℓ))) (ℓ : ℕ) :
    Measurable (nestedSdeDelta f gh ℓ) := by
  cases ℓ with
  | zero => exact hfm.comp (measurable_innerMean (hg 0) (2 ^ 0) measurable_id)
  | succ ℓ =>
    exact ((hfm.comp (measurable_innerMean (hg (ℓ + 1)) _ measurable_id)).sub
      ((hfm.comp (measurable_innerMean (hg ℓ) _ measurable_id)).div_const 2)).sub
      ((hfm.comp (measurable_innerMean (hg ℓ) _ (measurable_shiftSeq (2 ^ ℓ)))).div_const 2)

/-- **The discretised correction has the correct expectation** (Giles 2015, §9.1, p. 57: "Note that
this has the correct expectation, i.e. `E[Y_ℓ] = E[P_ℓ − P_{ℓ−1}]`", for the inner approximations
of §9.2).  If every `P_ℓ` (`nestedSdeP`) is integrable, then `E[Y_ℓ] = E[P_ℓ − P_{ℓ−1}]`
(`P_{−1} ≡ 0`): the second half of the inner samples has the law of the first. -/
theorem integral_nestedSdeDelta (ν : Measure 𝒵) [IsProbabilityMeasure ν] (ρ : Measure 𝒲)
    [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (gh : ℕ → 𝒵 → 𝒲 → ℝ)
    (hint : ∀ ℓ, Integrable (nestedSdeP f gh ℓ) (nestedLaw ν ρ)) (ℓ : ℕ) :
    ∫ p, nestedSdeDelta f gh ℓ p ∂(nestedLaw ν ρ) =
      ∫ p, levelDiff (nestedSdeP f gh) ℓ p ∂(nestedLaw ν ρ) := by
  cases ℓ with
  | zero => rfl
  | succ ℓ =>
    have hφ : MeasurePreserving (fun p : 𝒵 × (ℕ → 𝒲) => (p.1, shiftSeq (2 ^ ℓ) p.2))
        (nestedLaw ν ρ) (nestedLaw ν ρ) :=
      (MeasurePreserving.id ν).prod (measurePreserving_shiftSeq ρ (2 ^ ℓ))
    have hsame : ∫ p, f (innerMean (gh ℓ) (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) ∂(nestedLaw ν ρ) =
        ∫ p, nestedSdeP f gh ℓ p ∂(nestedLaw ν ρ) :=
      integral_comp_of_measurePreserving hφ (hint ℓ).aestronglyMeasurable
    have hint2 : Integrable (fun p : 𝒵 × (ℕ → 𝒲) =>
        f (innerMean (gh ℓ) (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2))) (nestedLaw ν ρ) :=
      hφ.integrable_comp_of_integrable (hint ℓ)
    have hA : Integrable (fun p => nestedSdeP f gh (ℓ + 1) p - nestedSdeP f gh ℓ p / 2)
        (nestedLaw ν ρ) :=
      (hint (ℓ + 1)).sub ((hint ℓ).div_const 2)
    show ∫ p, (nestedSdeP f gh (ℓ + 1) p - nestedSdeP f gh ℓ p / 2 -
        f (innerMean (gh ℓ) (2 ^ ℓ) p.1 (shiftSeq (2 ^ ℓ) p.2)) / 2) ∂(nestedLaw ν ρ) =
      ∫ p, (nestedSdeP f gh (ℓ + 1) p - nestedSdeP f gh ℓ p) ∂(nestedLaw ν ρ)
    rw [integral_sub hA (hint2.div_const 2),
      integral_sub (hint (ℓ + 1)) ((hint ℓ).div_const 2), integral_div, integral_div, hsame,
      integral_sub (hint (ℓ + 1)) (hint ℓ)]
    ring

variable (ν : Measure 𝒵) [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **`β = 2` for nested simulation with `2^ℓ` timesteps** (Giles 2015, §9.2, p. 59: "We could
continue to use MLMC, and on level `ℓ` we could use `2^ℓ` timesteps. When using the Milstein
discretisation (giving first order weak and strong convergence) this would still give `α = 1,
β = 2`").  Level `ℓ` uses `2^ℓ` inner samples of the level-`ℓ` approximation `g_ℓ` of the inner
quantity (`nestedSdeP`, `nestedSdeDelta`).  The properties of the Milstein scheme are not
formalised; they enter as hypotheses on `g_ℓ`: bounded fourth moments `E[g_ℓ(Z, W)⁴] ≤ m₄`, and
first order strong convergence in `L⁴`, `(2^ℓ)⁴ E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))⁴] ≤ cₛ`.  If `f′` is
`K`-Lipschitz (e.g. `|f″| ≤ K`), then the correction `Y_{ℓ+1}` is square-integrable and
`(2^ℓ)² E[Y_{ℓ+1}²] ≤ 3 (K/8)² · 224 m₄ + (3/2)(8(|f′(0)|⁴ + K⁴ m₄) + (1 + K²/2) cₛ)`, i.e.
`V_ℓ = O(2^{−2ℓ})`.  Proof: `Y_{ℓ+1}` is the §9.1 correction of `g_{ℓ+1}`, which is `O(2^{−ℓ})` in
`L²` (`nested_variance_rate`), plus `½(f(A) − f(B)) + ½(f(A′) − f(B′))`, where `A − B` is the mean
of `2^ℓ` samples of `g_{ℓ+1} − g_ℓ` (`nestedSdeDelta_succ_eq`, `sq_sub_le_of_lipschitz_deriv`).
Strong convergence in `L⁴` rather than `L²` is used because `f′(B)` is unbounded for a merely
Lipschitz `f′` (e.g. `f(x) = x²`). -/
theorem nested_sde_variance_rate {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hg : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hg4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ cₛ : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ) (ℓ : ℕ) :
    MemLp (nestedSdeDelta f gh (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      ((2 : ℝ) ^ ℓ) ^ 2 * ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        3 * ((K / 8) ^ 2 * (224 * m₄)) +
          3 / 2 * (8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ) := by
  set M : ℕ := 2 ^ ℓ with hMdef
  have hM : 0 < M := by positivity
  have hMr : ((M : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by rw [hMdef]; push_cast; ring
  have h2l : (1 : ℝ) ≤ (2 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  -- the pieces of the decomposition
  set A : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => innerMean (gh (ℓ + 1)) M p.1 p.2
  set B : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => innerMean (gh ℓ) M p.1 p.2
  set φ : 𝒵 × (ℕ → 𝒲) → 𝒵 × (ℕ → 𝒲) := fun p => (p.1, shiftSeq M p.2)
  have hφ : MeasurePreserving φ (nestedLaw ν ρ) (nestedLaw ν ρ) :=
    (MeasurePreserving.id ν).prod (measurePreserving_shiftSeq ρ M)
  set U : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => f (A p) - f (B p)
  have hdec : ∀ p, nestedSdeDelta f gh (ℓ + 1) p =
      nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p + U p / 2 + U (φ p) / 2 := fun p =>
    nestedSdeDelta_succ_eq f gh ℓ p
  obtain ⟨hN2, hNle⟩ := nested_variance_rate ν ρ hf hf' (hg (ℓ + 1)) (hg4 (ℓ + 1)) ℓ
  have hfA : MemLp (fun p => f (A p)) 2 (nestedLaw ν ρ) :=
    memLp_nestedP ν ρ hf hf' (hg (ℓ + 1)) (hg4 (ℓ + 1)) ℓ
  have hfB : MemLp (fun p => f (B p)) 2 (nestedLaw ν ρ) :=
    memLp_nestedP ν ρ hf hf' (hg ℓ) (hg4 ℓ) ℓ
  have hU2 : MemLp U 2 (nestedLaw ν ρ) := hfA.sub hfB
  have hUφ : MemLp (fun p => U (φ p)) 2 (nestedLaw ν ρ) := hU2.comp_measurePreserving hφ
  have hY2 : MemLp (nestedSdeDelta f gh (ℓ + 1)) 2 (nestedLaw ν ρ) := by
    have e : nestedSdeDelta f gh (ℓ + 1) = fun p =>
        nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p + 2⁻¹ * U p + 2⁻¹ * U (φ p) := by
      funext p
      rw [hdec p]
      ring
    rw [e]
    exact (hN2.add (hU2.const_mul 2⁻¹)).add (hUφ.const_mul 2⁻¹)
  refine ⟨hY2, ?_⟩
  -- the fourth moments of `B` and of `A − B`
  have hdiff : Measurable (Function.uncurry fun z v => gh (ℓ + 1) z v - gh ℓ z v) :=
    (hg (ℓ + 1)).sub (hg ℓ)
  have hdiff4 : Integrable (fun p : 𝒵 × 𝒲 => (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4)
      (ν.prod ρ) := by
    refine (((hg4 (ℓ + 1)).add (hg4 ℓ)).const_mul 8).mono'
      ((hdiff.pow_const 4).aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact sub_pow_four_le _ _
  have hB4 : Integrable (fun p => B p ^ 4) (nestedLaw ν ρ) :=
    integrable_innerMean_pow_four ν ρ (hg ℓ) (hg4 ℓ) hM
  have hB4le : ∫ p, B p ^ 4 ∂(nestedLaw ν ρ) ≤ m₄ :=
    (integral_innerMean_pow_four_le ν ρ (hg ℓ) (hg4 ℓ) hM).trans (hm₄ ℓ)
  have hAB : ∀ p, A p - B p = innerMean (fun z v => gh (ℓ + 1) z v - gh ℓ z v) M p.1 p.2 :=
    fun p => innerMean_sub _ _ M p.1 p.2
  have hAB4 : Integrable (fun p => (A p - B p) ^ 4) (nestedLaw ν ρ) := by
    simp only [hAB]
    exact integrable_innerMean_pow_four ν ρ hdiff hdiff4 hM
  have hAB4le : ((2 : ℝ) ^ ℓ) ^ 4 * ∫ p, (A p - B p) ^ 4 ∂(nestedLaw ν ρ) ≤ cₛ := by
    simp only [hAB]
    refine le_trans ?_ (hs ℓ)
    gcongr
    exact integral_innerMean_pow_four_le ν ρ hdiff hdiff4 hM
  have hcs : 0 ≤ cₛ := le_trans (by positivity) hAB4le
  -- `E[U²] ≤ 8(|f′(0)|⁴ + K⁴ m₄)/M² + (M² + K²/2) E[(A − B)⁴]`
  set s : ℝ := ((2 : ℝ) ^ ℓ) ^ 2 with hs_def
  have hs0 : 0 < s := by positivity
  have hUpt : ∀ p, U p ^ 2 ≤ 8 * (|f' 0| ^ 4 + K ^ 4 * B p ^ 4) / s +
      (s + K ^ 2 / 2) * (A p - B p) ^ 4 := fun p =>
    sq_sub_le_of_lipschitz_deriv hf hf' (A p) (B p) hs0
  have iC : Integrable (fun p => |f' 0| ^ 4 + K ^ 4 * B p ^ 4) (nestedLaw ν ρ) :=
    (integrable_const _).add (hB4.const_mul _)
  have i1 : Integrable (fun p => 8 * (|f' 0| ^ 4 + K ^ 4 * B p ^ 4) / s) (nestedLaw ν ρ) :=
    (iC.const_mul 8).div_const s
  have i2 : Integrable (fun p => (s + K ^ 2 / 2) * (A p - B p) ^ 4) (nestedLaw ν ρ) :=
    hAB4.const_mul _
  have iB : Integrable (fun p => K ^ 4 * B p ^ 4) (nestedLaw ν ρ) := hB4.const_mul _
  have hUle : ∫ p, U p ^ 2 ∂(nestedLaw ν ρ) ≤
      8 * (|f' 0| ^ 4 + K ^ 4 * m₄) / s + (s + K ^ 2 / 2) * (cₛ / ((2 : ℝ) ^ ℓ) ^ 4) := by
    have i12 : Integrable (fun p => 8 * (|f' 0| ^ 4 + K ^ 4 * B p ^ 4) / s +
        (s + K ^ 2 / 2) * (A p - B p) ^ 4) (nestedLaw ν ρ) := i1.add i2
    refine (integral_mono hU2.integrable_sq i12 hUpt).trans ?_
    rw [integral_add i1 i2, integral_div, integral_const_mul, integral_add (integrable_const _) iB,
      integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul]
    have h1 : ∫ p, (A p - B p) ^ 4 ∂(nestedLaw ν ρ) ≤ cₛ / ((2 : ℝ) ^ ℓ) ^ 4 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    gcongr
  have hUφle : ∫ p, U (φ p) ^ 2 ∂(nestedLaw ν ρ) = ∫ p, U p ^ 2 ∂(nestedLaw ν ρ) :=
    integral_comp_of_measurePreserving hφ hU2.integrable_sq.aestronglyMeasurable
  -- `Y² ≤ 3 N² + (3/4) U² + (3/4) U(φ)²`
  have hYpt : ∀ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ≤
      3 * nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 + 3 / 4 * U p ^ 2 + 3 / 4 * U (φ p) ^ 2 :=
    fun p => by
      rw [hdec p]
      nlinarith [sq_nonneg (nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p - U p / 2),
        sq_nonneg (nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p - U (φ p) / 2),
        sq_nonneg (U p / 2 - U (φ p) / 2)]
  have j1 : Integrable (fun p => 3 * nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2) (nestedLaw ν ρ) :=
    hN2.integrable_sq.const_mul 3
  have j2 : Integrable (fun p => 3 / 4 * U p ^ 2) (nestedLaw ν ρ) := hU2.integrable_sq.const_mul _
  have j3 : Integrable (fun p => 3 / 4 * U (φ p) ^ 2) (nestedLaw ν ρ) :=
    hUφ.integrable_sq.const_mul _
  have j12 : Integrable (fun p => 3 * nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 + 3 / 4 * U p ^ 2)
      (nestedLaw ν ρ) := j1.add j2
  have j123 : Integrable (fun p => 3 * nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 +
      3 / 4 * U p ^ 2 + 3 / 4 * U (φ p) ^ 2) (nestedLaw ν ρ) := j12.add j3
  have hY2le := integral_mono hY2.integrable_sq j123 hYpt
  rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
    integral_const_mul, hUφle] at hY2le
  have hNle' : ((2 : ℝ) ^ ℓ) ^ 2 * ∫ p, nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)
      ≤ (K / 8) ^ 2 * (224 * m₄) :=
    hNle.trans (by gcongr; exact hm₄ (ℓ + 1))
  have hUle' : s * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ) ≤
      8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ := by
    have h1 : s * (8 * (|f' 0| ^ 4 + K ^ 4 * m₄) / s + (s + K ^ 2 / 2) * (cₛ / ((2 : ℝ) ^ ℓ) ^ 4))
        = 8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2 / s) * cₛ := by
      rw [hs_def]
      field_simp
    have h2 : K ^ 2 / 2 / s ≤ K ^ 2 / 2 := by
      rw [div_le_iff₀ hs0]
      have : (1 : ℝ) ≤ s := by rw [hs_def]; nlinarith
      nlinarith [sq_nonneg K]
    calc s * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ)
        ≤ s * (8 * (|f' 0| ^ 4 + K ^ 4 * m₄) / s + (s + K ^ 2 / 2) * (cₛ / ((2 : ℝ) ^ ℓ) ^ 4)) :=
          mul_le_mul_of_nonneg_left hUle hs0.le
      _ = 8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2 / s) * cₛ := h1
      _ ≤ 8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ := by gcongr
  calc ((2 : ℝ) ^ ℓ) ^ 2 * ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)
      ≤ ((2 : ℝ) ^ ℓ) ^ 2 * (3 * ∫ p, nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) +
          3 / 4 * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ) + 3 / 4 * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ)) :=
        mul_le_mul_of_nonneg_left hY2le (by positivity)
    _ = 3 * (((2 : ℝ) ^ ℓ) ^ 2 *
          ∫ p, nestedDelta f (gh (ℓ + 1)) (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)) +
          3 / 2 * (s * ∫ p, U p ^ 2 ∂(nestedLaw ν ρ)) := by rw [hs_def]; ring
    _ ≤ 3 * ((K / 8) ^ 2 * (224 * m₄)) +
          3 / 2 * (8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ) := by
        gcongr

/-- **`E[Y_ℓ] = O(2^{−ℓ})` for nested simulation with `2^ℓ` timesteps** (Giles 2015, §9.2, p. 59:
"this would still give `α = 1, β = 2`").  Under the hypotheses of `nested_sde_variance_rate`, with
`C` its bound, `2^ℓ |E[Y_{ℓ+1}]| ≤ (C + 1)/2` (`mul_abs_integral_le_of_memLp`). -/
theorem nested_sde_mean_rate {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hg : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hg4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ cₛ : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ) (ℓ : ℕ) :
    (2 : ℝ) ^ ℓ * |∫ p, nestedSdeDelta f gh (ℓ + 1) p ∂(nestedLaw ν ρ)| ≤
      (3 * ((K / 8) ^ 2 * (224 * m₄)) +
        3 / 2 * (8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ) + 1) / 2 := by
  obtain ⟨hY2, hV⟩ := nested_sde_variance_rate ν ρ hf hf' hg hg4 hm₄ hs ℓ
  refine (mul_abs_integral_le_of_memLp hY2 (by positivity : (0 : ℝ) < 2 ^ ℓ)).trans ?_
  gcongr

/-- **`α = 1` for nested simulation with `2^ℓ` timesteps** (Giles 2015, §9.2, p. 59: "When using
the Milstein discretisation (giving first order weak and strong convergence) this would still give
`α = 1`").  The first order weak convergence of the inner approximation is a hypothesis standing
in for the weak order of the Milstein scheme, uniformly in the outer sample:
`2^ℓ |E_W[g_ℓ(z, W)] − E_W[g(z, W)]| ≤ c_w` for `ν`-a.e. `z`, where `g` is the exact inner
quantity.  With `E[g_ℓ(Z, W)⁴] ≤ m₄`, `E[g(Z, W)⁴] < ∞` and `f′` `K`-Lipschitz, the level-`ℓ`
approximation has the bias
`2^ℓ |E[P_ℓ] − E_Z[f(E_W[g(Z, W)])]| ≤ (K/2)(1 + 16 m₄) + c_w E_Z|f′(E_W[g(Z, W)])| + (K/2) c_w²`:
the inner sampling error `O(2^{−ℓ})` (`nested_bias_rate`) plus the discretisation error
`O(2^{−ℓ})`. -/
theorem nested_sde_bias_rate {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ)) {c_w : ℝ}
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w) (ℓ : ℕ) :
    (2 : ℝ) ^ ℓ * |∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
      K / 2 * (1 + 16 * m₄) + c_w * ∫ z, |f' (∫ v, g z v ∂ρ)| ∂ν + K / 2 * c_w ^ 2 := by
  have hK := lipschitz_const_nonneg hf'
  have h2l : (1 : ℝ) ≤ (2 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  have h2l0 : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  -- the conditional means `G_ℓ(z) = E_W[g_ℓ(z, W)]` and `G(z) = E_W[g(z, W)]`
  obtain ⟨hGm, hG4⟩ := integrable_condMean_pow_four ν ρ hg hg4
  obtain ⟨hGlm, hGl4⟩ := integrable_condMean_pow_four ν ρ (hgh ℓ) (hgh4 ℓ)
  have hfG := memLp_two_comp_of_pow_four hf hf' hGm hG4
  have hfGl := memLp_two_comp_of_pow_four hf hf' hGlm hGl4
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hPl : Integrable (nestedSdeP f gh ℓ) (nestedLaw ν ρ) :=
    (memLp_nestedP ν ρ hf hf' (hgh ℓ) (hgh4 ℓ) ℓ).integrable one_le_two
  have hTl : Integrable (nestedTarget f (gh ℓ) ρ) (nestedLaw ν ρ) :=
    (memLp_nestedTarget ν ρ hf hf' (hgh ℓ) (hgh4 ℓ)).integrable one_le_two
  have hT : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    (memLp_nestedTarget ν ρ hf hf' hg hg4).integrable one_le_two
  -- split into the inner sampling error and the discretisation error
  have e1 : ∫ p, (nestedSdeP f gh ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p) ∂(nestedLaw ν ρ) +
        ∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν := by
    have e2 : ∫ p, (nestedTarget f (gh ℓ) ρ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
        ∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν :=
      integral_comp_of_measurePreserving hfst
        ((hfGl.integrable one_le_two).sub (hfG.integrable one_le_two)).aestronglyMeasurable
    have i1 : Integrable (fun p => nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p)
        (nestedLaw ν ρ) := hPl.sub hTl
    have i2 : Integrable (fun p => nestedTarget f (gh ℓ) ρ p - nestedTarget f g ρ p)
        (nestedLaw ν ρ) := hTl.sub hT
    rw [← e2, ← integral_add i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun p => by
      simp only [nestedSdeP, nestedP]
      ring)
  -- the inner sampling error, from the §9.1 analysis
  have hb1 := nested_bias_rate ν ρ hf hf' (hgh ℓ) (hgh4 ℓ) ℓ
  have hb1' : (2 : ℝ) ^ ℓ * |∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p)
      ∂(nestedLaw ν ρ)| ≤ K / 2 * (1 + 16 * m₄) :=
    hb1.trans (by gcongr; exact hm₄ ℓ)
  -- the discretisation error, from the weak error of `g_ℓ`
  have hf'm : Measurable f' := (continuous_of_lipschitz_deriv hf').measurable
  have hG1 : Integrable (fun z => ∫ v, g z v ∂ρ) ν := by
    simpa using integrable_pow_of_pow_four hGm hG4 (k := 1) (by norm_num)
  have hf'G : Integrable (fun z => |f' (∫ v, g z v ∂ρ)|) ν := by
    refine ((integrable_const |f' 0|).add (hG1.abs.const_mul K)).mono'
      (continuous_abs.measurable.comp (hf'm.comp hGm)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have h := abs_sub_abs_le_abs_sub (f' (∫ v, g z v ∂ρ)) (f' 0)
    have h' : |f' (∫ v, g z v ∂ρ) - f' 0| ≤ K * |∫ v, g z v ∂ρ| := by
      rcases le_total 0 (∫ v, g z v ∂ρ) with h0 | h0
      · rw [abs_of_nonneg h0]
        simpa using hf' 0 _ h0
      · rw [abs_sub_comm, abs_of_nonpos h0]
        simpa using hf' _ 0 h0
    show |f' (∫ v, g z v ∂ρ)| ≤ |f' 0| + K * |∫ v, g z v ∂ρ|
    linarith
  have hD : Integrable (fun z => f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ν :=
    (hfGl.integrable one_le_two).sub (hfG.integrable one_le_two)
  have hpt : ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)| ≤
      c_w * |f' (∫ v, g z v ∂ρ)| + K / 2 * c_w ^ 2 := by
    filter_upwards [hw ℓ] with z hz
    set a := ∫ v, gh ℓ z v ∂ρ
    set b := ∫ v, g z v ∂ρ
    have ht := abs_taylor_first_le hf hf' b a
    have hab : |a - b| ≤ c_w / (2 : ℝ) ^ ℓ := by
      rw [le_div_iff₀ h2l0, mul_comm]
      exact hz
    have hsq : (a - b) ^ 2 ≤ (c_w / (2 : ℝ) ^ ℓ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    have h1 : |f a - f b| ≤ |f' b| * |a - b| + K / 2 * (a - b) ^ 2 := by
      calc |f a - f b| = |f' b * (a - b) + (f a - f b - f' b * (a - b))| := by ring_nf
        _ ≤ |f' b * (a - b)| + |f a - f b - f' b * (a - b)| := abs_add_le _ _
        _ ≤ |f' b| * |a - b| + K / 2 * (a - b) ^ 2 := by rw [abs_mul]; gcongr
    calc (2 : ℝ) ^ ℓ * |f a - f b|
        ≤ (2 : ℝ) ^ ℓ * (|f' b| * (c_w / (2 : ℝ) ^ ℓ) + K / 2 * (c_w / (2 : ℝ) ^ ℓ) ^ 2) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = c_w * |f' b| + K / 2 * c_w ^ 2 / (2 : ℝ) ^ ℓ := by
          field_simp
      _ ≤ c_w * |f' b| + K / 2 * c_w ^ 2 := by
          gcongr
          exact div_le_self (by positivity) h2l
  have hb2 : (2 : ℝ) ^ ℓ * |∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν| ≤
      c_w * ∫ z, |f' (∫ v, g z v ∂ρ)| ∂ν + K / 2 * c_w ^ 2 := by
    rw [← integral_const_mul]
    have i3 : Integrable (fun z => c_w * |f' (∫ v, g z v ∂ρ)| + K / 2 * c_w ^ 2) ν :=
      (hf'G.const_mul c_w).add (integrable_const (K / 2 * c_w ^ 2))
    have h := integral_mono_ae ((hD.abs).const_mul ((2 : ℝ) ^ ℓ)) i3 hpt
    rw [integral_add (hf'G.const_mul c_w) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul] at h
    refine le_trans ?_ h
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs h2l0.le
  rw [e1]
  calc (2 : ℝ) ^ ℓ * |∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p) ∂(nestedLaw ν ρ) +
        ∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν|
      ≤ (2 : ℝ) ^ ℓ * |∫ p, (nestedP f (gh ℓ) ℓ p - nestedTarget f (gh ℓ) ρ p)
          ∂(nestedLaw ν ρ)| +
        (2 : ℝ) ^ ℓ * |∫ z, (f (∫ v, gh ℓ z v ∂ρ) - f (∫ v, g z v ∂ρ)) ∂ν| := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) h2l0.le
    _ ≤ K / 2 * (1 + 16 * m₄) + (c_w * ∫ z, |f' (∫ v, g z v ∂ρ)| ∂ν + K / 2 * c_w ^ 2) :=
        add_le_add hb1' hb2
    _ = _ := by ring

/-- **MLMC for nested simulation with `2^ℓ` timesteps has complexity `O(ε⁻²(log ε)²)`**
(Giles 2015, §9.2, p. 59: "this would still give `α = 1, β = 2`. However, we would now have
`γ = 2`, because the work on successive levels would go up by factor `4×`, because of using twice
as many timesteps as well as twice as many inner samples. This then leads to an overall MLMC
complexity which is `O(ε⁻²(log ε)⁻²)`").  Under the hypotheses of `nested_sde_variance_rate`
(bounded fourth moments, strong convergence in `L⁴`) and `nested_sde_bias_rate` (weak convergence
uniformly in `Z`), which stand in for the orders of the Milstein scheme, let the inputs
`ω^{(ℓ,n)}` be independent with law `ν ⊗ ρ^{⊗ℕ}` and let the level-`ℓ` cost have mean
`C_ℓ ≤ c₃ 4^ℓ`.  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` for which the MLMC estimator of `E_Z[f(E_W[g(Z, W)])]` has a square-integrable error
with mean square `< ε²`, and expected cost `≤ c₄ ε⁻² (log ε)²`: Theorem 1
(`giles_theorem1_corrections`) with `β = γ = 2`.  The exponent of `log ε` printed in the paper,
`−2`, should be `2` (see `nested_complexity`). -/
theorem nested_sde_mlmc_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f f' : ℝ → ℝ} {K : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ cₛ c_w : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ)
    {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g))
    (hg4 : Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ))
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, gh ℓ z v ∂ρ - ∫ v, g z v ∂ρ| ≤ c_w)
    (ω : ℕ × ℕ → Ω → 𝒵 × (ℕ → 𝒲)) (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ))
    (hind : iIndepFun ω μ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * 4 ^ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedSdeDelta f gh) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2) μ ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedSdeDelta f gh) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hfm : Measurable f := hfd.continuous.measurable
  have hPl : ∀ ℓ, Integrable (nestedSdeP f gh ℓ) (nestedLaw ν ρ) := fun ℓ =>
    (memLp_nestedP ν ρ hf hf' (hgh ℓ) (hgh4 ℓ) ℓ).integrable one_le_two
  have hP : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    (memLp_nestedTarget ν ρ hf hf' hg hg4).integrable one_le_two
  have hΔm : ∀ ℓ, Measurable (nestedSdeDelta f gh ℓ) := measurable_nestedSdeDelta hfm hgh
  have hΔ : ∀ ℓ, MemLp (nestedSdeDelta f gh ℓ) 2 (nestedLaw ν ρ) := fun ℓ => by
    cases ℓ with
    | zero => exact memLp_nestedP ν ρ hf hf' (hgh 0) (hgh4 0) 0
    | succ ℓ => exact (nested_sde_variance_rate ν ρ hf hf' hgh hgh4 hm₄ hs ℓ).1
  -- (i) the bias, `α = 1`
  obtain ⟨B₁, hB₁⟩ : ∃ B, B =
      K / 2 * (1 + 16 * m₄) + c_w * ∫ z, |f' (∫ v, g z v ∂ρ)| ∂ν + K / 2 * c_w ^ 2 := ⟨_, rfl⟩
  have h_i : ∀ ℓ : ℕ, |∫ y, nestedSdeP f gh ℓ y - nestedTarget f g ρ y ∂(nestedLaw ν ρ)| ≤
      (|B₁| + 1) * (2 : ℝ) ^ (-((1 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hb := nested_sde_bias_rate ν ρ hf hf' hgh hgh4 hm₄ hg hg4 hw ℓ
    rw [← hB₁] at hb
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast 2 ℓ,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    linarith [le_abs_self B₁]
  -- (iii) the variance, `β = 2`
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = 3 * ((K / 8) ^ 2 * (224 * m₄)) +
      3 / 2 * (8 * (|f' 0| ^ 4 + K ^ 4 * m₄) + (1 + K ^ 2 / 2) * cₛ) := ⟨_, rfl⟩
  have h_iii : ∀ ℓ : ℕ, variance (nestedSdeDelta f gh ℓ) (nestedLaw ν ρ) ≤
      (variance (nestedSdeDelta f gh 0) (nestedLaw ν ρ) + 4 * |B₂| + 1) *
        (2 : ℝ) ^ (-((2 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hv0 := variance_nonneg (nestedSdeDelta f gh 0) (nestedLaw ν ρ)
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_comm (2 : ℝ) (ℓ : ℝ),
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (ℓ : ℝ) 2, Real.rpow_natCast 2 ℓ,
      Real.rpow_two ((2 : ℝ) ^ ℓ), ← div_eq_mul_inv]
    cases ℓ with
    | zero =>
      rw [pow_zero, one_pow, div_one]
      linarith [abs_nonneg B₂]
    | succ ℓ =>
      have hv : variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) ≤
          ∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) := by
        simpa only [Pi.pow_apply] using
          variance_le_expectation_sq (hΔm (ℓ + 1)).aestronglyMeasurable
      have hr := (nested_sde_variance_rate ν ρ hf hf' hgh hgh4 hm₄ hs ℓ).2
      rw [← hB₂] at hr
      have h4 : variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) * ((2 : ℝ) ^ ℓ) ^ 2 ≤
          (∫ p, nestedSdeDelta f gh (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ)) * ((2 : ℝ) ^ ℓ) ^ 2 :=
        mul_le_mul_of_nonneg_right hv (by positivity)
      have e : variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) * ((2 : ℝ) ^ (ℓ + 1)) ^ 2 =
          4 * (variance (nestedSdeDelta f gh (ℓ + 1)) (nestedLaw ν ρ) * ((2 : ℝ) ^ ℓ) ^ 2) := by
        rw [pow_succ]
        ring
      rw [le_div_iff₀ (by positivity), e]
      rw [mul_comm] at hr
      linarith [le_abs_self B₂]
  -- (iv) the cost, `γ = 2`
  have h_iv : ∀ ℓ : ℕ, C ℓ ≤ c₃ * (2 : ℝ) ^ ((2 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, Real.rpow_natCast]
    norm_num
    exact hC ℓ
  have hc₁ : 0 < |B₁| + 1 := by positivity
  have hc₂ : 0 < variance (nestedSdeDelta f gh 0) (nestedLaw ν ρ) + 4 * |B₂| + 1 := by
    have := variance_nonneg (nestedSdeDelta f gh 0) (nestedLaw ν ρ)
    positivity
  have hαβγ : min (2 : ℝ) 2 / 2 ≤ 1 := by norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_corrections (nestedTarget f g ρ) (nestedSdeP f gh)
    (nestedSdeDelta f gh) ω cost C one_pos two_pos two_pos hc₁ hc₂ hc₃ hαβγ hω hind hP hPl hΔm
    hΔ hcost hcostC h_i (integral_nestedSdeDelta ν ρ f gh hPl) h_iii h_iv
  -- the quantity of interest is `E_Z[f(E_W[g(Z, W)])]`
  have hGm : Measurable fun z => ∫ v, g z v ∂ρ := (integrable_condMean_pow_four ν ρ hg hg4).1
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hPint : ∫ y, nestedTarget f g ρ y ∂(nestedLaw ν ρ) = ∫ z, f (∫ v, g z v ∂ρ) ∂ν :=
    integral_comp_of_measurePreserving hfst (hfm.comp hGm).aestronglyMeasurable
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := h ε hε hε1
  rw [hPint] at hmse
  rw [complexityBound_of_eq rfl ε] at hcost'
  exact ⟨L, N, hN, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω hΔ ℓ (N ℓ)).sub
    (memLp_const _)).integrable_sq, hmse, hcost'⟩

end Discretised

/-! ### §9.1: a piecewise linear `f` (Bujok, Hambly and Reisinger), `β = 1.5` -/

/-- The second difference `Φ = max(A₁ − k, 0) + max(A₂ − k, 0) − 2 max(½(A₁ + A₂) − k, 0)` of the
hinge at `k` satisfies `0 ≤ Φ ≤ ½|A₁ − A₂|`, and `Φ = 0` if `A₁, A₂` lie on the same side of `k`. -/
lemma hinge_second_diff (k A₁ A₂ : ℝ) :
    0 ≤ max (A₁ - k) 0 + max (A₂ - k) 0 - 2 * max ((A₁ + A₂) / 2 - k) 0 ∧
      max (A₁ - k) 0 + max (A₂ - k) 0 - 2 * max ((A₁ + A₂) / 2 - k) 0 ≤ |A₁ - A₂| / 2 ∧
      (0 ≤ (A₁ - k) * (A₂ - k) →
        max (A₁ - k) 0 + max (A₂ - k) 0 - 2 * max ((A₁ + A₂) / 2 - k) 0 = 0) := by
  rcases abs_cases (A₁ - A₂) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;>
    simp only [max_def] <;> split_ifs <;>
    refine ⟨by linarith, by linarith, fun h => by nlinarith⟩

/-- **The antithetic difference for a piecewise linear `f`** (Giles 2015, §9.1, p. 58: "Bujok et al.
(2013) used multilevel nested simulation for a financial credit derivative application. In their
case, the function `f` was piecewise linear, not twice differentiable, and so the rate of variance
convergence was slightly lower, with `β = 1.5`").  Let `f(x) = a₀ + a₁x + c max(x − k, 0)`, which
covers every continuous piecewise linear `f` with one kink at `k` (e.g. `max(x − k, 0)` and
`|x − k|`).  Then `D = f(½(A₁ + A₂)) − ½ f(A₁) − ½ f(A₂)` vanishes unless `k` lies strictly between
`A₁` and `A₂`, and `|D| ≤ (|c|/4)|A₁ − A₂|`; the constant `¼` is attained at `A₁ = k − d`,
`A₂ = k + d`.  So `D² ≤ (c²/16)(A₁ − A₂)² 1{k between A₁ and A₂}`. -/
theorem antithetic_kink {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) (A₁ A₂ : ℝ) :
    (0 ≤ (A₁ - k) * (A₂ - k) → f ((A₁ + A₂) / 2) - f A₁ / 2 - f A₂ / 2 = 0) ∧
      |f ((A₁ + A₂) / 2) - f A₁ / 2 - f A₂ / 2| ≤ |c| / 4 * |A₁ - A₂| ∧
      ∀ d : ℝ, |f ((k - d + (k + d)) / 2) - f (k - d) / 2 - f (k + d) / 2| =
        |c| / 4 * |k - d - (k + d)| := by
  have e : ∀ x y : ℝ, f ((x + y) / 2) - f x / 2 - f y / 2 =
      -(c / 2) * (max (x - k) 0 + max (y - k) 0 - 2 * max ((x + y) / 2 - k) 0) := fun x y => by
    simp only [hf]
    ring
  obtain ⟨h0, h1, h2⟩ := hinge_second_diff k A₁ A₂
  refine ⟨fun h => by rw [e, h2 h, mul_zero], ?_, fun d => ?_⟩
  · rw [e, abs_mul, abs_neg, abs_div, abs_two, abs_of_nonneg h0]
    calc |c| / 2 * (max (A₁ - k) 0 + max (A₂ - k) 0 - 2 * max ((A₁ + A₂) / 2 - k) 0)
        ≤ |c| / 2 * (|A₁ - A₂| / 2) := by gcongr
      _ = |c| / 4 * |A₁ - A₂| := by ring
  · rw [e, show k - d - k = -d by ring, show k + d - k = d by ring,
      show (k - d + (k + d)) / 2 - k = 0 by ring, show k - d - (k + d) = -(2 * d) by ring,
      max_self, add_comm (max (-d) 0), max_zero_add_max_neg_zero_eq_abs_self]
    simp only [abs_mul, abs_neg, abs_div, abs_abs, abs_two, mul_zero, sub_zero]
    ring

/-- **The pathwise bounds behind `β = 1.5`** (Giles 2015, §9.1, p. 58): for `f` with one kink at
`k`, `D = f(½(A₁ + A₂)) − ½ f(A₁) − ½ f(A₂)` satisfies `D² ≤ (c²/16)(A₁ − A₂)²` and, for every `G`,
`(G − k)² D² ≤ (c²/2)((A₁ − G)⁴ + (A₂ − G)⁴)`: `D` vanishes unless `k` lies between `A₁` and `A₂`,
and then `|G − k| ≤ |A₁ − G| + |A₂ − G|`. -/
lemma sq_antithetic_kink_le {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) (G A₁ A₂ : ℝ) :
    (f ((A₁ + A₂) / 2) - f A₁ / 2 - f A₂ / 2) ^ 2 ≤ c ^ 2 / 16 * (A₁ - A₂) ^ 2 ∧
      (G - k) ^ 2 * (f ((A₁ + A₂) / 2) - f A₁ / 2 - f A₂ / 2) ^ 2 ≤
        c ^ 2 / 2 * ((A₁ - G) ^ 4 + (A₂ - G) ^ 4) := by
  obtain ⟨h0, h1, -⟩ := antithetic_kink hf A₁ A₂
  set Y := f ((A₁ + A₂) / 2) - f A₁ / 2 - f A₂ / 2
  have hY2 : Y ^ 2 ≤ c ^ 2 / 16 * (A₁ - A₂) ^ 2 := by
    calc Y ^ 2 = |Y| ^ 2 := (sq_abs _).symm
      _ ≤ (|c| / 4 * |A₁ - A₂|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = c ^ 2 / 16 * (A₁ - A₂) ^ 2 := by rw [mul_pow, div_pow, sq_abs, sq_abs]; ring
  refine ⟨hY2, ?_⟩
  have hR : 0 ≤ c ^ 2 / 2 * ((A₁ - G) ^ 4 + (A₂ - G) ^ 4) := by positivity
  by_cases hk : 0 ≤ (A₁ - k) * (A₂ - k)
  · rw [h0 hk]
    simpa using hR
  -- `k` lies strictly between `A₁` and `A₂`
  rw [not_le] at hk
  set S := |A₁ - G| + |A₂ - G|
  have hS : |G - k| ≤ S := by
    have a1 := le_abs_self (A₁ - G)
    have a2 := neg_abs_le (A₁ - G)
    have a3 := le_abs_self (A₂ - G)
    have a4 := neg_abs_le (A₂ - G)
    rcases mul_neg_iff.1 hk with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact abs_le.2 ⟨by linarith, by linarith⟩
    · exact abs_le.2 ⟨by linarith, by linarith⟩
  have hD : |A₁ - A₂| ≤ S := by
    have := abs_sub (A₁ - G) (A₂ - G)
    rwa [sub_sub_sub_cancel_right] at this
  have hS4 : S ^ 4 ≤ 8 * ((A₁ - G) ^ 4 + (A₂ - G) ^ 4) := by
    have h := sub_pow_four_le (|A₁ - G|) (-|A₂ - G|)
    rw [sub_neg_eq_add, neg_pow, show ((-1 : ℝ)) ^ 4 = 1 by norm_num, one_mul] at h
    have e1 : |A₁ - G| ^ 4 = (A₁ - G) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    have e2 : |A₂ - G| ^ 4 = (A₂ - G) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    rwa [e1, e2] at h
  have hGk : (G - k) ^ 2 ≤ S ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hS 2
  have hDk : (A₁ - A₂) ^ 2 ≤ S ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hD 2
  calc (G - k) ^ 2 * Y ^ 2 ≤ S ^ 2 * (c ^ 2 / 16 * (A₁ - A₂) ^ 2) :=
        mul_le_mul hGk hY2 (sq_nonneg _) (sq_nonneg _)
    _ ≤ S ^ 2 * (c ^ 2 / 16 * S ^ 2) := by gcongr
    _ = c ^ 2 / 16 * S ^ 4 := by ring
    _ ≤ c ^ 2 / 16 * (8 * ((A₁ - G) ^ 4 + (A₂ - G) ^ 4)) := by gcongr
    _ = c ^ 2 / 2 * ((A₁ - G) ^ 4 + (A₂ - G) ^ 4) := by ring

/-- A piecewise linear function with one kink is continuous. -/
lemma continuous_kink {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) : Continuous f := by
  have e : f = fun x => a₀ + a₁ * x + c * max (x - k) 0 := funext hf
  rw [e]
  fun_prop

/-- A piecewise linear `f` with one kink is Lipschitz with constant `|a₁| + |c|`. -/
lemma abs_kink_sub_le {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) (x y : ℝ) :
    |f x - f y| ≤ (|a₁| + |c|) * |x - y| := by
  have e : f x - f y = a₁ * (x - y) + c * (max (x - k) 0 - max (y - k) 0) := by
    rw [hf, hf]
    ring
  have h := abs_max_sub_max_le_abs (x - k) (y - k) 0
  rw [sub_sub_sub_cancel_right] at h
  rw [e]
  calc |a₁ * (x - y) + c * (max (x - k) 0 - max (y - k) 0)|
      ≤ |a₁| * |x - y| + |c| * |max (x - k) 0 - max (y - k) 0| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ |a₁| * |x - y| + |c| * |x - y| := by gcongr
    _ = (|a₁| + |c|) * |x - y| := by ring

/-- A piecewise linear `f` with one kink grows at most linearly:
`f(x)² ≤ 2 f(0)² + 2 (|a₁| + |c|)² x²`. -/
lemma sq_kink_le {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) (x : ℝ) :
    f x ^ 2 ≤ 2 * f 0 ^ 2 + 2 * (|a₁| + |c|) ^ 2 * x ^ 2 := by
  have h := abs_kink_sub_le hf x 0
  rw [sub_zero] at h
  have h1 : |f x| ≤ |f 0| + (|a₁| + |c|) * |x| := by
    have := abs_sub_abs_le_abs_sub (f x) (f 0)
    linarith
  have h2 : f x ^ 2 ≤ (|f 0| + (|a₁| + |c|) * |x|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [sq_nonneg (|f 0| - (|a₁| + |c|) * |x|), sq_abs (f 0), sq_abs x]

/-- `f(X) ∈ L²` for a piecewise linear `f` with one kink and `X ∈ L²`. -/
lemma memLp_two_kink_comp {α : Type*} [MeasurableSpace α] {μ' : Measure α} [IsFiniteMeasure μ']
    {f : ℝ → ℝ} {a₀ a₁ c k : ℝ} (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {X : α → ℝ}
    (hX : Measurable X) (hX2 : Integrable (fun ω => X ω ^ 2) μ') :
    MemLp (fun ω => f (X ω)) 2 μ' := by
  have hfX : Measurable fun ω => f (X ω) := (continuous_kink hf).measurable.comp hX
  refine (memLp_two_iff_integrable_sq hfX.aestronglyMeasurable).2 ?_
  refine ((integrable_const (2 * f 0 ^ 2)).add (hX2.const_mul (2 * (|a₁| + |c|) ^ 2))).mono'
    (hfX.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_kink_le hf (X ω)

/-- **The small-ball estimate behind `β = 1.5`** (Giles 2015, §9.1, p. 58).  Let `F ≥ 0` be
a.e.-measurable with `F ≤ A` and `u² F ≤ B` a.e., and let `u` put little mass near `0`:
`ν{|u| ≤ t} ≤ c t` for every `t > 0`, `c ≥ 0`.  Then `∫ F dν ≤ 2 c √(A B)`.  Proof: the layer-cake
formula for `F = (√F)²`, with `ν{t ≤ √F} ≤ ν{|u| ≤ √B/t} ≤ c √B/t` for `0 < t ≤ √A` and
`ν{t ≤ √F} = 0` for `t > √A`. -/
lemma integral_le_of_small_ball {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {F u : α → ℝ} {A B c : ℝ} (hFm : AEMeasurable F ν) (hF0 : ∀ᵐ z ∂ν, 0 ≤ F z)
    (hFA : ∀ᵐ z ∂ν, F z ≤ A) (hFB : ∀ᵐ z ∂ν, u z ^ 2 * F z ≤ B) (hc : 0 ≤ c)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |u z| ≤ t} ≤ ENNReal.ofReal (c * t)) :
    ∫ z, F z ∂ν ≤ 2 * c * Real.sqrt (A * B) := by
  by_cases hA : A < 0
  · -- then `ν = 0`
    have h0 : ν Set.univ = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hF0, hFA] with z h1 h2
      linarith
    rw [Measure.measure_univ_eq_zero.1 h0, integral_zero_measure]
    positivity
  rw [not_lt] at hA
  by_cases hB : B < 0
  · have h0 : ν Set.univ = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hF0, hFB] with z h1 h2
      nlinarith [sq_nonneg (u z), mul_nonneg (sq_nonneg (u z)) h1]
    rw [Measure.measure_univ_eq_zero.1 h0, integral_zero_measure]
    positivity
  rw [not_lt] at hB
  have hR : 0 ≤ 2 * c * Real.sqrt (A * B) := by positivity
  -- the small-ball bound also holds for the radius `0`
  have hball' : ∀ r : ℝ, 0 ≤ r → ν {z | |u z| ≤ r} ≤ ENNReal.ofReal (c * r) := by
    intro r hr
    rcases hr.lt_or_eq with hr | hr
    · exact hball r hr
    · subst hr
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      have hs : (0 : ℝ) < ε / (c + 1) := div_pos hε (by linarith)
      calc ν {z | |u z| ≤ 0} ≤ ν {z | |u z| ≤ ε / (c + 1)} :=
            measure_mono fun z (hz : |u z| ≤ 0) => (show |u z| ≤ ε / (c + 1) by linarith)
        _ ≤ ENNReal.ofReal (c * (ε / (c + 1))) := hball _ hs
        _ ≤ ENNReal.ofReal ε := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [mul_div_assoc', div_le_iff₀ (by linarith)]
            nlinarith [NNReal.coe_nonneg ε]
        _ = ENNReal.ofReal (c * 0) + ε := by simp
  rw [integral_eq_lintegral_of_nonneg_ae hF0 hFm.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hR ?_
  -- the layer-cake formula for `F = (√F)²`
  have hlc := lintegral_comp_eq_lintegral_meas_le_mul ν (f := fun z => Real.sqrt (F z))
    (g := fun t => 2 * t) (Eventually.of_forall fun z => Real.sqrt_nonneg _)
    hFm.sqrt (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => by
      positivity))
  have hsq : ∀ s : ℝ, ∫ t in (0 : ℝ)..s, 2 * t = s ^ 2 := fun s => by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  simp only [hsq] at hlc
  have hL : ∫⁻ z, ENNReal.ofReal (F z) ∂ν = ∫⁻ z, ENNReal.ofReal (Real.sqrt (F z) ^ 2) ∂ν :=
    lintegral_congr_ae (hF0.mono fun z hz => by simp only [Real.sq_sqrt hz])
  rw [hL, hlc]
  -- the integrand is at most `2 c √B` on `(0, √A]` and vanishes beyond
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), ν {a | t ≤ Real.sqrt (F a)} * ENNReal.ofReal (2 * t) ≤
      (Set.Ioc 0 (Real.sqrt A)).indicator (fun _ => ENNReal.ofReal (2 * c * Real.sqrt B)) t := by
    intro t (ht : 0 < t)
    by_cases htA : t ≤ Real.sqrt A
    · rw [Set.indicator_of_mem (show t ∈ Set.Ioc 0 (Real.sqrt A) from ⟨ht, htA⟩)]
      have hsub : {a | t ≤ Real.sqrt (F a)} ≤ᵐ[ν] {z | |u z| ≤ Real.sqrt B / t} := by
        filter_upwards [hF0, hFB] with z h0 h1 hz
        have hz' : t ≤ Real.sqrt (F z) := hz
        have ht2 : t ^ 2 ≤ F z := by
          have := pow_le_pow_left₀ ht.le hz' 2
          rwa [Real.sq_sqrt h0] at this
        have h2 : (|u z| * t) ^ 2 ≤ B := by
          rw [mul_pow, sq_abs]
          calc u z ^ 2 * t ^ 2 ≤ u z ^ 2 * F z := mul_le_mul_of_nonneg_left ht2 (sq_nonneg _)
            _ ≤ B := h1
        have h3 : |u z| * t ≤ Real.sqrt B := Real.le_sqrt_of_sq_le h2
        show |u z| ≤ Real.sqrt B / t
        rw [le_div_iff₀ ht]
        exact h3
      calc ν {a | t ≤ Real.sqrt (F a)} * ENNReal.ofReal (2 * t)
          ≤ ENNReal.ofReal (c * (Real.sqrt B / t)) * ENNReal.ofReal (2 * t) := by
            gcongr
            exact (measure_mono_ae hsub).trans (hball' _ (by positivity))
        _ = ENNReal.ofReal (2 * c * Real.sqrt B) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ioc 0 (Real.sqrt A) from fun h => htA h.2)]
      rw [not_le] at htA
      have h0 : ν {a | t ≤ Real.sqrt (F a)} = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hFA] with z hz hzs
        have := Real.sqrt_le_sqrt hz
        linarith
      rw [h0, zero_mul]
  calc ∫⁻ t in Set.Ioi 0, ν {a | t ≤ Real.sqrt (F a)} * ENNReal.ofReal (2 * t)
      ≤ ∫⁻ t in Set.Ioi 0,
          (Set.Ioc 0 (Real.sqrt A)).indicator (fun _ => ENNReal.ofReal (2 * c * Real.sqrt B)) t :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ ≤ ∫⁻ t, (Set.Ioc 0 (Real.sqrt A)).indicator
          (fun _ => ENNReal.ofReal (2 * c * Real.sqrt B)) t :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (2 * c * Real.sqrt B) * ENNReal.ofReal (Real.sqrt A) := by
        rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (2 * c * Real.sqrt (A * B)) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.sqrt_mul hA]
        ring_nf

/-- **A bounded density gives the small-ball bound** (Giles 2015, §9.1, p. 58, the setting of Bujok
et al.: `E_W[g(Z, W)]` has a bounded density near the kink).  If the law of `G` has a density at
most `ρ_max` on `[k − r, k + r]`, i.e. `ν(G⁻¹ s) ≤ ρ_max |s|` for measurable `s ⊆ [k − r, k + r]`,
then `ν{|G − k| ≤ t} ≤ max(2ρ_max, 1/r) t` for every `t > 0`. -/
lemma small_ball_of_density {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {G : α → ℝ} {k r ρ_max : ℝ} (hr : 0 < r)
    (hdens : ∀ s ⊆ Set.Icc (k - r) (k + r), MeasurableSet s →
      ν (G ⁻¹' s) ≤ ENNReal.ofReal ρ_max * volume s) (t : ℝ) (ht : 0 < t) :
    ν {z | |G z - k| ≤ t} ≤ ENNReal.ofReal (max (2 * ρ_max) (1 / r) * t) := by
  have hset : {z | |G z - k| ≤ t} = G ⁻¹' Set.Icc (k - t) (k + t) := by
    ext z
    show |G z - k| ≤ t ↔ k - t ≤ G z ∧ G z ≤ k + t
    rw [abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  rw [hset]
  by_cases htr : t ≤ r
  · have hsub : Set.Icc (k - t) (k + t) ⊆ Set.Icc (k - r) (k + r) :=
      Set.Icc_subset_Icc (by linarith) (by linarith)
    calc ν (G ⁻¹' Set.Icc (k - t) (k + t))
        ≤ ENNReal.ofReal ρ_max * volume (Set.Icc (k - t) (k + t)) :=
          hdens _ hsub measurableSet_Icc
      _ = ENNReal.ofReal (ρ_max * (2 * t)) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul' (by linarith)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (max (2 * ρ_max) (1 / r) * t) := by
          apply ENNReal.ofReal_le_ofReal
          have := le_max_left (2 * ρ_max) (1 / r)
          nlinarith
  · rw [not_le] at htr
    calc ν (G ⁻¹' Set.Icc (k - t) (k + t)) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (max (2 * ρ_max) (1 / r) * t) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : 1 ≤ 1 / r * t := by
            rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hr]
            linarith
          have := le_max_right (2 * ρ_max) (1 / r)
          nlinarith

/-- A small-ball bound `ν{|u| ≤ t} ≤ c t` for all `t > 0` under a probability measure forces
`c ≥ 0` (else every `ν{|u| ≤ t}` would vanish, and so would `ν(univ)`). -/
lemma nonneg_of_small_ball {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {u : α → ℝ} {c : ℝ}
    (hball : ∀ t : ℝ, 0 < t → ν {z | |u z| ≤ t} ≤ ENNReal.ofReal (c * t)) : 0 ≤ c := by
  by_contra hc
  rw [not_le] at hc
  have h0 : ∀ n : ℕ, ν {z | |u z| ≤ (n : ℝ) + 1} = 0 := fun n => by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine le_antisymm ((hball _ (by positivity)).trans_eq
      (ENNReal.ofReal_eq_zero.2 (by nlinarith [hn]))) zero_le
  have hU : (Set.univ : Set α) = ⋃ n : ℕ, {z | |u z| ≤ (n : ℝ) + 1} := by
    refine (Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 ⟨⌈|u z|⌉₊, ?_⟩).symm
    show |u z| ≤ (⌈|u z|⌉₊ : ℝ) + 1
    linarith [Nat.le_ceil |u z|]
  have h1 : ν Set.univ = 0 := by
    rw [hU]
    exact measure_iUnion_null h0
  simp at h1

section Kink

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- **Bounded conditional moments give a joint moment** (Giles 2015, §9.1): if
`E_W[g(z, W)⁴] ≤ m₄` for `ν`-a.e. `z`, then `E[g(Z, W)⁴] < ∞`. -/
lemma integrable_pow_four_of_fiber {g : 𝒵 → 𝒲 → ℝ} (hg : Measurable (Function.uncurry g))
    {m₄ : ℝ} (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧ ∫ v, g z v ^ 4 ∂ρ ≤ m₄) :
    Integrable (fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4) (ν.prod ρ) := by
  have hm : Measurable fun p : 𝒵 × 𝒲 => g p.1 p.2 ^ 4 := hg.pow_const 4
  refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨hfib.mono fun z hz => hz.1, ?_⟩
  refine (integrable_const m₄).mono'
    (hm.norm.stronglyMeasurable.integral_prod_right' (ν := ρ)).aestronglyMeasurable
    (hfib.mono fun z hz => ?_)
  have e : ∫ v, ‖g z v ^ 4‖ ∂ρ = ∫ v, g z v ^ 4 ∂ρ :=
    integral_congr_ae (Eventually.of_forall fun v => Real.norm_of_nonneg (by positivity))
  rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _), e]
  exact hz.2

/-- **`β = 1.5` for a piecewise linear `f`** (Giles 2015, §9.1, p. 58: "In their case, the function
`f` was piecewise linear, not twice differentiable, and so the rate of variance convergence was
slightly lower, with `β = 1.5`").  Let `f(x) = a₀ + a₁x + c max(x − k, 0)`, let the conditional
fourth moments be bounded, `E_W[g(z, W)⁴] ≤ m₄` for `ν`-a.e. `z`, and let the conditional mean put
little mass near the kink: `ν{|E_W[g(Z, W)] − k| ≤ t} ≤ c_d t` for all `t > 0` (true if
`E_W[g(Z, W)]` has a bounded density near `k`: `nested_kink_variance_rate_of_density`).  Then the
§9.1 correction `Y_{ℓ+1}` (`2^ℓ` coarse inner samples) is square-integrable and
`2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ 2 c_d c² √(8 m₄ (1 + 16 m₄))`, i.e. `V_ℓ = O(M_ℓ^{−3/2})`.  Proof:
`Y_{ℓ+1}` vanishes unless `k` lies between the two coarse inner means, which forces `E_W[g(z, W)]`
within the inner sampling error of `k`; for each outer sample `E_W[Y²] = O(M⁻¹)` and
`(E_W[g(z, W)] − k)² E_W[Y²] = O(M⁻²)` (`sq_antithetic_kink_le`), and the small-ball bound turns
these into `O(M^{−3/2})` (`integral_le_of_small_ball`).  The paper states no hypotheses for this
case; the argument needs the small-ball bound and bounded conditional fourth moments.  Bounding the
raw moments `E_W[g(z, W)⁴]` rather than the centred ones is a simplification: it also bounds the
conditional mean `E_W[g(z, W)]`, which excludes, e.g., `g(Z, W) = Z + W` with a Gaussian outer
variable `Z`.  A bound `P(k between A_M and A′_M) = O(M^{−1/2})`
on the probability of straddling the kink, with fourth moments, would not be enough: Cauchy–Schwarz
then gives only `E[Y²] = O(M^{−5/4})`, and `(A_M − A′_M)² = M^{−3/4}` on an event of probability
`M^{−1/2}` (and `0` elsewhere) attains it; this is why the argument conditions on the outer
sample. -/
theorem nested_kink_variance_rate {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g)) {m₄ c_d : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧ ∫ v, g z v ^ 4 ∂ρ ≤ m₄)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (ℓ : ℕ) :
    MemLp (nestedDelta f g (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        2 * c_d * c ^ 2 * Real.sqrt (8 * m₄ * (1 + 16 * m₄)) := by
  have hfm : Measurable f := (continuous_kink hf).measurable
  obtain ⟨z₀, hz₀⟩ := hfib.exists
  have hm₄ : 0 ≤ m₄ := le_trans (integral_nonneg fun v => by positivity) hz₀.2
  set M : ℕ := 2 ^ ℓ with hMdef
  have hM : 0 < M := by positivity
  have hMr : (M : ℝ) = (2 : ℝ) ^ ℓ := by rw [hMdef]; push_cast; ring
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.2 hM
  -- the two coarse inner means and the conditional mean
  set Y := nestedDelta f g (ℓ + 1)
  have hYeq : ∀ p : 𝒵 × (ℕ → 𝒲), Y p =
      f ((innerMean g M p.1 p.2 + innerMean g M p.1 (shiftSeq M p.2)) / 2) -
        f (innerMean g M p.1 p.2) / 2 - f (innerMean g M p.1 (shiftSeq M p.2)) / 2 :=
    fun p => nestedDelta_succ_eq f g ℓ p
  have hYm : Measurable Y := measurable_nestedDelta hfm hg (ℓ + 1)
  -- the fibre bounds, for almost every outer sample
  have hfibY : ∀ᵐ z ∂ν, Integrable (fun w => Y (z, w) ^ 2) (innerLaw ρ) ∧
      ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ) ≤ c ^ 2 * (1 + 16 * m₄) / (8 * M) ∧
      (∫ v, g z v ∂ρ - k) ^ 2 * ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ) ≤ 64 * c ^ 2 * m₄ / M ^ 2 := by
    filter_upwards [hfib] with z ⟨hz4, hzm⟩
    have hgz : Measurable (g z) := hg.of_uncurry_left
    obtain ⟨i4, h2, -, -, -, -⟩ := fiber_nested_moments ρ g z hgz hz4 hM
    obtain ⟨j4, h4⟩ := fiber_centred_fourth_moment ρ g z hgz hz4 hM
    set G := ∫ v, g z v ∂ρ
    have hA : Measurable fun w : ℕ → 𝒲 => innerMean g M z w := measurable_innerMean_right hgz M
    have hA' : Measurable fun w : ℕ → 𝒲 => innerMean g M z (shiftSeq M w) :=
      hA.comp (measurable_shiftSeq M)
    have hsh : MeasurePreserving (shiftSeq (𝒲 := 𝒲) M) (innerLaw ρ) (innerLaw ρ) :=
      measurePreserving_shiftSeq ρ M
    have hD2 : Integrable (fun w => (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2)
        (innerLaw ρ) := integrable_pow_of_pow_four (hA.sub hA') i4 (by norm_num)
    have j4' : Integrable (fun w => (innerMean g M z (shiftSeq M w) - G) ^ 4) (innerLaw ρ) :=
      hsh.integrable_comp_of_integrable j4
    have e4' : ∫ w, (innerMean g M z (shiftSeq M w) - G) ^ 4 ∂(innerLaw ρ) =
        ∫ w, (innerMean g M z w - G) ^ 4 ∂(innerLaw ρ) :=
      integral_comp_of_measurePreserving hsh j4.aestronglyMeasurable
    have hYz : Measurable fun w => Y (z, w) := hYm.comp measurable_prodMk_left
    have hP1 : ∀ w, Y (z, w) ^ 2 ≤ c ^ 2 / 16 *
        (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2 := fun w => by
      rw [hYeq]
      exact (sq_antithetic_kink_le hf G _ _).1
    have hP2 : ∀ w, (G - k) ^ 2 * Y (z, w) ^ 2 ≤ c ^ 2 / 2 *
        ((innerMean g M z w - G) ^ 4 + (innerMean g M z (shiftSeq M w) - G) ^ 4) := fun w => by
      rw [hYeq]
      exact (sq_antithetic_kink_le hf G _ _).2
    have hY2 : Integrable (fun w => Y (z, w) ^ 2) (innerLaw ρ) :=
      (hD2.const_mul (c ^ 2 / 16)).mono' (hYz.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun w => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact hP1 w)
    refine ⟨hY2, ?_, ?_⟩
    · calc ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ)
          ≤ ∫ w, c ^ 2 / 16 * (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2
              ∂(innerLaw ρ) := integral_mono hY2 (hD2.const_mul _) hP1
        _ = c ^ 2 / 16 * ∫ w, (innerMean g M z w - innerMean g M z (shiftSeq M w)) ^ 2
              ∂(innerLaw ρ) := integral_const_mul _ _
        _ ≤ c ^ 2 / 16 * (2 * (1 + 16 * m₄) / M) := by
            gcongr
            rw [le_div_iff₀ hM0, mul_comm]
            linarith
        _ = c ^ 2 * (1 + 16 * m₄) / (8 * M) := by field_simp; ring
    · have i2 : Integrable (fun w => c ^ 2 / 2 *
          ((innerMean g M z w - G) ^ 4 + (innerMean g M z (shiftSeq M w) - G) ^ 4))
          (innerLaw ρ) := (j4.add j4').const_mul _
      calc (G - k) ^ 2 * ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ)
          = ∫ w, (G - k) ^ 2 * Y (z, w) ^ 2 ∂(innerLaw ρ) := (integral_const_mul _ _).symm
        _ ≤ ∫ w, c ^ 2 / 2 *
              ((innerMean g M z w - G) ^ 4 + (innerMean g M z (shiftSeq M w) - G) ^ 4)
              ∂(innerLaw ρ) := integral_mono (hY2.const_mul _) i2 hP2
        _ = c ^ 2 * ∫ w, (innerMean g M z w - G) ^ 4 ∂(innerLaw ρ) := by
            rw [integral_const_mul, integral_add j4 j4', e4']
            ring
        _ ≤ c ^ 2 * (64 * m₄ / M ^ 2) := by
            gcongr
            rw [le_div_iff₀ (by positivity), mul_comm]
            linarith
        _ = 64 * c ^ 2 * m₄ / M ^ 2 := by ring
  -- integrability on the product and Fubini
  obtain ⟨hY2int, -⟩ := integrable_of_fiber_bound ν ρ (F := fun p => Y p ^ 2)
    (hYm.pow_const 2) (fun p => sq_nonneg _) (integrable_const (c ^ 2 * (1 + 16 * m₄) / (8 * M)))
    (hfibY.mono fun z hz => ⟨hz.1, hz.2.1⟩)
  have hMemLp : MemLp Y 2 (nestedLaw ν ρ) :=
    (memLp_two_iff_integrable_sq hYm.aestronglyMeasurable).2 hY2int
  refine ⟨hMemLp, ?_⟩
  have hFub : ∫ p, Y p ^ 2 ∂(nestedLaw ν ρ) = ∫ z, ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ) ∂ν :=
    integral_prod _ hY2int
  have hFm : AEMeasurable (fun z => ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ)) ν :=
    ((hYm.pow_const 2).stronglyMeasurable.integral_prod_right' (ν := innerLaw ρ)).measurable
      |>.aemeasurable
  have key := integral_le_of_small_ball (ν := ν) (F := fun z => ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ))
    (u := fun z => ∫ v, g z v ∂ρ - k) hFm
    (Eventually.of_forall fun z => integral_nonneg fun w => sq_nonneg _)
    (hfibY.mono fun z hz => hz.2.1) (hfibY.mono fun z hz => hz.2.2)
    (nonneg_of_small_ball hball) hball
  rw [hFub]
  -- the constant: `2^{3ℓ/2} √(A B) = c² √(8 m₄ (1 + 16 m₄))`
  set r : ℝ := (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = (M : ℝ) ^ 3 := by
    rw [hr, hMr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have hAB : r * Real.sqrt (c ^ 2 * (1 + 16 * m₄) / (8 * M) * (64 * c ^ 2 * m₄ / M ^ 2)) =
      c ^ 2 * Real.sqrt (8 * m₄ * (1 + 16 * m₄)) := by
    have e : c ^ 2 * (1 + 16 * m₄) / (8 * M) * (64 * c ^ 2 * m₄ / M ^ 2) =
        (c ^ 2) ^ 2 * (8 * m₄ * (1 + 16 * m₄)) / r ^ 2 := by
      rw [hr2]
      field_simp
      ring
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr0,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    by_cases hr' : r = 0
    · exfalso
      have : (0 : ℝ) < r := by positivity
      exact this.ne' hr'
    field_simp
  calc r * ∫ z, ∫ w, Y (z, w) ^ 2 ∂(innerLaw ρ) ∂ν
      ≤ r * (2 * c_d * Real.sqrt (c ^ 2 * (1 + 16 * m₄) / (8 * M) * (64 * c ^ 2 * m₄ / M ^ 2))) :=
        mul_le_mul_of_nonneg_left key hr0
    _ = 2 * c_d * (r * Real.sqrt (c ^ 2 * (1 + 16 * m₄) / (8 * M) * (64 * c ^ 2 * m₄ / M ^ 2))) :=
        by ring
    _ = 2 * c_d * c ^ 2 * Real.sqrt (8 * m₄ * (1 + 16 * m₄)) := by rw [hAB]; ring

/-- **`β = 1.5` for a piecewise linear `f`, with a bounded density** (Giles 2015, §9.1, p. 58:
"the function `f` was piecewise linear, not twice differentiable, and so the rate of variance
convergence was slightly lower, with `β = 1.5`").  As `nested_kink_variance_rate`, with the
small-ball hypothesis replaced by: `E_W[g(Z, W)]` has a density at most `ρ_max` on `[k − r, k + r]`.
Then `2^{3ℓ/2} E[Y_{ℓ+1}²] ≤ 2 max(2ρ_max, 1/r) c² √(8 m₄ (1 + 16 m₄))`. -/
theorem nested_kink_variance_rate_of_density {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g)) {m₄ ρ_max r : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧ ∫ v, g z v ^ 4 ∂ρ ≤ m₄) (hr : 0 < r)
    (hdens : ∀ s ⊆ Set.Icc (k - r) (k + r), MeasurableSet s →
      ν ((fun z => ∫ v, g z v ∂ρ) ⁻¹' s) ≤ ENNReal.ofReal ρ_max * volume s) (ℓ : ℕ) :
    MemLp (nestedDelta f g (ℓ + 1)) 2 (nestedLaw ν ρ) ∧
      (2 : ℝ) ^ ((3 / 2 : ℝ) * ℓ) * ∫ p, nestedDelta f g (ℓ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        2 * max (2 * ρ_max) (1 / r) * c ^ 2 * Real.sqrt (8 * m₄ * (1 + 16 * m₄)) :=
  nested_kink_variance_rate ν ρ hf hg hfib (small_ball_of_density hr hdens) ℓ

/-- **`α = ½` for a piecewise linear `f`** (Giles 2015, §9.1, p. 58, the setting of Bujok et al.;
the paper does not state `α` for this case).  Under the moment hypothesis of
`nested_kink_variance_rate`, the level-`ℓ` approximation `P_ℓ = f(A_{2^ℓ})` has the bias
`2^{ℓ/2} |E[P_ℓ] − E_Z[f(E_W[g(Z, W)])]| ≤ (|a₁| + |c|)(1 + 8 m₄)`: `f` is Lipschitz and the inner
sampling error is `O(2^{−ℓ/2})` in `L¹`.  This is the rate needed for Theorem 1 with
`α = ½ min(β, γ) = ½`. -/
theorem nested_kink_bias_rate {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g)) {m₄ : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧ ∫ v, g z v ^ 4 ∂ρ ≤ m₄) (ℓ : ℕ) :
    (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) *
        |∫ p, (nestedP f g ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ)| ≤
      (|a₁| + |c|) * (1 + 8 * m₄) := by
  have hg4 := integrable_pow_four_of_fiber ν ρ hg hfib
  have hfm : Measurable f := (continuous_kink hf).measurable
  set M : ℕ := 2 ^ ℓ with hMdef
  have hM : 0 < M := by positivity
  set s : ℝ := (2 : ℝ) ^ ((1 / 2 : ℝ) * ℓ) with hs
  have hs0 : 0 < s := by positivity
  have hs2 : s ^ 2 = M := by
    rw [hs, hMdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast
    rw [← Real.rpow_natCast]
    congr 1
    ring
  -- integrability of `P_ℓ − P`
  obtain ⟨hGm, hG4⟩ := integrable_condMean_pow_four ν ρ hg hg4
  have hA : Measurable fun p : 𝒵 × (ℕ → 𝒲) => innerMean g M p.1 p.2 :=
    measurable_innerMean hg M measurable_id
  have hPl : Integrable (nestedP f g ℓ) (nestedLaw ν ρ) :=
    (memLp_two_kink_comp hf hA (integrable_pow_of_pow_four hA
      (integrable_innerMean_pow_four ν ρ hg hg4 hM) (by norm_num))).integrable one_le_two
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hP : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    ((memLp_two_kink_comp hf hGm (integrable_pow_of_pow_four hGm hG4
      (by norm_num))).comp_measurePreserving hfst).integrable one_le_two
  have hint : Integrable (fun p => nestedP f g ℓ p - nestedTarget f g ρ p) (nestedLaw ν ρ) :=
    hPl.sub hP
  have e : ∫ p, (nestedP f g ℓ p - nestedTarget f g ρ p) ∂(nestedLaw ν ρ) =
      ∫ z, ∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ) ∂ν :=
    integral_prod _ hint
  -- the bound for a fixed outer sample
  have hfib' : ∀ᵐ z ∂ν, |∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ)| ≤
      (|a₁| + |c|) * (1 + 8 * m₄) / s := by
    filter_upwards [hfib] with z ⟨hz4, hzm⟩
    have hgz : Measurable (g z) := hg.of_uncurry_left
    obtain ⟨-, -, -, i4, h2, -⟩ := fiber_nested_moments ρ g z hgz hz4 hM
    set G := ∫ v, g z v ∂ρ
    have hAz : Measurable fun w : ℕ → 𝒲 => innerMean g M z w - G :=
      (measurable_innerMean_right hgz M).sub_const G
    have i1 : Integrable (fun w : ℕ → 𝒲 => innerMean g M z w - G) (innerLaw ρ) := by
      simpa using integrable_pow_of_pow_four hAz i4 (k := 1) (by norm_num)
    have i2 : Integrable (fun w : ℕ → 𝒲 => (innerMean g M z w - G) ^ 2) (innerLaw ρ) :=
      integrable_pow_of_pow_four hAz i4 (by norm_num)
    have hfA : Integrable (fun w => f (innerMean g M z w) - f G) (innerLaw ρ) :=
      (i1.abs.const_mul (|a₁| + |c|)).mono'
        ((hfm.comp (measurable_innerMean_right hgz M)).sub_const _).aestronglyMeasurable
        (Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs]
          exact abs_kink_sub_le hf _ _)
    -- `|x| ≤ ½ (s x² + 1/s)`
    have hamgm : ∀ x : ℝ, |x| ≤ (s * x ^ 2 + 1 / s) / 2 := fun x => by
      have e : (s * x ^ 2 + 1 / s) / 2 - |x| = (s * |x| - 1) ^ 2 / (2 * s) := by
        rw [← sq_abs x]
        field_simp
        ring
      have : 0 ≤ (s * |x| - 1) ^ 2 / (2 * s) := by positivity
      linarith
    have hE : ∫ w, |innerMean g M z w - G| ∂(innerLaw ρ) ≤ (1 + 8 * m₄) / s := by
      have hM2 : ∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ) ≤ (1 + 16 * m₄) / s ^ 2 := by
        rw [hs2, le_div_iff₀ (Nat.cast_pos.2 hM), mul_comm]
        linarith
      calc ∫ w, |innerMean g M z w - G| ∂(innerLaw ρ)
          ≤ ∫ w, (s * (innerMean g M z w - G) ^ 2 + 1 / s) / 2 ∂(innerLaw ρ) :=
            integral_mono i1.abs (((i2.const_mul s).add (integrable_const _)).div_const 2)
              fun w => hamgm _
        _ = (s * ∫ w, (innerMean g M z w - G) ^ 2 ∂(innerLaw ρ) + 1 / s) / 2 := by
            rw [integral_div, integral_add (i2.const_mul s) (integrable_const _),
              integral_const_mul, integral_const, probReal_univ, one_smul]
        _ ≤ (s * ((1 + 16 * m₄) / s ^ 2) + 1 / s) / 2 := by gcongr
        _ = (1 + 8 * m₄) / s := by field_simp; ring
    calc |∫ w, (f (innerMean g M z w) - f G) ∂(innerLaw ρ)|
        ≤ ∫ w, |f (innerMean g M z w) - f G| ∂(innerLaw ρ) := abs_integral_le_integral_abs
      _ ≤ ∫ w, (|a₁| + |c|) * |innerMean g M z w - G| ∂(innerLaw ρ) :=
          integral_mono hfA.abs (i1.abs.const_mul _) fun w => abs_kink_sub_le hf _ _
      _ = (|a₁| + |c|) * ∫ w, |innerMean g M z w - G| ∂(innerLaw ρ) := integral_const_mul _ _
      _ ≤ (|a₁| + |c|) * ((1 + 8 * m₄) / s) := by gcongr
      _ = (|a₁| + |c|) * (1 + 8 * m₄) / s := by ring
  rw [e]
  have h1 : |∫ z, ∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ) ∂ν| ≤
      (|a₁| + |c|) * (1 + 8 * m₄) / s := by
    refine abs_integral_le_integral_abs.trans ?_
    have := integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
      (integrable_const ((|a₁| + |c|) * (1 + 8 * m₄) / s)) hfib'
    rwa [integral_const, probReal_univ, one_smul] at this
  calc s * |∫ z, ∫ w, (f (innerMean g M z w) - f (∫ v, g z v ∂ρ)) ∂(innerLaw ρ) ∂ν|
      ≤ s * ((|a₁| + |c|) * (1 + 8 * m₄) / s) := mul_le_mul_of_nonneg_left h1 hs0.le
    _ = (|a₁| + |c|) * (1 + 8 * m₄) := by field_simp

/-- **MLMC for nested simulation with a piecewise linear `f` has complexity `O(ε⁻²)`** (Giles 2015,
§9.1, p. 58: "In their case, the function `f` was piecewise linear, not twice differentiable, and so
the rate of variance convergence was slightly lower, with `β = 1.5`. However, this is still
sufficiently large to achieve an overall complexity which is `O(ε⁻²)`").  Under the hypotheses of
`nested_kink_variance_rate`, for independent inputs `ω^{(ℓ,n)}` with law `ν ⊗ ρ^{⊗ℕ}` and level-`ℓ`
costs with mean `C_ℓ ≤ c₃ 2^ℓ` (`M_ℓ = 2^ℓ` inner samples), there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the MLMC estimator
`∑_{ℓ ≤ L} N_ℓ⁻¹ ∑_{n < N_ℓ} Y_ℓ(ω^{(ℓ,n)})` of `E_Z[f(E_W[g(Z, W)])]` has a square-integrable
error with mean square `< ε²`, and expected cost `≤ c₄ ε⁻²`: Theorem 1
(`giles_theorem1_corrections`) with `α = ½` (`nested_kink_bias_rate`), `β = 3/2`
(`nested_kink_variance_rate`) and `γ = 1`. -/
theorem nested_kink_mlmc_complexity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : ℝ → ℝ} {a₀ a₁ c k : ℝ}
    (hf : ∀ x, f x = a₀ + a₁ * x + c * max (x - k) 0) {g : 𝒵 → 𝒲 → ℝ}
    (hg : Measurable (Function.uncurry g)) {m₄ c_d : ℝ}
    (hfib : ∀ᵐ z ∂ν, Integrable (fun v => g z v ^ 4) ρ ∧ ∫ v, g z v ^ 4 ∂ρ ≤ m₄)
    (hball : ∀ t : ℝ, 0 < t → ν {z | |∫ v, g z v ∂ρ - k| ≤ t} ≤ ENNReal.ofReal (c_d * t))
    (ω : ℕ × ℕ → Ω → 𝒵 × (ℕ → 𝒲)) (hω : ∀ p, MeasurePreserving (ω p) μ (nestedLaw ν ρ))
    (hind : iIndepFun ω μ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ) {c₃ : ℝ} (hc₃ : 0 < c₃)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (hC : ∀ ℓ : ℕ, C ℓ ≤ c₃ * 2 ^ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedDelta f g) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2) μ ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1), blockMean (nestedDelta f g) ω ℓ (N ℓ) x -
          ∫ z, f (∫ v, g z v ∂ρ) ∂ν) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * ε ^ (-2 : ℝ) := by
  have hg4 := integrable_pow_four_of_fiber ν ρ hg hfib
  have hfm : Measurable f := (continuous_kink hf).measurable
  obtain ⟨hGm, hG4⟩ := integrable_condMean_pow_four ν ρ hg hg4
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hPl2 : ∀ ℓ, MemLp (nestedP f g ℓ) 2 (nestedLaw ν ρ) := fun ℓ => by
    have hA : Measurable fun p : 𝒵 × (ℕ → 𝒲) => innerMean g (2 ^ ℓ) p.1 p.2 :=
      measurable_innerMean hg _ measurable_id
    exact memLp_two_kink_comp hf hA (integrable_pow_of_pow_four hA
      (integrable_innerMean_pow_four ν ρ hg hg4 (by positivity)) (by norm_num))
  have hPl : ∀ ℓ, Integrable (nestedP f g ℓ) (nestedLaw ν ρ) := fun ℓ =>
    (hPl2 ℓ).integrable one_le_two
  have hP : Integrable (nestedTarget f g ρ) (nestedLaw ν ρ) :=
    ((memLp_two_kink_comp hf hGm (integrable_pow_of_pow_four hGm hG4
      (by norm_num))).comp_measurePreserving hfst).integrable one_le_two
  have hΔm : ∀ ℓ, Measurable (nestedDelta f g ℓ) := measurable_nestedDelta hfm hg
  have hΔ : ∀ ℓ, MemLp (nestedDelta f g ℓ) 2 (nestedLaw ν ρ) := fun ℓ => by
    cases ℓ with
    | zero => exact hPl2 0
    | succ ℓ => exact (nested_kink_variance_rate ν ρ hf hg hfib hball ℓ).1
  -- (i) the bias, `α = ½`
  obtain ⟨B₁, hB₁⟩ : ∃ B, B = (|a₁| + |c|) * (1 + 8 * m₄) := ⟨_, rfl⟩
  have h_i : ∀ ℓ : ℕ, |∫ y, nestedP f g ℓ y - nestedTarget f g ρ y ∂(nestedLaw ν ρ)| ≤
      (|B₁| + 1) * (2 : ℝ) ^ (-((1 / 2 : ℝ) * (ℓ : ℝ))) := fun ℓ => by
    have hb := nested_kink_bias_rate ν ρ hf hg hfib ℓ
    rw [← hB₁] at hb
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← div_eq_mul_inv,
      le_div_iff₀ (by positivity), mul_comm]
    linarith [le_abs_self B₁]
  -- (iii) the variance, `β = 3/2`
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = 2 * c_d * c ^ 2 * Real.sqrt (8 * m₄ * (1 + 16 * m₄)) :=
    ⟨_, rfl⟩
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
      have hr := (nested_kink_variance_rate ν ρ hf hg hfib hball ℓ).2
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
  have hαβγ : min (3 / 2 : ℝ) 1 / 2 ≤ 1 / 2 := by norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_corrections (nestedTarget f g ρ) (nestedP f g)
    (nestedDelta f g) ω cost C (by norm_num) (by norm_num) one_pos hc₁ hc₂ hc₃ hαβγ hω hind hP
    hPl hΔm hΔ hcost hcostC h_i (integral_nestedDelta ν ρ f g hPl) h_iii h_iv
  have hPint : ∫ y, nestedTarget f g ρ y ∂(nestedLaw ν ρ) = ∫ z, f (∫ v, g z v ∂ρ) ∂ν :=
    integral_comp_of_measurePreserving hfst (hfm.comp hGm).aestronglyMeasurable
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost'⟩ := h ε hε hε1
  rw [hPint] at hmse
  rw [complexityBound_of_lt (by norm_num) ε] at hcost'
  exact ⟨L, N, hN, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω hΔ ℓ (N ℓ)).sub
    (memLp_const _)).integrable_sq, hmse, hcost'⟩

end Kink

/-! ### §9.2: the MIMC rates -/

section MIMC

variable {𝒵 𝒲 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒲] (ν : Measure 𝒵)
  [IsProbabilityMeasure ν] (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]

/-- The nested MIMC correction (Giles 2015, §9.2, p. 59: "We now have a pair of level indices
`(ℓ₁, ℓ₂)`, with the number of inner samples equal to `2^{ℓ₁}` and the number of timesteps
proportional to `2^{ℓ₂}`. If we use the natural extension of the MLMC estimator to the corresponding
MIMC estimator …"): for one outer sample, the §9.1 correction on level `ℓ₁` (`nestedDelta`,
`2^{ℓ₁}` inner samples) of the level-`ℓ₂` inner approximation `g_{ℓ₂}`, minus the same for
`g_{ℓ₂−1}` when `ℓ₂ > 0`.  For `ℓ₁, ℓ₂ > 0` these are the six terms of the paper's `Y_ℓ`. -/
noncomputable def nestedMimcDelta (f : ℝ → ℝ) (gh : ℕ → 𝒵 → 𝒲 → ℝ) (ℓ₁ : ℕ) :
    ℕ → 𝒵 × (ℕ → 𝒲) → ℝ
  | 0 => nestedDelta f (gh 0) ℓ₁
  | ℓ₂ + 1 => fun p => nestedDelta f (gh (ℓ₂ + 1)) ℓ₁ p - nestedDelta f (gh ℓ₂) ℓ₁ p

/-- The square of the pathwise MIMC bound (Giles 2015, §9.2): if
`|Y| ≤ (L/8) X² |μ| + (K/2) X |C| + (K/4) X |E|` with `X⁴ ≤ T` and `|μ| ≤ w`, then for every
`q > 0`, `Y² ≤ 3((L/8)² w² + K²/(8q²) + K²/(32q²)) T + (3K²q²/8) C⁴ + (3K²q²/32) E⁴`. -/
lemma sq_le_of_mimc_pathwise {Y X μ C E T q w K L : ℝ} (hq : 0 < q) (hX4 : X ^ 4 ≤ T)
    (hμ : |μ| ≤ w)
    (hY : |Y| ≤ L / 8 * X ^ 2 * |μ| + K / 2 * X * |C| + K / 4 * X * |E|) :
    Y ^ 2 ≤ 3 * ((L / 8) ^ 2 * w ^ 2 + K ^ 2 / 8 / q ^ 2 + K ^ 2 / 32 / q ^ 2) * T +
      3 * (K ^ 2 / 8 * q ^ 2) * C ^ 4 + 3 * (K ^ 2 / 32 * q ^ 2) * E ^ 4 := by
  have h3 := sq_le_three_mul_of_abs_le hY
  have hT : 0 ≤ T := le_trans (by positivity) hX4
  have hμ2 : μ ^ 2 ≤ w ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hμ 2
  have hα : (L / 8 * X ^ 2 * |μ|) ^ 2 ≤ (L / 8) ^ 2 * w ^ 2 * T := by
    rw [mul_pow, mul_pow, sq_abs, ← pow_mul]
    calc (L / 8) ^ 2 * X ^ (2 * 2) * μ ^ 2 ≤ (L / 8) ^ 2 * T * w ^ 2 := by gcongr
      _ = (L / 8) ^ 2 * w ^ 2 * T := by ring
  have hβ : (K / 2 * X * |C|) ^ 2 ≤ K ^ 2 / 4 * ((T / q ^ 2 + q ^ 2 * C ^ 4) / 2) := by
    rw [mul_pow, mul_pow, sq_abs, div_pow, mul_assoc]
    have := sq_mul_sq_le_of_pow_four_le (Z := C) hq hX4
    norm_num
    gcongr
  have hγ : (K / 4 * X * |E|) ^ 2 ≤ K ^ 2 / 16 * ((T / q ^ 2 + q ^ 2 * E ^ 4) / 2) := by
    rw [mul_pow, mul_pow, sq_abs, div_pow, mul_assoc]
    have := sq_mul_sq_le_of_pow_four_le (Z := E) hq hX4
    norm_num
    gcongr
  calc Y ^ 2 ≤ 3 * ((L / 8 * X ^ 2 * |μ|) ^ 2 + (K / 2 * X * |C|) ^ 2 + (K / 4 * X * |E|) ^ 2) :=
        h3
    _ ≤ 3 * ((L / 8) ^ 2 * w ^ 2 * T + K ^ 2 / 4 * ((T / q ^ 2 + q ^ 2 * C ^ 4) / 2) +
          K ^ 2 / 16 * ((T / q ^ 2 + q ^ 2 * E ^ 4) / 2)) := by gcongr
    _ = _ := by ring

/-- **`V_ℓ = O(2^{−2ℓ₁−2ℓ₂})` for the nested MIMC correction** (Giles 2015, §9.2, p. 60: "Combining
these results we obtain `(Δg_{1,ℓ₂} − Δg_{2,ℓ₂})² − (Δg_{1,ℓ₂−1} − Δg_{2,ℓ₂−1})² = O(2^{−ℓ₁−ℓ₂})`
and therefore `E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` and `V_ℓ = O(2^{−2ℓ₁−2ℓ₂})`").  For
`ℓ = (ℓ₁ + 1, ℓ₂ + 1)` (the paper's `ℓ₁, ℓ₂ > 0`), `nestedMimcDelta` is the paper's six-term
correction.  Hypotheses: `f′` (with derivative `f″`) is `K`-Lipschitz and `f″` is `L`-Lipschitz
(the paper's "twice differentiable" does not control the Taylor remainder); `E[g_ℓ(Z, W)⁴] ≤ m₄`;
first order strong convergence in `L⁴`, `(2^ℓ)⁴ E[(g_{ℓ+1}(Z, W) − g_ℓ(Z, W))⁴] ≤ cₛ` (the paper
assumes "first order strong convergence"); and first order weak convergence of the level
differences uniformly in the outer sample, `2^ℓ |E_W[g_{ℓ+1}(z, W) − g_ℓ(z, W)]| ≤ c_w` for `ν`-a.e.
`z`.  The strong and weak orders of the time discretisation are hypotheses, not formalised here.
Then `4^{ℓ₁+ℓ₂} E[Y²] ≤ 21 L² c_w² m₄ + 210 K² m₄ + 27 K² cₛ`.  The weak-convergence hypothesis
is needed because of the re-centring explained in `abs_mimc_antithetic_le_of_deriv2`: the paper's
`Δg_{1,ℓ₂} − Δg_{1,ℓ₂−1}` is `O(2^{−ℓ₂})`, not `O(2^{−ℓ₁/2−ℓ₂})`, and its conditional mean enters
through the change of `f″` between the two inner approximations. -/
theorem nested_mimc_variance_rate {f f' f'' : ℝ → ℝ} {K L : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hK : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x))
    (hL : ∀ x y, x ≤ y → |f'' y - f'' x| ≤ L * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ cₛ c_w : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ)
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, (gh (ℓ + 1) z v - gh ℓ z v) ∂ρ| ≤ c_w)
    (ℓ₁ ℓ₂ : ℕ) :
    MemLp (nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1)) 2 (nestedLaw ν ρ) ∧
      ((2 : ℝ) ^ (ℓ₁ + ℓ₂)) ^ 2 *
          ∫ p, nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) p ^ 2 ∂(nestedLaw ν ρ) ≤
        21 * L ^ 2 * c_w ^ 2 * m₄ + 210 * K ^ 2 * m₄ + 27 * K ^ 2 * cₛ := by
  set M : ℕ := 2 ^ ℓ₁ with hMdef
  have hM : 0 < M := by positivity
  set r : ℝ := (2 : ℝ) ^ ℓ₁ with hr
  have hMr : (M : ℝ) = r := by rw [hMdef, hr]; push_cast; ring
  set q : ℝ := (2 : ℝ) ^ ℓ₂
  have hr0 : 0 < r := by positivity
  have hq0 : 0 < q := by positivity
  -- the level difference `H = g_{ℓ₂+1} − g_{ℓ₂}` of the inner quantity
  set H : 𝒵 → 𝒲 → ℝ := fun z v => gh (ℓ₂ + 1) z v - gh ℓ₂ z v
  have hHm : Measurable (Function.uncurry H) := (hgh (ℓ₂ + 1)).sub (hgh ℓ₂)
  have hH4 : Integrable (fun p : 𝒵 × 𝒲 => H p.1 p.2 ^ 4) (ν.prod ρ) := by
    refine (((hgh4 (ℓ₂ + 1)).add (hgh4 ℓ₂)).const_mul 8).mono'
      ((hHm.pow_const 4).aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact sub_pow_four_le _ _
  have hH4le : q ^ 4 * ∫ p, H p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ cₛ := hs ℓ₂
  -- the correction is square-integrable
  obtain ⟨hN1, -⟩ := nested_variance_rate ν ρ hf hK (hgh (ℓ₂ + 1)) (hgh4 (ℓ₂ + 1)) ℓ₁
  obtain ⟨hN0, -⟩ := nested_variance_rate ν ρ hf hK (hgh ℓ₂) (hgh4 ℓ₂) ℓ₁
  have hY2 : MemLp (nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1)) 2 (nestedLaw ν ρ) := hN1.sub hN0
  refine ⟨hY2, ?_⟩
  -- the moments of the antithetic differences and of the centred mean of `H`
  obtain ⟨iA, hA⟩ := integral_antithetic_pow_four_le ν ρ (hgh (ℓ₂ + 1)) (hgh4 (ℓ₂ + 1)) hM
  obtain ⟨iB, hB⟩ := integral_antithetic_pow_four_le ν ρ (hgh ℓ₂) (hgh4 ℓ₂) hM
  obtain ⟨iE, hE⟩ := integral_antithetic_pow_four_le ν ρ hHm hH4 hM
  obtain ⟨iC, hC⟩ := integral_centred_pow_four_le ν ρ hHm hH4 (M := 2 * M) (by positivity)
  rw [hMr] at hA hB hE
  have h2M : ((2 * M : ℕ) : ℝ) = 2 * r := by push_cast; rw [hMr]
  rw [h2M] at hC
  set A4 : 𝒵 × (ℕ → 𝒲) → ℝ := fun p =>
    (innerMean (gh (ℓ₂ + 1)) M p.1 p.2 - innerMean (gh (ℓ₂ + 1)) M p.1 (shiftSeq M p.2)) ^ 4
  set B4 : 𝒵 × (ℕ → 𝒲) → ℝ := fun p =>
    (innerMean (gh ℓ₂) M p.1 p.2 - innerMean (gh ℓ₂) M p.1 (shiftSeq M p.2)) ^ 4
  set C4 : 𝒵 × (ℕ → 𝒲) → ℝ := fun p => (innerMean H (2 * M) p.1 p.2 - ∫ v, H p.1 v ∂ρ) ^ 4
  set E4 : 𝒵 × (ℕ → 𝒲) → ℝ := fun p =>
    (innerMean H M p.1 p.2 - innerMean H M p.1 (shiftSeq M p.2)) ^ 4
  have hTle : r ^ 2 * (∫ p, A4 p ∂(nestedLaw ν ρ) + ∫ p, B4 p ∂(nestedLaw ν ρ)) ≤ 448 * m₄ := by
    have h1 : r ^ 2 * ∫ p, A4 p ∂(nestedLaw ν ρ) ≤ 224 * m₄ :=
      hA.trans (mul_le_mul_of_nonneg_left (hm₄ (ℓ₂ + 1)) (by norm_num))
    have h2 : r ^ 2 * ∫ p, B4 p ∂(nestedLaw ν ρ) ≤ 224 * m₄ :=
      hB.trans (mul_le_mul_of_nonneg_left (hm₄ ℓ₂) (by norm_num))
    linarith
  have hEle : q ^ 4 * (r ^ 2 * ∫ p, E4 p ∂(nestedLaw ν ρ)) ≤ 224 * cₛ := by
    calc q ^ 4 * (r ^ 2 * ∫ p, E4 p ∂(nestedLaw ν ρ))
        ≤ q ^ 4 * (224 * ∫ p, H p.1 p.2 ^ 4 ∂(ν.prod ρ)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 224 * (q ^ 4 * ∫ p, H p.1 p.2 ^ 4 ∂(ν.prod ρ)) := by ring
      _ ≤ 224 * cₛ := by gcongr
  have hCle : q ^ 4 * (r ^ 2 * ∫ p, C4 p ∂(nestedLaw ν ρ)) ≤ 16 * cₛ := by
    have hC' : r ^ 2 * ∫ p, C4 p ∂(nestedLaw ν ρ) ≤ 16 * ∫ p, H p.1 p.2 ^ 4 ∂(ν.prod ρ) := by
      have e : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
      rw [e] at hC
      linarith
    calc q ^ 4 * (r ^ 2 * ∫ p, C4 p ∂(nestedLaw ν ρ))
        ≤ q ^ 4 * (16 * ∫ p, H p.1 p.2 ^ 4 ∂(ν.prod ρ)) :=
          mul_le_mul_of_nonneg_left hC' (by positivity)
      _ = 16 * (q ^ 4 * ∫ p, H p.1 p.2 ^ 4 ∂(ν.prod ρ)) := by ring
      _ ≤ 16 * cₛ := by gcongr
  -- the pathwise bound, with the re-centring `μ = E_W[H(Z, W)]`
  have hfst : MeasurePreserving (Prod.fst : 𝒵 × (ℕ → 𝒲) → 𝒵) (nestedLaw ν ρ) ν :=
    measurePreserving_fst
  have hwp : ∀ᵐ p ∂(nestedLaw ν ρ), q * |∫ v, H p.1 v ∂ρ| ≤ c_w :=
    hfst.quasiMeasurePreserving.ae (hw ℓ₂)
  set c₁ : ℝ := 3 * ((L / 8) ^ 2 * (c_w / q) ^ 2 + K ^ 2 / 8 / q ^ 2 + K ^ 2 / 32 / q ^ 2)
    with hc₁
  set c₂ : ℝ := 3 * (K ^ 2 / 8 * q ^ 2) with hc₂
  set c₃ : ℝ := 3 * (K ^ 2 / 32 * q ^ 2) with hc₃
  have hpt : ∀ᵐ p ∂(nestedLaw ν ρ), nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) p ^ 2 ≤
      c₁ * (A4 p + B4 p) + c₂ * C4 p + c₃ * E4 p := by
    filter_upwards [hwp] with p hp
    have hY : nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) p =
        nestedDelta f (gh (ℓ₂ + 1)) (ℓ₁ + 1) p - nestedDelta f (gh ℓ₂) (ℓ₁ + 1) p := rfl
    rw [hY, nestedDelta_succ_eq, nestedDelta_succ_eq]
    have hb := abs_mimc_antithetic_le_of_deriv2 hf hf' hK hL
      (innerMean (gh (ℓ₂ + 1)) M p.1 p.2) (innerMean (gh (ℓ₂ + 1)) M p.1 (shiftSeq M p.2))
      (innerMean (gh ℓ₂) M p.1 p.2) (innerMean (gh ℓ₂) M p.1 (shiftSeq M p.2))
      (∫ v, H p.1 v ∂ρ)
    rw [innerMean_sub, innerMean_sub, ← innerMean_two_mul H M p.1 p.2] at hb
    have hμ : |∫ v, H p.1 v ∂ρ| ≤ c_w / q := by
      rw [le_div_iff₀ hq0, mul_comm]
      exact hp
    refine (sq_le_of_mimc_pathwise hq0 (max_abs_pow_four_le _ _) hμ hb).trans_eq ?_
    rw [hc₁, hc₂, hc₃]
  -- integrate
  have iT : Integrable (fun p => A4 p + B4 p) (nestedLaw ν ρ) := iA.add iB
  have iR1 : Integrable (fun p => c₁ * (A4 p + B4 p) + c₂ * C4 p) (nestedLaw ν ρ) :=
    (iT.const_mul c₁).add (iC.const_mul c₂)
  have iR : Integrable (fun p => c₁ * (A4 p + B4 p) + c₂ * C4 p + c₃ * E4 p) (nestedLaw ν ρ) :=
    iR1.add (iE.const_mul c₃)
  have hint := integral_mono_ae hY2.integrable_sq iR hpt
  rw [integral_add iR1 (iE.const_mul c₃), integral_add (iT.const_mul c₁) (iC.const_mul c₂),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_add iA iB] at hint
  have e2 : (2 : ℝ) ^ (ℓ₁ + ℓ₂) = r * q := by rw [pow_add]
  rw [e2]
  have e3 : (r * q) ^ 2 * (c₁ * (∫ p, A4 p ∂(nestedLaw ν ρ) + ∫ p, B4 p ∂(nestedLaw ν ρ)) +
      c₂ * ∫ p, C4 p ∂(nestedLaw ν ρ) + c₃ * ∫ p, E4 p ∂(nestedLaw ν ρ)) =
      c₁ * q ^ 2 * (r ^ 2 * (∫ p, A4 p ∂(nestedLaw ν ρ) + ∫ p, B4 p ∂(nestedLaw ν ρ))) +
        c₂ / q ^ 2 * (q ^ 4 * (r ^ 2 * ∫ p, C4 p ∂(nestedLaw ν ρ))) +
        c₃ / q ^ 2 * (q ^ 4 * (r ^ 2 * ∫ p, E4 p ∂(nestedLaw ν ρ))) := by
    field_simp
  have e4 : c₁ * q ^ 2 * (448 * m₄) + c₂ / q ^ 2 * (16 * cₛ) + c₃ / q ^ 2 * (224 * cₛ) =
      21 * L ^ 2 * c_w ^ 2 * m₄ + 210 * K ^ 2 * m₄ + 27 * K ^ 2 * cₛ := by
    rw [hc₁, hc₂, hc₃]
    field_simp
    ring
  calc (r * q) ^ 2 * ∫ p, nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) p ^ 2 ∂(nestedLaw ν ρ)
      ≤ (r * q) ^ 2 * (c₁ * (∫ p, A4 p ∂(nestedLaw ν ρ) + ∫ p, B4 p ∂(nestedLaw ν ρ)) +
          c₂ * ∫ p, C4 p ∂(nestedLaw ν ρ) + c₃ * ∫ p, E4 p ∂(nestedLaw ν ρ)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = c₁ * q ^ 2 * (r ^ 2 * (∫ p, A4 p ∂(nestedLaw ν ρ) + ∫ p, B4 p ∂(nestedLaw ν ρ))) +
          c₂ / q ^ 2 * (q ^ 4 * (r ^ 2 * ∫ p, C4 p ∂(nestedLaw ν ρ))) +
          c₃ / q ^ 2 * (q ^ 4 * (r ^ 2 * ∫ p, E4 p ∂(nestedLaw ν ρ))) := e3
    _ ≤ c₁ * q ^ 2 * (448 * m₄) + c₂ / q ^ 2 * (16 * cₛ) + c₃ / q ^ 2 * (224 * cₛ) := by
        gcongr
    _ = 21 * L ^ 2 * c_w ^ 2 * m₄ + 210 * K ^ 2 * m₄ + 27 * K ^ 2 * cₛ := e4

/-- **`E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})` for the nested MIMC correction** (Giles 2015, §9.2, p. 60: "and
therefore `E[Y_ℓ] = O(2^{−ℓ₁−ℓ₂})`").  Under the hypotheses of `nested_mimc_variance_rate`, with `C`
its bound, `2^{ℓ₁+ℓ₂} |E[Y_{(ℓ₁+1, ℓ₂+1)}]| ≤ (C + 1)/2` (`mul_abs_integral_le_of_memLp`). -/
theorem nested_mimc_mean_rate {f f' f'' : ℝ → ℝ} {K L : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hK : ∀ x y, x ≤ y → |f' y - f' x| ≤ K * (y - x))
    (hL : ∀ x y, x ≤ y → |f'' y - f'' x| ≤ L * (y - x)) {gh : ℕ → 𝒵 → 𝒲 → ℝ}
    (hgh : ∀ ℓ, Measurable (Function.uncurry (gh ℓ)))
    (hgh4 : ∀ ℓ, Integrable (fun p : 𝒵 × 𝒲 => gh ℓ p.1 p.2 ^ 4) (ν.prod ρ)) {m₄ cₛ c_w : ℝ}
    (hm₄ : ∀ ℓ, ∫ p, gh ℓ p.1 p.2 ^ 4 ∂(ν.prod ρ) ≤ m₄)
    (hs : ∀ ℓ, ((2 : ℝ) ^ ℓ) ^ 4 *
      ∫ p, (gh (ℓ + 1) p.1 p.2 - gh ℓ p.1 p.2) ^ 4 ∂(ν.prod ρ) ≤ cₛ)
    (hw : ∀ ℓ, ∀ᵐ z ∂ν, (2 : ℝ) ^ ℓ * |∫ v, (gh (ℓ + 1) z v - gh ℓ z v) ∂ρ| ≤ c_w)
    (ℓ₁ ℓ₂ : ℕ) :
    (2 : ℝ) ^ (ℓ₁ + ℓ₂) * |∫ p, nestedMimcDelta f gh (ℓ₁ + 1) (ℓ₂ + 1) p ∂(nestedLaw ν ρ)| ≤
      (21 * L ^ 2 * c_w ^ 2 * m₄ + 210 * K ^ 2 * m₄ + 27 * K ^ 2 * cₛ + 1) / 2 := by
  obtain ⟨hY2, hV⟩ := nested_mimc_variance_rate ν ρ hf hf' hK hL hgh hgh4 hm₄ hs hw ℓ₁ ℓ₂
  refine (mul_abs_integral_le_of_memLp hY2 (by positivity : (0 : ℝ) < 2 ^ (ℓ₁ + ℓ₂))).trans ?_
  gcongr

end MIMC

end MLMC
