import MlmcLean.GBMEulerMaruyama
import MlmcLean.PDEExamples

/-!
# Geometric Brownian motion: the Milstein MLMC estimator end to end (Giles 2015, §5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.2
"Milstein discretisation" (pp. 32–35) and Figure 5.5.  §5.2: "For Lipschitz payoffs, the variance
`V_ℓ` for the natural multilevel estimator converges at twice the order of the strong convergence of
the numerical approximation of the SDE. This immediately suggests that it would be better to replace
the Euler-Maruyama discretisation by the Milstein discretisation … since it gives first order strong
convergence … For a scalar SDE the Milstein discretisation is
`Ŝ_{n+1} = Ŝ_n + a h + b ΔW_n + ½ b ∂b/∂S (ΔW_n² − h)` and Figure 5.5 demonstrates the improved
results obtained for the call option based on a single underlying GBM asset. `V_ℓ` is now
`O(h_ℓ²)`, leading to `α = 1, β = 2, γ = 1` … Because `β > γ`, the dominant computational cost is on
the coarsest levels."

For geometric Brownian motion `dS = rS dt + σS dW` the exact solution is known in closed form, so
all of this is proved here, with the exact solution and the Milstein path driven by the same
Brownian increments `ΔW_i = √h Z_i`, `Z_i` independent standard normal (`stdNormalSeq`).

* `integral_sq_mul_exp_mul_gaussian`, `integral_pow_three_gaussian`, `integral_pow_four_gaussian`:
  the Gaussian moments `E[Z² e^{aZ}] = (1 + a²) e^{a²/2}`, `E[Z³] = 0`, `E[Z⁴] = 3`, from the
  derivatives of the moment generating function.
* `milsteinPath_gbm`: the Milstein path (`milsteinPath`, iterating `milsteinStep`) of GBM is
  `Ŝ_n = S_0 ∏_{i<n} (1 + rh + σ√h Z_i + ½σ²(h Z_i² − h))`.
* `integral_sq_prod_sub_prod_of`: `E[(S_0 ∏ A_i − S_0 ∏ B_i)²] = S_0² (aⁿ − 2bⁿ + cⁿ)` with
  `a = E[A²]`, `b = E[AB]`, `c = E[B²]`; for the Milstein step `a = e^{(2r+σ²)h}`,
  `b = e^{rh}(1 + rh + σ²h + σ⁴h²/2)`, `c = (1 + rh)² + σ²h + σ⁴h²/2`.
* `abs_pow_sub_two_mul_pow_add_pow_le`:
  `|aⁿ − 2bⁿ + cⁿ| ≤ n² Mⁿ |a − b| |b − c| + n Mⁿ |a − 2b + c|`, and for the Milstein moments
  `|a − b|, |b − c| = O(h²)`, `|a − 2b + c| = O(h³)`.
* `gbm_mil_strong_error`: **first-order strong convergence of the Milstein scheme for GBM**,
  `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h²` at every grid time `t_n = nh`, with an explicit constant
  `gbmMilStrongConst`.
* `gbm_mil_weak_error_le`: for a `K`-Lipschitz payoff `g`, `|E[g(Ŝ_ℓ)] − E[g(S_T)]| = O(2^{−ℓ})`
  (`α = 1`); `gbm_mil_correction_variance_le`: `V_{ℓ+1} = O(4^{−ℓ})` (`β = 2`).
* `gbm_mil_mlmc_theorem1`: **Theorem 1 for the Milstein MLMC estimator of `E[g(S_T)]`** for GBM,
  with no assumed rate: for every `0 < ε < e⁻¹` there are `L` and `N_ℓ` with mean square error
  `< ε²` and cost `∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε⁻²` (the case `β > γ`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### Gaussian moments -/

/-- The derivative of `t ↦ e^{t²/2}` (the moment generating function of `N(0,1)`) is
`t e^{t²/2}`. -/
lemma hasDerivAt_exp_sq_div_two (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t := by
  have hp : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t :=
    ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by norm_num)
  exact hp.exp.congr_deriv (mul_comm _ _)

/-- `t ↦ E[Zⁿ e^{tZ}]` has derivative `E[Zⁿ⁺¹ e^{aZ}]` at `a`, for a standard normal `Z`. -/
lemma hasDerivAt_integral_pow_mul_exp_gaussian (a : ℝ) (n : ℕ) :
    HasDerivAt (fun t => ∫ x, x ^ n * Real.exp (t * x) ∂gaussianReal 0 1)
      (∫ x, x ^ (n + 1) * Real.exp (a * x) ∂gaussianReal 0 1) a :=
  hasDerivAt_integral_pow_mul_exp_real (mem_interior_integrableExpSet_gaussian a) n

/-- `E[Z² e^{aZ}] = (1 + a²) e^{a²/2}` for a standard normal `Z` (used for the Milstein moments,
Giles 2015, §5.2). -/
lemma integral_sq_mul_exp_mul_gaussian (a : ℝ) :
    ∫ x, x ^ 2 * Real.exp (a * x) ∂gaussianReal 0 1 = (1 + a ^ 2) * Real.exp (a ^ 2 / 2) := by
  have h1 : (fun t => ∫ x, x ^ 1 * Real.exp (t * x) ∂gaussianReal 0 1) =
      fun t => t * Real.exp (t ^ 2 / 2) := by
    funext t
    simp only [pow_one]
    exact integral_mul_exp_mul_gaussian t
  have h2 : HasDerivAt (fun t => ∫ x, x ^ 1 * Real.exp (t * x) ∂gaussianReal 0 1)
      (∫ x, x ^ 2 * Real.exp (a * x) ∂gaussianReal 0 1) a :=
    hasDerivAt_integral_pow_mul_exp_gaussian a 1
  rw [h1] at h2
  have h3 : HasDerivAt (fun t : ℝ => t * Real.exp (t ^ 2 / 2))
      ((1 + a ^ 2) * Real.exp (a ^ 2 / 2)) a :=
    ((hasDerivAt_id' a).fun_mul (hasDerivAt_exp_sq_div_two a)).congr_deriv (by ring)
  exact h2.unique h3

/-- `E[Z³ e^{aZ}] = (3a + a³) e^{a²/2}` for a standard normal `Z`. -/
lemma integral_pow_three_mul_exp_mul_gaussian (a : ℝ) :
    ∫ x, x ^ 3 * Real.exp (a * x) ∂gaussianReal 0 1 = (3 * a + a ^ 3) * Real.exp (a ^ 2 / 2) := by
  have h1 : (fun t => ∫ x, x ^ 2 * Real.exp (t * x) ∂gaussianReal 0 1) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) :=
    funext integral_sq_mul_exp_mul_gaussian
  have h2 : HasDerivAt (fun t => ∫ x, x ^ 2 * Real.exp (t * x) ∂gaussianReal 0 1)
      (∫ x, x ^ 3 * Real.exp (a * x) ∂gaussianReal 0 1) a :=
    hasDerivAt_integral_pow_mul_exp_gaussian a 2
  rw [h1] at h2
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * a) a :=
    (hasDerivAt_pow 2 a).congr_deriv (by norm_num)
  have h3 : HasDerivAt (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2))
      ((3 * a + a ^ 3) * Real.exp (a ^ 2 / 2)) a :=
    ((hsq.const_add 1).fun_mul (hasDerivAt_exp_sq_div_two a)).congr_deriv (by ring)
  exact h2.unique h3

/-- `E[Z⁴ e^{aZ}] = (3 + 6a² + a⁴) e^{a²/2}` for a standard normal `Z`. -/
lemma integral_pow_four_mul_exp_mul_gaussian (a : ℝ) :
    ∫ x, x ^ 4 * Real.exp (a * x) ∂gaussianReal 0 1 =
      (3 + 6 * a ^ 2 + a ^ 4) * Real.exp (a ^ 2 / 2) := by
  have h1 : (fun t => ∫ x, x ^ 3 * Real.exp (t * x) ∂gaussianReal 0 1) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) :=
    funext integral_pow_three_mul_exp_mul_gaussian
  have h2 : HasDerivAt (fun t => ∫ x, x ^ 3 * Real.exp (t * x) ∂gaussianReal 0 1)
      (∫ x, x ^ 4 * Real.exp (a * x) ∂gaussianReal 0 1) a :=
    hasDerivAt_integral_pow_mul_exp_gaussian a 3
  rw [h1] at h2
  have hcube : HasDerivAt (fun t : ℝ => t ^ 3) (3 * a ^ 2) a :=
    (hasDerivAt_pow 3 a).congr_deriv (by norm_num)
  have h3 : HasDerivAt (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2))
      ((3 + 6 * a ^ 2 + a ^ 4) * Real.exp (a ^ 2 / 2)) a :=
    ((((hasDerivAt_id' a).const_mul 3).fun_add hcube).fun_mul
      (hasDerivAt_exp_sq_div_two a)).congr_deriv (by ring)
  exact h2.unique h3

/-- `E[Z³] = 0` for a standard normal `Z`. -/
lemma integral_pow_three_gaussian : ∫ x, x ^ 3 ∂gaussianReal 0 1 = 0 := by
  simpa using integral_pow_three_mul_exp_mul_gaussian 0

/-- `E[Z⁴] = 3` for a standard normal `Z`. -/
lemma integral_pow_four_gaussian : ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  simpa using integral_pow_four_mul_exp_mul_gaussian 0

/-- `Zⁿ e^{aZ}` is integrable for `Z ~ N(0,1)`. -/
lemma integrable_pow_mul_exp_mul_gaussian (a : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (a * x)) (gaussianReal 0 1) :=
  integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (mem_interior_integrableExpSet_gaussian a) n

/-- `Zⁿ` is integrable for `Z ~ N(0,1)`. -/
lemma integrable_pow_gaussian (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  simpa using integrable_pow_mul_exp_mul_gaussian 0 n

/-! ### Polynomial integrals -/

/-- A quartic polynomial of `Z ~ N(0,1)` is integrable. -/
lemma integrable_quartic_gaussian (c₀ c₁ c₂ c₃ c₄ : ℝ) :
    Integrable (fun x : ℝ => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4)
      (gaussianReal 0 1) :=
  ((((integrable_const c₀).add (integrable_id_gaussian.const_mul c₁)).add
    ((integrable_pow_gaussian 2).const_mul c₂)).add
    ((integrable_pow_gaussian 3).const_mul c₃)).add ((integrable_pow_gaussian 4).const_mul c₄)

/-- `E[c₀ + c₁Z + c₂Z² + c₃Z³ + c₄Z⁴] = c₀ + c₂ + 3c₄` for `Z ~ N(0,1)`. -/
lemma integral_quartic_gaussian (c₀ c₁ c₂ c₃ c₄ : ℝ) :
    ∫ x, (c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4) ∂gaussianReal 0 1 =
      c₀ + c₂ + 3 * c₄ := by
  have i0 : Integrable (fun _ : ℝ => c₀) (gaussianReal 0 1) := integrable_const _
  have i1 : Integrable (fun x : ℝ => c₁ * x) (gaussianReal 0 1) :=
    integrable_id_gaussian.const_mul _
  have i2 : Integrable (fun x : ℝ => c₂ * x ^ 2) (gaussianReal 0 1) :=
    (integrable_pow_gaussian 2).const_mul _
  have i3 : Integrable (fun x : ℝ => c₃ * x ^ 3) (gaussianReal 0 1) :=
    (integrable_pow_gaussian 3).const_mul _
  have i4 : Integrable (fun x : ℝ => c₄ * x ^ 4) (gaussianReal 0 1) :=
    (integrable_pow_gaussian 4).const_mul _
  have j1 : Integrable (fun x : ℝ => c₀ + c₁ * x) (gaussianReal 0 1) := i0.add i1
  have j2 : Integrable (fun x : ℝ => c₀ + c₁ * x + c₂ * x ^ 2) (gaussianReal 0 1) := j1.add i2
  have j3 : Integrable (fun x : ℝ => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3) (gaussianReal 0 1) :=
    j2.add i3
  rw [integral_add j3 i4, integral_add j2 i3, integral_add j1 i2, integral_add i0 i1,
    integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_id_gaussianReal, integral_sq_gaussian,
    integral_pow_three_gaussian, integral_pow_four_gaussian]
  ring

/-- The square of a quadratic polynomial of `Z ~ N(0,1)` is integrable. -/
lemma integrable_sq_quadratic_gaussian (α s β : ℝ) :
    Integrable (fun x : ℝ => (α + s * x + β * x ^ 2) ^ 2) (gaussianReal 0 1) := by
  have e : (fun x : ℝ => (α + s * x + β * x ^ 2) ^ 2) = fun x =>
      α ^ 2 + 2 * α * s * x + (s ^ 2 + 2 * α * β) * x ^ 2 + 2 * s * β * x ^ 3 + β ^ 2 * x ^ 4 := by
    funext x
    ring
  rw [e]
  exact integrable_quartic_gaussian _ _ _ _ _

/-- `E[(α + sZ + βZ²)²] = α² + s² + 2αβ + 3β²` for `Z ~ N(0,1)`. -/
lemma integral_sq_quadratic_gaussian (α s β : ℝ) :
    ∫ x, (α + s * x + β * x ^ 2) ^ 2 ∂gaussianReal 0 1 = α ^ 2 + s ^ 2 + 2 * α * β + 3 * β ^ 2 := by
  have e : (fun x : ℝ => (α + s * x + β * x ^ 2) ^ 2) = fun x =>
      α ^ 2 + 2 * α * s * x + (s ^ 2 + 2 * α * β) * x ^ 2 + 2 * s * β * x ^ 3 + β ^ 2 * x ^ 4 := by
    funext x
    ring
  rw [e, integral_quartic_gaussian]
  ring

/-- `(c₀ + c₁Z + c₂Z²) e^{aZ}` is integrable for `Z ~ N(0,1)`. -/
lemma integrable_quadratic_mul_exp_gaussian (c₀ c₁ c₂ a : ℝ) :
    Integrable (fun x : ℝ => (c₀ + c₁ * x + c₂ * x ^ 2) * Real.exp (a * x)) (gaussianReal 0 1) := by
  have e : (fun x : ℝ => (c₀ + c₁ * x + c₂ * x ^ 2) * Real.exp (a * x)) = fun x =>
      c₀ * Real.exp (a * x) + c₁ * (x * Real.exp (a * x)) + c₂ * (x ^ 2 * Real.exp (a * x)) := by
    funext x
    ring
  rw [e]
  exact (((integrable_exp_mul_gaussianReal a).const_mul c₀).add
    ((integrable_mul_exp_mul_gaussian a).const_mul c₁)).add
    ((integrable_pow_mul_exp_mul_gaussian a 2).const_mul c₂)

/-- `E[(c₀ + c₁Z + c₂Z²) e^{aZ}] = (c₀ + c₁a + c₂(1 + a²)) e^{a²/2}` for `Z ~ N(0,1)`. -/
lemma integral_quadratic_mul_exp_gaussian (c₀ c₁ c₂ a : ℝ) :
    ∫ x, (c₀ + c₁ * x + c₂ * x ^ 2) * Real.exp (a * x) ∂gaussianReal 0 1 =
      (c₀ + c₁ * a + c₂ * (1 + a ^ 2)) * Real.exp (a ^ 2 / 2) := by
  have e : (fun x : ℝ => (c₀ + c₁ * x + c₂ * x ^ 2) * Real.exp (a * x)) = fun x =>
      c₀ * Real.exp (a * x) + c₁ * (x * Real.exp (a * x)) + c₂ * (x ^ 2 * Real.exp (a * x)) := by
    funext x
    ring
  have i0 : Integrable (fun x : ℝ => c₀ * Real.exp (a * x)) (gaussianReal 0 1) :=
    (integrable_exp_mul_gaussianReal a).const_mul c₀
  have i1 : Integrable (fun x : ℝ => c₁ * (x * Real.exp (a * x))) (gaussianReal 0 1) :=
    (integrable_mul_exp_mul_gaussian a).const_mul c₁
  have i2 : Integrable (fun x : ℝ => c₂ * (x ^ 2 * Real.exp (a * x))) (gaussianReal 0 1) :=
    (integrable_pow_mul_exp_mul_gaussian a 2).const_mul c₂
  have j1 : Integrable (fun x : ℝ => c₀ * Real.exp (a * x) + c₁ * (x * Real.exp (a * x)))
      (gaussianReal 0 1) := i0.add i1
  rw [e, integral_add j1 i2, integral_add i0 i1, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_exp_mul_gaussian, integral_mul_exp_mul_gaussian,
    integral_sq_mul_exp_mul_gaussian]
  ring

/-! ### One Milstein step -/

/-- One Milstein step of GBM, `1 + rh + σΔW + ½σ²(ΔW² − h)` with `ΔW = √h Z` (Giles 2015, §5.2:
`Ŝ_{n+1} = Ŝ_n + a h + b ΔW_n + ½ b ∂b/∂S (ΔW_n² − h)` with `a(S) = rS`, `b(S) = σS`). -/
noncomputable def gbmMilFactor (r σ h x : ℝ) : ℝ :=
  1 + r * h + σ * (Real.sqrt h * x) + σ ^ 2 / 2 * ((Real.sqrt h * x) ^ 2 - h)

/-- The Milstein step as a quadratic polynomial of the normal increment. -/
lemma gbmMilFactor_eq_quadratic (r σ h x : ℝ) :
    gbmMilFactor r σ h x =
      1 + r * h - σ ^ 2 * h / 2 + σ * Real.sqrt h * x + σ ^ 2 / 2 * Real.sqrt h ^ 2 * x ^ 2 := by
  unfold gbmMilFactor
  ring

lemma measurable_gbmMilFactor (r σ h : ℝ) : Measurable fun x => gbmMilFactor r σ h x := by
  unfold gbmMilFactor
  fun_prop

lemma integrable_gbmMilFactor_sq (r σ h : ℝ) :
    Integrable (fun x => gbmMilFactor r σ h x ^ 2) (gaussianReal 0 1) := by
  simp_rw [gbmMilFactor_eq_quadratic]
  exact integrable_sq_quadratic_gaussian _ _ _

lemma integrable_gbmExpFactor_mul_gbmMilFactor (r σ h : ℝ) :
    Integrable (fun x => gbmExpFactor r σ h x * gbmMilFactor r σ h x) (gaussianReal 0 1) := by
  have e : (fun x => gbmExpFactor r σ h x * gbmMilFactor r σ h x) = fun x =>
      Real.exp ((r - σ ^ 2 / 2) * h) * ((1 + r * h - σ ^ 2 * h / 2 + σ * Real.sqrt h * x +
        σ ^ 2 / 2 * Real.sqrt h ^ 2 * x ^ 2) * Real.exp (σ * Real.sqrt h * x)) := by
    funext x
    rw [gbmMilFactor_eq_quadratic, gbmExpFactor, Real.exp_add]
    ring
  rw [e]
  exact (integrable_quadratic_mul_exp_gaussian _ _ _ _).const_mul _

/-- `E[B²] = (1 + rh)² + σ²h + σ⁴h²/2` for the Milstein step `B` (Giles 2015, §5.2). -/
lemma integral_gbmMilFactor_sq (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ x, gbmMilFactor r σ h x ^ 2 ∂gaussianReal 0 1 =
      (1 + r * h) ^ 2 + σ ^ 2 * h + (σ ^ 2 * h) ^ 2 / 2 := by
  simp_rw [gbmMilFactor_eq_quadratic]
  rw [integral_sq_quadratic_gaussian, mul_pow σ (Real.sqrt h), Real.sq_sqrt hh]
  ring

/-- `E[AB] = e^{rh}(1 + rh + σ²h + σ⁴h²/2)` for the exact step `A = e^{(r − σ²/2)h + σ√h Z}` and
the Milstein step `B` driven by the same increment (Giles 2015, §5.2). -/
lemma integral_gbmExpFactor_mul_gbmMilFactor (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ x, gbmExpFactor r σ h x * gbmMilFactor r σ h x ∂gaussianReal 0 1 =
      Real.exp (r * h) * (1 + r * h + σ ^ 2 * h + (σ ^ 2 * h) ^ 2 / 2) := by
  have e : (fun x => gbmExpFactor r σ h x * gbmMilFactor r σ h x) = fun x =>
      Real.exp ((r - σ ^ 2 / 2) * h) * ((1 + r * h - σ ^ 2 * h / 2 + σ * Real.sqrt h * x +
        σ ^ 2 / 2 * Real.sqrt h ^ 2 * x ^ 2) * Real.exp (σ * Real.sqrt h * x)) := by
    funext x
    rw [gbmMilFactor_eq_quadratic, gbmExpFactor, Real.exp_add]
    ring
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  have hs' : σ * Real.sqrt h * (σ * Real.sqrt h) = σ ^ 2 * h := by
    rw [← hs]
    ring
  have he : Real.exp (r * h) = Real.exp ((r - σ ^ 2 / 2) * h) * Real.exp (σ ^ 2 * h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e, integral_const_mul, integral_quadratic_mul_exp_gaussian, hs, Real.sq_sqrt hh, he]
  linear_combination (Real.exp ((r - σ ^ 2 / 2) * h) * Real.exp (σ ^ 2 * h / 2)) * hs'

/-! ### The Milstein path -/

/-- The Milstein scheme of Giles 2015, §5.2, for a scalar SDE `dS = a(S) dt + b(S) dW` with
time-independent coefficients: `Ŝ_0 = S₀` and `Ŝ_{n+1} = Ŝ_n + a(Ŝ_n) h + b(Ŝ_n) ΔW_n +
½ b(Ŝ_n) b'(Ŝ_n)(ΔW_n² − h)` (`milsteinStep`), with `ΔW_n = √h Z_n` driven by the normal
increments `z = (Z_0, Z_1, …)`. -/
noncomputable def milsteinPath (a b : ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => S₀
  | i + 1 => milsteinStep a b h (milsteinPath a b h S₀ z i) (Real.sqrt h * z i)

lemma milsteinPath_succ (a b : ℝ → ℝ) (h S₀ : ℝ) (z : ℕ → ℝ) (i : ℕ) :
    milsteinPath a b h S₀ z (i + 1) =
      milsteinStep a b h (milsteinPath a b h S₀ z i) (Real.sqrt h * z i) := rfl

/-- **The Milstein path of GBM is a product** (Giles 2015, §5.2, with `a(S) = rS`, `b(S) = σS`,
`∂b/∂S = σ`): `Ŝ_n = S_0 ∏_{i<n} (1 + rh + σ√h Z_i + ½σ²(h Z_i² − h))`. -/
theorem milsteinPath_gbm (r σ h s₀ : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    milsteinPath (fun S => r * S) (fun S => σ * S) h s₀ z n =
      s₀ * ∏ i ∈ range n, gbmMilFactor r σ h (z i) := by
  have hd : ∀ S : ℝ, deriv (fun S : ℝ => σ * S) S = σ := fun S =>
    (hasDerivAt_const_mul σ).deriv
  induction n with
  | zero => simp [milsteinPath]
  | succ n ih =>
    rw [milsteinPath_succ, ih, Finset.prod_range_succ, milsteinStep, gbmMilFactor, hd]
    ring

/-! ### The second moment of the error -/

/-- **The second moment of the difference of two products of independent factors**:
`E[(S_0 ∏_{i<n} F(Z_i) − S_0 ∏_{i<n} G(Z_i))²] = S_0² (aⁿ − 2bⁿ + cⁿ)` with `a = E[F(Z)²]`,
`b = E[F(Z) G(Z)]`, `c = E[G(Z)²]` (the exact solution and a one-step scheme for GBM, Giles 2015,
§5.1–5.2). -/
theorem integral_sq_prod_sub_prod_of {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hF2 : Integrable (fun x => F x ^ 2) (gaussianReal 0 1))
    (hG2 : Integrable (fun x => G x ^ 2) (gaussianReal 0 1))
    (hFG : Integrable (fun x => F x * G x) (gaussianReal 0 1)) (s₀ : ℝ) (n : ℕ) :
    ∫ z, (s₀ * ∏ i ∈ range n, F (z i) - s₀ * ∏ i ∈ range n, G (z i)) ^ 2 ∂stdNormalSeq =
      s₀ ^ 2 * ((∫ x, F x ^ 2 ∂gaussianReal 0 1) ^ n -
        2 * (∫ x, F x * G x ∂gaussianReal 0 1) ^ n + (∫ x, G x ^ 2 ∂gaussianReal 0 1) ^ n) := by
  have hF2m : Measurable fun x => F x ^ 2 := hF.pow_const 2
  have hG2m : Measurable fun x => G x ^ 2 := hG.pow_const 2
  have hFGm : Measurable fun x => F x * G x := hF.mul hG
  have e : ∀ z : ℕ → ℝ, (s₀ * ∏ i ∈ range n, F (z i) - s₀ * ∏ i ∈ range n, G (z i)) ^ 2 =
      s₀ ^ 2 * ∏ i ∈ range n, F (z i) ^ 2 - 2 * s₀ ^ 2 * ∏ i ∈ range n, (F (z i) * G (z i)) +
        s₀ ^ 2 * ∏ i ∈ range n, G (z i) ^ 2 := fun z => by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow]
    ring
  simp_rw [e]
  have iA : Integrable (fun z : ℕ → ℝ => s₀ ^ 2 * ∏ i ∈ range n, F (z i) ^ 2) stdNormalSeq :=
    (integrable_prod_stdNormalSeq hF2m hF2 n).const_mul _
  have iAB : Integrable (fun z : ℕ → ℝ => 2 * s₀ ^ 2 * ∏ i ∈ range n, (F (z i) * G (z i)))
      stdNormalSeq :=
    (integrable_prod_stdNormalSeq hFGm hFG n).const_mul _
  have iB : Integrable (fun z : ℕ → ℝ => s₀ ^ 2 * ∏ i ∈ range n, G (z i) ^ 2) stdNormalSeq :=
    (integrable_prod_stdNormalSeq hG2m hG2 n).const_mul _
  have iAAB : Integrable (fun z : ℕ → ℝ => s₀ ^ 2 * ∏ i ∈ range n, F (z i) ^ 2 -
      2 * s₀ ^ 2 * ∏ i ∈ range n, (F (z i) * G (z i))) stdNormalSeq :=
    iA.sub iAB
  rw [integral_add iAAB iB, integral_sub iA iAB, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_prod_stdNormalSeq hF2m, integral_prod_stdNormalSeq hFGm,
    integral_prod_stdNormalSeq hG2m]
  ring

/-! ### The algebra of the strong error -/

/-- `|xy| ≤ XY` from `|x| ≤ X` and `|y| ≤ Y`. -/
lemma abs_mul_le_of_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) ((abs_nonneg x).trans hx)

/-- `0 ≤ e^x − 1 − x − x²/2 ≤ x³` for `0 ≤ x ≤ 1`. -/
lemma exp_sub_quadratic_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ Real.exp x - 1 - x - x ^ 2 / 2 ∧ Real.exp x - 1 - x - x ^ 2 / 2 ≤ x ^ 3 := by
  refine ⟨by linarith [Real.quadratic_le_exp_of_nonneg h0], ?_⟩
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith [pow_nonneg h0 3]

/-- **The second-order analogue of `pow_sub_two_mul_pow_add_pow_le`**:
`|aⁿ − 2bⁿ + cⁿ| ≤ n² Mⁿ |a − b| |b − c| + n Mⁿ |a − 2b + c|` for `|a|, |b|, |c| ≤ M` with
`M ≥ 1` (for the Milstein strong error, Giles 2015, §5.2). -/
theorem abs_pow_sub_two_mul_pow_add_pow_le {a b c M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M)
    (hc : |c| ≤ M) (hM : 1 ≤ M) (n : ℕ) :
    |a ^ n - 2 * b ^ n + c ^ n| ≤
      (n : ℝ) ^ 2 * M ^ n * (|a - b| * |b - c|) + n * M ^ n * |a - 2 * b + c| := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hM0 : 0 ≤ M := zero_le_one.trans hM
    have hMn : 0 ≤ M ^ n := pow_nonneg hM0 n
    have hMn1 : M ^ n ≤ M ^ n * M := le_mul_of_one_le_right hMn hM
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hX : 0 ≤ |a - b| * |b - c| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hY : 0 ≤ |a - 2 * b + c| := abs_nonneg _
    have hbc : |b ^ n - c ^ n| ≤ n * M ^ n * |b - c| := by
      have h1 := abs_pow_sub_pow_le b c n
      have h2 : max |b| |c| ^ (n - 1) ≤ M ^ n :=
        (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg b)) (max_le hb hc) (n - 1)).trans
          (pow_le_pow_right₀ hM (Nat.sub_le n 1))
      calc |b ^ n - c ^ n| ≤ |b - c| * n * max |b| |c| ^ (n - 1) := h1
        _ ≤ |b - c| * n * M ^ n :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg _) hn)
        _ = n * M ^ n * |b - c| := by ring
    have hcn : |c ^ n| ≤ M ^ n := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg c) hc n
    have e : a ^ (n + 1) - 2 * b ^ (n + 1) + c ^ (n + 1) =
        a * (a ^ n - 2 * b ^ n + c ^ n) + 2 * ((a - b) * (b ^ n - c ^ n)) +
          (a - 2 * b + c) * c ^ n := by ring
    have t1 : |a * (a ^ n - 2 * b ^ n + c ^ n)| ≤
        M * ((n : ℝ) ^ 2 * M ^ n * (|a - b| * |b - c|) + n * M ^ n * |a - 2 * b + c|) :=
      abs_mul_le_of_le ha ih
    have t2 : |(a - b) * (b ^ n - c ^ n)| ≤ |a - b| * (n * M ^ n * |b - c|) :=
      abs_mul_le_of_le le_rfl hbc
    have t3 : |(a - 2 * b + c) * c ^ n| ≤ |a - 2 * b + c| * M ^ n :=
      abs_mul_le_of_le le_rfl hcn
    have t4 := abs_add_le (a * (a ^ n - 2 * b ^ n + c ^ n) + 2 * ((a - b) * (b ^ n - c ^ n)))
      ((a - 2 * b + c) * c ^ n)
    have t5 := abs_add_le (a * (a ^ n - 2 * b ^ n + c ^ n)) (2 * ((a - b) * (b ^ n - c ^ n)))
    have t6 : |2 * ((a - b) * (b ^ n - c ^ n))| = 2 * |(a - b) * (b ^ n - c ^ n)| := by
      rw [abs_mul, abs_two]
    have k1 : 0 ≤ 2 * n * (M ^ n * M - M ^ n) * (|a - b| * |b - c|) :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hn) (sub_nonneg.2 hMn1)) hX
    have k2 : 0 ≤ M ^ n * M * (|a - b| * |b - c|) := mul_nonneg (mul_nonneg hMn hM0) hX
    have k3 : 0 ≤ (M ^ n * M - M ^ n) * |a - 2 * b + c| := mul_nonneg (sub_nonneg.2 hMn1) hY
    rw [e, pow_succ M n]
    push_cast
    linarith

/-- The one-step second moments of the Milstein scheme for GBM are bounded by `e^m`,
`m ≥ 2|u| + v` (with `u = rh`, `v = σ²h`). -/
lemma mil_one_step_bounds {u v m : ℝ} (hv : 0 ≤ v) (hm : 2 * |u| + v ≤ m) :
    |Real.exp (2 * u + v)| ≤ Real.exp m ∧ |Real.exp u * (1 + u + v + v ^ 2 / 2)| ≤ Real.exp m ∧
      |(1 + u) ^ 2 + v + v ^ 2 / 2| ≤ Real.exp m := by
  have hu1 := le_abs_self u
  have hu2 := neg_abs_le u
  have hu0 := abs_nonneg u
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith)
  · have hq := Real.quadratic_le_exp_of_nonneg (add_nonneg hu0 hv)
    have h1 : |1 + u + v + v ^ 2 / 2| ≤ Real.exp (|u| + v) := by
      rw [abs_le]
      constructor <;> linarith [sq_nonneg |u|, mul_nonneg hu0 hv, sq_nonneg v]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp u * |1 + u + v + v ^ 2 / 2| ≤ Real.exp u * Real.exp (|u| + v) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (u + (|u| + v)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp m := Real.exp_le_exp.2 (by linarith)
  · have hc0 : 0 ≤ (1 + u) ^ 2 + v + v ^ 2 / 2 :=
      add_nonneg (add_nonneg (sq_nonneg _) hv) (by positivity)
    rw [abs_of_nonneg hc0]
    have e1 : |1 + u| ≤ Real.exp |u| := by
      have := Real.add_one_le_exp |u|
      rw [abs_le]
      constructor <;> linarith
    have h1 : (1 + u) ^ 2 ≤ Real.exp |u| ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) e1 2
    have h3 : 1 ≤ Real.exp |u| ^ 2 := one_le_pow₀ (Real.one_le_exp hu0)
    have h4 : 1 + v + v ^ 2 / 2 ≤ Real.exp v := Real.quadratic_le_exp_of_nonneg hv
    have h5 : Real.exp (2 * |u| + v) = Real.exp |u| ^ 2 * Real.exp v := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h6 : Real.exp (2 * |u| + v) ≤ Real.exp m := Real.exp_le_exp.2 hm
    have h7 : 1 ≤ Real.exp v := Real.one_le_exp hv
    linarith [mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h7)]

/-- For `w ≥ |u| + v` with `w ≤ 1` and `v ≥ 0`, the one-step second moments of the Milstein scheme
agree to second order and their second difference is of third order: `|a − b| ≤ 5w²`,
`|b − c| ≤ 6w²` and `|a − 2b + c| ≤ 16w³`, for `a = e^{2u+v}`, `b = e^u(1 + u + v + v²/2)` and
`c = (1 + u)² + v + v²/2` (with `u = rh`, `v = σ²h`, Giles 2015, §5.2). -/
lemma mil_one_step_diff {u v w : ℝ} (hv : 0 ≤ v) (huv : |u| + v ≤ w) (hw : w ≤ 1) :
    |Real.exp (2 * u + v) - Real.exp u * (1 + u + v + v ^ 2 / 2)| ≤ 5 * w ^ 2 ∧
      |Real.exp u * (1 + u + v + v ^ 2 / 2) - ((1 + u) ^ 2 + v + v ^ 2 / 2)| ≤ 6 * w ^ 2 ∧
      |Real.exp (2 * u + v) - 2 * (Real.exp u * (1 + u + v + v ^ 2 / 2)) +
        ((1 + u) ^ 2 + v + v ^ 2 / 2)| ≤ 16 * w ^ 3 := by
  have hu0 := abs_nonneg u
  have huw : |u| ≤ w := by linarith
  have hvw : v ≤ w := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hu1 : |u| ≤ 1 := huw.trans hw
  have hv1 : v ≤ 1 := hvw.trans hw
  obtain ⟨hu1a, hu1b⟩ := abs_le.1 hu1
  have hu2 : u ^ 2 ≤ w ^ 2 := by
    rw [← sq_abs u]
    exact pow_le_pow_left₀ hu0 huw 2
  have hvv : v ^ 2 ≤ v := by
    rw [sq]
    exact mul_le_of_le_one_left hv hv1
  have hv2 : v ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hv hvw 2
  have hw3 : 0 ≤ w ^ 3 := pow_nonneg hw0 3
  have hw4 : w ^ 4 ≤ w ^ 3 := pow_le_pow_of_le_one hw0 hw (by norm_num)
  have hw5 : w ^ 5 ≤ w ^ 3 := pow_le_pow_of_le_one hw0 hw (by norm_num)
  have hexpu : Real.exp u ≤ 3 := (Real.exp_le_exp.2 hu1b).trans Real.exp_one_lt_three.le
  have hexpv : Real.exp v ≤ 3 := (Real.exp_le_exp.2 hv1).trans Real.exp_one_lt_three.le
  have hE : |Real.exp u - 1 - u| ≤ w ^ 2 := (Real.abs_exp_sub_one_sub_id_le hu1).trans hu2
  obtain ⟨hF0, hF1⟩ := exp_sub_quadratic_le hv hv1
  have hFw : Real.exp v - 1 - v - v ^ 2 / 2 ≤ w ^ 3 := hF1.trans (pow_le_pow_left₀ hv hvw 3)
  have hFa : |Real.exp v - 1 - v - v ^ 2 / 2| ≤ w ^ 3 := by
    rw [abs_of_nonneg hF0]
    exact hFw
  have hq0 : 0 ≤ v + v ^ 2 / 2 := by positivity
  have hq : |v + v ^ 2 / 2| ≤ 3 / 2 * w := by
    rw [abs_of_nonneg hq0]
    linarith
  have h1u : |1 + u| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · have huv1 : |u + v| ≤ w := by
      have := abs_add_le u v
      rw [abs_of_nonneg hv] at this
      linarith
    have hG := Real.abs_exp_sub_one_sub_id_le (huv1.trans hw)
    have huv2 : (u + v) ^ 2 ≤ w ^ 2 := by
      rw [← sq_abs (u + v)]
      exact pow_le_pow_left₀ (abs_nonneg _) huv1 2
    obtain ⟨hG1, hG2⟩ := abs_le.1 (hG.trans huv2)
    have e1 : Real.exp (2 * u + v) - Real.exp u * (1 + u + v + v ^ 2 / 2) =
        Real.exp u * (Real.exp (u + v) - 1 - (u + v) - v ^ 2 / 2) := by
      have : Real.exp (2 * u + v) = Real.exp u * Real.exp (u + v) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this]
      ring
    have h1 : |Real.exp (u + v) - 1 - (u + v) - v ^ 2 / 2| ≤ 3 / 2 * w ^ 2 := by
      rw [abs_le]
      constructor <;> linarith [sq_nonneg v]
    rw [e1, abs_mul, abs_of_pos (Real.exp_pos u)]
    calc Real.exp u * |Real.exp (u + v) - 1 - (u + v) - v ^ 2 / 2| ≤ 3 * (3 / 2 * w ^ 2) :=
          mul_le_mul hexpu h1 (abs_nonneg _) (by norm_num)
      _ ≤ 5 * w ^ 2 := by linarith [sq_nonneg w]
  · have e2 : Real.exp u * (1 + u + v + v ^ 2 / 2) - ((1 + u) ^ 2 + v + v ^ 2 / 2) =
        u * (v + v ^ 2 / 2) + (Real.exp u - 1 - u) * (1 + u + v + v ^ 2 / 2) := by ring
    have hb : |1 + u + v + v ^ 2 / 2| ≤ 4 := by
      rw [abs_le]
      constructor <;> linarith [sq_nonneg v]
    have k1 := abs_mul_le_of_le huw hq
    have k2 := abs_mul_le_of_le hE hb
    have k3 := abs_add_le (u * (v + v ^ 2 / 2)) ((Real.exp u - 1 - u) * (1 + u + v + v ^ 2 / 2))
    rw [e2]
    linarith [sq_nonneg w]
  · have hX : Real.exp (2 * u + v) = Real.exp u * Real.exp u * Real.exp v := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have e3 : Real.exp (2 * u + v) - 2 * (Real.exp u * (1 + u + v + v ^ 2 / 2)) +
        ((1 + u) ^ 2 + v + v ^ 2 / 2) =
        u ^ 2 * (v + v ^ 2 / 2) + (Real.exp v - 1 - v - v ^ 2 / 2) * (1 + u) ^ 2 +
          2 * ((Real.exp u - 1 - u) * u * (v + v ^ 2 / 2)) +
          2 * ((Real.exp u - 1 - u) * (Real.exp v - 1 - v - v ^ 2 / 2) * (1 + u)) +
          Real.exp v * (Real.exp u - 1 - u) ^ 2 := by
      rw [hX]
      ring
    have h1u2 : (1 + u) ^ 2 ≤ 4 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1u 2
      rw [sq_abs] at this
      linarith
    have k1 : u ^ 2 * (v + v ^ 2 / 2) ≤ w ^ 2 * (3 / 2 * w) :=
      mul_le_mul hu2 (by linarith) hq0 (sq_nonneg w)
    have k1' : 0 ≤ u ^ 2 * (v + v ^ 2 / 2) := mul_nonneg (sq_nonneg u) hq0
    have k2 : (Real.exp v - 1 - v - v ^ 2 / 2) * (1 + u) ^ 2 ≤ w ^ 3 * 4 :=
      mul_le_mul hFw h1u2 (sq_nonneg _) hw3
    have k2' : 0 ≤ (Real.exp v - 1 - v - v ^ 2 / 2) * (1 + u) ^ 2 :=
      mul_nonneg hF0 (sq_nonneg _)
    have k3 := abs_mul_le_of_le (abs_mul_le_of_le hE huw) hq
    have k4 := abs_mul_le_of_le (abs_mul_le_of_le hE hFa) h1u
    have hE2 : (Real.exp u - 1 - u) ^ 2 ≤ (w ^ 2) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hE 2
      rwa [sq_abs] at this
    have k5 : Real.exp v * (Real.exp u - 1 - u) ^ 2 ≤ 3 * (w ^ 2) ^ 2 :=
      mul_le_mul hexpv hE2 (sq_nonneg _) (by norm_num)
    have k5' : 0 ≤ Real.exp v * (Real.exp u - 1 - u) ^ 2 :=
      mul_nonneg (Real.exp_pos v).le (sq_nonneg _)
    obtain ⟨k3a, k3b⟩ := abs_le.1 k3
    obtain ⟨k4a, k4b⟩ := abs_le.1 k4
    rw [e3, abs_le]
    constructor <;> linarith only [k1, k1', k2, k2', k3a, k3b, k4a, k4b, k5, k5', hw3, hw4, hw5]

/-- The combination of the one-step bounds: with `|a|, |b|, |c| ≤ M`, `M ≥ 1`, and the one-step
bounds of `mil_one_step_diff` when `qh ≤ 1`,
`aⁿ − 2bⁿ + cⁿ ≤ Mⁿ q² (30 q² (nh)² + 16 q (nh) + 4) h²`. -/
lemma mil_combo_le {a b c M q h : ℝ} (n : ℕ) (hh : 0 ≤ h) (hq : 0 ≤ q) (hM : 1 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M)
    (hsmall : q * h ≤ 1 → |a - b| ≤ 5 * (q * h) ^ 2 ∧ |b - c| ≤ 6 * (q * h) ^ 2 ∧
      |a - 2 * b + c| ≤ 16 * (q * h) ^ 3) :
    a ^ n - 2 * b ^ n + c ^ n ≤
      M ^ n * q ^ 2 * (30 * q ^ 2 * (n * h) ^ 2 + 16 * q * (n * h) + 4) * h ^ 2 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMn : 0 ≤ M ^ n := pow_nonneg hM0 n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hs : q * h ≤ 1
  · obtain ⟨hab, hbc, habc⟩ := hsmall hs
    have h1 := abs_pow_sub_two_mul_pow_add_pow_le ha hb hc hM n
    have k1 : |a - b| * |b - c| ≤ 5 * (q * h) ^ 2 * (6 * (q * h) ^ 2) :=
      mul_le_mul hab hbc (abs_nonneg _) (by positivity)
    have k2 : (n : ℝ) ^ 2 * M ^ n * (|a - b| * |b - c|) ≤
        (n : ℝ) ^ 2 * M ^ n * (5 * (q * h) ^ 2 * (6 * (q * h) ^ 2)) :=
      mul_le_mul_of_nonneg_left k1 (mul_nonneg (sq_nonneg _) hMn)
    have k3 : (n : ℝ) * M ^ n * |a - 2 * b + c| ≤ (n : ℝ) * M ^ n * (16 * (q * h) ^ 3) :=
      mul_le_mul_of_nonneg_left habc (mul_nonneg hn hMn)
    have k4 : 0 ≤ M ^ n * q ^ 2 * 4 * h ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hMn (sq_nonneg q)) (by norm_num)) (sq_nonneg h)
    have key : (n : ℝ) ^ 2 * M ^ n * (5 * (q * h) ^ 2 * (6 * (q * h) ^ 2)) +
        (n : ℝ) * M ^ n * (16 * (q * h) ^ 3) + M ^ n * q ^ 2 * 4 * h ^ 2 =
        M ^ n * q ^ 2 * (30 * q ^ 2 * (n * h) ^ 2 + 16 * q * (n * h) + 4) * h ^ 2 := by ring
    linarith [le_abs_self (a ^ n - 2 * b ^ n + c ^ n)]
  · have hs : 1 < q * h := not_le.mp hs
    have h1 := pow_sub_two_mul_pow_add_pow_le_four ha hb hc n
    have hs2 : 1 ≤ (q * h) ^ 2 := one_le_pow₀ hs.le
    have k4 : M ^ n * 4 ≤ M ^ n * 4 * (q * h) ^ 2 :=
      le_mul_of_one_le_right (mul_nonneg hMn (by norm_num)) hs2
    have k5 : 0 ≤ M ^ n * q ^ 2 * (30 * q ^ 2 * (n * h) ^ 2 + 16 * q * (n * h)) * h ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hMn (sq_nonneg q))
        (add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) hq)
          (mul_nonneg hn hh)))) (sq_nonneg h)
    have key : M ^ n * q ^ 2 * (30 * q ^ 2 * (n * h) ^ 2 + 16 * q * (n * h) + 4) * h ^ 2 =
        M ^ n * q ^ 2 * (30 * q ^ 2 * (n * h) ^ 2 + 16 * q * (n * h)) * h ^ 2 +
          M ^ n * 4 * (q * h) ^ 2 := by ring
    linarith

/-- **The algebraic core of the Milstein strong error**: for the one-step moments of
`integral_gbmExpFactor_sq`, `integral_gbmExpFactor_mul_gbmMilFactor` and `integral_gbmMilFactor_sq`,
`aⁿ − 2bⁿ + cⁿ ≤ e^{(2|r|+σ²)nh} (|r| + σ²)² (30(|r| + σ²)²(nh)² + 16(|r| + σ²)nh + 4) h²`. -/
lemma gbm_mil_moment_combo_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    Real.exp ((2 * r + σ ^ 2) * h) ^ n -
        2 * (Real.exp (r * h) * (1 + r * h + σ ^ 2 * h + (σ ^ 2 * h) ^ 2 / 2)) ^ n +
        ((1 + r * h) ^ 2 + σ ^ 2 * h + (σ ^ 2 * h) ^ 2 / 2) ^ n ≤
      Real.exp ((2 * |r| + σ ^ 2) * (n * h)) * (|r| + σ ^ 2) ^ 2 *
        (30 * (|r| + σ ^ 2) ^ 2 * (n * h) ^ 2 + 16 * (|r| + σ ^ 2) * (n * h) + 4) * h ^ 2 := by
  have hv : 0 ≤ σ ^ 2 * h := mul_nonneg (sq_nonneg σ) hh
  have hm : 2 * |r * h| + σ ^ 2 * h ≤ (2 * |r| + σ ^ 2) * h := by
    rw [abs_mul, abs_of_nonneg hh]
    linarith
  have hMn : Real.exp ((2 * |r| + σ ^ 2) * h) ^ n = Real.exp ((2 * |r| + σ ^ 2) * (n * h)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [show (2 * r + σ ^ 2) * h = 2 * (r * h) + σ ^ 2 * h by ring, ← hMn]
  obtain ⟨ha, hb, hc⟩ := mil_one_step_bounds hv hm
  refine mil_combo_le n hh (by positivity) (Real.one_le_exp (mul_nonneg (by positivity) hh))
    ha hb hc fun hs => mil_one_step_diff hv ?_ hs
  rw [abs_mul, abs_of_nonneg hh]
  linarith

/-! ### The strong error -/

/-- The constant of the Milstein strong error bound for GBM,
`C(t) = S_0² e^{(2|r| + σ²)t} (|r| + σ²)² (30(|r| + σ²)² t² + 16(|r| + σ²)t + 4)`
(Giles 2015, §5.2). -/
noncomputable def gbmMilStrongConst (r σ t s₀ : ℝ) : ℝ :=
  s₀ ^ 2 * Real.exp ((2 * |r| + σ ^ 2) * t) * (|r| + σ ^ 2) ^ 2 *
    (30 * (|r| + σ ^ 2) ^ 2 * t ^ 2 + 16 * (|r| + σ ^ 2) * t + 4)

lemma gbmMilStrongConst_nonneg (r σ s₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gbmMilStrongConst r σ t s₀ := by
  unfold gbmMilStrongConst
  positivity

/-- **First-order strong convergence of the Milstein scheme for GBM** (Giles 2015, §5.2: the
Milstein discretisation "gives first order strong convergence"; Figure 5.5).  With timestep
`h ≥ 0`, the exact solution `S_{t_n} = S_0 exp((r − σ²/2) t_n + σ W_{t_n})` at the grid time
`t_n = nh`, `W_{t_n} = √h ∑_{i<n} Z_i`, and the Milstein value `Ŝ_n` driven by the same increments
satisfy `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h²`, where
`C(t) = S_0² e^{(2|r| + σ²)t} (|r| + σ²)² (30(|r| + σ²)² t² + 16(|r| + σ²)t + 4)`. -/
theorem gbm_mil_strong_error (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
        milsteinPath (fun S => r * S) (fun S => σ * S) h s₀ z n) ^ 2 ∂stdNormalSeq ≤
      gbmMilStrongConst r σ (n * h) s₀ * h ^ 2 := by
  simp_rw [gbmExp_eq_prod, milsteinPath_gbm]
  rw [integral_sq_prod_sub_prod_of (measurable_gbmExpFactor r σ h) (measurable_gbmMilFactor r σ h)
      (integrable_gbmExpFactor_sq r σ h) (integrable_gbmMilFactor_sq r σ h)
      (integrable_gbmExpFactor_mul_gbmMilFactor r σ h) s₀ n,
    integral_gbmExpFactor_sq r σ hh, integral_gbmExpFactor_mul_gbmMilFactor r σ hh,
    integral_gbmMilFactor_sq r σ hh, gbmMilStrongConst]
  calc _ ≤ s₀ ^ 2 * (Real.exp ((2 * |r| + σ ^ 2) * (n * h)) * (|r| + σ ^ 2) ^ 2 *
        (30 * (|r| + σ ^ 2) ^ 2 * (n * h) ^ 2 + 16 * (|r| + σ ^ 2) * (n * h) + 4) * h ^ 2) :=
        mul_le_mul_of_nonneg_left (gbm_mil_moment_combo_le r σ hh n) (sq_nonneg s₀)
    _ = _ := by ring

/-! ### The levels -/

/-- The level-`ℓ` Milstein approximation of `S_T` for GBM (Giles 2015, §5.2): `2^ℓ` steps of size
`h_ℓ = T 2^{−ℓ}` driven by the increments `Z_i`. -/
noncomputable def gbmMil (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ)

lemma gbmMil_eq_prod (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmMil r σ T s₀ ℓ z = s₀ * ∏ i ∈ range (2 ^ ℓ), gbmMilFactor r σ (T / 2 ^ ℓ) (z i) :=
  milsteinPath_gbm r σ (T / 2 ^ ℓ) s₀ z (2 ^ ℓ)

lemma measurable_gbmMil (r σ T s₀ : ℝ) (ℓ : ℕ) : Measurable (gbmMil r σ T s₀ ℓ) := by
  have e : gbmMil r σ T s₀ ℓ =
      fun z => s₀ * ∏ i ∈ range (2 ^ ℓ), gbmMilFactor r σ (T / 2 ^ ℓ) (z i) :=
    funext (gbmMil_eq_prod r σ T s₀ ℓ)
  rw [e]
  exact (Finset.measurable_prod _ fun i _ =>
    (measurable_gbmMilFactor r σ (T / 2 ^ ℓ)).comp (measurable_pi_apply i)).const_mul s₀

lemma memLp_gbmMil (r σ T s₀ : ℝ) (ℓ : ℕ) : MemLp (gbmMil r σ T s₀ ℓ) 2 stdNormalSeq := by
  refine (memLp_two_iff_integrable_sq (measurable_gbmMil r σ T s₀ ℓ).aestronglyMeasurable).2 ?_
  have e : (fun z => gbmMil r σ T s₀ ℓ z ^ 2) =
      fun z => s₀ ^ 2 * ∏ i ∈ range (2 ^ ℓ), gbmMilFactor r σ (T / 2 ^ ℓ) (z i) ^ 2 := by
    funext z
    rw [gbmMil_eq_prod, mul_pow, ← Finset.prod_pow]
  rw [e]
  exact (integrable_prod_stdNormalSeq ((measurable_gbmMilFactor r σ _).pow_const 2)
    (integrable_gbmMilFactor_sq r σ _) _).const_mul _

/-- **The Milstein strong error on level `ℓ`** (Giles 2015, §5.2): `E[(S_T − Ŝ_ℓ)²] ≤ C(T) h_ℓ²`
with `h_ℓ = T 2^{−ℓ}`. -/
theorem gbm_mil_strong_error_level (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ : ℕ) :
    ∫ z, (gbmExact r σ T s₀ ℓ z - gbmMil r σ T s₀ ℓ z) ^ 2 ∂stdNormalSeq ≤
      gbmMilStrongConst r σ T s₀ * (T / 2 ^ ℓ) ^ 2 := by
  have hh : 0 ≤ T / 2 ^ ℓ := div_nonneg hT (by positivity)
  have h := gbm_mil_strong_error r σ s₀ hh (2 ^ ℓ)
  rw [cast_two_pow_mul_div] at h
  exact h

lemma integrable_sq_gbm_mil_err (r σ T s₀ : ℝ) (ℓ : ℕ) :
    Integrable (fun z => (gbmExact r σ T s₀ ℓ z - gbmMil r σ T s₀ ℓ z) ^ 2) stdNormalSeq :=
  ((memLp_gbmExact r σ T s₀ ℓ).sub (memLp_gbmMil r σ T s₀ ℓ)).integrable_sq

/-! ### The rates -/

/-- **The weak error of the Milstein scheme for GBM with a Lipschitz payoff** (Giles 2015, §5.2:
"`α = 1`"; Theorem 1 (i)).  For `|g(x) − g(y)| ≤ K|x − y|` and `T ≥ 0`,
`|E[g(Ŝ_ℓ) − g(S_T)]| ≤ K √(C(T) T²) 2^{−ℓ}`, where `S_T` is the exact solution (whose law does not
depend on the level, `map_gbmExact`). -/
theorem gbm_mil_weak_error_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (ℓ : ℕ) :
    |∫ z, g (gbmMil r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq| ≤
      K * Real.sqrt (gbmMilStrongConst r σ T s₀ * T ^ 2) * ((2 : ℝ) ^ ℓ)⁻¹ := by
  obtain ⟨hK, hgc⟩ := continuous_of_abs_sub_le hg
  have hC := gbmMilStrongConst_nonneg r σ s₀ hT
  have hA : MemLp (fun z => g (gbmMil r σ T s₀ ℓ z)) 2 stdNormalSeq :=
    memLp_two_comp_of_abs_sub_le hg (memLp_gbmMil r σ T s₀ ℓ)
  have hB : ∀ k, MemLp (fun z => g (gbmExact r σ T s₀ k z)) 2 stdNormalSeq := fun k =>
    memLp_two_comp_of_abs_sub_le hg (memLp_gbmExact r σ T s₀ k)
  have e1 : ∫ z, g (gbmMil r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq =
      ∫ z, g (gbmMil r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z) ∂stdNormalSeq := by
    rw [integral_sub (hA.integrable one_le_two) ((hB 0).integrable one_le_two),
      integral_sub (hA.integrable one_le_two) ((hB ℓ).integrable one_le_two),
      integral_comp_gbmExact r σ T s₀ ℓ hgc.measurable]
  have hD : MemLp (fun z => g (gbmMil r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z)) 2
      stdNormalSeq :=
    hA.sub (hB ℓ)
  have hpt : ∀ z, (g (gbmMil r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z)) ^ 2 ≤
      K ^ 2 * (gbmExact r σ T s₀ ℓ z - gbmMil r σ T s₀ ℓ z) ^ 2 := fun z => by
    have h1 := hg (gbmMil r σ T s₀ ℓ z) (gbmExact r σ T s₀ ℓ z)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    linarith
  have hint : ∫ z, (g (gbmMil r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z)) ^ 2 ∂stdNormalSeq ≤
      K ^ 2 * ∫ z, (gbmExact r σ T s₀ ℓ z - gbmMil r σ T s₀ ℓ z) ^ 2 ∂stdNormalSeq := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
      ((integrable_sq_gbm_mil_err r σ T s₀ ℓ).const_mul _) (Filter.Eventually.of_forall hpt)
  have hstrong := gbm_mil_strong_error_level r σ s₀ hT ℓ
  have hsq : (∫ z, g (gbmMil r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq) ^ 2 ≤
      (K * Real.sqrt (gbmMilStrongConst r σ T s₀ * T ^ 2) * ((2 : ℝ) ^ ℓ)⁻¹) ^ 2 := by
    rw [e1, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hC (sq_nonneg T))]
    calc _ ≤ ∫ z, (g (gbmMil r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z)) ^ 2 ∂stdNormalSeq :=
          sq_integral_le_integral_sq_of_memLp hD
      _ ≤ K ^ 2 * (gbmMilStrongConst r σ T s₀ * (T / 2 ^ ℓ) ^ 2) :=
          hint.trans (mul_le_mul_of_nonneg_left hstrong (sq_nonneg K))
      _ = _ := by ring
  have := sq_le_sq.1 hsq
  rwa [abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ K * Real.sqrt (gbmMilStrongConst r σ T s₀ * T ^ 2) * ((2 : ℝ) ^ ℓ)⁻¹)] at this

/-- **The variance of the Milstein level corrections for GBM** (Giles 2015, §5.2: "`V_ℓ` is now
`O(h_ℓ²)`, leading to … `β = 2`"; Theorem 1 (iii)).  The correction on level `ℓ + 1` is the payoff
of the fine path minus the payoff of the coarse path driven by the summed increments
`(Z_{2k} + Z_{2k+1})/√2`; its variance is at most `10 K² C(T) T² 4^{−(ℓ+1)}`. -/
theorem gbm_mil_correction_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (ℓ : ℕ) :
    variance (fun z => g (gbmMil r σ T s₀ (ℓ + 1) z) - g (gbmMil r σ T s₀ ℓ (pairAvg z)))
        stdNormalSeq ≤
      10 * K ^ 2 * (gbmMilStrongConst r σ T s₀ * T ^ 2) * ((4 : ℝ) ^ (ℓ + 1))⁻¹ := by
  obtain ⟨-, hgc⟩ := continuous_of_abs_sub_le hg
  have hm1 := measurable_gbmMil r σ T s₀ (ℓ + 1)
  have hm0 := (measurable_gbmMil r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable
  have hY : AEStronglyMeasurable
      (fun z => g (gbmMil r σ T s₀ (ℓ + 1) z) - g (gbmMil r σ T s₀ ℓ (pairAvg z))) stdNormalSeq :=
    ((hgc.measurable.comp hm1).sub (hgc.measurable.comp hm0)).aestronglyMeasurable
  refine (variance_le_expectation_sq hY).trans ?_
  simp only [Pi.pow_apply]
  have hI1 := integrable_sq_gbm_mil_err r σ T s₀ (ℓ + 1)
  have hI0' := integrable_sq_gbm_mil_err r σ T s₀ ℓ
  have hI0 : Integrable (fun z => (gbmExact r σ T s₀ ℓ (pairAvg z) -
      gbmMil r σ T s₀ ℓ (pairAvg z)) ^ 2) stdNormalSeq :=
    (measurePreserving_pairAvg.integrable_comp hI0'.aestronglyMeasurable).2 hI0'
  have hpt : ∀ z, (g (gbmMil r σ T s₀ (ℓ + 1) z) - g (gbmMil r σ T s₀ ℓ (pairAvg z))) ^ 2 ≤
      2 * K ^ 2 * (gbmExact r σ T s₀ (ℓ + 1) z - gbmMil r σ T s₀ (ℓ + 1) z) ^ 2 +
        2 * K ^ 2 * (gbmExact r σ T s₀ ℓ (pairAvg z) - gbmMil r σ T s₀ ℓ (pairAvg z)) ^ 2 :=
    fun z => by
    have h1 := hg (gbmMil r σ T s₀ (ℓ + 1) z) (gbmMil r σ T s₀ ℓ (pairAvg z))
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    rw [gbmExact_pairAvg]
    linarith [mul_nonneg (sq_nonneg K) (sq_nonneg (gbmExact r σ T s₀ (ℓ + 1) z -
      gbmMil r σ T s₀ (ℓ + 1) z + (gbmExact r σ T s₀ (ℓ + 1) z - gbmMil r σ T s₀ ℓ (pairAvg z))))]
  have hK2 : (0 : ℝ) ≤ 2 * K ^ 2 := by positivity
  have hs1 := gbm_mil_strong_error_level r σ s₀ hT (ℓ + 1)
  have hs0 := gbm_mil_strong_error_level r σ s₀ hT ℓ
  calc ∫ z, (g (gbmMil r σ T s₀ (ℓ + 1) z) - g (gbmMil r σ T s₀ ℓ (pairAvg z))) ^ 2 ∂stdNormalSeq
      ≤ ∫ z, (2 * K ^ 2 * (gbmExact r σ T s₀ (ℓ + 1) z - gbmMil r σ T s₀ (ℓ + 1) z) ^ 2 +
          2 * K ^ 2 * (gbmExact r σ T s₀ ℓ (pairAvg z) - gbmMil r σ T s₀ ℓ (pairAvg z)) ^ 2)
          ∂stdNormalSeq :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
          ((hI1.const_mul (2 * K ^ 2)).add (hI0.const_mul (2 * K ^ 2)))
          (Filter.Eventually.of_forall hpt)
    _ = 2 * K ^ 2 * ∫ z, (gbmExact r σ T s₀ (ℓ + 1) z - gbmMil r σ T s₀ (ℓ + 1) z) ^ 2
          ∂stdNormalSeq +
        2 * K ^ 2 * ∫ z, (gbmExact r σ T s₀ ℓ z - gbmMil r σ T s₀ ℓ z) ^ 2 ∂stdNormalSeq := by
        rw [integral_add (hI1.const_mul _) (hI0.const_mul _), integral_const_mul,
          integral_const_mul, integral_comp_of_measurePreserving measurePreserving_pairAvg
            hI0'.aestronglyMeasurable]
    _ ≤ 2 * K ^ 2 * (gbmMilStrongConst r σ T s₀ * (T / 2 ^ (ℓ + 1)) ^ 2) +
        2 * K ^ 2 * (gbmMilStrongConst r σ T s₀ * (T / 2 ^ ℓ) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hs1 hK2) (mul_le_mul_of_nonneg_left hs0 hK2)
    _ = 10 * K ^ 2 * (gbmMilStrongConst r σ T s₀ * T ^ 2) * ((4 : ℝ) ^ (ℓ + 1))⁻¹ := by
        have e2 : T / 2 ^ ℓ = 2 * (T / 2 ^ (ℓ + 1)) := by
          rw [pow_succ, ← div_div, mul_div_cancel₀ _ two_ne_zero]
        have e4 : (4 : ℝ) ^ (ℓ + 1) = ((2 : ℝ) ^ (ℓ + 1)) ^ 2 := by
          rw [pow_right_comm]
          norm_num
        have e5 : (T / 2 ^ (ℓ + 1)) ^ 2 = T ^ 2 * ((4 : ℝ) ^ (ℓ + 1))⁻¹ := by
          rw [div_pow, ← e4, div_eq_mul_inv]
        rw [e2, mul_pow, e5]
        ring

/-! ### Theorem 1 -/

/-- `2^{−2ℓ} = 4^{−ℓ}`. -/
lemma two_rpow_neg_two_mul (ℓ : ℕ) : (2 : ℝ) ^ (-(2 * (ℓ : ℝ))) = ((4 : ℝ) ^ ℓ)⁻¹ := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_natCast, Real.rpow_ofNat]
  norm_num

/-- **Theorem 1 for the Milstein MLMC estimator of GBM** (Giles 2015, §5.2 and Figure 5.5, with
Theorem 1 and (2.4), §2.1: "`V_ℓ` is now `O(h_ℓ²)`, leading to `α = 1, β = 2, γ = 1`").  Let
`dS = rS dt + σS dW`, `S_0 = s₀`, `T ≥ 0`, and let `g` be `K`-Lipschitz (for example the call payoff
`e^{−rT} max(S_T − K', 0)`).  Level `ℓ` uses `2^ℓ` Milstein steps of size `h_ℓ = T 2^{−ℓ}`; its
correction is the payoff of the fine path minus the payoff of the coarse path driven by the summed
increments, the samples are independent, and a level-`ℓ` sample costs `2^ℓ`.  Then there is
`c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel
estimator of `E[g(S_T)] = E[g(s₀ e^{(r − σ²/2)T + σ √T Z})]`, `Z ~ N(0,1)`, has a
square-integrable error with mean square `< ε²`, and cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²`.  No rate is
assumed: the weak rate `α = 1` (`gbm_mil_weak_error_le`), the variance rate `β = 2`
(`gbm_mil_correction_variance_le`) and (2.4) are proved. -/
theorem gbm_mil_mlmc_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun ℓ z => g (gbmMil r σ T s₀ ℓ z))
              (fun ℓ z => g (gbmMil r σ T s₀ ℓ (pairAvg z)))) (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun ℓ z => g (gbmMil r σ T s₀ ℓ z))
              (fun ℓ z => g (gbmMil r σ T s₀ ℓ (pairAvg z)))) (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨hK, hgc⟩ := continuous_of_abs_sub_le hg
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hC := gbmMilStrongConst_nonneg r σ s₀ hT
  -- the target: `E[g(S_T)]`, computed from the level-`0` increment
  have hPint : ∫ z, g (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq =
      ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1 := by
    simp_rw [gbmExact_zero]
    have hF : Measurable fun w : ℝ =>
        g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) :=
      hgc.measurable.comp (by fun_prop)
    exact integral_comp_of_measurePreserving
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0) hF.aestronglyMeasurable
  have hP : MemLp (fun z => g (gbmExact r σ T s₀ 0 z)) 2 stdNormalSeq :=
    memLp_two_comp_of_abs_sub_le hg (memLp_gbmExact r σ T s₀ 0)
  have hPf : ∀ ℓ, MemLp (fun z => g (gbmMil r σ T s₀ ℓ z)) 2 stdNormalSeq := fun ℓ =>
    memLp_two_comp_of_abs_sub_le hg (memLp_gbmMil r σ T s₀ ℓ)
  have hPfm : ∀ ℓ, Measurable (fun z => g (gbmMil r σ T s₀ ℓ z)) := fun ℓ =>
    hgc.measurable.comp (measurable_gbmMil r σ T s₀ ℓ)
  have hPcm : ∀ ℓ, Measurable (fun z => g (gbmMil r σ T s₀ ℓ (pairAvg z))) := fun ℓ =>
    (hPfm ℓ).comp measurePreserving_pairAvg.measurable
  have hPc : ∀ ℓ, MemLp (fun z => g (gbmMil r σ T s₀ ℓ (pairAvg z))) 2 stdNormalSeq := fun ℓ =>
    (hPf ℓ).comp_measurePreserving measurePreserving_pairAvg
  -- (2.4): the coarse path has the law of the fine path of the level below
  have h24 : ∀ ℓ, ∫ z, g (gbmMil r σ T s₀ ℓ z) ∂stdNormalSeq =
      ∫ z, g (gbmMil r σ T s₀ ℓ (pairAvg z)) ∂stdNormalSeq := fun ℓ =>
    (integral_comp_of_measurePreserving measurePreserving_pairAvg
      (hPfm ℓ).aestronglyMeasurable).symm
  -- (i): the weak rate `α = 1`
  have hc₁ : 0 < K * Real.sqrt (gbmMilStrongConst r σ T s₀ * T ^ 2) + 1 := by positivity
  have h_i : ∀ ℓ : ℕ, |∫ z, g (gbmMil r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq| ≤
      (K * Real.sqrt (gbmMilStrongConst r σ T s₀ * T ^ 2) + 1) * (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) := by
    intro ℓ
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    have h := gbm_mil_weak_error_le r σ s₀ hT hg ℓ
    have hpos : 0 < ((2 : ℝ) ^ ℓ)⁻¹ := by positivity
    calc _ ≤ K * Real.sqrt (gbmMilStrongConst r σ T s₀ * T ^ 2) * ((2 : ℝ) ^ ℓ)⁻¹ := h
      _ ≤ _ := by linarith
  -- (iii): the variance rate `β = 2`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (fineCoarseDiff (fun ℓ z => g (gbmMil r σ T s₀ ℓ z))
      (fun ℓ z => g (gbmMil r σ T s₀ ℓ (pairAvg z))) 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀]
    exact variance_nonneg _ _
  have hc₂ : 0 < V₀ + 10 * K ^ 2 * (gbmMilStrongConst r σ T s₀ * T ^ 2) + 1 := by positivity
  have h_iii : ∀ ℓ, variance (fineCoarseDiff (fun ℓ z => g (gbmMil r σ T s₀ ℓ z))
      (fun ℓ z => g (gbmMil r σ T s₀ ℓ (pairAvg z))) ℓ) stdNormalSeq ≤
      (V₀ + 10 * K ^ 2 * (gbmMilStrongConst r σ T s₀ * T ^ 2) + 1) *
        (2 : ℝ) ^ (-(2 * (ℓ : ℝ))) := by
    intro ℓ
    rw [two_rpow_neg_two_mul ℓ]
    cases ℓ with
    | zero =>
      rw [← hV₀, pow_zero, inv_one, mul_one]
      linarith [mul_nonneg (sq_nonneg K) (mul_nonneg hC (sq_nonneg T))]
    | succ ℓ =>
      have hv := gbm_mil_correction_variance_le r σ s₀ hT hg ℓ
      have hinv : 0 < ((4 : ℝ) ^ (ℓ + 1))⁻¹ := by positivity
      exact hv.trans (by linarith [mul_nonneg hV₀0 hinv.le])
  -- (iv): a level-`ℓ` sample costs `2^ℓ`
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ 1 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, one_mul, Real.rpow_natCast]
  have hαβγ : min (2 : ℝ) 1 / 2 ≤ 1 := by
    rw [min_eq_right (by norm_num : (1 : ℝ) ≤ 2)]
    norm_num
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq)
    (fun z => g (gbmExact r σ T s₀ 0 z)) (fun ℓ z => g (gbmMil r σ T s₀ ℓ z))
    (fun ℓ z => g (gbmMil r σ T s₀ ℓ (pairAvg z))) (fun p x => x p) (fun ℓ _ _ => (2 : ℝ) ^ ℓ)
    (fun ℓ => (2 : ℝ) ^ ℓ) (α := 1) (β := 2) (γ := 1) one_pos two_pos one_pos hc₁ hc₂ one_pos
    hαβγ hω hind (hP.integrable one_le_two) hPfm hPcm hPf hPc h24
    (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ?_, ?_, ?_⟩
  · exact ((memLp_finsetSum _ fun ℓ _ =>
      memLp_blockMean hω (memLp_fineCoarseDiff hPf hPc) ℓ (N ℓ)).sub (memLp_const _)).integrable_sq
  · rw [← hPint]
    exact hmse
  · simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul] at hcost
    rw [complexityBound_of_lt (by norm_num : (1 : ℝ) < 2) ε] at hcost
    exact hcost

end MLMC
