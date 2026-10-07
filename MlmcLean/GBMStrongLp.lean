import MlmcLean.GBMDigital

/-!
# Higher moments of the strong error for geometric Brownian motion and the digital option
(Giles 2015, §5.1–§5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1
"Euler-Maruyama discretisation" (p. 29, l. 1296–1299 of `docs/giles2015.txt`: the strong error;
p. 33, l. 1435–1446: the digital option; Table 5.2, l. 1424–1434) and §5.2 "Milstein
discretisation" (p. 35, l. 1499–1500: first-order strong convergence; paragraph "Digital options",
l. 1525–1532).  Geometric Brownian motion `dS = rS dt + σS dW` with the exact solution and the
discretisations driven by the same increments `Z_i ∼ N(0,1)` (`stdNormalSeq`), as in
`MlmcLean.GBMEulerMaruyama`, `MlmcLean.GBMMilstein` and `MlmcLean.GBMDigital`.

The repository had only the mean-square strong errors (`gbm_em_strong_error`,
`gbm_mil_strong_error`), which give the digital option `V_ℓ = O(h^{1/3})` (Euler–Maruyama) and
`O(h^{2/3})` (Milstein), and no better from mean-square information alone
(`digital_mismatch_exponent_sharp`).  The paper's rates (§5.1, l. 1436–1446: "`V_ℓ = O(h^{1/2})`
… `E[(P_ℓ−P_{ℓ−1})⁴] = O(h_ℓ^{1/2})`"; §5.2, l. 1529–1531: "`V_ℓ = O(h_ℓ)`") use that the error is
small on (almost) every path; here this is replaced by the strong error in every `L^{2m}`, proved
for GBM, which gives every exponent below the paper's.

* **Gaussian tools.**  `integral_exp_mul_mul_gaussian`: the Cameron–Martin shift
  `E[e^{aZ} g(Z)] = e^{a²/2} E[g(Z + a)]`; `integral_pow_add_two_mul_exp_gaussian`:
  `E[Z^{n+2} e^{aZ}] = a E[Z^{n+1} e^{aZ}] + (n+1) E[Zⁿ e^{aZ}]`; `integral_pow_two_mul_gaussian`:
  `E[Z^{2k}] = (2k − 1)!!`.
* **Products of i.i.d. factors.**  `integral_pow_prod_sub_prod_le`: for
  `D_n = ∏_{i<n} G(Z_i) − ∏_{i<n} F(Z_i)` (the scheme minus the exact solution, both products of
  i.i.d. one-step factors), the recursion `D_{n+1} = D_n F(Z_n) + Q_n (G(Z_n) − F(Z_n))`, the
  binomial formula, independence and Young's inequality bound `E[D_n^{2m}]` by the one-step
  weighted moments `E[(G − F)^k F^{2m−k}]`.  The first of them has a cancellation: it is `O(h²)`
  although `G − F` is only `O(h)` (Euler–Maruyama) or `O(h^{3/2})` (Milstein); it is computed
  exactly (`gbm_em_onestep_one`, `gbm_mil_onestep_one`).  The others are bounded by the
  Cameron–Martin shift and the Gaussian moments (`abs_integral_sub_pow_mul_exp_pow_le`,
  `gbm_em_onestep_le`, `gbm_mil_onestep_le`).
* **The strong error in `L^{2m}`.**  `gbm_em_moment_error`: `E[(S_{t_n} − Ŝ_n)^{2m}] ≤ C h^m` for
  Euler–Maruyama; `gbm_mil_moment_error`: `≤ C h^{2m}` for Milstein, with explicit constants
  `gbmEMMomentConst`, `gbmMilMomentConst` depending on `m, r, σ, t_n = nh, S_0`;
  `gbm_em_moment_error_le`, `gbm_mil_moment_error_le`: the same with the constant `C_m(T)` for
  every grid time `t_n ≤ T`; `gbm_em_strong_error_four`, `gbm_mil_strong_error_four`: the fourth
  moments are `≤ C₂(T) h²` and `≤ C₂(T) h⁴` for `t_n ≤ T`; `gbm_em_moment_error_level`,
  `gbm_mil_moment_error_level`: on level `ℓ`.
* **The digital option.**  `gbm_em_digital_variance_le_moment`,
  `gbm_mil_digital_variance_le_moment`: the fraction of paths on either side of the strike, hence
  `V_ℓ`, is `O(h_ℓ^{m/(2m+1)})`, resp. `O(h_ℓ^{2m/(2m+1)})` (`digital_mismatch_le_of_moment`);
  `gbm_em_digital_fourth_moment_le_of_four`, `gbm_mil_digital_fourth_moment_le_of_four`: from the
  fourth moments, `V_ℓ` and `E[(P_ℓ − P_{ℓ−1})⁴]` are `O(h^{2/5})`, resp. `O(h^{4/5})` (the
  repository had `h^{1/3}`, `h^{2/3}`), and the kurtosis is at least the reciprocal;
  `gbm_em_digital_rate`, `gbm_mil_digital_rate`: for every `q < ½` (Euler–Maruyama), resp. every
  `q < 1` (Milstein), there is `C` with `V_ℓ ≤ C h_ℓ^q` and `E[(P_ℓ − P_{ℓ−1})⁴] ≤ C h_ℓ^q`.

**How close to the paper.**  The paper's exponents `½` (Euler–Maruyama) and `1` (natural Milstein
estimator) are reached up to an arbitrarily small loss; the endpoints, and the `O(h^{1/2} log h)` of
Table 5.2 (Avikainen 2009), are not proved.  The kurtosis bounds are lower bounds `κ ≥ c h^{−q}`;
the paper's `O(h^{−1/2})`, `O(h^{−1})` are upper bounds and need a lower bound on the mismatch
probability, which is not proved.

**The constants** are explicit (`gbmEMMomentConst`, `gbmMilMomentConst`, built from `gbmLpRate`,
`gbmEMStepConst`, `gbmMilStepConst`, `lpIncr`, `lpGrowth`) but far from sharp: they come from crude
Taylor and Gaussian-moment bounds of the one-step error, uniform in `h ≤ t`, and from the
linearisation of the recursion by Young's inequality, and they grow very fast with `σ²t` and `m`.
They were checked numerically against the exact moments
`E[(S_{t_n} − Ŝ_n)^{2m}] = S_0^{2m} ∑_k C(2m, k) (−1)^k (E[A^{2m−k} B^k])ⁿ` (`A`, `B` the exact and
the scheme step); e.g. for `r = 0.05`, `σ = 0.2`, `t = 1`, `S_0 = 1`, the Euler–Maruyama constant
for `m = 2` is about `1.6·10⁷`, against `E[(S_1 − Ŝ_n)⁴]/h² ≤ 2.2·10⁻⁵`.

The digital payoff `H(x − K)` is `(Set.Ioi K).indicator 1 x`; the factors `10 e^{−rT}` (§5.1) and
`25 e^{−rT}` (§5.2) of the paper's payoffs are omitted (they scale the variance and the fourth
moment and do not change the kurtosis).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### Gaussian tools -/

/-- `φ(x) e^{ax} = e^{a²/2} φ(x − a)` for the standard normal density `φ` (the identity behind the
Cameron–Martin shift `integral_exp_mul_mul_gaussian`, used for the GBM weights `e^{j(c + sZ)}`,
Giles 2015, §5.1–§5.2). -/
lemma gaussianPDFReal_mul_exp (a x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (a * x) = Real.exp (a ^ 2 / 2) * gaussianPDFReal a 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_comm (Real.exp (a ^ 2 / 2)), mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-- **The Cameron–Martin shift for `N(0,1)`**: `E[e^{aZ} g(Z)] = e^{a²/2} E[g(Z + a)]` for every
measurable `g` (both sides are `0` when the integrands are not integrable).  The exact GBM step is
`A = e^{c + sZ}`, so the weighted one-step moments `E[A^j f(Z)]` of Giles 2015, §5.1–§5.2, are
moments of a shifted Gaussian. -/
lemma integral_exp_mul_mul_gaussian (a : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ x, Real.exp (a * x) * g x ∂gaussianReal 0 1 =
      Real.exp (a ^ 2 / 2) * ∫ x, g (x + a) ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (· + a) = gaussianReal a 1 := by
    rw [gaussianReal_map_add_const, zero_add]
  have e1 : ∫ x, gaussianPDFReal 0 1 x • (Real.exp (a * x) * g x) =
      ∫ x, Real.exp (a ^ 2 / 2) * (gaussianPDFReal a 1 x • g x) := by
    congr 1
    funext x
    simp only [smul_eq_mul]
    rw [← mul_assoc, gaussianPDFReal_mul_exp]
    ring
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, e1, integral_const_mul,
    ← integral_gaussianReal_eq_integral_smul one_ne_zero, ← hmap,
    integral_map (by fun_prop) hg.aestronglyMeasurable]

/-- Integrability under the Cameron–Martin shift: if `g(Z + a)` is integrable for `Z ∼ N(0,1)`,
so is `e^{aZ} g(Z)` (Giles 2015, §5.1–§5.2, GBM weights). -/
lemma integrable_exp_mul_mul_gaussian (a : ℝ) {g : ℝ → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x => g (x + a)) (gaussianReal 0 1)) :
    Integrable (fun x => Real.exp (a * x) * g x) (gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (· + a) = gaussianReal a 1 := by
    rw [gaussianReal_map_add_const, zero_add]
  have h1 : Integrable g (gaussianReal a 1) := by
    rw [← hmap, integrable_map_measure hg.aestronglyMeasurable (by fun_prop)]
    exact hi
  rw [integrable_gaussianReal_iff_mul_pdf one_ne_zero] at h1 ⊢
  have h2 := h1.const_mul (Real.exp (a ^ 2 / 2))
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← mul_assoc, ← gaussianPDFReal_mul_exp]
  ring

/-- Gaussian integration by parts, `E[Z^{n+2} e^{aZ}] = a E[Z^{n+1} e^{aZ}] + (n+1) E[Zⁿ e^{aZ}]`
for `Z ∼ N(0,1)`, from the derivatives of the moment generating function (it extends
`integral_pow_four_mul_exp_mul_gaussian` of `MlmcLean.GBMMilstein` to every power; used for the
higher moments of the GBM error, Giles 2015, §5.1–§5.2). -/
lemma integral_pow_add_two_mul_exp_gaussian (n : ℕ) (a : ℝ) :
    ∫ x, x ^ (n + 2) * Real.exp (a * x) ∂gaussianReal 0 1 =
      a * ∫ x, x ^ (n + 1) * Real.exp (a * x) ∂gaussianReal 0 1 +
        (n + 1) * ∫ x, x ^ n * Real.exp (a * x) ∂gaussianReal 0 1 := by
  induction n generalizing a with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, one_mul, Nat.cast_zero]
    rw [integral_sq_mul_exp_mul_gaussian, integral_mul_exp_mul_gaussian,
      integral_exp_mul_gaussian]
    ring
  | succ n ih =>
    have hfun : (fun t => ∫ x, x ^ (n + 2) * Real.exp (t * x) ∂gaussianReal 0 1) =
        fun t => t * (∫ x, x ^ (n + 1) * Real.exp (t * x) ∂gaussianReal 0 1) +
          (n + 1) * ∫ x, x ^ n * Real.exp (t * x) ∂gaussianReal 0 1 := funext ih
    have h1 := hasDerivAt_integral_pow_mul_exp_gaussian a (n + 2)
    rw [hfun] at h1
    have h2 := ((hasDerivAt_id a).mul (hasDerivAt_integral_pow_mul_exp_gaussian a (n + 1))).add
      ((hasDerivAt_integral_pow_mul_exp_gaussian a n).const_mul ((n : ℝ) + 1))
    have h3 := h1.unique h2
    simp only [id, one_mul] at h3
    push_cast
    linear_combination h3

/-- `E[Z^{n+2}] = (n+1) E[Zⁿ]` for `Z ∼ N(0,1)` (the Gaussian moments behind the one-step bounds for
GBM, Giles 2015, §5.1–§5.2). -/
lemma integral_pow_add_two_gaussian (n : ℕ) :
    ∫ x, x ^ (n + 2) ∂gaussianReal 0 1 = (n + 1) * ∫ x, x ^ n ∂gaussianReal 0 1 := by
  have h := integral_pow_add_two_mul_exp_gaussian n 0
  simpa using h

/-- **The even Gaussian moments** `E[Z^{2k}] = (2k − 1)!!` for `Z ∼ N(0,1)` (`Nat.doubleFactorial`;
for `k = 0` this is `(0 − 1)!! = 0!! = 1`), used to bound the one-step errors of GBM in every
`L^{2m}` (Giles 2015, §5.1–§5.2). -/
lemma integral_pow_two_mul_gaussian (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂gaussianReal 0 1 = (Nat.doubleFactorial (2 * k - 1) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, integral_pow_add_two_gaussian, ih,
      show 2 * k + 2 - 1 = 2 * k + 1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    ring

/-- `(a + b + c)^k ≤ 3^{k−1} (a^k + b^k + c^k)` for `a, b, c ≥ 0` (convexity of `t ↦ t^k`; used for
the one-step bounds for GBM, Giles 2015, §5.1–§5.2). -/
lemma add_three_pow_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (k : ℕ) :
    (a + b + c) ^ k ≤ 3 ^ (k - 1) * (a ^ k + b ^ k + c ^ k) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · norm_num
  set z : ℕ → ℝ := fun i => if i = 0 then a else if i = 1 then b else c
  have hz : ∀ i ∈ range 3, 0 ≤ z i := fun i _ => by
    simp only [z]
    split_ifs <;> assumption
  have h := Real.pow_arith_mean_le_arith_mean_pow (range 3) (fun _ => (1 / 3 : ℝ)) z
    (fun _ _ => by norm_num) (by simp) hz k
  simp only [sum_range_succ, sum_range_zero, z] at h
  norm_num at h
  have e : ((3 : ℝ) ^ (k - 1)) * 3 = 3 ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have e2 : 1 / 3 * a + 1 / 3 * b + 1 / 3 * c = (a + b + c) / 3 := by ring
  rw [e2, div_pow, div_le_iff₀ h3] at h
  have e3 : (1 / 3 * a ^ k + 1 / 3 * b ^ k + 1 / 3 * c ^ k) * 3 ^ k =
      3 ^ (k - 1) * (a ^ k + b ^ k + c ^ k) := by
    rw [← e]
    ring
  linarith

/-- `E[(P₀ + P₁Z² + P₂Z⁴)^k] ≤ 3^{k−1} (P₀^k + P₁^k (2k−1)!! + P₂^k (4k−1)!!)` for `Z ∼ N(0,1)` and
`P₀, P₁, P₂ ≥ 0` (the shifted one-step errors of GBM are dominated by such quartics, Giles 2015,
§5.1–§5.2). -/
lemma integral_quartic_pow_le {P₀ P₁ P₂ : ℝ} (h0 : 0 ≤ P₀) (h1 : 0 ≤ P₁) (h2 : 0 ≤ P₂)
    (k : ℕ) :
    ∫ x, (P₀ + P₁ * x ^ 2 + P₂ * x ^ 4) ^ k ∂gaussianReal 0 1 ≤
      3 ^ (k - 1) * (P₀ ^ k + P₁ ^ k * Nat.doubleFactorial (2 * k - 1) +
        P₂ ^ k * Nat.doubleFactorial (4 * k - 1)) := by
  have i2 := (integrable_pow_gaussian (2 * k)).const_mul (P₁ ^ k)
  have i4 := (integrable_pow_gaussian (4 * k)).const_mul (P₂ ^ k)
  have hint : Integrable (fun x : ℝ => 3 ^ (k - 1) * (P₀ ^ k + P₁ ^ k * x ^ (2 * k) +
      P₂ ^ k * x ^ (4 * k))) (gaussianReal 0 1) :=
    (((integrable_const _).add i2).add i4).const_mul _
  have hpt : ∀ x : ℝ, (P₀ + P₁ * x ^ 2 + P₂ * x ^ 4) ^ k ≤
      3 ^ (k - 1) * (P₀ ^ k + P₁ ^ k * x ^ (2 * k) + P₂ ^ k * x ^ (4 * k)) := fun x => by
    have h := add_three_pow_le h0 (mul_nonneg h1 (sq_nonneg x))
      (mul_nonneg h2 (by positivity : (0 : ℝ) ≤ x ^ 4)) k
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at h
    exact h
  calc ∫ x, (P₀ + P₁ * x ^ 2 + P₂ * x ^ 4) ^ k ∂gaussianReal 0 1
      ≤ ∫ x, 3 ^ (k - 1) * (P₀ ^ k + P₁ ^ k * x ^ (2 * k) + P₂ ^ k * x ^ (4 * k))
          ∂gaussianReal 0 1 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hint
          (Filter.Eventually.of_forall hpt)
    _ = _ := by
        have j1 : Integrable (fun x : ℝ => P₀ ^ k + P₁ ^ k * x ^ (2 * k)) (gaussianReal 0 1) :=
          (integrable_const _).add i2
        rw [integral_const_mul, integral_add j1 i4, integral_add (integrable_const _) i2,
          integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul,
          integral_pow_two_mul_gaussian, show 4 * k = 2 * (2 * k) by ring,
          integral_pow_two_mul_gaussian, show 2 * (2 * k) - 1 = 4 * k - 1 by omega]

/-- `(P₀ + P₁Z² + P₂Z⁴)^k` is integrable for `Z ∼ N(0,1)` and `P₀, P₁, P₂ ≥ 0` (the shifted one-step
errors of GBM are dominated by such quartics, Giles 2015, §5.1–§5.2). -/
lemma integrable_quartic_pow {P₀ P₁ P₂ : ℝ} (h0 : 0 ≤ P₀) (h1 : 0 ≤ P₁) (h2 : 0 ≤ P₂) (k : ℕ) :
    Integrable (fun x : ℝ => (P₀ + P₁ * x ^ 2 + P₂ * x ^ 4) ^ k) (gaussianReal 0 1) := by
  have i2 := (integrable_pow_gaussian (2 * k)).const_mul (P₁ ^ k)
  have i4 := (integrable_pow_gaussian (4 * k)).const_mul (P₂ ^ k)
  have hint : Integrable (fun x : ℝ => 3 ^ (k - 1) * (P₀ ^ k + P₁ ^ k * x ^ (2 * k) +
      P₂ ^ k * x ^ (4 * k))) (gaussianReal 0 1) :=
    (((integrable_const _).add i2).add i4).const_mul _
  refine hint.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have hx0 : 0 ≤ P₀ + P₁ * x ^ 2 + P₂ * x ^ 4 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx0 k)]
  have h := add_three_pow_le h0 (mul_nonneg h1 (sq_nonneg x))
    (mul_nonneg h2 (by positivity : (0 : ℝ) ≤ x ^ 4)) k
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at h
  exact h

/-- A nonnegative measurable `f ≤ P₀ + P₁x² + P₂x⁴` has `E[f(Z)^k] ≤ 3^{k−1} (P₀^k + P₁^k (2k−1)!! +
P₂^k (4k−1)!!)` for `Z ∼ N(0,1)`, and `f(Z)^k` is integrable (the Gaussian-moment bound of the
one-step errors for GBM, Giles 2015, §5.1–§5.2). -/
lemma integral_pow_le_of_le_quartic {f : ℝ → ℝ} (hf : Measurable f) {P₀ P₁ P₂ : ℝ}
    (h0 : 0 ≤ P₀) (h1 : 0 ≤ P₁) (h2 : 0 ≤ P₂) (hf0 : ∀ x, 0 ≤ f x)
    (hle : ∀ x, f x ≤ P₀ + P₁ * x ^ 2 + P₂ * x ^ 4) (k : ℕ) :
    Integrable (fun x => f x ^ k) (gaussianReal 0 1) ∧
      ∫ x, f x ^ k ∂gaussianReal 0 1 ≤ 3 ^ (k - 1) * (P₀ ^ k +
        P₁ ^ k * Nat.doubleFactorial (2 * k - 1) + P₂ ^ k * Nat.doubleFactorial (4 * k - 1)) := by
  have hq := integrable_quartic_pow h0 h1 h2 k
  have hpt : ∀ x, f x ^ k ≤ (P₀ + P₁ * x ^ 2 + P₂ * x ^ 4) ^ k := fun x =>
    pow_le_pow_left₀ (hf0 x) (hle x) k
  have hint : Integrable (fun x => f x ^ k) (gaussianReal 0 1) :=
    hq.mono' (hf.pow_const k).aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf0 x) k)]
      exact hpt x)
  refine ⟨hint, ?_⟩
  calc ∫ x, f x ^ k ∂gaussianReal 0 1
      ≤ ∫ x, (P₀ + P₁ * x ^ 2 + P₂ * x ^ 4) ^ k ∂gaussianReal 0 1 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => pow_nonneg (hf0 x) k) hq
          (Filter.Eventually.of_forall hpt)
    _ ≤ _ := integral_quartic_pow_le h0 h1 h2 k

/-- A measurable `G` with `G² ≤ P₀ + P₁x² + P₂x⁴` has `G(Z)^{2m}` integrable for `Z ∼ N(0,1)` (the
Euler–Maruyama and Milstein steps of GBM, Giles 2015, §5.1–§5.2). -/
lemma integrable_pow_two_mul_of_sq_le {G : ℝ → ℝ} (hG : Measurable G) {P₀ P₁ P₂ : ℝ}
    (h0 : 0 ≤ P₀) (h1 : 0 ≤ P₁) (h2 : 0 ≤ P₂) (hle : ∀ x, G x ^ 2 ≤ P₀ + P₁ * x ^ 2 + P₂ * x ^ 4)
    (m : ℕ) : Integrable (fun x => G x ^ (2 * m)) (gaussianReal 0 1) := by
  have h := (integral_pow_le_of_le_quartic (f := fun x => G x ^ 2) (hG.pow_const 2) h0 h1 h2
    (fun x => sq_nonneg _) hle m).1
  simpa only [← pow_mul] using h

/-! ### Taylor remainders of the exponential -/

/-- `0 ≤ e^y − 1 − y ≤ y² max(1, e^y)` for every real `y` (the remainder of the Euler–Maruyama
step of GBM, Giles 2015, §5.1). -/
lemma exp_sub_one_sub_le_sq_mul_max (y : ℝ) :
    0 ≤ Real.exp y - 1 - y ∧ Real.exp y - 1 - y ≤ y ^ 2 * max 1 (Real.exp y) := by
  refine ⟨by linarith [Real.add_one_le_exp y], ?_⟩
  have hm1 : 1 ≤ max 1 (Real.exp y) := le_max_left _ _
  have hme : Real.exp y ≤ max 1 (Real.exp y) := le_max_right _ _
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  rcases le_or_gt |y| 1 with hy | hy
  · have h := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hy)).2
    nlinarith [mul_le_mul_of_nonneg_left hm1 hy2]
  · have hy1 : 1 < y ^ 2 := (one_lt_sq_iff_one_lt_abs y).2 hy
    rcases le_or_gt 0 y with h0 | h0
    · nlinarith [mul_le_mul_of_nonneg_right hy1.le (zero_le_one.trans hm1)]
    · have he : Real.exp y < 1 := by simpa using Real.exp_lt_exp.2 h0
      rw [abs_of_neg h0] at hy
      nlinarith [mul_le_mul_of_nonneg_left hm1 hy2]

/-- `|e^y − 1 − y − y²/2| ≤ |y|³ max(1, e^y)` for every real `y` (the remainder of the Milstein step
of GBM, Giles 2015, §5.2). -/
lemma abs_exp_sub_quadratic_le (y : ℝ) :
    |Real.exp y - 1 - y - y ^ 2 / 2| ≤ |y| ^ 3 * max 1 (Real.exp y) := by
  have hm1 : 1 ≤ max 1 (Real.exp y) := le_max_left _ _
  have hme : Real.exp y ≤ max 1 (Real.exp y) := le_max_right _ _
  have hy3 : 0 ≤ |y| ^ 3 := pow_nonneg (abs_nonneg y) 3
  rcases le_or_gt |y| 1 with hy | hy
  · have h := Real.exp_bound hy (n := 3) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    have e : Real.exp y - 1 - y - y ^ 2 / 2 = Real.exp y - (1 + y + y ^ 2 / 2) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hm1 hy3]
  · have hy' : 1 ≤ |y| := hy.le
    have hy2 : 1 ≤ |y| ^ 2 := one_le_pow₀ hy'
    have hy3' : 1 ≤ |y| ^ 3 := one_le_pow₀ hy'
    have hsq : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    have h23 : |y| ^ 2 ≤ |y| ^ 3 := pow_le_pow_right₀ hy' (by norm_num)
    rcases le_or_gt 0 y with h0 | h0
    · have hq := Real.quadratic_le_exp_of_nonneg h0
      rw [abs_of_nonneg (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right hy3' (zero_le_one.trans hm1)]
    · have he : Real.exp y < 1 := by simpa using Real.exp_lt_exp.2 h0
      have hep : 0 < Real.exp y := Real.exp_pos y
      have hya : |y| = -y := abs_of_neg h0
      rw [abs_le]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left hm1 hy3]

/-! ### Even moments of the difference of two products of i.i.d. factors -/

/-- `|x^j y^{N−j}| ≤ 2^{N−1} (a^N + b^N)` if `|x|, |y| ≤ |a| + |b|`, `j ≤ N` and `N` is even (the
integrability of the terms of the binomial expansion of the moment recursion for the strong error of
GBM, Giles 2015, §5.1–§5.2). -/
lemma abs_pow_mul_pow_le_of_le {x y a b : ℝ} (hx : |x| ≤ |a| + |b|) (hy : |y| ≤ |a| + |b|)
    {j N : ℕ} (hj : j ≤ N) (hN : Even N) :
    |x ^ j * y ^ (N - j)| ≤ 2 ^ (N - 1) * (a ^ N + b ^ N) := by
  have hab : 0 ≤ |a| + |b| := by positivity
  rw [abs_mul, abs_pow, abs_pow]
  calc |x| ^ j * |y| ^ (N - j) ≤ (|a| + |b|) ^ j * (|a| + |b|) ^ (N - j) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg x) hx j)
          (pow_le_pow_left₀ (abs_nonneg y) hy (N - j)) (by positivity) (by positivity)
    _ = (|a| + |b|) ^ N := by rw [← pow_add, Nat.add_sub_cancel' hj]
    _ ≤ 2 ^ (N - 1) * (|a| ^ N + |b| ^ N) := add_pow_le (abs_nonneg a) (abs_nonneg b) N
    _ = 2 ^ (N - 1) * (a ^ N + b ^ N) := by rw [hN.pow_abs, hN.pow_abs]

/-- Young-type splitting: `|p|^k |d|^{N−k} ≤ λ^{N−k} |p|^N + λ^{−k} |d|^N` for `λ > 0`, `k ≤ N`
(compare `|d|` with `λ|p|`; the linearisation of the moment recursion for the strong error of GBM,
Giles 2015, §5.1–§5.2). -/
lemma abs_pow_mul_pow_le_lam {p d lam : ℝ} (hlam : 0 < lam) {k N : ℕ} (hk : k ≤ N) :
    |p| ^ k * |d| ^ (N - k) ≤ lam ^ (N - k) * |p| ^ N + (lam ^ k)⁻¹ * |d| ^ N := by
  have hp := abs_nonneg p
  have hd := abs_nonneg d
  have hlk : 0 < lam ^ k := pow_pos hlam k
  rcases le_or_gt |d| (lam * |p|) with h | h
  · have h1 : |d| ^ (N - k) ≤ (lam * |p|) ^ (N - k) := pow_le_pow_left₀ hd h _
    have h2 : |p| ^ k * |d| ^ (N - k) ≤ lam ^ (N - k) * |p| ^ N := by
      calc |p| ^ k * |d| ^ (N - k) ≤ |p| ^ k * (lam * |p|) ^ (N - k) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = lam ^ (N - k) * |p| ^ N := by
            rw [mul_pow, ← mul_assoc, mul_comm (|p| ^ k), mul_assoc, ← pow_add,
              Nat.add_sub_cancel' hk]
    have h3 : 0 ≤ (lam ^ k)⁻¹ * |d| ^ N := by positivity
    linarith
  · have h1 : |p| ^ k ≤ (|d| / lam) ^ k := by
      refine pow_le_pow_left₀ hp ?_ k
      rw [le_div_iff₀ hlam]
      linarith
    have h2 : |p| ^ k * |d| ^ (N - k) ≤ (lam ^ k)⁻¹ * |d| ^ N := by
      calc |p| ^ k * |d| ^ (N - k) ≤ (|d| / lam) ^ k * |d| ^ (N - k) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (lam ^ k)⁻¹ * |d| ^ N := by
            rw [div_pow, div_eq_inv_mul, mul_assoc, ← pow_add, Nat.add_sub_cancel' hk]
    have h3 : 0 ≤ lam ^ (N - k) * |p| ^ N := by positivity
    linarith

/-- **The pointwise inequality of the moment recursion** (Giles 2015, §5.1–§5.2: the strong error of
GBM): for `N` even, `k ≤ N` and `λ > 0`, `|(p + d)^k d^{N−k}| ≤ 2^{k−1} (λ^{N−k} p^N + (1 + λ^{−k})
d^N)`. With `p = P_n` (the product of exact steps), `d = D_n` (the error) and `p + d = Q_n` (the
product of scheme steps) this linearises the mixed moments `E[Q_n^k D_n^{N−k}]` in `E[D_n^N]` and
`E[P_n^N]`. -/
lemma abs_add_pow_mul_pow_le {p d lam : ℝ} (hlam : 0 < lam) {k N : ℕ} (hk : k ≤ N)
    (hN : Even N) :
    |(p + d) ^ k * d ^ (N - k)| ≤
      2 ^ (k - 1) * (lam ^ (N - k) * p ^ N + (1 + (lam ^ k)⁻¹) * d ^ N) := by
  have hp := abs_nonneg p
  have hd := abs_nonneg d
  rw [abs_mul, abs_pow, abs_pow]
  have h1 : |p + d| ^ k ≤ 2 ^ (k - 1) * (|p| ^ k + |d| ^ k) :=
    (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le p d) k).trans (add_pow_le hp hd k)
  have h2 := abs_pow_mul_pow_le_lam (p := p) (d := d) hlam hk
  have h3 : |d| ^ k * |d| ^ (N - k) = |d| ^ N := by rw [← pow_add, Nat.add_sub_cancel' hk]
  have h4 : (0 : ℝ) ≤ 2 ^ (k - 1) := by positivity
  rw [← hN.pow_abs p, ← hN.pow_abs d]
  calc |p + d| ^ k * |d| ^ (N - k) ≤ 2 ^ (k - 1) * (|p| ^ k + |d| ^ k) * |d| ^ (N - k) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 ^ (k - 1) * (|p| ^ k * |d| ^ (N - k) + |d| ^ k * |d| ^ (N - k)) := by ring
    _ ≤ 2 ^ (k - 1) * ((lam ^ (N - k) * |p| ^ N + (lam ^ k)⁻¹ * |d| ^ N) + |d| ^ N) := by
        rw [h3]
        gcongr
    _ = 2 ^ (k - 1) * (lam ^ (N - k) * |p| ^ N + (1 + (lam ^ k)⁻¹) * |d| ^ N) := by ring

/-- Under `N(0,1)^{⊗ℕ}`, a measurable function `A` of `Z_0, …, Z_{n−1}` and a function `B(Z_n)` of
the next increment are independent, so `E[A B(Z_n)] = E[A] E[B(Z)]` (`indepFun_incr_of_eq_lt`;
Giles 2015, §5.1: the Brownian increments of the successive time steps are independent). -/
lemma integral_mul_comp_eval_of_eq_lt {A : (ℕ → ℝ) → ℝ} (hA : Measurable A) {n : ℕ}
    (hdep : ∀ z z' : ℕ → ℝ, (∀ i < n, z i = z' i) → A z = A z') {B : ℝ → ℝ}
    (hB : Measurable B) :
    ∫ z, A z * B (z n) ∂stdNormalSeq =
      (∫ z, A z ∂stdNormalSeq) * ∫ x, B x ∂gaussianReal 0 1 := by
  have hind : IndepFun A (fun z => B (z n)) stdNormalSeq :=
    (indepFun_incr_of_eq_lt hA hdep).comp measurable_id hB
  rw [hind.integral_fun_mul_eq_mul_integral hA.aestronglyMeasurable
    (hB.comp (measurable_pi_apply n)).aestronglyMeasurable]
  congr 1
  exact integral_comp_of_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) n) hB.aestronglyMeasurable

/-- In the setting of `integral_mul_comp_eval_of_eq_lt`, `A B(Z_n)` is integrable if `A` and `B(Z)`
are (the Brownian increments of successive time steps are independent, Giles 2015, §5.1). -/
lemma integrable_mul_comp_eval_of_eq_lt {A : (ℕ → ℝ) → ℝ} (hA : Measurable A) {n : ℕ}
    (hdep : ∀ z z' : ℕ → ℝ, (∀ i < n, z i = z' i) → A z = A z') {B : ℝ → ℝ}
    (hB : Measurable B) (hAi : Integrable A stdNormalSeq) (hBi : Integrable B (gaussianReal 0 1)) :
    Integrable (fun z => A z * B (z n)) stdNormalSeq := by
  have hind : IndepFun A (fun z => B (z n)) stdNormalSeq :=
    (indepFun_incr_of_eq_lt hA hdep).comp measurable_id hB
  have hBi' : Integrable (fun z : ℕ → ℝ => B (z n)) stdNormalSeq :=
    ((measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) n).integrable_comp
      hB.aestronglyMeasurable).2 hBi
  exact hind.integrable_mul hAi hBi'

/-- `∏_{i<n} F(z_i)` depends only on `z_0, …, z_{n−1}` (the GBM solution and its discretisations at
`t_n` use only the first `n` increments, Giles 2015, §5.1–§5.2). -/
lemma prod_range_eq_of_eq_lt (F : ℝ → ℝ) {n : ℕ} {z z' : ℕ → ℝ} (h : ∀ i < n, z i = z' i) :
    ∏ i ∈ range n, F (z i) = ∏ i ∈ range n, F (z' i) :=
  prod_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

/-- `z ↦ ∏_{i<n} F(z_i)` is measurable for measurable `F` (the product form of GBM paths,
Giles 2015, §5.1–§5.2). -/
lemma measurable_prod_range {F : ℝ → ℝ} (hF : Measurable F) (n : ℕ) :
    Measurable fun z : ℕ → ℝ => ∏ i ∈ range n, F (z i) :=
  Finset.measurable_prod _ fun i _ => hF.comp (measurable_pi_apply i)

/-- `(∏_{i<n} F(Z_i))^N` is integrable if `F(Z)^N` is, `Z_i` i.i.d. `N(0,1)` (the product form of
GBM paths, Giles 2015, §5.1–§5.2). -/
lemma integrable_prod_range_pow {F : ℝ → ℝ} (hF : Measurable F) {N : ℕ}
    (hFN : Integrable (fun x => F x ^ N) (gaussianReal 0 1)) (n : ℕ) :
    Integrable (fun z : ℕ → ℝ => (∏ i ∈ range n, F (z i)) ^ N) stdNormalSeq := by
  simp_rw [← prod_pow]
  exact integrable_prod_stdNormalSeq (hF.pow_const N) hFN n

/-- `E[(∏_{i<n} F(Z_i))^N] = (E[F(Z)^N])ⁿ` for i.i.d. `Z_i ∼ N(0,1)` (the product form of GBM paths,
Giles 2015, §5.1–§5.2). -/
lemma integral_prod_range_pow {F : ℝ → ℝ} (hF : Measurable F) (N n : ℕ) :
    ∫ z, (∏ i ∈ range n, F (z i)) ^ N ∂stdNormalSeq = (∫ x, F x ^ N ∂gaussianReal 0 1) ^ n := by
  simp_rw [← prod_pow]
  exact integral_prod_stdNormalSeq (hF.pow_const N) n

/-- `(∏_{i<n} G(Z_i) − ∏_{i<n} F(Z_i))^N` is integrable for even `N` if `F(Z)^N`, `G(Z)^N` are (the
error of a GBM discretisation in `L^N`, Giles 2015, §5.1–§5.2). -/
lemma integrable_pow_prod_sub_prod {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    {N : ℕ} (hN : Even N) (hF2 : Integrable (fun x => F x ^ N) (gaussianReal 0 1))
    (hG2 : Integrable (fun x => G x ^ N) (gaussianReal 0 1)) (n : ℕ) :
    Integrable (fun z => (∏ i ∈ range n, G (z i) - ∏ i ∈ range n, F (z i)) ^ N)
      stdNormalSeq := by
  refine (((integrable_prod_range_pow hF hF2 n).add
    (integrable_prod_range_pow hG hG2 n)).const_mul (2 ^ (N - 1))).mono'
    (((measurable_prod_range hG n).sub
      (measurable_prod_range hF n)).pow_const N).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  calc |∏ i ∈ range n, G (z i) - ∏ i ∈ range n, F (z i)| ^ N
      ≤ (|∏ i ∈ range n, F (z i)| + |∏ i ∈ range n, G (z i)|) ^ N :=
        pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by rw [add_comm])) N
    _ ≤ 2 ^ (N - 1) * (|∏ i ∈ range n, F (z i)| ^ N + |∏ i ∈ range n, G (z i)| ^ N) :=
        add_pow_le (abs_nonneg _) (abs_nonneg _) N
    _ = _ := by rw [hN.pow_abs, hN.pow_abs]; rfl

/-- **One step of the moment recursion.**  Let `P_n = ∏_{i<n} F(Z_i)`, `Q_n = ∏_{i<n} G(Z_i)`
(the exact GBM solution and the scheme on the grid, Giles 2015, §5.1–§5.2), `D_n = Q_n − P_n`,
`N = 2m`, and let `b_k ≥ |E[(G − F)^{k+1} F^{N−k−1}]|`.  From `D_{n+1} = D_n F(Z_n) +
Q_n (G(Z_n) − F(Z_n))`, the binomial formula, the independence of `Z_n` from the past and
`abs_add_pow_mul_pow_le`,
`E[D_{n+1}^N] ≤ E[F^N] E[D_n^N] + ∑_{k<N} C(N, k+1) 2^k b_k (λ^{N−k−1} (E[F^N])ⁿ +
(1 + λ^{−k−1}) E[D_n^N])`. -/
lemma integral_pow_prod_sub_prod_succ_le {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    {m : ℕ} (hF2 : Integrable (fun x => F x ^ (2 * m)) (gaussianReal 0 1))
    (hG2 : Integrable (fun x => G x ^ (2 * m)) (gaussianReal 0 1)) {b : ℕ → ℝ}
    (hb : ∀ k < 2 * m,
      |∫ x, (G x - F x) ^ (k + 1) * F x ^ (2 * m - (k + 1)) ∂gaussianReal 0 1| ≤ b k)
    {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ∫ z, (∏ i ∈ range (n + 1), G (z i) - ∏ i ∈ range (n + 1), F (z i)) ^ (2 * m)
        ∂stdNormalSeq ≤
      (∫ x, F x ^ (2 * m) ∂gaussianReal 0 1) *
          ∫ z, (∏ i ∈ range n, G (z i) - ∏ i ∈ range n, F (z i)) ^ (2 * m) ∂stdNormalSeq +
        ∑ k ∈ range (2 * m), ((2 * m).choose (k + 1) : ℝ) * 2 ^ k * b k *
          (lam ^ (2 * m - (k + 1)) * (∫ x, F x ^ (2 * m) ∂gaussianReal 0 1) ^ n +
            (1 + (lam ^ (k + 1))⁻¹) *
              ∫ z, (∏ i ∈ range n, G (z i) - ∏ i ∈ range n, F (z i)) ^ (2 * m)
                ∂stdNormalSeq) := by
  set N := 2 * m with hNdef
  have hN : Even N := even_two_mul m
  set P : (ℕ → ℝ) → ℝ := fun z => ∏ i ∈ range n, F (z i) with hPdef
  set Q : (ℕ → ℝ) → ℝ := fun z => ∏ i ∈ range n, G (z i) with hQdef
  set W := ∫ z, (Q z - P z) ^ N ∂stdNormalSeq with hWdef
  set m₀ := ∫ x, F x ^ N ∂gaussianReal 0 1 with hm₀
  have hPm : Measurable P := measurable_prod_range hF n
  have hQm : Measurable Q := measurable_prod_range hG n
  have hP2 : Integrable (fun z => P z ^ N) stdNormalSeq := integrable_prod_range_pow hF hF2 n
  have hQ2 : Integrable (fun z => Q z ^ N) stdNormalSeq := integrable_prod_range_pow hG hG2 n
  -- the `j`-th term of the binomial expansion
  set A : ℕ → (ℕ → ℝ) → ℝ := fun j z => Q z ^ j * (Q z - P z) ^ (N - j) with hAdef
  set B : ℕ → ℝ → ℝ := fun j x => (G x - F x) ^ j * F x ^ (N - j) with hBdef
  have hAm : ∀ j, Measurable (A j) := fun j => (hQm.pow_const j).mul ((hQm.sub hPm).pow_const _)
  have hBm : ∀ j, Measurable (B j) := fun j => ((hG.sub hF).pow_const j).mul (hF.pow_const _)
  have hAdep : ∀ j, ∀ z z' : ℕ → ℝ, (∀ i < n, z i = z' i) → A j z = A j z' := by
    intro j z z' h
    simp only [hAdef, hQdef, hPdef, prod_range_eq_of_eq_lt G h, prod_range_eq_of_eq_lt F h]
  have hAi : ∀ j ≤ N, Integrable (A j) stdNormalSeq := by
    intro j hj
    refine ((hP2.add hQ2).const_mul (2 ^ (N - 1))).mono' (hAm j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact abs_pow_mul_pow_le_of_le (by rw [add_comm]; exact le_add_of_nonneg_right (abs_nonneg _))
      ((abs_sub _ _).trans (by rw [add_comm])) hj hN
  have hBi : ∀ j ≤ N, Integrable (B j) (gaussianReal 0 1) := by
    intro j hj
    refine ((hF2.add hG2).const_mul (2 ^ (N - 1))).mono' (hBm j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact abs_pow_mul_pow_le_of_le ((abs_sub _ _).trans (by rw [add_comm]))
      (le_add_of_nonneg_right (abs_nonneg _)) hj hN
  -- the recursion `D_{n+1} = D_n F(Z_n) + Q_n (G(Z_n) − F(Z_n))` and the binomial formula
  have hexp : ∀ z : ℕ → ℝ,
      (∏ i ∈ range (n + 1), G (z i) - ∏ i ∈ range (n + 1), F (z i)) ^ N =
        ∑ j ∈ range (N + 1), (N.choose j : ℝ) * (A j z * B j (z n)) := by
    intro z
    rw [prod_range_succ, prod_range_succ]
    have e : (∏ i ∈ range n, G (z i)) * G (z n) - (∏ i ∈ range n, F (z i)) * F (z n) =
        Q z * (G (z n) - F (z n)) + (Q z - P z) * F (z n) := by
      simp only [hQdef, hPdef]
      ring
    rw [e, add_pow]
    refine sum_congr rfl fun j _ => ?_
    simp only [hAdef, hBdef]
    rw [mul_pow, mul_pow]
    ring
  have hterm : ∀ j ∈ range (N + 1),
      Integrable (fun z => (N.choose j : ℝ) * (A j z * B j (z n))) stdNormalSeq := by
    intro j hj
    have hj' : j ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hj)
    exact (integrable_mul_comp_eval_of_eq_lt (hAm j) (hAdep j) (hBm j) (hAi j hj')
      (hBi j hj')).const_mul _
  have hsplit : ∫ z, (∏ i ∈ range (n + 1), G (z i) - ∏ i ∈ range (n + 1), F (z i)) ^ N
      ∂stdNormalSeq =
      ∑ j ∈ range (N + 1), (N.choose j : ℝ) * ((∫ z, A j z ∂stdNormalSeq) *
        ∫ x, B j x ∂gaussianReal 0 1) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ hterm]
    refine sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_mul_comp_eval_of_eq_lt (hAm j) (hAdep j) (hBm j)]
  rw [hsplit, sum_range_succ']
  -- the `j = 0` term
  have h0 : ((N.choose 0 : ℕ) : ℝ) * ((∫ z, A 0 z ∂stdNormalSeq) * ∫ x, B 0 x ∂gaussianReal 0 1) =
      m₀ * W := by
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, hAdef, hBdef, pow_zero,
      Nat.sub_zero, hWdef, hm₀]
    ring
  rw [h0, add_comm]
  refine add_le_add le_rfl (sum_le_sum fun k hk => ?_)
  have hk' : k + 1 ≤ N := mem_range.1 hk
  -- the moment of `Q^{k+1} D^{N-k-1}`
  have hA : |∫ z, A (k + 1) z ∂stdNormalSeq| ≤
      2 ^ k * (lam ^ (N - (k + 1)) * m₀ ^ n + (1 + (lam ^ (k + 1))⁻¹) * W) := by
    have hD2 : Integrable (fun z => (Q z - P z) ^ N) stdNormalSeq :=
      (hAi 0 (Nat.zero_le _)).congr (Filter.Eventually.of_forall fun z => by simp [hAdef])
    have hPint : ∫ z, P z ^ N ∂stdNormalSeq = m₀ ^ n := integral_prod_range_pow hF N n
    have hint : Integrable (fun z => 2 ^ k * (lam ^ (N - (k + 1)) * P z ^ N +
        (1 + (lam ^ (k + 1))⁻¹) * (Q z - P z) ^ N)) stdNormalSeq :=
      ((hP2.const_mul _).add (hD2.const_mul _)).const_mul _
    calc |∫ z, A (k + 1) z ∂stdNormalSeq| ≤ ∫ z, |A (k + 1) z| ∂stdNormalSeq :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, 2 ^ k * (lam ^ (N - (k + 1)) * P z ^ N +
            (1 + (lam ^ (k + 1))⁻¹) * (Q z - P z) ^ N) ∂stdNormalSeq := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _) hint
            (Filter.Eventually.of_forall fun z => ?_)
          have h := abs_add_pow_mul_pow_le (p := P z) (d := Q z - P z) hlam hk' hN
          simp only [hAdef]
          rw [show P z + (Q z - P z) = Q z by ring, Nat.add_sub_cancel] at h
          exact h
      _ = 2 ^ k * (lam ^ (N - (k + 1)) * m₀ ^ n + (1 + (lam ^ (k + 1))⁻¹) * W) := by
          rw [integral_const_mul, integral_add (hP2.const_mul _) (hD2.const_mul _),
            integral_const_mul, integral_const_mul, hPint]
  have hBk := hb k (by omega)
  have hb0 : 0 ≤ b k := (abs_nonneg _).trans hBk
  have hc : (0 : ℝ) ≤ (N.choose (k + 1) : ℝ) := Nat.cast_nonneg _
  calc ((N.choose (k + 1) : ℕ) : ℝ) * ((∫ z, A (k + 1) z ∂stdNormalSeq) *
          ∫ x, B (k + 1) x ∂gaussianReal 0 1)
      ≤ |((N.choose (k + 1) : ℕ) : ℝ) * ((∫ z, A (k + 1) z ∂stdNormalSeq) *
          ∫ x, B (k + 1) x ∂gaussianReal 0 1)| := le_abs_self _
    _ = (N.choose (k + 1) : ℝ) * (|∫ z, A (k + 1) z ∂stdNormalSeq| *
          |∫ x, B (k + 1) x ∂gaussianReal 0 1|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc]
    _ ≤ (N.choose (k + 1) : ℝ) * ((2 ^ k * (lam ^ (N - (k + 1)) * m₀ ^ n +
          (1 + (lam ^ (k + 1))⁻¹) * W)) * b k) := by
        have hW0 : 0 ≤ W := integral_nonneg fun z => hN.pow_nonneg _
        have hm0 : 0 ≤ m₀ := integral_nonneg fun x => hN.pow_nonneg _
        gcongr
    _ = _ := by ring

/-- **Even moments of the difference of two products of i.i.d. factors** (the structure behind the
strong error of GBM in Giles 2015, §5.1–§5.2: the exact solution and the Euler–Maruyama or Milstein
path driven by the same increments are `S_0 ∏_{i<n} F(Z_i)` and `S_0 ∏_{i<n} G(Z_i)`).  For
measurable `F`, `G` with `F(Z)^{2m}`, `G(Z)^{2m}` integrable (`m ≥ 1`), one-step bounds
`|E[(G − F)^{k+1} F^{2m−k−1}]| ≤ b_k` (`k < 2m`), `λ > 0` and
`I ≥ ∑_{k<2m} C(2m, k+1) 2^k b_k λ^{2m−k−1}`,
`M ≥ E[F^{2m}] + ∑_{k<2m} C(2m, k+1) 2^k b_k (1 + λ^{−k−1})`,
`E[(∏_{i<n} G(Z_i) − ∏_{i<n} F(Z_i))^{2m}] ≤ n I M^{n−1}` for every `n` (induction on
`integral_pow_prod_sub_prod_succ_le`).  The rate in `h` comes from `b_0` (a first-order
cancellation, `O(h²)`) and from the choice of `λ` (`√h` for Euler–Maruyama, `h` for Milstein). -/
theorem integral_pow_prod_sub_prod_le {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    {m : ℕ} (hm : 0 < m) (hF2 : Integrable (fun x => F x ^ (2 * m)) (gaussianReal 0 1))
    (hG2 : Integrable (fun x => G x ^ (2 * m)) (gaussianReal 0 1)) {b : ℕ → ℝ}
    (hb : ∀ k < 2 * m,
      |∫ x, (G x - F x) ^ (k + 1) * F x ^ (2 * m - (k + 1)) ∂gaussianReal 0 1| ≤ b k)
    {lam I M : ℝ} (hlam : 0 < lam)
    (hI : ∑ k ∈ range (2 * m), ((2 * m).choose (k + 1) : ℝ) * 2 ^ k * b k *
      lam ^ (2 * m - (k + 1)) ≤ I)
    (hM : ∫ x, F x ^ (2 * m) ∂gaussianReal 0 1 + ∑ k ∈ range (2 * m),
      ((2 * m).choose (k + 1) : ℝ) * 2 ^ k * b k * (1 + (lam ^ (k + 1))⁻¹) ≤ M) (n : ℕ) :
    ∫ z, (∏ i ∈ range n, G (z i) - ∏ i ∈ range n, F (z i)) ^ (2 * m) ∂stdNormalSeq ≤
      n * I * M ^ (n - 1) := by
  set m₀ := ∫ x, F x ^ (2 * m) ∂gaussianReal 0 1 with hm₀def
  have hN : Even (2 * m) := even_two_mul m
  have hm₀ : 0 ≤ m₀ := integral_nonneg fun x => hN.pow_nonneg _
  have hb0 : ∀ k ∈ range (2 * m), 0 ≤ b k := fun k hk =>
    (abs_nonneg _).trans (hb k (mem_range.1 hk))
  set S₁ := ∑ k ∈ range (2 * m), ((2 * m).choose (k + 1) : ℝ) * 2 ^ k * b k *
    lam ^ (2 * m - (k + 1)) with hS₁
  set S₂ := ∑ k ∈ range (2 * m), ((2 * m).choose (k + 1) : ℝ) * 2 ^ k * b k *
    (1 + (lam ^ (k + 1))⁻¹) with hS₂
  have hS₁0 : 0 ≤ S₁ := sum_nonneg fun k hk => by have := hb0 k hk; positivity
  have hS₂0 : 0 ≤ S₂ := sum_nonneg fun k hk => by have := hb0 k hk; positivity
  have hI0 : 0 ≤ I := hS₁0.trans hI
  have hMm : m₀ ≤ M := by linarith
  have hM0 : 0 ≤ M := hm₀.trans hMm
  induction n with
  | zero =>
    simp [zero_pow (by omega : 2 * m ≠ 0)]
  | succ n ih =>
    have hstep := integral_pow_prod_sub_prod_succ_le hF hG hF2 hG2 hb hlam n
    set W := ∫ z, (∏ i ∈ range n, G (z i) - ∏ i ∈ range n, F (z i)) ^ (2 * m)
      ∂stdNormalSeq with hW
    have hW0 : 0 ≤ W := integral_nonneg fun z => hN.pow_nonneg _
    have e : ∑ k ∈ range (2 * m), ((2 * m).choose (k + 1) : ℝ) * 2 ^ k * b k *
        (lam ^ (2 * m - (k + 1)) * m₀ ^ n + (1 + (lam ^ (k + 1))⁻¹) * W) =
        S₁ * m₀ ^ n + S₂ * W := by
      rw [hS₁, hS₂, sum_mul, sum_mul, ← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      ring
    rw [e] at hstep
    have hpow : m₀ ^ n ≤ M ^ n := pow_le_pow_left₀ hm₀ hMm n
    have h1 : M * W ≤ M * (n * I * M ^ (n - 1)) := mul_le_mul_of_nonneg_left ih hM0
    have h2 : M * (n * I * M ^ (n - 1)) = n * I * M ^ n := by
      rcases n with _ | n
      · simp
      · rw [Nat.add_sub_cancel, pow_succ]
        ring
    have h3 : S₁ * m₀ ^ n ≤ I * M ^ n :=
      mul_le_mul hI hpow (pow_nonneg hm₀ n) hI0
    have h4 : m₀ * W + S₂ * W ≤ M * W := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) hW0
    rw [Nat.add_sub_cancel]
    push_cast
    nlinarith [h1, h2, h3, h4, hstep]

/-- The growth constant `L = 2m β₁ (τ² + τ^{3−a}) + ∑_{i<2m−1} C(2m, i+2) 2^{i+1} E_{i+2}
(τ^{a(i+2)−2} + τ^i)` of `integral_pow_prod_sub_prod_le_rate` (Giles 2015, §5.1–§5.2: the strong
error of GBM in `L^{2m}`).  Here `β₁` and `E_k` are the constants of the one-step bounds,
`a = 2` (Euler–Maruyama) or `a = 3` (Milstein), and `τ = √t` bounds `√h`. -/
noncomputable def lpGrowth (m a : ℕ) (β₁ τ : ℝ) (E : ℕ → ℝ) : ℝ :=
  2 * m * β₁ * (τ ^ 2 + τ ^ (3 - a)) + ∑ i ∈ range (2 * m - 1),
    ((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * E (i + 2) * (τ ^ (a * (i + 2) - 2) + τ ^ i)

/-- The increment constant `J = 2m β₁ τ^{3−a} + ∑_{i<2m−1} C(2m, i+2) 2^{i+1} E_{i+2} τ^i` of
`integral_pow_prod_sub_prod_le_rate` (Giles 2015, §5.1–§5.2), with the notation of `lpGrowth`. -/
noncomputable def lpIncr (m a : ℕ) (β₁ τ : ℝ) (E : ℕ → ℝ) : ℝ :=
  2 * m * β₁ * τ ^ (3 - a) + ∑ i ∈ range (2 * m - 1),
    ((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * E (i + 2) * τ ^ i

/-- `J ≥ 0` for nonnegative one-step constants (the constant of the `L^{2m}` strong error of GBM,
Giles 2015, §5.1–§5.2). -/
lemma lpIncr_nonneg (m a : ℕ) {β₁ τ : ℝ} {E : ℕ → ℝ} (hβ₁ : 0 ≤ β₁) (hτ : 0 ≤ τ)
    (hE : ∀ k, 0 ≤ E k) : 0 ≤ lpIncr m a β₁ τ E := by
  unfold lpIncr
  exact add_nonneg (by positivity) (sum_nonneg fun i _ => by have := hE (i + 2); positivity)

/-- `L ≥ 0` for nonnegative one-step constants (the growth rate of the `L^{2m}` strong error of
GBM, Giles 2015, §5.1–§5.2). -/
lemma lpGrowth_nonneg (m a : ℕ) {β₁ τ : ℝ} {E : ℕ → ℝ} (hβ₁ : 0 ≤ β₁) (hτ : 0 ≤ τ)
    (hE : ∀ k, 0 ≤ E k) : 0 ≤ lpGrowth m a β₁ τ E := by
  unfold lpGrowth
  exact add_nonneg (by positivity) (sum_nonneg fun i _ => by have := hE (i + 2); positivity)

/-- `J` is monotone in `β₁ ≥ 0`, `τ ≥ 0` and the one-step constants `E ≥ 0` (so that the constant
of the strong error of GBM at a grid time `t_n ≤ T` is at most its value at `T`, Giles 2015,
§5.1–§5.2). -/
lemma lpIncr_mono (m a : ℕ) {β₁ β₁' τ τ' : ℝ} {E E' : ℕ → ℝ} (hβ₁ : 0 ≤ β₁) (hβ : β₁ ≤ β₁')
    (hτ : 0 ≤ τ) (hττ : τ ≤ τ') (hE : ∀ k, 0 ≤ E k) (hEE : ∀ k, E k ≤ E' k) :
    lpIncr m a β₁ τ E ≤ lpIncr m a β₁' τ' E' := by
  unfold lpIncr
  have hβ₁' : 0 ≤ β₁' := hβ₁.trans hβ
  refine add_le_add (by gcongr) (sum_le_sum fun i _ => ?_)
  have h1 := hE (i + 2)
  have h2 := (hE (i + 2)).trans (hEE (i + 2))
  have h3 := hEE (i + 2)
  gcongr

/-- `L` is monotone in `β₁ ≥ 0`, `τ ≥ 0` and the one-step constants `E ≥ 0` (Giles 2015,
§5.1–§5.2; see `lpIncr_mono`). -/
lemma lpGrowth_mono (m a : ℕ) {β₁ β₁' τ τ' : ℝ} {E E' : ℕ → ℝ} (hβ₁ : 0 ≤ β₁) (hβ : β₁ ≤ β₁')
    (hτ : 0 ≤ τ) (hττ : τ ≤ τ') (hE : ∀ k, 0 ≤ E k) (hEE : ∀ k, E k ≤ E' k) :
    lpGrowth m a β₁ τ E ≤ lpGrowth m a β₁' τ' E' := by
  unfold lpGrowth
  have hβ₁' : 0 ≤ β₁' := hβ₁.trans hβ
  refine add_le_add (by gcongr) (sum_le_sum fun i _ => ?_)
  have h1 := hE (i + 2)
  have h2 := (hE (i + 2)).trans (hEE (i + 2))
  have h3 := hEE (i + 2)
  gcongr

/-- **From one-step bounds to the rate.**  In the setting of `integral_pow_prod_sub_prod_le`, with
`δ = √h`, `δ ≤ τ`, `a ∈ {2, 3}`, `E[F^{2m}] ≤ e^{ωδ²}`, the first-order cancellation
`|E[(G − F) F^{2m−1}]| ≤ e^{ωδ²} β₁ δ⁴` and `|E[(G − F)^k F^{2m−k}]| ≤ e^{ωδ²} E_k δ^{ak}` for
`2 ≤ k ≤ 2m`, the choice `λ = δ^{a−1}` gives
`E[(∏ G − ∏ F)^{2m}] ≤ nδ² J e^{(ω + L) nδ²} δ^{2m(a−1)}` with `J = lpIncr`, `L = lpGrowth`, i.e.
`O(h^m)` for `a = 2` (Euler–Maruyama) and `O(h^{2m})` for `a = 3` (Milstein) at the time `t = nh`
(Giles 2015, §5.1–§5.2). -/
lemma integral_pow_prod_sub_prod_le_rate {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    {m : ℕ} (hm : 0 < m) (hF2 : Integrable (fun x => F x ^ (2 * m)) (gaussianReal 0 1))
    (hG2 : Integrable (fun x => G x ^ (2 * m)) (gaussianReal 0 1)) {a : ℕ} (ha : 2 ≤ a)
    (ha' : a ≤ 3) {δ τ ω β₁ : ℝ} {E : ℕ → ℝ} (hδ : 0 < δ) (hδτ : δ ≤ τ)
    (hβ₁ : 0 ≤ β₁) (hE : ∀ k, 0 ≤ E k)
    (hm₀ : ∫ x, F x ^ (2 * m) ∂gaussianReal 0 1 ≤ Real.exp (ω * δ ^ 2))
    (h₁ : |∫ x, (G x - F x) ^ 1 * F x ^ (2 * m - 1) ∂gaussianReal 0 1| ≤
      Real.exp (ω * δ ^ 2) * β₁ * δ ^ 4)
    (hk : ∀ k, 2 ≤ k → k ≤ 2 * m →
      |∫ x, (G x - F x) ^ k * F x ^ (2 * m - k) ∂gaussianReal 0 1| ≤
        Real.exp (ω * δ ^ 2) * E k * δ ^ (a * k)) (n : ℕ) :
    ∫ z, (∏ i ∈ range n, G (z i) - ∏ i ∈ range n, F (z i)) ^ (2 * m) ∂stdNormalSeq ≤
      n * δ ^ 2 * lpIncr m a β₁ τ E *
        Real.exp ((ω + lpGrowth m a β₁ τ E) * (n * δ ^ 2)) * δ ^ (2 * m * (a - 1)) := by
  have hτ : 0 ≤ τ := hδ.le.trans hδτ
  have hδ0 := hδ.le
  set eω := Real.exp (ω * δ ^ 2) with heω
  have heω0 : 0 < eω := Real.exp_pos _
  set J := lpIncr m a β₁ τ E with hJ
  set L := lpGrowth m a β₁ τ E with hL
  have hJ0 : 0 ≤ J := by
    rw [hJ, lpIncr]
    exact add_nonneg (by positivity) (sum_nonneg fun i _ => by have := hE (i + 2); positivity)
  have hL0 : 0 ≤ L := by
    rw [hL, lpGrowth]
    exact add_nonneg (by positivity) (sum_nonneg fun i _ => by have := hE (i + 2); positivity)
  set b : ℕ → ℝ := fun k => if k = 0 then eω * β₁ * δ ^ 4 else eω * E (k + 1) * δ ^ (a * (k + 1))
    with hbdef
  have hb : ∀ k < 2 * m,
      |∫ x, (G x - F x) ^ (k + 1) * F x ^ (2 * m - (k + 1)) ∂gaussianReal 0 1| ≤ b k := by
    intro k hk2
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa [hbdef] using h₁
    · simp only [hbdef, Nat.pos_iff_ne_zero.1 hk0, if_false]
      exact hk (k + 1) (by omega) (by omega)
  obtain ⟨M', hM'⟩ : ∃ M', 2 * m = M' + 1 := ⟨2 * m - 1, by omega⟩
  have hlam : 0 < δ ^ (a - 1) := pow_pos hδ _
  -- the increment
  have hI : ∑ k ∈ range (2 * m), ((2 * m).choose (k + 1) : ℝ) * 2 ^ k * b k *
      (δ ^ (a - 1)) ^ (2 * m - (k + 1)) ≤ eω * J * δ ^ (2 * m * (a - 1) + 2) := by
    rw [hM', sum_range_succ']
    have hcast : (M' : ℝ) + 1 = 2 * m := by exact_mod_cast hM'.symm
    have h0 : ((M' + 1).choose (0 + 1) : ℝ) * 2 ^ 0 * b 0 * (δ ^ (a - 1)) ^ (M' + 1 - (0 + 1)) ≤
        eω * (2 * m * β₁ * τ ^ (3 - a)) * δ ^ (2 * m * (a - 1) + 2) := by
      have e1 : δ ^ 4 * (δ ^ (a - 1)) ^ M' = δ ^ (2 * m * (a - 1) + 2) * δ ^ (3 - a) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        interval_cases a <;> omega
      have e2 : δ ^ (3 - a) ≤ τ ^ (3 - a) := pow_le_pow_left₀ hδ0 hδτ _
      simp only [hbdef, if_true, zero_add, Nat.choose_one_right, pow_zero, mul_one,
        Nat.add_sub_cancel]
      push_cast
      rw [hcast]
      calc 2 * (m : ℝ) * (eω * β₁ * δ ^ 4) * (δ ^ (a - 1)) ^ M'
          = 2 * m * eω * β₁ * (δ ^ 4 * (δ ^ (a - 1)) ^ M') := by ring
        _ = 2 * m * eω * β₁ * (δ ^ (2 * m * (a - 1) + 2) * δ ^ (3 - a)) := by rw [e1]
        _ ≤ 2 * m * eω * β₁ * (δ ^ (2 * m * (a - 1) + 2) * τ ^ (3 - a)) := by gcongr
        _ = _ := by ring
    have hi : ∀ i ∈ range M', ((M' + 1).choose (i + 1 + 1) : ℝ) * 2 ^ (i + 1) * b (i + 1) *
        (δ ^ (a - 1)) ^ (M' + 1 - (i + 1 + 1)) ≤
        eω * (((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * E (i + 2) * τ ^ i) *
          δ ^ (2 * m * (a - 1) + 2) := by
      intro i hi
      have hi' : i + 2 ≤ 2 * m := by have := mem_range.1 hi; omega
      have e1 : δ ^ (a * (i + 1 + 1)) * (δ ^ (a - 1)) ^ (M' + 1 - (i + 1 + 1)) =
          δ ^ (2 * m * (a - 1) + 2) * δ ^ i := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        interval_cases a <;> omega
      have e2 : δ ^ i ≤ τ ^ i := pow_le_pow_left₀ hδ0 hδτ _
      have hEi := hE (i + 2)
      simp only [hbdef, show i + 1 ≠ 0 by omega, if_false]
      rw [← hM']
      calc ((2 * m).choose (i + 1 + 1) : ℝ) * 2 ^ (i + 1) * (eω * E (i + 1 + 1) *
            δ ^ (a * (i + 1 + 1))) * (δ ^ (a - 1)) ^ (2 * m - (i + 1 + 1))
          = ((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * eω * E (i + 2) *
            (δ ^ (a * (i + 1 + 1)) * (δ ^ (a - 1)) ^ (M' + 1 - (i + 1 + 1))) := by
            rw [hM']
            ring
        _ = ((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * eω * E (i + 2) *
            (δ ^ (2 * m * (a - 1) + 2) * δ ^ i) := by rw [e1]
        _ ≤ ((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * eω * E (i + 2) *
            (δ ^ (2 * m * (a - 1) + 2) * τ ^ i) := by gcongr
        _ = _ := by ring
    calc _ ≤ ∑ i ∈ range M', eω * (((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * E (i + 2) *
          τ ^ i) * δ ^ (2 * m * (a - 1) + 2) +
          eω * (2 * m * β₁ * τ ^ (3 - a)) * δ ^ (2 * m * (a - 1) + 2) :=
          add_le_add (sum_le_sum hi) h0
      _ = eω * J * δ ^ (2 * m * (a - 1) + 2) := by
          rw [← sum_mul, ← mul_sum, hJ, lpIncr, show 2 * m - 1 = M' by omega]
          ring
      _ = eω * J * δ ^ ((M' + 1) * (a - 1) + 2) := by rw [← hM']
  -- the growth
  have hM : ∫ x, F x ^ (2 * m) ∂gaussianReal 0 1 + ∑ k ∈ range (2 * m),
      ((2 * m).choose (k + 1) : ℝ) * 2 ^ k * b k * (1 + ((δ ^ (a - 1)) ^ (k + 1))⁻¹) ≤
      eω * (1 + L * δ ^ 2) := by
    have hcast : (M' : ℝ) + 1 = 2 * m := by exact_mod_cast hM'.symm
    have h0 : ((2 * m).choose (0 + 1) : ℝ) * 2 ^ 0 * b 0 * (1 + ((δ ^ (a - 1)) ^ (0 + 1))⁻¹) ≤
        eω * (2 * m * β₁ * (τ ^ 2 + τ ^ (3 - a))) * δ ^ 2 := by
      have e1 : δ ^ 4 = δ ^ (a - 1) * δ ^ (5 - a) := by
        rw [← pow_add]
        congr 1
        omega
      have e2 : δ ^ (5 - a) = δ ^ 2 * δ ^ (3 - a) := by
        rw [← pow_add]
        congr 1
        omega
      have key : δ ^ 4 * (δ ^ (a - 1))⁻¹ = δ ^ 2 * δ ^ (3 - a) := by
        rw [e1, mul_comm (δ ^ (a - 1)), mul_assoc, mul_inv_cancel₀ hlam.ne', mul_one, e2]
      have e3 : δ ^ 4 * (1 + (δ ^ (a - 1))⁻¹) = δ ^ 2 * δ ^ 2 + δ ^ 2 * δ ^ (3 - a) := by
        rw [mul_add, mul_one, key]
        ring
      have e4 : δ ^ 2 * δ ^ 2 + δ ^ 2 * δ ^ (3 - a) ≤ δ ^ 2 * (τ ^ 2 + τ ^ (3 - a)) := by
        rw [← mul_add]
        gcongr
      simp only [hbdef, if_true, zero_add, Nat.choose_one_right, pow_zero, pow_one, mul_one]
      push_cast
      calc 2 * (m : ℝ) * (eω * β₁ * δ ^ 4) * (1 + (δ ^ (a - 1))⁻¹)
          = 2 * m * eω * β₁ * (δ ^ 4 * (1 + (δ ^ (a - 1))⁻¹)) := by ring
        _ = 2 * m * eω * β₁ * (δ ^ 2 * δ ^ 2 + δ ^ 2 * δ ^ (3 - a)) := by rw [e3]
        _ ≤ 2 * m * eω * β₁ * (δ ^ 2 * (τ ^ 2 + τ ^ (3 - a))) := by gcongr
        _ = _ := by ring
    have hi : ∀ i ∈ range M', ((2 * m).choose (i + 1 + 1) : ℝ) * 2 ^ (i + 1) * b (i + 1) *
        (1 + ((δ ^ (a - 1)) ^ (i + 1 + 1))⁻¹) ≤
        eω * (((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * E (i + 2) *
          (τ ^ (a * (i + 2) - 2) + τ ^ i)) * δ ^ 2 := by
      intro i _
      have e1 : δ ^ (a * (i + 1 + 1)) = (δ ^ (a - 1)) ^ (i + 1 + 1) * δ ^ (i + 2) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        interval_cases a <;> ring
      have e2 : δ ^ (a * (i + 1 + 1)) = δ ^ 2 * δ ^ (a * (i + 2) - 2) := by
        rw [← pow_add]
        congr 1
        interval_cases a <;> omega
      have e3 : δ ^ (a * (i + 1 + 1)) * (1 + ((δ ^ (a - 1)) ^ (i + 1 + 1))⁻¹) =
          δ ^ (a * (i + 1 + 1)) + δ ^ (i + 2) := by
        rw [mul_add, mul_one]
        congr 1
        rw [e1, mul_comm ((δ ^ (a - 1)) ^ (i + 1 + 1)), mul_assoc,
          mul_inv_cancel₀ (pow_pos hlam _).ne', mul_one]
      have e4 : δ ^ (a * (i + 1 + 1)) + δ ^ (i + 2) ≤
          δ ^ 2 * (τ ^ (a * (i + 2) - 2) + τ ^ i) := by
        rw [e2, show δ ^ (i + 2) = δ ^ 2 * δ ^ i by ring, ← mul_add]
        gcongr
      have hEi := hE (i + 2)
      simp only [hbdef, show i + 1 ≠ 0 by omega, if_false]
      calc ((2 * m).choose (i + 1 + 1) : ℝ) * 2 ^ (i + 1) * (eω * E (i + 1 + 1) *
            δ ^ (a * (i + 1 + 1))) * (1 + ((δ ^ (a - 1)) ^ (i + 1 + 1))⁻¹)
          = ((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * eω * E (i + 2) *
            (δ ^ (a * (i + 1 + 1)) * (1 + ((δ ^ (a - 1)) ^ (i + 1 + 1))⁻¹)) := by ring
        _ = ((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * eω * E (i + 2) *
            (δ ^ (a * (i + 1 + 1)) + δ ^ (i + 2)) := by rw [e3]
        _ ≤ ((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * eω * E (i + 2) *
            (δ ^ 2 * (τ ^ (a * (i + 2) - 2) + τ ^ i)) := by gcongr
        _ = _ := by ring
    have hsum : ∑ k ∈ range (2 * m), ((2 * m).choose (k + 1) : ℝ) * 2 ^ k * b k *
        (1 + ((δ ^ (a - 1)) ^ (k + 1))⁻¹) ≤ eω * L * δ ^ 2 := by
      rw [show range (2 * m) = range (M' + 1) by rw [hM'], sum_range_succ']
      calc _ ≤ ∑ i ∈ range M', eω * (((2 * m).choose (i + 2) : ℝ) * 2 ^ (i + 1) * E (i + 2) *
            (τ ^ (a * (i + 2) - 2) + τ ^ i)) * δ ^ 2 +
            eω * (2 * m * β₁ * (τ ^ 2 + τ ^ (3 - a))) * δ ^ 2 :=
            add_le_add (sum_le_sum hi) h0
        _ = eω * L * δ ^ 2 := by
            rw [← sum_mul, ← mul_sum, hL, lpGrowth, show 2 * m - 1 = M' by omega]
            ring
    nlinarith [hsum, hm₀]
  have hmain := integral_pow_prod_sub_prod_le hF hG hm hF2 hG2 hb hlam hI hM n
  have hMle : eω * (1 + L * δ ^ 2) ≤ Real.exp ((ω + L) * δ ^ 2) := by
    rw [add_mul, Real.exp_add, ← heω]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (L * δ ^ 2)]) heω0.le
  have hM0 : 0 ≤ eω * (1 + L * δ ^ 2) := by positivity
  refine hmain.trans ?_
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel]
    have hpow : (eω * (1 + L * δ ^ 2)) ^ n ≤ Real.exp ((ω + L) * δ ^ 2) ^ n :=
      pow_le_pow_left₀ hM0 hMle n
    have hexp : eω * Real.exp ((ω + L) * δ ^ 2) ^ n ≤
        Real.exp ((ω + L) * ((n + 1 : ℕ) * δ ^ 2)) := by
      rw [← Real.exp_nat_mul, heω, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      push_cast
      nlinarith [sq_nonneg δ]
    have hd : 0 ≤ δ ^ (2 * m * (a - 1)) := by positivity
    calc ((n + 1 : ℕ) : ℝ) * (eω * J * δ ^ (2 * m * (a - 1) + 2)) *
          (eω * (1 + L * δ ^ 2)) ^ n
        ≤ ((n + 1 : ℕ) : ℝ) * (eω * J * δ ^ (2 * m * (a - 1) + 2)) *
          Real.exp ((ω + L) * δ ^ 2) ^ n := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) * δ ^ 2 * J * (eω * Real.exp ((ω + L) * δ ^ 2) ^ n) *
          δ ^ (2 * m * (a - 1)) := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * δ ^ 2 * J * Real.exp ((ω + L) * ((n + 1 : ℕ) * δ ^ 2)) *
          δ ^ (2 * m * (a - 1)) := by gcongr

/-! ### The weighted one-step bound -/

/-- `e^{(c + sx) j} = e^{jc} e^{(js) x}` (the weights `A^j` of the exact GBM step, Giles 2015,
§5.1–§5.2). -/
lemma exp_add_mul_pow (c s x : ℝ) (j : ℕ) :
    Real.exp (c + s * x) ^ j = Real.exp (j * c) * Real.exp (j * s * x) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- **Weighted moments by the Cameron–Martin shift**: `E[Φ(c + sZ)^k e^{j(c + sZ)}] =
e^{jc + (js)²/2} E[Φ(c + js² + sZ)^k]`, and the left integrand is integrable if the right one is
(Giles 2015, §5.1–§5.2: the exact GBM step is `A = e^{c + sZ}`). -/
lemma integral_pow_mul_exp_pow_eq {Φ : ℝ → ℝ} (hΦ : Measurable Φ) (c s : ℝ) (k j : ℕ)
    (hint : Integrable (fun x => Φ (c + j * s ^ 2 + s * x) ^ k) (gaussianReal 0 1)) :
    Integrable (fun x => Φ (c + s * x) ^ k * Real.exp (c + s * x) ^ j) (gaussianReal 0 1) ∧
      ∫ x, Φ (c + s * x) ^ k * Real.exp (c + s * x) ^ j ∂gaussianReal 0 1 =
        Real.exp (j * c + (j * s) ^ 2 / 2) *
          ∫ x, Φ (c + j * s ^ 2 + s * x) ^ k ∂gaussianReal 0 1 := by
  have hg : Measurable fun x => Φ (c + s * x) ^ k := (hΦ.comp (by fun_prop)).pow_const k
  have hshift : (fun x => Φ (c + s * (x + j * s)) ^ k) =
      fun x => Φ (c + j * s ^ 2 + s * x) ^ k := by
    funext x
    congr 2
    ring
  have e : (fun x => Φ (c + s * x) ^ k * Real.exp (c + s * x) ^ j) =
      fun x => Real.exp (j * c) * (Real.exp (j * s * x) * Φ (c + s * x) ^ k) := by
    funext x
    rw [exp_add_mul_pow]
    ring
  have hi : Integrable (fun x => Φ (c + s * (x + j * s)) ^ k) (gaussianReal 0 1) := by
    rw [hshift]
    exact hint
  rw [e]
  refine ⟨(integrable_exp_mul_mul_gaussian (j * s) hg hi).const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_mul_mul_gaussian (j * s) hg, hshift, ← mul_assoc,
    ← Real.exp_add]

/-- `max(1, e^y)^k ≤ 1 + e^{ky}` (for the weighted one-step bound, Giles 2015, §5.1–§5.2). -/
lemma max_one_exp_pow_le (y : ℝ) (k : ℕ) :
    max 1 (Real.exp y) ^ k ≤ 1 + Real.exp y ^ k := by
  rcases le_total 1 (Real.exp y) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h, one_pow]
    linarith [pow_nonneg (Real.exp_pos y).le k]

/-- **The weighted one-step bound.**  If the scheme step `G` and the exact step `A = e^{c + sx}`
satisfy `|G(x) − A(x)| ≤ Φ(c + sx) max(1, A(x))` with `Φ ≥ 0`, then for `k ≤ N`
`|E[(G − A)^k A^{N−k}]| ≤ e^{(N−k)c + ((N−k)s)²/2} E[Φ(c + (N−k)s² + sZ)^k] +
e^{Nc + (Ns)²/2} E[Φ(c + Ns² + sZ)^k]` (pointwise `max(1, A)^k A^{N−k} ≤ A^{N−k} + A^N` and the
Cameron–Martin shift `integral_pow_mul_exp_pow_eq`; Giles 2015, §5.1–§5.2). -/
lemma abs_integral_sub_pow_mul_exp_pow_le {G Φ : ℝ → ℝ} (hΦ : Measurable Φ)
    (hΦ0 : ∀ y, 0 ≤ Φ y) {c s : ℝ}
    (hGF : ∀ x, |G x - Real.exp (c + s * x)| ≤ Φ (c + s * x) * max 1 (Real.exp (c + s * x)))
    {k N : ℕ} (hk : k ≤ N)
    (hint : ∀ j : ℕ, Integrable (fun x => Φ (c + j * s ^ 2 + s * x) ^ k) (gaussianReal 0 1)) :
    |∫ x, (G x - Real.exp (c + s * x)) ^ k * Real.exp (c + s * x) ^ (N - k) ∂gaussianReal 0 1| ≤
      Real.exp ((N - k : ℕ) * c + ((N - k : ℕ) * s) ^ 2 / 2) *
          ∫ x, Φ (c + (N - k : ℕ) * s ^ 2 + s * x) ^ k ∂gaussianReal 0 1 +
        Real.exp (N * c + (N * s) ^ 2 / 2) *
          ∫ x, Φ (c + N * s ^ 2 + s * x) ^ k ∂gaussianReal 0 1 := by
  obtain ⟨i1, e1⟩ := integral_pow_mul_exp_pow_eq hΦ c s k (N - k) (hint (N - k))
  obtain ⟨i2, e2⟩ := integral_pow_mul_exp_pow_eq hΦ c s k N (hint N)
  have hpt : ∀ x, |(G x - Real.exp (c + s * x)) ^ k * Real.exp (c + s * x) ^ (N - k)| ≤
      Φ (c + s * x) ^ k * Real.exp (c + s * x) ^ (N - k) +
        Φ (c + s * x) ^ k * Real.exp (c + s * x) ^ N := by
    intro x
    set y := c + s * x
    have hey : 0 < Real.exp y := Real.exp_pos y
    have hΦy := hΦ0 y
    rw [abs_mul, abs_pow, abs_pow, abs_of_pos hey]
    have h1 : |G x - Real.exp y| ^ k ≤ (Φ y * max 1 (Real.exp y)) ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) (hGF x) k
    have h2 := max_one_exp_pow_le y k
    have h3 : Real.exp y ^ k * Real.exp y ^ (N - k) = Real.exp y ^ N := by
      rw [← pow_add, Nat.add_sub_cancel' hk]
    calc |G x - Real.exp y| ^ k * Real.exp y ^ (N - k)
        ≤ (Φ y * max 1 (Real.exp y)) ^ k * Real.exp y ^ (N - k) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Φ y ^ k * (max 1 (Real.exp y) ^ k * Real.exp y ^ (N - k)) := by ring
      _ ≤ Φ y ^ k * ((1 + Real.exp y ^ k) * Real.exp y ^ (N - k)) := by gcongr
      _ = Φ y ^ k * Real.exp y ^ (N - k) + Φ y ^ k * Real.exp y ^ N := by rw [← h3]; ring
  calc |∫ x, (G x - Real.exp (c + s * x)) ^ k * Real.exp (c + s * x) ^ (N - k) ∂gaussianReal 0 1|
      ≤ ∫ x, |(G x - Real.exp (c + s * x)) ^ k * Real.exp (c + s * x) ^ (N - k)|
          ∂gaussianReal 0 1 := abs_integral_le_integral_abs
    _ ≤ ∫ x, (Φ (c + s * x) ^ k * Real.exp (c + s * x) ^ (N - k) +
          Φ (c + s * x) ^ k * Real.exp (c + s * x) ^ N) ∂gaussianReal 0 1 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) (i1.add i2)
          (Filter.Eventually.of_forall hpt)
    _ = _ := by rw [integral_add i1 i2, e1, e2]

/-! ### Geometric Brownian motion: the exact step -/

/-- The exponential rate `ω = 2m |r − σ²/2| + 2m²σ² + |r| + 2mσ²` of the `2m`-th moment bounds for
GBM (Giles 2015, §5.1–§5.2): `E[A^{2m}] ≤ e^{ωh}` for the exact step `A`, and the weights
`e^{jc + (js)²/2}`, `j ≤ 2m`, and the factor `e^{|x₁|}` of the first-order term are at most
`e^{ωh}`. -/
noncomputable def gbmLpRate (m : ℕ) (r σ : ℝ) : ℝ :=
  2 * m * |r - σ ^ 2 / 2| + 2 * m ^ 2 * σ ^ 2 + (|r| + 2 * m * σ ^ 2)

/-- `ω ≥ 0` (Giles 2015, §5.1–§5.2). -/
lemma gbmLpRate_nonneg (m : ℕ) (r σ : ℝ) : 0 ≤ gbmLpRate m r σ := by
  unfold gbmLpRate
  positivity

/-- The exponent of the weights: `jc + (js)²/2 ≤ (2m |r − σ²/2| + 2m²σ²) h` for `j ≤ 2m`, with
`c = (r − σ²/2) h` and `s = σ√h` (Giles 2015, §5.1–§5.2). -/
lemma weight_exponent_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) {m j : ℕ} (hj : j ≤ 2 * m) :
    (j : ℝ) * ((r - σ ^ 2 / 2) * h) + ((j : ℝ) * (σ * Real.sqrt h)) ^ 2 / 2 ≤
      (2 * m * |r - σ ^ 2 / 2| + 2 * m ^ 2 * σ ^ 2) * h := by
  have hj' : (j : ℝ) ≤ 2 * m := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  have h1 : (j : ℝ) * ((r - σ ^ 2 / 2) * h) ≤ 2 * m * |r - σ ^ 2 / 2| * h := by
    have := le_abs_self (r - σ ^ 2 / 2)
    have h2 : (j : ℝ) * (r - σ ^ 2 / 2) ≤ 2 * m * |r - σ ^ 2 / 2| :=
      (mul_le_mul_of_nonneg_left this hj0).trans
        (mul_le_mul_of_nonneg_right hj' (abs_nonneg _))
    nlinarith
  have h3 : ((j : ℝ) * (σ * Real.sqrt h)) ^ 2 / 2 ≤ 2 * m ^ 2 * σ ^ 2 * h := by
    rw [mul_pow, hs]
    have : (j : ℝ) ^ 2 ≤ (2 * m) ^ 2 := pow_le_pow_left₀ hj0 hj' 2
    nlinarith [mul_nonneg (sq_nonneg σ) hh]
  nlinarith

/-- The weights are at most `e^{ωh}`: `e^{jc + (js)²/2} ≤ e^{ωh}` for `j ≤ 2m` (Giles 2015,
§5.1–§5.2). -/
lemma weight_exp_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) {m j : ℕ} (hj : j ≤ 2 * m) :
    Real.exp (j * ((r - σ ^ 2 / 2) * h) + (j * (σ * Real.sqrt h)) ^ 2 / 2) ≤
      Real.exp (gbmLpRate m r σ * h) := by
  have hρh : 0 ≤ (|r| + 2 * m * σ ^ 2) * h := mul_nonneg (by positivity) hh
  refine Real.exp_le_exp.2 ((weight_exponent_le r σ hh hj).trans ?_)
  rw [gbmLpRate]
  linarith

/-- The shifted centre is small: `|c + j s²| ≤ (|r − σ²/2| + 2mσ²) h` for `j ≤ 2m` (Giles 2015,
§5.1–§5.2). -/
lemma abs_shift_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) {m j : ℕ} (hj : j ≤ 2 * m) :
    |(r - σ ^ 2 / 2) * h + (j : ℝ) * (σ * Real.sqrt h) ^ 2| ≤
      (|r - σ ^ 2 / 2| + 2 * m * σ ^ 2) * h := by
  have hj' : (j : ℝ) ≤ 2 * m := by exact_mod_cast hj
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  rw [hs]
  calc |(r - σ ^ 2 / 2) * h + (j : ℝ) * (σ ^ 2 * h)|
      ≤ |(r - σ ^ 2 / 2) * h| + |(j : ℝ) * (σ ^ 2 * h)| := abs_add_le _ _
    _ = |r - σ ^ 2 / 2| * h + j * (σ ^ 2 * h) := by
        have e1 : |(r - σ ^ 2 / 2) * h| = |r - σ ^ 2 / 2| * h := by rw [abs_mul, abs_of_nonneg hh]
        have e2 : |(j : ℝ) * (σ ^ 2 * h)| = j * (σ ^ 2 * h) := abs_of_nonneg (by positivity)
        rw [e1, e2]
    _ ≤ |r - σ ^ 2 / 2| * h + 2 * m * (σ ^ 2 * h) := by gcongr
    _ = _ := by ring

/-- `E[A^j] = e^{jc + (js)²/2}` for the exact GBM step `A = e^{c + sZ}` (Giles 2015, §5.1). -/
lemma integral_gbmExpFactor_pow (r σ h : ℝ) (j : ℕ) :
    ∫ x, gbmExpFactor r σ h x ^ j ∂gaussianReal 0 1 =
      Real.exp (j * ((r - σ ^ 2 / 2) * h) + (j * (σ * Real.sqrt h)) ^ 2 / 2) := by
  unfold gbmExpFactor
  simp_rw [exp_add_mul_pow]
  rw [integral_const_mul, integral_exp_mul_gaussian, ← Real.exp_add]

/-- `A^j` is integrable for the exact GBM step `A` (Giles 2015, §5.1). -/
lemma integrable_gbmExpFactor_pow (r σ h : ℝ) (j : ℕ) :
    Integrable (fun x => gbmExpFactor r σ h x ^ j) (gaussianReal 0 1) := by
  unfold gbmExpFactor
  simp_rw [exp_add_mul_pow]
  exact (integrable_exp_mul_gaussianReal _).const_mul _

/-- `E[A^{2m}] ≤ e^{ω (√h)²}` for the exact GBM step `A` (Giles 2015, §5.1–§5.2). -/
lemma integral_gbmExpFactor_pow_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (m : ℕ) :
    ∫ x, gbmExpFactor r σ h x ^ (2 * m) ∂gaussianReal 0 1 ≤
      Real.exp (gbmLpRate m r σ * Real.sqrt h ^ 2) := by
  rw [integral_gbmExpFactor_pow, Real.sq_sqrt hh]
  exact weight_exp_le r σ hh le_rfl

/-- `(s₀ a − s₀ b)^{2m} = s₀^{2m} (b − a)^{2m}` (the factor `S_0^{2m}` of the strong error of GBM,
Giles 2015, §5.1–§5.2). -/
lemma mul_sub_mul_pow_two_mul (s₀ a b : ℝ) (m : ℕ) :
    (s₀ * a - s₀ * b) ^ (2 * m) = s₀ ^ (2 * m) * (b - a) ^ (2 * m) := by
  rw [pow_mul, pow_mul, pow_mul, ← mul_pow]
  congr 1
  ring

/-! ### §5.1: the Euler–Maruyama scheme -/

/-- The one-step constant of the Euler–Maruyama scheme for GBM in `L^{2m}` (Giles 2015, §5.1):
`E_k = 2·3^{k−1} ((σ² + 2(|r − σ²/2| + 2mσ²)² t)^k + (2σ²)^k (2k−1)!!)`, so that
`|E[(B − A)^k A^{2m−k}]| ≤ e^{ωh} E_k h^k` for `2 ≤ k ≤ 2m` and `h ≤ t`
(`gbm_em_onestep_le`). -/
noncomputable def gbmEMStepConst (m : ℕ) (r σ t : ℝ) (k : ℕ) : ℝ :=
  2 * 3 ^ (k - 1) * ((σ ^ 2 + 2 * (|r - σ ^ 2 / 2| + 2 * m * σ ^ 2) ^ 2 * t) ^ k +
    (2 * σ ^ 2) ^ k * Nat.doubleFactorial (2 * k - 1))

/-- The Euler–Maruyama one-step constant is monotone in `t ≥ 0` (Giles 2015, §5.1). -/
lemma gbmEMStepConst_mono (m : ℕ) (r σ : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (k : ℕ) :
    gbmEMStepConst m r σ t k ≤ gbmEMStepConst m r σ T k := by
  unfold gbmEMStepConst
  gcongr

/-- **The Euler–Maruyama step against the exact step** (Giles 2015, §5.1): with `y = c + σ√h x`,
`|1 + rh + σ√h x − e^y| ≤ (σ²h + y²) max(1, e^y)`, since `1 + rh + σ√h x = 1 + y + σ²h/2`. -/
lemma abs_gbmEMFactor_sub_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    |gbmEMFactor r σ h x - Real.exp ((r - σ ^ 2 / 2) * h + σ * Real.sqrt h * x)| ≤
      (σ ^ 2 * h + ((r - σ ^ 2 / 2) * h + σ * Real.sqrt h * x) ^ 2) *
        max 1 (Real.exp ((r - σ ^ 2 / 2) * h + σ * Real.sqrt h * x)) := by
  set y := (r - σ ^ 2 / 2) * h + σ * Real.sqrt h * x with hy
  have e : gbmEMFactor r σ h x - Real.exp y = σ ^ 2 * h / 2 - (Real.exp y - 1 - y) := by
    rw [gbmEMFactor, hy]
    ring
  obtain ⟨h0, h1⟩ := exp_sub_one_sub_le_sq_mul_max y
  have hm1 : 1 ≤ max 1 (Real.exp y) := le_max_left _ _
  have hv : 0 ≤ σ ^ 2 * h := mul_nonneg (sq_nonneg σ) hh
  rw [e, abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hm1 hv,
    mul_le_mul_of_nonneg_left hm1 (sq_nonneg y)]

/-- The shifted Euler–Maruyama moments: for `j ≤ 2m`, `k ≥ 1` and `0 ≤ h ≤ t`,
`e^{jc + (js)²/2} E[(σ²h + (c + js² + sZ)²)^k] ≤ e^{ωh} 3^{k−1} ((σ² + 2(|r − σ²/2| + 2mσ²)² t)^k +
(2σ²)^k (2k−1)!!) h^k` (Giles 2015, §5.1). -/
lemma gbm_em_shifted_le (r σ : ℝ) {h t : ℝ} (hh : 0 ≤ h) (hht : h ≤ t) {m k j : ℕ}
    (hj : j ≤ 2 * m) (hk1 : 1 ≤ k) :
    Integrable (fun x => (σ ^ 2 * h + ((r - σ ^ 2 / 2) * h + j * (σ * Real.sqrt h) ^ 2 +
      σ * Real.sqrt h * x) ^ 2) ^ k) (gaussianReal 0 1) ∧
    Real.exp (j * ((r - σ ^ 2 / 2) * h) + (j * (σ * Real.sqrt h)) ^ 2 / 2) *
      ∫ x, (σ ^ 2 * h + ((r - σ ^ 2 / 2) * h + j * (σ * Real.sqrt h) ^ 2 +
        σ * Real.sqrt h * x) ^ 2) ^ k ∂gaussianReal 0 1 ≤
      Real.exp (gbmLpRate m r σ * h) * (3 ^ (k - 1) *
        ((σ ^ 2 + 2 * (|r - σ ^ 2 / 2| + 2 * m * σ ^ 2) ^ 2 * t) ^ k +
          (2 * σ ^ 2) ^ k * Nat.doubleFactorial (2 * k - 1))) * h ^ k := by
  set A := (r - σ ^ 2 / 2) * h + j * (σ * Real.sqrt h) ^ 2 with hA
  set ā := |r - σ ^ 2 / 2| + 2 * m * σ ^ 2 with hā
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  have hv : 0 ≤ σ ^ 2 * h := mul_nonneg (sq_nonneg σ) hh
  have hle : ∀ x, σ ^ 2 * h + (A + σ * Real.sqrt h * x) ^ 2 ≤
      (σ ^ 2 * h + 2 * A ^ 2) + 2 * (σ ^ 2 * h) * x ^ 2 + 0 * x ^ 4 := by
    intro x
    nlinarith [sq_nonneg (A - σ * Real.sqrt h * x), hs]
  obtain ⟨hint, hbd⟩ := integral_pow_le_of_le_quartic
    (f := fun x => σ ^ 2 * h + (A + σ * Real.sqrt h * x) ^ 2) (by fun_prop)
    (by positivity) (by positivity) le_rfl (fun x => by positivity) hle k
  refine ⟨hint, ?_⟩
  have hA2 : A ^ 2 ≤ ā ^ 2 * t * h := by
    have h1 := abs_shift_le r σ hh hj
    rw [← hA, ← hā] at h1
    have h2 : A ^ 2 ≤ (ā * h) ^ 2 := by
      rw [← sq_abs A]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hā0 : 0 ≤ ā := by positivity
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ā) hh) (sub_nonneg.2 hht)]
  have hP0 : σ ^ 2 * h + 2 * A ^ 2 ≤ (σ ^ 2 + 2 * ā ^ 2 * t) * h := by nlinarith
  have hω := weight_exp_le r σ hh hj (m := m)
  have hk0 : (0 : ℝ) ^ k = 0 := zero_pow (by omega)
  rw [hk0, zero_mul, add_zero] at hbd
  have hbd' : ∫ x, (σ ^ 2 * h + (A + σ * Real.sqrt h * x) ^ 2) ^ k ∂gaussianReal 0 1 ≤
      3 ^ (k - 1) * ((σ ^ 2 + 2 * ā ^ 2 * t) ^ k + (2 * σ ^ 2) ^ k *
        Nat.doubleFactorial (2 * k - 1)) * h ^ k := by
    refine hbd.trans ?_
    have e1 : (2 * (σ ^ 2 * h)) ^ k = (2 * σ ^ 2) ^ k * h ^ k := by rw [← mul_pow]; ring
    have e2 : (σ ^ 2 * h + 2 * A ^ 2) ^ k ≤ ((σ ^ 2 + 2 * ā ^ 2 * t) * h) ^ k :=
      pow_le_pow_left₀ (by positivity) hP0 k
    rw [e1, mul_pow] at *
    have : (0 : ℝ) ≤ 3 ^ (k - 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left e2 this]
  have hI0 : 0 ≤ ∫ x, (σ ^ 2 * h + (A + σ * Real.sqrt h * x) ^ 2) ^ k ∂gaussianReal 0 1 :=
    integral_nonneg fun x => by positivity
  calc Real.exp (j * ((r - σ ^ 2 / 2) * h) + (j * (σ * Real.sqrt h)) ^ 2 / 2) *
        ∫ x, (σ ^ 2 * h + (A + σ * Real.sqrt h * x) ^ 2) ^ k ∂gaussianReal 0 1
      ≤ Real.exp (gbmLpRate m r σ * h) * (3 ^ (k - 1) * ((σ ^ 2 + 2 * ā ^ 2 * t) ^ k +
          (2 * σ ^ 2) ^ k * Nat.doubleFactorial (2 * k - 1)) * h ^ k) :=
        mul_le_mul hω hbd' hI0 (Real.exp_pos _).le
    _ = _ := by ring

/-- `(σ²h + (A + σ√h Z)²)^k` is integrable for `Z ∼ N(0,1)` (the shifted Euler–Maruyama error,
Giles 2015, §5.1). -/
lemma integrable_em_shifted (σ h A : ℝ) (hh : 0 ≤ h) (k : ℕ) :
    Integrable (fun x => (σ ^ 2 * h + (A + σ * Real.sqrt h * x) ^ 2) ^ k) (gaussianReal 0 1) := by
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  have hv : 0 ≤ σ ^ 2 * h := mul_nonneg (sq_nonneg σ) hh
  exact (integral_pow_le_of_le_quartic (f := fun x => σ ^ 2 * h + (A + σ * Real.sqrt h * x) ^ 2)
    (P₀ := σ ^ 2 * h + 2 * A ^ 2) (P₁ := 2 * (σ ^ 2 * h)) (P₂ := 0)
    (by fun_prop) (by positivity) (by positivity) le_rfl (fun x => by positivity)
    (fun x => by nlinarith [sq_nonneg (A - σ * Real.sqrt h * x), hs]) k).1

/-- **The one-step weighted moments of the Euler–Maruyama error** (Giles 2015, §5.1): for
`1 ≤ k ≤ 2m` and `0 ≤ h ≤ t`, `|E[(B − A)^k A^{2m−k}]| ≤ e^{ωh} E_k h^k` with
`E_k = gbmEMStepConst m r σ t k`, `A` the exact step and `B = 1 + rh + σ√h Z` the scheme step. -/
lemma gbm_em_onestep_le (r σ : ℝ) {h t : ℝ} (hh : 0 ≤ h) (hht : h ≤ t) {m k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ 2 * m) :
    |∫ x, (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ k * gbmExpFactor r σ h x ^ (2 * m - k)
        ∂gaussianReal 0 1| ≤
      Real.exp (gbmLpRate m r σ * h) * gbmEMStepConst m r σ t k * h ^ k := by
  have hgen := abs_integral_sub_pow_mul_exp_pow_le (G := gbmEMFactor r σ h)
    (Φ := fun y => σ ^ 2 * h + y ^ 2) (by fun_prop) (fun y => by positivity)
    (c := (r - σ ^ 2 / 2) * h) (s := σ * Real.sqrt h) (abs_gbmEMFactor_sub_le r σ hh) hk
    (fun j => integrable_em_shifted σ h _ hh k)
  have h1 := (gbm_em_shifted_le r σ hh hht (m := m) (k := k) (Nat.sub_le (2 * m) k) hk1).2
  have h2 := (gbm_em_shifted_le r σ hh hht (m := m) (k := k) le_rfl hk1).2
  unfold gbmExpFactor
  refine hgen.trans ?_
  calc _ ≤ Real.exp (gbmLpRate m r σ * h) * (3 ^ (k - 1) *
        ((σ ^ 2 + 2 * (|r - σ ^ 2 / 2| + 2 * m * σ ^ 2) ^ 2 * t) ^ k +
          (2 * σ ^ 2) ^ k * Nat.doubleFactorial (2 * k - 1))) * h ^ k +
      Real.exp (gbmLpRate m r σ * h) * (3 ^ (k - 1) *
        ((σ ^ 2 + 2 * (|r - σ ^ 2 / 2| + 2 * m * σ ^ 2) ^ 2 * t) ^ k +
          (2 * σ ^ 2) ^ k * Nat.doubleFactorial (2 * k - 1))) * h ^ k := add_le_add h1 h2
    _ = _ := by
        unfold gbmEMStepConst
        ring

/-- **The first-order cancellation for Euler–Maruyama** (Giles 2015, §5.1): with `j = 2m − 1`,
`E[(B − A) A^j] = −e^{jc + (js)²/2} (e^{x₁} − 1 − x₁)`, `x₁ = (r + jσ²) h`, computed exactly from
`E[e^{aZ}] = e^{a²/2}` and `E[Z e^{aZ}] = a e^{a²/2}`; hence
`|E[(B − A) A^{2m−1}]| ≤ e^{ωh} (|r| + 2mσ²)² h²`, of second order although `B − A` is only of
first order. -/
lemma gbm_em_onestep_one (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) {m : ℕ} (hm : 0 < m) :
    |∫ x, (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ 1 *
        gbmExpFactor r σ h x ^ (2 * m - 1) ∂gaussianReal 0 1| ≤
      Real.exp (gbmLpRate m r σ * h) * (|r| + 2 * m * σ ^ 2) ^ 2 * h ^ 2 := by
  set j := 2 * m - 1 with hj
  have hjm : j ≤ 2 * m := Nat.sub_le _ _
  have hjc : (j : ℝ) = 2 * m - 1 := by rw [hj, Nat.cast_sub (by omega)]; push_cast; ring
  set c := (r - σ ^ 2 / 2) * h with hc
  set s := σ * Real.sqrt h with hsdef
  have hs : s ^ 2 = σ ^ 2 * h := by rw [hsdef, mul_pow, Real.sq_sqrt hh]
  set x₁ := (r + j * σ ^ 2) * h with hx₁
  set A := Real.exp (j * c + (j * s) ^ 2 / 2) with hA
  -- the integrand
  have e : ∀ x, (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ 1 * gbmExpFactor r σ h x ^ j =
      Real.exp (j * c) * ((1 + r * h) * Real.exp (j * s * x) + s * (x * Real.exp (j * s * x))) -
        gbmExpFactor r σ h x ^ (j + 1) := by
    intro x
    rw [pow_one, sub_mul, ← pow_succ']
    unfold gbmExpFactor gbmEMFactor
    rw [exp_add_mul_pow]
    ring
  have i1 : Integrable (fun x => Real.exp (j * c) * ((1 + r * h) * Real.exp (j * s * x) +
      s * (x * Real.exp (j * s * x)))) (gaussianReal 0 1) :=
    (((integrable_exp_mul_gaussianReal _).const_mul _).add
      ((integrable_mul_exp_mul_gaussian _).const_mul _)).const_mul _
  have hval : ∫ x, (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ 1 *
      gbmExpFactor r σ h x ^ j ∂gaussianReal 0 1 = -(A * (Real.exp x₁ - 1 - x₁)) := by
    simp_rw [e]
    rw [integral_sub i1 (integrable_gbmExpFactor_pow r σ h (j + 1)), integral_const_mul,
      integral_add ((integrable_exp_mul_gaussianReal _).const_mul _)
        ((integrable_mul_exp_mul_gaussian _).const_mul _),
      integral_const_mul, integral_const_mul, integral_exp_mul_gaussian,
      integral_mul_exp_mul_gaussian, integral_gbmExpFactor_pow r σ h]
    have e2 : Real.exp (((j + 1 : ℕ) : ℝ) * ((r - σ ^ 2 / 2) * h) +
        (((j + 1 : ℕ) : ℝ) * (σ * Real.sqrt h)) ^ 2 / 2) = A * Real.exp x₁ := by
      rw [hA, ← Real.exp_add]
      congr 1
      push_cast
      rw [hx₁, ← hc, ← hsdef]
      linear_combination ((j : ℝ) + 1 / 2) * hs
    rw [e2, hA]
    have e3 : Real.exp (j * c) * ((1 + r * h) * Real.exp ((j * s) ^ 2 / 2) +
        s * ((j * s) * Real.exp ((j * s) ^ 2 / 2))) =
        Real.exp (j * c + (j * s) ^ 2 / 2) * (1 + x₁) := by
      rw [Real.exp_add, hx₁]
      linear_combination (Real.exp (j * c) * Real.exp ((j * s) ^ 2 / 2) * j) * hs
    rw [e3]
    ring
  rw [hval, abs_neg]
  obtain ⟨hψ0, hψ1⟩ := exp_sub_one_sub_le_sq_mul_max x₁
  have hA0 : 0 < A := Real.exp_pos _
  rw [abs_of_nonneg (mul_nonneg hA0.le hψ0)]
  -- the bounds
  set ρ := |r| + 2 * m * σ ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hx₁le : |x₁| ≤ ρ * h := by
    rw [hx₁, abs_mul, abs_of_nonneg hh]
    refine mul_le_mul_of_nonneg_right ?_ hh
    calc |r + j * σ ^ 2| ≤ |r| + |(j : ℝ) * σ ^ 2| := abs_add_le _ _
      _ = |r| + j * σ ^ 2 := by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) * σ ^ 2)]
      _ ≤ ρ := by
          rw [hρ]
          have : (j : ℝ) ≤ 2 * m := by exact_mod_cast hjm
          gcongr
  have hx₁sq : x₁ ^ 2 ≤ ρ ^ 2 * h ^ 2 := by
    rw [← mul_pow, ← sq_abs x₁]
    exact pow_le_pow_left₀ (abs_nonneg _) hx₁le 2
  have hmax : max 1 (Real.exp x₁) ≤ Real.exp (ρ * h) := by
    refine max_le (Real.one_le_exp (by positivity)) (Real.exp_le_exp.2 ?_)
    exact (le_abs_self x₁).trans hx₁le
  have hAle : A ≤ Real.exp ((2 * m * |r - σ ^ 2 / 2| + 2 * m ^ 2 * σ ^ 2) * h) :=
    Real.exp_le_exp.2 (weight_exponent_le r σ hh hjm)
  have hω : Real.exp ((2 * m * |r - σ ^ 2 / 2| + 2 * m ^ 2 * σ ^ 2) * h) *
      Real.exp (ρ * h) = Real.exp (gbmLpRate m r σ * h) := by
    rw [← Real.exp_add, gbmLpRate, hρ]
    ring_nf
  calc A * (Real.exp x₁ - 1 - x₁) ≤ A * (x₁ ^ 2 * max 1 (Real.exp x₁)) :=
        mul_le_mul_of_nonneg_left hψ1 hA0.le
    _ ≤ Real.exp ((2 * m * |r - σ ^ 2 / 2| + 2 * m ^ 2 * σ ^ 2) * h) *
        (ρ ^ 2 * h ^ 2 * Real.exp (ρ * h)) := by
        gcongr
    _ = Real.exp (gbmLpRate m r σ * h) * ρ ^ 2 * h ^ 2 := by
        rw [← hω]
        ring

/-- `B^{2m}` is integrable for the Euler–Maruyama step `B = 1 + rh + σ√h Z` of GBM (Giles 2015,
§5.1). -/
lemma integrable_gbmEMFactor_pow (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (m : ℕ) :
    Integrable (fun x => gbmEMFactor r σ h x ^ (2 * m)) (gaussianReal 0 1) := by
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  refine integrable_pow_two_mul_of_sq_le (measurable_gbmEMFactor r σ h)
    (P₀ := 2 * (1 + r * h) ^ 2) (P₁ := 2 * (σ ^ 2 * h)) (P₂ := 0) (by positivity)
    (mul_nonneg zero_le_two (mul_nonneg (sq_nonneg σ) hh)) le_rfl (fun x => ?_) m
  unfold gbmEMFactor
  nlinarith [sq_nonneg (1 + r * h - σ * Real.sqrt h * x), hs]

/-- **The constant of the `2m`-th moment bound for Euler–Maruyama** (Giles 2015, §5.1):
`C_m(t) = S_0^{2m} t J e^{(ω + L) t}` with `ω = gbmLpRate m r σ`, `J = lpIncr m 2 β₁ √t E` and
`L = lpGrowth m 2 β₁ √t E`, `β₁ = (|r| + 2mσ²)²`, `E_k = gbmEMStepConst m r σ t k`.  It is explicit
but far from sharp (see the module docstring). -/
noncomputable def gbmEMMomentConst (m : ℕ) (r σ t s₀ : ℝ) : ℝ :=
  s₀ ^ (2 * m) * t * lpIncr m 2 ((|r| + 2 * m * σ ^ 2) ^ 2) (Real.sqrt t)
      (gbmEMStepConst m r σ t) *
    Real.exp ((gbmLpRate m r σ + lpGrowth m 2 ((|r| + 2 * m * σ ^ 2) ^ 2) (Real.sqrt t)
      (gbmEMStepConst m r σ t)) * t)

/-- The Euler–Maruyama moment constant is nonnegative for `t ≥ 0` (Giles 2015, §5.1). -/
lemma gbmEMMomentConst_nonneg (m : ℕ) (r σ s₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gbmEMMomentConst m r σ t s₀ := by
  unfold gbmEMMomentConst
  have hE : ∀ k, 0 ≤ gbmEMStepConst m r σ t k := fun k => by
    unfold gbmEMStepConst
    positivity
  have := lpIncr_nonneg m 2 (sq_nonneg (|r| + 2 * m * σ ^ 2)) (Real.sqrt_nonneg t) hE
  have hs := (even_two_mul m).pow_nonneg s₀
  positivity

/-- The Euler–Maruyama moment constant is monotone in `t ≥ 0`, so the bound at a grid time
`t_n ≤ T` holds with `C_m(T)` (Giles 2015, §5.1). -/
lemma gbmEMMomentConst_mono (m : ℕ) (r σ s₀ : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    gbmEMMomentConst m r σ t s₀ ≤ gbmEMMomentConst m r σ T s₀ := by
  have hT : 0 ≤ T := ht.trans htT
  have hE : ∀ k, 0 ≤ gbmEMStepConst m r σ t k := fun k => by
    unfold gbmEMStepConst
    positivity
  have hET : ∀ k, 0 ≤ gbmEMStepConst m r σ T k := fun k => by
    unfold gbmEMStepConst
    positivity
  have hs : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hβ : 0 ≤ (|r| + 2 * m * σ ^ 2) ^ 2 := sq_nonneg _
  have hJ := lpIncr_mono m 2 hβ le_rfl (Real.sqrt_nonneg t) hs hE
    (gbmEMStepConst_mono m r σ ht htT)
  have hL := lpGrowth_mono m 2 hβ le_rfl (Real.sqrt_nonneg t) hs hE
    (gbmEMStepConst_mono m r σ ht htT)
  have hJ0 := lpIncr_nonneg m 2 hβ (Real.sqrt_nonneg t) hE
  have hJ0T := lpIncr_nonneg m 2 hβ (Real.sqrt_nonneg T) hET
  have hL0 := lpGrowth_nonneg m 2 hβ (Real.sqrt_nonneg T) hET
  have hω := gbmLpRate_nonneg m r σ
  have hs0 := (even_two_mul m).pow_nonneg s₀
  unfold gbmEMMomentConst
  gcongr

/-- **The strong error of the Euler–Maruyama scheme for GBM in every `L^{2m}`** (Giles 2015, §5.1,
p. 29, l. 1296–1299: "Provided the SDE satisfies the usual conditions (see Theorem 10.2.2 in
(Kloeden and Platen 1992)), the strong error for the Euler discretisation with timestep `h` is
`O(h^{1/2})`"; p. 33, l. 1436: "noting that the strong error is `O(h_ℓ^{1/2})`").  For
`dS = rS dt + σS dW`, a timestep `h ≥ 0` and `m ≥ 1`, the exact solution
`S_{t_n} = S_0 exp((r − σ²/2) t_n + σ W_{t_n})` at the grid time `t_n = nh`,
`W_{t_n} = √h ∑_{i<n} Z_i`, and the Euler–Maruyama value `Ŝ_n` driven by the same increments
satisfy `E[(S_{t_n} − Ŝ_n)^{2m}] ≤ C_m(t_n) h^m`, with the explicit constant
`C_m(t) = gbmEMMomentConst m r σ t S_0` (for `m = 1` this is the mean-square error of
`gbm_em_strong_error`, with a worse constant).  So the strong error is `O(h^{1/2})` in every
`L^{2m}`, as the digital-option heuristic of the paper needs.  The constant is explicit but far
from sharp (see the module docstring). -/
theorem gbm_em_moment_error (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) {m : ℕ} (hm : 0 < m) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
        emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m) ∂stdNormalSeq ≤
      gbmEMMomentConst m r σ (n * h) s₀ * h ^ m := by
  simp_rw [gbmExp_eq_prod, emPath_gbm, mul_sub_mul_pow_two_mul]
  rw [integral_const_mul]
  have hm2 : 2 * m ≠ 0 := by omega
  rcases hh.eq_or_lt with rfl | hh0
  · have hB : ∀ x, gbmEMFactor r σ 0 x = 1 := fun x => by
      rw [gbmEMFactor, Real.sqrt_zero]
      ring
    have hA : ∀ x, gbmExpFactor r σ 0 x = 1 := fun x => by
      rw [gbmExpFactor, Real.sqrt_zero]
      simp
    simp only [hA, hB, prod_const_one, sub_self, zero_pow hm2, integral_zero, mul_zero,
      zero_pow (by omega : m ≠ 0), le_refl]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul, prod_range_zero, sub_self, zero_pow hm2, integral_zero,
      mul_zero]
    exact mul_nonneg (gbmEMMomentConst_nonneg m r σ s₀ le_rfl) (pow_nonneg hh0.le m)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hht : h ≤ n * h := le_mul_of_one_le_left hh hn1
  set δ := Real.sqrt h with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.2 hh0
  have hδ2 : δ ^ 2 = h := Real.sq_sqrt hh
  have hδτ : δ ≤ Real.sqrt (n * h) := Real.sqrt_le_sqrt hht
  have hρ : 0 ≤ (|r| + 2 * m * σ ^ 2) ^ 2 := sq_nonneg _
  have hE : ∀ k, 0 ≤ gbmEMStepConst m r σ (n * h) k := fun k => by
    unfold gbmEMStepConst
    have : 0 ≤ n * h := by positivity
    positivity
  have h₁ : |∫ x, (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ 1 *
      gbmExpFactor r σ h x ^ (2 * m - 1) ∂gaussianReal 0 1| ≤
      Real.exp (gbmLpRate m r σ * δ ^ 2) * (|r| + 2 * m * σ ^ 2) ^ 2 * δ ^ 4 := by
    rw [hδ2, show δ ^ 4 = h ^ 2 by rw [← hδ2]; ring]
    exact gbm_em_onestep_one r σ hh hm
  have hk : ∀ k, 2 ≤ k → k ≤ 2 * m →
      |∫ x, (gbmEMFactor r σ h x - gbmExpFactor r σ h x) ^ k *
        gbmExpFactor r σ h x ^ (2 * m - k) ∂gaussianReal 0 1| ≤
        Real.exp (gbmLpRate m r σ * δ ^ 2) * gbmEMStepConst m r σ (n * h) k * δ ^ (2 * k) := by
    intro k hk2 hk
    rw [hδ2, pow_mul, hδ2]
    exact gbm_em_onestep_le r σ hh hht (by omega) hk
  have key := integral_pow_prod_sub_prod_le_rate (measurable_gbmExpFactor r σ h)
    (measurable_gbmEMFactor r σ h) hm (integrable_gbmExpFactor_pow r σ h (2 * m))
    (integrable_gbmEMFactor_pow r σ hh m) (a := 2) le_rfl (by norm_num) hδ hδτ hρ hE
    (integral_gbmExpFactor_pow_le r σ hh m) h₁ hk n
  rw [hδ2, show 2 * m * (2 - 1) = 2 * m by ring, pow_mul, hδ2] at key
  have hs0 : 0 ≤ s₀ ^ (2 * m) := (even_two_mul m).pow_nonneg _
  calc s₀ ^ (2 * m) * ∫ z, (∏ i ∈ range n, gbmEMFactor r σ h (z i) -
        ∏ i ∈ range n, gbmExpFactor r σ h (z i)) ^ (2 * m) ∂stdNormalSeq
      ≤ s₀ ^ (2 * m) * (n * h * lpIncr m 2 ((|r| + 2 * m * σ ^ 2) ^ 2) (Real.sqrt (n * h))
          (gbmEMStepConst m r σ (n * h)) * Real.exp ((gbmLpRate m r σ +
            lpGrowth m 2 ((|r| + 2 * m * σ ^ 2) ^ 2) (Real.sqrt (n * h))
              (gbmEMStepConst m r σ (n * h))) * (n * h)) * h ^ m) :=
        mul_le_mul_of_nonneg_left key hs0
    _ = _ := by
        unfold gbmEMMomentConst
        ring

/-- **The `L^{2m}` strong error of Euler–Maruyama for GBM, uniformly on the grid up to `T`**
(Giles 2015, §5.1, p. 29, l. 1296–1299: "the strong error for the Euler discretisation with
timestep `h` is `O(h^{1/2})`").  For `h ≥ 0`, `m ≥ 1` and every grid time `t_n = nh ≤ T`,
`E[(S_{t_n} − Ŝ_n)^{2m}] ≤ C_m(T) h^m` with the constant `C_m(T) = gbmEMMomentConst m r σ T S_0`
of the final time (`gbm_em_moment_error` and the monotonicity `gbmEMMomentConst_mono`). -/
theorem gbm_em_moment_error_le (r σ s₀ : ℝ) {h T : ℝ} (hh : 0 ≤ h) (n : ℕ) (hnT : n * h ≤ T)
    {m : ℕ} (hm : 0 < m) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
        emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m) ∂stdNormalSeq ≤
      gbmEMMomentConst m r σ T s₀ * h ^ m :=
  (gbm_em_moment_error r σ s₀ hh n hm).trans (mul_le_mul_of_nonneg_right
    (gbmEMMomentConst_mono m r σ s₀ (by positivity) hnT) (pow_nonneg hh m))

/-- **The fourth moment of the Euler–Maruyama error for GBM is `O(h²)`** (Giles 2015, §5.1, p. 29,
l. 1296–1299: "the strong error for the Euler discretisation with timestep `h` is `O(h^{1/2})`"):
`E[(S_{t_n} − Ŝ_n)⁴] ≤ C₂(T) h²` for every grid time `t_n = nh ≤ T`, with
`C₂(T) = gbmEMMomentConst 2 r σ T S_0`, the case `m = 2` of `gbm_em_moment_error_le`. -/
theorem gbm_em_strong_error_four (r σ s₀ : ℝ) {h T : ℝ} (hh : 0 ≤ h) (n : ℕ)
    (hnT : n * h ≤ T) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
        emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 4 ∂stdNormalSeq ≤
      gbmEMMomentConst 2 r σ T s₀ * h ^ 2 :=
  gbm_em_moment_error_le r σ s₀ hh n hnT two_pos

/-- **The `L^{2m}` strong error of Euler–Maruyama on level `ℓ`** (Giles 2015, §5.1):
`E[(S_T − Ŝ_ℓ)^{2m}] ≤ C_m(T) h_ℓ^m` with `h_ℓ = T 2^{−ℓ}` (`gbm_em_moment_error` with `2^ℓ`
steps). -/
theorem gbm_em_moment_error_level (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ : ℕ) {m : ℕ}
    (hm : 0 < m) :
    ∫ z, (gbmExact r σ T s₀ ℓ z - gbmEM r σ T s₀ ℓ z) ^ (2 * m) ∂stdNormalSeq ≤
      gbmEMMomentConst m r σ T s₀ * (T / 2 ^ ℓ) ^ m := by
  have hh : 0 ≤ T / 2 ^ ℓ := div_nonneg hT (by positivity)
  have h := gbm_em_moment_error r σ s₀ hh (2 ^ ℓ) hm
  rw [cast_two_pow_mul_div] at h
  exact h

/-! ### §5.2: the Milstein scheme -/

/-- The one-step constant of the Milstein scheme for GBM in `L^{2m}` (Giles 2015, §5.2):
`E_k = 2·3^{k−1} (π₀^k + π₁^k (2k−1)!! + π₂^k (4k−1)!!)` with `γ = |r − σ²/2|`, `ā = γ + 2mσ²`,
`π₀ = 4ā³ t √t + (γ²/2 + γā) √t + γ|σ|/2`, `π₁ = 2|σ|³ + γ|σ|/2`, `π₂ = 2|σ|³`, so that
`|E[(B − A)^k A^{2m−k}]| ≤ e^{ωh} E_k h^{3k/2}` for `k ≤ 2m` and `h ≤ t`
(`gbm_mil_onestep_le`). -/
noncomputable def gbmMilStepConst (m : ℕ) (r σ t : ℝ) (k : ℕ) : ℝ :=
  2 * 3 ^ (k - 1) *
    ((4 * (|r - σ ^ 2 / 2| + 2 * m * σ ^ 2) ^ 3 * t * Real.sqrt t +
        (|r - σ ^ 2 / 2| ^ 2 / 2 + |r - σ ^ 2 / 2| * (|r - σ ^ 2 / 2| + 2 * m * σ ^ 2)) *
          Real.sqrt t + |r - σ ^ 2 / 2| * |σ| / 2) ^ k +
      (2 * |σ| ^ 3 + |r - σ ^ 2 / 2| * |σ| / 2) ^ k * Nat.doubleFactorial (2 * k - 1) +
      (2 * |σ| ^ 3) ^ k * Nat.doubleFactorial (4 * k - 1))

/-- The Milstein one-step constant is monotone in `t ≥ 0` (Giles 2015, §5.2). -/
lemma gbmMilStepConst_mono (m : ℕ) (r σ : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (k : ℕ) :
    gbmMilStepConst m r σ t k ≤ gbmMilStepConst m r σ T k := by
  have hT : 0 ≤ T := ht.trans htT
  have hs : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  unfold gbmMilStepConst
  gcongr

/-- **The Milstein step against the exact step** (Giles 2015, §5.2): with `c = (r − σ²/2) h` and
`y = c + σ√h x`, the Milstein step is `1 + y + (y − c)²/2`, so
`|B − e^y| ≤ (|y|³ + c²/2 + |c| |y|) max(1, e^y)` (`abs_exp_sub_quadratic_le`). -/
lemma abs_gbmMilFactor_sub_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    |gbmMilFactor r σ h x - Real.exp ((r - σ ^ 2 / 2) * h + σ * Real.sqrt h * x)| ≤
      (|(r - σ ^ 2 / 2) * h + σ * Real.sqrt h * x| ^ 3 + ((r - σ ^ 2 / 2) * h) ^ 2 / 2 +
        |(r - σ ^ 2 / 2) * h| * |(r - σ ^ 2 / 2) * h + σ * Real.sqrt h * x|) *
        max 1 (Real.exp ((r - σ ^ 2 / 2) * h + σ * Real.sqrt h * x)) := by
  set c := (r - σ ^ 2 / 2) * h with hc
  set y := c + σ * Real.sqrt h * x with hy
  have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh
  have e : gbmMilFactor r σ h x - Real.exp y =
      -(Real.exp y - 1 - y - y ^ 2 / 2) + (c ^ 2 - 2 * c * y) / 2 := by
    rw [gbmMilFactor_eq_quadratic, hsq, hy, hc]
    ring_nf
    rw [hsq]
    ring
  have h3 := abs_exp_sub_quadratic_le y
  have hm1 : 1 ≤ max 1 (Real.exp y) := le_max_left _ _
  have hcy : |c ^ 2 - 2 * c * y| / 2 ≤ c ^ 2 / 2 + |c| * |y| := by
    have := abs_sub (c ^ 2) (2 * c * y)
    rw [abs_of_nonneg (sq_nonneg c), abs_mul, abs_mul, abs_two] at this
    linarith
  have hq : 0 ≤ c ^ 2 / 2 + |c| * |y| := by positivity
  rw [e]
  calc |-(Real.exp y - 1 - y - y ^ 2 / 2) + (c ^ 2 - 2 * c * y) / 2|
      ≤ |Real.exp y - 1 - y - y ^ 2 / 2| + |c ^ 2 - 2 * c * y| / 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_div, abs_two]
    _ ≤ |y| ^ 3 * max 1 (Real.exp y) + (c ^ 2 / 2 + |c| * |y|) * max 1 (Real.exp y) := by
        gcongr
        exact hcy.trans (le_mul_of_one_le_right hq hm1)
    _ = _ := by ring

/-- The shifted Milstein bound is a quartic: `|A + sx|³ + c²/2 + |c| |A + sx| ≤ (4|A|³ + c²/2 +
|c||A| + |c||s|/2) + (2|s|³ + |c||s|/2) x² + 2|s|³ x⁴` (Giles 2015, §5.2). -/
lemma mil_shift_le (c A s x : ℝ) :
    |A + s * x| ^ 3 + c ^ 2 / 2 + |c| * |A + s * x| ≤
      (4 * |A| ^ 3 + c ^ 2 / 2 + |c| * |A| + |c| * |s| / 2) +
        (2 * |s| ^ 3 + |c| * |s| / 2) * x ^ 2 + 2 * |s| ^ 3 * x ^ 4 := by
  have hA := abs_nonneg A
  have hs := abs_nonneg s
  have hc := abs_nonneg c
  have hx := abs_nonneg x
  have h1 : |A + s * x| ≤ |A| + |s| * |x| := (abs_add_le _ _).trans (by rw [abs_mul])
  have h2 : |A + s * x| ^ 3 ≤ 4 * (|A| ^ 3 + (|s| * |x|) ^ 3) :=
    (pow_le_pow_left₀ (abs_nonneg _) h1 3).trans (by
      have := add_pow_le hA (mul_nonneg hs hx) 3
      norm_num at this
      linarith)
  have hx3 : |x| ^ 3 ≤ (x ^ 2 + x ^ 4) / 2 := by
    have : |x| ≤ (1 + x ^ 2) / 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
    have hx2 : |x| ^ 3 = |x| * x ^ 2 := by rw [← sq_abs x]; ring
    rw [hx2]
    nlinarith [sq_nonneg x]
  have hx1 : |x| ≤ (1 + x ^ 2) / 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have h3 : |c| * |A + s * x| ≤ |c| * |A| + |c| * |s| * ((1 + x ^ 2) / 2) := by
    calc |c| * |A + s * x| ≤ |c| * (|A| + |s| * |x|) := mul_le_mul_of_nonneg_left h1 hc
      _ ≤ |c| * (|A| + |s| * ((1 + x ^ 2) / 2)) := by gcongr
      _ = _ := by ring
  have h4 : (|s| * |x|) ^ 3 ≤ |s| ^ 3 * ((x ^ 2 + x ^ 4) / 2) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hx3 (by positivity)
  nlinarith [h2, h3, h4]

/-- `(|A + σ√h Z|³ + c²/2 + |c| |A + σ√h Z|)^k` is integrable for `Z ∼ N(0,1)` (the shifted Milstein
error, Giles 2015, §5.2). -/
lemma integrable_mil_shifted (c σ h A : ℝ) (k : ℕ) :
    Integrable (fun x => (|A + σ * Real.sqrt h * x| ^ 3 + c ^ 2 / 2 +
      |c| * |A + σ * Real.sqrt h * x|) ^ k) (gaussianReal 0 1) :=
  (integral_pow_le_of_le_quartic
    (f := fun x => |A + σ * Real.sqrt h * x| ^ 3 + c ^ 2 / 2 + |c| * |A + σ * Real.sqrt h * x|)
    (by fun_prop) (by positivity) (by positivity) (by positivity) (fun x => by positivity)
    (fun x => mil_shift_le c A (σ * Real.sqrt h) x) k).1

/-- The shifted Milstein moments: for `j ≤ 2m` and `0 ≤ h ≤ t`,
`e^{jc + (js)²/2} E[(|c + js² + sZ|³ + c²/2 + |c| |c + js² + sZ|)^k] ≤ e^{ωh} (E_k / 2) h^{3k/2}`
with `E_k = gbmMilStepConst m r σ t k` (Giles 2015, §5.2). -/
lemma gbm_mil_shifted_le (r σ : ℝ) {h t : ℝ} (hh : 0 ≤ h) (hht : h ≤ t) {m k j : ℕ}
    (hj : j ≤ 2 * m) :
    Real.exp (j * ((r - σ ^ 2 / 2) * h) + (j * (σ * Real.sqrt h)) ^ 2 / 2) *
      ∫ x, (|(r - σ ^ 2 / 2) * h + j * (σ * Real.sqrt h) ^ 2 + σ * Real.sqrt h * x| ^ 3 +
        ((r - σ ^ 2 / 2) * h) ^ 2 / 2 + |(r - σ ^ 2 / 2) * h| *
          |(r - σ ^ 2 / 2) * h + j * (σ * Real.sqrt h) ^ 2 + σ * Real.sqrt h * x|) ^ k
        ∂gaussianReal 0 1 ≤
      Real.exp (gbmLpRate m r σ * h) * (gbmMilStepConst m r σ t k / 2) *
        Real.sqrt h ^ (3 * k) := by
  set c := (r - σ ^ 2 / 2) * h with hc
  set A := c + j * (σ * Real.sqrt h) ^ 2 with hA
  set s := σ * Real.sqrt h with hs
  set γ := |r - σ ^ 2 / 2| with hγ
  set ā := γ + 2 * m * σ ^ 2 with hā
  set δ := Real.sqrt h with hδ
  set τ := Real.sqrt t with hτ
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg h
  have hδτ : δ ≤ τ := Real.sqrt_le_sqrt hht
  have hδ2 : δ ^ 2 = h := Real.sq_sqrt hh
  have hτ2 : τ ^ 2 = t := Real.sq_sqrt (hh.trans hht)
  have hγ0 : 0 ≤ γ := abs_nonneg _
  have hā0 : 0 ≤ ā := by positivity
  have hcabs : |c| = γ * δ ^ 2 := by rw [hc, abs_mul, abs_of_nonneg hh, hδ2]
  have hsabs : |s| = |σ| * δ := by rw [hs, abs_mul, abs_of_nonneg hδ0]
  have hAabs : |A| ≤ ā * δ ^ 2 := by
    have := abs_shift_le r σ hh hj
    rw [← hc, ← hA, ← hγ, ← hā, ← hδ2] at this
    exact this
  -- the quartic bound
  obtain ⟨-, hbd⟩ := integral_pow_le_of_le_quartic
    (f := fun x => |A + s * x| ^ 3 + c ^ 2 / 2 + |c| * |A + s * x|)
    (P₀ := 4 * |A| ^ 3 + c ^ 2 / 2 + |c| * |A| + |c| * |s| / 2)
    (P₁ := 2 * |s| ^ 3 + |c| * |s| / 2) (P₂ := 2 * |s| ^ 3)
    (by fun_prop) (by positivity) (by positivity) (by positivity) (fun x => by positivity)
    (fun x => mil_shift_le c A s x) k
  set π₀ := 4 * ā ^ 3 * t * τ + (γ ^ 2 / 2 + γ * ā) * τ + γ * |σ| / 2 with hπ₀
  set π₁ := 2 * |σ| ^ 3 + γ * |σ| / 2 with hπ₁
  set π₂ := 2 * |σ| ^ 3 with hπ₂
  have hd3 : 0 ≤ δ ^ 3 := pow_nonneg hδ0 3
  have hP0 : 4 * |A| ^ 3 + c ^ 2 / 2 + |c| * |A| + |c| * |s| / 2 ≤ π₀ * δ ^ 3 := by
    have h1 : |A| ^ 3 ≤ (ā * δ ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hAabs 3
    have h2 : δ ^ 3 ≤ τ ^ 3 := pow_le_pow_left₀ hδ0 hδτ 3
    have h3 : c ^ 2 = γ ^ 2 * δ ^ 4 := by rw [← sq_abs c, hcabs]; ring
    have h4 : δ ^ 6 ≤ t * τ * δ ^ 3 := by
      have : δ ^ 6 = δ ^ 3 * δ ^ 3 := by ring
      rw [this, show t * τ = τ ^ 3 by rw [← hτ2]; ring]
      nlinarith
    have h5 : δ ^ 4 ≤ τ * δ ^ 3 := by
      have : δ ^ 4 = δ * δ ^ 3 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hδτ hd3
    have h6 : |c| * |A| ≤ γ * ā * δ ^ 4 := by
      rw [hcabs]
      calc γ * δ ^ 2 * |A| ≤ γ * δ ^ 2 * (ā * δ ^ 2) := by gcongr
        _ = γ * ā * δ ^ 4 := by ring
    rw [hπ₀, h3, hsabs, hcabs]
    have hāc : (ā * δ ^ 2) ^ 3 = ā ^ 3 * δ ^ 6 := by ring
    rw [hāc] at h1
    have : 0 ≤ ā ^ 3 := pow_nonneg hā0 3
    have h7 := mul_le_mul_of_nonneg_left h4 this
    have h8 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ γ ^ 2 / 2 + γ * ā)
    rw [hcabs] at h6
    linarith [h1, h6, h7, h8]
  have hP1 : 2 * |s| ^ 3 + |c| * |s| / 2 = π₁ * δ ^ 3 := by rw [hsabs, hcabs, hπ₁]; ring
  have hP2 : 2 * |s| ^ 3 = π₂ * δ ^ 3 := by rw [hsabs, hπ₂]; ring
  rw [hP1, hP2] at hbd
  have hP0k : (4 * |A| ^ 3 + c ^ 2 / 2 + |c| * |A| + |c| * |s| / 2) ^ k ≤ (π₀ * δ ^ 3) ^ k :=
    pow_le_pow_left₀ (by positivity) hP0 k
  have hint_le : ∫ x, (|A + s * x| ^ 3 + c ^ 2 / 2 + |c| * |A + s * x|) ^ k ∂gaussianReal 0 1 ≤
      gbmMilStepConst m r σ t k / 2 * δ ^ (3 * k) := by
    refine hbd.trans ?_
    have e : gbmMilStepConst m r σ t k / 2 * δ ^ (3 * k) = 3 ^ (k - 1) * ((π₀ * δ ^ 3) ^ k +
        (π₁ * δ ^ 3) ^ k * Nat.doubleFactorial (2 * k - 1) +
        (π₂ * δ ^ 3) ^ k * Nat.doubleFactorial (4 * k - 1)) := by
      rw [gbmMilStepConst, ← hγ, ← hā, ← hτ, mul_pow, mul_pow, mul_pow, ← pow_mul, mul_comm 3 k]
      ring
    rw [e]
    gcongr
  have hω : Real.exp (j * c + (j * s) ^ 2 / 2) ≤ Real.exp (gbmLpRate m r σ * h) :=
    weight_exp_le r σ hh hj
  have hI0 : 0 ≤ ∫ x, (|A + s * x| ^ 3 + c ^ 2 / 2 + |c| * |A + s * x|) ^ k ∂gaussianReal 0 1 :=
    integral_nonneg fun x => by positivity
  calc Real.exp (j * c + (j * s) ^ 2 / 2) *
        ∫ x, (|A + s * x| ^ 3 + c ^ 2 / 2 + |c| * |A + s * x|) ^ k ∂gaussianReal 0 1
      ≤ Real.exp (gbmLpRate m r σ * h) * (gbmMilStepConst m r σ t k / 2 * δ ^ (3 * k)) :=
        mul_le_mul hω hint_le hI0 (Real.exp_pos _).le
    _ = _ := by ring

/-- **The one-step weighted moments of the Milstein error** (Giles 2015, §5.2): for `k ≤ 2m` and
`0 ≤ h ≤ t`, `|E[(B − A)^k A^{2m−k}]| ≤ e^{ωh} E_k (√h)^{3k}` with
`E_k = gbmMilStepConst m r σ t k`. -/
lemma gbm_mil_onestep_le (r σ : ℝ) {h t : ℝ} (hh : 0 ≤ h) (hht : h ≤ t) {m k : ℕ}
    (hk : k ≤ 2 * m) :
    |∫ x, (gbmMilFactor r σ h x - gbmExpFactor r σ h x) ^ k *
        gbmExpFactor r σ h x ^ (2 * m - k) ∂gaussianReal 0 1| ≤
      Real.exp (gbmLpRate m r σ * h) * gbmMilStepConst m r σ t k * Real.sqrt h ^ (3 * k) := by
  have hgen := abs_integral_sub_pow_mul_exp_pow_le (G := gbmMilFactor r σ h)
    (Φ := fun y => |y| ^ 3 + ((r - σ ^ 2 / 2) * h) ^ 2 / 2 + |(r - σ ^ 2 / 2) * h| * |y|)
    (by fun_prop) (fun y => by positivity)
    (c := (r - σ ^ 2 / 2) * h) (s := σ * Real.sqrt h) (abs_gbmMilFactor_sub_le r σ hh) hk
    (fun j => integrable_mil_shifted _ σ h _ k)
  have h1 := gbm_mil_shifted_le r σ hh hht (m := m) (k := k) (Nat.sub_le (2 * m) k)
  have h2 := gbm_mil_shifted_le r σ hh hht (m := m) (k := k) le_rfl
  unfold gbmExpFactor
  refine hgen.trans ?_
  calc _ ≤ Real.exp (gbmLpRate m r σ * h) * (gbmMilStepConst m r σ t k / 2) *
        Real.sqrt h ^ (3 * k) + Real.exp (gbmLpRate m r σ * h) *
          (gbmMilStepConst m r σ t k / 2) * Real.sqrt h ^ (3 * k) := add_le_add h1 h2
    _ = _ := by ring

/-- **The first-order cancellation for Milstein** (Giles 2015, §5.2): with `j = 2m − 1`,
`v = σ²h` and `x₁ = rh + jv`, `E[(B − A) A^j] = e^{jc + (js)²/2} (1 + x₁ + j²v²/2 − e^{x₁})`
(computed exactly with `integral_quadratic_mul_exp_gaussian`), and
`1 + x₁ + j²v²/2 − e^{x₁} = −(e^{x₁} − 1 − x₁ − x₁²/2) − rh (rh + 2jv)/2`, so
`|E[(B − A) A^{2m−1}]| ≤ e^{ωh} ((|r| + 2mσ²)³ t + (|r| + 2mσ²)²) h²` for `0 ≤ h ≤ t`.  The term
`rh (rh + 2jv)/2` is of second order only, unless `r = 0`. -/
lemma gbm_mil_onestep_one (r σ : ℝ) {h t : ℝ} (hh : 0 ≤ h) (hht : h ≤ t) {m : ℕ} (hm : 0 < m) :
    |∫ x, (gbmMilFactor r σ h x - gbmExpFactor r σ h x) ^ 1 *
        gbmExpFactor r σ h x ^ (2 * m - 1) ∂gaussianReal 0 1| ≤
      Real.exp (gbmLpRate m r σ * h) *
        ((|r| + 2 * m * σ ^ 2) ^ 3 * t + (|r| + 2 * m * σ ^ 2) ^ 2) * h ^ 2 := by
  set j := 2 * m - 1 with hj
  have hjm : j ≤ 2 * m := Nat.sub_le _ _
  set c := (r - σ ^ 2 / 2) * h with hc
  set s := σ * Real.sqrt h with hsdef
  have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh
  have hs : s ^ 2 = σ ^ 2 * h := by rw [hsdef, mul_pow, hsq]
  set x₁ := (r + j * σ ^ 2) * h with hx₁
  set A := Real.exp (j * c + (j * s) ^ 2 / 2) with hA
  set c₀ := 1 + r * h - σ ^ 2 * h / 2 with hc₀
  set c₂ := σ ^ 2 / 2 * Real.sqrt h ^ 2 with hc₂
  have e : ∀ x, (gbmMilFactor r σ h x - gbmExpFactor r σ h x) ^ 1 * gbmExpFactor r σ h x ^ j =
      Real.exp (j * c) * ((c₀ + s * x + c₂ * x ^ 2) * Real.exp (j * s * x)) -
        gbmExpFactor r σ h x ^ (j + 1) := by
    intro x
    rw [pow_one, sub_mul, ← pow_succ', gbmMilFactor_eq_quadratic]
    unfold gbmExpFactor
    rw [exp_add_mul_pow]
    ring
  have i1 : Integrable (fun x => Real.exp (j * c) * ((c₀ + s * x + c₂ * x ^ 2) *
      Real.exp (j * s * x))) (gaussianReal 0 1) :=
    (integrable_quadratic_mul_exp_gaussian _ _ _ _).const_mul _
  have hval : ∫ x, (gbmMilFactor r σ h x - gbmExpFactor r σ h x) ^ 1 *
      gbmExpFactor r σ h x ^ j ∂gaussianReal 0 1 =
      A * ((1 + x₁ + j ^ 2 * (σ ^ 2 * h) ^ 2 / 2) - Real.exp x₁) := by
    simp_rw [e]
    rw [integral_sub i1 (integrable_gbmExpFactor_pow r σ h (j + 1)), integral_const_mul,
      integral_quadratic_mul_exp_gaussian, integral_gbmExpFactor_pow r σ h]
    have e2 : Real.exp (((j + 1 : ℕ) : ℝ) * ((r - σ ^ 2 / 2) * h) +
        (((j + 1 : ℕ) : ℝ) * (σ * Real.sqrt h)) ^ 2 / 2) = A * Real.exp x₁ := by
      rw [hA, ← Real.exp_add]
      congr 1
      push_cast
      rw [hx₁, ← hc, ← hsdef]
      linear_combination ((j : ℝ) + 1 / 2) * hs
    rw [e2, hA, Real.exp_add, hx₁, hc₀, hc₂, hsq]
    have hjs : (j * s) ^ 2 = j ^ 2 * (σ ^ 2 * h) := by rw [mul_pow, hs]
    rw [hjs]
    linear_combination (Real.exp (j * c) * Real.exp (j ^ 2 * (σ ^ 2 * h) / 2) * j) * hs
  rw [hval]
  have hA0 : 0 < A := Real.exp_pos _
  have hψ := abs_exp_sub_quadratic_le x₁
  set ρ := |r| + 2 * m * σ ^ 2 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hjr : (j : ℝ) ≤ 2 * m := by exact_mod_cast hjm
  have hx₁le : |x₁| ≤ ρ * h := by
    rw [hx₁, abs_mul, abs_of_nonneg hh]
    refine mul_le_mul_of_nonneg_right ?_ hh
    calc |r + j * σ ^ 2| ≤ |r| + |(j : ℝ) * σ ^ 2| := abs_add_le _ _
      _ = |r| + j * σ ^ 2 := by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) * σ ^ 2)]
      _ ≤ ρ := by rw [hρ]; gcongr
  have hmax : max 1 (Real.exp x₁) ≤ Real.exp (ρ * h) :=
    max_le (Real.one_le_exp (by positivity)) (Real.exp_le_exp.2 ((le_abs_self x₁).trans hx₁le))
  -- `1 + x + j²v²/2 − e^x = −(e^x − 1 − x − x²/2) − r h (r h + 2 j v)/2`
  have e3 : (1 + x₁ + j ^ 2 * (σ ^ 2 * h) ^ 2 / 2) - Real.exp x₁ =
      -(Real.exp x₁ - 1 - x₁ - x₁ ^ 2 / 2) - r * h * (r * h + 2 * j * (σ ^ 2 * h)) / 2 := by
    rw [hx₁]
    ring
  have h4 : |r * h * (r * h + 2 * j * (σ ^ 2 * h)) / 2| ≤ ρ ^ 2 * h ^ 2 := by
    rw [abs_div, abs_two, abs_mul, abs_mul, abs_of_nonneg hh]
    have h5 : |r * h + 2 * j * (σ ^ 2 * h)| ≤ 2 * ρ * h := by
      calc |r * h + 2 * j * (σ ^ 2 * h)| ≤ |r * h| + |2 * j * (σ ^ 2 * h)| := abs_add_le _ _
        _ = |r| * h + 2 * j * (σ ^ 2 * h) := by
            rw [abs_mul, abs_of_nonneg hh, abs_of_nonneg (by positivity :
              (0 : ℝ) ≤ 2 * j * (σ ^ 2 * h))]
        _ ≤ 2 * ρ * h := by
            rw [hρ]
            nlinarith [abs_nonneg r, mul_nonneg (sq_nonneg σ) hh]
    have hr : |r| ≤ ρ := by rw [hρ]; nlinarith [sq_nonneg σ]
    calc |r| * h * |r * h + 2 * j * (σ ^ 2 * h)| / 2 ≤ ρ * h * (2 * ρ * h) / 2 := by gcongr
      _ = ρ ^ 2 * h ^ 2 := by ring
  have h6 : |x₁| ^ 3 * max 1 (Real.exp x₁) ≤ ρ ^ 3 * t * h ^ 2 * Real.exp (ρ * h) := by
    have h7 : |x₁| ^ 3 ≤ (ρ * h) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hx₁le 3
    have h8 : (ρ * h) ^ 3 ≤ ρ ^ 3 * t * h ^ 2 := by
      rw [mul_pow, show h ^ 3 = h * h ^ 2 by ring]
      have : 0 ≤ ρ ^ 3 := pow_nonneg hρ0 3
      nlinarith [mul_le_mul_of_nonneg_left hht (mul_nonneg this (sq_nonneg h))]
    have ht : 0 ≤ t := hh.trans hht
    calc |x₁| ^ 3 * max 1 (Real.exp x₁) ≤ (ρ ^ 3 * t * h ^ 2) * Real.exp (ρ * h) :=
          mul_le_mul (h7.trans h8) hmax (by positivity)
            (mul_nonneg (mul_nonneg (pow_nonneg hρ0 3) ht) (sq_nonneg h))
      _ = _ := by ring
  have hAle : A ≤ Real.exp ((2 * m * |r - σ ^ 2 / 2| + 2 * m ^ 2 * σ ^ 2) * h) :=
    Real.exp_le_exp.2 (weight_exponent_le r σ hh hjm)
  have hω : Real.exp ((2 * m * |r - σ ^ 2 / 2| + 2 * m ^ 2 * σ ^ 2) * h) *
      Real.exp (ρ * h) = Real.exp (gbmLpRate m r σ * h) := by
    rw [← Real.exp_add, gbmLpRate, hρ]
    ring_nf
  have he1 : 1 ≤ Real.exp (ρ * h) := Real.one_le_exp (by positivity)
  rw [e3, abs_mul, abs_of_pos hA0]
  have hsum : |-(Real.exp x₁ - 1 - x₁ - x₁ ^ 2 / 2) - r * h * (r * h + 2 * j * (σ ^ 2 * h)) / 2| ≤
      |x₁| ^ 3 * max 1 (Real.exp x₁) + ρ ^ 2 * h ^ 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_neg]
    exact add_le_add hψ h4
  have hsum2 : |x₁| ^ 3 * max 1 (Real.exp x₁) + ρ ^ 2 * h ^ 2 ≤
      ρ ^ 3 * t * h ^ 2 * Real.exp (ρ * h) + ρ ^ 2 * h ^ 2 * Real.exp (ρ * h) :=
    add_le_add h6 (le_mul_of_one_le_right (by positivity) he1)
  set E₀ := Real.exp ((2 * m * |r - σ ^ 2 / 2| + 2 * m ^ 2 * σ ^ 2) * h) with hE₀
  set P := |-(Real.exp x₁ - 1 - x₁ - x₁ ^ 2 / 2) - r * h * (r * h + 2 * j * (σ ^ 2 * h)) / 2|
  set Q := |x₁| ^ 3 * max 1 (Real.exp x₁) + ρ ^ 2 * h ^ 2
  set R := ρ ^ 3 * t * h ^ 2 * Real.exp (ρ * h) + ρ ^ 2 * h ^ 2 * Real.exp (ρ * h) with hR
  have hP0 : 0 ≤ P := abs_nonneg _
  clear_value P Q
  calc A * P ≤ E₀ * R := mul_le_mul hAle (hsum.trans hsum2) hP0 (Real.exp_pos _).le
    _ = Real.exp (gbmLpRate m r σ * h) * (ρ ^ 3 * t + ρ ^ 2) * h ^ 2 := by
        rw [← hω, hR]
        ring

/-- `B^{2m}` is integrable for the Milstein step `B` of GBM (Giles 2015, §5.2). -/
lemma integrable_gbmMilFactor_pow (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (m : ℕ) :
    Integrable (fun x => gbmMilFactor r σ h x ^ (2 * m)) (gaussianReal 0 1) := by
  have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh
  refine integrable_pow_two_mul_of_sq_le (measurable_gbmMilFactor r σ h)
    (P₀ := 3 * (1 + r * h - σ ^ 2 * h / 2) ^ 2) (P₁ := 3 * (σ ^ 2 * h))
    (P₂ := 3 * (σ ^ 2 / 2 * h) ^ 2) (by positivity)
    (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg σ) hh)) (by positivity) (fun x => ?_) m
  rw [gbmMilFactor_eq_quadratic, hsq]
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, hsq]
  nlinarith [sq_nonneg (1 + r * h - σ ^ 2 * h / 2 - σ * Real.sqrt h * x),
    sq_nonneg (1 + r * h - σ ^ 2 * h / 2 - σ ^ 2 / 2 * h * x ^ 2),
    sq_nonneg (σ * Real.sqrt h * x - σ ^ 2 / 2 * h * x ^ 2), hs]

/-- **The constant of the `2m`-th moment bound for Milstein** (Giles 2015, §5.2):
`C_m(t) = S_0^{2m} t J e^{(ω + L) t}` with `ω = gbmLpRate m r σ`, `J = lpIncr m 3 β₁ √t E`,
`L = lpGrowth m 3 β₁ √t E`, `β₁ = (|r| + 2mσ²)³ t + (|r| + 2mσ²)²` and
`E_k = gbmMilStepConst m r σ t k`.  It is explicit but far from sharp (see the module docstring). -/
noncomputable def gbmMilMomentConst (m : ℕ) (r σ t s₀ : ℝ) : ℝ :=
  s₀ ^ (2 * m) * t * lpIncr m 3 ((|r| + 2 * m * σ ^ 2) ^ 3 * t + (|r| + 2 * m * σ ^ 2) ^ 2)
      (Real.sqrt t) (gbmMilStepConst m r σ t) *
    Real.exp ((gbmLpRate m r σ + lpGrowth m 3 ((|r| + 2 * m * σ ^ 2) ^ 3 * t +
      (|r| + 2 * m * σ ^ 2) ^ 2) (Real.sqrt t) (gbmMilStepConst m r σ t)) * t)

/-- The Milstein moment constant is nonnegative for `t ≥ 0` (Giles 2015, §5.2). -/
lemma gbmMilMomentConst_nonneg (m : ℕ) (r σ s₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gbmMilMomentConst m r σ t s₀ := by
  unfold gbmMilMomentConst
  have hE : ∀ k, 0 ≤ gbmMilStepConst m r σ t k := fun k => by
    unfold gbmMilStepConst
    positivity
  have := lpIncr_nonneg m 3 (by positivity :
    0 ≤ (|r| + 2 * m * σ ^ 2) ^ 3 * t + (|r| + 2 * m * σ ^ 2) ^ 2) (Real.sqrt_nonneg t) hE
  have hs := (even_two_mul m).pow_nonneg s₀
  positivity

/-- The Milstein moment constant is monotone in `t ≥ 0`, so the bound at a grid time `t_n ≤ T`
holds with `C_m(T)` (Giles 2015, §5.2). -/
lemma gbmMilMomentConst_mono (m : ℕ) (r σ s₀ : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    gbmMilMomentConst m r σ t s₀ ≤ gbmMilMomentConst m r σ T s₀ := by
  have hT : 0 ≤ T := ht.trans htT
  have hE : ∀ k, 0 ≤ gbmMilStepConst m r σ t k := fun k => by
    unfold gbmMilStepConst
    positivity
  have hET : ∀ k, 0 ≤ gbmMilStepConst m r σ T k := fun k => by
    unfold gbmMilStepConst
    positivity
  have hs : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hβ : 0 ≤ (|r| + 2 * m * σ ^ 2) ^ 3 * t + (|r| + 2 * m * σ ^ 2) ^ 2 := by positivity
  have hββ : (|r| + 2 * m * σ ^ 2) ^ 3 * t + (|r| + 2 * m * σ ^ 2) ^ 2 ≤
      (|r| + 2 * m * σ ^ 2) ^ 3 * T + (|r| + 2 * m * σ ^ 2) ^ 2 := by gcongr
  have hβT : 0 ≤ (|r| + 2 * m * σ ^ 2) ^ 3 * T + (|r| + 2 * m * σ ^ 2) ^ 2 := by positivity
  have hJ := lpIncr_mono m 3 hβ hββ (Real.sqrt_nonneg t) hs hE
    (gbmMilStepConst_mono m r σ ht htT)
  have hL := lpGrowth_mono m 3 hβ hββ (Real.sqrt_nonneg t) hs hE
    (gbmMilStepConst_mono m r σ ht htT)
  have hJ0 := lpIncr_nonneg m 3 hβ (Real.sqrt_nonneg t) hE
  have hJ0T := lpIncr_nonneg m 3 hβT (Real.sqrt_nonneg T) hET
  have hL0 := lpGrowth_nonneg m 3 hβT (Real.sqrt_nonneg T) hET
  have hω := gbmLpRate_nonneg m r σ
  have hs0 := (even_two_mul m).pow_nonneg s₀
  unfold gbmMilMomentConst
  gcongr

/-- **First-order strong convergence of the Milstein scheme for GBM in every `L^{2m}`** (Giles 2015,
§5.2, p. 35, l. 1499–1500: the Milstein discretisation "gives first order strong convergence under
certain conditions (see Theorem 10.3.5 in (Kloeden and Platen 1992))").  With the notation of
`gbm_em_moment_error` and the Milstein path `Ŝ_n` (`milsteinPath`) driven by the same increments,
`E[(S_{t_n} − Ŝ_n)^{2m}] ≤ C_m(t_n) h^{2m}` for every `m ≥ 1`, with the explicit constant
`C_m(t) = gbmMilMomentConst m r σ t S_0` (`m = 1` is `gbm_mil_strong_error`, with a worse
constant).  The constant is explicit but far from sharp (see the module docstring). -/
theorem gbm_mil_moment_error (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) {m : ℕ} (hm : 0 < m) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
        milsteinPath (fun S => r * S) (fun S => σ * S) h s₀ z n) ^ (2 * m) ∂stdNormalSeq ≤
      gbmMilMomentConst m r σ (n * h) s₀ * h ^ (2 * m) := by
  simp_rw [gbmExp_eq_prod, milsteinPath_gbm, mul_sub_mul_pow_two_mul]
  rw [integral_const_mul]
  have hm2 : 2 * m ≠ 0 := by omega
  rcases hh.eq_or_lt with rfl | hh0
  · have hB : ∀ x, gbmMilFactor r σ 0 x = 1 := fun x => by
      rw [gbmMilFactor, Real.sqrt_zero]
      ring
    have hA : ∀ x, gbmExpFactor r σ 0 x = 1 := fun x => by
      rw [gbmExpFactor, Real.sqrt_zero]
      simp
    simp only [hA, hB, prod_const_one, sub_self, zero_pow hm2, integral_zero, mul_zero, le_refl]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul, prod_range_zero, sub_self, zero_pow hm2, integral_zero,
      mul_zero]
    exact mul_nonneg (gbmMilMomentConst_nonneg m r σ s₀ le_rfl) (pow_nonneg hh0.le _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hht : h ≤ n * h := le_mul_of_one_le_left hh hn1
  set δ := Real.sqrt h with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.2 hh0
  have hδ2 : δ ^ 2 = h := Real.sq_sqrt hh
  have hδτ : δ ≤ Real.sqrt (n * h) := Real.sqrt_le_sqrt hht
  have hβ : 0 ≤ (|r| + 2 * m * σ ^ 2) ^ 3 * (n * h) + (|r| + 2 * m * σ ^ 2) ^ 2 := by positivity
  have hE : ∀ k, 0 ≤ gbmMilStepConst m r σ (n * h) k := fun k => by
    unfold gbmMilStepConst
    have : 0 ≤ n * h := by positivity
    positivity
  have h₁ : |∫ x, (gbmMilFactor r σ h x - gbmExpFactor r σ h x) ^ 1 *
      gbmExpFactor r σ h x ^ (2 * m - 1) ∂gaussianReal 0 1| ≤
      Real.exp (gbmLpRate m r σ * δ ^ 2) *
        ((|r| + 2 * m * σ ^ 2) ^ 3 * (n * h) + (|r| + 2 * m * σ ^ 2) ^ 2) * δ ^ 4 := by
    rw [hδ2, show δ ^ 4 = h ^ 2 by rw [← hδ2]; ring]
    exact gbm_mil_onestep_one r σ hh hht hm
  have hk : ∀ k, 2 ≤ k → k ≤ 2 * m →
      |∫ x, (gbmMilFactor r σ h x - gbmExpFactor r σ h x) ^ k *
        gbmExpFactor r σ h x ^ (2 * m - k) ∂gaussianReal 0 1| ≤
        Real.exp (gbmLpRate m r σ * δ ^ 2) * gbmMilStepConst m r σ (n * h) k * δ ^ (3 * k) := by
    intro k _ hk
    rw [hδ2]
    exact gbm_mil_onestep_le r σ hh hht hk
  have key := integral_pow_prod_sub_prod_le_rate (measurable_gbmExpFactor r σ h)
    (measurable_gbmMilFactor r σ h) hm (integrable_gbmExpFactor_pow r σ h (2 * m))
    (integrable_gbmMilFactor_pow r σ hh m) (a := 3) (by norm_num) le_rfl hδ hδτ hβ hE
    (integral_gbmExpFactor_pow_le r σ hh m) h₁ hk n
  rw [hδ2, show 2 * m * (3 - 1) = 2 * (2 * m) by ring, pow_mul, hδ2] at key
  have hs0 : 0 ≤ s₀ ^ (2 * m) := (even_two_mul m).pow_nonneg _
  calc s₀ ^ (2 * m) * ∫ z, (∏ i ∈ range n, gbmMilFactor r σ h (z i) -
        ∏ i ∈ range n, gbmExpFactor r σ h (z i)) ^ (2 * m) ∂stdNormalSeq
      ≤ s₀ ^ (2 * m) * (n * h * lpIncr m 3 ((|r| + 2 * m * σ ^ 2) ^ 3 * (n * h) +
          (|r| + 2 * m * σ ^ 2) ^ 2) (Real.sqrt (n * h)) (gbmMilStepConst m r σ (n * h)) *
          Real.exp ((gbmLpRate m r σ + lpGrowth m 3 ((|r| + 2 * m * σ ^ 2) ^ 3 * (n * h) +
            (|r| + 2 * m * σ ^ 2) ^ 2) (Real.sqrt (n * h)) (gbmMilStepConst m r σ (n * h))) *
            (n * h)) * h ^ (2 * m)) :=
        mul_le_mul_of_nonneg_left key hs0
    _ = _ := by
        unfold gbmMilMomentConst
        ring

/-- **The `L^{2m}` strong error of Milstein for GBM, uniformly on the grid up to `T`** (Giles 2015,
§5.2, p. 35, l. 1499–1500: "first order strong convergence").  For `h ≥ 0`, `m ≥ 1` and every grid
time `t_n = nh ≤ T`, `E[(S_{t_n} − Ŝ_n)^{2m}] ≤ C_m(T) h^{2m}` with the constant
`C_m(T) = gbmMilMomentConst m r σ T S_0` of the final time (`gbm_mil_moment_error` and the
monotonicity `gbmMilMomentConst_mono`). -/
theorem gbm_mil_moment_error_le (r σ s₀ : ℝ) {h T : ℝ} (hh : 0 ≤ h) (n : ℕ) (hnT : n * h ≤ T)
    {m : ℕ} (hm : 0 < m) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
        milsteinPath (fun S => r * S) (fun S => σ * S) h s₀ z n) ^ (2 * m) ∂stdNormalSeq ≤
      gbmMilMomentConst m r σ T s₀ * h ^ (2 * m) :=
  (gbm_mil_moment_error r σ s₀ hh n hm).trans (mul_le_mul_of_nonneg_right
    (gbmMilMomentConst_mono m r σ s₀ (by positivity) hnT) (pow_nonneg hh _))

/-- **The fourth moment of the Milstein error for GBM is `O(h⁴)`** (Giles 2015, §5.2, p. 35,
l. 1499–1500: "first order strong convergence"): `E[(S_{t_n} − Ŝ_n)⁴] ≤ C₂(T) h⁴` for every grid
time `t_n = nh ≤ T`, with `C₂(T) = gbmMilMomentConst 2 r σ T S_0`, the case `m = 2` of
`gbm_mil_moment_error_le`. -/
theorem gbm_mil_strong_error_four (r σ s₀ : ℝ) {h T : ℝ} (hh : 0 ≤ h) (n : ℕ)
    (hnT : n * h ≤ T) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
        milsteinPath (fun S => r * S) (fun S => σ * S) h s₀ z n) ^ 4 ∂stdNormalSeq ≤
      gbmMilMomentConst 2 r σ T s₀ * h ^ 4 :=
  gbm_mil_moment_error_le r σ s₀ hh n hnT two_pos

/-- **The `L^{2m}` strong error of Milstein on level `ℓ`** (Giles 2015, §5.2):
`E[(S_T − Ŝ_ℓ)^{2m}] ≤ C_m(T) h_ℓ^{2m}` with `h_ℓ = T 2^{−ℓ}` (`gbm_mil_moment_error` with `2^ℓ`
steps). -/
theorem gbm_mil_moment_error_level (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ : ℕ) {m : ℕ}
    (hm : 0 < m) :
    ∫ z, (gbmExact r σ T s₀ ℓ z - gbmMil r σ T s₀ ℓ z) ^ (2 * m) ∂stdNormalSeq ≤
      gbmMilMomentConst m r σ T s₀ * (T / 2 ^ ℓ) ^ (2 * m) := by
  have hh : 0 ≤ T / 2 ^ ℓ := div_nonneg hT (by positivity)
  have h := gbm_mil_moment_error r σ s₀ hh (2 ^ ℓ) hm
  rw [cast_two_pow_mul_div] at h
  exact h

/-! ### §5.1–§5.2: the digital option -/

/-- `(S_T − Ŝ_ℓ)^{2m}` is integrable for the Euler–Maruyama approximation on level `ℓ` (Giles 2015,
§5.1). -/
lemma integrable_gbm_em_err_pow (r σ T s₀ : ℝ) {ℓ : ℕ} (hh : 0 ≤ T / 2 ^ ℓ) (m : ℕ) :
    Integrable (fun z => (gbmExact r σ T s₀ ℓ z - gbmEM r σ T s₀ ℓ z) ^ (2 * m)) stdNormalSeq := by
  simp_rw [gbmExact_eq_prod, gbmEM_eq_prod, mul_sub_mul_pow_two_mul]
  exact (integrable_pow_prod_sub_prod (measurable_gbmExpFactor r σ _)
    (measurable_gbmEMFactor r σ _) (even_two_mul m) (integrable_gbmExpFactor_pow r σ _ _)
    (integrable_gbmEMFactor_pow r σ hh m) _).const_mul _

/-- `(S_T − Ŝ_ℓ)^{2m}` is integrable for the Milstein approximation on level `ℓ` (Giles 2015,
§5.2). -/
lemma integrable_gbm_mil_err_pow (r σ T s₀ : ℝ) {ℓ : ℕ} (hh : 0 ≤ T / 2 ^ ℓ) (m : ℕ) :
    Integrable (fun z => (gbmExact r σ T s₀ ℓ z - gbmMil r σ T s₀ ℓ z) ^ (2 * m))
      stdNormalSeq := by
  simp_rw [gbmExact_eq_prod, gbmMil_eq_prod, mul_sub_mul_pow_two_mul]
  exact (integrable_pow_prod_sub_prod (measurable_gbmExpFactor r σ _)
    (measurable_gbmMilFactor r σ _) (even_two_mul m) (integrable_gbmExpFactor_pow r σ _ _)
    (integrable_gbmMilFactor_pow r σ hh m) _).const_mul _

/-- **The fraction of GBM paths on either side of the strike, from `2m`-th moments** (Giles 2015,
§5.1, p. 33, l. 1436–1441: "noting that the strong error is `O(h_ℓ^{1/2})`, and there is a bounded
density of paths terminating in the neighbourhood of `K`, there is therefore an `O(h_ℓ^{1/2})`
fraction of the samples with the coarse and fine paths on either side of the strike").  For a fine
approximation `Y^f` of `S_T` on level `ℓ + 1` and a coarse one `Y^c` on level `ℓ`, driven by the
summed increments (`pairAvg`), the payoffs `H(Y^f − K)`, `H(Y^c − K)` differ with probability at
most `(2ρ + 1) (E[(S_T − Y^f)^{2m}]^{1/(2m+1)} + E[(S_T − Y^c)^{2m}]^{1/(2m+1)})`, `ρ` the
maximum of the lognormal density (`gbmExact_smallBall`, `digital_mismatch_le_of_moment`). -/
lemma gbm_digital_mismatch_le_of_moment (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (ℓ : ℕ) {Yf Yc : (ℕ → ℝ) → ℝ} (hYf : Measurable Yf)
    (hYc : Measurable Yc) {m : ℕ}
    (hintf : Integrable (fun z => (gbmExact r σ T s₀ (ℓ + 1) z - Yf z) ^ (2 * m)) stdNormalSeq)
    (hintc : Integrable (fun z => (gbmExact r σ T s₀ ℓ z - Yc z) ^ (2 * m)) stdNormalSeq) :
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (Yf z) ≠
        (Set.Ioi K).indicator 1 (Yc (pairAvg z))} ≤
      (2 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1) *
        ((∫ z, (gbmExact r σ T s₀ (ℓ + 1) z - Yf z) ^ (2 * m) ∂stdNormalSeq) ^
            (1 / (2 * m + 1 : ℝ)) +
          (∫ z, (gbmExact r σ T s₀ ℓ z - Yc z) ^ (2 * m) ∂stdNormalSeq) ^
            (1 / (2 * m + 1 : ℝ))) := by
  set ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)
    with hρdef
  set X := gbmExact r σ T s₀ (ℓ + 1) with hXdef
  have hXm : Measurable X := measurable_gbmExact r σ T s₀ (ℓ + 1)
  have hball : ∀ δ, 0 < δ → stdNormalSeq.real {z | |X z - K| ≤ δ} ≤ 2 * ρ * δ := fun δ hδ =>
    gbmExact_smallBall r σ hs₀ hσ hT K (ℓ + 1) hδ
  have hXc : ∀ z, X z = gbmExact r σ T s₀ ℓ (pairAvg z) := fun z =>
    (gbmExact_pairAvg r σ T s₀ ℓ z).symm
  have hN : Even (2 * m) := even_two_mul m
  have hcast : ((2 * m : ℕ) : ℝ) + 1 = 2 * m + 1 := by push_cast; ring
  have hintf' : Integrable (fun z => |X z - Yf z| ^ (2 * m)) stdNormalSeq := by
    simp_rw [hN.pow_abs]
    exact hintf
  have hintc' : Integrable (fun z => |X z - Yc (pairAvg z)| ^ (2 * m)) stdNormalSeq := by
    simp_rw [hN.pow_abs, hXc]
    exact (measurePreserving_pairAvg.integrable_comp hintc.aestronglyMeasurable).2 hintc
  have hYc' : Measurable fun z => Yc (pairAvg z) := hYc.comp measurePreserving_pairAvg.measurable
  have h1 := (digital_mismatch_le_of_moment hXm hYf hball hintf').2
  have h2 := (digital_mismatch_le_of_moment hXm hYc' hball hintc').2
  rw [hcast] at h1 h2
  have e1 : ∫ z, |X z - Yf z| ^ (2 * m) ∂stdNormalSeq =
      ∫ z, (gbmExact r σ T s₀ (ℓ + 1) z - Yf z) ^ (2 * m) ∂stdNormalSeq := by
    simp_rw [hN.pow_abs, hXdef]
  have e2 : ∫ z, |X z - Yc (pairAvg z)| ^ (2 * m) ∂stdNormalSeq =
      ∫ z, (gbmExact r σ T s₀ ℓ z - Yc z) ^ (2 * m) ∂stdNormalSeq := by
    simp_rw [hN.pow_abs, hXc]
    exact integral_comp_of_measurePreserving measurePreserving_pairAvg
      hintc.aestronglyMeasurable
  rw [e1] at h1
  rw [e2] at h2
  calc _ ≤ stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X z) ≠
          (Set.Ioi K).indicator 1 (Yf z)} +
        stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X z) ≠
          (Set.Ioi K).indicator 1 (Yc (pairAvg z))} :=
        (measureReal_mono (digital_ne_subset_union X _ _ K)).trans (measureReal_union_le _ _)
    _ ≤ _ := by rw [mul_add]; exact add_le_add h1 h2

/-- `0 ≤ W ≤ C hᵖ` gives `W^e ≤ C^e h^{pe}` for `C, h, e ≥ 0` (the exponent `m/(2m+1)` of the
digital option, Giles 2015, §5.1–§5.2). -/
lemma rpow_le_of_le_mul_pow {W C h : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) (hh : 0 ≤ h) {p : ℕ}
    {e : ℝ} (he : 0 ≤ e) (hle : W ≤ C * h ^ p) : W ^ e ≤ C ^ e * h ^ ((p : ℝ) * e) := by
  calc W ^ e ≤ (C * h ^ p) ^ e := Real.rpow_le_rpow hW hle he
    _ = C ^ e * (h ^ p) ^ e := Real.mul_rpow hC (pow_nonneg hh p)
    _ = C ^ e * h ^ ((p : ℝ) * e) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hh]

/-- `h_{ℓ+1}^a + h_ℓ^a ≤ T^{a−q} (1 + 2^q) h_{ℓ+1}^q` for `q ≤ a` and `h_ℓ = T 2^{−ℓ}`, `T > 0`
(from the level exponent `a` to any `q ≤ a`, Giles 2015, §5.1–§5.2). -/
lemma level_rpow_add_le {T : ℝ} (hT : 0 < T) {a q : ℝ} (hqa : q ≤ a) (ℓ : ℕ) :
    (T / 2 ^ (ℓ + 1)) ^ a + (T / 2 ^ ℓ) ^ a ≤
      T ^ (a - q) * (1 + 2 ^ q) * (T / 2 ^ (ℓ + 1)) ^ q := by
  set h' := T / 2 ^ (ℓ + 1) with hh'
  have hh'0 : 0 < h' := by positivity
  have hh'T : h' ≤ T := div_le_self hT.le (one_le_pow₀ (by norm_num))
  have hh : T / 2 ^ ℓ = 2 * h' := by rw [hh', pow_succ]; field_simp
  have hhT : 2 * h' ≤ T := by rw [← hh]; exact div_le_self hT.le (one_le_pow₀ (by norm_num))
  have haq : 0 ≤ a - q := sub_nonneg.2 hqa
  have h1 : h' ^ a ≤ h' ^ q * T ^ (a - q) := by
    rw [show a = q + (a - q) by ring, Real.rpow_add hh'0, add_sub_cancel_left]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh'0.le hh'T haq)
      (Real.rpow_nonneg hh'0.le _)
  have h2 : (2 * h') ^ a ≤ 2 ^ q * h' ^ q * T ^ (a - q) := by
    have h20 : 0 < 2 * h' := by positivity
    rw [show a = q + (a - q) by ring, Real.rpow_add h20, add_sub_cancel_left,
      Real.mul_rpow (by norm_num) hh'0.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h20.le hhT haq)
      (by positivity)
  rw [hh]
  nlinarith [h1, h2]

/-- **The digital option with Euler–Maruyama from the `2m`-th moments: `V_ℓ = O(h_ℓ^{m/(2m+1)})`**
(Giles 2015, §5.1, p. 33, l. 1436–1441: "there is therefore an `O(h_ℓ^{1/2})` fraction of the
samples with the coarse and fine paths on either side of the strike, with `P_ℓ − P_{ℓ−1} = ±1`.
This gives `V_ℓ = O(h^{1/2})`").  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, `m ≥ 1` and the correction
`D = H(Ŝ^f_{ℓ+1} − K) − H(Ŝ^c_ℓ − K)` of the digital payoff (the coarse path driven by the summed
increments, as in `gbm_digital_variance_le`),
`V[D] ≤ P(D ≠ 0) ≤ (2ρ + 1) C_m(T)^{1/(2m+1)} (h_{ℓ+1}^{m/(2m+1)} + h_ℓ^{m/(2m+1)})`, where
`h_ℓ = T 2^{−ℓ}`, `C_m = gbmEMMomentConst` and `ρ = e^{(σ²−r)T}/(√(2π) |s₀| |σ| √T)` is the
maximum of the lognormal density of `S_T`.  The exponent `m/(2m+1)` (`1/3` for the mean-square
error, `2/5` for the fourth moment) increases to the paper's `½` as `m → ∞`
(`gbm_em_digital_rate`). -/
theorem gbm_em_digital_variance_le_moment (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) {m : ℕ} (hm : 0 < m) (ℓ : ℕ) :
    variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ∧
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ≤
      (2 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1) *
        gbmEMMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
        ((T / 2 ^ (ℓ + 1)) ^ ((m : ℝ) / (2 * m + 1)) + (T / 2 ^ ℓ) ^ ((m : ℝ) / (2 * m + 1))) := by
  have hm1 := measurable_gbmEM r σ T s₀ (ℓ + 1)
  have hm0 := measurable_gbmEM r σ T s₀ ℓ
  refine ⟨variance_digital_le_measureReal hm1 (hm0.comp measurePreserving_pairAvg.measurable) K,
    ?_⟩
  have hh1 : 0 ≤ T / 2 ^ (ℓ + 1) := by positivity
  have hh0 : 0 ≤ T / 2 ^ ℓ := by positivity
  have h := gbm_digital_mismatch_le_of_moment r σ hs₀ hσ hT K ℓ hm1 hm0
    (integrable_gbm_em_err_pow r σ T s₀ hh1 m) (integrable_gbm_em_err_pow r σ T s₀ hh0 m)
  have hC := gbmEMMomentConst_nonneg m r σ s₀ hT.le
  have he : (0 : ℝ) ≤ 1 / (2 * m + 1) := by positivity
  have hpe : (m : ℝ) * (1 / (2 * m + 1)) = (m : ℝ) / (2 * m + 1) := mul_one_div _ _
  have hf := rpow_le_of_le_mul_pow (integral_nonneg fun z => (even_two_mul m).pow_nonneg _)
    hC hh1 he (gbm_em_moment_error_level r σ s₀ hT.le (ℓ + 1) hm)
  have hc := rpow_le_of_le_mul_pow (integral_nonneg fun z => (even_two_mul m).pow_nonneg _)
    hC hh0 he (gbm_em_moment_error_level r σ s₀ hT.le ℓ hm)
  rw [hpe] at hf hc
  refine h.trans ?_
  have hρ : 0 ≤ 2 * (Real.exp ((σ ^ 2 - r) * T) /
      (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1 := by positivity
  have hsum := add_le_add hf hc
  rw [← mul_add] at hsum
  calc _ ≤ (2 * (Real.exp ((σ ^ 2 - r) * T) /
        (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1) *
        (gbmEMMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
          ((T / 2 ^ (ℓ + 1)) ^ ((m : ℝ) / (2 * m + 1)) +
            (T / 2 ^ ℓ) ^ ((m : ℝ) / (2 * m + 1)))) := mul_le_mul_of_nonneg_left hsum hρ
    _ = _ := by ring

/-- **The natural Milstein estimator of the digital option from the `2m`-th moments:
`V_ℓ = O(h_ℓ^{2m/(2m+1)})`** (Giles 2015, §5.2, p. 35, l. 1529–1531: "In the case of a digital
option, if we use the natural multilevel estimator then `P_ℓ−P_{ℓ−1} = O(1)` for an `O(h_ℓ)`
fraction of the paths, giving `V_ℓ = O(h_ℓ)`").  With the notation of
`gbm_em_digital_variance_le_moment` and the Milstein paths (as in `gbm_mil_digital_variance_le`),
`V[D] ≤ P(D ≠ 0) ≤ (2ρ + 1) C_m(T)^{1/(2m+1)} (h_{ℓ+1}^{2m/(2m+1)} + h_ℓ^{2m/(2m+1)})` with
`C_m = gbmMilMomentConst`.  The exponent `2m/(2m+1)` increases to the paper's `1` as `m → ∞`
(`gbm_mil_digital_rate`). -/
theorem gbm_mil_digital_variance_le_moment (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) {m : ℕ} (hm : 0 < m) (ℓ : ℕ) :
    variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} ∧
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} ≤
      (2 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1) *
        gbmMilMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
        ((T / 2 ^ (ℓ + 1)) ^ (2 * (m : ℝ) / (2 * m + 1)) +
          (T / 2 ^ ℓ) ^ (2 * (m : ℝ) / (2 * m + 1))) := by
  have hm1 := measurable_gbmMil r σ T s₀ (ℓ + 1)
  have hm0 := measurable_gbmMil r σ T s₀ ℓ
  refine ⟨variance_digital_le_measureReal hm1 (hm0.comp measurePreserving_pairAvg.measurable) K,
    ?_⟩
  have hh1 : 0 ≤ T / 2 ^ (ℓ + 1) := by positivity
  have hh0 : 0 ≤ T / 2 ^ ℓ := by positivity
  have h := gbm_digital_mismatch_le_of_moment r σ hs₀ hσ hT K ℓ hm1 hm0
    (integrable_gbm_mil_err_pow r σ T s₀ hh1 m) (integrable_gbm_mil_err_pow r σ T s₀ hh0 m)
  have hC := gbmMilMomentConst_nonneg m r σ s₀ hT.le
  have he : (0 : ℝ) ≤ 1 / (2 * m + 1) := by positivity
  have hpe : ((2 * m : ℕ) : ℝ) * (1 / (2 * m + 1)) = 2 * (m : ℝ) / (2 * m + 1) := by
    push_cast
    exact mul_one_div _ _
  have hf := rpow_le_of_le_mul_pow (integral_nonneg fun z => (even_two_mul m).pow_nonneg _)
    hC hh1 he (gbm_mil_moment_error_level r σ s₀ hT.le (ℓ + 1) hm)
  have hc := rpow_le_of_le_mul_pow (integral_nonneg fun z => (even_two_mul m).pow_nonneg _)
    hC hh0 he (gbm_mil_moment_error_level r σ s₀ hT.le ℓ hm)
  rw [hpe] at hf hc
  refine h.trans ?_
  have hρ : 0 ≤ 2 * (Real.exp ((σ ^ 2 - r) * T) /
      (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1 := by positivity
  have hsum := add_le_add hf hc
  rw [← mul_add] at hsum
  calc _ ≤ (2 * (Real.exp ((σ ^ 2 - r) * T) /
        (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1) *
        (gbmMilMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
          ((T / 2 ^ (ℓ + 1)) ^ (2 * (m : ℝ) / (2 * m + 1)) +
            (T / 2 ^ ℓ) ^ (2 * (m : ℝ) / (2 * m + 1)))) := mul_le_mul_of_nonneg_left hsum hρ
    _ = _ := by ring

/-- **The digital option with Euler–Maruyama from the fourth moments: `V_ℓ` and
`E[(P_ℓ − P_{ℓ−1})⁴]` are `O(h^{2/5})`** (Giles 2015, §5.1, p. 33, l. 1441–1446: "This gives
`V_ℓ = O(h^{1/2})` … Furthermore, `E[(P_ℓ−P_{ℓ−1})⁴] = O(h_ℓ^{1/2})` and so the kurtosis is
`O(h_ℓ^{−1/2})`").  With the notation of `gbm_em_digital_variance_le_moment` and `m = 2`:
* `V[D] ≤ P(D ≠ 0)` and `E[D⁴] = P(D ≠ 0)` (`D` takes values in `{−1, 0, 1}`),
* `P(D ≠ 0) ≤ B_ℓ = (2ρ + 1) C₂(T)^{1/5} (h_{ℓ+1}^{2/5} + h_ℓ^{2/5})`,
* if `P(D ≠ 0) > 0`, the kurtosis `κ = E[D⁴]/E[D²]²` (`kurtosis`) is at least `B_ℓ⁻¹`.

This improves the exponent `1/3` of `gbm_em_digital_fourth_moment_le` (from the mean-square error)
to `2/5`; every exponent below the paper's `½` is `gbm_em_digital_rate`.  As in
`gbm_em_digital_fourth_moment_le`, `κ` is the raw-moment kurtosis, and the paper's
`κ = O(h^{−1/2})` (an upper bound) needs a lower bound on `P(D ≠ 0)`, which is not proved. -/
theorem gbm_em_digital_fourth_moment_le_of_four (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) (K : ℝ) (ℓ : ℕ) :
    variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ∧
    ∫ z, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 4 ∂stdNormalSeq =
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ∧
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ≤
      (2 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1) *
        gbmEMMomentConst 2 r σ T s₀ ^ (1 / 5 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (2 / 5 : ℝ) + (T / 2 ^ ℓ) ^ (2 / 5 : ℝ)) ∧
    (0 < stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} →
      ((2 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1) *
        gbmEMMomentConst 2 r σ T s₀ ^ (1 / 5 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (2 / 5 : ℝ) + (T / 2 ^ ℓ) ^ (2 / 5 : ℝ)))⁻¹ ≤
      kurtosis (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq) := by
  have hm1 := measurable_gbmEM r σ T s₀ (ℓ + 1)
  have hm0 := (measurable_gbmEM r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable
  obtain ⟨hv, hP⟩ := gbm_em_digital_variance_le_moment r σ hs₀ hσ hT K two_pos ℓ
  have e1 : (1 / (2 * ((2 : ℕ) : ℝ) + 1)) = (1 / 5 : ℝ) := by norm_num
  have e2 : ((2 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ) + 1) = (2 / 5 : ℝ) := by norm_num
  rw [e1, e2] at hP
  exact ⟨hv, integral_pow_four_digital_sub hm1 hm0 K, hP,
    fun h => inv_le_kurtosis_digital hm1 hm0 K h hP⟩

/-- **The natural Milstein estimator of the digital option from the fourth moments: `V_ℓ` and
`E[(P_ℓ − P_{ℓ−1})⁴]` are `O(h^{4/5})`** (Giles 2015, §5.2, p. 35, l. 1529–1532: "if we use the
natural multilevel estimator then `P_ℓ−P_{ℓ−1} = O(1)` for an `O(h_ℓ)` fraction of the paths,
giving `V_ℓ = O(h_ℓ)`, and a kurtosis which is `O(h_ℓ^{−1})`").  With the notation of
`gbm_mil_digital_variance_le_moment` and `m = 2`: `V[D] ≤ P(D ≠ 0)`, `E[D⁴] = P(D ≠ 0)`,
`P(D ≠ 0) ≤ B_ℓ = (2ρ + 1) C₂(T)^{1/5} (h_{ℓ+1}^{4/5} + h_ℓ^{4/5})`, and `κ ≥ B_ℓ⁻¹` if
`P(D ≠ 0) > 0`.  This improves the exponent `2/3` of `gbm_mil_digital_fourth_moment_le` to `4/5`;
every exponent below the paper's `1` is `gbm_mil_digital_rate`.  The kurtosis bound is a lower
bound; the paper's `O(h_ℓ^{−1})` needs a lower bound on `P(D ≠ 0)`, not proved. -/
theorem gbm_mil_digital_fourth_moment_le_of_four (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) (K : ℝ) (ℓ : ℕ) :
    variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} ∧
    ∫ z, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) ^ 4 ∂stdNormalSeq =
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} ∧
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} ≤
      (2 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1) *
        gbmMilMomentConst 2 r σ T s₀ ^ (1 / 5 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (4 / 5 : ℝ) + (T / 2 ^ ℓ) ^ (4 / 5 : ℝ)) ∧
    (0 < stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} →
      ((2 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) + 1) *
        gbmMilMomentConst 2 r σ T s₀ ^ (1 / 5 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (4 / 5 : ℝ) + (T / 2 ^ ℓ) ^ (4 / 5 : ℝ)))⁻¹ ≤
      kurtosis (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) stdNormalSeq) := by
  have hm1 := measurable_gbmMil r σ T s₀ (ℓ + 1)
  have hm0 := (measurable_gbmMil r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable
  obtain ⟨hv, hP⟩ := gbm_mil_digital_variance_le_moment r σ hs₀ hσ hT K two_pos ℓ
  have e1 : (1 / (2 * ((2 : ℕ) : ℝ) + 1)) = (1 / 5 : ℝ) := by norm_num
  have e2 : 2 * ((2 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ) + 1) = (4 / 5 : ℝ) := by norm_num
  rw [e1, e2] at hP
  exact ⟨hv, integral_pow_four_digital_sub hm1 hm0 K, hP,
    fun h => inv_le_kurtosis_digital hm1 hm0 K h hP⟩

/-- **The digital option with Euler–Maruyama: `V_ℓ = O(h_ℓ^q)` for every `q < ½`** (Giles 2015,
§5.1, p. 33, l. 1436–1446: "there is therefore an `O(h_ℓ^{1/2})` fraction of the samples with the
coarse and fine paths on either side of the strike … This gives `V_ℓ = O(h^{1/2})` … Furthermore,
`E[(P_ℓ−P_{ℓ−1})⁴] = O(h_ℓ^{1/2})` and so the kurtosis is `O(h_ℓ^{−1/2})`"; Table 5.2, l. 1431:
digital option, Euler–Maruyama, numerics `O(h^{1/2})`, analysis `O(h^{1/2} log h)`).  For `s₀ ≠ 0`,
`σ ≠ 0`, `T > 0`, every strike `K` and every `q < ½` there is `C ≥ 0` such that on every level the
correction `D_ℓ = H(Ŝ^f_{ℓ+1} − K) − H(Ŝ^c_ℓ − K)` satisfies `V[D_ℓ] ≤ C h_{ℓ+1}^q`,
`E[D_ℓ⁴] ≤ C h_{ℓ+1}^q`, and, if `P(D_ℓ ≠ 0) > 0`, `kurtosis(D_ℓ) ≥ (C h_{ℓ+1}^q)⁻¹`
(`h_ℓ = T 2^{−ℓ}`).  Proof: `gbm_em_digital_variance_le_moment` with `m` so large that
`m/(2m+1) ≥ q`.

**How close to the paper.**  These are the paper's rates `V_ℓ = O(h^{1/2})` and
`E[(P_ℓ − P_{ℓ−1})⁴] = O(h^{1/2})` up to an arbitrarily small loss in the exponent; the endpoint
`q = ½` (and Avikainen's `O(h^{1/2} log h)` of Table 5.2) is not proved: moment bounds of the
strong error give only exponents below `½`.  The kurtosis statement is a lower bound; the paper's
upper bound `O(h^{−1/2})` needs a lower bound on `P(D_ℓ ≠ 0)`, which is not proved. -/
theorem gbm_em_digital_rate (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) {q : ℝ} (hq : q < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
        C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      ∫ z, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 4 ∂stdNormalSeq ≤
        C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      (0 < stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} →
        (C * (T / 2 ^ (ℓ + 1)) ^ q)⁻¹ ≤
          kurtosis (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
            (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (q / (1 - 2 * q))
  have h12 : 0 < 1 - 2 * q := by linarith
  have hqn : q < n * (1 - 2 * q) := by rwa [div_lt_iff₀ h12] at hn
  set m := n + 1 with hmdef
  have hm : 0 < m := Nat.succ_pos n
  have hmc : (m : ℝ) = n + 1 := by rw [hmdef]; push_cast; ring
  have hqa : q ≤ (m : ℝ) / (2 * m + 1) := by
    rw [le_div_iff₀ (by positivity), hmc]
    nlinarith
  set a := (m : ℝ) / (2 * m + 1) with ha
  set ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)
    with hρ
  set C := (2 * ρ + 1) * gbmEMMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
    (T ^ (a - q) * (1 + 2 ^ q)) with hCdef
  have hC0 : 0 ≤ C := by
    have := gbmEMMomentConst_nonneg m r σ s₀ hT.le
    positivity
  refine ⟨C, hC0, fun ℓ => ?_⟩
  have hm1 := measurable_gbmEM r σ T s₀ (ℓ + 1)
  have hm0 := (measurable_gbmEM r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable
  obtain ⟨hv, hP⟩ := gbm_em_digital_variance_le_moment r σ hs₀ hσ hT K hm ℓ
  have hlev := level_rpow_add_le hT hqa ℓ
  have hK : 0 ≤ (2 * ρ + 1) * gbmEMMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) := by
    have := gbmEMMomentConst_nonneg m r σ s₀ hT.le
    positivity
  have hP' : stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (gbmEM r σ T s₀ (ℓ + 1) z) ≠ (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ≤
      C * (T / 2 ^ (ℓ + 1)) ^ q := by
    refine hP.trans ?_
    calc (2 * ρ + 1) * gbmEMMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
          ((T / 2 ^ (ℓ + 1)) ^ a + (T / 2 ^ ℓ) ^ a)
        ≤ (2 * ρ + 1) * gbmEMMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
          (T ^ (a - q) * (1 + 2 ^ q) * (T / 2 ^ (ℓ + 1)) ^ q) :=
          mul_le_mul_of_nonneg_left hlev hK
      _ = C * (T / 2 ^ (ℓ + 1)) ^ q := by rw [hCdef]; ring
  exact ⟨hv.trans hP', (integral_pow_four_digital_sub hm1 hm0 K).trans_le hP',
    fun h => inv_le_kurtosis_digital hm1 hm0 K h hP'⟩

/-- **The natural Milstein estimator of the digital option: `V_ℓ = O(h_ℓ^q)` for every `q < 1`**
(Giles 2015, §5.2, p. 35, l. 1529–1532: "if we use the natural multilevel estimator then
`P_ℓ−P_{ℓ−1} = O(1)` for an `O(h_ℓ)` fraction of the paths, giving `V_ℓ = O(h_ℓ)`, and a kurtosis
which is `O(h_ℓ^{−1})`").  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, every strike `K` and every `q < 1` there
is `C ≥ 0` such that on every level the Milstein correction `D_ℓ` (as in
`gbm_mil_digital_variance_le`) satisfies `V[D_ℓ] ≤ C h_{ℓ+1}^q`, `E[D_ℓ⁴] ≤ C h_{ℓ+1}^q`, and, if
`P(D_ℓ ≠ 0) > 0`, `kurtosis(D_ℓ) ≥ (C h_{ℓ+1}^q)⁻¹`.  Proof: `gbm_mil_digital_variance_le_moment`
with `m` so large that `2m/(2m+1) ≥ q`.

**How close to the paper.**  This is the paper's `V_ℓ = O(h_ℓ)` for the natural estimator up to an
arbitrarily small loss in the exponent; `q = 1` itself is not proved.  The Milstein row of
Table 5.2 (`O(h^{3/2})`) is for the improved estimators of §5.2 (conditional expectation,
splitting, change of measure), not for the natural one.  The kurtosis statement is a lower bound;
the paper's `O(h_ℓ^{−1})` needs a lower bound on `P(D_ℓ ≠ 0)`, not proved. -/
theorem gbm_mil_digital_rate (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) {q : ℝ} (hq : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
          (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
        C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      ∫ z, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
          (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) ^ 4 ∂stdNormalSeq ≤
        C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      (0 < stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
          (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} →
        (C * (T / 2 ^ (ℓ + 1)) ^ q)⁻¹ ≤
          kurtosis (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
            (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) stdNormalSeq) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (q / (2 * (1 - q)))
  have h12 : 0 < 2 * (1 - q) := by linarith
  have hqn : q < n * (2 * (1 - q)) := by rwa [div_lt_iff₀ h12] at hn
  set m := n + 1 with hmdef
  have hm : 0 < m := Nat.succ_pos n
  have hmc : (m : ℝ) = n + 1 := by rw [hmdef]; push_cast; ring
  have hqa : q ≤ 2 * (m : ℝ) / (2 * m + 1) := by
    rw [le_div_iff₀ (by positivity), hmc]
    nlinarith
  set a := 2 * (m : ℝ) / (2 * m + 1) with ha
  set ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)
    with hρ
  set C := (2 * ρ + 1) * gbmMilMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
    (T ^ (a - q) * (1 + 2 ^ q)) with hCdef
  have hC0 : 0 ≤ C := by
    have := gbmMilMomentConst_nonneg m r σ s₀ hT.le
    positivity
  refine ⟨C, hC0, fun ℓ => ?_⟩
  have hm1 := measurable_gbmMil r σ T s₀ (ℓ + 1)
  have hm0 := (measurable_gbmMil r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable
  obtain ⟨hv, hP⟩ := gbm_mil_digital_variance_le_moment r σ hs₀ hσ hT K hm ℓ
  have hlev := level_rpow_add_le hT hqa ℓ
  have hK : 0 ≤ (2 * ρ + 1) * gbmMilMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) := by
    have := gbmMilMomentConst_nonneg m r σ s₀ hT.le
    positivity
  have hP' : stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (gbmMil r σ T s₀ (ℓ + 1) z) ≠ (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} ≤
      C * (T / 2 ^ (ℓ + 1)) ^ q := by
    refine hP.trans ?_
    calc (2 * ρ + 1) * gbmMilMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
          ((T / 2 ^ (ℓ + 1)) ^ a + (T / 2 ^ ℓ) ^ a)
        ≤ (2 * ρ + 1) * gbmMilMomentConst m r σ T s₀ ^ (1 / (2 * m + 1 : ℝ)) *
          (T ^ (a - q) * (1 + 2 ^ q) * (T / 2 ^ (ℓ + 1)) ^ q) :=
          mul_le_mul_of_nonneg_left hlev hK
      _ = C * (T / 2 ^ (ℓ + 1)) ^ q := by rw [hCdef]; ring
  exact ⟨hv.trans hP', (integral_pow_four_digital_sub hm1 hm0 K).trans_le hP',
    fun h => inv_le_kurtosis_digital hm1 hm0 K h hP'⟩

end MLMC
