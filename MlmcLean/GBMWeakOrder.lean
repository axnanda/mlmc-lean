import MlmcLean.GBMStrongLp
import MlmcLean.EndToEndInstances

/-!
# Weak order one of the Euler–Maruyama scheme for geometric Brownian motion (Giles 2015, §5.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1
"Euler-Maruyama discretisation", pp. 29–30 (p. 30, l. 1317–1320 of `docs/giles2015.txt`): "If
`h_ℓ = 4^{−ℓ}h_0`, as in the numerical examples in (Giles 2008b), then this gives `α = 2`, `β = 2`
and `γ = 2`. Alternatively, if `h_ℓ = 2^{−ℓ}h_0` with twice as many timesteps on each successive
level, as used in the numerical examples in this article, then `α = 1`, `β = 1` and `γ = 1`", and
the GBM example of Figure 5.3 (l. 1335–1336: "`log₂|E[P_ℓ − P_{ℓ−1}]|` also has a slope of
approximately `−1`, implying an `O(h_ℓ)` weak convergence").  The rate `α = 1` (`α = log₂ M`
for `h_ℓ = M^{−ℓ}h_0`) is the weak order one of the Euler–Maruyama scheme, which the paper takes
from the SDE literature.  `MlmcLean.GBMEulerMaruyama` proves only the rate `α = ½` that follows
from the strong error (`gbm_weak_error_le`, and `gbm_weak_error_le_M` in
`MlmcLean.EndToEndInstances`).  This file proves weak order one for GBM `dS = rS dt + σS dW`,
with the Euler–Maruyama path `Ŝ_n = S_0 ∏_{i<n} A_i`, `A_i = 1 + rh + σ√h Z_i`, and the exact
solution `S_{t_n} = S_0 ∏_{i<n} B_i`, `B_i = e^{(r − σ²/2)h + σ√h Z_i}`, driven by the same
independent `Z_i ∼ N(0,1)` (`stdNormalSeq`).

* **Exact moments.** `integral_emPath_gbm_pow`: `E[Ŝ_N^p] = S_0^p (E[(1 + rh + σ√h Z)^p])^N`;
  `integral_gbmExp_pow`, `integral_gbmExact_pow`: `E[S_T^p] = S_0^p e^{p(r + (p−1)σ²/2)T}`.
* **Monomial and polynomial payoffs.** `gbm_em_weak_error_pow`, `gbm_weak_error_pow`:
  `|E[Ŝ^p] − E[S_T^p]| ≤ C_p(T) h` with `C_p(T) = 2|S_0|^p Λ_p² T e^{Λ_p T}`, `Λ_p = p(|r| + pσ²)`
  (`gbmWeakPowConst`).  The one-step moments `a_p = E[A^p]` satisfy
  `a_{p+2} = (1 + rh) a_{p+1} + (p+1)σ²h a_p` (`integral_gbmEMFactor_pow_add_two`), from which
  `|a_p − 1 − (pr + p(p−1)σ²/2)h| ≤ Λ_p² h² e^{Λ_p h}` (`gbmEMFactor_moment_lin_le`), so
  `|a_p − E[B^p]| ≤ 2Λ_p² h² e^{Λ_p h}`.  `gbm_weak_error_poly`, `gbm_weak_error_poly_M`: the same
  for every polynomial payoff, with the constant `∑_k |c_k| C_k(T)`, for refinement factor `2` and
  for refinement factor `M` (`α = log₂ M`).
* **Smooth payoffs.** `gbm_em_weak_error_smooth`, `gbm_weak_error_smooth`: if `g` is four times
  differentiable with `|g^{(k)}| ≤ K` for `k = 1, …, 4`, then
  `|E[g(Ŝ)] − E[g(S_T)]| ≤ C(T) h` with `C(T) = 5KΛ²(1 + S_0⁴) T e^{ΛT}`, `Λ = 4|r| + 8σ²`
  (`gbmWeakSmoothConst`).  The proof is the standard telescoping argument with the explicit backward
  functions of GBM: `u_k = Q^k g`, `Q f(x) = E[f(xB)]` (`gbmBackOp`), so that
  `E[g(S_{t_n})] = u_n(S_0)` by independence (`integral_comp_gbmExp_prod_eq`,
  `integral_comp_mul_eval_eq`); the derivatives `u_k^{(j)} = Q_j^k g^{(j)}`,
  `Q_j f(x) = E[B^j f(xB)]`, are obtained by differentiating under the Gaussian integral
  (`hasDerivAt_gbmBackOp`, `gbmBackOp_iterate_chain`) and are bounded by `K e^{Λkh}`; one Euler step
  changes `E[u_k(·)]` by `|E[u(xA)] − E[u(xB)]| ≤ 5K'Λ²h²e^{Λh}(1 + x⁴)` (`gbm_one_step_weak_le`:
  third-order Taylor expansion with a fourth-order remainder, `abs_integral_taylor_four_le`; the
  first three moments of `A − 1` and `B − 1` agree up to `O(h²)` and their fourth moments are
  `O(h²)`, `gbm_step_moment_bounds`), and the steps are summed with `E[Ŝ_j⁴] ≤ S_0⁴ e^{Λjh}`.
* **Theorem 1 with the paper's rates.** `gbm_mlmc_theorem1_smooth_M`: for such `g`, refinement
  factor `M ≥ 2` and `h_0 = T/m`, Theorem 1 with `α = β = γ = log₂ M` (the paper's
  `α = β = γ = 2` for `h_ℓ = 4^{−ℓ}h_0`; `α` from `gbm_weak_error_smooth_M`, `β` from
  `gbm_correction_variance_le_M`, as `g` is `K`-Lipschitz); `gbm_mlmc_theorem1_smooth` is its case
  `m = 1`, `M = 2` (`α = β = γ = 1`).  `gbm_mlmc_theorem1_poly_M`, `gbm_mlmc_theorem1_poly`: the
  same for every polynomial payoff `q` (not Lipschitz in general), with `β` from
  `gbm_poly_correction_variance_le_M` (and `gbm_poly_correction_variance_le` for `M = 2`): by
  `|q(x) − q(y)| ≤ c_q |x − y| (1 + |x| + |y|)^d` (`abs_eval_sub_eval_le`) and
  `ab ≤ a²/(2h) + hb²/2`, `E[(q(S_{t_n}) − q(Ŝ_n))²] = O(h)` from the fourth moment of the strong
  error (`gbm_em_moment_error`) and the moments of `Ŝ_n`, `S_{t_n}` of order `4d`
  (`integral_sq_poly_gbm_em_err_le`).  Besides the paper's conclusions (square-integrable error
  with mean square `< ε²`, cost `O(ε⁻²(log ε)²)`), the four Theorem 1 statements bound the finest
  level, `M^L ≤ c₅ ε⁻¹` (`2^L ≤ c₅ ε⁻¹` for `M = 2`): the paper's `C_L = O(ε^{−γ/α})` (p. 7,
  l. 326) with `γ/α = 1`.  This conclusion is where the weak rate shows; it comes from
  `giles_theorem1_fineCoarse_levels`, Theorem 1 for fine and coarse approximations with the bound
  `2^{αL} ≤ K/ε` of its construction kept.

**Deviations and scope.**  The smooth-payoff results assume four bounded derivatives (one more than
needed for the expansion, to bound its remainder); the paper's call option (Figure 5.3) and digital
option are not smooth, and their weak order one (Bally–Talay, via the smoothing of the law of `S_T`)
is not proved here.  For smooth payoffs the cost and mean-square-error conclusions of Theorem 1 are
already those of `gbm_mlmc_theorem1` and `gbm_mlmc_theorem1_M` (every Lipschitz payoff, weaker
`α = ½ log₂ M`): with `β = γ` the complexity does not depend on `α`.  What the weak rate adds is
the bound on the finest level, `M^L = O(ε⁻¹)` instead of `O(ε⁻²)`.  The polynomial Theorem 1
statements are new also in their other conclusions (polynomial payoffs are not Lipschitz).  The
constants are explicit but far from sharp: checked numerically (trapezoidal Gaussian quadrature,
`1104` one-step and `432` end-to-end checks with `n ≤ 2`, payoffs `sin`, `cos(3x)/81`, softplus,
`arctan`) the bound exceeds the true error by a factor of at least `400`; the monomial bound was
checked against the exact moments (`5292` cases, `p ≤ 8`, `n ≤ 256`), with ratio at most `0.25`.
The smooth-payoff constant is not scale invariant, as the hypothesis bounds `g^{(k)}` uniformly: for
a payoff `g(x) = G(x/S_0)` the true error does not depend on `S_0`, while the constant grows like
`S_0³` as `S_0 → ∞` and like `S_0^{−4}` as `S_0 → 0` (a hypothesis `|x^k g^{(k)}(x)| ≤ K` would
remove this; it is not pursued here).
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### Exact moments -/

/-- **The moments of the Euler–Maruyama approximation of GBM** (Giles 2015, §5.1, p. 29, l. 1280:
`Ŝ_{n+1} = Ŝ_n + a(Ŝ_n, t_n)h + b(Ŝ_n, t_n)ΔW_n` with `a(S, t) = rS`, `b(S, t) = σS`).  For every
`p, N ∈ ℕ`, `E[Ŝ_N^p] = S_0^p (E[(1 + rh + σ√h Z)^p])^N`, `Z ∼ N(0,1)`: `Ŝ_N` is `S_0` times a
product of `N` independent copies of the one-step factor. -/
theorem integral_emPath_gbm_pow (r σ h s₀ : ℝ) (N p : ℕ) :
    ∫ z, emPath (gbmDrift r) (gbmVol σ) h s₀ z N ^ p ∂stdNormalSeq =
      s₀ ^ p * (∫ x, gbmEMFactor r σ h x ^ p ∂gaussianReal 0 1) ^ N := by
  simp_rw [emPath_gbm, mul_pow, ← Finset.prod_pow]
  rw [integral_const_mul, integral_prod_stdNormalSeq (F := fun x => gbmEMFactor r σ h x ^ p)
    ((measurable_gbmEMFactor r σ h).pow_const p)]

/-- `E[B^p] = e^{(pr + p(p−1)σ²/2)h}` for the exact GBM step `B = e^{(r − σ²/2)h + σ√h Z}`,
`h ≥ 0` (Giles 2015, §5.1, GBM example). -/
lemma integral_gbmExpFactor_pow_eq (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (p : ℕ) :
    ∫ x, gbmExpFactor r σ h x ^ p ∂gaussianReal 0 1 =
      Real.exp ((p * r + p * (p - 1) * σ ^ 2 / 2) * h) := by
  rw [integral_gbmExpFactor_pow, mul_pow, mul_pow, Real.sq_sqrt hh]
  congr 1
  ring

/-- **The moments of the exact GBM solution on the grid** (Giles 2015, §5.1, p. 30,
l. 1326–1328: "a financial call option with a single underlying asset satisfying Geometric Brownian
Motion SDE, `dS_t = rS_t dt + σS_t dW`").  The paper gives only the SDE; its solution
`S_t = S_0 e^{(r − σ²/2)t + σW_t}` is the standard explicit one.  For `h ≥ 0` and `t_n = nh`,
`E[S_{t_n}^p] = S_0^p e^{p(r + (p−1)σ²/2) t_n}`, with `W_{t_n} = √h ∑_{i<n} Z_i`. -/
theorem integral_gbmExp_pow (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n p : ℕ) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
        σ * (Real.sqrt h * ∑ i ∈ range n, z i))) ^ p ∂stdNormalSeq =
      s₀ ^ p * Real.exp (p * (r + (p - 1) * σ ^ 2 / 2) * (n * h)) := by
  simp_rw [gbmExp_eq_prod, mul_pow, ← Finset.prod_pow]
  rw [integral_const_mul, integral_prod_stdNormalSeq (F := fun x => gbmExpFactor r σ h x ^ p)
    ((measurable_gbmExpFactor r σ h).pow_const p), integral_gbmExpFactor_pow_eq r σ hh,
    ← Real.exp_nat_mul]
  congr 2
  ring

/-- **The moments of `S_T`** (Giles 2015, §5.1, p. 30, l. 1326–1328: "a single underlying asset
satisfying Geometric Brownian Motion SDE, `dS_t = rS_t dt + σS_t dW`"; the closed form
`S_T = S_0 e^{(r − σ²/2)T + σW_T}` is the standard explicit solution, not the paper's text): for
`T ≥ 0`, every level `ℓ` and `p ∈ ℕ`, the exact solution `S_T` driven by the level-`ℓ` increments
(`gbmExact`) has `E[S_T^p] = S_0^p e^{p(r + (p−1)σ²/2)T}`. -/
theorem integral_gbmExact_pow (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ p : ℕ) :
    ∫ z, gbmExact r σ T s₀ ℓ z ^ p ∂stdNormalSeq =
      s₀ ^ p * Real.exp (p * (r + (p - 1) * σ ^ 2 / 2) * T) := by
  have h := integral_gbmExp_pow r σ s₀ (div_nonneg hT (by positivity : (0 : ℝ) ≤ 2 ^ ℓ))
    (2 ^ ℓ) p
  rw [cast_two_pow_mul_div] at h
  exact h

/-! ### Monomial and polynomial payoffs -/

/-- The moment recursion of the Euler–Maruyama step `A = 1 + rh + σ√h Z` of GBM (Giles 2015,
§5.1): `E[A^{q+2}] = (1 + rh) E[A^{q+1}] + (q+1)σ²h E[A^q]` for `h ≥ 0` (Gaussian integration by
parts, `integral_affine_pow_add_two`). -/
lemma integral_gbmEMFactor_pow_add_two (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (q : ℕ) :
    ∫ x, gbmEMFactor r σ h x ^ (q + 2) ∂gaussianReal 0 1 =
      (1 + r * h) * ∫ x, gbmEMFactor r σ h x ^ (q + 1) ∂gaussianReal 0 1 +
        (q + 1) * (σ ^ 2 * h) * ∫ x, gbmEMFactor r σ h x ^ q ∂gaussianReal 0 1 := by
  have e := integral_affine_pow_add_two (1 + r * h) (σ * Real.sqrt h) q
  rw [mul_pow, Real.sq_sqrt hh] at e
  exact e

/-- `E[A] = 1 + rh` for the Euler–Maruyama step of GBM (Giles 2015, §5.1). -/
lemma integral_gbmEMFactor_pow_one (r σ h : ℝ) :
    ∫ x, gbmEMFactor r σ h x ^ 1 ∂gaussianReal 0 1 = 1 + r * h :=
  integral_affine_pow_one (1 + r * h) (σ * Real.sqrt h)

/-- The exponential rates of the GBM moments are bounded: `|qr + q(q−1)σ²/2| ≤ P(|r| + Pσ²)` for
`q ≤ P` (the rate `E[S_t^q] = S_0^q e^{(qr + q(q−1)σ²/2)t}`, Giles 2015, §5.1). -/
lemma abs_gbmMomentRate_le (r σ : ℝ) {q P : ℕ} (hq : q ≤ P) :
    |(q : ℝ) * r + q * (q - 1) * σ ^ 2 / 2| ≤ P * (|r| + P * σ ^ 2) := by
  have hqP : (q : ℝ) ≤ P := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqq : 0 ≤ (q : ℝ) * (q - 1) := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · simp [h0]
    · have : (1 : ℝ) ≤ q := by exact_mod_cast h0
      nlinarith
  have hs : 0 ≤ σ ^ 2 := sq_nonneg σ
  have e1 : |(q : ℝ) * r| ≤ P * |r| := by
    rw [abs_mul, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_right hqP (abs_nonneg r)
  have e2 : |(q : ℝ) * (q - 1) * σ ^ 2 / 2| ≤ P * (P * σ ^ 2) := by
    rw [abs_of_nonneg (by positivity)]
    have : (q : ℝ) * (q - 1) ≤ P * P := by nlinarith
    nlinarith
  calc _ ≤ |(q : ℝ) * r| + |(q : ℝ) * (q - 1) * σ ^ 2 / 2| := abs_add_le _ _
    _ ≤ P * |r| + P * (P * σ ^ 2) := add_le_add e1 e2
    _ = _ := by ring

/-- **The moments of the Euler–Maruyama step to first order** (Giles 2015, §5.1).  For `h ≥ 0`,
`P ∈ ℕ` and `q ≤ P`,
`|E[A^q] − 1 − (qr + q(q−1)σ²/2)h| ≤ h² q (|r| + Pσ²) Λ_P (1 + (|r| + Pσ²)h)^q` with
`Λ_P = P(|r| + Pσ²)`: the first-order terms are those of `E[B^q] = e^{(qr + q(q−1)σ²/2)h}`.
Proof by two-step induction with the recursion `integral_gbmEMFactor_pow_add_two`. -/
lemma gbmEMFactor_moment_lin_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (P : ℕ) :
    ∀ q ≤ P, |∫ x, gbmEMFactor r σ h x ^ q ∂gaussianReal 0 1 - 1 -
        ((q : ℝ) * r + q * (q - 1) * σ ^ 2 / 2) * h| ≤
      h ^ 2 * q * ((|r| + P * σ ^ 2) * (P * (|r| + P * σ ^ 2))) *
        (1 + (|r| + P * σ ^ 2) * h) ^ q := by
  have hν : 0 ≤ |r| + P * σ ^ 2 := by positivity
  have hρ : 1 ≤ 1 + (|r| + P * σ ^ 2) * h := le_add_of_nonneg_right (mul_nonneg hν hh)
  intro q hq
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  match q, hq, ih with
  | 0, _, _ => simp
  | 1, _, _ =>
    rw [integral_gbmEMFactor_pow_one]
    simp only [Nat.cast_one, one_mul, sub_self, mul_zero, zero_mul, zero_div, add_zero, pow_one]
    rw [show 1 + r * h - 1 - r * h = 0 by ring, abs_zero]
    positivity
  | q + 2, hq, ih =>
    have h0 := ih q (by omega) (by omega)
    have h1 := ih (q + 1) (by omega) (by omega)
    set ν : ℝ := |r| + P * σ ^ 2 with hνdef
    set Λ : ℝ := P * ν with hΛdef
    set ρ : ℝ := 1 + ν * h with hρdef
    set M0 := ∫ x, gbmEMFactor r σ h x ^ q ∂gaussianReal 0 1 with hM0
    set M1 := ∫ x, gbmEMFactor r σ h x ^ (q + 1) ∂gaussianReal 0 1 with hM1
    rw [integral_gbmEMFactor_pow_add_two r σ hh q, ← hM0, ← hM1]
    set c0 : ℝ := (q : ℝ) * r + q * (q - 1) * σ ^ 2 / 2 with hc0
    set c1 : ℝ := ((q + 1 : ℕ) : ℝ) * r + ((q + 1 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) - 1) * σ ^ 2 / 2
      with hc1
    have hc0b : |c0| ≤ Λ := abs_gbmMomentRate_le r σ (by omega)
    have hc1b : |c1| ≤ Λ := abs_gbmMomentRate_le r σ (by omega)
    have hqP : (q : ℝ) + 2 ≤ P := by exact_mod_cast hq
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hs : 0 ≤ σ ^ 2 := sq_nonneg σ
    have key : (1 + r * h) * M1 + (q + 1) * (σ ^ 2 * h) * M0 - 1 -
        (((q + 2 : ℕ) : ℝ) * r + ((q + 2 : ℕ) : ℝ) * (((q + 2 : ℕ) : ℝ) - 1) * σ ^ 2 / 2) * h =
        (1 + r * h) * (M1 - 1 - c1 * h) + ((q + 1) * (σ ^ 2 * h)) * (M0 - 1 - c0 * h) +
          h ^ 2 * (r * c1 + (q + 1) * σ ^ 2 * c0) := by
      rw [hc0, hc1]
      push_cast
      ring
    rw [key]
    have hd : |r * c1 + (q + 1) * σ ^ 2 * c0| ≤ ν * Λ := by
      calc _ ≤ |r| * |c1| + (q + 1) * σ ^ 2 * |c0| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q + 1) * σ ^ 2)]
        _ ≤ |r| * Λ + P * σ ^ 2 * Λ := by
            gcongr
            linarith
        _ = ν * Λ := by rw [hνdef]; ring
    have hrh : |1 + r * h| ≤ 1 + |r| * h := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_one, abs_mul, abs_of_nonneg hh]
    have hpow : ρ ^ q ≤ ρ ^ (q + 1) := pow_le_pow_right₀ hρ (Nat.le_succ q)
    have hpow2 : 1 ≤ ρ ^ (q + 2) := one_le_pow₀ hρ
    have hD : 0 ≤ h ^ 2 * (ν * Λ) := by positivity
    have hgrow : 1 + |r| * h + q * σ ^ 2 * h ≤ ρ := by
      rw [hρdef, hνdef]
      have : (q : ℝ) * σ ^ 2 * h ≤ P * σ ^ 2 * h := by
        have : (q : ℝ) ≤ P := by linarith
        gcongr
      nlinarith
    have hF1 := h1
    have hF0 := h0
    push_cast at hF1
    calc |(1 + r * h) * (M1 - 1 - c1 * h) + ((q + 1) * (σ ^ 2 * h)) * (M0 - 1 - c0 * h) +
          h ^ 2 * (r * c1 + (q + 1) * σ ^ 2 * c0)|
        ≤ (1 + |r| * h) * |M1 - 1 - c1 * h| + ((q + 1) * (σ ^ 2 * h)) * |M0 - 1 - c0 * h| +
            h ^ 2 * (ν * Λ) := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_right hrh (abs_nonneg _)
          · rw [abs_mul, abs_of_nonneg (by positivity)]
          · rw [abs_mul, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ (1 + |r| * h) * (h ^ 2 * ((q : ℝ) + 1) * (ν * Λ) * ρ ^ (q + 1)) +
            ((q + 1) * (σ ^ 2 * h)) * (h ^ 2 * q * (ν * Λ) * ρ ^ q) + h ^ 2 * (ν * Λ) := by
          gcongr
      _ ≤ h ^ 2 * (ν * Λ) * (((q : ℝ) + 1) * ρ ^ (q + 1) * (1 + |r| * h + q * σ ^ 2 * h) +
            ρ ^ (q + 2)) := by
          have e1 : ((q + 1) * (σ ^ 2 * h)) * (h ^ 2 * q * (ν * Λ) * ρ ^ q) ≤
              ((q + 1) * (σ ^ 2 * h)) * (h ^ 2 * q * (ν * Λ) * ρ ^ (q + 1)) := by
            gcongr
          linarith [e1, mul_le_mul_of_nonneg_left hpow2 hD]
      _ ≤ h ^ 2 * (ν * Λ) * (((q : ℝ) + 1) * ρ ^ (q + 1) * ρ + ρ ^ (q + 2)) := by
          gcongr
      _ = h ^ 2 * (((q + 2 : ℕ) : ℝ)) * (ν * Λ) * ρ ^ (q + 2) := by
          push_cast
          ring

/-- `0 ≤ e^{ch} − 1 − ch ≤ Λ²h²e^{Λh}` for `|c| ≤ Λ` and `h ≥ 0` (the remainder of the first-order
expansion of the GBM moments `E[B^j] = e^{c_j h}`, Giles 2015, §5.1). -/
lemma exp_mul_sub_one_sub_le {c Λ h : ℝ} (hc : |c| ≤ Λ) (hh : 0 ≤ h) :
    0 ≤ Real.exp (c * h) - 1 - c * h ∧
      Real.exp (c * h) - 1 - c * h ≤ Λ ^ 2 * h ^ 2 * Real.exp (Λ * h) := by
  have hΛ : 0 ≤ Λ := (abs_nonneg c).trans hc
  have hE := exp_sub_one_sub_le_sq_mul_max (c * h)
  have hch : c * h ≤ Λ * h := mul_le_mul_of_nonneg_right ((le_abs_self c).trans hc) hh
  have hmax : max 1 (Real.exp (c * h)) ≤ Real.exp (Λ * h) :=
    max_le (Real.one_le_exp (mul_nonneg hΛ hh)) (Real.exp_le_exp.2 hch)
  have hsq : (c * h) ^ 2 ≤ Λ ^ 2 * h ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg c) hΛ).2 hc |>.trans_eq'
      (sq_abs c)) (sq_nonneg h)
  exact ⟨hE.1, hE.2.trans (mul_le_mul hsq hmax (by positivity) (by positivity))⟩

/-- **The `P`-th moments of one Euler–Maruyama step and one exact step agree to second order**
(Giles 2015, §5.1): `|E[A^P] − E[B^P]| ≤ 2Λ_P²h²e^{Λ_P h}` with `Λ_P = P(|r| + Pσ²)`, `h ≥ 0`. -/
lemma abs_gbmEMFactor_moment_sub_exp_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (P : ℕ) :
    |∫ x, gbmEMFactor r σ h x ^ P ∂gaussianReal 0 1 -
        Real.exp (((P : ℝ) * r + P * (P - 1) * σ ^ 2 / 2) * h)| ≤
      2 * (P * (|r| + P * σ ^ 2)) ^ 2 * h ^ 2 * Real.exp (P * (|r| + P * σ ^ 2) * h) := by
  set ν : ℝ := |r| + P * σ ^ 2 with hνdef
  set Λ : ℝ := P * ν with hΛdef
  set c : ℝ := (P : ℝ) * r + P * (P - 1) * σ ^ 2 / 2 with hcdef
  have hν : 0 ≤ ν := by positivity
  have hF := gbmEMFactor_moment_lin_le r σ hh P P le_rfl
  have hρ : (1 + ν * h) ^ P ≤ Real.exp (Λ * h) := by
    calc (1 + ν * h) ^ P ≤ Real.exp (ν * h) ^ P :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (ν * h)]) P
      _ = Real.exp (Λ * h) := by
          rw [← Real.exp_nat_mul, hΛdef]
          ring_nf
  obtain ⟨hE1, hE2⟩ := exp_mul_sub_one_sub_le (abs_gbmMomentRate_le r σ le_rfl : |c| ≤ Λ) hh
  have e1 : |∫ x, gbmEMFactor r σ h x ^ P ∂gaussianReal 0 1 - 1 - c * h| ≤
      Λ ^ 2 * h ^ 2 * Real.exp (Λ * h) := by
    refine hF.trans ?_
    calc h ^ 2 * P * (ν * Λ) * (1 + ν * h) ^ P = Λ ^ 2 * h ^ 2 * (1 + ν * h) ^ P := by
          rw [hΛdef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hρ (by positivity)
  have e3 := abs_sub (∫ x, gbmEMFactor r σ h x ^ P ∂gaussianReal 0 1 - 1 - c * h)
    (Real.exp (c * h) - 1 - c * h)
  rw [abs_of_nonneg hE1] at e3
  calc _ = |(∫ x, gbmEMFactor r σ h x ^ P ∂gaussianReal 0 1 - 1 - c * h) -
        (Real.exp (c * h) - 1 - c * h)| := by ring_nf
    _ ≤ _ := by linarith

/-- `|E[A^P]| ≤ e^{(P|r| + P²σ²/2)h}` for the Euler–Maruyama step `A` of GBM and `h ≥ 0` (Giles
2015, §5.1; `abs_integral_affine_pow_le`). -/
lemma abs_integral_gbmEMFactor_pow_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (P : ℕ) :
    |∫ x, gbmEMFactor r σ h x ^ P ∂gaussianReal 0 1| ≤
      Real.exp ((P * |r| + (P : ℝ) ^ 2 * σ ^ 2 / 2) * h) := by
  have hA : 1 ≤ 1 + |r| * h := le_add_of_nonneg_right (by positivity)
  have haA : |1 + r * h| ≤ 1 + |r| * h := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_one, abs_mul, abs_of_nonneg hh]
  have h1 := abs_integral_affine_pow_le (s := σ * Real.sqrt h) hA haA P
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  have h2 : (1 + |r| * h) ^ P ≤ Real.exp (P * |r| * h) := by
    calc (1 + |r| * h) ^ P ≤ Real.exp (|r| * h) ^ P :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (|r| * h)]) _
      _ = Real.exp (P * |r| * h) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  refine h1.trans ?_
  rw [hs]
  calc (1 + |r| * h) ^ P * Real.exp ((P : ℝ) ^ 2 * (σ ^ 2 * h) / 2)
      ≤ Real.exp (P * |r| * h) * Real.exp ((P : ℝ) ^ 2 * (σ ^ 2 * h) / 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp ((P * |r| + (P : ℝ) ^ 2 * σ ^ 2 / 2) * h) := by
        rw [← Real.exp_add]
        ring_nf

/-- The constant of the weak error of the Euler–Maruyama scheme for the monomial payoff `x^p`
(Giles 2015, §5.1): `C_p(t) = 2|S_0|^p Λ_p² t e^{Λ_p t}` with `Λ_p = p(|r| + pσ²)`. -/
noncomputable def gbmWeakPowConst (p : ℕ) (r σ t s₀ : ℝ) : ℝ :=
  2 * |s₀| ^ p * (p * (|r| + p * σ ^ 2)) ^ 2 * t * Real.exp (p * (|r| + p * σ ^ 2) * t)

/-- **Weak order one for monomial payoffs, at every grid time** (Giles 2015, §5.1, p. 30,
l. 1318–1320: "if `h_ℓ = 2^{−ℓ}h_0` … then `α = 1`").  For `h ≥ 0` and `n, p ∈ ℕ`, the
Euler–Maruyama value `Ŝ_n` and the exact solution `S_{t_n}`, `t_n = nh`, driven by the same
increments satisfy `|E[Ŝ_n^p] − E[S_{t_n}^p]| ≤ C_p(t_n) h` with
`C_p(t) = 2|S_0|^p Λ_p² t e^{Λ_p t}`, `Λ_p = p(|r| + pσ²)` (`gbmWeakPowConst`).  Both moments
are explicit, `S_0^p a^n` and `S_0^p b^n` with `a = E[A^p]`, `b = E[B^p]`, and `|a − b| = O(h²)`,
`|a|, |b| ≤ e^{Λ_p h}`. -/
theorem gbm_em_weak_error_pow (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n p : ℕ) :
    |∫ z, emPath (gbmDrift r) (gbmVol σ) h s₀ z n ^ p ∂stdNormalSeq -
        ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
          σ * (Real.sqrt h * ∑ i ∈ range n, z i))) ^ p ∂stdNormalSeq| ≤
      gbmWeakPowConst p r σ (n * h) s₀ * h := by
  rw [integral_emPath_gbm_pow, integral_gbmExp_pow r σ s₀ hh]
  set Λ : ℝ := p * (|r| + p * σ ^ 2) with hΛdef
  set a := ∫ x, gbmEMFactor r σ h x ^ p ∂gaussianReal 0 1 with hadef
  set b := Real.exp (((p : ℝ) * r + p * (p - 1) * σ ^ 2 / 2) * h) with hbdef
  have hb : Real.exp (p * (r + (p - 1) * σ ^ 2 / 2) * (n * h)) = b ^ n := by
    rw [hbdef, ← Real.exp_nat_mul]
    ring_nf
  have hab := abs_gbmEMFactor_moment_sub_exp_le r σ hh p
  have ha : |a| ≤ Real.exp (Λ * h) := by
    refine (abs_integral_gbmEMFactor_pow_le r σ hh p).trans (Real.exp_le_exp.2 ?_)
    refine mul_le_mul_of_nonneg_right ?_ hh
    have : 0 ≤ (p : ℝ) ^ 2 * σ ^ 2 := by positivity
    rw [hΛdef]
    nlinarith
  have hbb : |b| ≤ Real.exp (Λ * h) := by
    rw [hbdef, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (abs_gbmMomentRate_le r σ le_rfl)) hh)
  rw [← hadef, ← hbdef] at hab
  rw [hb, ← mul_sub, abs_mul, abs_pow]
  have hmax : max |a| |b| ^ (n - 1) ≤ Real.exp (Λ * h) ^ (n - 1) :=
    pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg a)) (max_le ha hbb) _
  have hpow := abs_pow_sub_pow_le a b n
  have key : |a ^ n - b ^ n| ≤ 2 * Λ ^ 2 * (n * h) * Real.exp (Λ * (n * h)) * h := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp
    · have hexp : Real.exp (Λ * h) * Real.exp (Λ * h) ^ (n - 1) = Real.exp (Λ * (n * h)) := by
        rw [← pow_succ', Nat.sub_add_cancel h0, ← Real.exp_nat_mul]
        ring_nf
      calc |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) := hpow
        _ ≤ (2 * Λ ^ 2 * h ^ 2 * Real.exp (Λ * h)) * n * Real.exp (Λ * h) ^ (n - 1) := by
            gcongr
        _ = 2 * Λ ^ 2 * (n * h) * (Real.exp (Λ * h) * Real.exp (Λ * h) ^ (n - 1)) * h := by
            ring
        _ = _ := by rw [hexp]
  calc |s₀| ^ p * |a ^ n - b ^ n| ≤
        |s₀| ^ p * (2 * Λ ^ 2 * (n * h) * Real.exp (Λ * (n * h)) * h) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by
        rw [gbmWeakPowConst, ← hΛdef]
        ring

/-- **Weak order one for monomial payoffs on level `ℓ`** (Giles 2015, §5.1, p. 30, l. 1318–1320:
"if `h_ℓ = 2^{−ℓ}h_0` with twice as many timesteps on each successive level … then `α = 1`").  For
`T ≥ 0`, every level `ℓ` and `p ∈ ℕ`, `|E[Ŝ_ℓ^p] − E[S_T^p]| ≤ C_p(T) h_ℓ` with `h_ℓ = T 2^{−ℓ}`
and `C_p(T) = 2|S_0|^p Λ_p² T e^{Λ_p T}`, `Λ_p = p(|r| + pσ²)` (`gbmWeakPowConst`). -/
theorem gbm_weak_error_pow (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ p : ℕ) :
    |∫ z, gbmEM r σ T s₀ ℓ z ^ p ∂stdNormalSeq - ∫ z, gbmExact r σ T s₀ ℓ z ^ p ∂stdNormalSeq| ≤
      gbmWeakPowConst p r σ T s₀ * (T / 2 ^ ℓ) := by
  have h := gbm_em_weak_error_pow r σ s₀ (div_nonneg hT (by positivity : (0 : ℝ) ≤ 2 ^ ℓ))
    (2 ^ ℓ) p
  rw [cast_two_pow_mul_div] at h
  exact h

/-- The powers of the Euler–Maruyama value `Ŝ_n` of GBM are integrable (Giles 2015, §5.1):
`Ŝ_n^i = S_0^i ∏_{k<n} A_k^i` with independent Gaussian polynomials `A_k^i`. -/
lemma integrable_emPath_gbm_pow (r σ h s₀ : ℝ) (n i : ℕ) :
    Integrable (fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z n ^ i) stdNormalSeq := by
  simp_rw [emPath_gbm, mul_pow, ← prod_pow]
  exact (integrable_prod_stdNormalSeq (F := fun x => gbmEMFactor r σ h x ^ i)
    ((measurable_gbmEMFactor _ _ _).pow_const i) (integrable_affine_pow_gaussian _ _ i)
    _).const_mul _

/-- The powers of the exact GBM solution `S_{t_n}` on the grid are integrable (Giles 2015, §5.1):
`S_{t_n}^i = S_0^i ∏_{k<n} B_k^i` with independent log-normal factors `B_k^i`. -/
lemma integrable_gbmExp_pow (r σ h s₀ : ℝ) (n i : ℕ) :
    Integrable (fun z => (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
      σ * (Real.sqrt h * ∑ k ∈ range n, z k))) ^ i) stdNormalSeq := by
  simp_rw [gbmExp_eq_prod, mul_pow, ← prod_pow]
  exact (integrable_prod_stdNormalSeq (F := fun x => gbmExpFactor r σ h x ^ i)
    ((measurable_gbmExpFactor _ _ _).pow_const i) (integrable_gbmExpFactor_pow _ _ _ i)
    _).const_mul _

/-- The powers of the level-`ℓ` Euler–Maruyama approximation of GBM are integrable (Giles 2015,
§5.1). -/
lemma integrable_gbmEM_pow (r σ T s₀ : ℝ) (ℓ i : ℕ) :
    Integrable (fun z => gbmEM r σ T s₀ ℓ z ^ i) stdNormalSeq :=
  integrable_emPath_gbm_pow r σ (T / 2 ^ ℓ) s₀ (2 ^ ℓ) i

/-- The powers of the exact GBM solution are integrable (Giles 2015, §5.1). -/
lemma integrable_gbmExact_pow (r σ T s₀ : ℝ) (ℓ i : ℕ) :
    Integrable (fun z => gbmExact r σ T s₀ ℓ z ^ i) stdNormalSeq := by
  simp_rw [gbmExact_eq_prod, mul_pow, ← prod_pow]
  exact (integrable_prod_stdNormalSeq (F := fun x => gbmExpFactor r σ (T / 2 ^ ℓ) x ^ i)
    ((measurable_gbmExpFactor _ _ _).pow_const i) (integrable_gbmExpFactor_pow _ _ _ i)
    _).const_mul _

/-- Weak order one for polynomial payoffs at every grid time (Giles 2015, §5.1): for `h ≥ 0`,
`n ∈ ℕ` and every real polynomial `q = ∑_k c_k X^k`,
`|E[q(Ŝ_n)] − E[q(S_{t_n})]| ≤ (∑_k |c_k| C_k(t_n)) h`, `t_n = nh`, with the monomial constants
`C_k` of `gbm_em_weak_error_pow` (`gbmWeakPowConst`). -/
lemma gbm_em_weak_error_poly (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) (q : Polynomial ℝ) :
    |∫ z, q.eval (emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ∂stdNormalSeq -
        ∫ z, q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
          σ * (Real.sqrt h * ∑ i ∈ range n, z i))) ∂stdNormalSeq| ≤
      (∑ i ∈ range (q.natDegree + 1), |q.coeff i| * gbmWeakPowConst i r σ (n * h) s₀) * h := by
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [integral_finsetSum _ (fun i _ => (integrable_emPath_gbm_pow r σ h s₀ n i).const_mul _),
    integral_finsetSum _ (fun i _ => (integrable_gbmExp_pow r σ h s₀ n i).const_mul _),
    ← sum_sub_distrib, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [integral_const_mul, integral_const_mul, ← mul_sub, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (gbm_em_weak_error_pow r σ s₀ hh n i) (abs_nonneg _)

/-- **Weak order one for polynomial payoffs** (Giles 2015, §5.1, p. 30, l. 1318–1320:
"Alternatively, if `h_ℓ = 2^{−ℓ}h_0` with twice as many timesteps on each successive level, as used
in the numerical examples in this article, then `α = 1`, `β = 1` and `γ = 1`").  For `T ≥ 0`, every
level `ℓ` and every real polynomial `q = ∑_k c_k X^k`,
`|E[q(Ŝ_ℓ)] − E[q(S_T)]| ≤ (∑_k |c_k| C_k(T)) h_ℓ`, `h_ℓ = T 2^{−ℓ}`, with the monomial constants
`C_k(T)` of `gbm_weak_error_pow` (`gbmWeakPowConst`): the rate `α = 1`. -/
theorem gbm_weak_error_poly (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ : ℕ) (q : Polynomial ℝ) :
    |∫ z, q.eval (gbmEM r σ T s₀ ℓ z) ∂stdNormalSeq -
        ∫ z, q.eval (gbmExact r σ T s₀ ℓ z) ∂stdNormalSeq| ≤
      (∑ i ∈ range (q.natDegree + 1), |q.coeff i| * gbmWeakPowConst i r σ T s₀) *
        (T / 2 ^ ℓ) := by
  have h := gbm_em_weak_error_poly r σ s₀ (div_nonneg hT (by positivity : (0 : ℝ) ≤ 2 ^ ℓ))
    (2 ^ ℓ) q
  rw [cast_two_pow_mul_div] at h
  exact h

/-- **Weak order one for polynomial payoffs with refinement factor `M`** (Giles 2015, §5.1, p. 29,
l. 1281–1282: "On level `ℓ`, the uniform timestep is taken to be `h_ℓ = h_0 M^ℓ` [read
`h_0 M^{−ℓ}`], for some integer `M`", and p. 30, l. 1317–1318: "If `h_ℓ = 4^{−ℓ}h_0`, as in the
numerical examples in (Giles 2008b), then this gives `α = 2`").  For `T ≥ 0`, `m, M ≥ 1`,
`h_0 = T/m`, `h_ℓ = h_0 M^{−ℓ}` and every real polynomial `q = ∑_k c_k X^k`, the Euler–Maruyama
payoff after `m M^ℓ` steps of size `h_ℓ` (`emFineM`) satisfies
`|E[q(Ŝ_ℓ)] − E[q(S_T)]| ≤ (∑_k |c_k| C_k(T)) h_ℓ` (`gbmWeakPowConst`), with
`S_T = S_0 e^{(r − σ²/2)T + σ√T Z}`, `Z ∼ N(0,1)`: the rate `α = log₂ M` in Theorem 1's base `2`
(`α = 2` for `M = 4`). -/
theorem gbm_weak_error_poly_M (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m M : ℕ} (hm : 0 < m)
    (hM : 0 < M) (q : Polynomial ℝ) (ℓ : ℕ) :
    |∫ z, emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => q.eval (path (m * M ^ ℓ)))
        ℓ z ∂stdNormalSeq -
      ∫ w, q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1|
      ≤ (∑ i ∈ range (q.natDegree + 1), |q.coeff i| * gbmWeakPowConst i r σ T s₀) *
        (T / m / (M : ℝ) ^ ℓ) := by
  have hh : 0 ≤ T / m / (M : ℝ) ^ ℓ := by positivity
  have H := gbm_em_weak_error_poly r σ s₀ hh (m * M ^ ℓ) q
  rw [cast_mul_pow_mul_div hm hM] at H
  change |∫ z, q.eval (emPath (gbmDrift r) (gbmVol σ) (T / m / (M : ℝ) ^ ℓ) s₀ z (m * M ^ ℓ))
      ∂stdNormalSeq - ∫ z, q.eval (gbmExactM r σ T s₀ m M ℓ z) ∂stdNormalSeq| ≤ _ at H
  rw [integral_comp_gbmExactM r σ T s₀ hm hM ℓ q.continuous.measurable] at H
  exact H

/-! ### Taylor's formula with a bound on the derivative -/

/-- `|f(t)| ≤ C t^{k+1}/(k+1)` for `t ≥ 0` if `f(0) = 0` and `|f'(s)| ≤ C|s|^k` (the integrated
remainder bounds behind the Taylor expansion of the backward functions, Giles 2015, §5.1). -/
lemma abs_le_of_hasDerivAt_le_pow_of_nonneg {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) {C : ℝ} {k : ℕ} (hb : ∀ t, |f' t| ≤ C * |t| ^ k) {t : ℝ} (ht : 0 ≤ t) :
    |f t| ≤ C * t ^ (k + 1) / (k + 1) := by
  have hB : ∀ s, HasDerivAt (fun s : ℝ => C * s ^ (k + 1) / (k + 1)) (C * s ^ k) s := fun s => by
    refine (((hasDerivAt_pow (k + 1) s).const_mul C).div_const ((k : ℝ) + 1)).congr_deriv ?_
    rw [Nat.add_sub_cancel]
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t)
    (f := f) (f' := f') (B := fun s : ℝ => C * s ^ (k + 1) / (k + 1)) (B' := fun s => C * s ^ k)
    (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s _ => (hf s).hasDerivWithinAt)
    (by simp [h0]) hB (fun s hs => by
      rw [Real.norm_eq_abs]
      have := hb s
      rwa [abs_of_nonneg hs.1] at this) ⟨ht, le_rfl⟩
  simpa [Real.norm_eq_abs] using key

/-- `|f(t)| ≤ C|t|^{k+1}/(k+1)` for every `t` if `f(0) = 0` and `|f'(s)| ≤ C|s|^k` (Giles 2015,
§5.1: the Taylor remainders of the backward functions). -/
lemma abs_le_of_hasDerivAt_le_pow {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) {C : ℝ} {k : ℕ} (hb : ∀ t, |f' t| ≤ C * |t| ^ k) (t : ℝ) :
    |f t| ≤ C * |t| ^ (k + 1) / (k + 1) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact abs_le_of_hasDerivAt_le_pow_of_nonneg hf h0 hb ht
  · have hg : ∀ s, HasDerivAt (fun s => f (-s)) (-f' (-s)) s := fun s =>
      ((hf (-s)).comp s (hasDerivAt_neg s)).congr_deriv (by ring)
    have h := abs_le_of_hasDerivAt_le_pow_of_nonneg hg (by simpa using h0)
      (fun s => by simpa [abs_neg] using hb (-s)) (neg_nonneg.2 ht.le)
    simp only [neg_neg] at h
    rw [abs_of_neg ht]
    exact h

/-- **Taylor's formula of order three with the Lagrange bound of the remainder** (the expansion of
the backward function over one time step, Giles 2015, §5.1): if `u, u₁, u₂, u₃` have derivatives
`u₁, u₂, u₃, u₄` and `|u₄| ≤ K`, then
`|u(x + y) − u(x) − u₁(x) y − u₂(x) y²/2 − u₃(x) y³/6| ≤ K y⁴/24`. -/
lemma abs_taylor_four_le {u u₁ u₂ u₃ u₄ : ℝ → ℝ} (h0 : ∀ x, HasDerivAt u (u₁ x) x)
    (h1 : ∀ x, HasDerivAt u₁ (u₂ x) x) (h2 : ∀ x, HasDerivAt u₂ (u₃ x) x)
    (h3 : ∀ x, HasDerivAt u₃ (u₄ x) x) {K : ℝ} (hK : ∀ x, |u₄ x| ≤ K) (x y : ℝ) :
    |u (x + y) - u x - u₁ x * y - u₂ x * y ^ 2 / 2 - u₃ x * y ^ 3 / 6| ≤ K * y ^ 4 / 24 := by
  have e3 : ∀ t, |u₃ (x + t) - u₃ x| ≤ K * |t| ^ 1 := fun t => by
    have := abs_le_of_hasDerivAt_le_pow (f := fun t => u₃ (x + t) - u₃ x)
      (f' := fun t => u₄ (x + t)) (fun t => ((h3 (x + t)).comp_const_add x t).sub_const _)
      (by simp) (k := 0) (fun t => by simpa using hK (x + t)) t
    simpa using this
  have e2 : ∀ t, |u₂ (x + t) - u₂ x - u₃ x * t| ≤ K / 2 * |t| ^ 2 := fun t => by
    have := abs_le_of_hasDerivAt_le_pow (f := fun t => u₂ (x + t) - u₂ x - u₃ x * t)
      (f' := fun t => u₃ (x + t) - u₃ x)
      (fun t => ((((h2 (x + t)).comp_const_add x t).sub_const (u₂ x)).sub
          ((hasDerivAt_id t).const_mul (u₃ x))).congr_deriv (by simp))
      (by simp) (k := 1) e3 t
    calc _ ≤ K * |t| ^ (1 + 1) / ((1 : ℕ) + 1) := this
      _ = _ := by push_cast; ring
  have e1 : ∀ t, |u₁ (x + t) - u₁ x - u₂ x * t - u₃ x * t ^ 2 / 2| ≤ K / 6 * |t| ^ 3 :=
    fun t => by
    have := abs_le_of_hasDerivAt_le_pow
      (f := fun t => u₁ (x + t) - u₁ x - u₂ x * t - u₃ x * t ^ 2 / 2)
      (f' := fun t => u₂ (x + t) - u₂ x - u₃ x * t)
      (fun t => (((((h1 (x + t)).comp_const_add x t).sub_const (u₁ x)).sub
          ((hasDerivAt_id t).const_mul (u₂ x))).sub
          (((hasDerivAt_pow 2 t).const_mul (u₃ x)).div_const 2)).congr_deriv
          (by norm_num; ring))
      (by simp) (k := 2) e2 t
    calc _ ≤ K / 2 * |t| ^ (2 + 1) / ((2 : ℕ) + 1) := this
      _ = _ := by push_cast; ring
  have e0 := abs_le_of_hasDerivAt_le_pow
    (f := fun t => u (x + t) - u x - u₁ x * t - u₂ x * t ^ 2 / 2 - u₃ x * t ^ 3 / 6)
    (f' := fun t => u₁ (x + t) - u₁ x - u₂ x * t - u₃ x * t ^ 2 / 2)
    (fun t => ((((((h0 (x + t)).comp_const_add x t).sub_const (u x)).sub
        ((hasDerivAt_id t).const_mul (u₁ x))).sub
        (((hasDerivAt_pow 2 t).const_mul (u₂ x)).div_const 2)).sub
        (((hasDerivAt_pow 3 t).const_mul (u₃ x)).div_const 6)).congr_deriv
        (by norm_num; ring))
    (by simp) (k := 3) e1 y
  calc _ ≤ K / 6 * |y| ^ (3 + 1) / ((3 : ℕ) + 1) := e0
    _ = _ := by
        rw [← abs_pow, abs_of_nonneg (by norm_num; positivity)]
        push_cast
        ring

/-- A function whose derivative is bounded by `K` grows at most linearly:
`|u(y)| ≤ |u(0)| + K|y|` (the integrability of the backward functions of GBM, Giles 2015, §5.1). -/
lemma abs_le_abs_zero_add_of_hasDerivAt {u u₁ : ℝ → ℝ} (h0 : ∀ x, HasDerivAt u (u₁ x) x) {K : ℝ}
    (hK : ∀ x, |u₁ x| ≤ K) (y : ℝ) : |u y| ≤ |u 0| + K * |y| := by
  have := abs_le_of_hasDerivAt_le_pow (f := fun t => u t - u 0) (f' := u₁)
    (fun t => (h0 t).sub_const _) (by simp) (k := 0) (fun t => by simpa using hK t) y
  simp only [zero_add, pow_one, Nat.cast_zero, div_one] at this
  linarith [abs_sub_abs_le_abs_sub (u y) (u 0)]

/-! ### One time step -/

/-- The integral of a polynomial of degree at most four in an integrable `F` with integrable powers
(the moments of the one-step errors of GBM, Giles 2015, §5.1). -/
lemma integral_quartic_comb {ν : Measure ℝ} [IsProbabilityMeasure ν] {F : ℝ → ℝ}
    (h1 : Integrable F ν) (h2 : Integrable (fun w => F w ^ 2) ν)
    (h3 : Integrable (fun w => F w ^ 3) ν) (h4 : Integrable (fun w => F w ^ 4) ν)
    (a₀ a₁ a₂ a₃ a₄ : ℝ) :
    ∫ w, (a₀ + a₁ * F w + a₂ * F w ^ 2 + a₃ * F w ^ 3 + a₄ * F w ^ 4) ∂ν =
      a₀ + a₁ * ∫ w, F w ∂ν + a₂ * ∫ w, F w ^ 2 ∂ν + a₃ * ∫ w, F w ^ 3 ∂ν +
        a₄ * ∫ w, F w ^ 4 ∂ν := by
  have i1 : Integrable (fun w => a₀ + a₁ * F w) ν := (integrable_const _).add (h1.const_mul _)
  have i2 : Integrable (fun w => a₀ + a₁ * F w + a₂ * F w ^ 2) ν := i1.add (h2.const_mul _)
  have i3 : Integrable (fun w => a₀ + a₁ * F w + a₂ * F w ^ 2 + a₃ * F w ^ 3) ν :=
    i2.add (h3.const_mul _)
  rw [integral_add i3 (h4.const_mul _), integral_add i2 (h3.const_mul _),
    integral_add i1 (h2.const_mul _), integral_add (integrable_const _) (h1.const_mul _),
    integral_const, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, probReal_univ, one_smul]

/-- **Taylor's formula in expectation** (Giles 2015, §5.1, one step of the weak-error argument):
under the hypotheses of `abs_taylor_four_le`, for a random step `x + xY` with `Y, …, Y⁴`
integrable, `|E[u(x + xY)] − u(x) − u₁(x) x E[Y] − u₂(x) x² E[Y²]/2 − u₃(x) x³ E[Y³]/6|
≤ K x⁴ E[Y⁴]/24`. -/
lemma abs_integral_taylor_four_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {u u₁ u₂ u₃ u₄ : ℝ → ℝ} (h0 : ∀ x, HasDerivAt u (u₁ x) x)
    (h1 : ∀ x, HasDerivAt u₁ (u₂ x) x) (h2 : ∀ x, HasDerivAt u₂ (u₃ x) x)
    (h3 : ∀ x, HasDerivAt u₃ (u₄ x) x) {K : ℝ} (hK : ∀ x, |u₄ x| ≤ K) {Y : ℝ → ℝ}
    (hY1 : Integrable Y ν) (hY2 : Integrable (fun w => Y w ^ 2) ν)
    (hY3 : Integrable (fun w => Y w ^ 3) ν) (hY4 : Integrable (fun w => Y w ^ 4) ν) (x : ℝ)
    (hu : Integrable (fun w => u (x + x * Y w)) ν) :
    |∫ w, u (x + x * Y w) ∂ν - (u x + u₁ x * x * ∫ w, Y w ∂ν +
        u₂ x * x ^ 2 / 2 * ∫ w, Y w ^ 2 ∂ν + u₃ x * x ^ 3 / 6 * ∫ w, Y w ^ 3 ∂ν)| ≤
      K * x ^ 4 / 24 * ∫ w, Y w ^ 4 ∂ν := by
  have hpint := integral_quartic_comb hY1 hY2 hY3 hY4 (u x) (u₁ x * x) (u₂ x * x ^ 2 / 2)
    (u₃ x * x ^ 3 / 6) 0
  have hp : Integrable (fun w => u x + u₁ x * x * Y w + u₂ x * x ^ 2 / 2 * Y w ^ 2 +
      u₃ x * x ^ 3 / 6 * Y w ^ 3 + 0 * Y w ^ 4) ν :=
    ((((integrable_const _).add (hY1.const_mul _)).add (hY2.const_mul _)).add
      (hY3.const_mul _)).add (hY4.const_mul _)
  rw [zero_mul, add_zero] at hpint
  rw [← hpint, ← integral_sub hu hp, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hY4.const_mul (K * x ^ 4 / 24))
    (Filter.Eventually.of_forall fun w => ?_)).trans_eq (integral_const_mul _ _)
  rw [Real.norm_eq_abs]
  have := abs_taylor_four_le h0 h1 h2 h3 hK x (x * Y w)
  calc |u (x + x * Y w) - (u x + u₁ x * x * Y w + u₂ x * x ^ 2 / 2 * Y w ^ 2 +
        u₃ x * x ^ 3 / 6 * Y w ^ 3 + 0 * Y w ^ 4)|
      = |u (x + x * Y w) - u x - u₁ x * (x * Y w) - u₂ x * (x * Y w) ^ 2 / 2 -
          u₃ x * (x * Y w) ^ 3 / 6| := by ring_nf
    _ ≤ K * (x * Y w) ^ 4 / 24 := this
    _ = _ := by ring

/-- The moments of the one-step error `A − 1 = rh + σ√h Z` of the Euler–Maruyama scheme for GBM
(Giles 2015, §5.1): `rh`, `r²h² + σ²h`, `r³h³ + 3rσ²h²`, `r⁴h⁴ + 6r²σ²h³ + 3σ⁴h²`. -/
lemma gbm_step_moments (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ w, (gbmEMFactor r σ h w - 1) ∂gaussianReal 0 1 = r * h ∧
    ∫ w, (gbmEMFactor r σ h w - 1) ^ 2 ∂gaussianReal 0 1 = r ^ 2 * h ^ 2 + σ ^ 2 * h ∧
    ∫ w, (gbmEMFactor r σ h w - 1) ^ 3 ∂gaussianReal 0 1 = r ^ 3 * h ^ 3 + 3 * r * σ ^ 2 * h ^ 2 ∧
    ∫ w, (gbmEMFactor r σ h w - 1) ^ 4 ∂gaussianReal 0 1 =
      r ^ 4 * h ^ 4 + 6 * r ^ 2 * σ ^ 2 * h ^ 3 + 3 * σ ^ 4 * h ^ 2 := by
  have e : ∀ k : ℕ, ∫ w, (gbmEMFactor r σ h w - 1) ^ k ∂gaussianReal 0 1 =
      ∫ w, (r * h + σ * Real.sqrt h * w) ^ k ∂gaussianReal 0 1 := fun k => by
    congr 1
    funext w
    unfold gbmEMFactor
    ring
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  have m0 : ∫ w, (r * h + σ * Real.sqrt h * w) ^ 0 ∂gaussianReal 0 1 = 1 := by simp
  have m1 := integral_affine_pow_one (r * h) (σ * Real.sqrt h)
  have m2 := integral_affine_pow_add_two (r * h) (σ * Real.sqrt h) 0
  have m3 := integral_affine_pow_add_two (r * h) (σ * Real.sqrt h) 1
  have m4 := integral_affine_pow_add_two (r * h) (σ * Real.sqrt h) 2
  rw [hs] at m2 m3 m4
  simp only [zero_add, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd, Nat.cast_ofNat] at m2 m3 m4
  rw [m0, m1] at m2
  rw [m1, m2] at m3
  rw [m3, m2] at m4
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (e 1).trans m1
  · rw [e 2, m2]; ring
  · rw [e 3, m3]; ring
  · rw [e 4, m4]; ring

/-- The exact GBM step `B` is integrable under `N(0,1)` (Giles 2015, §5.1). -/
lemma integrable_gbmExpFactor (r σ h : ℝ) :
    Integrable (fun x => gbmExpFactor r σ h x) (gaussianReal 0 1) := by
  simpa using integrable_gbmExpFactor_pow r σ h 1

/-- The Euler–Maruyama step `A` of GBM is integrable under `N(0,1)` (Giles 2015, §5.1). -/
lemma integrable_gbmEMFactor (r σ h : ℝ) :
    Integrable (fun w => gbmEMFactor r σ h w) (gaussianReal 0 1) :=
  (integrable_affine_pow_gaussian (1 + r * h) (σ * Real.sqrt h) 1).congr
    (Filter.Eventually.of_forall fun w => by simp [gbmEMFactor])

/-- The moments of the one-step error `B − 1` of the exact GBM solution (Giles 2015, §5.1), from
`E[B^j] = e^{c_j h}`, `c_1 = r`, `c_2 = 2r + σ²`, `c_3 = 3r + 3σ²`, `c_4 = 4r + 6σ²`. -/
lemma gbm_exact_step_moments (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ w, (gbmExpFactor r σ h w - 1) ∂gaussianReal 0 1 = Real.exp (r * h) - 1 ∧
    ∫ w, (gbmExpFactor r σ h w - 1) ^ 2 ∂gaussianReal 0 1 =
      Real.exp ((2 * r + σ ^ 2) * h) - 2 * Real.exp (r * h) + 1 ∧
    ∫ w, (gbmExpFactor r σ h w - 1) ^ 3 ∂gaussianReal 0 1 =
      Real.exp ((3 * r + 3 * σ ^ 2) * h) - 3 * Real.exp ((2 * r + σ ^ 2) * h) +
        3 * Real.exp (r * h) - 1 ∧
    ∫ w, (gbmExpFactor r σ h w - 1) ^ 4 ∂gaussianReal 0 1 =
      Real.exp ((4 * r + 6 * σ ^ 2) * h) - 4 * Real.exp ((3 * r + 3 * σ ^ 2) * h) +
        6 * Real.exp ((2 * r + σ ^ 2) * h) - 4 * Real.exp (r * h) + 1 := by
  have i1 := integrable_gbmExpFactor r σ h
  have i2 := integrable_gbmExpFactor_pow r σ h 2
  have i3 := integrable_gbmExpFactor_pow r σ h 3
  have i4 := integrable_gbmExpFactor_pow r σ h 4
  have e1 : ∫ w, gbmExpFactor r σ h w ∂gaussianReal 0 1 = Real.exp (r * h) := by
    simpa using integral_gbmExpFactor_pow_eq r σ hh 1
  have e2 : ∫ w, gbmExpFactor r σ h w ^ 2 ∂gaussianReal 0 1 = Real.exp ((2 * r + σ ^ 2) * h) := by
    rw [integral_gbmExpFactor_pow_eq r σ hh 2]
    congr 1
    push_cast
    ring
  have e3 : ∫ w, gbmExpFactor r σ h w ^ 3 ∂gaussianReal 0 1 =
      Real.exp ((3 * r + 3 * σ ^ 2) * h) := by
    rw [integral_gbmExpFactor_pow_eq r σ hh 3]
    congr 1
    push_cast
    ring
  have e4 : ∫ w, gbmExpFactor r σ h w ^ 4 ∂gaussianReal 0 1 =
      Real.exp ((4 * r + 6 * σ ^ 2) * h) := by
    rw [integral_gbmExpFactor_pow_eq r σ hh 4]
    congr 1
    push_cast
    ring
  have q := integral_quartic_comb i1 i2 i3 i4
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := q (-1) 1 0 0 0
    rw [e1, e2, e3, e4] at this
    rw [← show (∫ w, (-1 + 1 * gbmExpFactor r σ h w + 0 * gbmExpFactor r σ h w ^ 2 +
      0 * gbmExpFactor r σ h w ^ 3 + 0 * gbmExpFactor r σ h w ^ 4) ∂gaussianReal 0 1) =
        ∫ w, (gbmExpFactor r σ h w - 1) ∂gaussianReal 0 1 by congr 1; funext w; ring, this]
    ring
  · have := q 1 (-2) 1 0 0
    rw [e1, e2, e3, e4] at this
    rw [← show (∫ w, (1 + (-2) * gbmExpFactor r σ h w + 1 * gbmExpFactor r σ h w ^ 2 +
      0 * gbmExpFactor r σ h w ^ 3 + 0 * gbmExpFactor r σ h w ^ 4) ∂gaussianReal 0 1) =
        ∫ w, (gbmExpFactor r σ h w - 1) ^ 2 ∂gaussianReal 0 1 by congr 1; funext w; ring, this]
    ring
  · have := q (-1) 3 (-3) 1 0
    rw [e1, e2, e3, e4] at this
    rw [← show (∫ w, (-1 + 3 * gbmExpFactor r σ h w + (-3) * gbmExpFactor r σ h w ^ 2 +
      1 * gbmExpFactor r σ h w ^ 3 + 0 * gbmExpFactor r σ h w ^ 4) ∂gaussianReal 0 1) =
        ∫ w, (gbmExpFactor r σ h w - 1) ^ 3 ∂gaussianReal 0 1 by congr 1; funext w; ring, this]
    ring
  · have := q 1 (-4) 6 (-4) 1
    rw [e1, e2, e3, e4] at this
    rw [← show (∫ w, (1 + (-4) * gbmExpFactor r σ h w + 6 * gbmExpFactor r σ h w ^ 2 +
      (-4) * gbmExpFactor r σ h w ^ 3 + 1 * gbmExpFactor r σ h w ^ 4) ∂gaussianReal 0 1) =
        ∫ w, (gbmExpFactor r σ h w - 1) ^ 4 ∂gaussianReal 0 1 by congr 1; funext w; ring, this]
    ring

/-- **The one-step moments agree to second order** (Giles 2015, §5.1): with `Λ = 4|r| + 8σ²`,
`E = Λ²h²e^{Λh}` and `h ≥ 0`, the first and second moments of `A − 1` and `B − 1` differ by at most
`E` and `4E`, their third moments are at most `2E` and `7E`, and their fourth moments at most `4E`
and `7E` in absolute value. -/
lemma gbm_step_moment_bounds (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |∫ w, (gbmEMFactor r σ h w - 1) ∂gaussianReal 0 1 -
        ∫ w, (gbmExpFactor r σ h w - 1) ∂gaussianReal 0 1| ≤
      (4 * |r| + 8 * σ ^ 2) ^ 2 * h ^ 2 * Real.exp ((4 * |r| + 8 * σ ^ 2) * h) ∧
    |∫ w, (gbmEMFactor r σ h w - 1) ^ 2 ∂gaussianReal 0 1 -
        ∫ w, (gbmExpFactor r σ h w - 1) ^ 2 ∂gaussianReal 0 1| ≤
      4 * ((4 * |r| + 8 * σ ^ 2) ^ 2 * h ^ 2 * Real.exp ((4 * |r| + 8 * σ ^ 2) * h)) ∧
    |∫ w, (gbmEMFactor r σ h w - 1) ^ 3 ∂gaussianReal 0 1| ≤
      2 * ((4 * |r| + 8 * σ ^ 2) ^ 2 * h ^ 2 * Real.exp ((4 * |r| + 8 * σ ^ 2) * h)) ∧
    |∫ w, (gbmExpFactor r σ h w - 1) ^ 3 ∂gaussianReal 0 1| ≤
      7 * ((4 * |r| + 8 * σ ^ 2) ^ 2 * h ^ 2 * Real.exp ((4 * |r| + 8 * σ ^ 2) * h)) ∧
    ∫ w, (gbmEMFactor r σ h w - 1) ^ 4 ∂gaussianReal 0 1 ≤
      4 * ((4 * |r| + 8 * σ ^ 2) ^ 2 * h ^ 2 * Real.exp ((4 * |r| + 8 * σ ^ 2) * h)) ∧
    ∫ w, (gbmExpFactor r σ h w - 1) ^ 4 ∂gaussianReal 0 1 ≤
      7 * ((4 * |r| + 8 * σ ^ 2) ^ 2 * h ^ 2 * Real.exp ((4 * |r| + 8 * σ ^ 2) * h)) := by
  obtain ⟨a1, a2, a3, a4⟩ := gbm_step_moments r σ hh
  obtain ⟨b1, b2, b3, b4⟩ := gbm_exact_step_moments r σ hh
  rw [a1, a2, a3, a4, b1, b2, b3, b4]
  set Λ : ℝ := 4 * |r| + 8 * σ ^ 2 with hΛdef
  set E : ℝ := Λ ^ 2 * h ^ 2 * Real.exp (Λ * h) with hEdef
  have hs : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hr : 0 ≤ |r| := abs_nonneg r
  have c1 : |r| ≤ Λ := by rw [hΛdef]; linarith
  have c2 : |2 * r + σ ^ 2| ≤ Λ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hs, abs_two]; linarith
  have c3 : |3 * r + 3 * σ ^ 2| ≤ Λ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith
  have c4 : |4 * r + 6 * σ ^ 2| ≤ Λ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 6)]; linarith
  obtain ⟨p1, q1⟩ := exp_mul_sub_one_sub_le c1 hh
  obtain ⟨p2, q2⟩ := exp_mul_sub_one_sub_le c2 hh
  obtain ⟨p3, q3⟩ := exp_mul_sub_one_sub_le c3 hh
  obtain ⟨p4, q4⟩ := exp_mul_sub_one_sub_le c4 hh
  set a : ℝ := |r| * h with hadef
  set b : ℝ := σ ^ 2 * h with hbdef
  have ha : 0 ≤ a := mul_nonneg hr hh
  have hb : 0 ≤ b := mul_nonneg hs hh
  have hy : Λ * h = 4 * a + 8 * b := by rw [hΛdef, hadef, hbdef]; ring
  have hE : E = (4 * a + 8 * b) ^ 2 * Real.exp (4 * a + 8 * b) := by
    rw [hEdef, ← hy]; ring
  have hey := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 4 * a + 8 * b)
  have hra : r ^ 2 * h ^ 2 = a ^ 2 := by rw [hadef, mul_pow, sq_abs]
  have hm4 : r ^ 4 * h ^ 4 + 6 * r ^ 2 * σ ^ 2 * h ^ 3 + 3 * σ ^ 4 * h ^ 2 =
      a ^ 4 + 6 * a ^ 2 * b + 3 * b ^ 2 := by
    rw [← hra, hbdef, hadef, mul_pow, mul_pow, ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 4)]
    ring
  have hr3 : |r ^ 3 * h ^ 3 + 3 * r * σ ^ 2 * h ^ 2| ≤ a ^ 3 + 3 * a * b := by
    have t1 : |r ^ 3 * h ^ 3| = a ^ 3 := by
      rw [hadef, abs_mul, abs_pow, abs_pow, abs_of_nonneg hh]; ring
    have t2 : |3 * r * σ ^ 2 * h ^ 2| = 3 * a * b := by
      rw [hadef, hbdef, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg (sq_nonneg h),
        abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      ring
    exact (abs_add_le _ _).trans (by rw [t1, t2])
  set y : ℝ := 4 * a + 8 * b with hydef
  set ey := Real.exp y with heydef
  have hy0 : 0 ≤ y := by positivity
  have hay : a ≤ y / 4 := by rw [hydef]; linarith
  have hby : b ≤ y / 8 := by rw [hydef]; linarith
  have hey1 : 1 ≤ ey := Real.one_le_exp hy0
  have hey2 : y ≤ ey := by linarith [Real.add_one_le_exp y]
  have hey3 : y ^ 2 / 2 ≤ ey := by linarith
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy3 : 0 ≤ y ^ 3 := pow_nonneg hy0 3
  have hy4 : 0 ≤ y ^ 4 := pow_nonneg hy0 4
  have hE1 : y ^ 2 ≤ E := by rw [hE]; exact le_mul_of_one_le_right hy2 hey1
  have hE2 : y ^ 3 ≤ E := by
    rw [hE, pow_succ]; exact mul_le_mul_of_nonneg_left hey2 hy2
  have hE3 : y ^ 4 / 2 ≤ E := by
    rw [hE]
    calc y ^ 4 / 2 = y ^ 2 * (y ^ 2 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hey3 hy2
  have hya : a ^ 2 ≤ E := by
    have e1 : a ^ 2 ≤ (y / 4) ^ 2 := pow_le_pow_left₀ ha hay 2
    have e2 : (y / 4) ^ 2 = y ^ 2 / 16 := by ring
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show r * h - (Real.exp (r * h) - 1) = -(Real.exp (r * h) - 1 - r * h) by ring, abs_neg,
      abs_of_nonneg p1]
    exact q1
  · rw [show r ^ 2 * h ^ 2 + b - (Real.exp ((2 * r + σ ^ 2) * h) - 2 * Real.exp (r * h) + 1)
      = r ^ 2 * h ^ 2 - (Real.exp ((2 * r + σ ^ 2) * h) - 1 - (2 * r + σ ^ 2) * h) +
        2 * (Real.exp (r * h) - 1 - r * h) by rw [hbdef]; ring]
    have : r ^ 2 * h ^ 2 ≤ E := by rw [hra]; exact hya
    have h0 : 0 ≤ r ^ 2 * h ^ 2 := by positivity
    rw [abs_le]
    constructor <;> linarith
  · refine hr3.trans ?_
    have e1 : a ^ 3 ≤ (y / 4) ^ 3 := pow_le_pow_left₀ ha hay 3
    have e2 : a * b ≤ y / 4 * (y / 8) := mul_le_mul hay hby hb (by positivity)
    have e3 : (y / 4) ^ 3 = y ^ 3 / 64 := by ring
    have e4 : y / 4 * (y / 8) = y ^ 2 / 32 := by ring
    linarith
  · rw [show Real.exp ((3 * r + 3 * σ ^ 2) * h) - 3 * Real.exp ((2 * r + σ ^ 2) * h) +
        3 * Real.exp (r * h) - 1 =
      (Real.exp ((3 * r + 3 * σ ^ 2) * h) - 1 - (3 * r + 3 * σ ^ 2) * h) -
        3 * (Real.exp ((2 * r + σ ^ 2) * h) - 1 - (2 * r + σ ^ 2) * h) +
        3 * (Real.exp (r * h) - 1 - r * h) by ring]
    rw [abs_le]
    constructor <;> linarith
  · rw [hm4]
    have e1 : a ^ 4 ≤ (y / 4) ^ 4 := pow_le_pow_left₀ ha hay 4
    have e2 : a ^ 2 ≤ (y / 4) ^ 2 := pow_le_pow_left₀ ha hay 2
    have e3 : a ^ 2 * b ≤ (y / 4) ^ 2 * (y / 8) := mul_le_mul e2 hby hb (by positivity)
    have e4 : b ^ 2 ≤ (y / 8) ^ 2 := pow_le_pow_left₀ hb hby 2
    have f1 : (y / 4) ^ 4 = y ^ 4 / 256 := by ring
    have f2 : (y / 4) ^ 2 * (y / 8) = y ^ 3 / 128 := by ring
    have f3 : (y / 8) ^ 2 = y ^ 2 / 64 := by ring
    linarith
  · rw [show Real.exp ((4 * r + 6 * σ ^ 2) * h) - 4 * Real.exp ((3 * r + 3 * σ ^ 2) * h) +
        6 * Real.exp ((2 * r + σ ^ 2) * h) - 4 * Real.exp (r * h) + 1 =
      (Real.exp ((4 * r + 6 * σ ^ 2) * h) - 1 - (4 * r + 6 * σ ^ 2) * h) -
        4 * (Real.exp ((3 * r + 3 * σ ^ 2) * h) - 1 - (3 * r + 3 * σ ^ 2) * h) +
        6 * (Real.exp ((2 * r + σ ^ 2) * h) - 1 - (2 * r + σ ^ 2) * h) -
        4 * (Real.exp (r * h) - 1 - r * h) by ring]
    linarith

/-- `u(xF)` is integrable if `u` has a bounded derivative and `F` is integrable (Giles 2015, §5.1:
the backward functions of GBM evaluated after one step). -/
lemma integrable_comp_mul_of_hasDerivAt {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {u u₁ : ℝ → ℝ} (h0 : ∀ x, HasDerivAt u (u₁ x) x) {K : ℝ} (hK : ∀ x, |u₁ x| ≤ K)
    {F : ℝ → ℝ} (hF : Measurable F) (hFi : Integrable F ν) (x : ℝ) :
    Integrable (fun w => u (x * F w)) ν := by
  have hc : Continuous u := continuous_iff_continuousAt.2 fun x => (h0 x).continuousAt
  refine ((integrable_const |u 0|).add (hFi.abs.const_mul (K * |x|))).mono'
    (hc.measurable.comp (hF.const_mul x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs]
  have := abs_le_abs_zero_add_of_hasDerivAt h0 hK (x * F w)
  rw [abs_mul] at this
  refine this.trans (le_of_eq ?_)
  simp only [Pi.add_apply]
  ring

/-- The powers of the one-step error `A − 1` of the Euler–Maruyama scheme are integrable (Giles
2015, §5.1). -/
lemma integrable_gbmEMFactor_sub_one_pow (r σ h : ℝ) (k : ℕ) :
    Integrable (fun w => (gbmEMFactor r σ h w - 1) ^ k) (gaussianReal 0 1) :=
  (integrable_affine_pow_gaussian (r * h) (σ * Real.sqrt h) k).congr
    (Filter.Eventually.of_forall fun w => by simp only [gbmEMFactor]; ring)

/-- The powers of the one-step error `B − 1` of the exact GBM solution are integrable (Giles 2015,
§5.1). -/
lemma integrable_gbmExpFactor_sub_one_pow (r σ h : ℝ) (k : ℕ) :
    Integrable (fun w => (gbmExpFactor r σ h w - 1) ^ k) (gaussianReal 0 1) := by
  have e : (fun w => (gbmExpFactor r σ h w - 1) ^ k) = fun w =>
      ∑ m ∈ range (k + 1), gbmExpFactor r σ h w ^ m * (-1) ^ (k - m) * (k.choose m : ℝ) := by
    funext w
    rw [sub_eq_add_neg, add_pow]
  rw [e]
  exact integrable_finsetSum _ fun m _ =>
    ((integrable_gbmExpFactor_pow r σ h m).mul_const _).mul_const _

/-- `t, t², t³ ≤ 1 + t⁴` for `t ≥ 0` (the polynomial weight of the one-step weak error, Giles 2015,
§5.1). -/
lemma pow_le_one_add_pow_four {t : ℝ} (ht : 0 ≤ t) :
    t ≤ 1 + t ^ 4 ∧ t ^ 2 ≤ 1 + t ^ 4 ∧ t ^ 3 ≤ 1 + t ^ 4 := by
  have h1 : 0 ≤ (t - 1) ^ 2 * (t ^ 2 + t + 1) := by positivity
  have h2 : 0 ≤ (t ^ 2 - 1) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ t ^ 3 := by positivity
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- **One Euler–Maruyama step against one exact step** (Giles 2015, §5.1, the local weak error):
if `u` has derivatives `u₁, …, u₄` bounded by `K` and `h ≥ 0`, then for every `x`,
`|E[u(xA)] − E[u(xB)]| ≤ 5KΛ²h²e^{Λh}(1 + x⁴)` with `Λ = 4|r| + 8σ²`, where `A = 1 + rh + σ√h Z`
and `B = e^{(r − σ²/2)h + σ√h Z}`: third-order Taylor expansion of `u` at `x`
(`abs_integral_taylor_four_le`) and the moment bounds `gbm_step_moment_bounds`. -/
lemma gbm_one_step_weak_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) {u u₁ u₂ u₃ u₄ : ℝ → ℝ}
    (h0 : ∀ x, HasDerivAt u (u₁ x) x) (h1 : ∀ x, HasDerivAt u₁ (u₂ x) x)
    (h2 : ∀ x, HasDerivAt u₂ (u₃ x) x) (h3 : ∀ x, HasDerivAt u₃ (u₄ x) x) {K : ℝ}
    (hK1 : ∀ x, |u₁ x| ≤ K) (hK2 : ∀ x, |u₂ x| ≤ K) (hK3 : ∀ x, |u₃ x| ≤ K)
    (hK4 : ∀ x, |u₄ x| ≤ K) (x : ℝ) :
    |∫ w, u (x * gbmEMFactor r σ h w) ∂gaussianReal 0 1 -
        ∫ w, u (x * gbmExpFactor r σ h w) ∂gaussianReal 0 1| ≤
      5 * K * ((4 * |r| + 8 * σ ^ 2) ^ 2 * h ^ 2 * Real.exp ((4 * |r| + 8 * σ ^ 2) * h)) *
        (1 + x ^ 4) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hK1 0)
  set E : ℝ := (4 * |r| + 8 * σ ^ 2) ^ 2 * h ^ 2 * Real.exp ((4 * |r| + 8 * σ ^ 2) * h)
    with hEdef
  have hE : 0 ≤ E := by positivity
  have iA := integrable_gbmEMFactor_sub_one_pow r σ h
  have iB := integrable_gbmExpFactor_sub_one_pow r σ h
  have eA : ∀ w, x + x * (gbmEMFactor r σ h w - 1) = x * gbmEMFactor r σ h w := fun w => by ring
  have eB : ∀ w, x + x * (gbmExpFactor r σ h w - 1) = x * gbmExpFactor r σ h w := fun w => by
    ring
  have TA := abs_integral_taylor_four_le h0 h1 h2 h3 hK4 (by simpa using iA 1) (iA 2) (iA 3)
    (iA 4) x (by
      simp only [eA]
      exact integrable_comp_mul_of_hasDerivAt h0 hK1 (measurable_gbmEMFactor r σ h)
        (integrable_gbmEMFactor r σ h) x)
  have TB := abs_integral_taylor_four_le h0 h1 h2 h3 hK4 (by simpa using iB 1) (iB 2) (iB 3)
    (iB 4) x (by
      simp only [eB]
      exact integrable_comp_mul_of_hasDerivAt h0 hK1 (measurable_gbmExpFactor r σ h)
        (integrable_gbmExpFactor r σ h) x)
  simp only [eA, eB] at TA TB
  obtain ⟨d1, d2, a3, b3, a4, b4⟩ := gbm_step_moment_bounds r σ hh
  rw [← hEdef] at d1 d2 a3 b3 a4 b4
  set IA := ∫ w, u (x * gbmEMFactor r σ h w) ∂gaussianReal 0 1
  set IB := ∫ w, u (x * gbmExpFactor r σ h w) ∂gaussianReal 0 1
  set mA1 := ∫ w, (gbmEMFactor r σ h w - 1) ∂gaussianReal 0 1
  set mA2 := ∫ w, (gbmEMFactor r σ h w - 1) ^ 2 ∂gaussianReal 0 1
  set mA3 := ∫ w, (gbmEMFactor r σ h w - 1) ^ 3 ∂gaussianReal 0 1
  set mA4 := ∫ w, (gbmEMFactor r σ h w - 1) ^ 4 ∂gaussianReal 0 1
  set mB1 := ∫ w, (gbmExpFactor r σ h w - 1) ∂gaussianReal 0 1
  set mB2 := ∫ w, (gbmExpFactor r σ h w - 1) ^ 2 ∂gaussianReal 0 1
  set mB3 := ∫ w, (gbmExpFactor r σ h w - 1) ^ 3 ∂gaussianReal 0 1
  set mB4 := ∫ w, (gbmExpFactor r σ h w - 1) ^ 4 ∂gaussianReal 0 1
  set t := |x| with htdef
  have ht : 0 ≤ t := abs_nonneg x
  have hx2 : x ^ 2 = t ^ 2 := (sq_abs x).symm
  have hx4 : x ^ 4 = t ^ 4 := by
    rw [htdef, ← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
  obtain ⟨p1, p2, p3⟩ := pow_le_one_add_pow_four ht
  have b1 : |u₁ x * x * (mA1 - mB1)| ≤ K * t * E := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hK1 x) ht) d1 (abs_nonneg _) (by positivity)
  have b2 : |u₂ x * x ^ 2 / 2 * (mA2 - mB2)| ≤ K * t ^ 2 / 2 * (4 * E) := by
    rw [abs_mul, abs_div, abs_mul, abs_two, abs_of_nonneg (sq_nonneg x), hx2]
    gcongr
    exact hK2 x
  have b3 : |u₃ x * x ^ 3 / 6 * (mA3 - mB3)| ≤ K * t ^ 3 / 6 * (9 * E) := by
    rw [abs_mul, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have : |mA3 - mB3| ≤ 9 * E := by
      refine (abs_sub _ _).trans ?_
      linarith
    gcongr
    exact hK3 x
  have hA4 : 0 ≤ K * x ^ 4 / 24 := by positivity
  have r1 := abs_le.1 TA
  have r2 := abs_le.1 TB
  have s1 := abs_le.1 b1
  have s2 := abs_le.1 b2
  have s3 := abs_le.1 b3
  have q4A : K * x ^ 4 / 24 * mA4 ≤ K * x ^ 4 / 24 * (4 * E) := mul_le_mul_of_nonneg_left a4 hA4
  have q4B : K * x ^ 4 / 24 * mB4 ≤ K * x ^ 4 / 24 * (7 * E) := mul_le_mul_of_nonneg_left b4 hA4
  have key : IA - IB = (IA - (u x + u₁ x * x * mA1 + u₂ x * x ^ 2 / 2 * mA2 +
      u₃ x * x ^ 3 / 6 * mA3)) - (IB - (u x + u₁ x * x * mB1 + u₂ x * x ^ 2 / 2 * mB2 +
      u₃ x * x ^ 3 / 6 * mB3)) + u₁ x * x * (mA1 - mB1) + u₂ x * x ^ 2 / 2 * (mA2 - mB2) +
      u₃ x * x ^ 3 / 6 * (mA3 - mB3) := by ring
  have fin : K * t * E + K * t ^ 2 / 2 * (4 * E) + K * t ^ 3 / 6 * (9 * E) +
      K * x ^ 4 / 24 * (4 * E) + K * x ^ 4 / 24 * (7 * E) ≤ 5 * K * E * (1 + x ^ 4) := by
    rw [hx4]
    have hKE : 0 ≤ K * E := mul_nonneg hK hE
    linarith [mul_le_mul_of_nonneg_left p1 hKE, mul_le_mul_of_nonneg_left p2 hKE,
      mul_le_mul_of_nonneg_left p3 hKE, mul_nonneg hKE (pow_nonneg ht 4)]
  rw [key, abs_le]
  constructor <;> linarith

/-! ### The backward functions of geometric Brownian motion -/

/-- The weighted backward operator of GBM over one time step (Giles 2015, §5.1: the exact solution
`S_{t+h} = S_t B`, `B = e^{(r − σ²/2)h + σ√h Z}`): `Q_j f(x) = E[B^j f(xB)]`.  The backward function
`u(t, x) = E[g(x Y_{T−t})]` of the payoff `g` is `Q_0^k g` after `k` steps, and its `j`-th
derivative is `Q_j^k g^{(j)}` (`gbmBackOp_iterate_chain`). -/
noncomputable def gbmBackOp (r σ h : ℝ) (j : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ w, gbmExpFactor r σ h w ^ j * f (x * gbmExpFactor r σ h w) ∂gaussianReal 0 1

/-- The exact GBM step `B = e^{(r − σ²/2)h + σ√h Z}` is positive (Giles 2015, §5.1). -/
lemma gbmExpFactor_pos (r σ h w : ℝ) : 0 < gbmExpFactor r σ h w := Real.exp_pos _

/-- **Differentiation of the backward operator under the Gaussian integral** (Giles 2015, §5.1): if
`f' = f₁` with `|f₁| ≤ K`, then `(Q_j f)' = Q_{j+1} f₁`, i.e.
`d/dx E[B^j f(xB)] = E[B^{j+1} f₁(xB)]` (dominated by `K B^{j+1}`). -/
lemma hasDerivAt_gbmBackOp (r σ h : ℝ) (j : ℕ) {f f₁ : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f₁ x) x) {K : ℝ} (hK : ∀ x, |f₁ x| ≤ K) (x : ℝ) :
    HasDerivAt (gbmBackOp r σ h j f) (gbmBackOp r σ h (j + 1) f₁ x) x := by
  have hBm := measurable_gbmExpFactor r σ h
  have hf₁m : Measurable f₁ := by
    have e : f₁ = deriv f := funext fun x => (hf x).deriv.symm
    rw [e]
    exact measurable_deriv f
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hlin := abs_le_abs_zero_add_of_hasDerivAt hf hK
  have hint : Integrable (fun w => gbmExpFactor r σ h w ^ j * f (x * gbmExpFactor r σ h w))
      (gaussianReal 0 1) := by
    refine (((integrable_gbmExpFactor_pow r σ h j).const_mul |f 0|).add
      ((integrable_gbmExpFactor_pow r σ h (j + 1)).const_mul (K * |x|))).mono'
      ((hBm.pow_const j).mul (hfc.measurable.comp (hBm.const_mul x))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    have hB := gbmExpFactor_pos r σ h w
    have h1 := hlin (x * gbmExpFactor r σ h w)
    rw [abs_mul, abs_of_pos hB] at h1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hB j)]
    simp only [Pi.add_apply]
    calc gbmExpFactor r σ h w ^ j * |f (x * gbmExpFactor r σ h w)|
        ≤ gbmExpFactor r σ h w ^ j * (|f 0| + K * (|x| * gbmExpFactor r σ h w)) :=
          mul_le_mul_of_nonneg_left h1 (pow_pos hB j).le
      _ = _ := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun x w => gbmExpFactor r σ h w ^ j * f (x * gbmExpFactor r σ h w))
    (F' := fun x w => gbmExpFactor r σ h w ^ (j + 1) * f₁ (x * gbmExpFactor r σ h w))
    (bound := fun w => K * gbmExpFactor r σ h w ^ (j + 1)) (x₀ := x) Filter.univ_mem
    (Filter.Eventually.of_forall fun x' =>
      ((hBm.pow_const j).mul (hfc.measurable.comp (hBm.const_mul x'))).aestronglyMeasurable)
    hint ((hBm.pow_const (j + 1)).mul (hf₁m.comp (hBm.const_mul x))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w x' _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos (gbmExpFactor_pos r σ h w) _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hK _) (pow_pos (gbmExpFactor_pos r σ h w) _).le)
    ((integrable_gbmExpFactor_pow r σ h (j + 1)).const_mul K)
    (Filter.Eventually.of_forall fun w x' _ =>
      (((hf (x' * gbmExpFactor r σ h w)).comp x'
        (hasDerivAt_mul_const (gbmExpFactor r σ h w))).const_mul
        (gbmExpFactor r σ h w ^ j)).congr_deriv (by rw [pow_succ]; ring))
  exact key.2

/-- `E[B^j] ≤ e^{Λh}` with `Λ = 4|r| + 8σ²` for `j ≤ 4` and `h ≥ 0` (Giles 2015, §5.1). -/
lemma integral_gbmExpFactor_pow_le_four (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) {j : ℕ} (hj : j ≤ 4) :
    ∫ w, gbmExpFactor r σ h w ^ j ∂gaussianReal 0 1 ≤
      Real.exp ((4 * |r| + 8 * σ ^ 2) * h) := by
  rw [integral_gbmExpFactor_pow_eq r σ hh]
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hh)
  have hj' : (j : ℝ) ≤ 4 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hs : 0 ≤ σ ^ 2 := sq_nonneg σ
  have h1 : (j : ℝ) * r ≤ 4 * |r| := by
    calc (j : ℝ) * r ≤ j * |r| := mul_le_mul_of_nonneg_left (le_abs_self r) hj0
      _ ≤ 4 * |r| := mul_le_mul_of_nonneg_right hj' (abs_nonneg r)
  have h2 : (j : ℝ) * (j - 1) ≤ 16 := by nlinarith
  nlinarith

/-- **The derivatives of the backward functions of GBM** (Giles 2015, §5.1).  Let `G_0, …, G_4` be
a chain of derivatives (`G_j' = G_{j+1}` for `j < 4`) with `|G_j| ≤ K` for `1 ≤ j ≤ 4`, and `h ≥ 0`.
Then after `k` steps `(Q_j^k G_j)' = Q_{j+1}^k G_{j+1}` for `j < 4`, and
`|Q_j^k G_j| ≤ K e^{Λhk}`, `Λ = 4|r| + 8σ²`, for `1 ≤ j ≤ 4`. -/
lemma gbmBackOp_iterate_chain (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) {G : ℕ → ℝ → ℝ}
    (hG : ∀ j < 4, ∀ x, HasDerivAt (G j) (G (j + 1) x) x) {K : ℝ}
    (hK : ∀ j, 1 ≤ j → j ≤ 4 → ∀ x, |G j x| ≤ K) (k : ℕ) :
    (∀ j < 4, ∀ x, HasDerivAt ((gbmBackOp r σ h j)^[k] (G j))
      ((gbmBackOp r σ h (j + 1))^[k] (G (j + 1)) x) x) ∧
    (∀ j, 1 ≤ j → j ≤ 4 → ∀ x, |(gbmBackOp r σ h j)^[k] (G j) x| ≤
      K * Real.exp ((4 * |r| + 8 * σ ^ 2) * h) ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun j hj x => hG j hj x, fun j hj1 hj4 x => ?_⟩
    simpa using hK j hj1 hj4 x
  | succ k ih =>
    obtain ⟨hd, hb⟩ := ih
    refine ⟨fun j hj x => ?_, fun j hj1 hj4 x => ?_⟩
    · rw [Function.iterate_succ', Function.iterate_succ']
      exact hasDerivAt_gbmBackOp r σ h j (hd j hj) (hb (j + 1) (by omega) (by omega)) x
    · rw [Function.iterate_succ', Function.comp_apply]
      set e := Real.exp ((4 * |r| + 8 * σ ^ 2) * h)
      have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK j hj1 hj4 0)
      have hint := (integrable_gbmExpFactor_pow r σ h j).const_mul (K * e ^ k)
      have hle := norm_integral_le_of_norm_le (f := fun w => gbmExpFactor r σ h w ^ j *
          (gbmBackOp r σ h j)^[k] (G j) (x * gbmExpFactor r σ h w)) hint
        (Filter.Eventually.of_forall fun w => by
          have hB := gbmExpFactor_pos r σ h w
          calc ‖gbmExpFactor r σ h w ^ j *
                (gbmBackOp r σ h j)^[k] (G j) (x * gbmExpFactor r σ h w)‖
              = gbmExpFactor r σ h w ^ j *
                  |(gbmBackOp r σ h j)^[k] (G j) (x * gbmExpFactor r σ h w)| := by
                rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hB j)]
            _ ≤ gbmExpFactor r σ h w ^ j * (K * e ^ k) :=
                mul_le_mul_of_nonneg_left (hb j hj1 hj4 _) (pow_pos hB j).le
            _ = K * e ^ k * gbmExpFactor r σ h w ^ j := by ring)
      rw [integral_const_mul] at hle
      have hE := integral_gbmExpFactor_pow_le_four r σ hh hj4
      calc |gbmBackOp r σ h j ((gbmBackOp r σ h j)^[k] (G j)) x|
          ≤ K * e ^ k * ∫ w, gbmExpFactor r σ h w ^ j ∂gaussianReal 0 1 := hle
        _ ≤ K * e ^ k * e := mul_le_mul_of_nonneg_left hE (by positivity)
        _ = K * e ^ (k + 1) := by ring

/-! ### Independence of the increments -/

/-- **The last increment is independent of the past** (Giles 2015, §5.1: the Brownian increments of
the successive time steps are independent).  If `X` depends only on `Z_0, …, Z_{n−1}` and is
integrable, `F(Z)` is integrable and `|f(y)| ≤ a + b|y|`, then
`E[f(X F(Z_n))] = E[φ(X)]` with `φ(x) = E[f(x F(Z))]`, `Z ∼ N(0,1)` (Fubini for the product law of
`(X, Z_n)`). -/
lemma integral_comp_mul_eval_eq {X : (ℕ → ℝ) → ℝ} (hX : Measurable X) {n : ℕ}
    (hdep : ∀ z z' : ℕ → ℝ, (∀ i < n, z i = z' i) → X z = X z')
    (hXi : Integrable X stdNormalSeq) {F : ℝ → ℝ} (hF : Measurable F)
    (hFi : Integrable F (gaussianReal 0 1)) {f : ℝ → ℝ} (hf : Measurable f) {a b : ℝ}
    (hfb : ∀ y, |f y| ≤ a + b * |y|) :
    ∫ z, f (X z * F (z n)) ∂stdNormalSeq =
      ∫ z, (∫ w, f (X z * F w) ∂gaussianReal 0 1) ∂stdNormalSeq := by
  set G : ℝ × ℝ → ℝ := fun p => f (p.1 * F p.2) with hG
  have hGm : Measurable G := hf.comp (measurable_fst.mul (hF.comp measurable_snd))
  have hind := indepFun_incr_of_eq_lt hX hdep
  have hev : Measurable (fun z : ℕ → ℝ => z n) := measurable_pi_apply n
  have hpm : Measurable (fun z => (X z, z n)) := hX.prodMk hev
  have hmap : stdNormalSeq.map (fun z => (X z, z n)) =
      (stdNormalSeq.map X).prod (gaussianReal 0 1) := by
    rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hev.aemeasurable]
    congr 1
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) n).map_eq
  have hint : Integrable (fun z => f (X z * F (z n))) stdNormalSeq := by
    have hXF := integrable_mul_comp_eval_of_eq_lt (A := fun z => |X z|) hX.abs
      (fun z z' h => by rw [hdep z z' h]) hF.abs hXi.abs hFi.abs
    refine ((integrable_const a).add (hXF.const_mul b)).mono'
      (hGm.comp hpm).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    refine (hfb _).trans (le_of_eq ?_)
    simp only [Pi.add_apply, abs_mul]
  have hGi : Integrable G ((stdNormalSeq.map X).prod (gaussianReal 0 1)) := by
    rw [← hmap, integrable_map_measure hGm.aestronglyMeasurable hpm.aemeasurable]
    exact hint
  calc ∫ z, f (X z * F (z n)) ∂stdNormalSeq
      = ∫ p, G p ∂(stdNormalSeq.map (fun z => (X z, z n))) := by
        rw [integral_map hpm.aemeasurable hGm.aestronglyMeasurable]
    _ = ∫ x, ∫ w, G (x, w) ∂gaussianReal 0 1 ∂(stdNormalSeq.map X) := by
        rw [hmap, integral_prod G hGi]
    _ = _ := by
        rw [integral_map hX.aemeasurable]
        exact (hGm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable

/-- `x ↦ E[f(x F(Z))]` is measurable for measurable `f`, `F` (the one-step operators of Giles 2015,
§5.1). -/
lemma measurable_integral_comp_mul {F : ℝ → ℝ} (hF : Measurable F) {f : ℝ → ℝ}
    (hf : Measurable f) : Measurable fun x => ∫ w, f (x * F w) ∂gaussianReal 0 1 := by
  have h : Measurable fun p : ℝ × ℝ => f (p.1 * F p.2) :=
    hf.comp (measurable_fst.mul (hF.comp measurable_snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- One step preserves linear growth: if `|f(y)| ≤ a + b|y|`, then
`|E[f(x F(Z))]| ≤ a + b E|F(Z)| |x|` (Giles 2015, §5.1). -/
lemma abs_integral_comp_mul_le {F : ℝ → ℝ} (hFi : Integrable F (gaussianReal 0 1)) {f : ℝ → ℝ}
    {a b : ℝ} (hfb : ∀ y, |f y| ≤ a + b * |y|) (x : ℝ) :
    |∫ w, f (x * F w) ∂gaussianReal 0 1| ≤
      a + (b * ∫ w, |F w| ∂gaussianReal 0 1) * |x| := by
  have hg : Integrable (fun w => a + b * |x| * |F w|) (gaussianReal 0 1) :=
    (integrable_const a).add (hFi.abs.const_mul _)
  have h := norm_integral_le_of_norm_le (f := fun w => f (x * F w)) hg
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]
      refine (hfb _).trans (le_of_eq ?_)
      rw [abs_mul]
      ring)
  rw [integral_add (integrable_const a) (hFi.abs.const_mul _), integral_const, probReal_univ,
    one_smul, integral_const_mul] at h
  calc _ = ‖∫ w, f (x * F w) ∂gaussianReal 0 1‖ := (Real.norm_eq_abs _).symm
    _ ≤ _ := h
    _ = _ := by ring

/-- `φ(X)` is integrable for measurable `φ` of linear growth and integrable `X` (Giles 2015,
§5.1). -/
lemma integrable_comp_of_abs_le {X : (ℕ → ℝ) → ℝ} (hX : Measurable X)
    (hXi : Integrable X stdNormalSeq) {φ : ℝ → ℝ} (hφ : Measurable φ) {a b : ℝ}
    (hb : ∀ y, |φ y| ≤ a + b * |y|) : Integrable (fun z => φ (X z)) stdNormalSeq :=
  ((integrable_const a).add (hXi.abs.const_mul b)).mono' (hφ.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]
      exact hb _)

/-- `S_0 ∏_{i<k} F(Z_i)` is integrable if `F(Z)` is (the GBM paths, Giles 2015, §5.1). -/
lemma integrable_mul_prod_stdNormalSeq {F : ℝ → ℝ} (hF : Measurable F)
    (hFi : Integrable F (gaussianReal 0 1)) (s₀ : ℝ) (k : ℕ) :
    Integrable (fun z : ℕ → ℝ => s₀ * ∏ i ∈ range k, F (z i)) stdNormalSeq :=
  (integrable_prod_stdNormalSeq hF hFi k).const_mul s₀

/-- **The exact solution through the backward operator** (Giles 2015, §5.1): for measurable `f` of
linear growth, `E[f(S_0 ∏_{i<k} B_i)] = Q_0^k f(S_0)`, i.e. `E[g(S_{t_k})]` is the backward function
`u(0, S_0)` of `g` (by induction on `k`, peeling off the last step with
`integral_comp_mul_eval_eq`). -/
lemma integral_comp_gbmExp_prod_eq (r σ h s₀ : ℝ) (k : ℕ) :
    ∀ f : ℝ → ℝ, Measurable f → (∃ a b : ℝ, ∀ y, |f y| ≤ a + b * |y|) →
      ∫ z, f (s₀ * ∏ i ∈ range k, gbmExpFactor r σ h (z i)) ∂stdNormalSeq =
        (gbmBackOp r σ h 0)^[k] f s₀ := by
  have hBm := measurable_gbmExpFactor r σ h
  have hBi := integrable_gbmExpFactor r σ h
  have e0 : ∀ f : ℝ → ℝ, gbmBackOp r σ h 0 f =
      fun x => ∫ w, f (x * gbmExpFactor r σ h w) ∂gaussianReal 0 1 := fun f => by
    funext x
    simp [gbmBackOp]
  induction k with
  | zero =>
    intro f _ _
    simp
  | succ k ih =>
    intro f hf ⟨a, b, hab⟩
    have hX : Measurable fun z : ℕ → ℝ => s₀ * ∏ i ∈ range k, gbmExpFactor r σ h (z i) :=
      (measurable_prod_range hBm k).const_mul s₀
    have e1 : ∀ z : ℕ → ℝ, s₀ * ∏ i ∈ range (k + 1), gbmExpFactor r σ h (z i) =
        (s₀ * ∏ i ∈ range k, gbmExpFactor r σ h (z i)) * gbmExpFactor r σ h (z k) := fun z => by
      rw [prod_range_succ, mul_assoc]
    simp_rw [e1]
    rw [integral_comp_mul_eval_eq hX (fun z z' h => by rw [prod_range_eq_of_eq_lt _ h])
      (integrable_mul_prod_stdNormalSeq hBm hBi s₀ k) hBm hBi hf hab,
      Function.iterate_succ_apply, e0 f]
    exact ih _ (measurable_integral_comp_mul hBm hf)
      ⟨a, b * ∫ w, |gbmExpFactor r σ h w| ∂gaussianReal 0 1, abs_integral_comp_mul_le hBi hab⟩

/-! ### Weak order one for smooth payoffs -/

/-- `E[A⁴] ≤ e^{(4|r| + 8σ²)h}` for the Euler–Maruyama step `A` of GBM and `h ≥ 0` (Giles 2015,
§5.1). -/
lemma integral_gbmEMFactor_pow_four_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ x, gbmEMFactor r σ h x ^ 4 ∂gaussianReal 0 1 ≤ Real.exp ((4 * |r| + 8 * σ ^ 2) * h) := by
  refine (le_abs_self _).trans ((abs_integral_gbmEMFactor_pow_le r σ hh 4).trans (le_of_eq ?_))
  congr 1
  push_cast
  ring

/-- The constant of the weak error of the Euler–Maruyama scheme for GBM with a smooth payoff (Giles
2015, §5.1): `C(t) = 5KΛ²(1 + S_0⁴) t e^{Λt}` with `Λ = 4|r| + 8σ²`, where `K` bounds the first four
derivatives of the payoff.  It is explicit but neither sharp nor scale invariant (see the module
docstring). -/
noncomputable def gbmWeakSmoothConst (K r σ s₀ t : ℝ) : ℝ :=
  5 * K * (4 * |r| + 8 * σ ^ 2) ^ 2 * (1 + s₀ ^ 4) * t * Real.exp ((4 * |r| + 8 * σ ^ 2) * t)

/-- **Weak order one for smooth payoffs, in product form** (Giles 2015, §5.1): if `g` is four times
differentiable with `|g^{(k)}| ≤ K` for `1 ≤ k ≤ 4` and `h ≥ 0`, then
`|E[g(S_0 ∏_{i<n} A_i)] − E[g(S_0 ∏_{i<n} B_i)]| ≤ C(nh) h` (`gbmWeakSmoothConst`).  Telescoping
over the steps with the backward functions `u_k = Q_0^k g`:
`E[g(Ŝ_n)] − u_n(S_0) = ∑_{j<n} E[(E_A u_{n−j−1} − E_B u_{n−j−1})(Ŝ_j)]`, each term bounded by
`gbm_one_step_weak_le` with the derivative bounds of `gbmBackOp_iterate_chain`. -/
lemma gbm_weak_error_smooth_prod (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) {g : ℝ → ℝ}
    (hg : ∀ k < 4, Differentiable ℝ (iteratedDeriv k g)) {K : ℝ}
    (hK : ∀ k, 1 ≤ k → k ≤ 4 → ∀ x, |iteratedDeriv k g x| ≤ K) :
    |∫ z, g (s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i)) ∂stdNormalSeq -
        ∫ z, g (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i)) ∂stdNormalSeq| ≤
      gbmWeakSmoothConst K r σ s₀ (n * h) * h := by
  set Λ : ℝ := 4 * |r| + 8 * σ ^ 2 with hΛdef
  set e : ℝ := Real.exp (Λ * h) with hedef
  have hΛ : 0 ≤ Λ := by positivity
  have he1 : 1 ≤ e := Real.one_le_exp (mul_nonneg hΛ hh)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 1 le_rfl (by norm_num) 0)
  set G : ℕ → ℝ → ℝ := fun j => iteratedDeriv j g with hGdef
  have hG : ∀ j < 4, ∀ x, HasDerivAt (G j) (G (j + 1) x) x := fun j hj x => by
    simp only [hGdef]
    rw [iteratedDeriv_succ]
    exact ((hg j hj) x).hasDerivAt
  have hG0 : G 0 = g := iteratedDeriv_zero
  have chain := gbmBackOp_iterate_chain r σ hh hG hK
  set U : ℕ → ℝ → ℝ := fun k => (gbmBackOp r σ h 0)^[k] g with hUdef
  have hU1 : ∀ k x, HasDerivAt (U k) ((gbmBackOp r σ h 1)^[k] (G 1) x) x := fun k x => by
    have := (chain k).1 0 (by norm_num) x
    rw [hG0] at this
    exact this
  have hUb : ∀ k x, |(gbmBackOp r σ h 1)^[k] (G 1) x| ≤ K * e ^ k := fun k x =>
    (chain k).2 1 le_rfl (by norm_num) x
  have hUm : ∀ k, Measurable (U k) := fun k =>
    (continuous_iff_continuousAt.2 fun x => (hU1 k x).continuousAt).measurable
  have hUlin : ∀ k y, |U k y| ≤ |U k 0| + K * e ^ k * |y| := fun k y =>
    abs_le_abs_zero_add_of_hasDerivAt (hU1 k) (hUb k) y
  have hstep : ∀ k x, |∫ w, U k (x * gbmEMFactor r σ h w) ∂gaussianReal 0 1 -
      ∫ w, U k (x * gbmExpFactor r σ h w) ∂gaussianReal 0 1| ≤
      5 * (K * e ^ k) * (Λ ^ 2 * h ^ 2 * e) * (1 + x ^ 4) := fun k x => by
    obtain ⟨hd, hb⟩ := chain k
    exact gbm_one_step_weak_le r σ hh (hU1 k) (hd 1 (by norm_num)) (hd 2 (by norm_num))
      (hd 3 (by norm_num)) (hb 1 le_rfl (by norm_num)) (hb 2 (by norm_num) (by norm_num))
      (hb 3 (by norm_num) (by norm_num)) (hb 4 (by norm_num) le_rfl) x
  have hAm := measurable_gbmEMFactor r σ h
  have hAi := integrable_gbmEMFactor r σ h
  have hBm := measurable_gbmExpFactor r σ h
  have hBi := integrable_gbmExpFactor r σ h
  set X : ℕ → (ℕ → ℝ) → ℝ := fun j z => s₀ * ∏ i ∈ range j, gbmEMFactor r σ h (z i) with hXdef
  have hXm : ∀ j, Measurable (X j) := fun j => (measurable_prod_range hAm j).const_mul s₀
  have hXi : ∀ j, Integrable (X j) stdNormalSeq := fun j =>
    integrable_mul_prod_stdNormalSeq hAm hAi s₀ j
  have hXdep : ∀ j, ∀ z z' : ℕ → ℝ, (∀ i < j, z i = z' i) → X j z = X j z' :=
    fun j z z' h' => by
    simp only [hXdef]
    rw [prod_range_eq_of_eq_lt _ h']
  have hX4 : ∀ j, Integrable (fun z => X j z ^ 4) stdNormalSeq := fun j => by
    simp only [hXdef, mul_pow, ← prod_pow]
    exact (integrable_prod_stdNormalSeq (F := fun x => gbmEMFactor r σ h x ^ 4)
      (hAm.pow_const 4) (integrable_affine_pow_gaussian _ _ 4) j).const_mul _
  have hX4int : ∀ j, ∫ z, X j z ^ 4 ∂stdNormalSeq ≤ s₀ ^ 4 * e ^ j := fun j => by
    simp only [hXdef, mul_pow, ← prod_pow]
    rw [integral_const_mul, integral_prod_stdNormalSeq (F := fun x => gbmEMFactor r σ h x ^ 4)
      (hAm.pow_const 4)]
    have h0 : 0 ≤ ∫ x, gbmEMFactor r σ h x ^ 4 ∂gaussianReal 0 1 :=
      integral_nonneg fun x => by positivity
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ h0 (integral_gbmEMFactor_pow_four_le r σ hh) j) (by positivity)
  set φ : ℕ → ℝ := fun j => ∫ z, U (n - j) (X j z) ∂stdNormalSeq with hφdef
  have hφn : φ n = ∫ z, g (s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i)) ∂stdNormalSeq := by
    simp only [hφdef, Nat.sub_self]
    rfl
  have hφ0 : φ 0 = ∫ z, g (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i)) ∂stdNormalSeq := by
    have hlin0 : ∀ y, |g y| ≤ |g 0| + K * |y| := fun y => by
      have := hUlin 0 y
      rw [pow_zero, mul_one] at this
      exact this
    rw [integral_comp_gbmExp_prod_eq r σ h s₀ n g (hUm 0) ⟨|g 0|, K, hlin0⟩]
    simp only [hφdef, Nat.sub_zero, hXdef, prod_range_zero, mul_one, integral_const,
      probReal_univ, one_smul]
    rfl
  have hterm : ∀ j ∈ range n, |φ (j + 1) - φ j| ≤
      5 * K * (Λ ^ 2 * h ^ 2) * (1 + s₀ ^ 4) * e ^ n := fun j hj => by
    obtain ⟨k, hk⟩ : ∃ k, n = j + 1 + k := ⟨n - (j + 1), by have := mem_range.1 hj; omega⟩
    have e1 : n - (j + 1) = k := by omega
    have e2 : n - j = k + 1 := by omega
    have hXs : ∀ z, X (j + 1) z = X j z * gbmEMFactor r σ h (z j) := fun z => by
      simp only [hXdef]
      rw [prod_range_succ, mul_assoc]
    have hlin : ∀ y, |U k y| ≤ |U k 0| + K * e ^ k * |y| := hUlin k
    have hPA := integral_comp_mul_eval_eq (hXm j) (hXdep j) (hXi j) hAm hAi (hUm k) hlin
    have hφ1 : φ (j + 1) = ∫ z, (∫ w, U k (X j z * gbmEMFactor r σ h w) ∂gaussianReal 0 1)
        ∂stdNormalSeq := by
      simp only [hφdef, e1, hXs]
      exact hPA
    have hφ2 : φ j = ∫ z, (∫ w, U k (X j z * gbmExpFactor r σ h w) ∂gaussianReal 0 1)
        ∂stdNormalSeq := by
      simp only [hφdef, e2, hUdef]
      congr 1
      funext z
      rw [Function.iterate_succ_apply']
      simp [gbmBackOp]
    have iA := integrable_comp_of_abs_le (hXm j) (hXi j)
      (measurable_integral_comp_mul hAm (hUm k)) (abs_integral_comp_mul_le hAi hlin)
    have iB := integrable_comp_of_abs_le (hXm j) (hXi j)
      (measurable_integral_comp_mul hBm (hUm k)) (abs_integral_comp_mul_le hBi hlin)
    have hbd : Integrable (fun z => 5 * (K * e ^ k) * (Λ ^ 2 * h ^ 2 * e) * (1 + X j z ^ 4))
        stdNormalSeq := ((integrable_const 1).add (hX4 j)).const_mul _
    rw [hφ1, hφ2, ← integral_sub iA iB, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hbd (Filter.Eventually.of_forall fun z => ?_)).trans ?_
    · rw [Real.norm_eq_abs]
      exact hstep k (X j z)
    · rw [integral_const_mul, integral_add (integrable_const 1) (hX4 j), integral_const,
        probReal_univ, one_smul]
      have h4 := hX4int j
      have hej : e ^ (k + 1) * e ^ j = e ^ n := by rw [← pow_add, hk]; ring_nf
      have hek : e ^ (k + 1) ≤ e ^ n := pow_le_pow_right₀ he1 (by omega)
      have hc : 0 ≤ 5 * K * (Λ ^ 2 * h ^ 2) := by positivity
      calc 5 * (K * e ^ k) * (Λ ^ 2 * h ^ 2 * e) * (1 + ∫ z, X j z ^ 4 ∂stdNormalSeq)
          ≤ 5 * (K * e ^ k) * (Λ ^ 2 * h ^ 2 * e) * (1 + s₀ ^ 4 * e ^ j) := by gcongr
        _ = 5 * K * (Λ ^ 2 * h ^ 2) * (e ^ (k + 1) + s₀ ^ 4 * (e ^ (k + 1) * e ^ j)) := by ring
        _ ≤ 5 * K * (Λ ^ 2 * h ^ 2) * (e ^ n + s₀ ^ 4 * e ^ n) := by
          rw [hej]
          gcongr
        _ = _ := by ring
  rw [← hφn, ← hφ0, ← sum_range_sub φ n]
  calc |∑ j ∈ range n, (φ (j + 1) - φ j)| ≤ ∑ j ∈ range n, |φ (j + 1) - φ j| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range n, 5 * K * (Λ ^ 2 * h ^ 2) * (1 + s₀ ^ 4) * e ^ n := sum_le_sum hterm
    _ = _ := by
        rw [sum_const, card_range, nsmul_eq_mul, gbmWeakSmoothConst, ← hΛdef, hedef,
          ← Real.exp_nat_mul]
        ring_nf

/-- **Weak order one of the Euler–Maruyama scheme for GBM with a smooth payoff, at every grid time**
(Giles 2015, §5.1, p. 30, l. 1317–1320: "If `h_ℓ = 4^{−ℓ}h_0` … then this gives `α = 2` … if
`h_ℓ = 2^{−ℓ}h_0` … then `α = 1`", i.e. the weak error is `O(h)`).  Let `g : ℝ → ℝ` be four times
differentiable with `|g^{(k)}(x)| ≤ K` for `k = 1, …, 4` and all `x` (for instance `g` of class
`C⁴` with bounded derivatives), `h ≥ 0` and `n ∈ ℕ`.  Then the Euler–Maruyama value `Ŝ_n` and the
exact solution `S_{t_n} = S_0 e^{(r − σ²/2)t_n + σW_{t_n}}`, `t_n = nh`, `W_{t_n} = √h ∑_{i<n} Z_i`,
satisfy `|E[g(Ŝ_n)] − E[g(S_{t_n})]| ≤ C(t_n) h` with `C(t) = 5KΛ²(1 + S_0⁴) t e^{Λt}`,
`Λ = 4|r| + 8σ²` (`gbmWeakSmoothConst`).  Deviation: the paper uses this rate for the call option,
which is not smooth; non-smooth payoffs are not covered. -/
theorem gbm_em_weak_error_smooth (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) {g : ℝ → ℝ}
    (hg : ∀ k < 4, Differentiable ℝ (iteratedDeriv k g)) {K : ℝ}
    (hK : ∀ k, 1 ≤ k → k ≤ 4 → ∀ x, |iteratedDeriv k g x| ≤ K) :
    |∫ z, g (emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ∂stdNormalSeq -
        ∫ z, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
          σ * (Real.sqrt h * ∑ i ∈ range n, z i))) ∂stdNormalSeq| ≤
      gbmWeakSmoothConst K r σ s₀ (n * h) * h := by
  simp_rw [emPath_gbm, gbmExp_eq_prod]
  exact gbm_weak_error_smooth_prod r σ s₀ hh n hg hK

/-- **Weak order one on level `ℓ` for smooth payoffs** (Giles 2015, §5.1, p. 30, l. 1318–1320:
"if `h_ℓ = 2^{−ℓ}h_0` with twice as many timesteps on each successive level … then `α = 1`").  For
`g` as in `gbm_em_weak_error_smooth`, `T ≥ 0` and every level `ℓ`, the level-`ℓ` Euler–Maruyama
approximation (`2^ℓ` steps of size `h_ℓ = T 2^{−ℓ}`) and the exact solution driven by the same
increments satisfy `|E[g(Ŝ_ℓ)] − E[g(S_T)]| ≤ C(T) h_ℓ` (`gbmWeakSmoothConst`). -/
theorem gbm_weak_error_smooth (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ : ℕ) {g : ℝ → ℝ}
    (hg : ∀ k < 4, Differentiable ℝ (iteratedDeriv k g)) {K : ℝ}
    (hK : ∀ k, 1 ≤ k → k ≤ 4 → ∀ x, |iteratedDeriv k g x| ≤ K) :
    |∫ z, g (gbmEM r σ T s₀ ℓ z) ∂stdNormalSeq - ∫ z, g (gbmExact r σ T s₀ ℓ z) ∂stdNormalSeq| ≤
      gbmWeakSmoothConst K r σ s₀ T * (T / 2 ^ ℓ) := by
  have h := gbm_em_weak_error_smooth r σ s₀ (div_nonneg hT (by positivity : (0 : ℝ) ≤ 2 ^ ℓ))
    (2 ^ ℓ) hg hK
  rw [cast_two_pow_mul_div] at h
  exact h

/-! ### Theorem 1 with a bound on the finest level -/

/-- **Theorem 1 for fine and coarse approximations, with a bound on the finest level** (Giles 2015,
§2.1, Theorem 1 with (2.4), and the discussion of its proof, p. 7, l. 326: "Because of condition
i), we have `2^{−αL} = O(ε)`, and hence `C_L = O(ε^{−γ/α})`", said there for `β < γ`; the choice
of `L` is the same in every regime).  Under the hypotheses of `giles_theorem1_fineCoarse` (its
`β > 0` is not needed), with a deterministic cost `C_ℓ` per level-`ℓ` sample, there is `c₄ > 0`
such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel
estimator has a square-integrable error with mean square `< ε²`, cost
`∑_{ℓ≤L} N_ℓ C_ℓ ≤ c₄ · complexityBound α β γ ε`, and finest level `2^{αL} ≤ K/ε` with
`K = 2^α (1 + 2c₁)` (`K1`): the weak rate `α` fixes the number of levels.  This is the construction
of `mlmc_complexity_core` (`exists_L_N`, `cost_le_of_level`) with the bound on `L` kept. -/
lemma giles_theorem1_fineCoarse_levels {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω]
    {ν : Measure Ω₀} {μ : Measure Ω} [IsProbabilityMeasure μ] (P : Ω₀ → ℝ)
    (Pf Pc : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (C : ℕ → ℝ) {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α)
    (hγ : 0 < γ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) (hP : Integrable P ν)
    (hPfm : ∀ ℓ, Measurable (Pf ℓ)) (hPcm : ∀ ℓ, Measurable (Pc ℓ))
    (hPf : ∀ ℓ, MemLp (Pf ℓ) 2 ν) (hPc : ∀ ℓ, MemLp (Pc ℓ) 2 ν)
    (h24 : ∀ ℓ, ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν)
    (h_i : ∀ ℓ : ℕ, |∫ y, Pf ℓ y - P y ∂ν| ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance (fineCoarseDiff Pf Pc ℓ) ν ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ) x -
          ∫ y, P y ∂ν) ^ 2) μ ∧
        ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ) x -
          ∫ y, P y ∂ν) ^ 2 ∂μ < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ c₄ * complexityBound α β γ ε ∧
        (2 : ℝ) ^ (α * (L : ℝ)) ≤ K1 α c₁ / ε := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  obtain ⟨c₄, hc₄, hcost⟩ := cost_le_of_level (β := β) hα hγ hc₂ hc₃ (K1_pos (α := α) hc₁) hαβγ
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hbias, hvar, hcost', hL, -⟩ :=
    exists_L_N (β := β) (γ := γ) hα hc₁ hc₂ hc₃ hε hε1
  have hΔ : ∀ ℓ, MemLp (fineCoarseDiff Pf Pc ℓ) 2 ν := memLp_fineCoarseDiff hPf hPc
  have hΔm : ∀ ℓ, Measurable (fineCoarseDiff Pf Pc ℓ) := measurable_fineCoarseDiff hPfm hPcm
  have hΔ1 : ∀ ℓ, Integrable (fineCoarseDiff Pf Pc ℓ) ν := fun ℓ => (hΔ ℓ).integrable one_le_two
  have hPf1 : ∀ ℓ, Integrable (Pf ℓ) ν := fun ℓ => (hPf ℓ).integrable one_le_two
  have hPc1 : ∀ ℓ, Integrable (Pc ℓ) ν := fun ℓ => (hPc ℓ).integrable one_le_two
  have hY : ∀ ℓ, MemLp (blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ)) 2 μ :=
    fun ℓ => memLp_blockMean hω hΔ ℓ (N ℓ)
  have hD : MemLp (fun x => ∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ) x -
      ∫ y, P y ∂ν) 2 μ :=
    (memLp_finsetSum _ fun ℓ _ => hY ℓ).sub (memLp_const _)
  refine ⟨L, N, hN, hD.integrable_sq, ?_, ?_, hL⟩
  · -- the mean square error, `MSE = ∑_ℓ V[Y_ℓ] + (E[P_L] − E[P])²` (Giles (2.1), (2.3))
    have tr : ∀ f : Ω₀ → ℝ, Integrable f ν → ∫ x, f (ω (0, 0) x) ∂μ = ∫ y, f y ∂ν :=
      fun f hf => integral_comp_of_measurePreserving (hω (0, 0)) hf.aestronglyMeasurable
    have hPlμ : ∀ ℓ, Integrable (fun x => Pf ℓ (ω (0, 0) x)) μ :=
      fun ℓ => ((hω (0, 0)).integrable_comp (hPf1 ℓ).aestronglyMeasurable).2 (hPf1 ℓ)
    have hind' : Set.Pairwise ↑(range (L + 1)) fun i j =>
        IndepFun (blockMean (fineCoarseDiff Pf Pc) ω i (N i))
          (blockMean (fineCoarseDiff Pf Pc) ω j (N j)) μ :=
      fun i _ j _ hij => indepFun_blockMean (fun p => (hω p).measurable) hind hΔm hij _ _
    have h0 : ∫ x, blockMean (fineCoarseDiff Pf Pc) ω 0 (N 0) x ∂μ =
        ∫ x, Pf 0 (ω (0, 0) x) ∂μ := by
      rw [integral_blockMean hω hΔ1 0 (hN 0), tr (Pf 0) (hPf1 0)]
      rfl
    have hs : ∀ ℓ, ∫ x, blockMean (fineCoarseDiff Pf Pc) ω (ℓ + 1) (N (ℓ + 1)) x ∂μ =
        ∫ x, Pf (ℓ + 1) (ω (0, 0) x) - Pf ℓ (ω (0, 0) x) ∂μ := fun ℓ => by
      rw [integral_blockMean hω hΔ1 (ℓ + 1) (hN (ℓ + 1)),
        integral_fineCoarseDiff hPf1 hPc1 h24 (ℓ + 1),
        tr (fun y => Pf (ℓ + 1) y - Pf ℓ y) ((hPf1 (ℓ + 1)).sub (hPf1 ℓ)), levelDiff_succ]
    have hmse := mlmc_mse (fun ℓ x => Pf ℓ (ω (0, 0) x))
      (fun ℓ => blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ)) L (∫ y, P y ∂ν) hY hPlμ hind' h0 hs
    have hb : (∫ y, Pf L y ∂ν - ∫ y, P y ∂ν) ^ 2 ≤ (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := by
      have h := h_i L
      rw [integral_sub (hPf1 L) hP] at h
      exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
    have hv : ∑ ℓ ∈ range (L + 1), variance (blockMean (fineCoarseDiff Pf Pc) ω ℓ (N ℓ)) μ ≤
        ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) := by
      refine sum_le_sum fun ℓ _ => ?_
      rw [variance_blockMean hω hind hΔm hΔ ℓ (hN ℓ)]
      exact div_le_div_of_nonneg_right (h_iii ℓ) (by positivity)
    have hL' : ∫ x, Pf L (ω (0, 0) x) ∂μ = ∫ y, Pf L y ∂ν := tr (Pf L) (hPf1 L)
    have hε2 := pow_pos hε 2
    simp only at hmse
    rw [hmse, hL']
    linarith
  · -- the cost
    calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ
        ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ :=
          sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (h_iv ℓ) (by positivity)
      _ ≤ c₄ * complexityBound α β γ ε := hcost'.trans (hcost ε hε hε1 L hL)

/-- **Theorem 1 for the Euler–Maruyama estimator with refinement factor `M`, with a bound on the
finest level** (Giles 2015, §2.1, Theorem 1 with (2.4), and §5.1, p. 29, l. 1281–1282: "On level
`ℓ`, the uniform timestep is taken to be `h_ℓ = h_0 M^ℓ` [read `h_0 M^{−ℓ}`], for some integer
`M`").  The estimator of `em_mlmc_theorem1_M`, with a deterministic cost `C_ℓ` per level-`ℓ`
sample: under (i), (iii) and (iv) with `α ≥ ½ min(β, γ)` there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with a square-integrable error, `MSE < ε²`,
`∑_{ℓ≤L} N_ℓ C_ℓ ≤ c₄ · complexityBound α β γ ε` and `2^{αL} ≤ K1 α c₁ / ε`
(`giles_theorem1_fineCoarse_levels`; (2.4) is `integral_emCoarseM`). -/
lemma em_mlmc_theorem1_levels_M {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (a b : ℝ → ℝ → ℝ) (h₀ S₀ : ℝ) {M : ℕ} (hM : 0 < M)
    (Φ : ℕ → (ℕ → ℝ) → ℝ) (P : (ℕ → ℝ) → ℝ) (ω : ℕ × ℕ → Ω → ℕ → ℝ) (C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α) (hω : ∀ p, MeasurePreserving (ω p) μ stdNormalSeq)
    (hind : iIndepFun ω μ) (hP : Integrable P stdNormalSeq)
    (hPfm : ∀ ℓ, Measurable (emFineM a b h₀ S₀ M Φ ℓ))
    (hPf : ∀ ℓ, MemLp (emFineM a b h₀ S₀ M Φ ℓ) 2 stdNormalSeq)
    (h_i : ∀ ℓ : ℕ, |∫ z, emFineM a b h₀ S₀ M Φ ℓ z - P z ∂stdNormalSeq| ≤
      c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance
      (fineCoarseDiff (emFineM a b h₀ S₀ M Φ) (emCoarseM a b h₀ S₀ M Φ) ℓ) stdNormalSeq ≤
        c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
          blockMean (fineCoarseDiff (emFineM a b h₀ S₀ M Φ) (emCoarseM a b h₀ S₀ M Φ)) ω ℓ
            (N ℓ) x - ∫ z, P z ∂stdNormalSeq) ^ 2) μ ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
          blockMean (fineCoarseDiff (emFineM a b h₀ S₀ M Φ) (emCoarseM a b h₀ S₀ M Φ)) ω ℓ
            (N ℓ) x - ∫ z, P z ∂stdNormalSeq) ^ 2 ∂μ < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ ≤ c₄ * complexityBound α β γ ε ∧
        (2 : ℝ) ^ (α * (L : ℝ)) ≤ K1 α c₁ / ε := by
  have hc : ∀ ℓ, emCoarseM a b h₀ S₀ M Φ ℓ = emFineM a b h₀ S₀ M Φ ℓ ∘ blockAvg M := fun ℓ =>
    funext (emCoarseM_eq a b h₀ S₀ hM Φ ℓ)
  have hPcm : ∀ ℓ, Measurable (emCoarseM a b h₀ S₀ M Φ ℓ) := fun ℓ => by
    rw [hc]
    exact (hPfm ℓ).comp (measurePreserving_blockAvg hM).measurable
  have hPc : ∀ ℓ, MemLp (emCoarseM a b h₀ S₀ M Φ ℓ) 2 stdNormalSeq := fun ℓ => by
    rw [hc]
    exact (hPf ℓ).comp_measurePreserving (measurePreserving_blockAvg hM)
  exact giles_theorem1_fineCoarse_levels P (emFineM a b h₀ S₀ M Φ) (emCoarseM a b h₀ S₀ M Φ) ω C
    hα hγ hc₁ hc₂ hc₃ hαβγ hω hind hP hPfm hPcm hPf hPc
    (fun ℓ => (integral_emCoarseM a b h₀ S₀ hM Φ ℓ (hPfm ℓ).aestronglyMeasurable).symm)
    h_i h_iii h_iv

/-! ### Theorem 1 with the paper's rates -/

/-- A payoff with `|g'| ≤ K` (and `g` differentiable) is continuous and `K`-Lipschitz, so the
variance results of Giles 2015, §5.1 for Lipschitz payoffs apply to it. -/
lemma continuous_lipschitz_of_iteratedDeriv {g : ℝ → ℝ}
    (hg : ∀ k < 4, Differentiable ℝ (iteratedDeriv k g)) {K : ℝ}
    (hK : ∀ k, 1 ≤ k → k ≤ 4 → ∀ x, |iteratedDeriv k g x| ≤ K) :
    Continuous g ∧ ∀ x y, |g x - g y| ≤ K * |x - y| := by
  have hd : Differentiable ℝ g := by simpa using hg 0 (by norm_num)
  have h1 : ∀ x, HasDerivAt g (iteratedDeriv 1 g x) x := fun x => by
    rw [iteratedDeriv_one]
    exact (hd x).hasDerivAt
  refine ⟨hd.continuous, fun x y => ?_⟩
  have := abs_le_of_hasDerivAt_le_pow (f := fun t => g (y + t) - g y)
    (f' := fun t => iteratedDeriv 1 g (y + t))
    (fun t => ((h1 (y + t)).comp_const_add y t).sub_const _)
    (by simp) (k := 0) (fun t => by simpa using hK 1 le_rfl (by norm_num) (y + t)) (x - y)
  simp only [zero_add, pow_one, Nat.cast_zero, div_one, add_sub_cancel] at this
  exact this

/-- **Weak order one for refinement factor `M`** (Giles 2015, §5.1, p. 29, l. 1281–1282: "On level
`ℓ`, the uniform timestep is taken to be `h_ℓ = h_0 M^ℓ` [read `h_0 M^{−ℓ}`], for some integer `M`",
and p. 30, l. 1317–1318: "If `h_ℓ = 4^{−ℓ}h_0` … then this gives `α = 2`").  For `g` as in
`gbm_em_weak_error_smooth`, `T ≥ 0`, `m, M ≥ 1`, `h_0 = T/m` and `h_ℓ = h_0 M^{−ℓ}`, the
Euler–Maruyama payoff after `m M^ℓ` steps of size `h_ℓ` (`emFineM`) satisfies
`|E[g(Ŝ_ℓ)] − E[g(S_T)]| ≤ C(T) h_ℓ` (`gbmWeakSmoothConst`), i.e. `α = log₂ M` in Theorem 1's
base `2`: the paper's weak rate, which improves `gbm_weak_error_le_M` (`α = ½ log₂ M`, for every
Lipschitz payoff). -/
theorem gbm_weak_error_smooth_M (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m M : ℕ} (hm : 0 < m)
    (hM : 0 < M) {g : ℝ → ℝ} (hg : ∀ k < 4, Differentiable ℝ (iteratedDeriv k g)) {K : ℝ}
    (hK : ∀ k, 1 ≤ k → k ≤ 4 → ∀ x, |iteratedDeriv k g x| ≤ K) (ℓ : ℕ) :
    |∫ z, emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))) ℓ z
        ∂stdNormalSeq -
      ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1| ≤
      gbmWeakSmoothConst K r σ s₀ T * (T / m / (M : ℝ) ^ ℓ) := by
  obtain ⟨hgc, -⟩ := continuous_lipschitz_of_iteratedDeriv hg hK
  have hh : 0 ≤ T / m / (M : ℝ) ^ ℓ := by positivity
  have H := gbm_em_weak_error_smooth r σ s₀ hh (m * M ^ ℓ) hg hK
  rw [cast_mul_pow_mul_div hm hM] at H
  change |∫ z, g (emPath (gbmDrift r) (gbmVol σ) (T / m / (M : ℝ) ^ ℓ) s₀ z (m * M ^ ℓ))
      ∂stdNormalSeq - ∫ z, g (gbmExactM r σ T s₀ m M ℓ z) ∂stdNormalSeq| ≤ _ at H
  rw [integral_comp_gbmExactM r σ T s₀ hm hM ℓ hgc.measurable] at H
  exact H

/-- **Theorem 1 for GBM with refinement factor `M` and a smooth payoff, with the paper's rates
`α = β = γ = log₂ M`** (Giles 2015, §5.1, p. 30, l. 1317–1321: "If `h_ℓ = 4^{−ℓ}h_0`, as in the
numerical examples in (Giles 2008b), then this gives `α = 2`, `β = 2` and `γ = 2` … In either case,
Theorem 1 gives the complexity to achieve a root-mean-square error of `ε` to be
`O(ε^{−2}(log ε)²)`"; §2.1, p. 7, l. 326: "Because of condition i), we have `2^{−αL} = O(ε)`, and
hence `C_L = O(ε^{−γ/α})`").  Let `dS = rS dt + σS dW`, `T ≥ 0`, `m ≥ 1`, `M ≥ 2`, and let `g` be
four times differentiable with `|g^{(k)}| ≤ K` for `k = 1, …, 4`.  Level `ℓ` uses `m M^ℓ`
Euler–Maruyama steps of size `h_ℓ = h_0 M^{−ℓ}`, `h_0 = T/m` (`emFineM`); the coarse path of a
level-`(ℓ+1)` sample is driven by the sums of `M` fine increments (`emCoarseM`); the samples are
independent and a level-`ℓ` sample costs `m M^ℓ`.  Then there are `c₄, c₅ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel estimator of `E[g(S_T)]` has a
square-integrable error with mean square `< ε²`, cost `∑_{ℓ≤L} N_ℓ m M^ℓ ≤ c₄ ε⁻²(log ε)²`, and
finest level `M^L ≤ c₅ ε⁻¹`, i.e. `m M^L = O(ε⁻¹)` time steps on the finest level (the paper's
`C_L = O(ε^{−γ/α})` with `γ/α = 1`).  The rates are the paper's, in Theorem 1's base `2`:
`α = log₂ M` (`gbm_weak_error_smooth_M`), `β = log₂ M` (`gbm_correction_variance_le_M`) and
`γ = log₂ M`; for `M = 4`, `α = β = γ = 2`.  The bound on the finest level is where the weak rate
shows: from `α = ½ log₂ M` alone (`gbm_weak_error_le_M`, any Lipschitz payoff) the same
construction gives only `M^L = O(ε⁻²)`; the other three conclusions are those of
`gbm_mlmc_theorem1_M`, since with `β = γ` the complexity does not depend on `α`.  The coarsest
step is `T/m` so that the grid reaches `T`. -/
theorem gbm_mlmc_theorem1_smooth_M (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m M : ℕ} (hm : 0 < m)
    (hM : 2 ≤ M) {g : ℝ → ℝ} (hg : ∀ k < 4, Differentiable ℝ (iteratedDeriv k g)) {K : ℝ}
    (hK : ∀ k, 1 ≤ k → k ≤ 4 → ∀ x, |iteratedDeriv k g x| ≤ K) :
    ∃ c₄ c₅ : ℝ, 0 < c₄ ∧ 0 < c₅ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
              (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
                (fun ℓ path => g (path (m * M ^ ℓ)))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
              (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
                (fun ℓ path => g (path (m * M ^ ℓ)))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (m * (M : ℝ) ^ ℓ) ≤
          c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) ∧
        (M : ℝ) ^ L ≤ c₅ / ε := by
  have hM0 : 0 < M := by omega
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hβ : 0 < Real.logb 2 M := Real.logb_pos (by norm_num) hM1
  obtain ⟨hgc, hgL⟩ := continuous_lipschitz_of_iteratedDeriv hg hK
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 1 le_rfl (by norm_num) 0)
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hC := gbmStrongConst_nonneg r σ s₀ hT
  have hTm : 0 ≤ T / m := div_nonneg hT hm'.le
  set P : (ℕ → ℝ) → ℝ :=
    fun z => g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * z 0))) with hPdef
  have hPint : ∫ z, P z ∂stdNormalSeq =
      ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1 := by
    have hF : Measurable fun w : ℝ =>
        g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) :=
      hgc.measurable.comp (by fun_prop)
    exact integral_comp_of_measurePreserving
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0) hF.aestronglyMeasurable
  have eP : P = fun z => g (gbmExactM r σ T s₀ 1 M 0 z) := funext fun z => by
    rw [hPdef, gbmExactM_one_zero]
  have hP : MemLp P 2 stdNormalSeq := by
    rw [eP]
    exact memLp_two_comp_of_abs_sub_le hgL (memLp_gbmExactM r σ T s₀ one_pos hM0 0)
  have hPfm : ∀ ℓ, Measurable (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => g (path (m * M ^ ℓ))) ℓ) := fun ℓ => by
    have h := hgc.measurable.comp (measurable_gbmEMn r σ (T / m / (M : ℝ) ^ ℓ) s₀ (m * M ^ ℓ))
    exact h
  have hPf : ∀ ℓ, MemLp (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => g (path (m * M ^ ℓ))) ℓ) 2 stdNormalSeq := fun ℓ => by
    have h := memLp_two_comp_of_abs_sub_le hgL
      (memLp_gbmEMn r σ (T / m / (M : ℝ) ^ ℓ) s₀ (m * M ^ ℓ))
    exact h
  -- (i): the weak rate `α = log₂ M`
  have hCW : 0 ≤ gbmWeakSmoothConst K r σ s₀ T := by
    unfold gbmWeakSmoothConst
    positivity
  have hc₁ : 0 < gbmWeakSmoothConst K r σ s₀ T * (T / m) + 1 := by positivity
  have h_i : ∀ ℓ : ℕ, |∫ z, emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => g (path (m * M ^ ℓ))) ℓ z - P z ∂stdNormalSeq| ≤
      (gbmWeakSmoothConst K r σ s₀ T * (T / m) + 1) *
        (2 : ℝ) ^ (-(Real.logb 2 M * (ℓ : ℝ))) := fun ℓ => by
    have h := gbm_weak_error_smooth_M r σ s₀ hT hm hM0 hg hK ℓ
    rw [← hPint, ← integral_sub ((hPf ℓ).integrable one_le_two) (hP.integrable one_le_two)] at h
    rw [two_rpow_neg_logb_mul hM0]
    have hinv : 0 < ((M : ℝ) ^ ℓ)⁻¹ := by positivity
    calc _ ≤ gbmWeakSmoothConst K r σ s₀ T * (T / m / (M : ℝ) ^ ℓ) := h
      _ = gbmWeakSmoothConst K r σ s₀ T * (T / m) * ((M : ℝ) ^ ℓ)⁻¹ := by
          rw [div_eq_mul_inv (T / m)]
          ring
      _ ≤ _ := by nlinarith
  -- (iii): the variance rate `β = log₂ M`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => g (path (m * M ^ ℓ))) 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := hV₀ ▸ variance_nonneg _ _
  have hc₂ : 0 < V₀ + 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) + 1 := by
    positivity
  have h_iii : ∀ ℓ, variance (fineCoarseDiff
      (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
      (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ)))) ℓ)
      stdNormalSeq ≤
      (V₀ + 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) + 1) *
        (2 : ℝ) ^ (-(Real.logb 2 M * (ℓ : ℝ))) := by
    intro ℓ
    rw [two_rpow_neg_logb_mul hM0]
    cases ℓ with
    | zero =>
      change variance (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
        (fun ℓ path => g (path (m * M ^ ℓ))) 0) stdNormalSeq ≤ _
      rw [pow_zero, inv_one, mul_one, ← hV₀]
      have : 0 ≤ 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) := by positivity
      linarith
    | succ ℓ =>
      have hv := gbm_correction_variance_le_M r σ s₀ hT hm hM0 hgL ℓ
      have hinv : 0 < ((M : ℝ) ^ (ℓ + 1))⁻¹ := by positivity
      calc _ ≤ 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) /
            (M : ℝ) ^ (ℓ + 1) := hv
        _ = 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) *
            ((M : ℝ) ^ (ℓ + 1))⁻¹ := by
          rw [div_eq_mul_inv]
        _ ≤ _ := by nlinarith
  -- (iv): a level-`ℓ` sample costs `m M^ℓ = m 2^{ℓ log₂ M}`
  have h_iv : ∀ ℓ : ℕ, (m : ℝ) * (M : ℝ) ^ ℓ ≤ m * (2 : ℝ) ^ (Real.logb 2 M * (ℓ : ℝ)) :=
    fun ℓ => by rw [two_rpow_logb_mul hM0]
  obtain ⟨c₄, hc₄, h⟩ := em_mlmc_theorem1_levels_M
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq)
    (gbmDrift r) (gbmVol σ) (T / m) s₀ hM0 (fun ℓ path => g (path (m * M ^ ℓ))) P
    (fun p x => x p) (fun ℓ => (m : ℝ) * (M : ℝ) ^ ℓ) (α := Real.logb 2 M)
    (β := Real.logb 2 M) (γ := Real.logb 2 M) hβ hβ hc₁ hc₂ hm' (by rw [min_self]; linarith)
    hω hind (hP.integrable one_le_two) hPfm hPf h_i h_iii h_iv
  refine ⟨c₄, K1 (Real.logb 2 M) (gbmWeakSmoothConst K r σ s₀ T * (T / m) + 1), hc₄,
    K1_pos hc₁, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost, hL⟩ := h ε hε hε1
  rw [hPint] at hint hmse
  rw [complexityBound_of_eq rfl ε] at hcost
  rw [two_rpow_logb_mul hM0] at hL
  exact ⟨L, N, hN, hint, hmse, hcost, hL⟩

/-- **Theorem 1 for the Euler–Maruyama MLMC estimator of GBM with a smooth payoff, with the paper's
rates `α = β = γ = 1`** (Giles 2015, §5.1, p. 30, l. 1318–1321: "Alternatively, if
`h_ℓ = 2^{−ℓ}h_0` with twice as many timesteps on each successive level, as used in the numerical
examples in this article, then `α = 1`, `β = 1` and `γ = 1`. In either case, Theorem 1 gives the
complexity to achieve a root-mean-square error of `ε` to be `O(ε^{−2}(log ε)²)`"; §2.1, p. 7,
l. 326: "Because of condition i), we have `2^{−αL} = O(ε)`, and hence `C_L = O(ε^{−γ/α})`").  Let
`dS = rS dt + σS dW`, `S_0 = s₀`, `T ≥ 0`, and let `g` be four times differentiable with
`|g^{(k)}| ≤ K` for `k = 1, …, 4`.  Level `ℓ` uses `2^ℓ` Euler–Maruyama steps of size
`h_ℓ = T 2^{−ℓ}`; its correction is the payoff of the fine path minus the payoff of the coarse path
driven by the summed increments, the samples are independent, and a level-`ℓ` sample costs `2^ℓ`.
Then there are `c₄, c₅ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for
which the multilevel estimator of `E[g(S_T)] = E[g(s₀ e^{(r − σ²/2)T + σ √T Z})]`, `Z ∼ N(0,1)`,
has a square-integrable error with mean square `< ε²`, cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`,
and finest level `2^L ≤ c₅ ε⁻¹` (`O(ε⁻¹)` time steps on the finest level).  The rates are all
proved: `α = 1` (`gbm_weak_error_smooth`), `β = 1` (`gbm_correction_variance_le`, as `g` is
`K`-Lipschitz) and `γ = 1`.  The bound on the finest level is where `α = 1` shows: from the rate
`α = ½` of `gbm_weak_error_le` (any Lipschitz payoff) the same construction gives only
`2^L = O(ε⁻²)`; the other three conclusions are those of `gbm_mlmc_theorem1` (any Lipschitz
payoff), since with `β = γ` the complexity does not depend on `α`.  The case `m = 1`, `M = 2` of
`gbm_mlmc_theorem1_smooth_M`. -/
theorem gbm_mlmc_theorem1_smooth (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    (hg : ∀ k < 4, Differentiable ℝ (iteratedDeriv k g)) {K : ℝ}
    (hK : ∀ k, 1 ≤ k → k ≤ 4 → ∀ x, |iteratedDeriv k g x| ≤ K) :
    ∃ c₄ c₅ : ℝ, 0 < c₄ ∧ 0 < c₅ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g))
              (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g))) (fun p x => x p) ℓ
              (N ℓ) x -
            ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g))
              (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g))) (fun p x => x p) ℓ
              (N ℓ) x -
            ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) ∧
        (2 : ℝ) ^ L ≤ c₅ / ε := by
  have H := gbm_mlmc_theorem1_smooth_M r σ s₀ hT (m := 1) (M := 2) one_pos le_rfl hg hK
  simp only [Nat.cast_one, div_one, one_mul, Nat.cast_ofNat, emFineM_two, emCoarseM_two] at H
  exact H

/-! ### Theorem 1 for polynomial payoffs -/

/-- The even moments of the Euler–Maruyama value of GBM: `E[Ŝ_n^{2m}] ≤ S_0^{2m} e^{(2m|r| +
2m²σ²) t_n}` for `h ≥ 0` and `t_n = nh` (Giles 2015, §5.1). -/
lemma integral_emPath_gbm_pow_two_mul_le (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n m : ℕ) :
    ∫ z, emPath (gbmDrift r) (gbmVol σ) h s₀ z n ^ (2 * m) ∂stdNormalSeq ≤
      s₀ ^ (2 * m) * Real.exp ((2 * m * |r| + 2 * m ^ 2 * σ ^ 2) * (n * h)) := by
  rw [integral_emPath_gbm_pow]
  have h0 : 0 ≤ ∫ x, gbmEMFactor r σ h x ^ (2 * m) ∂gaussianReal 0 1 :=
    integral_nonneg fun x => by rw [pow_mul]; positivity
  have h1 := (le_abs_self _).trans (abs_integral_gbmEMFactor_pow_le r σ hh (2 * m))
  have h2 : Real.exp ((((2 * m : ℕ) : ℝ) * |r| + ((2 * m : ℕ) : ℝ) ^ 2 * σ ^ 2 / 2) * h) ^ n =
      Real.exp ((2 * m * |r| + 2 * m ^ 2 * σ ^ 2) * (n * h)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc s₀ ^ (2 * m) * (∫ x, gbmEMFactor r σ h x ^ (2 * m) ∂gaussianReal 0 1) ^ n
      ≤ s₀ ^ (2 * m) * Real.exp ((((2 * m : ℕ) : ℝ) * |r| +
          ((2 * m : ℕ) : ℝ) ^ 2 * σ ^ 2 / 2) * h) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 _) (by rw [pow_mul]; positivity)
    _ = _ := by rw [h2]

/-- The even moments of the exact GBM solution on the grid:
`E[S_{t_n}^{2m}] ≤ S_0^{2m} e^{(2m|r| + 2m²σ²) t_n}` for `h ≥ 0` and `t_n = nh` (Giles 2015,
§5.1). -/
lemma integral_gbmExp_pow_two_mul_le (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n m : ℕ) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
        σ * (Real.sqrt h * ∑ i ∈ range n, z i))) ^ (2 * m) ∂stdNormalSeq ≤
      s₀ ^ (2 * m) * Real.exp ((2 * m * |r| + 2 * m ^ 2 * σ ^ 2) * (n * h)) := by
  rw [integral_gbmExp_pow r σ s₀ hh]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_
    (by positivity))) (by rw [pow_mul]; positivity)
  push_cast
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (m : ℝ) * r ≤ m * |r| := mul_le_mul_of_nonneg_left (le_abs_self r) hm
  have h2 : 0 ≤ (m : ℝ) * σ ^ 2 := mul_nonneg hm (sq_nonneg σ)
  linarith

/-- **A polynomial is locally Lipschitz with polynomial growth**: for `q = ∑_{k≤d} c_k X^k`,
`|q(x) − q(y)| ≤ (∑_k |c_k| k) |x − y| (1 + |x| + |y|)^d` (the polynomial payoffs of Giles 2015,
§5.1). -/
lemma abs_eval_sub_eval_le (q : Polynomial ℝ) (x y : ℝ) :
    |q.eval x - q.eval y| ≤ (∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k) * |x - y| *
      (1 + |x| + |y|) ^ q.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← sum_sub_distrib, sum_mul,
    sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk' : k ≤ q.natDegree := Nat.lt_succ_iff.1 (mem_range.1 hk)
  have hB : 1 ≤ 1 + |x| + |y| := by linarith [abs_nonneg x, abs_nonneg y]
  have hmax : max |x| |y| ≤ 1 + |x| + |y| :=
    max_le (by linarith [abs_nonneg y]) (by linarith [abs_nonneg x])
  have h1 := abs_pow_sub_pow_le x y k
  have h2 : max |x| |y| ^ (k - 1) ≤ (1 + |x| + |y|) ^ q.natDegree :=
    (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg x)) hmax _).trans
      (pow_le_pow_right₀ hB (by omega))
  rw [← mul_sub, abs_mul]
  have h3 : |x ^ k - y ^ k| ≤ |x - y| * k * (1 + |x| + |y|) ^ q.natDegree :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  calc |q.coeff k| * |x ^ k - y ^ k| ≤
        |q.coeff k| * (|x - y| * k * (1 + |x| + |y|) ^ q.natDegree) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = _ := by ring

/-- **The squared difference of a polynomial payoff** (Giles 2015, §5.1): for `h > 0`,
`(q(x) − q(y))² ≤ c_q² ((x − y)⁴/(2h) + h 3^{N−1}(1 + x^N + y^N)/2)` with `N = 4d`,
`c_q = ∑_k |c_k| k` (`abs_eval_sub_eval_le` and `ab ≤ a²/(2h) + hb²/2`). -/
lemma sq_eval_sub_eval_le (q : Polynomial ℝ) {h : ℝ} (hh : 0 < h) (x y : ℝ) :
    (q.eval x - q.eval y) ^ 2 ≤ (∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k) ^ 2 *
      ((x - y) ^ 4 / (2 * h) + h * (3 ^ (2 * (2 * q.natDegree) - 1) *
        (1 + x ^ (2 * (2 * q.natDegree)) + y ^ (2 * (2 * q.natDegree)))) / 2) := by
  set c := ∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k with hcdef
  set d := q.natDegree with hddef
  have hc : 0 ≤ c := sum_nonneg fun k _ => by positivity
  set B := (1 + |x| + |y|) ^ d with hBdef
  have hB0 : 0 ≤ B := by positivity
  have h1 := abs_eval_sub_eval_le q x y
  rw [← hcdef, ← hddef, ← hBdef] at h1
  have h2 : (q.eval x - q.eval y) ^ 2 ≤ c ^ 2 * ((x - y) ^ 2 * B ^ 2) := by
    rw [← sq_abs]
    calc |q.eval x - q.eval y| ^ 2 ≤ (c * |x - y| * B) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = _ := by rw [mul_pow, mul_pow, sq_abs]; ring
  have h3 : (x - y) ^ 2 * B ^ 2 ≤ (x - y) ^ 4 / (2 * h) + h * B ^ 4 / 2 := by
    have key : 0 ≤ ((x - y) ^ 2 - h * B ^ 2) ^ 2 := sq_nonneg _
    have e : (x - y) ^ 4 / (2 * h) + h * B ^ 4 / 2 - (x - y) ^ 2 * B ^ 2 =
        ((x - y) ^ 2 - h * B ^ 2) ^ 2 / (2 * h) := by
      field_simp
      ring
    have : 0 ≤ ((x - y) ^ 2 - h * B ^ 2) ^ 2 / (2 * h) := div_nonneg key (by positivity)
    linarith
  have h4 : B ^ 4 ≤ 3 ^ (2 * (2 * d) - 1) * (1 + x ^ (2 * (2 * d)) + y ^ (2 * (2 * d))) := by
    have e1 : B ^ 4 = (1 + |x| + |y|) ^ (2 * (2 * d)) := by
      rw [hBdef, ← pow_mul]
      ring_nf
    have e2 : |x| ^ (2 * (2 * d)) = x ^ (2 * (2 * d)) := by
      rw [pow_mul, sq_abs, ← pow_mul]
    have e3 : |y| ^ (2 * (2 * d)) = y ^ (2 * (2 * d)) := by
      rw [pow_mul, sq_abs, ← pow_mul]
    have := add_three_pow_le zero_le_one (abs_nonneg x) (abs_nonneg y) (2 * (2 * d))
    rw [one_pow, e2, e3] at this
    rw [e1]
    exact this
  calc (q.eval x - q.eval y) ^ 2 ≤ c ^ 2 * ((x - y) ^ 2 * B ^ 2) := h2
    _ ≤ c ^ 2 * ((x - y) ^ 4 / (2 * h) + h * B ^ 4 / 2) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
    _ ≤ _ := by gcongr

/-- The exact GBM solution on the grid (Giles 2015, §5.1) is a measurable function of the
increments. -/
lemma measurable_gbmExp (r σ h s₀ : ℝ) (n : ℕ) :
    Measurable fun z : ℕ → ℝ => s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
      σ * (Real.sqrt h * ∑ i ∈ range n, z i)) :=
  ((((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_mul
    (Real.sqrt h)).const_mul σ).const_add _).exp.const_mul s₀

/-- `(S_{t_n} − Ŝ_n)^{2m}` is integrable for the Euler–Maruyama approximation of GBM on the grid
`t_n = nh`, `h ≥ 0` (Giles 2015, §5.1). -/
lemma integrable_gbmExp_sub_emPath_pow (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n m : ℕ) :
    Integrable (fun z => (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
        σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
      emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ (2 * m)) stdNormalSeq := by
  simp_rw [gbmExp_eq_prod, emPath_gbm, mul_sub_mul_pow_two_mul]
  exact (integrable_pow_prod_sub_prod (measurable_gbmExpFactor r σ _)
    (measurable_gbmEMFactor r σ _) (even_two_mul m) (integrable_gbmExpFactor_pow r σ _ _)
    (integrable_gbmEMFactor_pow r σ hh m) _).const_mul _

/-- **The mean square error of a polynomial payoff at a grid time** (Giles 2015, §5.1, p. 29:
"`V[P − P_ℓ] ≤ E[(P − P_ℓ)²]`").  For `h > 0`, `n ∈ ℕ` and `t_n = nh`,
`E[(q(S_{t_n}) − q(Ŝ_n))²]` is finite and at most
`c_q² (C₂(t_n) + 3^{N−1}(1 + 2M_N(t_n)))/2 · h`, with `N = 4d` (`d = deg q`),
`c_q = ∑_k |c_k| k`, `C₂` the fourth-moment constant of the strong error (`gbmEMMomentConst 2`,
`gbm_em_moment_error`) and `M_N(t) = S_0^N e^{(N|r| + N²σ²/2)t}` the moment bound of
`integral_emPath_gbm_pow_two_mul_le` and `integral_gbmExp_pow_two_mul_le`; the pointwise bound is
`sq_eval_sub_eval_le`. -/
lemma integral_sq_poly_gbm_em_err_le (r σ s₀ : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ)
    (q : Polynomial ℝ) :
    Integrable (fun z => (q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
        σ * (Real.sqrt h * ∑ i ∈ range n, z i))) -
      q.eval (emPath (gbmDrift r) (gbmVol σ) h s₀ z n)) ^ 2) stdNormalSeq ∧
    ∫ z, (q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
        σ * (Real.sqrt h * ∑ i ∈ range n, z i))) -
      q.eval (emPath (gbmDrift r) (gbmVol σ) h s₀ z n)) ^ 2 ∂stdNormalSeq ≤
      (∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k) ^ 2 *
        (gbmEMMomentConst 2 r σ (n * h) s₀ + 3 ^ (2 * (2 * q.natDegree) - 1) *
          (1 + 2 * (s₀ ^ (2 * (2 * q.natDegree)) * Real.exp ((2 * ((2 * q.natDegree : ℕ) : ℝ) *
            |r| + 2 * ((2 * q.natDegree : ℕ) : ℝ) ^ 2 * σ ^ 2) * (n * h))))) / 2 * h := by
  set c := ∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k with hcdef
  set N : ℕ := 2 * (2 * q.natDegree) with hNdef
  set Mom := s₀ ^ (2 * (2 * q.natDegree)) * Real.exp ((2 * ((2 * q.natDegree : ℕ) : ℝ) * |r| +
    2 * ((2 * q.natDegree : ℕ) : ℝ) ^ 2 * σ ^ 2) * (n * h)) with hMomdef
  set E := fun z : ℕ → ℝ => s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) +
    σ * (Real.sqrt h * ∑ i ∈ range n, z i)) with hEdef
  set F := fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z n with hFdef
  have iD : Integrable (fun z => (E z - F z) ^ 4) stdNormalSeq :=
    integrable_gbmExp_sub_emPath_pow r σ s₀ hh.le n 2
  have iE : Integrable (fun z => E z ^ N) stdNormalSeq := integrable_gbmExp_pow r σ h s₀ n N
  have iF : Integrable (fun z => F z ^ N) stdNormalSeq := integrable_emPath_gbm_pow r σ h s₀ n N
  have iG : Integrable (fun z => c ^ 2 * ((E z - F z) ^ 4 / (2 * h) +
      h * (3 ^ (N - 1) * (1 + E z ^ N + F z ^ N)) / 2)) stdNormalSeq :=
    ((iD.div_const _).add ((((integrable_const 1).add iE).add iF).const_mul _
      |>.const_mul h |>.div_const 2)).const_mul _
  have hpt : ∀ z, (q.eval (E z) - q.eval (F z)) ^ 2 ≤ c ^ 2 * ((E z - F z) ^ 4 / (2 * h) +
      h * (3 ^ (N - 1) * (1 + E z ^ N + F z ^ N)) / 2) := fun z =>
    sq_eval_sub_eval_le q hh (E z) (F z)
  have hm : Measurable fun z => (q.eval (E z) - q.eval (F z)) ^ 2 :=
    ((q.continuous.measurable.comp (measurable_gbmExp r σ h s₀ n)).sub
      (q.continuous.measurable.comp (measurable_gbmEMn r σ h s₀ n))).pow_const 2
  refine ⟨iG.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt z
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _) iG
    (Filter.Eventually.of_forall hpt)).trans ?_
  have hD := gbm_em_moment_error r σ s₀ hh.le n (m := 2) two_pos
  have hEN : ∫ z, E z ^ N ∂stdNormalSeq ≤ Mom :=
    integral_gbmExp_pow_two_mul_le r σ s₀ hh.le n (2 * q.natDegree)
  have hFN : ∫ z, F z ^ N ∂stdNormalSeq ≤ Mom :=
    integral_emPath_gbm_pow_two_mul_le r σ s₀ hh.le n (2 * q.natDegree)
  have iS1 : Integrable (fun z => 1 + E z ^ N) stdNormalSeq := (integrable_const 1).add iE
  have iS : Integrable (fun z => 1 + E z ^ N + F z ^ N) stdNormalSeq := iS1.add iF
  have iQ : Integrable (fun z => (E z - F z) ^ 4 / (2 * h)) stdNormalSeq := iD.div_const _
  have iP : Integrable (fun z => h * (3 ^ (N - 1) * (1 + E z ^ N + F z ^ N)) / 2) stdNormalSeq :=
    ((iS.const_mul _).const_mul h).div_const 2
  rw [integral_const_mul, integral_add iQ iP, integral_div, integral_div, integral_const_mul,
    integral_const_mul, integral_add iS1 iF, integral_add (integrable_const 1) iE, integral_const,
    probReal_univ, one_smul]
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have h3 : (0 : ℝ) ≤ 3 ^ (N - 1) := by positivity
  have e4 : ∫ z, (E z - F z) ^ 4 ∂stdNormalSeq ≤ gbmEMMomentConst 2 r σ (n * h) s₀ * h ^ 2 := hD
  have k1 : (∫ z, (E z - F z) ^ 4 ∂stdNormalSeq) / (2 * h) ≤
      gbmEMMomentConst 2 r σ (n * h) s₀ * h / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have k2 : h * (3 ^ (N - 1) * (1 + ∫ z, E z ^ N ∂stdNormalSeq + ∫ z, F z ^ N ∂stdNormalSeq)) /
      2 ≤ h * (3 ^ (N - 1) * (1 + 2 * Mom)) / 2 := by
    have hXY : 1 + ∫ z, E z ^ N ∂stdNormalSeq + ∫ z, F z ^ N ∂stdNormalSeq ≤ 1 + 2 * Mom := by
      linarith
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXY h3) hh.le
    linarith
  calc _ ≤ c ^ 2 * (gbmEMMomentConst 2 r σ (n * h) s₀ * h / 2 +
        h * (3 ^ (N - 1) * (1 + 2 * Mom)) / 2) :=
        mul_le_mul_of_nonneg_left (add_le_add k1 k2) hc2
    _ = _ := by ring

/-- **The mean square error of a polynomial payoff on level `ℓ`** (Giles 2015, §5.1, p. 29:
"`V[P − P_ℓ] ≤ E[(P − P_ℓ)²]`").  For `T > 0`, `E[(q(S_T) − q(Ŝ_ℓ))²]` is finite and at most
`c_q² (C₂(T) + 3^{N−1}(1 + 2M_N(T)))/2 · h_ℓ`, with `h_ℓ = T 2^{−ℓ}` (the grid bound
`integral_sq_poly_gbm_em_err_le` with `2^ℓ` steps). -/
lemma integral_sq_poly_gbm_err_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 < T) (q : Polynomial ℝ) (ℓ : ℕ) :
    Integrable (fun z => (q.eval (gbmExact r σ T s₀ ℓ z) - q.eval (gbmEM r σ T s₀ ℓ z)) ^ 2)
      stdNormalSeq ∧
    ∫ z, (q.eval (gbmExact r σ T s₀ ℓ z) - q.eval (gbmEM r σ T s₀ ℓ z)) ^ 2 ∂stdNormalSeq ≤
      (∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k) ^ 2 *
        (gbmEMMomentConst 2 r σ T s₀ + 3 ^ (2 * (2 * q.natDegree) - 1) *
          (1 + 2 * (s₀ ^ (2 * (2 * q.natDegree)) * Real.exp ((2 * ((2 * q.natDegree : ℕ) : ℝ) *
            |r| + 2 * ((2 * q.natDegree : ℕ) : ℝ) ^ 2 * σ ^ 2) * T)))) / 2 * (T / 2 ^ ℓ) := by
  have H := integral_sq_poly_gbm_em_err_le r σ s₀ (div_pos hT (by positivity : (0 : ℝ) < 2 ^ ℓ))
    (2 ^ ℓ) q
  rw [cast_two_pow_mul_div] at H
  exact H

/-- **The variance of the level corrections for a polynomial payoff** (Giles 2015, §5.1, p. 29,
l. 1310–1313: "`V_ℓ ≡ V[P_ℓ − P_{ℓ−1}] ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`, and hence
`V_ℓ = O(h_ℓ)`", and p. 30, l. 1318–1320: "if `h_ℓ = 2^{−ℓ}h_0` … then `α = 1`, `β = 1`"; the rate
`β = 1`, here for polynomial payoffs, which are not Lipschitz, while the paper's argument is for
Lipschitz payoffs).  For `T ≥ 0`, every polynomial `q`
and every level `ℓ`, the correction on level `ℓ + 1`, the payoff of the fine path minus the payoff
of the coarse path driven by the summed increments, has variance at most
`3 c_q² T (C₂(T) + 3^{N−1}(1 + 2M_N(T))) 2^{−(ℓ+1)}` (constants of
`integral_sq_poly_gbm_err_le`). -/
theorem gbm_poly_correction_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (q : Polynomial ℝ)
    (ℓ : ℕ) :
    variance (fun z => q.eval (gbmEM r σ T s₀ (ℓ + 1) z) - q.eval (gbmEM r σ T s₀ ℓ (pairAvg z)))
        stdNormalSeq ≤
      3 * (∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k) ^ 2 * T *
        (gbmEMMomentConst 2 r σ T s₀ + 3 ^ (2 * (2 * q.natDegree) - 1) *
          (1 + 2 * (s₀ ^ (2 * (2 * q.natDegree)) * Real.exp ((2 * ((2 * q.natDegree : ℕ) : ℝ) *
            |r| + 2 * ((2 * q.natDegree : ℕ) : ℝ) ^ 2 * σ ^ 2) * T)))) *
        ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by
  rcases eq_or_lt_of_le hT with hT0 | hT0
  · -- `T = 0`: both paths stay at `s₀`
    subst hT0
    have hS : ∀ k z, gbmEM r σ 0 s₀ k z = s₀ := fun k z => by
      rw [gbmEM_eq_prod]
      simp [gbmEMFactor]
    have e : (fun z => q.eval (gbmEM r σ 0 s₀ (ℓ + 1) z) - q.eval (gbmEM r σ 0 s₀ ℓ (pairAvg z))) =
        0 := by
      funext z
      simp [hS]
    rw [e, variance_zero]
    simp
  have hMP := measurePreserving_pairAvg
  obtain ⟨i1, j1⟩ := integral_sq_poly_gbm_err_le r σ s₀ hT0 q (ℓ + 1)
  obtain ⟨i0, j0⟩ := integral_sq_poly_gbm_err_le r σ s₀ hT0 q ℓ
  set K := (∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k) ^ 2 *
    (gbmEMMomentConst 2 r σ T s₀ + 3 ^ (2 * (2 * q.natDegree) - 1) *
      (1 + 2 * (s₀ ^ (2 * (2 * q.natDegree)) * Real.exp ((2 * ((2 * q.natDegree : ℕ) : ℝ) *
        |r| + 2 * ((2 * q.natDegree : ℕ) : ℝ) ^ 2 * σ ^ 2) * T)))) with hKdef
  have i0' : Integrable (fun z => (q.eval (gbmExact r σ T s₀ ℓ (pairAvg z)) -
      q.eval (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 2) stdNormalSeq :=
    (hMP.integrable_comp i0.aestronglyMeasurable).2 i0
  have hm : Measurable fun z => q.eval (gbmEM r σ T s₀ (ℓ + 1) z) -
      q.eval (gbmEM r σ T s₀ ℓ (pairAvg z)) :=
    (q.continuous.measurable.comp (measurable_gbmEM r σ T s₀ (ℓ + 1))).sub
      (q.continuous.measurable.comp ((measurable_gbmEM r σ T s₀ ℓ).comp hMP.measurable))
  refine (variance_le_expectation_sq hm.aestronglyMeasurable).trans ?_
  simp only [Pi.pow_apply]
  have hpt : ∀ z, (q.eval (gbmEM r σ T s₀ (ℓ + 1) z) - q.eval (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 2
      ≤ 2 * (q.eval (gbmExact r σ T s₀ (ℓ + 1) z) - q.eval (gbmEM r σ T s₀ (ℓ + 1) z)) ^ 2 +
        2 * (q.eval (gbmExact r σ T s₀ ℓ (pairAvg z)) -
          q.eval (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 2 := fun z => by
    rw [gbmExact_pairAvg]
    nlinarith [sq_nonneg (q.eval (gbmExact r σ T s₀ (ℓ + 1) z) -
      q.eval (gbmEM r σ T s₀ (ℓ + 1) z) + (q.eval (gbmExact r σ T s₀ (ℓ + 1) z) -
      q.eval (gbmEM r σ T s₀ ℓ (pairAvg z))))]
  have hT' : T / 2 ^ ℓ = 2 * (T / 2 ^ (ℓ + 1)) := by
    rw [pow_succ, ← div_div, mul_div_cancel₀ _ two_ne_zero]
  calc ∫ z, (q.eval (gbmEM r σ T s₀ (ℓ + 1) z) - q.eval (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 2
        ∂stdNormalSeq
      ≤ ∫ z, (2 * (q.eval (gbmExact r σ T s₀ (ℓ + 1) z) - q.eval (gbmEM r σ T s₀ (ℓ + 1) z)) ^ 2 +
        2 * (q.eval (gbmExact r σ T s₀ ℓ (pairAvg z)) -
          q.eval (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 2) ∂stdNormalSeq :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
          ((i1.const_mul 2).add (i0'.const_mul 2)) (Filter.Eventually.of_forall hpt)
    _ = 2 * ∫ z, (q.eval (gbmExact r σ T s₀ (ℓ + 1) z) - q.eval (gbmEM r σ T s₀ (ℓ + 1) z)) ^ 2
          ∂stdNormalSeq +
        2 * ∫ z, (q.eval (gbmExact r σ T s₀ ℓ z) - q.eval (gbmEM r σ T s₀ ℓ z)) ^ 2
          ∂stdNormalSeq := by
        rw [integral_add (i1.const_mul _) (i0'.const_mul _), integral_const_mul,
          integral_const_mul, integral_comp_of_measurePreserving hMP i0.aestronglyMeasurable]
    _ ≤ 2 * (K / 2 * (T / 2 ^ (ℓ + 1))) + 2 * (K / 2 * (T / 2 ^ ℓ)) := by
        gcongr
    _ = _ := by
        rw [hT', div_eq_mul_inv T]
        ring

/-- **The variance of the level corrections for a polynomial payoff with refinement factor `M`**
(Giles 2015, §5.1, p. 29, l. 1310–1313: "`V_ℓ ≡ V[P_ℓ − P_{ℓ−1}] ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`,
and hence `V_ℓ = O(h_ℓ)`", and p. 30, l. 1317–1318: "If `h_ℓ = 4^{−ℓ}h_0` … then this gives
`α = 2`, `β = 2`"; here for polynomial payoffs, which are not Lipschitz).  For `T ≥ 0`, `m, M ≥ 1`,
`h_0 = T/m`, every polynomial `q` and every level `ℓ`, the correction on level `ℓ + 1`, the payoff
of the fine path with `m M^{ℓ+1}` steps minus the payoff of the coarse path with `m M^ℓ` steps
driven by the block sums of the same increments (`emCoarseM`), has variance at most
`K_q(T) h_0 (M + 1) M^{−(ℓ+1)}`, `K_q(T) = c_q² (C₂(T) + 3^{N−1}(1 + 2M_N(T)))` (constants of
`integral_sq_poly_gbm_em_err_le`): `V_ℓ = O(h_ℓ)`, the rate `β = log₂ M` in Theorem 1's base
`2`. -/
theorem gbm_poly_correction_variance_le_M (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m M : ℕ}
    (hm : 0 < m) (hM : 0 < M) (q : Polynomial ℝ) (ℓ : ℕ) :
    variance (fineCoarseDiff
        (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => q.eval (path (m * M ^ ℓ))))
        (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
          (fun ℓ path => q.eval (path (m * M ^ ℓ)))) (ℓ + 1)) stdNormalSeq ≤
      (∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k) ^ 2 *
        (gbmEMMomentConst 2 r σ T s₀ + 3 ^ (2 * (2 * q.natDegree) - 1) *
          (1 + 2 * (s₀ ^ (2 * (2 * q.natDegree)) * Real.exp ((2 * ((2 * q.natDegree : ℕ) : ℝ) *
            |r| + 2 * ((2 * q.natDegree : ℕ) : ℝ) ^ 2 * σ ^ 2) * T)))) * (T / m) * (M + 1) /
        (M : ℝ) ^ (ℓ + 1) := by
  rcases eq_or_lt_of_le hT with hT0 | hT0
  · -- `T = 0`: both paths stay at `s₀`
    subst hT0
    have hS : ∀ k z, emPath (gbmDrift r) (gbmVol σ) 0 s₀ z k = s₀ := fun k z => by
      rw [emPath_gbm]
      simp [gbmEMFactor]
    have e : fineCoarseDiff
        (emFineM (gbmDrift r) (gbmVol σ) (0 / m) s₀ M (fun ℓ path => q.eval (path (m * M ^ ℓ))))
        (emCoarseM (gbmDrift r) (gbmVol σ) (0 / m) s₀ M
          (fun ℓ path => q.eval (path (m * M ^ ℓ)))) (ℓ + 1) = 0 := by
      funext z
      show emFineM (gbmDrift r) (gbmVol σ) (0 / m) s₀ M (fun ℓ path => q.eval (path (m * M ^ ℓ)))
          (ℓ + 1) z - emCoarseM (gbmDrift r) (gbmVol σ) (0 / m) s₀ M
            (fun ℓ path => q.eval (path (m * M ^ ℓ))) ℓ z = 0
      simp only [emFineM, emCoarseM, zero_div, mul_zero, hS, sub_self]
    rw [e, variance_zero]
    simp
  set KP := (∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k) ^ 2 *
    (gbmEMMomentConst 2 r σ T s₀ + 3 ^ (2 * (2 * q.natDegree) - 1) *
      (1 + 2 * (s₀ ^ (2 * (2 * q.natDegree)) * Real.exp ((2 * ((2 * q.natDegree : ℕ) : ℝ) *
        |r| + 2 * ((2 * q.natDegree : ℕ) : ℝ) ^ 2 * σ ^ 2) * T)))) with hKPdef
  have hMp := measurePreserving_blockAvg hM
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set F : ℕ → (ℕ → ℝ) → ℝ :=
    fun k z => emPath (gbmDrift r) (gbmVol σ) (T / m / (M : ℝ) ^ k) s₀ z (m * M ^ k) with hFdef
  set X : ℕ → (ℕ → ℝ) → ℝ := fun k => gbmExactM r σ T s₀ m M k with hXdef
  have e : fineCoarseDiff
      (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => q.eval (path (m * M ^ ℓ))))
      (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => q.eval (path (m * M ^ ℓ))))
      (ℓ + 1) = fun z => q.eval (F (ℓ + 1) z) - q.eval (F ℓ (blockAvg M z)) := by
    funext z
    show emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => q.eval (path (m * M ^ ℓ)))
        (ℓ + 1) z -
      emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => q.eval (path (m * M ^ ℓ))) ℓ z
        = _
    rw [emCoarseM_eq _ _ _ _ hM]
    rfl
  rw [e]
  have hErr : ∀ k, Integrable (fun z => (q.eval (X k z) - q.eval (F k z)) ^ 2) stdNormalSeq ∧
      ∫ z, (q.eval (X k z) - q.eval (F k z)) ^ 2 ∂stdNormalSeq ≤
        KP / 2 * (T / m / (M : ℝ) ^ k) := fun k => by
    have hh : 0 < T / m / (M : ℝ) ^ k := by positivity
    have H := integral_sq_poly_gbm_em_err_le r σ s₀ hh (m * M ^ k) q
    rw [cast_mul_pow_mul_div hm hM] at H
    exact H
  have hm1 : Measurable (F (ℓ + 1)) := measurable_gbmEMn r σ _ s₀ _
  have hm0 : Measurable fun z => F ℓ (blockAvg M z) :=
    (measurable_gbmEMn r σ _ s₀ _).comp hMp.measurable
  have hY : AEStronglyMeasurable (fun z => q.eval (F (ℓ + 1) z) - q.eval (F ℓ (blockAvg M z)))
      stdNormalSeq :=
    ((q.continuous.measurable.comp hm1).sub (q.continuous.measurable.comp hm0)).aestronglyMeasurable
  refine (variance_le_expectation_sq hY).trans ?_
  simp only [Pi.pow_apply]
  obtain ⟨i1, j1⟩ := hErr (ℓ + 1)
  obtain ⟨i0, j0⟩ := hErr ℓ
  have i0' : Integrable (fun z => (q.eval (X ℓ (blockAvg M z)) -
      q.eval (F ℓ (blockAvg M z))) ^ 2) stdNormalSeq :=
    (hMp.integrable_comp i0.aestronglyMeasurable).2 i0
  have hpt : ∀ z, (q.eval (F (ℓ + 1) z) - q.eval (F ℓ (blockAvg M z))) ^ 2 ≤
      2 * (q.eval (X (ℓ + 1) z) - q.eval (F (ℓ + 1) z)) ^ 2 +
        2 * (q.eval (X ℓ (blockAvg M z)) - q.eval (F ℓ (blockAvg M z))) ^ 2 := fun z => by
    have hx : X ℓ (blockAvg M z) = X (ℓ + 1) z := gbmExactM_blockAvg r σ T s₀ m hM ℓ z
    rw [hx]
    nlinarith [sq_nonneg (q.eval (X (ℓ + 1) z) - q.eval (F (ℓ + 1) z) +
      (q.eval (X (ℓ + 1) z) - q.eval (F ℓ (blockAvg M z))))]
  calc ∫ z, (q.eval (F (ℓ + 1) z) - q.eval (F ℓ (blockAvg M z))) ^ 2 ∂stdNormalSeq
      ≤ ∫ z, (2 * (q.eval (X (ℓ + 1) z) - q.eval (F (ℓ + 1) z)) ^ 2 +
          2 * (q.eval (X ℓ (blockAvg M z)) - q.eval (F ℓ (blockAvg M z))) ^ 2) ∂stdNormalSeq :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
          ((i1.const_mul 2).add (i0'.const_mul 2)) (Filter.Eventually.of_forall hpt)
    _ = 2 * ∫ z, (q.eval (X (ℓ + 1) z) - q.eval (F (ℓ + 1) z)) ^ 2 ∂stdNormalSeq +
        2 * ∫ z, (q.eval (X ℓ z) - q.eval (F ℓ z)) ^ 2 ∂stdNormalSeq := by
        rw [integral_add (i1.const_mul _) (i0'.const_mul _), integral_const_mul,
          integral_const_mul, integral_comp_of_measurePreserving hMp i0.aestronglyMeasurable]
    _ ≤ 2 * (KP / 2 * (T / m / (M : ℝ) ^ (ℓ + 1))) + 2 * (KP / 2 * (T / m / (M : ℝ) ^ ℓ)) := by
        gcongr
    _ = KP * (T / m) * (M + 1) / (M : ℝ) ^ (ℓ + 1) := by
        rw [pow_succ]
        field_simp
        ring

/-- The powers of the exact GBM solution on the level-`ℓ` grid with refinement factor `M`
(`gbmExactM`, Giles 2015, §5.1) are integrable. -/
lemma integrable_gbmExactM_pow (r σ T s₀ : ℝ) {m M : ℕ} (hm : 0 < m) (hM : 0 < M) (ℓ i : ℕ) :
    Integrable (fun z => gbmExactM r σ T s₀ m M ℓ z ^ i) stdNormalSeq := by
  have H := integrable_gbmExp_pow r σ (T / m / (M : ℝ) ^ ℓ) s₀ (m * M ^ ℓ) i
  rw [cast_mul_pow_mul_div hm hM] at H
  exact H

/-- A polynomial in a random variable with integrable powers is square integrable (Giles 2015,
§5.1, polynomial payoffs). -/
lemma memLp_two_eval_of_integrable_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : Measurable X) (hi : ∀ k, Integrable (fun z => X z ^ k) μ)
    (q : Polynomial ℝ) : MemLp (fun z => q.eval (X z)) 2 μ := by
  simp_rw [Polynomial.eval_eq_sum_range]
  refine memLp_finsetSum _ fun k _ => MemLp.const_mul ?_ _
  refine (memLp_two_iff_integrable_sq (hX.pow_const k).aestronglyMeasurable).2 ?_
  simp_rw [← pow_mul]
  exact hi (k * 2)

/-- **Theorem 1 for the Euler–Maruyama MLMC estimator of GBM with a polynomial payoff and
refinement factor `M`** (Giles 2015, §5.1, p. 30, l. 1317–1321: "If `h_ℓ = 4^{−ℓ}h_0`, as in the
numerical examples in (Giles 2008b), then this gives `α = 2`, `β = 2` and `γ = 2` … In either case,
Theorem 1 gives the complexity to achieve a root-mean-square error of `ε` to be
`O(ε^{−2}(log ε)²)`"; §2.1, p. 7, l. 326: "Because of condition i), we have `2^{−αL} = O(ε)`, and
hence `C_L = O(ε^{−γ/α})`").  Let `dS = rS dt + σS dW`, `T ≥ 0`, `m ≥ 1`, `M ≥ 2`, and let `q` be
any real polynomial (a payoff which is not Lipschitz unless `deg q ≤ 1`, so `gbm_mlmc_theorem1_M`
does not apply).  With the levels, corrections, independent samples and costs `m M^ℓ` of
`gbm_mlmc_theorem1_smooth_M`, there are `c₄, c₅ > 0` such that for every `0 < ε < e⁻¹` there are
`L` and `N_ℓ ≥ 1` for which the multilevel estimator of `E[q(S_T)]` has a square-integrable error
with mean square `< ε²`, cost `∑_{ℓ≤L} N_ℓ m M^ℓ ≤ c₄ ε⁻²(log ε)²`, and finest level
`M^L ≤ c₅ ε⁻¹`.  The rates are proved, in Theorem 1's base `2`: `α = log₂ M`
(`gbm_weak_error_poly_M`), `β = log₂ M` (`gbm_poly_correction_variance_le_M`, from the fourth
moment of the strong error and the moments of `Ŝ` and `S_T`) and `γ = log₂ M`; for `M = 4`,
`α = β = γ = 2`. -/
theorem gbm_mlmc_theorem1_poly_M (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m M : ℕ} (hm : 0 < m)
    (hM : 2 ≤ M) (q : Polynomial ℝ) :
    ∃ c₄ c₅ : ℝ, 0 < c₄ ∧ 0 < c₅ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
                (fun ℓ path => q.eval (path (m * M ^ ℓ))))
              (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
                (fun ℓ path => q.eval (path (m * M ^ ℓ)))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
                (fun ℓ path => q.eval (path (m * M ^ ℓ))))
              (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
                (fun ℓ path => q.eval (path (m * M ^ ℓ)))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (m * (M : ℝ) ^ ℓ) ≤
          c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) ∧
        (M : ℝ) ^ L ≤ c₅ / ε := by
  have hM0 : 0 < M := by omega
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hβ : 0 < Real.logb 2 M := Real.logb_pos (by norm_num) hM1
  have hqm : Measurable fun x => q.eval x := q.continuous.measurable
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hTm : 0 ≤ T / m := div_nonneg hT hm'.le
  set P : (ℕ → ℝ) → ℝ :=
    fun z => q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * z 0))) with hPdef
  have hPint : ∫ z, P z ∂stdNormalSeq =
      ∫ w, q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
        ∂gaussianReal 0 1 := by
    have hF : Measurable fun w : ℝ =>
        q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) :=
      hqm.comp (by fun_prop)
    exact integral_comp_of_measurePreserving
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0) hF.aestronglyMeasurable
  have eP : P = fun z => q.eval (gbmExactM r σ T s₀ 1 M 0 z) := funext fun z => by
    rw [hPdef, gbmExactM_one_zero]
  have hP : MemLp P 2 stdNormalSeq := by
    rw [eP]
    exact memLp_two_eval_of_integrable_pow (measurable_gbmExactM r σ T s₀ 1 M 0)
      (integrable_gbmExactM_pow r σ T s₀ one_pos hM0 0) q
  have hPfm : ∀ ℓ, Measurable (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => q.eval (path (m * M ^ ℓ))) ℓ) := fun ℓ => by
    have h := hqm.comp (measurable_gbmEMn r σ (T / m / (M : ℝ) ^ ℓ) s₀ (m * M ^ ℓ))
    exact h
  have hPf : ∀ ℓ, MemLp (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => q.eval (path (m * M ^ ℓ))) ℓ) 2 stdNormalSeq := fun ℓ => by
    have h := memLp_two_eval_of_integrable_pow
      (measurable_gbmEMn r σ (T / m / (M : ℝ) ^ ℓ) s₀ (m * M ^ ℓ))
      (integrable_emPath_gbm_pow r σ (T / m / (M : ℝ) ^ ℓ) s₀ (m * M ^ ℓ)) q
    exact h
  -- (i): the weak rate `α = log₂ M`
  set CP := ∑ i ∈ range (q.natDegree + 1), |q.coeff i| * gbmWeakPowConst i r σ T s₀ with hCPdef
  have hCP : 0 ≤ CP := sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by
    unfold gbmWeakPowConst
    positivity)
  have hc₁ : 0 < CP * (T / m) + 1 := by positivity
  have h_i : ∀ ℓ : ℕ, |∫ z, emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => q.eval (path (m * M ^ ℓ))) ℓ z - P z ∂stdNormalSeq| ≤
      (CP * (T / m) + 1) * (2 : ℝ) ^ (-(Real.logb 2 M * (ℓ : ℝ))) := fun ℓ => by
    have h := gbm_weak_error_poly_M r σ s₀ hT hm hM0 q ℓ
    rw [← hPint, ← integral_sub ((hPf ℓ).integrable one_le_two) (hP.integrable one_le_two)] at h
    rw [two_rpow_neg_logb_mul hM0]
    have hinv : 0 < ((M : ℝ) ^ ℓ)⁻¹ := by positivity
    calc _ ≤ CP * (T / m / (M : ℝ) ^ ℓ) := h
      _ = CP * (T / m) * ((M : ℝ) ^ ℓ)⁻¹ := by
          rw [div_eq_mul_inv (T / m)]
          ring
      _ ≤ _ := by nlinarith
  -- (iii): the variance rate `β = log₂ M`
  set KV := (∑ k ∈ range (q.natDegree + 1), |q.coeff k| * k) ^ 2 *
    (gbmEMMomentConst 2 r σ T s₀ + 3 ^ (2 * (2 * q.natDegree) - 1) *
      (1 + 2 * (s₀ ^ (2 * (2 * q.natDegree)) * Real.exp ((2 * ((2 * q.natDegree : ℕ) : ℝ) *
        |r| + 2 * ((2 * q.natDegree : ℕ) : ℝ) ^ 2 * σ ^ 2) * T)))) with hKVdef
  have hKV : 0 ≤ KV := by
    have h1 := gbmEMMomentConst_nonneg 2 r σ s₀ hT
    have h2 : 0 ≤ s₀ ^ (2 * (2 * q.natDegree)) := by rw [pow_mul]; positivity
    rw [hKVdef]
    positivity
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => q.eval (path (m * M ^ ℓ))) 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := hV₀ ▸ variance_nonneg _ _
  have hc₂ : 0 < V₀ + KV * (T / m) * (M + 1) + 1 := by positivity
  have h_iii : ∀ ℓ, variance (fineCoarseDiff
      (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => q.eval (path (m * M ^ ℓ))))
      (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
        (fun ℓ path => q.eval (path (m * M ^ ℓ)))) ℓ) stdNormalSeq ≤
      (V₀ + KV * (T / m) * (M + 1) + 1) * (2 : ℝ) ^ (-(Real.logb 2 M * (ℓ : ℝ))) := by
    intro ℓ
    rw [two_rpow_neg_logb_mul hM0]
    cases ℓ with
    | zero =>
      change variance (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
        (fun ℓ path => q.eval (path (m * M ^ ℓ))) 0) stdNormalSeq ≤ _
      rw [pow_zero, inv_one, mul_one, ← hV₀]
      have : 0 ≤ KV * (T / m) * (M + 1) := by positivity
      linarith
    | succ ℓ =>
      have hv := gbm_poly_correction_variance_le_M r σ s₀ hT hm hM0 q ℓ
      have hinv : 0 < ((M : ℝ) ^ (ℓ + 1))⁻¹ := by positivity
      calc _ ≤ KV * (T / m) * (M + 1) / (M : ℝ) ^ (ℓ + 1) := hv
        _ = KV * (T / m) * (M + 1) * ((M : ℝ) ^ (ℓ + 1))⁻¹ := by
          rw [div_eq_mul_inv]
        _ ≤ _ := by nlinarith
  -- (iv): a level-`ℓ` sample costs `m M^ℓ = m 2^{ℓ log₂ M}`
  have h_iv : ∀ ℓ : ℕ, (m : ℝ) * (M : ℝ) ^ ℓ ≤ m * (2 : ℝ) ^ (Real.logb 2 M * (ℓ : ℝ)) :=
    fun ℓ => by rw [two_rpow_logb_mul hM0]
  obtain ⟨c₄, hc₄, h⟩ := em_mlmc_theorem1_levels_M
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq)
    (gbmDrift r) (gbmVol σ) (T / m) s₀ hM0 (fun ℓ path => q.eval (path (m * M ^ ℓ))) P
    (fun p x => x p) (fun ℓ => (m : ℝ) * (M : ℝ) ^ ℓ) (α := Real.logb 2 M)
    (β := Real.logb 2 M) (γ := Real.logb 2 M) hβ hβ hc₁ hc₂ hm' (by rw [min_self]; linarith)
    hω hind (hP.integrable one_le_two) hPfm hPf h_i h_iii h_iv
  refine ⟨c₄, K1 (Real.logb 2 M) (CP * (T / m) + 1), hc₄, K1_pos hc₁, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost, hL⟩ := h ε hε hε1
  rw [hPint] at hint hmse
  rw [complexityBound_of_eq rfl ε] at hcost
  rw [two_rpow_logb_mul hM0] at hL
  exact ⟨L, N, hN, hint, hmse, hcost, hL⟩

/-- **Theorem 1 for the Euler–Maruyama MLMC estimator of GBM with a polynomial payoff** (Giles
2015, §5.1, p. 30, l. 1318–1321: "Alternatively, if `h_ℓ = 2^{−ℓ}h_0` with twice as many timesteps
on each successive level, as used in the numerical examples in this article, then `α = 1`, `β = 1`
and `γ = 1`. In either case, Theorem 1 gives the complexity to achieve a root-mean-square error of
`ε` to be `O(ε^{−2}(log ε)²)`"; §2.1, p. 7, l. 326: "Because of condition i), we have
`2^{−αL} = O(ε)`, and hence `C_L = O(ε^{−γ/α})`").  Let `dS = rS dt + σS dW`, `S_0 = s₀`, `T ≥ 0`,
and let `q` be any real polynomial (a payoff which is not Lipschitz unless `deg q ≤ 1`, so
`gbm_mlmc_theorem1` does not apply).  With the levels, corrections, independent samples and costs
`2^ℓ` of `gbm_mlmc_theorem1`, there are `c₄, c₅ > 0` such that for every `0 < ε < e⁻¹` there are
`L` and `N_ℓ ≥ 1` for which the multilevel estimator of `E[q(S_T)]` has a square-integrable error
with mean square `< ε²`, cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`, and finest level
`2^L ≤ c₅ ε⁻¹`.  The rates are proved: `α = 1` (`gbm_weak_error_poly`), `β = 1`
(`gbm_poly_correction_variance_le`) and `γ = 1`.  The case `m = 1`, `M = 2` of
`gbm_mlmc_theorem1_poly_M`. -/
theorem gbm_mlmc_theorem1_poly (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (q : Polynomial ℝ) :
    ∃ c₄ c₅ : ℝ, 0 < c₄ ∧ 0 < c₅ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff fun x => q.eval x))
              (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff fun x => q.eval x)))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff fun x => q.eval x))
              (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff fun x => q.eval x)))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, q.eval (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) ∧
        (2 : ℝ) ^ L ≤ c₅ / ε := by
  have H := gbm_mlmc_theorem1_poly_M r σ s₀ hT (m := 1) (M := 2) one_pos le_rfl q
  simp only [Nat.cast_one, div_one, one_mul, Nat.cast_ofNat, emFineM_two, emCoarseM_two] at H
  exact H

end MLMC
