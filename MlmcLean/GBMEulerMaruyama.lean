import MlmcLean.EulerMaruyama
import MlmcLean.FixedPointPath
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Geometric Brownian motion: the Euler–Maruyama MLMC estimator end to end (Giles 2015, §5.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1
"Euler–Maruyama discretisation" (pp. 29–30) and its Geometric Brownian Motion example
(Figure 5.3): `dS_t = r S_t dt + σ S_t dW` with a Lipschitz payoff such as the European call
`P(S) = e^{−rT} max(S_T − K, 0)`.

§5.1 takes the analytic inputs of Theorem 1 from the SDE literature: "the strong error for the
Euler discretisation with timestep `h` is `O(h^{1/2})`, so that `E[‖S − Ŝ‖²] = O(h)`", then
`V[P − P_ℓ] ≤ K² E[‖S − Ŝ_ℓ‖²]`, `V_ℓ ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`, hence `V_ℓ = O(h_ℓ)`, and
with `h_ℓ = 2^{−ℓ} h_0` Theorem 1 gives the complexity `O(ε⁻²(log ε)²)`.  For GBM the exact
solution is known in closed form, `S_T = S_0 exp((r − σ²/2) T + σ W_T)`, so every one of these
steps is proved here, with the exact solution and the Euler–Maruyama path driven by the same
Brownian increments `ΔW_i = √h Z_i`, `Z_i` independent standard normal (`stdNormalSeq`).

* `integral_exp_mul_gaussian`, `integral_mul_exp_mul_gaussian`, `integral_sq_gaussian`: the
  Gaussian moments `E[e^{aZ}] = e^{a²/2}`, `E[Z e^{aZ}] = a e^{a²/2}`, `E[Z²] = 1`.
* `emPath_gbm`: the Euler–Maruyama path is `Ŝ_n = S_0 ∏_{i<n} (1 + rh + σ√h Z_i)`;
  `gbmExp_eq_prod`: the exact solution on the grid is
  `S_{t_n} = S_0 ∏_{i<n} e^{(r − σ²/2)h + σ√h Z_i}`.
* `integral_sq_prod_sub_prod`: `E[(S_{t_n} − Ŝ_n)²] = S_0² (aⁿ − 2bⁿ + cⁿ)` with the one-step
  moments `a = e^{(2r+σ²)h}`, `b = e^{rh}(1 + rh + σ²h)`, `c = (1 + rh)² + σ²h`.
* `gbm_em_strong_error`: **the strong error of the Euler–Maruyama scheme**,
  `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h` at every grid time `t_n = nh`, with an explicit constant
  `gbmStrongConst` depending only on `r, σ, t_n, S_0` ("`E[‖S − Ŝ‖²] = O(h)`").
* `gbmExact_pairAvg`, `map_gbmExact`: the exact solution driven by the level-`ℓ` increments is the
  exact solution driven by the coarse increments `(Z_{2k} + Z_{2k+1})/√2` of level `ℓ + 1`
  ("summing the Brownian increments for the fine path timesteps to obtain the Brownian increments
  for the coarse timesteps"), and its law does not depend on the level.
* `gbm_weak_error_le`: for a `K`-Lipschitz payoff `g`, `|E[g(Ŝ_ℓ)] − E[g(S_T)]| = O(2^{−ℓ/2})`
  (weak rate `α = ½`, enough for Theorem 1 since `α ≥ ½ min(β, γ)`);
  `gbm_correction_variance_le`: `V_{ℓ+1} = V[g(Ŝ^f_{ℓ+1}) − g(Ŝ^c_ℓ)] = O(2^{−ℓ})` (`β = 1`).
* `gbm_mlmc_theorem1`: **Theorem 1 for the Euler–Maruyama MLMC estimator of `E[g(S_T)]`** for GBM,
  with no assumed rate: for every `0 < ε < e⁻¹` there are `L` and `N_ℓ` with mean square error
  `< ε²` and cost `∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace MLMC

/-! ### Gaussian moments -/

/-- `E[e^{aZ}] = e^{a²/2}` for a standard normal `Z` (the moment generating function of `N(0,1)`,
used for the moments of the GBM solution in Giles 2015, §5.1). -/
lemma integral_exp_mul_gaussian (a : ℝ) :
    ∫ x, Real.exp (a * x) ∂gaussianReal 0 1 = Real.exp (a ^ 2 / 2) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) a
  simp only [mgf, NNReal.coe_one, zero_mul, zero_add, one_mul] at h
  exact h

/-- Every real number is in the interior of the set where `e^{tZ}` is integrable, `Z ~ N(0,1)`. -/
lemma mem_interior_integrableExpSet_gaussian (a : ℝ) :
    a ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
  simp

/-- `E[Z e^{aZ}] = a e^{a²/2}` for a standard normal `Z` (the derivative of the moment generating
function; Giles 2015, §5.1, GBM example). -/
lemma integral_mul_exp_mul_gaussian (a : ℝ) :
    ∫ x, x * Real.exp (a * x) ∂gaussianReal 0 1 = a * Real.exp (a ^ 2 / 2) := by
  have h1 := hasDerivAt_mgf (mem_interior_integrableExpSet_gaussian a)
  have hm : mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t => Real.exp (t ^ 2 / 2) := by
    rw [mgf_fun_id_gaussianReal]
    funext t
    simp
  rw [hm] at h1
  have hp : HasDerivAt (fun t : ℝ => t ^ 2 / 2) a a :=
    ((hasDerivAt_pow 2 a).div_const 2).congr_deriv (by norm_num)
  exact (h1.unique hp.exp).trans (mul_comm _ _)

/-- `Z` is integrable for `Z ~ N(0,1)`. -/
lemma integrable_id_gaussian : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal' 2 (by simp)).integrable one_le_two

/-- `Z²` is integrable for `Z ~ N(0,1)`. -/
lemma integrable_sq_gaussian : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal' 2 (by simp)).integrable_sq

/-- `Z e^{aZ}` is integrable for `Z ~ N(0,1)`. -/
lemma integrable_mul_exp_mul_gaussian (a : ℝ) :
    Integrable (fun x : ℝ => x * Real.exp (a * x)) (gaussianReal 0 1) := by
  simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (mem_interior_integrableExpSet_gaussian a) 1

/-- `E[Z²] = 1` for `Z ~ N(0,1)`. -/
lemma integral_sq_gaussian : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

/-! ### One time step -/

/-- One step of the exact GBM solution, `e^{(r − σ²/2)h + σ√h Z}` (Giles 2015, §5.1, GBM example:
`S_{t+h} = S_t e^{(r − σ²/2)h + σ(W_{t+h} − W_t)}` with `W_{t+h} − W_t = √h Z`). -/
noncomputable def gbmExpFactor (r σ h x : ℝ) : ℝ :=
  Real.exp ((r - σ ^ 2 / 2) * h + σ * Real.sqrt h * x)

/-- One Euler–Maruyama step of GBM, `1 + rh + σ√h Z` (Giles 2015, §5.1:
`Ŝ_{n+1} = Ŝ_n + a(Ŝ_n, t_n) h + b(Ŝ_n, t_n) ΔW_n` with `a(S, t) = rS`, `b(S, t) = σS`). -/
noncomputable def gbmEMFactor (r σ h x : ℝ) : ℝ := 1 + r * h + σ * Real.sqrt h * x

lemma measurable_gbmExpFactor (r σ h : ℝ) : Measurable fun x => gbmExpFactor r σ h x := by
  unfold gbmExpFactor
  fun_prop

lemma measurable_gbmEMFactor (r σ h : ℝ) : Measurable fun x => gbmEMFactor r σ h x := by
  unfold gbmEMFactor
  fun_prop

lemma gbmExpFactor_sq (r σ h x : ℝ) :
    gbmExpFactor r σ h x ^ 2 =
      Real.exp (2 * ((r - σ ^ 2 / 2) * h)) * Real.exp (2 * σ * Real.sqrt h * x) := by
  rw [gbmExpFactor, sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma gbmEMFactor_sq (r σ h x : ℝ) :
    gbmEMFactor r σ h x ^ 2 = (1 + r * h) ^ 2 + 2 * (1 + r * h) * (σ * Real.sqrt h) * x +
      (σ * Real.sqrt h) ^ 2 * x ^ 2 := by
  rw [gbmEMFactor]
  ring

lemma gbmExpFactor_mul_gbmEMFactor (r σ h x : ℝ) :
    gbmExpFactor r σ h x * gbmEMFactor r σ h x =
      Real.exp ((r - σ ^ 2 / 2) * h) * (1 + r * h) * Real.exp (σ * Real.sqrt h * x) +
        Real.exp ((r - σ ^ 2 / 2) * h) * (σ * Real.sqrt h) *
          (x * Real.exp (σ * Real.sqrt h * x)) := by
  rw [gbmExpFactor, gbmEMFactor, Real.exp_add]
  ring

lemma integrable_gbmExpFactor_sq (r σ h : ℝ) :
    Integrable (fun x => gbmExpFactor r σ h x ^ 2) (gaussianReal 0 1) := by
  simp_rw [gbmExpFactor_sq]
  exact (integrable_exp_mul_gaussianReal (2 * σ * Real.sqrt h)).const_mul
    (Real.exp (2 * ((r - σ ^ 2 / 2) * h)))

lemma integrable_gbmEMFactor_sq (r σ h : ℝ) :
    Integrable (fun x => gbmEMFactor r σ h x ^ 2) (gaussianReal 0 1) := by
  simp_rw [gbmEMFactor_sq]
  exact ((integrable_const ((1 + r * h) ^ 2)).add
    (integrable_id_gaussian.const_mul (2 * (1 + r * h) * (σ * Real.sqrt h)))).add
      (integrable_sq_gaussian.const_mul ((σ * Real.sqrt h) ^ 2))

lemma integrable_gbmExpFactor_mul_gbmEMFactor (r σ h : ℝ) :
    Integrable (fun x => gbmExpFactor r σ h x * gbmEMFactor r σ h x) (gaussianReal 0 1) := by
  simp_rw [gbmExpFactor_mul_gbmEMFactor]
  exact ((integrable_exp_mul_gaussianReal (σ * Real.sqrt h)).const_mul
      (Real.exp ((r - σ ^ 2 / 2) * h) * (1 + r * h))).add
    ((integrable_mul_exp_mul_gaussian (σ * Real.sqrt h)).const_mul
      (Real.exp ((r - σ ^ 2 / 2) * h) * (σ * Real.sqrt h)))

/-- `E[A²] = e^{(2r + σ²)h}` for the exact step `A = e^{(r − σ²/2)h + σ√h Z}`. -/
lemma integral_gbmExpFactor_sq (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ x, gbmExpFactor r σ h x ^ 2 ∂gaussianReal 0 1 = Real.exp ((2 * r + σ ^ 2) * h) := by
  simp_rw [gbmExpFactor_sq]
  rw [integral_const_mul, integral_exp_mul_gaussian, ← Real.exp_add]
  congr 1
  rw [mul_pow, mul_pow, Real.sq_sqrt hh]
  ring

/-- `E[B²] = (1 + rh)² + σ²h` for the Euler–Maruyama step `B = 1 + rh + σ√h Z`. -/
lemma integral_gbmEMFactor_sq (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ x, gbmEMFactor r σ h x ^ 2 ∂gaussianReal 0 1 = (1 + r * h) ^ 2 + σ ^ 2 * h := by
  simp_rw [gbmEMFactor_sq]
  have i1 : Integrable (fun x : ℝ => (1 + r * h) ^ 2 + 2 * (1 + r * h) * (σ * Real.sqrt h) * x)
      (gaussianReal 0 1) :=
    (integrable_const _).add (integrable_id_gaussian.const_mul _)
  have i2 : Integrable (fun x : ℝ => (σ * Real.sqrt h) ^ 2 * x ^ 2) (gaussianReal 0 1) :=
    integrable_sq_gaussian.const_mul _
  have i3 : Integrable (fun x : ℝ => 2 * (1 + r * h) * (σ * Real.sqrt h) * x)
      (gaussianReal 0 1) :=
    integrable_id_gaussian.const_mul _
  rw [integral_add i1 i2, integral_add (integrable_const _) i3, integral_const, probReal_univ,
    one_smul, integral_const_mul, integral_const_mul, integral_id_gaussianReal,
    integral_sq_gaussian, mul_pow, Real.sq_sqrt hh]
  ring

/-- `E[AB] = e^{rh}(1 + rh + σ²h)` for the exact and the Euler–Maruyama steps driven by the same
increment. -/
lemma integral_gbmExpFactor_mul_gbmEMFactor (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ x, gbmExpFactor r σ h x * gbmEMFactor r σ h x ∂gaussianReal 0 1 =
      Real.exp (r * h) * (1 + r * h + σ ^ 2 * h) := by
  simp_rw [gbmExpFactor_mul_gbmEMFactor]
  have i1 : Integrable (fun x : ℝ => Real.exp ((r - σ ^ 2 / 2) * h) * (1 + r * h) *
      Real.exp (σ * Real.sqrt h * x)) (gaussianReal 0 1) :=
    (integrable_exp_mul_gaussianReal _).const_mul _
  have i2 : Integrable (fun x : ℝ => Real.exp ((r - σ ^ 2 / 2) * h) * (σ * Real.sqrt h) *
      (x * Real.exp (σ * Real.sqrt h * x))) (gaussianReal 0 1) :=
    (integrable_mul_exp_mul_gaussian _).const_mul _
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  have he : Real.exp (r * h) = Real.exp ((r - σ ^ 2 / 2) * h) * Real.exp (σ ^ 2 * h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_exp_mul_gaussian,
    integral_mul_exp_mul_gaussian, hs, he]
  have hs' : σ * Real.sqrt h * (σ * Real.sqrt h) = σ ^ 2 * h := by
    rw [← hs]
    ring
  linear_combination (Real.exp ((r - σ ^ 2 / 2) * h) * Real.exp (σ ^ 2 * h / 2)) * hs'

/-! ### Products over independent increments -/

/-- `E[∏_{i<n} F(Z_i)] = (E[F(Z)])ⁿ` for independent standard normal `Z_i`. -/
lemma integral_prod_stdNormalSeq {F : ℝ → ℝ} (hF : Measurable F) (n : ℕ) :
    ∫ z, ∏ i ∈ range n, F (z i) ∂stdNormalSeq = (∫ x, F x ∂gaussianReal 0 1) ^ n := by
  have hind : iIndepFun (fun i (z : ℕ → ℝ) => F (z i)) stdNormalSeq :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ x => F x) fun _ => hF
  rw [integral_prod_of_iIndepFun hind (fun i => hF.comp (measurable_pi_apply i))]
  have h1 : ∀ i, ∫ z, F (z i) ∂stdNormalSeq = ∫ x, F x ∂gaussianReal 0 1 := fun i =>
    integral_comp_of_measurePreserving
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i) hF.aestronglyMeasurable
  simp only [h1, Finset.prod_const, Finset.card_range]

/-- `∏_{i<n} F(Z_i)` is integrable for independent standard normal `Z_i` if `F(Z)` is. -/
lemma integrable_prod_stdNormalSeq {F : ℝ → ℝ} (hF : Measurable F)
    (hFi : Integrable F (gaussianReal 0 1)) (n : ℕ) :
    Integrable (fun z : ℕ → ℝ => ∏ i ∈ range n, F (z i)) stdNormalSeq := by
  have hind : iIndepFun (fun i (z : ℕ → ℝ) => F (z i)) stdNormalSeq :=
    iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ x => F x) fun _ => hF
  exact integrable_prod_of_iIndepFun hind (fun i => hF.comp (measurable_pi_apply i))
    (fun i => ((measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i).integrable_comp
      hF.aestronglyMeasurable).2 hFi) (range n)

/-! ### The exact solution and the Euler–Maruyama path -/

/-- The GBM drift `a(S, t) = rS` (Giles 2015, §5.1: `dS_t = r S_t dt + σ S_t dW`). -/
noncomputable def gbmDrift (r : ℝ) : ℝ → ℝ → ℝ := fun S _ => r * S

/-- The GBM volatility `b(S, t) = σS` (Giles 2015, §5.1: `dS_t = r S_t dt + σ S_t dW`). -/
noncomputable def gbmVol (σ : ℝ) : ℝ → ℝ → ℝ := fun S _ => σ * S

/-- **The Euler–Maruyama path of GBM is a product** (Giles 2015, §5.1):
`Ŝ_n = S_0 ∏_{i<n} (1 + rh + σ√h Z_i)`. -/
theorem emPath_gbm (r σ h s₀ : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    emPath (gbmDrift r) (gbmVol σ) h s₀ z n = s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) := by
  induction n with
  | zero => simp [emPath]
  | succ n ih =>
    rw [emPath_succ, ih, Finset.prod_range_succ]
    simp only [gbmDrift, gbmVol, gbmEMFactor]
    ring

/-- **The exact GBM solution on the grid is a product** (Giles 2015, §5.1, GBM example):
`S_0 exp((r − σ²/2) t_n + σ W_{t_n}) = S_0 ∏_{i<n} e^{(r − σ²/2)h + σ√h Z_i}` for `t_n = nh` and
`W_{t_n} = √h ∑_{i<n} Z_i`. -/
theorem gbmExp_eq_prod (r σ h s₀ : ℝ) (n : ℕ) (z : ℕ → ℝ) :
    s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) =
      s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) := by
  unfold gbmExpFactor
  rw [← Real.exp_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum]
  congr 2
  ring

/-- `2^ℓ (T/2^ℓ) = T`. -/
lemma cast_two_pow_mul_div (T : ℝ) (ℓ : ℕ) : ((2 ^ ℓ : ℕ) : ℝ) * (T / 2 ^ ℓ) = T := by
  push_cast
  exact mul_div_cancel₀ T (by positivity)

/-- The exact solution of the GBM SDE `dS = rS dt + σS dW` at time `T` (Giles 2015, §5.1, GBM
example), `S_T = S_0 exp((r − σ²/2)T + σ W_T)`, with the Brownian motion sampled on the level-`ℓ`
grid: `W_T = √h_ℓ ∑_{i<2^ℓ} Z_i`, `h_ℓ = T 2^{−ℓ}`, driven by the same increments `Z_i` as the
level-`ℓ` Euler–Maruyama path. -/
noncomputable def gbmExact (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt (T / 2 ^ ℓ) * ∑ i ∈ range (2 ^ ℓ), z i))

/-- The level-`ℓ` Euler–Maruyama approximation of `S_T` for GBM (Giles 2015, §5.1): `2^ℓ` steps
of size `h_ℓ = T 2^{−ℓ}` driven by the increments `Z_i`. -/
noncomputable def gbmEM (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  emPath (gbmDrift r) (gbmVol σ) (T / 2 ^ ℓ) s₀ z (2 ^ ℓ)

lemma gbmExact_eq_prod (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmExact r σ T s₀ ℓ z = s₀ * ∏ i ∈ range (2 ^ ℓ), gbmExpFactor r σ (T / 2 ^ ℓ) (z i) := by
  unfold gbmExact
  rw [← gbmExp_eq_prod, cast_two_pow_mul_div]

lemma gbmEM_eq_prod (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmEM r σ T s₀ ℓ z = s₀ * ∏ i ∈ range (2 ^ ℓ), gbmEMFactor r σ (T / 2 ^ ℓ) (z i) :=
  emPath_gbm r σ (T / 2 ^ ℓ) s₀ z (2 ^ ℓ)

lemma measurable_gbmExact (r σ T s₀ : ℝ) (ℓ : ℕ) : Measurable (gbmExact r σ T s₀ ℓ) := by
  have hs : Measurable fun z : ℕ → ℝ => ∑ i ∈ range (2 ^ ℓ), z i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact (((hs.const_mul (Real.sqrt (T / 2 ^ ℓ))).const_mul σ).const_add
    ((r - σ ^ 2 / 2) * T)).exp.const_mul s₀

lemma measurable_gbmEM (r σ T s₀ : ℝ) (ℓ : ℕ) : Measurable (gbmEM r σ T s₀ ℓ) := by
  have e : gbmEM r σ T s₀ ℓ =
      fun z => s₀ * ∏ i ∈ range (2 ^ ℓ), gbmEMFactor r σ (T / 2 ^ ℓ) (z i) :=
    funext (gbmEM_eq_prod r σ T s₀ ℓ)
  rw [e]
  exact (Finset.measurable_prod _ fun i _ =>
    (measurable_gbmEMFactor r σ (T / 2 ^ ℓ)).comp (measurable_pi_apply i)).const_mul s₀

lemma memLp_gbmExact (r σ T s₀ : ℝ) (ℓ : ℕ) : MemLp (gbmExact r σ T s₀ ℓ) 2 stdNormalSeq := by
  refine (memLp_two_iff_integrable_sq (measurable_gbmExact r σ T s₀ ℓ).aestronglyMeasurable).2 ?_
  have e : (fun z => gbmExact r σ T s₀ ℓ z ^ 2) =
      fun z => s₀ ^ 2 * ∏ i ∈ range (2 ^ ℓ), gbmExpFactor r σ (T / 2 ^ ℓ) (z i) ^ 2 := by
    funext z
    rw [gbmExact_eq_prod, mul_pow, ← Finset.prod_pow]
  rw [e]
  exact (integrable_prod_stdNormalSeq ((measurable_gbmExpFactor r σ _).pow_const 2)
    (integrable_gbmExpFactor_sq r σ _) _).const_mul _

lemma memLp_gbmEM (r σ T s₀ : ℝ) (ℓ : ℕ) : MemLp (gbmEM r σ T s₀ ℓ) 2 stdNormalSeq := by
  refine (memLp_two_iff_integrable_sq (measurable_gbmEM r σ T s₀ ℓ).aestronglyMeasurable).2 ?_
  have e : (fun z => gbmEM r σ T s₀ ℓ z ^ 2) =
      fun z => s₀ ^ 2 * ∏ i ∈ range (2 ^ ℓ), gbmEMFactor r σ (T / 2 ^ ℓ) (z i) ^ 2 := by
    funext z
    rw [gbmEM_eq_prod, mul_pow, ← Finset.prod_pow]
  rw [e]
  exact (integrable_prod_stdNormalSeq ((measurable_gbmEMFactor r σ _).pow_const 2)
    (integrable_gbmEMFactor_sq r σ _) _).const_mul _

/-! ### The coupling of the levels -/

/-- `∑_{i<2n} f(i) = ∑_{k<n} (f(2k) + f(2k+1))`. -/
lemma sum_range_two_mul (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- **The exact solution is consistent across levels** (Giles 2015, §5.1: "summing the Brownian
increments for the fine path timesteps to obtain the Brownian increments for the coarse
timesteps").  The exact solution driven by the coarse increments `(Z_{2k} + Z_{2k+1})/√2` on the
level-`ℓ` grid is the exact solution driven by the increments `Z_i` on the level-`(ℓ+1)` grid: both
use the same Brownian value `W_T`. -/
theorem gbmExact_pairAvg (r σ T s₀ : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmExact r σ T s₀ ℓ (pairAvg z) = gbmExact r σ T s₀ (ℓ + 1) z := by
  have key : Real.sqrt (T / 2 ^ ℓ) * ∑ i ∈ range (2 ^ ℓ), pairAvg z i =
      Real.sqrt (T / 2 ^ (ℓ + 1)) * ∑ i ∈ range (2 ^ (ℓ + 1)), z i := by
    rw [show (2 : ℕ) ^ (ℓ + 1) = 2 * 2 ^ ℓ from pow_succ' 2 ℓ,
      show (2 : ℝ) ^ (ℓ + 1) = 2 ^ ℓ * 2 from pow_succ 2 ℓ, sum_range_two_mul, ← div_div,
      Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [pairAvg]
    rw [← Finset.sum_div]
    ring
  unfold gbmExact
  rw [key]

/-- **The law of the exact solution does not depend on the level** (Giles 2015, §5.1): under
`N(0,1)^{⊗ℕ}`, `S_T` computed from the level-`ℓ` increments has the law of `S_T` computed from the
single increment of level `0`. -/
theorem map_gbmExact (r σ T s₀ : ℝ) (ℓ : ℕ) :
    stdNormalSeq.map (gbmExact r σ T s₀ ℓ) = stdNormalSeq.map (gbmExact r σ T s₀ 0) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    have e : gbmExact r σ T s₀ (ℓ + 1) = gbmExact r σ T s₀ ℓ ∘ pairAvg :=
      funext fun z => (gbmExact_pairAvg r σ T s₀ ℓ z).symm
    rw [e, ← Measure.map_map (measurable_gbmExact r σ T s₀ ℓ)
      measurePreserving_pairAvg.measurable, measurePreserving_pairAvg.map_eq, ih]

lemma integral_comp_gbmExact (r σ T s₀ : ℝ) (ℓ : ℕ) {F : ℝ → ℝ} (hF : Measurable F) :
    ∫ z, F (gbmExact r σ T s₀ ℓ z) ∂stdNormalSeq =
      ∫ z, F (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq := by
  rw [← integral_map (measurable_gbmExact r σ T s₀ ℓ).aemeasurable hF.aestronglyMeasurable,
    ← integral_map (measurable_gbmExact r σ T s₀ 0).aemeasurable hF.aestronglyMeasurable,
    map_gbmExact r σ T s₀ ℓ]

/-- At level `0` the exact solution is `S_0 exp((r − σ²/2)T + σ √T Z_0)`. -/
lemma gbmExact_zero (r σ T s₀ : ℝ) (z : ℕ → ℝ) :
    gbmExact r σ T s₀ 0 z = s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * z 0)) := by
  unfold gbmExact
  simp only [pow_zero, div_one, Finset.range_one, Finset.sum_singleton]

/-! ### The strong error -/

/-- `aⁿ − 2bⁿ + cⁿ ≤ n Mⁿ (|a − b| + |c − b|)` for `|a|, |b|, |c| ≤ M` with `M ≥ 1`. -/
lemma pow_sub_two_mul_pow_add_pow_le {a b c M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M)
    (hM : 1 ≤ M) (n : ℕ) :
    a ^ n - 2 * b ^ n + c ^ n ≤ n * M ^ n * (|a - b| + |c - b|) := by
  have hmax : ∀ x y : ℝ, |x| ≤ M → |y| ≤ M → max |x| |y| ^ (n - 1) ≤ M ^ n := fun x y hx hy =>
    (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg x)) (max_le hx hy) (n - 1)).trans
      (pow_le_pow_right₀ hM (Nat.sub_le n 1))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 := abs_pow_sub_pow_le a b n
  have h2 := abs_pow_sub_pow_le c b n
  have e1 : |a - b| * n * max |a| |b| ^ (n - 1) ≤ |a - b| * n * M ^ n :=
    mul_le_mul_of_nonneg_left (hmax a b ha hb) (mul_nonneg (abs_nonneg _) hn)
  have e2 : |c - b| * n * max |c| |b| ^ (n - 1) ≤ |c - b| * n * M ^ n :=
    mul_le_mul_of_nonneg_left (hmax c b hc hb) (mul_nonneg (abs_nonneg _) hn)
  have e3 := le_abs_self (a ^ n - b ^ n)
  have e4 := le_abs_self (c ^ n - b ^ n)
  linarith

/-- `aⁿ − 2bⁿ + cⁿ ≤ 4Mⁿ` for `|a|, |b|, |c| ≤ M`. -/
lemma pow_sub_two_mul_pow_add_pow_le_four {a b c M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M)
    (hc : |c| ≤ M) (n : ℕ) :
    a ^ n - 2 * b ^ n + c ^ n ≤ 4 * M ^ n := by
  have h : ∀ x : ℝ, |x| ≤ M → |x ^ n| ≤ M ^ n := fun x hx => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx n
  have h1 := h a ha
  have h2 := h b hb
  have h3 := h c hc
  have e1 := le_abs_self (a ^ n)
  have e2 := neg_le_abs (b ^ n)
  have e3 := le_abs_self (c ^ n)
  linarith

/-- The one-step second moments are bounded by `M = e^{(2|r| + σ²)h}`. -/
lemma gbm_one_step_bounds (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |Real.exp ((2 * r + σ ^ 2) * h)| ≤ Real.exp ((2 * |r| + σ ^ 2) * h) ∧
      |Real.exp (r * h) * (1 + r * h + σ ^ 2 * h)| ≤ Real.exp ((2 * |r| + σ ^ 2) * h) ∧
      |(1 + r * h) ^ 2 + σ ^ 2 * h| ≤ Real.exp ((2 * |r| + σ ^ 2) * h) := by
  have hr1 : r * h ≤ |r| * h := mul_le_mul_of_nonneg_right (le_abs_self r) hh
  have hr2 : -(|r| * h) ≤ r * h := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le r) hh
    linarith
  have hσ : 0 ≤ σ ^ 2 * h := mul_nonneg (sq_nonneg σ) hh
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith [le_abs_self r]) hh)
  · have h1 : |1 + r * h + σ ^ 2 * h| ≤ Real.exp ((|r| + σ ^ 2) * h) := by
      have := Real.add_one_le_exp ((|r| + σ ^ 2) * h)
      rw [abs_le]
      constructor <;> linarith
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (r * h) * |1 + r * h + σ ^ 2 * h|
        ≤ Real.exp (r * h) * Real.exp ((|r| + σ ^ 2) * h) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp ((r + |r| + σ ^ 2) * h) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp ((2 * |r| + σ ^ 2) * h) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith [le_abs_self r]) hh)
  · have hc0 : 0 ≤ (1 + r * h) ^ 2 + σ ^ 2 * h := add_nonneg (sq_nonneg _) hσ
    rw [abs_of_nonneg hc0]
    have e1 : |1 + r * h| ≤ Real.exp (|r| * h) := by
      have := Real.add_one_le_exp (|r| * h)
      rw [abs_le]
      constructor <;> linarith
    have h1 : (1 + r * h) ^ 2 ≤ Real.exp (|r| * h) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) e1 2
    have h2 : Real.exp (|r| * h) ^ 2 = Real.exp (2 * |r| * h) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h3 : 1 ≤ Real.exp (2 * |r| * h) :=
      Real.one_le_exp (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg r)) hh)
    have h4 : 1 + σ ^ 2 * h ≤ Real.exp (σ ^ 2 * h) := by
      have := Real.add_one_le_exp (σ ^ 2 * h)
      linarith
    have h5 : Real.exp ((2 * |r| + σ ^ 2) * h) = Real.exp (2 * |r| * h) * Real.exp (σ ^ 2 * h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h5]
    linarith [mul_nonneg (sub_nonneg.2 h3) hσ,
      mul_le_mul_of_nonneg_left h4 (zero_le_one.trans h3)]

/-- For `(|r| + σ²)h ≤ 1` the one-step moments agree to second order:
`|a − b| ≤ 3((|r| + σ²)h)²` and `|c − b| ≤ 2((|r| + σ²)h)²`. -/
lemma gbm_one_step_diff (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (hs : (|r| + σ ^ 2) * h ≤ 1) :
    |Real.exp ((2 * r + σ ^ 2) * h) - Real.exp (r * h) * (1 + r * h + σ ^ 2 * h)| ≤
        3 * ((|r| + σ ^ 2) * h) ^ 2 ∧
      |(1 + r * h) ^ 2 + σ ^ 2 * h - Real.exp (r * h) * (1 + r * h + σ ^ 2 * h)| ≤
        2 * ((|r| + σ ^ 2) * h) ^ 2 := by
  have hr1 : r * h ≤ |r| * h := mul_le_mul_of_nonneg_right (le_abs_self r) hh
  have hr2 : -(|r| * h) ≤ r * h := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le r) hh
    linarith
  have hσ : 0 ≤ σ ^ 2 * h := mul_nonneg (sq_nonneg σ) hh
  have hrh : 0 ≤ |r| * h := mul_nonneg (abs_nonneg r) hh
  refine ⟨?_, ?_⟩
  · have hy2 : |(r + σ ^ 2) * h| ≤ (|r| + σ ^ 2) * h := by
      rw [abs_le]
      constructor <;> linarith
    have hE := Real.abs_exp_sub_one_sub_id_le (hy2.trans hs)
    have hy3 : ((r + σ ^ 2) * h) ^ 2 ≤ ((|r| + σ ^ 2) * h) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hy2 2
      rwa [sq_abs] at this
    have hexp : Real.exp (r * h) ≤ 3 :=
      (Real.exp_le_exp.2 (by linarith : r * h ≤ 1)).trans Real.exp_one_lt_three.le
    have e : Real.exp ((2 * r + σ ^ 2) * h) - Real.exp (r * h) * (1 + r * h + σ ^ 2 * h) =
        Real.exp (r * h) * (Real.exp ((r + σ ^ 2) * h) - 1 - (r + σ ^ 2) * h) := by
      have : Real.exp ((2 * r + σ ^ 2) * h) = Real.exp (r * h) * Real.exp ((r + σ ^ 2) * h) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this]
      ring
    rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hexp (hE.trans hy3) (abs_nonneg _) (by norm_num)
  · have hy : |r * h| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hE1 := Real.abs_exp_sub_one_sub_id_le hy
    have hE2 := Real.abs_exp_sub_one_le hy
    have e : (1 + r * h) ^ 2 + σ ^ 2 * h - Real.exp (r * h) * (1 + r * h + σ ^ 2 * h) =
        -((1 + r * h) * (Real.exp (r * h) - 1 - r * h) + σ ^ 2 * h * (Real.exp (r * h) - 1)) := by
      ring
    have hy' := abs_le.1 hy
    have h1 : |1 + r * h| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hy'.1, hy'.2]
    have e1 : |r * h| = |r| * h := by rw [abs_mul, abs_of_nonneg hh]
    have e2 : (r * h) ^ 2 = (|r| * h) ^ 2 := by rw [← e1, sq_abs]
    rw [e, abs_neg]
    calc |(1 + r * h) * (Real.exp (r * h) - 1 - r * h) + σ ^ 2 * h * (Real.exp (r * h) - 1)|
        ≤ |(1 + r * h) * (Real.exp (r * h) - 1 - r * h)| +
            |σ ^ 2 * h * (Real.exp (r * h) - 1)| := abs_add_le _ _
      _ = |1 + r * h| * |Real.exp (r * h) - 1 - r * h| +
            σ ^ 2 * h * |Real.exp (r * h) - 1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hσ]
      _ ≤ 2 * (r * h) ^ 2 + σ ^ 2 * h * (2 * |r * h|) :=
          add_le_add (mul_le_mul h1 hE1 (abs_nonneg _) zero_le_two)
            (mul_le_mul_of_nonneg_left hE2 hσ)
      _ ≤ 2 * ((|r| + σ ^ 2) * h) ^ 2 := by
          rw [e1, e2]
          linarith [mul_nonneg hrh hσ, sq_nonneg (σ ^ 2 * h)]

/-- **The algebraic core of the strong error**: `aⁿ − 2bⁿ + cⁿ ≤ e^{(2|r|+σ²)nh} (|r| + σ²)
(5(|r| + σ²) nh + 4) h` for the one-step moments `a, b, c` of `gbm_one_step_bounds`. -/
lemma gbm_moment_combo_le (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    Real.exp ((2 * r + σ ^ 2) * h) ^ n - 2 * (Real.exp (r * h) * (1 + r * h + σ ^ 2 * h)) ^ n +
        ((1 + r * h) ^ 2 + σ ^ 2 * h) ^ n ≤
      Real.exp ((2 * |r| + σ ^ 2) * (n * h)) * (|r| + σ ^ 2) *
        (5 * (|r| + σ ^ 2) * (n * h) + 4) * h := by
  obtain ⟨ha, hb, hc⟩ := gbm_one_step_bounds r σ hh
  have hM1 : 1 ≤ Real.exp ((2 * |r| + σ ^ 2) * h) :=
    Real.one_le_exp (mul_nonneg (by positivity) hh)
  have hMn : Real.exp ((2 * |r| + σ ^ 2) * h) ^ n = Real.exp ((2 * |r| + σ ^ 2) * (n * h)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hq : 0 ≤ |r| + σ ^ 2 := by positivity
  have hE : 0 < Real.exp ((2 * |r| + σ ^ 2) * (n * h)) := Real.exp_pos _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hs : (|r| + σ ^ 2) * h ≤ 1
  · obtain ⟨hab, hcb⟩ := gbm_one_step_diff r σ hh hs
    have h1 := pow_sub_two_mul_pow_add_pow_le ha hb hc hM1 n
    rw [hMn] at h1
    have h2 := mul_le_mul_of_nonneg_left (add_le_add hab hcb) (mul_nonneg hn hE.le)
    linarith [mul_nonneg (mul_nonneg hE.le hq) hh]
  · have hs : 1 < (|r| + σ ^ 2) * h := not_le.mp hs
    have h1 := pow_sub_two_mul_pow_add_pow_le_four ha hb hc n
    rw [hMn] at h1
    linarith [mul_nonneg (mul_nonneg hE.le hn) (sq_nonneg ((|r| + σ ^ 2) * h)),
      mul_nonneg hE.le (sub_nonneg.2 hs.le)]

/-- The second moment of the difference of the two products:
`E[(S_0 ∏ A_i − S_0 ∏ B_i)²] = S_0² (aⁿ − 2bⁿ + cⁿ)`. -/
lemma integral_sq_prod_sub_prod (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) (s₀ : ℝ) (n : ℕ) :
    ∫ z, (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) -
        s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i)) ^ 2 ∂stdNormalSeq =
      s₀ ^ 2 * (Real.exp ((2 * r + σ ^ 2) * h) ^ n -
        2 * (Real.exp (r * h) * (1 + r * h + σ ^ 2 * h)) ^ n +
          ((1 + r * h) ^ 2 + σ ^ 2 * h) ^ n) := by
  have hA2 : Measurable fun x => gbmExpFactor r σ h x ^ 2 :=
    (measurable_gbmExpFactor r σ h).pow_const 2
  have hB2 : Measurable fun x => gbmEMFactor r σ h x ^ 2 :=
    (measurable_gbmEMFactor r σ h).pow_const 2
  have hAB : Measurable fun x => gbmExpFactor r σ h x * gbmEMFactor r σ h x :=
    (measurable_gbmExpFactor r σ h).mul (measurable_gbmEMFactor r σ h)
  have e : ∀ z : ℕ → ℝ, (s₀ * ∏ i ∈ range n, gbmExpFactor r σ h (z i) -
      s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i)) ^ 2 =
      s₀ ^ 2 * ∏ i ∈ range n, gbmExpFactor r σ h (z i) ^ 2 -
        2 * s₀ ^ 2 * ∏ i ∈ range n, (gbmExpFactor r σ h (z i) * gbmEMFactor r σ h (z i)) +
        s₀ ^ 2 * ∏ i ∈ range n, gbmEMFactor r σ h (z i) ^ 2 := fun z => by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow]
    ring
  simp_rw [e]
  have iA : Integrable (fun z : ℕ → ℝ => s₀ ^ 2 * ∏ i ∈ range n, gbmExpFactor r σ h (z i) ^ 2)
      stdNormalSeq :=
    (integrable_prod_stdNormalSeq hA2 (integrable_gbmExpFactor_sq r σ h) n).const_mul _
  have iAB : Integrable (fun z : ℕ → ℝ =>
      2 * s₀ ^ 2 * ∏ i ∈ range n, (gbmExpFactor r σ h (z i) * gbmEMFactor r σ h (z i)))
      stdNormalSeq :=
    (integrable_prod_stdNormalSeq hAB (integrable_gbmExpFactor_mul_gbmEMFactor r σ h) n).const_mul _
  have iB : Integrable (fun z : ℕ → ℝ => s₀ ^ 2 * ∏ i ∈ range n, gbmEMFactor r σ h (z i) ^ 2)
      stdNormalSeq :=
    (integrable_prod_stdNormalSeq hB2 (integrable_gbmEMFactor_sq r σ h) n).const_mul _
  have iAAB : Integrable (fun z : ℕ → ℝ =>
      s₀ ^ 2 * ∏ i ∈ range n, gbmExpFactor r σ h (z i) ^ 2 -
        2 * s₀ ^ 2 * ∏ i ∈ range n, (gbmExpFactor r σ h (z i) * gbmEMFactor r σ h (z i)))
      stdNormalSeq :=
    iA.sub iAB
  rw [integral_add iAAB iB, integral_sub iA iAB, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_prod_stdNormalSeq hA2, integral_prod_stdNormalSeq hAB,
    integral_prod_stdNormalSeq hB2, integral_gbmExpFactor_sq r σ hh,
    integral_gbmExpFactor_mul_gbmEMFactor r σ hh, integral_gbmEMFactor_sq r σ hh]
  ring

/-- The constant of the strong error bound for GBM,
`C(t) = S_0² e^{(2|r| + σ²)t} (|r| + σ²)(5(|r| + σ²)t + 4)` (Giles 2015, §5.1). -/
noncomputable def gbmStrongConst (r σ t s₀ : ℝ) : ℝ :=
  s₀ ^ 2 * Real.exp ((2 * |r| + σ ^ 2) * t) * (|r| + σ ^ 2) * (5 * (|r| + σ ^ 2) * t + 4)

lemma gbmStrongConst_nonneg (r σ s₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gbmStrongConst r σ t s₀ := by
  unfold gbmStrongConst
  positivity

/-- **The strong error of the Euler–Maruyama scheme for GBM** (Giles 2015, §5.1: "the strong error
for the Euler discretisation with timestep `h` is `O(h^{1/2})`, so that `E[‖S − Ŝ‖²] = O(h)`").
With timestep `h ≥ 0`, the exact solution `S_{t_n} = S_0 exp((r − σ²/2) t_n + σ W_{t_n})` at the
grid time `t_n = nh`, `W_{t_n} = √h ∑_{i<n} Z_i`, and the Euler–Maruyama value `Ŝ_n` driven by the
same increments satisfy `E[(S_{t_n} − Ŝ_n)²] ≤ C(t_n) h`, where
`C(t) = S_0² e^{(2|r| + σ²)t} (|r| + σ²)(5(|r| + σ²)t + 4)`. -/
theorem gbm_em_strong_error (r σ s₀ : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    ∫ z, (s₀ * Real.exp ((r - σ ^ 2 / 2) * (n * h) + σ * (Real.sqrt h * ∑ i ∈ range n, z i)) -
        emPath (gbmDrift r) (gbmVol σ) h s₀ z n) ^ 2 ∂stdNormalSeq ≤
      gbmStrongConst r σ (n * h) s₀ * h := by
  simp_rw [gbmExp_eq_prod, emPath_gbm]
  rw [integral_sq_prod_sub_prod r σ hh s₀ n, gbmStrongConst]
  have := gbm_moment_combo_le r σ hh n
  calc _ ≤ s₀ ^ 2 * (Real.exp ((2 * |r| + σ ^ 2) * (n * h)) * (|r| + σ ^ 2) *
          (5 * (|r| + σ ^ 2) * (n * h) + 4) * h) :=
        mul_le_mul_of_nonneg_left this (sq_nonneg s₀)
    _ = _ := by ring

/-- **The strong error on level `ℓ`** (Giles 2015, §5.1): `E[(S_T − Ŝ_ℓ)²] ≤ C(T) h_ℓ` with
`h_ℓ = T 2^{−ℓ}`. -/
theorem gbm_strong_error (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (ℓ : ℕ) :
    ∫ z, (gbmExact r σ T s₀ ℓ z - gbmEM r σ T s₀ ℓ z) ^ 2 ∂stdNormalSeq ≤
      gbmStrongConst r σ T s₀ * (T / 2 ^ ℓ) := by
  have hh : 0 ≤ T / 2 ^ ℓ := div_nonneg hT (by positivity)
  have h := gbm_em_strong_error r σ s₀ hh (2 ^ ℓ)
  rw [cast_two_pow_mul_div] at h
  exact h

lemma integrable_sq_gbm_err (r σ T s₀ : ℝ) (ℓ : ℕ) :
    Integrable (fun z => (gbmExact r σ T s₀ ℓ z - gbmEM r σ T s₀ ℓ z) ^ 2) stdNormalSeq :=
  ((memLp_gbmExact r σ T s₀ ℓ).sub (memLp_gbmEM r σ T s₀ ℓ)).integrable_sq

/-! ### Lipschitz payoffs -/

/-- A `K`-Lipschitz function has `K ≥ 0` and is continuous. -/
lemma continuous_of_abs_sub_le {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    0 ≤ K ∧ Continuous g := by
  have hK : 0 ≤ K := by
    have := hg 1 0
    rw [sub_zero, abs_one, mul_one] at this
    exact (abs_nonneg _).trans this
  have hL : LipschitzWith K.toNNReal g := LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK]
    exact hg x y
  exact ⟨hK, hL.continuous⟩

/-- A Lipschitz function of a square-integrable random variable is square integrable. -/
lemma memLp_two_comp_of_abs_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|)
    {X : Ω → ℝ} (hX : MemLp X 2 μ) : MemLp (fun ω => g (X ω)) 2 μ := by
  obtain ⟨hK, hgc⟩ := continuous_of_abs_sub_le hg
  have hm : AEStronglyMeasurable (fun ω => g (X ω)) μ := hgc.comp_aestronglyMeasurable hX.1
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have hb : Integrable (fun ω => 2 * g 0 ^ 2 + 2 * K ^ 2 * X ω ^ 2) μ :=
    (integrable_const (2 * g 0 ^ 2)).add (hX2.const_mul (2 * K ^ 2))
  refine (memLp_two_iff_integrable_sq hm).2
    (hb.mono' (hm.pow 2) (Filter.Eventually.of_forall fun ω => ?_))
  have h1 := hg (X ω) 0
  rw [sub_zero] at h1
  have hKX : K * |X ω| = |K * X ω| := by rw [abs_mul, abs_of_nonneg hK]
  have h2 : |g (X ω)| ≤ |g 0| + |K * X ω| := by
    have := abs_sub_abs_le_abs_sub (g (X ω)) (g 0)
    linarith
  have h3 : g (X ω) ^ 2 ≤ (|g 0| + |K * X ω|) ^ 2 := by
    rw [← sq_abs (g (X ω))]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  linarith [sq_nonneg (|g 0| - |K * X ω|), sq_abs (g 0), sq_abs (K * X ω)]

/-- `(E[X])² ≤ E[X²]` on a probability space. -/
lemma sq_integral_le_integral_sq_of_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂μ := by
  have h := variance_nonneg X μ
  rw [variance_eq_sub hX] at h
  simp only [Pi.pow_apply] at h
  linarith

/-- `2^{−ℓ/2}` squared is `2^{−ℓ}`. -/
lemma rpow_neg_half_mul_sq (ℓ : ℕ) :
    ((2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ)))) ^ 2 = ((2 : ℝ) ^ ℓ)⁻¹ := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ)))) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show -(1 / 2 * (ℓ : ℝ)) * ((2 : ℕ) : ℝ) = -(ℓ : ℝ) by push_cast; ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- **The weak error of the Euler–Maruyama scheme for GBM with a Lipschitz payoff** (Giles 2015,
§5.1; the rate `α = ½` of Theorem 1 (i)).  For `|g(x) − g(y)| ≤ K|x − y|` and `T ≥ 0`,
`|E[g(Ŝ_ℓ) − g(S_T)]| ≤ K √(C(T) T) 2^{−ℓ/2}`, where `S_T` is the exact solution (whose law does not
depend on the level, `map_gbmExact`). -/
theorem gbm_weak_error_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (ℓ : ℕ) :
    |∫ z, g (gbmEM r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq| ≤
      K * Real.sqrt (gbmStrongConst r σ T s₀ * T) * (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) := by
  obtain ⟨hK, hgc⟩ := continuous_of_abs_sub_le hg
  have hC := gbmStrongConst_nonneg r σ s₀ hT
  have hA : MemLp (fun z => g (gbmEM r σ T s₀ ℓ z)) 2 stdNormalSeq :=
    memLp_two_comp_of_abs_sub_le hg (memLp_gbmEM r σ T s₀ ℓ)
  have hB : ∀ k, MemLp (fun z => g (gbmExact r σ T s₀ k z)) 2 stdNormalSeq := fun k =>
    memLp_two_comp_of_abs_sub_le hg (memLp_gbmExact r σ T s₀ k)
  have e1 : ∫ z, g (gbmEM r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq =
      ∫ z, g (gbmEM r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z) ∂stdNormalSeq := by
    rw [integral_sub (hA.integrable one_le_two) ((hB 0).integrable one_le_two),
      integral_sub (hA.integrable one_le_two) ((hB ℓ).integrable one_le_two),
      integral_comp_gbmExact r σ T s₀ ℓ hgc.measurable]
  have hD : MemLp (fun z => g (gbmEM r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z)) 2 stdNormalSeq :=
    hA.sub (hB ℓ)
  have hpt : ∀ z, (g (gbmEM r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z)) ^ 2 ≤
      K ^ 2 * (gbmExact r σ T s₀ ℓ z - gbmEM r σ T s₀ ℓ z) ^ 2 := fun z => by
    have h1 := hg (gbmEM r σ T s₀ ℓ z) (gbmExact r σ T s₀ ℓ z)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    linarith
  have hint : ∫ z, (g (gbmEM r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z)) ^ 2 ∂stdNormalSeq ≤
      K ^ 2 * ∫ z, (gbmExact r σ T s₀ ℓ z - gbmEM r σ T s₀ ℓ z) ^ 2 ∂stdNormalSeq := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
      ((integrable_sq_gbm_err r σ T s₀ ℓ).const_mul _) (Filter.Eventually.of_forall hpt)
  have hstrong := gbm_strong_error r σ s₀ hT ℓ
  have hsq : (∫ z, g (gbmEM r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq) ^ 2 ≤
      (K * Real.sqrt (gbmStrongConst r σ T s₀ * T) * (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ)))) ^ 2 := by
    rw [e1, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hC hT), rpow_neg_half_mul_sq]
    calc _ ≤ ∫ z, (g (gbmEM r σ T s₀ ℓ z) - g (gbmExact r σ T s₀ ℓ z)) ^ 2 ∂stdNormalSeq :=
          sq_integral_le_integral_sq_of_memLp hD
      _ ≤ K ^ 2 * (gbmStrongConst r σ T s₀ * (T / 2 ^ ℓ)) :=
          hint.trans (mul_le_mul_of_nonneg_left hstrong (sq_nonneg K))
      _ = _ := by ring
  have := sq_le_sq.1 hsq
  rwa [abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ K * Real.sqrt (gbmStrongConst r σ T s₀ * T) * (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))))]
    at this

/-- **The variance of the level corrections for GBM** (Giles 2015, §5.1: "`V[P − P_ℓ] ≤
E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]` … `V_ℓ ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`, and hence
`V_ℓ = O(h_ℓ)`"; the rate `β = 1` of Theorem 1 (iii)).  The correction on level `ℓ + 1` is the
payoff of the fine path minus the payoff of the coarse path driven by the summed increments
`(Z_{2k} + Z_{2k+1})/√2`; it is square integrable and its variance is at most
`6 K² C(T) T 2^{−(ℓ+1)}`. -/
theorem gbm_correction_variance_le (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (ℓ : ℕ) :
    MemLp (fun z => g (gbmEM r σ T s₀ (ℓ + 1) z) - g (gbmEM r σ T s₀ ℓ (pairAvg z))) 2
        stdNormalSeq ∧
    variance (fun z => g (gbmEM r σ T s₀ (ℓ + 1) z) - g (gbmEM r σ T s₀ ℓ (pairAvg z)))
        stdNormalSeq ≤
      6 * K ^ 2 * (gbmStrongConst r σ T s₀ * T) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by
  refine ⟨(memLp_two_comp_of_abs_sub_le hg (memLp_gbmEM r σ T s₀ (ℓ + 1))).sub
    ((memLp_two_comp_of_abs_sub_le hg (memLp_gbmEM r σ T s₀ ℓ)).comp_measurePreserving
      measurePreserving_pairAvg), ?_⟩
  obtain ⟨-, hgc⟩ := continuous_of_abs_sub_le hg
  have hm1 := measurable_gbmEM r σ T s₀ (ℓ + 1)
  have hm0 := (measurable_gbmEM r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable
  have hY : AEStronglyMeasurable
      (fun z => g (gbmEM r σ T s₀ (ℓ + 1) z) - g (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq :=
    ((hgc.measurable.comp hm1).sub (hgc.measurable.comp hm0)).aestronglyMeasurable
  refine (variance_le_expectation_sq hY).trans ?_
  simp only [Pi.pow_apply]
  have hI1 := integrable_sq_gbm_err r σ T s₀ (ℓ + 1)
  have hI0' := integrable_sq_gbm_err r σ T s₀ ℓ
  have hI0 : Integrable (fun z => (gbmExact r σ T s₀ ℓ (pairAvg z) -
      gbmEM r σ T s₀ ℓ (pairAvg z)) ^ 2) stdNormalSeq :=
    (measurePreserving_pairAvg.integrable_comp hI0'.aestronglyMeasurable).2 hI0'
  have hpt : ∀ z, (g (gbmEM r σ T s₀ (ℓ + 1) z) - g (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 2 ≤
      2 * K ^ 2 * (gbmExact r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ (ℓ + 1) z) ^ 2 +
        2 * K ^ 2 * (gbmExact r σ T s₀ ℓ (pairAvg z) - gbmEM r σ T s₀ ℓ (pairAvg z)) ^ 2 :=
    fun z => by
    have h1 := hg (gbmEM r σ T s₀ (ℓ + 1) z) (gbmEM r σ T s₀ ℓ (pairAvg z))
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    rw [gbmExact_pairAvg]
    linarith [mul_nonneg (sq_nonneg K) (sq_nonneg (gbmExact r σ T s₀ (ℓ + 1) z -
      gbmEM r σ T s₀ (ℓ + 1) z + (gbmExact r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ ℓ (pairAvg z))))]
  have hK2 : (0 : ℝ) ≤ 2 * K ^ 2 := by positivity
  have hs1 := gbm_strong_error r σ s₀ hT (ℓ + 1)
  have hs0 := gbm_strong_error r σ s₀ hT ℓ
  calc ∫ z, (g (gbmEM r σ T s₀ (ℓ + 1) z) - g (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 2 ∂stdNormalSeq
      ≤ ∫ z, (2 * K ^ 2 * (gbmExact r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ (ℓ + 1) z) ^ 2 +
          2 * K ^ 2 * (gbmExact r σ T s₀ ℓ (pairAvg z) - gbmEM r σ T s₀ ℓ (pairAvg z)) ^ 2)
          ∂stdNormalSeq :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
          ((hI1.const_mul (2 * K ^ 2)).add (hI0.const_mul (2 * K ^ 2)))
          (Filter.Eventually.of_forall hpt)
    _ = 2 * K ^ 2 * ∫ z, (gbmExact r σ T s₀ (ℓ + 1) z - gbmEM r σ T s₀ (ℓ + 1) z) ^ 2
          ∂stdNormalSeq +
        2 * K ^ 2 * ∫ z, (gbmExact r σ T s₀ ℓ z - gbmEM r σ T s₀ ℓ z) ^ 2 ∂stdNormalSeq := by
        rw [integral_add (hI1.const_mul _) (hI0.const_mul _), integral_const_mul,
          integral_const_mul, integral_comp_of_measurePreserving measurePreserving_pairAvg
            hI0'.aestronglyMeasurable]
    _ ≤ 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / 2 ^ (ℓ + 1))) +
        2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / 2 ^ ℓ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hs1 hK2) (mul_le_mul_of_nonneg_left hs0 hK2)
    _ = 6 * K ^ 2 * (gbmStrongConst r σ T s₀ * T) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by
        have e2 : T / 2 ^ ℓ = 2 * (T / 2 ^ (ℓ + 1)) := by
          rw [pow_succ, ← div_div, mul_div_cancel₀ _ two_ne_zero]
        rw [e2, div_eq_mul_inv]
        ring

/-! ### Theorem 1 -/

/-- A European payoff `g(S_T)` of a path with `2^ℓ` steps (Giles 2015, §5.1, Figure 5.3: the
European call `P(S) = e^{−rT} max(S_T − K, 0)` is of this form with a Lipschitz `g`). -/
def europeanPayoff (g : ℝ → ℝ) : ℕ → (ℕ → ℝ) → ℝ := fun ℓ path => g (path (2 ^ ℓ))

/-- **Theorem 1 for the Euler–Maruyama MLMC estimator of GBM** (Giles 2015, §5.1, with
Theorem 1 and (2.4), §2.1; the GBM example of Figure 5.3).  Let `dS = rS dt + σS dW`, `S_0 = s₀`,
`T ≥ 0`, and let `g` be `K`-Lipschitz (for example the call payoff `e^{−rT} max(S_T − K', 0)`).
Level `ℓ` uses `2^ℓ` Euler–Maruyama steps of size `h_ℓ = T 2^{−ℓ}`; its correction is the payoff of
the fine path minus the payoff of the coarse path driven by the summed increments, the samples are
independent, and a level-`ℓ` sample costs `2^ℓ`.  Then there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel estimator of
`E[g(S_T)] = E[g(s₀ e^{(r − σ²/2)T + σ √T Z})]`, `Z ~ N(0,1)`, has a square-integrable error with
mean square `< ε²`, and cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`.  No rate is assumed: the weak rate
`α = ½` (`gbm_weak_error_le`), the variance rate `β = 1` (`gbm_correction_variance_le`) and (2.4)
(`integral_emCoarse`) are proved. -/
theorem gbm_mlmc_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {K : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
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
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  obtain ⟨hK, hgc⟩ := continuous_of_abs_sub_le hg
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hC := gbmStrongConst_nonneg r σ s₀ hT
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
  have hPf : ∀ ℓ, MemLp (emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g) ℓ) 2
      stdNormalSeq := fun ℓ => memLp_two_comp_of_abs_sub_le hg (memLp_gbmEM r σ T s₀ ℓ)
  have hPfm : ∀ ℓ, Measurable (emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g) ℓ) :=
    fun ℓ => hgc.measurable.comp (measurable_gbmEM r σ T s₀ ℓ)
  -- (i): the weak rate `α = ½`
  have hc₁ : 0 < K * Real.sqrt (gbmStrongConst r σ T s₀ * T) + 1 := by positivity
  have h_i : ∀ ℓ : ℕ, |∫ z, emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g) ℓ z -
      g (gbmExact r σ T s₀ 0 z) ∂stdNormalSeq| ≤
      (K * Real.sqrt (gbmStrongConst r σ T s₀ * T) + 1) * (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) :=
    fun ℓ => by
    have h := gbm_weak_error_le r σ s₀ hT hg ℓ
    have hpos : 0 < (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) := by positivity
    calc _ ≤ K * Real.sqrt (gbmStrongConst r σ T s₀ * T) * (2 : ℝ) ^ (-(1 / 2 * (ℓ : ℝ))) := h
      _ ≤ _ := by linarith
  -- (iii): the variance rate `β = 1`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance
      (emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g) 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀]
    exact variance_nonneg _ _
  have hc₂ : 0 < V₀ + 6 * K ^ 2 * (gbmStrongConst r σ T s₀ * T) + 1 := by positivity
  have h_iii : ∀ ℓ, variance (fineCoarseDiff
      (emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g))
      (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g)) ℓ) stdNormalSeq ≤
      (V₀ + 6 * K ^ 2 * (gbmStrongConst r σ T s₀ * T) + 1) * (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) := by
    intro ℓ
    rw [one_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    cases ℓ with
    | zero =>
      simp only [fineCoarseDiff, pow_zero, inv_one, mul_one]
      rw [← hV₀]
      linarith [mul_nonneg (sq_nonneg K) (mul_nonneg hC hT)]
    | succ ℓ =>
      have hv := (gbm_correction_variance_le r σ s₀ hT hg ℓ).2
      have e : fineCoarseDiff (emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g))
          (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g)) (ℓ + 1) =
          fun z => g (gbmEM r σ T s₀ (ℓ + 1) z) - g (gbmEM r σ T s₀ ℓ (pairAvg z)) := by
        funext z
        simp only [fineCoarseDiff, emCoarse_eq]
        rfl
      rw [e]
      have hinv : 0 < ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by positivity
      calc _ ≤ 6 * K ^ 2 * (gbmStrongConst r σ T s₀ * T) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ := hv
        _ ≤ _ := by linarith [mul_nonneg hV₀0 hinv.le]
  -- (iv): a level-`ℓ` sample costs `2^ℓ`
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ 1 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, one_mul, Real.rpow_natCast]
  obtain ⟨c₄, hc₄, h⟩ := em_mlmc_theorem1
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq)
    (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g) (fun z => g (gbmExact r σ T s₀ 0 z))
    (fun p x => x p) (fun ℓ _ _ => (2 : ℝ) ^ ℓ) (fun ℓ => (2 : ℝ) ^ ℓ) (α := 1 / 2) (β := 1)
    (γ := 1) (by norm_num) one_pos one_pos hc₁ hc₂ one_pos (by norm_num) hω hind
    (hP.integrable one_le_two) hPfm hPf (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i h_iii h_iv
  have hPc : ∀ ℓ, MemLp (emCoarse (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g) ℓ) 2
      stdNormalSeq := fun ℓ => by
    rw [show emCoarse (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g) ℓ =
        emFine (gbmDrift r) (gbmVol σ) T s₀ (europeanPayoff g) ℓ ∘ pairAvg from
      funext (emCoarse_eq _ _ _ _ _ ℓ)]
    exact (hPf ℓ).comp_measurePreserving measurePreserving_pairAvg
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ?_, ?_, ?_⟩
  · exact ((memLp_finsetSum _ fun ℓ _ =>
      memLp_blockMean hω (memLp_fineCoarseDiff hPf hPc) ℓ (N ℓ)).sub (memLp_const _)).integrable_sq
  · rw [← hPint]
    exact hmse
  · simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul] at hcost
    rw [complexityBound_of_eq rfl ε] at hcost
    exact hcost

end MLMC
