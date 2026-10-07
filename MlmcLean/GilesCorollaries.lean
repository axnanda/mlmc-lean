import MlmcLean.MarkovLimitLaw
import MlmcLean.PDEExamples
import MlmcLean.LUTLimits
import MlmcLean.AsymptoticNormal
import MlmcLean.CostComparison
import MlmcLean.ErrorAnalysis
import MlmcLean.RectangularMIMC
import MlmcLean.GBMEulerMaruyama
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Corollaries of the library (Giles 2015, §2.1, §2.4, §5.1, §5.5, §10.1; Haas–Giles 2025, §3.2)

References: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1 (p. 7),
§2.4 (pp. 15–16), §5.1 (p. 29), §5.5 (p. 43) and §10.1 (p. 61); I.-B. Haas and M.B. Giles, *A
nested MLMC framework for efficient simulations on FPGAs*, arXiv:2502.07123 (2025), §3.2 (p. 5).

Short consequences of results proved elsewhere in the library.

**Contracting SDEs with a fixed time step (Giles 2015, §10.1, p. 61).**  For
`dX = a(X) dt + b(X) dW` with a dissipative drift, `(x − y)(a(x) − a(y)) ≤ −κ (x − y)²`, Lipschitz
`a` (constant `K_a`) and `b` (constant `K_b`), and a step `h > 0` with `K_b² + K_a² h < 2κ`, the
Euler–Maruyama step `x ↦ x + a(x) h + b(x) ΔW`, `ΔW ~ N(0, h)` (`emStep` of
`MlmcLean/PDEExamples.lean`), contracts in mean square with factor
`ρ = 1 − 2κh + K_a² h² + K_b² h ∈ [0, 1)` (`emStep_meanSquare_contraction`), and by Jensen its
`2γ`-th moment contracts with factor `ρ^γ` for `0 < γ ≤ 1` (`lintegral_dist_rpow_le_of_sq`).  So
the Markov-chain results of `MlmcLean/MarkovLimitLaw.lean` apply, and the multilevel estimator of
`E[f(X^h_∞)]` for `γ`-Hölder `f`, where the level-`ℓ` sample runs the discretised chain over
`[−N_ℓ h, 0]` with `N_ℓ` growing linearly, has mean square error `< ε²` at cost `O(ε⁻²)`
(`contracting_sde_mlmc`; the paper's range is `γ ∈ (0, 1)`, `γ = 1` is included here).

**The lookup-table streams of method 2 (Haas–Giles 2025, §3.2, p. 5).**  If `f` is monotone on
`(0, 1)` and `f(U) ~ N(0, 1)` for `U` uniform (so `f = Φ⁻¹` a.e.), the method-1 lookup table with
`2^d` entries read at the first `d` bits of a uniform variable, `Z_{⌊2^d U⌋}`, converges to `f(U)`
in mean square (`tendsto_method1MSE`), hence in probability and in distribution:
`Z_{⌊2^d U⌋} → N(0, 1)` (`lutStream_tendstoInDistribution`).  With `n` independent streams scaled by
`n^{−1/2}`, each converges to `N(0, 1/n)`, and their sum converges to `N(0, 1)`
(`lutStreams_sum_tendstoInDistribution`): the premise of `tendstoInDistribution_sum_of_approxNormal`
is proved here, not assumed.

**Standard Monte Carlo for exit times (Giles 2015, §5.5, p. 43).**  `mc_exit_time_complexity`:
`mc_complexity` with weak order `1/2` gives `O(ε⁻⁴)` and with weak order `1` gives `O(ε⁻³)`; the
multilevel cost `ε⁻³ |log ε|^{1/2}` is `o(ε⁻⁴)` but not below `ε⁻³`.  `mc_complexity_lower`: if
the weak order `α` is attained, any plain Monte Carlo estimator with `MSE ≤ ε²` costs at least
`c ε^{−2−γ/α}` (`ε⁻⁴` and `ε⁻³` here), so the comparison is with a lower bound.

**`β ≤ 2α` (Giles 2015, §2.1, p. 7).**  If, for all large `ℓ`, `V_ℓ ≥ κ E[(ΔP_ℓ)²]` with `κ > 0`
and `V_ℓ ≤ c₂ 2^{−βℓ}`, then `β ≤ 2α` whenever the rate `α` is attained infinitely often, either by
the mean correction, `|E[ΔP_ℓ]| ≥ c 2^{−αℓ}` (`beta_le_two_alpha`), or by the bias of condition i),
`|E[P_ℓ − P]| ≥ a₁ 2^{−αℓ}` (`beta_le_two_alpha_of_bias`).

**Standard MLMC with `β ≤ γ` is not optimal (Giles 2015, §2.4, pp. 15–16).**
`mlmc_optimal_complexity_necessary`: the case `D = 1` of `mimc_rect_necessary`, stated for the
standard estimator: under attained rates, cost `O(ε⁻²)` forces `γ < β` (and `γ ≤ 2α`).

**The Euler–Maruyama coupling with refinement factor `M` (Giles 2015, §5.1, p. 29).**  With
`h_ℓ = h₀ M^{−ℓ}` (the paper prints `h₀ M^ℓ`), the coarse path of a level-`(ℓ + 1)` sample takes
steps `M h_{ℓ+1} = h_ℓ` driven by the block sums of `M` fine increments: in normalised form
`Z^c_k = (Z_{Mk} + ⋯ + Z_{Mk+M−1})/√M` (`blockAvg`; `sqrt_mul_blockAvg`: the coarse Brownian
increment is the sum of the fine ones).  These are again independent `N(0, 1)`
(`map_blockSum_gaussian`, `measurePreserving_blockAvg`), so (2.4) holds (`integral_emCoarseM`) and
Theorem 1 applies (`em_mlmc_theorem1_M`).  `MlmcLean/EulerMaruyama.lean` treats `M = 2`: for
`M = 2` the definitions here agree with those there (`blockAvg_two`, `emFineM_two`,
`emCoarseM_two`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace MLMC

/-! ### Contracting SDEs with a fixed time step (Giles 2015, §10.1) -/

section Contracting

/-- The second moment of an affine function of a centred Gaussian:
`E[(A + B W)²] = A² + B² v` for `W ~ N(0, v)`. -/
lemma integral_sq_affine_gaussianReal (A B : ℝ) (v : ℝ≥0) :
    ∫ w, (A + B * w) ^ 2 ∂gaussianReal 0 v = A ^ 2 + B ^ 2 * v := by
  have hL2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := memLp_id_gaussianReal' 2 (by norm_num)
  have h1 : Integrable (fun w : ℝ => w) (gaussianReal 0 v) := hL2.integrable one_le_two
  have h2 : Integrable (fun w : ℝ => w ^ 2) (gaussianReal 0 v) := hL2.integrable_sq
  have hmean : ∫ w, w ∂gaussianReal 0 v = 0 := integral_id_gaussianReal
  have hsq : ∫ w, w ^ 2 ∂gaussianReal 0 v = v := by
    have h := variance_eq_sub hL2
    rw [variance_id_gaussianReal] at h
    have e : (∫ w, (id ^ 2 : ℝ → ℝ) w ∂gaussianReal 0 v) = ∫ w, w ^ 2 ∂gaussianReal 0 v := rfl
    have e' : (∫ w, (id : ℝ → ℝ) w ∂gaussianReal 0 v) = 0 := hmean
    rw [e, e'] at h
    linarith
  have e : (fun w : ℝ => (A + B * w) ^ 2) = fun w => (A ^ 2 + 2 * A * B * w) + B ^ 2 * w ^ 2 :=
    funext fun w => by ring
  have i1 : Integrable (fun w : ℝ => A ^ 2 + 2 * A * B * w) (gaussianReal 0 v) :=
    (integrable_const _).add (h1.const_mul _)
  have i2 : Integrable (fun w : ℝ => B ^ 2 * w ^ 2) (gaussianReal 0 v) := h2.const_mul _
  have i3 : Integrable (fun w : ℝ => 2 * A * B * w) (gaussianReal 0 v) := h1.const_mul _
  rw [e, integral_add i1 i2, integral_add (integrable_const _) i3, integral_const,
    integral_const_mul, integral_const_mul, hmean, hsq]
  simp

/-- `E[(A + B W)²] = A² + B² v` for `W ~ N(0, v)`, as a lower Lebesgue integral. -/
lemma lintegral_sq_affine_gaussianReal (A B : ℝ) (v : ℝ≥0) :
    ∫⁻ w, ENNReal.ofReal ((A + B * w) ^ 2) ∂gaussianReal 0 v =
      ENNReal.ofReal (A ^ 2 + B ^ 2 * v) := by
  have hL2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := memLp_id_gaussianReal' 2 (by norm_num)
  have h1 : Integrable (fun w : ℝ => w) (gaussianReal 0 v) := hL2.integrable one_le_two
  have h2 : Integrable (fun w : ℝ => w ^ 2) (gaussianReal 0 v) := hL2.integrable_sq
  have e : (fun w : ℝ => (A + B * w) ^ 2) = fun w => (A ^ 2 + 2 * A * B * w) + B ^ 2 * w ^ 2 :=
    funext fun w => by ring
  have hint : Integrable (fun w : ℝ => (A + B * w) ^ 2) (gaussianReal 0 v) := by
    rw [e]
    exact ((integrable_const _).add (h1.const_mul _)).add (h2.const_mul _)
  rw [← integral_sq_affine_gaussianReal, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun w => sq_nonneg _)]

/-- **The Euler–Maruyama step of a dissipative SDE contracts in mean square** (Giles 2015, §10.1,
p. 61: "A very similar approach can also be used for contracting SDEs which converge to a limiting
distribution … the contraction property will ensure that the multilevel variance decays with
level").  Let `a` be Lipschitz with constant `K_a` and dissipative,
`(x − y)(a(x) − a(y)) ≤ −κ (x − y)²` (a one-sided Lipschitz constant `−κ`), let `b` be Lipschitz
with constant `K_b` (`K_b = 0` for additive noise), and let the step `h > 0` satisfy
`K_b² + K_a² h < 2κ`.  Then `ρ = 1 − 2κh + K_a² h² + K_b² h` satisfies `0 ≤ ρ < 1`, and the
Euler–Maruyama step `φ(x, ΔW) = x + a(x) h + b(x) ΔW` (`emStep a b h`) with a Brownian increment
`ΔW ~ N(0, h)` is a random contraction in mean square:
`E[(φ(x, ΔW) − φ(y, ΔW))²] ≤ ρ (x − y)²` for all `x, y`.  This is Giles' condition
`sup_{x≠y} E[(d(φ(x), φ(y))/d(x, y))^{2γ}] < 1` with `γ = 1`; for the paper's range
`0 < γ < 1` it follows with the factor `ρ^γ` by Jensen (`lintegral_dist_rpow_le_of_sq`).  The
condition on `h` is the discrete analogue of `K_b² < 2κ`, which makes the SDE itself contract in
mean square. -/
theorem emStep_meanSquare_contraction {a b : ℝ → ℝ} {Ka Kb : ℝ≥0} {κ : ℝ} {h : ℝ≥0}
    (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hh : 0 < h)
    (hstep : (Kb : ℝ) ^ 2 + (Ka : ℝ) ^ 2 * h < 2 * κ) :
    0 ≤ 1 - 2 * κ * h + (Ka : ℝ) ^ 2 * h ^ 2 + (Kb : ℝ) ^ 2 * h ∧
    1 - 2 * κ * h + (Ka : ℝ) ^ 2 * h ^ 2 + (Kb : ℝ) ^ 2 * h < 1 ∧
    ∀ x y, ∫⁻ w, ENNReal.ofReal ((emStep a b h x w - emStep a b h y w) ^ 2) ∂gaussianReal 0 h ≤
      ENNReal.ofReal (1 - 2 * κ * h + (Ka : ℝ) ^ 2 * h ^ 2 + (Kb : ℝ) ^ 2 * h) *
        ENNReal.ofReal ((x - y) ^ 2) := by
  have hh' : (0 : ℝ) < h := hh
  have hsq : ∀ {g : ℝ → ℝ} {K : ℝ≥0}, LipschitzWith K g → ∀ x y,
      (g x - g y) ^ 2 ≤ (K : ℝ) ^ 2 * (x - y) ^ 2 := fun {g K} hg x y => by
    have h1 := hg.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq] at h1
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [mul_pow, sq_abs, sq_abs] at h2
  -- `0 < κ ≤ K_a`, so the contraction factor is nonnegative
  have hκ : 0 < κ := by nlinarith [sq_nonneg (Kb : ℝ), sq_nonneg (Ka : ℝ)]
  have hκK : κ ≤ Ka := by
    have h1 := hdiss 1 0
    have h2 := ha.dist_le_mul 1 0
    rw [Real.dist_eq, Real.dist_eq] at h2
    norm_num at h1 h2
    linarith [neg_abs_le (a 1 - a 0)]
  have hρ0 : 0 ≤ 1 - 2 * κ * h + (Ka : ℝ) ^ 2 * h ^ 2 + (Kb : ℝ) ^ 2 * h := by
    have h1 : κ ^ 2 ≤ (Ka : ℝ) ^ 2 := pow_le_pow_left₀ hκ.le hκK 2
    have h2 : (h : ℝ) ^ 2 * κ ^ 2 ≤ h ^ 2 * (Ka : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    nlinarith [sq_nonneg (1 - κ * h), mul_nonneg (sq_nonneg (Kb : ℝ)) hh'.le]
  refine ⟨hρ0, ?_, fun x y => ?_⟩
  · nlinarith
  · have e : ∀ w, emStep a b h x w - emStep a b h y w =
        (x - y + (a x - a y) * h) + (b x - b y) * w := fun w => by
      simp only [emStep]
      ring
    simp_rw [e]
    rw [lintegral_sq_affine_gaussianReal, ← ENNReal.ofReal_mul hρ0]
    apply ENNReal.ofReal_le_ofReal
    have h1 := hdiss x y
    have h2 := hsq ha x y
    have h3 := hsq hb x y
    have h4 : (h : ℝ) * ((x - y) * (a x - a y)) ≤ h * (-(κ * (x - y) ^ 2)) :=
      mul_le_mul_of_nonneg_left h1 hh'.le
    have h5 : (h : ℝ) ^ 2 * (a x - a y) ^ 2 ≤ h ^ 2 * ((Ka : ℝ) ^ 2 * (x - y) ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have h6 : (b x - b y) ^ 2 * h ≤ (Kb : ℝ) ^ 2 * (x - y) ^ 2 * h :=
      mul_le_mul_of_nonneg_right h3 hh'.le
    nlinarith

/-- The multilevel estimator is linear in the payoff: scaling every `P_ℓ` by `c` scales `Y`. -/
lemma mlmcEstimator_const_mul {Ω₀ Ω : Type*} (c : ℝ) (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀)
    (L : ℕ) (M : ℕ → ℕ) (x : Ω) :
    mlmcEstimator (fun ℓ y => c * Pl ℓ y) ω L M x = c * mlmcEstimator Pl ω L M x := by
  have hd : ∀ ℓ y, levelDiff (fun ℓ y => c * Pl ℓ y) ℓ y = c * levelDiff Pl ℓ y := by
    intro ℓ y
    cases ℓ with
    | zero => rw [levelDiff_zero, levelDiff_zero]
    | succ ℓ =>
      rw [levelDiff_succ, levelDiff_succ]
      show c * Pl (ℓ + 1) y - c * Pl ℓ y = c * (Pl (ℓ + 1) y - Pl ℓ y)
      ring
  unfold mlmcEstimator levelEstimator
  simp only [hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun n _ => ?_
  ring

/-- For `0 ≤ ρ < 1` and `m ≥ 1` there is `β > 0` with `ρ^m ≤ 2^{−β}`. -/
lemma exists_pow_le_two_rpow_neg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ β : ℝ, 0 < β ∧ ρ ^ m ≤ (2 : ℝ) ^ (-β) := by
  set r : ℝ := max ρ (1 / 2)
  have hr0 : 0 < r := lt_max_of_lt_right (by norm_num)
  have hr1 : r < 1 := max_lt hρ1 (by norm_num)
  have hrm0 : 0 < r ^ m := pow_pos hr0 m
  have hrm1 : r ^ m < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  refine ⟨-Real.logb 2 (r ^ m), neg_pos.2 (Real.logb_neg one_lt_two hrm0 hrm1), ?_⟩
  rw [neg_neg, Real.rpow_logb two_pos (by norm_num) hrm0]
  exact pow_le_pow_left₀ hρ0 (le_max_left _ _) m

/-- Jensen's inequality for the concave power `t ↦ t^γ`, `0 < γ ≤ 1`, on a probability space:
`∫⁻ F^γ ≤ (∫⁻ F)^γ` (the `L^γ` norm is at most the `L¹` norm). -/
lemma lintegral_rpow_le_rpow_lintegral {X : Type*} {mX : MeasurableSpace X} {ν : Measure X}
    [IsProbabilityMeasure ν] {F : X → ℝ≥0∞} (hF : AEMeasurable F ν) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) : ∫⁻ x, F x ^ γ ∂ν ≤ (∫⁻ x, F x ∂ν) ^ γ := by
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le hγ0 hγ1 ν hF.aestronglyMeasurable
  simp only [eLpNorm', enorm_eq_self, ENNReal.rpow_one, div_one] at h
  have h2 := ENNReal.rpow_le_rpow h hγ0.le
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel hγ0.ne', ENNReal.rpow_one] at h2

/-- `|u − v|^{2γ} = ((u − v)²)^γ`, inside `ENNReal.ofReal`, for `γ ≥ 0`. -/
lemma ofReal_dist_rpow_two_mul (u v : ℝ) {γ : ℝ} (hγ : 0 ≤ γ) :
    ENNReal.ofReal (dist u v ^ (2 * γ)) = ENNReal.ofReal ((u - v) ^ 2) ^ γ := by
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hγ, Real.rpow_mul dist_nonneg, Real.rpow_two,
    Real.dist_eq, sq_abs]

/-- A random map that contracts in mean square with factor `ρ` contracts the `2γ`-th moment of
the distance with factor `ρ^γ`, `0 < γ ≤ 1` (Jensen, `lintegral_rpow_le_rpow_lintegral`):
`E[|φ(x) − φ(y)|^{2γ}] ≤ (E[(φ(x) − φ(y))²])^γ ≤ ρ^γ |x − y|^{2γ}`. -/
lemma lintegral_dist_rpow_le_of_sq {E : Type*} {mE : MeasurableSpace E} {ν : Measure E}
    [IsProbabilityMeasure ν] {φ : ℝ → E → ℝ} (hφ : ∀ x, Measurable (φ x)) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (h : ∀ x y, ∫⁻ e, ENNReal.ofReal ((φ x e - φ y e) ^ 2) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal ((x - y) ^ 2)) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (x y : ℝ) :
    ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal (ρ ^ γ) * ENNReal.ofReal (dist x y ^ (2 * γ)) := by
  simp_rw [ofReal_dist_rpow_two_mul _ _ hγ0.le]
  rw [← ENNReal.ofReal_rpow_of_nonneg hρ0 hγ0.le, ← ENNReal.mul_rpow_of_nonneg _ _ hγ0.le]
  refine (lintegral_rpow_le_rpow_lintegral ?_ hγ0 hγ1).trans (ENNReal.rpow_le_rpow (h x y) hγ0.le)
  exact (((hφ x).sub (hφ y)).pow_const 2).ennreal_ofReal.aemeasurable

/-- A `γ`-Hölder function, `|f(x) − f(y)| ≤ K |x − y|^γ` with `γ > 0`, is continuous. -/
lemma continuous_of_holder {f : ℝ → ℝ} {K γ : ℝ} (hγ : 0 < γ)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y| ^ γ) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => tendsto_iff_dist_tendsto_zero.2 ?_
  have h1 : Tendsto (fun y => |y - x|) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_sub_right x).abs.tendsto x
  have h2 := (h1.rpow_const (Or.inr hγ.le)).const_mul K
  rw [Real.zero_rpow hγ.ne', mul_zero] at h2
  exact squeeze_zero (fun _ => dist_nonneg) (fun y => by rw [Real.dist_eq]; exact hf y x) h2

/-- **Multilevel Monte Carlo for a contracting SDE with a fixed time step** (Giles 2015, §10.1,
p. 61: "A very similar approach can also be used for contracting SDEs which converge to a limiting
distribution.  For these, the level `ℓ` path will perform a simulation for the time interval
`[−T_ℓ, 0]`, using timestep `h_ℓ`.  The coarse and fine paths will share the same driving Brownian
path for the overlapping time interval `[−T_{ℓ−1}, 0]`, and the contraction property will ensure
that the multilevel variance decays with level").  With the hypotheses of
`emStep_meanSquare_contraction` (dissipative Lipschitz drift, Lipschitz volatility, step `h > 0`
with `K_b² + K_a² h < 2κ`) and a `γ`-Hölder payoff `f`, `|f(x) − f(y)| ≤ K_f |x − y|^γ` with
`0 < γ ≤ 1`, let the Brownian increments `ΔW_k` be independent `N(0, h)` and let `X^h_∞` be the
almost sure limit of the discretised chain started `n` steps in the past at `x₀` (it exists by
`ae_tendsto_backIter`; its law is the unique invariant law of the Euler–Maruyama chain,
`existsUnique_invariant`, `map_limit_eq_of_invariant`).  Let the level-`ℓ` sample simulate
`[−N_ℓ h, 0]`, sharing the increments of `[−N_{ℓ−1} h, 0]` with level `ℓ − 1`, with `N`
nondecreasing and `m₁ ℓ ≤ N_ℓ ≤ m₂ (ℓ + 1)`, `m₁ ≥ 1` ("`N_ℓ` to increase linearly with level").
Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and sample sizes `M_ℓ ≥ 1`
for which the standard multilevel estimator of `E[f(X^h_∞)]`, each sample computed from its own
independent sequence of increments, has a square-integrable error, mean square error `< ε²` and
cost `∑_{ℓ ≤ L} M_ℓ N_ℓ ≤ c₄ ε⁻²`.
Deviations: the time step is fixed (`h_ℓ = h`, `T_ℓ = N_ℓ h`), so the target is the expectation
under the limit law of the discretised chain, not of the SDE (the bias in `h` needs SDE theory);
one dimension; the cost of a sample is counted as the `N_ℓ` steps of its fine path (the coarse
path adds at most as many).  The paper (§10.1, p. 61) assumes
`sup_{x≠y} E[(d(φx, φy)/d(x, y))^{2γ}] < 1` and `|f(y) − f(x)| ≤ d(x, y)^γ` "for some
`γ ∈ (0, 1)`"; here `0 < γ ≤ 1`, so `γ = 1` (Lipschitz `f`, mean-square contraction), which is
outside the paper's range, is included (the library's `markov_mlmc_theorem1` allows it), and the
Hölder constant `K_f` is arbitrary.  Proof: `emStep_meanSquare_contraction` gives the
mean-square contraction factor `ρ`, Jensen (`lintegral_dist_rpow_le_of_sq`) gives Giles'
contraction with exponent `2γ` and factor `ρ^γ < 1`, and `markov_mlmc_theorem1` applies to
`f / max(K_f, 1)`. -/
theorem contracting_sde_mlmc {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b f : ℝ → ℝ} {Ka Kb Kf : ℝ≥0} {κ : ℝ} {h : ℝ≥0}
    (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hdiss : ∀ x y, (x - y) * (a x - a y) ≤ -(κ * (x - y) ^ 2)) (hh : 0 < h)
    (hstep : (Kb : ℝ) ^ 2 + (Ka : ℝ) ^ 2 * h < 2 * κ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hf : ∀ x y, |f x - f y| ≤ Kf * |x - y| ^ γ)
    {ξ : ℕ → Ω → ℝ} (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = gaussianReal 0 h) (x₀ : ℝ) {X : Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter (emStep a b h) n (fun k => ξ k ω) x₀) atTop
      (𝓝 (X ω)))
    {N : ℕ → ℕ} (hN : Monotone N) {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hN₁ : ∀ ℓ, m₁ * ℓ ≤ N ℓ)
    (hN₂ : ∀ ℓ, N ℓ ≤ m₂ * (ℓ + 1)) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (M : ℕ → ℕ), (∀ ℓ, 0 < M ℓ) ∧
        Integrable (fun x => (mlmcEstimator
            (fun ℓ (e : ℕ → ℝ) => f (backIter (emStep a b h) (N ℓ) e x₀))
            (fun p x => x p) L M x - ∫ ω, f (X ω) ∂μ) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 h) ∧
        ∫ x, (mlmcEstimator (fun ℓ (e : ℕ → ℝ) => f (backIter (emStep a b h) (N ℓ) e x₀))
            (fun p x => x p) L M x - ∫ ω, f (X ω) ∂μ) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 h)
          < ε ^ 2 ∧
        ∫ x, totalCost (fun ℓ _ _ => (N ℓ : ℝ)) L M x
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 h)
          ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨hρ0, hρ1, hcon⟩ := emStep_meanSquare_contraction ha hb hdiss hh hstep
  set ρ : ℝ := 1 - 2 * κ * h + (Ka : ℝ) ^ 2 * h ^ 2 + (Kb : ℝ) ^ 2 * h
  -- the hypotheses of `markov_mlmc_theorem1` with exponent `γ` and factor `ρ^γ`
  have hma : Measurable a := ha.continuous.measurable
  have hmb : Measurable b := hb.continuous.measurable
  have hφm : Measurable fun q : ℝ × ℝ => emStep a b h q.1 q.2 := by
    unfold emStep
    fun_prop
  have hφw : ∀ x, Measurable (emStep a b h x) := fun x => by
    unfold emStep
    fun_prop
  have hφ := lintegral_dist_rpow_le_of_sq hφw hρ0 hcon hγ0 hγ1
  have hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (emStep a b h x₀ e) ^ (2 * γ))
      ∂gaussianReal 0 h ≠ ∞ := by
    simp_rw [ofReal_dist_rpow_two_mul _ _ hγ0.le]
    refine ne_top_of_le_ne_top ?_ (lintegral_rpow_le_rpow_lintegral ?_ hγ0 hγ1)
    · have e : ∀ w, x₀ - emStep a b h x₀ w = -(a x₀ * h) + (-b x₀) * w := fun w => by
        unfold emStep
        ring
      simp_rw [e]
      rw [lintegral_sq_affine_gaussianReal]
      exact ENNReal.rpow_ne_top_of_nonneg hγ0.le ENNReal.ofReal_ne_top
    · exact ((measurable_const.sub (hφw x₀)).pow_const 2).ennreal_ofReal.aemeasurable
  have hργ0 : 0 ≤ ρ ^ γ := Real.rpow_nonneg hρ0 _
  have hργ1 : ρ ^ γ < 1 := Real.rpow_lt_one hρ0 hρ1 hγ0
  -- the normalised payoff `f / max(K_f, 1)` is `γ`-Hölder with constant `1`
  set K : ℝ := max (Kf : ℝ) 1
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hgm : Measurable fun x => f x / K := (continuous_of_holder hγ0 hf).measurable.div_const K
  have hg : ∀ x y, |f x / K - f y / K| ≤ dist x y ^ γ := fun x y => by
    rw [← sub_div, abs_div, abs_of_pos hK0, div_le_iff₀ hK0, Real.dist_eq]
    calc |f x - f y| ≤ Kf * |x - y| ^ γ := hf x y
      _ ≤ |x - y| ^ γ * K := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
  obtain ⟨β, hβ, hρβ⟩ := exists_pow_le_two_rpow_neg hργ0 hργ1 hm₁
  obtain ⟨c₄, hc₄, H⟩ := markov_mlmc_theorem1 (μ := μ) (ν := gaussianReal 0 h) (ξ := ξ)
    (φ := emStep a b h) hφm hφ hξ hξm hlaw hγ0 hγ1 hργ0 hργ1 x₀ hc hgm hg hX hN hN₁ hN₂
    (β := β) (δ := β / 2) (by positivity) (by linarith) hρβ
  -- the levels are square integrable on the canonical noise space
  obtain ⟨hind', hm', hl'⟩ := canonical_noise (ν := gaussianReal 0 h)
  have hlev : ∀ ℓ, MemLp (fun e : ℕ → ℝ => f (backIter (emStep a b h) (N ℓ) e x₀)) 2
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 h) := fun ℓ => by
    have h1 := (memLp_level hφm hφ hind' hm' hl' hγ0 hγ1 hργ0 hργ1 x₀ hc hgm hg
      (N ℓ)).const_mul K
    have e : (fun e : ℕ → ℝ => f (backIter (emStep a b h) (N ℓ) e x₀)) =
        fun e => K * (f (backIter (emStep a b h) (N ℓ) e x₀) / K) := funext fun e => by
      field_simp
    rw [e]
    exact h1
  have hω' : ∀ p : ℕ × ℕ, MeasurePreserving (fun x : ℕ × ℕ → ℕ → ℝ => x p)
      (Measure.infinitePi fun _ : ℕ × ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 h)
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 h) := fun p =>
    measurePreserving_eval_infinitePi _ p
  refine ⟨c₄ * K ^ 2, by positivity, fun ε hε hε1 => ?_⟩
  have hεK : 0 < ε / K := div_pos hε hK0
  obtain ⟨L, M, hM, hmse, hcost⟩ := H (ε / K) hεK
    (lt_of_le_of_lt (div_le_self hε.le hK1) hε1)
  have hY : MemLp (mlmcEstimator (fun ℓ (e : ℕ → ℝ) => f (backIter (emStep a b h) (N ℓ) e x₀))
      (fun p x => x p) L M) 2
      (Measure.infinitePi fun _ : ℕ × ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 h) :=
    memLp_finsetSum _ fun ℓ _ => memLp_levelEstimator hω' hlev ℓ (M ℓ)
  refine ⟨L, M, hM, (hY.sub (memLp_const _)).integrable_sq, ?_, ?_⟩
  · have hY : ∀ x : ℕ × ℕ → ℕ → ℝ,
        mlmcEstimator (fun ℓ (e : ℕ → ℝ) => f (backIter (emStep a b h) (N ℓ) e x₀))
          (fun p x => x p) L M x =
        K * mlmcEstimator (fun ℓ (e : ℕ → ℝ) => f (backIter (emStep a b h) (N ℓ) e x₀) / K)
          (fun p x => x p) L M x := fun x => by
      rw [← mlmcEstimator_const_mul]
      congr 1
      funext ℓ e
      field_simp
    have hT : ∫ ω, f (X ω) ∂μ = K * ∫ ω, f (X ω) / K ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext ω
      field_simp
    simp_rw [hY, hT, ← mul_sub, mul_pow]
    rw [integral_const_mul]
    calc K ^ 2 * _ < K ^ 2 * (ε / K) ^ 2 := mul_lt_mul_of_pos_left hmse (by positivity)
      _ = ε ^ 2 := by field_simp
  · refine hcost.trans (le_of_eq ?_)
    rw [Real.div_rpow hε.le hK0.le, Real.rpow_neg hK0.le, Real.rpow_two]
    field_simp

end Contracting

/-! ### The lookup-table streams of method 2 (Haas–Giles 2025, §3.2) -/

section LUT

variable {f : ℝ → ℝ}

/-- An inverse CDF of `N(0, 1)` on `(0, 1)` and its square are integrable on `[0, 1]`: if `f(U)`
has law `N(0, 1)` for `U` uniform on `(0, 1)`, then `f` and `f²` are interval integrable. -/
lemma intervalIntegrable_of_hasLaw_gaussian
    (hf : HasLaw f (gaussianReal 0 1) (volume.restrict (Set.Ioo 0 1))) :
    IntervalIntegrable f volume 0 1 ∧ IntervalIntegrable (fun u => f u ^ 2) volume 0 1 := by
  have hL2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal' 2 (by norm_num)
  have h1 : Integrable (id : ℝ → ℝ) ((volume.restrict (Set.Ioo (0 : ℝ) 1)).map f) := by
    rw [hf.map_eq]
    exact hL2.integrable one_le_two
  have h2 : Integrable (fun x : ℝ => x ^ 2) ((volume.restrict (Set.Ioo (0 : ℝ) 1)).map f) := by
    rw [hf.map_eq]
    exact hL2.integrable_sq
  have i1 := (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).1 h1
  have i2 := (integrable_map_measure (by fun_prop) hf.aemeasurable).1 h2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo, integrableOn_Ioc_iff_integrableOn_Ioo]
  exact ⟨i1, i2⟩

/-- On the open cell `(u_j, u_{j+1})` the table index `⌊2^d u⌋` is `j`. -/
lemma floor_eq_of_mem_cell {d j : ℕ} {u : ℝ}
    (hu : u ∈ Set.Ioo (gridPt d j) (gridPt d (j + 1))) : ⌊(2 : ℝ) ^ d * u⌋₊ = j := by
  have hpos : (0 : ℝ) < 2 ^ d := by positivity
  obtain ⟨h1, h2⟩ := hu
  unfold gridPt at h1 h2
  rw [div_lt_iff₀ hpos] at h1
  rw [lt_div_iff₀ hpos] at h2
  rw [Nat.floor_eq_iff (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])]
  push_cast at h2
  constructor <;> nlinarith

/-- The mean-square error of the lookup table read at a uniform index is the MSE of method 1:
`∫_0^1 (Z_{⌊2^d u⌋} − f(u))² du = ∑_j ∫_{I_j} (Z_j − f)²` (and the integrand is integrable). -/
lemma integral_lut_sq_sub (hf : IntervalIntegrable f volume 0 1)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume 0 1) (d : ℕ) :
    IntervalIntegrable (fun u => (lutValue f d ⌊(2 : ℝ) ^ d * u⌋₊ - f u) ^ 2) volume 0 1 ∧
    ∫ u in (0 : ℝ)..1, (lutValue f d ⌊(2 : ℝ) ^ d * u⌋₊ - f u) ^ 2 = method1MSE f d := by
  set G : ℝ → ℝ := fun u => (lutValue f d ⌊(2 : ℝ) ^ d * u⌋₊ - f u) ^ 2 with hG
  have heq : ∀ j, Set.EqOn G (fun u => (lutValue f d j - f u) ^ 2)
      (Set.Ioo (gridPt d j) (gridPt d (j + 1))) := fun j u hu => by
    simp only [hG, floor_eq_of_mem_cell hu]
  have hcell : ∀ j < 2 ^ d, IntervalIntegrable G volume (gridPt d j) (gridPt d (j + 1)) :=
    fun j hj => by
      have hint := intervalIntegrable_sq_sub (intervalIntegrable_cell hf hj)
        (intervalIntegrable_cell hf2 hj) (lutValue f d j)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (gridPt_lt d j).le,
        integrableOn_Ioc_iff_integrableOn_Ioo] at hint ⊢
      exact hint.congr_fun (heq j).symm measurableSet_Ioo
  have h0 : gridPt d 0 = 0 := by simp [gridPt]
  have h1 : gridPt d (2 ^ d) = 1 := by
    unfold gridPt
    push_cast
    exact div_self (by positivity)
  refine ⟨?_, ?_⟩
  · have := IntervalIntegrable.trans_iterate hcell
    rwa [h0, h1] at this
  · rw [← h0, ← h1, ← intervalIntegral.sum_integral_adjacent_intervals hcell, method1MSE]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_of_le (gridPt_lt d j).le,
      intervalIntegral.integral_of_le (gridPt_lt d j).le, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo (heq j)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The scaled lookup-table stream `c Z_{⌊2^d U⌋}` converges in probability to `c f(U)` as
`d → ∞` (Chebyshev's inequality and `tendsto_method1MSE`). -/
lemma tendstoInMeasure_lut (hmono : MonotoneOn f (Set.Ioo 0 1))
    (hf : HasLaw f (gaussianReal 0 1) (volume.restrict (Set.Ioo 0 1))) {U : Ω → ℝ}
    (hU : HasLaw U (volume.restrict (Set.Ioo 0 1)) P) (c : ℝ) :
    TendstoInMeasure P (fun (d : ℕ) ω => c * lutValue f d ⌊(2 : ℝ) ^ d * U ω⌋₊) atTop
      (fun ω => c * f (U ω)) := by
  obtain ⟨hfi, hf2⟩ := intervalIntegrable_of_hasLaw_gaussian hf
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε2 : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hbound : ∀ d : ℕ, P {ω | ε ≤ dist (c * lutValue f d ⌊(2 : ℝ) ^ d * U ω⌋₊)
      (c * f (U ω))} ≤ ENNReal.ofReal (c ^ 2 * method1MSE f d) / ENNReal.ofReal (ε ^ 2) := by
    intro d
    obtain ⟨hGi, hGint⟩ := integral_lut_sq_sub hfi hf2 d
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
      integrableOn_Ioc_iff_integrableOn_Ioo] at hGi
    have hGi' : IntegrableOn (fun u => c ^ 2 * (lutValue f d ⌊(2 : ℝ) ^ d * u⌋₊ - f u) ^ 2)
        (Set.Ioo 0 1) := hGi.const_mul _
    have hGm : AEMeasurable (fun u => ENNReal.ofReal
        (c ^ 2 * (lutValue f d ⌊(2 : ℝ) ^ d * u⌋₊ - f u) ^ 2)) (volume.restrict (Set.Ioo 0 1)) :=
      hGi'.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hlint : ∫⁻ ω, ENNReal.ofReal (c ^ 2 * (lutValue f d ⌊(2 : ℝ) ^ d * U ω⌋₊ -
        f (U ω)) ^ 2) ∂P = ENNReal.ofReal (c ^ 2 * method1MSE f d) := by
      rw [hU.lintegral_comp hGm, ← ofReal_integral_eq_lintegral_ofReal hGi'
        (Eventually.of_forall fun u => by positivity), integral_const_mul,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hGint]
    have hsub : {ω | ε ≤ dist (c * lutValue f d ⌊(2 : ℝ) ^ d * U ω⌋₊) (c * f (U ω))} ⊆
        {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal (c ^ 2 *
          (lutValue f d ⌊(2 : ℝ) ^ d * U ω⌋₊ - f (U ω)) ^ 2)} := fun ω (hω : ε ≤ _) => by
      show ENNReal.ofReal _ ≤ ENNReal.ofReal _
      apply ENNReal.ofReal_le_ofReal
      have h := pow_le_pow_left₀ hε.le hω 2
      rwa [Real.dist_eq, sq_abs, ← mul_sub, mul_pow] at h
    refine (measure_mono hsub).trans ?_
    rw [← hlint]
    exact meas_ge_le_lintegral_div ((hU.map_eq ▸ hGm).comp_aemeasurable hU.aemeasurable) hε2
      ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun d : ℕ => ENNReal.ofReal (c ^ 2 * method1MSE f d) /
      ENNReal.ofReal (ε ^ 2)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.div_const (ENNReal.tendsto_ofReal
      ((tendsto_method1MSE hmono hfi hf2).const_mul (c ^ 2))) (Or.inr hε2)
    rwa [mul_zero, ENNReal.ofReal_zero, ENNReal.zero_div] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    hbound

/-- The scaled lookup-table value `c Z_{⌊2^d u⌋}` is a measurable function of `u`. -/
lemma measurable_lut (d : ℕ) (c : ℝ) :
    Measurable fun u : ℝ => c * lutValue f d ⌊(2 : ℝ) ^ d * u⌋₊ := by
  have h : Measurable fun u : ℝ => ⌊(2 : ℝ) ^ d * u⌋₊ := (measurable_id.const_mul _).nat_floor
  exact ((measurable_from_nat (f := lutValue f d)).comp h).const_mul c

/-- Convergence in distribution only depends on the law of the limit. -/
lemma tendstoInDistribution_of_map_eq {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {Z : Ω → ℝ} {W : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => P) P) (hW : AEMeasurable W P')
    (heq : P'.map W = P.map Z) : TendstoInDistribution X atTop W (fun _ => P) P' := by
  refine ⟨h.forall_aemeasurable, hW, ?_⟩
  have e : (⟨P'.map W, Measure.isProbabilityMeasure_map hW⟩ : ProbabilityMeasure ℝ) =
      ⟨P.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩ := Subtype.ext heq
  rw [e]
  exact h.tendsto

/-- **Each lookup-table stream converges in distribution to `N(0, 1)`** (the premise of
Haas–Giles 2025, §3.2, p. 5: "produce an approximate random number `X^{(1)}` from the first `d/n`
bits of `j`, then `X^{(2)}` from the next `d/n` bits and so on, where each `X^{(i)}` follows
approximately the distribution `N(0,1/n)`"; the table is that of method 1, §3.1, (15)).  Let `f`
be monotone on `(0, 1)` with `f(U) ~ N(0, 1)` for `U` uniform on `(0, 1)` (as `Φ⁻¹` is), and let
`U` be uniform on `(0, 1)`.  Reading the method-1 table `Z_j = 2^d ∫_{I_j} f` with `2^d` entries
at the first `d` bits of `U`, `j = ⌊2^d U⌋`, gives random variables `Z_{⌊2^d U⌋}` that converge in
distribution to `N(0, 1)` as `d → ∞` (to any `G ~ N(0, 1)`).  The mean-square error
`E[(Z_{⌊2^d U⌋} − f(U))²]` is the MSE of method 1 (`integral_lut_sq_sub`), which tends to `0`
(`tendsto_method1MSE`); convergence in mean square gives convergence in probability (Chebyshev)
and hence in distribution (`TendstoInMeasure.tendstoInDistribution`). -/
theorem lutStream_tendstoInDistribution {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] (hmono : MonotoneOn f (Set.Ioo 0 1))
    (hf : HasLaw f (gaussianReal 0 1) (volume.restrict (Set.Ioo 0 1))) {U : Ω → ℝ}
    (hU : HasLaw U (volume.restrict (Set.Ioo 0 1)) P) {G : Ω' → ℝ}
    (hG : HasLaw G (gaussianReal 0 1) P') :
    TendstoInDistribution (fun (d : ℕ) ω => lutValue f d ⌊(2 : ℝ) ^ d * U ω⌋₊) atTop G
      (fun _ => P) P' := by
  have h := (tendstoInMeasure_lut hmono hf hU 1).tendstoInDistribution fun d =>
    (measurable_lut d 1).comp_aemeasurable hU.aemeasurable
  simp only [one_mul] at h
  refine tendstoInDistribution_of_map_eq h hG.aemeasurable ?_
  rw [hG.map_eq]
  exact ((hf.comp hU).map_eq).symm

/-- **The sum of `n` lookup-table streams is approximately `N(0, 1)`** (Haas–Giles 2025, §3.2,
p. 5: "For example take an integer `n` that divides `d` and produce an approximate random number
`X^{(1)}` from the first `d/n` bits of `j`, then `X^{(2)}` from the next `d/n` bits and so on,
where each `X^{(i)}` follows approximately the distribution `N(0,1/n)`.  Then `∑_{i=1}^n X^{(i)}`
has approximately the distribution `N(0,1)`."), with "approximately" read as convergence in
distribution as the bit width per stream `d → ∞` (`n ≥ 1` fixed).  Let `f` be as in
`lutStream_tendstoInDistribution` and `U_1, …, U_n` independent and uniform on `(0, 1)` (the
disjoint bit blocks of `j`).  Then `X_d^{(i)} = n^{−1/2} Z_{⌊2^d U_i⌋}` converges in distribution to
`N(0, 1/n)` for each `i`, and `∑_i X_d^{(i)}` converges in distribution to `N(0, 1)`: the premise of
`tendstoInDistribution_sum_of_approxNormal` holds, so that theorem applies.  Deviation: each
stream reads the method-1 table (15) scaled by `n^{−1/2}`, not the table that method 2 fits to the
sum by the least-squares iteration (16); the sign-bit storage of §3.1 is not used (for odd `f` it
gives the same values, `lutValue_upper_half`). -/
theorem lutStreams_sum_tendstoInDistribution {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] (hmono : MonotoneOn f (Set.Ioo 0 1))
    (hf : HasLaw f (gaussianReal 0 1) (volume.restrict (Set.Ioo 0 1))) {n : ℕ} (hn : 0 < n)
    {U : Fin n → Ω → ℝ} (hU : ∀ i, HasLaw (U i) (volume.restrict (Set.Ioo 0 1)) P)
    (hind : iIndepFun U P) {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal 0 1) P') :
    (∀ i, TendstoInDistribution
      (fun (d : ℕ) ω => (√(n : ℝ))⁻¹ * lutValue f d ⌊(2 : ℝ) ^ d * U i ω⌋₊) atTop id
      (fun _ => P) (gaussianReal 0 (n : ℝ≥0)⁻¹)) ∧
    TendstoInDistribution
      (fun (d : ℕ) ω => ∑ i, (√(n : ℝ))⁻¹ * lutValue f d ⌊(2 : ℝ) ^ d * U i ω⌋₊) atTop G
      (fun _ => P) P' := by
  have hind' : ∀ d : ℕ, iIndepFun
      (fun i ω => (√(n : ℝ))⁻¹ * lutValue f d ⌊(2 : ℝ) ^ d * U i ω⌋₊) P := fun d =>
    hind.comp (fun _ u => (√(n : ℝ))⁻¹ * lutValue f d ⌊(2 : ℝ) ^ d * u⌋₊)
      fun _ => measurable_lut d _
  have hlaw : (gaussianReal 0 1).map (fun x => (√(n : ℝ))⁻¹ * x) =
      gaussianReal 0 (n : ℝ≥0)⁻¹ := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp only [NNReal.coe_mk, NNReal.coe_inv, NNReal.coe_natCast, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  have hX : ∀ i, TendstoInDistribution
      (fun (d : ℕ) ω => (√(n : ℝ))⁻¹ * lutValue f d ⌊(2 : ℝ) ^ d * U i ω⌋₊) atTop id
      (fun _ => P) (gaussianReal 0 (n : ℝ≥0)⁻¹) := fun i => by
    have h := (tendstoInMeasure_lut hmono hf (hU i) (√(n : ℝ))⁻¹).tendstoInDistribution
      fun d => (measurable_lut d _).comp_aemeasurable (hU i).aemeasurable
    refine tendstoInDistribution_of_map_eq h aemeasurable_id ?_
    rw [Measure.map_id, ← hlaw, ← (hf.comp (hU i)).map_eq,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hf.comp (hU i)).aemeasurable]
    rfl
  exact ⟨hX, tendstoInDistribution_sum_of_approxNormal hn hind' hX hG⟩

end LUT

/-! ### Standard Monte Carlo for exit times (Giles 2015, §5.5) -/

/-- **Standard Monte Carlo for exit times costs `O(ε⁻⁴)`, or `O(ε⁻³)` with first-order weak
convergence** (Giles 2015, §5.5, p. 43: "They prove that this can be achieved for very general
multi-dimensional SDEs at a computational cost which is `O(ε^{−3}|log ε|^{1/2})`.  This is better
than the `O(ε^{−4})` complexity of a standard Monte Carlo simulation using the same numerical
approximation of the exit time, but is not better than the complexity achieved by Gobet and
Menozzi (2010) using a Monte Carlo simulation with a boundary correction which improves the weak
order of convergence to first order").  With time step `h_L = 2^{−L}`, cost `c₃ 2^L` per sample
(`γ = 1`), `V[P_L] ≤ V̄` and the bias bound `c₁ h_L^{1/2}` (weak order `1/2` of the uncorrected
exit time), `mc_complexity` gives `L` and `N ≥ 1` with `(c₁ 2^{−L/2})² + V̄/N ≤ ε²` (a bound on
the MSE) at cost `N c₃ 2^L ≤ c₄ ε⁻⁴`; with the bias bound `c₁ h_L` (weak order `1`,
Gobet–Menozzi) the cost is `≤ c₄ ε⁻³`.  The multilevel cost `ε⁻³ |log ε|^{1/2}` is `o(ε⁻⁴)` as
`ε → 0` ("better than"), and at least `ε⁻³` for `ε ≤ e⁻¹` ("not better than").  Like
`mc_complexity`, the first two parts are statements about the parameters only: the weak orders
enter through the form of the bias bound `c₁ h_L^{1/2}` (resp. `c₁ h_L`) in the bound
`(bias)² + V̄/N` on the MSE of the plain Monte Carlo mean (`mc_estimate`,
`mse_eq_variance_add_sq_bias`), and no estimator appears (the exit-time analysis is not
formalised).  These are upper bounds; the matching lower bounds for an estimator whose weak order
is attained, cost `≥ c ε⁻⁴` (resp. `≥ c ε⁻³`), are `mc_complexity_lower` with `α = 1/2`
(resp. `α = 1`) and `γ = 1`, so the comparison "better than `O(ε⁻⁴)`" is between the paper's
multilevel bound and that lower bound.  The paper does not write out the rate `ε⁻³`. -/
theorem mc_exit_time_complexity {c₁ c₃ Vbar : ℝ} (hc₁ : 0 < c₁) (hc₃ : 0 < c₃)
    (hV : 0 ≤ Vbar) :
    (∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ L N : ℕ, 0 < N ∧
      (c₁ * (2 : ℝ) ^ (-((L : ℝ) / 2))) ^ 2 + Vbar / N ≤ ε ^ 2 ∧
      (N : ℝ) * (c₃ * 2 ^ L) ≤ c₄ * ε ^ (-4 : ℝ)) ∧
    (∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ L N : ℕ, 0 < N ∧
      (c₁ * (2 : ℝ) ^ (-(L : ℝ))) ^ 2 + Vbar / N ≤ ε ^ 2 ∧
      (N : ℝ) * (c₃ * 2 ^ L) ≤ c₄ * ε ^ (-3 : ℝ)) ∧
    Tendsto (fun ε : ℝ => ε ^ (-3 : ℝ) * Real.sqrt |Real.log ε| / ε ^ (-4 : ℝ)) (𝓝[>] 0)
      (𝓝 0) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-1) →
      ε ^ (-3 : ℝ) ≤ ε ^ (-3 : ℝ) * Real.sqrt |Real.log ε| := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨c₄, hc₄, h⟩ := mc_complexity (α := 1 / 2) (γ := 1) (by norm_num) one_pos hc₁ hc₃ hV
    refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
    obtain ⟨L, N, hN, h1, h2⟩ := h ε hε hε1
    refine ⟨L, N, hN, ?_, ?_⟩
    · rwa [show (1 / 2 : ℝ) * (L : ℝ) = (L : ℝ) / 2 by ring] at h1
    · rwa [one_mul, Real.rpow_natCast, show (-2 : ℝ) - 1 / (1 / 2) = -4 by norm_num] at h2
  · obtain ⟨c₄, hc₄, h⟩ := mc_complexity (α := 1) (γ := 1) one_pos one_pos hc₁ hc₃ hV
    refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
    obtain ⟨L, N, hN, h1, h2⟩ := h ε hε hε1
    refine ⟨L, N, hN, ?_, ?_⟩
    · rwa [one_mul] at h1
    · rwa [one_mul, Real.rpow_natCast, show (-2 : ℝ) - 1 / 1 = -3 by norm_num] at h2
  · -- `ε^{−3} √|log ε| / ε^{−4} = ε √|log ε| ≤ ε − ε log ε` on `(0, 1)`
    have hup : Tendsto (fun ε : ℝ => ε - Real.log ε * ε ^ (1 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using h1.sub (tendsto_log_mul_rpow_nhdsGT_zero one_pos)
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hev] with ε hε
      have := hε.1
      positivity
    · filter_upwards [hev] with ε hε
      obtain ⟨h0, h1⟩ := hε
      have hlog : Real.log ε < 0 := Real.log_neg h0 h1
      have e : ε ^ (-3 : ℝ) * Real.sqrt |Real.log ε| / ε ^ (-4 : ℝ) =
          ε * Real.sqrt |Real.log ε| := by
        rw [mul_div_right_comm, ← Real.rpow_sub h0]
        norm_num
      have hs : Real.sqrt |Real.log ε| ≤ 1 + |Real.log ε| := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [abs_nonneg (Real.log ε)]
      rw [e, Real.rpow_one, abs_of_neg hlog] at *
      nlinarith [mul_le_mul_of_nonneg_left hs h0.le]
  · intro ε hε hεe
    have hlog : Real.log ε ≤ -1 := by
      calc Real.log ε ≤ Real.log (Real.exp (-1)) := Real.log_le_log hε hεe
        _ = -1 := Real.log_exp _
    have h1 : 1 ≤ Real.sqrt |Real.log ε| := by
      rw [Real.one_le_sqrt, abs_of_neg (by linarith)]
      linarith
    exact le_mul_of_one_le_right (Real.rpow_nonneg hε.le _) h1

section MCLower

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω}

/-- **Standard Monte Carlo with an attained weak order costs at least `ε^{−2−γ/α}`** (Giles 2015,
§5.5, p. 43: "This is better than the `O(ε^{−4})` complexity of a standard Monte Carlo simulation
using the same numerical approximation of the exit time"; §2.1, p. 7: "`C_L = O(ε^{−γ/α})`").  Let
`P_L` be square integrable and `P` integrable, and let the plain Monte Carlo mean of `N ≥ 1`
independent samples `P_L(ω⁽ⁿ⁾)` (inputs of law `ν`) have `MSE = E[(Ŷ − E[P])²] ≤ ε²`, `ε > 0`.  If
the bias is attained, `|E[P_L − P]| ≥ a₁ 2^{−αL}` (`a₁, α > 0`), `V[P_L] ≥ v`, and each sample costs
`C ≥ a₃ 2^{γL}` (`a₃, γ ≥ 0`), then the total cost is `N C ≥ v a₃ a₁^{γ/α} ε^{−2−γ/α}`.  Indeed
`MSE = V[P_L]/N + (E[P_L − P])²` forces `N ≥ v ε⁻²` and `2^{αL} ≥ a₁/ε`.  For exit times
(`γ = 1`, time step `2^{−L}`) weak order `α = 1/2` gives `ε⁻⁴` and `α = 1` gives `ε⁻³`, the
matching lower bounds for `mc_exit_time_complexity`. -/
theorem mc_complexity_lower [IsProbabilityMeasure μ] (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {P PL : Ω₀ → ℝ}
    (hP : Integrable P ν) (hPLm : Measurable PL) (hPL : MemLp PL 2 ν)
    {α γ a₁ v a₃ C ε : ℝ} {L N : ℕ} (hα : 0 < α) (hγ : 0 ≤ γ) (ha₁ : 0 < a₁) (ha₃ : 0 ≤ a₃)
    (hbias : a₁ * (2 : ℝ) ^ (-(α * (L : ℝ))) ≤ |∫ y, PL y - P y ∂ν|)
    (hvar : v ≤ variance PL ν) (hC : a₃ * (2 : ℝ) ^ (γ * (L : ℝ)) ≤ C) (hN : 0 < N)
    (hε : 0 < ε)
    (hmse : μ[fun x => ((N : ℝ)⁻¹ * ∑ n ∈ range N, PL (ω n x) - ∫ y, P y ∂ν) ^ 2] ≤ ε ^ 2) :
    v * a₃ * a₁ ^ (γ / α) * ε ^ (-2 - γ / α) ≤ N * C := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω 0).map_eq]
    exact Measure.isProbabilityMeasure_map (hω 0).measurable.aemeasurable
  obtain ⟨hmean, hvarY, -, -⟩ := mc_estimate ω hω hind hPLm hPL hN
  have hY : MemLp (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, PL (ω n x)) 2 μ :=
    (memLp_finsetSum _ fun n _ => hPL.comp_measurePreserving (hω n)).const_mul _
  rw [mse_eq_variance_add_sq_bias hY, hmean, hvarY,
    ← integral_sub (hPL.integrable one_le_two) hP] at hmse
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hVN : 0 ≤ variance PL ν / N := div_nonneg (variance_nonneg _ _) hNpos.le
  have h2L : 0 < (2 : ℝ) ^ (α * (L : ℝ)) := Real.rpow_pos_of_pos two_pos _
  -- the bias: `a₁ 2^{−αL} ≤ ε`, so `a₁/ε ≤ 2^{αL}`
  have hb : a₁ * (2 : ℝ) ^ (-(α * (L : ℝ))) ≤ ε := by
    have h1 : (a₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 ≤ ε ^ 2 := by
      calc (a₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 ≤ |∫ y, PL y - P y ∂ν| ^ 2 :=
            pow_le_pow_left₀ (by positivity) hbias 2
        _ = (∫ y, PL y - P y ∂ν) ^ 2 := sq_abs _
        _ ≤ ε ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hε.le two_ne_zero).1 h1
  have h1 : a₁ / ε ≤ (2 : ℝ) ^ (α * (L : ℝ)) := by
    rw [Real.rpow_neg zero_le_two, ← div_eq_mul_inv, div_le_iff₀ h2L] at hb
    rw [div_le_iff₀ hε]
    linarith
  have hL : (a₁ / ε) ^ (γ / α) ≤ (2 : ℝ) ^ (γ * (L : ℝ)) := by
    calc (a₁ / ε) ^ (γ / α) ≤ ((2 : ℝ) ^ (α * (L : ℝ))) ^ (γ / α) :=
          Real.rpow_le_rpow (by positivity) h1 (div_nonneg hγ hα.le)
      _ = (2 : ℝ) ^ (γ * (L : ℝ)) := by
        rw [← Real.rpow_mul zero_le_two]
        congr 1
        field_simp
  -- the sample size: `v ≤ N ε²`
  have hv : v ≤ N * ε ^ 2 := by
    have h2 : variance PL ν / N ≤ ε ^ 2 := by nlinarith [sq_nonneg (∫ y, PL y - P y ∂ν)]
    rw [div_le_iff₀ hNpos] at h2
    linarith
  have hC0 : 0 ≤ a₃ * (2 : ℝ) ^ (γ * (L : ℝ)) := by positivity
  rcases le_or_gt v 0 with hv0 | hv0
  · have h3 : 0 ≤ -v * a₃ * a₁ ^ (γ / α) * ε ^ (-2 - γ / α) := by
      have := neg_nonneg.2 hv0
      positivity
    have h4 : 0 ≤ (N : ℝ) * C := mul_nonneg hNpos.le (hC0.trans hC)
    linarith
  · have hεγ : 0 < ε ^ (γ / α) := Real.rpow_pos_of_pos hε _
    have he : v * a₃ * a₁ ^ (γ / α) * ε ^ (-2 - γ / α) =
        v * (ε ^ 2)⁻¹ * (a₃ * (a₁ / ε) ^ (γ / α)) := by
      rw [Real.div_rpow ha₁.le hε.le, Real.rpow_sub hε, Real.rpow_neg hε.le, Real.rpow_two]
      field_simp
    have hvN : v * (ε ^ 2)⁻¹ ≤ N := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      exact hv
    rw [he]
    calc v * (ε ^ 2)⁻¹ * (a₃ * (a₁ / ε) ^ (γ / α)) ≤ N * (a₃ * (2 : ℝ) ^ (γ * (L : ℝ))) :=
          mul_le_mul hvN (mul_le_mul_of_nonneg_left hL ha₃) (by positivity) hNpos.le
      _ ≤ N * C := mul_le_mul_of_nonneg_left hC hNpos.le

end MCLower

/-! ### `β ≤ 2α` and the optimality of standard MLMC (Giles 2015, §2.1 and §2.4) -/

/-- `2^{−δℓ} → 0` as `ℓ → ∞` for `δ > 0`. -/
lemma tendsto_two_rpow_neg_mul_nat {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ℓ : ℕ => (2 : ℝ) ^ (-(δ * ℓ))) atTop (𝓝 0) := by
  have h : (fun ℓ : ℕ => (2 : ℝ) ^ (-(δ * ℓ))) = fun ℓ : ℕ => ((2 : ℝ) ^ (-δ)) ^ ℓ :=
    funext fun ℓ => by rw [← two_rpow_mul_nat, neg_mul]
  rw [h]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg zero_le_two _)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))

/-- If `a₁ 2^{−αℓ} ≤ C 2^{−δℓ}` for infinitely many `ℓ` and `a₁ > 0`, then `δ ≤ α`. -/
lemma le_of_frequently_two_rpow_le {a₁ C α δ : ℝ} (ha₁ : 0 < a₁)
    (h : ∃ᶠ ℓ : ℕ in atTop, a₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) ≤ C * (2 : ℝ) ^ (-(δ * (ℓ : ℝ)))) :
    δ ≤ α := by
  by_contra hlt
  rw [not_le] at hlt
  have hsmall : ∀ᶠ ℓ : ℕ in atTop, C * (2 : ℝ) ^ (-((δ - α) * ℓ)) < a₁ := by
    have h := (tendsto_two_rpow_neg_mul_nat (sub_pos.2 hlt)).const_mul C
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds ha₁)
  obtain ⟨ℓ, h1, h2⟩ := (h.and_eventually hsmall).exists
  have hx : (2 : ℝ) ^ (-(δ * (ℓ : ℝ))) =
      (2 : ℝ) ^ (-((δ - α) * ℓ)) * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) := by
    rw [← Real.rpow_add two_pos]
    ring_nf
  rw [hx, ← mul_assoc] at h1
  have := le_of_mul_le_mul_right h1 (Real.rpow_pos_of_pos two_pos _)
  linarith

section Rates

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **`β ≤ 2α` when the variance is comparable to the second moment** (Giles 2015, §2.1, p. 7:
"If `β = 2α`, which is usually the best that can be achieved since typically `V[P_ℓ − P_{ℓ−1}]` is
similar in magnitude to `E[(P_ℓ − P_{ℓ−1})²]` which is greater than `(E[P_ℓ − P_{ℓ−1}])²`"), with
the rate `α` of the mean correction.  Let the `P_ℓ` be square integrable, and for all large `ℓ`
let `V_ℓ = V[P_ℓ − P_{ℓ−1}] ≥ κ E[(P_ℓ − P_{ℓ−1})²]` with `κ > 0` ("similar in magnitude") and
`V_ℓ ≤ c₂ 2^{−βℓ}` (condition iii)).  If the weak rate is attained infinitely often,
`|E[P_ℓ − P_{ℓ−1}]| ≥ c 2^{−αℓ}` with `c > 0`, then `β ≤ 2α`: indeed
`κ c² 2^{−2αℓ} ≤ κ (E[ΔP_ℓ])² ≤ κ E[(ΔP_ℓ)²] ≤ V_ℓ ≤ c₂ 2^{−βℓ}`.  The hypothesis on `κ` is needed:
for the deterministic corrections `ΔP_ℓ = 2^{−αℓ}`, `V_ℓ = 0` satisfies iii) for every `β`. -/
theorem beta_le_two_alpha {Pl : ℕ → Ω → ℝ} {α β κ c c₂ : ℝ}
    (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ) (hκ : 0 < κ) (hc : 0 < c)
    (hVκ : ∀ᶠ ℓ : ℕ in atTop,
      κ * ∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ ≤ variance (levelDiff Pl ℓ) μ)
    (h_iii : ∀ᶠ ℓ : ℕ in atTop,
      variance (levelDiff Pl ℓ) μ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (hweak : ∃ᶠ ℓ : ℕ in atTop,
      c * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) ≤ |∫ ω, levelDiff Pl ℓ ω ∂μ|) :
    β ≤ 2 * α := by
  by_contra hlt
  rw [not_le] at hlt
  have hδ : 0 < β - 2 * α := by linarith
  have hsmall : ∀ᶠ ℓ : ℕ in atTop, c₂ * (2 : ℝ) ^ (-((β - 2 * α) * ℓ)) < c ^ 2 * κ := by
    have h := (tendsto_two_rpow_neg_mul_nat hδ).const_mul c₂
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  obtain ⟨ℓ, ⟨h3, h1, h2⟩, h4⟩ :=
    ((hweak.and_eventually (hVκ.and h_iii)).and_eventually hsmall).exists
  -- `c² κ 2^{−2αℓ} ≤ κ (E ΔP)² ≤ κ E[ΔP²] ≤ V ≤ c₂ 2^{−βℓ}`
  have hx : (2 : ℝ) ^ (-(β * (ℓ : ℝ))) =
      (2 : ℝ) ^ (-((β - 2 * α) * ℓ)) * ((2 : ℝ) ^ (-(α * (ℓ : ℝ)))) ^ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos]
    congr 1
    push_cast
    ring
  have hpos : 0 < (2 : ℝ) ^ (-(α * (ℓ : ℝ))) := Real.rpow_pos_of_pos two_pos _
  have hsq : (c * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) ^ 2 ≤ (∫ ω, levelDiff Pl ℓ ω ∂μ) ^ 2 := by
    rw [← sq_abs (∫ ω, levelDiff Pl ℓ ω ∂μ)]
    exact pow_le_pow_left₀ (by positivity) h3 2
  have hJ := sq_integral_le_integral_sq_of_memLp (memLp_levelDiff hPl ℓ)
  have hchain : κ * (c * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) ^ 2 ≤
      c₂ * (2 : ℝ) ^ (-((β - 2 * α) * ℓ)) * ((2 : ℝ) ^ (-(α * (ℓ : ℝ)))) ^ 2 := by
    calc κ * (c * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) ^ 2 ≤ κ * ∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_left (hsq.trans hJ) hκ.le
      _ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) := h1.trans h2
      _ = _ := by rw [hx, mul_assoc]
  rw [mul_pow, ← mul_assoc, mul_comm κ] at hchain
  have := le_of_mul_le_mul_right hchain (pow_pos hpos 2)
  linarith

/-- **`β ≤ 2α` for the weak rate of condition i)** (Giles 2015, §2.1, p. 7: "If `β = 2α`, which is
usually the best that can be achieved since typically `V[P_ℓ − P_{ℓ−1}]` is similar in magnitude
to `E[(P_ℓ − P_{ℓ−1})²]` which is greater than `(E[P_ℓ − P_{ℓ−1}])²`"), with `α` the rate of the
bias `|E[P_ℓ − P]|` as in Theorem 1.  Let `P` be integrable, the `P_ℓ` square integrable with
`E[P_ℓ] → E[P]`, and for all large `ℓ` let `V_ℓ ≥ κ E[(P_ℓ − P_{ℓ−1})²]` with `κ > 0` and
`V_ℓ ≤ c₂ 2^{−βℓ}`.  If the bias rate is attained infinitely often, `|E[P_ℓ − P]| ≥ a₁ 2^{−αℓ}` with
`a₁ > 0`, then `β ≤ 2α`.  For `β > 0`, `E[(ΔP_ℓ)²] ≤ (c₂/κ) 2^{−βℓ}` for `ℓ ≥ ℓ₀` gives
`|E[P_ℓ − P]| = O(2^{−βℓ/2})` (`weak_rate_of_second_moment`, applied to the shifted sequence
`P_{ℓ₀ + k}`); for `β ≤ 0`, the bias tends to `0`, so `α ≥ 0`. -/
theorem beta_le_two_alpha_of_bias {P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {α β κ a₁ c₂ : ℝ}
    (hP : Integrable P μ) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ)
    (hlim : Tendsto (fun ℓ => μ[Pl ℓ]) atTop (𝓝 (μ[P]))) (hκ : 0 < κ) (ha₁ : 0 < a₁)
    (hVκ : ∀ᶠ ℓ : ℕ in atTop,
      κ * ∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ ≤ variance (levelDiff Pl ℓ) μ)
    (h_iii : ∀ᶠ ℓ : ℕ in atTop,
      variance (levelDiff Pl ℓ) μ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (hbias : ∃ᶠ ℓ : ℕ in atTop,
      a₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) ≤ |∫ ω, Pl ℓ ω - P ω ∂μ|) :
    β ≤ 2 * α := by
  rcases le_or_gt β 0 with hβ | hβ
  · -- the bias tends to `0`, so `α ≥ 0`
    have hb : Tendsto (fun ℓ : ℕ => |∫ ω, Pl ℓ ω - P ω ∂μ|) atTop (𝓝 0) := by
      have h := (hlim.sub_const (μ[P])).abs
      rw [sub_self, abs_zero] at h
      refine h.congr fun ℓ => ?_
      rw [integral_sub ((hPl ℓ).integrable one_le_two) hP]
    have hev : ∀ᶠ ℓ : ℕ in atTop,
        |∫ ω, Pl ℓ ω - P ω ∂μ| ≤ a₁ / 2 * (2 : ℝ) ^ (-(0 * (ℓ : ℝ))) :=
      (hb.eventually (ge_mem_nhds (half_pos ha₁))).mono fun ℓ h => by
        rwa [zero_mul, neg_zero, Real.rpow_zero, mul_one]
    have hα := le_of_frequently_two_rpow_le ha₁
      ((hbias.and_eventually hev).mono fun ℓ h => h.1.trans h.2)
    linarith
  · -- `E[ΔP_ℓ²] ≤ (c₂/κ) 2^{−βℓ}` for `ℓ ≥ ℓ₀`, so `|E[P_ℓ − P]| = O(2^{−βℓ/2})`
    obtain ⟨ℓ₀, hℓ₀⟩ := eventually_atTop.1 (hVκ.and h_iii)
    have hc₂ : 0 ≤ c₂ := by
      have h := (variance_nonneg _ μ).trans (hℓ₀ ℓ₀ le_rfl).2
      exact nonneg_of_mul_nonneg_left h (Real.rpow_pos_of_pos two_pos _)
    -- the shifted sequence `k ↦ P_{ℓ₀ + k}`
    have hshift : ∀ j : ℕ, levelDiff (fun k => Pl (ℓ₀ + k)) (j + 1) = levelDiff Pl (ℓ₀ + j + 1) :=
      fun j => rfl
    have h2 : ∀ k : ℕ, 1 ≤ k → ∫ ω, levelDiff (fun k => Pl (ℓ₀ + k)) k ω ^ 2 ∂μ ≤
        c₂ / κ * (2 : ℝ) ^ (-(β * (ℓ₀ : ℝ))) * (2 : ℝ) ^ (-(β * (k : ℝ))) := fun k hk => by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h := hℓ₀ (ℓ₀ + j + 1) (by omega)
      have e : (2 : ℝ) ^ (-(β * ((ℓ₀ + j + 1 : ℕ) : ℝ))) =
          (2 : ℝ) ^ (-(β * (ℓ₀ : ℝ))) * (2 : ℝ) ^ (-(β * ((j + 1 : ℕ) : ℝ))) := by
        rw [← Real.rpow_add two_pos]
        congr 1
        push_cast
        ring
      rw [hshift j, mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hκ, mul_comm _ κ, ← e]
      exact h.1.trans h.2
    have hlim' : Tendsto (fun k => μ[Pl (ℓ₀ + k)]) atTop (𝓝 (μ[P])) :=
      hlim.comp ((tendsto_add_atTop_nat ℓ₀).congr fun k => Nat.add_comm k ℓ₀)
    have hw := weak_rate_of_second_moment hβ
      (mul_nonneg (div_nonneg hc₂ hκ.le) (Real.rpow_nonneg zero_le_two _)) hP
      (fun k => hPl (ℓ₀ + k)) hlim' h2
    set C : ℝ := Real.sqrt (c₂ / κ * (2 : ℝ) ^ (-(β * (ℓ₀ : ℝ)))) / ((2 : ℝ) ^ (β / 2) - 1)
    have hev : ∀ᶠ ℓ : ℕ in atTop, |∫ ω, Pl ℓ ω - P ω ∂μ| ≤
        C * (2 : ℝ) ^ (β / 2 * (ℓ₀ : ℝ)) * (2 : ℝ) ^ (-(β / 2 * (ℓ : ℝ))) :=
      eventually_atTop.2 ⟨ℓ₀, fun ℓ hℓ => by
        obtain ⟨k, rfl⟩ : ∃ k, ℓ = ℓ₀ + k := ⟨ℓ - ℓ₀, by omega⟩
        refine (hw k).trans (le_of_eq ?_)
        rw [mul_assoc, ← Real.rpow_add two_pos]
        congr 2
        push_cast
        ring⟩
    have h := le_of_frequently_two_rpow_le ha₁
      ((hbias.and_eventually hev).mono fun ℓ h => h.1.trans h.2)
    linarith

/-- A rectangle in one dimension is an interval of levels:
`∑_{ℓ ∈ rect L} g(ℓ_0) = ∑_{k ≤ L_0} g(k)`. -/
lemma sum_rectSet_fin_one {β : Type*} [AddCommMonoid β] (L : Fin 1 → ℕ) (g : ℕ → β) :
    ∑ ℓ ∈ rectSet L, g (ℓ 0) = ∑ k ∈ range (L 0 + 1), g k := by
  refine Finset.sum_nbij' (fun ℓ => ℓ 0) (fun k _ => k) (fun ℓ hℓ => ?_) (fun k hk => ?_)
    (fun ℓ _ => ?_) (fun k _ => rfl) (fun ℓ _ => rfl)
  · rw [mem_rectSet] at hℓ
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (hℓ 0))
  · rw [mem_rectSet]
    intro d
    rw [Subsingleton.elim d 0]
    exact Nat.le_of_lt_succ (Finset.mem_range.1 hk)
  · funext d
    rw [Subsingleton.elim d 0]

/-- In one dimension the cross-difference of `m ↦ P_{m_0}` is the MLMC correction
`P_ℓ − P_{ℓ−1}` (`P_{−1} ≡ 0`). -/
lemma crossDiff_fin_one {Ω₀ : Type*} (Pl : ℕ → Ω₀ → ℝ) (ℓ : Fin 1 → ℕ) (ω : Ω₀) :
    crossDiff (fun m : Fin 1 → ℕ => Pl (m 0) ω) ℓ = levelDiff Pl (ℓ 0) ω := by
  rw [crossDiff_one, Fin.cons_zero]
  cases ℓ 0 with
  | zero => rw [if_pos rfl, sub_zero, levelDiff_zero]
  | succ k => rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, levelDiff_succ]

/-- **Standard MLMC attains `O(ε⁻²)` only if `γ < β`** (Giles 2015, §2.4, pp. 15–16: "Using the
standard MLMC approach, `β`, the rate of convergence of the multilevel variance, will usually be
independent of `D`, but `γ`, the rate of increase in the computational cost, will increase at
least linearly with `D`.  Therefore, in a high enough dimension we will have `β ≤ γ` and therefore
the overall computational complexity will be less (often much less) than the optimal `O(ε⁻²)`"),
the case `D = 1` of `mimc_rect_necessary`.  Let the level estimators `Y ℓ n` (`n ≥ 1` samples) be
square integrable with `E[Y ℓ n] = E[P_ℓ − P_{ℓ−1}]` and `V[Y ℓ n] = V_ℓ/n`, independent across
levels, with costs of mean `n C_ℓ`, and let the rates be attained: `|E[P_ℓ − P]| ≥ a₁ 2^{−αℓ}`,
`V_ℓ ≥ a₂ 2^{−βℓ}`, `C_ℓ ≥ a₃ 2^{γℓ}` (`α, a₁, a₂, a₃ > 0`, `γ ≥ 0`).  If for some `c₄` and `ε₀ > 0`
every `0 < ε < ε₀` admits `L` and `N_ℓ ≥ 1` with `MSE < ε²` and expected cost `≤ c₄ ε⁻²`, then
`γ < β` and `γ/α ≤ 2`; so with `β ≤ γ` the optimal complexity `O(ε⁻²)` is out of reach.  The paper
gives no hypotheses for this direction; the attained rates are ours.  The paper's "less (often
much less) than the optimal" means suboptimal, i.e. a cost of larger order than `ε⁻²`. -/
theorem mlmc_optimal_complexity_necessary (P : Ω → ℝ) (Pl : ℕ → Ω → ℝ)
    (Y : ℕ → ℕ → Ω → ℝ) (Cost : ℕ → ℕ → Ω → ℝ) (V C : ℕ → ℝ) {α β γ a₁ a₂ a₃ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hP : Integrable P μ) (hPl : ∀ ℓ, Integrable (Pl ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost_int : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (hCost_mean : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_var : ∀ ℓ n, 0 < n → variance (Y ℓ n) μ = V ℓ / n)
    (h_iii : ∀ ℓ n, 0 < n → μ[Y ℓ n] = μ[levelDiff Pl ℓ])
    (hbias : ∀ ℓ : ℕ, a₁ * (2 : ℝ) ^ (-(α * ℓ)) ≤ |μ[fun ω => Pl ℓ ω - P ω]|)
    (hV : ∀ ℓ : ℕ, a₂ * (2 : ℝ) ^ (-(β * ℓ)) ≤ V ℓ)
    (hC : ∀ ℓ : ℕ, a₃ * (2 : ℝ) ^ (γ * ℓ) ≤ C ℓ)
    (hopt : ∃ c₄ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun ω => (∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - μ[P]) ^ 2] < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] ≤ c₄ * ε ^ (-2 : ℝ)) :
    γ < β ∧ γ / α ≤ 2 := by
  have hdot : ∀ (a : ℝ) (ℓ : Fin 1 → ℕ), dot (fun _ => a) ℓ = a * ℓ 0 := fun a ℓ => by
    simp [dot]
  have hfun : ∀ ℓ : Fin 1 → ℕ, (fun _ : Fin 1 => ℓ 0) = ℓ := fun ℓ => by
    funext d
    rw [Subsingleton.elim d 0]
  obtain ⟨h1, h2⟩ := mimc_rect_necessary (D := 1) (μ := μ) P (fun ℓ => Pl (ℓ 0))
    (fun ℓ => Y (ℓ 0)) (fun ℓ => Cost (ℓ 0)) (fun ℓ => V (ℓ 0)) (fun ℓ => C (ℓ 0))
    (α := fun _ => α) (β := fun _ => β) (γ := fun _ => γ) (fun _ => hα) (fun _ => hγ)
    ha₁ ha₂ ha₃ hP (fun ℓ => hPl (ℓ 0)) (fun ℓ => hY (ℓ 0))
    (fun N hN i j hij => by
      have hij' : i 0 ≠ j 0 := fun h => hij (by rw [← hfun i, ← hfun j, h])
      have h := hind (fun k => N fun _ => k) (fun k => hN _) hij'
      simp only [hfun] at h
      exact h)
    (fun ℓ => hCost_int (ℓ 0)) (fun ℓ => hCost_mean (ℓ 0)) (fun ℓ => h_var (ℓ 0))
    (fun ℓ n hn => by
      rw [h_iii (ℓ 0) n hn]
      congr 1
      funext ω
      exact (crossDiff_fin_one Pl ℓ ω).symm)
    (fun ℓ d => by rw [Subsingleton.elim d 0]; exact hbias (ℓ 0))
    (fun ℓ => by rw [hdot]; exact hV (ℓ 0))
    (fun ℓ => by rw [hdot]; exact hC (ℓ 0))
    (by
      obtain ⟨c₄, ε₀, hε₀, h⟩ := hopt
      refine ⟨c₄, ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
      obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hεε₀
      refine ⟨fun _ => L, fun ℓ => N (ℓ 0), fun ℓ => hN (ℓ 0), ?_, ?_⟩
      · have e : ∀ x, ∑ ℓ ∈ rectSet (fun _ : Fin 1 => L), Y (ℓ 0) (N (ℓ 0)) x =
            ∑ k ∈ range (L + 1), Y k (N k) x := fun x =>
          sum_rectSet_fin_one (fun _ => L) (fun k => Y k (N k) x)
        simp only [e]
        exact hmse
      · have e : ∀ x, ∑ ℓ ∈ rectSet (fun _ : Fin 1 => L), Cost (ℓ 0) (N (ℓ 0)) x =
            ∑ k ∈ range (L + 1), Cost k (N k) x := fun x =>
          sum_rectSet_fin_one (fun _ => L) (fun k => Cost k (N k) x)
        simp only [e]
        exact hcost)
  exact ⟨h1 0, by simpa using h2⟩

end Rates

/-! ### The Euler–Maruyama coupling with refinement factor `M` (Giles 2015, §5.1) -/

section RefinementFactor

/-- The normal increments of the coarse path for the refinement factor `M` (Giles 2015, §5.1):
`Z^c_k = (Z_{Mk} + Z_{Mk+1} + ⋯ + Z_{Mk+M−1})/√M`, the normalised sum of the `M` fine increments
inside the `k`-th coarse step (`pairAvg` is the case `M = 2`). -/
noncomputable def blockAvg (M : ℕ) (z : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ range M, z (M * k + i)) / Real.sqrt M

/-- The fine level-`ℓ` approximation for the refinement factor `M` (Giles 2015, §5.1): a payoff
`Φ ℓ` of the Euler–Maruyama path with step `h_ℓ = h₀ M^{−ℓ}` driven by the normal increments
`z`. -/
noncomputable def emFineM (a b : ℝ → ℝ → ℝ) (h₀ S₀ : ℝ) (M : ℕ) (Φ : ℕ → (ℕ → ℝ) → ℝ) (ℓ : ℕ)
    (z : ℕ → ℝ) : ℝ :=
  Φ ℓ (emPath a b (h₀ / M ^ ℓ) S₀ z)

/-- The coarse level-`ℓ` approximation inside a level-`(ℓ + 1)` sample for the refinement factor
`M` (Giles 2015, §5.1): the same payoff `Φ ℓ` of the Euler–Maruyama path with step
`M h_{ℓ+1}` driven by the block increments `blockAvg M z`, i.e. by the sums of the fine Brownian
increments (`sqrt_mul_blockAvg`). -/
noncomputable def emCoarseM (a b : ℝ → ℝ → ℝ) (h₀ S₀ : ℝ) (M : ℕ) (Φ : ℕ → (ℕ → ℝ) → ℝ)
    (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  Φ ℓ (emPath a b (M * (h₀ / M ^ (ℓ + 1))) S₀ (blockAvg M z))

/-- **The coarse Brownian increments are the sums of the fine ones** (Giles 2015, §5.1, p. 29: "The
multilevel coupling is achieved by using the same underlying driving Brownian path for the coarse
and fine paths; this is accomplished by summing the Brownian increments for the fine path timesteps
to obtain the Brownian increments for the coarse timesteps").  With fine step `h ≥ 0` and coarse
step `M h` (`M ≥ 1`), the coarse increment `√(M h) Z^c_k` is the sum of the fine increments
`√h Z_{Mk+i}`, `i < M`. -/
theorem sqrt_mul_blockAvg {M : ℕ} (hM : 0 < M) {h : ℝ} (hh : 0 ≤ h) (z : ℕ → ℝ) (k : ℕ) :
    Real.sqrt (M * h) * blockAvg M z k = ∑ i ∈ range M, Real.sqrt h * z (M * k + i) := by
  have hM' : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.2 (Nat.cast_pos.2 hM)
  rw [blockAvg, Real.sqrt_mul' _ hh, ← Finset.mul_sum]
  field_simp

/-- **The coarse approximation is the fine approximation of the level below, driven by the block
increments** (Giles 2015, §5.1, p. 29: "the uniform timestep is taken to be `h_ℓ = h₀ M^ℓ`, for
some integer `M`", read `h_ℓ = h₀ M^{−ℓ}`): `P^c_ℓ(z) = P^f_ℓ(blockAvg M z)`, since
`M h_{ℓ+1} = h_ℓ`.  The paper's `h₀ M^ℓ` is a typo for `h₀ M^{−ℓ}` (the step decreases with the
level). -/
theorem emCoarseM_eq (a b : ℝ → ℝ → ℝ) (h₀ S₀ : ℝ) {M : ℕ} (hM : 0 < M)
    (Φ : ℕ → (ℕ → ℝ) → ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    emCoarseM a b h₀ S₀ M Φ ℓ z = emFineM a b h₀ S₀ M Φ ℓ (blockAvg M z) := by
  have e : (M : ℝ) * (h₀ / M ^ (ℓ + 1)) = h₀ / M ^ ℓ := by
    rw [pow_succ]
    field_simp
  unfold emCoarseM emFineM
  rw [e]

/-- **A block of `M` fine increments gives a standard normal coarse increment** (Giles 2015, §5.1,
p. 29: "summing the Brownian increments for the fine path timesteps to obtain the Brownian
increments for the coarse timesteps"): if `Z_0, …, Z_{M−1}` are independent standard normal
variables (`M ≥ 1`), then `(Z_0 + ⋯ + Z_{M−1})/√M` is standard normal. -/
theorem map_blockSum_gaussian {M : ℕ} (hM : 0 < M) :
    (Measure.infinitePi fun _ : Fin M => gaussianReal 0 1).map
      (fun y : Fin M → ℝ => (∑ i, y i) / Real.sqrt M) = gaussianReal 0 1 := by
  have hind : iIndepFun (fun (i : Fin M) (y : Fin M → ℝ) => y i)
      (Measure.infinitePi fun _ : Fin M => gaussianReal 0 1) :=
    iIndepFun_infinitePi (P := fun _ : Fin M => gaussianReal 0 1) (X := fun _ x => x)
      fun _ => measurable_id
  have hlaw : ∀ i : Fin M, HasLaw (fun y : Fin M → ℝ => y i) (gaussianReal 0 1)
      (Measure.infinitePi fun _ : Fin M => gaussianReal 0 1) := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have hsum := hasLaw_finsetSum_gaussianReal (m := fun _ => 0) (v := fun _ => 1) hlaw hind
    Finset.univ
  have hcomp : (fun y : Fin M → ℝ => (∑ i, y i) / Real.sqrt M) =
      (fun x => x / Real.sqrt M) ∘ (fun y : Fin M → ℝ => ∑ i ∈ Finset.univ, y i) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), hsum.map_eq,
    gaussianReal_map_div_const]
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  congr 1
  · simp
  · rw [← NNReal.coe_inj]
    simp [Real.sq_sqrt hM'.le, hM'.ne']

/-- **The coarse increments are again independent standard normal variables** (Giles 2015, §5.1,
p. 29: "this is accomplished by summing the Brownian increments for the fine path timesteps to
obtain the Brownian increments for the coarse timesteps", for a general integer refinement factor
`M ≥ 1`): `z ↦ blockAvg M z` preserves `N(0,1)^{⊗ℕ}`, so the coarse path is driven by independent
Brownian increments of the right variance.  The blocks `(z_{Mk}, …, z_{Mk+M−1})` are independent
(the product measure, reindexed and curried), and each block is mapped to a standard normal
(`map_blockSum_gaussian`). -/
theorem measurePreserving_blockAvg {M : ℕ} (hM : 0 < M) :
    MeasurePreserving (blockAvg M) stdNormalSeq stdNormalSeq := by
  have hf : Function.Injective (fun p : ℕ × Fin M => M * p.1 + (p.2 : ℕ)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    change M * a + (i : ℕ) = M * b + (j : ℕ) at h
    have hi := i.isLt
    have hj := j.isLt
    have h1 : (M * a + (i : ℕ)) / M = (M * b + (j : ℕ)) / M := by rw [h]
    rw [Nat.mul_add_div hM, Nat.mul_add_div hM, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj] at h1
    simp only [add_zero] at h1
    subst h1
    have h2 : (i : ℕ) = j := by omega
    rw [Fin.ext h2]
  -- reindex the coordinates by the blocks `(k, i) ↦ Mk + i`
  have m1 : MeasurePreserving (fun (z : ℕ → ℝ) (p : ℕ × Fin M) => z (M * p.1 + (p.2 : ℕ)))
      stdNormalSeq (Measure.infinitePi fun _ : ℕ × Fin M => gaussianReal 0 1) :=
    ⟨measurable_pi_lambda _ fun p => measurable_pi_apply _,
      Measure.map_infinitePi_infinitePi_of_inj hf⟩
  -- curry: a sequence of independent blocks
  have m2 : MeasurePreserving (MeasurableEquiv.curry ℕ (Fin M) ℝ)
      (Measure.infinitePi fun _ : ℕ × Fin M => gaussianReal 0 1)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin M => gaussianReal 0 1) :=
    ⟨(MeasurableEquiv.curry ℕ (Fin M) ℝ).measurable,
      Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1)⟩
  -- map each block to its normalised sum
  have m3 : MeasurePreserving
      (fun (x : ℕ → Fin M → ℝ) (k : ℕ) => (∑ i, x k i) / Real.sqrt M)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin M => gaussianReal 0 1)
      stdNormalSeq := by
    refine ⟨measurable_pi_lambda _ fun k => ?_, ?_⟩
    · fun_prop
    · refine (Measure.infinitePi_map_pi _
        (f := fun _ (y : Fin M → ℝ) => (∑ i, y i) / Real.sqrt M)
        (fun _ => by fun_prop)).trans ?_
      simp only [map_blockSum_gaussian hM, stdNormalSeq]
  have h := (m3.comp m2).comp m1
  have e : ((fun (x : ℕ → Fin M → ℝ) (k : ℕ) => (∑ i, x k i) / Real.sqrt M) ∘
      (MeasurableEquiv.curry ℕ (Fin M) ℝ)) ∘
      (fun (z : ℕ → ℝ) (p : ℕ × Fin M) => z (M * p.1 + (p.2 : ℕ))) = blockAvg M := by
    funext z k
    simp only [Function.comp_apply, MeasurableEquiv.coe_curry, Function.curry, blockAvg]
    rw [Fin.sum_univ_eq_sum_range (fun i => z (M * k + i)) M]
  rwa [e] at h

/-- For `M = 2` the block increments are the pair increments `pairAvg` of
`MlmcLean/EulerMaruyama.lean`: `(Z_{2k} + Z_{2k+1})/√2`. -/
lemma blockAvg_two : blockAvg 2 = pairAvg := by
  funext z k
  rw [blockAvg, pairAvg, Finset.sum_range_succ, Finset.sum_range_one, add_zero, Nat.cast_ofNat]

/-- For `M = 2` the fine approximation is `emFine` of `MlmcLean/EulerMaruyama.lean` (with
`h₀ = T`). -/
lemma emFineM_two (a b : ℝ → ℝ → ℝ) (T S₀ : ℝ) : emFineM a b T S₀ 2 = emFine a b T S₀ := by
  funext Φ ℓ z
  rw [emFineM, emFine, Nat.cast_ofNat]

/-- For `M = 2` the coarse approximation is `emCoarse` of `MlmcLean/EulerMaruyama.lean`, the
frozen-coefficient coarse path of Haas–Giles 2025, (5), read at the coarse times (`h₀ = T`;
`emCoarsePath_two_mul`). -/
lemma emCoarseM_two (a b : ℝ → ℝ → ℝ) (T S₀ : ℝ) : emCoarseM a b T S₀ 2 = emCoarse a b T S₀ := by
  funext Φ ℓ z
  rw [emCoarseM, emCoarse, blockAvg_two, Nat.cast_ofNat]
  congr 1
  funext k
  rw [emCoarsePath_two_mul]

/-- **The coupling with refinement factor `M` satisfies (2.4)** (Giles 2015, §2.1, (2.4)
"`E[P^f_ℓ] = E[P^c_ℓ]`", and §5.1, p. 29: "the uniform timestep is taken to be `h_ℓ = h₀ M^ℓ`
[read `h₀ M^{−ℓ}`], for some integer `M` … summing the Brownian increments for the fine path
timesteps to obtain the Brownian increments for the coarse timesteps").  With independent standard
normal increments and `M ≥ 1`, the payoff of the coarse path in a level-`(ℓ + 1)` sample has the
same expectation as the payoff of the fine path on level `ℓ`. -/
theorem integral_emCoarseM (a b : ℝ → ℝ → ℝ) (h₀ S₀ : ℝ) {M : ℕ} (hM : 0 < M)
    (Φ : ℕ → (ℕ → ℝ) → ℝ) (ℓ : ℕ)
    (hm : AEStronglyMeasurable (emFineM a b h₀ S₀ M Φ ℓ) stdNormalSeq) :
    ∫ z, emCoarseM a b h₀ S₀ M Φ ℓ z ∂stdNormalSeq =
      ∫ z, emFineM a b h₀ S₀ M Φ ℓ z ∂stdNormalSeq := by
  simp_rw [emCoarseM_eq a b h₀ S₀ hM]
  exact integral_comp_of_measurePreserving (measurePreserving_blockAvg hM) hm

/-- **Theorem 1 for the Euler–Maruyama estimator with refinement factor `M`** (Giles 2015, §2.1,
Theorem 1 with (2.4), and §5.1, p. 29: "On level `ℓ`, the uniform timestep is taken to be
`h_ℓ = h₀ M^ℓ` [read `h₀ M^{−ℓ}`], for some integer `M`.  The timestep `h₀` on the coarsest level is
often taken to be the interval length `T` … but this is not required … The multilevel estimator is
then the natural one defined in (2.2)").  The level-`ℓ` correction is the fine payoff with step
`h_ℓ` minus the coarse payoff with step `M h_ℓ = h_{ℓ−1}` driven by the block sums of the same
normal increments, `Y_ℓ = N_ℓ⁻¹ ∑_n (P^f_ℓ − P^c_{ℓ−1})(ω^{(ℓ,n)})`, with the samples `ω^{(ℓ,n)}`
independent with law `N(0,1)^{⊗ℕ}`.  Condition (2.4) holds (`integral_emCoarseM`), so under (i)
for `P^f_ℓ`, (iii) for `V_ℓ = V[P^f_ℓ − P^c_{ℓ−1}]` and (iv) with `α ≥ ½ min(β, γ)`, there is
`c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with a square-integrable
error, `MSE < ε²` and `E[C] ≤ c₄ · bound(ε)`.  The rates are in base `2` as in Theorem 1 (a rate
`r` in `h_ℓ` is the rate `r log₂ M` in `ℓ`).  For `M = 2` and `h₀ = T` the fine and coarse
approximations are those of `em_mlmc_theorem1` (`emFineM_two`, `emCoarseM_two`), so this
generalises it. -/
theorem em_mlmc_theorem1_M {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (a b : ℝ → ℝ → ℝ) (h₀ S₀ : ℝ) {M : ℕ} (hM : 0 < M)
    (Φ : ℕ → (ℕ → ℝ) → ℝ) (P : (ℕ → ℝ) → ℝ)
    (ω : ℕ × ℕ → Ω → ℕ → ℝ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ stdNormalSeq) (hind : iIndepFun ω μ)
    (hP : Integrable P stdNormalSeq) (hPfm : ∀ ℓ, Measurable (emFineM a b h₀ S₀ M Φ ℓ))
    (hPf : ∀ ℓ, MemLp (emFineM a b h₀ S₀ M Φ ℓ) 2 stdNormalSeq)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
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
        μ[fun x => (∑ ℓ ∈ range (L + 1),
          blockMean (fineCoarseDiff (emFineM a b h₀ S₀ M Φ) (emCoarseM a b h₀ S₀ M Φ)) ω ℓ
            (N ℓ) x - ∫ z, P z ∂stdNormalSeq) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * complexityBound α β γ ε := by
  have hc : ∀ ℓ, emCoarseM a b h₀ S₀ M Φ ℓ = emFineM a b h₀ S₀ M Φ ℓ ∘ blockAvg M := fun ℓ =>
    funext (emCoarseM_eq a b h₀ S₀ hM Φ ℓ)
  have hPcm : ∀ ℓ, Measurable (emCoarseM a b h₀ S₀ M Φ ℓ) := fun ℓ => by
    rw [hc]
    exact (hPfm ℓ).comp (measurePreserving_blockAvg hM).measurable
  have hPc : ∀ ℓ, MemLp (emCoarseM a b h₀ S₀ M Φ ℓ) 2 stdNormalSeq := fun ℓ => by
    rw [hc]
    exact (hPf ℓ).comp_measurePreserving (measurePreserving_blockAvg hM)
  obtain ⟨c₄, hc₄, H⟩ := giles_theorem1_fineCoarse P (emFineM a b h₀ S₀ M Φ)
    (emCoarseM a b h₀ S₀ M Φ) ω cost C hα hβ hγ hc₁ hc₂ hc₃ hαβγ hω hind hP hPfm hPcm hPf hPc
    (fun ℓ => (integral_emCoarseM a b h₀ S₀ hM Φ ℓ (hPfm ℓ).aestronglyMeasurable).symm)
    hcost hcostC h_i h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hC⟩ := H ε hε hε1
  have hD := memLp_fineCoarseDiff hPf hPc
  refine ⟨L, N, hN, ?_, hmse, hC⟩
  exact ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω hD ℓ (N ℓ)).sub
    (memLp_const _)).integrable_sq

end RefinementFactor

end MLMC
