import MlmcLean.Complexity
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Two simple PDE examples (Giles 2015, §7.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §7.1 "Two
simple examples" (pp. 49–51).

**The elliptic example** (p. 49): "Level `ℓ` uses a uniform grid with spacing `h_ℓ = 2^{−(ℓ+1)}`
… The uniform second order accuracy means that there is a constant `K` such that
`|P − P_ℓ| < K h_ℓ²` and therefore we have `α = 2`, `β = 4` and `γ = 1`, resulting in an `O(ε⁻²)`
complexity."

**The parabolic example** (p. 51): "`u^{n+1}_j = u^n_j + k/h² (u^n_{j+1} − 2u^n_j + u^n_{j−1})
+ 10 ΔW_n`.  The level `ℓ` approximation uses `h_ℓ = 2^{−(ℓ+1)}`, `k_ℓ = ¼ h_ℓ²`.  Keeping
`k_ℓ/h_ℓ² = ¼` ensures the explicit numerical discretisation is stable on all levels.  Since the
number of grid points doubles on each level, and the number of timesteps increases by factor 4, the
cost per sample increases by factor 8, giving `γ = 3`.  Because the stochastic forcing is additive,
i.e. the volatility does not depend on `u(x, t)`, the Euler-Maruyama discretisation is actually
equivalent to a Milstein discretisation … the solution error is `O(2^{−2ℓ})` and hence `α = 2` and
`β = 4`.  This leads to the optimal complexity of `O(ε⁻²)`."

* `rates_of_pathwise`: a pathwise error `|P − P_ℓ| ≤ K 2^{−pℓ}` gives the weak rate `α = p` and
  the variance rate `β = 2p`: `V[P_{ℓ+1} − P_ℓ] ≤ (1 + 2^p)² K² 2^{−2p(ℓ+1)}`;
  `elliptic_rates`: with `|P − P_ℓ| ≤ K h_ℓ²`, `h_ℓ = 2^{−(ℓ+1)}`, this is `α = 2`, `β = 4`.
* `abs_heatStep_le`, `heatStep_sub`: for `λ = k/h² ≤ ½` the explicit scheme satisfies the discrete
  maximum principle, so the difference of two solutions driven by the same (additive) noise does
  not grow; `heatStep_alternating`: for `λ > ½` the mode `(−1)^j` grows by `|1 − 4λ| > 1` per step.
  With `λ = ¼` the scheme is stable on all levels.
* `parabolic_cost`: grid points times timesteps is `32 T 2^{3ℓ}`, so `γ = 3`.
* `milsteinStep_eq_emStep`: with a volatility that does not depend on the state, the Milstein
  correction `½ b ∂b/∂S (ΔW² − h)` vanishes and the Milstein step is the Euler–Maruyama step.
* `pde_complexity`: `(α, β, γ) = (2, 4, 1)` and `(2, 4, 3)` both give `O(ε⁻²)` in Theorem 1.
-/

open MeasureTheory ProbabilityTheory

namespace MLMC

/-! ### Pathwise errors give the weak and variance rates -/

section rates

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Giles 2015, §7.1: pathwise accuracy gives `α` and `β = 2α`.**  If `|P − P_ℓ| ≤ K 2^{−pℓ}`
everywhere, with the `P_ℓ` integrable, then `|E[P_ℓ − P]| ≤ K 2^{−pℓ}` (condition (i) of
Theorem 1 with `α = p`) and `V[P_{ℓ+1} − P_ℓ] ≤ (1 + 2^p)² K² 2^{−2p(ℓ+1)}` (condition (iii)
with `β = 2p`). -/
theorem rates_of_pathwise {P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {K p : ℝ}
    (hPl : ∀ ℓ, Integrable (Pl ℓ) μ)
    (herr : ∀ ℓ ω, |P ω - Pl ℓ ω| ≤ K * (2 : ℝ) ^ (-(p * (ℓ : ℝ)))) :
    (∀ ℓ : ℕ, |∫ ω, (Pl ℓ ω - P ω) ∂μ| ≤ K * (2 : ℝ) ^ (-(p * (ℓ : ℝ)))) ∧
    (∀ ℓ : ℕ, variance (fun ω => Pl (ℓ + 1) ω - Pl ℓ ω) μ ≤
      (1 + (2 : ℝ) ^ p) ^ 2 * K ^ 2 * (2 : ℝ) ^ (-(2 * p * ((ℓ : ℝ) + 1)))) := by
  refine ⟨fun ℓ => ?_, fun ℓ => ?_⟩
  · calc |∫ ω, (Pl ℓ ω - P ω) ∂μ| ≤ ∫ ω, |Pl ℓ ω - P ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ω, K * (2 : ℝ) ^ (-(p * (ℓ : ℝ))) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
            (integrable_const _)
            (Filter.Eventually.of_forall fun ω => (abs_sub_comm _ _).trans_le (herr ℓ ω))
      _ = K * (2 : ℝ) ^ (-(p * (ℓ : ℝ))) := by
          rw [integral_const, probReal_univ, one_smul]
  · have h2 : (0 : ℝ) < 2 := two_pos
    have hsplit : (2 : ℝ) ^ (-(p * (ℓ : ℝ))) = (2 : ℝ) ^ p * (2 : ℝ) ^ (-(p * ((ℓ : ℝ) + 1))) := by
      rw [← Real.rpow_add h2]
      congr 1
      ring
    have hsq : (2 : ℝ) ^ (-(2 * p * ((ℓ : ℝ) + 1))) = ((2 : ℝ) ^ (-(p * ((ℓ : ℝ) + 1)))) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le]
      congr 1
      push_cast
      ring
    have hpt : ∀ ω, (Pl (ℓ + 1) ω - Pl ℓ ω) ^ 2 ≤
        (1 + (2 : ℝ) ^ p) ^ 2 * K ^ 2 * (2 : ℝ) ^ (-(2 * p * ((ℓ : ℝ) + 1))) := by
      intro ω
      have h1 := herr (ℓ + 1) ω
      have h0 := herr ℓ ω
      push_cast at h1
      have hb : |Pl (ℓ + 1) ω - Pl ℓ ω| ≤
          (1 + (2 : ℝ) ^ p) * (K * (2 : ℝ) ^ (-(p * ((ℓ : ℝ) + 1)))) := by
        calc |Pl (ℓ + 1) ω - Pl ℓ ω| ≤ |P ω - Pl (ℓ + 1) ω| + |P ω - Pl ℓ ω| := by
              rw [show Pl (ℓ + 1) ω - Pl ℓ ω = (P ω - Pl ℓ ω) - (P ω - Pl (ℓ + 1) ω) by ring]
              exact (abs_sub _ _).trans_eq (add_comm _ _)
          _ ≤ K * (2 : ℝ) ^ (-(p * ((ℓ : ℝ) + 1))) + K * (2 : ℝ) ^ (-(p * (ℓ : ℝ))) :=
              add_le_add h1 h0
          _ = (1 + (2 : ℝ) ^ p) * (K * (2 : ℝ) ^ (-(p * ((ℓ : ℝ) + 1)))) := by
              rw [hsplit]
              ring
      rw [hsq, ← sq_abs]
      calc |Pl (ℓ + 1) ω - Pl ℓ ω| ^ 2
          ≤ ((1 + (2 : ℝ) ^ p) * (K * (2 : ℝ) ^ (-(p * ((ℓ : ℝ) + 1))))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = (1 + (2 : ℝ) ^ p) ^ 2 * K ^ 2 * ((2 : ℝ) ^ (-(p * ((ℓ : ℝ) + 1)))) ^ 2 := by ring
    have hm : AEStronglyMeasurable (fun ω => Pl (ℓ + 1) ω - Pl ℓ ω) μ :=
      ((hPl (ℓ + 1)).sub (hPl ℓ)).aestronglyMeasurable
    calc variance (fun ω => Pl (ℓ + 1) ω - Pl ℓ ω) μ
        ≤ ∫ ω, (Pl (ℓ + 1) ω - Pl ℓ ω) ^ 2 ∂μ := variance_le_expectation_sq hm
      _ ≤ ∫ _ω, (1 + (2 : ℝ) ^ p) ^ 2 * K ^ 2 * (2 : ℝ) ^ (-(2 * p * ((ℓ : ℝ) + 1))) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hpt)
      _ = (1 + (2 : ℝ) ^ p) ^ 2 * K ^ 2 * (2 : ℝ) ^ (-(2 * p * ((ℓ : ℝ) + 1))) := by
          rw [integral_const, probReal_univ, one_smul]

/-- **Giles 2015, §7.1, the elliptic example: "`|P − P_ℓ| < K h_ℓ²` and therefore we have `α = 2`,
`β = 4`"**, with `h_ℓ = 2^{−(ℓ+1)}`: `|E[P_ℓ − P]| ≤ (K/4) 2^{−2ℓ}` and
`V[P_{ℓ+1} − P_ℓ] ≤ (25/16) K² 2^{−4(ℓ+1)}`. -/
theorem elliptic_rates {P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {K : ℝ}
    (hPl : ∀ ℓ, Integrable (Pl ℓ) μ)
    (herr : ∀ (ℓ : ℕ) ω, |P ω - Pl ℓ ω| ≤ K * ((2 : ℝ) ^ (-((ℓ : ℝ) + 1))) ^ 2) :
    (∀ ℓ : ℕ, |∫ ω, (Pl ℓ ω - P ω) ∂μ| ≤ K / 4 * (2 : ℝ) ^ (-(2 * (ℓ : ℝ)))) ∧
    (∀ ℓ : ℕ, variance (fun ω => Pl (ℓ + 1) ω - Pl ℓ ω) μ ≤
      25 / 16 * K ^ 2 * (2 : ℝ) ^ (-(4 * ((ℓ : ℝ) + 1)))) := by
  have hh : ∀ ℓ : ℕ, K * ((2 : ℝ) ^ (-((ℓ : ℝ) + 1))) ^ 2 = K / 4 * (2 : ℝ) ^ (-(2 * (ℓ : ℝ))) := by
    intro ℓ
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show -((ℓ : ℝ) + 1) * ((2 : ℕ) : ℝ) = -(2 * (ℓ : ℝ)) + -2 by push_cast; ring,
      Real.rpow_add (by norm_num),
      show (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 by rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num]
    ring
  have h := rates_of_pathwise (p := 2) hPl fun ℓ ω => (herr ℓ ω).trans_eq (hh ℓ)
  refine ⟨h.1, fun ℓ => (h.2 ℓ).trans_eq ?_⟩
  rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by rw [Real.rpow_two]; norm_num,
    show 2 * (2 : ℝ) * ((ℓ : ℝ) + 1) = 4 * ((ℓ : ℝ) + 1) by ring]
  ring

end rates

/-! ### The explicit scheme for the heat equation -/

/-- One step of the explicit scheme of Giles 2015, §7.1, without the noise:
`u_j + λ (u_{j+1} − 2u_j + u_{j−1})` with `λ = k/h²`. -/
def heatStep (lam : ℝ) (u : ℤ → ℝ) (j : ℤ) : ℝ := u j + lam * (u (j + 1) - 2 * u j + u (j - 1))

/-- **The discrete maximum principle** (Giles 2015, §7.1: "Keeping `k_ℓ/h_ℓ² = ¼` ensures the
explicit numerical discretisation is stable on all levels"): for `0 ≤ λ ≤ ½` the explicit step is
a convex combination `λ u_{j−1} + (1 − 2λ) u_j + λ u_{j+1}`, so it does not increase the maximum
norm. -/
theorem abs_heatStep_le {lam M : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1 / 2) {u : ℤ → ℝ}
    (hu : ∀ j, |u j| ≤ M) (j : ℤ) : |heatStep lam u j| ≤ M := by
  have e : heatStep lam u j = lam * u (j - 1) + (1 - 2 * lam) * u j + lam * u (j + 1) := by
    unfold heatStep
    ring
  rw [e]
  have h2 : 0 ≤ 1 - 2 * lam := by linarith
  calc |lam * u (j - 1) + (1 - 2 * lam) * u j + lam * u (j + 1)|
      ≤ |lam * u (j - 1)| + |(1 - 2 * lam) * u j| + |lam * u (j + 1)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = lam * |u (j - 1)| + (1 - 2 * lam) * |u j| + lam * |u (j + 1)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h2]
    _ ≤ lam * M + (1 - 2 * lam) * M + lam * M :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hu _) h0)
          (mul_le_mul_of_nonneg_left (hu _) h2)) (mul_le_mul_of_nonneg_left (hu _) h0)
    _ = M := by ring

/-- The explicit step is linear, so with an additive noise `w` the difference of two solutions
driven by the same noise follows the noise-free step: `(S u + w) − (S v + w) = S (u − v)`. -/
theorem heatStep_sub (lam : ℝ) (u v : ℤ → ℝ) (w : ℤ → ℝ) (j : ℤ) :
    (heatStep lam u j + w j) - (heatStep lam v j + w j) = heatStep lam (u - v) j := by
  unfold heatStep
  simp only [Pi.sub_apply]
  ring

/-- **Instability for `λ > ½`** (Giles 2015, §7.1): the explicit step multiplies the alternating
mode `(−1)^j` by `1 − 4λ`, and `|1 − 4λ| > 1` when `λ > ½`. -/
theorem heatStep_alternating (lam : ℝ) (j : ℤ) :
    heatStep lam (fun i => (-1 : ℝ) ^ i) j = (1 - 4 * lam) * (-1 : ℝ) ^ j := by
  have h1 : (-1 : ℝ) ≠ 0 := by norm_num
  simp only [heatStep]
  rw [zpow_add₀ h1, zpow_sub₀ h1, zpow_one, div_neg, div_one]
  ring

lemma one_lt_abs_one_sub_four_mul {lam : ℝ} (h : 1 / 2 < lam) : 1 < |1 - 4 * lam| := by
  rw [abs_of_neg (by linarith)]
  linarith

/-- **The parabolic example is stable on all levels** (Giles 2015, §7.1): with
`h_ℓ = 2^{−(ℓ+1)}` and `k_ℓ = ¼ h_ℓ²` the ratio `λ = k_ℓ/h_ℓ² = ¼` lies in `[0, ½]`. -/
theorem parabolic_ratio (ℓ : ℕ) :
    ((2 : ℝ) ^ (-((ℓ : ℝ) + 1))) ^ 2 / 4 / ((2 : ℝ) ^ (-((ℓ : ℝ) + 1))) ^ 2 = 1 / 4 := by
  have h : ((2 : ℝ) ^ (-((ℓ : ℝ) + 1))) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Real.rpow_pos_of_pos two_pos _).ne'
  rw [div_right_comm, div_self h]

/-- **The cost of the parabolic example grows by the factor 8** (Giles 2015, §7.1: "Since the
number of grid points doubles on each level, and the number of timesteps increases by factor 4, the
cost per sample increases by factor 8, giving `γ = 3`"): with `h_ℓ = 2^{−(ℓ+1)}` and
`k_ℓ = ¼ h_ℓ²`, the number of grid intervals `1/h_ℓ` times the number of timesteps `T/k_ℓ` is
`32 T 2^{3ℓ}`. -/
theorem parabolic_cost (T : ℝ) (ℓ : ℕ) :
    ((2 : ℝ) ^ (-((ℓ : ℝ) + 1)))⁻¹ * (T / (((2 : ℝ) ^ (-((ℓ : ℝ) + 1))) ^ 2 / 4)) =
      32 * T * (2 : ℝ) ^ (3 * (ℓ : ℝ)) := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have hx : (2 : ℝ) ^ (-((ℓ : ℝ) + 1)) = ((2 : ℝ) ^ ((ℓ : ℝ) + 1))⁻¹ := Real.rpow_neg h2.le _
  have h3 : (2 : ℝ) ^ (3 * (ℓ : ℝ)) = ((2 : ℝ) ^ (ℓ : ℝ)) ^ 3 := by
    rw [mul_comm, Real.rpow_mul h2.le, Real.rpow_ofNat]
  have h1 : (2 : ℝ) ^ ((ℓ : ℝ) + 1) = 2 * (2 : ℝ) ^ (ℓ : ℝ) := by
    rw [Real.rpow_add h2, Real.rpow_one, mul_comm]
  rw [hx, h3, h1, inv_inv, div_div_eq_mul_div, inv_pow, div_inv_eq_mul]
  ring

/-! ### Additive noise: Euler–Maruyama is Milstein -/

/-- The Euler–Maruyama step `S + a(S) h + b(S) ΔW`. -/
def emStep (a b : ℝ → ℝ) (h S dW : ℝ) : ℝ := S + a S * h + b S * dW

/-- The Milstein step of Giles 2015, §5.2: `S + a(S) h + b(S) ΔW + ½ b(S) ∂b/∂S(S) (ΔW² − h)`. -/
noncomputable def milsteinStep (a b : ℝ → ℝ) (h S dW : ℝ) : ℝ :=
  S + a S * h + b S * dW + 1 / 2 * b S * deriv b S * (dW ^ 2 - h)

/-- **Giles 2015, §7.1: "Because the stochastic forcing is additive, i.e. the volatility does not
depend on `u(x, t)`, the Euler-Maruyama discretisation is actually equivalent to a Milstein
discretisation"**: with a constant volatility `b = σ` the Milstein correction vanishes. -/
theorem milsteinStep_eq_emStep (a : ℝ → ℝ) (σ h S dW : ℝ) :
    milsteinStep a (fun _ => σ) h S dW = emStep a (fun _ => σ) h S dW := by
  simp [milsteinStep, emStep, deriv_const]

/-! ### The complexity -/

/-- **Giles 2015, §7.1: both examples have the optimal complexity `O(ε⁻²)`**:
`(α, β, γ) = (2, 4, 1)` (elliptic) and `(2, 4, 3)` (parabolic) have `β > γ`, so Theorem 1 gives
`ε⁻²`. -/
theorem pde_complexity (ε : ℝ) :
    complexityBound 2 4 1 ε = ε ^ (-2 : ℝ) ∧ complexityBound 2 4 3 ε = ε ^ (-2 : ℝ) :=
  ⟨complexityBound_of_lt (by norm_num) ε, complexityBound_of_lt (by norm_num) ε⟩

end MLMC
