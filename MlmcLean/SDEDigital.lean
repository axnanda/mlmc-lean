import MlmcLean.GBMEulerMaruyama
import Mathlib.Probability.CDF
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Lipschitz and digital payoffs, payoff smoothing and change of measure (Giles 2015, §5.1–§5.4)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1
"Euler-Maruyama discretisation" (pp. 29–33), §5.2 "Milstein discretisation", paragraph "Digital
options" (pp. 35–38), and §5.4 "Computing sensitivities" (p. 42).  As in `MlmcLean.SDEExtras`, the
SDE theory (the strong and weak convergence of the discretisations) is not formalised; this file
proves the probabilistic and analytic steps that these sections rely on.

* **§5.1, Lipschitz payoffs.**  `lipschitz_european_asian_lookback`: the European call
  `max(x_n − K, 0)`, the Asian call `max(x̄ − K, 0)` on the average `x̄ = (n + 1)⁻¹ ∑_i x_i` and the
  lookback payoffs `max(max_i x_i − K, 0)`, `x_n − min_i x_i`, `max_i x_i − x_n` are Lipschitz for
  the sup norm on discrete paths `(x_0, …, x_n)`; `variance_lipschitz_payoff_le`: for a
  `K`-Lipschitz path functional, `V[P − P_ℓ] ≤ E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`.
* **§5.1–§5.2, digital options: the paths on either side of the strike.**  `digital_mismatch_le`:
  if the law of `X` has density at most `ρ` near the strike `K`, then
  `P(1_{X>K} ≠ 1_{Y>K}) ≤ 2ρδ + P(|X − Y| > δ)` for every `δ > 0`, hence
  `≤ 2ρδ + E[(X − Y)²]/δ²` and `≤ 3ρ^{2/3} E[(X − Y)²]^{1/3}` (an inequality of Avikainen's type,
  for `p = 2`).  `variance_digital_le`, `variance_digital_levelDiff_le`: the variance of the digital
  correction is at most this fraction; `variance_digital_rate`: a mean-square strong error
  `E[(X − Y_ℓ)²] ≤ c h_ℓ` gives `V_ℓ = O(h_ℓ^{1/3})`; `digital_mismatch_le_of_moment`: a `p`-th
  moment bound `E|X − Y|^p ≤ c h^{p/2}` gives `O(h^{p/(2(p+1))})`; `digital_mismatch_le_of_tail`:
  Gaussian-type tails of the error give `O((h log(1/h))^{1/2})`; `gbm_digital_variance_le`: for
  geometric Brownian motion with the Euler–Maruyama estimator, `V_ℓ = O(h_ℓ^{1/3})` with explicit
  constants.  The paper's `V_ℓ = O(h_ℓ^{1/2})` is the observed rate; `digital_mismatch_le` explains
  the difference.
* **§5.2, conditional expectation.**  `integral_digital_final_step`:
  `E[1_{x + ah + b√h Z > K}] = Φ((x + ah − K)/(|b|√h))` for `Z ∼ N(0,1)`;
  `condExp_digital_last_step`, `digital_smoothing`: given the path before the last step, the
  conditional expectation of the digital payoff is `Φ((Ŝ_{N−1} + a h − K)/(|b| √h))`, which has the
  mean of the digital payoff (so the telescoping identity (2.4) is kept) and no larger variance;
  `digital_smoothing_coarse`: the coarse-path formula (with a typo of the paper corrected);
  `digital_smoothing_level_zero`: with one timestep on level `0` the smoothed payoff is
  deterministic, `V_0 = 0`.
* **§5.2, change of measure.**  `gaussian_change_of_measure`:
  `dN(m', v')/dN(m, v) = φ_{m',v'}/φ_{m,v}`; `integral_mul_likelihoodRatio`,
  `integral_mul_sub_likelihoodRatio`: a sample of a third Gaussian weighted by the Radon–Nikodym
  derivative keeps the expectation, and the fine–coarse difference is the difference of the
  Radon–Nikodym derivatives.
* **§5.4.**  `hasDerivAt_call_payoff`: the derivative of the call payoff `max(x − K, 0)` is the
  Heaviside function `H(x − K)`, which is discontinuous at `K`.

`Φ` is the standard normal distribution function `cdf (gaussianReal 0 1)`, and the digital payoff
`H(x − K)` is `(Set.Ioi K).indicator 1 x` (so `H(0) = 0`; the value at the strike does not matter
when the law has a density).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MLMC

/-! ### §5.1: Lipschitz payoffs -/

/-- The call payoff `x ↦ max(x − K, 0)` is `1`-Lipschitz (Giles 2015, §5.1). -/
lemma lipschitzWith_callPayoff (K : ℝ) : LipschitzWith 1 (fun x : ℝ => max (x - K) 0) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  calc |max (x - K) 0 - max (y - K) 0| ≤ |(x - K) - (y - K)| := abs_max_sub_max_le_abs _ _ _
    _ = |x - y| := by rw [sub_sub_sub_cancel_right]

/-- The average `(n + 1)⁻¹ ∑_{i ≤ n} x_i` of a path `(x_0, …, x_n)` is `1`-Lipschitz for the sup
norm (the Asian option of Giles 2015, §5.1). -/
lemma lipschitzWith_pathAverage (n : ℕ) :
    LipschitzWith 1 (fun x : Fin (n + 1) → ℝ => (∑ i, x i) / (n + 1)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [Real.dist_eq, NNReal.coe_one, one_mul, ← sub_div, ← Finset.sum_sub_distrib, abs_div,
    abs_of_pos hn, div_le_iff₀ hn]
  calc |∑ i, (x i - y i)| ≤ ∑ i, |x i - y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (n + 1), dist x y := Finset.sum_le_sum fun i _ => by
        rw [← Real.dist_eq]
        exact dist_le_pi_dist x y i
    _ = dist x y * (n + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
        push_cast
        ring

/-- The maximum `max_i x_i` of a path is `1`-Lipschitz for the sup norm (the lookback option of
Giles 2015, §5.1). -/
lemma lipschitzWith_pathMax (n : ℕ) :
    LipschitzWith 1 (fun x : Fin (n + 1) → ℝ => Finset.univ.sup' Finset.univ_nonempty x) := by
  have h : ∀ x y : Fin (n + 1) → ℝ, Finset.univ.sup' Finset.univ_nonempty x ≤
      Finset.univ.sup' Finset.univ_nonempty y + dist x y := by
    intro x y
    refine Finset.sup'_le _ _ fun i _ => ?_
    have h1 : x i - y i ≤ dist x y :=
      (le_abs_self _).trans (by rw [← Real.dist_eq]; exact dist_le_pi_dist x y i)
    have h2 : y i ≤ Finset.univ.sup' Finset.univ_nonempty y := Finset.le_sup' y (Finset.mem_univ i)
    linarith
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  have h1 := h x y
  have h2 := h y x
  rw [dist_comm] at h2
  constructor <;> linarith

/-- The minimum `min_i x_i` of a path is `1`-Lipschitz for the sup norm (the lookback option of
Giles 2015, §5.1). -/
lemma lipschitzWith_pathMin (n : ℕ) :
    LipschitzWith 1 (fun x : Fin (n + 1) → ℝ => Finset.univ.inf' Finset.univ_nonempty x) := by
  have h : ∀ x y : Fin (n + 1) → ℝ, Finset.univ.inf' Finset.univ_nonempty y - dist x y ≤
      Finset.univ.inf' Finset.univ_nonempty x := by
    intro x y
    refine Finset.le_inf' _ _ fun i _ => ?_
    have h1 : y i - x i ≤ dist x y :=
      (le_abs_self _).trans (by rw [← Real.dist_eq, dist_comm]; exact dist_le_pi_dist x y i)
    have h2 : Finset.univ.inf' Finset.univ_nonempty y ≤ y i := Finset.inf'_le y (Finset.mem_univ i)
    linarith
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  have h1 := h x y
  have h2 := h y x
  rw [dist_comm] at h2
  constructor <;> linarith

/-- **European, Asian and lookback payoffs are Lipschitz** (Giles 2015, §5.1, p. 29: "For
Lipschitz payoff functions `P` (such as European, Asian and lookback options in finance) for which
`|P(S₁) − P(S₂)| ≤ K‖S₁ − S₂‖`, we have …"; p. 33: "the Asian option is based on the average value
of the underlying asset, the lookback is based on its maximum or minimum value").  On discrete
paths `x = (x_0, …, x_n)` with the sup norm `‖x‖ = max_i |x_i|`, the European call
`max(x_n − K, 0)`, the Asian call `max((n + 1)⁻¹ ∑_i x_i − K, 0)` and the fixed-strike lookback call
`max(max_i x_i − K, 0)` are `1`-Lipschitz, and the floating-strike lookback call `x_n − min_i x_i`
and put `max_i x_i − x_n` are `2`-Lipschitz.  (The discount factor `e^{−rT}` of the paper multiplies
the constants by `e^{−rT}`.) -/
theorem lipschitz_european_asian_lookback (n : ℕ) (K : ℝ) :
    LipschitzWith 1 (fun x : Fin (n + 1) → ℝ => max (x (Fin.last n) - K) 0) ∧
      LipschitzWith 1 (fun x : Fin (n + 1) → ℝ => max ((∑ i, x i) / (n + 1) - K) 0) ∧
      LipschitzWith 1
        (fun x : Fin (n + 1) → ℝ => max (Finset.univ.sup' Finset.univ_nonempty x - K) 0) ∧
      LipschitzWith 2
        (fun x : Fin (n + 1) → ℝ => x (Fin.last n) - Finset.univ.inf' Finset.univ_nonempty x) ∧
      LipschitzWith 2
        (fun x : Fin (n + 1) → ℝ => Finset.univ.sup' Finset.univ_nonempty x - x (Fin.last n)) := by
  have hc := lipschitzWith_callPayoff K
  have he : LipschitzWith 1 (fun x : Fin (n + 1) → ℝ => x (Fin.last n)) :=
    LipschitzWith.eval (Fin.last n)
  have h2 : (1 : ℝ≥0) + 1 = 2 := one_add_one_eq_two
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Function.comp_def] using hc.comp he
  · simpa [Function.comp_def] using hc.comp (lipschitzWith_pathAverage n)
  · simpa [Function.comp_def] using hc.comp (lipschitzWith_pathMax n)
  · simpa [h2] using he.sub (lipschitzWith_pathMin n)
  · simpa [h2] using (lipschitzWith_pathMax n).sub he

section Lipschitz

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Lipschitz payoffs of paths** (Giles 2015, §5.1, p. 29: "For Lipschitz payoff functions `P`
… for which `|P(S₁) − P(S₂)| ≤ K‖S₁ − S₂‖`, we have
`V[P − P_ℓ] ≤ E[(P − P_ℓ)²] ≤ K² E[‖S − Ŝ_ℓ‖²]`").  For a `K`-Lipschitz functional `g` on a normed
space of paths `E` (for instance `Fin (n + 1) → ℝ` with the sup norm, see
`lipschitz_european_asian_lookback`) and random paths `S`, `Ŝ_ℓ` with `E[‖S − Ŝ_ℓ‖²] < ∞`,
`V[g(S) − g(Ŝ_ℓ)] ≤ E[(g(S) − g(Ŝ_ℓ))²] ≤ K² E[‖S − Ŝ_ℓ‖²]`. -/
theorem variance_lipschitz_payoff_le {E : Type*} [SeminormedAddCommGroup E] {g : E → ℝ}
    {L : ℝ≥0} (hg : LipschitzWith L g) {S Sl : Ω → E} (hS : AEStronglyMeasurable S μ)
    (hSl : AEStronglyMeasurable Sl μ) (hD : Integrable (fun ω => ‖S ω - Sl ω‖ ^ 2) μ) :
    variance (fun ω => g (S ω) - g (Sl ω)) μ ≤ ∫ ω, (g (S ω) - g (Sl ω)) ^ 2 ∂μ ∧
      ∫ ω, (g (S ω) - g (Sl ω)) ^ 2 ∂μ ≤ (L : ℝ) ^ 2 * ∫ ω, ‖S ω - Sl ω‖ ^ 2 ∂μ :=
  variance_sub_le_of_lipschitz ((hg.continuous.comp_aestronglyMeasurable hS).sub
    (hg.continuous.comp_aestronglyMeasurable hSl)) hD fun ω => by
      rw [← Real.dist_eq, ← dist_eq_norm]
      exact hg.dist_le_mul _ _

end Lipschitz

/-! ### §5.1–§5.2: digital options, the paths on either side of the strike -/

section Digital

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace Ω] in
/-- If the digital payoffs `1_{X>K}` and `1_{Y>K}` differ, then `K` lies between `X` and `Y`, so
`|X − K| ≤ |X − Y|`: either `|X − K| ≤ δ` or `|X − Y| > δ` (Giles 2015, §5.1, p. 33). -/
lemma digital_ne_subset (X Y : Ω → ℝ) (K δ : ℝ) :
    {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ⊆
      {ω | |X ω - K| ≤ δ} ∪ {ω | δ < |X ω - Y ω|} := by
  intro ω hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_lt] at hcon hω
  obtain ⟨h1, h2⟩ := hcon
  apply hω
  have h3 := le_abs_self (X ω - Y ω)
  have h4 := neg_abs_le (X ω - Y ω)
  rcases le_or_gt (X ω) K with hX | hX
  · rw [abs_of_nonpos (by linarith)] at h1
    rw [Set.indicator_of_notMem (by simpa using hX),
      Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; linarith)]
  · rw [abs_of_pos (by linarith)] at h1
    rw [Set.indicator_of_mem (by simpa using hX),
      Set.indicator_of_mem (by simp only [Set.mem_Ioi]; linarith)]
    rfl

/-- The fraction of samples on either side of the strike is at most
`P(|X − K| ≤ δ) + P(|X − Y| > δ)`, for every `δ` (Giles 2015, §5.1, p. 33). -/
lemma measureReal_digital_ne_le [IsFiniteMeasure μ] (X Y : Ω → ℝ) (K δ : ℝ) :
    μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
      μ.real {ω | |X ω - K| ≤ δ} + μ.real {ω | δ < |X ω - Y ω|} :=
  (measureReal_mono (digital_ne_subset X Y K δ)).trans (measureReal_union_le _ _)

/-- Chebyshev's inequality: `P(|X − Y| > δ) ≤ E[(X − Y)²]/δ²` for `δ > 0`. -/
lemma measureReal_lt_abs_sub_le_div_sq [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hint : Integrable (fun ω => (X ω - Y ω) ^ 2) μ) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | δ < |X ω - Y ω|} ≤ (∫ ω, (X ω - Y ω) ^ 2 ∂μ) / δ ^ 2 := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => sq_nonneg (X ω - Y ω)) hint (δ ^ 2)
  rw [le_div_iff₀ (by positivity), mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono fun ω hω => ?_) (by positivity)) h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have := pow_le_pow_left₀ hδ.le hω.le 2
  rwa [sq_abs] at this

/-- A density bound gives the small-ball bound at the strike: if `P(X ∈ A) ≤ ρ vol(A)` for every
Borel set `A` (`μ.map X ≤ ρ • volume`), then `P(|X − K| ≤ δ) ≤ 2ρδ` (Giles 2015, §5.1, p. 33: "a
bounded density of paths terminating in the neighbourhood of `K`"). -/
lemma measureReal_abs_sub_le_of_map_le [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hmap : μ.map X ≤ ENNReal.ofReal ρ • volume) (K : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) : μ.real {ω | |X ω - K| ≤ δ} ≤ 2 * ρ * δ := by
  have e : {ω | |X ω - K| ≤ δ} = X ⁻¹' Set.Icc (K - δ) (K + δ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have h := Measure.le_iff.1 hmap _ (measurableSet_Icc (a := K - δ) (b := K + δ))
  rw [Measure.map_apply hX measurableSet_Icc, Measure.smul_apply, Real.volume_Icc, smul_eq_mul,
    ← ENNReal.ofReal_mul hρ] at h
  rw [e, measureReal_def]
  calc _ ≤ (ENNReal.ofReal (ρ * (K + δ - (K - δ)))).toReal := ENNReal.toReal_mono
        ENNReal.ofReal_ne_top h
    _ = 2 * ρ * δ := by
        rw [ENNReal.toReal_ofReal (mul_nonneg hρ (by linarith))]
        ring

/-- If `p ≤ 2ρδ + m/δ²` for every `δ > 0`, then `p³ ≤ 27ρ²m` (take `δ = p/(3ρ)`; if `ρ = 0`, let
`δ → ∞`). -/
lemma digital_pow_three_le_of_forall {p ρ m : ℝ} (hp : 0 ≤ p) (hρ : 0 ≤ ρ) (hm : 0 ≤ m)
    (h : ∀ δ, 0 < δ → p ≤ 2 * ρ * δ + m / δ ^ 2) : p ^ 3 ≤ 27 * ρ ^ 2 * m := by
  rcases hp.eq_or_lt with hp0 | hp0
  · rw [← hp0, zero_pow three_ne_zero]
    positivity
  rcases hρ.eq_or_lt with hρ0 | hρ0
  · -- `ρ = 0`: letting `δ → ∞` gives `p ≤ 0`
    exfalso
    have h1 := h (2 * m / p + 1) (by positivity)
    rw [← hρ0, mul_zero, zero_mul, zero_add] at h1
    have ht : 0 ≤ 2 * m / p := by positivity
    have h2 : 2 * m / p + 1 ≤ (2 * m / p + 1) ^ 2 := by
      nlinarith [mul_nonneg ht (by linarith : (0 : ℝ) ≤ 2 * m / p + 1)]
    have h3 : m / (2 * m / p + 1) ^ 2 ≤ m / (2 * m / p + 1) :=
      div_le_div_of_nonneg_left hm (by positivity) h2
    have h4 : m / (2 * m / p + 1) < p := by
      rw [div_lt_iff₀ (by positivity)]
      have : p * (2 * m / p) = 2 * m := by field_simp
      nlinarith
    linarith
  · have h1 := h (p / (3 * ρ)) (by positivity)
    have e1 : 2 * ρ * (p / (3 * ρ)) = 2 * p / 3 := by field_simp
    have e2 : m / (p / (3 * ρ)) ^ 2 = 9 * ρ ^ 2 * m / p ^ 2 := by field_simp; ring
    rw [e1, e2] at h1
    have h2 : p / 3 * p ^ 2 ≤ 9 * ρ ^ 2 * m := by
      rw [← le_div_iff₀ (by positivity)]
      linarith
    nlinarith

/-- `p³ ≤ 27ρ²m` gives `p ≤ 3ρ^{2/3}m^{1/3}` for nonnegative `p`, `ρ`, `m`. -/
lemma digital_le_three_mul_rpow {p ρ m : ℝ} (hp : 0 ≤ p) (hρ : 0 ≤ ρ) (hm : 0 ≤ m)
    (h : p ^ 3 ≤ 27 * ρ ^ 2 * m) : p ≤ 3 * ρ ^ (2 / 3 : ℝ) * m ^ (1 / 3 : ℝ) := by
  have e3 : (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  have hp' : p = (p ^ 3) ^ (1 / 3 : ℝ) := by
    rw [e3, Real.pow_rpow_inv_natCast hp (by norm_num)]
  have h27 : (27 : ℝ) ^ (1 / 3 : ℝ) = 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, e3, Real.pow_rpow_inv_natCast (by norm_num)
      (by norm_num)]
  have hρ2 : (ρ ^ 2) ^ (1 / 3 : ℝ) = ρ ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ]
    norm_num
  calc p = (p ^ 3) ^ (1 / 3 : ℝ) := hp'
    _ ≤ (27 * ρ ^ 2 * m) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h (by norm_num)
    _ = 3 * ρ ^ (2 / 3 : ℝ) * m ^ (1 / 3 : ℝ) := by
        rw [Real.mul_rpow (by positivity) hm, Real.mul_rpow (by norm_num) (by positivity), h27,
          hρ2]

/-- **The fraction of paths on either side of the strike** (Giles 2015, §5.1, p. 33: "noting that
the strong error is `O(h_ℓ^{1/2})`, and there is a bounded density of paths terminating in the
neighbourhood of `K`, there is therefore an `O(h_ℓ^{1/2})` fraction of the samples with the coarse
and fine paths on either side of the strike, with `P_ℓ − P_{ℓ−1} = ±1`"; "the digital option
analysis is due to Avikainen (Avikainen 2009)").  Suppose that the law of `X` has density at most
`ρ` near the strike, in the form `P(|X − K| ≤ δ) ≤ 2ρδ` for all `δ > 0` (the paper states this
hypothesis in words; it follows from `μ.map X ≤ ρ • volume`, `measureReal_abs_sub_le_of_map_le`,
and from a density bound `ρ̄` on `[K − δ₀, K + δ₀]` alone with `ρ = max(ρ̄, 1/(2δ₀))`).  Then, for
every `δ > 0`,
* `P(1_{X>K} ≠ 1_{Y>K}) ≤ 2ρδ + P(|X − Y| > δ)` (if the payoffs differ, `K` lies between `X` and
  `Y`, so `|X − K| ≤ |X − Y|`),
* `P(1_{X>K} ≠ 1_{Y>K}) ≤ 2ρδ + E[(X − Y)²]/δ²` (Chebyshev), and, optimising over `δ`,
* `P(1_{X>K} ≠ 1_{Y>K}) ≤ 3ρ^{2/3} E[(X − Y)²]^{1/3}` (an inequality of Avikainen's type, with the
  mean-square error, `p = 2`).

**The rate.**  With the mean-square strong error `E[(X − Y)²] = O(h)` of §5.1 this is an
`O(h^{1/3})` fraction, not `O(h^{1/2})`, and the exponent `1/3` cannot be improved from these two
hypotheses alone: for `X` uniform on `[−1, 1]` (`ρ = ½`), `K = 0` and `Y = X − 2d 1_{0<X<d}`, the
fraction is `d/2` and `E[(X − Y)²] = 2d³`.  The paper's heuristic uses that the error is
`O(h^{1/2})` on (almost) every path, which is more than a mean-square bound: moment bounds
`E|X − Y|^p = O(h^{p/2})` for every `p` give every rate below `½` through the first inequality
(`digital_mismatch_le_of_moment`), and
Gaussian-type tails give `O((h log(1/h))^{1/2})` (`digital_mismatch_le_of_tail`); Table 5.2 lists
`O(h^{1/2} log h)` as the rate proved by Avikainen for Euler–Maruyama, and `O(h^{1/2})` as the
observed one. -/
theorem digital_mismatch_le [IsFiniteMeasure μ] {X Y : Ω → ℝ} {K ρ : ℝ}
    (hρ : ∀ δ, 0 < δ → μ.real {ω | |X ω - K| ≤ δ} ≤ 2 * ρ * δ)
    (hint : Integrable (fun ω => (X ω - Y ω) ^ 2) μ) :
    (∀ δ, 0 < δ →
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
        2 * ρ * δ + μ.real {ω | δ < |X ω - Y ω|}) ∧
    (∀ δ, 0 < δ →
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
        2 * ρ * δ + (∫ ω, (X ω - Y ω) ^ 2 ∂μ) / δ ^ 2) ∧
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
        3 * ρ ^ (2 / 3 : ℝ) * (∫ ω, (X ω - Y ω) ^ 2 ∂μ) ^ (1 / 3 : ℝ) := by
  have hρ0 : 0 ≤ ρ := by
    have := hρ 1 one_pos
    linarith [measureReal_nonneg (μ := μ) (s := {ω | |X ω - K| ≤ 1})]
  have h1 : ∀ δ, 0 < δ →
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
        2 * ρ * δ + μ.real {ω | δ < |X ω - Y ω|} := fun δ hδ =>
    (measureReal_digital_ne_le X Y K δ).trans (add_le_add (hρ δ hδ) le_rfl)
  have h2 : ∀ δ, 0 < δ →
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
        2 * ρ * δ + (∫ ω, (X ω - Y ω) ^ 2 ∂μ) / δ ^ 2 := fun δ hδ =>
    (h1 δ hδ).trans (add_le_add le_rfl (measureReal_lt_abs_sub_le_div_sq hint hδ))
  have hm : 0 ≤ ∫ ω, (X ω - Y ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  exact ⟨h1, h2, digital_le_three_mul_rpow measureReal_nonneg hρ0 hm
    (digital_pow_three_le_of_forall measureReal_nonneg hρ0 hm h2)⟩

/-- The digital payoff `ω ↦ 1_{X(ω) > K}` of a measurable `X` is measurable. -/
lemma measurable_digital {X : Ω → ℝ} (hX : Measurable X) (K : ℝ) :
    Measurable fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) :=
  (measurable_one.indicator measurableSet_Ioi).comp hX

omit [MeasurableSpace Ω] in
/-- `(1_{X>K} − 1_{Y>K})² = 1_{1_{X>K} ≠ 1_{Y>K}}`: the digital correction is `0` or `±1`. -/
lemma sq_digital_sub_eq_indicator (X Y : Ω → ℝ) (K : ℝ) (ω : Ω) :
    ((Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω)) ^ 2 =
      {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)}.indicator
        1 ω := by
  simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_ofPred_eq, Pi.one_apply]
  split_ifs <;> simp_all

/-- `E[(1_{X>K} − 1_{Y>K})²] = P(1_{X>K} ≠ 1_{Y>K})`. -/
lemma integral_sq_digital_sub [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (K : ℝ) :
    ∫ ω, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω)) ^ 2 ∂μ =
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} := by
  have hs : MeasurableSet
      {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} :=
    (measurableSet_eq_fun (measurable_digital hX K) (measurable_digital hY K)).compl
  simp only [sq_digital_sub_eq_indicator X Y K]
  exact integral_indicator_one hs

/-- `V[1_{X>K} − 1_{Y>K}] ≤ P(1_{X>K} ≠ 1_{Y>K})`. -/
lemma variance_digital_le_measureReal [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (K : ℝ) :
    variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω))
        μ ≤
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} := by
  have hm : AEStronglyMeasurable (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) -
      (Set.Ioi K).indicator 1 (Y ω)) μ :=
    ((measurable_digital hX K).sub (measurable_digital hY K)).aestronglyMeasurable
  have hv := variance_le_expectation_sq hm
  simp only [Pi.pow_apply] at hv
  rwa [integral_sq_digital_sub hX hY K] at hv

/-- **The variance of the digital correction is at most the fraction of paths on either side of
the strike** (Giles 2015, §5.1, p. 33: "… with `P_ℓ − P_{ℓ−1} = ±1`. This gives
`V_ℓ = O(h^{1/2})`").  The difference `D = 1_{X>K} − 1_{Y>K}` takes values in `{−1, 0, 1}`, so
`V[D] ≤ E[D²] = P(1_{X>K} ≠ 1_{Y>K}) ≤ 3ρ^{2/3} E[(X − Y)²]^{1/3}` under the density hypothesis of
`digital_mismatch_le`. -/
theorem variance_digital_le [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) {K ρ : ℝ} (hρ : ∀ δ, 0 < δ → μ.real {ω | |X ω - K| ≤ δ} ≤ 2 * ρ * δ)
    (hint : Integrable (fun ω => (X ω - Y ω) ^ 2) μ) :
    variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω))
        μ ≤ ∫ ω, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω)) ^ 2 ∂μ ∧
      ∫ ω, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω)) ^ 2 ∂μ =
        μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ∧
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
        3 * ρ ^ (2 / 3 : ℝ) * (∫ ω, (X ω - Y ω) ^ 2 ∂μ) ^ (1 / 3 : ℝ) := by
  refine ⟨?_, integral_sq_digital_sub hX hY K, (digital_mismatch_le hρ hint).2.2⟩
  rw [integral_sq_digital_sub hX hY K]
  exact variance_digital_le_measureReal hX hY K

omit [MeasurableSpace Ω] in
/-- If the fine and coarse payoffs differ, one of them differs from the exact payoff. -/
lemma digital_ne_subset_union (X Y₁ Y₂ : Ω → ℝ) (K : ℝ) :
    {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (Y₁ ω) ≠ (Set.Ioi K).indicator 1 (Y₂ ω)} ⊆
      {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y₁ ω)} ∪
        {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y₂ ω)} := by
  intro ω hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon hω
  exact hω (hcon.1.symm.trans hcon.2)

/-- **The digital correction between a fine and a coarse approximation** (Giles 2015, §5.1, p. 33:
"there is therefore an `O(h_ℓ^{1/2})` fraction of the samples with the coarse and fine paths on
either side of the strike, with `P_ℓ − P_{ℓ−1} = ±1`").  If the exact value `X` has density at
most `ρ` near `K` (as in `digital_mismatch_le`) and `Y₁`, `Y₂` are the fine and the coarse
approximations, the fine and coarse payoffs can only differ where one of them differs from the
exact payoff, so
`V[1_{Y₁>K} − 1_{Y₂>K}] ≤ 3ρ^{2/3} (E[(X − Y₁)²]^{1/3} + E[(X − Y₂)²]^{1/3})`.  The density
hypothesis is on the exact solution only, not on the approximations. -/
theorem variance_digital_levelDiff_le [IsProbabilityMeasure μ] {X Y₁ Y₂ : Ω → ℝ}
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) {K ρ : ℝ}
    (hρ : ∀ δ, 0 < δ → μ.real {ω | |X ω - K| ≤ δ} ≤ 2 * ρ * δ)
    (hint₁ : Integrable (fun ω => (X ω - Y₁ ω) ^ 2) μ)
    (hint₂ : Integrable (fun ω => (X ω - Y₂ ω) ^ 2) μ) :
    variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (Y₁ ω) - (Set.Ioi K).indicator 1 (Y₂ ω))
        μ ≤ 3 * ρ ^ (2 / 3 : ℝ) * ((∫ ω, (X ω - Y₁ ω) ^ 2 ∂μ) ^ (1 / 3 : ℝ) +
          (∫ ω, (X ω - Y₂ ω) ^ 2 ∂μ) ^ (1 / 3 : ℝ)) := by
  refine (variance_digital_le_measureReal hY₁ hY₂ K).trans
    ((measureReal_mono (digital_ne_subset_union X Y₁ Y₂ K)).trans
      ((measureReal_union_le _ _).trans ?_))
  rw [mul_add]
  exact add_le_add (digital_mismatch_le hρ hint₁).2.2 (digital_mismatch_le hρ hint₂).2.2

/-- **The variance rate of the digital option from the strong rate** (Giles 2015, §5.1, p. 33:
"This gives `V_ℓ = O(h^{1/2})`"; §5.2, p. 35: "In the case of a digital option, if we use the
natural multilevel estimator then `P_ℓ−P_{ℓ−1} = O(1)` for an `O(h_ℓ)` fraction of the paths,
giving `V_ℓ = O(h_ℓ)`").  If the exact value `X` has density at most `ρ` near `K` and the
approximations `Y_ℓ` have the mean-square strong error `E[(X − Y_ℓ)²] ≤ c h_ℓ` (strong order `½`,
e.g. `gbm_strong_error`), then `V[1_{X>K} − 1_{Y_ℓ>K}] ≤ 3ρ^{2/3} c^{1/3} h_ℓ^{1/3}` and
`V[1_{Y_{ℓ+1}>K} − 1_{Y_ℓ>K}] ≤ 3ρ^{2/3} c^{1/3} (h_{ℓ+1}^{1/3} + h_ℓ^{1/3})`, i.e.
`V_ℓ = O(h_ℓ^{1/3})`.  This is weaker than the paper's `O(h_ℓ^{1/2})`, which needs more than the
mean-square error (see `digital_mismatch_le`); likewise, for first-order strong convergence
(Milstein, `E[(X − Y_ℓ)²] ≤ c h_ℓ²`) this gives `O(h_ℓ^{2/3})` in place of the paper's `O(h_ℓ)`. -/
theorem variance_digital_rate [IsProbabilityMeasure μ] {X : Ω → ℝ} {Y : ℕ → Ω → ℝ}
    (hX : Measurable X) (hY : ∀ ℓ, Measurable (Y ℓ)) {K ρ c : ℝ} (hc : 0 ≤ c)
    (hρ : ∀ δ, 0 < δ → μ.real {ω | |X ω - K| ≤ δ} ≤ 2 * ρ * δ)
    (hint : ∀ ℓ, Integrable (fun ω => (X ω - Y ℓ ω) ^ 2) μ) {h : ℕ → ℝ} (hh : ∀ ℓ, 0 ≤ h ℓ)
    (hs : ∀ ℓ, ∫ ω, (X ω - Y ℓ ω) ^ 2 ∂μ ≤ c * h ℓ) (ℓ : ℕ) :
    variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ℓ ω))
        μ ≤ 3 * ρ ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) * h ℓ ^ (1 / 3 : ℝ) ∧
      variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (Y (ℓ + 1) ω) -
          (Set.Ioi K).indicator 1 (Y ℓ ω)) μ ≤
        3 * ρ ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) * (h (ℓ + 1) ^ (1 / 3 : ℝ) + h ℓ ^ (1 / 3 : ℝ)) := by
  have hr : ∀ k, (∫ ω, (X ω - Y k ω) ^ 2 ∂μ) ^ (1 / 3 : ℝ) ≤
      c ^ (1 / 3 : ℝ) * h k ^ (1 / 3 : ℝ) := fun k => by
    rw [← Real.mul_rpow hc (hh k)]
    exact Real.rpow_le_rpow (integral_nonneg fun ω => sq_nonneg _) (hs k) (by norm_num)
  have hρ' : 0 ≤ 3 * ρ ^ (2 / 3 : ℝ) := by
    have := hρ 1 one_pos
    have hρ0 : 0 ≤ ρ := by linarith [measureReal_nonneg (μ := μ) (s := {ω | |X ω - K| ≤ 1})]
    positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := variance_digital_le (K := K) hX (hY ℓ) hρ (hint ℓ)
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h3
      _ ≤ 3 * ρ ^ (2 / 3 : ℝ) * (c ^ (1 / 3 : ℝ) * h ℓ ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hr ℓ) hρ'
      _ = _ := by ring
  · calc _ ≤ _ := variance_digital_levelDiff_le (hY (ℓ + 1)) (hY ℓ) hρ (hint (ℓ + 1)) (hint ℓ)
      _ ≤ 3 * ρ ^ (2 / 3 : ℝ) * (c ^ (1 / 3 : ℝ) * h (ℓ + 1) ^ (1 / 3 : ℝ) +
          c ^ (1 / 3 : ℝ) * h ℓ ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add (hr (ℓ + 1)) (hr ℓ)) hρ'
      _ = _ := by ring

/-- **Gaussian tails of the strong error give the rate `(h log(1/h))^{1/2}`** (Giles 2015, §5.1,
p. 33, Table 5.2: the digital option with Euler–Maruyama has the observed rate `O(h^{1/2})` and the
analysis rate `O(h^{1/2} log h)`).  If `X` has density at most `ρ` near `K` and the error has
Gaussian-type tails, `P(|X − Y| > δ) ≤ A e^{−δ²/(Bh)}` for all `δ > 0`, with `B > 0` and
`0 < h < 1`, then (taking `δ = (B h log(1/h))^{1/2}` in `digital_mismatch_le`)
`V[1_{X>K} − 1_{Y>K}] ≤ P(1_{X>K} ≠ 1_{Y>K}) ≤ 2ρ (B h log(1/h))^{1/2} + A h`.  The tail bound
is a hypothesis: for the Euler–Maruyama scheme it is SDE theory, not proved here.  Only the value
`δ = (B h log(1/h))^{1/2}` is used.  The bound holds, for example, when `Y − X` is `√h` times a
standard Gaussian; it does not hold for all `δ` for the Euler–Maruyama error of geometric Brownian
motion, whose tails are lognormal, and that case is `gbm_digital_variance_le`. -/
theorem digital_mismatch_le_of_tail [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) {K ρ A B h : ℝ}
    (hρ : ∀ δ, 0 < δ → μ.real {ω | |X ω - K| ≤ δ} ≤ 2 * ρ * δ) (hB : 0 < B) (hh : 0 < h)
    (hh1 : h < 1)
    (htail : ∀ δ, 0 < δ → μ.real {ω | δ < |X ω - Y ω|} ≤ A * Real.exp (-(δ ^ 2 / (B * h)))) :
    variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω))
        μ ≤ μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ∧
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
        2 * ρ * Real.sqrt (B * h * Real.log h⁻¹) + A * h := by
  refine ⟨variance_digital_le_measureReal hX hY K, ?_⟩
  have hlog : 0 < Real.log h⁻¹ := Real.log_pos ((one_lt_inv₀ hh).2 hh1)
  have hBh : 0 < B * h := mul_pos hB hh
  set δ := Real.sqrt (B * h * Real.log h⁻¹) with hδ
  have hδ0 : 0 < δ := Real.sqrt_pos.2 (mul_pos hBh hlog)
  have hexp : Real.exp (-(δ ^ 2 / (B * h))) = h := by
    rw [hδ, Real.sq_sqrt (mul_pos hBh hlog).le, mul_div_cancel_left₀ _ hBh.ne', Real.exp_neg,
      Real.exp_log (inv_pos.2 hh), inv_inv]
  calc _ ≤ _ := measureReal_digital_ne_le X Y K δ
    _ ≤ 2 * ρ * δ + A * Real.exp (-(δ ^ 2 / (B * h))) := add_le_add (hρ δ hδ0) (htail δ hδ0)
    _ = _ := by rw [hexp]

/-- Markov's inequality for the `p`-th moment: `P(|X − Y| > δ) ≤ E|X − Y|^p/δ^p` for `δ > 0`. -/
lemma measureReal_lt_abs_sub_le_div_pow [IsFiniteMeasure μ] {X Y : Ω → ℝ} {p : ℕ}
    (hint : Integrable (fun ω => |X ω - Y ω| ^ p) μ) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | δ < |X ω - Y ω|} ≤ (∫ ω, |X ω - Y ω| ^ p ∂μ) / δ ^ p := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => pow_nonneg (abs_nonneg (X ω - Y ω)) p) hint (δ ^ p)
  rw [le_div_iff₀ (by positivity), mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono fun ω hω => ?_) (by positivity)) h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact pow_le_pow_left₀ hδ.le hω.le p

/-- **Higher moments of the strong error give rates closer to `½`** (Giles 2015, §5.1, p. 33:
"noting that the strong error is `O(h_ℓ^{1/2})`, and there is a bounded density of paths
terminating in the neighbourhood of `K`, there is therefore an `O(h_ℓ^{1/2})` fraction of the
samples with the coarse and fine paths on either side of the strike").  If `X` has density at most
`ρ` near `K` (as in `digital_mismatch_le`) and `|X − Y|^p` is integrable for some `p ∈ ℕ`, then,
taking `δ = E[|X − Y|^p]^{1/(p+1)}` in the first bound of `digital_mismatch_le` together with
Markov's inequality, `V[1_{X>K} − 1_{Y>K}] ≤ P(1_{X>K} ≠ 1_{Y>K}) ≤
(2ρ + 1) E[|X − Y|^p]^{1/(p+1)}`.  A strong error of order `½` in `L^p`, `E|X − Y|^p ≤ c h^{p/2}`,
gives `O(h^{p/(2(p+1))})`, so strong order `½` in every `L^p` (as for Euler–Maruyama under the
usual conditions, which is SDE theory and not proved here) gives every rate below `½`. -/
theorem digital_mismatch_le_of_moment [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) {K ρ : ℝ} (hρ : ∀ δ, 0 < δ → μ.real {ω | |X ω - K| ≤ δ} ≤ 2 * ρ * δ)
    {p : ℕ} (hint : Integrable (fun ω => |X ω - Y ω| ^ p) μ) :
    variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω))
        μ ≤ μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ∧
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
        (2 * ρ + 1) * (∫ ω, |X ω - Y ω| ^ p ∂μ) ^ (1 / (p + 1 : ℝ)) := by
  refine ⟨variance_digital_le_measureReal hX hY K, ?_⟩
  have hρ0 : 0 ≤ ρ := by
    have := hρ 1 one_pos
    linarith [measureReal_nonneg (μ := μ) (s := {ω | |X ω - K| ≤ 1})]
  set P := μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)}
  set m := ∫ ω, |X ω - Y ω| ^ p ∂μ
  have hm0 : 0 ≤ m := integral_nonneg fun ω => pow_nonneg (abs_nonneg _) p
  have hδ : ∀ δ, 0 < δ → P ≤ 2 * ρ * δ + m / δ ^ p := fun δ hδ =>
    (measureReal_digital_ne_le X Y K δ).trans
      (add_le_add (hρ δ hδ) (measureReal_lt_abs_sub_le_div_pow hint hδ))
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  rcases hm0.eq_or_lt with hm00 | hmpos
  · -- `m = 0`: `P ≤ 2ρδ` for every `δ > 0`
    rw [← hm00, Real.zero_rpow (one_div_pos.2 hp1).ne', mul_zero]
    by_contra hPpos'
    have hPpos := not_le.1 hPpos'
    have h1 := hδ (P / (4 * ρ + 1)) (by positivity)
    rw [← hm00, zero_div, add_zero] at h1
    have h2 : 2 * ρ * (P / (4 * ρ + 1)) < P := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  · -- `m > 0`: take `δ = m^{1/(p+1)}`
    have hd : 0 < m ^ (1 / (p + 1 : ℝ)) := Real.rpow_pos_of_pos hmpos _
    have h1 := hδ _ hd
    have e : m / (m ^ (1 / (p + 1 : ℝ))) ^ p = m ^ (1 / (p + 1 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le, div_eq_iff (by positivity),
        ← Real.rpow_add hmpos]
      have : 1 / ((p : ℝ) + 1) + 1 / ((p : ℝ) + 1) * p = 1 := by
        field_simp
        ring
      rw [this, Real.rpow_one]
    rw [e] at h1
    linarith

end Digital

/-! ### §5.1: the digital option for geometric Brownian motion -/

/-- **The lognormal law has a bounded density**: for `s₀ ≠ 0`, `s ≠ 0` and `Z ∼ N(0,1)`, the law
of `s₀ e^{μ₀ + sZ}` is at most `ρ` times Lebesgue measure, `ρ = e^{s²/2 − μ₀}/(√(2π) |s₀| |s|)`
(the maximum of its density).  By the change of variables `x = s₀ e^{μ₀ + su}`, it suffices that
`φ(u) ≤ ρ |s₀ s| e^{μ₀ + su}`, i.e. `−u²/2 ≤ s²/2 + su`. -/
lemma map_lognormal_le_smul_volume {s₀ μ₀ s : ℝ} (hs₀ : s₀ ≠ 0) (hs : s ≠ 0) :
    (gaussianReal 0 1).map (fun u => s₀ * Real.exp (μ₀ + s * u)) ≤
      ENNReal.ofReal (Real.exp (s ^ 2 / 2 - μ₀) / (Real.sqrt (2 * Real.pi) * |s₀| * |s|)) •
        volume := by
  set f : ℝ → ℝ := fun u => s₀ * Real.exp (μ₀ + s * u)
  set ρ := Real.exp (s ^ 2 / 2 - μ₀) / (Real.sqrt (2 * Real.pi) * |s₀| * |s|) with hρ
  have hfm : Measurable f := by fun_prop
  have hderiv : ∀ u, HasDerivAt f (s₀ * Real.exp (μ₀ + s * u) * s) u := fun u => by
    have h1 : HasDerivAt (fun u => μ₀ + s * u) s u := by
      simpa using ((hasDerivAt_id u).const_mul s).const_add μ₀
    simpa [mul_assoc] using h1.exp.const_mul s₀
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hpt : ∀ u, gaussianPDFReal 0 1 u ≤ |s₀ * Real.exp (μ₀ + s * u) * s| * ρ := by
    intro u
    have e1 : gaussianPDFReal 0 1 u = Real.exp (-u ^ 2 / 2) / Real.sqrt (2 * Real.pi) := by
      simp [gaussianPDFReal, div_eq_inv_mul]
    have e2 : |s₀ * Real.exp (μ₀ + s * u) * s| * ρ =
        Real.exp (s ^ 2 / 2 + s * u) / Real.sqrt (2 * Real.pi) := by
      rw [hρ, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have habs : 0 < |s| := abs_pos.2 hs
      have habs₀ : 0 < |s₀| := abs_pos.2 hs₀
      have : Real.exp (s ^ 2 / 2 + s * u) =
          Real.exp (μ₀ + s * u) * Real.exp (s ^ 2 / 2 - μ₀) := by
        rw [← Real.exp_add]
        ring_nf
      rw [this]
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith [sq_nonneg (u + s)]))
      hsqrt.le
  refine Measure.le_iff.2 fun A hA => ?_
  have hpre : MeasurableSet (f ⁻¹' A) := hfm hA
  have hinj : Set.InjOn f (f ⁻¹' A) := fun u _ v _ huv => by
    have h1 := mul_left_cancel₀ hs₀ huv
    have h2 := Real.exp_injective h1
    exact mul_left_cancel₀ hs (by linarith)
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul hpre
    (fun u _ => (hderiv u).hasDerivWithinAt) hinj (fun _ => ENNReal.ofReal ρ)
  rw [Measure.map_apply hfm hA, Measure.smul_apply, smul_eq_mul]
  calc gaussianReal 0 1 (f ⁻¹' A) = ∫⁻ u in f ⁻¹' A, gaussianPDF 0 1 u :=
        gaussianReal_apply 0 one_ne_zero _
    _ ≤ ∫⁻ u in f ⁻¹' A, ENNReal.ofReal |s₀ * Real.exp (μ₀ + s * u) * s| * ENNReal.ofReal ρ := by
        refine lintegral_mono fun u => ?_
        rw [gaussianPDF, ← ENNReal.ofReal_mul (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hpt u)
    _ = ∫⁻ x in f '' (f ⁻¹' A), ENNReal.ofReal ρ := hcov.symm
    _ = ENNReal.ofReal ρ * volume (f '' (f ⁻¹' A)) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ρ * volume A := by
        gcongr
        exact Set.image_preimage_subset f A

/-- **The digital option for geometric Brownian motion with Euler–Maruyama: `V_ℓ = O(h_ℓ^{1/3})`**
(Giles 2015, §5.1, pp. 30 and 33, Figure 5.4: "the payoff is a digital option with payoff
`P(S) ≡ 10 exp(−rT) H(S_T−K)`, where `H(x)` is the Heaviside step function … This gives
`V_ℓ = O(h^{1/2})`").  For `dS = rS dt + σS dW` with `s₀ ≠ 0`, `σ ≠ 0` and `T > 0`, the
correction on level `ℓ + 1` of the digital payoff `H(S_T − K)` (the payoff of the fine
Euler–Maruyama path minus that of the coarse path driven by the summed increments, as in
`gbm_correction_variance_le`) has variance
`V_{ℓ+1} ≤ 3ρ^{2/3} C(T)^{1/3} (h_{ℓ+1}^{1/3} + h_ℓ^{1/3})`, `h_ℓ = T 2^{−ℓ}`, where `C(T)` is the
constant of the strong error (`gbmStrongConst`, `gbm_strong_error`) and
`ρ = e^{(σ² − r)T}/(√(2π) |s₀| |σ| √T)` is the maximum of the lognormal density of `S_T`
(`map_lognormal_le_smul_volume`).  This proves `β = 1/3` with no assumption; the paper's `β = ½` is
the observed rate (see `digital_mismatch_le`).  The factor `10 e^{−rT}` of the payoff multiplies the
variance by `100 e^{−2rT}`. -/
theorem gbm_digital_variance_le (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) (ℓ : ℕ) :
    variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
      3 * (Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) ^
          (2 / 3 : ℝ) * gbmStrongConst r σ T s₀ ^ (1 / 3 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (1 / 3 : ℝ) + (T / 2 ^ ℓ) ^ (1 / 3 : ℝ)) := by
  set ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)
    with hρdef
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hρ0 : 0 ≤ ρ := by positivity
  have hC := gbmStrongConst_nonneg r σ s₀ hT.le
  -- the exact solution at maturity, driven by the fine increments
  set X := gbmExact r σ T s₀ (ℓ + 1) with hXdef
  -- its law is lognormal, with density at most `ρ`
  have hlaw : stdNormalSeq.map X = (gaussianReal 0 1).map
      (fun u => s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * u)) := by
    have e : gbmExact r σ T s₀ 0 =
        (fun u => s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * u)) ∘
          (fun z : ℕ → ℝ => z 0) := by
      funext z
      simp only [Function.comp_apply, gbmExact_zero, mul_assoc]
    have hgm : Measurable
        (fun u : ℝ => s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * u)) := by fun_prop
    rw [hXdef, map_gbmExact, e, ← Measure.map_map hgm (measurable_pi_apply 0),
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0).map_eq]
  have hmap : stdNormalSeq.map X ≤ ENNReal.ofReal ρ • volume := by
    have hs : σ * Real.sqrt T ≠ 0 := mul_ne_zero hσ hsT.ne'
    have h1 := map_lognormal_le_smul_volume (μ₀ := (r - σ ^ 2 / 2) * T) hs₀ hs
    have e3 : Real.exp ((σ * Real.sqrt T) ^ 2 / 2 - (r - σ ^ 2 / 2) * T) /
        (Real.sqrt (2 * Real.pi) * |s₀| * |σ * Real.sqrt T|) = ρ := by
      rw [hρdef, abs_mul, abs_of_pos hsT, mul_pow, Real.sq_sqrt hT.le, ← mul_assoc]
      congr 2
      ring
    rw [e3] at h1
    rw [hlaw]
    exact h1
  have hball : ∀ δ, 0 < δ → stdNormalSeq.real {z | |X z - K| ≤ δ} ≤ 2 * ρ * δ := fun δ hδ =>
    measureReal_abs_sub_le_of_map_le (measurable_gbmExact r σ T s₀ (ℓ + 1)) hρ0 hmap K hδ.le
  -- the strong errors of the fine and the coarse path
  have hint₁ := integrable_sq_gbm_err r σ T s₀ (ℓ + 1)
  have hI0' := integrable_sq_gbm_err r σ T s₀ ℓ
  have hXc : ∀ z, X z = gbmExact r σ T s₀ ℓ (pairAvg z) := fun z =>
    (gbmExact_pairAvg r σ T s₀ ℓ z).symm
  have hint₂ : Integrable (fun z => (X z - gbmEM r σ T s₀ ℓ (pairAvg z)) ^ 2) stdNormalSeq := by
    simp only [hXc]
    exact (measurePreserving_pairAvg.integrable_comp hI0'.aestronglyMeasurable).2 hI0'
  have hs₁ := gbm_strong_error r σ s₀ hT.le (ℓ + 1)
  have hs₂ : ∫ z, (X z - gbmEM r σ T s₀ ℓ (pairAvg z)) ^ 2 ∂stdNormalSeq ≤
      gbmStrongConst r σ T s₀ * (T / 2 ^ ℓ) := by
    simp only [hXc]
    rw [integral_comp_of_measurePreserving measurePreserving_pairAvg hI0'.aestronglyMeasurable]
    exact gbm_strong_error r σ s₀ hT.le ℓ
  have hv := variance_digital_levelDiff_le (K := K)
    (measurable_gbmEM r σ T s₀ (ℓ + 1))
    ((measurable_gbmEM r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable) hball
    hint₁ hint₂
  have hr : ∀ {m h : ℝ}, m ≤ gbmStrongConst r σ T s₀ * h → 0 ≤ m → 0 ≤ h →
      m ^ (1 / 3 : ℝ) ≤ gbmStrongConst r σ T s₀ ^ (1 / 3 : ℝ) * h ^ (1 / 3 : ℝ) := by
    intro m h hm hm0 hh
    rw [← Real.mul_rpow hC hh]
    exact Real.rpow_le_rpow hm0 hm (by norm_num)
  have hT1 : 0 ≤ T / 2 ^ (ℓ + 1) := by positivity
  have hT0 : 0 ≤ T / 2 ^ ℓ := by positivity
  refine hv.trans ?_
  calc 3 * ρ ^ (2 / 3 : ℝ) * ((∫ z, (X z - gbmEM r σ T s₀ (ℓ + 1) z) ^ 2 ∂stdNormalSeq) ^
          (1 / 3 : ℝ) + (∫ z, (X z - gbmEM r σ T s₀ ℓ (pairAvg z)) ^ 2 ∂stdNormalSeq) ^
          (1 / 3 : ℝ))
      ≤ 3 * ρ ^ (2 / 3 : ℝ) * (gbmStrongConst r σ T s₀ ^ (1 / 3 : ℝ) *
          (T / 2 ^ (ℓ + 1)) ^ (1 / 3 : ℝ) + gbmStrongConst r σ T s₀ ^ (1 / 3 : ℝ) *
          (T / 2 ^ ℓ) ^ (1 / 3 : ℝ)) := by
        gcongr
        · exact hr hs₁ (integral_nonneg fun _ => sq_nonneg _) hT1
        · exact hr hs₂ (integral_nonneg fun _ => sq_nonneg _) hT0
    _ = _ := by ring

/-! ### §5.2: the conditional expectation of the digital payoff -/

/-- `Φ(x) = ∫_{−∞}^x φ(t) dt` with `φ(t) = e^{−t²/2}/√(2π)`: Mathlib's `cdf (gaussianReal 0 1)` is
the "Normal cumulative distribution function" `Φ` of Giles 2015, §5.2, p. 36. -/
lemma cdf_stdGaussian_eq_integral (x : ℝ) :
    cdf (gaussianReal 0 1) x = ∫ t in Set.Iic x, gaussianPDFReal 0 1 t := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg fun t => gaussianPDFReal_nonneg 0 1 t)]

/-- `0 < Φ(x)`: the standard normal law charges every half-line. -/
lemma cdf_stdGaussian_pos (x : ℝ) : 0 < cdf (gaussianReal 0 1) x := by
  rw [cdf_eq_real]
  refine ENNReal.toReal_pos (fun h0 => ?_) (measure_ne_top _ _)
  have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0) h0
  rw [Real.volume_Iic] at this
  exact ENNReal.top_ne_zero this

/-- `Φ(x) < 1`. -/
lemma cdf_stdGaussian_lt_one (x : ℝ) : cdf (gaussianReal 0 1) x < 1 := by
  have h : 0 < (gaussianReal 0 1).real (Set.Iic x)ᶜ := by
    refine ENNReal.toReal_pos (fun h0 => ?_) (measure_ne_top _ _)
    have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0) h0
    rw [Set.compl_Iic, Real.volume_Ioi] at this
    exact ENNReal.top_ne_zero this
  rw [probReal_compl_eq_one_sub measurableSet_Iic] at h
  rw [cdf_eq_real]
  linarith

/-- `P(m + sZ > K) = Φ((m − K)/|s|)` for `Z ∼ N(0,1)` and `s ≠ 0`. -/
lemma stdGaussian_measureReal_gt {m s : ℝ} (hs : s ≠ 0) (K : ℝ) :
    (gaussianReal 0 1).real {z | K < m + s * z} = cdf (gaussianReal 0 1) ((m - K) / |s|) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  -- the case `s < 0`
  have hneg : ∀ s : ℝ, s < 0 →
      (gaussianReal 0 1).real {z | K < m + s * z} = cdf (gaussianReal 0 1) ((m - K) / |s|) := by
    intro s hs
    have e : {z : ℝ | K < m + s * z} = Set.Iio ((m - K) / |s|) := by
      ext z
      rw [Set.mem_ofPred_eq, Set.mem_Iio, abs_of_neg hs, lt_div_iff₀ (neg_pos.2 hs)]
      constructor <;> intro h <;> linarith
    rw [e, cdf_eq_real, measureReal_congr Iio_ae_eq_Iic]
  rcases lt_or_gt_of_ne hs with h | h
  · exact hneg s h
  · -- `z ↦ −z` preserves `N(0,1)` and turns `s` into `−s`
    have hsym : (gaussianReal 0 1).real {z | K < m + s * z} =
        (gaussianReal 0 1).real {z | K < m + -s * z} := by
      have hmeas : MeasurableSet {z : ℝ | K < m + -s * z} :=
        measurableSet_lt measurable_const (by fun_prop)
      have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
        rw [gaussianReal_map_neg, neg_zero]
      conv_rhs => rw [← hmap, map_measureReal_apply measurable_neg hmeas]
      congr 1
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      ring_nf
    rw [hsym, hneg (-s) (by linarith), abs_neg]

/-- `E[1_{m + sZ > K}] = Φ((m − K)/|s|)` for `Z ∼ N(0,1)` and `s ≠ 0`. -/
lemma integral_digital_gaussian {m s : ℝ} (hs : s ≠ 0) (K : ℝ) :
    ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (m + s * z) ∂gaussianReal 0 1 =
      cdf (gaussianReal 0 1) ((m - K) / |s|) := by
  have hmeas : MeasurableSet {z : ℝ | K < m + s * z} :=
    measurableSet_lt measurable_const (by fun_prop)
  have e : (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (m + s * z)) =
      {z : ℝ | K < m + s * z}.indicator 1 := by
    funext z
    simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_ofPred_eq, Pi.one_apply]
  rw [e, integral_indicator_one hmeas, stdGaussian_measureReal_gt hs]

/-- **The expected digital payoff over the last Euler–Maruyama step** (Giles 2015, §5.2,
pp. 35–36: "Conditional on the value `Ŝ_{N−1}` which is the numerical approximation of `S_{T−h}`
one timestep before the maturity `T`, the numerical approximation for the final value `Ŝ_N` has a
Gaussian distribution, and for a simple digital option the conditional expectation is known
analytically. Thus the fine path payoff can be taken to be
`P^f_ℓ = 25 exp(−rT) Φ((Ŝ^f_{N−1} + a(Ŝ^f_{N−1}) h_ℓ − K)/(b(Ŝ^f_{N−1}) √h_ℓ))`, where `Φ` is the
Normal cumulative distribution function").  For `h > 0`, `b ≠ 0` and `Z ∼ N(0,1)`,
`E[1_{x + ah + b√h Z > K}] = Φ((x + ah − K)/(|b|√h))`.  The paper writes `b` for `|b|` (it has
`b > 0` in mind: for `b < 0` its formula gives `1 − Φ(…)`) and keeps the constant factor
`25 e^{−rT}`, which is omitted here. -/
theorem integral_digital_final_step {x a b h : ℝ} (hb : b ≠ 0) (hh : 0 < h) (K : ℝ) :
    ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (x + a * h + b * Real.sqrt h * z) ∂gaussianReal 0 1 =
      cdf (gaussianReal 0 1) ((x + a * h - K) / (|b| * Real.sqrt h)) := by
  have hs : b * Real.sqrt h ≠ 0 := mul_ne_zero hb (Real.sqrt_pos.2 hh).ne'
  rw [integral_digital_gaussian hs, abs_mul, abs_of_pos (Real.sqrt_pos.2 hh)]

section CondExp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The conditional expectation of the digital payoff given the path before the last step**
(Giles 2015, §5.2, pp. 35–36: "Conditional on the value `Ŝ_{N−1}` … the numerical approximation
for the final value `Ŝ_N` has a Gaussian distribution, and for a simple digital option the
conditional expectation is known analytically").  Let `X` (the information before the last step,
with values in any measurable space) be independent of `Z ∼ N(0,1)`, and let the final value be
`m(X) + s(X) Z` with `s(X) ≠ 0` a.s.  Then `E[1_{m(X) + s(X) Z > K} | X] = Φ((m(X) − K)/|s(X)|)`
a.s.  The fine path has `m(x) = x + a(x) h_ℓ`, `s(x) = b(x) √h_ℓ` (`digital_smoothing`); the coarse
path has `m = Ŝ^c_{N−2} + a h_{ℓ−1} + b ΔW_{N−2}`, `s = b √h_ℓ` (`digital_smoothing_coarse`). -/
theorem condExp_digital_last_step {E : Type*} [mE : MeasurableSpace E] {X : Ω → E} {Z : Ω → ℝ}
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hZlaw : μ.map Z = gaussianReal 0 1) {m s : E → ℝ} (hm : Measurable m) (hs : Measurable s)
    (hs0 : ∀ᵐ ω ∂μ, s (X ω) ≠ 0) (K : ℝ) :
    μ[fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (m (X ω) + s (X ω) * Z ω) | mE.comap X] =ᵐ[μ]
      fun ω => cdf (gaussianReal 0 1) ((m (X ω) - K) / |s (X ω)|) := by
  set f : E × ℝ → ℝ := fun p => (Set.Ioi K).indicator (1 : ℝ → ℝ) (m p.1 + s p.1 * p.2) with hf
  have hfm : Measurable f :=
    (measurable_one.indicator measurableSet_Ioi).comp
      ((hm.comp measurable_fst).add ((hs.comp measurable_fst).mul measurable_snd))
  have hint : Integrable (fun ω => f (X ω, Z ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (hfm.comp (hX.prodMk hZ)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    simp only [hf, Set.indicator_apply]
    split_ifs <;> simp
  have h1 := condExp_prod_ae_eq_integral_condDistrib hX hZ.aemeasurable
    hfm.stronglyMeasurable hint
  -- by independence, the conditional law of `Z` given `X` is `N(0,1)`
  have hlaw : μ.map (fun ω => (X ω, Z ω)) = μ.map X ⊗ₘ Kernel.const E (gaussianReal 0 1) := by
    rw [Measure.compProd_const, ← hZlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).1 hXZ
  have h2 := condDistrib_ae_eq_of_measure_eq_compProd X hZ.aemeasurable hlaw
  have h3 := ae_of_ae_map hX.aemeasurable h2
  filter_upwards [h1, h3, hs0] with ω hω1 hω3 hω0
  rw [hω1, hω3, Kernel.const_apply]
  exact integral_digital_gaussian (m := m (X ω)) hω0 K

/-- A `[0, 1]`-valued `G` with the mean of a `{0, 1}`-valued `F` has `V[G] ≤ V[F]`:
`V[G] = E[G²] − E[G]² ≤ E[G] − E[F]² = E[F²] − E[F]² = V[F]`. -/
lemma variance_smoothed_le_of_integral_eq {G F : Ω → ℝ} (hG : Measurable G) (hF : Measurable F)
    (hG01 : ∀ ω, 0 ≤ G ω ∧ G ω ≤ 1) (hF01 : ∀ ω, F ω = 0 ∨ F ω = 1)
    (hmean : ∫ ω, G ω ∂μ = ∫ ω, F ω ∂μ) : variance G μ ≤ variance F μ := by
  have hGb : ∀ ω, G ω ∈ Set.Icc (0 : ℝ) 1 := fun ω => hG01 ω
  have hFb : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1 := fun ω => by
    rcases hF01 ω with h | h <;> simp [h]
  have hGL : MemLp G 2 μ := memLp_of_bounded (Eventually.of_forall hGb) hG.aestronglyMeasurable 2
  have hFL : MemLp F 2 μ := memLp_of_bounded (Eventually.of_forall hFb) hF.aestronglyMeasurable 2
  rw [variance_eq_sub hGL, variance_eq_sub hFL, hmean]
  simp only [Pi.pow_apply]
  have hF2 : ∫ ω, F ω ^ 2 ∂μ = ∫ ω, F ω ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by rcases hF01 ω with h | h <;> simp [h])
  have hG2 : ∫ ω, G ω ^ 2 ∂μ ≤ ∫ ω, G ω ∂μ :=
    integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
      (hGL.integrable one_le_two) (Eventually.of_forall fun ω => by
        have := hG01 ω
        nlinarith)
  rw [hF2]
  linarith

/-- The digital payoff is `0` or `1`. -/
lemma digital_eq_zero_or_one (K x : ℝ) :
    (Set.Ioi K).indicator (1 : ℝ → ℝ) x = 0 ∨ (Set.Ioi K).indicator (1 : ℝ → ℝ) x = 1 := by
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Payoff smoothing by conditional expectation keeps the mean and does not increase the
variance** (Giles 2015, §5.2, pp. 35–36: the fine path payoff
`P^f_ℓ = 25 exp(−rT) Φ((Ŝ^f_{N−1} + a(Ŝ^f_{N−1}) h_ℓ − K)/(b(Ŝ^f_{N−1}) √h_ℓ))`, and p. 36: "It is
very important in this conditional expectation formulation that `E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` …
This ensures that the identity in Equation (2.4) is respected").  Let `X = Ŝ_{N−1}` be independent
of the last normalised Brownian increment `Z ∼ N(0,1)`, and let the last step be Euler–Maruyama,
`Ŝ_N = X + a(X) h + b(X) √h Z`, with `h > 0` and `b(X) ≠ 0` a.s.  Then
`E[1_{Ŝ_N > K} | X] = Φ((X + a(X) h − K)/(|b(X)| √h))` a.s., the smoothed payoff has the mean of the
digital payoff `1_{Ŝ_N > K}` (so if the fine and coarse smoothed payoffs of level `ℓ − 1` are the
smoothings of digital payoffs with the same mean, (2.4) holds, cf.
`integral_condExp_eq_of_map_eq`), and its variance is at most that of the digital payoff.  (The
paper writes `b` for `|b|` and keeps the factor `25 e^{−rT}`.) -/
theorem digital_smoothing {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z μ) (hZlaw : μ.map Z = gaussianReal 0 1) {a b : ℝ → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hb0 : ∀ᵐ ω ∂μ, b (X ω) ≠ 0) {h : ℝ} (hh : 0 < h)
    (K : ℝ) :
    μ[fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (X ω + a (X ω) * h + b (X ω) * Real.sqrt h * Z ω) | MeasurableSpace.comap X inferInstance]
        =ᵐ[μ]
        (fun ω => cdf (gaussianReal 0 1) ((X ω + a (X ω) * h - K) / (|b (X ω)| * Real.sqrt h))) ∧
      ∫ ω, cdf (gaussianReal 0 1) ((X ω + a (X ω) * h - K) / (|b (X ω)| * Real.sqrt h)) ∂μ =
        ∫ ω, (Set.Ioi K).indicator (1 : ℝ → ℝ)
          (X ω + a (X ω) * h + b (X ω) * Real.sqrt h * Z ω) ∂μ ∧
      variance
          (fun ω => cdf (gaussianReal 0 1) ((X ω + a (X ω) * h - K) / (|b (X ω)| * Real.sqrt h)))
          μ ≤
        variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
          (X ω + a (X ω) * h + b (X ω) * Real.sqrt h * Z ω)) μ := by
  have hsq : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hce := condExp_digital_last_step hX hZ hXZ hZlaw (m := fun x => x + a x * h)
    (s := fun x => b x * Real.sqrt h) (measurable_id.add (ha.mul_const h)) (hb.mul_const _)
    (hb0.mono fun ω hω => mul_ne_zero hω hsq.ne') K
  have hce' : μ[fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (X ω + a (X ω) * h + b (X ω) * Real.sqrt h * Z ω) | MeasurableSpace.comap X inferInstance]
        =ᵐ[μ] fun ω =>
          cdf (gaussianReal 0 1) ((X ω + a (X ω) * h - K) / (|b (X ω)| * Real.sqrt h)) := by
    filter_upwards [hce] with ω hω
    rw [hω, abs_mul, abs_of_pos hsq]
  have hFm : Measurable fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (X ω + a (X ω) * h + b (X ω) * Real.sqrt h * Z ω) :=
    (measurable_one.indicator measurableSet_Ioi).comp
      ((hX.add ((ha.comp hX).mul_const h)).add (((hb.comp hX).mul_const _).mul hZ))
  have hGm : Measurable fun ω =>
      cdf (gaussianReal 0 1) ((X ω + a (X ω) * h - K) / (|b (X ω)| * Real.sqrt h)) :=
    (monotone_cdf (gaussianReal 0 1)).measurable.comp
      (((hX.add ((ha.comp hX).mul_const h)).sub_const K).div ((hb.comp hX).abs.mul_const _))
  have hmean :
      ∫ ω, cdf (gaussianReal 0 1) ((X ω + a (X ω) * h - K) / (|b (X ω)| * Real.sqrt h)) ∂μ =
      ∫ ω, (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (X ω + a (X ω) * h + b (X ω) * Real.sqrt h * Z ω) ∂μ := by
    rw [← integral_congr_ae hce']
    exact integral_condExp hX.comap_le
  exact ⟨hce', hmean, variance_smoothed_le_of_integral_eq hGm hFm
    (fun ω => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩) (fun ω => digital_eq_zero_or_one _ _)
    hmean⟩

/-- **The coarse-path conditional expectation** (Giles 2015, §5.2, p. 36: "A similar treatment is
used for the coarse path, except that in the final timestep, we re-use the known value of the
Brownian increment for the second last fine timestep, which corresponds to the first half of the
final coarse timestep. … the corresponding coarse path payoff function is
`P^c_{ℓ−1} = 25 exp(−rT) Φ((Ŝ^c_{N−2} + a(Ŝ^c_{N−2}) h_{ℓ−1} + b(Ŝ^c_{N−2}) √h_ℓ − K)/
(b(Ŝ^c_{N−2}) √h_ℓ))`").  The last coarse step is `Ŝ^c_N = S + a(S) h_{ℓ−1} + b(S)(W + √h_ℓ Z)`
with `S = Ŝ^c_{N−2}`, `W = ΔW_{N−2}` the known first fine increment and `√h_ℓ Z = ΔW_{N−1}` the
second.  If `(S, W)` is independent of `Z ∼ N(0,1)`, `h_ℓ > 0` and `b(S) ≠ 0` a.s., then
`E[1_{Ŝ^c_N > K} | S, W] = Φ((S + a(S) h_{ℓ−1} + b(S) W − K)/(|b(S)| √h_ℓ))` a.s.
**Correction:** the numerator of the paper's formula has `b(Ŝ^c_{N−2}) √h_ℓ` where the re-used
increment belongs, `b(Ŝ^c_{N−2}) ΔW_{N−2}` (`= b √h_ℓ Z_{N−2}`); with `√h_ℓ` in its place the
formula does not use the re-used increment and is not the conditional expectation. -/
theorem digital_smoothing_coarse {S W Z : Ω → ℝ} (hS : Measurable S) (hW : Measurable W)
    (hZ : Measurable Z) (hind : IndepFun (fun ω => (S ω, W ω)) Z μ)
    (hZlaw : μ.map Z = gaussianReal 0 1) {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hb0 : ∀ᵐ ω ∂μ, b (S ω) ≠ 0) {hc hf : ℝ} (hhf : 0 < hf) (K : ℝ) :
    μ[fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (S ω + a (S ω) * hc + b (S ω) * (W ω + Real.sqrt hf * Z ω)) |
        MeasurableSpace.comap (fun ω => (S ω, W ω)) inferInstance] =ᵐ[μ]
      fun ω => cdf (gaussianReal 0 1) ((S ω + a (S ω) * hc + b (S ω) * W ω - K) /
        (|b (S ω)| * Real.sqrt hf)) := by
  have hsq : 0 < Real.sqrt hf := Real.sqrt_pos.2 hhf
  have hce := condExp_digital_last_step (hS.prodMk hW) hZ hind hZlaw
    (m := fun p : ℝ × ℝ => p.1 + a p.1 * hc + b p.1 * p.2) (s := fun p => b p.1 * Real.sqrt hf)
    ((measurable_fst.add ((ha.comp measurable_fst).mul_const hc)).add
      ((hb.comp measurable_fst).mul measurable_snd))
    ((hb.comp measurable_fst).mul_const _) (hb0.mono fun ω hω => mul_ne_zero hω hsq.ne') K
  have e : (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (S ω + a (S ω) * hc + b (S ω) * (W ω + Real.sqrt hf * Z ω))) =
      fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
        ((S ω + a (S ω) * hc + b (S ω) * W ω) + b (S ω) * Real.sqrt hf * Z ω) :=
    funext fun ω => by ring_nf
  rw [e]
  filter_upwards [hce] with ω hω
  rw [hω, abs_mul, abs_of_pos hsq]

/-- **Zero variance on the coarsest level** (Giles 2015, §5.2, p. 36: "One particularly
interesting feature of these results is that there is zero variance on the coarsest level. This
is because there is only one timestep on the coarsest level, and therefore the conditional
expectation is taken immediately and every sample gives the same payoff").  With one timestep of
size `h₀ > 0` from the deterministic `S₀` (and `b = b(S₀) ≠ 0`, `a = a(S₀)`), the conditional
expectation given the path before the last step (the constant `S₀`) is a.s. the constant
`p = Φ((S₀ + a h₀ − K)/(|b| √h₀))`, so `V_0 = 0`, whereas the unsmoothed digital payoff has variance
`p(1 − p) > 0`. -/
theorem digital_smoothing_level_zero {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZlaw : μ.map Z = gaussianReal 0 1) {S₀ a b h₀ : ℝ} (hb : b ≠ 0) (hh : 0 < h₀) (K : ℝ) :
    (μ[fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω) |
        MeasurableSpace.comap (fun _ : Ω => S₀) inferInstance] =ᵐ[μ]
        fun _ => cdf (gaussianReal 0 1) ((S₀ + a * h₀ - K) / (|b| * Real.sqrt h₀))) ∧
      variance (μ[fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω) |
        MeasurableSpace.comap (fun _ : Ω => S₀) inferInstance]) μ = 0 ∧
      variance (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω))
          μ = cdf (gaussianReal 0 1) ((S₀ + a * h₀ - K) / (|b| * Real.sqrt h₀)) *
            (1 - cdf (gaussianReal 0 1) ((S₀ + a * h₀ - K) / (|b| * Real.sqrt h₀))) ∧
      0 < cdf (gaussianReal 0 1) ((S₀ + a * h₀ - K) / (|b| * Real.sqrt h₀)) *
            (1 - cdf (gaussianReal 0 1) ((S₀ + a * h₀ - K) / (|b| * Real.sqrt h₀))) := by
  obtain ⟨h1, h2, -⟩ := digital_smoothing (X := fun _ : Ω => S₀) measurable_const hZ
    (indepFun_const_left S₀ Z) hZlaw (a := fun _ => a) (b := fun _ => b) measurable_const
    measurable_const (Eventually.of_forall fun _ => hb) hh K
  set p := cdf (gaussianReal 0 1) ((S₀ + a * h₀ - K) / (|b| * Real.sqrt h₀))
  have hconst : ∀ c : ℝ, variance (fun _ : Ω => c) μ = 0 := fun c => by
    rw [variance_eq_integral measurable_const.aemeasurable]
    simp
  refine ⟨h1, (variance_congr h1).trans (hconst p), ?_,
    mul_pos (cdf_stdGaussian_pos _) (sub_pos.2 (cdf_stdGaussian_lt_one _))⟩
  have hFm : Measurable fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω) :=
    (measurable_one.indicator measurableSet_Ioi).comp (measurable_const.add (hZ.const_mul _))
  have hFL : MemLp (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω)) 2 μ :=
    memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun ω => by
      rcases digital_eq_zero_or_one K (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω) with h | h <;>
        simp [h]) hFm.aestronglyMeasurable 2
  have hF2 : ∫ ω, ((Set.Ioi K).indicator (1 : ℝ → ℝ)
      (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω)) ^ 2 ∂μ =
      ∫ ω, (Set.Ioi K).indicator (1 : ℝ → ℝ) (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by
      rcases digital_eq_zero_or_one K (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω) with h | h <;>
        simp [h])
  have hmean : ∫ ω, (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (S₀ + a * h₀ + b * Real.sqrt h₀ * Z ω) ∂μ = p := by
    rw [← h2]
    simp
  rw [variance_eq_sub hFL]
  simp only [Pi.pow_apply]
  rw [hF2, hmean]
  ring

end CondExp

/-! ### §5.2: change of measure -/

/-- Integrability against `N(m, v)`, `v ≠ 0`, is integrability of `φ_{m,v} f` against Lebesgue
measure. -/
lemma integrable_gaussianReal_iff_mul_pdf {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal m v) ↔ Integrable (fun x => gaussianPDFReal m v x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

/-- **The Radon–Nikodym derivative between two Gaussian laws** (Giles 2015, §5.2, p. 38: "Using the
Euler-Maruyama approximation for the final timestep, the fine and coarse path conditional
distributions at maturity are two very similar Gaussian distributions. Instead of following the
splitting approach of taking corresponding samples from these two distributions, we can take a
sample from a third Gaussian distribution (with a mean and variance perhaps equal to the average of
the other two). This leads to the introduction of a Radon-Nikodym derivative for each path").  For
variances `v, v' ≠ 0`, `N(m', v') = L · N(m, v)` with `L = φ_{m',v'}/φ_{m,v}` the ratio of the
densities, and `L` is the Radon–Nikodym derivative `dN(m', v')/dN(m, v)` a.e. -/
theorem gaussian_change_of_measure {m m' : ℝ} {v v' : ℝ≥0} (hv : v ≠ 0) (hv' : v' ≠ 0) :
    gaussianReal m' v' =
        (gaussianReal m v).withDensity (fun z => gaussianPDF m' v' z / gaussianPDF m v z) ∧
      (gaussianReal m' v').rnDeriv (gaussianReal m v) =ᵐ[gaussianReal m v]
        fun z => gaussianPDF m' v' z / gaussianPDF m v z := by
  have hmeas : Measurable fun z => gaussianPDF m' v' z / gaussianPDF m v z :=
    (measurable_gaussianPDF _ _).div (measurable_gaussianPDF _ _)
  have h : gaussianReal m' v' =
      (gaussianReal m v).withDensity (fun z => gaussianPDF m' v' z / gaussianPDF m v z) := by
    rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv',
      ← withDensity_mul _ (measurable_gaussianPDF _ _) hmeas]
    congr 1
    funext z
    simp only [Pi.mul_apply]
    rw [ENNReal.mul_div_cancel (gaussianPDF_pos _ hv _).ne' gaussianPDF_ne_top]
  refine ⟨h, ?_⟩
  rw [h]
  exact Measure.rnDeriv_withDensity _ hmeas

/-- **The change of measure is unbiased** (Giles 2015, §5.2, p. 38: "we can take a sample from a
third Gaussian distribution … This leads to the introduction of a Radon-Nikodym derivative for each
path").  For `g` integrable under `N(m', v')` (`v, v' ≠ 0`), `g φ_{m',v'}/φ_{m,v}` is integrable
under `N(m, v)` and `E_{Z∼N(m,v)}[g(Z) φ_{m',v'}(Z)/φ_{m,v}(Z)] = E_{Z∼N(m',v')}[g(Z)]`: a sample of
the third Gaussian weighted by the Radon–Nikodym derivative has the conditional expectation of the
fine (or coarse) payoff, so the expectation of each level, and (2.4), are kept. -/
theorem integral_mul_likelihoodRatio {m m' : ℝ} {v v' : ℝ≥0} (hv : v ≠ 0) (hv' : v' ≠ 0)
    {g : ℝ → ℝ} (hg : Integrable g (gaussianReal m' v')) :
    Integrable (fun z => g z * (gaussianPDFReal m' v' z / gaussianPDFReal m v z))
        (gaussianReal m v) ∧
      ∫ z, g z * (gaussianPDFReal m' v' z / gaussianPDFReal m v z) ∂gaussianReal m v =
        ∫ z, g z ∂gaussianReal m' v' := by
  have e : ∀ z, gaussianPDFReal m v z * (g z * (gaussianPDFReal m' v' z / gaussianPDFReal m v z))
      = gaussianPDFReal m' v' z * g z := fun z => by
    have := (gaussianPDFReal_pos m v z hv).ne'
    field_simp
  refine ⟨?_, ?_⟩
  · rw [integrable_gaussianReal_iff_mul_pdf hv]
    simp only [e]
    exact (integrable_gaussianReal_iff_mul_pdf hv').1 hg
  · rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv']
    simp only [smul_eq_mul, e]

/-- **The fine–coarse difference is the difference of the Radon–Nikodym derivatives** (Giles 2015,
§5.2, p. 38: "the difference in the payoffs from the two paths is then due to the difference in
their Radon-Nikodym derivatives").  With a common sample `Z ∼ N(m, v)` and the fine and coarse
conditional laws `N(m_f, v_f)`, `N(m_c, v_c)` (all variances nonzero), the correction
`g(Z) (φ_{m_f,v_f}(Z)/φ_{m,v}(Z) − φ_{m_c,v_c}(Z)/φ_{m,v}(Z))` has the mean
`E_{N(m_f,v_f)}[g] − E_{N(m_c,v_c)}[g]` of the difference of the fine and coarse payoffs. -/
theorem integral_mul_sub_likelihoodRatio {m mf mc : ℝ} {v vf vc : ℝ≥0} (hv : v ≠ 0)
    (hvf : vf ≠ 0) (hvc : vc ≠ 0) {g : ℝ → ℝ} (hgf : Integrable g (gaussianReal mf vf))
    (hgc : Integrable g (gaussianReal mc vc)) :
    ∫ z, g z * (gaussianPDFReal mf vf z / gaussianPDFReal m v z -
        gaussianPDFReal mc vc z / gaussianPDFReal m v z) ∂gaussianReal m v =
      ∫ z, g z ∂gaussianReal mf vf - ∫ z, g z ∂gaussianReal mc vc := by
  obtain ⟨hif, hf⟩ := integral_mul_likelihoodRatio (m := m) hv hvf hgf
  obtain ⟨hic, hc⟩ := integral_mul_likelihoodRatio (m := m) hv hvc hgc
  simp only [mul_sub]
  rw [integral_sub hif hic, hf, hc]

/-! ### §5.4: the derivative of the call payoff -/

/-- **The derivative of the call payoff is discontinuous** (Giles 2015, §5.4, p. 42: "From a
multilevel Monte Carlo point of view, the difficulty that this introduces is that the derivative
of a call option payoff function is discontinuous. Hence, computing first order sensitivities for
a call option has similar difficulties to computing the option price for a digital option").  The
call payoff `f(x) = max(x − K, 0)` has the derivative `f′(x) = H(x − K) = 1_{x>K}` (the digital
payoff) at every `x ≠ K`, it is not differentiable at `K`, and no function continuous at `K` is a
derivative of `f` on `ℝ ∖ {K}`. -/
theorem hasDerivAt_call_payoff (K : ℝ) :
    (∀ x, x ≠ K → HasDerivAt (fun y => max (y - K) 0) ((Set.Ioi K).indicator 1 x) x) ∧
      ¬ DifferentiableAt ℝ (fun y => max (y - K) 0) K ∧
      ¬ ∃ g : ℝ → ℝ, ContinuousAt g K ∧
        ∀ x, x ≠ K → HasDerivAt (fun y => max (y - K) 0) (g x) x := by
  -- below `K` the payoff vanishes, above `K` it is `x − K`
  have hlt : ∀ x, x < K → HasDerivAt (fun y => max (y - K) 0) 0 x := by
    intro x hx
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact max_eq_right (by linarith [Set.mem_Iio.1 hy])
  have hgt : ∀ x, K < x → HasDerivAt (fun y => max (y - K) 0) 1 x := by
    intro x hx
    refine ((hasDerivAt_id x).sub_const K).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact max_eq_left (by linarith [Set.mem_Ioi.1 hy])
  -- the one-sided derivatives at `K` are `0` and `1`
  have hleft : ∀ d, HasDerivWithinAt (fun y => max (y - K) 0) d (Set.Iio K) K → d = 0 := by
    intro d hd
    have h0 : HasDerivWithinAt (fun y => max (y - K) 0) 0 (Set.Iio K) K := by
      refine (hasDerivWithinAt_const K (Set.Iio K) (0 : ℝ)).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact max_eq_right (by linarith [Set.mem_Iio.1 hy])
      · simp
    exact (uniqueDiffWithinAt_Iio K).eq_deriv _ hd h0
  have hright : ∀ d, HasDerivWithinAt (fun y => max (y - K) 0) d (Set.Ioi K) K → d = 1 := by
    intro d hd
    have h1 : HasDerivWithinAt (fun y => max (y - K) 0) 1 (Set.Ioi K) K := by
      refine ((hasDerivAt_id K).sub_const K).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact max_eq_left (by linarith [Set.mem_Ioi.1 hy])
      · simp
    exact (uniqueDiffWithinAt_Ioi K).eq_deriv _ hd h1
  refine ⟨fun x hx => ?_, fun hd => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hx with h | h
    · rw [Set.indicator_of_notMem (by simp [h.le])]
      exact hlt x h
    · rw [Set.indicator_of_mem (by simpa using h), Pi.one_apply]
      exact hgt x h
  · have h0 := hleft _ hd.hasDerivAt.hasDerivWithinAt
    have h1 := hright _ hd.hasDerivAt.hasDerivWithinAt
    rw [h0] at h1
    exact zero_ne_one h1
  · rintro ⟨g, hgK, hg⟩
    have hgl : ∀ x, x < K → g x = 0 := fun x hx => (hg x hx.ne).unique (hlt x hx)
    have hgr : ∀ x, K < x → g x = 1 := fun x hx => (hg x hx.ne').unique (hgt x hx)
    have hl : Tendsto g (𝓝[<] K) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (hgl x hx).symm)
    have hr : Tendsto g (𝓝[>] K) (𝓝 1) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (hgr x hx).symm)
    have e0 := tendsto_nhds_unique (hgK.tendsto.mono_left nhdsWithin_le_nhds) hl
    have e1 := tendsto_nhds_unique (hgK.tendsto.mono_left nhdsWithin_le_nhds) hr
    rw [e0] at e1
    exact zero_ne_one e1

end MLMC
