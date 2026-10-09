import MlmcLean.GBMStrongLp

/-!
# The digital option for GBM with Euler–Maruyama: the endpoint `O(h^{1/2} log h)` of Table 5.2
(Giles 2015, §5.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1
"Euler-Maruyama discretisation", p. 33, Table 5.2 (l. 1425–1434 of `docs/giles2015.txt`),
"Observed and theoretical convergence rates for the multilevel correction variance for scalar
SDEs, using the Euler-Maruyama and Milstein discretisations" (l. 1432–1434), row "digital"
(l. 1431): Euler–Maruyama numerics "`O(h^{1/2})`", analysis "`O(h^{1/2} log h)`"; "the digital
option analysis is due to Avikainen (Avikainen 2009)" (l. 1457–1458).  The text of p. 33
(l. 1436–1445): "noting that the strong error is `O(h_ℓ^{1/2})`, and there is a bounded density of
paths terminating in the neighbourhood of `K`, there is therefore an `O(h_ℓ^{1/2})` fraction of the
samples with the coarse and fine paths on either side of the strike, with `P_ℓ−P_{ℓ−1} = ±1`. This
gives `V_ℓ = O(h^{1/2})` … Furthermore, `E[(P_ℓ−P_{ℓ−1})⁴] = O(h_ℓ^{1/2})`".  The setting is that
of `MlmcLean.GBMEulerMaruyama`: geometric Brownian motion `dS = rS dt + σS dW` (l. 1327–1330), the
exact solution `S_T` and the Euler–Maruyama paths driven by the same independent increments
`Z_i ∼ N(0,1)` (`stdNormalSeq`), the coarse path driven by `(Z_{2k} + Z_{2k+1})/√2` (`pairAvg`),
and the digital payoff `H(S_T − K)` (l. 1357–1359), written `(Set.Ioi K).indicator 1`.

**What is proved.**  `MlmcLean.GBMStrongLp` (`gbm_em_digital_rate`) gives `O(h^q)` for every
`q < ½`.  This file proves the endpoint with Avikainen's logarithm, in the slightly stronger form
`(h log(1/h))^{1/2} ≤ h^{1/2} log(1/h)`:
* `gbm_em_exact_mismatch_le`: one level `n` against the exact solution, with explicit constants:
  for `h = T 2^{−n}`, `D = σ² + r²T`, `S_0 ≠ 0`, `σ ≠ 0`, `T > 0` and every strike `K`,
  `P(1_{S_T>K} ≠ 1_{Ŝ_n>K}) ≤ 48 T h D² + 2h/T + 2 (T (r²h/2 + 6D (hD)^{1/2})`
  `+ 160 D (T h n log 2)^{1/2}) / (|σ| (2πT)^{1/2})`, which is `O((h log(T/h))^{1/2})`.
* `gbm_em_digital_endpoint`: there is `C`, depending only on `r`, `σ` and `T`, such that for every
  `S_0`, every strike `K` and every level `ℓ` the correction
  `ΔP_ℓ = H(Ŝ^f_{ℓ+1} − K) − H(Ŝ^c_ℓ − K)` has `V[ΔP_ℓ]`, `P(ΔP_ℓ ≠ 0)` and `E[ΔP_ℓ⁴]` at most
  `C (h_{ℓ+1} (ℓ + 1))^{1/2}`, `h_{ℓ+1} = T 2^{−(ℓ+1)}`; note `(ℓ + 1) log 2 = log(T/h_{ℓ+1})`.
* `gbm_em_digital_endpoint_log`: the same bound `C (h log(1/h))^{1/2}` with the paper's `log(1/h)`
  for the levels with `h = h_{ℓ+1} < e^{−1}`, and `(h log(1/h))^{1/2} ≤ h^{1/2} log(1/h)`: Table
  5.2's analysis rate `O(h^{1/2} log h)` for `V_ℓ` (and for `E[ΔP_ℓ⁴]`).

**The route.**  If the fine and the coarse payoff differ, one of them differs from the payoff of
the exact solution (`gbm_em_pair_mismatch_le`), so it suffices to compare one Euler–Maruyama path
`Ŝ_n = S_0 ∏_i (1 + u_i)`, `u_i = rh + σ√h Z_i`, with `S_T = S_0 ∏_i e^{u_i − σ²h/2}`.
* Off the event that some `u_i ≤ −½`, which has probability at most `48 T h D²` (Markov's
  inequality for `u_i⁴` and a union bound), both paths have the sign of `S_0`, and if the payoffs
  differ then `log|K|` lies between `log|S_T|` and `log|Ŝ_n|`, so `|log|S_T| − log|K||` is at most
  `|∑_i ψ(Z_i)|`, `ψ = log(1 + u) − u + σ²h/2` the one-step log-ratio (`logRatioStep`,
  `abs_log_sub_log_le_of_digital_ne`).
* `log|S_T|` is Gaussian with standard deviation `|σ|√T`, so the bounded density near the strike
  becomes `P(|log|S_T| − log|K|| ≤ δ) ≤ 2δ/(|σ| (2πT)^{1/2})`, uniformly in `S_0` and `K`
  (`gbmExact_logSmallBall`).
* The log error `∑_i ψ(Z_i)` has Gaussian-type tails, by Chernoff's bound: `E[ψ] = O(h^{3/2})`
  (the terms of order `h` cancel), and `E[e^{sψ}] ≤ 1 + |s| m + 4096 s² V²` for `|s| V ≤ 1/32`,
  `V = hD`, `m = r²h²/2 + 6V^{3/2}` (`integrable_and_integral_exp_mul_logRatioStep_le`, from
  `e^y ≤ 1 + y + y² e^{|y|}`, `|ψ| ≤ σ²h/2 + 2u²` and `E[e^{aZ²}] = (1 − 2a)^{−1/2}`).  With
  `t = (log(T/h)/(Th))^{1/2}/(32D)` and `δ = T(r²h/2 + 6D(hD)^{1/2}) + 160 D (Th log(T/h))^{1/2}`
  both tails are at most `e^{−log(T/h)} = h/T` (`measureReal_le_sum_logRatioStep`,
  `gbm_em_exact_mismatch_le`).  These tails of the *log* error replace the Gaussian tails of the
  error itself, the hypothesis of `digital_mismatch_le_of_tail`, which fail for GBM.

**Deviations.**  `σ ≠ 0` (it cannot be dropped, see `gbm_em_digital_rate`) and `T > 0`; `S_0` and
`K` are arbitrary reals (for `S_0 = 0`, `K = 0` or `K` of the other sign than `S_0` the payoffs can
only differ where some `u_i ≤ −½`).  The logarithm in `gbm_em_digital_endpoint` is
`log(T/h_{ℓ+1}) = (ℓ + 1) log 2`, which needs no restriction on the level;
`gbm_em_digital_endpoint_log` uses the paper's `log(1/h)`, for `h < e^{−1}`, with a constant that
also depends on `|log T|`.  The factor `10 e^{−rT}` of the paper's payoff is omitted (it multiplies
`V_ℓ` by `100 e^{−2rT}`).  The proof uses the product form of both GBM paths; it is not
Avikainen's argument, which covers general scalar SDEs.

**The constants** are explicit and far from sharp: `gbm_em_digital_endpoint` takes
`C = (1 + √2)(A + B)`, `A = 48 T^{3/2} D² + (T r² + 12 T^{1/2} D^{3/2})/(|σ|√(2π)) + 2/√T`,
`B = 320 D/(|σ|√(2π))`.  At the paper's `r = 0.05`, `σ = 0.2`, `T = 1` (l. 1329–1330) this is
`C ≈ 71`, and `C (h_{ℓ+1} (ℓ + 1))^{1/2} < 1` only from level `ℓ = 16` on, while a Monte Carlo
estimate (`2·10⁵` samples, not part of the proof) of `P(ΔP_ℓ ≠ 0)` for `S_0 = K = 100` is about
`0.019, 0.014, 0.008, 0.004` at `ℓ = 0, 2, 4, 6` (roughly `0.04 h_{ℓ+1}^{1/2}` on the finer
levels).

**Not proved.**  The observed rate `O(h^{1/2})` without the logarithm (Table 5.2, numerics
column); the kurtosis `O(h_ℓ^{−1/2})` (l. 1444–1445), which needs a lower bound on `P(ΔP_ℓ ≠ 0)`;
Avikainen's result for general scalar SDEs; the Milstein column of Table 5.2.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### Gaussian and elementary inequalities -/

/-- `φ(x) e^{ax²} = e^{−(1/2 − a)x²}/√(2π)` for the standard normal density `φ` (the moment
generating function of `Z²`, used for the tails of the log error of the Euler–Maruyama scheme for
GBM, Giles 2015, §5.1, p. 33, Table 5.2). -/
lemma gaussianPDFReal_mul_exp_sq (a x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (a * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - a) * x ^ 2) := by
  rw [gaussianPDFReal, mul_assoc, ← Real.exp_add]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

/-- `e^{aZ²}` is integrable for `Z ∼ N(0,1)` and `a < ½`. -/
lemma integrable_exp_mul_sq_gaussian {a : ℝ} (ha : a < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (a * x ^ 2)) (gaussianReal 0 1) := by
  rw [integrable_gaussianReal_iff_mul_pdf one_ne_zero]
  simp_rw [gaussianPDFReal_mul_exp_sq]
  exact (integrable_exp_neg_mul_sq (by linarith : (0 : ℝ) < 1 / 2 - a)).const_mul _

/-- `E[e^{aZ²}] = (1 − 2a)^{−1/2}` for `Z ∼ N(0,1)` and `a < ½` (the moment generating function of
the `χ²` law with one degree of freedom). -/
lemma integral_exp_mul_sq_gaussian {a : ℝ} (ha : a < 1 / 2) :
    ∫ x, Real.exp (a * x ^ 2) ∂gaussianReal 0 1 = (Real.sqrt (1 - 2 * a))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [smul_eq_mul, gaussianPDFReal_mul_exp_sq]
  rw [integral_const_mul, integral_gaussian]
  have h1 : 0 < 1 - 2 * a := by linarith
  have h2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h3 : 0 < Real.sqrt (1 - 2 * a) := Real.sqrt_pos.2 h1
  rw [show Real.pi / (1 / 2 - a) = (2 * Real.pi) / (1 - 2 * a) by field_simp,
    Real.sqrt_div' _ h1.le]
  field_simp

/-- `E[e^{aZ²}] ≤ √2` for `Z ∼ N(0,1)` and `a ≤ ¼`. -/
lemma integral_exp_mul_sq_gaussian_le {a : ℝ} (ha : a ≤ 1 / 4) :
    ∫ x, Real.exp (a * x ^ 2) ∂gaussianReal 0 1 ≤ Real.sqrt 2 := by
  rw [integral_exp_mul_sq_gaussian (by linarith)]
  have h1 : 1 / 2 ≤ 1 - 2 * a := by linarith
  have h3 : 0 < Real.sqrt (1 - 2 * a) := Real.sqrt_pos.2 (by linarith)
  have h4 : Real.sqrt 2 * Real.sqrt (1 - 2 * a) ≥ 1 := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.one_le_sqrt.2 (by linarith)
  rw [inv_le_iff_one_le_mul₀ h3]
  linarith

/-- `log(1 + u) ≤ u` for `u > −1`. -/
lemma log_one_add_le (u : ℝ) (hu : -1 < u) : Real.log (1 + u) ≤ u := by
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + u)
  linarith

/-- `u − 2u² ≤ log(1 + u)` for `u ≥ −½`. -/
lemma sub_two_mul_sq_le_log_one_add {u : ℝ} (hu : -(1 / 2) ≤ u) :
    u - 2 * u ^ 2 ≤ Real.log (1 + u) := by
  rcases le_or_gt 0 u with h0 | h0
  · have h1 := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + u)
    have h2 : u - 2 * u ^ 2 ≤ 1 - (1 + u)⁻¹ := by
      rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring, le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg u, mul_nonneg h0 (sq_nonneg u)]
    linarith
  · have hx : |-u| < 1 := by rw [abs_of_pos (by linarith)]; linarith
    have h := Real.abs_log_sub_add_sum_range_le hx 1
    simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one, sub_neg_eq_add,
      abs_neg] at h
    rw [abs_of_neg h0, add_comm 1 u] at h
    rw [add_comm 1 u]
    have h3 : u ^ 2 / (1 - -u) ≤ 2 * u ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg u]
    have h4 := (abs_le.1 h).1
    rw [neg_sq] at h4
    nlinarith

/-- `|log(1 + u) − u + u²/2| ≤ 3|u|³` for `u ≥ −½` (the second-order Taylor remainder of the
logarithm). -/
lemma abs_log_one_add_sub_quadratic_le {u : ℝ} (hu : -(1 / 2) ≤ u) :
    |Real.log (1 + u) - u + u ^ 2 / 2| ≤ 3 * |u| ^ 3 := by
  rcases le_or_gt u (1 / 2) with h1 | h1
  · have hx : |-u| < 1 := by rw [abs_neg]; exact (abs_le.2 ⟨hu, h1⟩).trans_lt (by norm_num)
    have h := Real.abs_log_sub_add_sum_range_le hx 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
    norm_num at h
    have hu' : |u| ≤ 1 / 2 := abs_le.2 ⟨hu, h1⟩
    have e : -u + u ^ 2 / 2 + Real.log (1 + u) = Real.log (1 + u) - u + u ^ 2 / 2 := by ring
    rw [e] at h
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg (abs_nonneg u) 3]
  · have h0 : 0 ≤ u := by linarith
    have hl1 := log_one_add_le u (by linarith)
    have h2 : u - u ^ 2 ≤ Real.log (1 + u) := by
      have h1 := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + u)
      have h2 : u - u ^ 2 ≤ 1 - (1 + u)⁻¹ := by
        rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring, le_div_iff₀ (by linarith)]
        nlinarith [sq_nonneg u, mul_nonneg h0 (sq_nonneg u)]
      linarith
    rw [abs_of_nonneg h0]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg u, mul_nonneg h0 (sq_nonneg u)]

/-! ### The one-step log-ratio of the Euler–Maruyama and the exact step -/

/-- The logarithm of the ratio of one Euler–Maruyama step of geometric Brownian motion to the exact
step driven by the same increment (Giles 2015, §5.1): with `u = a + bx` (for GBM `a = rh`,
`b = σ√h`), the Euler–Maruyama factor is `1 + u` and the exact factor `e^{u − b²/2}`, so the
logarithm of their ratio (the difference of their logarithms) is `log(1 + u) − u + b²/2`; this is
the value where `1 + u > ½`, and elsewhere the value is the second-order approximation
`(b² − u²)/2`. -/
noncomputable def logRatioStep (a b x : ℝ) : ℝ :=
  if -(1 / 2) < a + b * x then Real.log (1 + (a + b * x)) - (a + b * x) + b ^ 2 / 2
  else (b ^ 2 - (a + b * x) ^ 2) / 2

/-- The one-step log-ratio is measurable. -/
lemma measurable_logRatioStep (a b : ℝ) : Measurable (logRatioStep a b) := by
  unfold logRatioStep
  exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop)
    (by fun_prop)

/-- `|ψ(x)| ≤ b²/2 + 2(a + bx)²` for the one-step log-ratio `ψ`. -/
lemma abs_logRatioStep_le (a b x : ℝ) :
    |logRatioStep a b x| ≤ b ^ 2 / 2 + 2 * (a + b * x) ^ 2 := by
  unfold logRatioStep
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  have hu : 0 ≤ (a + b * x) ^ 2 := sq_nonneg _
  split_ifs with h
  · have h1 := log_one_add_le (a + b * x) (by linarith)
    have h2 := sub_two_mul_sq_le_log_one_add h.le
    rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-- The one-step log-ratio is `(b² − u²)/2` up to `3|u|³`, `u = a + bx`. -/
lemma abs_logRatioStep_sub_le (a b x : ℝ) :
    |logRatioStep a b x - (b ^ 2 - (a + b * x) ^ 2) / 2| ≤ 3 * |a + b * x| ^ 3 := by
  unfold logRatioStep
  split_ifs with h
  · have e : Real.log (1 + (a + b * x)) - (a + b * x) + b ^ 2 / 2 - (b ^ 2 - (a + b * x) ^ 2) / 2
        = Real.log (1 + (a + b * x)) - (a + b * x) + (a + b * x) ^ 2 / 2 := by ring
    rw [e]
    exact abs_log_one_add_sub_quadratic_le h.le
  · rw [sub_self, abs_zero]
    positivity

/-- `E[(a + bZ)²] = a² + b²` for `Z ∼ N(0,1)`. -/
lemma integral_affine_sq (a b : ℝ) :
    ∫ x, (a + b * x) ^ 2 ∂gaussianReal 0 1 = a ^ 2 + b ^ 2 := by
  have m1 := integral_affine_pow_one a b
  have m2 := integral_affine_pow_add_two a b 0
  simp only [zero_add, pow_zero, integral_const, probReal_univ, one_smul, Nat.cast_zero,
    one_mul] at m2 m1
  rw [m2, m1]
  ring

/-- `E[(a + bZ)⁴] = a⁴ + 6a²b² + 3b⁴` for `Z ∼ N(0,1)`. -/
lemma integral_affine_four (a b : ℝ) :
    ∫ x, (a + b * x) ^ 4 ∂gaussianReal 0 1 = a ^ 4 + 6 * a ^ 2 * b ^ 2 + 3 * b ^ 4 := by
  have m1 := integral_affine_pow_one a b
  have m2 := integral_affine_sq a b
  have m3 := integral_affine_pow_add_two a b 1
  have m4 := integral_affine_pow_add_two a b 2
  simp only [pow_one] at m1
  norm_num at m3 m4
  rw [m4, m3, m2, m1]
  ring

/-- `E[(a + bZ)⁴] ≤ 3V²` for `Z ∼ N(0,1)` if `a² + b² ≤ V`. -/
lemma integral_affine_four_le {a b V : ℝ} (hV : a ^ 2 + b ^ 2 ≤ V) :
    ∫ x, (a + b * x) ^ 4 ∂gaussianReal 0 1 ≤ 3 * V ^ 2 := by
  rw [integral_affine_four]
  have h0 : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg (sq_nonneg a) (sq_nonneg b)]

/-- `P(a + bZ ≤ −½) ≤ 16 E[(a + bZ)⁴] ≤ 48V²` for `Z ∼ N(0,1)` and `a² + b² ≤ V` (Markov's
inequality): an Euler–Maruyama factor `1 + rh + σ√h Z` of GBM below `½` is rare. -/
lemma measureReal_affine_le_neg_half_le {a b V : ℝ} (hV : a ^ 2 + b ^ 2 ≤ V) :
    (gaussianReal 0 1).real {x | a + b * x ≤ -(1 / 2)} ≤ 48 * V ^ 2 := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := gaussianReal 0 1)
    (Eventually.of_forall fun x => (by positivity : (0 : ℝ) ≤ (a + b * x) ^ 4))
    (integrable_affine_pow_gaussian a b 4) (1 / 16)
  have hsub : {x | a + b * x ≤ -(1 / 2)} ⊆ {x | (1 / 16 : ℝ) ≤ (a + b * x) ^ 4} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    nlinarith [sq_nonneg (a + b * x), sq_nonneg ((a + b * x) ^ 2 - 1 / 4)]
  have h4 := integral_affine_four_le hV
  have hm := measureReal_mono (μ := gaussianReal 0 1) hsub
  nlinarith

/-- `|u|³ ≤ (c²u² + u⁴)/(2c)` for `c > 0`. -/
lemma abs_pow_three_le (c u : ℝ) (hc : 0 < c) : |u| ^ 3 ≤ (c ^ 2 * u ^ 2 + u ^ 4) / (2 * c) := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  have h2 : u ^ 4 = (|u| ^ 2) ^ 2 := by rw [← h1]; ring
  rw [h1, h2]
  nlinarith [sq_nonneg (c * |u| - |u| ^ 2), abs_nonneg u]

/-- `|a + bZ|³` is integrable for `Z ∼ N(0,1)`. -/
lemma integrable_abs_affine_pow_three (a b : ℝ) :
    Integrable (fun x => |a + b * x| ^ 3) (gaussianReal 0 1) := by
  refine Integrable.mono' (((integrable_affine_pow_gaussian a b 2).const_mul 1).add
    (integrable_affine_pow_gaussian a b 4)) (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := abs_pow_three_le 1 (a + b * x) one_pos
  simp only [one_pow, one_mul, mul_one, Pi.add_apply] at this ⊢
  nlinarith [sq_nonneg (a + b * x), pow_nonneg (sq_nonneg (a + b * x)) 2]

/-- `E|a + bZ|³ ≤ 2V^{3/2}` for `Z ∼ N(0,1)` and `a² + b² ≤ V`. -/
lemma integral_abs_affine_pow_three_le {a b V : ℝ} (hVp : 0 < V) (hV : a ^ 2 + b ^ 2 ≤ V) :
    ∫ x, |a + b * x| ^ 3 ∂gaussianReal 0 1 ≤ 2 * V * Real.sqrt V := by
  have hc : 0 < Real.sqrt V := Real.sqrt_pos.2 hVp
  have hint : Integrable (fun x => (Real.sqrt V ^ 2 * (a + b * x) ^ 2 + (a + b * x) ^ 4) /
      (2 * Real.sqrt V)) (gaussianReal 0 1) :=
    (((integrable_affine_pow_gaussian a b 2).const_mul _).add
      (integrable_affine_pow_gaussian a b 4)).div_const _
  calc ∫ x, |a + b * x| ^ 3 ∂gaussianReal 0 1
      ≤ ∫ x, (Real.sqrt V ^ 2 * (a + b * x) ^ 2 + (a + b * x) ^ 4) / (2 * Real.sqrt V)
          ∂gaussianReal 0 1 :=
        integral_mono (integrable_abs_affine_pow_three a b) hint
          fun x => abs_pow_three_le _ _ hc
    _ = (Real.sqrt V ^ 2 * (a ^ 2 + b ^ 2) + ∫ x, (a + b * x) ^ 4 ∂gaussianReal 0 1) /
          (2 * Real.sqrt V) := by
        rw [integral_div, integral_add ((integrable_affine_pow_gaussian a b 2).const_mul _)
          (integrable_affine_pow_gaussian a b 4), integral_const_mul, integral_affine_sq]
    _ ≤ (Real.sqrt V ^ 2 * V + 3 * V ^ 2) / (2 * Real.sqrt V) := by
        gcongr
        exact integral_affine_four_le hV
    _ = 2 * V * Real.sqrt V := by
        rw [Real.sq_sqrt hVp.le]
        field_simp
        rw [Real.sq_sqrt hVp.le]
        ring

/-- The one-step log-ratio `ψ(Z)` is integrable for `Z ∼ N(0,1)`. -/
lemma integrable_logRatioStep (a b : ℝ) :
    Integrable (logRatioStep a b) (gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_const (b ^ 2 / 2)).add
    ((integrable_affine_pow_gaussian a b 2).const_mul 2))
    (measurable_logRatioStep a b).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_logRatioStep_le a b x

/-- **The mean of the one-step log-ratio is of order `h^{3/2}`** (Giles 2015, §5.1, Table 5.2):
`|E[ψ(Z)]| ≤ a²/2 + 6V^{3/2}` for `a² + b² ≤ V`.  The terms of order `h` cancel, since
`E[(b² − (a + bZ)²)/2] = −a²/2`; the rest is bounded by `3E|a + bZ|³`. -/
lemma abs_integral_logRatioStep_le {a b V : ℝ} (hVp : 0 < V) (hV : a ^ 2 + b ^ 2 ≤ V) :
    |∫ x, logRatioStep a b x ∂gaussianReal 0 1| ≤ a ^ 2 / 2 + 6 * (V * Real.sqrt V) := by
  set q : ℝ → ℝ := fun x => (b ^ 2 - (a + b * x) ^ 2) / 2 with hqdef
  have hq : Integrable q (gaussianReal 0 1) :=
    ((integrable_const _).sub (integrable_affine_pow_gaussian a b 2)).div_const 2
  have hψ := integrable_logRatioStep a b
  have e : ∫ x, logRatioStep a b x ∂gaussianReal 0 1 =
      ∫ x, q x ∂gaussianReal 0 1 + ∫ x, (logRatioStep a b x - q x) ∂gaussianReal 0 1 := by
    rw [← integral_add hq (by exact hψ.sub hq :
      Integrable (fun x => logRatioStep a b x - q x) (gaussianReal 0 1))]
    congr 1
    funext x
    ring
  have eq : ∫ x, q x ∂gaussianReal 0 1 = -(a ^ 2 / 2) := by
    rw [hqdef, integral_div, integral_sub (integrable_const _)
      (integrable_affine_pow_gaussian a b 2), integral_const, integral_affine_sq]
    simp only [probReal_univ, one_smul]
    ring
  have hd : |∫ x, (logRatioStep a b x - q x) ∂gaussianReal 0 1| ≤ 6 * (V * Real.sqrt V) := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |logRatioStep a b x - q x| ∂gaussianReal 0 1
        ≤ ∫ x, 3 * |a + b * x| ^ 3 ∂gaussianReal 0 1 :=
          integral_mono (hψ.sub hq).abs ((integrable_abs_affine_pow_three a b).const_mul 3)
            fun x => abs_logRatioStep_sub_le a b x
      _ = 3 * ∫ x, |a + b * x| ^ 3 ∂gaussianReal 0 1 := integral_const_mul _ _
      _ ≤ 3 * (2 * V * Real.sqrt V) := by
          gcongr
          exact integral_abs_affine_pow_three_le hVp hV
      _ = 6 * (V * Real.sqrt V) := by ring
  rw [e, eq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_of_nonneg (by positivity)]
  linarith

/-- `e^{1/4} √2 ≤ 2`. -/
lemma exp_quarter_mul_sqrt_two_le : Real.exp (1 / 4) * Real.sqrt 2 ≤ 2 := by
  have h1 : Real.exp (1 / 4) ≤ 1 + 1 / 4 + (1 / 4) ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := 1 / 4) (by norm_num [abs_of_pos])
    have := (abs_le.1 h).2
    linarith
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [Real.exp_pos (1 / 4)]

/-- **The moment generating function of the one-step log-ratio** (Giles 2015, §5.1, Table 5.2):
for `a² + b² ≤ V`, `V > 0` and `|s| V ≤ 1/32`, `e^{sψ(Z)}` is integrable and
`E[e^{sψ(Z)}] ≤ 1 + |s| (a²/2 + 6V^{3/2}) + 4096 s² V²`.  Proof:
`e^y ≤ 1 + y + y² max(1, e^y)` (`exp_sub_one_sub_le_sq_mul_max`), `|ψ| ≤ w = b²/2 + 2(a + bZ)²`,
`w² ≤ 2048 V² e^{w/(32V)}` and `E[e^{κZ²}] ≤ √2` for `κ ≤ ¼`. -/
lemma integrable_and_integral_exp_mul_logRatioStep_le {a b V s : ℝ} (hVp : 0 < V)
    (hV : a ^ 2 + b ^ 2 ≤ V) (hs : |s| * V ≤ 1 / 32) :
    Integrable (fun x => Real.exp (s * logRatioStep a b x)) (gaussianReal 0 1) ∧
      ∫ x, Real.exp (s * logRatioStep a b x) ∂gaussianReal 0 1 ≤
        1 + |s| * (a ^ 2 / 2 + 6 * (V * Real.sqrt V)) + 4096 * s ^ 2 * V ^ 2 := by
  set w : ℝ → ℝ := fun x => b ^ 2 / 2 + 2 * (a + b * x) ^ 2 with hwdef
  set lam := 1 / (32 * V) + |s| with hlam
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hlam0 : 0 ≤ lam := by positivity
  have hlamV : lam * V ≤ 1 / 16 := by
    rw [hlam, add_mul, div_mul_eq_mul_div, one_mul, div_eq_mul_inv]
    rw [mul_inv, ← mul_assoc, mul_comm V, mul_assoc, mul_inv_cancel₀ hVp.ne', mul_one]
    linarith
  have ha2 : a ^ 2 ≤ V := by nlinarith [sq_nonneg b]
  have hb2 : b ^ 2 ≤ V := by nlinarith [sq_nonneg a]
  set κ := 4 * lam * b ^ 2 with hκ
  have hκ4 : κ ≤ 1 / 4 := by
    rw [hκ]
    nlinarith [mul_le_mul_of_nonneg_left hb2 hlam0]
  have hw0 : ∀ x, 0 ≤ w x := fun x => by positivity
  have hwle : ∀ x, lam * w x ≤ 1 / 4 + κ * x ^ 2 := fun x => by
    have h1 : (a + b * x) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 * x ^ 2 := by
      nlinarith [sq_nonneg (a - b * x)]
    have h2 : lam * (b ^ 2 / 2 + 4 * a ^ 2) ≤ 1 / 4 := by
      nlinarith [mul_le_mul_of_nonneg_left ha2 hlam0, mul_le_mul_of_nonneg_left hb2 hlam0]
    simp only [hwdef, hκ]
    nlinarith [mul_le_mul_of_nonneg_left h1 hlam0]
  have hintκ : Integrable (fun x : ℝ => Real.exp (κ * x ^ 2)) (gaussianReal 0 1) :=
    integrable_exp_mul_sq_gaussian (by linarith)
  have hwm : Measurable w := by rw [hwdef]; fun_prop
  have hintw : Integrable (fun x => Real.exp (lam * w x)) (gaussianReal 0 1) := by
    refine Integrable.mono' (hintκ.const_mul (Real.exp (1 / 4)))
      (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.2 (hwle x)
  have hEw : ∫ x, Real.exp (lam * w x) ∂gaussianReal 0 1 ≤ 2 := by
    calc ∫ x, Real.exp (lam * w x) ∂gaussianReal 0 1
        ≤ ∫ x, Real.exp (1 / 4) * Real.exp (κ * x ^ 2) ∂gaussianReal 0 1 :=
          integral_mono hintw (hintκ.const_mul _) fun x => by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.2 (hwle x)
      _ = Real.exp (1 / 4) * ∫ x, Real.exp (κ * x ^ 2) ∂gaussianReal 0 1 :=
          integral_const_mul _ _
      _ ≤ Real.exp (1 / 4) * Real.sqrt 2 := by
          gcongr
          exact integral_exp_mul_sq_gaussian_le hκ4
      _ ≤ 2 := exp_quarter_mul_sqrt_two_le
  -- pointwise bounds
  have hψw : ∀ x, |logRatioStep a b x| ≤ w x := fun x => abs_logRatioStep_le a b x
  have hpt : ∀ x, Real.exp (s * logRatioStep a b x) ≤
      1 + s * logRatioStep a b x + 2048 * V ^ 2 * s ^ 2 * Real.exp (lam * w x) := by
    intro x
    set y := s * logRatioStep a b x with hy
    have hT := (exp_sub_one_sub_le_sq_mul_max y).2
    have hyw : |y| ≤ |s| * w x := by
      rw [hy, abs_mul]
      exact mul_le_mul_of_nonneg_left (hψw x) hs0
    have hmax : max 1 (Real.exp y) ≤ Real.exp (|s| * w x) := by
      refine max_le (Real.one_le_exp (by positivity)) (Real.exp_le_exp.2 ?_)
      exact (le_abs_self y).trans hyw
    have hy2 : y ^ 2 ≤ s ^ 2 * w x ^ 2 := by
      have h1 : logRatioStep a b x ^ 2 ≤ w x ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hψw x) 2
      rw [hy, mul_pow]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
    have hw2 : w x ^ 2 ≤ 2048 * V ^ 2 * Real.exp (w x / (32 * V)) := by
      have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ w x / (32 * V))
      have e : (w x / (32 * V)) ^ 2 = w x ^ 2 / (1024 * V ^ 2) := by field_simp; ring
      have hpos : 0 < 1024 * V ^ 2 := by positivity
      have h3 : w x ^ 2 / (1024 * V ^ 2) ≤ 2 * Real.exp (w x / (32 * V)) := by
        have := hw0 x
        nlinarith [show 0 ≤ w x / (32 * V) by positivity]
      rw [div_le_iff₀ hpos] at h3
      nlinarith
    have he : Real.exp (w x / (32 * V)) * Real.exp (|s| * w x) = Real.exp (lam * w x) := by
      rw [← Real.exp_add, hlam]
      congr 1
      field_simp
    calc Real.exp y = 1 + y + (Real.exp y - 1 - y) := by ring
      _ ≤ 1 + y + y ^ 2 * max 1 (Real.exp y) := by linarith
      _ ≤ 1 + y + s ^ 2 * w x ^ 2 * Real.exp (|s| * w x) := by
          gcongr
      _ ≤ 1 + y + s ^ 2 * (2048 * V ^ 2 * Real.exp (w x / (32 * V))) *
            Real.exp (|s| * w x) := by gcongr
      _ = 1 + y + 2048 * V ^ 2 * s ^ 2 * Real.exp (lam * w x) := by
          rw [← he]
          ring
  have hint : Integrable (fun x => Real.exp (s * logRatioStep a b x)) (gaussianReal 0 1) := by
    refine Integrable.mono' hintw
      (by have := measurable_logRatioStep a b; fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    calc |s| * |logRatioStep a b x| ≤ |s| * w x := mul_le_mul_of_nonneg_left (hψw x) hs0
      _ ≤ lam * w x := by
          have : |s| ≤ lam := by rw [hlam]; linarith [show 0 ≤ 1 / (32 * V) by positivity]
          exact mul_le_mul_of_nonneg_right this (hw0 x)
  refine ⟨hint, ?_⟩
  have hψi := integrable_logRatioStep a b
  have hR : Integrable (fun x => 1 + s * logRatioStep a b x +
      2048 * V ^ 2 * s ^ 2 * Real.exp (lam * w x)) (gaussianReal 0 1) :=
    ((integrable_const 1).add (hψi.const_mul s)).add (hintw.const_mul _)
  have hmean := abs_integral_logRatioStep_le hVp hV
  calc ∫ x, Real.exp (s * logRatioStep a b x) ∂gaussianReal 0 1
      ≤ ∫ x, (1 + s * logRatioStep a b x + 2048 * V ^ 2 * s ^ 2 * Real.exp (lam * w x))
          ∂gaussianReal 0 1 := integral_mono hint hR hpt
    _ = 1 + s * ∫ x, logRatioStep a b x ∂gaussianReal 0 1 +
          2048 * V ^ 2 * s ^ 2 * ∫ x, Real.exp (lam * w x) ∂gaussianReal 0 1 := by
        have h1 : Integrable (fun x => (1 : ℝ) + s * logRatioStep a b x) (gaussianReal 0 1) :=
          (integrable_const 1).add (hψi.const_mul s)
        have h2 : Integrable (fun x => 2048 * V ^ 2 * s ^ 2 * Real.exp (lam * w x))
            (gaussianReal 0 1) := hintw.const_mul _
        have h3 : Integrable (fun x => s * logRatioStep a b x) (gaussianReal 0 1) :=
          hψi.const_mul s
        rw [integral_add h1 h2, integral_add (integrable_const 1) h3, integral_const_mul,
          integral_const_mul, integral_const]
        simp
    _ ≤ 1 + |s| * (a ^ 2 / 2 + 6 * (V * Real.sqrt V)) + 2048 * V ^ 2 * s ^ 2 * 2 := by
        have hsm : s * ∫ x, logRatioStep a b x ∂gaussianReal 0 1 ≤
            |s| * (a ^ 2 / 2 + 6 * (V * Real.sqrt V)) :=
          calc s * ∫ x, logRatioStep a b x ∂gaussianReal 0 1
              ≤ |s * ∫ x, logRatioStep a b x ∂gaussianReal 0 1| := le_abs_self _
            _ = |s| * |∫ x, logRatioStep a b x ∂gaussianReal 0 1| := abs_mul _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left hmean hs0
        have hE := mul_le_mul_of_nonneg_left hEw (by positivity : (0 : ℝ) ≤ 2048 * V ^ 2 * s ^ 2)
        linarith
    _ = 1 + |s| * (a ^ 2 / 2 + 6 * (V * Real.sqrt V)) + 4096 * s ^ 2 * V ^ 2 := by ring

/-! ### Chernoff's bound for the log error -/

/-- **Chernoff's bound for sums of i.i.d. terms**: for independent standard normal `Z_i` and
`s ≥ 0`, `P(δ ≤ ∑_{i<N} ψ(Z_i)) ≤ e^{−sδ} (E[e^{sψ(Z)}])^N` if `e^{sψ(Z)}` is integrable. -/
lemma measureReal_le_sum_le_exp {ψ : ℝ → ℝ} (hψ : Measurable ψ) {s : ℝ} (hs : 0 ≤ s)
    (hint : Integrable (fun x => Real.exp (s * ψ x)) (gaussianReal 0 1)) (N : ℕ) (δ : ℝ) :
    stdNormalSeq.real {z | δ ≤ ∑ i ∈ range N, ψ (z i)} ≤
      Real.exp (-s * δ) * (∫ x, Real.exp (s * ψ x) ∂gaussianReal 0 1) ^ N := by
  have he : ∀ z : ℕ → ℝ, Real.exp (s * ∑ i ∈ range N, ψ (z i)) =
      ∏ i ∈ range N, Real.exp (s * ψ (z i)) := fun z => by
    rw [Finset.mul_sum, Real.exp_sum]
  have hF : Measurable fun x => Real.exp (s * ψ x) := by fun_prop
  have hI : Integrable (fun z => Real.exp (s * ∑ i ∈ range N, ψ (z i))) stdNormalSeq := by
    simp_rw [he]
    exact integrable_prod_stdNormalSeq hF hint N
  have h := measure_ge_le_exp_mul_mgf (μ := stdNormalSeq)
    (X := fun z => ∑ i ∈ range N, ψ (z i)) δ hs hI
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [mgf]
  simp_rw [he]
  exact integral_prod_stdNormalSeq hF N

/-- **Gaussian-type tails of the log error** (Giles 2015, §5.1, p. 33, Table 5.2): for
`a² + b² ≤ V`, `V > 0`, `t ≥ 0` and `tV ≤ 1/32`, both tails of the sum `∑_{i<N} ψ(Z_i)` of
one-step log-ratios, `P(δ ≤ ∑ψ(Z_i))` and `P(δ ≤ −∑ψ(Z_i))`, are at most
`e^{−tδ + N(t m + 4096 t² V²)}`, `m = a²/2 + 6V^{3/2}`.  For GBM (`a = rh`, `b = σ√h`, `V = hD`)
this is, for `δ − N m ≤ 256 T D` (the range allowed by `tV ≤ 1/32`), the Gaussian tail
`e^{−(δ − O(h^{1/2}))²/(c h)}` of the logarithm of the ratio of the Euler–Maruyama path to the
exact solution. -/
lemma measureReal_le_sum_logRatioStep {a b V t : ℝ} (hVp : 0 < V) (hV : a ^ 2 + b ^ 2 ≤ V)
    (ht : 0 ≤ t) (htV : t * V ≤ 1 / 32) (N : ℕ) (δ : ℝ) :
    stdNormalSeq.real {z | δ ≤ ∑ i ∈ range N, logRatioStep a b (z i)} ≤
        Real.exp (-(t * δ) + N * (t * (a ^ 2 / 2 + 6 * (V * Real.sqrt V)) +
          4096 * t ^ 2 * V ^ 2)) ∧
      stdNormalSeq.real {z | δ ≤ -∑ i ∈ range N, logRatioStep a b (z i)} ≤
        Real.exp (-(t * δ) + N * (t * (a ^ 2 / 2 + 6 * (V * Real.sqrt V)) +
          4096 * t ^ 2 * V ^ 2)) := by
  set m := a ^ 2 / 2 + 6 * (V * Real.sqrt V) with hm
  have key : ∀ s : ℝ, |s| = t → ∀ ψ : ℝ → ℝ, Measurable ψ →
      (∀ x, Real.exp (t * ψ x) = Real.exp (s * logRatioStep a b x)) →
      stdNormalSeq.real {z | δ ≤ ∑ i ∈ range N, ψ (z i)} ≤
        Real.exp (-(t * δ) + N * (t * m + 4096 * t ^ 2 * V ^ 2)) := by
    intro s hst ψ hψ hψe
    have hs' : |s| * V ≤ 1 / 32 := by rw [hst]; exact htV
    obtain ⟨hint, hle⟩ := integrable_and_integral_exp_mul_logRatioStep_le hVp hV hs'
    have hint' : Integrable (fun x => Real.exp (t * ψ x)) (gaussianReal 0 1) := by
      simp_rw [hψe]; exact hint
    have h1 := measureReal_le_sum_le_exp hψ ht hint' N δ
    have e1 : ∫ x, Real.exp (t * ψ x) ∂gaussianReal 0 1 =
        ∫ x, Real.exp (s * logRatioStep a b x) ∂gaussianReal 0 1 := by simp_rw [hψe]
    rw [e1] at h1
    rw [hst, ← hm] at hle
    have hsq : s ^ 2 = t ^ 2 := by rw [← sq_abs, hst]
    rw [hsq] at hle
    have h0 : 0 ≤ ∫ x, Real.exp (s * logRatioStep a b x) ∂gaussianReal 0 1 :=
      integral_nonneg fun x => (Real.exp_pos _).le
    have h2 : (∫ x, Real.exp (s * logRatioStep a b x) ∂gaussianReal 0 1) ^ N ≤
        Real.exp (N * (t * m + 4096 * t ^ 2 * V ^ 2)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ h0 (hle.trans (by
        have := Real.add_one_le_exp (t * m + 4096 * t ^ 2 * V ^ 2)
        linarith)) N
    calc _ ≤ _ := h1
      _ ≤ Real.exp (-t * δ) * Real.exp (N * (t * m + 4096 * t ^ 2 * V ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, neg_mul]
  refine ⟨key t (abs_of_nonneg ht) _ (measurable_logRatioStep a b) fun x => rfl, ?_⟩
  have e : {z : ℕ → ℝ | δ ≤ -∑ i ∈ range N, logRatioStep a b (z i)} =
      {z | δ ≤ ∑ i ∈ range N, (fun x => -logRatioStep a b x) (z i)} := by
    ext z
    simp [Finset.sum_neg_distrib]
  rw [e]
  exact key (-t) (by rw [abs_neg, abs_of_nonneg ht]) _ (measurable_logRatioStep a b).neg
    fun x => by simp only [Pi.neg_apply, mul_neg, neg_mul]

/-! ### The exact solution in log scale -/

/-- The standard normal law has density at most `1/√(2π)`. -/
lemma gaussianReal_le_smul_volume :
    gaussianReal 0 1 ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ • volume := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [gaussianReal_apply 0 one_ne_zero A, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in A, gaussianPDF 0 1 x ≤ ∫⁻ _ in A, ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ := by
        refine lintegral_mono fun x => ?_
        rw [gaussianPDF]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [gaussianPDFReal]
        simp only [NNReal.coe_one, mul_one]
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (x - 0) ^ 2 := sq_nonneg _
        have h2 : (0 : ℝ) < 2 := by norm_num
        rw [neg_div]
        exact neg_nonpos.2 (div_nonneg this h2.le)
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ * volume A := setLIntegral_const _ _

/-- `P(|α + βZ − c| ≤ δ) ≤ 2δ/(|β|√(2π))` for `Z ∼ N(0,1)` and `β ≠ 0`. -/
lemma measureReal_abs_affine_sub_le {α β c δ : ℝ} (hβ : β ≠ 0) (hδ : 0 ≤ δ) :
    (gaussianReal 0 1).real {u | |α + β * u - c| ≤ δ} ≤
      2 * δ / (|β| * Real.sqrt (2 * Real.pi)) := by
  set m := (c - α) / β
  have hb : 0 < |β| := abs_pos.2 hβ
  have e : {u : ℝ | |α + β * u - c| ≤ δ} = {u | |id u - m| ≤ δ / |β|} := by
    ext u
    simp only [Set.mem_ofPred_eq, id]
    have : α + β * u - c = β * (u - m) := by
      simp only [m]
      field_simp
      ring
    rw [this, abs_mul, le_div_iff₀ hb, mul_comm]
  rw [e]
  have hmap : (gaussianReal 0 1).map id ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ • volume := by
    rw [Measure.map_id]
    exact gaussianReal_le_smul_volume
  have h := measureReal_abs_sub_le_of_map_le measurable_id (by positivity) hmap m
    (div_nonneg hδ hb.le)
  refine h.trans (le_of_eq ?_)
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- **The bounded density near the strike, in log scale** (Giles 2015, §5.1, p. 33, l. 1437–1438:
"there is a bounded density of paths terminating in the neighbourhood of `K`"): `log|S_T|` is
`log|S_0| + (r − σ²/2)T + σW_T`, Gaussian with standard deviation `|σ|√T`, so for `S_0 ≠ 0`,
`σ ≠ 0`, `T > 0` and every `c`, `P(|log|S_T| − c| ≤ δ) ≤ 2δ/(|σ| √T √(2π))`, uniformly in `S_0`
(`S_T` on any level, `gbmExact`). -/
lemma gbmExact_logSmallBall (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (c : ℝ) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    stdNormalSeq.real {z | |Real.log |gbmExact r σ T s₀ n z| - c| ≤ δ} ≤
      2 * δ / (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi)) := by
  set S := {x : ℝ | |Real.log |x| - c| ≤ δ} with hSdef
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have e1 : {z | |Real.log |gbmExact r σ T s₀ n z| - c| ≤ δ} = gbmExact r σ T s₀ n ⁻¹' S := rfl
  rw [e1, ← map_measureReal_apply (measurable_gbmExact r σ T s₀ n) hS, map_gbmExact,
    map_measureReal_apply (measurable_gbmExact r σ T s₀ 0) hS]
  set α := Real.log |s₀| + (r - σ ^ 2 / 2) * T
  set β := σ * Real.sqrt T
  have e2 : gbmExact r σ T s₀ 0 ⁻¹' S =
      (fun z : ℕ → ℝ => z 0) ⁻¹' {u | |α + β * u - c| ≤ δ} := by
    ext z
    simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, gbmExact_zero]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), Real.log_mul (abs_ne_zero.2 hs₀)
      (Real.exp_pos _).ne', Real.log_exp]
    have : Real.log |s₀| + ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * z 0)) = α + β * z 0 := by
      simp only [α, β]
      ring
    rw [this]
  rw [e2, (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0).measureReal_preimage
    (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet]
  have hβ : β ≠ 0 := mul_ne_zero hσ (Real.sqrt_pos.2 hT).ne'
  refine (measureReal_abs_affine_sub_le hβ hδ).trans (le_of_eq ?_)
  simp only [β, abs_mul, abs_of_nonneg (Real.sqrt_nonneg T)]

/-- If `k` lies between `p` and `q`, then `|p − k| ≤ |p − q|`. -/
lemma abs_sub_le_abs_sub_of_between {p q k : ℝ} (h : (p ≤ k ∧ k ≤ q) ∨ (q ≤ k ∧ k ≤ p)) :
    |p - k| ≤ |p - q| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- **The paths on either side of the strike, in log scale** (Giles 2015, §5.1, p. 33,
l. 1439–1441): if `x`, `y` have the same sign and the digital payoffs `1_{x>K}`, `1_{y>K}` differ,
then `log|K|` lies between `log|x|` and `log|y|`, so `|log|x| − log|K|| ≤ |log|x| − log|y||`. -/
lemma abs_log_sub_log_le_of_digital_ne {x y K : ℝ} (hxy : 0 < x * y)
    (hne : (Set.Ioi K).indicator (1 : ℝ → ℝ) x ≠ (Set.Ioi K).indicator 1 y) :
    |Real.log (|x|) - Real.log (|K|)| ≤ |Real.log (|x|) - Real.log (|y|)| := by
  have hK : (K < x ∧ y ≤ K) ∨ (x ≤ K ∧ K < y) := by
    rcases lt_or_ge K x with hx | hx <;> rcases lt_or_ge K y with hy | hy
    · exact absurd (by rw [Set.indicator_of_mem (by exact hx), Set.indicator_of_mem
        (by exact hy)]; rfl) hne
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
    · exact absurd (by rw [Set.indicator_of_notMem (by simpa using hx),
        Set.indicator_of_notMem (by simpa using hy)]) hne
  refine abs_sub_le_abs_sub_of_between ?_
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [abs_of_pos hx, abs_of_pos hy]
    rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_pos (by linarith)]
      exact Or.inr ⟨Real.log_le_log hy h2, Real.log_le_log (by linarith) h1.le⟩
    · rw [abs_of_pos (by linarith)]
      exact Or.inl ⟨Real.log_le_log hx h1, Real.log_le_log (by linarith) h2.le⟩
  · rw [abs_of_neg hx, abs_of_neg hy]
    rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_neg (by linarith)]
      exact Or.inl ⟨Real.log_le_log (by linarith) (by linarith),
        Real.log_le_log (by linarith) (by linarith)⟩
    · rw [abs_of_neg (by linarith)]
      exact Or.inr ⟨Real.log_le_log (by linarith) (by linarith),
        Real.log_le_log (by linarith) (by linarith)⟩

/-! ### One level against the exact solution -/

/-- Where the Euler–Maruyama factor `1 + rh + σ√h x` of GBM is larger than `½`, the logarithm of
the exact step minus that of the Euler–Maruyama step is `−ψ(x)`, `ψ` the one-step log-ratio with
`a = rh`, `b = σ√h` (Giles 2015, §5.1). -/
lemma log_gbmExpFactor_sub_log_gbmEMFactor (r σ : ℝ) {h : ℝ} (hh : 0 ≤ h) {x : ℝ}
    (hx : -(1 / 2) < r * h + σ * Real.sqrt h * x) :
    Real.log (gbmExpFactor r σ h x) - Real.log (gbmEMFactor r σ h x) =
      -logRatioStep (r * h) (σ * Real.sqrt h) x := by
  have hs : (σ * Real.sqrt h) ^ 2 = σ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]
  have e : gbmEMFactor r σ h x = 1 + (r * h + σ * Real.sqrt h * x) := by
    unfold gbmEMFactor
    ring
  unfold logRatioStep
  rw [if_pos hx, gbmExpFactor, Real.log_exp, e, hs]
  ring

/-- `P(∃ i < N, a + bZ_i ≤ −½) ≤ 48 N V²` for independent standard normal `Z_i` and
`a² + b² ≤ V` (a union bound). -/
lemma measureReal_exists_le_neg_half_le {a b V : ℝ} (hV : a ^ 2 + b ^ 2 ≤ V) (N : ℕ) :
    stdNormalSeq.real {z | ∃ i < N, a + b * z i ≤ -(1 / 2)} ≤ N * (48 * V ^ 2) := by
  have e : {z : ℕ → ℝ | ∃ i < N, a + b * z i ≤ -(1 / 2)} =
      ⋃ i ∈ range N, (fun z : ℕ → ℝ => z i) ⁻¹' {x | a + b * x ≤ -(1 / 2)} := by
    ext z
    simp
  rw [e]
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have hB : MeasurableSet {x : ℝ | a + b * x ≤ -(1 / 2)} :=
    measurableSet_le (by fun_prop) measurable_const
  have h1 : ∀ i, stdNormalSeq.real ((fun z : ℕ → ℝ => z i) ⁻¹' {x | a + b * x ≤ -(1 / 2)}) =
      (gaussianReal 0 1).real {x | a + b * x ≤ -(1 / 2)} := fun i =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i).measureReal_preimage
      hB.nullMeasurableSet
  simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left (measureReal_affine_le_neg_half_le hV) (Nat.cast_nonneg N)

/-- One level against the exact solution, for every `t ≥ 0` with `tV ≤ 1/32` and every `δ ≥ 0`
(Giles 2015, §5.1, p. 33, l. 1436–1441): with `h = T 2^{−n}` and `V = h(σ² + r²T)`,
`P(1_{S_T>K} ≠ 1_{Ŝ_n>K}) ≤ 2ⁿ 48V² + 2δ/(|σ| √T √(2π)) + 2e^{−tδ + 2ⁿ(t m + 4096 t² V²)}`,
`m = (rh)²/2 + 6V^{3/2}`: the three terms are the event that some Euler–Maruyama factor is at most
`½`, the small ball of `log|S_T|` around `log|K|`, and the two tails of the log error. -/
lemma gbm_em_exact_mismatch_le_aux (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (n : ℕ) {h V t δ : ℝ} (hh : h = T / 2 ^ n)
    (hV : V = h * (σ ^ 2 + r ^ 2 * T)) (ht : 0 ≤ t) (hδ : 0 ≤ δ) (htV : t * V ≤ 1 / 32) :
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ n z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ n z)} ≤
      2 ^ n * (48 * V ^ 2) + 2 * δ / (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi)) +
        2 * Real.exp (-(t * δ) + 2 ^ n * (t * ((r * h) ^ 2 / 2 + 6 * (V * Real.sqrt V)) +
          4096 * t ^ 2 * V ^ 2)) := by
  set N := 2 ^ n with hN
  set a := r * h with ha
  set b := σ * Real.sqrt h with hb
  have hh0 : 0 < h := by rw [hh]; positivity
  have hhT : h ≤ T := by
    rw [hh]
    exact div_le_self hT.le (one_le_pow₀ (by norm_num))
  have hab : a ^ 2 + b ^ 2 ≤ V := by
    rw [ha, hb, hV, mul_pow, mul_pow, Real.sq_sqrt hh0.le]
    nlinarith [mul_le_mul_of_nonneg_left hhT (mul_nonneg (sq_nonneg r) hh0.le)]
  have hVp : 0 < V := by
    rw [hV]
    have : 0 < σ ^ 2 := by positivity
    positivity
  set X := gbmExact r σ T s₀ n
  set Y := gbmEM r σ T s₀ n
  set ψ := logRatioStep a b
  have hsub : {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X z) ≠ (Set.Ioi K).indicator 1 (Y z)} ⊆
      {z | ∃ i < N, a + b * z i ≤ -(1 / 2)} ∪
        {z | |Real.log (|X z|) - Real.log (|K|)| ≤ δ} ∪
        {z | δ ≤ ∑ i ∈ range N, ψ (z i)} ∪ {z | δ ≤ -∑ i ∈ range N, ψ (z i)} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    by_cases hbad : ∃ i < N, a + b * z i ≤ -(1 / 2)
    · exact Or.inl (Or.inl (Or.inl hbad))
    push Not at hbad
    have hXe : X z = s₀ * ∏ i ∈ range N, gbmExpFactor r σ h (z i) := by
      show gbmExact r σ T s₀ n z = _
      rw [gbmExact_eq_prod, ← hh]
    have hYe : Y z = s₀ * ∏ i ∈ range N, gbmEMFactor r σ h (z i) := by
      show gbmEM r σ T s₀ n z = _
      rw [gbmEM_eq_prod, ← hh]
    have hEpos : ∀ i ∈ range N, 0 < gbmExpFactor r σ h (z i) := fun i _ => Real.exp_pos _
    have hFpos : ∀ i ∈ range N, 0 < gbmEMFactor r σ h (z i) := fun i hi => by
      have := hbad i (Finset.mem_range.1 hi)
      unfold gbmEMFactor
      simp only [ha, hb] at this
      linarith
    have hPE := Finset.prod_pos hEpos
    have hPF := Finset.prod_pos hFpos
    have hs0 : 0 < |s₀| := abs_pos.2 hs₀
    have hxy : 0 < X z * Y z := by
      rw [hXe, hYe]
      have : 0 < s₀ ^ 2 := by positivity
      nlinarith [mul_pos hPE hPF]
    have hlog : Real.log (|X z|) - Real.log (|Y z|) = -∑ i ∈ range N, ψ (z i) := by
      rw [hXe, hYe, abs_mul, abs_mul, abs_of_pos hPE, abs_of_pos hPF,
        Real.log_mul hs0.ne' hPE.ne', Real.log_mul hs0.ne' hPF.ne',
        Real.log_prod (fun i hi => (hEpos i hi).ne'), Real.log_prod (fun i hi => (hFpos i hi).ne'),
        ← Finset.sum_neg_distrib]
      rw [show ∀ (A B C : ℝ), A + B - (A + C) = B - C from fun A B C => by ring,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      exact log_gbmExpFactor_sub_log_gbmEMFactor r σ hh0.le (hbad i (Finset.mem_range.1 hi))
    have key := abs_log_sub_log_le_of_digital_ne hxy hz
    rw [hlog, abs_neg] at key
    by_cases hsb : |Real.log (|X z|) - Real.log (|K|)| ≤ δ
    · exact Or.inl (Or.inl (Or.inr hsb))
    push Not at hsb
    rcases le_abs.1 (hsb.trans_le key).le with h1 | h1
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1
  obtain ⟨hU, hW⟩ := measureReal_le_sum_logRatioStep hVp hab ht htV N δ
  have hbad := measureReal_exists_le_neg_half_le hab N
  have hSB := gbmExact_logSmallBall r σ hs₀ hσ hT (Real.log (|K|)) n hδ
  have hNc : ((N : ℕ) : ℝ) = 2 ^ n := by rw [hN]; push_cast; ring
  rw [hNc] at hbad hU hW
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ stdNormalSeq.real {z | ∃ i < N, a + b * z i ≤ -(1 / 2)} +
          stdNormalSeq.real {z | |Real.log (|X z|) - Real.log (|K|)| ≤ δ} +
          stdNormalSeq.real {z | δ ≤ ∑ i ∈ range N, ψ (z i)} +
          stdNormalSeq.real {z | δ ≤ -∑ i ∈ range N, ψ (z i)} := by
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measureReal_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measureReal_union_le _ _
    _ ≤ _ := by
        rw [ha] at hU hW
        linarith

/-- **One Euler–Maruyama level against the exact solution: the fraction of paths on either side
of the strike is `O((h log(T/h))^{1/2})`** (Giles 2015, §5.1, p. 33, l. 1436–1441: "noting that
the strong error is `O(h_ℓ^{1/2})`, and there is a bounded density of paths terminating in the
neighbourhood of `K`, there is therefore an `O(h_ℓ^{1/2})` fraction of the samples with the coarse
and fine paths on either side of the strike"; Table 5.2, l. 1431: digital, Euler–Maruyama,
analysis "`O(h^{1/2} log h)`", "due to Avikainen", l. 1457–1458).  For GBM with `S_0 ≠ 0`,
`σ ≠ 0`, `T > 0`, every strike `K` and every level `n`, with `h = T 2^{−n}` and
`D = σ² + r²T`, the exact solution `S_T` and the Euler–Maruyama approximation `Ŝ_n` driven by the
same increments satisfy
`P(1_{S_T>K} ≠ 1_{Ŝ_n>K}) ≤ 48 T h D² + 2 (T (r²h/2 + 6D (hD)^{1/2})`
`+ 160 D (T h n log 2)^{1/2}) / (|σ| √T √(2π)) + 2h/T`.
Since `n log 2 = log(T/h)` this is `O((h log(T/h))^{1/2})`, uniformly in `S_0` and `K`.  Proof:
`gbm_em_exact_mismatch_le_aux` with `t = (log(T/h)/(Th))^{1/2}/(32D)` and
`δ = T(r²h/2 + 6D(hD)^{1/2}) + 160 D (Th log(T/h))^{1/2}`, which make the tails of the log error
`e^{−log(T/h)} = h/T`. -/
theorem gbm_em_exact_mismatch_le (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (n : ℕ) {h D : ℝ} (hh : h = T / 2 ^ n) (hD : D = σ ^ 2 + r ^ 2 * T) :
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ n z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ n z)} ≤
      48 * T * h * D ^ 2 +
        2 * (T * (r ^ 2 * h / 2 + 6 * D * Real.sqrt (h * D)) +
          160 * D * Real.sqrt (T * h * (n * Real.log 2))) /
          (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi)) + 2 * h / T := by
  have hh0 : 0 < h := by rw [hh]; positivity
  have hD0 : 0 < D := by
    have : 0 < σ ^ 2 := by positivity
    rw [hD]
    positivity
  have h2n : (2 : ℝ) ^ n * h = T := by rw [hh]; field_simp
  set L := (n : ℝ) * Real.log 2 with hL
  have hL0 : 0 ≤ L := by rw [hL]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  set V := h * D with hVdef
  set t := Real.sqrt (L / (T * h)) / (32 * D) with htdef
  set m := (r * h) ^ 2 / 2 + 6 * (V * Real.sqrt V) with hm
  set δ := 2 ^ n * m + 160 * D * Real.sqrt (T * h * L) with hδdef
  have ht : 0 ≤ t := by positivity
  have hm0 : 0 ≤ m := by positivity
  have hδ : 0 ≤ δ := by positivity
  have hLh : L * h / T ≤ 1 := by
    rw [hL, hh, div_le_one hT]
    have h1 : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
    have h3 : (n : ℝ) * Real.log 2 ≤ 2 ^ n := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc (n : ℝ) * Real.log 2 * (T / 2 ^ n) = (n * Real.log 2 / 2 ^ n) * T := by ring
      _ ≤ 1 * T := by
          gcongr
          rw [div_le_one (by positivity)]
          exact h3
      _ = T := one_mul T
  have htV : t * V ≤ 1 / 32 := by
    have e : t * V = Real.sqrt (L * h / T) / 32 := by
      rw [htdef, hVdef]
      have e2 : Real.sqrt (L * h / T) = Real.sqrt (L / (T * h)) * h := by
        rw [show L * h / T = L / (T * h) * h ^ 2 by field_simp, Real.sqrt_mul' _ (sq_nonneg h),
          Real.sqrt_sq hh0.le]
      rw [e2]
      field_simp
    rw [e]
    have : Real.sqrt (L * h / T) ≤ 1 := Real.sqrt_le_one.mpr hLh
    linarith
  have haux := gbm_em_exact_mismatch_le_aux r σ hs₀ hσ hT K n hh (by rw [hVdef, hD]) ht hδ htV
  -- the exponent is `−L`
  have e5 : t * (160 * D * Real.sqrt (T * h * L)) = 5 * L := by
    have hThL : Real.sqrt (L / (T * h)) * Real.sqrt (T * h * L) = L := by
      rw [← Real.sqrt_mul (by positivity), show L / (T * h) * (T * h * L) = L ^ 2 by
        field_simp, Real.sqrt_sq hL0]
    calc t * (160 * D * Real.sqrt (T * h * L))
        = (Real.sqrt (L / (T * h)) * Real.sqrt (T * h * L)) * (160 * D / (32 * D)) := by
          rw [htdef]
          ring
      _ = 5 * L := by
          rw [hThL, mul_div_mul_right _ _ hD0.ne']
          norm_num
          ring
  have e4 : (2 : ℝ) ^ n * (4096 * t ^ 2 * V ^ 2) = 4 * L := by
    rw [htdef, hVdef, div_pow, Real.sq_sqrt (by positivity)]
    calc (2 : ℝ) ^ n * (4096 * (L / (T * h) / (32 * D) ^ 2) * (h * D) ^ 2)
        = 4 * L * (2 ^ n * h) / T := by
          field_simp
          ring
      _ = 4 * L := by
          rw [h2n]
          field_simp
  have hexp : -(t * δ) + 2 ^ n * (t * m + 4096 * t ^ 2 * V ^ 2) = -L := by
    have : t * δ = t * (2 ^ n * m) + 5 * L := by rw [hδdef, mul_add, e5]
    rw [this]
    linear_combination e4
  have hexpL : Real.exp (-L) = h / T := by
    rw [hL, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), hh]
    field_simp
  rw [hexp, hexpL] at haux
  refine haux.trans (le_of_eq ?_)
  have e1 : (2 : ℝ) ^ n * (48 * V ^ 2) = 48 * T * h * D ^ 2 := by
    rw [hVdef, ← h2n]
    ring
  have e2 : (2 : ℝ) ^ n * m = T * (r ^ 2 * h / 2 + 6 * D * Real.sqrt (h * D)) := by
    rw [hm, hVdef, ← h2n, Real.sqrt_mul hh0.le]
    ring
  rw [e1, hδdef, e2]
  ring

/-- The bound of `gbm_em_exact_mismatch_le` is at most `√h (A + B √L)`, with
`A = 48 T^{3/2} D² + (T r² + 12 √T D^{3/2})/(|σ|√(2π)) + 2/√T` and `B = 320 D/(|σ|√(2π))`, for
`0 < h ≤ T` (Giles 2015, §5.1, Table 5.2). -/
lemma endpoint_bound_le_sqrt {r σ T h D L : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) (hh0 : 0 < h)
    (hhT : h ≤ T) :
    48 * T * h * D ^ 2 +
        2 * (T * (r ^ 2 * h / 2 + 6 * D * Real.sqrt (h * D)) +
          160 * D * Real.sqrt (T * h * L)) /
          (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi)) + 2 * h / T ≤
      Real.sqrt h * (48 * T * Real.sqrt T * D ^ 2 +
        (T * r ^ 2 + 12 * Real.sqrt T * D * Real.sqrt D) / (|σ| * Real.sqrt (2 * Real.pi)) +
        2 / Real.sqrt T + 320 * D / (|σ| * Real.sqrt (2 * Real.pi)) * Real.sqrt L) := by
  set x := Real.sqrt h with hx
  set y := Real.sqrt T with hy
  set c := |σ| * Real.sqrt (2 * Real.pi) with hc
  have hc0 : 0 < c := by
    have := abs_pos.2 hσ
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hx0 : 0 < x := Real.sqrt_pos.2 hh0
  have hy0 : 0 < y := Real.sqrt_pos.2 hT
  have hxx : x * x = h := Real.mul_self_sqrt hh0.le
  have hyy : y * y = T := Real.mul_self_sqrt hT.le
  have hxy : x ≤ y := Real.sqrt_le_sqrt hhT
  have hhxy : h ≤ x * y := by rw [← hxx]; exact mul_le_mul_of_nonneg_left hxy hx0.le
  have hsD : Real.sqrt (h * D) = x * Real.sqrt D := Real.sqrt_mul hh0.le D
  have hsL : Real.sqrt (T * h * L) = y * x * Real.sqrt L := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hT.le]
  have hden : |σ| * Real.sqrt T * Real.sqrt (2 * Real.pi) = c * y := by rw [hc, hy]; ring
  have p1 : 48 * T * h * D ^ 2 ≤ x * (48 * T * y * D ^ 2) := by
    calc 48 * T * h * D ^ 2 = 48 * T * D ^ 2 * h := by ring
      _ ≤ 48 * T * D ^ 2 * (x * y) := by gcongr
      _ = x * (48 * T * y * D ^ 2) := by ring
  have p2 : 2 * (T * (r ^ 2 * h / 2 + 6 * D * Real.sqrt (h * D)) +
      160 * D * Real.sqrt (T * h * L)) / (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi)) ≤
      x * ((T * r ^ 2 + 12 * y * D * Real.sqrt D) / c + 320 * D / c * Real.sqrt L) := by
    rw [hden, div_le_iff₀ (by positivity), hsD, hsL]
    have hr : 0 ≤ T * r ^ 2 := by positivity
    calc 2 * (T * (r ^ 2 * h / 2 + 6 * D * (x * Real.sqrt D)) + 160 * D * (y * x * Real.sqrt L))
        = T * r ^ 2 * h + 12 * T * D * x * Real.sqrt D + 320 * D * y * x * Real.sqrt L := by ring
      _ ≤ T * r ^ 2 * (x * y) + 12 * (y * y) * D * x * Real.sqrt D +
          320 * D * y * x * Real.sqrt L := by rw [hyy]; gcongr
      _ = x * ((T * r ^ 2 + 12 * y * D * Real.sqrt D) / c + 320 * D / c * Real.sqrt L) *
          (c * y) := by
          field_simp
  have p3 : 2 * h / T ≤ x * (2 / y) := by
    rw [← hyy, div_le_iff₀ (by positivity)]
    calc 2 * h ≤ 2 * (x * y) := by gcongr
      _ = x * (2 / y) * (y * y) := by field_simp
  calc _ ≤ x * (48 * T * y * D ^ 2) +
        x * ((T * r ^ 2 + 12 * y * D * Real.sqrt D) / c + 320 * D / c * Real.sqrt L) +
        x * (2 / y) := by linarith
    _ = _ := by ring

/-! ### The fine and the coarse path -/

/-- **Fine and coarse paths against the exact solution** (Giles 2015, §5.1, p. 33, l. 1438–1441):
if the payoffs of the fine path (level `ℓ + 1`) and of the coarse path (level `ℓ`, driven by the
summed increments `pairAvg`) differ, one of them differs from the payoff of the exact solution
driven by the same increments; so the probability is at most the sum of the probabilities `P_n`
that the level-`n` payoff differs from the exact one, for `n = ℓ + 1` and `n = ℓ` (for the coarse
path `measurePreserving_pairAvg`). -/
lemma gbm_em_pair_mismatch_le (r σ T s₀ K : ℝ) (ℓ : ℕ) :
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ≤
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ (ℓ + 1) z)} +
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z)} := by
  set X := gbmExact r σ T s₀ (ℓ + 1)
  refine (measureReal_mono (digital_ne_subset_union X _ _ K)).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl (le_of_eq ?_)))
  have hm : MeasurableSet {w | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ w) ≠
      (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ w)} :=
    (measurableSet_eq_fun (measurable_digital (measurable_gbmExact r σ T s₀ ℓ) K)
      (measurable_digital (measurable_gbmEM r σ T s₀ ℓ) K)).compl
  have e : {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X z) ≠
      (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} =
      pairAvg ⁻¹' {w | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ w) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ w)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, X, gbmExact_pairAvg]
  rw [e, measurePreserving_pairAvg.measureReal_preimage hm.nullMeasurableSet]

/-- **The digital option with Euler–Maruyama: `V_ℓ`, `P(P_ℓ ≠ P_{ℓ−1})` and `E[(P_ℓ − P_{ℓ−1})⁴]`
are `O((h_ℓ log(T/h_ℓ))^{1/2})`, uniformly in `K` and `S_0`** (Giles 2015, §5.1, p. 33, Table 5.2,
l. 1431: digital option, Euler–Maruyama, numerics "`O(h^{1/2})`", analysis "`O(h^{1/2} log h)`"; l.
1438–1444: "an `O(h_ℓ^{1/2})` fraction of the samples with the coarse and fine paths on either side
of the strike, with `P_ℓ−P_{ℓ−1} = ±1`. This gives `V_ℓ = O(h^{1/2})` … Furthermore,
`E[(P_ℓ−P_{ℓ−1})⁴] = O(h_ℓ^{1/2})`").  For GBM with `σ ≠ 0` and `T > 0` there is `C ≥ 0`, depending
only on `r`, `σ` and `T`, such that for every initial value `s₀`, every strike `K` and every level
`ℓ` the correction `ΔP_ℓ = H(Ŝ^f_{ℓ+1} − K) − H(Ŝ^c_ℓ − K)` (the fine Euler–Maruyama path on level
`ℓ + 1`, the coarse one on level `ℓ` driven by the summed increments `pairAvg`) satisfies
`V[ΔP_ℓ] ≤ C (h_{ℓ+1} (ℓ + 1))^{1/2}`, `P(ΔP_ℓ ≠ 0) ≤ C (h_{ℓ+1} (ℓ + 1))^{1/2}` and
`E[ΔP_ℓ⁴] ≤ C (h_{ℓ+1} (ℓ + 1))^{1/2}`, where `h_{ℓ+1} = T 2^{−(ℓ+1)}` and
`(ℓ + 1) log 2 = log(T/h_{ℓ+1})`.  This is the endpoint `q = ½` of `gbm_em_digital_rate` up to a
factor `(ℓ + 1)^{1/2} ≍ (log(1/h))^{1/2}`, the square root of the logarithmic factor of Table 5.2's
analysis column (see `gbm_em_digital_endpoint_log` for the paper's `log(1/h)`); the observed
`O(h^{1/2})` is not proved.  As in `gbm_em_digital_rate`, the kurtosis is at least the reciprocal of
the bound when `P(ΔP_ℓ ≠ 0) > 0`.  `C = (1 + √2)(A + B)` with `A`, `B` as in
`endpoint_bound_le_sqrt` and `D = σ² + r²T` (`C ≈ 71` at the paper's `r = 0.05`, `σ = 0.2`, `T = 1`,
l. 1329–1330).  Proof: `gbm_em_pair_mismatch_le`, `gbm_em_exact_mismatch_le` on the levels `ℓ + 1`
and `ℓ`, `endpoint_bound_le_sqrt`; `V[ΔP_ℓ] ≤ E[ΔP_ℓ²] = P(ΔP_ℓ ≠ 0) = E[ΔP_ℓ⁴]`; for `s₀ = 0` both
paths vanish. -/
theorem gbm_em_digital_endpoint (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ K : ℝ) (ℓ : ℕ),
      variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
        C * Real.sqrt (T / 2 ^ (ℓ + 1) * (ℓ + 1)) ∧
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ≤
        C * Real.sqrt (T / 2 ^ (ℓ + 1) * (ℓ + 1)) ∧
      ∫ z, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 4 ∂stdNormalSeq ≤
        C * Real.sqrt (T / 2 ^ (ℓ + 1) * (ℓ + 1)) ∧
      (0 < stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} →
        (C * Real.sqrt (T / 2 ^ (ℓ + 1) * (ℓ + 1)))⁻¹ ≤
          kurtosis (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
            (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq) := by
  set D := σ ^ 2 + r ^ 2 * T with hD
  set A := 48 * T * Real.sqrt T * D ^ 2 +
    (T * r ^ 2 + 12 * Real.sqrt T * D * Real.sqrt D) / (|σ| * Real.sqrt (2 * Real.pi)) +
    2 / Real.sqrt T with hA
  set B := 320 * D / (|σ| * Real.sqrt (2 * Real.pi)) with hB
  have hD0 : 0 ≤ D := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine ⟨(1 + Real.sqrt 2) * (A + B), by positivity, fun s₀ K ℓ => ?_⟩
  set H := T / 2 ^ (ℓ + 1) with hH
  set k : ℝ := (ℓ : ℝ) + 1 with hk
  have hH0 : 0 < H := by positivity
  have hk1 : 1 ≤ k := by rw [hk]; linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hsk : 1 ≤ Real.sqrt k := Real.one_le_sqrt.2 hk1
  have hm1 := measurable_gbmEM r σ T s₀ (ℓ + 1)
  have hm0 := (measurable_gbmEM r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable
  have hP : stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (gbmEM r σ T s₀ (ℓ + 1) z) ≠ (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ≤
      (1 + Real.sqrt 2) * (A + B) * Real.sqrt (H * k) := by
    rcases eq_or_ne s₀ 0 with rfl | hs₀
    · have hz : ∀ ℓ' z, gbmEM r σ T 0 ℓ' z = 0 := fun ℓ' z => by rw [gbmEM_eq_prod, zero_mul]
      have hset : {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T 0 (ℓ + 1) z) ≠
          (Set.Ioi K).indicator 1 (gbmEM r σ T 0 ℓ (pairAvg z))} = ∅ := by
        ext z
        simp [hz]
      rw [hset, measureReal_empty]
      positivity
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog21 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      norm_num at this
      linarith
    -- the fine level
    have hf := (gbm_em_exact_mismatch_le r σ hs₀ hσ hT K (ℓ + 1) rfl hD).trans
      (endpoint_bound_le_sqrt (r := r) (D := D) (L := ((ℓ + 1 : ℕ) : ℝ) * Real.log 2) hσ hT
        hH0 (div_le_self hT.le (one_le_pow₀ (by norm_num))))
    -- the coarse level
    have hc := (gbm_em_exact_mismatch_le r σ hs₀ hσ hT K ℓ rfl hD).trans
      (endpoint_bound_le_sqrt (r := r) (D := D) (L := (ℓ : ℝ) * Real.log 2) hσ hT
        (by positivity) (div_le_self hT.le (one_le_pow₀ (by norm_num))))
    rw [← hA, ← hB] at hf hc
    have hLf : Real.sqrt (((ℓ + 1 : ℕ) : ℝ) * Real.log 2) ≤ Real.sqrt k := by
      refine Real.sqrt_le_sqrt ?_
      rw [hk]
      push_cast
      nlinarith
    have hLc : Real.sqrt ((ℓ : ℝ) * Real.log 2) ≤ Real.sqrt k := by
      refine Real.sqrt_le_sqrt ?_
      rw [hk]
      nlinarith [Nat.cast_nonneg (α := ℝ) ℓ]
    have hAB : ∀ y, y ≤ Real.sqrt k → A + B * y ≤ (A + B) * Real.sqrt k := fun y hy => by
      nlinarith [mul_le_mul_of_nonneg_left hy hB0]
    have hHc : Real.sqrt (T / 2 ^ ℓ) = Real.sqrt 2 * Real.sqrt H := by
      rw [← Real.sqrt_mul (by norm_num), hH, pow_succ]
      congr 1
      field_simp
    rw [hHc] at hc
    have hsH : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have e : Real.sqrt (H * k) = Real.sqrt H * Real.sqrt k := Real.sqrt_mul hH0.le k
    have h1 : stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (gbmExact r σ T s₀ (ℓ + 1) z) ≠ (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ (ℓ + 1) z)} ≤
        Real.sqrt H * ((A + B) * Real.sqrt k) := by
      refine hf.trans ?_
      rw [← hH]
      exact mul_le_mul_of_nonneg_left (hAB _ hLf) hsH
    have h2 : stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (gbmExact r σ T s₀ ℓ z) ≠ (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z)} ≤
        Real.sqrt 2 * Real.sqrt H * ((A + B) * Real.sqrt k) :=
      hc.trans (mul_le_mul_of_nonneg_left (hAB _ hLc) (by positivity))
    calc _ ≤ _ := gbm_em_pair_mismatch_le r σ T s₀ K ℓ
      _ ≤ Real.sqrt H * ((A + B) * Real.sqrt k) +
          Real.sqrt 2 * Real.sqrt H * ((A + B) * Real.sqrt k) := add_le_add h1 h2
      _ = _ := by rw [e]; ring
  refine ⟨(variance_digital_le_measureReal hm1 hm0 K).trans hP, hP,
    (integral_pow_four_digital_sub hm1 hm0 K).trans_le hP,
    fun h => inv_le_kurtosis_digital hm1 hm0 K h (by rw [hH, hk] at hP; exact hP)⟩

/-- **Table 5.2's `O(h^{1/2} log h)` for the digital option with Euler–Maruyama** (Giles 2015,
§5.1, p. 33, Table 5.2, l. 1425–1434: "Observed and theoretical convergence rates for the
multilevel correction variance for scalar SDEs", row "digital", l. 1431, Euler–Maruyama analysis
"`O(h^{1/2} log h)`"; l. 1457–1458: "the digital option analysis is due to Avikainen (Avikainen
2009)").  For GBM with `σ ≠ 0` and `T > 0` there is `C ≥ 0`, depending only on `r`, `σ` and `T`,
such that for every `s₀`, every strike `K` and every level `ℓ` with `h = T 2^{−(ℓ+1)} < e^{−1}`
the correction `ΔP_ℓ` of `gbm_em_digital_endpoint` satisfies `V[ΔP_ℓ]`, `P(ΔP_ℓ ≠ 0)`,
`E[ΔP_ℓ⁴] ≤ C (h log(1/h))^{1/2}`, and `(h log(1/h))^{1/2} ≤ h^{1/2} log(1/h)`, so
`V_ℓ = O(h^{1/2} |log h|)`.  The restriction `h < e^{−1}` makes `log(1/h) > 1`.  Proof:
`gbm_em_digital_endpoint` and `(ℓ + 1) log 2 = log T + log(1/h) ≤ (1 + |log T|) log(1/h)`, so
`C = C₀ ((1 + |log T|)/log 2)^{1/2}`. -/
theorem gbm_em_digital_endpoint_log (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ K : ℝ) (ℓ : ℕ), T / 2 ^ (ℓ + 1) < Real.exp (-1) →
      variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
        C * Real.sqrt (T / 2 ^ (ℓ + 1) * Real.log (T / 2 ^ (ℓ + 1))⁻¹) ∧
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ≤
        C * Real.sqrt (T / 2 ^ (ℓ + 1) * Real.log (T / 2 ^ (ℓ + 1))⁻¹) ∧
      ∫ z, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 4 ∂stdNormalSeq ≤
        C * Real.sqrt (T / 2 ^ (ℓ + 1) * Real.log (T / 2 ^ (ℓ + 1))⁻¹) ∧
      Real.sqrt (T / 2 ^ (ℓ + 1) * Real.log (T / 2 ^ (ℓ + 1))⁻¹) ≤
        Real.sqrt (T / 2 ^ (ℓ + 1)) * Real.log (T / 2 ^ (ℓ + 1))⁻¹ := by
  obtain ⟨C₀, hC₀, hmain⟩ := gbm_em_digital_endpoint r σ hσ hT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c := (1 + |Real.log T|) / Real.log 2 with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨C₀ * Real.sqrt c, by positivity, fun s₀ K ℓ hsmall => ?_⟩
  set h := T / 2 ^ (ℓ + 1) with hh
  have hh0 : 0 < h := by positivity
  have hlog1 : 1 < Real.log h⁻¹ := by
    have h1 : Real.exp 1 < h⁻¹ := by
      rw [Real.exp_neg] at hsmall
      exact (lt_inv_comm₀ hh0 (Real.exp_pos 1)).1 hsmall
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log h⁻¹ := Real.log_lt_log (Real.exp_pos 1) h1
  have hkey : Real.sqrt (h * ((ℓ : ℝ) + 1)) ≤ Real.sqrt c * Real.sqrt (h * Real.log h⁻¹) := by
    rw [← Real.sqrt_mul hc0]
    refine Real.sqrt_le_sqrt ?_
    have hk : ((ℓ : ℝ) + 1) * Real.log 2 = Real.log T + Real.log h⁻¹ := by
      have e : (2 : ℝ) ^ (ℓ + 1) = T * h⁻¹ := by rw [hh]; field_simp
      rw [← Real.log_mul hT.ne' (inv_pos.2 hh0).ne', ← e, Real.log_pow]
      push_cast
      ring
    have hk2 : (ℓ : ℝ) + 1 ≤ c * Real.log h⁻¹ := by
      rw [hc, div_mul_eq_mul_div, le_div_iff₀ hlog2, hk]
      have := le_abs_self (Real.log T)
      nlinarith [abs_nonneg (Real.log T)]
    calc h * ((ℓ : ℝ) + 1) ≤ h * (c * Real.log h⁻¹) := mul_le_mul_of_nonneg_left hk2 hh0.le
      _ = c * (h * Real.log h⁻¹) := by ring
  obtain ⟨hV, hP, h4, -⟩ := hmain s₀ K ℓ
  have hfin : C₀ * Real.sqrt (h * ((ℓ : ℝ) + 1)) ≤
      C₀ * Real.sqrt c * Real.sqrt (h * Real.log h⁻¹) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hkey hC₀
  refine ⟨hV.trans hfin, hP.trans hfin, h4.trans hfin, ?_⟩
  rw [Real.sqrt_mul hh0.le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg h)
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- The hypotheses of `gbm_em_digital_endpoint` hold in the paper's example (Giles 2015, §5.1,
p. 30, l. 1327–1330 and 1357–1359: "`r = 0.05`, `σ = 0.2`, `T = 1`, `S_0 = 100`, `K = 100`", the
digital payoff `H(S_T − K)`): the fraction of samples with the fine and coarse payoffs on either
side of the strike is `O((h_{ℓ+1} (ℓ + 1))^{1/2})`. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
    stdNormalSeq.real {z | (Set.Ioi (100 : ℝ)).indicator (1 : ℝ → ℝ)
        (gbmEM (1 / 20) (1 / 5) 1 100 (ℓ + 1) z) ≠
        (Set.Ioi 100).indicator 1 (gbmEM (1 / 20) (1 / 5) 1 100 ℓ (pairAvg z))} ≤
      C * Real.sqrt (1 / 2 ^ (ℓ + 1) * (ℓ + 1)) := by
  obtain ⟨C, hC, h⟩ := gbm_em_digital_endpoint (1 / 20) (1 / 5) (T := 1) (by norm_num) one_pos
  exact ⟨C, hC, fun ℓ => (h 100 100 ℓ).2.1⟩

end MLMC
