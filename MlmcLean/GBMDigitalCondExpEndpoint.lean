import MlmcLean.GBMDigitalCondExpExtras
import MlmcLean.GBMDigitalEndpoint

/-!
# The conditional-expectation estimator of the digital option for GBM: the endpoint `β = 3/2`
up to a logarithm (Giles 2015, §5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.2, paragraph
"Digital options", pp. 35–36, l. 1525–1590 of `docs/giles2015.txt`.  The text of p. 35,
l. 1541–1544: "We start by considering the fine path simulation, and make a slight change by using
the Euler-Maruyama discretisation for the final timestep, instead of the Milstein discretisation";
l. 1560–1578: "A similar treatment is used for the coarse path, except that in the final timestep,
we re-use the known value of the Brownian increment for the second last fine timestep, which
corresponds to the first half of the final coarse timestep. This results in the conditional
distribution for the coarse path underlying at maturity matching that of the fine path to within
`O(h)`, for both the mean and the standard deviation … Consequently, the difference in payoff
between the coarse and fine paths near the payoff discontinuity is `O(h^{1/2})`, giving a variance
which is approximately `O(h^{3/2})`, and a kurtosis which is approximately `O(h^{−1/2})`. This
leads to `α=1`, `β=3/2` and `γ=1`."  Table 5.2 (p. 33, l. 1425–1434), row "digital", Milstein:
numerics "`O(h^{3/2})`", analysis "`o(h^{3/2−δ})`" (l. 1431); the bound below sharpens that analysis
entry to `O(h^{3/2} (log(1/h))^{5/2})`.  The setting is that of `MlmcLean.GBMDigitalCondExp`:
geometric Brownian motion `dS = rS dt + σS dW`, the fine Milstein path of level `ℓ + 1`
(`N = 2^{ℓ+1}` steps of size `h = T 2^{−(ℓ+1)}`) driven by i.i.d. `Z_i ∼ N(0,1)` (`stdNormalSeq`),
its last (Euler–Maruyama) step replaced by the conditional expectation
`P^f_{ℓ+1} = Φ((m_f − K)/s_f)` (`gbmDigitalCondFine`), and the coarse path driven by the summed
increments (`pairAvg`), with the payoff `P^c_ℓ = Φ((m_c − K)/s_c)` (`gbmDigitalCondCoarse`).

**What is proved.**  `MlmcLean.GBMDigitalCondExp` (`gbm_digital_condExp_variance_rate`) gives
`V_ℓ = O(h_ℓ^q)` for every `q < 3/2` (for `K ≠ 0`).  This file proves the endpoint `q = 3/2` up to
the factor `(ℓ + 1)^{5/2} ≍ (log(1/h))^{5/2}`:
* `gbm_digital_condExp_variance_endpoint`: for `σ ≠ 0`, `T > 0` there is `C ≥ 0`, depending only
  on `r`, `σ` and `T`, such that for every `s₀ ≠ 0`, every strike `K` (`K = 0` included) and every
  level `ℓ + 1 ≥ 1`, `E[(P^f_{ℓ+1} − P^c_ℓ)²]` and `V[P^f_{ℓ+1} − P^c_ℓ]` are at most
  `C h^{3/2} (ℓ + 1)^{5/2}`, `h = T 2^{−(ℓ+1)}`; note `(ℓ + 1) log 2 = log(T/h)`.
* `gbm_digital_condExp_variance_rate_endpoint`: the same in the form of
  `gbm_digital_condExp_variance_rate` (fixed `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, now every `K`): the
  correction is square integrable, and its second moment and variance are
  `O(h^{3/2} (ℓ + 1)^{5/2})`.
* `gbm_digital_condExp_variance_endpoint_log`: the bound `C h^{3/2} (log(1/h))^{5/2}` with
  `log(1/h)` in place of `ℓ + 1` (the paper gives no logarithm for this estimator), on the levels
  with `h < e^{−1}` (where `log(1/h) > 1`).

**The route.**  The loss `q < 3/2` of `gbm_digital_condExp_variance_rate` comes from the tails of
the mismatch of the conditional means and standard deviations, bounded there by Markov's
inequality in a fixed `L^{2p}` (the constants of these bounds involve the moments of the lognormal
solution and grow too fast in `p` to let `p` grow with `log(1/h)`).  Here the logarithm of the
Milstein path against the exact solution is controlled on an event of probability `1 − O(h²)`:
* The Milstein factor `M(z) = 1 + rh + σ√h z + ½σ²h(z² − 1)` and the exact factor
  `e^{(r − σ²/2)h + σ√h z}` have the log-ratio `ψ = log M − (r − σ²/2)h − σ√h z`
  (`gbmMilLogRatio`) with `|ψ(z)| ≤ 26Λ³(√h(1 + |z|))³` (`gbmMilLogRatio_bounds`) and, since
  `M(z) M(−z) = (1 + (r − σ²/2)h + ½σ²hz²)² − σ²hz²`, `|ψ(z) + ψ(−z)| ≤ 87Λ³(√h(1 + |z|))⁴`
  (`abs_gbmMilLogRatio_add_neg_le`), `Λ = 1 + |r| + |σ| + σ²`: the terms of order `h^{3/2}` are odd
  in `z`, so the mean is `O(h²)` per step.
* Truncated at `|z| ≤ A`, `ψ` has `E[e^{sψ̃(Z)}] ≤ 1 + Dh` for `|s| ≤ 1/h`, `D = 720 · 49152 Λ⁶`
  (`integrable_integral_exp_mul_truncLogRatio_le`), so by Chernoff's bound the truncated log error
  of `m ≤ T/h` steps exceeds `x` with probability at most `2e^{−x/h + DT}`
  (`measureReal_lt_abs_sum_truncLogRatio_le`).  With `A = 4(ℓ + 1)^{1/2}`
  (`P(|Z| > A) ≤ √2 e^{−A²/4}`, `gaussianReal_real_lt_abs_le_exp`) and `x = h(4(ℓ + 1) + 2DT)`,
  outside an event of probability `O(4^{−(ℓ+1)}) = O(h²)` the fine value one step before maturity
  is `S e^F M(Z_{N−2})` and the coarse value is `S e^G` with `|F|, |G| ≤ x`, `S` the exact solution
  at `t_{N−2}` (`prod_gbmMilFactor_eq_mul_exp`; the coarse events are pulled back by the
  measure-preserving `pairAvg`).
* There the conditional means and standard deviations match to within `O(h (ℓ + 1))` and
  `O(h (ℓ + 1)^{1/2})` relative to the fine value, so (`abs_cdf_div_sub_cdf_div_le`) the payoffs
  differ by at most `2P(|Z| > t) + O(h^{1/2} (ℓ + 1))`, `t = 2(ℓ + 1)^{1/2}`, when `log|S_T|` lies
  within `O((h (ℓ + 1))^{1/2})` of `log|K|`, and by `2P(|Z| > t)` otherwise
  (`condPayoff_sq_le_of_good`, `condExp_sq_le_of_good_sample`).  The bounded density of `log|S_T|`
  (`gbmExact_logSmallBall`, uniform in `s₀` and `K`) gives `O(h (ℓ + 1)²) · O((h (ℓ + 1))^{1/2})`
  (`condExp_integral_sq_le`, `condExp_endpoint_scales`, `condExp_endpoint_small`); on the levels
  where `h (ℓ + 1)` is not small, `E[(P^f − P^c)²] ≤ 1 ≤ C (h (ℓ + 1))^{3/2}`.

**Deviations.**
* The logarithmic factor: the bound is `h^{3/2} (ℓ + 1)^{5/2}`, not the paper's "approximately
  `O(h^{3/2})`".  The power `5/2` comes from the sizes `A, t ≍ (log(1/h))^{1/2}` of the truncation
  and of the Gaussian tail and is not claimed to be sharp.
* The hypotheses are those of `MlmcLean.GBMDigitalCondExp`: `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`; the strike
  is arbitrary (for `K = 0` there is no window: on the good event the paths keep the sign of `s₀`),
  and since the analysis is in log scale the constant depends neither on `s₀` nor on `K`.
* The factor `25 e^{−rT}` of the paper's payoffs is omitted (it multiplies `C` by `625 e^{−2rT}`);
  as in `MlmcLean.GBMDigitalCondExp`, the coarse numerator uses the re-used increment `b ΔW_{N−2}`.
* The constants are explicit in the proofs (`condExp_endpoint_small`) but enormous and not meant to
  be sharp: at `r = 0.05`, `σ = 0.2`, `T = 1` the constant of the proof is of order `10³²`, so the
  bound is below `1` only from about level `83`, while a Monte Carlo check (scratch script, not in
  the repository; `10⁵` samples per level, `s₀ = K = 1`) gives `V_ℓ/h^{3/2} ≈ 0.0045` for
  `h = 2^{−4}, …, 2^{−8}`.

**Not proved.**  The bound without the logarithm; the kurtosis "approximately `O(h^{−1/2})`"
(l. 1577), which needs lower bounds; the weak-order endpoint `α = 1` (l. 1578); the endpoint for
the splitting estimator.  Theorem 1 for this estimator (l. 1578: "Since `β > γ`, the MLMC complexity
is `O(ε⁻²)`") is already proved without a logarithmic factor (`gbm_digital_condExp_theorem1`,
`gbm_digital_condExp_theorem1_all`), so no new complexity theorem is needed.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### The one-step log-ratio of the Milstein and the exact step of GBM -/

/-- **The logarithm of the ratio of one Milstein step of GBM to the exact step** (Giles 2015, §5.2,
p. 35, l. 1501–1506: "For a scalar SDE the Milstein discretisation is
`Ŝ_{n+1} = Ŝ_n + a(Ŝ_n,t_n)h + b(Ŝ_n,t_n)ΔW_n + ½ b(Ŝ_n,t_n) ∂b/∂S(Ŝ_n,t_n)(ΔW_n² − h)`", here with
`a(S) = rS`, `b(S) = σS`, against
the exact solution of GBM driven by the same increment): with the Milstein factor
`M = 1 + rk + σ√k x + ½σ²(k x² − k)` and the exact factor `e^{(r − σ²/2)k + σ√k x}`, this is
`log M − (r − σ²/2)k − σ√k x` (the value of `Real.log` at `M ≤ 0` is a junk value; it is only used
where `M ≥ ½`). -/
noncomputable def gbmMilLogRatio (r σ k x : ℝ) : ℝ :=
  Real.log (gbmMilFactor r σ k x) - ((r - σ ^ 2 / 2) * k + σ * Real.sqrt k * x)

/-- The Milstein log-ratio is measurable (Giles 2015, §5.2). -/
lemma measurable_gbmMilLogRatio (r σ k : ℝ) : Measurable (gbmMilLogRatio r σ k) := by
  have h := measurable_gbmMilFactor r σ k
  unfold gbmMilLogRatio
  exact (Real.measurable_log.comp h).sub (by fun_prop)

/-- Where the Milstein factor is positive it is the exact factor times `e^ψ`, `ψ` the log-ratio
(Giles 2015, §5.2). -/
lemma gbmMilFactor_eq_mul_exp (r σ k x : ℝ) (h : 0 < gbmMilFactor r σ k x) :
    gbmMilFactor r σ k x = gbmExpFactor r σ k x * Real.exp (gbmMilLogRatio r σ k x) := by
  unfold gbmExpFactor gbmMilLogRatio
  rw [← Real.exp_add, add_sub_cancel, Real.exp_log h]

/-- **The scales of one Milstein step of GBM** (Giles 2015, §5.2, p. 35, l. 1501–1506, the Milstein
discretisation of GBM): with
`Λ = 1 + |r| + |σ| + σ²` and `θ = √k (1 + |x|) ≤ 1/(4Λ)`, the parts `p = σ√k x` and
`v = rk + ½σ²(kx² − k)` of the Milstein factor `1 + p + v` satisfy `|p| ≤ Λθ`, `|v| ≤ Λθ²`; also
`1 ≤ Λ`, `Λθ ≤ ¼` and `k ≤ θ²`. -/
lemma gbmMil_step_scales (r σ : ℝ) {k x : ℝ} (hk : 0 ≤ k)
    (hθ : Real.sqrt k * (1 + |x|) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2))) :
    1 ≤ 1 + |r| + |σ| + σ ^ 2 ∧ 0 ≤ Real.sqrt k * (1 + |x|) ∧
      (1 + |r| + |σ| + σ ^ 2) * (Real.sqrt k * (1 + |x|)) ≤ 1 / 4 ∧
      k ≤ (Real.sqrt k * (1 + |x|)) ^ 2 ∧
      |σ * (Real.sqrt k * x)| ≤ (1 + |r| + |σ| + σ ^ 2) * (Real.sqrt k * (1 + |x|)) ∧
      |r * k + σ ^ 2 / 2 * ((Real.sqrt k * x) ^ 2 - k)| ≤
        (1 + |r| + |σ| + σ ^ 2) * (Real.sqrt k * (1 + |x|)) ^ 2 := by
  set Λ := 1 + |r| + |σ| + σ ^ 2 with hΛ
  set sk := Real.sqrt k with hsk
  set θ := sk * (1 + |x|) with hθdef
  have hr0 := abs_nonneg r
  have hσ0 := abs_nonneg σ
  have hσ2 := sq_nonneg σ
  have hΛ1 : 1 ≤ Λ := by linarith
  have hsk0 : 0 ≤ sk := Real.sqrt_nonneg k
  have hskk : sk ^ 2 = k := Real.sq_sqrt hk
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hθ0 : 0 ≤ θ := by positivity
  have hΛθ : Λ * θ ≤ 1 / 4 := by
    have h4 : 0 < 4 * Λ := by positivity
    rw [le_div_iff₀ h4] at hθ
    linarith
  have hsx : sk * |x| ≤ θ := by
    rw [hθdef, mul_add, mul_one]
    linarith
  have hp' : |σ * (sk * x)| ≤ Λ * θ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hsk0]
    have h1 : |σ| ≤ Λ := by linarith
    exact mul_le_mul h1 hsx (by positivity) (by linarith)
  have hk2 : k ≤ θ ^ 2 := by
    rw [hθdef, mul_pow]
    calc k = sk ^ 2 * 1 := by rw [hskk, mul_one]
      _ ≤ sk ^ 2 * (1 + |x|) ^ 2 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith)) (sq_nonneg sk)
  have hkx : (sk * x) ^ 2 + k ≤ θ ^ 2 := by
    rw [hθdef, mul_pow, mul_pow, ← sq_abs x, ← hskk]
    have e : sk ^ 2 * (1 + |x|) ^ 2 = sk ^ 2 * |x| ^ 2 + sk ^ 2 + 2 * (sk ^ 2 * |x|) := by ring
    rw [e]
    linarith [mul_nonneg (sq_nonneg sk) hx0]
  have hv' : |r * k + σ ^ 2 / 2 * ((sk * x) ^ 2 - k)| ≤ Λ * θ ^ 2 := by
    have h1 : |r * k| ≤ |r| * θ ^ 2 := by
      rw [abs_mul, abs_of_nonneg hk]
      exact mul_le_mul_of_nonneg_left hk2 (abs_nonneg r)
    have h2 : |σ ^ 2 / 2 * ((sk * x) ^ 2 - k)| ≤ σ ^ 2 / 2 * θ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ σ ^ 2 / 2)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [abs_le]
      constructor <;> linarith [sq_nonneg (sk * x)]
    have h3 : 0 ≤ (1 + |σ| + σ ^ 2 / 2) * θ ^ 2 := by positivity
    calc |r * k + σ ^ 2 / 2 * ((sk * x) ^ 2 - k)| ≤ |r| * θ ^ 2 + σ ^ 2 / 2 * θ ^ 2 :=
          (abs_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ Λ * θ ^ 2 := by
          rw [hΛ]
          linarith
  exact ⟨hΛ1, hθ0, hΛθ, hk2, hp', hv'⟩

/-- **The Milstein step of GBM against the exact step** (Giles 2015, §5.2, p. 35, l. 1499–1500: the
Milstein discretisation "gives first order strong convergence under certain conditions"; here one
step against the exact step, with explicit constants).  With
`Λ = 1 + |r| + |σ| + σ²` and `θ = √k (1 + |x|) ≤ 1/(4Λ)`: `|M − 1| ≤ 2Λθ` for the Milstein factor
`M` and `|ψ| ≤ 26 Λ³ θ³` for the log-ratio `ψ = log M − (r − σ²/2)k − σ√k x`.  Proof: with
`p = σ√k x`, `v = rk + ½σ²(kx² − k)`, `u = M − 1 = p + v`, `ψ = log(1 + u) − u + u²/2 + (p² − u²)/2`
and `p² − u² = −v(2p + v)`. -/
lemma gbmMilLogRatio_bounds (r σ : ℝ) {k x : ℝ} (hk : 0 ≤ k)
    (hθ : Real.sqrt k * (1 + |x|) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2))) :
    |gbmMilFactor r σ k x - 1| ≤ 2 * (1 + |r| + |σ| + σ ^ 2) * (Real.sqrt k * (1 + |x|)) ∧
      |gbmMilLogRatio r σ k x| ≤
        26 * (1 + |r| + |σ| + σ ^ 2) ^ 3 * (Real.sqrt k * (1 + |x|)) ^ 3 := by
  obtain ⟨hΛ1, hθ0, hΛθ, -, hp', hv'⟩ := gbmMil_step_scales r σ hk hθ
  set Λ := 1 + |r| + |σ| + σ ^ 2 with hΛ
  set sk := Real.sqrt k with hsk
  set θ := sk * (1 + |x|) with hθdef
  have hskk : sk ^ 2 = k := Real.sq_sqrt hk
  have hθ1 : θ ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_right hΛ1 hθ0
    linarith
  set p := σ * (sk * x) with hp
  set v := r * k + σ ^ 2 / 2 * ((sk * x) ^ 2 - k) with hv
  have hu : gbmMilFactor r σ k x - 1 = p + v := by
    unfold gbmMilFactor
    rw [hp, hv, hsk]
    ring
  have hΛθ2 : Λ * θ ^ 2 ≤ Λ * θ := by
    have : θ ^ 2 ≤ θ := by
      rw [sq]
      exact mul_le_of_le_one_left hθ0 (by linarith)
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have huu : |p + v| ≤ 2 * Λ * θ := by
    have := abs_add_le p v
    linarith
  refine ⟨?_, ?_⟩
  · rw [hu]
    exact huu
  have hψ : gbmMilLogRatio r σ k x =
      (Real.log (1 + (p + v)) - (p + v) + (p + v) ^ 2 / 2) - v * (2 * p + v) / 2 := by
    unfold gbmMilLogRatio
    rw [show gbmMilFactor r σ k x = 1 + (p + v) by linarith, ← hsk, hp, hv, ← hskk]
    ring
  have hu2 : -(1 / 2) ≤ p + v := by
    have := neg_abs_le (p + v)
    linarith
  have hT := abs_log_one_add_sub_quadratic_le hu2
  have h3 : |p + v| ^ 3 ≤ (2 * Λ * θ) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) huu 3
  have h5 : |2 * p + v| ≤ 3 * Λ * θ := by
    have := abs_add_le (2 * p) v
    rw [abs_mul, abs_two] at this
    linarith
  have h4 : |v * (2 * p + v) / 2| ≤ Λ * θ ^ 2 * (3 * Λ * θ) / 2 := by
    rw [abs_div, abs_mul, abs_two]
    have := mul_le_mul hv' h5 (abs_nonneg _) (by positivity)
    linarith
  rw [hψ]
  have hsplit := abs_sub (Real.log (1 + (p + v)) - (p + v) + (p + v) ^ 2 / 2)
    (v * (2 * p + v) / 2)
  have hΛ2 : Λ ^ 2 ≤ Λ ^ 3 := by
    calc Λ ^ 2 = Λ ^ 2 * 1 := (mul_one _).symm
      _ ≤ Λ ^ 2 * Λ := mul_le_mul_of_nonneg_left hΛ1 (sq_nonneg Λ)
      _ = Λ ^ 3 := by ring
  have hθ3 : 0 ≤ θ ^ 3 := by positivity
  have e1 : Λ * θ ^ 2 * (3 * Λ * θ) / 2 = 3 / 2 * (Λ ^ 2 * θ ^ 3) := by ring
  have e2 : (2 * Λ * θ) ^ 3 = 8 * (Λ ^ 3 * θ ^ 3) := by ring
  have h6 := mul_le_mul_of_nonneg_right hΛ2 hθ3
  rw [e1] at h4
  rw [e2] at h3
  have e3 : 26 * Λ ^ 3 * θ ^ 3 = 26 * (Λ ^ 3 * θ ^ 3) := by ring
  rw [e3]
  have h7 : 0 ≤ Λ ^ 3 * θ ^ 3 := by positivity
  linarith

/-- **The odd part of the Milstein log-ratio cancels to order `k²`** (Giles 2015, §5.2, p. 35,
l. 1499–1500; the mean of the log-ratio is `O(k²)`, so its sum over the `T/k` steps of a path is
`O(k)`).  With `Λ`, `θ = √k (1 + |x|) ≤ 1/(4Λ)` as in `gbmMilLogRatio_bounds`:
`|ψ(x) + ψ(−x)| ≤ 87 Λ³ θ⁴`.  Proof: `M(x) M(−x) = (1 + v)² − p² = 1 + ω` with `ω = 2bk + v²`,
`b = r − σ²/2`, so `ψ(x) + ψ(−x) = log(1 + ω) − 2bk = log(1 + ω) − ω + v²`. -/
lemma abs_gbmMilLogRatio_add_neg_le (r σ : ℝ) {k x : ℝ} (hk : 0 ≤ k)
    (hθ : Real.sqrt k * (1 + |x|) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2))) :
    |gbmMilLogRatio r σ k x + gbmMilLogRatio r σ k (-x)| ≤
      87 * (1 + |r| + |σ| + σ ^ 2) ^ 3 * (Real.sqrt k * (1 + |x|)) ^ 4 := by
  have hθ' : Real.sqrt k * (1 + |-x|) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2)) := by
    rw [abs_neg]
    exact hθ
  obtain ⟨hΛ1, hθ0, hΛθ, hk2, -, hv'⟩ := gbmMil_step_scales r σ hk hθ
  have hM1 := (gbmMilLogRatio_bounds r σ hk hθ).1
  have hM2 := (gbmMilLogRatio_bounds r σ hk hθ').1
  rw [abs_neg] at hM2
  set Λ := 1 + |r| + |σ| + σ ^ 2 with hΛ
  set sk := Real.sqrt k with hsk
  set θ := sk * (1 + |x|) with hθdef
  have hθ1 : θ ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_right hΛ1 hθ0
    linarith
  have hpos1 : 0 < gbmMilFactor r σ k x := by
    have := (abs_le.1 hM1).1
    linarith
  have hpos2 : 0 < gbmMilFactor r σ k (-x) := by
    have := (abs_le.1 hM2).1
    linarith
  set v := r * k + σ ^ 2 / 2 * ((sk * x) ^ 2 - k) with hv
  set ω := 2 * (r - σ ^ 2 / 2) * k + v ^ 2 with hω
  have eprod : gbmMilFactor r σ k x * gbmMilFactor r σ k (-x) = 1 + ω := by
    unfold gbmMilFactor
    rw [hω, hv, hsk]
    ring
  have esum : gbmMilLogRatio r σ k x + gbmMilLogRatio r σ k (-x) =
      (Real.log (1 + ω) - ω + ω ^ 2 / 2) - ω ^ 2 / 2 + v ^ 2 := by
    unfold gbmMilLogRatio
    have e : Real.log (gbmMilFactor r σ k x) - ((r - σ ^ 2 / 2) * k + σ * Real.sqrt k * x) +
        (Real.log (gbmMilFactor r σ k (-x)) - ((r - σ ^ 2 / 2) * k + σ * Real.sqrt k * -x)) =
        Real.log (gbmMilFactor r σ k x * gbmMilFactor r σ k (-x)) -
          2 * (r - σ ^ 2 / 2) * k := by
      rw [Real.log_mul hpos1.ne' hpos2.ne']
      ring
    rw [e, eprod, hω]
    ring
  have hb : |2 * (r - σ ^ 2 / 2) * k| ≤ 2 * Λ * θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hk]
    have h1 : |r - σ ^ 2 / 2| ≤ Λ := by
      have := abs_sub r (σ ^ 2 / 2)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ σ ^ 2 / 2)] at this
      have := abs_nonneg σ
      have := sq_nonneg σ
      linarith
    have := mul_le_mul h1 hk2 hk (by linarith)
    linarith
  have hΛθ2 : Λ * θ ^ 2 ≤ 1 / 16 := by
    calc Λ * θ ^ 2 = (Λ * θ) * θ := by ring
      _ ≤ (1 / 4) * (1 / 4) := mul_le_mul hΛθ hθ1 hθ0 (by norm_num)
      _ = 1 / 16 := by norm_num
  have hΛθ20 : 0 ≤ Λ * θ ^ 2 := by positivity
  have hv2 : v ^ 2 ≤ Λ ^ 2 * θ ^ 4 := by
    calc v ^ 2 = |v| ^ 2 := (sq_abs v).symm
      _ ≤ (Λ * θ ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg v) hv' 2
      _ = Λ ^ 2 * θ ^ 4 := by ring
  have hv2' : v ^ 2 ≤ Λ * θ ^ 2 := by
    have e : Λ ^ 2 * θ ^ 4 = (Λ * θ ^ 2) * (Λ * θ ^ 2) := by ring
    have : (Λ * θ ^ 2) * (Λ * θ ^ 2) ≤ Λ * θ ^ 2 :=
      mul_le_of_le_one_right hΛθ20 (by linarith)
    linarith
  have hω' : |ω| ≤ 3 * Λ * θ ^ 2 := by
    have := abs_add_le (2 * (r - σ ^ 2 / 2) * k) (v ^ 2)
    rw [abs_of_nonneg (sq_nonneg v)] at this
    rw [hω]
    linarith
  have hωh : -(1 / 2) ≤ ω := by
    have := neg_abs_le ω
    linarith
  have hT := abs_log_one_add_sub_quadratic_le hωh
  rw [esum]
  have hω3 : |ω| ^ 3 ≤ (3 * Λ * θ ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hω' 3
  have hω2 : ω ^ 2 ≤ (3 * Λ * θ ^ 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω' 2
  have hθ2 : θ ^ 2 ≤ 1 := by
    rw [sq]
    exact mul_le_one₀ (by linarith) hθ0 (by linarith)
  have hΛ2 : Λ ^ 2 ≤ Λ ^ 3 := by
    calc Λ ^ 2 = Λ ^ 2 * 1 := (mul_one _).symm
      _ ≤ Λ ^ 2 * Λ := mul_le_mul_of_nonneg_left hΛ1 (sq_nonneg Λ)
      _ = Λ ^ 3 := by ring
  have hθ4 : 0 ≤ θ ^ 4 := by positivity
  have e3 : (3 * Λ * θ ^ 2) ^ 3 = 27 * (Λ ^ 3 * θ ^ 4) * θ ^ 2 := by ring
  have h6 : 27 * (Λ ^ 3 * θ ^ 4) * θ ^ 2 ≤ 27 * (Λ ^ 3 * θ ^ 4) :=
    mul_le_of_le_one_right (by positivity) hθ2
  have h7 := mul_le_mul_of_nonneg_right hΛ2 hθ4
  have e4 : (3 * Λ * θ ^ 2) ^ 2 = 9 * (Λ ^ 2 * θ ^ 4) := by ring
  rw [e3] at hω3
  rw [e4] at hω2
  have hsplit := abs_add_le ((Real.log (1 + ω) - ω + ω ^ 2 / 2) - ω ^ 2 / 2) (v ^ 2)
  have hsplit2 := abs_sub (Real.log (1 + ω) - ω + ω ^ 2 / 2) (ω ^ 2 / 2)
  rw [abs_of_nonneg (sq_nonneg v)] at hsplit
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ω ^ 2 / 2)] at hsplit2
  have e5 : 87 * Λ ^ 3 * θ ^ 4 = 87 * (Λ ^ 3 * θ ^ 4) := by ring
  rw [e5]
  have h8 : 0 ≤ Λ ^ 3 * θ ^ 4 := by positivity
  have h9 : 0 ≤ Λ ^ 2 * θ ^ 4 := by positivity
  linarith

/-! ### Gaussian tails and an exponential moment -/

/-- **A Gaussian tail** (Giles 2015, §5.2: the increments of a path are, with high probability, at
most of order `√(log(1/h))`): `P(|Z| > A) ≤ √2 e^{−A²/4}` for `Z ∼ N(0,1)` and `A ≥ 0` (Markov's
inequality for `e^{Z²/4}` and `E[e^{Z²/4}] ≤ √2`). -/
lemma gaussianReal_real_lt_abs_le_exp {A : ℝ} (hA : 0 ≤ A) :
    (gaussianReal 0 1).real {x | A < |x|} ≤ Real.sqrt 2 * Real.exp (-(A ^ 2 / 4)) := by
  have h : Real.exp (1 / 4 * A ^ 2) *
      (gaussianReal 0 1).real {x | Real.exp (1 / 4 * A ^ 2) ≤ Real.exp (1 / 4 * x ^ 2)} ≤
      ∫ x, Real.exp (1 / 4 * x ^ 2) ∂gaussianReal 0 1 :=
    mul_meas_ge_le_integral_of_nonneg (μ := gaussianReal 0 1)
      (Eventually.of_forall fun x => (Real.exp_pos (1 / 4 * x ^ 2)).le)
      (integrable_exp_mul_sq_gaussian (by norm_num : (1 / 4 : ℝ) < 1 / 2)) _
  have hsub : {x : ℝ | A < |x|} ⊆
      {x | Real.exp (1 / 4 * A ^ 2) ≤ Real.exp (1 / 4 * x ^ 2)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    refine Real.exp_le_exp.2 ?_
    have : A ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]
      exact pow_le_pow_left₀ hA hx.le 2
    linarith
  have hm := measureReal_mono (μ := gaussianReal 0 1) hsub
  have hI := integral_exp_mul_sq_gaussian_le (a := 1 / 4) le_rfl
  have hpos := Real.exp_pos (1 / 4 * A ^ 2)
  have he : Real.exp (-(A ^ 2 / 4)) = (Real.exp (1 / 4 * A ^ 2))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  rw [he, ← div_eq_mul_inv, le_div_iff₀ hpos]
  nlinarith

/-- `(1 + |y|)⁶ e^{(1+|y|)²/16} ≤ 24576 e^{1/4} e^{y²/4}` (`w³ ≤ 6e^w` with `w = (1 + |y|)²/16`;
the moment generating function of the Milstein log-ratio, Giles 2015, §5.2). -/
lemma pow_six_mul_exp_le (y : ℝ) :
    (1 + |y|) ^ 6 * Real.exp ((1 + |y|) ^ 2 / 16) ≤
      24576 * Real.exp (1 / 4) * Real.exp (1 / 4 * y ^ 2) := by
  set w := (1 + |y|) ^ 2 / 16 with hw
  have hw0 : 0 ≤ w := by positivity
  have h1 : (1 + |y|) ^ 6 = 4096 * w ^ 3 := by
    rw [hw]
    ring
  have h2 : w ^ 3 ≤ 6 * Real.exp w := by
    have := Real.pow_div_factorial_le_exp w hw0 3
    norm_num [Nat.factorial] at this
    linarith
  have h3 : 2 * w ≤ 1 / 4 + 1 / 4 * y ^ 2 := by
    rw [hw]
    nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
  calc (1 + |y|) ^ 6 * Real.exp w = 4096 * w ^ 3 * Real.exp w := by rw [h1]
    _ ≤ 4096 * (6 * Real.exp w) * Real.exp w := by gcongr
    _ = 24576 * Real.exp (2 * w) := by
        rw [two_mul, Real.exp_add]
        ring
    _ ≤ 24576 * Real.exp (1 / 4 + 1 / 4 * y ^ 2) := by gcongr
    _ = _ := by
        rw [Real.exp_add]
        ring

/-- **An exponential moment of the standard normal law** (the moment generating function of the
Milstein log-ratio, Giles 2015, §5.2): `(1 + |Z|)⁶ e^{(1+|Z|)²/16}` is integrable and its mean is
at most `49152` (`pow_six_mul_exp_le`, `E[e^{Z²/4}] ≤ √2`, `e^{1/4}√2 ≤ 2`). -/
lemma integrable_integral_pow_six_mul_exp :
    Integrable (fun y : ℝ => (1 + |y|) ^ 6 * Real.exp ((1 + |y|) ^ 2 / 16)) (gaussianReal 0 1) ∧
      ∫ y, (1 + |y|) ^ 6 * Real.exp ((1 + |y|) ^ 2 / 16) ∂gaussianReal 0 1 ≤ 49152 := by
  have hint := (integrable_exp_mul_sq_gaussian (a := 1 / 4) (by norm_num)).const_mul
    (24576 * Real.exp (1 / 4))
  have hm : Measurable fun y : ℝ => (1 + |y|) ^ 6 * Real.exp ((1 + |y|) ^ 2 / 16) := by fun_prop
  have hi : Integrable (fun y : ℝ => (1 + |y|) ^ 6 * Real.exp ((1 + |y|) ^ 2 / 16))
      (gaussianReal 0 1) :=
    hint.mono' hm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_six_mul_exp_le y)
  refine ⟨hi, ?_⟩
  calc _ ≤ ∫ y, 24576 * Real.exp (1 / 4) * Real.exp (1 / 4 * y ^ 2) ∂gaussianReal 0 1 :=
        integral_mono hi hint pow_six_mul_exp_le
    _ = 24576 * Real.exp (1 / 4) * ∫ y, Real.exp (1 / 4 * y ^ 2) ∂gaussianReal 0 1 :=
        integral_const_mul _ _
    _ ≤ 24576 * Real.exp (1 / 4) * Real.sqrt 2 := by
        gcongr
        exact integral_exp_mul_sq_gaussian_le le_rfl
    _ ≤ 49152 := by
        have := exp_quarter_mul_sqrt_two_le
        nlinarith

/-- The standard normal law is symmetric: `E[f(−Z)] = E[f(Z)]` (the odd terms of the Milstein
log-ratio cancel in the mean, Giles 2015, §5.2). -/
lemma integral_comp_neg_gaussianReal {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f (-x) ∂gaussianReal 0 1 = ∫ x, f x ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  conv_rhs => rw [← hmap]
  rw [integral_map measurable_neg.aemeasurable]
  rw [hmap]
  exact hf.aestronglyMeasurable

/-! ### Chernoff's bound for the truncated Milstein log error -/

/-- The truncation `1_{|·| ≤ A} f` at a point with `|y| ≤ A` (Giles 2015, §5.2). -/
lemma indicator_abs_le_of_le {A y : ℝ} (f : ℝ → ℝ) (hy : |y| ≤ A) :
    {x : ℝ | |x| ≤ A}.indicator f y = f y :=
  Set.indicator_of_mem (show y ∈ {x : ℝ | |x| ≤ A} from hy) f

/-- The truncation `1_{|·| ≤ A} f` at a point with `|y| > A` (Giles 2015, §5.2). -/
lemma indicator_abs_le_of_not_le {A y : ℝ} (f : ℝ → ℝ) (hy : ¬ |y| ≤ A) :
    {x : ℝ | |x| ≤ A}.indicator f y = 0 :=
  Set.indicator_of_notMem (show y ∉ {x : ℝ | |x| ≤ A} from hy) f

/-- **The moment generating function of the truncated Milstein log-ratio** (Giles 2015, §5.2,
p. 36, l. 1563–1566: the coarse and the fine path "matching … to within `O(h)`"; here the
logarithm of one Milstein step against the exact step).  Let `Λ = 1 + |r| + |σ| + σ²`, `k > 0`,
`A` with `√k (1 + A) ≤ 1/(4Λ)` and `26 Λ³ √k (1 + A) ≤ 1/16`, and `ψ̃ = 1_{|·| ≤ A} ψ` the
log-ratio `ψ` of `gbmMilLogRatio` truncated at `A`.  Then for `|s| ≤ 1/k`, `e^{sψ̃(Z)}` is
integrable and `E[e^{sψ̃(Z)}] ≤ 1 + 720 · 49152 Λ⁶ k`.  Proof: `e^y ≤ 1 + y + y² max(1, e^y)`,
`|sψ̃| ≤ (1 + |Z|)²/16`, `(sψ̃)² ≤ 676 Λ⁶ k (1 + |Z|)⁶` (`gbmMilLogRatio_bounds`), and
`|E[ψ̃]| = ½|E[ψ̃(Z) + ψ̃(−Z)]| ≤ 44 Λ³ k² E[(1 + |Z|)⁴]` (`abs_gbmMilLogRatio_add_neg_le`): the
terms of order `k^{3/2}` are odd in `Z` and cancel. -/
lemma integrable_integral_exp_mul_truncLogRatio_le (r σ : ℝ) {k A s : ℝ} (hk : 0 < k)
    (hθ : Real.sqrt k * (1 + A) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2)))
    (hθ' : 26 * (1 + |r| + |σ| + σ ^ 2) ^ 3 * (Real.sqrt k * (1 + A)) ≤ 1 / 16)
    (hs : |s| ≤ 1 / k) :
    Integrable (fun x => Real.exp (s * {y : ℝ | |y| ≤ A}.indicator (gbmMilLogRatio r σ k) x))
        (gaussianReal 0 1) ∧
      ∫ x, Real.exp (s * {y : ℝ | |y| ≤ A}.indicator (gbmMilLogRatio r σ k) x)
          ∂gaussianReal 0 1 ≤ 1 + 720 * 49152 * (1 + |r| + |σ| + σ ^ 2) ^ 6 * k := by
  obtain ⟨hgi, hgb⟩ := integrable_integral_pow_six_mul_exp
  set Λ := 1 + |r| + |σ| + σ ^ 2 with hΛ
  set ψt := {y : ℝ | |y| ≤ A}.indicator (gbmMilLogRatio r σ k) with hψt
  set g : ℝ → ℝ := fun y => (1 + |y|) ^ 6 * Real.exp ((1 + |y|) ^ 2 / 16) with hg
  have hΛ1 : 1 ≤ Λ := by
    have := abs_nonneg r
    have := abs_nonneg σ
    have := sq_nonneg σ
    linarith
  have hΛ0 : 0 < Λ := by linarith
  set sk := Real.sqrt k with hskdef
  have hsk : 0 < sk := Real.sqrt_pos.2 hk
  have hskk : sk ^ 2 = k := Real.sq_sqrt hk.le
  have hS : MeasurableSet {y : ℝ | |y| ≤ A} := measurableSet_le (by fun_prop) measurable_const
  have hψm : Measurable ψt := (measurable_gbmMilLogRatio r σ k).indicator hS
  have hgm : Measurable g := by rw [hg]; fun_prop
  have hg1 : ∀ y : ℝ, (1 + |y|) ^ 6 ≤ g y := fun y =>
    le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  have hgexp : ∀ y : ℝ, Real.exp ((1 + |y|) ^ 2 / 16) ≤ g y := fun y =>
    le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ (by linarith [abs_nonneg y]))
  have hgeq : ∀ y : ℝ, g y = (1 + |y|) ^ 6 * Real.exp ((1 + |y|) ^ 2 / 16) := fun y => rfl
  clear_value Λ ψt g sk
  have hg0 : ∀ y : ℝ, 0 ≤ g y := fun y => le_trans (by positivity) (hg1 y)
  have hθy : ∀ y : ℝ, |y| ≤ A → sk * (1 + |y|) ≤ 1 / (4 * Λ) := fun y hy =>
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hsk.le) hθ
  have hθy' : ∀ y : ℝ, |y| ≤ A →
      Real.sqrt k * (1 + |y|) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2)) := fun y hy => by
    rw [← hskdef, ← hΛ]
    exact hθy y hy
  have hbd : ∀ y : ℝ, |y| ≤ A →
      |gbmMilLogRatio r σ k y| ≤ 26 * Λ ^ 3 * (sk * (1 + |y|)) ^ 3 := fun y hy => by
    have := (gbmMilLogRatio_bounds r σ hk.le (hθy' y hy)).2
    rw [← hskdef, ← hΛ] at this
    exact this
  have hbd2 : ∀ y : ℝ, |y| ≤ A →
      |gbmMilLogRatio r σ k y + gbmMilLogRatio r σ k (-y)| ≤
        87 * Λ ^ 3 * (sk * (1 + |y|)) ^ 4 := fun y hy => by
    have := abs_gbmMilLogRatio_add_neg_le r σ hk.le (hθy' y hy)
    rw [← hskdef, ← hΛ] at this
    exact this
  have hpow : ∀ y : ℝ, ∀ n : ℕ, n ≤ 6 → (1 + |y|) ^ n ≤ g y := fun y n hn =>
    (pow_le_pow_right₀ (by linarith [abs_nonneg y]) hn).trans (hg1 y)
  -- the pointwise bounds
  have hb : ∀ y, |s * ψt y| ≤ (1 + |y|) ^ 2 / 16 ∧
      (s * ψt y) ^ 2 ≤ 676 * Λ ^ 6 * k * (1 + |y|) ^ 6 := by
    intro y
    by_cases hy : |y| ≤ A
    · have hψy : ψt y = gbmMilLogRatio r σ k y := by
        rw [hψt]
        exact indicator_abs_le_of_le _ hy
      rw [hψy]
      have h1 := hbd y hy
      have e : (sk * (1 + |y|)) ^ 3 = k * (sk * (1 + |y|) ^ 3) := by
        rw [← hskk]
        ring
      have habs : |s * gbmMilLogRatio r σ k y| ≤ 26 * Λ ^ 3 * (sk * (1 + |y|) ^ 3) := by
        rw [abs_mul]
        calc |s| * |gbmMilLogRatio r σ k y| ≤ (1 / k) * (26 * Λ ^ 3 * (sk * (1 + |y|)) ^ 3) :=
              mul_le_mul hs h1 (abs_nonneg _) (by positivity)
          _ = 26 * Λ ^ 3 * (sk * (1 + |y|) ^ 3) := by
              rw [e]
              field_simp
      constructor
      · have h2 : 26 * Λ ^ 3 * (sk * (1 + |y|)) ≤ 1 / 16 := by
          refine le_trans ?_ hθ'
          gcongr
        calc |s * gbmMilLogRatio r σ k y| ≤ 26 * Λ ^ 3 * (sk * (1 + |y|) ^ 3) := habs
          _ = 26 * Λ ^ 3 * (sk * (1 + |y|)) * (1 + |y|) ^ 2 := by ring
          _ ≤ 1 / 16 * (1 + |y|) ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = (1 + |y|) ^ 2 / 16 := by ring
      · calc (s * gbmMilLogRatio r σ k y) ^ 2 = |s * gbmMilLogRatio r σ k y| ^ 2 :=
              (sq_abs _).symm
          _ ≤ (26 * Λ ^ 3 * (sk * (1 + |y|) ^ 3)) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) habs 2
          _ = 676 * Λ ^ 6 * k * (1 + |y|) ^ 6 := by
              rw [← hskk]
              ring
    · rw [hψt, indicator_abs_le_of_not_le _ hy, mul_zero, abs_zero]
      constructor
      · positivity
      · rw [sq, mul_zero]
        positivity
  -- integrability
  have hψb : ∀ y, |ψt y| ≤ 26 * Λ ^ 3 * sk ^ 3 * g y := by
    intro y
    by_cases hy : |y| ≤ A
    · rw [hψt, indicator_abs_le_of_le _ hy]
      calc |gbmMilLogRatio r σ k y| ≤ 26 * Λ ^ 3 * (sk * (1 + |y|)) ^ 3 := hbd y hy
        _ = 26 * Λ ^ 3 * sk ^ 3 * (1 + |y|) ^ 3 := by ring
        _ ≤ 26 * Λ ^ 3 * sk ^ 3 * g y :=
            mul_le_mul_of_nonneg_left (hpow y 3 (by norm_num)) (by positivity)
    · rw [hψt, indicator_abs_le_of_not_le _ hy, abs_zero]
      have := hg0 y
      positivity
  have hψi : Integrable ψt (gaussianReal 0 1) :=
    (hgi.const_mul (26 * Λ ^ 3 * sk ^ 3)).mono' hψm.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hψb y)
  have hψi' : Integrable (fun y => ψt (-y)) (gaussianReal 0 1) :=
    (hgi.const_mul (26 * Λ ^ 3 * sk ^ 3)).mono' (hψm.comp measurable_neg).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        have h := hψb (-y)
        rw [hgeq, abs_neg, ← hgeq] at h
        exact h)
  have hEi : Integrable (fun x => Real.exp (s * ψt x)) (gaussianReal 0 1) := by
    refine hgi.mono' (by fun_prop) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (s * ψt y) ≤ Real.exp ((1 + |y|) ^ 2 / 16) :=
          Real.exp_le_exp.2 ((le_abs_self _).trans (hb y).1)
      _ ≤ g y := hgexp y
  refine ⟨hEi, ?_⟩
  -- the pointwise Taylor bound
  have hpt2 : ∀ y, Real.exp (s * ψt y) ≤ 1 + s * ψt y + 676 * Λ ^ 6 * k * g y := by
    intro y
    have hT := (exp_sub_one_sub_le_sq_mul_max (s * ψt y)).2
    have hmax : max 1 (Real.exp (s * ψt y)) ≤ Real.exp ((1 + |y|) ^ 2 / 16) :=
      max_le (Real.one_le_exp (by positivity))
        (Real.exp_le_exp.2 ((le_abs_self _).trans (hb y).1))
    have hm0 : 0 ≤ max 1 (Real.exp (s * ψt y)) := le_trans zero_le_one (le_max_left _ _)
    have hc0 : 0 ≤ 676 * Λ ^ 6 * k * (1 + |y|) ^ 6 := by
      have := hk.le
      have : 0 ≤ (1 + |y|) ^ 6 := by positivity
      have : 0 ≤ Λ ^ 6 := by positivity
      positivity
    have h3 : (s * ψt y) ^ 2 * max 1 (Real.exp (s * ψt y)) ≤
        676 * Λ ^ 6 * k * (1 + |y|) ^ 6 * Real.exp ((1 + |y|) ^ 2 / 16) :=
      mul_le_mul (hb y).2 hmax hm0 hc0
    have e : 676 * Λ ^ 6 * k * g y =
        676 * Λ ^ 6 * k * (1 + |y|) ^ 6 * Real.exp ((1 + |y|) ^ 2 / 16) := by
      rw [hgeq]
      ring
    linarith
  -- the mean of the truncated log-ratio
  have hmean : |∫ y, ψt y ∂gaussianReal 0 1| ≤ 87 / 2 * Λ ^ 3 * k ^ 2 * 49152 := by
    have hsym := integral_comp_neg_gaussianReal hψm
    have e2 : ∫ y, ψt y ∂gaussianReal 0 1 =
        (1 / 2) * ∫ y, (ψt y + ψt (-y)) ∂gaussianReal 0 1 := by
      rw [integral_add hψi hψi', hsym]
      ring
    have hpt3 : ∀ y, ‖ψt y + ψt (-y)‖ ≤ 87 * Λ ^ 3 * k ^ 2 * g y := by
      intro y
      rw [Real.norm_eq_abs]
      by_cases hy : |y| ≤ A
      · have hy' : |-y| ≤ A := by rw [abs_neg]; exact hy
        rw [hψt, indicator_abs_le_of_le _ hy, indicator_abs_le_of_le _ hy']
        calc |gbmMilLogRatio r σ k y + gbmMilLogRatio r σ k (-y)| ≤
              87 * Λ ^ 3 * (sk * (1 + |y|)) ^ 4 := hbd2 y hy
          _ = 87 * Λ ^ 3 * k ^ 2 * (1 + |y|) ^ 4 := by
              rw [← hskk]
              ring
          _ ≤ 87 * Λ ^ 3 * k ^ 2 * g y :=
              mul_le_mul_of_nonneg_left (hpow y 4 (by norm_num)) (by positivity)
      · have hy' : ¬ |-y| ≤ A := by rw [abs_neg]; exact hy
        rw [hψt, indicator_abs_le_of_not_le _ hy, indicator_abs_le_of_not_le _ hy', add_zero,
          abs_zero]
        have := hg0 y
        positivity
    have h4 := norm_integral_le_of_norm_le (hgi.const_mul (87 * Λ ^ 3 * k ^ 2))
      (Eventually.of_forall hpt3)
    rw [Real.norm_eq_abs, integral_const_mul] at h4
    rw [e2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h5 : 87 * Λ ^ 3 * k ^ 2 * ∫ y, g y ∂gaussianReal 0 1 ≤ 87 * Λ ^ 3 * k ^ 2 * 49152 :=
      mul_le_mul_of_nonneg_left hgb (by positivity)
    linarith
  have hR : Integrable (fun y => 1 + s * ψt y + 676 * Λ ^ 6 * k * g y) (gaussianReal 0 1) :=
    ((integrable_const 1).add (hψi.const_mul s)).add (hgi.const_mul _)
  have hsm : s * ∫ y, ψt y ∂gaussianReal 0 1 ≤ 1 / k * (87 / 2 * Λ ^ 3 * k ^ 2 * 49152) :=
    calc s * ∫ y, ψt y ∂gaussianReal 0 1 ≤ |s * ∫ y, ψt y ∂gaussianReal 0 1| := le_abs_self _
      _ = |s| * |∫ y, ψt y ∂gaussianReal 0 1| := abs_mul _ _
      _ ≤ _ := mul_le_mul hs hmean (abs_nonneg _) (by positivity)
  have e3 : 1 / k * (87 / 2 * Λ ^ 3 * k ^ 2 * 49152) = 87 / 2 * Λ ^ 3 * 49152 * k := by
    field_simp
  have hΛ3 : Λ ^ 3 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ1 (by norm_num)
  calc ∫ x, Real.exp (s * ψt x) ∂gaussianReal 0 1
      ≤ ∫ y, (1 + s * ψt y + 676 * Λ ^ 6 * k * g y) ∂gaussianReal 0 1 :=
        integral_mono hEi hR hpt2
    _ = 1 + s * ∫ y, ψt y ∂gaussianReal 0 1 + 676 * Λ ^ 6 * k * ∫ y, g y ∂gaussianReal 0 1 := by
        have h1 : Integrable (fun y => 1 + s * ψt y) (gaussianReal 0 1) :=
          (integrable_const 1).add (hψi.const_mul s)
        have h2 : Integrable (fun y => 676 * Λ ^ 6 * k * g y) (gaussianReal 0 1) :=
          hgi.const_mul _
        have h3 : Integrable (fun y => s * ψt y) (gaussianReal 0 1) := hψi.const_mul s
        rw [integral_add h1 h2, integral_add (integrable_const 1) h3, integral_const_mul,
          integral_const_mul, integral_const]
        simp only [probReal_univ, one_smul]
    _ ≤ 1 + 87 / 2 * Λ ^ 3 * 49152 * k + 676 * Λ ^ 6 * k * 49152 := by
        have := mul_le_mul_of_nonneg_left hgb (by positivity : (0 : ℝ) ≤ 676 * Λ ^ 6 * k)
        linarith
    _ ≤ 1 + 720 * 49152 * Λ ^ 6 * k := by
        have := mul_le_mul_of_nonneg_right hΛ3 (by positivity : (0 : ℝ) ≤ 49152 * k)
        nlinarith

/-- **Chernoff's bound for the truncated Milstein log error** (Giles 2015, §5.2, p. 36,
l. 1563–1566: "matching … to within `O(h)`"; the Gaussian-type tails of the logarithm of the ratio
of the Milstein path to the exact solution).  In the setting of
`integrable_integral_exp_mul_truncLogRatio_le`, for independent standard normal `Z_j`, every `m`
and every `x`: `P(x < |∑_{j<m} ψ̃(Z_j)|) ≤ 2 e^{−x/k + D m k}`, `D = 720 · 49152 Λ⁶`
(`measureReal_le_sum_le_exp` with `s = ±1/k`). -/
lemma measureReal_lt_abs_sum_truncLogRatio_le (r σ : ℝ) {k A : ℝ} (hk : 0 < k)
    (hθ : Real.sqrt k * (1 + A) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2)))
    (hθ' : 26 * (1 + |r| + |σ| + σ ^ 2) ^ 3 * (Real.sqrt k * (1 + A)) ≤ 1 / 16) (m : ℕ)
    (x : ℝ) :
    stdNormalSeq.real {w : ℕ → ℝ | x <
        |∑ j ∈ range m, {y : ℝ | |y| ≤ A}.indicator (gbmMilLogRatio r σ k) (w j)|} ≤
      2 * Real.exp (-(x / k) + 720 * 49152 * (1 + |r| + |σ| + σ ^ 2) ^ 6 * (m * k)) := by
  set D := 720 * 49152 * (1 + |r| + |σ| + σ ^ 2) ^ 6 with hD
  set ψt := {y : ℝ | |y| ≤ A}.indicator (gbmMilLogRatio r σ k) with hψt
  have hS : MeasurableSet {y : ℝ | |y| ≤ A} := measurableSet_le (by fun_prop) measurable_const
  have hψm : Measurable ψt := (measurable_gbmMilLogRatio r σ k).indicator hS
  have hD0 : 0 ≤ D := by positivity
  have hk1 : 0 ≤ 1 / k := by positivity
  have hpow : ∀ I : ℝ, 0 ≤ I → I ≤ 1 + D * k → I ^ m ≤ Real.exp (D * (m * k)) := by
    intro I hI0 hI
    have h1 : I ≤ Real.exp (D * k) := hI.trans (by linarith [Real.add_one_le_exp (D * k)])
    calc I ^ m ≤ Real.exp (D * k) ^ m := pow_le_pow_left₀ hI0 h1 m
      _ = Real.exp (D * (m * k)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  -- the upper tail
  obtain ⟨hi1, hb1⟩ := integrable_integral_exp_mul_truncLogRatio_le r σ (s := 1 / k) hk hθ hθ'
    (by rw [abs_of_nonneg hk1])
  have hup := measureReal_le_sum_le_exp hψm hk1 hi1 m x
  have hup' : stdNormalSeq.real {w : ℕ → ℝ | x ≤ ∑ j ∈ range m, ψt (w j)} ≤
      Real.exp (-(x / k)) * Real.exp (D * (m * k)) := by
    refine hup.trans ?_
    have e : Real.exp (-(1 / k) * x) = Real.exp (-(x / k)) := by ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (hpow _ (integral_nonneg fun _ => (Real.exp_pos _).le) hb1)
      (Real.exp_pos _).le
  -- the lower tail
  obtain ⟨hi2, hb2⟩ := integrable_integral_exp_mul_truncLogRatio_le r σ (s := -(1 / k)) hk hθ
    hθ' (by rw [abs_neg, abs_of_nonneg hk1])
  have hneg : ∀ y, Real.exp (1 / k * (-ψt) y) = Real.exp (-(1 / k) * ψt y) := by
    intro y
    rw [Pi.neg_apply]
    ring_nf
  have hi2' : Integrable (fun y => Real.exp (1 / k * (-ψt) y)) (gaussianReal 0 1) := by
    simp_rw [hneg]
    exact hi2
  have hlow := measureReal_le_sum_le_exp hψm.neg hk1 hi2' m x
  have hlow' : stdNormalSeq.real {w : ℕ → ℝ | x ≤ ∑ j ∈ range m, (-ψt) (w j)} ≤
      Real.exp (-(x / k)) * Real.exp (D * (m * k)) := by
    refine hlow.trans ?_
    have e : Real.exp (-(1 / k) * x) = Real.exp (-(x / k)) := by ring_nf
    have e2 : ∫ y, Real.exp (1 / k * (-ψt) y) ∂gaussianReal 0 1 =
        ∫ y, Real.exp (-(1 / k) * ψt y) ∂gaussianReal 0 1 := by simp_rw [hneg]
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left (hpow _ (integral_nonneg fun _ => (Real.exp_pos _).le) hb2)
      (Real.exp_pos _).le
  have hsub : {w : ℕ → ℝ | x < |∑ j ∈ range m, ψt (w j)|} ⊆
      {w | x ≤ ∑ j ∈ range m, ψt (w j)} ∪ {w | x ≤ ∑ j ∈ range m, (-ψt) (w j)} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply, Finset.sum_neg_distrib] at hw ⊢
    rcases lt_abs.1 hw with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  calc _ ≤ _ := (measureReal_mono hsub).trans (measureReal_union_le _ _)
    _ ≤ Real.exp (-(x / k)) * Real.exp (D * (m * k)) +
          Real.exp (-(x / k)) * Real.exp (D * (m * k)) := add_le_add hup' hlow'
    _ = 2 * Real.exp (-(x / k) + D * (m * k)) := by
        rw [Real.exp_add]
        ring

/-- **A union bound for the increments of a path** (Giles 2015, §5.2): for independent standard
normal `Z_j`, `P(∃ j < m, |Z_j| > A) ≤ m √2 e^{−A²/4}` (`gaussianReal_real_lt_abs_le_exp`). -/
lemma measureReal_exists_lt_abs_le_exp {A : ℝ} (hA : 0 ≤ A) (m : ℕ) :
    stdNormalSeq.real {w : ℕ → ℝ | ∃ j < m, A < |w j|} ≤
      m * (Real.sqrt 2 * Real.exp (-(A ^ 2 / 4))) := by
  have e : {w : ℕ → ℝ | ∃ j < m, A < |w j|} =
      ⋃ j ∈ range m, (fun w : ℕ → ℝ => w j) ⁻¹' {y | A < |y|} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_preimage, exists_prop]
  rw [e]
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have hB : MeasurableSet {y : ℝ | A < |y|} := measurableSet_lt measurable_const (by fun_prop)
  have h1 : ∀ j, stdNormalSeq.real ((fun w : ℕ → ℝ => w j) ⁻¹' {y | A < |y|}) =
      (gaussianReal 0 1).real {y | A < |y|} := fun j =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) j).measureReal_preimage
      hB.nullMeasurableSet
  simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left (gaussianReal_real_lt_abs_le_exp hA) (Nat.cast_nonneg m)

/-- On the event that all increments are at most `A` in absolute value, the truncated sum is the
sum (Giles 2015, §5.2). -/
lemma sum_indicator_abs_le_eq {A : ℝ} (f : ℝ → ℝ) {w : ℕ → ℝ} {m : ℕ}
    (h : ∀ j < m, |w j| ≤ A) :
    ∑ j ∈ range m, {y : ℝ | |y| ≤ A}.indicator f (w j) = ∑ j ∈ range m, f (w j) :=
  Finset.sum_congr rfl fun j hj => indicator_abs_le_of_le f (h j (Finset.mem_range.1 hj))

/-- **The Milstein path of GBM is the exact solution times `e^{∑ ψ}`** (Giles 2015, §5.2): if the
Milstein factors are positive,
`∏_{j<m} M(w_j) = (∏_{j<m} e^{(r−σ²/2)k + σ√k w_j}) e^{∑_{j<m} ψ(w_j)}` with the log-ratio `ψ` of
`gbmMilLogRatio`. -/
lemma prod_gbmMilFactor_eq_mul_exp (r σ k : ℝ) {w : ℕ → ℝ} {m : ℕ}
    (h : ∀ j < m, 0 < gbmMilFactor r σ k (w j)) :
    ∏ j ∈ range m, gbmMilFactor r σ k (w j) =
      (∏ j ∈ range m, gbmExpFactor r σ k (w j)) *
        Real.exp (∑ j ∈ range m, gbmMilLogRatio r σ k (w j)) := by
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j hj =>
    gbmMilFactor_eq_mul_exp r σ k (w j) (h j (Finset.mem_range.1 hj))

/-! ### The two payoffs on a good sample -/

/-- `|log y| ≤ 2|y − 1|` for `|y − 1| ≤ ½` (the window around the strike in log scale, Giles 2015,
§5.2, p. 36, l. 1575–1577). -/
lemma abs_log_le_two_mul_abs_sub_one {y : ℝ} (hy : |y - 1| ≤ 1 / 2) :
    |Real.log y| ≤ 2 * |y - 1| := by
  have hy0 : 1 / 2 ≤ y := by
    have := (abs_le.1 hy).1
    linarith
  have hpos : 0 < y := by linarith
  have h1 := Real.log_le_sub_one_of_pos hpos
  have h2 := Real.one_sub_inv_le_log_of_pos hpos
  have h3 : -(2 * |y - 1|) ≤ 1 - y⁻¹ := by
    have e : 1 - y⁻¹ = (y - 1) / y := by field_simp
    rw [e, le_div_iff₀ hpos]
    have := neg_abs_le (y - 1)
    have := abs_nonneg (y - 1)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * y - 1) (abs_nonneg (y - 1))]
  rw [abs_le]
  constructor
  · linarith
  · have := le_abs_self (y - 1)
    linarith

/-- **The squared difference of the two conditional-expectation payoffs on a good sample** (Giles
2015, §5.2, p. 36, l. 1563–1577: "This results in the conditional distribution for the coarse path
underlying at maturity matching that of the fine path to within `O(h)`, for both the mean and the
standard deviation … the difference in payoff between the coarse and fine paths near the payoff
discontinuity is `O(h^{1/2})`").  Let `S ≠ 0` (the exact solution two fine steps before maturity),
`X = S e^F M(z)` (the fine Milstein value one step before maturity, `M` the Milstein factor of
step `h`, `e^F` the ratio of the Milstein path to the exact solution), `Y = S e^G` (the coarse
value), `S_T = S e^{(r−σ²/2)h + σ√h z} e^{(r−σ²/2)h + σ√h z'}` (the exact solution at maturity) with
`|F|, |G| ≤ x ≤ ¼`, `|M(z) − 1| ≤ e ≤ ½`, `|M(z)(1 + rh) − (1 + 2rh + σ√h z)| ≤ d`,
`|2rh + σ√h z| ≤ 1`.  With `a_m = 16x + 2d`, `a_s = 2|σ|√h (e + 4x)` the conditional means and
standard deviations satisfy `|m_f − m_c| ≤ a_m |X|`, `|s_f − s_c| ≤ a_s |X|`, and for `t ≥ 0`,
`ρ = a_m + t a_s + t|σ|√h` with `ρ + |r|h ≤ ½`, `(a_m + t a_s)/(|σ|√h) ≤ c̄` and
`2(ρ + |r|h) + x + |ψ(z)| + |(r − σ²/2)h + σ√h z'| ≤ δ̄`:
`(Φ((m_f − K)/s_f) − Φ((m_c − K)/s_c))² ≤ 8 P(|Z| > t)² + 2 c̄² 1_{|log|S_T| − log|K|| ≤ δ̄}`, for
every strike `K` (`abs_cdf_div_sub_cdf_div_le`; near the strike `|X − K| ≤ |X|/2`, so `K ≠ 0` and
`|log|X| − log|K|| ≤ 2(ρ + |r|h)`). -/
lemma condPayoff_sq_le_of_good {r σ h S F G z z' K x d e t cbar δbar X Y ST : ℝ} (hσ : σ ≠ 0)
    (hh : 0 < h) (hS : S ≠ 0) (hF : |F| ≤ x) (hG : |G| ≤ x) (hx : x ≤ 1 / 4)
    (he : |gbmMilFactor r σ h z - 1| ≤ e) (he2 : e ≤ 1 / 2)
    (hd : |gbmMilFactor r σ h z * (1 + r * h) - (1 + r * (2 * h) + σ * (Real.sqrt h * z))| ≤ d)
    (hQ : |r * (2 * h) + σ * (Real.sqrt h * z)| ≤ 1) (ht : 0 ≤ t)
    (hρ : 16 * x + 2 * d + t * (2 * |σ| * Real.sqrt h * (e + 4 * x)) + t * |σ| * Real.sqrt h +
      |r| * h ≤ 1 / 2)
    (hc : (16 * x + 2 * d + t * (2 * |σ| * Real.sqrt h * (e + 4 * x))) / (|σ| * Real.sqrt h) ≤
      cbar)
    (hδ : 2 * (16 * x + 2 * d + t * (2 * |σ| * Real.sqrt h * (e + 4 * x)) +
      t * |σ| * Real.sqrt h + |r| * h) + x + |gbmMilLogRatio r σ h z| +
      |(r - σ ^ 2 / 2) * h + σ * Real.sqrt h * z'| ≤ δbar)
    (hX : X = S * Real.exp F * gbmMilFactor r σ h z) (hY : Y = S * Real.exp G)
    (hST : ST = S * (gbmExpFactor r σ h z * gbmExpFactor r σ h z')) :
    (cdf (gaussianReal 0 1) ((X + r * X * h - K) / (|σ * X| * Real.sqrt h)) -
        cdf (gaussianReal 0 1) ((Y + r * Y * (2 * h) + σ * Y * (Real.sqrt h * z) - K) /
          (|σ * Y| * Real.sqrt h))) ^ 2 ≤
      8 * (gaussianReal 0 1).real {u | t < |u|} ^ 2 +
        2 * cbar ^ 2 * {u : ℝ | |Real.log |u| - Real.log (|K|)| ≤ δbar}.indicator 1 ST := by
  have hψdef : gbmMilLogRatio r σ h z =
      Real.log (gbmMilFactor r σ h z) - ((r - σ ^ 2 / 2) * h + σ * Real.sqrt h * z) := rfl
  set μ := gbmMilFactor r σ h z with hμ
  set sh := Real.sqrt h with hsh
  set τ := (gaussianReal 0 1).real {u | t < |u|} with hτ
  set am := 16 * x + 2 * d with ham
  set as := 2 * |σ| * sh * (e + 4 * x) with has
  have hsh0 : 0 < sh := Real.sqrt_pos.2 hh
  have hσ0 : 0 < |σ| := abs_pos.2 hσ
  have hμ1 : 1 / 2 ≤ μ := by
    have := (abs_le.1 he).1
    linarith only [this, he2]
  have hμ0 : 0 < μ := by linarith only [hμ1]
  have hS0 : 0 < |S| := abs_pos.2 hS
  have heF : 0 < Real.exp F := Real.exp_pos F
  have hx0 : 0 ≤ x := (abs_nonneg F).trans hF
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hX0 : X ≠ 0 := by
    rw [hX]
    exact mul_ne_zero (mul_ne_zero hS heF.ne') hμ0.ne'
  have hY0 : Y ≠ 0 := by
    rw [hY]
    exact mul_ne_zero hS (Real.exp_pos G).ne'
  have hXabs : |X| = |S| * Real.exp F * μ := by
    rw [hX, abs_mul, abs_mul, abs_of_pos heF, abs_of_pos hμ0]
  have hSF : |S| * Real.exp F ≤ 2 * |X| := by
    rw [hXabs]
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * μ by linarith only [hμ1])
      (mul_pos hS0 heF).le
    linarith only [this]
  have hGF : |G - F| ≤ 2 * x := (abs_sub G F).trans (by linarith only [hF, hG])
  have hexp1 : |Real.exp (G - F) - 1| ≤ 4 * x := by
    have := Real.abs_exp_sub_one_le (hGF.trans (by linarith only [hx]))
    linarith only [this, hGF]
  have hexpG : Real.exp G = Real.exp F * Real.exp (G - F) := by
    rw [← Real.exp_add]
    ring_nf
  have hexp : |Real.exp G - Real.exp F| ≤ Real.exp F * (4 * x) := by
    have h1 : Real.exp G - Real.exp F = Real.exp F * (Real.exp (G - F) - 1) := by
      rw [hexpG]
      ring
    rw [h1, abs_mul, abs_of_pos heF]
    exact mul_le_mul_of_nonneg_left hexp1 heF.le
  set Q := 1 + r * (2 * h) + σ * (sh * z) with hQdef
  have hQ2 : |Q| ≤ 2 := by
    have := abs_add_le (1 : ℝ) (r * (2 * h) + σ * (sh * z))
    rw [abs_one] at this
    rw [hQdef, add_assoc]
    linarith only [this, hQ]
  -- the conditional means
  have hm : |X + r * X * h - (Y + r * Y * (2 * h) + σ * Y * (sh * z))| ≤ am * |X| := by
    have e1 : X + r * X * h - (Y + r * Y * (2 * h) + σ * Y * (sh * z)) =
        S * (Real.exp F * (μ * (1 + r * h) - Q) - (Real.exp G - Real.exp F) * Q) := by
      rw [hX, hY, hQdef]
      ring
    rw [e1, abs_mul]
    have h3 : |Real.exp F * (μ * (1 + r * h) - Q) - (Real.exp G - Real.exp F) * Q| ≤
        Real.exp F * (d + 8 * x) := by
      calc _ ≤ |Real.exp F * (μ * (1 + r * h) - Q)| + |(Real.exp G - Real.exp F) * Q| :=
            abs_sub _ _
        _ = Real.exp F * |μ * (1 + r * h) - Q| + |Real.exp G - Real.exp F| * |Q| := by
            rw [abs_mul, abs_mul, abs_of_pos heF]
        _ ≤ Real.exp F * d + Real.exp F * (4 * x) * 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hd heF.le)
              (mul_le_mul hexp hQ2 (abs_nonneg _) (by positivity))
        _ = Real.exp F * (d + 8 * x) := by ring
    calc |S| * |Real.exp F * (μ * (1 + r * h) - Q) - (Real.exp G - Real.exp F) * Q|
        ≤ |S| * (Real.exp F * (d + 8 * x)) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = |S| * Real.exp F * (d + 8 * x) := by ring
      _ ≤ 2 * |X| * (d + 8 * x) := mul_le_mul_of_nonneg_right hSF (by positivity)
      _ = am * |X| := by rw [ham]; ring
  -- the conditional standard deviations
  have hs : |(|σ * X| * sh - |σ * Y| * sh)| ≤ as * |X| := by
    have e1 : |σ * X| * sh - |σ * Y| * sh = |σ| * sh * (|X| - |Y|) := by
      rw [abs_mul, abs_mul]
      ring
    rw [e1, abs_mul, abs_mul, abs_of_pos hσ0, abs_of_pos hsh0]
    have h1 : |(|X| - |Y|)| ≤ |X - Y| := abs_abs_sub_abs_le_abs_sub X Y
    have e2 : X - Y = S * Real.exp F * ((μ - 1) - (Real.exp (G - F) - 1)) := by
      rw [hX, hY, hexpG]
      ring
    have h2 : |X - Y| ≤ |S| * Real.exp F * (e + 4 * x) := by
      rw [e2, abs_mul, abs_mul, abs_of_pos heF]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (abs_sub _ _).trans (add_le_add he hexp1)
    have h3 : |X - Y| ≤ 2 * |X| * (e + 4 * x) :=
      h2.trans (mul_le_mul_of_nonneg_right hSF (by positivity))
    calc |σ| * sh * |(|X| - |Y|)| ≤ |σ| * sh * (2 * |X| * (e + 4 * x)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)
      _ = as * |X| := by rw [has]; ring
  -- the two payoffs
  have hs₁ : 0 < |σ * X| * sh := mul_pos (abs_pos.2 (mul_ne_zero hσ hX0)) hsh0
  have hs₂ : 0 < |σ * Y| * sh := mul_pos (abs_pos.2 (mul_ne_zero hσ hY0)) hsh0
  obtain ⟨hA1, hA2⟩ := abs_cdf_div_sub_cdf_div_le (m₁ := X + r * X * h)
    (m₂ := Y + r * Y * (2 * h) + σ * Y * (sh * z)) hs₁ hs₂ K ht
  set w := |X + r * X * h - (Y + r * Y * (2 * h) + σ * Y * (sh * z))| +
    t * |(|σ * X| * sh - |σ * Y| * sh)| with hwdef
  have hw : w ≤ (am + t * as) * |X| := by
    have := mul_le_mul_of_nonneg_left hs ht
    rw [hwdef]
    linarith only [this, hm]
  have hs1eq : |σ * X| * sh = |σ| * sh * |X| := by
    rw [abs_mul]
    ring
  have hc' : am + t * as ≤ cbar * (|σ| * sh) := by
    rw [div_le_iff₀ (by positivity)] at hc
    exact hc
  have hwc : w / (|σ * X| * sh) ≤ cbar := by
    rw [div_le_iff₀ hs₁]
    calc w ≤ (am + t * as) * |X| := hw
      _ ≤ cbar * (|σ| * sh) * |X| := mul_le_mul_of_nonneg_right hc' (abs_nonneg _)
      _ = cbar * (|σ * X| * sh) := by rw [abs_mul]; ring
  have hτ0 : 0 ≤ τ := measureReal_nonneg
  have hind0 : 0 ≤ {u : ℝ | |Real.log |u| - Real.log (|K|)| ≤ δbar}.indicator (1 : ℝ → ℝ) ST :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases hfar : (am + t * as + t * |σ| * sh) * |X| < |X + r * X * h - K|
  · have hlt : w + t * (|σ * X| * sh) < |X + r * X * h - K| := by
      have : w + t * (|σ * X| * sh) ≤ (am + t * as + t * |σ| * sh) * |X| := by
        rw [hs1eq]
        linarith only [hw]
      linarith only [this, hfar]
    have h2 := hA2 hlt
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs] at hsq
    have : 0 ≤ 2 * cbar ^ 2 * {u : ℝ | |Real.log |u| - Real.log (|K|)| ≤ δbar}.indicator
        (1 : ℝ → ℝ) ST := by positivity
    linarith only [hsq, this, sq_nonneg τ]
  · rw [not_lt] at hfar
    set ρ := am + t * as + t * |σ| * sh with hρdef
    have hρ' : ρ + |r| * h ≤ 1 / 2 := by
      rw [hρdef]
      linarith only [hρ]
    have hXK : |X - K| ≤ (ρ + |r| * h) * |X| := by
      have h1 := abs_add_le (X + r * X * h - K) (-(r * X * h))
      have e1 : X + r * X * h - K + -(r * X * h) = X - K := by ring
      rw [e1, abs_neg] at h1
      have e2 : |r * X * h| = |r| * h * |X| := by
        rw [abs_mul, abs_mul, abs_of_pos hh]
        ring
      rw [e2] at h1
      linarith only [h1, hfar]
    have hX1 : 0 < |X| := abs_pos.2 hX0
    have hXK2 : |X - K| ≤ |X| / 2 := by
      have := mul_le_mul_of_nonneg_right hρ' (abs_nonneg X)
      linarith only [this, hXK]
    have hK0 : K ≠ 0 := by
      intro hK
      rw [hK, sub_zero] at hXK2
      linarith only [hXK2, hX1]
    have hq : |K / X - 1| ≤ ρ + |r| * h := by
      have e1 : K / X - 1 = -((X - K) / X) := by
        field_simp
        ring
      rw [e1, abs_neg, abs_div, div_le_iff₀ hX1]
      exact hXK
    have hlogKX : |Real.log |K| - Real.log (|X|)| ≤ 2 * (ρ + |r| * h) := by
      have h1 : Real.log |K| - Real.log |X| = Real.log (K / X) := by
        rw [← Real.log_div (abs_ne_zero.2 hK0) (abs_ne_zero.2 hX0), ← abs_div]
        have hpos : 0 < K / X := by
          have := (abs_le.1 (hq.trans hρ')).1
          linarith only [this]
        rw [abs_of_pos hpos]
      rw [h1]
      exact (abs_log_le_two_mul_abs_sub_one (hq.trans hρ')).trans (by linarith only [hq])
    have hlogST : Real.log |ST| = Real.log |S| + ((r - σ ^ 2 / 2) * h + σ * sh * z) +
        ((r - σ ^ 2 / 2) * h + σ * sh * z') := by
      rw [hST]
      unfold gbmExpFactor
      rw [← Real.exp_add, abs_mul, abs_of_pos (Real.exp_pos _),
        Real.log_mul hS0.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    have hlogX : Real.log |X| = Real.log |S| + F + Real.log μ := by
      rw [hXabs, Real.log_mul (mul_pos hS0 heF).ne' hμ0.ne', Real.log_mul hS0.ne' heF.ne',
        Real.log_exp]
    have hlogSTX : |Real.log |ST| - Real.log (|X|)| ≤
        x + |gbmMilLogRatio r σ h z| + |(r - σ ^ 2 / 2) * h + σ * sh * z'| := by
      have e1 : Real.log |ST| - Real.log |X| =
          ((r - σ ^ 2 / 2) * h + σ * sh * z') - F - gbmMilLogRatio r σ h z := by
        rw [hlogST, hlogX, hψdef]
        ring
      rw [e1]
      have h1 := abs_sub (((r - σ ^ 2 / 2) * h + σ * sh * z') - F) (gbmMilLogRatio r σ h z)
      have h2 := abs_sub ((r - σ ^ 2 / 2) * h + σ * sh * z') F
      linarith only [h1, h2, hF]
    have hmem : ST ∈ {u : ℝ | |Real.log |u| - Real.log (|K|)| ≤ δbar} := by
      simp only [Set.mem_ofPred_eq]
      have h1 := abs_sub_le (Real.log |ST|) (Real.log |X|) (Real.log |K|)
      rw [abs_sub_comm (Real.log |X|) (Real.log |K|)] at h1
      have h2 : 2 * (ρ + |r| * h) + x + |gbmMilLogRatio r σ h z| +
          |(r - σ ^ 2 / 2) * h + σ * sh * z'| ≤ δbar := by
        rw [hρdef]
        linarith only [hδ]
      linarith only [h1, h2, hlogSTX, hlogKX]
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    have h1 := hA1.trans (add_le_add le_rfl hwc)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at hsq
    linarith only [hsq, sq_nonneg (2 * τ - cbar)]

/-! ### One level on a good sample -/

/-- `|M(y) − 1| ≤ |r|h + |σ|√h A + ½σ²(hA² + h)` for the Milstein factor `M` of GBM with step
`h ≥ 0` and `|y| ≤ A` (Giles 2015, §5.2). -/
lemma abs_gbmMilFactor_sub_one_le (r σ : ℝ) {h A y : ℝ} (hh : 0 ≤ h) (hy : |y| ≤ A) :
    |gbmMilFactor r σ h y - 1| ≤
      |r| * h + |σ| * Real.sqrt h * A + σ ^ 2 / 2 * (h * A ^ 2 + h) := by
  have hsh := Real.sqrt_nonneg h
  have hshh : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh
  have e : gbmMilFactor r σ h y - 1 =
      r * h + σ * (Real.sqrt h * y) + σ ^ 2 / 2 * (h * y ^ 2 - h) := by
    unfold gbmMilFactor
    rw [mul_pow, hshh]
    ring
  rw [e]
  have h1 : |r * h| = |r| * h := by rw [abs_mul, abs_of_nonneg hh]
  have h2 : |σ * (Real.sqrt h * y)| ≤ |σ| * Real.sqrt h * A := by
    rw [abs_mul, abs_mul, abs_of_nonneg hsh, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hy (by positivity)
  have hy2 : y ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have h3 : |σ ^ 2 / 2 * (h * y ^ 2 - h)| ≤ σ ^ 2 / 2 * (h * A ^ 2 + h) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ σ ^ 2 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h4 := mul_le_mul_of_nonneg_left hy2 hh
    have h5 := mul_nonneg hh (sq_nonneg y)
    rw [abs_le]
    constructor <;> linarith
  have h6 := abs_add_le (r * h + σ * (Real.sqrt h * y)) (σ ^ 2 / 2 * (h * y ^ 2 - h))
  have h7 := abs_add_le (r * h) (σ * (Real.sqrt h * y))
  linarith

/-- `|M(y)(1 + rh) − (1 + 2rh + σ√h y)| ≤ ½σ²(hA² + h) + |r|h e` for the Milstein factor `M` of
GBM, `|y| ≤ A` and `|M(y) − 1| ≤ e` (the conditional means of the fine and the coarse path,
Giles 2015, §5.2, p. 36, l. 1551–1574): the difference is `½σ²(hy² − h) + rh(M(y) − 1)`. -/
lemma abs_gbmMilFactor_mul_sub_le (r σ : ℝ) {h A y e : ℝ} (hh : 0 ≤ h) (hy : |y| ≤ A)
    (he : |gbmMilFactor r σ h y - 1| ≤ e) :
    |gbmMilFactor r σ h y * (1 + r * h) - (1 + r * (2 * h) + σ * (Real.sqrt h * y))| ≤
      σ ^ 2 / 2 * (h * A ^ 2 + h) + |r| * h * e := by
  have hshh : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh
  have e1 : gbmMilFactor r σ h y * (1 + r * h) - (1 + r * (2 * h) + σ * (Real.sqrt h * y)) =
      σ ^ 2 / 2 * (h * y ^ 2 - h) + r * h * (gbmMilFactor r σ h y - 1) := by
    unfold gbmMilFactor
    rw [mul_pow, hshh]
    ring
  rw [e1]
  have hy2 : y ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have h3 : |σ ^ 2 / 2 * (h * y ^ 2 - h)| ≤ σ ^ 2 / 2 * (h * A ^ 2 + h) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ σ ^ 2 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h4 := mul_le_mul_of_nonneg_left hy2 hh
    have h5 := mul_nonneg hh (sq_nonneg y)
    rw [abs_le]
    constructor <;> linarith
  have h4 : |r * h * (gbmMilFactor r σ h y - 1)| ≤ |r| * h * e := by
    rw [abs_mul, abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left he (by positivity)
  exact (abs_add_le _ _).trans (add_le_add h3 h4)

/-- **One level of the conditional-expectation estimator on a good sample** (Giles 2015, §5.2,
p. 36, l. 1563–1577).  On level `ℓ + 1` (`h = T 2^{−(ℓ+1)}`, `n = 2^ℓ − 1`), if all fine increments
`Z_j`, `j < 2^{ℓ+1}`, and all coarse increments `W_j = (Z_{2j} + Z_{2j+1})/√2`, `j < n`, are at most
`A` in absolute value, and the truncated Milstein log errors of the fine path after `2n` steps and
of the coarse path after `n` steps are at most `x`, then (with `√h (1 + A)`, `√(2h) (1 + A)` at most
`1/(4Λ)` and the scales of `condPayoff_sq_le_of_good`) the squared correction is at most
`8 P(|Z| > t)² + 2 c̄² 1_{|log|S_T| − log|K|| ≤ δ̄}`: the fine value one step before maturity is
`S e^F M(Z_{2n})`, the coarse value is `S e^G`, `S_T = S e^{…Z_{2n}} e^{…Z_{2n+1}}` with `S` the
exact solution at `t_{2n}` (`prod_gbmMilFactor_eq_mul_exp`, `prod_gbmExpFactor_pairAvg`). -/
lemma condExp_sq_le_of_good_sample (r σ : ℝ) {s₀ T K A t x e d cbar δbar : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) (ℓ : ℕ)
    (hθ₁ : Real.sqrt (T / 2 ^ (ℓ + 1)) * (1 + A) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2)))
    (hθ₂ : Real.sqrt (T / 2 ^ ℓ) * (1 + A) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2)))
    (hx : x ≤ 1 / 4)
    (he : e = |r| * (T / 2 ^ (ℓ + 1)) + |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * A +
      σ ^ 2 / 2 * (T / 2 ^ (ℓ + 1) * A ^ 2 + T / 2 ^ (ℓ + 1)))
    (he2 : e ≤ 1 / 2)
    (hd : d = σ ^ 2 / 2 * (T / 2 ^ (ℓ + 1) * A ^ 2 + T / 2 ^ (ℓ + 1)) +
      |r| * (T / 2 ^ (ℓ + 1)) * e)
    (hQ : 2 * |r| * (T / 2 ^ (ℓ + 1)) + |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * A ≤ 1) (ht : 0 ≤ t)
    (hρ : 16 * x + 2 * d + t * (2 * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * (e + 4 * x)) +
      t * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) + |r| * (T / 2 ^ (ℓ + 1)) ≤ 1 / 2)
    (hc : (16 * x + 2 * d + t * (2 * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * (e + 4 * x))) /
      (|σ| * Real.sqrt (T / 2 ^ (ℓ + 1))) ≤ cbar)
    (hδ : 2 * (16 * x + 2 * d + t * (2 * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * (e + 4 * x)) +
      t * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) + |r| * (T / 2 ^ (ℓ + 1))) + x +
      26 * (1 + |r| + |σ| + σ ^ 2) ^ 3 * (Real.sqrt (T / 2 ^ (ℓ + 1)) * (1 + A)) ^ 3 +
      (|r - σ ^ 2 / 2| * (T / 2 ^ (ℓ + 1)) + |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * A) ≤ δbar)
    {z : ℕ → ℝ} (h1 : ∀ j < 2 ^ (ℓ + 1), |z j| ≤ A) (h2 : ∀ j < 2 ^ ℓ - 1, |pairAvg z j| ≤ A)
    (h3 : |∑ j ∈ range (2 * (2 ^ ℓ - 1)),
      {y : ℝ | |y| ≤ A}.indicator (gbmMilLogRatio r σ (T / 2 ^ (ℓ + 1))) (z j)| ≤ x)
    (h4 : |∑ j ∈ range (2 ^ ℓ - 1),
      {y : ℝ | |y| ≤ A}.indicator (gbmMilLogRatio r σ (T / 2 ^ ℓ)) (pairAvg z j)| ≤ x) :
    (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2 ≤
      8 * (gaussianReal 0 1).real {u | t < |u|} ^ 2 + 2 * cbar ^ 2 *
        {u : ℝ | |Real.log |u| - Real.log (|K|)| ≤ δbar}.indicator 1
          (gbmExact r σ T s₀ (ℓ + 1) z) := by
  obtain ⟨Xf, hXf⟩ : ∃ X, X = milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀
      z (2 ^ (ℓ + 1) - 1) := ⟨_, rfl⟩
  obtain ⟨Yc, hYc⟩ : ∃ Y, Y = milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀
      (pairAvg z) (2 ^ ℓ - 1) := ⟨_, rfl⟩
  have hk2 : T / 2 ^ ℓ = 2 * (T / 2 ^ (ℓ + 1)) := div_two_pow_eq_two_mul T ℓ
  have hfine : gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z =
      cdf (gaussianReal 0 1) ((Xf + r * Xf * (T / 2 ^ (ℓ + 1)) - K) /
        (|σ * Xf| * Real.sqrt (T / 2 ^ (ℓ + 1)))) := by
    rw [hXf]
    rfl
  have hcoarse : gbmDigitalCondCoarse r σ T s₀ K ℓ z =
      cdf (gaussianReal 0 1) ((Yc + r * Yc * (2 * (T / 2 ^ (ℓ + 1))) +
        σ * Yc * (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 * (2 ^ ℓ - 1))) - K) /
        (|σ * Yc| * Real.sqrt (T / 2 ^ (ℓ + 1)))) := by
    rw [hYc, ← hk2, ← two_pow_succ_sub_two_eq ℓ]
    rfl
  rw [hfine, hcoarse]
  set h := T / 2 ^ (ℓ + 1) with hhdef
  set k := T / 2 ^ ℓ with hkdef
  set n := 2 ^ ℓ - 1 with hn
  have hN : 2 ^ (ℓ + 1) = 2 * n + 1 + 1 := two_pow_succ_eq_add_two ℓ
  have hh : 0 < h := by positivity
  have hk : 0 < k := by positivity
  set Λ := 1 + |r| + |σ| + σ ^ 2 with hΛ
  -- the Milstein factors on the truncation are positive
  have hMpos : ∀ (k' : ℝ), 0 ≤ k' → Real.sqrt k' * (1 + A) ≤ 1 / (4 * Λ) →
      ∀ y, |y| ≤ A → 0 < gbmMilFactor r σ k' y := by
    intro k' hk' hθ y hy
    have hθy : Real.sqrt k' * (1 + |y|) ≤ 1 / (4 * Λ) :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)) hθ
    have hb := (gbmMilLogRatio_bounds r σ hk' hθy).1
    have hs := (gbmMil_step_scales r σ hk' hθy).2.2.1
    have := (abs_le.1 hb).1
    linarith
  have hz2n : |z (2 * n)| ≤ A := h1 _ (by omega)
  have hz2n1 : |z (2 * n + 1)| ≤ A := h1 _ (by omega)
  -- the log errors
  set F := ∑ j ∈ range (2 * n), gbmMilLogRatio r σ h (z j) with hFdef
  set G := ∑ j ∈ range n, gbmMilLogRatio r σ k (pairAvg z j) with hGdef
  have hF : |F| ≤ x := by
    rw [hFdef, ← sum_indicator_abs_le_eq _ (fun j hj => h1 j (by omega))]
    exact h3
  have hG : |G| ≤ x := by
    rw [hGdef, ← sum_indicator_abs_le_eq _ h2]
    exact h4
  -- the product forms
  set S := s₀ * ∏ j ∈ range (2 * n), gbmExpFactor r σ h (z j) with hSdef
  have hS : S ≠ 0 := by
    rw [hSdef]
    refine mul_ne_zero hs₀ (Finset.prod_ne_zero_iff.2 fun j _ => ?_)
    unfold gbmExpFactor
    exact (Real.exp_pos _).ne'
  have hX : Xf = S * Real.exp F * gbmMilFactor r σ h (z (2 * n)) := by
    rw [hXf, milsteinPath_fine_eq_prod, ← hhdef, ← hn, Finset.prod_range_succ,
      prod_gbmMilFactor_eq_mul_exp r σ h (fun j hj => hMpos h hh.le hθ₁ _ (h1 j (by omega))),
      hSdef, hFdef]
    ring
  have hY : Yc = S * Real.exp G := by
    rw [hYc, milsteinPath_gbm,
      prod_gbmMilFactor_eq_mul_exp r σ k (fun j hj => hMpos k hk.le hθ₂ _ (h2 j hj)), hSdef,
      hGdef]
    have hp : ∏ j ∈ range n, gbmExpFactor r σ k (pairAvg z j) =
        ∏ i ∈ range (2 * n), gbmExpFactor r σ h (z i) := by
      rw [hk2]
      exact prod_gbmExpFactor_pairAvg r σ h z n
    rw [hp]
    ring
  have hST : gbmExact r σ T s₀ (ℓ + 1) z =
      S * (gbmExpFactor r σ h (z (2 * n)) * gbmExpFactor r σ h (z (2 * n + 1))) := by
    rw [gbmExact_eq_prod, ← hhdef]
    have hr : range (2 ^ (ℓ + 1)) = range (2 * n + 1 + 1) := by rw [hN]
    rw [hr, Finset.prod_range_succ, Finset.prod_range_succ, hSdef]
    ring
  -- the scales at `Z_{2n}`, `Z_{2n+1}`
  have he' : |gbmMilFactor r σ h (z (2 * n)) - 1| ≤ e := by
    rw [he]
    exact abs_gbmMilFactor_sub_one_le r σ hh.le hz2n
  have hd' : |gbmMilFactor r σ h (z (2 * n)) * (1 + r * h) -
      (1 + r * (2 * h) + σ * (Real.sqrt h * z (2 * n)))| ≤ d := by
    rw [hd]
    exact abs_gbmMilFactor_mul_sub_le r σ hh.le hz2n he'
  have hQ' : |r * (2 * h) + σ * (Real.sqrt h * z (2 * n))| ≤ 1 := by
    have h5 : |σ * (Real.sqrt h * z (2 * n))| ≤ |σ| * Real.sqrt h * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg h), ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hz2n (by positivity)
    have h6 : |r * (2 * h)| = 2 * |r| * h := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * h)]
      ring
    have := abs_add_le (r * (2 * h)) (σ * (Real.sqrt h * z (2 * n)))
    linarith
  have hψ : |gbmMilLogRatio r σ h (z (2 * n))| ≤ 26 * Λ ^ 3 * (Real.sqrt h * (1 + A)) ^ 3 := by
    have hθy : Real.sqrt h * (1 + |z (2 * n)|) ≤ 1 / (4 * Λ) :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)) hθ₁
    refine (gbmMilLogRatio_bounds r σ hh.le hθy).2.trans ?_
    have h5 : Real.sqrt h * (1 + |z (2 * n)|) ≤ Real.sqrt h * (1 + A) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    have h6 := pow_le_pow_left₀ (by positivity) h5 3
    have hΛ0 : 0 ≤ Λ := by positivity
    exact mul_le_mul_of_nonneg_left h6 (by positivity)
  have hlast : |(r - σ ^ 2 / 2) * h + σ * Real.sqrt h * z (2 * n + 1)| ≤
      |r - σ ^ 2 / 2| * h + |σ| * Real.sqrt h * A := by
    have h5 : |σ * Real.sqrt h * z (2 * n + 1)| ≤ |σ| * Real.sqrt h * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg h)]
      exact mul_le_mul_of_nonneg_left hz2n1 (by positivity)
    have h6 : |(r - σ ^ 2 / 2) * h| = |r - σ ^ 2 / 2| * h := by
      rw [abs_mul, abs_of_pos hh]
    have := abs_add_le ((r - σ ^ 2 / 2) * h) (σ * Real.sqrt h * z (2 * n + 1))
    linarith
  have hδ' : 2 * (16 * x + 2 * d + t * (2 * |σ| * Real.sqrt h * (e + 4 * x)) +
      t * |σ| * Real.sqrt h + |r| * h) + x + |gbmMilLogRatio r σ h (z (2 * n))| +
      |(r - σ ^ 2 / 2) * h + σ * Real.sqrt h * z (2 * n + 1)| ≤ δbar := by
    linarith
  rw [hST]
  exact condPayoff_sq_le_of_good hσ hh hS hF hG hx he' he2 hd' hQ' ht hρ hc hδ' hX hY rfl

/-- The event that one of the first `m` increments exceeds `A` in absolute value is measurable
(Giles 2015, §5.2). -/
lemma measurableSet_exists_lt_abs (A : ℝ) (m : ℕ) :
    MeasurableSet {w : ℕ → ℝ | ∃ j < m, A < |w j|} := by
  have e : {w : ℕ → ℝ | ∃ j < m, A < |w j|} =
      ⋃ j ∈ range m, (fun w : ℕ → ℝ => w j) ⁻¹' {y | A < |y|} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_preimage, exists_prop]
  rw [e]
  exact Finset.measurableSet_biUnion _ fun j _ =>
    (measurable_pi_apply j) (measurableSet_lt measurable_const (by fun_prop))

/-- **The second moment of one correction, by events** (Giles 2015, §5.2, p. 36, l. 1563–1577:
"matching that of the fine path to within `O(h)` … the difference in payoff between the coarse and
fine paths near the payoff discontinuity is `O(h^{1/2})`").  In the setting of
`condExp_sq_le_of_good_sample`, if moreover `26Λ³√h(1 + A) ≤ 1/16`, `26Λ³√(2h)(1 + A) ≤ 1/16`,
`A ≥ 0` and `δ̄ ≥ 0`, then `E[(P^f_{ℓ+1} − P^c_ℓ)²]` is at most
`(2^{ℓ+1} + n) √2 e^{−A²/4}` (an increment larger than `A`, `measureReal_exists_lt_abs_le_exp`)
`+ 2e^{−x/h + D·2n·h} + 2e^{−x/(2h) + D·n·2h}` (a log error larger than `x`,
`measureReal_lt_abs_sum_truncLogRatio_le`, `D = 720 · 49152 Λ⁶`)
`+ 8 P(|Z| > t)² + 2c̄² · 2δ̄/(|σ| √T √(2π))` (`condExp_sq_le_of_good_sample` and the small ball of
`log|S_T|`, `gbmExact_logSmallBall`); here `n = 2^ℓ − 1` and the coarse events are pulled back by
the measure-preserving `pairAvg`. -/
lemma condExp_integral_sq_le (r σ : ℝ) {s₀ T K A t x e d cbar δbar : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) (ℓ : ℕ) (hA : 0 ≤ A)
    (hθ₁ : Real.sqrt (T / 2 ^ (ℓ + 1)) * (1 + A) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2)))
    (hθ₁' : 26 * (1 + |r| + |σ| + σ ^ 2) ^ 3 * (Real.sqrt (T / 2 ^ (ℓ + 1)) * (1 + A)) ≤ 1 / 16)
    (hθ₂ : Real.sqrt (T / 2 ^ ℓ) * (1 + A) ≤ 1 / (4 * (1 + |r| + |σ| + σ ^ 2)))
    (hθ₂' : 26 * (1 + |r| + |σ| + σ ^ 2) ^ 3 * (Real.sqrt (T / 2 ^ ℓ) * (1 + A)) ≤ 1 / 16)
    (hx : x ≤ 1 / 4)
    (he : e = |r| * (T / 2 ^ (ℓ + 1)) + |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * A +
      σ ^ 2 / 2 * (T / 2 ^ (ℓ + 1) * A ^ 2 + T / 2 ^ (ℓ + 1)))
    (he2 : e ≤ 1 / 2)
    (hd : d = σ ^ 2 / 2 * (T / 2 ^ (ℓ + 1) * A ^ 2 + T / 2 ^ (ℓ + 1)) +
      |r| * (T / 2 ^ (ℓ + 1)) * e)
    (hQ : 2 * |r| * (T / 2 ^ (ℓ + 1)) + |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * A ≤ 1) (ht : 0 ≤ t)
    (hρ : 16 * x + 2 * d + t * (2 * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * (e + 4 * x)) +
      t * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) + |r| * (T / 2 ^ (ℓ + 1)) ≤ 1 / 2)
    (hc : (16 * x + 2 * d + t * (2 * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * (e + 4 * x))) /
      (|σ| * Real.sqrt (T / 2 ^ (ℓ + 1))) ≤ cbar)
    (hδ : 2 * (16 * x + 2 * d + t * (2 * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * (e + 4 * x)) +
      t * |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) + |r| * (T / 2 ^ (ℓ + 1))) + x +
      26 * (1 + |r| + |σ| + σ ^ 2) ^ 3 * (Real.sqrt (T / 2 ^ (ℓ + 1)) * (1 + A)) ^ 3 +
      (|r - σ ^ 2 / 2| * (T / 2 ^ (ℓ + 1)) + |σ| * Real.sqrt (T / 2 ^ (ℓ + 1)) * A) ≤ δbar)
    (hδ0 : 0 ≤ δbar) :
    ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2
        ∂stdNormalSeq ≤
      (((2 ^ (ℓ + 1) : ℕ) : ℝ) + ((2 ^ ℓ - 1 : ℕ) : ℝ)) *
          (Real.sqrt 2 * Real.exp (-(A ^ 2 / 4))) +
        2 * Real.exp (-(x / (T / 2 ^ (ℓ + 1))) + 720 * 49152 * (1 + |r| + |σ| + σ ^ 2) ^ 6 *
          (((2 * (2 ^ ℓ - 1) : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)))) +
        2 * Real.exp (-(x / (T / 2 ^ ℓ)) + 720 * 49152 * (1 + |r| + |σ| + σ ^ 2) ^ 6 *
          (((2 ^ ℓ - 1 : ℕ) : ℝ) * (T / 2 ^ ℓ))) +
        8 * (gaussianReal 0 1).real {u | t < |u|} ^ 2 +
        2 * cbar ^ 2 * (2 * δbar / (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi))) := by
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have hk : 0 < T / 2 ^ ℓ := by positivity
  set ψ₁ := {y : ℝ | |y| ≤ A}.indicator (gbmMilLogRatio r σ (T / 2 ^ (ℓ + 1))) with hψ₁
  set ψ₂ := {y : ℝ | |y| ≤ A}.indicator (gbmMilLogRatio r σ (T / 2 ^ ℓ)) with hψ₂
  have hSA : MeasurableSet {y : ℝ | |y| ≤ A} := measurableSet_le (by fun_prop) measurable_const
  have hψ₁m : Measurable ψ₁ := (measurable_gbmMilLogRatio r σ _).indicator hSA
  have hψ₂m : Measurable ψ₂ := (measurable_gbmMilLogRatio r σ _).indicator hSA
  set B₁ : Set (ℕ → ℝ) := {z | ∃ j < 2 ^ (ℓ + 1), A < |z j|} with hB₁
  set C₂ : Set (ℕ → ℝ) := {w | ∃ j < 2 ^ ℓ - 1, A < |w j|} with hC₂
  set C₃ : Set (ℕ → ℝ) := {w | x < |∑ j ∈ range (2 * (2 ^ ℓ - 1)), ψ₁ (w j)|} with hC₃
  set C₄ : Set (ℕ → ℝ) := {w | x < |∑ j ∈ range (2 ^ ℓ - 1), ψ₂ (w j)|} with hC₄
  set E : Set (ℕ → ℝ) := gbmExact r σ T s₀ (ℓ + 1) ⁻¹'
    {u : ℝ | |Real.log |u| - Real.log (|K|)| ≤ δbar} with hE
  have hB₁m : MeasurableSet B₁ := measurableSet_exists_lt_abs A _
  have hC₂m : MeasurableSet C₂ := measurableSet_exists_lt_abs A _
  have hsum₁ : Measurable fun w : ℕ → ℝ => |∑ j ∈ range (2 * (2 ^ ℓ - 1)), ψ₁ (w j)| :=
    (Finset.measurable_sum _ fun j _ => hψ₁m.comp (measurable_pi_apply j)).abs
  have hsum₂ : Measurable fun w : ℕ → ℝ => |∑ j ∈ range (2 ^ ℓ - 1), ψ₂ (w j)| :=
    (Finset.measurable_sum _ fun j _ => hψ₂m.comp (measurable_pi_apply j)).abs
  have hC₃m : MeasurableSet C₃ := measurableSet_lt measurable_const hsum₁
  have hC₄m : MeasurableSet C₄ := measurableSet_lt measurable_const hsum₂
  have hEm : MeasurableSet E :=
    (measurable_gbmExact r σ T s₀ (ℓ + 1)) (measurableSet_le (by fun_prop) measurable_const)
  have hB₂m : MeasurableSet (pairAvg ⁻¹' C₂) := measurable_pairAvg hC₂m
  have hB₄m : MeasurableSet (pairAvg ⁻¹' C₄) := measurable_pairAvg hC₄m
  set τ := (gaussianReal 0 1).real {u | t < |u|} with hτ
  -- the pointwise bound
  have hpt : ∀ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
      gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2 ≤
      B₁.indicator 1 z + (pairAvg ⁻¹' C₂).indicator 1 z + C₃.indicator 1 z +
        (pairAvg ⁻¹' C₄).indicator 1 z + (8 * τ ^ 2 + 2 * cbar ^ 2 * E.indicator 1 z) := by
    intro z
    have hI : ∀ s : Set (ℕ → ℝ), 0 ≤ s.indicator (1 : (ℕ → ℝ) → ℝ) z := fun s =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hrest : 0 ≤ 8 * τ ^ 2 + 2 * cbar ^ 2 * E.indicator 1 z := by
      have := hI E
      positivity
    have hle1 := sq_gbmDigitalCond_sub_le_one r σ T s₀ K ℓ z
    have h1' := hI B₁
    have h2' := hI (pairAvg ⁻¹' C₂)
    have h3' := hI C₃
    have h4' := hI (pairAvg ⁻¹' C₄)
    by_cases hz1 : z ∈ B₁
    · rw [Set.indicator_of_mem hz1, Pi.one_apply]
      linarith
    by_cases hz2 : z ∈ pairAvg ⁻¹' C₂
    · rw [Set.indicator_of_mem hz2, Pi.one_apply]
      linarith
    by_cases hz3 : z ∈ C₃
    · rw [Set.indicator_of_mem hz3, Pi.one_apply]
      linarith
    by_cases hz4 : z ∈ pairAvg ⁻¹' C₄
    · rw [Set.indicator_of_mem hz4, Pi.one_apply]
      linarith
    rw [Set.indicator_of_notMem hz1, Set.indicator_of_notMem hz2, Set.indicator_of_notMem hz3,
      Set.indicator_of_notMem hz4]
    simp only [zero_add]
    have h1 : ∀ j < 2 ^ (ℓ + 1), |z j| ≤ A := by
      intro j hj
      by_contra hcon
      exact hz1 ⟨j, hj, lt_of_not_ge hcon⟩
    have h2 : ∀ j < 2 ^ ℓ - 1, |pairAvg z j| ≤ A := by
      intro j hj
      by_contra hcon
      exact hz2 ⟨j, hj, lt_of_not_ge hcon⟩
    have h3 : |∑ j ∈ range (2 * (2 ^ ℓ - 1)), ψ₁ (z j)| ≤ x := by
      simp only [hC₃, Set.mem_ofPred_eq, not_lt] at hz3
      exact hz3
    have h4 : |∑ j ∈ range (2 ^ ℓ - 1), ψ₂ (pairAvg z j)| ≤ x := by
      simp only [hC₄, Set.mem_preimage, Set.mem_ofPred_eq, not_lt] at hz4
      exact hz4
    have key := condExp_sq_le_of_good_sample r σ (K := K) hs₀ hσ hT ℓ hθ₁ hθ₂ hx he he2 hd hQ ht
      hρ hc hδ h1 h2 h3 h4
    have hEind : E.indicator (1 : (ℕ → ℝ) → ℝ) z =
        {u : ℝ | |Real.log |u| - Real.log (|K|)| ≤ δbar}.indicator 1
          (gbmExact r σ T s₀ (ℓ + 1) z) := by
      by_cases hzE : z ∈ E
      · rw [Set.indicator_of_mem hzE, Set.indicator_of_mem (show gbmExact r σ T s₀ (ℓ + 1) z ∈
          {u : ℝ | |Real.log |u| - Real.log (|K|)| ≤ δbar} from hzE)]
        rfl
      · rw [Set.indicator_of_notMem hzE, Set.indicator_of_notMem (show gbmExact r σ T s₀ (ℓ + 1) z ∉
          {u : ℝ | |Real.log |u| - Real.log (|K|)| ≤ δbar} from hzE)]
    rw [hEind]
    exact key
  -- integrate
  have hg : ∀ s : Set (ℕ → ℝ), MeasurableSet s →
      Integrable (s.indicator (1 : (ℕ → ℝ) → ℝ)) stdNormalSeq := fun s hs =>
    (integrable_const (1 : ℝ)).indicator hs
  have hf : Integrable (fun z => (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
      gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2) stdNormalSeq :=
    (memLp_gbmDigitalCond_sub r σ T s₀ K ℓ).integrable_sq
  have i1 : Integrable (fun z => B₁.indicator (1 : (ℕ → ℝ) → ℝ) z +
      (pairAvg ⁻¹' C₂).indicator 1 z) stdNormalSeq := (hg _ hB₁m).add (hg _ hB₂m)
  have i2 : Integrable (fun z => B₁.indicator (1 : (ℕ → ℝ) → ℝ) z +
      (pairAvg ⁻¹' C₂).indicator 1 z + C₃.indicator 1 z) stdNormalSeq := i1.add (hg _ hC₃m)
  have i3 : Integrable (fun z => B₁.indicator (1 : (ℕ → ℝ) → ℝ) z +
      (pairAvg ⁻¹' C₂).indicator 1 z + C₃.indicator 1 z + (pairAvg ⁻¹' C₄).indicator 1 z)
      stdNormalSeq := i2.add (hg _ hB₄m)
  have i4 : Integrable (fun z => 2 * cbar ^ 2 * E.indicator (1 : (ℕ → ℝ) → ℝ) z)
      stdNormalSeq := (hg _ hEm).const_mul _
  have i5 : Integrable (fun z => 8 * τ ^ 2 + 2 * cbar ^ 2 * E.indicator (1 : (ℕ → ℝ) → ℝ) z)
      stdNormalSeq := (integrable_const _).add i4
  have hR : Integrable (fun z => B₁.indicator (1 : (ℕ → ℝ) → ℝ) z +
      (pairAvg ⁻¹' C₂).indicator 1 z + C₃.indicator 1 z + (pairAvg ⁻¹' C₄).indicator 1 z +
      (8 * τ ^ 2 + 2 * cbar ^ 2 * E.indicator 1 z)) stdNormalSeq := i3.add i5
  have e1 : ∫ z, (B₁.indicator (1 : (ℕ → ℝ) → ℝ) z + (pairAvg ⁻¹' C₂).indicator 1 z +
      C₃.indicator 1 z + (pairAvg ⁻¹' C₄).indicator 1 z +
      (8 * τ ^ 2 + 2 * cbar ^ 2 * E.indicator 1 z)) ∂stdNormalSeq =
      stdNormalSeq.real B₁ + stdNormalSeq.real (pairAvg ⁻¹' C₂) + stdNormalSeq.real C₃ +
        stdNormalSeq.real (pairAvg ⁻¹' C₄) + (8 * τ ^ 2 + 2 * cbar ^ 2 * stdNormalSeq.real E) := by
    rw [integral_add i3 i5, integral_add i2 (hg _ hB₄m), integral_add i1 (hg _ hC₃m),
      integral_add (hg _ hB₁m) (hg _ hB₂m), integral_add (integrable_const _) i4,
      integral_const (8 * τ ^ 2), integral_const_mul (2 * cbar ^ 2),
      integral_indicator_one hB₁m, integral_indicator_one hB₂m,
      integral_indicator_one hC₃m, integral_indicator_one hB₄m, integral_indicator_one hEm,
      probReal_univ, one_smul]
  -- the probabilities
  have hP1 := measureReal_exists_lt_abs_le_exp hA (2 ^ (ℓ + 1))
  have hP2 : stdNormalSeq.real (pairAvg ⁻¹' C₂) ≤
      ((2 ^ ℓ - 1 : ℕ) : ℝ) * (Real.sqrt 2 * Real.exp (-(A ^ 2 / 4))) := by
    rw [measurePreserving_pairAvg.measureReal_preimage hC₂m.nullMeasurableSet]
    exact measureReal_exists_lt_abs_le_exp hA _
  have hP3 := measureReal_lt_abs_sum_truncLogRatio_le r σ hh hθ₁ hθ₁' (2 * (2 ^ ℓ - 1)) x
  have hP4 : stdNormalSeq.real (pairAvg ⁻¹' C₄) ≤
      2 * Real.exp (-(x / (T / 2 ^ ℓ)) + 720 * 49152 * (1 + |r| + |σ| + σ ^ 2) ^ 6 *
        (((2 ^ ℓ - 1 : ℕ) : ℝ) * (T / 2 ^ ℓ))) := by
    rw [measurePreserving_pairAvg.measureReal_preimage hC₄m.nullMeasurableSet]
    exact measureReal_lt_abs_sum_truncLogRatio_le r σ hk hθ₂ hθ₂' _ x
  have hP5 : stdNormalSeq.real E ≤ 2 * δbar / (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi)) :=
    gbmExact_logSmallBall r σ hs₀ hσ hT (Real.log (|K|)) (ℓ + 1) hδ0
  have hP5' := mul_le_mul_of_nonneg_left hP5 (by positivity : (0 : ℝ) ≤ 2 * cbar ^ 2)
  calc _ ≤ _ := integral_mono hf hR hpt
    _ = _ := e1
    _ ≤ _ := by
        have hP1' : stdNormalSeq.real B₁ ≤ ((2 ^ (ℓ + 1) : ℕ) : ℝ) *
            (Real.sqrt 2 * Real.exp (-(A ^ 2 / 4))) := hP1
        have hP3' : stdNormalSeq.real C₃ ≤ 2 * Real.exp (-(x / (T / 2 ^ (ℓ + 1))) +
            720 * 49152 * (1 + |r| + |σ| + σ ^ 2) ^ 6 *
              (((2 * (2 ^ ℓ - 1) : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)))) := hP3
        linarith

/-! ### The scales of the endpoint -/

/-- **The scales of the endpoint** (Giles 2015, §5.2, p. 36, l. 1575–1577, with a logarithmic
factor).  With `h = q²`, `L = v²` (`v ≥ 1`), the truncation level `A = 4v`, the Gaussian tail level
`t = 2v`, the log-error level `x = q²(4v² + 2DT)` and `e`, `d` the bounds of
`abs_gbmMilFactor_sub_one_le`, `abs_gbmMilFactor_mul_sub_le`, all smallness conditions of
`condExp_integral_sq_le` hold once `ε = qv ≤ 1/K_ε`, and the coefficient and the window are at most
`K_c q v²` and `K_N q v`; the constants depend only on `r`, `σ`, `T` (through
`Λ = 1 + |r| + |σ| + σ²` and `D ≥ 0`). -/
lemma condExp_endpoint_scales {r σ T D Λ P Km Kc Kρ KN Kε q v x e d : ℝ} (hσ : σ ≠ 0)
    (hT : 0 < T) (hΛ : Λ = 1 + |r| + |σ| + σ ^ 2) (hD : 0 ≤ D) (hP : P = 4 + 2 * D * T)
    (hKm : Km = 16 * P + 20 * Λ) (hKc : Kc = Km / |σ| + 4 * (14 * Λ + 4 * P))
    (hKρ : Kρ = Km + 4 * Λ * (14 * Λ + 4 * P) + 3 * Λ)
    (hKN : KN = 2 * Kρ + P + 3250 * Λ ^ 3 + 5 * Λ)
    (hKε : Kε = 4160 * Λ ^ 3 + 4 * P + 2 * Kρ + 40 * Λ + 1)
    (hq : 0 < q) (hv : 1 ≤ v) (hε : q * v ≤ 1 / Kε)
    (hx : x = q ^ 2 * (4 * v ^ 2 + 2 * D * T))
    (he : e = |r| * q ^ 2 + |σ| * q * (4 * v) + σ ^ 2 / 2 * (q ^ 2 * (4 * v) ^ 2 + q ^ 2))
    (hd : d = σ ^ 2 / 2 * (q ^ 2 * (4 * v) ^ 2 + q ^ 2) + |r| * q ^ 2 * e) :
    q * (1 + 4 * v) ≤ 1 / (4 * Λ) ∧ 26 * Λ ^ 3 * (q * (1 + 4 * v)) ≤ 1 / 16 ∧
      2 * q * (1 + 4 * v) ≤ 1 / (4 * Λ) ∧ 26 * Λ ^ 3 * (2 * q * (1 + 4 * v)) ≤ 1 / 16 ∧
      x ≤ 1 / 4 ∧ e ≤ 1 / 2 ∧ 2 * |r| * q ^ 2 + |σ| * q * (4 * v) ≤ 1 ∧
      16 * x + 2 * d + 2 * v * (2 * |σ| * q * (e + 4 * x)) + 2 * v * |σ| * q + |r| * q ^ 2 ≤
        1 / 2 ∧
      (16 * x + 2 * d + 2 * v * (2 * |σ| * q * (e + 4 * x))) / (|σ| * q) ≤ Kc * q * v ^ 2 ∧
      2 * (16 * x + 2 * d + 2 * v * (2 * |σ| * q * (e + 4 * x)) + 2 * v * |σ| * q +
        |r| * q ^ 2) + x + 26 * Λ ^ 3 * (q * (1 + 4 * v)) ^ 3 +
        (|r - σ ^ 2 / 2| * q ^ 2 + |σ| * q * (4 * v)) ≤ KN * (q * v) := by
  have hr0 := abs_nonneg r
  have hσ0 : 0 < |σ| := abs_pos.2 hσ
  have hσ2 := sq_nonneg σ
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; linarith
  have hrΛ : |r| ≤ Λ := by rw [hΛ]; linarith
  have hσΛ : |σ| ≤ Λ := by rw [hΛ]; linarith
  have hσ2Λ : σ ^ 2 ≤ Λ := by rw [hΛ]; linarith
  have hbΛ : |r - σ ^ 2 / 2| ≤ Λ := by
    have := abs_sub r (σ ^ 2 / 2)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ σ ^ 2 / 2)] at this
    rw [hΛ]
    linarith
  have hDT : 0 ≤ D * T := mul_nonneg hD hT.le
  have hP4 : 4 ≤ P := by rw [hP]; linarith
  have hKm0 : 0 ≤ Km := by rw [hKm]; positivity
  have hKρ0 : 0 ≤ Kρ := by rw [hKρ]; positivity
  have hKε1 : 1 ≤ Kε := by
    have : 0 ≤ 4160 * Λ ^ 3 + 4 * P + 2 * Kρ + 40 * Λ := by positivity
    rw [hKε]
    linarith
  have hqv : q ≤ q * v := by
    calc q = q * 1 := (mul_one q).symm
      _ ≤ q * v := mul_le_mul_of_nonneg_left hv hq.le
  set ε := q * v with hεdef
  have hε0 : 0 < ε := lt_of_lt_of_le hq hqv
  have hKεε : Kε * ε ≤ 1 := by
    rw [le_div_iff₀ (by linarith)] at hε
    linarith
  -- the pieces of `K_ε ε ≤ 1`
  have hΛ3ε : 0 ≤ Λ ^ 3 * ε := by positivity
  have hPε : 0 ≤ P * ε := by positivity
  have hKρε : 0 ≤ Kρ * ε := by positivity
  have hΛε : 0 ≤ Λ * ε := by positivity
  have hsplit : 4160 * (Λ ^ 3 * ε) + 4 * (P * ε) + 2 * (Kρ * ε) + 40 * (Λ * ε) + ε ≤ 1 := by
    rw [hKε] at hKεε
    linarith only [hKεε]
  have c1 : 4160 * (Λ ^ 3 * ε) ≤ 1 := by linarith only [hsplit, hPε, hKρε, hΛε, hε0]
  have c2 : 4 * (P * ε) ≤ 1 := by linarith only [hsplit, hΛ3ε, hKρε, hΛε, hε0]
  have c3 : 2 * (Kρ * ε) ≤ 1 := by linarith only [hsplit, hΛ3ε, hPε, hΛε, hε0]
  have c4 : 40 * (Λ * ε) ≤ 1 := by linarith only [hsplit, hΛ3ε, hPε, hKρε, hε0]
  have c5 : ε ≤ 1 := by linarith only [hsplit, hΛ3ε, hPε, hKρε, hΛε]
  have hq0 := hq.le
  have hε2 : ε ^ 2 ≤ ε := by
    rw [sq]
    exact mul_le_of_le_one_right hε0.le c5
  have hε3 : ε ^ 3 ≤ ε := by
    have := pow_le_pow_of_le_one hε0.le c5 (show 1 ≤ 3 by norm_num)
    rwa [pow_one] at this
  have hq2 : q ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hq0 hqv 2
  have hqv2 : q ^ 2 * v ^ 2 = ε ^ 2 := by rw [hεdef]; ring
  have hΛε2 : Λ * ε ^ 2 ≤ Λ * ε := mul_le_mul_of_nonneg_left hε2 (by linarith)
  have hΛε20 : 0 ≤ Λ * ε ^ 2 := by positivity
  -- the three basic bounds
  have hx' : x ≤ P * ε ^ 2 := by
    rw [hx, hP]
    have e1 : q ^ 2 * (4 * v ^ 2 + 2 * D * T) = 4 * (q ^ 2 * v ^ 2) + 2 * D * T * q ^ 2 := by
      ring
    rw [e1, hqv2]
    have := mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ 2 * D * T)
    linarith only [this]
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hPε2 : P * ε ^ 2 ≤ P * ε := mul_le_mul_of_nonneg_left hε2 (by linarith)
  have h16 : q ^ 2 * (4 * v) ^ 2 = 16 * ε ^ 2 := by rw [← hqv2]; ring
  have hσε : |σ| * ε ≤ Λ * ε := mul_le_mul_of_nonneg_right hσΛ hε0.le
  have hrq : |r| * q ^ 2 ≤ Λ * ε ^ 2 := mul_le_mul hrΛ hq2 (by positivity) (by linarith)
  have hσq : |σ| * q * (4 * v) = 4 * (|σ| * ε) := by rw [hεdef]; ring
  have he' : e ≤ 14 * Λ * ε := by
    rw [he]
    have h4 : q ^ 2 * (4 * v) ^ 2 + q ^ 2 ≤ 17 * ε := by
      rw [h16]
      linarith only [hε2, hq2]
    have h5 : σ ^ 2 / 2 * (q ^ 2 * (4 * v) ^ 2 + q ^ 2) ≤ Λ / 2 * (17 * ε) :=
      mul_le_mul (by linarith only [hσ2Λ]) h4 (by positivity) (by linarith only [hΛ1])
    rw [hσq]
    linarith only [hrq, hΛε2, hσε, h5, hΛε]
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he2 : e ≤ 1 / 2 := by linarith only [he', c4, hΛε]
  have hd' : d ≤ 10 * Λ * ε ^ 2 := by
    rw [hd]
    have h4 : q ^ 2 * (4 * v) ^ 2 + q ^ 2 ≤ 17 * ε ^ 2 := by
      rw [h16]
      linarith only [hq2]
    have h5 : σ ^ 2 / 2 * (q ^ 2 * (4 * v) ^ 2 + q ^ 2) ≤ Λ / 2 * (17 * ε ^ 2) :=
      mul_le_mul (by linarith only [hσ2Λ]) h4 (by positivity) (by linarith only [hΛ1])
    have h6 : |r| * q ^ 2 * e ≤ Λ * ε ^ 2 * (1 / 2) :=
      mul_le_mul hrq he2 he0 (by positivity)
    linarith only [h5, h6, hΛε20]
  -- the mean and standard-deviation coefficients
  have hm' : 16 * x + 2 * d ≤ Km * ε ^ 2 := by
    rw [hKm]
    linarith only [hx', hd']
  have hex : e + 4 * x ≤ (14 * Λ + 4 * P) * ε := by linarith only [he', hx', hPε2]
  have h4σ : 2 * v * (2 * |σ| * q * (e + 4 * x)) = 4 * |σ| * ε * (e + 4 * x) := by
    rw [hεdef]; ring
  have has' : 2 * v * (2 * |σ| * q * (e + 4 * x)) ≤ 4 * Λ * (14 * Λ + 4 * P) * ε ^ 2 := by
    rw [h4σ]
    have h1 : 4 * |σ| * ε ≤ 4 * Λ * ε := by linarith only [hσε]
    calc 4 * |σ| * ε * (e + 4 * x) ≤ 4 * Λ * ε * ((14 * Λ + 4 * P) * ε) :=
          mul_le_mul h1 hex (by positivity) (by positivity)
      _ = 4 * Λ * (14 * Λ + 4 * P) * ε ^ 2 := by ring
  have hsq' : 2 * v * |σ| * q = 2 * (|σ| * ε) := by rw [hεdef]; ring
  have hρ' : 16 * x + 2 * d + 2 * v * (2 * |σ| * q * (e + 4 * x)) + 2 * v * |σ| * q +
      |r| * q ^ 2 ≤ Kρ * ε := by
    rw [hsq', hKρ]
    have hKm2 : Km * ε ^ 2 ≤ Km * ε := mul_le_mul_of_nonneg_left hε2 hKm0
    have hA2 : 4 * Λ * (14 * Λ + 4 * P) * ε ^ 2 ≤ 4 * Λ * (14 * Λ + 4 * P) * ε :=
      mul_le_mul_of_nonneg_left hε2 (by positivity)
    linarith only [hm', hKm2, has', hA2, hσε, hrq, hΛε2]
  have hq1 : q * (1 + 4 * v) ≤ 5 * ε := by
    have : q * (1 + 4 * v) = q + 4 * ε := by rw [hεdef]; ring
    rw [this]
    linarith only [hqv]
  have hΛ0 : 0 < Λ := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, he2, ?_, by linarith only [hρ', c3], ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hq1 (by positivity : (0 : ℝ) ≤ 4 * Λ)
    linarith only [this, c4, hΛε]
  · have := mul_le_mul_of_nonneg_left hq1 (by positivity : (0 : ℝ) ≤ 26 * Λ ^ 3)
    linarith only [this, c1, hΛ3ε]
  · rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hq1 (by positivity : (0 : ℝ) ≤ 8 * Λ)
    linarith only [this, c4, hΛε]
  · have := mul_le_mul_of_nonneg_left hq1 (by positivity : (0 : ℝ) ≤ 52 * Λ ^ 3)
    linarith only [this, c1, hΛ3ε]
  · linarith only [hx', hPε2, c2]
  · rw [hσq]
    linarith only [hrq, hΛε2, hσε, c4, hΛε]
  · rw [div_le_iff₀ (by positivity)]
    have hσne := hσ0.ne'
    have e1 : Kc * q * v ^ 2 * (|σ| * q) =
        Km * ε ^ 2 + 4 * (14 * Λ + 4 * P) * |σ| * ε ^ 2 := by
      rw [hKc, hεdef]
      field_simp
    rw [e1, h4σ]
    have h2 : 4 * |σ| * ε * (e + 4 * x) ≤ 4 * |σ| * ε * ((14 * Λ + 4 * P) * ε) :=
      mul_le_mul_of_nonneg_left hex (by positivity)
    linarith only [hm', h2]
  · have h1 : (q * (1 + 4 * v)) ^ 3 ≤ (5 * ε) ^ 3 := pow_le_pow_left₀ (by positivity) hq1 3
    have h3 : |r - σ ^ 2 / 2| * q ^ 2 ≤ Λ * ε ^ 2 :=
      mul_le_mul hbΛ hq2 (by positivity) (by linarith)
    have h4 : 26 * Λ ^ 3 * (q * (1 + 4 * v)) ^ 3 ≤ 26 * Λ ^ 3 * (125 * ε) := by
      have : (5 * ε) ^ 3 ≤ 125 * ε := by
        have e2 : (5 * ε) ^ 3 = 125 * ε ^ 3 := by ring
        rw [e2]
        linarith only [hε3]
      exact mul_le_mul_of_nonneg_left (h1.trans this) (by positivity)
    rw [hσq, hKN]
    linarith only [hρ', hx', hPε2, h4, h3, hΛε2, hσε]

/-- `e^{−c(ℓ+1)} ≤ (2^{−(ℓ+1)})^c` (`e ≥ 2`; Giles 2015, §5.2: the tails `e^{−cL}` against the step
`h = T 2^{−L}`). -/
lemma exp_neg_nat_mul_succ_le (c ℓ : ℕ) :
    Real.exp (-(c * ((ℓ : ℝ) + 1))) ≤ (1 / 2 ^ (ℓ + 1)) ^ c := by
  have h1 : (2 : ℝ) ^ (ℓ + 1) ≤ Real.exp ((ℓ : ℝ) + 1) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc (2 : ℝ) ^ (ℓ + 1) ≤ Real.exp 1 ^ (ℓ + 1) := pow_le_pow_left₀ (by norm_num) h2 _
      _ = Real.exp ((ℓ : ℝ) + 1) := by
          rw [← Real.exp_nat_mul]
          push_cast
          ring_nf
  have e : -(c * ((ℓ : ℝ) + 1)) = c * (-((ℓ : ℝ) + 1)) := by ring
  rw [e, Real.exp_nat_mul, Real.exp_neg]
  refine pow_le_pow_left₀ (by positivity) ?_ c
  rw [one_div]
  exact inv_anti₀ (by positivity) h1

/-- `(√a)^n = a^{n/2}` for `a ≥ 0` (the rate `h^{3/2}` of Giles 2015, §5.2, p. 36, l. 1577). -/
lemma sqrt_pow_eq_rpow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt a ^ n = a ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha]
  ring_nf

/-- **The endpoint on the levels with `h log(1/h)` small** (Giles 2015, §5.2, p. 36, l. 1575–1577:
"a variance which is approximately `O(h^{3/2})`").  For GBM with `σ ≠ 0`, `T > 0` there are
`ε₀ > 0` and `C ≥ 0`, depending only on `r`, `σ`, `T`, such that for every `s₀ ≠ 0`, every strike
`K` and every level `ℓ + 1` with `√h √(ℓ + 1) ≤ ε₀` (`h = T 2^{−(ℓ+1)}`):
`E[(P^f_{ℓ+1} − P^c_ℓ)²] ≤ C h^{3/2} (ℓ + 1)^{5/2}`, written `C (√h)³ (√(ℓ+1))⁵`.  Proof:
`condExp_integral_sq_le` with `A = 4√(ℓ+1)`, `t = 2√(ℓ+1)`, `x = h(4(ℓ + 1) + 2DT)`
(`condExp_endpoint_scales`); the four tails are at most `23 · 4^{−(ℓ+1)} = 23 (h/T)²`
(`exp_neg_nat_mul_succ_le`) and the main term is `2c̄² · 2δ̄/(|σ|√(2πT))` with
`c̄ = K_c h^{1/2}(ℓ+1)`, `δ̄ = K_N (h(ℓ + 1))^{1/2}`. -/
lemma condExp_endpoint_small (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ K : ℝ), s₀ ≠ 0 → ∀ ℓ : ℕ,
      Real.sqrt (T / 2 ^ (ℓ + 1)) * Real.sqrt ((ℓ : ℝ) + 1) ≤ ε₀ →
      ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2
          ∂stdNormalSeq ≤
        C * (Real.sqrt (T / 2 ^ (ℓ + 1)) ^ 3 * Real.sqrt ((ℓ : ℝ) + 1) ^ 5) := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = 1 + |r| + |σ| + σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 720 * 49152 * Λ ^ 6 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 4 + 2 * D * T := ⟨_, rfl⟩
  obtain ⟨Km, hKm⟩ : ∃ Km : ℝ, Km = 16 * P + 20 * Λ := ⟨_, rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = Km / |σ| + 4 * (14 * Λ + 4 * P) := ⟨_, rfl⟩
  obtain ⟨Kρ, hKρ⟩ : ∃ Kρ : ℝ, Kρ = Km + 4 * Λ * (14 * Λ + 4 * P) + 3 * Λ := ⟨_, rfl⟩
  obtain ⟨KN, hKN⟩ : ∃ KN : ℝ, KN = 2 * Kρ + P + 3250 * Λ ^ 3 + 5 * Λ := ⟨_, rfl⟩
  obtain ⟨Kε, hKε⟩ : ∃ Kε : ℝ, Kε = 4160 * Λ ^ 3 + 4 * P + 2 * Kρ + 40 * Λ + 1 := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hKm0 : 0 ≤ Km := by rw [hKm]; positivity
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hKρ0 : 0 ≤ Kρ := by rw [hKρ]; positivity
  have hKN0 : 0 ≤ KN := by rw [hKN]; positivity
  have hKε0 : 0 < Kε := by rw [hKε]; positivity
  have hsT := Real.sqrt_pos.2 hT
  refine ⟨1 / Kε, by positivity,
    23 * Real.sqrt T / T ^ 2 + 4 * Kc ^ 2 * KN / (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi)),
    by positivity, fun s₀ K hs₀ ℓ hε => ?_⟩
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  set q := Real.sqrt (T / 2 ^ (ℓ + 1)) with hqdef
  set v := Real.sqrt ((ℓ : ℝ) + 1) with hvdef
  have hq : 0 < q := Real.sqrt_pos.2 hh
  have hqne : q ≠ 0 := hq.ne'
  have hTne : T ≠ 0 := hT.ne'
  have hq2 : q ^ 2 = T / 2 ^ (ℓ + 1) := Real.sq_sqrt hh.le
  have hL0 : (0 : ℝ) ≤ (ℓ : ℝ) + 1 := by positivity
  have hv1 : 1 ≤ v := Real.one_le_sqrt.2 (by linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)])
  have hv2 : v ^ 2 = (ℓ : ℝ) + 1 := Real.sq_sqrt hL0
  set x := q ^ 2 * (4 * v ^ 2 + 2 * D * T) with hx
  set e := |r| * q ^ 2 + |σ| * q * (4 * v) + σ ^ 2 / 2 * (q ^ 2 * (4 * v) ^ 2 + q ^ 2) with he
  set d := σ ^ 2 / 2 * (q ^ 2 * (4 * v) ^ 2 + q ^ 2) + |r| * q ^ 2 * e with hd
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := condExp_endpoint_scales hσ hT hΛ hD0 hP
    hKm hKc hKρ hKN hKε hq hv1 hε hx he hd
  have hk2 : Real.sqrt (T / 2 ^ ℓ) ≤ 2 * q := by
    rw [div_two_pow_eq_two_mul T ℓ, ← hq2]
    calc Real.sqrt (2 * q ^ 2) ≤ Real.sqrt ((2 * q) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith only [sq_nonneg q])
      _ = 2 * q := Real.sqrt_sq (by positivity)
  have hk2' : Real.sqrt (T / 2 ^ ℓ) * (1 + 4 * v) ≤ 2 * q * (1 + 4 * v) :=
    mul_le_mul_of_nonneg_right hk2 (by positivity)
  have key := condExp_integral_sq_le r σ (s₀ := s₀) (K := K) (A := 4 * v) (t := 2 * v) (x := x)
    (e := e) (d := d) (cbar := Kc * q * v ^ 2) (δbar := KN * (q * v)) hs₀ hσ hT ℓ
    (by positivity) (by rw [← hqdef, ← hΛ]; exact s1) (by rw [← hqdef, ← hΛ]; exact s2)
    (by rw [← hΛ]; exact hk2'.trans s3)
    (by
      rw [← hΛ]
      exact (mul_le_mul_of_nonneg_left hk2' (by positivity)).trans s4)
    s5 (by rw [← hqdef, ← hq2]) s6 (by rw [← hq2]) (by rw [← hqdef, ← hq2]; exact s7)
    (by positivity) (by rw [← hqdef, ← hq2]; exact s8) (by rw [← hqdef]; exact s9)
    (by rw [← hqdef, ← hq2, ← hΛ]; exact s10) (by positivity)
  rw [← hΛ, ← hD] at key
  -- the four tails
  set a : ℝ := 1 / 2 ^ (ℓ + 1) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have h2a : (2 : ℝ) ^ (ℓ + 1) * a = 1 := by rw [ha]; field_simp
  have hqa : q ^ 2 = T * a := by rw [hq2, ha]; ring
  have hT1 : ((((2 ^ (ℓ + 1) : ℕ) : ℝ) + ((2 ^ ℓ - 1 : ℕ) : ℝ)) *
      (Real.sqrt 2 * Real.exp (-((4 * v) ^ 2 / 4)))) ≤ 3 * a ^ 2 := by
    have hc1 : (((2 ^ (ℓ + 1) : ℕ) : ℝ) + ((2 ^ ℓ - 1 : ℕ) : ℝ)) ≤ 2 * 2 ^ (ℓ + 1) := by
      have h1 : ((2 ^ ℓ - 1 : ℕ) : ℝ) ≤ ((2 ^ ℓ : ℕ) : ℝ) := Nat.cast_le.2 (Nat.sub_le _ _)
      push_cast at h1 ⊢
      have h2 : (2 : ℝ) ^ ℓ ≤ 2 ^ (ℓ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have he4 : Real.exp (-((4 * v) ^ 2 / 4)) ≤ a ^ 4 := by
      have e1 : (4 * v) ^ 2 / 4 = ((4 : ℕ) : ℝ) * ((ℓ : ℝ) + 1) := by
        rw [← hv2]
        push_cast
        ring
      rw [e1]
      exact exp_neg_nat_mul_succ_le 4 ℓ
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    calc (((2 ^ (ℓ + 1) : ℕ) : ℝ) + ((2 ^ ℓ - 1 : ℕ) : ℝ)) *
          (Real.sqrt 2 * Real.exp (-((4 * v) ^ 2 / 4)))
        ≤ (2 * 2 ^ (ℓ + 1)) * (3 / 2 * a ^ 4) :=
          mul_le_mul hc1 (mul_le_mul hs2 he4 (by positivity) (by norm_num)) (by positivity)
            (by positivity)
      _ = 3 * a ^ 3 * ((2 : ℝ) ^ (ℓ + 1) * a) := by ring
      _ = 3 * a ^ 3 := by rw [h2a, mul_one]
      _ ≤ 3 * a ^ 2 := by
          have : a ^ 3 ≤ a ^ 2 := pow_le_pow_of_le_one ha0.le ha1 (by norm_num)
          linarith
  have hT2 : 2 * Real.exp (-(x / (T / 2 ^ (ℓ + 1))) + D *
      (((2 * (2 ^ ℓ - 1) : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)))) ≤ 2 * a ^ 2 := by
    have hm : (((2 * (2 ^ ℓ - 1) : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1))) ≤ T :=
      natCast_mul_div_two_pow_le hT.le (two_mul_two_pow_sub_one_le ℓ)
    have e1 : x / (T / 2 ^ (ℓ + 1)) = 4 * v ^ 2 + 2 * D * T := by
      rw [← hq2, hx]
      field_simp
    have hexp : -(x / (T / 2 ^ (ℓ + 1))) + D * (((2 * (2 ^ ℓ - 1) : ℕ) : ℝ) * (T / 2 ^ (ℓ + 1)))
        ≤ -(((4 : ℕ) : ℝ) * ((ℓ : ℝ) + 1)) := by
      have e2 : -(((4 : ℕ) : ℝ) * ((ℓ : ℝ) + 1)) = -(4 * v ^ 2) := by
        rw [hv2]
        push_cast
        ring
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_left hm hD0
      linarith only [this, mul_nonneg hD0 hT.le]
    have h1 := (Real.exp_le_exp.2 hexp).trans (exp_neg_nat_mul_succ_le 4 ℓ)
    have h2 : a ^ 4 ≤ a ^ 2 := pow_le_pow_of_le_one ha0.le ha1 (by norm_num)
    linarith only [h1, h2]
  have hT3 : 2 * Real.exp (-(x / (T / 2 ^ ℓ)) + D *
      (((2 ^ ℓ - 1 : ℕ) : ℝ) * (T / 2 ^ ℓ))) ≤ 2 * a ^ 2 := by
    have hm : (((2 ^ ℓ - 1 : ℕ) : ℝ) * (T / 2 ^ ℓ)) ≤ T :=
      natCast_mul_div_two_pow_le hT.le (Nat.sub_le _ _)
    have e1 : x / (T / 2 ^ ℓ) = 2 * v ^ 2 + D * T := by
      rw [div_two_pow_eq_two_mul T ℓ, ← hq2, hx]
      field_simp
      ring
    have hexp : -(x / (T / 2 ^ ℓ)) + D * (((2 ^ ℓ - 1 : ℕ) : ℝ) * (T / 2 ^ ℓ))
        ≤ -(((2 : ℕ) : ℝ) * ((ℓ : ℝ) + 1)) := by
      have e2 : -(((2 : ℕ) : ℝ) * ((ℓ : ℝ) + 1)) = -(2 * v ^ 2) := by
        rw [hv2]
        push_cast
        ring
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_left hm hD0
      linarith only [this]
    have h1 := (Real.exp_le_exp.2 hexp).trans (exp_neg_nat_mul_succ_le 2 ℓ)
    linarith only [h1]
  have hT4 : 8 * (gaussianReal 0 1).real {u | 2 * v < |u|} ^ 2 ≤ 16 * a ^ 2 := by
    have h1 := gaussianReal_real_lt_abs_le_exp (A := 2 * v) (by positivity)
    have e1 : (2 * v) ^ 2 / 4 = ((1 : ℕ) : ℝ) * ((ℓ : ℝ) + 1) := by
      rw [← hv2]
      push_cast
      ring
    rw [e1] at h1
    have h2 := exp_neg_nat_mul_succ_le 1 ℓ
    rw [pow_one] at h2
    have h3 : (gaussianReal 0 1).real {u | 2 * v < |u|} ≤ Real.sqrt 2 * a :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2))
    have h4 := pow_le_pow_left₀ measureReal_nonneg h3 2
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h4
    linarith only [h4]
  -- `a² ≤ √T q³ / T²`
  have hqT : q ≤ Real.sqrt T := by
    rw [hqdef]
    exact Real.sqrt_le_sqrt (div_le_self hT.le (one_le_pow₀ (by norm_num)))
  have ha2 : a ^ 2 ≤ Real.sqrt T / T ^ 2 * q ^ 3 := by
    have e1 : a ^ 2 = q ^ 3 * q / T ^ 2 := by
      have : q ^ 3 * q = (q ^ 2) ^ 2 := by ring
      rw [this, hqa]
      field_simp
    rw [e1, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    calc q ^ 3 * q ≤ q ^ 3 * Real.sqrt T := mul_le_mul_of_nonneg_left hqT (by positivity)
      _ = Real.sqrt T * q ^ 3 := by ring
  -- the main term
  have hmain : 2 * (Kc * q * v ^ 2) ^ 2 * (2 * (KN * (q * v)) /
      (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi))) =
      4 * Kc ^ 2 * KN / (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi)) * (q ^ 3 * v ^ 5) := by
    ring
  have hv5 : q ^ 3 ≤ q ^ 3 * v ^ 5 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hv1)
  have hC1 : 0 ≤ Real.sqrt T / T ^ 2 := by positivity
  have hfin := mul_le_mul_of_nonneg_left (ha2.trans (mul_le_mul_of_nonneg_left hv5 hC1))
    (by norm_num : (0 : ℝ) ≤ 23)
  calc _ ≤ _ := key
    _ ≤ 23 * a ^ 2 + 4 * Kc ^ 2 * KN / (|σ| * Real.sqrt T * Real.sqrt (2 * Real.pi)) *
          (q ^ 3 * v ^ 5) := by
        rw [← hmain]
        linarith only [hT1, hT2, hT3, hT4]
    _ ≤ _ := by
        rw [add_mul]
        have e2 : 23 * Real.sqrt T / T ^ 2 * (q ^ 3 * v ^ 5) =
            23 * (Real.sqrt T / T ^ 2 * (q ^ 3 * v ^ 5)) := by ring
        rw [e2]
        linarith only [hfin]

/-! ### The endpoint `β = 3/2` up to a logarithmic factor -/

/-- **G5.2-14/15 at the endpoint: the variance of the conditional-expectation correction is
`O(h^{3/2} (log(1/h))^{5/2})`, uniformly in `s₀` and `K`** (Giles 2015, §5.2, p. 36, l. 1575–1577:
"Consequently, the difference in payoff between the coarse and fine paths near the payoff
discontinuity is `O(h^{1/2})`, giving a variance which is approximately `O(h^{3/2})`").  For GBM
`dS = rS dt + σS dW` with `σ ≠ 0` and `T > 0` there is `C ≥ 0`, depending only on `r`, `σ` and
`T`, such that for every initial value `s₀ ≠ 0`, every strike `K ∈ ℝ` (`K = 0` included) and every
level `ℓ + 1 ≥ 1` (`h_{ℓ+1} = T 2^{−(ℓ+1)}`, so `(ℓ + 1) log 2 = log(T/h_{ℓ+1})`) the correction
`P^f_{ℓ+1} − P^c_ℓ` of the conditional-expectation payoffs (`gbmDigitalCondFine`,
`gbmDigitalCondCoarse`) is square integrable and satisfies
`E[(P^f_{ℓ+1} − P^c_ℓ)²] ≤ C h_{ℓ+1}^{3/2} (ℓ + 1)^{5/2}`, hence
`V_{ℓ+1} ≤ C h_{ℓ+1}^{3/2} (ℓ + 1)^{5/2}`.

Proof: on the levels with `h (ℓ + 1)` small (`condExp_endpoint_small`): outside an event of
probability `O(h²)` all increments are `O((ℓ + 1)^{1/2})` and the logarithms of the ratios of the
fine and the coarse Milstein paths to the exact solution are `O(h (ℓ + 1))`
(`measureReal_lt_abs_sum_truncLogRatio_le`: Chernoff's bound for the truncated log-ratio, whose
mean is `O(h²)` per step because its terms of order `h^{3/2}` are odd); there the conditional means
and standard deviations match to within `O(h (ℓ + 1))` relative to the fine value, and the two
payoffs differ by at most `2P(|Z| > t) + O(h^{1/2} (ℓ + 1))` near the strike, in a window of
`log|S_T|` of width `O((h (ℓ + 1))^{1/2})` (`condPayoff_sq_le_of_good`), by `2P(|Z| > t)` away from
it, with `t = 2(ℓ + 1)^{1/2}`; the bounded density of `log|S_T|` (`gbmExact_logSmallBall`) gives
`O(h (ℓ + 1)²) · O((h (ℓ + 1))^{1/2})`.  On the other levels
`E[(P^f − P^c)²] ≤ 1 ≤ C (h (ℓ+1))^{3/2}`; `V ≤ E[(·)²]`.

**Deviation.**  The paper's `O(h^{3/2})` is proved up to the factor
`(ℓ + 1)^{5/2} ≍ (log(1/h))^{5/2}` (`gbm_digital_condExp_variance_endpoint_log` with
`log(1/h)`); the constant is explicit in the proof but far from sharp, and the factor `25 e^{−rT}`
is omitted. -/
theorem gbm_digital_condExp_variance_endpoint (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ K : ℝ), s₀ ≠ 0 → ∀ ℓ : ℕ,
      MemLp (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ K ℓ z) 2 stdNormalSeq ∧
      ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2
          ∂stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ (3 / 2 : ℝ) * ((ℓ : ℝ) + 1) ^ (5 / 2 : ℝ) ∧
      variance (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
          gbmDigitalCondCoarse r σ T s₀ K ℓ z) stdNormalSeq ≤
        C * (T / 2 ^ (ℓ + 1)) ^ (3 / 2 : ℝ) * ((ℓ : ℝ) + 1) ^ (5 / 2 : ℝ) := by
  obtain ⟨ε₀, hε₀, C₀, hC₀, hsmall⟩ := condExp_endpoint_small r σ hσ hT
  refine ⟨C₀ + 1 / ε₀ ^ 3, by positivity, fun s₀ K hs₀ ℓ => ?_⟩
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have hL0 : (0 : ℝ) ≤ (ℓ : ℝ) + 1 := by positivity
  set q := Real.sqrt (T / 2 ^ (ℓ + 1)) with hqdef
  set v := Real.sqrt ((ℓ : ℝ) + 1) with hvdef
  have hq : 0 < q := Real.sqrt_pos.2 hh
  have hv1 : 1 ≤ v := Real.one_le_sqrt.2 (by linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)])
  have hconv : q ^ 3 * v ^ 5 =
      (T / 2 ^ (ℓ + 1)) ^ (3 / 2 : ℝ) * ((ℓ : ℝ) + 1) ^ (5 / 2 : ℝ) := by
    rw [hqdef, hvdef, sqrt_pow_eq_rpow hh.le, sqrt_pow_eq_rpow hL0]
    norm_num
  have hqv : 0 ≤ q ^ 3 * v ^ 5 := by positivity
  have key : ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
      gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2 ∂stdNormalSeq ≤
      (C₀ + 1 / ε₀ ^ 3) * (q ^ 3 * v ^ 5) := by
    by_cases hε : q * v ≤ ε₀
    · have h1 := hsmall s₀ K hs₀ ℓ hε
      have h2 : 0 ≤ 1 / ε₀ ^ 3 * (q ^ 3 * v ^ 5) := by positivity
      rw [add_mul]
      linarith
    · rw [not_le] at hε
      have h1 : ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
          gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2 ∂stdNormalSeq ≤ 1 := by
        refine (integral_mono (memLp_gbmDigitalCond_sub r σ T s₀ K ℓ).integrable_sq
          (integrable_const 1) (sq_gbmDigitalCond_sub_le_one r σ T s₀ K ℓ)).trans (le_of_eq ?_)
        simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      have h2 : 1 ≤ 1 / ε₀ ^ 3 * (q ^ 3 * v ^ 5) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity), one_mul]
        calc ε₀ ^ 3 ≤ (q * v) ^ 3 := pow_le_pow_left₀ hε₀.le hε.le 3
          _ = q ^ 3 * v ^ 3 := by ring
          _ ≤ q ^ 3 * v ^ 5 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv1 (by norm_num)) (by positivity)
      have h3 : 0 ≤ C₀ * (q ^ 3 * v ^ 5) := by positivity
      rw [add_mul]
      linarith
  rw [hconv, ← mul_assoc] at key
  refine ⟨memLp_gbmDigitalCond_sub r σ T s₀ K ℓ, key, ?_⟩
  exact (variance_le_expectation_sq ((measurable_gbmDigitalCondFine r σ T s₀ K (ℓ + 1)).sub
    (measurable_gbmDigitalCondCoarse r σ T s₀ K ℓ)).aestronglyMeasurable).trans key

/-- **G5.2-14/15 at the endpoint, in the form of `gbm_digital_condExp_variance_rate`** (Giles 2015,
§5.2, p. 36, l. 1575–1577: "a variance which is approximately `O(h^{3/2})`").  For GBM with
`s₀ ≠ 0`, `σ ≠ 0`, `T > 0` and every strike `K ∈ ℝ` there is `C ≥ 0` such that on every level
`ℓ + 1` (`h_{ℓ+1} = T 2^{−(ℓ+1)}`) the conditional-expectation correction `P^f_{ℓ+1} − P^c_ℓ`
(`gbmDigitalCondFine`, `gbmDigitalCondCoarse`) is square integrable,
`E[(P^f_{ℓ+1} − P^c_ℓ)²] ≤ C h_{ℓ+1}^{3/2} (ℓ + 1)^{5/2}` and
`V_{ℓ+1} ≤ C h_{ℓ+1}^{3/2} (ℓ + 1)^{5/2}`: the endpoint `q = 3/2` of the range `q < 3/2` of
`gbm_digital_condExp_variance_rate` (for `K ≠ 0`) up to the logarithmic
factor `(ℓ + 1)^{5/2} = (log(T/h_{ℓ+1})/log 2)^{5/2}`.  `C` depends only on `r`, `σ`, `T`
(`gbm_digital_condExp_variance_endpoint`).

**Deviation.**  The factor `(ℓ + 1)^{5/2}`: the paper's "approximately `O(h^{3/2})`" is not proved
without a logarithm; the factor `25 e^{−rT}` is omitted. -/
theorem gbm_digital_condExp_variance_rate_endpoint (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ K ℓ z) 2 stdNormalSeq ∧
      ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2
        ∂stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ (3 / 2 : ℝ) * ((ℓ : ℝ) + 1) ^ (5 / 2 : ℝ) ∧
      variance (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ K ℓ z) stdNormalSeq ≤
        C * (T / 2 ^ (ℓ + 1)) ^ (3 / 2 : ℝ) * ((ℓ : ℝ) + 1) ^ (5 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := gbm_digital_condExp_variance_endpoint r σ hσ hT
  exact ⟨C, hC, fun ℓ => h s₀ K hs₀ ℓ⟩

/-- **The endpoint with `log(1/h)` in place of `ℓ + 1`** (Giles 2015, §5.2, p. 36, l. 1575–1577: "a
variance which is approximately `O(h^{3/2})`").  For GBM with `σ ≠ 0` and `T > 0` there is `C ≥ 0`,
depending only on `r`, `σ` and `T`, such that for every `s₀ ≠ 0`, every strike `K` and every level
`ℓ + 1` with `h = T 2^{−(ℓ+1)} < e^{−1}` (so that `log(1/h) > 1`): the correction is square
integrable, `E[(P^f_{ℓ+1} − P^c_ℓ)²] ≤ C h^{3/2} (log(1/h))^{5/2}` and
`V_{ℓ+1} ≤ C h^{3/2} (log(1/h))^{5/2}`. Proof: `gbm_digital_condExp_variance_endpoint` and
`(ℓ + 1) log 2 = log T + log(1/h) ≤ (1 + |log T|) log(1/h)`. -/
theorem gbm_digital_condExp_variance_endpoint_log (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ K : ℝ), s₀ ≠ 0 → ∀ ℓ : ℕ, T / 2 ^ (ℓ + 1) < Real.exp (-1) →
      MemLp (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ K ℓ z) 2 stdNormalSeq ∧
      ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2
          ∂stdNormalSeq ≤
        C * (T / 2 ^ (ℓ + 1)) ^ (3 / 2 : ℝ) * Real.log (T / 2 ^ (ℓ + 1))⁻¹ ^ (5 / 2 : ℝ) ∧
      variance (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
          gbmDigitalCondCoarse r σ T s₀ K ℓ z) stdNormalSeq ≤
        C * (T / 2 ^ (ℓ + 1)) ^ (3 / 2 : ℝ) * Real.log (T / 2 ^ (ℓ + 1))⁻¹ ^ (5 / 2 : ℝ) := by
  obtain ⟨C₀, hC₀, hmain⟩ := gbm_digital_condExp_variance_endpoint r σ hσ hT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c := (1 + |Real.log T|) / Real.log 2 with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨C₀ * c ^ (5 / 2 : ℝ), by positivity, fun s₀ K hs₀ ℓ hsmall => ?_⟩
  set h := T / 2 ^ (ℓ + 1) with hh
  have hh0 : 0 < h := by positivity
  have hlog1 : 1 < Real.log h⁻¹ := by
    have h1 : Real.exp 1 < h⁻¹ := by
      rw [Real.exp_neg] at hsmall
      exact (lt_inv_comm₀ hh0 (Real.exp_pos 1)).1 hsmall
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log h⁻¹ := Real.log_lt_log (Real.exp_pos 1) h1
  have hk : ((ℓ : ℝ) + 1) * Real.log 2 = Real.log T + Real.log h⁻¹ := by
    have e : (2 : ℝ) ^ (ℓ + 1) = T * h⁻¹ := by rw [hh]; field_simp
    rw [← Real.log_mul hT.ne' (inv_pos.2 hh0).ne', ← e, Real.log_pow]
    push_cast
    ring
  have hk2 : (ℓ : ℝ) + 1 ≤ c * Real.log h⁻¹ := by
    rw [hc, div_mul_eq_mul_div, le_div_iff₀ hlog2, hk]
    have := le_abs_self (Real.log T)
    nlinarith [abs_nonneg (Real.log T)]
  have hL : ((ℓ : ℝ) + 1) ^ (5 / 2 : ℝ) ≤ c ^ (5 / 2 : ℝ) * Real.log h⁻¹ ^ (5 / 2 : ℝ) := by
    rw [← Real.mul_rpow hc0 (by linarith)]
    exact Real.rpow_le_rpow (by positivity) hk2 (by norm_num)
  have hfin : C₀ * h ^ (3 / 2 : ℝ) * ((ℓ : ℝ) + 1) ^ (5 / 2 : ℝ) ≤
      C₀ * c ^ (5 / 2 : ℝ) * h ^ (3 / 2 : ℝ) * Real.log h⁻¹ ^ (5 / 2 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ C₀ * h ^ (3 / 2 : ℝ))
    calc C₀ * h ^ (3 / 2 : ℝ) * ((ℓ : ℝ) + 1) ^ (5 / 2 : ℝ)
        ≤ C₀ * h ^ (3 / 2 : ℝ) * (c ^ (5 / 2 : ℝ) * Real.log h⁻¹ ^ (5 / 2 : ℝ)) := h1
      _ = _ := by ring
  obtain ⟨hm, h1, h2⟩ := hmain s₀ K hs₀ ℓ
  exact ⟨hm, h1.trans hfin, h2.trans hfin⟩

end MLMC
