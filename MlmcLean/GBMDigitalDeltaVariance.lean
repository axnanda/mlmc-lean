import MlmcLean.GBMSensitivities

/-!
# The variance of the digital-delta corrections for GBM (Giles 2015, §5.4)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.4
"Computing sensitivities", p. 42, l. 1819–1835 of `docs/giles2015.txt`: "Hence, computing first
order sensitivities for a call option has similar difficulties to computing the option price for a
digital option. Sensitivities for digital options can be obtained by first using the conditional
expectation approach described previously, and then applying pathwise sensitivity analysis to
this. Full details on how to formulate appropriate MLMC estimators are given by Burgos and Giles
(2012), and the numerical analysis of the resulting variance is given by Burgos (2014)"
(l. 1828–1835).  The conditional expectation approach is that of §5.2, pp. 35–36, l. 1541–1590
(`MlmcLean.GBMDigitalCondExp`); the pathwise sensitivities of its payoffs, their unbiasedness, (2.4)
and the telescoping sum are in `MlmcLean.GBMSensitivities` (`gbmDigitalCondFineDelta`,
`gbmDigitalCondCoarseDelta`, `gbm_digital_condExp_delta`, `gbm_digital_condExp_delta_telescope`).
This module proves the variance rate of the resulting multilevel corrections (coverage row
G5.4-04), for which the paper gives no rate and refers to Burgos (2014).

**Setting.**  GBM `dS = rS dt + σS dW`, `S_0 = s₀`, Milstein steps and an Euler–Maruyama last fine
step replaced by its conditional expectation (§5.2).  On level `ℓ + 1` (`N = 2^{ℓ+1}` fine steps of
size `h = T 2^{−(ℓ+1)}`), with the fine value `X = Ŝ^f_{N−1}`, the coarse value `Y = Ŝ^c_{N−2}`
(driven by the summed increments) and the re-used half increment `ΔW_{N−2} = √h Z_{N−2}`:
`m_f = X + rXh`, `s_f = |σX|√h`, `m_c = Y W` with `W = 1 + r h_ℓ + σ ΔW_{N−2}`, `s_c = |σY|√h`.
The delta payoffs are `∂P^f_{ℓ+1}/∂s₀ = φ((m_f − K)/s_f) K/(s₀ s_f)` and
`∂P^c_ℓ/∂s₀ = φ((m_c − K)/s_c) K/(s₀ s_c)`, so the correction is
`D = (K/s₀) (G(m_f, s_f) − G(m_c, s_c))` with `G(m, s) = φ((m − K)/s)/s`, the density at `K` of
`N(m, s²)`.

**Heuristic.**  `G(m, s)` is of size `1/s ~ h^{−1/2}` on a window `|m − K| = O(√h)` around the
strike and exponentially small outside it, and its derivatives in `m` and `s` are `O(1/s²) = O(1/h)`
there.  The conditional means and standard deviations match to within `O(h)` (§5.2, l. 1563–1566,
`gbm_digital_cond_moments_match`), so near the strike `D = O(h) O(1/h) = O(1)`, on an event of
probability `O(√h)` (the bounded density of `S_T`): `E[D²] ≈ O(1) O(√h) = O(h^{1/2})`.  (For the
payoff itself the difference is `O(h) O(h^{−1/2})`, whence the `O(h^{3/2})` of §5.2, l. 1575–1577.)
A Monte Carlo check (scratch script, not in the repository; `r = 0.05`, `σ = 0.2`,
`T = s₀ = K = 1`, `10⁵` samples per level, `h = 2^{−1}, …, 2^{−10}`) gives `V/√h ≈ 0.10–0.11` for
`h = 2^{−4}, …, 2^{−10}` and successive slopes `log₂(V(2h)/V(h)) ≈ 0.43–0.51` for
`h = 2^{−5}, …, 2^{−10}`: `V_ℓ ≈ 0.11 h_ℓ^{1/2}`.

**What is proved.**
* `gbm_digital_condExp_delta_variance_rate`: for `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, any strike `K` and
  every `q < 1/2` there is `C ≥ 0` such that, for every `ℓ`, the level-`ℓ + 1` correction
  `D = ∂P^f_{ℓ+1}/∂s₀ − ∂P^c_ℓ/∂s₀` is square integrable, `E[D²] ≤ C h_{ℓ+1}^q` and
  `V[D] ≤ C h_{ℓ+1}^q`.
* `gbm_digital_condExp_delta_corrections_rate`: the same for the corrections
  `fineCoarseDiff (gbmDigitalCondFineDelta …) (gbmDigitalCondCoarseDelta …) ℓ` whose means
  telescope (`gbm_digital_condExp_delta_telescope`): `V_ℓ ≤ C h_ℓ^q` on every level, level `0`
  included (its delta is the same number for every sample).
* The abstract form `condDelta_sq_rate`: for families of fine and coarse values with the `L^{2p}`
  matching of the conditional means and standard deviations, a reference `S` with
  `P(|S − K| ≤ η) ≤ 2ρη` for every `η > 0` (as for a density at most `ρ`), `K ≠ 0`, and
  `E[(S − X)^{2p}] = O(h^p)`, and coarse factors `W` with bounded fourth moments,
  `E[(G(m_f, s_f) − G(m_c, s_c))²] ≤ C h^{1/2 − 8δ}`.

**The proof** (`condDelta_sq_le_indicators`, `condDelta_sq_le_main`).  With `v = h^δ`, the matching
scale `a = h/v`, the Gaussian tail scale `t = 1/v` and the window `ε = √h/v²`:
* outside the events `|m_f − m_c| > a`, `|s_f − s_c| > a` (probability `O(v^{2p})`, Markov's
  inequality and the `L^{2p}` matching) and near the strike, `|X − K| ≤ C₁ε`: both standard
  deviations are at least `c = |σ||K|√h/4`, `φ` is `1`-Lipschitz and the standardised distance of
  the coarse mean is at most `U = O(v^{−2})`, so `|G_f − G_c| ≤ (1 + U) 2a/c² = O(v^{−3})`
  (`abs_pdf_div_sub_pdf_div_le`), on an event of probability `O(ε)` (`gbmExact_smallBall` and the
  `L^{2p}` distance `O(√h)` of `X` from `S_T`);
* away from the strike both standardised distances exceed `t` and
  `G = |u|φ(u)/|m − K| ≤ (p+1)! 2^{p+1} t^{−2p}/(at)` (`pdf_div_le_of_far`);
* on the bad events `|K| G ≤ |m|/s + 1` (`abs_mul_pdf_div_le`) gives `(G_f − G_c)² ≤ (c₀ + c₁W²)/h`
  (`condDelta_sq_le_bad`), unbounded: it is truncated, `W² ≤ M + 2W⁴/M` with `M = h^{−3/2}`,
  and `E[W⁴]` is bounded.
So `E[(G_f − G_c)²] = O(√h/v⁸) = O(h^{1/2 − 8δ})`; `δ = (1/2 − max(q, 0))/8`.

**Deviations.**
* The exponent is every `q < 1/2`, not `1/2` itself; the loss comes from the tails (the `O(h)`
  matching holds in every `L^{2p}`, not on every path), as for the payoff (`q < 3/2`,
  `gbm_digital_condExp_variance_rate`).  The constant depends on `s₀`, `K`, `r`, `σ`, `T` and `q`.
* GBM and the delta only (the paper and Burgos treat general SDEs and Greeks); the factor
  `e^{−rT}` is omitted.  `s₀ ≠ 0`, `σ ≠ 0`, `T > 0` are the hypotheses under which the formulas are
  the pathwise derivatives (`gbm_digital_condExp_delta`); `K = 0` is allowed (both sensitivities
  then vanish identically).
* The rate is an upper bound; that `V_ℓ` is not `o(h^{1/2})` (the numerics above) is not proved.
* The coarse delta inherits the re-used increment `b ΔW_{N−2}` in place of the paper's `b √h_ℓ`
  from `gbmDigitalCondCoarse` (the correction recorded in `MlmcLean.GBMDigitalCondExp`).

**What is not proved.**  The endpoint `q = 1/2`.  Theorem 1 for the digital delta: it needs a weak
rate `|E[∂P^f_L/∂s₀] − d/ds₀ P(S_T > K)| = O(h_L^α)`, i.e. the convergence of the density of the
discretised `S_T` at the strike (the telescoping sum only gives `d/ds₀ P(Ŝ^f_N > K)`,
`gbm_digital_condExp_delta_telescope`); this is not attempted.  Burgos (2014) is not in `docs/` and
was not consulted.  The paper states no rate (l. 1833–1835), so the exponent `1/2` here rests only
on the heuristic and the numerics above and has not been checked against Burgos's analysis.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### The Gaussian density at the strike -/

/-- **The standard normal density is `1`-Lipschitz**: `|φ(x) − φ(y)| ≤ |x − y|`, since
`|φ'(u)| = |u| φ(u) ≤ 1` (the near-strike step of the digital delta, Giles 2015, §5.4, p. 42,
l. 1829–1832). -/
lemma abs_gaussianPDFReal_std_sub_le (x y : ℝ) :
    |gaussianPDFReal 0 1 x - gaussianPDFReal 0 1 y| ≤ |x - y| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := gaussianPDFReal 0 1) (f' := fun u => -u * gaussianPDFReal 0 1 u) (C := 1)
    (fun u _ => (hasDerivAt_gaussianPDFReal_std u).hasDerivWithinAt)
    (fun u _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 u)]
      exact abs_mul_gaussianPDFReal_std_le_one u)
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- **Two Gaussian densities at the strike** (Giles 2015, §5.4, p. 42, l. 1829–1832: "applying
pathwise sensitivity analysis to" the conditional-expectation payoffs, whose derivatives are
`φ((m − K)/s) K/(s₀ s)`; §5.2, p. 36, l. 1563–1566: means and standard deviations "matching … to
within `O(h)`").  For `s₁, s₂ ≥ c > 0` and `|m₂ − K| ≤ U s₂`,
`|φ((m₁ − K)/s₁)/s₁ − φ((m₂ − K)/s₂)/s₂| ≤ (1 + U)(|m₁ − m₂| + |s₁ − s₂|)/c²`: write the difference
as `(φ(u₁) − φ(u₂))/s₁ + φ(u₂)(s₂ − s₁)/(s₁ s₂)`, `|u₁ − u₂| ≤ (|m₁ − m₂| + |u₂||s₁ − s₂|)/s₁`. -/
lemma abs_pdf_div_sub_pdf_div_le {m₁ m₂ s₁ s₂ K c U : ℝ} (hc : 0 < c) (hs₁ : c ≤ s₁)
    (hs₂ : c ≤ s₂) (hU : |m₂ - K| ≤ U * s₂) :
    |gaussianPDFReal 0 1 ((m₁ - K) / s₁) / s₁ - gaussianPDFReal 0 1 ((m₂ - K) / s₂) / s₂| ≤
      (1 + U) * (|m₁ - m₂| + |s₁ - s₂|) / c ^ 2 := by
  have hs₁0 : 0 < s₁ := hc.trans_le hs₁
  have hs₂0 : 0 < s₂ := hc.trans_le hs₂
  have hU0 : 0 ≤ U := by
    by_contra hneg
    have : U * s₂ < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) hs₂0
    linarith [abs_nonneg (m₂ - K)]
  set u₁ := (m₁ - K) / s₁ with hu₁
  set u₂ := (m₂ - K) / s₂ with hu₂
  have hu₂b : |u₂| ≤ U := by
    rw [hu₂, abs_div, abs_of_pos hs₂0, div_le_iff₀ hs₂0]
    exact hU
  have hdiff : u₁ - u₂ = ((m₁ - m₂) + u₂ * (s₂ - s₁)) / s₁ := by
    rw [hu₁, hu₂]
    field_simp
    ring
  have hφ1 := gaussianPDFReal_std_le_one u₂
  have hφ0 := gaussianPDFReal_nonneg 0 1 u₂
  have e : gaussianPDFReal 0 1 u₁ / s₁ - gaussianPDFReal 0 1 u₂ / s₂ =
      (gaussianPDFReal 0 1 u₁ - gaussianPDFReal 0 1 u₂) / s₁ +
        gaussianPDFReal 0 1 u₂ * (s₂ - s₁) / (s₁ * s₂) := by
    field_simp
    ring
  rw [e]
  have h1 : |gaussianPDFReal 0 1 u₁ - gaussianPDFReal 0 1 u₂| * s₁ ≤
      |m₁ - m₂| + U * |s₁ - s₂| := by
    have h2 : |u₁ - u₂| * s₁ ≤ |m₁ - m₂| + U * |s₁ - s₂| := by
      rw [hdiff, abs_div, abs_of_pos hs₁0, div_mul_cancel₀ _ hs₁0.ne']
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_sub_comm s₂ s₁]
      have := mul_le_mul_of_nonneg_right hu₂b (abs_nonneg (s₁ - s₂))
      linarith
    exact (mul_le_mul_of_nonneg_right (abs_gaussianPDFReal_std_sub_le u₁ u₂) hs₁0.le).trans h2
  have hc2 : c ^ 2 ≤ s₁ * s₁ := by nlinarith
  have hc2' : c ^ 2 ≤ s₁ * s₂ := by nlinarith
  have hA : |(gaussianPDFReal 0 1 u₁ - gaussianPDFReal 0 1 u₂) / s₁| ≤
      (|m₁ - m₂| + U * |s₁ - s₂|) / c ^ 2 := by
    rw [abs_div, abs_of_pos hs₁0, div_le_div_iff₀ hs₁0 (by positivity)]
    have h0 : 0 ≤ |gaussianPDFReal 0 1 u₁ - gaussianPDFReal 0 1 u₂| := abs_nonneg _
    nlinarith
  have hB : |gaussianPDFReal 0 1 u₂ * (s₂ - s₁) / (s₁ * s₂)| ≤ |s₁ - s₂| / c ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hφ0, abs_of_pos (mul_pos hs₁0 hs₂0),
      abs_sub_comm s₂ s₁, div_le_div_iff₀ (mul_pos hs₁0 hs₂0) (by positivity)]
    have h0 : 0 ≤ |s₁ - s₂| := abs_nonneg _
    have h3 : gaussianPDFReal 0 1 u₂ * |s₁ - s₂| ≤ |s₁ - s₂| := by nlinarith
    nlinarith
  calc _ ≤ |(gaussianPDFReal 0 1 u₁ - gaussianPDFReal 0 1 u₂) / s₁| +
        |gaussianPDFReal 0 1 u₂ * (s₂ - s₁) / (s₁ * s₂)| := abs_add_le _ _
    _ ≤ (|m₁ - m₂| + U * |s₁ - s₂|) / c ^ 2 + |s₁ - s₂| / c ^ 2 := add_le_add hA hB
    _ ≤ (1 + U) * (|m₁ - m₂| + |s₁ - s₂|) / c ^ 2 := by
        rw [← add_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have := abs_nonneg (m₁ - m₂)
        nlinarith

/-- **The Gaussian tail of `|u| φ(u)`**: for `|u| ≥ t ≥ 1`,
`|u| φ(u) ≤ (n+1)! 2^{n+1}/t^{2n}` (from `e^{u²/2} ≥ (u²/2)^{n+1}/(n+1)!` and `|u| ≤ u²`; away from
the strike the smoothed digital delta of Giles 2015, §5.4, p. 42, l. 1829–1832, is negligible). -/
lemma abs_mul_pdf_le_of_le_abs {u t : ℝ} (ht : 1 ≤ t) (hut : t ≤ |u|) (n : ℕ) :
    |u| * gaussianPDFReal 0 1 u ≤ ((n + 1).factorial * 2 ^ (n + 1) : ℝ) / t ^ (2 * n) := by
  have hu1 : 1 ≤ |u| := ht.trans hut
  have hx1 : 1 ≤ u ^ 2 := by nlinarith [sq_abs u]
  have hux : |u| ≤ u ^ 2 := by nlinarith [sq_abs u]
  have htx : t ^ 2 ≤ u ^ 2 := by
    rw [← sq_abs u]
    exact pow_le_pow_left₀ (by linarith) hut 2
  have hE : 0 < Real.exp (u ^ 2 / 2) := Real.exp_pos _
  have hφ : gaussianPDFReal 0 1 u ≤ (Real.exp (u ^ 2 / 2))⁻¹ := by
    rw [gaussianPDFReal_std, neg_div, Real.exp_neg]
    have h1 : (√(2 * Real.pi))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by nlinarith [Real.two_le_pi]))
    have h2 : 0 < (Real.exp (u ^ 2 / 2))⁻¹ := inv_pos.2 hE
    nlinarith
  have hfac := Real.pow_div_factorial_le_exp (u ^ 2 / 2) (by positivity) (n + 1)
  have hF : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hx0 : 0 < u ^ 2 := by linarith
  have hu0 : u ≠ 0 := fun h0 => by rw [h0] at hx0; norm_num at hx0
  have hinv : (Real.exp (u ^ 2 / 2))⁻¹ ≤ (n + 1).factorial / (u ^ 2 / 2) ^ (n + 1) := by
    rw [inv_le_iff_one_le_mul₀ hE]
    rw [div_le_iff₀ hF] at hfac
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
    linarith
  have hφ0 := gaussianPDFReal_nonneg 0 1 u
  calc |u| * gaussianPDFReal 0 1 u ≤ u ^ 2 * ((n + 1).factorial / (u ^ 2 / 2) ^ (n + 1)) :=
        mul_le_mul hux (hφ.trans hinv) hφ0 (by positivity)
    _ = ((n + 1).factorial * 2 ^ (n + 1) : ℝ) / (u ^ 2) ^ n := by
        rw [div_pow, pow_succ (u ^ 2) n]
        field_simp
    _ ≤ ((n + 1).factorial * 2 ^ (n + 1) : ℝ) / t ^ (2 * n) := by
        rw [pow_mul]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) htx n)

/-- **The smoothed digital delta away from the strike** (Giles 2015, §5.4, p. 42, l. 1829–1832):
for `s > 0`, `t ≥ 1` and `t s ≤ |m − K|`,
`φ((m − K)/s)/s = |u| φ(u)/|m − K| ≤ (n+1)! 2^{n+1}/(t^{2n} |m − K|)` (`u = (m − K)/s`); no lower
bound on `s` is needed. -/
lemma pdf_div_le_of_far {m s K t : ℝ} (hs : 0 < s) (ht : 1 ≤ t) (hts : t * s ≤ |m - K|)
    (n : ℕ) :
    gaussianPDFReal 0 1 ((m - K) / s) / s ≤
      ((n + 1).factorial * 2 ^ (n + 1) : ℝ) / (t ^ (2 * n) * |m - K|) := by
  have hmK : 0 < |m - K| := lt_of_lt_of_le (by positivity) hts
  have hus : |(m - K) / s| = |m - K| / s := by rw [abs_div, abs_of_pos hs]
  have hut : t ≤ |(m - K) / s| := by rw [hus, le_div_iff₀ hs]; exact hts
  have e : gaussianPDFReal 0 1 ((m - K) / s) / s =
      |(m - K) / s| * gaussianPDFReal 0 1 ((m - K) / s) / |m - K| := by
    rw [hus]
    field_simp
  rw [e, ← div_div]
  exact div_le_div_of_nonneg_right (abs_mul_pdf_le_of_le_abs ht hut n) hmK.le

/-- **A crude bound on the smoothed digital delta**: `|K| φ((m − K)/s)/s ≤ |m|/s + 1` for `s > 0`
(`K/s = m/s − u`, `φ ≤ 1`, `|u| φ(u) ≤ 1`; the bound behind the square integrability of the
sensitivities of Giles 2015, §5.4, p. 42, l. 1829–1832, `abs_pdf_mul_div_le`, in the variables
`m`, `s`). -/
lemma abs_mul_pdf_div_le (m K : ℝ) {s : ℝ} (hs : 0 < s) :
    |K| * (gaussianPDFReal 0 1 ((m - K) / s) / s) ≤ |m| / s + 1 := by
  set u := (m - K) / s with hu
  have hK : K / s = m / s - u := by
    rw [hu]
    field_simp
    ring
  have hφ := gaussianPDFReal_nonneg 0 1 u
  calc |K| * (gaussianPDFReal 0 1 u / s) = gaussianPDFReal 0 1 u * |K / s| := by
        rw [abs_div, abs_of_pos hs]
        ring
    _ = gaussianPDFReal 0 1 u * |m / s - u| := by rw [hK]
    _ ≤ gaussianPDFReal 0 1 u * (|m| / s + |u|) := by
        refine mul_le_mul_of_nonneg_left ?_ hφ
        refine (abs_sub _ _).trans ?_
        rw [abs_div, abs_of_pos hs]
    _ = gaussianPDFReal 0 1 u * (|m| / s) + |u| * gaussianPDFReal 0 1 u := by ring
    _ ≤ 1 * (|m| / s) + 1 :=
        add_le_add (mul_le_mul_of_nonneg_right (gaussianPDFReal_std_le_one u) (by positivity))
          (abs_mul_gaussianPDFReal_std_le_one u)
    _ = |m| / s + 1 := by ring

/-! ### The difference of the fine and the coarse smoothed deltas -/

/-- **The digital-delta difference on the bad events** (Giles 2015, §5.4, p. 42, l. 1829–1832).
With `X, Y ≠ 0` the fine and coarse values before the last step, `m_f = X + rXh`, `s_f = |σX|√h`,
`m_c = YW`, `s_c = |σY|√h`, `0 < h ≤ H`:
`(φ((m_f − K)/s_f)/s_f − φ((m_c − K)/s_c)/s_c)² ≤ (c₀ + c₁ W²)/h` with
`c₀ = ((1 + |r|H + |σ|√H)² + 2σ²H)/(K²σ²)`, `c₁ = 2/(K²σ²)`, from
`|K| G_f ≤ |1 + rh|/(|σ|√h) + 1`, `|K| G_c ≤ |W|/(|σ|√h) + 1` (`abs_mul_pdf_div_le`). -/
lemma condDelta_sq_le_bad {X Y W K r σ h H : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0) (hσ : σ ≠ 0)
    (hK : K ≠ 0) (hh : 0 < h) (hhH : h ≤ H) :
    (gaussianPDFReal 0 1 ((X + r * X * h - K) / (|σ * X| * Real.sqrt h)) /
        (|σ * X| * Real.sqrt h) -
      gaussianPDFReal 0 1 ((Y * W - K) / (|σ * Y| * Real.sqrt h)) / (|σ * Y| * Real.sqrt h)) ^ 2 ≤
      (((1 + |r| * H + |σ| * Real.sqrt H) ^ 2 + 2 * σ ^ 2 * H) / (K ^ 2 * σ ^ 2) +
        2 / (K ^ 2 * σ ^ 2) * W ^ 2) / h := by
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have hK' : 0 < |K| := abs_pos.2 hK
  have hH : 0 < H := hh.trans_le hhH
  have hshH : Real.sqrt h ≤ Real.sqrt H := Real.sqrt_le_sqrt hhH
  set d := |σ| * Real.sqrt h with hd
  have hd0 : 0 < d := by positivity
  have hd2 : d ^ 2 = σ ^ 2 * h := by rw [hd, mul_pow, sq_abs, Real.sq_sqrt hh.le]
  have hsf : |σ * X| * Real.sqrt h = |X| * d := by rw [hd, abs_mul]; ring
  have hsc : |σ * Y| * Real.sqrt h = |Y| * d := by rw [hd, abs_mul]; ring
  have hsf0 : 0 < |σ * X| * Real.sqrt h := by rw [hsf]; have := abs_pos.2 hX; positivity
  have hsc0 : 0 < |σ * Y| * Real.sqrt h := by rw [hsc]; have := abs_pos.2 hY; positivity
  set Gf := gaussianPDFReal 0 1 ((X + r * X * h - K) / (|σ * X| * Real.sqrt h)) /
    (|σ * X| * Real.sqrt h) with hGf
  set Gc := gaussianPDFReal 0 1 ((Y * W - K) / (|σ * Y| * Real.sqrt h)) /
    (|σ * Y| * Real.sqrt h) with hGc
  have hGf0 : 0 ≤ Gf := div_nonneg (gaussianPDFReal_nonneg 0 1 _) hsf0.le
  have hGc0 : 0 ≤ Gc := div_nonneg (gaussianPDFReal_nonneg 0 1 _) hsc0.le
  set A := 1 + |r| * H + |σ| * Real.sqrt H with hA
  have hf : |K| * Gf ≤ A / d := by
    refine (abs_mul_pdf_div_le _ K hsf0).trans ?_
    have h1 : |X + r * X * h| / (|σ * X| * Real.sqrt h) ≤ |1 + r * h| / d := by
      rw [hsf, show X + r * X * h = X * (1 + r * h) by ring]
      exact abs_mul_div_abs_mul_le X _ hd0.le
    have h2 : |1 + r * h| ≤ 1 + |r| * H := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_one, abs_mul, abs_of_pos hh]
      have := mul_le_mul_of_nonneg_left hhH (abs_nonneg r)
      linarith
    have h3 : |1 + r * h| / d + 1 ≤ A / d := by
      rw [div_add_one hd0.ne', hA]
      refine div_le_div_of_nonneg_right ?_ hd0.le
      have := mul_le_mul_of_nonneg_left hshH hσ'.le
      rw [hd]
      linarith
    linarith
  have hc : |K| * Gc ≤ (|W| + |σ| * Real.sqrt H) / d := by
    refine (abs_mul_pdf_div_le _ K hsc0).trans ?_
    have h1 : |Y * W| / (|σ * Y| * Real.sqrt h) ≤ |W| / d := by
      rw [hsc]
      exact abs_mul_div_abs_mul_le Y _ hd0.le
    have h3 : |W| / d + 1 ≤ (|W| + |σ| * Real.sqrt H) / d := by
      rw [div_add_one hd0.ne']
      refine div_le_div_of_nonneg_right ?_ hd0.le
      have := mul_le_mul_of_nonneg_left hshH hσ'.le
      rw [hd]
      linarith
    linarith
  have hKf0 : 0 ≤ |K| * Gf := by positivity
  have hKc0 : 0 ≤ |K| * Gc := by positivity
  have hsq : (|W| + |σ| * Real.sqrt H) ^ 2 ≤ 2 * W ^ 2 + 2 * σ ^ 2 * H := by
    have e : (|σ| * Real.sqrt H) ^ 2 = σ ^ 2 * H := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hH.le]
    nlinarith [sq_nonneg (|W| - |σ| * Real.sqrt H), sq_abs W]
  have key : K ^ 2 * (Gf - Gc) ^ 2 ≤ (A ^ 2 + 2 * σ ^ 2 * H + 2 * W ^ 2) / d ^ 2 := by
    have e : K ^ 2 * (Gf - Gc) ^ 2 = (|K| * Gf - |K| * Gc) ^ 2 := by
      rw [← sq_abs K]
      ring
    rw [e]
    have h1 : (|K| * Gf - |K| * Gc) ^ 2 ≤ (|K| * Gf) ^ 2 + (|K| * Gc) ^ 2 := by nlinarith
    have h2 : (|K| * Gf) ^ 2 ≤ (A / d) ^ 2 := pow_le_pow_left₀ hKf0 hf 2
    have h3 : (|K| * Gc) ^ 2 ≤ ((|W| + |σ| * Real.sqrt H) / d) ^ 2 := pow_le_pow_left₀ hKc0 hc 2
    rw [div_pow] at h2 h3
    have h4 : (|W| + |σ| * Real.sqrt H) ^ 2 / d ^ 2 ≤ (2 * W ^ 2 + 2 * σ ^ 2 * H) / d ^ 2 :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have e2 : (A ^ 2 + 2 * σ ^ 2 * H + 2 * W ^ 2) / d ^ 2 =
        A ^ 2 / d ^ 2 + (2 * W ^ 2 + 2 * σ ^ 2 * H) / d ^ 2 := by ring
    linarith
  have hK2 : 0 < K ^ 2 := by positivity
  have e : ((A ^ 2 + 2 * σ ^ 2 * H) / (K ^ 2 * σ ^ 2) + 2 / (K ^ 2 * σ ^ 2) * W ^ 2) / h =
      (A ^ 2 + 2 * σ ^ 2 * H + 2 * W ^ 2) / d ^ 2 / K ^ 2 := by
    rw [hd2]
    have : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
    field_simp
  rw [e, le_div_iff₀ hK2, mul_comm]
  exact key

/-- **The pointwise bound of the variance estimate for the digital delta** (Giles 2015, §5.4,
p. 42, l. 1829–1832; the matching of §5.2, p. 36, l. 1563–1566).  In the setting of
`condDelta_sq_le_bad`, with a matching scale `a > 0`, a tail scale `t ≥ 1`, `M > 0`, a window
`R' ≤ |K|/2` containing the window `2(a(1 + t) + |K|η)` of `abs_condDigital_sub_le`
(`η = t|σ|√h + |r|h ≤ 1/2`), `a ≤ c = |σ||K|√h/4`, `N` bounding the near-strike coefficient and
`Fa` the far one:
`(G_f − G_c)² ≤ ((c₀ + c₁M)/h)(1_{|m_f − m_c| > a} + 1_{|s_f − s_c| > a}) + (2c₁/(Mh)) W⁴ +
N² 1_{|X − K| ≤ R'} + Fa²`.
Bad events: `condDelta_sq_le_bad` and `W² ≤ M + 2W⁴/M`.  Near the strike: `s_f ≥ 2c`, `s_c ≥ c`,
`|m_c − K| ≤ U s_c` (`abs_pdf_div_sub_pdf_div_le`).  Away from it: `|m_f − K| > a(1 + t) + t s_f`,
so both standardised distances exceed `t` and both distances to `K` exceed `at`
(`pdf_div_le_of_far`). -/
lemma condDelta_sq_le_indicators {X Y W K r σ h H a t R' M N Fa : ℝ} (hX : X ≠ 0)
    (hY : Y ≠ 0) (hσ : σ ≠ 0) (hK : K ≠ 0) (hh : 0 < h) (hhH : h ≤ H) (ha : 0 < a)
    (ht : 1 ≤ t) (hM : 0 < M) (hη : t * |σ| * Real.sqrt h + |r| * h ≤ 1 / 2)
    (hR : 2 * (a * (1 + t) + |K| * (t * |σ| * Real.sqrt h + |r| * h)) ≤ R')
    (hR' : R' ≤ |K| / 2) (has : a ≤ |σ| * |K| * Real.sqrt h / 4)
    (hN : (1 + (R' + 2 * |r| * |K| * h + a) / (|σ| * |K| * Real.sqrt h / 4)) * (2 * a) /
      (|σ| * |K| * Real.sqrt h / 4) ^ 2 ≤ N) {n : ℕ}
    (hFa : ((n + 1).factorial * 2 ^ (n + 1) : ℝ) / (t ^ (2 * n) * (a * t)) ≤ Fa) :
    (gaussianPDFReal 0 1 ((X + r * X * h - K) / (|σ * X| * Real.sqrt h)) /
        (|σ * X| * Real.sqrt h) -
      gaussianPDFReal 0 1 ((Y * W - K) / (|σ * Y| * Real.sqrt h)) / (|σ * Y| * Real.sqrt h)) ^ 2 ≤
      (((1 + |r| * H + |σ| * Real.sqrt H) ^ 2 + 2 * σ ^ 2 * H) / (K ^ 2 * σ ^ 2) +
          2 / (K ^ 2 * σ ^ 2) * M) / h *
        ({x : ℝ | a < |x|}.indicator 1 (X + r * X * h - Y * W) +
          {x : ℝ | a < |x|}.indicator 1 (|σ * X| * Real.sqrt h - |σ * Y| * Real.sqrt h)) +
        2 * (2 / (K ^ 2 * σ ^ 2)) / (M * h) * W ^ 4 +
        N ^ 2 * {x : ℝ | |x - K| ≤ R'}.indicator 1 X + Fa ^ 2 := by
  have hbad := condDelta_sq_le_bad (W := W) (r := r) hX hY hσ hK hh hhH
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have hK' : 0 < |K| := abs_pos.2 hK
  have hX' : 0 < |X| := abs_pos.2 hX
  have hY' : 0 < |Y| := abs_pos.2 hY
  have hH : 0 < H := hh.trans_le hhH
  set c₀ := ((1 + |r| * H + |σ| * Real.sqrt H) ^ 2 + 2 * σ ^ 2 * H) / (K ^ 2 * σ ^ 2) with hc₀
  set c₁ := 2 / (K ^ 2 * σ ^ 2) with hc₁
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  set I₁ := {x : ℝ | a < |x|}.indicator (1 : ℝ → ℝ) (X + r * X * h - Y * W) with hI₁
  set I₂ := {x : ℝ | a < |x|}.indicator (1 : ℝ → ℝ)
    (|σ * X| * Real.sqrt h - |σ * Y| * Real.sqrt h) with hI₂
  set I₃ := {x : ℝ | |x - K| ≤ R'}.indicator (1 : ℝ → ℝ) X with hI₃
  have hI₁0 : 0 ≤ I₁ := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hI₂0 : 0 ≤ I₂ := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hI₃0 : 0 ≤ I₃ := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hW4 : 0 ≤ 2 * c₁ / (M * h) * W ^ 4 := by
    have : 0 ≤ W ^ 4 := by positivity
    positivity
  have hN2 : 0 ≤ N ^ 2 * I₃ := mul_nonneg (sq_nonneg _) hI₃0
  have hFa2 : 0 ≤ Fa ^ 2 := sq_nonneg _
  have hB0 : 0 ≤ (c₀ + c₁ * M) / h := by positivity
  -- truncation of the unbounded coarse factor
  have htrunc : (c₀ + c₁ * W ^ 2) / h ≤ (c₀ + c₁ * M) / h + 2 * c₁ / (M * h) * W ^ 4 := by
    have h1 : W ^ 2 ≤ M + 2 * (W ^ 4 / M) := by
      by_cases hWM : W ^ 2 ≤ M
      · have : 0 ≤ W ^ 4 / M := by positivity
        linarith
      · have h2 : M < W ^ 2 := not_le.1 hWM
        have h3 : W ^ 2 ≤ W ^ 4 / M := by
          rw [le_div_iff₀ hM]
          have : W ^ 4 = W ^ 2 * W ^ 2 := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left h2.le (sq_nonneg W)
        have h4 : 0 ≤ W ^ 4 / M := by positivity
        linarith
    have e : (c₀ + c₁ * M) / h + 2 * c₁ / (M * h) * W ^ 4 =
        (c₀ + c₁ * (M + 2 * (W ^ 4 / M))) / h := by
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right (by nlinarith) hh.le
  set sh := Real.sqrt h with hshdef
  set sf := |σ * X| * sh with hsf
  set sc := |σ * Y| * sh with hsc
  set mf := X + r * X * h with hmf
  set mc := Y * W with hmc
  set Gf := gaussianPDFReal 0 1 ((mf - K) / sf) / sf with hGf
  set Gc := gaussianPDFReal 0 1 ((mc - K) / sc) / sc with hGc
  have hsf0 : 0 < sf := by rw [hsf]; have := abs_pos.2 (mul_ne_zero hσ hX); positivity
  have hsc0 : 0 < sc := by rw [hsc]; have := abs_pos.2 (mul_ne_zero hσ hY); positivity
  have hGf0 : 0 ≤ Gf := div_nonneg (gaussianPDFReal_nonneg 0 1 _) hsf0.le
  have hGc0 : 0 ≤ Gc := div_nonneg (gaussianPDFReal_nonneg 0 1 _) hsc0.le
  by_cases b1 : a < |mf - mc|
  · have e1 : I₁ = 1 := by
      rw [hI₁, Set.indicator_of_mem (show mf - mc ∈ {x : ℝ | a < |x|} from b1), Pi.one_apply]
    rw [e1]
    have : (c₀ + c₁ * M) / h * 1 ≤ (c₀ + c₁ * M) / h * (1 + I₂) :=
      mul_le_mul_of_nonneg_left (by linarith) hB0
    linarith only [hbad, htrunc, this, hW4, hN2, hFa2]
  by_cases b2 : a < |sf - sc|
  · have e2 : I₂ = 1 := by
      rw [hI₂, Set.indicator_of_mem (show sf - sc ∈ {x : ℝ | a < |x|} from b2), Pi.one_apply]
    rw [e2]
    have : (c₀ + c₁ * M) / h * 1 ≤ (c₀ + c₁ * M) / h * (I₁ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hB0
    linarith only [hbad, htrunc, this, hW4, hN2, hFa2]
  have hΔm : |mf - mc| ≤ a := not_lt.1 b1
  have hΔs : |sf - sc| ≤ a := not_lt.1 b2
  have hrest : 0 ≤ (c₀ + c₁ * M) / h * (I₁ + I₂) := mul_nonneg hB0 (add_nonneg hI₁0 hI₂0)
  set η := t * |σ| * sh + |r| * h with hηdef
  have hη0 : 0 ≤ η := by positivity
  by_cases hnear : |X - K| ≤ R'
  · -- near the strike: both standard deviations are of order `√h`
    have e3 : I₃ = 1 := by
      rw [hI₃, Set.indicator_of_mem (show X ∈ {x : ℝ | |x - K| ≤ R'} from hnear), Pi.one_apply]
    rw [e3, mul_one]
    set c := |σ| * |K| * sh / 4 with hcdef
    have hc0 : 0 < c := by positivity
    have hXge : |K| ≤ 2 * |X| := by
      have := abs_sub_abs_le_abs_sub K X
      rw [abs_sub_comm] at this
      linarith
    have hXle : |X| ≤ 3 * |K| / 2 := by
      have := abs_sub_abs_le_abs_sub X K
      linarith
    have hsf2 : 2 * c ≤ sf := by
      rw [hsf, hcdef, abs_mul]
      have := mul_le_mul_of_nonneg_left hXge (by positivity : (0 : ℝ) ≤ |σ| * sh)
      linarith
    have hsc1 : c ≤ sc := by
      have := le_abs_self (sf - sc)
      linarith
    have hsf1 : c ≤ sf := by linarith
    have hmfK : |mf - K| ≤ R' + 2 * |r| * |K| * h := by
      rw [hmf, show X + r * X * h - K = (X - K) + r * X * h by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hh]
      have h1 : |r| * |X| * h ≤ |r| * (3 * |K| / 2) * h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXle (abs_nonneg r)) hh.le
      have h0 : 0 ≤ |r| * |K| * h := by positivity
      linarith
    set U := (R' + 2 * |r| * |K| * h + a) / c with hUdef
    have hU0 : 0 ≤ U := by
      rw [hUdef]
      have : 0 ≤ R' := (abs_nonneg _).trans hnear
      positivity
    have hmcK : |mc - K| ≤ U * sc := by
      have h1 : |mc - K| ≤ |mf - K| + |mf - mc| := by
        have := abs_sub_le (mc) (mf) K
        rw [abs_sub_comm mc mf] at this
        linarith
      have h2 : U * c = R' + 2 * |r| * |K| * h + a := by
        rw [hUdef]
        field_simp
      have h3 : U * c ≤ U * sc := mul_le_mul_of_nonneg_left hsc1 hU0
      linarith
    have hL := abs_pdf_div_sub_pdf_div_le (m₁ := mf) (K := K) hc0 hsf1 hsc1 hmcK
    have hL2 : |Gf - Gc| ≤ N := by
      refine hL.trans (le_trans ?_ hN)
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hsq : (Gf - Gc) ^ 2 ≤ N ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hL2 2
    linarith only [hsq, hrest, hW4, hFa2]
  · -- away from the strike: both deltas are in the far Gaussian tail
    have e3 : I₃ = 0 := by
      rw [hI₃, Set.indicator_of_notMem (show X ∉ {x : ℝ | |x - K| ≤ R'} from hnear)]
    rw [e3, mul_zero]
    have hlt : 2 * (a * (1 + t) + |K| * η) < |X - K| := lt_of_le_of_lt hR (not_le.1 hnear)
    have h1 : |X| ≤ |X - K| + |K| := by
      have := abs_sub_abs_le_abs_sub X K
      linarith
    have h2 : |X - K| - |r| * h * |X| ≤ |mf - K| := by
      have := abs_sub_abs_le_abs_sub (X - K) (-(r * X * h))
      rw [abs_neg, sub_neg_eq_add, show X - K + r * X * h = mf - K by rw [hmf]; ring, abs_mul,
        abs_mul, abs_of_pos hh] at this
      linarith
    have h3 : t * sf + |r| * h * |X| = η * |X| := by
      rw [hsf, abs_mul, hηdef]
      ring
    have h4 : η * |X| ≤ η * (|X - K| + |K|) := mul_le_mul_of_nonneg_left h1 hη0
    have hat1 : 0 ≤ a * (1 + t) := by positivity
    have hts : 0 ≤ t * sf := by positivity
    have h5 : η * |X - K| ≤ |X - K| / 2 := by
      have := mul_le_mul_of_nonneg_right hη (abs_nonneg (X - K))
      linarith
    have hfar : a * (1 + t) + t * sf < |mf - K| := by linarith
    have hat : 0 < a * t := by positivity
    have hcf : 0 ≤ ((n + 1).factorial * 2 ^ (n + 1) : ℝ) := by positivity
    have hfar_f : t * sf ≤ |mf - K| := by linarith
    have hfar_c : t * sc ≤ |mc - K| := by
      have h6 : |mf - K| ≤ |mc - K| + |mf - mc| := by
        have := abs_sub_le mf mc K
        linarith
      have h7 : sc ≤ sf + a := by
        have := le_abs_self (sc - sf)
        rw [abs_sub_comm] at this
        linarith
      have h8 := mul_le_mul_of_nonneg_left h7 (by linarith : (0 : ℝ) ≤ t)
      linarith
    have hmf_at : a * t ≤ |mf - K| := by linarith
    have hmc_at : a * t ≤ |mc - K| := by
      have h6 : |mf - K| ≤ |mc - K| + |mf - mc| := by
        have := abs_sub_le mf mc K
        linarith
      linarith
    have hBf : Gf ≤ Fa := by
      refine (pdf_div_le_of_far hsf0 ht hfar_f n).trans (le_trans ?_ hFa)
      exact div_le_div_of_nonneg_left hcf (by positivity)
        (mul_le_mul_of_nonneg_left hmf_at (by positivity))
    have hBc : Gc ≤ Fa := by
      refine (pdf_div_le_of_far hsc0 ht hfar_c n).trans (le_trans ?_ hFa)
      exact div_le_div_of_nonneg_left hcf (by positivity)
        (mul_le_mul_of_nonneg_left hmc_at (by positivity))
    have hsq : (Gf - Gc) ^ 2 ≤ Fa ^ 2 := by
      rw [← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [abs_le]
      constructor <;> linarith
    refine hsq.trans (le_add_of_nonneg_left ?_)
    rw [add_zero]
    exact add_nonneg hrest hW4

/-! ### The second moment of the difference -/

/-- **The scales of the variance estimate for the digital delta** (Giles 2015, §5.4, p. 42; the
scales of `condDigital_scales`, §5.2, p. 36): with `v ∈ (0, 1]`, `0 < h ≤ 1`,
`ε = √h/v² ≤ |σ||K|/4`, `a = h/v`, `t = 1/v`: `a ≤ |σ||K|√h/4`; the near-strike coefficient with
the window `C₁ε` is at most `N₀/v³`, `N₀ = 32(1 + 4(C₁ + 2|r||K| + 1)/(|σ||K|))/(|σ||K|)²`; and
the far coefficient is `(p+1)! 2^{p+1} v^{2p+2}/h`. -/
lemma condDelta_scales {σ r K h v ε C₁ : ℝ} (hσ : σ ≠ 0) (hK : K ≠ 0) (hh : 0 < h)
    (hh1 : h ≤ 1) (hv0 : 0 < v) (hv1 : v ≤ 1) (hε : ε = Real.sqrt h / v ^ 2) (hC₁ : 0 ≤ C₁)
    (hεc : ε ≤ |σ| * |K| / 4) (p : ℕ) :
    h / v ≤ |σ| * |K| * Real.sqrt h / 4 ∧
    (1 + (C₁ * ε + 2 * |r| * |K| * h + h / v) / (|σ| * |K| * Real.sqrt h / 4)) * (2 * (h / v)) /
        (|σ| * |K| * Real.sqrt h / 4) ^ 2 ≤
      32 * (1 + 4 * (C₁ + 2 * |r| * |K| + 1) / (|σ| * |K|)) / (|σ| * |K|) ^ 2 / v ^ 3 ∧
    ((p + 1).factorial * 2 ^ (p + 1) : ℝ) / ((1 / v) ^ (2 * p) * (h / v * (1 / v))) =
      (p + 1).factorial * 2 ^ (p + 1) * v ^ (2 * p + 2) / h := by
  obtain ⟨sh, hshdef⟩ : ∃ sh, sh = Real.sqrt h := ⟨_, rfl⟩
  rw [← hshdef] at hε ⊢
  have hsh0 : 0 < sh := hshdef ▸ Real.sqrt_pos.2 hh
  have hsh1 : sh ≤ 1 := hshdef ▸ Real.sqrt_le_one.2 hh1
  have hshsq : sh * sh = h := hshdef ▸ Real.mul_self_sqrt hh.le
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have hK' : 0 < |K| := abs_pos.2 hK
  set s := |σ| * |K| with hsdef
  have hs0 : 0 < s := by positivity
  have hv2 : v ^ 2 ≤ 1 := pow_le_one₀ hv0.le hv1
  have hv2v : v ^ 2 ≤ v := by nlinarith
  have hhsh : h ≤ sh := by rw [← hshsq]; nlinarith
  have hsh_v2 : sh ≤ sh / v ^ 2 := le_div_self hsh0.le (by positivity) hv2
  have hhv : h / v ≤ sh / v ^ 2 := by
    rw [div_le_div_iff₀ hv0 (by positivity)]
    have : h * v ^ 2 ≤ h * v := mul_le_mul_of_nonneg_left hv2v hh.le
    nlinarith
  have hshv : sh / v ≤ ε := by
    rw [hε]
    exact div_le_div_of_nonneg_left hsh0.le (by positivity) hv2v
  refine ⟨?_, ?_, ?_⟩
  · have e : h / v = sh * (sh / v) := by rw [← hshsq]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (hshv.trans hεc) hsh0.le
    linarith
  · set C₄ := 4 * (C₁ + 2 * |r| * |K| + 1) / s with hC₄
    have hC₄0 : 0 ≤ C₄ := by rw [hC₄]; positivity
    have hD : C₁ * ε + 2 * |r| * |K| * h + h / v ≤ (C₁ + 2 * |r| * |K| + 1) * (sh / v ^ 2) := by
      have h1 : 2 * |r| * |K| * h ≤ 2 * |r| * |K| * (sh / v ^ 2) :=
        mul_le_mul_of_nonneg_left (hhsh.trans hsh_v2) (by positivity)
      rw [hε]
      nlinarith
    have hU : (C₁ * ε + 2 * |r| * |K| * h + h / v) / (s * sh / 4) ≤ C₄ / v ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      calc C₁ * ε + 2 * |r| * |K| * h + h / v ≤ (C₁ + 2 * |r| * |K| + 1) * (sh / v ^ 2) := hD
        _ = C₄ / v ^ 2 * (s * sh / 4) := by
          rw [hC₄]
          field_simp
    have h2a : 2 * (h / v) / (s * sh / 4) ^ 2 = 32 / s ^ 2 / v := by
      rw [← hshsq]
      field_simp
      ring
    have h1U : 1 + C₄ / v ^ 2 ≤ (1 + C₄) / v ^ 2 := by
      rw [add_div]
      have : 1 ≤ 1 / v ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    calc (1 + (C₁ * ε + 2 * |r| * |K| * h + h / v) / (s * sh / 4)) * (2 * (h / v)) /
          (s * sh / 4) ^ 2
        = (1 + (C₁ * ε + 2 * |r| * |K| * h + h / v) / (s * sh / 4)) *
            (2 * (h / v) / (s * sh / 4) ^ 2) := by ring
      _ ≤ (1 + C₄) / v ^ 2 * (32 / s ^ 2 / v) := by
          rw [h2a]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 32 * (1 + C₄) / s ^ 2 / v ^ 3 := by
          field_simp
  · rw [one_div_pow, pow_succ v (2 * p + 1), pow_succ v (2 * p)]
    field_simp

/-- **The squared digital-delta difference is integrable, with mean `O(1/h)`** (Giles 2015, §5.4,
p. 42, l. 1829–1832): if `X, Y ≠ 0` a.s., `0 < h ≤ H` and `E[W⁴] ≤ C_W`, then
`E[(G_f − G_c)²] ≤ (c₀ + c₁(1 + C_W))/h` (`condDelta_sq_le_bad`, `W² ≤ 1 + W⁴`). -/
lemma integrable_integral_condDelta_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {r σ K h H CW : ℝ} (hσ : σ ≠ 0) (hK : K ≠ 0) (hh : 0 < h)
    (hhH : h ≤ H) {X Y W : Ω → ℝ} (hXm : Measurable X) (hYm : Measurable Y)
    (hWm : Measurable W) (hX0 : ∀ᵐ ω ∂μ, X ω ≠ 0) (hY0 : ∀ᵐ ω ∂μ, Y ω ≠ 0)
    (hWi : Integrable (fun ω => W ω ^ 4) μ) (hWb : ∫ ω, W ω ^ 4 ∂μ ≤ CW) :
    Integrable (fun ω => (gaussianPDFReal 0 1 ((X ω + r * X ω * h - K) /
        (|σ * X ω| * Real.sqrt h)) / (|σ * X ω| * Real.sqrt h) -
      gaussianPDFReal 0 1 ((Y ω * W ω - K) / (|σ * Y ω| * Real.sqrt h)) /
        (|σ * Y ω| * Real.sqrt h)) ^ 2) μ ∧
    ∫ ω, (gaussianPDFReal 0 1 ((X ω + r * X ω * h - K) / (|σ * X ω| * Real.sqrt h)) /
        (|σ * X ω| * Real.sqrt h) -
      gaussianPDFReal 0 1 ((Y ω * W ω - K) / (|σ * Y ω| * Real.sqrt h)) /
        (|σ * Y ω| * Real.sqrt h)) ^ 2 ∂μ ≤
      (((1 + |r| * H + |σ| * Real.sqrt H) ^ 2 + 2 * σ ^ 2 * H) / (K ^ 2 * σ ^ 2) +
        2 / (K ^ 2 * σ ^ 2) * (1 + CW)) / h := by
  set c₀ := ((1 + |r| * H + |σ| * Real.sqrt H) ^ 2 + 2 * σ ^ 2 * H) / (K ^ 2 * σ ^ 2) with hc₀
  set c₁ := 2 / (K ^ 2 * σ ^ 2) with hc₁
  have hH : 0 < H := hh.trans_le hhH
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  have hφm : Measurable (gaussianPDFReal 0 1) := measurable_gaussianPDFReal 0 1
  have hFm : Measurable fun ω => (gaussianPDFReal 0 1 ((X ω + r * X ω * h - K) /
        (|σ * X ω| * Real.sqrt h)) / (|σ * X ω| * Real.sqrt h) -
      gaussianPDFReal 0 1 ((Y ω * W ω - K) / (|σ * Y ω| * Real.sqrt h)) /
        (|σ * Y ω| * Real.sqrt h)) ^ 2 :=
    (((hφm.comp (by fun_prop)).div (by fun_prop)).sub
      ((hφm.comp (by fun_prop)).div (by fun_prop))).pow_const 2
  have hW2le : ∀ ω, W ω ^ 2 ≤ 1 + W ω ^ 4 := fun ω => by nlinarith [sq_nonneg (W ω ^ 2 - 1)]
  have hW2i : Integrable (fun ω => W ω ^ 2) μ := by
    refine ((integrable_const 1).add hWi).mono' (hWm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hW2le ω
  have hW2b : ∫ ω, W ω ^ 2 ∂μ ≤ 1 + CW := by
    calc ∫ ω, W ω ^ 2 ∂μ ≤ ∫ ω, (1 + W ω ^ 4) ∂μ :=
          integral_mono hW2i ((integrable_const 1).add hWi) hW2le
      _ = 1 + ∫ ω, W ω ^ 4 ∂μ := by
          rw [integral_add (integrable_const 1) hWi, integral_const, probReal_univ, one_smul]
      _ ≤ 1 + CW := by linarith
  have hBi : Integrable (fun ω => (c₀ + c₁ * W ω ^ 2) / h) μ :=
    ((integrable_const c₀).add (hW2i.const_mul c₁)).div_const h
  have hpt : ∀ᵐ ω ∂μ, (gaussianPDFReal 0 1 ((X ω + r * X ω * h - K) /
        (|σ * X ω| * Real.sqrt h)) / (|σ * X ω| * Real.sqrt h) -
      gaussianPDFReal 0 1 ((Y ω * W ω - K) / (|σ * Y ω| * Real.sqrt h)) /
        (|σ * Y ω| * Real.sqrt h)) ^ 2 ≤ (c₀ + c₁ * W ω ^ 2) / h := by
    filter_upwards [hX0, hY0] with ω hXω hYω
    exact condDelta_sq_le_bad hXω hYω hσ hK hh hhH
  have hint : Integrable (fun ω => (gaussianPDFReal 0 1 ((X ω + r * X ω * h - K) /
        (|σ * X ω| * Real.sqrt h)) / (|σ * X ω| * Real.sqrt h) -
      gaussianPDFReal 0 1 ((Y ω * W ω - K) / (|σ * Y ω| * Real.sqrt h)) /
        (|σ * Y ω| * Real.sqrt h)) ^ 2) μ := by
    refine hBi.mono' hFm.aestronglyMeasurable ?_
    filter_upwards [hpt] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  refine ⟨hint, (integral_mono_ae hint hBi hpt).trans ?_⟩
  rw [integral_div, integral_add (integrable_const c₀) (hW2i.const_mul c₁), integral_const,
    probReal_univ, one_smul, integral_const_mul]
  refine div_le_div_of_nonneg_right ?_ hh.le
  have := mul_le_mul_of_nonneg_left hW2b hc₁0.le
  linarith

/-- **The variance estimate for the digital delta on one level, for small steps** (Giles 2015,
§5.4, p. 42, l. 1829–1835; the matching of §5.2, p. 36, l. 1563–1566).  With `v = h^δ`,
`ε = √h/v² ≤ ε₀`, `2pδ ≥ 3`, the `L^{2p}` matching `E[(m_f − m_c)^{2p}] ≤ C_m h^{2p}`,
`E[(s_f − s_c)^{2p}] ≤ C_s h^{2p}`, `E[(S − X)^{2p}] ≤ C_X h^p`, `P(|S − K| ≤ η) ≤ 2ρη` and
`E[W⁴] ≤ C_W`:
`E[(G_f − G_c)²] ≤ ((C_m + C_s)(c₀ + c₁) + 2c₁C_W + N₀²(4ρC₁ + C_X/C₁^{2p}) + c_p²) √h/v⁸`
(`condDelta_sq_le_indicators` with `a = h/v`, `t = 1/v`, `R' = C₁ε`, `M = h^{−3/2}`; Markov's
inequality for the bad events, `P(|X − K| ≤ C₁ε) ≤ 4ρC₁ε + C_X v^{4p}/C₁^{2p}` and
`v^{2p} ≤ h³`). -/
lemma condDelta_sq_le_main {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {r σ K ρ δ h v ε H C₁ Cm Cs CX CW c₀ c₁ N₀ cp : ℝ} {p : ℕ}
    (hσ : σ ≠ 0) (hK : K ≠ 0) (hpδ : 3 ≤ 2 * p * δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hhH : h ≤ H) (hδ0 : 0 ≤ δ) (hv : v = h ^ δ)
    (hε : ε = Real.sqrt h / v ^ 2) (hC₁ : C₁ = 2 * (2 + |K| * (|σ| + |r|)))
    (hεa : ε ≤ 1 / (2 * (|σ| + |r| + 1))) (hεb : ε ≤ |K| / (2 * C₁))
    (hεc : ε ≤ |σ| * |K| / 4)
    (hc₀ : c₀ = ((1 + |r| * H + |σ| * Real.sqrt H) ^ 2 + 2 * σ ^ 2 * H) / (K ^ 2 * σ ^ 2))
    (hc₁ : c₁ = 2 / (K ^ 2 * σ ^ 2))
    (hN₀ : N₀ = 32 * (1 + 4 * (C₁ + 2 * |r| * |K| + 1) / (|σ| * |K|)) / (|σ| * |K|) ^ 2)
    (hcp : cp = (p + 1).factorial * 2 ^ (p + 1))
    {X Y W ST : Ω → ℝ} (hXm : Measurable X) (hYm : Measurable Y) (hWm : Measurable W)
    (hX0 : ∀ᵐ ω ∂μ, X ω ≠ 0) (hY0 : ∀ᵐ ω ∂μ, Y ω ≠ 0)
    (hball : ∀ η, 0 < η → μ.real {ω | |ST ω - K| ≤ η} ≤ 2 * ρ * η)
    (hmi : Integrable (fun ω => (X ω + r * X ω * h - Y ω * W ω) ^ (2 * p)) μ)
    (hmb : ∫ ω, (X ω + r * X ω * h - Y ω * W ω) ^ (2 * p) ∂μ ≤ Cm * h ^ (2 * p))
    (hsi : Integrable (fun ω => (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) ^ (2 * p))
      μ)
    (hsb : ∫ ω, (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) ^ (2 * p) ∂μ ≤
      Cs * h ^ (2 * p))
    (hxi : Integrable (fun ω => (ST ω - X ω) ^ (2 * p)) μ)
    (hxb : ∫ ω, (ST ω - X ω) ^ (2 * p) ∂μ ≤ CX * h ^ p)
    (hWi : Integrable (fun ω => W ω ^ 4) μ) (hWb : ∫ ω, W ω ^ 4 ∂μ ≤ CW)
    (hCm : 0 ≤ Cm) (hCs : 0 ≤ Cs) (hCX : 0 ≤ CX) (hCW : 0 ≤ CW) :
    ∫ ω, (gaussianPDFReal 0 1 ((X ω + r * X ω * h - K) / (|σ * X ω| * Real.sqrt h)) /
        (|σ * X ω| * Real.sqrt h) -
      gaussianPDFReal 0 1 ((Y ω * W ω - K) / (|σ * Y ω| * Real.sqrt h)) /
        (|σ * Y ω| * Real.sqrt h)) ^ 2 ∂μ ≤
      ((Cm + Cs) * (c₀ + c₁) + 2 * c₁ * CW + N₀ ^ 2 * (4 * ρ * C₁ + CX / C₁ ^ (2 * p)) +
        cp ^ 2) * (Real.sqrt h / v ^ 8) := by
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have hK' : 0 < |K| := abs_pos.2 hK
  have hH : 0 < H := hh.trans_le hhH
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hcp0 : 0 ≤ cp := by rw [hcp]; positivity
  have hv0 : 0 < v := by rw [hv]; exact Real.rpow_pos_of_pos hh δ
  have hv1 : v ≤ 1 := by rw [hv]; exact Real.rpow_le_one hh.le hh1 hδ0
  obtain ⟨sh, hshdef⟩ : ∃ sh, sh = Real.sqrt h := ⟨_, rfl⟩
  have hsh0 : 0 < sh := hshdef ▸ Real.sqrt_pos.2 hh
  have hsh1 : sh ≤ 1 := hshdef ▸ Real.sqrt_le_one.2 hh1
  have hshsq : sh * sh = h := hshdef ▸ Real.mul_self_sqrt hh.le
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨hη, -, hRε, -⟩ := condDigital_scales (r := r) hσ hK hh hh1 hv0 hv1 hε hεa
    (by rw [← hC₁]; exact hεb)
  rw [← hC₁] at hRε
  obtain ⟨has, hN, hFa⟩ := condDelta_scales (r := r) hσ hK hh hh1 hv0 hv1 hε hC₁0.le hεc p
  rw [← hN₀] at hN
  have hR' : C₁ * ε ≤ |K| / 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C₁)] at hεb
    linarith
  have ha0 : 0 < h / v := by positivity
  have ht1 : 1 ≤ 1 / v := by rw [le_div_iff₀ hv0]; linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 / (h * sh) := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  obtain ⟨Fa, hFadef⟩ : ∃ Fa : ℝ, Fa = (p + 1).factorial * 2 ^ (p + 1) * v ^ (2 * p + 2) / h :=
    ⟨_, rfl⟩
  rw [← hFadef] at hFa
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂μ, (gaussianPDFReal 0 1 ((X ω + r * X ω * h - K) /
        (|σ * X ω| * Real.sqrt h)) / (|σ * X ω| * Real.sqrt h) -
      gaussianPDFReal 0 1 ((Y ω * W ω - K) / (|σ * Y ω| * Real.sqrt h)) /
        (|σ * Y ω| * Real.sqrt h)) ^ 2 ≤
      (c₀ + c₁ * M) / h * ({x : ℝ | h / v < |x|}.indicator 1 (X ω + r * X ω * h - Y ω * W ω) +
          {x : ℝ | h / v < |x|}.indicator 1 (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h)) +
        2 * c₁ / (M * h) * W ω ^ 4 +
        (N₀ / v ^ 3) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 (X ω) + Fa ^ 2 := by
    filter_upwards [hX0, hY0] with ω hXω hYω
    have h1 := condDelta_sq_le_indicators (W := W ω) (r := r) (M := M) hXω hYω hσ hK hh hhH ha0
      ht1 hM hη hRε hR' has hN hFa.le
    rw [← hc₀, ← hc₁] at h1
    exact h1
  -- integrability
  have hFi := (integrable_integral_condDelta_sq_le (r := r) (CW := CW) hσ hK hh hhH hXm hYm hWm
    hX0 hY0 hWi hWb).1
  have hS1 : MeasurableSet {x : ℝ | h / v < |x|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hS3 : MeasurableSet {x : ℝ | |x - K| ≤ C₁ * ε} :=
    measurableSet_le (by fun_prop) measurable_const
  have hΔmm : Measurable fun ω => X ω + r * X ω * h - Y ω * W ω := by fun_prop
  have hΔsm : Measurable fun ω => |σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h := by
    fun_prop
  obtain ⟨hi1, he1⟩ := integrable_integral_indicator_one_comp (μ := μ) hΔmm hS1
  obtain ⟨hi2, he2⟩ := integrable_integral_indicator_one_comp (μ := μ) hΔsm hS1
  obtain ⟨hi3, he3⟩ := integrable_integral_indicator_one_comp (μ := μ) hXm hS3
  have hi12 : Integrable (fun ω =>
      {x : ℝ | h / v < |x|}.indicator (1 : ℝ → ℝ) (X ω + r * X ω * h - Y ω * W ω) +
        {x : ℝ | h / v < |x|}.indicator 1 (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h))
      μ := hi1.add hi2
  have hA : Integrable (fun ω => (c₀ + c₁ * M) / h *
      ({x : ℝ | h / v < |x|}.indicator 1 (X ω + r * X ω * h - Y ω * W ω) +
        {x : ℝ | h / v < |x|}.indicator 1 (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h)))
      μ := hi12.const_mul _
  have hB : Integrable (fun ω => 2 * c₁ / (M * h) * W ω ^ 4) μ := hWi.const_mul _
  have hC : Integrable (fun ω => (N₀ / v ^ 3) ^ 2 *
      {x : ℝ | |x - K| ≤ C₁ * ε}.indicator (1 : ℝ → ℝ) (X ω)) μ := hi3.const_mul _
  have hAB : Integrable (fun ω => (c₀ + c₁ * M) / h *
      ({x : ℝ | h / v < |x|}.indicator 1 (X ω + r * X ω * h - Y ω * W ω) +
        {x : ℝ | h / v < |x|}.indicator 1 (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h)) +
      2 * c₁ / (M * h) * W ω ^ 4) μ := hA.add hB
  have hABC : Integrable (fun ω => (c₀ + c₁ * M) / h *
      ({x : ℝ | h / v < |x|}.indicator 1 (X ω + r * X ω * h - Y ω * W ω) +
        {x : ℝ | h / v < |x|}.indicator 1 (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h)) +
      2 * c₁ / (M * h) * W ω ^ 4 +
      (N₀ / v ^ 3) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 (X ω)) μ := hAB.add hC
  have hint : ∫ ω, ((c₀ + c₁ * M) / h *
      ({x : ℝ | h / v < |x|}.indicator 1 (X ω + r * X ω * h - Y ω * W ω) +
          {x : ℝ | h / v < |x|}.indicator 1 (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h)) +
        2 * c₁ / (M * h) * W ω ^ 4 +
        (N₀ / v ^ 3) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 (X ω) + Fa ^ 2) ∂μ =
      (c₀ + c₁ * M) / h * (μ.real {ω | X ω + r * X ω * h - Y ω * W ω ∈ {x : ℝ | h / v < |x|}} +
        μ.real {ω | |σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h ∈
          {x : ℝ | h / v < |x|}}) +
        2 * c₁ / (M * h) * ∫ ω, W ω ^ 4 ∂μ +
        (N₀ / v ^ 3) ^ 2 * μ.real {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}} + Fa ^ 2 := by
    rw [integral_add hABC (integrable_const _), integral_add hAB hC,
      integral_add hA hB, integral_const_mul, integral_add hi1 hi2, integral_const_mul,
      integral_const_mul, he1, he2, he3, integral_const, probReal_univ, one_smul]
  -- the probabilities
  have hP1 : μ.real {ω | X ω + r * X ω * h - Y ω * W ω ∈ {x : ℝ | h / v < |x|}} ≤
      Cm * v ^ (2 * p) := by
    refine (measureReal_lt_abs_le_integral_pow_div hmi ha0).trans ?_
    calc (∫ ω, (X ω + r * X ω * h - Y ω * W ω) ^ (2 * p) ∂μ) / (h / v) ^ (2 * p)
        ≤ Cm * h ^ (2 * p) / (h / v) ^ (2 * p) :=
          div_le_div_of_nonneg_right hmb (by positivity)
      _ = Cm * v ^ (2 * p) := by
          rw [div_pow]
          field_simp
  have hP2 : μ.real {ω | |σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h ∈
      {x : ℝ | h / v < |x|}} ≤ Cs * v ^ (2 * p) := by
    refine (measureReal_lt_abs_le_integral_pow_div hsi ha0).trans ?_
    calc (∫ ω, (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h) ^ (2 * p) ∂μ) /
          (h / v) ^ (2 * p)
        ≤ Cs * h ^ (2 * p) / (h / v) ^ (2 * p) :=
          div_le_div_of_nonneg_right hsb (by positivity)
      _ = Cs * v ^ (2 * p) := by
          rw [div_pow]
          field_simp
  have hP3 : μ.real {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}} ≤
      4 * ρ * C₁ * ε + CX * v ^ (4 * p) / C₁ ^ (2 * p) := by
    have hsub : {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}} ⊆
        {ω | |ST ω - K| ≤ 2 * (C₁ * ε)} ∪ {ω | C₁ * ε < |ST ω - X ω|} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_cases hω' : C₁ * ε < |ST ω - X ω|
      · exact Or.inr hω'
      · left
        simp only [Set.mem_ofPred_eq]
        rw [not_lt] at hω'
        calc |ST ω - K| = |(ST ω - X ω) + (X ω - K)| := by ring_nf
          _ ≤ |ST ω - X ω| + |X ω - K| := abs_add_le _ _
          _ ≤ 2 * (C₁ * ε) := by linarith
    have hC1e : 0 < C₁ * ε := by positivity
    have hεp : (C₁ * ε) ^ (2 * p) = C₁ ^ (2 * p) * (h ^ p / v ^ (4 * p)) := by
      rw [mul_pow, hε, ← hshdef, div_pow, ← pow_mul, pow_mul sh 2 p, sq, hshsq,
        show 2 * (2 * p) = 4 * p by ring]
    calc μ.real {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}}
        ≤ μ.real {ω | |ST ω - K| ≤ 2 * (C₁ * ε)} + μ.real {ω | C₁ * ε < |ST ω - X ω|} :=
          (measureReal_mono hsub).trans (measureReal_union_le _ _)
      _ ≤ 2 * ρ * (2 * (C₁ * ε)) + (∫ ω, (ST ω - X ω) ^ (2 * p) ∂μ) / (C₁ * ε) ^ (2 * p) :=
          add_le_add (hball _ (by positivity)) (measureReal_lt_abs_le_integral_pow_div hxi hC1e)
      _ ≤ 2 * ρ * (2 * (C₁ * ε)) + CX * h ^ p / (C₁ * ε) ^ (2 * p) :=
          add_le_add le_rfl (div_le_div_of_nonneg_right hxb (by positivity))
      _ = 4 * ρ * C₁ * ε + CX * v ^ (4 * p) / C₁ ^ (2 * p) := by
          rw [hεp]
          field_simp
          ring
  -- the powers of `v`
  have hw : v ^ (2 * p) ≤ h ^ 3 := by
    have h1 : (h ^ δ) ^ (2 * p) ≤ h ^ ((3 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast (h ^ δ), ← Real.rpow_mul hh.le]
      refine Real.rpow_le_rpow_of_exponent_ge hh hh1 ?_
      push_cast
      linarith
    rw [Real.rpow_natCast] at h1
    rw [hv]
    exact h1
  have hw0 : 0 ≤ v ^ (2 * p) := by positivity
  have hv4p : v ^ (4 * p) = (v ^ (2 * p)) ^ 2 := by rw [← pow_mul]; ring_nf
  have hhsh : h ≤ sh := by rw [← hshsq]; exact mul_le_of_le_one_right hsh0.le hsh1
  have hh2 : h ^ 2 ≤ sh := (pow_le_of_le_one hh.le hh1 (by norm_num)).trans hhsh
  have hh3 : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have hv8 : sh ≤ sh / v ^ 8 := le_div_self hsh0.le (by positivity) (pow_le_one₀ hv0.le hv1)
  have hEW := hWb
  -- the four terms
  have T1 : (c₀ + c₁ * M) / h * (μ.real {ω | X ω + r * X ω * h - Y ω * W ω ∈
        {x : ℝ | h / v < |x|}} + μ.real {ω | |σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h ∈
          {x : ℝ | h / v < |x|}}) ≤ (Cm + Cs) * (c₀ + c₁) * sh := by
    have hB1 : 0 ≤ (c₀ + c₁ * M) / h := by positivity
    have e : (c₀ + c₁ * M) / h * h ^ 3 = c₀ * h ^ 2 + c₁ * sh := by
      rw [hMdef, ← hshsq]
      field_simp
    calc _ ≤ (c₀ + c₁ * M) / h * ((Cm + Cs) * h ^ 3) := by
          refine mul_le_mul_of_nonneg_left ?_ hB1
          have := mul_le_mul_of_nonneg_left hw hCm
          have := mul_le_mul_of_nonneg_left hw hCs
          linarith
      _ = (Cm + Cs) * (c₀ * h ^ 2 + c₁ * sh) := by rw [← e]; ring
      _ ≤ (Cm + Cs) * (c₀ * sh + c₁ * sh) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := mul_le_mul_of_nonneg_left hh2 hc₀0
          linarith
      _ = (Cm + Cs) * (c₀ + c₁) * sh := by ring
  have T2 : 2 * c₁ / (M * h) * ∫ ω, W ω ^ 4 ∂μ ≤ 2 * c₁ * CW * sh := by
    have e : 2 * c₁ / (M * h) = 2 * c₁ * sh := by
      rw [hMdef, ← hshsq]
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hEW (by positivity : (0 : ℝ) ≤ 2 * c₁ * sh)
    linarith
  have T3 : (N₀ / v ^ 3) ^ 2 * μ.real {ω | X ω ∈ {x : ℝ | |x - K| ≤ C₁ * ε}} ≤
      N₀ ^ 2 * (4 * ρ * C₁ + CX / C₁ ^ (2 * p)) * (sh / v ^ 8) := by
    have hN2 : 0 ≤ (N₀ / v ^ 3) ^ 2 := sq_nonneg _
    have hvw : v ^ (4 * p) * v ^ 2 ≤ sh := by
      rw [hv4p]
      have h1 : (v ^ (2 * p)) ^ 2 ≤ (h ^ 3) ^ 2 := pow_le_pow_left₀ hw0 hw 2
      have h2 : (h ^ 3) ^ 2 ≤ h ^ 2 := by
        rw [← pow_mul]
        exact pow_le_pow_of_le_one hh.le hh1 (by norm_num)
      have h3 : v ^ 2 ≤ 1 := pow_le_one₀ hv0.le hv1
      have h4 : 0 ≤ (v ^ (2 * p)) ^ 2 := sq_nonneg _
      exact (mul_le_of_le_one_right h4 h3).trans ((h1.trans h2).trans hh2)
    calc _ ≤ (N₀ / v ^ 3) ^ 2 * (4 * ρ * C₁ * ε + CX * v ^ (4 * p) / C₁ ^ (2 * p)) :=
          mul_le_mul_of_nonneg_left hP3 hN2
      _ = N₀ ^ 2 * (4 * ρ * C₁) * (sh / v ^ 8) +
            N₀ ^ 2 * (CX / C₁ ^ (2 * p)) * (v ^ (4 * p) * v ^ 2 / v ^ 8) := by
          rw [hε, ← hshdef]
          field_simp
      _ ≤ N₀ ^ 2 * (4 * ρ * C₁) * (sh / v ^ 8) + N₀ ^ 2 * (CX / C₁ ^ (2 * p)) * (sh / v ^ 8) := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact div_le_div_of_nonneg_right hvw (by positivity)
      _ = _ := by ring
  have T4 : Fa ^ 2 ≤ cp ^ 2 * (sh / v ^ 8) := by
    have e : Fa ^ 2 = cp ^ 2 * ((v ^ (2 * p)) ^ 2 * v ^ 12 / (h ^ 2 * v ^ 8)) := by
      rw [hFadef, hcp]
      field_simp
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (v ^ (2 * p)) ^ 2 ≤ (h ^ 3) ^ 2 := pow_le_pow_left₀ hw0 hw 2
    have h2 : v ^ 12 ≤ 1 := pow_le_one₀ hv0.le hv1
    have h3 : (h ^ 3) ^ 2 ≤ h ^ 2 * sh := by
      have : (h ^ 3) ^ 2 = h ^ 2 * (h ^ 2) ^ 2 := by ring
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : (h ^ 2) ^ 2 ≤ h ^ 2 := pow_le_of_le_one (by positivity)
        (pow_le_one₀ hh.le hh1) (by norm_num)
      linarith
    have h4 : 0 ≤ (v ^ (2 * p)) ^ 2 := sq_nonneg _
    have h5 : (v ^ (2 * p)) ^ 2 * v ^ 12 ≤ h ^ 2 * sh :=
      (mul_le_of_le_one_right h4 h2).trans (h1.trans h3)
    calc (v ^ (2 * p)) ^ 2 * v ^ 12 * v ^ 8 ≤ h ^ 2 * sh * v ^ 8 :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = sh * (h ^ 2 * v ^ 8) := by ring
  calc _ ≤ ∫ ω, ((c₀ + c₁ * M) / h *
        ({x : ℝ | h / v < |x|}.indicator 1 (X ω + r * X ω * h - Y ω * W ω) +
          {x : ℝ | h / v < |x|}.indicator 1 (|σ * X ω| * Real.sqrt h - |σ * Y ω| * Real.sqrt h)) +
        2 * c₁ / (M * h) * W ω ^ 4 +
        (N₀ / v ^ 3) ^ 2 * {x : ℝ | |x - K| ≤ C₁ * ε}.indicator 1 (X ω) + Fa ^ 2) ∂μ :=
        integral_mono_ae hFi (hABC.add (integrable_const _)) hpt
    _ = _ := hint
    _ ≤ (Cm + Cs) * (c₀ + c₁) * sh + 2 * c₁ * CW * sh +
          N₀ ^ 2 * (4 * ρ * C₁ + CX / C₁ ^ (2 * p)) * (sh / v ^ 8) + cp ^ 2 * (sh / v ^ 8) := by
        linarith only [T1, T2, T3, T4]
    _ ≤ ((Cm + Cs) * (c₀ + c₁) + 2 * c₁ * CW + N₀ ^ 2 * (4 * ρ * C₁ + CX / C₁ ^ (2 * p)) +
          cp ^ 2) * (sh / v ^ 8) := by
        have h1 : 0 ≤ (Cm + Cs) * (c₀ + c₁) + 2 * c₁ * CW := by positivity
        have := mul_le_mul_of_nonneg_left hv8 h1
        linarith only [this]
    _ = _ := by rw [hshdef]

/-- `h^{1/2 − 8δ} = √h/(h^δ)⁸` for `h > 0` (the exponent `1/2` of the digital-delta variance, less
`8δ`; Giles 2015, §5.4, p. 42). -/
lemma rpow_half_sub_eight_mul_eq {h : ℝ} (hh : 0 < h) (δ : ℝ) :
    h ^ (1 / 2 - 8 * δ) = Real.sqrt h / (h ^ δ) ^ 8 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hh.le, ← Real.rpow_sub hh]
  congr 1
  push_cast
  ring

/-- **The variance rate of the digital-delta corrections, abstract form** (Giles 2015, §5.4, p. 42,
l. 1829–1835: "Sensitivities for digital options can be obtained by first using the conditional
expectation approach described previously, and then applying pathwise sensitivity analysis to
this. … the numerical analysis of the resulting variance is given by Burgos (2014)"; the matching
of §5.2, p. 36, l. 1563–1566: "matching that of the fine path to within `O(h)`, for both the mean
and the standard deviation").  For a family of fine values `X_i ≠ 0`, coarse values `Y_i ≠ 0`,
coarse factors `W_i` (`m_c = Y W`) with `E[W⁴] = O(1)`, steps `0 < h_i ≤ H` and a reference `S_i`
with density at most `ρ` near `K ≠ 0`, if for some `p` with `2pδ ≥ 3` (`0 < δ ≤ 1/16`), uniformly,
`E[(m_f − m_c)^{2p}] = O(h^{2p})`, `E[(s_f − s_c)^{2p}] = O(h^{2p})` and `E[(S − X)^{2p}] = O(h^p)`,
then `(G_f − G_c)²` is integrable and `E[(G_f − G_c)²] ≤ C h_i^{1/2 − 8δ}` for one `C` and all `i`,
`G = φ((m − K)/s)/s`.  For `h > 1` or `ε = √h/v² > ε₀` the bound `O(1/h)` of
`integrable_integral_condDelta_sq_le` is used. -/
lemma condDelta_sq_rate {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {r σ K ρ δ H : ℝ} (hσ : σ ≠ 0) (hK : K ≠ 0) (hρ : 0 ≤ ρ)
    (hH : 0 < H) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) {p : ℕ} (hpδ : 3 ≤ 2 * p * δ)
    {h : ι → ℝ} (hh : ∀ i, 0 < h i) (hhH : ∀ i, h i ≤ H) {X Y W ST : ι → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ i, Measurable (Y i)) (hWm : ∀ i, Measurable (W i))
    (hX0 : ∀ i, ∀ᵐ ω ∂μ, X i ω ≠ 0) (hY0 : ∀ i, ∀ᵐ ω ∂μ, Y i ω ≠ 0)
    (hball : ∀ i η, 0 < η → μ.real {ω | |ST i ω - K| ≤ η} ≤ 2 * ρ * η)
    (hΔm : MomentBound μ (fun i ω => X i ω + r * X i ω * h i - Y i ω * W i ω) p
      (fun i => h i ^ (2 * p)))
    (hΔs : MomentBound μ (fun i ω => |σ * X i ω| * Real.sqrt (h i) -
      |σ * Y i ω| * Real.sqrt (h i)) p (fun i => h i ^ (2 * p)))
    (hXS : MomentBound μ (fun i ω => ST i ω - X i ω) p (fun i => h i ^ p))
    (hW : MomentBound μ W 2 (fun _ => 1)) :
    ∃ C, 0 ≤ C ∧ ∀ i,
      Integrable (fun ω => (gaussianPDFReal 0 1 ((X i ω + r * X i ω * h i - K) /
          (|σ * X i ω| * Real.sqrt (h i))) / (|σ * X i ω| * Real.sqrt (h i)) -
        gaussianPDFReal 0 1 ((Y i ω * W i ω - K) / (|σ * Y i ω| * Real.sqrt (h i))) /
          (|σ * Y i ω| * Real.sqrt (h i))) ^ 2) μ ∧
      ∫ ω, (gaussianPDFReal 0 1 ((X i ω + r * X i ω * h i - K) /
          (|σ * X i ω| * Real.sqrt (h i))) / (|σ * X i ω| * Real.sqrt (h i)) -
        gaussianPDFReal 0 1 ((Y i ω * W i ω - K) / (|σ * Y i ω| * Real.sqrt (h i))) /
          (|σ * Y i ω| * Real.sqrt (h i))) ^ 2 ∂μ ≤ C * h i ^ (1 / 2 - 8 * δ) := by
  obtain ⟨Cm, hCm, hm⟩ := hΔm
  obtain ⟨Cs, hCs, hs⟩ := hΔs
  obtain ⟨CX, hCX, hx⟩ := hXS
  obtain ⟨CW, hCW, hw⟩ := hW
  have e4 : (2 * 2 : ℕ) = 4 := rfl
  rw [e4] at hw
  have hW4 : ∀ i, Integrable (fun ω => W i ω ^ 4) μ ∧ ∫ ω, W i ω ^ 4 ∂μ ≤ CW := fun i =>
    ⟨(hw i).1, by simpa only [mul_one] using (hw i).2⟩
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have hK' : 0 < |K| := abs_pos.2 hK
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 2 * (2 + |K| * (|σ| + |r|)) := ⟨_, rfl⟩
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ,
      ε₀ = min (min (1 / (2 * (|σ| + |r| + 1))) (|K| / (2 * C₁))) (|σ| * |K| / 4) := ⟨_, rfl⟩
  have hε₀0 : 0 < ε₀ := by
    rw [hε₀]
    exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ,
      c₀ = ((1 + |r| * H + |σ| * Real.sqrt H) ^ 2 + 2 * σ ^ 2 * H) / (K ^ 2 * σ ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = 2 / (K ^ 2 * σ ^ 2) := ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℝ,
      N₀ = 32 * (1 + 4 * (C₁ + 2 * |r| * |K| + 1) / (|σ| * |K|)) / (|σ| * |K|) ^ 2 := ⟨_, rfl⟩
  obtain ⟨cp, hcp⟩ : ∃ cp : ℝ, cp = (p + 1).factorial * 2 ^ (p + 1) := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  obtain ⟨CB, hCB⟩ : ∃ CB : ℝ, CB = c₀ + c₁ * (1 + CW) := ⟨_, rfl⟩
  have hCB0 : 0 ≤ CB := by rw [hCB]; positivity
  obtain ⟨Cmain, hCmain⟩ : ∃ Cmain : ℝ, Cmain = (Cm + Cs) * (c₀ + c₁) + 2 * c₁ * CW +
      N₀ ^ 2 * (4 * ρ * C₁ + CX / C₁ ^ (2 * p)) + cp ^ 2 := ⟨_, rfl⟩
  have hCmain0 : 0 ≤ Cmain := by rw [hCmain]; positivity
  refine ⟨CB + CB / ε₀ ^ 3 + Cmain, by positivity, fun i => ?_⟩
  have hi := hh i
  have hbad := integrable_integral_condDelta_sq_le (r := r) (K := K) hσ hK hi (hhH i) (hXm i)
    (hYm i) (hWm i) (hX0 i) (hY0 i) (hW4 i).1 (hW4 i).2
  rw [← hc₀, ← hc₁, ← hCB] at hbad
  refine ⟨hbad.1, ?_⟩
  by_cases hbig : 1 < h i
  · have h1 : 1 ≤ h i ^ (1 / 2 - 8 * δ) := Real.one_le_rpow hbig.le (by linarith)
    have h2 : CB / h i ≤ CB := div_le_self hCB0 hbig.le
    have h3 : 0 ≤ CB / ε₀ ^ 3 + Cmain := by positivity
    calc _ ≤ CB / h i := hbad.2
      _ ≤ (CB + CB / ε₀ ^ 3 + Cmain) * 1 := by linarith only [h2, h3]
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hh1 : h i ≤ 1 := not_lt.1 hbig
  obtain ⟨v, hv⟩ : ∃ v, v = h i ^ δ := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε, ε = Real.sqrt (h i) / v ^ 2 := ⟨_, rfl⟩
  have hv0 : 0 < v := by rw [hv]; exact Real.rpow_pos_of_pos hi δ
  have hv1 : v ≤ 1 := by rw [hv]; exact Real.rpow_le_one hi.le hh1 hδ0.le
  have hsh0 : 0 < Real.sqrt (h i) := Real.sqrt_pos.2 hi
  rw [rpow_half_sub_eight_mul_eq hi δ, ← hv]
  have hpos : 0 ≤ Real.sqrt (h i) / v ^ 8 := by positivity
  by_cases hεbig : ε₀ < ε
  · have key : ε₀ ^ 3 ≤ h i * (Real.sqrt (h i) / v ^ 8) := by
      have h1 : ε₀ ^ 3 ≤ ε ^ 3 := pow_le_pow_left₀ hε₀0.le hεbig.le 3
      have h2 : ε ^ 3 ≤ h i * (Real.sqrt (h i) / v ^ 8) := by
        have e1 : ε ^ 3 = Real.sqrt (h i) ^ 3 / v ^ 6 := by rw [hε, div_pow, ← pow_mul]
        have e3 : Real.sqrt (h i) ^ 3 = h i * Real.sqrt (h i) := by
          rw [pow_succ, Real.sq_sqrt hi.le]
        have e2 : h i * (Real.sqrt (h i) / v ^ 8) = Real.sqrt (h i) ^ 3 / v ^ 8 := by
          rw [e3]
          ring
        rw [e1, e2]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_of_le_one hv0.le hv1 (by norm_num))
      linarith
    have h3 : CB / h i ≤ CB / ε₀ ^ 3 * (Real.sqrt (h i) / v ^ 8) := by
      rw [div_le_iff₀ hi]
      calc CB = CB / ε₀ ^ 3 * ε₀ ^ 3 := by field_simp
        _ ≤ CB / ε₀ ^ 3 * (h i * (Real.sqrt (h i) / v ^ 8)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
        _ = _ := by ring
    have h4 : 0 ≤ (CB + Cmain) * (Real.sqrt (h i) / v ^ 8) := by positivity
    calc _ ≤ CB / h i := hbad.2
      _ ≤ CB / ε₀ ^ 3 * (Real.sqrt (h i) / v ^ 8) := h3
      _ ≤ _ := by linarith only [h4]
  have hε' : ε ≤ ε₀ := not_lt.1 hεbig
  have hεa : ε ≤ 1 / (2 * (|σ| + |r| + 1)) :=
    hε'.trans (by rw [hε₀]; exact (min_le_left _ _).trans (min_le_left _ _))
  have hεb : ε ≤ |K| / (2 * C₁) :=
    hε'.trans (by rw [hε₀]; exact (min_le_left _ _).trans (min_le_right _ _))
  have hεc : ε ≤ |σ| * |K| / 4 := hε'.trans (by rw [hε₀]; exact min_le_right _ _)
  have hmain := condDelta_sq_le_main (r := r) (K := K) (ρ := ρ) (H := H) hσ hK hpδ hi hh1
    (hhH i) hδ0.le hv hε hC₁ hεa hεb hεc hc₀ hc₁ hN₀ hcp (hXm i) (hYm i) (hWm i) (hX0 i)
    (hY0 i) (hball i) (hm i).1 (hm i).2
    (hs i).1 (hs i).2 (hx i).1 (hx i).2 (hW4 i).1 (hW4 i).2 hCm hCs hCX hCW
  rw [← hCmain] at hmain
  have h4 : 0 ≤ (CB + CB / ε₀ ^ 3) * (Real.sqrt (h i) / v ^ 8) := by positivity
  calc _ ≤ Cmain * (Real.sqrt (h i) / v ^ 8) := hmain
    _ ≤ _ := by linarith only [h4]

/-! ### The variance rate for GBM -/

/-- **G5.4-04: the variance of the digital-delta corrections is `O(h_ℓ^q)` for every `q < 1/2`**
(Giles 2015, §5.4, p. 42, l. 1829–1835: "Sensitivities for digital options can be obtained by first
using the conditional expectation approach described previously, and then applying pathwise
sensitivity analysis to this. Full details on how to formulate appropriate MLMC estimators are given
by Burgos and Giles (2012), and the numerical analysis of the resulting variance is given by Burgos
(2014)"; the conditional-expectation payoffs of §5.2, p. 36, l. 1551–1574).  For GBM
`dS = rS dt + σS dW` with `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, any strike `K` and every `q < 1/2` there is
`C ≥ 0` such that for every level `ℓ + 1 ≥ 1` (`h_{ℓ+1} = T 2^{−(ℓ+1)}`) the correction
`D = ∂P^f_{ℓ+1}/∂s₀ − ∂P^c_ℓ/∂s₀` of the pathwise sensitivities of the conditional-expectation
payoffs (`gbmDigitalCondFineDelta`, `gbmDigitalCondCoarseDelta`; they are the derivatives in `s₀`,
`gbm_digital_condExp_delta`) is square integrable, `E[D²] ≤ C h_{ℓ+1}^q` and
`V[D] ≤ C h_{ℓ+1}^q`.

Proof: `D = (K/s₀)(φ((m_f − K)/s_f)/s_f − φ((m_c − K)/s_c)/s_c)` with `m_c = Y W`,
`W = 1 + r h_ℓ + σ ΔW_{N−2}`; `condDelta_sq_rate` with the `L^{2p}` matching
(`momentBound_condMean_diff`, `momentBound_condStd_diff`), the `L^{2p}` distance `O(√h)` of the fine
value from `S_T` (`momentBound_gbmExact_sub_fine`), the bounded density of `S_T`
(`gbmExact_smallBall`), `E[W⁴] = O(1)` (`momentBound_affine_gaussian`) and
`δ = (1/2 − max(q, 0))/8`.
For `K = 0` both sensitivities vanish.

**Deviation.**  The paper states no rate (it defers to Burgos 2014, l. 1834–1835, not consulted).
Every `q < 1/2`, not `q = 1/2` (heuristically and numerically `V_ℓ ≈ O(h^{1/2})`, see the module
docstring); GBM and the delta only; `e^{−rT}` omitted. -/
theorem gbm_digital_condExp_delta_variance_rate (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) (K : ℝ) {q : ℝ} (hq : q < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fun z => gbmDigitalCondFineDelta r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z) 2 stdNormalSeq ∧
      ∫ z, (gbmDigitalCondFineDelta r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z) ^ 2 ∂stdNormalSeq ≤
          C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      variance (fun z => gbmDigitalCondFineDelta r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z) stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ q := by
  have hL : ∀ ℓ : ℕ, MemLp (fun z => gbmDigitalCondFineDelta r σ T s₀ K (ℓ + 1) z -
      gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z) 2 stdNormalSeq := fun ℓ =>
    (gbm_digital_condExp_delta r σ hs₀ hσ hT K (ℓ + 1)).2.2.1.sub
      (gbm_digital_condExp_delta r σ hs₀ hσ hT K ℓ).2.2.2.1
  rcases eq_or_ne K 0 with rfl | hK
  · -- `K = 0`: both sensitivities vanish
    refine ⟨0, le_rfl, fun ℓ => ⟨hL ℓ, ?_, ?_⟩⟩
    · have e : ∀ z, (gbmDigitalCondFineDelta r σ T s₀ 0 (ℓ + 1) z -
          gbmDigitalCondCoarseDelta r σ T s₀ 0 ℓ z) ^ 2 = 0 := fun z => by
        unfold gbmDigitalCondFineDelta gbmDigitalCondCoarseDelta
        simp only [zero_div, mul_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]
      simp only [e, integral_zero, zero_mul, le_refl]
    · rw [variance_eq_zero_of_forall_eq (c := 0) fun z => by
        unfold gbmDigitalCondFineDelta gbmDigitalCondCoarseDelta
        simp only [zero_div, mul_zero, sub_self], zero_mul]
  obtain ⟨q₁, hq₁def⟩ : ∃ q₁ : ℝ, q₁ = max q 0 := ⟨_, rfl⟩
  have hq₁ : q₁ < 1 / 2 := hq₁def ▸ max_lt hq (by norm_num)
  have hq₁0 : 0 ≤ q₁ := hq₁def ▸ le_max_right _ _
  have hqq₁ : q ≤ q₁ := hq₁def ▸ le_max_left _ _
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (1 / 2 - q₁) / 8 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 / 16 := by rw [hδdef]; linarith
  obtain ⟨p, hp⟩ := exists_nat_gt (3 / (2 * δ))
  have hpδ : 3 ≤ 2 * p * δ := by
    rw [div_lt_iff₀ (by positivity)] at hp
    linarith
  have hp0 : 0 < p := by
    have : (0 : ℝ) < p := lt_trans (by positivity) hp
    exact_mod_cast this
  have hh : ∀ ℓ : ℕ, 0 < T / 2 ^ (ℓ + 1) := fun ℓ => by positivity
  have hhT : ∀ ℓ : ℕ, T / 2 ^ (ℓ + 1) ≤ T := fun ℓ =>
    div_le_self hT.le (one_le_pow₀ (by norm_num))
  have hXm : ∀ ℓ : ℕ, Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S)
      (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1) := fun ℓ =>
    measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _
  have hYm : ∀ ℓ : ℕ, Measurable fun z : ℕ → ℝ => milsteinPath (fun S => r * S)
      (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) := fun ℓ =>
    (measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _).comp measurable_pairAvg
  have hWm : ∀ ℓ : ℕ, Measurable fun z : ℕ → ℝ =>
      1 + r * (T / 2 ^ ℓ) + σ * (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2)) := fun ℓ => by
    have : Measurable fun z : ℕ → ℝ => z (2 ^ (ℓ + 1) - 2) := measurable_pi_apply _
    fun_prop
  have hX0 : ∀ ℓ : ℕ, ∀ᵐ z ∂stdNormalSeq, milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1) ≠ 0 := fun ℓ =>
    (ae_gbm_milsteinPath_ne_zero r σ hs₀ hσ (hh ℓ) _).mono fun z hz => right_ne_zero_of_mul hz
  have hY0 : ∀ ℓ : ℕ, ∀ᵐ z ∂stdNormalSeq, milsteinPath (fun S => r * S) (fun S => σ * S)
      (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) ≠ 0 := fun ℓ =>
    (measurePreserving_pairAvg.quasiMeasurePreserving.ae (ae_gbm_milsteinPath_ne_zero r σ hs₀ hσ
      (by positivity : (0 : ℝ) < T / 2 ^ ℓ) (2 ^ ℓ - 1))).mono fun z hz => right_ne_zero_of_mul hz
  -- the coarse factor `W = 1 + r h_ℓ + σ ΔW_{N−2}` has bounded fourth moments
  have hA : (1 : ℝ) ≤ 1 + |r| * T := by have := abs_nonneg r; nlinarith
  have hWg : MomentBound (gaussianReal 0 1) (fun ℓ (x : ℝ) =>
      (1 + r * (T / 2 ^ ℓ)) + σ * Real.sqrt (T / 2 ^ (ℓ + 1)) * x) 2 (fun _ => 1) :=
    momentBound_affine_gaussian (a := fun ℓ => 1 + r * (T / 2 ^ ℓ))
      (s := fun ℓ => σ * Real.sqrt (T / 2 ^ (ℓ + 1))) (S := σ ^ 2 * T) hA
      (fun ℓ => abs_one_add_mul_le r (by positivity)
        (div_le_self hT.le (one_le_pow₀ (by norm_num))))
      (fun ℓ => by
        rw [mul_pow, Real.sq_sqrt (hh ℓ).le]
        exact mul_le_mul_of_nonneg_left (hhT ℓ) (sq_nonneg σ)) 2
  have hU : MomentBound stdNormalSeq (fun (_ : ℕ) (_ : ℕ → ℝ) => (1 : ℝ)) 2 (fun _ => 1) :=
    ⟨1, zero_le_one, fun _ => ⟨integrable_const _, by simp⟩⟩
  have hW : MomentBound stdNormalSeq (fun ℓ (z : ℕ → ℝ) =>
      1 + r * (T / 2 ^ ℓ) + σ * (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2))) 2
      (fun _ => 1) :=
    ((hU.mul_eval hWg (n := fun ℓ => 2 ^ (ℓ + 1) - 2) (fun _ => measurable_const)
      (fun _ _ _ _ => rfl) (fun ℓ => by fun_prop)).congr fun ℓ z => by ring).mono
      (K := 1) zero_le_one fun ℓ => by norm_num
  obtain ⟨C, hC, hbd⟩ := condDelta_sq_rate (μ := stdNormalSeq) (r := r) (K := K)
    (ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T))
    (h := fun ℓ => T / 2 ^ (ℓ + 1))
    (X := fun ℓ z => milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z
      (2 ^ (ℓ + 1) - 1))
    (Y := fun ℓ z => milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z)
      (2 ^ ℓ - 1))
    (W := fun ℓ z => 1 + r * (T / 2 ^ ℓ) + σ * (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2)))
    (ST := fun ℓ => gbmExact r σ T s₀ (ℓ + 1))
    hσ hK (by positivity) hT hδ0 hδ1 hpδ hh hhT hXm hYm hWm hX0 hY0
    (fun ℓ η hη => gbmExact_smallBall r σ hs₀ hσ hT K (ℓ + 1) hη)
    ((momentBound_condMean_diff r σ s₀ hT.le hp0).congr fun ℓ z => by
      unfold gbmCondMeanFine gbmCondMeanCoarse
      ring)
    ((momentBound_condStd_diff r σ s₀ hT.le hp0).congr fun ℓ z => rfl)
    ((momentBound_gbmExact_sub_fine r σ s₀ hT.le hp0).congr fun ℓ z => by
      rw [milsteinPath_fine_eq_prod]) hW
  have hexp : 1 / 2 - 8 * δ = q₁ := by rw [hδdef]; ring
  have eD : ∀ ℓ z, (gbmDigitalCondFineDelta r σ T s₀ K (ℓ + 1) z -
      gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z) ^ 2 = (K / s₀) ^ 2 *
      (gaussianPDFReal 0 1 ((milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀
          z (2 ^ (ℓ + 1) - 1) + r * milsteinPath (fun S => r * S) (fun S => σ * S)
          (T / 2 ^ (ℓ + 1)) s₀ z (2 ^ (ℓ + 1) - 1) * (T / 2 ^ (ℓ + 1)) - K) /
          (|σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z
            (2 ^ (ℓ + 1) - 1)| * Real.sqrt (T / 2 ^ (ℓ + 1)))) /
          (|σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ (ℓ + 1)) s₀ z
            (2 ^ (ℓ + 1) - 1)| * Real.sqrt (T / 2 ^ (ℓ + 1))) -
        gaussianPDFReal 0 1 ((milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀
          (pairAvg z) (2 ^ ℓ - 1) * (1 + r * (T / 2 ^ ℓ) +
            σ * (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2))) - K) /
          (|σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z)
            (2 ^ ℓ - 1)| * Real.sqrt (T / 2 ^ (ℓ + 1)))) /
          (|σ * milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg z)
            (2 ^ ℓ - 1)| * Real.sqrt (T / 2 ^ (ℓ + 1)))) ^ 2 := fun ℓ z => by
    have e1 : gbmCondMeanCoarse r σ T s₀ ℓ z = milsteinPath (fun S => r * S) (fun S => σ * S)
        (T / 2 ^ ℓ) s₀ (pairAvg z) (2 ^ ℓ - 1) * (1 + r * (T / 2 ^ ℓ) +
          σ * (Real.sqrt (T / 2 ^ (ℓ + 1)) * z (2 ^ (ℓ + 1) - 2))) := by
      unfold gbmCondMeanCoarse
      ring
    unfold gbmDigitalCondFineDelta gbmDigitalCondCoarseDelta
    rw [e1]
    unfold gbmCondMeanFine gbmCondStdFine gbmCondStdCoarse
    ring
  have key : ∀ ℓ : ℕ, ∫ z, (gbmDigitalCondFineDelta r σ T s₀ K (ℓ + 1) z -
      gbmDigitalCondCoarseDelta r σ T s₀ K ℓ z) ^ 2 ∂stdNormalSeq ≤
      (K / s₀) ^ 2 * C * T ^ (q₁ - q) * (T / 2 ^ (ℓ + 1)) ^ q := fun ℓ => by
    obtain ⟨-, h1⟩ := hbd ℓ
    rw [hexp] at h1
    simp_rw [eD ℓ]
    rw [integral_const_mul]
    calc _ ≤ (K / s₀) ^ 2 * (C * (T / 2 ^ (ℓ + 1)) ^ q₁) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ ≤ (K / s₀) ^ 2 * (C * (T ^ (q₁ - q) * (T / 2 ^ (ℓ + 1)) ^ q)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hC) (sq_nonneg _)
          exact rpow_le_rpow_sub_mul_rpow (hh ℓ) (hhT ℓ) hqq₁
      _ = _ := by ring
  refine ⟨(K / s₀) ^ 2 * C * T ^ (q₁ - q), by positivity, fun ℓ => ⟨hL ℓ, key ℓ, ?_⟩⟩
  exact (variance_le_expectation_sq (hL ℓ).1).trans (key ℓ)

/-- **G5.4-04 for the multilevel corrections of the digital delta, on every level** (Giles 2015,
§5.4, p. 42, l. 1829–1835: "Sensitivities for digital options can be obtained by first using the
conditional expectation approach described previously, and then applying pathwise sensitivity
analysis to this … the numerical analysis of the resulting variance is given by Burgos (2014)"; the
corrections `P^f_ℓ − P^c_{ℓ−1}` of the estimator before (2.4), p. 8, l. 375–381).  For GBM with
`s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, any `K` and every `q < 1/2` there is `C ≥ 0` such that the level
corrections `fineCoarseDiff (gbmDigitalCondFineDelta …) (gbmDigitalCondCoarseDelta …) ℓ`
(`∂P^f_0/∂s₀` on level `0`, `∂P^f_ℓ/∂s₀ − ∂P^c_{ℓ−1}/∂s₀` on level `ℓ ≥ 1`), whose means sum to the
delta of the finest-level digital price (`gbm_digital_condExp_delta_telescope`), are square
integrable with `V_ℓ ≤ C h_ℓ^q`, `h_ℓ = T 2^{−ℓ}`.  Level `0` has one fine step and no randomness
before it, so `V_0 = 0`; the other levels are `gbm_digital_condExp_delta_variance_rate`. -/
theorem gbm_digital_condExp_delta_corrections_rate (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) (K : ℝ) {q : ℝ} (hq : q < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
        (gbmDigitalCondCoarseDelta r σ T s₀ K) ℓ) 2 stdNormalSeq ∧
      variance (fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
        (gbmDigitalCondCoarseDelta r σ T s₀ K) ℓ) stdNormalSeq ≤ C * (T / 2 ^ ℓ) ^ q := by
  obtain ⟨C, hC, h⟩ := gbm_digital_condExp_delta_variance_rate r σ hs₀ hσ hT K hq
  have hL := (gbm_digital_condExp_delta_telescope r σ hs₀ hσ hT K 0).1
  refine ⟨C, hC, fun ℓ => ⟨hL ℓ, ?_⟩⟩
  cases ℓ with
  | zero =>
    have hz : ∀ z, fineCoarseDiff (gbmDigitalCondFineDelta r σ T s₀ K)
        (gbmDigitalCondCoarseDelta r σ T s₀ K) 0 z =
        gaussianPDFReal 0 1 ((s₀ + r * s₀ * T - K) / (|σ * s₀| * Real.sqrt T)) *
          (K / (s₀ * (|σ * s₀| * Real.sqrt T))) := fun z => by
      show gbmDigitalCondFineDelta r σ T s₀ K 0 z = _
      unfold gbmDigitalCondFineDelta gbmCondMeanFine gbmCondStdFine
      rw [pow_zero, pow_zero, div_one, Nat.sub_self]
      rfl
    rw [variance_eq_zero_of_forall_eq hz]
    have : 0 ≤ (T / 2 ^ 0) ^ q := Real.rpow_nonneg (by positivity) q
    positivity
  | succ ℓ => exact (h ℓ).2.2

end MLMC
