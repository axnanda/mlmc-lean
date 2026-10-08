import MlmcLean.SDEDigital
import MlmcLean.GBMMilstein
import MlmcLean.PDEExamples
import MlmcLean.SDEExtras
import Mathlib.Probability.ConditionalProbability

/-!
# The digital option for geometric Brownian motion (Giles 2015, §5.1–§5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1
"Euler-Maruyama discretisation" (p. 33, l. 1435–1446 of `docs/giles2015.txt`) and §5.2
"Milstein discretisation", paragraph "Digital options" (pp. 35–36, l. 1525–1590).  This file
continues `MlmcLean.SDEDigital`, for geometric Brownian motion `dS = rS dt + σS dW` with the exact
solution and the discretisations driven by the same increments `Z_i ∼ N(0,1)` (`stdNormalSeq`),
as in `MlmcLean.GBMEulerMaruyama` and `MlmcLean.GBMMilstein`.

* **The natural Milstein estimator** (§5.2, l. 1529–1532: "`P_ℓ − P_{ℓ−1} = O(1)` for an `O(h_ℓ)`
  fraction of the paths, giving `V_ℓ = O(h_ℓ)`").  `gbm_mil_digital_variance_le`:
  `V_ℓ = O(h_ℓ^{2/3})`, from the first-order strong error `E[(S_T − Ŝ_ℓ)²] = O(h_ℓ²)`
  (`gbm_mil_strong_error_level`) and the bounded lognormal density (`digital_mismatch_le`).
* **The fourth moment and the kurtosis** (§5.1, l. 1442–1446: "`E[(P_ℓ − P_{ℓ−1})⁴] = O(h^{1/2})`
  and so the kurtosis is `O(h^{−1/2})`").  The correction `D = P_ℓ − P_{ℓ−1}` takes values in
  `{−1, 0, 1}`, so `E[D⁴] = P(D ≠ 0)`; `gbm_em_digital_fourth_moment_le`: `E[D⁴] = O(h^{1/3})`
  for Euler–Maruyama, `gbm_mil_digital_fourth_moment_le`: `E[D⁴] = O(h^{2/3})` for Milstein, and in
  both cases the kurtosis `κ = 1/P(D ≠ 0)` is at least the reciprocal of the bound (it grows at
  least like `h^{−1/3}`, resp. `h^{−2/3}`).  Here `κ` is the raw-moment kurtosis `kurtosis`
  (`E[D⁴]/E[D²]²`), as in the paper's own ternary example (§3.3, l. 1046–1053, "`E[X] ≈ 0`, and
  `κ ≈ (p+q)^{−1}`"); the definition of §3.3 (l. 1038–1042) is for zero-mean `X`.
* **The exponent `1/3` of the mean-square mismatch bound is sharp, for the mismatch probability and
  for the variance** (the example of the docstring of `digital_mismatch_le`).
  `digital_mismatch_example`: for `X` uniform on `[−1, 1]` and `Y = X − 2d 1_{0<X<d}`,
  `E[(X − Y)²] = 2d³`, `P(1_{X>0} ≠ 1_{Y>0}) = d/2 = (E[(X − Y)²]/16)^{1/3}` and
  `V[1_{X>0} − 1_{Y>0}] = d/2 − d²/4`; `digital_mismatch_exponent_sharp`: neither the mismatch
  probability nor the variance is bounded by `C E[(X − Y)²]^q` with `q > 1/3`.
* **`E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` for the conditional-expectation payoffs** (§5.2, l. 1584–1590).
  For a scalar SDE with measurable (autonomous) coefficients, the Milstein path with an
  Euler–Maruyama last step, and the coarse path that re-uses the first half of the last fine
  increment: `map_milsteinEM_coarse_eq_fine` (the law equality that `integral_condExp_eq_of_map_eq`
  assumes), `integral_condExp_milsteinEM_coarse_eq_fine` (any payoff; both means equal `E[g(Ŝ^f)]`),
  `digital_smoothing_milsteinEM_mean_eq` (the `Φ` formulas are the conditional expectations, with
  the independence proved, and have the same mean), `gbm_digital_smoothing_mean_eq` (for GBM, with
  no further assumption).

**What is not proved.**  The paper's rates `O(h^{1/2})` (Euler–Maruyama) and `O(h)` (Milstein) for
the mismatch probability need more than the mean-square strong error
(`digital_mismatch_exponent_sharp` shows that the mean-square error alone gives no better exponent
than `1/3`).  Strong errors in `L^p`, `E|S_T − Ŝ_ℓ|^p = O(h_ℓ^{p/2})` (resp. `O(h_ℓ^p)`), give
`O(h_ℓ^{p/(2(p+1))})` (resp. `O(h_ℓ^{p/(p+1)})`) through `digital_mismatch_le_of_moment`, hence
every exponent below `1/2` (resp. `1`); these `L^p` bounds are proved for GBM in
`MlmcLean.GBMStrongLp` (`gbm_em_moment_error`, `gbm_mil_moment_error`), which gives every such
exponent (`gbm_em_digital_rate`, `gbm_mil_digital_rate`); the endpoints are not proved.  The
Gaussian-tail version `digital_mismatch_le_of_tail` does not apply to GBM, whose discretisation
error has lognormal tails.  The kurtosis rates (an upper bound on `κ`) need a lower bound on the
mismatch probability, which is not proved either.

`Φ` is `cdf (gaussianReal 0 1)` and the digital payoff `H(x − K)` is `(Set.Ioi K).indicator 1 x`;
the constant factors `10 e^{−rT}` (§5.1) and `25 e^{−rT}` (§5.2) of the paper's payoffs are omitted
(they do not change the kurtosis, `kurtosis_const_mul`, and scale the variance).
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### The mismatch probability for geometric Brownian motion -/

/-- **The density hypothesis of `digital_mismatch_le` for GBM** (Giles 2015, §5.1, p. 33,
l. 1437–1438: "there is a bounded density of paths terminating in the neighbourhood of `K`").  For
`s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, the exact solution `S_T` (`gbmExact`, on any level) satisfies
`P(|S_T − K| ≤ δ) ≤ 2ρδ` with `ρ = e^{(σ² − r)T}/(√(2π) |s₀| |σ| √T)`, the maximum of its lognormal
density (`map_lognormal_le_smul_volume`). -/
lemma gbmExact_smallBall (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    (K : ℝ) (ℓ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    stdNormalSeq.real {z | |gbmExact r σ T s₀ ℓ z - K| ≤ δ} ≤
      2 * (Real.exp ((σ ^ 2 - r) * T) /
        (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) * δ := by
  set ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)
    with hρdef
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hρ0 : 0 ≤ ρ := by positivity
  have hlaw : stdNormalSeq.map (gbmExact r σ T s₀ ℓ) = (gaussianReal 0 1).map
      (fun u => s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * u)) := by
    have e : gbmExact r σ T s₀ 0 =
        (fun u => s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * u)) ∘
          (fun z : ℕ → ℝ => z 0) := by
      funext z
      simp only [Function.comp_apply, gbmExact_zero, mul_assoc]
    have hgm : Measurable
        (fun u : ℝ => s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * u)) := by fun_prop
    rw [map_gbmExact, e, ← Measure.map_map hgm (measurable_pi_apply 0),
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0).map_eq]
  have hmap : stdNormalSeq.map (gbmExact r σ T s₀ ℓ) ≤ ENNReal.ofReal ρ • volume := by
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
  exact measureReal_abs_sub_le_of_map_le (measurable_gbmExact r σ T s₀ ℓ) hρ0 hmap K hδ.le

/-- `E[(1_{X>K} − 1_{Y>K})⁴] = P(1_{X>K} ≠ 1_{Y>K})`: the digital correction takes values in
`{−1, 0, 1}`, so its fourth power is the indicator of `{1_{X>K} ≠ 1_{Y>K}}` (Giles 2015, §5.1,
p. 33, l. 1441–1443). -/
lemma integral_pow_four_digital_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (K : ℝ) :
    ∫ ω, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω)) ^ 4 ∂μ =
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} := by
  rw [← integral_sq_digital_sub hX hY K]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have h := sq_digital_sub_eq_indicator X Y K ω
  dsimp only
  rw [show ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 from fun x => by ring, h]
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs <;> norm_num

/-- `(x²)^{1/3} = x^{2/3}` for `x ≥ 0`. -/
lemma sq_rpow_one_third {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (1 / 3 : ℝ) = x ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- **A lower bound on the kurtosis of a digital correction** (Giles 2015, §3.3, p. 23,
l. 1046–1053, and §5.1, p. 33, l. 1443–1445): the kurtosis of `D = 1_{X>K} − 1_{Y>K}` is
`κ = 1/P(D ≠ 0)` (`kurtosis_of_ternary`), so an upper bound `P(D ≠ 0) ≤ B` with `P(D ≠ 0) > 0`
gives `κ ≥ B⁻¹`.  Here `kurtosis` is the raw-moment ratio `E[D⁴]/E[D²]²`; the paper's definition
(§3.3, l. 1038–1042) is for zero-mean `X` (see `gbm_em_digital_fourth_moment_le` for the centred
kurtosis). -/
lemma inv_le_kurtosis_digital {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (K : ℝ) {B : ℝ}
    (hP : 0 < μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠
      (Set.Ioi K).indicator 1 (Y ω)})
    (hPB : μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠
      (Set.Ioi K).indicator 1 (Y ω)} ≤ B) :
    B⁻¹ ≤ kurtosis (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) -
      (Set.Ioi K).indicator 1 (Y ω)) μ := by
  have e : {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω) ≠ 0} =
      {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, sub_ne_zero]
  have hD : ∀ ω, (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω) = -1 ∨
      (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω) = 0 ∨
      (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω) = 1 := by
    intro ω
    rcases digital_eq_zero_or_one K (X ω) with h1 | h1 <;>
      rcases digital_eq_zero_or_one K (Y ω) with h2 | h2 <;> simp [h1, h2]
  have hDm : Measurable fun ω =>
      (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) - (Set.Ioi K).indicator 1 (Y ω) :=
    (measurable_digital hX K).sub (measurable_digital hY K)
  rw [kurtosis_of_ternary hDm hD (by rw [e]; exact hP), e]
  exact inv_anti₀ hP hPB

/-- **The fraction of GBM paths on either side of the strike, from a strong error bound** (Giles
2015, §5.1, p. 33, l. 1436–1441: "noting that the strong error is `O(h_ℓ^{1/2})`, and there is a
bounded density of paths terminating in the neighbourhood of `K`, there is therefore an
`O(h_ℓ^{1/2})` fraction of the samples with the coarse and fine paths on either side of the
strike").  For a fine approximation `Y^f` of the GBM solution `S_T` on level `ℓ + 1` and a coarse
one `Y^c` on level `ℓ` with `E[(S_T − Y^f)²] ≤ C h_{ℓ+1}^p` and `E[(S_T − Y^c)²] ≤ C h_ℓ^p`
(`h_ℓ = T 2^{−ℓ}`), the fine approximation and the coarse one driven by the summed increments
(`pairAvg`) end on different sides of `K` with probability at most
`3ρ^{2/3} C^{1/3} ((h_{ℓ+1}^p)^{1/3} + (h_ℓ^p)^{1/3})` (`gbmExact_smallBall`, `digital_mismatch_le`,
`digital_ne_subset_union`). -/
lemma gbm_digital_mismatch_le_of_strong (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (ℓ : ℕ) {Yf Yc : (ℕ → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C) {p : ℕ}
    (hintf : Integrable (fun z => (gbmExact r σ T s₀ (ℓ + 1) z - Yf z) ^ 2) stdNormalSeq)
    (hintc : Integrable (fun z => (gbmExact r σ T s₀ ℓ z - Yc z) ^ 2) stdNormalSeq)
    (hsf : ∫ z, (gbmExact r σ T s₀ (ℓ + 1) z - Yf z) ^ 2 ∂stdNormalSeq ≤
      C * (T / 2 ^ (ℓ + 1)) ^ p)
    (hsc : ∫ z, (gbmExact r σ T s₀ ℓ z - Yc z) ^ 2 ∂stdNormalSeq ≤ C * (T / 2 ^ ℓ) ^ p) :
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (Yf z) ≠
        (Set.Ioi K).indicator 1 (Yc (pairAvg z))} ≤
      3 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) ^ (2 / 3 : ℝ) *
        C ^ (1 / 3 : ℝ) *
        (((T / 2 ^ (ℓ + 1)) ^ p) ^ (1 / 3 : ℝ) + ((T / 2 ^ ℓ) ^ p) ^ (1 / 3 : ℝ)) := by
  set ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)
    with hρdef
  set X := gbmExact r σ T s₀ (ℓ + 1) with hXdef
  have hball : ∀ δ, 0 < δ → stdNormalSeq.real {z | |X z - K| ≤ δ} ≤ 2 * ρ * δ := fun δ hδ =>
    gbmExact_smallBall r σ hs₀ hσ hT K (ℓ + 1) hδ
  have hXc : ∀ z, X z = gbmExact r σ T s₀ ℓ (pairAvg z) := fun z =>
    (gbmExact_pairAvg r σ T s₀ ℓ z).symm
  have hint₂ : Integrable (fun z => (X z - Yc (pairAvg z)) ^ 2) stdNormalSeq := by
    simp only [hXc]
    exact (measurePreserving_pairAvg.integrable_comp hintc.aestronglyMeasurable).2 hintc
  have hs₂ : ∫ z, (X z - Yc (pairAvg z)) ^ 2 ∂stdNormalSeq ≤ C * (T / 2 ^ ℓ) ^ p := by
    simp only [hXc]
    rw [integral_comp_of_measurePreserving measurePreserving_pairAvg hintc.aestronglyMeasurable]
    exact hsc
  have hρ' : 0 ≤ 3 * ρ ^ (2 / 3 : ℝ) := by positivity
  have hr : ∀ {m x : ℝ}, m ≤ C * x → 0 ≤ m → 0 ≤ x →
      m ^ (1 / 3 : ℝ) ≤ C ^ (1 / 3 : ℝ) * x ^ (1 / 3 : ℝ) := by
    intro m x hm hm0 hx
    rw [← Real.mul_rpow hC hx]
    exact Real.rpow_le_rpow hm0 hm (by norm_num)
  calc _ ≤ stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X z) ≠
          (Set.Ioi K).indicator 1 (Yf z)} +
        stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X z) ≠
          (Set.Ioi K).indicator 1 (Yc (pairAvg z))} :=
        (measureReal_mono (digital_ne_subset_union X _ _ K)).trans (measureReal_union_le _ _)
    _ ≤ 3 * ρ ^ (2 / 3 : ℝ) * (∫ z, (X z - Yf z) ^ 2 ∂stdNormalSeq) ^ (1 / 3 : ℝ) +
        3 * ρ ^ (2 / 3 : ℝ) * (∫ z, (X z - Yc (pairAvg z)) ^ 2 ∂stdNormalSeq) ^ (1 / 3 : ℝ) :=
        add_le_add (digital_mismatch_le hball hintf).2.2 (digital_mismatch_le hball hint₂).2.2
    _ ≤ 3 * ρ ^ (2 / 3 : ℝ) * (C ^ (1 / 3 : ℝ) * ((T / 2 ^ (ℓ + 1)) ^ p) ^ (1 / 3 : ℝ)) +
        3 * ρ ^ (2 / 3 : ℝ) * (C ^ (1 / 3 : ℝ) * ((T / 2 ^ ℓ) ^ p) ^ (1 / 3 : ℝ)) := by
        gcongr
        · exact hr hsf (integral_nonneg fun _ => sq_nonneg _) (by positivity)
        · exact hr hs₂ (integral_nonneg fun _ => sq_nonneg _) (by positivity)
    _ = _ := by ring

/-! ### §5.2: the natural Milstein estimator of the digital option -/

/-- **The natural Milstein estimator of the digital option for GBM: `V_ℓ = O(h_ℓ^{2/3})`** (Giles
2015, §5.2, p. 35, l. 1526–1532: "discontinuous payoffs pose a challenge to the multilevel Monte
Carlo approach because small differences in the coarse and fine path simulations can lead to an
`O(1)` difference in the payoff function. In the case of a digital option, if we use the natural
multilevel estimator then `P_ℓ−P_{ℓ−1} = O(1)` for an `O(h_ℓ)` fraction of the paths, giving
`V_ℓ = O(h_ℓ)`, and a kurtosis which is `O(h_ℓ^{−1})`").  For `dS = rS dt + σS dW` with `s₀ ≠ 0`,
`σ ≠ 0` and `T > 0`, the correction on level `ℓ + 1` of the digital payoff `H(S_T − K)` for the
Milstein estimator (the payoff of the fine Milstein path minus that of the coarse one driven by the
summed increments, as in `gbm_mil_correction_variance_le`) has variance
`V_{ℓ+1} ≤ 3ρ^{2/3} C(T)^{1/3} (h_{ℓ+1}^{2/3} + h_ℓ^{2/3})`, `h_ℓ = T 2^{−ℓ}`, where `C(T)` is the
constant of the first-order strong error `E[(S_T − Ŝ_ℓ)²] ≤ C(T) h_ℓ²` (`gbmMilStrongConst`,
`gbm_mil_strong_error_level`) and `ρ = e^{(σ² − r)T}/(√(2π) |s₀| |σ| √T)` is the maximum of the
lognormal density of `S_T`.

**Deviation.**  This is `β = 2/3`, not the paper's `V_ℓ = O(h_ℓ)`: the mean-square strong error and
a bounded density give no better exponent, for the variance as well as for the mismatch probability
(`digital_mismatch_exponent_sharp`); the rate `O(h_ℓ)` uses that the error is `O(h_ℓ)` on (almost)
every path, which is not proved here (`L^p` strong errors `O(h_ℓ^p)` give every exponent below `1`
through `digital_mismatch_le_of_moment`: `gbm_mil_digital_rate` in `MlmcLean.GBMStrongLp`). -/
theorem gbm_mil_digital_variance_le (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (ℓ : ℕ) :
    variance (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) stdNormalSeq ≤
      3 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) ^ (2 / 3 : ℝ) *
        gbmMilStrongConst r σ T s₀ ^ (1 / 3 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (2 / 3 : ℝ) + (T / 2 ^ ℓ) ^ (2 / 3 : ℝ)) := by
  have h := gbm_digital_mismatch_le_of_strong r σ hs₀ hσ hT K ℓ
    (gbmMilStrongConst_nonneg r σ s₀ hT.le) (p := 2)
    (integrable_sq_gbm_mil_err r σ T s₀ (ℓ + 1)) (integrable_sq_gbm_mil_err r σ T s₀ ℓ)
    (gbm_mil_strong_error_level r σ s₀ hT.le (ℓ + 1)) (gbm_mil_strong_error_level r σ s₀ hT.le ℓ)
  rw [sq_rpow_one_third (by positivity), sq_rpow_one_third (by positivity)] at h
  exact (variance_digital_le_measureReal (measurable_gbmMil r σ T s₀ (ℓ + 1))
    ((measurable_gbmMil r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable) K).trans h

/-! ### §5.1–§5.2: the fourth moment and the kurtosis of the digital correction -/

/-- **The fourth moment of the digital correction for GBM with Euler–Maruyama: `O(h^{1/3})`**
(Giles 2015, §5.1, p. 33, l. 1441–1446: "with `P_ℓ−P_{ℓ−1} = ±1`. This gives `V_ℓ = O(h^{1/2})`
… Furthermore, `E[(P_ℓ−P_{ℓ−1})⁴] = O(h_ℓ^{1/2})` and so the kurtosis is `O(h_ℓ^{−1/2})`; this
increase in kurtosis is obvious in the middle-right plot").  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0` and the
Euler–Maruyama correction `D = H(Ŝ^f_{ℓ+1} − K) − H(Ŝ^c_ℓ − K)` (coarse path driven by the summed
increments, as in `gbm_digital_variance_le`):
* `E[D⁴] = P(D ≠ 0)` (`D` takes values in `{−1, 0, 1}`),
* `P(D ≠ 0) ≤ B_ℓ = 3ρ^{2/3} C(T)^{1/3} (h_{ℓ+1}^{1/3} + h_ℓ^{1/3})`, `h_ℓ = T 2^{−ℓ}`, with the
  constants of `gbm_digital_variance_le`, so `E[D⁴] = O(h_ℓ^{1/3})`,
* if `P(D ≠ 0) > 0`, the kurtosis `κ = E[D⁴]/E[D²]² = 1/P(D ≠ 0)` (`kurtosis`) is at least
  `B_ℓ⁻¹`, so it grows at least like `h_ℓ^{−1/3}`.

**The kurtosis.**  `kurtosis` is the raw-moment ratio `E[D⁴]/E[D²]²`.  The paper gives this formula
for a random variable "with zero mean" (§3.3, p. 23, l. 1038–1042) and applies it to the ternary
correction with "`E[X] ≈ 0`, and `κ ≈ (p+q)^{−1}`" (l. 1046–1053); here `E[D]` (of the order of the
weak error) is not `0`.  Since `|E[D]| ≤ P(D ≠ 0)`, the kurtosis of the centred correction
`D − E[D]` is `(1 + O(P(D ≠ 0)))/P(D ≠ 0)`, so the two agree to leading order only asymptotically,
as `P(D ≠ 0) → 0`; the statement below is about the raw-moment kurtosis.

**What is not proved.**  The paper's `E[D⁴] = O(h^{1/2})` needs a sharper mismatch bound than the
mean-square one, whose exponent `1/3` cannot be improved (`digital_mismatch_exponent_sharp`).
Strong errors in `L^p`, `E|S_T − Ŝ_ℓ|^p = O(h_ℓ^{p/2})`, give `O(h_ℓ^{p/(2(p+1))})`, hence
every exponent below `1/2`, through `digital_mismatch_le_of_moment`; these `L^p` bounds are proved
for GBM in `MlmcLean.GBMStrongLp` (`gbm_em_digital_rate`; the endpoint is not proved).
`digital_mismatch_le_of_tail` would give `O((h log(1/h))^{1/2})`, but its
hypothesis (Gaussian tails of the error, for all `δ > 0`) fails for GBM, whose Euler–Maruyama error
has lognormal tails, so it is not used.  The kurtosis rate `κ = O(h^{−1/2})` of the paper (an upper
bound on `κ`) needs a lower bound on `P(D ≠ 0)`, which is not proved. -/
theorem gbm_em_digital_fourth_moment_le (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (ℓ : ℕ) :
    ∫ z, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) ^ 4 ∂stdNormalSeq =
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ∧
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} ≤
      3 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) ^ (2 / 3 : ℝ) *
        gbmStrongConst r σ T s₀ ^ (1 / 3 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (1 / 3 : ℝ) + (T / 2 ^ ℓ) ^ (1 / 3 : ℝ)) ∧
    (0 < stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))} →
      (3 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) ^ (2 / 3 : ℝ) *
        gbmStrongConst r σ T s₀ ^ (1 / 3 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (1 / 3 : ℝ) + (T / 2 ^ ℓ) ^ (1 / 3 : ℝ)))⁻¹ ≤
      kurtosis (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ (pairAvg z))) stdNormalSeq) := by
  have hm1 := measurable_gbmEM r σ T s₀ (ℓ + 1)
  have hm0 := (measurable_gbmEM r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable
  have h := gbm_digital_mismatch_le_of_strong r σ hs₀ hσ hT K ℓ
    (gbmStrongConst_nonneg r σ s₀ hT.le) (p := 1)
    (integrable_sq_gbm_err r σ T s₀ (ℓ + 1)) (integrable_sq_gbm_err r σ T s₀ ℓ)
    (by rw [pow_one]; exact gbm_strong_error r σ s₀ hT.le (ℓ + 1))
    (by rw [pow_one]; exact gbm_strong_error r σ s₀ hT.le ℓ)
  rw [pow_one, pow_one] at h
  exact ⟨integral_pow_four_digital_sub hm1 hm0 K, h,
    fun hP => inv_le_kurtosis_digital hm1 hm0 K hP h⟩

/-- **The fourth moment of the natural Milstein correction for GBM: `O(h^{2/3})`** (Giles 2015,
§5.2, p. 35, l. 1529–1532: "if we use the natural multilevel estimator then `P_ℓ−P_{ℓ−1} = O(1)`
for an `O(h_ℓ)` fraction of the paths, giving `V_ℓ = O(h_ℓ)`, and a kurtosis which is
`O(h_ℓ^{−1})`").  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0` and the Milstein correction
`D = H(Ŝ^f_{ℓ+1} − K) − H(Ŝ^c_ℓ − K)` (as in `gbm_mil_digital_variance_le`):
* `E[D⁴] = P(D ≠ 0)`,
* `P(D ≠ 0) ≤ B_ℓ = 3ρ^{2/3} C(T)^{1/3} (h_{ℓ+1}^{2/3} + h_ℓ^{2/3})` (the constants of
  `gbm_mil_digital_variance_le`): the fraction of the paths with `P_ℓ − P_{ℓ−1} = ±1` is
  `O(h_ℓ^{2/3})`,
* if `P(D ≠ 0) > 0`, the kurtosis `κ = 1/P(D ≠ 0)` is at least `B_ℓ⁻¹`, so it grows at least like
  `h_ℓ^{−2/3}`.

As in `gbm_em_digital_fourth_moment_le`, `κ` is the raw-moment kurtosis `kurtosis`; the paper's
definition is for zero-mean `X` (§3.3, l. 1038–1042), and since `|E[D]| ≤ P(D ≠ 0)` the centred
kurtosis agrees with it to leading order only asymptotically, as `P(D ≠ 0) → 0`.

**Deviation.**  The paper's `O(h_ℓ)` fraction (and the kurtosis `O(h_ℓ^{−1})`, which needs a lower
bound on `P(D ≠ 0)`) is not proved; from the mean-square strong error the exponent `2/3` cannot be
improved (`digital_mismatch_exponent_sharp`).  Strong errors in `L^p`, `E|S_T − Ŝ_ℓ|^p = O(h_ℓ^p)`,
give `O(h_ℓ^{p/(p+1)})`, hence every exponent below `1`, through
`digital_mismatch_le_of_moment`; these `L^p` bounds are proved for GBM in `MlmcLean.GBMStrongLp`
(`gbm_mil_digital_rate`; the endpoint is not proved). -/
theorem gbm_mil_digital_fourth_moment_le (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) (ℓ : ℕ) :
    ∫ z, ((Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) ^ 4 ∂stdNormalSeq =
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} ∧
    stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} ≤
      3 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) ^ (2 / 3 : ℝ) *
        gbmMilStrongConst r σ T s₀ ^ (1 / 3 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (2 / 3 : ℝ) + (T / 2 ^ ℓ) ^ (2 / 3 : ℝ)) ∧
    (0 < stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) ≠
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))} →
      (3 * (Real.exp ((σ ^ 2 - r) * T) /
          (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)) ^ (2 / 3 : ℝ) *
        gbmMilStrongConst r σ T s₀ ^ (1 / 3 : ℝ) *
        ((T / 2 ^ (ℓ + 1)) ^ (2 / 3 : ℝ) + (T / 2 ^ ℓ) ^ (2 / 3 : ℝ)))⁻¹ ≤
      kurtosis (fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ (ℓ + 1) z) -
        (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ (pairAvg z))) stdNormalSeq) := by
  have hm1 := measurable_gbmMil r σ T s₀ (ℓ + 1)
  have hm0 := (measurable_gbmMil r σ T s₀ ℓ).comp measurePreserving_pairAvg.measurable
  have h := gbm_digital_mismatch_le_of_strong r σ hs₀ hσ hT K ℓ
    (gbmMilStrongConst_nonneg r σ s₀ hT.le) (p := 2)
    (integrable_sq_gbm_mil_err r σ T s₀ (ℓ + 1)) (integrable_sq_gbm_mil_err r σ T s₀ ℓ)
    (gbm_mil_strong_error_level r σ s₀ hT.le (ℓ + 1)) (gbm_mil_strong_error_level r σ s₀ hT.le ℓ)
  rw [sq_rpow_one_third (by positivity), sq_rpow_one_third (by positivity)] at h
  exact ⟨integral_pow_four_digital_sub hm1 hm0 K, h,
    fun hP => inv_le_kurtosis_digital hm1 hm0 K hP h⟩

/-! ### The exponent `1/3` of the mean-square mismatch bound is sharp -/

/-- The uniform law on `[−1, 1]`, `volume[|[−1, 1]]`, is `½` times Lebesgue measure on
`[−1, 1]`. -/
lemma uniformPM1_apply (s : Set ℝ) :
    volume[|Set.Icc (-1 : ℝ) 1] s = (ENNReal.ofReal 2)⁻¹ * volume (Set.Icc (-1 : ℝ) 1 ∩ s) := by
  rw [cond_apply measurableSet_Icc, Real.volume_Icc]
  norm_num

/-- `P(0 < X < d) = d/2` for `X` uniform on `[−1, 1]` and `0 ≤ d ≤ 1`. -/
lemma uniformPM1_real_Ioo {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    (volume[|Set.Icc (-1 : ℝ) 1]).real (Set.Ioo 0 d) = d / 2 := by
  have e : Set.Icc (-1 : ℝ) 1 ∩ Set.Ioo 0 d = Set.Ioo 0 d :=
    Set.inter_eq_right.2 (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc (by norm_num) hd1))
  rw [measureReal_def, uniformPM1_apply, e, Real.volume_Ioo, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by linarith)]
  ring

/-- The uniform law on `[−1, 1]` has density at most `½`. -/
lemma uniformPM1_le_smul_volume :
    volume[|Set.Icc (-1 : ℝ) 1] ≤ ENNReal.ofReal (1 / 2) • volume := by
  refine Measure.le_iff.2 fun s _ => ?_
  rw [uniformPM1_apply, Measure.smul_apply, smul_eq_mul,
    show ENNReal.ofReal (1 / 2) = (ENNReal.ofReal 2)⁻¹ by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]]
  gcongr
  exact Set.inter_subset_right

/-- **The example behind "sharp": the exponent `1/3` of the mean-square mismatch bound is
attained** (Giles 2015, §5.1, p. 33, l. 1436–1441: "noting that the strong error is
`O(h_ℓ^{1/2})`, and there is a bounded density of paths terminating in the neighbourhood of `K`,
there is therefore an `O(h_ℓ^{1/2})` fraction of the samples with the coarse and fine paths on
either side of the strike"; this is the example of the docstring of `digital_mismatch_le`).  Let
`X` be uniform on `[−1, 1]` (the law `volume[|[−1, 1]]` on `ℝ`, `X(x) = x`), `K = 0`, and, for
`0 < d ≤ 1`, `Y = X − 2d 1_{0<X<d}`.  Then
* the density hypothesis of `digital_mismatch_le` holds with `ρ = ½`: `P(|X| ≤ δ) ≤ 2 · ½ · δ`,
* `E[(X − Y)²] = 2d³`,
* `P(1_{X>0} ≠ 1_{Y>0}) = d/2` (the payoffs differ exactly when `0 < X < d`),
* `V[1_{X>0} − 1_{Y>0}] = d/2 − d²/4` (the correction is `1_{0<X<d}`, a Bernoulli variable with
  parameter `d/2`), and
* `P(1_{X>0} ≠ 1_{Y>0}) = (E[(X − Y)²]/16)^{1/3}`.

So the bound `P ≤ 3ρ^{2/3} E[(X − Y)²]^{1/3}` of `digital_mismatch_le` is attained up to the
constant factor `3 · 2^{2/3} ≈ 4.76` (only the exponent is sharp, not the constant), the variance
is at least half the mismatch probability (`d/2 − d²/4 ≥ d/4` for `d ≤ 1`), and no larger exponent
is possible, for either of them (`digital_mismatch_exponent_sharp`). -/
theorem digital_mismatch_example {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    (∀ δ, 0 < δ → (volume[|Set.Icc (-1 : ℝ) 1]).real {x | |x| ≤ δ} ≤ 2 * (1 / 2) * δ) ∧
    ∫ x, (x - (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)) ^ 2
        ∂volume[|Set.Icc (-1 : ℝ) 1] = 2 * d ^ 3 ∧
    (volume[|Set.Icc (-1 : ℝ) 1]).real {x | (Set.Ioi 0).indicator (1 : ℝ → ℝ) x ≠
        (Set.Ioi 0).indicator 1 (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)} = d / 2 ∧
    variance (fun x => (Set.Ioi 0).indicator (1 : ℝ → ℝ) x -
        (Set.Ioi 0).indicator 1 (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x))
        (volume[|Set.Icc (-1 : ℝ) 1]) = d / 2 - d ^ 2 / 4 ∧
    (volume[|Set.Icc (-1 : ℝ) 1]).real {x | (Set.Ioi 0).indicator (1 : ℝ → ℝ) x ≠
        (Set.Ioi 0).indicator 1 (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)} =
      ((∫ x, (x - (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)) ^ 2
        ∂volume[|Set.Icc (-1 : ℝ) 1]) / 16) ^ (1 / 3 : ℝ) := by
  have hball : ∀ δ, 0 < δ → (volume[|Set.Icc (-1 : ℝ) 1]).real {x | |x| ≤ δ} ≤
      2 * (1 / 2) * δ := by
    intro δ hδ
    have h := measureReal_abs_sub_le_of_map_le (μ := volume[|Set.Icc (-1 : ℝ) 1])
      (X := fun x : ℝ => x) (ρ := 1 / 2) measurable_id (by norm_num)
      (by rw [Measure.map_id']; exact uniformPM1_le_smul_volume) 0 hδ.le
    simpa only [sub_zero] using h
  have hint : ∫ x, (x - (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)) ^ 2
      ∂volume[|Set.Icc (-1 : ℝ) 1] = 2 * d ^ 3 := by
    have e : (fun x : ℝ => (x - (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)) ^ 2) =
        fun x => 4 * d ^ 2 * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x := by
      funext x
      by_cases hx : x ∈ Set.Ioo 0 d
      · rw [Set.indicator_of_mem hx, Pi.one_apply]
        ring
      · rw [Set.indicator_of_notMem hx]
        ring
    rw [e, integral_const_mul, integral_indicator_one measurableSet_Ioo,
      uniformPM1_real_Ioo hd.le hd1]
    ring
  have hset : {x : ℝ | (Set.Ioi 0).indicator (1 : ℝ → ℝ) x ≠
      (Set.Ioi 0).indicator 1 (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)} =
      Set.Ioo 0 d := by
    ext x
    simp only [Set.mem_ofPred_eq]
    by_cases hx : x ∈ Set.Ioo 0 d
    · have hx' := hx
      rw [Set.mem_Ioo] at hx'
      rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one,
        Set.indicator_of_mem (Set.mem_Ioi.2 hx'.1),
        Set.indicator_of_notMem (by rw [Set.mem_Ioi]; linarith)]
      simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true, true_iff]
      exact hx
    · rw [Set.indicator_of_notMem hx, mul_zero, sub_zero]
      simp only [ne_eq, not_true_eq_false, false_iff]
      exact hx
  have hP : (volume[|Set.Icc (-1 : ℝ) 1]).real {x | (Set.Ioi 0).indicator (1 : ℝ → ℝ) x ≠
      (Set.Ioi 0).indicator 1 (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)} = d / 2 := by
    rw [hset, uniformPM1_real_Ioo hd.le hd1]
  -- the correction is the indicator of `(0, d)`, a Bernoulli variable with parameter `d/2`
  have hD : (fun x : ℝ => (Set.Ioi 0).indicator (1 : ℝ → ℝ) x -
      (Set.Ioi 0).indicator 1 (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)) =
      (Set.Ioo 0 d).indicator 1 := by
    funext x
    by_cases hx : x ∈ Set.Ioo 0 d
    · have hx' := hx
      rw [Set.mem_Ioo] at hx'
      rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one,
        Set.indicator_of_mem (Set.mem_Ioi.2 hx'.1),
        Set.indicator_of_notMem (by rw [Set.mem_Ioi]; linarith)]
      simp only [Pi.one_apply, sub_zero]
    · rw [Set.indicator_of_notMem hx, mul_zero, sub_zero, sub_self]
  have hvar : variance (fun x => (Set.Ioi 0).indicator (1 : ℝ → ℝ) x -
      (Set.Ioi 0).indicator 1 (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x))
      (volume[|Set.Icc (-1 : ℝ) 1]) = d / 2 - d ^ 2 / 4 := by
    have hprob : IsProbabilityMeasure (volume[|Set.Icc (-1 : ℝ) 1]) :=
      cond_isProbabilityMeasure_of_finite (by rw [Real.volume_Icc]; norm_num)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hmem : MemLp ((Set.Ioo 0 d).indicator (1 : ℝ → ℝ)) 2 (volume[|Set.Icc (-1 : ℝ) 1]) :=
      memLp_indicator_const 2 measurableSet_Ioo (1 : ℝ) (Or.inr (measure_ne_top _ _))
    have hsq : (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) ^ 2 = (Set.Ioo 0 d).indicator 1 := by
      funext x
      by_cases hx : x ∈ Set.Ioo 0 d
      · simp only [Pi.pow_apply, Set.indicator_of_mem hx, Pi.one_apply, one_pow]
      · simp only [Pi.pow_apply, Set.indicator_of_notMem hx, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow]
    rw [hD, variance_eq_sub hmem, hsq, integral_indicator_one measurableSet_Ioo,
      uniformPM1_real_Ioo hd.le hd1]
    ring
  refine ⟨hball, hint, hP, hvar, ?_⟩
  rw [hP, hint, show 2 * d ^ 3 / 16 = (d / 2) ^ 3 by ring, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num

/-- **No exponent larger than `1/3` in the mean-square mismatch bound, for the mismatch probability
and for the variance** (the word "sharp" for `digital_mismatch_le` and `variance_digital_rate`;
Giles 2015, §5.1, p. 33, l. 1436–1441, and §5.2, p. 35, l. 1529–1531, where the paper's rates
`O(h^{1/2})` and `O(h)` use more than the mean-square strong error).  For every constant `C` and
every exponent `q > 1/3` there is `d ∈ (0, 1]` such that, in the example of
`digital_mismatch_example` (`X` uniform on `[−1, 1]`, density at most `½`, `Y = X − 2d 1_{0<X<d}`,
`K = 0`), both `P(1_{X>0} ≠ 1_{Y>0}) > C E[(X − Y)²]^q` and
`V[1_{X>0} − 1_{Y>0}] > C E[(X − Y)²]^q`.  So neither `P(1_{X>K} ≠ 1_{Y>K}) ≤ C E[(X − Y)²]^q` nor
`V[1_{X>K} − 1_{Y>K}] ≤ C E[(X − Y)²]^q` with `q > 1/3` holds for all `X` with density at most `½`
and all `Y`.  Taking `X` as the exact solution and as the fine approximation (zero error) and `Y`
as the coarse one, the same example shows that the variance rates `h^{1/3}` (Euler–Maruyama,
`gbm_digital_variance_le`, from `E[(S_T − Ŝ_ℓ)²] = O(h_ℓ)`) and `h^{2/3}` (Milstein,
`gbm_mil_digital_variance_le`, from `O(h_ℓ²)`) are the best that the mean-square strong error and
a bounded density give; it says nothing about the actual GBM variances, which are smaller. -/
theorem digital_mismatch_exponent_sharp (C : ℝ) {q : ℝ} (hq : 1 / 3 < q) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      C * (∫ x, (x - (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)) ^ 2
        ∂volume[|Set.Icc (-1 : ℝ) 1]) ^ q <
      (volume[|Set.Icc (-1 : ℝ) 1]).real {x | (Set.Ioi 0).indicator (1 : ℝ → ℝ) x ≠
        (Set.Ioi 0).indicator 1 (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)} ∧
      C * (∫ x, (x - (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x)) ^ 2
        ∂volume[|Set.Icc (-1 : ℝ) 1]) ^ q <
      variance (fun x => (Set.Ioi 0).indicator (1 : ℝ → ℝ) x -
        (Set.Ioi 0).indicator 1 (x - 2 * d * (Set.Ioo 0 d).indicator (1 : ℝ → ℝ) x))
        (volume[|Set.Icc (-1 : ℝ) 1]) := by
  set e := 3 * q - 1 with he
  have he0 : 0 < e := by linarith
  set C' := max C 1 with hC'
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set A := 8 * C' * (2 : ℝ) ^ q with hA
  have hA0 : 0 < A := by positivity
  set d := min 1 (A ^ (-(1 / e))) with hd
  have hd0 : 0 < d := lt_min one_pos (Real.rpow_pos_of_pos hA0 _)
  have hd1 : d ≤ 1 := min_le_left _ _
  refine ⟨d, hd0, hd1, ?_⟩
  obtain ⟨-, hint, hP, hvar, -⟩ := digital_mismatch_example hd0 hd1
  rw [hint, hP, hvar]
  -- `d^e ≤ A⁻¹`, and `(2d³)^q = 2^q d^e d`
  have hde : d ^ e ≤ A⁻¹ := by
    calc d ^ e ≤ (A ^ (-(1 / e))) ^ e :=
          Real.rpow_le_rpow hd0.le (min_le_right _ _) he0.le
      _ = A⁻¹ := by
          rw [← Real.rpow_mul hA0.le, show -(1 / e) * e = -1 by field_simp, Real.rpow_neg_one]
  have hsplit : (2 * d ^ 3) ^ q = (2 : ℝ) ^ q * (d ^ e * d) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hd0.le, ← Real.rpow_add_one hd0.ne']
    congr 2
    rw [he]
    push_cast
    ring
  have hpos : 0 ≤ (2 * d ^ 3) ^ q := by positivity
  have hle : C * (2 * d ^ 3) ^ q ≤ d / 8 :=
    calc C * (2 * d ^ 3) ^ q ≤ C' * (2 * d ^ 3) ^ q :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ = C' * (2 : ℝ) ^ q * d ^ e * d := by rw [hsplit]; ring
      _ ≤ C' * (2 : ℝ) ^ q * A⁻¹ * d := by gcongr
      _ = d / 8 := by
          rw [hA]
          field_simp
  have hdd : d ^ 2 ≤ d := by nlinarith
  exact ⟨by linarith, by linarith⟩

/-! ### §5.2: `E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` for the conditional-expectation payoffs -/

/-- The Milstein path `Ŝ_n` (`milsteinPath`) is a measurable function of the increments, for
measurable coefficients `a`, `b` (Giles 2015, §5.2, l. 1501–1506). -/
lemma measurable_milsteinPath_incr {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (h S₀ : ℝ) (n : ℕ) : Measurable fun z : ℕ → ℝ => milsteinPath a b h S₀ z n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hd := measurable_deriv b
    have hz : Measurable fun z : ℕ → ℝ => z n := measurable_pi_apply n
    show Measurable fun z => milsteinPath a b h S₀ z n + a (milsteinPath a b h S₀ z n) * h +
      b (milsteinPath a b h S₀ z n) * (Real.sqrt h * z n) + 1 / 2 *
        b (milsteinPath a b h S₀ z n) * deriv b (milsteinPath a b h S₀ z n) *
          ((Real.sqrt h * z n) ^ 2 - h)
    fun_prop

/-- The Milstein path after `n` steps depends only on the first `n` increments `Z_0, …, Z_{n−1}`
(Giles 2015, §5.2). -/
lemma milsteinPath_eq_of_eq_lt (a b : ℝ → ℝ) (h S₀ : ℝ) {w w' : ℕ → ℝ} {n : ℕ}
    (hw : ∀ i < n, w i = w' i) : milsteinPath a b h S₀ w n = milsteinPath a b h S₀ w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [milsteinPath_succ, milsteinPath_succ, ih (fun i hi => hw i (by omega)),
      hw n (by omega)]

/-- Under `N(0,1)^{⊗ℕ}`, a measurable function of the increments `Z_0, …, Z_{m−1}` is independent
of `Z_m` (Giles 2015, §5.2, pp. 35–36, l. 1544–1550: "Conditional on the value `Ŝ_{N−1}` … the
numerical approximation for the final value `Ŝ_N` has a Gaussian distribution"). -/
lemma indepFun_incr_of_eq_lt {E : Type*} [MeasurableSpace E] {F : (ℕ → ℝ) → E}
    (hF : Measurable F) {m : ℕ} (hdep : ∀ z z' : ℕ → ℝ, (∀ i < m, z i = z' i) → F z = F z') :
    IndepFun F (fun z => z m) stdNormalSeq := by
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
    (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have h2 := hind.indepFun_finset (range m) {m} (by simp) (fun i => measurable_pi_apply i)
  set ext : (range m → ℝ) → (ℕ → ℝ) := fun y i => if hi : i ∈ range m then y ⟨i, hi⟩ else 0
    with hext
  have hextm : Measurable ext := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases hi : i ∈ range m
    · simp only [hext, hi, dite_true]
      exact measurable_pi_apply _
    · simp only [hext, hi, dite_false]
      exact measurable_const
  have h3 := h2.comp (hF.comp hextm)
    (measurable_pi_apply (⟨m, Finset.mem_singleton_self m⟩ : ({m} : Finset ℕ)))
  refine h3.congr (Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => rfl)
  refine (hdep _ _ fun i hi => ?_).symm
  have hi' : i ∈ range m := Finset.mem_range.2 hi
  simp only [hext, hi', dite_true]

/-- **The coarse path of level `ℓ` with an Euler–Maruyama last step has the law of the fine path of
level `ℓ − 1`: the hypothesis `hlaw` of `integral_condExp_eq_of_map_eq` for the actual
construction** (Giles 2015, §5.2, pp. 35–36, l. 1541–1544: "We start by considering the fine path
simulation, and make a slight change by using the Euler-Maruyama discretisation for the final
timestep, instead of the Milstein discretisation"; l. 1560–1563: "A similar treatment is used for
the coarse path, except that in the final timestep, we re-use the known value of the Brownian
increment for the second last fine timestep, which corresponds to the first half of the final
coarse timestep"; l. 1584–1587: "It is very important in this conditional expectation formulation
that `E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]`").  Take a scalar SDE `dS = a(S) dt + b(S) dW` with measurable
`a`, `b`, the fine timestep `h`, the increments `Z_i ∼ N(0,1)` independent (`stdNormalSeq`) and
`n ∈ ℕ`; on level `ℓ`, `h = h_ℓ = T 2^{−ℓ}` and there are `N = 2^ℓ = 2n + 2` fine timesteps.
* The coarse path of level `ℓ` takes `n` Milstein steps of size `2h` driven by the summed
  increments `ΔW_{2k} + ΔW_{2k+1} = √(2h) (Z_{2k} + Z_{2k+1})/√2` (`pairAvg`), reaching
  `Ŝ^c_{N−2}`, and then the Euler–Maruyama step
  `Ŝ^c_N = Ŝ^c_{N−2} + a(Ŝ^c_{N−2}) 2h + b(Ŝ^c_{N−2}) (ΔW_{N−2} + ΔW_{N−1})` with the two fine
  increments `ΔW_{N−2} = √h Z_{2n}` (re-used) and `ΔW_{N−1} = √h Z_{2n+1}`.
* The fine path of level `ℓ − 1` takes `n` Milstein steps of size `2h` driven by `W_0, W_1, …` and
  then the Euler–Maruyama step with the increment `√(2h) W_n`.

The two terminal values have the same law under `N(0,1)^{⊗ℕ}`: the first is the second evaluated
at `W = pairAvg Z`, and `pairAvg` preserves `N(0,1)^{⊗ℕ}` (`measurePreserving_pairAvg`).

**Deviations.**  The coefficients are autonomous, `a(S)`, `b(S)`: the paper's Milstein scheme
(l. 1501–1506) allows `a(S, t)`, `b(S, t)`, but `milsteinPath` is autonomous (GBM is).  No sign
condition on `h` is assumed: for `h < 0` the statement is degenerate (`√h = √(2h) = 0` in Lean, so
both paths are deterministic and equal); the meaningful case is `h > 0`. -/
theorem map_milsteinEM_coarse_eq_fine {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (h S₀ : ℝ) (n : ℕ) :
    stdNormalSeq.map (fun z => emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
        (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1))) =
      stdNormalSeq.map (fun w => emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
        (Real.sqrt (2 * h) * w n)) := by
  have hM := measurable_milsteinPath_incr ha hb (2 * h) S₀ n
  have hF : Measurable fun w : ℕ → ℝ => emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
      (Real.sqrt (2 * h) * w n) := by
    have hz : Measurable fun w : ℕ → ℝ => w n := measurable_pi_apply n
    unfold emStep
    fun_prop
  have e : (fun z => emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
        (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1))) =
      (fun w => emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
        (Real.sqrt (2 * h) * w n)) ∘ pairAvg := by
    funext z
    have hs : Real.sqrt (2 * h) * pairAvg z n =
        Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) h, pairAvg]
      field_simp
    rw [Function.comp_apply, hs]
  rw [e, ← Measure.map_map hF measurePreserving_pairAvg.measurable,
    measurePreserving_pairAvg.map_eq]

/-- **`E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` for the conditional-expectation payoffs, for any payoff**
(Giles 2015, §5.2, p. 36, l. 1584–1590: "It is very important in this conditional expectation
formulation that `E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` so that the numerical payoff approximation on level
`ℓ−1` has the same expected value regardless of whether it is the coarser or finer of the two
levels. This ensures that the identity in Equation (2.4) is respected so that the telescoping
summation remains valid").  With the paths of `map_milsteinEM_coarse_eq_fine` and any strongly
measurable payoff `g`, the coarse payoff of level `ℓ`,
`P^c_{ℓ−1} = E[g(Ŝ^c_N) | Ŝ^c_{N−2}, ΔW_{N−2}]` (the conditional expectation over the second half
`ΔW_{N−1}` of the last coarse step), and the fine payoff of level `ℓ − 1`,
`P^f_{ℓ−1} = E[g(Ŝ^f) | Ŝ^f_{before the last step}]`, have the same mean
(`integral_condExp_eq_of_map_eq` with `map_milsteinEM_coarse_eq_fine`), and this mean is
`E[g(Ŝ^f)]`, the mean of the payoff of the level-`(ℓ − 1)` path itself (the tower property,
`integral_condExp`).

**Junk cases.**  For integrable `g(Ŝ^f)` (e.g. any bounded `g`, as for the digital payoff) this is
the identity of the paper.  If `g(Ŝ^f)` is not integrable (then neither is `g(Ŝ^c_N)`, which has
the same law), the conditional expectations and `E[g(Ŝ^f)]` are all `0` by Lean's conventions; the
proof does not need integrability, so it is not assumed.  For `h < 0`, `√h = √(2h) = 0` in Lean
and the paths are deterministic (see `map_milsteinEM_coarse_eq_fine`).  The coefficients are
autonomous, `a(S)`, `b(S)` (the paper allows `a(S, t)`, `b(S, t)`). -/
theorem integral_condExp_milsteinEM_coarse_eq_fine {a b : ℝ → ℝ} (ha : Measurable a)
    (hb : Measurable b) (h S₀ : ℝ) (n : ℕ) {g : ℝ → ℝ} (hg : StronglyMeasurable g) :
    ∫ z, (stdNormalSeq[fun z => g (emStep a b (2 * h)
        (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
        (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1))) |
        MeasurableSpace.comap (fun z => (milsteinPath a b (2 * h) S₀ (pairAvg z) n,
          Real.sqrt h * z (2 * n))) inferInstance]) z ∂stdNormalSeq =
      ∫ w, (stdNormalSeq[fun w => g (emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
        (Real.sqrt (2 * h) * w n)) |
        MeasurableSpace.comap (fun w => milsteinPath a b (2 * h) S₀ w n) inferInstance]) w
        ∂stdNormalSeq ∧
    ∫ w, (stdNormalSeq[fun w => g (emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
        (Real.sqrt (2 * h) * w n)) |
        MeasurableSpace.comap (fun w => milsteinPath a b (2 * h) S₀ w n) inferInstance]) w
        ∂stdNormalSeq =
      ∫ w, g (emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n) (Real.sqrt (2 * h) * w n))
        ∂stdNormalSeq := by
  have hMc : Measurable fun z => milsteinPath a b (2 * h) S₀ (pairAvg z) n :=
    (measurable_milsteinPath_incr ha hb (2 * h) S₀ n).comp measurePreserving_pairAvg.measurable
  have hM := measurable_milsteinPath_incr ha hb (2 * h) S₀ n
  have hz : ∀ k, Measurable fun z : ℕ → ℝ => z k := fun k => measurable_pi_apply k
  have hSc : Measurable fun z => emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
      (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1)) := by
    have h1 := hz (2 * n)
    have h2 := hz (2 * n + 1)
    unfold emStep
    fun_prop
  have hSf : Measurable fun w => emStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
      (Real.sqrt (2 * h) * w n) := by
    have h1 := hz n
    unfold emStep
    fun_prop
  have hWc : Measurable fun z : ℕ → ℝ => (milsteinPath a b (2 * h) S₀ (pairAvg z) n,
      Real.sqrt h * z (2 * n)) := hMc.prodMk ((hz (2 * n)).const_mul _)
  exact ⟨integral_condExp_eq_of_map_eq hWc.comap_le hM.comap_le hSc hSf
    (map_milsteinEM_coarse_eq_fine ha hb h S₀ n) hg, integral_condExp hM.comap_le⟩

/-- **The smoothed digital payoffs of §5.2: the `Φ` formulas are the conditional expectations, and
`E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]`** (Giles 2015, §5.2, p. 36, l. 1551–1558: "Thus the fine path payoff
can be taken to be `P^f_ℓ = 25 exp(−rT) Φ((Ŝ^f_{N−1} + a(Ŝ^f_{N−1}) h_ℓ − K)/(b(Ŝ^f_{N−1}) √h_ℓ))`";
l. 1566–1574: "the corresponding coarse path payoff function is
`P^c_{ℓ−1} = 25 exp(−rT) Φ((Ŝ^c_{N−2} + a(Ŝ^c_{N−2}) h_{ℓ−1} + b(Ŝ^c_{N−2}) √h_ℓ − K)/
(b(Ŝ^c_{N−2}) √h_ℓ))`"; l. 1584–1590: "It is very important … that `E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]`").
With the paths of `map_milsteinEM_coarse_eq_fine`, `h > 0`, measurable `a`, `b`, and `b ≠ 0` a.s.
at the fine path of level `ℓ − 1` before its last step (then also at `Ŝ^c_{N−2}`, which is that
path evaluated at `pairAvg Z`):
* `E[1_{Ŝ^c_N > K} | Ŝ^c_{N−2}, ΔW_{N−2}] = Φ((Ŝ^c_{N−2} + a h_{ℓ−1} + b ΔW_{N−2} − K)/(|b| √h_ℓ))`
  a.s., with `h_{ℓ−1} = 2h`, `h_ℓ = h`, `ΔW_{N−2} = √h Z_{2n}` (`digital_smoothing_coarse`; the
  independence of `(Ŝ^c_{N−2}, ΔW_{N−2})` and `Z_{2n+1}` that it assumes is proved here,
  `indepFun_incr_of_eq_lt`);
* `E[1_{Ŝ^f > K} | Ŝ^f_{before}] = Φ((Ŝ^f_{before} + a h_{ℓ−1} − K)/(|b| √h_{ℓ−1}))` a.s.
  (`digital_smoothing`);
* the two `Φ` payoffs have the same mean, so (2.4) holds.

**Deviations.**  The factor `25 e^{−rT}` is omitted; the paper writes `b` for `|b|`; its coarse
formula has `b(Ŝ^c_{N−2}) √h_ℓ` in the numerator where the re-used increment belongs,
`b(Ŝ^c_{N−2}) ΔW_{N−2}` (as corrected in `digital_smoothing_coarse`); `b ≠ 0` a.s. is implicit in
the paper, which divides by `b`; the coefficients are autonomous, `a(S)`, `b(S)` (the paper's
Milstein scheme, l. 1501–1506, allows `a(S, t)`, `b(S, t)`; `milsteinPath` is autonomous, and GBM
is). -/
theorem digital_smoothing_milsteinEM_mean_eq {a b : ℝ → ℝ} (ha : Measurable a)
    (hb : Measurable b) {h : ℝ} (hh : 0 < h) (S₀ K : ℝ) (n : ℕ)
    (hb0 : ∀ᵐ w ∂stdNormalSeq, b (milsteinPath a b (2 * h) S₀ w n) ≠ 0) :
    stdNormalSeq[fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (emStep a b (2 * h)
        (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
        (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1))) |
        MeasurableSpace.comap (fun z => (milsteinPath a b (2 * h) S₀ (pairAvg z) n,
          Real.sqrt h * z (2 * n))) inferInstance] =ᵐ[stdNormalSeq]
      (fun z => cdf (gaussianReal 0 1) ((milsteinPath a b (2 * h) S₀ (pairAvg z) n +
        a (milsteinPath a b (2 * h) S₀ (pairAvg z) n) * (2 * h) +
        b (milsteinPath a b (2 * h) S₀ (pairAvg z) n) * (Real.sqrt h * z (2 * n)) - K) /
        (|b (milsteinPath a b (2 * h) S₀ (pairAvg z) n)| * Real.sqrt h))) ∧
    stdNormalSeq[fun w => (Set.Ioi K).indicator (1 : ℝ → ℝ) (emStep a b (2 * h)
        (milsteinPath a b (2 * h) S₀ w n) (Real.sqrt (2 * h) * w n)) |
        MeasurableSpace.comap (fun w => milsteinPath a b (2 * h) S₀ w n) inferInstance]
        =ᵐ[stdNormalSeq]
      (fun w => cdf (gaussianReal 0 1) ((milsteinPath a b (2 * h) S₀ w n +
        a (milsteinPath a b (2 * h) S₀ w n) * (2 * h) - K) /
        (|b (milsteinPath a b (2 * h) S₀ w n)| * Real.sqrt (2 * h)))) ∧
    ∫ z, cdf (gaussianReal 0 1) ((milsteinPath a b (2 * h) S₀ (pairAvg z) n +
        a (milsteinPath a b (2 * h) S₀ (pairAvg z) n) * (2 * h) +
        b (milsteinPath a b (2 * h) S₀ (pairAvg z) n) * (Real.sqrt h * z (2 * n)) - K) /
        (|b (milsteinPath a b (2 * h) S₀ (pairAvg z) n)| * Real.sqrt h)) ∂stdNormalSeq =
      ∫ w, cdf (gaussianReal 0 1) ((milsteinPath a b (2 * h) S₀ w n +
        a (milsteinPath a b (2 * h) S₀ w n) * (2 * h) - K) /
        (|b (milsteinPath a b (2 * h) S₀ w n)| * Real.sqrt (2 * h))) ∂stdNormalSeq := by
  have hMc : Measurable fun z => milsteinPath a b (2 * h) S₀ (pairAvg z) n :=
    (measurable_milsteinPath_incr ha hb (2 * h) S₀ n).comp measurePreserving_pairAvg.measurable
  have hM := measurable_milsteinPath_incr ha hb (2 * h) S₀ n
  have hz : ∀ k, Measurable fun z : ℕ → ℝ => z k := fun k => measurable_pi_apply k
  have hlaw : ∀ k, stdNormalSeq.map (fun z : ℕ → ℝ => z k) = gaussianReal 0 1 := fun k =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) k).map_eq
  -- the coarse path: `(Ŝ^c_{N−2}, ΔW_{N−2})` is independent of `Z_{2n+1}`
  have hindc : IndepFun (fun z => (milsteinPath a b (2 * h) S₀ (pairAvg z) n,
      Real.sqrt h * z (2 * n))) (fun z => z (2 * n + 1)) stdNormalSeq := by
    refine indepFun_incr_of_eq_lt (hMc.prodMk ((hz (2 * n)).const_mul _)) fun z z' hzz => ?_
    have h1 : milsteinPath a b (2 * h) S₀ (pairAvg z) n =
        milsteinPath a b (2 * h) S₀ (pairAvg z') n :=
      milsteinPath_eq_of_eq_lt a b (2 * h) S₀ fun i hi => by
        rw [pairAvg, pairAvg, hzz (2 * i) (by omega), hzz (2 * i + 1) (by omega)]
    rw [h1, hzz (2 * n) (by omega)]
  have hb0c : ∀ᵐ z ∂stdNormalSeq, b (milsteinPath a b (2 * h) S₀ (pairAvg z) n) ≠ 0 :=
    measurePreserving_pairAvg.quasiMeasurePreserving.ae hb0
  have hc := digital_smoothing_coarse hMc ((hz (2 * n)).const_mul (Real.sqrt h))
    (hz (2 * n + 1)) hindc (hlaw (2 * n + 1)) ha hb hb0c (hc := 2 * h) hh K
  -- the fine path of level `ℓ − 1`: the path before the last step is independent of `W_n`
  have hindf : IndepFun (fun w => milsteinPath a b (2 * h) S₀ w n) (fun w => w n)
      stdNormalSeq :=
    indepFun_incr_of_eq_lt hM fun w w' hww => milsteinPath_eq_of_eq_lt a b (2 * h) S₀ hww
  obtain ⟨hf, -, -⟩ := digital_smoothing hM (hz n) hindf (hlaw n) ha hb hb0
    (by positivity : (0 : ℝ) < 2 * h) K
  have ef : (fun w => (Set.Ioi K).indicator (1 : ℝ → ℝ) (emStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ w n) (Real.sqrt (2 * h) * w n))) =
      fun w => (Set.Ioi K).indicator (1 : ℝ → ℝ) (milsteinPath a b (2 * h) S₀ w n +
        a (milsteinPath a b (2 * h) S₀ w n) * (2 * h) +
        b (milsteinPath a b (2 * h) S₀ w n) * Real.sqrt (2 * h) * w n) := by
    funext w
    rw [emStep, mul_assoc (b _)]
  rw [← ef] at hf
  refine ⟨hc, hf, ?_⟩
  rw [← integral_congr_ae hc, ← integral_congr_ae hf]
  exact (integral_condExp_milsteinEM_coarse_eq_fine ha hb h S₀ n
    ((measurable_one.indicator measurableSet_Ioi).stronglyMeasurable)).1

/-- A nonzero quadratic `c₂x² + c₁x + c₀` (`c₂ ≠ 0`) vanishes on a null set of `N(0,1)`: its zeros
are among the two roots `(±√Δ − c₁)/(2c₂)`. -/
lemma ae_gaussian_quadratic_ne_zero {c₂ c₁ c₀ : ℝ} (hc : c₂ ≠ 0) :
    ∀ᵐ x ∂gaussianReal 0 1, c₂ * (x * x) + c₁ * x + c₀ ≠ 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hsub : {x : ℝ | c₂ * (x * x) + c₁ * x + c₀ = 0} ⊆
      {(Real.sqrt (discrim c₂ c₁ c₀) - c₁) / (2 * c₂),
        (-Real.sqrt (discrim c₂ c₁ c₀) - c₁) / (2 * c₂)} := by
    intro x hx
    have h1 := (quadratic_eq_zero_iff_discrim_eq_sq hc x).1 hx
    have habs : |2 * c₂ * x + c₁| = Real.sqrt (discrim c₂ c₁ c₀) := by
      rw [h1, Real.sqrt_sq_eq_abs]
    have h2c : 2 * c₂ ≠ 0 := mul_ne_zero two_ne_zero hc
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, eq_div_iff h2c, eq_div_iff h2c]
    rcases (abs_eq (Real.sqrt_nonneg _)).1 habs with h2 | h2
    · left
      linarith
    · right
      linarith
  have h0 : gaussianReal 0 1 {x : ℝ | c₂ * (x * x) + c₁ * x + c₀ = 0} = 0 :=
    measure_mono_null hsub ((Set.toFinite _).measure_zero _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
  exact hx

/-- The volatility `σ Ŝ_n` of the Milstein path of GBM vanishes only on a null set, for `s₀ ≠ 0`,
`σ ≠ 0`, `h > 0`: `Ŝ_n = s₀ ∏_{i<n} (1 + rh + σ√h Z_i + ½σ²h(Z_i² − 1))` (`milsteinPath_gbm`), and
each factor is a nonzero quadratic in `Z_i` (Giles 2015, §5.2). -/
lemma ae_gbm_milsteinPath_ne_zero (r σ : ℝ) {s₀ h : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hh : 0 < h) (n : ℕ) :
    ∀ᵐ w ∂stdNormalSeq, σ * milsteinPath (fun S => r * S) (fun S => σ * S) h s₀ w n ≠ 0 := by
  have hq : ∀ᵐ x ∂gaussianReal 0 1, gbmMilFactor r σ h x ≠ 0 := by
    have hc : σ ^ 2 / 2 * Real.sqrt h ^ 2 ≠ 0 := by
      have : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
      positivity
    filter_upwards [ae_gaussian_quadratic_ne_zero (c₁ := σ * Real.sqrt h)
      (c₀ := 1 + r * h - σ ^ 2 * h / 2) hc] with x hx
    rw [gbmMilFactor_eq_quadratic]
    intro h0
    apply hx
    linear_combination h0
  have hall : ∀ᵐ w ∂stdNormalSeq, ∀ i ∈ range n, gbmMilFactor r σ h (w i) ≠ 0 :=
    (eventually_all_finset _).2 fun i _ =>
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i
        ).quasiMeasurePreserving.ae hq
  filter_upwards [hall] with w hw
  rw [milsteinPath_gbm]
  exact mul_ne_zero hσ (mul_ne_zero hs₀ (Finset.prod_ne_zero_iff.2 hw))

/-- **`E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` for the smoothed digital option on GBM** (Giles 2015, §5.2,
p. 36, l. 1584–1590: "It is very important in this conditional expectation formulation that
`E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` … This ensures that the identity in Equation (2.4) is respected so
that the telescoping summation remains valid"; Figure 5.6).  For `dS = rS dt + σS dW`
(`a(S) = rS`, `b(S) = σS`) with `s₀ ≠ 0`, `σ ≠ 0` and fine timestep `h > 0`, the coarse smoothed
payoff `Φ((Ŝ^c_{N−2} + rŜ^c_{N−2} h_{ℓ−1} + σŜ^c_{N−2} ΔW_{N−2} − K)/(|σŜ^c_{N−2}| √h_ℓ))` of
level `ℓ` and the fine smoothed payoff
`Φ((Ŝ^f_{N/2−1} + rŜ^f_{N/2−1} h_{ℓ−1} − K)/(|σŜ^f_{N/2−1}| √h_{ℓ−1}))` of level `ℓ − 1`
(`h_ℓ = h`, `h_{ℓ−1} = 2h`, Milstein paths with an Euler–Maruyama last step, as in
`digital_smoothing_milsteinEM_mean_eq`) have the same mean.  No assumption beyond `s₀ ≠ 0`,
`σ ≠ 0`: the Milstein path of GBM vanishes only on a null set (`ae_gbm_milsteinPath_ne_zero`).
The factor `25 e^{−rT}` is omitted and the coarse formula is the corrected one of
`digital_smoothing_coarse`. -/
theorem gbm_digital_smoothing_mean_eq (r σ : ℝ) {s₀ h : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hh : 0 < h) (K : ℝ) (n : ℕ) :
    ∫ z, cdf (gaussianReal 0 1)
        ((milsteinPath (fun S => r * S) (fun S => σ * S) (2 * h) s₀ (pairAvg z) n +
          r * milsteinPath (fun S => r * S) (fun S => σ * S) (2 * h) s₀ (pairAvg z) n *
            (2 * h) +
          σ * milsteinPath (fun S => r * S) (fun S => σ * S) (2 * h) s₀ (pairAvg z) n *
            (Real.sqrt h * z (2 * n)) - K) /
        (|σ * milsteinPath (fun S => r * S) (fun S => σ * S) (2 * h) s₀ (pairAvg z) n| *
          Real.sqrt h)) ∂stdNormalSeq =
      ∫ w, cdf (gaussianReal 0 1)
        ((milsteinPath (fun S => r * S) (fun S => σ * S) (2 * h) s₀ w n +
          r * milsteinPath (fun S => r * S) (fun S => σ * S) (2 * h) s₀ w n * (2 * h) - K) /
        (|σ * milsteinPath (fun S => r * S) (fun S => σ * S) (2 * h) s₀ w n| *
          Real.sqrt (2 * h))) ∂stdNormalSeq :=
  (digital_smoothing_milsteinEM_mean_eq (measurable_id.const_mul r)
    (measurable_id.const_mul σ) hh s₀ K n
    (ae_gbm_milsteinPath_ne_zero r σ hs₀ hσ (by positivity) n)).2.2

end MLMC
