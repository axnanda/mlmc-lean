import MlmcLean.GBMStrongLp
import MlmcLean.GBMPathDependent

/-!
# The digital and the barrier option for GBM end to end (Giles 2015, §5.1–§5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1, p. 33,
l. 1435–1449 of `docs/giles2015.txt` (the digital option with Euler–Maruyama: "Consequently, this
application has `α = 1`, `β = ½`, `γ = 1`, leading to the MLMC complexity being `O(ε^{−2.5})`"),
Table 5.2 (l. 1424–1434, row "barrier") and l. 1454–1456 ("the barrier is a discontinuous function
of the maximum or minimum"); §5.2, paragraph "Digital options", l. 1525–1532 (the natural Milstein
estimator), l. 1592–1600 (splitting) and p. 38, l. 1635–1636 ("Furthermore, one can revert to
using the Milstein approximation for the final timestep").  Geometric Brownian motion
`dS = rS dt + σS dW`, the exact solution and the schemes driven by the same increments
`Z_i ∼ N(0, 1)` (`stdNormalSeq`), the coarse path of a sample driven by the summed increments
(`pairAvg`), as in `MlmcLean.GBMStrongLp`, `MlmcLean.GBMPathDependent` and `MlmcLean.GBMDigital`.

* **The weak error of the digital option** (condition (i) of Theorem 1).
  `gbm_em_digital_weak_rate`, `gbm_mil_digital_weak_rate`: the probability that the scheme and
  the exact solution end on different sides of the strike, and the weak error
  `|E[H(Ŝ_ℓ − K)] − E[H(S_T − K)]|`, are `≤ C h_ℓ^q` for every `q < ½` (Euler–Maruyama), resp.
  every `q < 1` (Milstein), uniformly in `S_0` and `K`.  The weak error is at most the mismatch
  probability (`abs_integral_digital_sub_le`); the mismatch probability is bounded by the density of
  `S_T` near `K` and a `2m`-th moment of the strong error (`digital_mismatch_le_rpow`), with `m` so
  large that the exponent `κm/(2m + 1)` exceeds `q` (`gbm_digital_mismatch_rate_of_moment`, with
  the `L^{2m}` strong errors `gbm_em_moment_error_level`, `gbm_mil_moment_error_level`).
* **Theorem 1 end to end for the digital option.**  `gbm_em_digital_theorem1`: for every `η > 0`,
  mean square error `< ε²` (with a square-integrable error) at cost `O(ε^{−3−η})`
  (`α = β = q = 1/(2 + η)`, `γ = 1`); `gbm_mil_digital_theorem1`: `O(ε^{−2−η})`
  (`q = 1/(1 + η)`).  `theorem1_pairAvg_of_rate` is Theorem 1 with `α = β = q < γ = 1` for a
  fine/coarse pair coupled by `pairAvg`.  With Euler–Maruyama the loss `η` is removed in
  `MlmcLean.GBMDigitalTheorem1Log`: cost `O(ε⁻³ |log ε|)` (`gbm_em_digital_theorem1_log`).
* **The barrier option at `m` fixed monitoring dates** `t_k = kT/m` (`barrierPayoff`:
  `g(S_T) ∏_{k=1}^m 1_A(S_{t_k})` with `A = (−∞, B]`, up-and-out, or `A = (B, ∞)`, down-and-out,
  and `g` Lipschitz, e.g. the down-and-out call `g(x) = (x − K)⁺`).  `gbm_em_barrier_rate`,
  `gbm_mil_barrier_rate`: the correction variance and the bias are `O(h^q)` for every `q < ½`,
  resp. `q < 1`, from the mismatch probabilities at the dates (a union bound over the dates of the
  marginal small-ball estimates, `gbm_mon_mismatch_rate_of_moment` with the density bound
  `gbmMonExact_smallBall` at every date), the strong error at `t_m`, and the moments of `S_T` of
  every order for the unbounded payoff `g(S_T)` on the mismatch event (a truncation at the level
  `t = h^{−q₀/n}` in place of Hölder's inequality, `mul_le_add_pow_div`, `barrierPayoff_sub_le`,
  `barrier_err_le`, `barrier_err_rate`, `variance_pairAvg_corr_le`, `barrier_rate_of`).
  `gbm_em_barrier_theorem1`, `gbm_mil_barrier_theorem1`: Theorem 1 end to end, cost
  `O(ε^{−3−η})`, resp. `O(ε^{−2−η})`.
* **Splitting with a Milstein final step** (l. 1635–1636).  `map_milstein_coarse_eq_fine`: the
  coarse path of level `ℓ` with a Milstein last step (re-using the known first half of the last
  coarse increment) has the law of the fine path of level `ℓ − 1` (the Milstein analogue of
  `map_milsteinEM_coarse_eq_fine`); `integral_condExp_milstein_coarse_eq_fine`: the
  conditional-expectation payoffs have the same mean; `splitting_milstein_mean_eq`: (2.4) for the
  splitting estimator with `M` sub-samples of the last fine increment
  (`measurePreserving_update_prod`).

**What is not proved.**  The paper's weak order `α = 1` of Euler–Maruyama for the digital option
(a result of Bally–Talay type, not cited in the paper, out of scope here), hence its `O(ε^{−2.5})`:
here `α` is the mismatch rate `q < ½`, which gives `O(ε^{−3−η})`.  The endpoints `q = ½`, `q = 1`
are not proved here, so the costs here carry the loss `η > 0`; Table 5.2's analysis rate
`O(h^{1/2} log h)` (Avikainen) for the Euler–Maruyama variance is proved in
`MlmcLean.GBMDigitalEndpoint` (`gbm_em_digital_endpoint_log`) but not used here.  With it, and
the weak error `O((h log(1/h))^{1/2})` from the mismatch probability, Theorem 1 with logarithmic
factors gives the Euler–Maruyama digital option the cost `O(ε⁻³ |log ε|)`
(`gbm_em_digital_theorem1_log`, `MlmcLean.GBMDigitalTheorem1Log`); the Milstein digital option
and the barrier options keep the loss `η`.  The barrier option of the paper is
continuously monitored; its analysis (Giles, Higham and Mao 2009) and the Milstein barrier row
`O(h^{3/2})` of Table 5.2 (Brownian-bridge estimators) are out of reach here (the Milstein digital
row `O(h^{3/2})`, for the conditional-expectation estimator, is proved up to a logarithmic factor
in `MlmcLean.GBMDigitalCondExpEndpoint`); for the discretely
monitored option with the natural estimators the rates are those of the digital option.  The
variance of the splitting estimator with a Milstein final step
(l. 1597–1600, "the variance is the same, to leading order") is not formalised; with an
Euler–Maruyama final step its rate (the rate of the conditional expectation, not the same variance
to leading order) is in `MlmcLean.GBMDigitalCondExp` (`gbm_digital_split_variance_rate`,
`gbm_digital_split_sqrt_rate`), together with the conditional-expectation estimator itself at cost
`O(ε⁻²)` (`gbm_digital_condExp_theorem1`).

**Hypotheses.**  `σ ≠ 0` is needed in the digital and the barrier statements: for `σ = 0`,
`s₀ = −1`, `r = T = 1` and `K = −e` the Euler–Maruyama (= Milstein) paths are deterministic,
`Ŝ_ℓ = −(1 + 2^{−ℓ})^{2^ℓ} > −e = S_T`, so `H(Ŝ_ℓ − K) = 1 ≠ 0 = H(S_T − K)` on every level and the
mean square error of the estimator of `gbm_em_digital_theorem1` is `1` for every `L` and `N`.  The
digital option's factor `10 e^{−rT}` (l. 1358: "payoff `P(S) ≡ 10 exp(−rT) H(S_T − K)`") is
omitted, as in `MlmcLean.GBMDigital`; `H(S_T − K)` is `1_{S_T > K}`.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### Generic tools -/

/-- `h^a ≤ T^{a−q} h^q` for `0 < h ≤ T` and `q ≤ a` (from the exponent `a` of a level bound to any
`q ≤ a`; Giles 2015, §5.1–§5.2). -/
lemma rpow_le_rpow_sub_mul_rpow {h T a q : ℝ} (hh : 0 < h) (hhT : h ≤ T) (hq : q ≤ a) :
    h ^ a ≤ T ^ (a - q) * h ^ q := by
  calc h ^ a = h ^ q * h ^ (a - q) := by rw [← Real.rpow_add hh, add_sub_cancel]
    _ ≤ h ^ q * T ^ (a - q) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh.le hhT (sub_nonneg.2 hq))
          (Real.rpow_nonneg hh.le _)
    _ = _ := mul_comm _ _

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The digital payoff `1_{X > K}` of a measurable `X` is integrable (it takes values in
`{0, 1}`; Giles 2015, §5.1, p. 33). -/
lemma integrable_digital [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (K : ℝ) :
    Integrable (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω)) μ :=
  Integrable.of_bound (measurable_digital hX K).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rcases digital_eq_zero_or_one K (X ω) with h | h <;> simp [h])

/-- The digital payoff `1_{X > K}` of a measurable `X` is square integrable (Giles 2015, §5.1). -/
lemma memLp_digital [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (K : ℝ) :
    MemLp (fun ω => (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω)) 2 μ :=
  MemLp.of_bound (measurable_digital hX K).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rcases digital_eq_zero_or_one K (X ω) with h | h <;> simp [h])

/-- **The weak error of a digital payoff is at most the mismatch probability** (Giles 2015, §5.1,
p. 33, l. 1436–1441): `|E[1_{Y>K}] − E[1_{X>K}]| ≤ P(1_{X>K} ≠ 1_{Y>K})`, since
`|1_{Y>K} − 1_{X>K}| = (1_{X>K} − 1_{Y>K})²` is the indicator of the mismatch
(`integral_sq_digital_sub`). -/
lemma abs_integral_digital_sub_le [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (K : ℝ) :
    |∫ ω, (Set.Ioi K).indicator (1 : ℝ → ℝ) (Y ω) ∂μ -
        ∫ ω, (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ∂μ| ≤
      μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} := by
  rw [← integral_sub (integrable_digital hY K) (integrable_digital hX K),
    ← integral_sq_digital_sub hX hY K]
  refine abs_integral_le_integral_abs.trans (le_of_eq (integral_congr_ae
    (Eventually.of_forall fun ω => ?_)))
  rcases digital_eq_zero_or_one K (X ω) with h1 | h1 <;>
    rcases digital_eq_zero_or_one K (Y ω) with h2 | h2 <;> simp [h1, h2]

/-- **The mismatch probability at a single level, from a `2m`-th moment bound** (Giles 2015, §5.1,
p. 33, l. 1436–1441: "noting that the strong error is `O(h_ℓ^{1/2})`, and there is a bounded
density of paths terminating in the neighbourhood of `K`, there is therefore an `O(h_ℓ^{1/2})`
fraction of the samples …").  If `X` has density at most `ρ > 0` near `K`, `(X − Y)^{2m}` is
integrable and `E[(X − Y)^{2m}] ≤ B hᵖ` with `0 < h ≤ T`, then for every
`q ≤ p/(2m + 1)`, `P(1_{X>K} ≠ 1_{Y>K}) ≤ 2 (2ρ)^{2m/(2m+1)} B^{1/(2m+1)} T^{p/(2m+1) − q} h^q`
(`digital_mismatch_le_of_moment_balanced`). -/
lemma digital_mismatch_le_rpow [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {K ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ δ, 0 < δ → μ.real {ω | |X ω - K| ≤ δ} ≤ 2 * ρ * δ) {m p : ℕ}
    (hint : Integrable (fun ω => (X ω - Y ω) ^ (2 * m)) μ) {B h T : ℝ} (hB : 0 ≤ B)
    (hh : 0 < h) (hhT : h ≤ T) (hmom : ∫ ω, (X ω - Y ω) ^ (2 * m) ∂μ ≤ B * h ^ p) {q : ℝ}
    (hq : q ≤ (p : ℝ) / (2 * m + 1)) :
    μ.real {ω | (Set.Ioi K).indicator (1 : ℝ → ℝ) (X ω) ≠ (Set.Ioi K).indicator 1 (Y ω)} ≤
      2 * (2 * ρ) ^ (2 * (m : ℝ) / (2 * m + 1)) * B ^ (1 / (2 * m + 1 : ℝ)) *
        T ^ ((p : ℝ) / (2 * m + 1) - q) * h ^ q := by
  have hN : Even (2 * m) := even_two_mul m
  have hint' : Integrable (fun ω => |X ω - Y ω| ^ (2 * m)) μ := by
    simp_rw [hN.pow_abs]
    exact hint
  have h1 := digital_mismatch_le_of_moment_balanced hρ0 hρ hint'
  have hcast1 : ((2 * m : ℕ) : ℝ) / ((2 * m : ℕ) + 1) = 2 * (m : ℝ) / (2 * m + 1) := by
    push_cast
    ring
  have hcast2 : (1 : ℝ) / ((2 * m : ℕ) + 1) = 1 / (2 * m + 1 : ℝ) := by
    push_cast
    ring
  rw [hcast1, hcast2] at h1
  have e1 : ∫ ω, |X ω - Y ω| ^ (2 * m) ∂μ = ∫ ω, (X ω - Y ω) ^ (2 * m) ∂μ := by
    simp_rw [hN.pow_abs]
  rw [e1] at h1
  have hM0 : 0 ≤ ∫ ω, (X ω - Y ω) ^ (2 * m) ∂μ :=
    integral_nonneg fun ω => hN.pow_nonneg _
  have he : (0 : ℝ) ≤ 1 / (2 * m + 1 : ℝ) := by positivity
  have h2 := rpow_le_mul_rpow_of_le_mul_pow hM0 hB hh.le he hmom
  have e2 : (p : ℝ) * (1 / (2 * m + 1 : ℝ)) = (p : ℝ) / (2 * m + 1) := by ring
  rw [e2] at h2
  have h3 := rpow_le_rpow_sub_mul_rpow hh hhT hq
  have hK : 0 ≤ 2 * (2 * ρ) ^ (2 * (m : ℝ) / (2 * m + 1)) := by positivity
  calc _ ≤ _ := h1
    _ ≤ 2 * (2 * ρ) ^ (2 * (m : ℝ) / (2 * m + 1)) *
          (B ^ (1 / (2 * m + 1 : ℝ)) * h ^ ((p : ℝ) / (2 * m + 1))) :=
        mul_le_mul_of_nonneg_left h2 hK
    _ ≤ 2 * (2 * ρ) ^ (2 * (m : ℝ) / (2 * m + 1)) *
          (B ^ (1 / (2 * m + 1 : ℝ)) * (T ^ ((p : ℝ) / (2 * m + 1) - q) * h ^ q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) hK
    _ = _ := by ring

end Generic

/-- For `0 < κ` and `q < κ/2` there is `m ≥ 1` with `q ≤ κ m/(2m + 1)` (the exponent of the
`2m`-th moment bound approaches `κ/2`; Giles 2015, §5.1–§5.2: `κ = 1` for Euler–Maruyama, `κ = 2`
for Milstein). -/
lemma exists_moment_exponent {κ : ℕ} (hκ : 0 < κ) {q : ℝ} (hq : q < κ / 2) :
    ∃ m : ℕ, 0 < m ∧ q ≤ ((κ * m : ℕ) : ℝ) / (2 * m + 1) := by
  have hκ' : (0 : ℝ) < κ := Nat.cast_pos.2 hκ
  have h12 : 0 < (κ : ℝ) - 2 * q := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (q / (κ - 2 * q))
  have hqn : q < n * (κ - 2 * q) := by rwa [div_lt_iff₀ h12] at hn
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  push_cast
  nlinarith

/-- `(T/2^ℓ)^q = T^q 2^{−qℓ}` for `T ≥ 0` (the dyadic step `h_ℓ = T 2^{−ℓ}`, Giles 2015, §2.1). -/
lemma div_two_pow_rpow {T : ℝ} (hT : 0 ≤ T) (q : ℝ) (ℓ : ℕ) :
    (T / 2 ^ ℓ) ^ q = T ^ q * (2 : ℝ) ^ (-(q * (ℓ : ℝ))) := by
  rw [Real.div_rpow hT (by positivity), Real.rpow_neg (by norm_num), div_eq_mul_inv]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]

/-! ### The digital option: the mismatch with the exact solution and the weak error -/

/-- The target `E[1_{S_T > K}]`, computed from the exact solution on any level, is the Gaussian
integral `∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)` (Giles 2015, §5.1, p. 33; the law of the
exact solution does not depend on the level, `map_gbmExact`). -/
lemma integral_digital_gbmExact (r σ T s₀ K : ℝ) (ℓ : ℕ) :
    ∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ z) ∂stdNormalSeq =
      ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1 := by
  rw [integral_comp_gbmExact r σ T s₀ ℓ (measurable_one.indicator (measurableSet_Ioi (a := K)))]
  simp_rw [gbmExact_zero]
  have hF : Measurable fun w : ℝ => (Set.Ioi K).indicator (1 : ℝ → ℝ)
      (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) :=
    (measurable_one.indicator measurableSet_Ioi).comp (by fun_prop)
  exact integral_comp_of_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0) hF.aestronglyMeasurable

/-- **The mismatch between a scheme and the exact solution at the strike, uniformly in `S_0` and
`K`, from `2m`-th moment bounds of the strong error** (Giles 2015, §5.1, p. 33, l. 1436–1441).
Let `σ ≠ 0`, `T > 0`, `κ ≥ 1`, and let `Y s₀ ℓ` be an approximation of `S_T` on level `ℓ`
(`h_ℓ = T 2^{−ℓ}`) that vanishes for `s₀ = 0` and satisfies, for every `m ≥ 1`,
`E[(S_T − Y)^{2m}] ≤ s₀^{2m} B_m h_ℓ^{κm}` (`B_m` independent of `s₀` and `ℓ`).  Then for every
`q < κ/2` there is `C` with `P(1_{S_T > K} ≠ 1_{Y > K}) ≤ C h_ℓ^q` for all `s₀`, `K`, `ℓ`:
`digital_mismatch_le_rpow` with `m` so large that `κm/(2m + 1) ≥ q`
(`exists_moment_exponent`), the lognormal density bound `gbmExact_smallBall`
(`ρ ∝ 1/|s₀|`) and the scaling identity `div_rpow_mul_pow_mul_rpow`. -/
lemma gbm_digital_mismatch_rate_of_moment (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T)
    {κ : ℕ} (hκ : 0 < κ) {Y : ℝ → ℕ → (ℕ → ℝ) → ℝ} (hY0 : ∀ ℓ z, Y 0 ℓ z = 0)
    (hmom : ∀ m : ℕ, 0 < m → ∃ B : ℝ, 0 ≤ B ∧ ∀ (s₀ : ℝ) (ℓ : ℕ),
      Integrable (fun z => (gbmExact r σ T s₀ ℓ z - Y s₀ ℓ z) ^ (2 * m)) stdNormalSeq ∧
      ∫ z, (gbmExact r σ T s₀ ℓ z - Y s₀ ℓ z) ^ (2 * m) ∂stdNormalSeq ≤
        s₀ ^ (2 * m) * B * (T / 2 ^ ℓ) ^ (κ * m))
    {q : ℝ} (hq : q < κ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ K : ℝ) (ℓ : ℕ),
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ z) ≠
        (Set.Ioi K).indicator 1 (Y s₀ ℓ z)} ≤ C * (T / 2 ^ ℓ) ^ q := by
  obtain ⟨m, hm, hqm⟩ := exists_moment_exponent hκ hq
  obtain ⟨B, hB, hYB⟩ := hmom m hm
  set ρ₁ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |σ| * Real.sqrt T)
    with hρ₁
  have hσ' := abs_pos.2 hσ
  have hsT := Real.sqrt_pos.2 hT
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hρ₁0 : 0 < ρ₁ := by positivity
  set C := 2 * (2 * ρ₁) ^ (2 * (m : ℝ) / (2 * m + 1)) * B ^ (1 / (2 * m + 1 : ℝ)) *
    T ^ (((κ * m : ℕ) : ℝ) / (2 * m + 1) - q) with hC
  refine ⟨C, by positivity, fun s₀ K ℓ => ?_⟩
  have hh : 0 < T / 2 ^ ℓ := by positivity
  have hhT : T / 2 ^ ℓ ≤ T := div_le_self hT.le (one_le_pow₀ (by norm_num))
  rcases eq_or_ne s₀ 0 with rfl | hs₀
  · have hset : {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T 0 ℓ z) ≠
        (Set.Ioi K).indicator 1 (Y 0 ℓ z)} = ∅ := by
      ext z
      simp [gbmExact, hY0]
    rw [hset, measureReal_empty]
    positivity
  set ρ := Real.exp ((σ ^ 2 - r) * T) / (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt T)
    with hρ
  have hs : 0 < |s₀| := abs_pos.2 hs₀
  have hρe : 2 * ρ = 2 * ρ₁ / |s₀| := by
    rw [hρ, hρ₁]
    field_simp
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨hint, hle⟩ := hYB s₀ ℓ
  have hsB : 0 ≤ s₀ ^ (2 * m) * B := mul_nonneg ((even_two_mul m).pow_nonneg s₀) hB
  have h := digital_mismatch_le_rpow hρ0
    (fun δ hδ => gbmExact_smallBall r σ hs₀ hσ hT K ℓ hδ) hint hsB hh hhT hle hqm
  have key := div_rpow_mul_pow_mul_rpow (A := 2 * ρ₁) (B := B) (by positivity) hB hs m
  refine h.trans_eq ?_
  rw [hρe, ← (even_two_mul m).pow_abs s₀, hC]
  linear_combination (2 * T ^ (((κ * m : ℕ) : ℝ) / (2 * m + 1) - q) * (T / 2 ^ ℓ) ^ q) * key

/-- **The digital option with Euler–Maruyama: the mismatch with the exact solution and the weak
error are `O(h_ℓ^q)` for every `q < ½`, uniformly in `S_0` and `K`** (Giles 2015, §5.1, p. 33,
l. 1436–1441: "noting that the strong error is `O(h_ℓ^{1/2})`, and there is a bounded density of
paths terminating in the neighbourhood of `K`, there is therefore an `O(h_ℓ^{1/2})` fraction of the
samples …"; condition (i) of Theorem 1, §2.1, p. 6).  For `σ ≠ 0`, `T > 0` and every `q < ½`
there is `C ≥ 0` such that for every `s₀`, `K` and level `ℓ` (`2^ℓ` steps of size
`h_ℓ = T 2^{−ℓ}`): `P(1_{S_T > K} ≠ 1_{Ŝ_ℓ > K}) ≤ C h_ℓ^q` (`S_T` the exact solution driven by
the same increments), and `|E[1_{Ŝ_ℓ > K}] − E[1_{S_T > K}]| ≤ C h_ℓ^q`, with
`E[1_{S_T > K}] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)`.  Proof:
`gbm_digital_mismatch_rate_of_moment` with the `L^{2m}` strong errors `gbm_em_moment_error_level`
(`κ = 1`), and `abs_integral_digital_sub_le`.

**How close to the paper.**  The paper takes `α = 1` for this application (l. 1447–1449:
"this application has `α = 1`, `β = ½`, `γ = 1`"), the weak order one of Euler–Maruyama for the
digital option (a result of Bally–Talay type for non-smooth payoffs, not cited in the paper),
which is out of scope here: the mismatch probability only gives `α = q < ½`.  `σ ≠ 0` is needed
(see `gbm_em_digital_theorem1`). -/
theorem gbm_em_digital_weak_rate (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {q : ℝ}
    (hq : q < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ K : ℝ) (ℓ : ℕ),
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ z) ≠
          (Set.Ioi K).indicator 1 (gbmEM r σ T s₀ ℓ z)} ≤ C * (T / 2 ^ ℓ) ^ q ∧
      |∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ z) ∂stdNormalSeq -
          ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
            (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1| ≤
        C * (T / 2 ^ ℓ) ^ q := by
  have hq' : q < ((1 : ℕ) : ℝ) / 2 := by rw [Nat.cast_one]; exact hq
  obtain ⟨C, hC, h⟩ := gbm_digital_mismatch_rate_of_moment r σ hσ hT one_pos
    (Y := fun s₀ ℓ z => gbmEM r σ T s₀ ℓ z)
    (fun ℓ z => by rw [gbmEM_eq_prod, zero_mul])
    (fun m hm => ⟨gbmEMMomentConst m r σ T 1, gbmEMMomentConst_nonneg m r σ 1 hT.le,
      fun s₀ ℓ => ⟨integrable_gbm_em_err_pow r σ T s₀ (by positivity) m, by
        have h := gbm_em_moment_error_level r σ s₀ hT.le ℓ hm
        rw [gbmEMMomentConst_eq_mul] at h
        rw [one_mul]
        exact h⟩⟩) hq'
  refine ⟨C, hC, fun s₀ K ℓ => ⟨h s₀ K ℓ, ?_⟩⟩
  rw [← integral_digital_gbmExact r σ T s₀ K ℓ]
  exact (abs_integral_digital_sub_le (measurable_gbmExact r σ T s₀ ℓ)
    (measurable_gbmEM r σ T s₀ ℓ) K).trans (h s₀ K ℓ)

/-- **The digital option with Milstein: the mismatch with the exact solution and the weak error
are `O(h_ℓ^q)` for every `q < 1`, uniformly in `S_0` and `K`** (Giles 2015, §5.2, p. 35,
l. 1529–1531: "`P_ℓ − P_{ℓ−1} = O(1)` for an `O(h_ℓ)` fraction of the paths"; condition (i) of
Theorem 1, §2.1, p. 6).  For `σ ≠ 0`, `T > 0` and every `q < 1` there is `C ≥ 0` such that for
every `s₀`, `K` and level `ℓ`: `P(1_{S_T > K} ≠ 1_{Ŝ_ℓ > K}) ≤ C h_ℓ^q` and
`|E[1_{Ŝ_ℓ > K}] − E[1_{S_T > K}]| ≤ C h_ℓ^q`, `Ŝ_ℓ` the Milstein approximation with `2^ℓ` steps.
Proof: as `gbm_em_digital_weak_rate`, with `gbm_mil_moment_error_level` (`κ = 2`).  The weak
order `1` of the Milstein scheme for the digital option is not proved (only every `q < 1`). -/
theorem gbm_mil_digital_weak_rate (r σ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {q : ℝ}
    (hq : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ K : ℝ) (ℓ : ℕ),
      stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ ℓ z) ≠
          (Set.Ioi K).indicator 1 (gbmMil r σ T s₀ ℓ z)} ≤ C * (T / 2 ^ ℓ) ^ q ∧
      |∫ z, (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ ℓ z) ∂stdNormalSeq -
          ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
            (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1| ≤
        C * (T / 2 ^ ℓ) ^ q := by
  have hq' : q < ((2 : ℕ) : ℝ) / 2 := by rw [Nat.cast_two, div_self two_ne_zero]; exact hq
  obtain ⟨C, hC, h⟩ := gbm_digital_mismatch_rate_of_moment r σ hσ hT two_pos
    (Y := fun s₀ ℓ z => gbmMil r σ T s₀ ℓ z)
    (fun ℓ z => by rw [gbmMil_eq_prod, zero_mul])
    (fun m hm => ⟨gbmMilMomentConst m r σ T 1, gbmMilMomentConst_nonneg m r σ 1 hT.le,
      fun s₀ ℓ => ⟨integrable_gbm_mil_err_pow r σ T s₀ (by positivity) m, by
        have h := gbm_mil_moment_error_level r σ s₀ hT.le ℓ hm
        rw [gbmMilMomentConst_eq_mul] at h
        exact h⟩⟩) hq'
  refine ⟨C, hC, fun s₀ K ℓ => ⟨h s₀ K ℓ, ?_⟩⟩
  rw [← integral_digital_gbmExact r σ T s₀ K ℓ]
  exact (abs_integral_digital_sub_le (measurable_gbmExact r σ T s₀ ℓ)
    (measurable_gbmMil r σ T s₀ ℓ) K).trans (h s₀ K ℓ)

/-! ### Theorem 1 with `α = β = q < γ = 1` -/

/-- **Theorem 1 for a fine/coarse estimator coupled by the summed increments, with `α = β = q`,
`γ = 1`** (Giles 2015, §2.1, Theorem 1, p. 6, the case `β < γ`: cost `O(ε^{−2−(γ−β)/α})`, with
(2.4), p. 8).  Let `T > 0`, `0 < q < 1`, `P_ℓ` (`Pf ℓ`) measurable and square integrable
functions of the increments `Z ∼ N(0,1)^{⊗ℕ}`, the coarse payoff `P_ℓ ∘ pairAvg` (so (2.4) holds),
`P` integrable, `|E[P_ℓ] − E[P]| ≤ c₁ h_ℓ^q` and `V[P_{ℓ+1} − P_ℓ ∘ pairAvg] ≤ c₂ h_{ℓ+1}^q` with
`h_ℓ = T 2^{−ℓ}`, independent samples and cost `2^ℓ` per level-`ℓ` sample.  Then there is `c₄ > 0`
such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the error of the
multilevel estimator of `E[P]` is square integrable, its mean square is `< ε²`, and the cost is
`∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε^{−2−(1−q)/q}` (`giles_theorem1_fineCoarse`). -/
lemma theorem1_pairAvg_of_rate {T : ℝ} (hT : 0 < T) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {Pf : ℕ → (ℕ → ℝ) → ℝ} {P : (ℕ → ℝ) → ℝ} (hPfm : ∀ ℓ, Measurable (Pf ℓ))
    (hPf : ∀ ℓ, MemLp (Pf ℓ) 2 stdNormalSeq) (hP : Integrable P stdNormalSeq) {c₁ c₂ : ℝ}
    (h_i : ∀ ℓ : ℕ, |∫ z, Pf ℓ z ∂stdNormalSeq - ∫ z, P z ∂stdNormalSeq| ≤
      c₁ * (T / 2 ^ ℓ) ^ q)
    (h_iii : ∀ ℓ : ℕ, variance (fun z => Pf (ℓ + 1) z - Pf ℓ (pairAvg z)) stdNormalSeq ≤
      c₂ * (T / 2 ^ (ℓ + 1)) ^ q) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf
            (fun ℓ z => Pf ℓ (pairAvg z))) (fun p x => x p) ℓ (N ℓ) x -
            ∫ z, P z ∂stdNormalSeq) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf
            (fun ℓ z => Pf ℓ (pairAvg z))) (fun p x => x p) ℓ (N ℓ) x -
            ∫ z, P z ∂stdNormalSeq) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) <
          ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 - (1 - q) / q) := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hTq : 0 < T ^ q := Real.rpow_pos_of_pos hT q
  have hPcm : ∀ ℓ, Measurable (fun z => Pf ℓ (pairAvg z)) := fun ℓ =>
    (hPfm ℓ).comp measurePreserving_pairAvg.measurable
  have hPc : ∀ ℓ, MemLp (fun z => Pf ℓ (pairAvg z)) 2 stdNormalSeq := fun ℓ =>
    (hPf ℓ).comp_measurePreserving measurePreserving_pairAvg
  have h24 : ∀ ℓ, ∫ z, Pf ℓ z ∂stdNormalSeq = ∫ z, Pf ℓ (pairAvg z) ∂stdNormalSeq := fun ℓ =>
    (integral_comp_of_measurePreserving measurePreserving_pairAvg
      (hPfm ℓ).aestronglyMeasurable).symm
  -- (i): `α = q`
  have hc₁ : 0 < (|c₁| + 1) * T ^ q := by positivity
  have h_i' : ∀ ℓ : ℕ, |∫ z, Pf ℓ z - P z ∂stdNormalSeq| ≤
      (|c₁| + 1) * T ^ q * (2 : ℝ) ^ (-(q * (ℓ : ℝ))) := fun ℓ => by
    rw [integral_sub ((hPf ℓ).integrable one_le_two) hP]
    have h2 : 0 ≤ T ^ q * (2 : ℝ) ^ (-(q * (ℓ : ℝ))) := by positivity
    calc _ ≤ c₁ * (T / 2 ^ ℓ) ^ q := h_i ℓ
      _ = c₁ * (T ^ q * (2 : ℝ) ^ (-(q * (ℓ : ℝ)))) := by rw [div_two_pow_rpow hT.le]
      _ ≤ (|c₁| + 1) * (T ^ q * (2 : ℝ) ^ (-(q * (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c₁]) h2
      _ = _ := by ring
  -- (iii): `β = q`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (Pf 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by
    rw [hV₀]
    exact variance_nonneg _ _
  have hc₂ : 0 < V₀ + (|c₂| + 1) * T ^ q := by positivity
  have h_iii' : ∀ ℓ, variance (fineCoarseDiff Pf (fun ℓ z => Pf ℓ (pairAvg z)) ℓ)
      stdNormalSeq ≤ (V₀ + (|c₂| + 1) * T ^ q) * (2 : ℝ) ^ (-(q * (ℓ : ℝ))) := by
    intro ℓ
    cases ℓ with
    | zero =>
      simp only [fineCoarseDiff, CharP.cast_eq_zero, mul_zero, neg_zero, Real.rpow_zero,
        mul_one]
      rw [← hV₀]
      have : 0 ≤ (|c₂| + 1) * T ^ q := by positivity
      linarith
    | succ ℓ =>
      have h2 : 0 ≤ T ^ q * (2 : ℝ) ^ (-(q * ((ℓ + 1 : ℕ) : ℝ))) := by positivity
      have h3 : 0 ≤ (2 : ℝ) ^ (-(q * ((ℓ + 1 : ℕ) : ℝ))) := by positivity
      calc variance (fineCoarseDiff Pf (fun ℓ z => Pf ℓ (pairAvg z)) (ℓ + 1)) stdNormalSeq
          = variance (fun z => Pf (ℓ + 1) z - Pf ℓ (pairAvg z)) stdNormalSeq := rfl
        _ ≤ c₂ * (T / 2 ^ (ℓ + 1)) ^ q := h_iii ℓ
        _ = c₂ * (T ^ q * (2 : ℝ) ^ (-(q * ((ℓ + 1 : ℕ) : ℝ)))) := by
            rw [div_two_pow_rpow hT.le]
        _ ≤ (|c₂| + 1) * (T ^ q * (2 : ℝ) ^ (-(q * ((ℓ + 1 : ℕ) : ℝ)))) :=
            mul_le_mul_of_nonneg_right (by linarith [le_abs_self c₂]) h2
        _ ≤ _ := by nlinarith [mul_nonneg hV₀0 h3]
  -- (iv): a level-`ℓ` sample costs `2^ℓ`
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ 1 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, one_mul, Real.rpow_natCast]
  have hαβγ : min q 1 / 2 ≤ q := by
    rw [min_eq_left hq1.le]
    linarith
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) P Pf (fun ℓ z => Pf ℓ (pairAvg z))
    (fun p x => x p) (fun ℓ _ _ => (2 : ℝ) ^ ℓ) (fun ℓ => (2 : ℝ) ^ ℓ) (α := q) (β := q)
    (γ := 1) hq0 hq0 one_pos hc₁ hc₂ one_pos hαβγ hω hind hP hPfm hPcm hPf hPc h24
    (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i' h_iii' h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω
    (memLp_fineCoarseDiff hPf hPc) ℓ (N ℓ)).sub (memLp_const _)).integrable_sq, hmse, ?_⟩
  simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul] at hcost
  rw [complexityBound_of_gt hq1 ε] at hcost
  exact hcost

/-- **Theorem 1 end to end for the digital option with Euler–Maruyama: MSE `< ε²` at cost
`O(ε^{−3−η})` for every `η > 0`** (Giles 2015, §5.1, p. 30, l. 1356: "Figure 5.4 illustrates the
problem with discontinuous payoff functions"; p. 33, l. 1447–1449: "Consequently, this application
has `α = 1`, `β = ½`, `γ = 1`, leading to the MLMC complexity being `O(ε^{−2.5})`", with Theorem 1,
§2.1, p. 6, and (2.4)).  For `dS = rS dt + σS dW`, `S_0 = s₀`, `σ ≠ 0`, `T > 0`, any strike `K`
and any `η > 0`: level `ℓ` uses `2^ℓ` Euler–Maruyama steps of size `T 2^{−ℓ}`, the payoff is
`H(Ŝ_ℓ − K) = 1_{Ŝ_ℓ > K}`, the coarse path of a sample is driven by the summed increments, the
samples are independent and a level-`ℓ` sample costs `2^ℓ`.  Then there is `c₄ > 0` such that
for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel estimator of
`E[H(S_T − K)] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)` has a square-integrable error with
mean square `< ε²`, at cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε^{−3−η}`.  No rate is assumed: Theorem 1 with
`α = β = q = 1/(2 + η) < ½`, `γ = 1` (`theorem1_pairAvg_of_rate`; cost
`ε^{−2−(1−q)/q} = ε^{−3−η}`), the weak rate `gbm_em_digital_weak_rate`, the variance rate
`gbm_em_digital_rate` and (2.4) (the coarse path is the fine path of the level below, driven by
`pairAvg`).

**How close to the paper.**  The paper's `O(ε^{−2.5})` uses the weak order `α = 1` of
Euler–Maruyama for the digital option (a result of Bally–Talay type for non-smooth payoffs, not
cited in the paper; a Malliavin-calculus argument that is out of scope here) together with
`β = ½`.  Here `α` is only the mismatch rate `q < ½`, and `β = q < ½` (`gbm_em_digital_rate`; the
endpoint `β = ½` is proved only up to a factor `(log(1/h))^{1/2}`, `gbm_em_digital_endpoint`, which
is not used here), so Theorem 1 gives `ε^{−2−(1−q)/q}`, i.e. `ε^{−3−η}` with `η > 0` arbitrary but
not `0`.  The constant `c₄` depends on `η`.  `gbm_em_digital_theorem1_log`
(`MlmcLean.GBMDigitalTheorem1Log`) removes the loss `η` for the same estimator: with `α` and `β`
equal to `½` up to the factor `(log(1/h))^{1/2}` it gives the cost `O(ε⁻³ |log ε|)`.

**`σ ≠ 0` is needed.**  For `σ = 0`, `s₀ = −1`, `r = T = 1`, the paths are deterministic,
`Ŝ_ℓ = −(1 + 2^{−ℓ})^{2^ℓ} > −e = S_T`, so with `K = −e` the estimator is `H(Ŝ_L − K) = 1` for
every `L` while `E[H(S_T − K)] = 0`: the mean square error is `1` for every choice of `L` and
`N`. -/
theorem gbm_em_digital_theorem1 (r σ s₀ K : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {η : ℝ}
    (hη : 0 < η) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ z))
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ (pairAvg z))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ z))
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ (pairAvg z))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-3 - η) := by
  set q := 1 / (2 + η) with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q < 1 / 2 := by
    rw [hqdef, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨C₁, -, hC₁⟩ := gbm_em_digital_weak_rate r σ hσ hT hq
  obtain ⟨C₂, -, hC₂⟩ := gbm_em_digital_rate r σ hσ hT hq
  obtain ⟨c₄, hc₄, h⟩ := theorem1_pairAvg_of_rate hT hq0 (by linarith)
    (Pf := fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmEM r σ T s₀ ℓ z))
    (P := fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ 0 z))
    (fun ℓ => measurable_digital (measurable_gbmEM r σ T s₀ ℓ) K)
    (fun ℓ => memLp_digital (measurable_gbmEM r σ T s₀ ℓ) K)
    (integrable_digital (measurable_gbmExact r σ T s₀ 0) K) (c₁ := C₁) (c₂ := C₂)
    (fun ℓ => by rw [integral_digital_gbmExact]; exact (hC₁ s₀ K ℓ).2)
    (fun ℓ => (hC₂ s₀ K ℓ).1)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  rw [integral_digital_gbmExact] at hint hmse
  have hexp : -2 - (1 - q) / q = -3 - η := by
    rw [hqdef]
    field_simp
    ring
  rw [hexp] at hcost
  exact ⟨L, N, hN, hint, hmse, hcost⟩

/-- **Theorem 1 end to end for the digital option with the natural Milstein estimator: MSE `< ε²`
at cost `O(ε^{−2−η})` for every `η > 0`** (Giles 2015, §5.2, p. 35, l. 1525–1532: "In the case of
a digital option, if we use the natural multilevel estimator then `P_ℓ−P_{ℓ−1} = O(1)` for an
`O(h_ℓ)` fraction of the paths, giving `V_ℓ = O(h_ℓ)`", with Theorem 1, §2.1, p. 6, and (2.4)).
In the setting of `gbm_em_digital_theorem1` with `2^ℓ` Milstein steps on level `ℓ`: for `σ ≠ 0`,
`T > 0`, any `K` and any `η > 0` there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L`
and `N_ℓ ≥ 1` for which the natural multilevel estimator of `E[H(S_T − K)]` has a
square-integrable error with mean square `< ε²`, at cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε^{−2−η}`.  No rate
is assumed: Theorem 1 with `α = β = q = 1/(1 + η) < 1`, `γ = 1` (cost `ε^{−2−(1−q)/q} = ε^{−2−η}`),
`gbm_mil_digital_weak_rate`, `gbm_mil_digital_rate` and (2.4).

**How close to the paper.**  The paper does not state the complexity of the natural Milstein
estimator; with its `V_ℓ = O(h_ℓ)` (`β = γ = 1`) and the weak order `α = 1` Theorem 1 would give
`O(ε^{−2}(log ε)²)`.  Here `β = q < 1` (the endpoint `β = 1` is not proved,
`gbm_mil_digital_rate`) and `α = q`, which gives `ε^{−2−η}` for every `η > 0`.  `σ ≠ 0` is
needed, as in `gbm_em_digital_theorem1` (for `σ = 0` the Milstein path is the Euler–Maruyama
one). -/
theorem gbm_mil_digital_theorem1 (r σ s₀ K : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {η : ℝ}
    (hη : 0 < η) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ ℓ z))
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ ℓ (pairAvg z))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ ℓ z))
              (fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ ℓ (pairAvg z))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 - η) := by
  set q := 1 / (1 + η) with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q < 1 := by
    rw [hqdef, div_lt_one (by positivity)]
    linarith
  obtain ⟨C₁, -, hC₁⟩ := gbm_mil_digital_weak_rate r σ hσ hT hq
  obtain ⟨C₂, -, hC₂⟩ := gbm_mil_digital_rate r σ hσ hT hq
  obtain ⟨c₄, hc₄, h⟩ := theorem1_pairAvg_of_rate hT hq0 hq
    (Pf := fun ℓ z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmMil r σ T s₀ ℓ z))
    (P := fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ 0 z))
    (fun ℓ => measurable_digital (measurable_gbmMil r σ T s₀ ℓ) K)
    (fun ℓ => memLp_digital (measurable_gbmMil r σ T s₀ ℓ) K)
    (integrable_digital (measurable_gbmExact r σ T s₀ 0) K) (c₁ := C₁) (c₂ := C₂)
    (fun ℓ => by rw [integral_digital_gbmExact]; exact (hC₁ s₀ K ℓ).2)
    (fun ℓ => (hC₂ s₀ K ℓ).1)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  rw [integral_digital_gbmExact] at hint hmse
  have hexp : -2 - (1 - q) / q = -2 - η := by
    rw [hqdef]
    field_simp
    ring
  rw [hexp] at hcost
  exact ⟨L, N, hN, hint, hmse, hcost⟩

/-! ### The barrier option at fixed monitoring dates -/

/-- **The discretely monitored knock-out (barrier) payoff** (Giles 2015, §5.1, p. 33, l. 1454–1456:
"the barrier is a discontinuous function of the maximum or minimum"; Table 5.2, l. 1430, row
"barrier"):
`g(S_{t_m}) ∏_{k=1}^m 1_A(S_{t_k})` of the values `S = (S_{t_0}, S_{t_1}, …)` at the monitoring
dates `t_k = kT/m`.  With `A = (−∞, B]` this is the up-and-out option `g(S_T) 1{max_{1≤k≤m} S_{t_k}
≤ B}`, with `A = (B, ∞)` the down-and-out option `g(S_T) 1{min_{1≤k≤m} S_{t_k} > B}`.  The date
`t_0 = 0`, where `S_0 = s₀` is known, is not monitored. -/
noncomputable def barrierPayoff (g : ℝ → ℝ) (A : Set ℝ) (m : ℕ) (S : ℕ → ℝ) : ℝ :=
  g (S m) * ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (S (k + 1))

/-- `1_{x ≤ B} = 1 − 1_{x > B}` (the up-and-out indicator is a digital payoff; Giles 2015, §5.1). -/
lemma indicator_Iic_eq_one_sub (B x : ℝ) :
    (Set.Iic B).indicator (1 : ℝ → ℝ) x = 1 - (Set.Ioi B).indicator (1 : ℝ → ℝ) x := by
  by_cases hx : x ≤ B
  · rw [Set.indicator_of_mem (Set.mem_Iic.2 hx),
      Set.indicator_of_notMem (fun h => (not_lt.2 hx) (Set.mem_Ioi.1 h))]
    simp
  · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Iic.1 h)),
      Set.indicator_of_mem (Set.mem_Ioi.2 (not_le.1 hx))]
    simp

/-- For `A = (−∞, B]` or `A = (B, ∞)`, the knock-out indicators of `x` and `y` differ only if the
digital payoffs `1_{x > B}`, `1_{y > B}` differ (Giles 2015, §5.1, p. 33). -/
lemma barrier_indicator_ne {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) {x y : ℝ}
    (h : A.indicator (1 : ℝ → ℝ) x ≠ A.indicator 1 y) :
    (Set.Ioi B).indicator (1 : ℝ → ℝ) x ≠ (Set.Ioi B).indicator 1 y := by
  rcases hA with rfl | rfl
  · intro h'
    apply h
    rw [indicator_Iic_eq_one_sub, indicator_Iic_eq_one_sub, h']
  · exact h

/-- The barrier sets `(−∞, B]` and `(B, ∞)` are measurable (the knock-out sets of the barrier
option, Giles 2015, §5.1, p. 33). -/
lemma measurableSet_barrier {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) :
    MeasurableSet A := by
  rcases hA with rfl | rfl
  · exact measurableSet_Iic
  · exact measurableSet_Ioi

/-- The barrier payoff is measurable for a measurable `g` and a measurable `A` (Giles 2015, §5.1,
p. 33). -/
lemma measurable_barrierPayoff {g : ℝ → ℝ} (hg : Measurable g) {A : Set ℝ}
    (hA : MeasurableSet A) (m : ℕ) : Measurable (barrierPayoff g A m) := by
  unfold barrierPayoff
  exact (hg.comp (measurable_pi_apply m)).mul (Finset.measurable_prod _ fun k _ =>
    (measurable_one.indicator hA).comp (measurable_pi_apply (k + 1)))

/-- If two products of knock-out indicators differ, one of the factors differs (the barrier option
is knocked out on one path and not on the other only if the paths are on different sides of the
barrier at some date; Giles 2015, §5.1, p. 33). -/
lemma prod_indicator_ne {A : Set ℝ} {m : ℕ} {a b : ℕ → ℝ}
    (h : ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) ≠
      ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (b (k + 1))) :
    ∃ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) ≠ A.indicator 1 (b (k + 1)) := by
  by_contra hcon
  exact h (Finset.prod_congr rfl fun k hk => not_not.1 fun hne => hcon ⟨k, hk, hne⟩)

/-- A knock-out indicator lies in `[0, 1]` (Giles 2015, §5.1, p. 33). -/
lemma indicator_one_mem_Icc (A : Set ℝ) (x : ℝ) :
    0 ≤ A.indicator (1 : ℝ → ℝ) x ∧ A.indicator (1 : ℝ → ℝ) x ≤ 1 := by
  by_cases hx : x ∈ A
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- For `f ≥ 0`, `0 ≤ D ≤ 1` and `t > 0`, `f D ≤ t D + f^{k+1}/t^k` (if `f ≤ t` the first term
suffices, otherwise `f ≤ f (f/t)^k`).  This truncation at the level `t` takes the place of
Hölder's inequality for the unbounded payoff `g(S_T)` on the event that the knock-out indicators of
the scheme and of the exact solution differ (the barrier option, Giles 2015, §5.1, p. 33). -/
lemma mul_le_add_pow_div {f D t : ℝ} (hf : 0 ≤ f) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (ht : 0 < t)
    (k : ℕ) : f * D ≤ t * D + f ^ (k + 1) / t ^ k := by
  rcases le_or_gt f t with hft | hft
  · have h1 : 0 ≤ f ^ (k + 1) / t ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hft hD0]
  · have h1 : 1 ≤ (f / t) ^ k := one_le_pow₀ ((one_le_div ht).2 hft.le)
    have h2 : f ^ (k + 1) / t ^ k = f * (f / t) ^ k := by
      rw [div_pow, pow_succ, mul_comm (f ^ k) f, mul_div_assoc]
    have h3 : f * D ≤ f := mul_le_of_le_one_right hf hD1
    have h4 : f ≤ f * (f / t) ^ k := le_mul_of_one_le_right hf h1
    have h5 : 0 ≤ t * D := mul_nonneg ht.le hD0
    rw [h2]
    linarith

/-- **The barrier payoff of a path against that of the exact path** (Giles 2015, §5.1, p. 33: the
barrier is "a discontinuous function"; the argument for the digital option, l. 1436–1441, at every
monitoring date).  For `g` with `|g(x) − g(y)| ≤ K_g |x − y|` (not necessarily bounded),
`A = (−∞, B]` or `(B, ∞)`, `t > 0` and `n ∈ ℕ`, with `S = ∑_{k<m} (1_{x_{k+1}>B} − 1_{a_{k+1}>B})²`
(the number of dates at which the digital payoffs of `a` and `x` differ):
`|Φ(a) − Φ(x)| ≤ K_g |x_m − a_m| + t S + g(x_m)^{2n+2}/t^{2n+1}` and
`(Φ(a) − Φ(x))² ≤ 2K_g² (x_m − a_m)² + 2(t S + g(x_m)^{2n+2}/tⁿ)`.  Write
`Φ(a) − Φ(x) = (g(a_m) − g(x_m)) Π_a + g(x_m)(Π_a − Π_x)` with `Π ∈ [0, 1]`; `Π_a ≠ Π_x` only if
the indicators differ at some date (`prod_indicator_ne`, `barrier_indicator_ne`), and
`|g(x_m)| 1{Π_a ≠ Π_x}` is bounded by `mul_le_add_pow_div`. -/
lemma barrierPayoff_sub_le {g : ℝ → ℝ} {Kg : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) (m n : ℕ) {t : ℝ} (ht : 0 < t)
    (a x : ℕ → ℝ) :
    |barrierPayoff g A m a - barrierPayoff g A m x| ≤ Kg * |x m - a m| +
        (t * ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (x (k + 1)) -
          (Set.Ioi B).indicator 1 (a (k + 1))) ^ 2 + g (x m) ^ (2 * (n + 1)) / t ^ (2 * n + 1)) ∧
    (barrierPayoff g A m a - barrierPayoff g A m x) ^ 2 ≤ 2 * Kg ^ 2 * (x m - a m) ^ 2 +
        2 * (t * ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (x (k + 1)) -
          (Set.Ioi B).indicator 1 (a (k + 1))) ^ 2 + g (x m) ^ (2 * (n + 1)) / t ^ n) := by
  set P := ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) with hP
  set Q := ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (x (k + 1)) with hQ
  set S := ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (x (k + 1)) -
    (Set.Ioi B).indicator 1 (a (k + 1))) ^ 2 with hS
  have hKg : 0 ≤ Kg := (continuous_of_abs_sub_le hg).1
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun k _ => (indicator_one_mem_Icc A _).1
  have hP1 : P ≤ 1 := Finset.prod_le_one (fun k _ => (indicator_one_mem_Icc A _).1)
    fun k _ => (indicator_one_mem_Icc A _).2
  have hQ0 : 0 ≤ Q := Finset.prod_nonneg fun k _ => (indicator_one_mem_Icc A _).1
  have hQ1 : Q ≤ 1 := Finset.prod_le_one (fun k _ => (indicator_one_mem_Icc A _).1)
    fun k _ => (indicator_one_mem_Icc A _).2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  -- `|P − Q| ≤ I ≤ S` for some `I ∈ [0, 1]`
  obtain ⟨I, hI0, hI1, hPQ, hIS⟩ : ∃ I : ℝ, 0 ≤ I ∧ I ≤ 1 ∧ |P - Q| ≤ I ∧ I ≤ S := by
    by_cases hpq : P = Q
    · exact ⟨0, le_rfl, zero_le_one, by rw [hpq, sub_self, abs_zero], hS0⟩
    · refine ⟨1, zero_le_one, le_rfl, abs_le.2 ⟨by linarith, by linarith⟩, ?_⟩
      obtain ⟨k, hk, hne⟩ := prod_indicator_ne hpq
      have hne' := barrier_indicator_ne hA (Ne.symm hne)
      have h1 : ((Set.Ioi B).indicator (1 : ℝ → ℝ) (x (k + 1)) -
          (Set.Ioi B).indicator 1 (a (k + 1))) ^ 2 = 1 := by
        rcases digital_eq_zero_or_one B (x (k + 1)) with h1 | h1 <;>
          rcases digital_eq_zero_or_one B (a (k + 1)) with h2 | h2 <;>
          rw [h1, h2] at hne' ⊢ <;> first | exact absurd rfl hne' | norm_num
      rw [← h1]
      exact Finset.single_le_sum (f := fun k => ((Set.Ioi B).indicator (1 : ℝ → ℝ) (x (k + 1)) -
        (Set.Ioi B).indicator 1 (a (k + 1))) ^ 2) (fun i _ => sq_nonneg _) hk
  have e : barrierPayoff g A m a - barrierPayoff g A m x =
      (g (a m) - g (x m)) * P + g (x m) * (P - Q) := by
    simp only [barrierPayoff, hP, hQ]
    ring
  have hu : |(g (a m) - g (x m)) * P| ≤ Kg * |x m - a m| := by
    rw [abs_mul, abs_of_nonneg hP0, abs_sub_comm (x m)]
    calc |g (a m) - g (x m)| * P ≤ Kg * |a m - x m| * 1 :=
          mul_le_mul (hg _ _) hP1 hP0 (mul_nonneg hKg (abs_nonneg _))
      _ = _ := mul_one _
  have hv : |g (x m) * (P - Q)| ≤ t * S + g (x m) ^ (2 * (n + 1)) / t ^ (2 * n + 1) := by
    have h := mul_le_add_pow_div (abs_nonneg (g (x m))) hI0 hI1 ht (2 * n + 1)
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, (even_two_mul (n + 1)).pow_abs] at h
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hPQ (abs_nonneg (g (x m))),
      mul_le_mul_of_nonneg_left hIS ht.le]
  have hv2 : (g (x m) * (P - Q)) ^ 2 ≤ t * S + g (x m) ^ (2 * (n + 1)) / t ^ n := by
    have h := mul_le_add_pow_div (sq_nonneg (g (x m))) hI0 hI1 ht n
    rw [← pow_mul] at h
    have hPQ2 : (P - Q) ^ 2 ≤ I := by
      rw [← sq_abs]
      nlinarith [mul_le_mul hPQ hPQ (abs_nonneg _) hI0, mul_le_mul_of_nonneg_left hI1 hI0]
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hPQ2 (sq_nonneg (g (x m))),
      mul_le_mul_of_nonneg_left hIS ht.le]
  rw [e]
  constructor
  · calc |(g (a m) - g (x m)) * P + g (x m) * (P - Q)|
        ≤ |(g (a m) - g (x m)) * P| + |g (x m) * (P - Q)| := abs_add_le _ _
      _ ≤ _ := add_le_add hu hv
  · have h1 : ((g (a m) - g (x m)) * P) ^ 2 ≤ Kg ^ 2 * (x m - a m) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hu 2
      rwa [sq_abs, mul_pow Kg, sq_abs] at this
    nlinarith [sq_nonneg ((g (a m) - g (x m)) * P - g (x m) * (P - Q))]

/-- `|Φ(a)| ≤ |g(a_m)|` for the barrier payoff `Φ`, whose knock-out factor lies in `[0, 1]`
(Giles 2015, §5.1, p. 33). -/
lemma abs_barrierPayoff_le (g : ℝ → ℝ) (A : Set ℝ) (m : ℕ) (a : ℕ → ℝ) :
    |barrierPayoff g A m a| ≤ |g (a m)| := by
  have hP0 : 0 ≤ ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) :=
    Finset.prod_nonneg fun k _ => (indicator_one_mem_Icc A _).1
  have hP1 : ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) ≤ 1 :=
    Finset.prod_le_one (fun k _ => (indicator_one_mem_Icc A _).1)
      fun k _ => (indicator_one_mem_Icc A _).2
  rw [barrierPayoff, abs_mul, abs_of_nonneg hP0]
  exact mul_le_of_le_one_right (abs_nonneg _) hP1

/-- `|g(y)| ≤ |g(0)| + K_g |y|` for a Lipschitz `g` (the linear growth of the payoff, e.g. of the
call `(y − K)⁺`; Giles 2015, §5.1, p. 33). -/
lemma abs_le_of_lipschitz {g : ℝ → ℝ} {Kg : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (y : ℝ) : |g y| ≤ |g 0| + Kg * |y| := by
  have h1 := hg y 0
  rw [sub_zero] at h1
  have h2 := abs_sub_abs_le_abs_sub (g y) (g 0)
  linarith

/-- The barrier payoff of a measurable path whose value at `t_m` is square integrable is square
integrable when `g` is Lipschitz (`|Φ(a)| ≤ |g(a_m)| ≤ |g(0)| + K_g |a_m|`; Giles 2015, §5.1,
p. 33). -/
lemma memLp_barrierPayoff {g : ℝ → ℝ} {Kg : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    {A : Set ℝ} (hA : MeasurableSet A) (m : ℕ) {W : (ℕ → ℝ) → ℕ → ℝ} (hW : Measurable W)
    (hW2 : MemLp (fun z => W z m) 2 stdNormalSeq) :
    MemLp (fun z => barrierPayoff g A m (W z)) 2 stdNormalSeq := by
  have hgc := (continuous_of_abs_sub_le hg).2
  have hKg := (continuous_of_abs_sub_le hg).1
  refine ((memLp_const |g 0|).add (hW2.norm.const_mul Kg)).of_le
    ((measurable_barrierPayoff hgc.measurable hA m).comp hW).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  have h0 : 0 ≤ |g 0| + Kg * |W z m| := add_nonneg (abs_nonneg _) (mul_nonneg hKg (abs_nonneg _))
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg h0]
  exact (abs_barrierPayoff_le g A m (W z)).trans (abs_le_of_lipschitz hg _)

/-- `g(X)^{2N}` is integrable if `X^{2N}` is and `g` is Lipschitz (`|g(x)| ≤ |g(0)| + K_g |x|` and
`(a + b)^{2N} ≤ 2^{2N−1}(a^{2N} + b^{2N})`; the moments of the payoff `g(S_T)`, Giles 2015, §5.1,
p. 33). -/
lemma integrable_lipschitz_pow {g : ℝ → ℝ} {Kg : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    {X : (ℕ → ℝ) → ℝ} (hX : Measurable X) (N : ℕ)
    (hXN : Integrable (fun z => X z ^ (2 * N)) stdNormalSeq) :
    Integrable (fun z => g (X z) ^ (2 * N)) stdNormalSeq := by
  have hgc := (continuous_of_abs_sub_le hg).2
  have hKg := (continuous_of_abs_sub_le hg).1
  refine (((integrable_const (|g 0| ^ (2 * N))).add (hXN.const_mul (Kg ^ (2 * N)))).const_mul
    (2 ^ (2 * N - 1))).mono' ((hgc.measurable.comp hX).pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  calc |g (X z)| ^ (2 * N) ≤ (|g 0| + Kg * |X z|) ^ (2 * N) :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_le_of_lipschitz hg _) _
    _ ≤ 2 ^ (2 * N - 1) * (|g 0| ^ (2 * N) + (Kg * |X z|) ^ (2 * N)) :=
        add_pow_le (abs_nonneg _) (mul_nonneg hKg (abs_nonneg _)) _
    _ = 2 ^ (2 * N - 1) * (|g 0| ^ (2 * N) + Kg ^ (2 * N) * X z ^ (2 * N)) := by
        rw [mul_pow, (even_two_mul N).pow_abs (X z)]

/-- The exact solution at a monitoring date has moments of every order: `(S_{t_k})^N` is integrable
(a product of `k 2^j` independent lognormal factors, `gbmMonExact_eq_prod`; Giles 2015, §5.1). -/
lemma integrable_gbmMonExact_pow (r σ T s₀ : ℝ) (m j k N : ℕ) :
    Integrable (fun z => gbmMonExact r σ T s₀ m j z k ^ N) stdNormalSeq := by
  have e : (fun z => gbmMonExact r σ T s₀ m j z k ^ N) = fun z => s₀ ^ N *
      (∏ i ∈ range (k * 2 ^ j), gbmExpFactor r σ (T / (m * 2 ^ j)) (z i)) ^ N :=
    funext fun z => by rw [gbmMonExact_eq_prod, mul_pow]
  rw [e]
  exact (integrable_prod_range_pow (measurable_gbmExpFactor r σ _)
    (integrable_gbmExpFactor_pow r σ _ N) _).const_mul _

/-- The law of `∑_{i<n} Z_i` under `N(0,1)^{⊗ℕ}` is `N(0, n)` (the Brownian value
`W_{t_n} = √h ∑_{i<n} Z_i`, Giles 2015, §5.1). -/
lemma map_sum_stdNormalSeq (n : ℕ) :
    stdNormalSeq.map (fun z : ℕ → ℝ => ∑ i ∈ range n, z i) = gaussianReal 0 n := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, gaussianReal_zero_var]
    rw [Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
    have hind : IndepFun (fun z : ℕ → ℝ => ∑ i ∈ range n, z i) (fun z => z n) stdNormalSeq :=
      indepFun_incr_of_eq_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
        fun z z' h => Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.1 hi)
    have h1 : stdNormalSeq.map (fun z : ℕ → ℝ => z n) = gaussianReal 0 1 :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) n).map_eq
    have e : (fun z : ℕ → ℝ => ∑ i ∈ range (n + 1), z i) =
        (fun z : ℕ → ℝ => ∑ i ∈ range n, z i) + (fun z => z n) := by
      funext z
      simp only [Finset.sum_range_succ, Pi.add_apply]
    rw [e, gaussianReal_add_gaussianReal_of_indepFun hind ih h1, add_zero, Nat.cast_succ]

/-- **The density bound at a monitoring date** (Giles 2015, §5.1, p. 33, l. 1437–1438: "there is a
bounded density of paths terminating in the neighbourhood of `K`", at every date).  For `s₀ ≠ 0`,
`σ ≠ 0`, `T > 0`, `m ≥ 1` and a date `t_k = kT/m` with `1 ≤ k ≤ m`, the exact solution `S_{t_k}`
(`gbmMonExact`, on any level `j`) satisfies `P(|S_{t_k} − B| ≤ δ) ≤ 2ρδ` with
`ρ = e^{|σ² − r| T}/(√(2π) |s₀| |σ| √(T/m))`, a bound for the lognormal density of `S_{t_k}` that
does not depend on `k` (`map_sum_stdNormalSeq`, `map_lognormal_le_smul_volume`). -/
lemma gbmMonExact_smallBall (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    {m : ℕ} (hm : 0 < m) (j : ℕ) {k : ℕ} (hk : 0 < k) (hkm : k ≤ m) (B : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    stdNormalSeq.real {z | |gbmMonExact r σ T s₀ m j z k - B| ≤ δ} ≤
      2 * (Real.exp (|σ ^ 2 - r| * T) /
        (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt (T / m))) * δ := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set h := T / (m * 2 ^ j) with hhdef
  set n := k * 2 ^ j with hndef
  set t := (k : ℝ) * (T / m) with htdef
  have hh : 0 < h := by positivity
  have hn : (0 : ℝ) < n := by
    rw [hndef]
    push_cast
    have : (0 : ℝ) < k := Nat.cast_pos.2 hk
    positivity
  have hnh : (n : ℝ) * h = t := monDate_eq T m j k
  have ht : T / m ≤ t := by
    rw [htdef]
    exact le_mul_of_one_le_left (by positivity) (Nat.one_le_cast.2 hk)
  have htT : t ≤ T := (monDate_mem_Icc hT.le hkm).2
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  set s := σ * (Real.sqrt h * Real.sqrt n) with hsdef
  have hs : s ≠ 0 :=
    mul_ne_zero hσ (mul_ne_zero (Real.sqrt_pos.2 hh).ne' (Real.sqrt_pos.2 hn).ne')
  have hs2 : s ^ 2 = σ ^ 2 * t := by
    rw [hsdef, mul_pow, mul_pow, Real.sq_sqrt hh.le, Real.sq_sqrt hn.le, ← hnh]
    ring
  have habs : |s| = |σ| * Real.sqrt t := by
    rw [hsdef, abs_mul, abs_of_pos (mul_pos (Real.sqrt_pos.2 hh) (Real.sqrt_pos.2 hn)),
      ← Real.sqrt_mul hh.le, mul_comm h, hnh]
  set μ₀ := (r - σ ^ 2 / 2) * t with hμ₀
  have hS : Measurable fun z : ℕ → ℝ => ∑ i ∈ range n, z i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hlaw : stdNormalSeq.map (fun z => gbmMonExact r σ T s₀ m j z k) =
      (gaussianReal 0 1).map (fun u => s₀ * Real.exp (μ₀ + s * u)) := by
    have e1 : (fun z => gbmMonExact r σ T s₀ m j z k) =
        (fun x => s₀ * Real.exp (μ₀ + σ * (Real.sqrt h * x))) ∘
          (fun z : ℕ → ℝ => ∑ i ∈ range n, z i) := rfl
    have e2 : (gaussianReal 0 1).map (fun u => Real.sqrt n * u) = gaussianReal 0 n := by
      rw [gaussianReal_map_const_mul, mul_zero]
      congr 1
      apply NNReal.eq
      simp [Real.sq_sqrt hn.le]
    have e3 : (fun u => s₀ * Real.exp (μ₀ + s * u)) =
        (fun x => s₀ * Real.exp (μ₀ + σ * (Real.sqrt h * x))) ∘
          (fun u => Real.sqrt n * u) := by
      funext u
      simp only [Function.comp_apply, hsdef]
      ring_nf
    rw [e1, ← Measure.map_map (by fun_prop) hS, map_sum_stdNormalSeq, e3,
      ← Measure.map_map (by fun_prop) (by fun_prop), e2]
  have hmap := map_lognormal_le_smul_volume (μ₀ := μ₀) hs₀ hs
  rw [← hlaw] at hmap
  have hρ0 : 0 ≤ Real.exp (s ^ 2 / 2 - μ₀) / (Real.sqrt (2 * Real.pi) * |s₀| * |s|) := by
    positivity
  have hXm : Measurable fun z => gbmMonExact r σ T s₀ m j z k :=
    (measurable_pi_apply k).comp (measurable_memLp_gbmMonExact r σ T s₀ m j).1
  have h1 := measureReal_abs_sub_le_of_map_le hXm hρ0 hmap B hδ.le
  refine h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ two_pos.le) hδ.le)
  rw [hs2, habs]
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs₀' := abs_pos.2 hs₀
  have hσ' := abs_pos.2 hσ
  refine div_le_div₀ (by positivity) (Real.exp_le_exp.2 ?_) (by positivity) ?_
  · have e4 : σ ^ 2 * t / 2 - μ₀ = (σ ^ 2 - r) * t := by
      rw [hμ₀]
      ring
    rw [e4]
    calc (σ ^ 2 - r) * t ≤ |σ ^ 2 - r| * t := mul_le_mul_of_nonneg_right (le_abs_self _) ht0.le
      _ ≤ |σ ^ 2 - r| * T := mul_le_mul_of_nonneg_left htT (abs_nonneg _)
  · have h5 := Real.sqrt_le_sqrt ht
    have h2 : 0 ≤ Real.sqrt (2 * Real.pi) * |s₀| * |σ| := by positivity
    calc Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt (T / m)
        ≤ Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt t := mul_le_mul_of_nonneg_left h5 h2
      _ = _ := by ring

section BarrierAbstract

variable {g : ℝ → ℝ} {Kg : ℝ} {A : Set ℝ} {B : ℝ} {m : ℕ}

/-- **The mean square and the mean absolute error of the barrier payoff of an approximation**
(Giles 2015, §5.1, p. 33, l. 1436–1441 at every monitoring date).  Let `X` (exact) and `Y`
(approximate) be measurable paths with `X_{t_m}`, `Y_{t_m}` square integrable,
`g(X_{t_m})^{2n+2}` integrable, `t > 0`, and `p_k = P(1_{X_{t_{k+1}} > B} ≠ 1_{Y_{t_{k+1}} > B})`.
Then, with `G = E[g(X_{t_m})^{2n+2}]`,
`E[(Φ(Y) − Φ(X))²] ≤ 2K_g² E[(X_{t_m} − Y_{t_m})²] + 2(t ∑_{k<m} p_k + G/tⁿ)` and
`E|Φ(Y) − Φ(X)| ≤ K_g √(E[(X_{t_m} − Y_{t_m})²]) + t ∑_{k<m} p_k + G/t^{2n+1}`
(`barrierPayoff_sub_le`, `integral_sq_digital_sub`).  The truncation level `t` takes the place of
Hölder's inequality `E[g(X)² 1_{mismatch}] ≤ ‖g(X)‖²_{2p} P(mismatch)^{1−1/p}` for unbounded `g`. -/
lemma barrier_err_le (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hA : A = Set.Iic B ∨ A = Set.Ioi B) {X Y : (ℕ → ℝ) → ℕ → ℝ} (hXm : Measurable X)
    (hYm : Measurable Y) (hX : MemLp (fun z => X z m) 2 stdNormalSeq)
    (hY : MemLp (fun z => Y z m) 2 stdNormalSeq) (n : ℕ)
    (hG : Integrable (fun z => g (X z m) ^ (2 * (n + 1))) stdNormalSeq) {t : ℝ} (ht : 0 < t) :
    ∫ z, (barrierPayoff g A m (Y z) - barrierPayoff g A m (X z)) ^ 2 ∂stdNormalSeq ≤
      2 * Kg ^ 2 * ∫ z, (X z m - Y z m) ^ 2 ∂stdNormalSeq +
        2 * (t * ∑ k ∈ range m, stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
          (X z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y z (k + 1))} +
          (∫ z, g (X z m) ^ (2 * (n + 1)) ∂stdNormalSeq) / t ^ n) ∧
    ∫ z, |barrierPayoff g A m (Y z) - barrierPayoff g A m (X z)| ∂stdNormalSeq ≤
      Kg * Real.sqrt (∫ z, (X z m - Y z m) ^ 2 ∂stdNormalSeq) +
        (t * ∑ k ∈ range m, stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
          (X z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y z (k + 1))} +
          (∫ z, g (X z m) ^ (2 * (n + 1)) ∂stdNormalSeq) / t ^ (2 * n + 1)) := by
  have hKg := (continuous_of_abs_sub_le hg).1
  have hXk : ∀ k, Measurable fun z => X z k := fun k => (measurable_pi_apply k).comp hXm
  have hYk : ∀ k, Measurable fun z => Y z k := fun k => (measurable_pi_apply k).comp hYm
  -- the number of dates with a digital mismatch
  have hDk : ∀ k, Integrable (fun z => ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X z (k + 1)) -
      (Set.Ioi B).indicator 1 (Y z (k + 1))) ^ 2) stdNormalSeq := fun k =>
    ((memLp_digital (hXk (k + 1)) B).sub (memLp_digital (hYk (k + 1)) B)).integrable_sq
  have hS : Integrable (fun z => ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X z (k + 1)) - (Set.Ioi B).indicator 1 (Y z (k + 1))) ^ 2) stdNormalSeq :=
    integrable_finsetSum _ fun k _ => hDk k
  have hSint : ∫ z, ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X z (k + 1)) -
      (Set.Ioi B).indicator 1 (Y z (k + 1))) ^ 2 ∂stdNormalSeq =
      ∑ k ∈ range m, stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
          (X z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y z (k + 1))} := by
    rw [integral_finsetSum _ fun k _ => hDk k]
    exact Finset.sum_congr rfl fun k _ => integral_sq_digital_sub (hXk (k + 1)) (hYk (k + 1)) B
  have hD : MemLp (fun z => X z m - Y z m) 2 stdNormalSeq := hX.sub hY
  have hD2 : Integrable (fun z => (X z m - Y z m) ^ 2) stdNormalSeq := hD.integrable_sq
  have hDabs : Integrable (fun z => |X z m - Y z m|) stdNormalSeq :=
    (hD.integrable one_le_two).abs
  have hSt : Integrable (fun z => t * ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X z (k + 1)) - (Set.Ioi B).indicator 1 (Y z (k + 1))) ^ 2) stdNormalSeq := hS.const_mul t
  have hGt : ∀ c : ℝ, Integrable (fun z => g (X z m) ^ (2 * (n + 1)) / c) stdNormalSeq :=
    fun c => hG.div_const c
  have hSG : ∀ c : ℝ, Integrable (fun z => t * ∑ k ∈ range m, ((Set.Ioi B).indicator
      (1 : ℝ → ℝ) (X z (k + 1)) - (Set.Ioi B).indicator 1 (Y z (k + 1))) ^ 2 +
      g (X z m) ^ (2 * (n + 1)) / c) stdNormalSeq := fun c => hSt.add (hGt c)
  have hSGi : ∀ c : ℝ, ∫ z, (t * ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X z (k + 1)) - (Set.Ioi B).indicator 1 (Y z (k + 1))) ^ 2 +
      g (X z m) ^ (2 * (n + 1)) / c) ∂stdNormalSeq =
      t * ∑ k ∈ range m, stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
          (X z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y z (k + 1))} +
        (∫ z, g (X z m) ^ (2 * (n + 1)) ∂stdNormalSeq) / c := fun c => by
    rw [integral_add hSt (hGt c), integral_const_mul, integral_div, hSint]
  constructor
  · have hR1 : Integrable (fun z => 2 * Kg ^ 2 * (X z m - Y z m) ^ 2) stdNormalSeq :=
      hD2.const_mul _
    have hR2 : Integrable (fun z => 2 * (t * ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ)
        (X z (k + 1)) - (Set.Ioi B).indicator 1 (Y z (k + 1))) ^ 2 +
        g (X z m) ^ (2 * (n + 1)) / t ^ n)) stdNormalSeq := (hSG _).const_mul 2
    have hR : Integrable (fun z => 2 * Kg ^ 2 * (X z m - Y z m) ^ 2 +
        2 * (t * ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X z (k + 1)) -
          (Set.Ioi B).indicator 1 (Y z (k + 1))) ^ 2 + g (X z m) ^ (2 * (n + 1)) / t ^ n))
        stdNormalSeq := hR1.add hR2
    refine (integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hR
      (Eventually.of_forall fun z => (barrierPayoff_sub_le hg hA m n ht (Y z) (X z)).2)).trans
      (le_of_eq ?_)
    rw [integral_add hR1 hR2, integral_const_mul, integral_const_mul, hSGi]
  · have hR1 : Integrable (fun z => Kg * |X z m - Y z m|) stdNormalSeq := hDabs.const_mul _
    have hR : Integrable (fun z => Kg * |X z m - Y z m| +
        (t * ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X z (k + 1)) -
          (Set.Ioi B).indicator 1 (Y z (k + 1))) ^ 2 +
          g (X z m) ^ (2 * (n + 1)) / t ^ (2 * n + 1))) stdNormalSeq := hR1.add (hSG _)
    refine (integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hR
      (Eventually.of_forall fun z => (barrierPayoff_sub_le hg hA m n ht (Y z) (X z)).1)).trans ?_
    rw [integral_add hR1 (hSG _), integral_const_mul, hSGi]
    have habs : ∫ z, |X z m - Y z m| ∂stdNormalSeq ≤
        Real.sqrt (∫ z, (X z m - Y z m) ^ 2 ∂stdNormalSeq) := by
      have h1 := sq_integral_le_integral_sq_of_memLp (X := fun z => |X z m - Y z m|) hD.norm
      simp only [sq_abs] at h1
      exact (le_abs_self _).trans (Real.abs_le_sqrt h1)
    linarith [mul_le_mul_of_nonneg_left habs hKg]

/-- **`V_ℓ ≤ 2(E[(P̂_ℓ − P)²] + E[(P̂_{ℓ−1} − P)²])` for a fine/coarse pair coupled by `pairAvg`**
(Giles 2015, §5.1, p. 29: "`V_ℓ ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`").  For level-consistent exact
paths `X_j` (`X_j ∘ pairAvg = X_{j+1}`), approximations `Y_j` and a measurable `Φ` with `Φ(X_j)`,
`Φ(Y_j)` square integrable, the correction `Φ(Y_{j+1}) − Φ(Y_j ∘ pairAvg)` is square integrable
with variance at most `2E[(Φ(Y_{j+1}) − Φ(X_{j+1}))²] + 2E[(Φ(Y_j) − Φ(X_j))²]`
(`measurePreserving_pairAvg`). -/
lemma variance_pairAvg_corr_le {Φ : (ℕ → ℝ) → ℝ} {X Y : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    (hX : ∀ j, MemLp (fun z => Φ (X j z)) 2 stdNormalSeq)
    (hY : ∀ j, MemLp (fun z => Φ (Y j z)) 2 stdNormalSeq)
    (hpair : ∀ j z, X j (pairAvg z) = X (j + 1) z) (j : ℕ) :
    MemLp (fun z => Φ (Y (j + 1) z) - Φ (Y j (pairAvg z))) 2 stdNormalSeq ∧
    variance (fun z => Φ (Y (j + 1) z) - Φ (Y j (pairAvg z))) stdNormalSeq ≤
      2 * ∫ z, (Φ (Y (j + 1) z) - Φ (X (j + 1) z)) ^ 2 ∂stdNormalSeq +
        2 * ∫ z, (Φ (Y j z) - Φ (X j z)) ^ 2 ∂stdNormalSeq := by
  have hpm := measurePreserving_pairAvg
  have hYc : MemLp (fun z => Φ (Y j (pairAvg z))) 2 stdNormalSeq :=
    (hY j).comp_measurePreserving hpm
  have hXc : MemLp (fun z => Φ (X j (pairAvg z))) 2 stdNormalSeq :=
    (hX j).comp_measurePreserving hpm
  refine ⟨(hY (j + 1)).sub hYc, ?_⟩
  refine (variance_le_expectation_sq ((hY (j + 1)).sub hYc).aestronglyMeasurable).trans ?_
  simp only [Pi.pow_apply]
  have h1 : Integrable (fun z => (Φ (Y (j + 1) z) - Φ (X (j + 1) z)) ^ 2) stdNormalSeq :=
    ((hY (j + 1)).sub (hX (j + 1))).integrable_sq
  have h0 : Integrable (fun z => (Φ (Y j z) - Φ (X j z)) ^ 2) stdNormalSeq :=
    ((hY j).sub (hX j)).integrable_sq
  have h0c : Integrable (fun z => (Φ (Y j (pairAvg z)) - Φ (X j (pairAvg z))) ^ 2)
      stdNormalSeq :=
    (hYc.sub hXc).integrable_sq
  have hpt : ∀ z, (Φ (Y (j + 1) z) - Φ (Y j (pairAvg z))) ^ 2 ≤
      2 * (Φ (Y (j + 1) z) - Φ (X (j + 1) z)) ^ 2 +
        2 * (Φ (Y j (pairAvg z)) - Φ (X j (pairAvg z))) ^ 2 := fun z => by
    rw [hpair j z]
    nlinarith [sq_nonneg (Φ (Y (j + 1) z) + Φ (Y j (pairAvg z)) - 2 * Φ (X (j + 1) z))]
  have hR : Integrable (fun z => 2 * (Φ (Y (j + 1) z) - Φ (X (j + 1) z)) ^ 2 +
      2 * (Φ (Y j (pairAvg z)) - Φ (X j (pairAvg z))) ^ 2) stdNormalSeq :=
    (h1.const_mul 2).add (h0c.const_mul 2)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hR
    (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_add (h1.const_mul 2) (h0c.const_mul 2), integral_const_mul, integral_const_mul,
    integral_comp_of_measurePreserving hpm h0.aestronglyMeasurable]

/-- `G/(h^{−a})^k = G h^{ak}` for `h > 0` (the truncation level `t = h^{−a}` of `barrier_err_le`;
Giles 2015, §5.1). -/
lemma div_rpow_neg_pow {h : ℝ} (hh : 0 < h) (G a : ℝ) (k : ℕ) :
    G / (h ^ (-a)) ^ k = G * h ^ (a * k) := by
  rw [← Real.rpow_mul_natCast hh.le, neg_mul, Real.rpow_neg hh.le, div_inv_eq_mul]

/-- **The barrier payoff error at one level, at the rate `h^{q₀}`** (Giles 2015, §5.1, p. 33,
Table 5.2, row "barrier").  In the setting of `barrier_err_le`, let `0 < h ≤ T`,
`E[(X_{t_m} − Y_{t_m})²] ≤ E h^κ`, `p_k ≤ C h^{q₁}` at the dates, `n ≥ 1`, `0 ≤ q₀ ≤ κ/2` and
`q₀ (n + 1) ≤ q₁ n`.  Then `E[(Φ(Y) − Φ(X))²] ≤ D₁ h^{q₀}` and `E|Φ(Y) − Φ(X)| ≤ D₂ h^{q₀}` with
`D₁ = 2K_g² E T^{κ−q₀} + 2(m C T^{q₁−q₀/n−q₀} + G)` and
`D₂ = K_g √E T^{κ/2−q₀} + m C T^{q₁−q₀/n−q₀} + G T^{q₀(2n+1)/n−q₀}`, `G = E[g(X_{t_m})^{2n+2}]`:
`barrier_err_le` with the truncation level `t = h^{−q₀/n}`, so that `t h^{q₁} = h^{q₁−q₀/n}`,
`G/tⁿ = G h^{q₀}` and `G/t^{2n+1} = G h^{q₀(2n+1)/n}` (`div_rpow_neg_pow`), and
`rpow_le_rpow_sub_mul_rpow`. -/
lemma barrier_err_rate (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hA : A = Set.Iic B ∨ A = Set.Ioi B) {X Y : (ℕ → ℝ) → ℕ → ℝ} (hXm : Measurable X)
    (hYm : Measurable Y) (hX : MemLp (fun z => X z m) 2 stdNormalSeq)
    (hY : MemLp (fun z => Y z m) 2 stdNormalSeq) {n : ℕ} (hn : 0 < n)
    (hG : Integrable (fun z => g (X z m) ^ (2 * (n + 1))) stdNormalSeq) {h T : ℝ} (hh : 0 < h)
    (hhT : h ≤ T) {κ : ℕ} {E C q₀ q₁ : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) (hq₀ : 0 ≤ q₀)
    (hq₀κ : q₀ ≤ κ / 2) (hq₀₁ : q₀ * (n + 1) ≤ q₁ * n)
    (hs2 : ∫ z, (X z m - Y z m) ^ 2 ∂stdNormalSeq ≤ E * h ^ κ)
    (hmis : ∀ k, k < m → stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y z (k + 1))} ≤ C * h ^ q₁) :
    ∫ z, (barrierPayoff g A m (Y z) - barrierPayoff g A m (X z)) ^ 2 ∂stdNormalSeq ≤
      (2 * Kg ^ 2 * E * T ^ ((κ : ℝ) - q₀) + 2 * (m * C * T ^ (q₁ - q₀ / n - q₀) +
        ∫ z, g (X z m) ^ (2 * (n + 1)) ∂stdNormalSeq)) * h ^ q₀ ∧
    ∫ z, |barrierPayoff g A m (Y z) - barrierPayoff g A m (X z)| ∂stdNormalSeq ≤
      (Kg * Real.sqrt E * T ^ ((κ : ℝ) / 2 - q₀) + m * C * T ^ (q₁ - q₀ / n - q₀) +
        (∫ z, g (X z m) ^ (2 * (n + 1)) ∂stdNormalSeq) *
          T ^ (q₀ / n * ((2 * n + 1 : ℕ) : ℝ) - q₀)) * h ^ q₀ := by
  have hKg := (continuous_of_abs_sub_le hg).1
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set G := ∫ z, g (X z m) ^ (2 * (n + 1)) ∂stdNormalSeq with hGdef
  have hG0 : 0 ≤ G := integral_nonneg fun z => (even_two_mul (n + 1)).pow_nonneg _
  have ht : 0 < h ^ (-(q₀ / n)) := Real.rpow_pos_of_pos hh _
  obtain ⟨h1, h2⟩ := barrier_err_le hg hA hXm hYm hX hY n hG ht
  -- the exponents
  have hq₁ : q₀ ≤ q₁ - q₀ / n := by
    have : q₀ / n ≤ q₁ - q₀ := by
      rw [div_le_iff₀ hn']
      linarith
    linarith
  have hq2 : q₀ ≤ q₀ / n * ((2 * n + 1 : ℕ) : ℝ) := by
    have e : q₀ / n * ((2 * n + 1 : ℕ) : ℝ) = 2 * q₀ + q₀ / n := by
      push_cast
      field_simp
    rw [e]
    have : 0 ≤ q₀ / n := div_nonneg hq₀ hn'.le
    linarith
  have hκ : q₀ ≤ (κ : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) κ]
  have hhq : 0 ≤ h ^ q₀ := Real.rpow_nonneg hh.le _
  -- the mismatch term
  have hsum : ∑ k ∈ range m, stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y z (k + 1))} ≤ m * (C * h ^ q₁) := by
    calc _ ≤ ∑ _k ∈ range m, C * h ^ q₁ :=
          Finset.sum_le_sum fun k hk => hmis k (Finset.mem_range.1 hk)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htm : h ^ (-(q₀ / n)) * (m * (C * h ^ q₁)) ≤
      m * C * T ^ (q₁ - q₀ / n - q₀) * h ^ q₀ := by
    have e : h ^ (-(q₀ / n)) * (m * (C * h ^ q₁)) = m * C * h ^ (q₁ - q₀ / n) := by
      rw [show q₁ - q₀ / n = -(q₀ / n) + q₁ by ring, Real.rpow_add hh]
      ring
    rw [e, mul_assoc (m * C)]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_sub_mul_rpow hh hhT hq₁) (by positivity)
  have hmt : h ^ (-(q₀ / n)) * ∑ k ∈ range m, stdNormalSeq.real {z | (Set.Ioi B).indicator
      (1 : ℝ → ℝ) (X z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y z (k + 1))} ≤
      m * C * T ^ (q₁ - q₀ / n - q₀) * h ^ q₀ :=
    (mul_le_mul_of_nonneg_left hsum ht.le).trans htm
  -- the moment term
  have hGn : G / (h ^ (-(q₀ / n))) ^ n = G * h ^ q₀ := by
    rw [div_rpow_neg_pow hh, div_mul_cancel₀ q₀ hn'.ne']
  have hGn2 : G / (h ^ (-(q₀ / n))) ^ (2 * n + 1) ≤
      G * T ^ (q₀ / n * ((2 * n + 1 : ℕ) : ℝ) - q₀) * h ^ q₀ := by
    rw [div_rpow_neg_pow hh, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_sub_mul_rpow hh hhT hq2) hG0
  -- the strong error at `t_m`
  have hE2 : E * h ^ κ ≤ E * T ^ ((κ : ℝ) - q₀) * h ^ q₀ := by
    rw [mul_assoc, ← Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_sub_mul_rpow hh hhT hκ) hE
  have hsq : Real.sqrt (∫ z, (X z m - Y z m) ^ 2 ∂stdNormalSeq) ≤
      Real.sqrt E * T ^ ((κ : ℝ) / 2 - q₀) * h ^ q₀ := by
    have e : Real.sqrt (E * h ^ κ) = Real.sqrt E * h ^ ((κ : ℝ) / 2) := by
      rw [Real.sqrt_mul hE, Real.sqrt_eq_rpow (h ^ κ), ← Real.rpow_natCast,
        ← Real.rpow_mul hh.le]
      ring_nf
    calc _ ≤ Real.sqrt (E * h ^ κ) := Real.sqrt_le_sqrt hs2
      _ = Real.sqrt E * h ^ ((κ : ℝ) / 2) := e
      _ ≤ Real.sqrt E * (T ^ ((κ : ℝ) / 2 - q₀) * h ^ q₀) :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow_sub_mul_rpow hh hhT hq₀κ)
            (Real.sqrt_nonneg _)
      _ = _ := by ring
  constructor
  · have a1 : 2 * Kg ^ 2 * ∫ z, (X z m - Y z m) ^ 2 ∂stdNormalSeq ≤
        2 * Kg ^ 2 * (E * T ^ ((κ : ℝ) - q₀) * h ^ q₀) :=
      mul_le_mul_of_nonneg_left (hs2.trans hE2) (by positivity)
    calc _ ≤ _ := h1
      _ ≤ 2 * Kg ^ 2 * (E * T ^ ((κ : ℝ) - q₀) * h ^ q₀) +
          2 * (m * C * T ^ (q₁ - q₀ / n - q₀) * h ^ q₀ + G * h ^ q₀) := by
        rw [hGn]
        linarith
      _ = _ := by ring
  · have a1 : Kg * Real.sqrt (∫ z, (X z m - Y z m) ^ 2 ∂stdNormalSeq) ≤
        Kg * (Real.sqrt E * T ^ ((κ : ℝ) / 2 - q₀) * h ^ q₀) :=
      mul_le_mul_of_nonneg_left hsq hKg
    calc _ ≤ _ := h2
      _ ≤ Kg * (Real.sqrt E * T ^ ((κ : ℝ) / 2 - q₀) * h ^ q₀) +
          (m * C * T ^ (q₁ - q₀ / n - q₀) * h ^ q₀ +
            G * T ^ (q₀ / n * ((2 * n + 1 : ℕ) : ℝ) - q₀) * h ^ q₀) := by
        linarith
      _ = _ := by ring

/-- **The barrier rates from the strong error and the mismatch rate** (Giles 2015, §5.1–§5.2,
Table 5.2, row "barrier").  Let `X_j` be level-consistent exact paths (`X_j ∘ pairAvg = X_{j+1}`)
and `Y_j` approximations, measurable and square integrable at `t_m`, `h_j = T 2^{−j}` (`T > 0`),
`E[(X_{j,t_m} − Y_{j,t_m})²] ≤ E h_j^κ`, mismatch probabilities `≤ C h_j^{q₁}` at the dates, and
`g(X_{j,t_m})^{2n+2}` integrable with `n ≥ 1`.  If `q ≤ q₀`, `0 ≤ q₀ ≤ κ/2` and
`q₀ (n + 1) ≤ q₁ n`, there is `C'` such that the correction `Φ(Y_{j+1}) − Φ(Y_j ∘ pairAvg)` is
square integrable with variance `≤ C' h_{j+1}^q` and `|E[Φ(Y_j)] − E[Φ(X_0)]| ≤ C' h_j^q`
(`barrier_err_rate`, `variance_pairAvg_corr_le`; the law of `X_j` does not depend on `j`,
`integral_comp_monLevel`; `dyadic_rpow_add_le`, `rpow_le_rpow_sub_mul_rpow`). -/
lemma barrier_rate_of (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hA : A = Set.Iic B ∨ A = Set.Ioi B) {X Y : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    (hXm : ∀ j, Measurable (X j)) (hYm : ∀ j, Measurable (Y j))
    (hX : ∀ j, MemLp (fun z => X j z m) 2 stdNormalSeq)
    (hY : ∀ j, MemLp (fun z => Y j z m) 2 stdNormalSeq)
    (hpair : ∀ j z, X j (pairAvg z) = X (j + 1) z) {n : ℕ} (hn : 0 < n)
    (hG : ∀ j, Integrable (fun z => g (X j z m) ^ (2 * (n + 1))) stdNormalSeq)
    {T : ℝ} (hT : 0 < T) {κ : ℕ} {E C q q₀ q₁ : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) (hqq₀ : q ≤ q₀)
    (hq₀ : 0 ≤ q₀) (hq₀κ : q₀ ≤ κ / 2) (hq₀₁ : q₀ * (n + 1) ≤ q₁ * n)
    (hs2 : ∀ j, ∫ z, (X j z m - Y j z m) ^ 2 ∂stdNormalSeq ≤ E * (T / 2 ^ j) ^ κ)
    (hmis : ∀ j k, k < m → stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X j z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y j z (k + 1))} ≤ C * (T / 2 ^ j) ^ q₁) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ j : ℕ,
      MemLp (fun z => barrierPayoff g A m (Y (j + 1) z) -
          barrierPayoff g A m (Y j (pairAvg z))) 2 stdNormalSeq ∧
      variance (fun z => barrierPayoff g A m (Y (j + 1) z) -
          barrierPayoff g A m (Y j (pairAvg z))) stdNormalSeq ≤ C' * (T / 2 ^ (j + 1)) ^ q ∧
      |∫ z, barrierPayoff g A m (Y j z) ∂stdNormalSeq -
          ∫ z, barrierPayoff g A m (X 0 z) ∂stdNormalSeq| ≤ C' * (T / 2 ^ j) ^ q := by
  have hKg := (continuous_of_abs_sub_le hg).1
  have hgc := (continuous_of_abs_sub_le hg).2
  have hAm := measurableSet_barrier hA
  have hΦm := measurable_barrierPayoff hgc.measurable hAm m
  have hΦX : ∀ j, MemLp (fun z => barrierPayoff g A m (X j z)) 2 stdNormalSeq := fun j =>
    memLp_barrierPayoff hg hAm m (hXm j) (hX j)
  have hΦY : ∀ j, MemLp (fun z => barrierPayoff g A m (Y j z)) 2 stdNormalSeq := fun j =>
    memLp_barrierPayoff hg hAm m (hYm j) (hY j)
  -- the moment of the payoff does not depend on the level
  set G := ∫ z, g (X 0 z m) ^ (2 * (n + 1)) ∂stdNormalSeq with hGdef
  have hGj : ∀ j, ∫ z, g (X j z m) ^ (2 * (n + 1)) ∂stdNormalSeq = G := fun j =>
    integral_comp_monLevel hpair hXm (F := fun S => g (S m) ^ (2 * (n + 1)))
      ((hgc.measurable.comp (measurable_pi_apply m)).pow_const _) j
  have hG0 : 0 ≤ G := integral_nonneg fun z => (even_two_mul (n + 1)).pow_nonneg _
  set D₁ := 2 * Kg ^ 2 * E * T ^ ((κ : ℝ) - q₀) + 2 * (m * C * T ^ (q₁ - q₀ / n - q₀) + G)
    with hD₁
  set D₂ := Kg * Real.sqrt E * T ^ ((κ : ℝ) / 2 - q₀) + m * C * T ^ (q₁ - q₀ / n - q₀) +
    G * T ^ (q₀ / n * ((2 * n + 1 : ℕ) : ℝ) - q₀) with hD₂
  have hD₁0 : 0 ≤ D₁ := by positivity
  have hD₂0 : 0 ≤ D₂ := by positivity
  have hlev : ∀ j : ℕ,
      ∫ z, (barrierPayoff g A m (Y j z) - barrierPayoff g A m (X j z)) ^ 2 ∂stdNormalSeq ≤
        D₁ * (T / 2 ^ j) ^ q₀ ∧
      ∫ z, |barrierPayoff g A m (Y j z) - barrierPayoff g A m (X j z)| ∂stdNormalSeq ≤
        D₂ * (T / 2 ^ j) ^ q₀ := fun j => by
    have h := barrier_err_rate hg hA (hXm j) (hYm j) (hX j) (hY j) hn (hG j)
      (h := T / 2 ^ j) (by positivity) (div_le_self hT.le (one_le_pow₀ (by norm_num))) hE hC hq₀
      hq₀κ hq₀₁ (hs2 j) (hmis j)
    rwa [hGj j] at h
  have hTq : 0 ≤ T ^ (q₀ - q) := Real.rpow_nonneg hT.le _
  have hconv : ∀ i : ℕ, (T / 2 ^ i) ^ q₀ ≤ T ^ (q₀ - q) * (T / 2 ^ i) ^ q := fun i =>
    rpow_le_rpow_sub_mul_rpow (by positivity) (div_le_self hT.le (one_le_pow₀ (by norm_num)))
      hqq₀
  refine ⟨2 * D₁ * (1 + 2 ^ q₀) * T ^ (q₀ - q) + D₂ * T ^ (q₀ - q), by positivity, fun j =>
    ⟨(variance_pairAvg_corr_le hΦX hΦY hpair j).1, ?_, ?_⟩⟩
  · have hv := (variance_pairAvg_corr_le hΦX hΦY hpair j).2
    have hd : (T / 2 ^ (j + 1)) ^ q₀ + (T / 2 ^ j) ^ q₀ ≤
        (1 + 2 ^ q₀) * (T / 2 ^ (j + 1)) ^ q₀ := by
      have := dyadic_rpow_add_le hT (le_refl q₀) j
      rwa [sub_self, Real.rpow_zero, one_mul] at this
    have hpos : 0 ≤ (T / 2 ^ (j + 1)) ^ q := by positivity
    have h2 : 0 ≤ D₂ * T ^ (q₀ - q) * (T / 2 ^ (j + 1)) ^ q := by positivity
    calc _ ≤ _ := hv
      _ ≤ 2 * (D₁ * (T / 2 ^ (j + 1)) ^ q₀) + 2 * (D₁ * (T / 2 ^ j) ^ q₀) := by
          linarith [(hlev (j + 1)).1, (hlev j).1]
      _ = 2 * D₁ * ((T / 2 ^ (j + 1)) ^ q₀ + (T / 2 ^ j) ^ q₀) := by ring
      _ ≤ 2 * D₁ * ((1 + 2 ^ q₀) * (T / 2 ^ (j + 1)) ^ q₀) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ 2 * D₁ * ((1 + 2 ^ q₀) * (T ^ (q₀ - q) * (T / 2 ^ (j + 1)) ^ q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hconv (j + 1)) (by positivity))
            (by positivity)
      _ ≤ _ := by nlinarith
  · have hint : ∀ i, Integrable (fun z => barrierPayoff g A m (Y i z)) stdNormalSeq := fun i =>
      (hΦY i).integrable one_le_two
    have hintX : ∀ i, Integrable (fun z => barrierPayoff g A m (X i z)) stdNormalSeq := fun i =>
      (hΦX i).integrable one_le_two
    rw [← integral_comp_monLevel hpair hXm hΦm j, ← integral_sub (hint j) (hintX j)]
    have hpos : 0 ≤ (T / 2 ^ j) ^ q := by positivity
    have h2 : 0 ≤ 2 * D₁ * (1 + 2 ^ q₀) * T ^ (q₀ - q) * (T / 2 ^ j) ^ q := by positivity
    calc _ ≤ _ := abs_integral_le_integral_abs
      _ ≤ D₂ * (T / 2 ^ j) ^ q₀ := (hlev j).2
      _ ≤ D₂ * (T ^ (q₀ - q) * (T / 2 ^ j) ^ q) := mul_le_mul_of_nonneg_left (hconv j) hD₂0
      _ ≤ _ := by nlinarith

end BarrierAbstract

/-- For `0 < κ` and `q < κ/2` there are exponents `q ≤ q₀`, `0 ≤ q₀ ≤ κ/2`, `q₁ < κ/2` and `n ≥ 1`
with `q₀ (n + 1) ≤ q₁ n` (`q₀ = max(q, 0)`, `q₁ = (q₀ + κ/2)/2`; the exponents of
`barrier_rate_of`, Giles 2015, §5.1–§5.2). -/
lemma exists_barrier_exponents {κ : ℕ} (hκ : 0 < κ) {q : ℝ} (hq : q < κ / 2) :
    ∃ q₀ q₁ : ℝ, ∃ n : ℕ, q ≤ q₀ ∧ 0 ≤ q₀ ∧ q₀ ≤ κ / 2 ∧ q₁ < κ / 2 ∧ 0 < n ∧
      q₀ * (n + 1) ≤ q₁ * n := by
  have hκ' : (0 : ℝ) < κ / 2 := by
    have : (0 : ℝ) < κ := Nat.cast_pos.2 hκ
    positivity
  have h0 : max q 0 < κ / 2 := max_lt hq hκ'
  have hd : 0 < (max q 0 + κ / 2) / 2 - max q 0 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (max q 0 / ((max q 0 + κ / 2) / 2 - max q 0))
  rw [div_lt_iff₀ hd] at hn
  refine ⟨max q 0, (max q 0 + κ / 2) / 2, n + 1, le_max_left _ _, le_max_right _ _, h0.le,
    by linarith, Nat.succ_pos n, ?_⟩
  push_cast
  nlinarith

/-- **The mismatch at the monitoring dates, from `2p`-th moment bounds of the strong error**
(Giles 2015, §5.1, p. 33, l. 1436–1441, at every date).  Let `σ ≠ 0`, `T > 0`, `m ≥ 1`, and let
`Y_j` be approximations of the monitored values on level `j` (`h_j = T/(m 2^j)`) that vanish for
`s₀ = 0` and satisfy, for every `p ≥ 1`, `E[(S_{t_k} − Y_{j,k})^{2p}] ≤ D_p h_j^{κp}` at the
dates `k ≤ m`.  Then for every `q < κ/2` there is `C` with
`P(1_{S_{t_{k+1}} > B} ≠ 1_{Y_{j,k+1} > B}) ≤ C h_j^q` for all levels `j` and dates `k < m`
(`digital_mismatch_le_rpow`, `gbmMonExact_smallBall`, `exists_moment_exponent`). -/
lemma gbm_mon_mismatch_rate_of_moment (r σ s₀ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {m : ℕ}
    (hm : 0 < m) (B : ℝ) {κ : ℕ} (hκ : 0 < κ) {Y : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    (hY0 : s₀ = 0 → ∀ j z k, Y j z k = 0)
    (hmom : ∀ p : ℕ, 0 < p → ∃ D : ℝ, 0 ≤ D ∧ ∀ j k : ℕ, k ≤ m →
      Integrable (fun z => (gbmMonExact r σ T s₀ m j z k - Y j z k) ^ (2 * p)) stdNormalSeq ∧
      ∫ z, (gbmMonExact r σ T s₀ m j z k - Y j z k) ^ (2 * p) ∂stdNormalSeq ≤
        D * (T / (m * 2 ^ j)) ^ (κ * p))
    {q : ℝ} (hq : q < κ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j k : ℕ, k < m →
      stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
        (gbmMonExact r σ T s₀ m j z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y j z (k + 1))} ≤
        C * (T / (m * 2 ^ j)) ^ q := by
  rcases eq_or_ne s₀ 0 with hs0 | hs₀
  · refine ⟨0, le_rfl, fun j k _ => ?_⟩
    have hset : {z | (Set.Ioi B).indicator (1 : ℝ → ℝ) (gbmMonExact r σ T s₀ m j z (k + 1)) ≠
        (Set.Ioi B).indicator 1 (Y j z (k + 1))} = ∅ := by
      ext z
      simp [gbmMonExact, hs0, hY0 hs0]
    rw [hset, measureReal_empty, zero_mul]
  obtain ⟨p, hp, hqp⟩ := exists_moment_exponent hκ hq
  obtain ⟨D, hD, hYD⟩ := hmom p hp
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hσ' := abs_pos.2 hσ
  have hs' := abs_pos.2 hs₀
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hTm : 0 < Real.sqrt (T / m) := Real.sqrt_pos.2 (div_pos hT hm')
  set ρ := Real.exp (|σ ^ 2 - r| * T) /
    (Real.sqrt (2 * Real.pi) * |s₀| * |σ| * Real.sqrt (T / m)) with hρ
  have hρ0 : 0 < ρ := by positivity
  refine ⟨2 * (2 * ρ) ^ (2 * (p : ℝ) / (2 * p + 1)) * D ^ (1 / (2 * p + 1 : ℝ)) *
    T ^ (((κ * p : ℕ) : ℝ) / (2 * p + 1) - q), by positivity, fun j k hk => ?_⟩
  have hh : 0 < T / (m * 2 ^ j) := div_pos hT (mul_pos hm' (by positivity))
  have hhT : T / (m * 2 ^ j) ≤ T := div_le_self hT.le
    (one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.2 hm) (one_le_pow₀ (by norm_num)))
  obtain ⟨hint, hle⟩ := hYD j (k + 1) hk
  exact digital_mismatch_le_rpow hρ0
    (fun δ hδ => gbmMonExact_smallBall r σ hs₀ hσ hT hm j (Nat.succ_pos k) hk B hδ) hint hD hh
    hhT hle hqp

/-- `(S_{t_k} − Ŝ_{t_k})^{2p}` is integrable for the monitored Euler–Maruyama path (Giles 2015,
§5.1). -/
lemma integrable_gbmMon_em_err_pow (r σ T s₀ : ℝ) (m j : ℕ) (hh : 0 ≤ T / (m * 2 ^ j))
    (k p : ℕ) :
    Integrable (fun z => (gbmMonExact r σ T s₀ m j z k - gbmMonEM r σ T s₀ m j z k) ^ (2 * p))
      stdNormalSeq := by
  simp_rw [gbmMonExact_eq_prod, gbmMonEM_eq_prod, mul_sub_mul_pow_two_mul]
  exact (integrable_pow_prod_sub_prod (measurable_gbmExpFactor r σ _)
    (measurable_gbmEMFactor r σ _) (even_two_mul p) (integrable_gbmExpFactor_pow r σ _ _)
    (integrable_gbmEMFactor_pow r σ hh p) _).const_mul _

/-- `(S_{t_k} − Ŝ_{t_k})^{2p}` is integrable for the monitored Milstein path (Giles 2015,
§5.2). -/
lemma integrable_gbmMon_mil_err_pow (r σ T s₀ : ℝ) (m j : ℕ) (hh : 0 ≤ T / (m * 2 ^ j))
    (k p : ℕ) :
    Integrable (fun z => (gbmMonExact r σ T s₀ m j z k - gbmMonMil r σ T s₀ m j z k) ^ (2 * p))
      stdNormalSeq := by
  simp_rw [gbmMonExact_eq_prod, gbmMonMil_eq_prod, mul_sub_mul_pow_two_mul]
  exact (integrable_pow_prod_sub_prod (measurable_gbmExpFactor r σ _)
    (measurable_gbmMilFactor r σ _) (even_two_mul p) (integrable_gbmExpFactor_pow r σ _ _)
    (integrable_gbmMilFactor_pow r σ hh p) _).const_mul _

/-- The `L^{2p}` strong error of Euler–Maruyama at a monitoring date `t_k ≤ T`:
`E[(S_{t_k} − Ŝ_{t_k})^{2p}] ≤ C_p(T) h_j^p` (Giles 2015, §5.1; `gbm_em_moment_error_le` at the
grid time `k 2^j`). -/
lemma gbmMon_em_moment_error (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (m j : ℕ) {k : ℕ} (hk : k ≤ m)
    {p : ℕ} (hp : 0 < p) :
    ∫ z, (gbmMonExact r σ T s₀ m j z k - gbmMonEM r σ T s₀ m j z k) ^ (2 * p) ∂stdNormalSeq ≤
      gbmEMMomentConst p r σ T s₀ * (T / (m * 2 ^ j)) ^ p := by
  have hh : 0 ≤ T / (m * 2 ^ j) := div_nonneg hT (by positivity)
  have hnT : ((k * 2 ^ j : ℕ) : ℝ) * (T / (m * 2 ^ j)) ≤ T := by
    rw [monDate_eq]
    exact (monDate_mem_Icc hT hk).2
  have h := gbm_em_moment_error_le r σ s₀ hh (k * 2 ^ j) hnT hp
  rw [monDate_eq] at h
  exact h

/-- The `L^{2p}` strong error of Milstein at a monitoring date `t_k ≤ T`:
`E[(S_{t_k} − Ŝ_{t_k})^{2p}] ≤ C_p(T) h_j^{2p}` (Giles 2015, §5.2; `gbm_mil_moment_error_le` at
the grid time `k 2^j`). -/
lemma gbmMon_mil_moment_error (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (m j : ℕ) {k : ℕ} (hk : k ≤ m)
    {p : ℕ} (hp : 0 < p) :
    ∫ z, (gbmMonExact r σ T s₀ m j z k - gbmMonMil r σ T s₀ m j z k) ^ (2 * p) ∂stdNormalSeq ≤
      gbmMilMomentConst p r σ T s₀ * (T / (m * 2 ^ j)) ^ (2 * p) := by
  have hh : 0 ≤ T / (m * 2 ^ j) := div_nonneg hT (by positivity)
  have hnT : ((k * 2 ^ j : ℕ) : ℝ) * (T / (m * 2 ^ j)) ≤ T := by
    rw [monDate_eq]
    exact (monDate_mem_Icc hT hk).2
  have h := gbm_mil_moment_error_le r σ s₀ hh (k * 2 ^ j) hnT hp
  rw [monDate_eq] at h
  exact h

/-- **The discretely monitored barrier option with Euler–Maruyama: `V_ℓ = O(h_ℓ^q)` and bias
`O(h_ℓ^q)` for every `q < ½`** (Giles 2015, §5.1, p. 33, Table 5.2, row "barrier", Euler–Maruyama:
numerics `O(h^{1/2})`, analysis `o(h^{1/2−δ})`; l. 1454–1456: "the barrier is a discontinuous
function of the maximum or minimum").  For GBM with `σ ≠ 0`, `T > 0`, `m ≥ 1` monitoring dates
`t_k = kT/m`, a Lipschitz payoff `g` (`|g(x) − g(y)| ≤ K_g |x − y|`, not necessarily bounded), and
the knock-out set `A = (−∞, B]` (up-and-out) or `A = (B, ∞)` (down-and-out), level `j` with
`m 2^j` steps of size `h_j = T/(m 2^j)` (`gbmMonEM`): for every `q < ½` there is `C` such that the
correction `Φ(Ŝ^f_{j+1}) − Φ(Ŝ^c_j)` (the coarse path driven by the summed increments) is square
integrable with variance `≤ C h_{j+1}^q`, and `|E[Φ(Ŝ_j)] − E[Φ(S)]| ≤ C h_j^q`,
`Φ = barrierPayoff g A m` and `S` the exact solution at the dates (`gbmMonExact … 0`).  Proof: the
mismatch probability at every date is `O(h_j^{q₁})` for some `q₁ ∈ (q, ½)`
(`gbm_mon_mismatch_rate_of_moment` with the `L^{2p}` strong errors `gbmMon_em_moment_error` and the
density bound `gbmMonExact_smallBall`: a union bound over the dates of the marginal small-ball
estimates), the Lipschitz part is `O(h_j)` (`gbm_em_monitored_strong_error`), and the payoff
`g(S_T)` on the mismatch event is controlled by the moments of `S_T` of every order
(`integrable_gbmMonExact_pow`, `integrable_lipschitz_pow`) with a truncation that replaces Hölder's
inequality (`barrier_err_le`); `barrier_rate_of`, `exists_barrier_exponents`.

**How close to the paper.**  The paper's barrier option is continuously monitored (its maximum or
minimum over `[0, T]`), and the analysis column of Table 5.2 is due to Giles, Higham and Mao
(2009); here the barrier is monitored at the `m` fixed dates, which lie on every grid, so no
Brownian-bridge argument is needed.  Every Lipschitz `g` is covered, e.g. the up-and-out and the
down-and-out calls `max(S_T − K, 0) 1{max_k S_{t_k} ≤ B}`, `max(S_T − K, 0) 1{min_k S_{t_k} > B}`.
`m = 0` is excluded: there are no dates and no time steps (`h_j = T/0` would be Lean's junk value
`0`), and `Φ ≡ g(s₀)` makes the statement trivial.  `σ ≠ 0` is needed (see
`gbm_em_barrier_theorem1`). -/
theorem gbm_em_barrier_rate (r σ s₀ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {m : ℕ}
    (hm : 0 < m) {g : ℝ → ℝ} {Kg : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) {q : ℝ} (hq : q < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      MemLp (fun z => barrierPayoff g A m (gbmMonEM r σ T s₀ m (j + 1) z) -
          barrierPayoff g A m (gbmMonEM r σ T s₀ m j (pairAvg z))) 2 stdNormalSeq ∧
      variance (fun z => barrierPayoff g A m (gbmMonEM r σ T s₀ m (j + 1) z) -
          barrierPayoff g A m (gbmMonEM r σ T s₀ m j (pairAvg z))) stdNormalSeq ≤
        C * (T / (m * 2 ^ (j + 1))) ^ q ∧
      |∫ z, barrierPayoff g A m (gbmMonEM r σ T s₀ m j z) ∂stdNormalSeq -
          ∫ z, barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq| ≤
        C * (T / (m * 2 ^ j)) ^ q := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hTm : 0 < T / m := div_pos hT hm'
  have hq' : q < ((1 : ℕ) : ℝ) / 2 := by rw [Nat.cast_one]; exact hq
  obtain ⟨q₀, q₁, n, hqq₀, hq₀, hq₀κ, hq₁, hn, hq₀₁⟩ := exists_barrier_exponents one_pos hq'
  obtain ⟨C, hC, hmis⟩ := gbm_mon_mismatch_rate_of_moment r σ s₀ hσ hT hm B one_pos
    (Y := gbmMonEM r σ T s₀ m) (fun hs0 j z k => by rw [gbmMonEM_eq_prod, hs0, zero_mul])
    (fun p hp => ⟨gbmEMMomentConst p r σ T s₀, gbmEMMomentConst_nonneg p r σ s₀ hT.le,
      fun j k hk => ⟨integrable_gbmMon_em_err_pow r σ T s₀ m j (by positivity) k p, by
        rw [one_mul]
        exact gbmMon_em_moment_error r σ s₀ hT.le m j hk hp⟩⟩) hq₁
  have e : ∀ j : ℕ, T / (m * 2 ^ j) = T / m / 2 ^ j := fun j => (div_div T m (2 ^ j)).symm
  obtain ⟨C', hC', h⟩ := barrier_rate_of hg hA (X := gbmMonExact r σ T s₀ m)
    (Y := gbmMonEM r σ T s₀ m) (fun j => (measurable_memLp_gbmMonExact r σ T s₀ m j).1)
    (fun j => (measurable_memLp_gbmMonEM r σ T s₀ m j).1)
    (fun j => (measurable_memLp_gbmMonExact r σ T s₀ m j).2 m)
    (fun j => (measurable_memLp_gbmMonEM r σ T s₀ m j).2 m)
    (gbmMonExact_pairAvg r σ T s₀ m) hn
    (fun j => integrable_lipschitz_pow hg
      ((measurable_pi_apply m).comp (measurable_memLp_gbmMonExact r σ T s₀ m j).1) (n + 1)
      (integrable_gbmMonExact_pow r σ T s₀ m j m _))
    hTm (κ := 1) (gbmStrongConst_nonneg r σ s₀ hT.le) hC hqq₀ hq₀ hq₀κ hq₀₁
    (fun j => by
      rw [pow_one, ← e]
      exact gbm_em_monitored_strong_error r σ s₀ hT.le m j le_rfl)
    (fun j k hk => by
      rw [← e]
      exact hmis j k hk)
  refine ⟨C', hC', fun j => ?_⟩
  rw [e, e]
  exact h j

/-- **The discretely monitored barrier option with the natural Milstein estimator:
`V_ℓ = O(h_ℓ^q)` and bias `O(h_ℓ^q)` for every `q < 1`** (Giles 2015, §5.2, p. 35, l. 1525–1531,
the paper's argument for the digital option, applied here at every monitoring date: "In the case
of a digital option, if we use the natural multilevel estimator then `P_ℓ − P_{ℓ−1} = O(1)` for an
`O(h_ℓ)` fraction of the paths, giving `V_ℓ = O(h_ℓ)`"; Table 5.2, l. 1430, row "barrier").  In
the setting of `gbm_em_barrier_rate` (`σ ≠ 0`, `T > 0`, `m ≥ 1` dates, `g` Lipschitz, up-and-out
or down-and-out) with the Milstein scheme (`gbmMonMil`): for every `q < 1` there is `C` such that
the correction is square integrable with `V[Φ(Ŝ^f_{j+1}) − Φ(Ŝ^c_j)] ≤ C h_{j+1}^q`, and
`|E[Φ(Ŝ_j)] − E[Φ(S)]| ≤ C h_j^q`.  Proof: as `gbm_em_barrier_rate` with
`gbmMon_mil_moment_error` (`κ = 2`) and `gbm_mil_monitored_strong_error`.

**How close to the paper.**  For the barrier option the paper states, for the continuously
monitored option (§5.2, p. 38, l. 1653–1662): an estimator "based directly on the minimum (or
maximum) of the values at the discrete timesteps will have a poor variance … an even worse
`O(h_ℓ^{1/2})` variance for barrier options", because of the `O(h^{1/2})` variation of the path
within a timestep; the Milstein row of Table 5.2 (`O(h^{3/2})`, `o(h^{3/2−δ})`) is for the
Brownian-bridge (conditional expectation) estimator of §5.2 (Giles 2008a; Giles, Debrabant and
Rößler 2013), which is not formalised.  For the discretely monitored option, whose dates lie on
every grid, the natural estimator has the rate `O(h_ℓ)` of the digital option up to the loss in the
exponent.  `m = 0` is excluded as in `gbm_em_barrier_rate`; `σ ≠ 0` is needed (for `σ = 0` the
Milstein path is the Euler–Maruyama one, see `gbm_em_barrier_theorem1`). -/
theorem gbm_mil_barrier_rate (r σ s₀ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {m : ℕ}
    (hm : 0 < m) {g : ℝ → ℝ} {Kg : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) {q : ℝ} (hq : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      MemLp (fun z => barrierPayoff g A m (gbmMonMil r σ T s₀ m (j + 1) z) -
          barrierPayoff g A m (gbmMonMil r σ T s₀ m j (pairAvg z))) 2 stdNormalSeq ∧
      variance (fun z => barrierPayoff g A m (gbmMonMil r σ T s₀ m (j + 1) z) -
          barrierPayoff g A m (gbmMonMil r σ T s₀ m j (pairAvg z))) stdNormalSeq ≤
        C * (T / (m * 2 ^ (j + 1))) ^ q ∧
      |∫ z, barrierPayoff g A m (gbmMonMil r σ T s₀ m j z) ∂stdNormalSeq -
          ∫ z, barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq| ≤
        C * (T / (m * 2 ^ j)) ^ q := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hTm : 0 < T / m := div_pos hT hm'
  have hq' : q < ((2 : ℕ) : ℝ) / 2 := by rw [Nat.cast_two, div_self two_ne_zero]; exact hq
  obtain ⟨q₀, q₁, n, hqq₀, hq₀, hq₀κ, hq₁, hn, hq₀₁⟩ := exists_barrier_exponents two_pos hq'
  obtain ⟨C, hC, hmis⟩ := gbm_mon_mismatch_rate_of_moment r σ s₀ hσ hT hm B two_pos
    (Y := gbmMonMil r σ T s₀ m) (fun hs0 j z k => by rw [gbmMonMil_eq_prod, hs0, zero_mul])
    (fun p hp => ⟨gbmMilMomentConst p r σ T s₀, gbmMilMomentConst_nonneg p r σ s₀ hT.le,
      fun j k hk => ⟨integrable_gbmMon_mil_err_pow r σ T s₀ m j (by positivity) k p,
        gbmMon_mil_moment_error r σ s₀ hT.le m j hk hp⟩⟩) hq₁
  have e : ∀ j : ℕ, T / (m * 2 ^ j) = T / m / 2 ^ j := fun j => (div_div T m (2 ^ j)).symm
  obtain ⟨C', hC', h⟩ := barrier_rate_of hg hA (X := gbmMonExact r σ T s₀ m)
    (Y := gbmMonMil r σ T s₀ m) (fun j => (measurable_memLp_gbmMonExact r σ T s₀ m j).1)
    (fun j => (measurable_memLp_gbmMonMil r σ T s₀ m j).1)
    (fun j => (measurable_memLp_gbmMonExact r σ T s₀ m j).2 m)
    (fun j => (measurable_memLp_gbmMonMil r σ T s₀ m j).2 m)
    (gbmMonExact_pairAvg r σ T s₀ m) hn
    (fun j => integrable_lipschitz_pow hg
      ((measurable_pi_apply m).comp (measurable_memLp_gbmMonExact r σ T s₀ m j).1) (n + 1)
      (integrable_gbmMonExact_pow r σ T s₀ m j m _))
    hTm (κ := 2) (gbmMilStrongConst_nonneg r σ s₀ hT.le) hC hqq₀ hq₀ hq₀κ hq₀₁
    (fun j => by
      rw [← e]
      exact gbm_mil_monitored_strong_error r σ s₀ hT.le m j le_rfl)
    (fun j k hk => by
      rw [← e]
      exact hmis j k hk)
  refine ⟨C', hC', fun j => ?_⟩
  rw [e, e]
  exact h j

/-- **Theorem 1 end to end for the discretely monitored barrier option with Euler–Maruyama: MSE
`< ε²` at cost `O(ε^{−3−η})` for every `η > 0`** (Giles 2015, §5.1, p. 33, Table 5.2, row
"barrier", with Theorem 1, §2.1, p. 6, and (2.4)).  In the setting of `gbm_em_barrier_rate`
(`σ ≠ 0`, `T > 0`, `m ≥ 1` dates, `g` Lipschitz, up-and-out or down-and-out), level `j` uses
`m 2^j` Euler–Maruyama steps, the coarse path of a sample is driven by the summed increments, the
samples are independent and a level-`j` sample costs `m 2^j`.  Then for every `η > 0` there is
`c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_j ≥ 1` for which the multilevel
estimator of `E[g(S_T) ∏_{k=1}^m 1_A(S_{t_k})]` (`S = gbmMonExact … 0`, the exact solution at the
dates) has a square-integrable error with mean square `< ε²`, at cost
`∑_{j≤L} N_j m 2^j ≤ c₄ ε^{−3−η}`.  No rate is assumed: `α = β = q = 1/(2 + η)` and `γ = 1`
(`gbm_em_barrier_rate`, `theorem1_pairAvg_of_rate`).

**How close to the paper.**  Table 5.2 gives only variance rates for the barrier option; the paper
states no weak rate `α` for it.  Here `α = q < ½` comes from the mismatch probability, as for the
digital option (`gbm_em_digital_theorem1`), and `β = q < ½` (Table 5.2: numerics `O(h^{1/2})`,
analysis `o(h^{1/2−δ})`; the endpoint `β = ½` is not proved), so the cost carries the loss
`η > 0`.  The barrier is monitored at the `m` fixed dates, not continuously (see
`gbm_em_barrier_rate`).  `σ ≠ 0` is needed: for `m = 1`,
`g = 1` and `A = (B, ∞)` the barrier payoff is the digital payoff, for which `σ = 0` gives a mean
square error `1` (`gbm_em_digital_theorem1`). -/
theorem gbm_em_barrier_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {m : ℕ}
    (hm : 0 < m) {g : ℝ → ℝ} {Kg : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) {η : ℝ} (hη : 0 < η) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => barrierPayoff g A m (gbmMonEM r σ T s₀ m j z))
              (fun j z => barrierPayoff g A m (gbmMonEM r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => barrierPayoff g A m (gbmMonEM r σ T s₀ m j z))
              (fun j z => barrierPayoff g A m (gbmMonEM r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤ c₄ * ε ^ (-3 - η) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hTm : 0 < T / m := div_pos hT hm'
  set q := 1 / (2 + η) with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q < 1 / 2 := by
    rw [hqdef, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hgc := (continuous_of_abs_sub_le hg).2
  have hAm := measurableSet_barrier hA
  have hΦm := measurable_barrierPayoff hgc.measurable hAm m
  obtain ⟨C, -, hC⟩ := gbm_em_barrier_rate r σ s₀ hσ hT hm hg hA hq
  have e : ∀ j : ℕ, T / (m * 2 ^ j) = T / m / 2 ^ j := fun j => (div_div T m (2 ^ j)).symm
  obtain ⟨c₄, hc₄, h⟩ := theorem1_pairAvg_of_rate hTm hq0 (by linarith)
    (Pf := fun j z => barrierPayoff g A m (gbmMonEM r σ T s₀ m j z))
    (P := fun z => barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z))
    (fun j => hΦm.comp (measurable_memLp_gbmMonEM r σ T s₀ m j).1)
    (fun j => memLp_barrierPayoff hg hAm m (measurable_memLp_gbmMonEM r σ T s₀ m j).1
      ((measurable_memLp_gbmMonEM r σ T s₀ m j).2 m))
    ((memLp_barrierPayoff hg hAm m (measurable_memLp_gbmMonExact r σ T s₀ m 0).1
      ((measurable_memLp_gbmMonExact r σ T s₀ m 0).2 m)).integrable one_le_two)
    (c₁ := C) (c₂ := C)
    (fun j => by
      rw [← e]
      exact (hC j).2.2)
    (fun j => by
      rw [← e]
      exact (hC j).2.1)
  refine ⟨m * c₄, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, hint, hmse, ?_⟩
  have hexp : -2 - (1 - q) / q = -3 - η := by
    rw [hqdef]
    field_simp
    ring
  rw [hexp] at hcost
  calc ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) =
        m * ∑ j ∈ range (L + 1), (N j : ℝ) * 2 ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ m * (c₄ * ε ^ (-3 - η)) := mul_le_mul_of_nonneg_left hcost hm'.le
    _ = m * c₄ * ε ^ (-3 - η) := by ring

/-- **Theorem 1 end to end for the discretely monitored barrier option with the natural Milstein
estimator: MSE `< ε²` at cost `O(ε^{−2−η})` for every `η > 0`** (Giles 2015, §5.2, p. 35,
l. 1525–1531 (the natural estimator of a discontinuous payoff), and Table 5.2, row "barrier", with
Theorem 1, §2.1, p. 6, and (2.4)).  In the setting of `gbm_mil_barrier_rate` (`σ ≠ 0`, `T > 0`,
`m ≥ 1` dates, `g` Lipschitz, up-and-out or down-and-out), with `m 2^j` Milstein steps on level
`j` and cost `m 2^j` per sample: for every `η > 0` there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_j ≥ 1` with a square-integrable error of mean square `< ε²` and
cost `∑_{j≤L} N_j m 2^j ≤ c₄ ε^{−2−η}`.  No rate is assumed: `α = β = q = 1/(1 + η)`, `γ = 1`
(`gbm_mil_barrier_rate`, `theorem1_pairAvg_of_rate`).

**How close to the paper.**  The Milstein barrier rate `β = 3/2 > γ = 1` of Table 5.2, which would
give `O(ε^{−2})`, is for the continuously monitored option with the Brownian-bridge estimator of
§5.2, which is not formalised.  For the natural estimator of the discretely monitored option
`β = q < 1` (the endpoint `β = 1` is not proved), hence `O(ε^{−2−η})`; the paper states no weak
rate for the barrier option, and here `α = q` comes from the mismatch probability.  `σ ≠ 0` is
needed: for `σ = 0` the Milstein path is the Euler–Maruyama one, and `m = 1`, `g = 1`,
`A = (B, ∞)` give the digital counterexample of `gbm_em_digital_theorem1`. -/
theorem gbm_mil_barrier_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {m : ℕ}
    (hm : 0 < m) {g : ℝ → ℝ} {Kg : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) {η : ℝ} (hη : 0 < η) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ j, 0 < N j) ∧
        Integrable (fun x => (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => barrierPayoff g A m (gbmMonMil r σ T s₀ m j z))
              (fun j z => barrierPayoff g A m (gbmMonMil r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ j ∈ range (L + 1),
            blockMean (fineCoarseDiff (fun j z => barrierPayoff g A m (gbmMonMil r σ T s₀ m j z))
              (fun j z => barrierPayoff g A m (gbmMonMil r σ T s₀ m j (pairAvg z))))
              (fun p x => x p) j (N j) x -
            ∫ z, barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z) ∂stdNormalSeq) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) ≤ c₄ * ε ^ (-2 - η) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hTm : 0 < T / m := div_pos hT hm'
  set q := 1 / (1 + η) with hqdef
  have hq0 : 0 < q := by positivity
  have hq : q < 1 := by
    rw [hqdef, div_lt_one (by positivity)]
    linarith
  have hgc := (continuous_of_abs_sub_le hg).2
  have hAm := measurableSet_barrier hA
  have hΦm := measurable_barrierPayoff hgc.measurable hAm m
  obtain ⟨C, -, hC⟩ := gbm_mil_barrier_rate r σ s₀ hσ hT hm hg hA hq
  have e : ∀ j : ℕ, T / (m * 2 ^ j) = T / m / 2 ^ j := fun j => (div_div T m (2 ^ j)).symm
  obtain ⟨c₄, hc₄, h⟩ := theorem1_pairAvg_of_rate hTm hq0 hq
    (Pf := fun j z => barrierPayoff g A m (gbmMonMil r σ T s₀ m j z))
    (P := fun z => barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z))
    (fun j => hΦm.comp (measurable_memLp_gbmMonMil r σ T s₀ m j).1)
    (fun j => memLp_barrierPayoff hg hAm m (measurable_memLp_gbmMonMil r σ T s₀ m j).1
      ((measurable_memLp_gbmMonMil r σ T s₀ m j).2 m))
    ((memLp_barrierPayoff hg hAm m (measurable_memLp_gbmMonExact r σ T s₀ m 0).1
      ((measurable_memLp_gbmMonExact r σ T s₀ m 0).2 m)).integrable one_le_two)
    (c₁ := C) (c₂ := C)
    (fun j => by
      rw [← e]
      exact (hC j).2.2)
    (fun j => by
      rw [← e]
      exact (hC j).2.1)
  refine ⟨m * c₄, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, hint, hmse, ?_⟩
  have hexp : -2 - (1 - q) / q = -2 - η := by
    rw [hqdef]
    field_simp
    ring
  rw [hexp] at hcost
  calc ∑ j ∈ range (L + 1), (N j : ℝ) * (m * 2 ^ j) =
        m * ∑ j ∈ range (L + 1), (N j : ℝ) * 2 ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ m * (c₄ * ε ^ (-2 - η)) := mul_le_mul_of_nonneg_left hcost hm'.le
    _ = m * c₄ * ε ^ (-2 - η) := by ring

/-! ### Splitting and conditional expectation with a Milstein final step -/

/-- **The coarse path of level `ℓ` with a Milstein last step has the law of the fine path of
level `ℓ − 1`** (Giles 2015, §5.2, p. 38, l. 1635–1636: "Furthermore, one can revert to using the
Milstein approximation for the final timestep"; the Milstein analogue of
`map_milsteinEM_coarse_eq_fine`).  For a scalar SDE `dS = a(S) dt + b(S) dW` with measurable `a`,
`b`, fine timestep `h` and `N = 2n + 2` fine steps on level `ℓ`: the coarse path takes `n` Milstein
steps of size `2h` driven by the summed increments (`pairAvg`), reaching `Ŝ^c_{N−2}`, and then the
Milstein step `milsteinStep a b (2h) Ŝ^c_{N−2} (ΔW_{N−2} + ΔW_{N−1})` with the two fine increments
`ΔW_{N−2} = √h Z_{2n}` and `ΔW_{N−1} = √h Z_{2n+1}`; the fine path of level `ℓ − 1` takes `n`
Milstein steps of size `2h` and then the Milstein step with the increment `√(2h) W_n`.  The two
terminal values have the same law: the first is the second evaluated at `W = pairAvg Z`.  As in
`map_milsteinEM_coarse_eq_fine`, the coefficients are autonomous and for `h < 0` the statement is
degenerate (`√h = √(2h) = 0` in Lean). -/
theorem map_milstein_coarse_eq_fine {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (h S₀ : ℝ) (n : ℕ) :
    stdNormalSeq.map (fun z => milsteinStep a b (2 * h)
        (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
        (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1))) =
      stdNormalSeq.map (fun w => milsteinStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
        (Real.sqrt (2 * h) * w n)) := by
  have hF : Measurable fun w : ℕ → ℝ => milsteinStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ w n) (Real.sqrt (2 * h) * w n) :=
    measurable_milsteinPath_incr ha hb (2 * h) S₀ (n + 1)
  have e : (fun z => milsteinStep a b (2 * h) (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
        (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1))) =
      (fun w => milsteinStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
        (Real.sqrt (2 * h) * w n)) ∘ pairAvg := by
    funext z
    have hs : Real.sqrt (2 * h) * pairAvg z n =
        Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) h, pairAvg]
      field_simp
    rw [Function.comp_apply, hs]
  rw [e, ← Measure.map_map hF measurePreserving_pairAvg.measurable,
    measurePreserving_pairAvg.map_eq]

/-- **(2.4) for the conditional-expectation payoffs with a Milstein final step, for any payoff**
(Giles 2015, §5.2, p. 36, l. 1584–1590: "It is very important in this conditional expectation
formulation that `E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` … This ensures that the identity in Equation (2.4)
is respected"; p. 38, l. 1635–1636: "one can revert to using the Milstein approximation for the
final timestep").  With the paths of `map_milstein_coarse_eq_fine` and any strongly measurable
payoff `g`, the coarse payoff `E[g(Ŝ^c_N) | Ŝ^c_{N−2}, ΔW_{N−2}]` of level `ℓ` and the fine payoff
`E[g(Ŝ^f) | Ŝ^f_{before the last step}]` of level `ℓ − 1` have the same mean, `E[g(Ŝ^f)]`, the
mean of the payoff of the level-`(ℓ − 1)` Milstein path (`integral_condExp_eq_of_map_eq`,
`integral_condExp`).  This is the limit of infinitely many sub-samples in the splitting estimator
(`splitting_milstein_mean_eq`).  If `g(Ŝ^f)` is not integrable, all three means are `0` by Lean's
conventions; integrability is not needed for the identity, so it is not assumed. -/
theorem integral_condExp_milstein_coarse_eq_fine {a b : ℝ → ℝ} (ha : Measurable a)
    (hb : Measurable b) (h S₀ : ℝ) (n : ℕ) {g : ℝ → ℝ} (hg : StronglyMeasurable g) :
    ∫ z, (stdNormalSeq[fun z => g (milsteinStep a b (2 * h)
        (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
        (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1))) |
        MeasurableSpace.comap (fun z => (milsteinPath a b (2 * h) S₀ (pairAvg z) n,
          Real.sqrt h * z (2 * n))) inferInstance]) z ∂stdNormalSeq =
      ∫ w, (stdNormalSeq[fun w => g (milsteinStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
        (Real.sqrt (2 * h) * w n)) |
        MeasurableSpace.comap (fun w => milsteinPath a b (2 * h) S₀ w n) inferInstance]) w
        ∂stdNormalSeq ∧
    ∫ w, (stdNormalSeq[fun w => g (milsteinStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
        (Real.sqrt (2 * h) * w n)) |
        MeasurableSpace.comap (fun w => milsteinPath a b (2 * h) S₀ w n) inferInstance]) w
        ∂stdNormalSeq =
      ∫ w, g (milsteinPath a b (2 * h) S₀ w (n + 1)) ∂stdNormalSeq := by
  have hMc : Measurable fun z => milsteinPath a b (2 * h) S₀ (pairAvg z) n :=
    (measurable_milsteinPath_incr ha hb (2 * h) S₀ n).comp measurePreserving_pairAvg.measurable
  have hM := measurable_milsteinPath_incr ha hb (2 * h) S₀ n
  have hz : ∀ k, Measurable fun z : ℕ → ℝ => z k := fun k => measurable_pi_apply k
  have hd := measurable_deriv b
  have hSc : Measurable fun z => milsteinStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
      (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1)) := by
    have h1 := hz (2 * n)
    have h2 := hz (2 * n + 1)
    unfold milsteinStep
    fun_prop
  have hSf : Measurable fun w => milsteinStep a b (2 * h) (milsteinPath a b (2 * h) S₀ w n)
      (Real.sqrt (2 * h) * w n) := measurable_milsteinPath_incr ha hb (2 * h) S₀ (n + 1)
  have hWc : Measurable fun z : ℕ → ℝ => (milsteinPath a b (2 * h) S₀ (pairAvg z) n,
      Real.sqrt h * z (2 * n)) := hMc.prodMk ((hz (2 * n)).const_mul _)
  exact ⟨integral_condExp_eq_of_map_eq hWc.comap_le hM.comap_le hSc hSf
    (map_milstein_coarse_eq_fine ha hb h S₀ n) hg, integral_condExp hM.comap_le⟩

/-- Replacing the `i`-th coordinate of an i.i.d. standard normal sequence by the `j`-th coordinate
of an independent one gives again an i.i.d. standard normal sequence: `(z, y) ↦ z[i ↦ y_j]`
preserves `N(0,1)^{⊗ℕ} ⊗ N(0,1)^{⊗ℕ} → N(0,1)^{⊗ℕ}` (the sub-samples of the last Brownian
increment in the splitting estimator, Giles 2015, §5.2, p. 36, l. 1594–1600; `eq_infinitePi`). -/
lemma measurePreserving_update_prod (i j : ℕ) :
    MeasurePreserving (fun p : (ℕ → ℝ) × (ℕ → ℝ) => Function.update p.1 i (p.2 j))
      (stdNormalSeq.prod stdNormalSeq) stdNormalSeq := by
  have hU : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => Function.update p.1 i (p.2 j) := by
    refine measurable_pi_lambda _ fun k => ?_
    by_cases hk : k = i
    · subst hk
      have e : (fun p : (ℕ → ℝ) × (ℕ → ℝ) => Function.update p.1 k (p.2 j) k) =
          fun p => p.2 j := funext fun p => Function.update_self _ _ _
      rw [e]
      exact (measurable_pi_apply j).comp measurable_snd
    · have e : (fun p : (ℕ → ℝ) × (ℕ → ℝ) => Function.update p.1 i (p.2 j) k) =
          fun p => p.1 k := funext fun p => Function.update_of_ne hk _ _
      rw [e]
      exact (measurable_pi_apply k).comp measurable_fst
  refine ⟨hU, Measure.eq_infinitePi (fun _ => gaussianReal 0 1) fun s t ht => ?_⟩
  have hev := measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) j
  rw [Measure.map_apply hU (MeasurableSet.pi s.countable_toSet fun k _ => ht k)]
  by_cases hi : i ∈ s
  · have hset : (fun p : (ℕ → ℝ) × (ℕ → ℝ) => Function.update p.1 i (p.2 j)) ⁻¹' Set.pi s t =
        Set.pi (s.erase i : Set ℕ) t ×ˢ ((fun y : ℕ → ℝ => y j) ⁻¹' t i) := by
      ext ⟨z, y⟩
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Finset.mem_coe, Finset.mem_erase]
      constructor
      · intro hz
        refine ⟨fun k hk => ?_, ?_⟩
        · have := hz k hk.2
          rwa [Function.update_of_ne hk.1] at this
        · have := hz i hi
          rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ k hk
        by_cases hki : k = i
        · subst hki
          rw [Function.update_self]
          exact h2
        · rw [Function.update_of_ne hki]
          exact h1 k ⟨hki, hk⟩
    rw [hset, Measure.prod_prod, Measure.infinitePi_pi _ fun k _ => ht k,
      hev.measure_preimage (ht i).nullMeasurableSet, Finset.prod_erase_mul s _ hi]
  · have hset : (fun p : (ℕ → ℝ) × (ℕ → ℝ) => Function.update p.1 i (p.2 j)) ⁻¹' Set.pi s t =
        Set.pi (s : Set ℕ) t ×ˢ (Set.univ : Set (ℕ → ℝ)) := by
      ext ⟨z, y⟩
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Finset.mem_coe, Set.mem_univ,
        and_true]
      refine forall₂_congr fun k hk => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hi)]
    rw [hset, Measure.prod_prod, measure_univ, mul_one, Measure.infinitePi_pi _ fun k _ => ht k]

/-- **(2.4) for the splitting estimator with a Milstein final step** (Giles 2015, §5.2, p. 36,
l. 1592–1600: "one can use the technique of "splitting" … for each set of Brownian increments up to
one fine timestep before the end, one uses a number of samples of the final Brownian increment to
produce an average payoff"; p. 38, l. 1635–1636: "Furthermore, one can revert to using the Milstein
approximation for the final timestep"; l. 1584–1590: "`E[P^c_{ℓ−1}] = E[P^f_{ℓ−1}]` … This ensures
that the identity in Equation (2.4) is respected").  Let the main increments `Z = (Z_0, Z_1, …)`
and the sub-samples `Y = (Y_0, Y_1, …)` be independent i.i.d. `N(0, 1)` sequences
(`stdNormalSeq.prod stdNormalSeq`), `M ≥ 1` sub-samples, any `a`, `b`, `g`, and the paths of
`map_milstein_coarse_eq_fine`.  The coarse splitting payoff of level `ℓ`,
`(1/M) ∑_{i<M} g(milsteinStep a b (2h) Ŝ^c_{N−2} (√h Z_{2n} + √h Y_i))` (the last coarse step
re-uses the known increment `ΔW_{N−2}` and the `i`-th sub-sample `√h Y_i` of `ΔW_{N−1}`), and the
fine splitting payoff of level `ℓ − 1`, `(1/M) ∑_{i<M} g(milsteinStep a b (2h) Ŝ^f (√(2h) Y_i))`,
have the same mean, `E[g(Ŝ^f_{N/2})]`, provided `g(Ŝ^f_{N/2})` is integrable for the Milstein path
of level `ℓ − 1` (e.g. any bounded `g`, as for the digital option).  Proof: each sub-sample term is
the payoff of a path whose last increment has been replaced by an independent normal
(`measurePreserving_update_prod`; the path before the last step does not change,
`milsteinPath_eq_of_eq_lt`), and `map_milstein_coarse_eq_fine`.

**Deviations.**  The coefficients are autonomous, `a(S)`, `b(S)`; the paper's splitting estimator
uses the same sub-samples for the fine path of level `ℓ` (not needed for (2.4)); for `h < 0` the
statement is degenerate (`√h = √(2h) = 0` in Lean).  The variance of the splitting estimator ("the
variance is the same, to leading order", l. 1597–1598) is not formalised here. -/
theorem splitting_milstein_mean_eq {a b : ℝ → ℝ} (h S₀ : ℝ) (n : ℕ) {M : ℕ} (hM : 0 < M)
    {g : ℝ → ℝ}
    (hint : Integrable (fun w => g (milsteinPath a b (2 * h) S₀ w (n + 1))) stdNormalSeq) :
    ∫ p, (∑ i ∈ range M, g (milsteinStep a b (2 * h)
        (milsteinPath a b (2 * h) S₀ (pairAvg p.1) n)
        (Real.sqrt h * p.1 (2 * n) + Real.sqrt h * p.2 i))) / M
        ∂(stdNormalSeq.prod stdNormalSeq) =
      ∫ p, (∑ i ∈ range M, g (milsteinStep a b (2 * h) (milsteinPath a b (2 * h) S₀ p.1 n)
        (Real.sqrt (2 * h) * p.2 i))) / M ∂(stdNormalSeq.prod stdNormalSeq) ∧
    ∫ p, (∑ i ∈ range M, g (milsteinStep a b (2 * h) (milsteinPath a b (2 * h) S₀ p.1 n)
        (Real.sqrt (2 * h) * p.2 i))) / M ∂(stdNormalSeq.prod stdNormalSeq) =
      ∫ w, g (milsteinPath a b (2 * h) S₀ w (n + 1)) ∂stdNormalSeq := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hpm := measurePreserving_pairAvg
  -- the payoffs of the coarse and the fine path, as functions of the increments
  set Ff : (ℕ → ℝ) → ℝ := fun w => g (milsteinStep a b (2 * h)
    (milsteinPath a b (2 * h) S₀ w n) (Real.sqrt (2 * h) * w n)) with hFf
  set Fc : (ℕ → ℝ) → ℝ := fun z => g (milsteinStep a b (2 * h)
    (milsteinPath a b (2 * h) S₀ (pairAvg z) n)
    (Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1))) with hFc
  have hFfi : Integrable Ff stdNormalSeq := hint
  have hcf : Fc = Ff ∘ pairAvg := by
    funext z
    have hs : Real.sqrt (2 * h) * pairAvg z n =
        Real.sqrt h * z (2 * n) + Real.sqrt h * z (2 * n + 1) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) h, pairAvg]
      field_simp
    rw [Function.comp_apply, hFc, hFf]
    beta_reduce
    rw [hs]
  have hFci : Integrable Fc stdNormalSeq := by
    rw [hcf]
    exact (hpm.integrable_comp hFfi.aestronglyMeasurable).2 hFfi
  have hEcf : ∫ z, Fc z ∂stdNormalSeq = ∫ w, Ff w ∂stdNormalSeq := by
    rw [hcf]
    exact integral_comp_of_measurePreserving hpm hFfi.aestronglyMeasurable
  -- a sub-sample replaces the last increment
  have hc : ∀ i, (fun p : (ℕ → ℝ) × (ℕ → ℝ) => g (milsteinStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ (pairAvg p.1) n)
      (Real.sqrt h * p.1 (2 * n) + Real.sqrt h * p.2 i))) =
      fun p => Fc (Function.update p.1 (2 * n + 1) (p.2 i)) := fun i => by
    funext p
    have hpath : milsteinPath a b (2 * h) S₀ (pairAvg (Function.update p.1 (2 * n + 1) (p.2 i))) n
        = milsteinPath a b (2 * h) S₀ (pairAvg p.1) n :=
      milsteinPath_eq_of_eq_lt a b (2 * h) S₀ fun k hk => by
        rw [pairAvg, pairAvg, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    rw [hFc]
    beta_reduce
    rw [hpath, Function.update_of_ne (by omega), Function.update_self]
  have hf : ∀ i, (fun p : (ℕ → ℝ) × (ℕ → ℝ) => g (milsteinStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ p.1 n) (Real.sqrt (2 * h) * p.2 i))) =
      fun p => Ff (Function.update p.1 n (p.2 i)) := fun i => by
    funext p
    have hpath : milsteinPath a b (2 * h) S₀ (Function.update p.1 n (p.2 i)) n =
        milsteinPath a b (2 * h) S₀ p.1 n :=
      milsteinPath_eq_of_eq_lt a b (2 * h) S₀ fun k hk => Function.update_of_ne (by omega) _ _
    rw [hFf]
    beta_reduce
    rw [hpath, Function.update_self]
  have hIc : ∀ i, ∫ p, g (milsteinStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ (pairAvg p.1) n)
      (Real.sqrt h * p.1 (2 * n) + Real.sqrt h * p.2 i)) ∂(stdNormalSeq.prod stdNormalSeq) =
      ∫ z, Fc z ∂stdNormalSeq := fun i => by
    rw [hc i]
    exact integral_comp_of_measurePreserving (measurePreserving_update_prod (2 * n + 1) i)
      hFci.aestronglyMeasurable
  have hIf : ∀ i, ∫ p, g (milsteinStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ p.1 n) (Real.sqrt (2 * h) * p.2 i))
      ∂(stdNormalSeq.prod stdNormalSeq) = ∫ w, Ff w ∂stdNormalSeq := fun i => by
    rw [hf i]
    exact integral_comp_of_measurePreserving (measurePreserving_update_prod n i)
      hFfi.aestronglyMeasurable
  have hic : ∀ i, Integrable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => g (milsteinStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ (pairAvg p.1) n)
      (Real.sqrt h * p.1 (2 * n) + Real.sqrt h * p.2 i))) (stdNormalSeq.prod stdNormalSeq) :=
    fun i => by
    rw [hc i]
    exact ((measurePreserving_update_prod (2 * n + 1) i).integrable_comp
      hFci.aestronglyMeasurable).2 hFci
  have hif : ∀ i, Integrable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => g (milsteinStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ p.1 n) (Real.sqrt (2 * h) * p.2 i)))
      (stdNormalSeq.prod stdNormalSeq) := fun i => by
    rw [hf i]
    exact ((measurePreserving_update_prod n i).integrable_comp
      hFfi.aestronglyMeasurable).2 hFfi
  have hfin : ∫ p, (∑ i ∈ range M, g (milsteinStep a b (2 * h)
      (milsteinPath a b (2 * h) S₀ p.1 n) (Real.sqrt (2 * h) * p.2 i))) / M
      ∂(stdNormalSeq.prod stdNormalSeq) = ∫ w, Ff w ∂stdNormalSeq := by
    rw [integral_div, integral_finsetSum _ fun i _ => hif i,
      Finset.sum_congr rfl fun i _ => hIf i, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel_left₀ _ hM']
  refine ⟨?_, hfin⟩
  rw [hfin, integral_div, integral_finsetSum _ fun i _ => hic i,
    Finset.sum_congr rfl fun i _ => hIc i, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hM', hEcf]

end MLMC
