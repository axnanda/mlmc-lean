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
  fine/coarse pair coupled by `pairAvg`.
* **The barrier option at `m` fixed monitoring dates** `t_k = kT/m` (`barrierPayoff`:
  `g(S_T) ∏_{k=1}^m 1_A(S_{t_k})` with `A = (−∞, B]`, up-and-out, or `A = (B, ∞)`, down-and-out,
  and `g` bounded and Lipschitz).  `gbm_em_barrier_rate`, `gbm_mil_barrier_rate`: the correction
  variance and the bias are `O(h^q)` for every `q < ½`, resp. `q < 1`, from the mismatch
  probabilities at the dates (a union bound over the dates of the marginal small-ball estimates,
  `gbm_mon_mismatch_rate_of_moment` with the density bound `gbmMonExact_smallBall` at every date)
  and the strong error at `t_m` (`barrierPayoff_sub_le`, `barrier_variance_le`, `barrier_bias_le`,
  `barrier_rate_of`).  `gbm_em_barrier_theorem1`, `gbm_mil_barrier_theorem1`: Theorem 1 end to end,
  cost `O(ε^{−3−η})`, resp. `O(ε^{−2−η})`.
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
(and Avikainen's `O(h^{1/2} log h)` of Table 5.2) are not proved, so the costs carry the loss
`η > 0`.  The barrier option of the paper is continuously monitored; its analysis (Giles, Higham and
Mao 2009) and the Milstein rows `O(h^{3/2})` of Table 5.2 (Brownian-bridge estimators) are out of
reach here; for the discretely monitored option with the natural estimators the rates are those of
the digital option.  Unbounded `g` (e.g. the down-and-out call) is not covered.  The variance of the
splitting estimator (l. 1597–1600, "the variance is the same, to leading order") is not formalised.

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
`O(ε^{−3−η})` for every `η > 0`** (Giles 2015, §5.1, p. 33, l. 1435–1449: "Figure 5.4 shows the
results for a digital call option … Consequently, this application has `α = 1`, `β = ½`, `γ = 1`,
leading to the MLMC complexity being `O(ε^{−2.5})`", with Theorem 1, §2.1, p. 6, and (2.4)).  For
`dS = rS dt + σS dW`, `S_0 = s₀`, `σ ≠ 0`, `T > 0`, any strike `K` and any `η > 0`: level `ℓ` uses
`2^ℓ` Euler–Maruyama steps of size `T 2^{−ℓ}`, the payoff is `H(Ŝ_ℓ − K) = 1_{Ŝ_ℓ > K}`, the
coarse path of a sample is driven by the summed increments, the samples are independent and a
level-`ℓ` sample costs `2^ℓ`.  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are
`L` and `N_ℓ ≥ 1` for which the multilevel estimator of
`E[H(S_T − K)] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)` has a square-integrable error with
mean square `< ε²`, at cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε^{−3−η}`.  No rate is assumed: Theorem 1 with
`α = β = q = 1/(2 + η) < ½`, `γ = 1` (`theorem1_pairAvg_of_rate`; cost
`ε^{−2−(1−q)/q} = ε^{−3−η}`), the weak rate `gbm_em_digital_weak_rate`, the variance rate
`gbm_em_digital_rate` and (2.4) (the coarse path is the fine path of the level below, driven by
`pairAvg`).

**How close to the paper.**  The paper's `O(ε^{−2.5})` uses the weak order `α = 1` of
Euler–Maruyama for the digital option (Bally and Talay 1996, not cited in the paper; a
Malliavin-calculus result that is out of scope here) together with `β = ½`.  Here `α` is only the
mismatch rate `q < ½`, and `β = q < ½` (the endpoint `β = ½` is not proved either,
`gbm_em_digital_rate`), so Theorem 1 gives `ε^{−2−(1−q)/q}`, i.e. `ε^{−3−η}` with `η > 0`
arbitrary but not `0`.  The constant `c₄` depends on `η`.

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

/-- The barrier sets `(−∞, B]` and `(B, ∞)` are measurable. -/
lemma measurableSet_barrier {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) :
    MeasurableSet A := by
  rcases hA with rfl | rfl
  · exact measurableSet_Iic
  · exact measurableSet_Ioi

/-- The barrier payoff is measurable for a measurable `g` and a measurable `A`. -/
lemma measurable_barrierPayoff {g : ℝ → ℝ} (hg : Measurable g) {A : Set ℝ}
    (hA : MeasurableSet A) (m : ℕ) : Measurable (barrierPayoff g A m) := by
  unfold barrierPayoff
  exact (hg.comp (measurable_pi_apply m)).mul (Finset.measurable_prod _ fun k _ =>
    (measurable_one.indicator hA).comp (measurable_pi_apply (k + 1)))

/-- If two products of knock-out indicators differ, one of the factors differs. -/
lemma prod_indicator_ne {A : Set ℝ} {m : ℕ} {a b : ℕ → ℝ}
    (h : ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) ≠
      ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (b (k + 1))) :
    ∃ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) ≠ A.indicator 1 (b (k + 1)) := by
  by_contra hcon
  exact h (Finset.prod_congr rfl fun k hk => not_not.1 fun hne => hcon ⟨k, hk, hne⟩)

/-- `(1_{a>B} − 1_{b>B})² ≤ (1_{c>B} − 1_{a>B})² + (1_{c>B} − 1_{b>B})²`: if the digital payoffs of
`a` and `b` differ, one of them differs from that of `c` (Giles 2015, §5.1, p. 33). -/
lemma sq_digital_sub_le_add (B a b c : ℝ) :
    ((Set.Ioi B).indicator (1 : ℝ → ℝ) a - (Set.Ioi B).indicator 1 b) ^ 2 ≤
      ((Set.Ioi B).indicator (1 : ℝ → ℝ) c - (Set.Ioi B).indicator 1 a) ^ 2 +
        ((Set.Ioi B).indicator (1 : ℝ → ℝ) c - (Set.Ioi B).indicator 1 b) ^ 2 := by
  rcases digital_eq_zero_or_one B a with h1 | h1 <;>
    rcases digital_eq_zero_or_one B b with h2 | h2 <;>
    rcases digital_eq_zero_or_one B c with h3 | h3 <;>
    · rw [h1, h2, h3]
      norm_num

/-- **The barrier payoff difference is controlled by the final values and the digital mismatches
at the dates** (Giles 2015, §5.1, p. 33: the barrier is "a discontinuous function"; the argument
for the digital option, l. 1436–1441, at every monitoring date).  For `g` with
`|g(x) − g(y)| ≤ K_g |x − y|` and `|g| ≤ M`, and `A = (−∞, B]` or `(B, ∞)`,
`|Φ(a) − Φ(b)| ≤ K_g |a_m − b_m| + M ∑_{k<m} (1_{a_{k+1}>B} − 1_{b_{k+1}>B})²` and
`(Φ(a) − Φ(b))² ≤ 2K_g² (a_m − b_m)² + 2M² ∑_{k<m} (1_{a_{k+1}>B} − 1_{b_{k+1}>B})²`: write
`Φ(a) − Φ(b) = (g(a_m) − g(b_m)) Π_a + g(b_m)(Π_a − Π_b)` with `Π ∈ [0, 1]`, and `Π_a ≠ Π_b` only
if the indicators differ at some date. -/
lemma barrierPayoff_sub_le {g : ℝ → ℝ} {Kg M : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hM : ∀ x, |g x| ≤ M) {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) (m : ℕ)
    (a b : ℕ → ℝ) :
    |barrierPayoff g A m a - barrierPayoff g A m b| ≤ Kg * |a m - b m| +
        M * ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (a (k + 1)) -
          (Set.Ioi B).indicator 1 (b (k + 1))) ^ 2 ∧
    (barrierPayoff g A m a - barrierPayoff g A m b) ^ 2 ≤ 2 * Kg ^ 2 * (a m - b m) ^ 2 +
        2 * M ^ 2 * ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (a (k + 1)) -
          (Set.Ioi B).indicator 1 (b (k + 1))) ^ 2 := by
  set P := ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) with hP
  set Q := ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (b (k + 1)) with hQ
  set S := ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (a (k + 1)) -
    (Set.Ioi B).indicator 1 (b (k + 1))) ^ 2 with hS
  have hKg : 0 ≤ Kg := (continuous_of_abs_sub_le hg).1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hind01 : ∀ x, 0 ≤ A.indicator (1 : ℝ → ℝ) x ∧ A.indicator (1 : ℝ → ℝ) x ≤ 1 := fun x => by
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun k _ => (hind01 _).1
  have hP1 : P ≤ 1 := Finset.prod_le_one (fun k _ => (hind01 _).1) fun k _ => (hind01 _).2
  have hQ0 : 0 ≤ Q := Finset.prod_nonneg fun k _ => (hind01 _).1
  have hQ1 : Q ≤ 1 := Finset.prod_le_one (fun k _ => (hind01 _).1) fun k _ => (hind01 _).2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  -- `|P − Q| ≤ I ≤ S` for some `I ∈ [0, 1]`
  obtain ⟨I, hI0, hI1, hPQ, hIS⟩ : ∃ I : ℝ, 0 ≤ I ∧ I ≤ 1 ∧ |P - Q| ≤ I ∧ I ≤ S := by
    by_cases hpq : P = Q
    · exact ⟨0, le_rfl, zero_le_one, by rw [hpq, sub_self, abs_zero], hS0⟩
    · refine ⟨1, zero_le_one, le_rfl, abs_le.2 ⟨by linarith, by linarith⟩, ?_⟩
      obtain ⟨k, hk, hne⟩ := prod_indicator_ne hpq
      have hne' := barrier_indicator_ne hA hne
      have h1 : ((Set.Ioi B).indicator (1 : ℝ → ℝ) (a (k + 1)) -
          (Set.Ioi B).indicator 1 (b (k + 1))) ^ 2 = 1 := by
        rcases digital_eq_zero_or_one B (a (k + 1)) with h1 | h1 <;>
          rcases digital_eq_zero_or_one B (b (k + 1)) with h2 | h2 <;>
          rw [h1, h2] at hne' ⊢ <;> first | exact absurd rfl hne' | norm_num
      rw [← h1]
      exact Finset.single_le_sum (f := fun k => ((Set.Ioi B).indicator (1 : ℝ → ℝ) (a (k + 1)) -
        (Set.Ioi B).indicator 1 (b (k + 1))) ^ 2) (fun i _ => sq_nonneg _) hk
  have e : barrierPayoff g A m a - barrierPayoff g A m b =
      (g (a m) - g (b m)) * P + g (b m) * (P - Q) := by
    simp only [barrierPayoff, hP, hQ]
    ring
  have hu : |(g (a m) - g (b m)) * P| ≤ Kg * |a m - b m| := by
    rw [abs_mul, abs_of_nonneg hP0]
    calc |g (a m) - g (b m)| * P ≤ Kg * |a m - b m| * 1 :=
          mul_le_mul (hg _ _) hP1 hP0 (by positivity)
      _ = _ := mul_one _
  have hv : |g (b m) * (P - Q)| ≤ M * I := by
    rw [abs_mul]
    exact mul_le_mul (hM _) hPQ (abs_nonneg _) hM0
  rw [e]
  constructor
  · calc |(g (a m) - g (b m)) * P + g (b m) * (P - Q)|
        ≤ |(g (a m) - g (b m)) * P| + |g (b m) * (P - Q)| := abs_add_le _ _
      _ ≤ Kg * |a m - b m| + M * I := add_le_add hu hv
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hIS hM0)
  · have h1 : ((g (a m) - g (b m)) * P) ^ 2 ≤ Kg ^ 2 * (a m - b m) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hu 2
      rwa [sq_abs, mul_pow Kg, sq_abs] at this
    have h2 : (g (b m) * (P - Q)) ^ 2 ≤ M ^ 2 * S := by
      have := pow_le_pow_left₀ (abs_nonneg _) hv 2
      rw [sq_abs, mul_pow M] at this
      have hII : I ^ 2 ≤ S := by nlinarith
      nlinarith [sq_nonneg M]
    nlinarith [sq_nonneg ((g (a m) - g (b m)) * P - g (b m) * (P - Q))]

/-- The barrier payoff is bounded by `M` when `|g| ≤ M`. -/
lemma abs_barrierPayoff_le {g : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |g x| ≤ M) (A : Set ℝ) (m : ℕ)
    (a : ℕ → ℝ) : |barrierPayoff g A m a| ≤ M := by
  have hind01 : ∀ x, 0 ≤ A.indicator (1 : ℝ → ℝ) x ∧ A.indicator (1 : ℝ → ℝ) x ≤ 1 := fun x => by
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hP0 : 0 ≤ ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) :=
    Finset.prod_nonneg fun k _ => (hind01 _).1
  have hP1 : ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) ≤ 1 :=
    Finset.prod_le_one (fun k _ => (hind01 _).1) fun k _ => (hind01 _).2
  rw [barrierPayoff, abs_mul, abs_of_nonneg hP0]
  calc |g (a m)| * ∏ k ∈ range m, A.indicator (1 : ℝ → ℝ) (a (k + 1)) ≤ M * 1 :=
        mul_le_mul (hM _) hP1 hP0 ((abs_nonneg _).trans (hM 0))
    _ = M := mul_one M

/-- The difference of two barrier payoffs of measurable paths is square integrable when `g` is
measurable and bounded (Giles 2015, §5.1; the correction of the barrier option). -/
lemma memLp_barrierPayoff_sub {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    {A : Set ℝ} (hA : MeasurableSet A) (m : ℕ) {U V : (ℕ → ℝ) → ℕ → ℝ} (hU : Measurable U)
    (hV : Measurable V) :
    MemLp (fun z => barrierPayoff g A m (U z) - barrierPayoff g A m (V z)) 2 stdNormalSeq :=
  (MemLp.of_bound ((measurable_barrierPayoff hg hA m).comp hU).aestronglyMeasurable M
      (Eventually.of_forall fun z => abs_barrierPayoff_le hM A m (U z))).sub
    (MemLp.of_bound ((measurable_barrierPayoff hg hA m).comp hV).aestronglyMeasurable M
      (Eventually.of_forall fun z => abs_barrierPayoff_le hM A m (V z)))

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

variable {g : ℝ → ℝ} {Kg M : ℝ} {A : Set ℝ} {B : ℝ} {m : ℕ} {X Y : ℕ → (ℕ → ℝ) → ℕ → ℝ}

/-- **The correction variance of the barrier option from the strong error at `t_m` and the
mismatch probabilities at the dates** (Giles 2015, §5.1, p. 33, l. 1436–1441 at every monitoring
date, and "`V_ℓ ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`", p. 29).  Let `X_j` be level-consistent exact
paths (`X_j ∘ pairAvg = X_{j+1}`) and `Y_j` approximations with
`E[(X_{j,t_m} − Y_{j,t_m})²] ≤ e₂(j)` and `P(1_{X_{j,t_{k+1}} > B} ≠ 1_{Y_{j,t_{k+1}} > B}) ≤ e₁(j)`
for `k < m`.  Then the correction `Φ(Y_{j+1}) − Φ(Y_j ∘ pairAvg)` of the barrier payoff `Φ`
(`barrierPayoff`) is square integrable with variance at most
`4K_g² (e₂(j+1) + e₂(j)) + 2M² m (e₁(j+1) + e₁(j))` (`barrierPayoff_sub_le`,
`sq_digital_sub_le_add`, `integral_sq_digital_sub`). -/
lemma barrier_variance_le (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|) (hM : ∀ x, |g x| ≤ M)
    (hA : A = Set.Iic B ∨ A = Set.Ioi B) (hXm : ∀ j, Measurable (X j))
    (hYm : ∀ j, Measurable (Y j)) (hX : ∀ j, MemLp (fun z => X j z m) 2 stdNormalSeq)
    (hY : ∀ j, MemLp (fun z => Y j z m) 2 stdNormalSeq)
    (hpair : ∀ j z, X j (pairAvg z) = X (j + 1) z) {e₂ e₁ : ℕ → ℝ}
    (hs2 : ∀ j, ∫ z, (X j z m - Y j z m) ^ 2 ∂stdNormalSeq ≤ e₂ j)
    (hmis : ∀ j k, k < m → stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X j z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y j z (k + 1))} ≤ e₁ j) (j : ℕ) :
    MemLp (fun z => barrierPayoff g A m (Y (j + 1) z) - barrierPayoff g A m (Y j (pairAvg z)))
        2 stdNormalSeq ∧
    variance (fun z => barrierPayoff g A m (Y (j + 1) z) - barrierPayoff g A m (Y j (pairAvg z)))
        stdNormalSeq ≤
      4 * Kg ^ 2 * (e₂ (j + 1) + e₂ j) + 2 * M ^ 2 * (m * (e₁ (j + 1) + e₁ j)) := by
  have hgc := (continuous_of_abs_sub_le hg).2
  have hΦm := measurable_barrierPayoff hgc.measurable (measurableSet_barrier hA) m
  have hpm := measurePreserving_pairAvg
  refine ⟨memLp_barrierPayoff_sub hgc.measurable hM (measurableSet_barrier hA) m (hYm (j + 1))
    ((hYm j).comp hpm.measurable), ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hXk : ∀ i k, Measurable fun z => X i z k := fun i k =>
    (measurable_pi_apply k).comp (hXm i)
  have hYk : ∀ i k, Measurable fun z => Y i z k := fun i k =>
    (measurable_pi_apply k).comp (hYm i)
  have hm : AEStronglyMeasurable (fun z => barrierPayoff g A m (Y (j + 1) z) -
      barrierPayoff g A m (Y j (pairAvg z))) stdNormalSeq :=
    ((hΦm.comp (hYm (j + 1))).sub ((hΦm.comp (hYm j)).comp hpm.measurable)).aestronglyMeasurable
  refine (variance_le_expectation_sq hm).trans ?_
  simp only [Pi.pow_apply]
  -- integrability of the four families of terms
  have hF₁ : Integrable (fun z => (X (j + 1) z m - Y (j + 1) z m) ^ 2) stdNormalSeq :=
    ((hX (j + 1)).sub (hY (j + 1))).integrable_sq
  have hF₀' : Integrable (fun z => (X j z m - Y j z m) ^ 2) stdNormalSeq :=
    ((hX j).sub (hY j)).integrable_sq
  have hF₀ : Integrable (fun z => (X j (pairAvg z) m - Y j (pairAvg z) m) ^ 2) stdNormalSeq :=
    (hpm.integrable_comp hF₀'.aestronglyMeasurable).2 hF₀'
  have hG : ∀ i k, Integrable (fun z => ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X i z (k + 1)) -
      (Set.Ioi B).indicator 1 (Y i z (k + 1))) ^ 2) stdNormalSeq := fun i k =>
    ((memLp_digital (hXk i (k + 1)) B).sub (memLp_digital (hYk i (k + 1)) B)).integrable_sq
  have hG₀ : ∀ k, Integrable (fun z => ((Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X j (pairAvg z) (k + 1)) - (Set.Ioi B).indicator 1 (Y j (pairAvg z) (k + 1))) ^ 2)
      stdNormalSeq := fun k =>
    (hpm.integrable_comp (hG j k).aestronglyMeasurable).2 (hG j k)
  -- the pointwise bound
  have hpt : ∀ z, (barrierPayoff g A m (Y (j + 1) z) - barrierPayoff g A m (Y j (pairAvg z))) ^ 2
      ≤ 4 * Kg ^ 2 * ((X (j + 1) z m - Y (j + 1) z m) ^ 2 +
          (X j (pairAvg z) m - Y j (pairAvg z) m) ^ 2) +
        2 * M ^ 2 * ∑ k ∈ range m, (((Set.Ioi B).indicator (1 : ℝ → ℝ) (X (j + 1) z (k + 1)) -
          (Set.Ioi B).indicator 1 (Y (j + 1) z (k + 1))) ^ 2 +
          ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X j (pairAvg z) (k + 1)) -
          (Set.Ioi B).indicator 1 (Y j (pairAvg z) (k + 1))) ^ 2) := fun z => by
    have h1 := (barrierPayoff_sub_le hg hM hA m (Y (j + 1) z) (Y j (pairAvg z))).2
    rw [hpair j z]
    have h2 : (Y (j + 1) z m - Y j (pairAvg z) m) ^ 2 ≤
        2 * (X (j + 1) z m - Y (j + 1) z m) ^ 2 + 2 * (X (j + 1) z m - Y j (pairAvg z) m) ^ 2 := by
      nlinarith [sq_nonneg (X (j + 1) z m - Y (j + 1) z m + (X (j + 1) z m - Y j (pairAvg z) m))]
    have h3 : ∑ k ∈ range m, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (Y (j + 1) z (k + 1)) -
        (Set.Ioi B).indicator 1 (Y j (pairAvg z) (k + 1))) ^ 2 ≤
        ∑ k ∈ range m, (((Set.Ioi B).indicator (1 : ℝ → ℝ) (X (j + 1) z (k + 1)) -
          (Set.Ioi B).indicator 1 (Y (j + 1) z (k + 1))) ^ 2 +
          ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X (j + 1) z (k + 1)) -
          (Set.Ioi B).indicator 1 (Y j (pairAvg z) (k + 1))) ^ 2) :=
      Finset.sum_le_sum fun k _ => sq_digital_sub_le_add B _ _ _
    have hK2 : 0 ≤ 2 * Kg ^ 2 := by positivity
    have hM2 : 0 ≤ 2 * M ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hK2, mul_le_mul_of_nonneg_left h3 hM2]
  have hR : Integrable (fun z => 4 * Kg ^ 2 * ((X (j + 1) z m - Y (j + 1) z m) ^ 2 +
          (X j (pairAvg z) m - Y j (pairAvg z) m) ^ 2) +
        2 * M ^ 2 * ∑ k ∈ range m, (((Set.Ioi B).indicator (1 : ℝ → ℝ) (X (j + 1) z (k + 1)) -
          (Set.Ioi B).indicator 1 (Y (j + 1) z (k + 1))) ^ 2 +
          ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X j (pairAvg z) (k + 1)) -
          (Set.Ioi B).indicator 1 (Y j (pairAvg z) (k + 1))) ^ 2)) stdNormalSeq :=
    ((hF₁.add hF₀).const_mul _).add ((integrable_finsetSum _ fun k _ =>
      (hG (j + 1) k).add (hG₀ k)).const_mul _)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hR
    (Eventually.of_forall hpt)).trans ?_
  -- the integrals of the terms
  have hI₀ : ∫ z, (X j (pairAvg z) m - Y j (pairAvg z) m) ^ 2 ∂stdNormalSeq ≤ e₂ j := by
    rw [integral_comp_of_measurePreserving hpm hF₀'.aestronglyMeasurable]
    exact hs2 j
  have hJ : ∀ i k, k < m → ∫ z, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X i z (k + 1)) -
      (Set.Ioi B).indicator 1 (Y i z (k + 1))) ^ 2 ∂stdNormalSeq ≤ e₁ i := fun i k hk => by
    rw [integral_sq_digital_sub (hXk i (k + 1)) (hYk i (k + 1)) B]
    exact hmis i k hk
  have hJ₀ : ∀ k, k < m → ∫ z, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X j (pairAvg z) (k + 1)) -
      (Set.Ioi B).indicator 1 (Y j (pairAvg z) (k + 1))) ^ 2 ∂stdNormalSeq ≤ e₁ j :=
    fun k hk => by
    rw [integral_comp_of_measurePreserving hpm (hG j k).aestronglyMeasurable]
    exact hJ j k hk
  have hF : Integrable (fun z => (X (j + 1) z m - Y (j + 1) z m) ^ 2 +
      (X j (pairAvg z) m - Y j (pairAvg z) m) ^ 2) stdNormalSeq := hF₁.add hF₀
  have hGk : ∀ k, Integrable (fun z => ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X (j + 1) z (k + 1)) -
      (Set.Ioi B).indicator 1 (Y (j + 1) z (k + 1))) ^ 2 +
      ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X j (pairAvg z) (k + 1)) -
      (Set.Ioi B).indicator 1 (Y j (pairAvg z) (k + 1))) ^ 2) stdNormalSeq := fun k =>
    (hG (j + 1) k).add (hG₀ k)
  rw [integral_add (hF.const_mul _) ((integrable_finsetSum _ fun k _ => hGk k).const_mul _),
    integral_const_mul, integral_const_mul, integral_add hF₁ hF₀,
    integral_finsetSum _ fun k _ => hGk k]
  have hsum : ∑ k ∈ range m, ∫ z, (((Set.Ioi B).indicator (1 : ℝ → ℝ) (X (j + 1) z (k + 1)) -
          (Set.Ioi B).indicator 1 (Y (j + 1) z (k + 1))) ^ 2 +
          ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X j (pairAvg z) (k + 1)) -
          (Set.Ioi B).indicator 1 (Y j (pairAvg z) (k + 1))) ^ 2) ∂stdNormalSeq ≤
      m * (e₁ (j + 1) + e₁ j) := by
    calc _ ≤ ∑ _k ∈ range m, (e₁ (j + 1) + e₁ j) := Finset.sum_le_sum fun k hk => by
          rw [integral_add (hG (j + 1) k) (hG₀ k)]
          exact add_le_add (hJ (j + 1) k (Finset.mem_range.1 hk))
            (hJ₀ k (Finset.mem_range.1 hk))
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK4 : 0 ≤ 4 * Kg ^ 2 := by positivity
  have hM2 : 0 ≤ 2 * M ^ 2 := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add (hs2 (j + 1)) hI₀) hK4)
    (mul_le_mul_of_nonneg_left hsum hM2)

/-- **The bias of the barrier option from the strong error at `t_m` and the mismatch
probabilities at the dates** (Giles 2015, §5.1, p. 33; condition (i) of Theorem 1, §2.1, p. 6).
In the setting of `barrier_variance_le`,
`|E[Φ(Y_j)] − E[Φ(X_0)]| ≤ K_g √(e₂(j)) + M m e₁(j)`: the law of `X_j` does not depend on `j`
(`integral_comp_monLevel`), `E|X_{j,t_m} − Y_{j,t_m}| ≤ √(e₂(j))` (Jensen), and the digital
mismatches at the dates cost at most `M` each (`barrierPayoff_sub_le`). -/
lemma barrier_bias_le (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|) (hM : ∀ x, |g x| ≤ M)
    (hA : A = Set.Iic B ∨ A = Set.Ioi B) (hXm : ∀ j, Measurable (X j))
    (hYm : ∀ j, Measurable (Y j)) (hX : ∀ j, MemLp (fun z => X j z m) 2 stdNormalSeq)
    (hY : ∀ j, MemLp (fun z => Y j z m) 2 stdNormalSeq)
    (hpair : ∀ j z, X j (pairAvg z) = X (j + 1) z) {e₂ e₁ : ℕ → ℝ}
    (hs2 : ∀ j, ∫ z, (X j z m - Y j z m) ^ 2 ∂stdNormalSeq ≤ e₂ j)
    (hmis : ∀ j k, k < m → stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X j z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y j z (k + 1))} ≤ e₁ j) (j : ℕ) :
    |∫ z, barrierPayoff g A m (Y j z) ∂stdNormalSeq -
        ∫ z, barrierPayoff g A m (X 0 z) ∂stdNormalSeq| ≤
      Kg * Real.sqrt (e₂ j) + M * (m * e₁ j) := by
  have hKg : 0 ≤ Kg := (continuous_of_abs_sub_le hg).1
  have hgc := (continuous_of_abs_sub_le hg).2
  have hΦm := measurable_barrierPayoff hgc.measurable (measurableSet_barrier hA) m
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hXk : ∀ k, Measurable fun z => X j z k := fun k => (measurable_pi_apply k).comp (hXm j)
  have hYk : ∀ k, Measurable fun z => Y j z k := fun k => (measurable_pi_apply k).comp (hYm j)
  have hint : ∀ W : (ℕ → ℝ) → ℕ → ℝ, Measurable W →
      Integrable (fun z => barrierPayoff g A m (W z)) stdNormalSeq := fun W hW =>
    Integrable.of_bound (hΦm.comp hW).aestronglyMeasurable M
      (Eventually.of_forall fun z => abs_barrierPayoff_le hM A m (W z))
  rw [← integral_comp_monLevel hpair hXm hΦm j,
    ← integral_sub (hint _ (hYm j)) (hint _ (hXm j))]
  refine abs_integral_le_integral_abs.trans ?_
  have hG : ∀ k, Integrable (fun z => ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X j z (k + 1)) -
      (Set.Ioi B).indicator 1 (Y j z (k + 1))) ^ 2) stdNormalSeq := fun k =>
    ((memLp_digital (hXk (k + 1)) B).sub (memLp_digital (hYk (k + 1)) B)).integrable_sq
  have hD : MemLp (fun z => X j z m - Y j z m) 2 stdNormalSeq := (hX j).sub (hY j)
  have hIabs : Integrable (fun z => |X j z m - Y j z m|) stdNormalSeq :=
    (hD.integrable one_le_two).abs
  have hpt : ∀ z, |barrierPayoff g A m (Y j z) - barrierPayoff g A m (X j z)| ≤
      Kg * |X j z m - Y j z m| + M * ∑ k ∈ range m,
        ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X j z (k + 1)) -
          (Set.Ioi B).indicator 1 (Y j z (k + 1))) ^ 2 := fun z => by
    rw [abs_sub_comm]
    exact (barrierPayoff_sub_le hg hM hA m (X j z) (Y j z)).1
  have hR : Integrable (fun z => Kg * |X j z m - Y j z m| + M * ∑ k ∈ range m,
        ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X j z (k + 1)) -
          (Set.Ioi B).indicator 1 (Y j z (k + 1))) ^ 2) stdNormalSeq :=
    (hIabs.const_mul Kg).add ((integrable_finsetSum _ fun k _ => hG k).const_mul M)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hR
    (Eventually.of_forall hpt)).trans ?_
  rw [integral_add (hIabs.const_mul Kg) ((integrable_finsetSum _ fun k _ => hG k).const_mul M),
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun k _ => hG k]
  have habs : ∫ z, |X j z m - Y j z m| ∂stdNormalSeq ≤ Real.sqrt (e₂ j) := by
    have h1 := sq_integral_le_integral_sq_of_memLp (X := fun z => |X j z m - Y j z m|) hD.norm
    simp only [sq_abs] at h1
    exact (le_abs_self _).trans (Real.abs_le_sqrt (h1.trans (hs2 j)))
  have hsum : ∑ k ∈ range m, ∫ z, ((Set.Ioi B).indicator (1 : ℝ → ℝ) (X j z (k + 1)) -
      (Set.Ioi B).indicator 1 (Y j z (k + 1))) ^ 2 ∂stdNormalSeq ≤ m * e₁ j := by
    calc _ ≤ ∑ _k ∈ range m, e₁ j := Finset.sum_le_sum fun k hk => by
          rw [integral_sq_digital_sub (hXk (k + 1)) (hYk (k + 1)) B]
          exact hmis j k (Finset.mem_range.1 hk)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left habs hKg) (mul_le_mul_of_nonneg_left hsum hM0)

end BarrierAbstract

section BarrierRate

variable {g : ℝ → ℝ} {Kg M : ℝ} {A : Set ℝ} {B : ℝ} {m : ℕ} {X Y : ℕ → (ℕ → ℝ) → ℕ → ℝ}

/-- **The barrier rates from the strong error and the mismatch rate** (Giles 2015, §5.1–§5.2,
Table 5.2, row "barrier").  In the setting of `barrier_variance_le`, with steps `h_j = T 2^{−j}`
(`T > 0`), `E[(X_{j,t_m} − Y_{j,t_m})²] ≤ E h_j^κ` and mismatch probabilities `≤ C h_j^q` at the
dates, for `q ≤ κ/2`: there is `C'` such that the correction `Φ(Y_{j+1}) − Φ(Y_j ∘ pairAvg)` is
square integrable with variance `≤ C' h_{j+1}^q`, and
`|E[Φ(Y_j)] − E[Φ(X_0)]| ≤ C' h_j^q` (`barrier_variance_le`, `barrier_bias_le`,
`dyadic_rpow_add_le`, `rpow_le_rpow_sub_mul_rpow`). -/
lemma barrier_rate_of (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|) (hM : ∀ x, |g x| ≤ M)
    (hA : A = Set.Iic B ∨ A = Set.Ioi B) (hXm : ∀ j, Measurable (X j))
    (hYm : ∀ j, Measurable (Y j)) (hX : ∀ j, MemLp (fun z => X j z m) 2 stdNormalSeq)
    (hY : ∀ j, MemLp (fun z => Y j z m) 2 stdNormalSeq)
    (hpair : ∀ j z, X j (pairAvg z) = X (j + 1) z) {T : ℝ} (hT : 0 < T) {κ : ℕ} {E C q : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hqκ : q ≤ κ / 2)
    (hs2 : ∀ j, ∫ z, (X j z m - Y j z m) ^ 2 ∂stdNormalSeq ≤ E * (T / 2 ^ j) ^ κ)
    (hmis : ∀ j k, k < m → stdNormalSeq.real {z | (Set.Ioi B).indicator (1 : ℝ → ℝ)
      (X j z (k + 1)) ≠ (Set.Ioi B).indicator 1 (Y j z (k + 1))} ≤ C * (T / 2 ^ j) ^ q) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ j : ℕ,
      MemLp (fun z => barrierPayoff g A m (Y (j + 1) z) -
          barrierPayoff g A m (Y j (pairAvg z))) 2 stdNormalSeq ∧
      variance (fun z => barrierPayoff g A m (Y (j + 1) z) -
          barrierPayoff g A m (Y j (pairAvg z))) stdNormalSeq ≤ C' * (T / 2 ^ (j + 1)) ^ q ∧
      |∫ z, barrierPayoff g A m (Y j z) ∂stdNormalSeq -
          ∫ z, barrierPayoff g A m (X 0 z) ∂stdNormalSeq| ≤ C' * (T / 2 ^ j) ^ q := by
  have hKg := (continuous_of_abs_sub_le hg).1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hκ0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  have hκq : q ≤ (κ : ℝ) := by linarith
  set Cv := 4 * Kg ^ 2 * E * (T ^ ((κ : ℝ) - q) * (1 + 2 ^ q)) +
    2 * M ^ 2 * m * C * (1 + 2 ^ q) with hCv
  set Cb := Kg * Real.sqrt E * T ^ ((κ : ℝ) / 2 - q) + M * m * C with hCb
  have hCv0 : 0 ≤ Cv := by positivity
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨Cv + Cb, by positivity, fun j =>
    ⟨(barrier_variance_le hg hM hA hXm hYm hX hY hpair hs2 hmis j).1, ?_, ?_⟩⟩
  · have hv := (barrier_variance_le hg hM hA hXm hYm hX hY hpair hs2 hmis j).2
    have hd1 : (T / 2 ^ (j + 1)) ^ κ + (T / 2 ^ j) ^ κ ≤
        T ^ ((κ : ℝ) - q) * (1 + 2 ^ q) * (T / 2 ^ (j + 1)) ^ q := by
      have := dyadic_rpow_add_le hT hκq j
      rwa [Real.rpow_natCast, Real.rpow_natCast] at this
    have hd2 : (T / 2 ^ (j + 1)) ^ q + (T / 2 ^ j) ^ q ≤ (1 + 2 ^ q) * (T / 2 ^ (j + 1)) ^ q := by
      have := dyadic_rpow_add_le hT (le_refl q) j
      rwa [sub_self, Real.rpow_zero, one_mul] at this
    have hpos : 0 ≤ (T / 2 ^ (j + 1)) ^ q := by positivity
    calc _ ≤ _ := hv
      _ = 4 * Kg ^ 2 * E * ((T / 2 ^ (j + 1)) ^ κ + (T / 2 ^ j) ^ κ) +
          2 * M ^ 2 * m * C * ((T / 2 ^ (j + 1)) ^ q + (T / 2 ^ j) ^ q) := by ring
      _ ≤ 4 * Kg ^ 2 * E * (T ^ ((κ : ℝ) - q) * (1 + 2 ^ q) * (T / 2 ^ (j + 1)) ^ q) +
          2 * M ^ 2 * m * C * ((1 + 2 ^ q) * (T / 2 ^ (j + 1)) ^ q) :=
          add_le_add (mul_le_mul_of_nonneg_left hd1 (by positivity))
            (mul_le_mul_of_nonneg_left hd2 (by positivity))
      _ = Cv * (T / 2 ^ (j + 1)) ^ q := by rw [hCv]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hpos
  · have hb := barrier_bias_le hg hM hA hXm hYm hX hY hpair hs2 hmis j
    have hh : 0 < T / 2 ^ j := by positivity
    have hhT : T / 2 ^ j ≤ T := div_le_self hT.le (one_le_pow₀ (by norm_num))
    have hpos : 0 ≤ (T / 2 ^ j) ^ q := by positivity
    have hsq : Real.sqrt (E * (T / 2 ^ j) ^ κ) = Real.sqrt E * (T / 2 ^ j) ^ ((κ : ℝ) / 2) := by
      rw [Real.sqrt_mul hE, Real.sqrt_eq_rpow ((T / 2 ^ j) ^ κ), ← Real.rpow_natCast,
        ← Real.rpow_mul hh.le]
      ring_nf
    have hr := rpow_le_rpow_sub_mul_rpow hh hhT hqκ
    calc _ ≤ _ := hb
      _ = Kg * Real.sqrt E * (T / 2 ^ j) ^ ((κ : ℝ) / 2) + M * m * C * (T / 2 ^ j) ^ q := by
          rw [hsq]
          ring
      _ ≤ Kg * Real.sqrt E * (T ^ ((κ : ℝ) / 2 - q) * (T / 2 ^ j) ^ q) +
          M * m * C * (T / 2 ^ j) ^ q :=
          add_le_add (mul_le_mul_of_nonneg_left hr (by positivity)) le_rfl
      _ = Cb * (T / 2 ^ j) ^ q := by rw [hCb]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hpos

end BarrierRate

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
`t_k = kT/m`, a payoff `g` with `|g(x) − g(y)| ≤ K_g |x − y|` and `|g| ≤ M`, and the knock-out set
`A = (−∞, B]` (up-and-out) or `A = (B, ∞)` (down-and-out), level `j` with `m 2^j` steps of size
`h_j = T/(m 2^j)` (`gbmMonEM`): for every `q < ½` there is `C` such that the correction
`Φ(Ŝ^f_{j+1}) − Φ(Ŝ^c_j)` (the coarse path driven by the summed increments) is square integrable
with variance `≤ C h_{j+1}^q`, and `|E[Φ(Ŝ_j)] − E[Φ(S)]| ≤ C h_j^q`, `Φ = barrierPayoff g A m`
and `S` the exact solution at the dates (`gbmMonExact … 0`).  Proof: the mismatch probability at
every date is `O(h_j^q)` (`gbm_mon_mismatch_rate_of_moment` with the `L^{2p}` strong errors
`gbmMon_em_moment_error` and the density bound `gbmMonExact_smallBall`: a union bound over the dates
of the marginal small-ball estimates), and the Lipschitz part is `O(h_j)`
(`gbm_em_monitored_strong_error`); `barrier_rate_of`.

**How close to the paper.**  The paper's barrier option is continuously monitored (its maximum or
minimum over `[0, T]`), and the analysis column of Table 5.2 is due to Giles, Higham and Mao
(2009); here the barrier is monitored at the `m` fixed dates, which lie on every grid, so no
Brownian-bridge argument is needed.  `g` is bounded: this covers the up-and-out call
`max(S_T − K, 0) 1{max_k S_{t_k} ≤ B}`, which equals the payoff with the bounded `1`-Lipschitz
`g(x) = max(min(x, B) − K, 0)`, but not the down-and-out call (unbounded `g`). -/
theorem gbm_em_barrier_rate (r σ s₀ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {m : ℕ}
    (hm : 0 < m) {g : ℝ → ℝ} {Kg M : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hM : ∀ x, |g x| ≤ M) {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) {q : ℝ}
    (hq : q < 1 / 2) :
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
  obtain ⟨C, hC, hmis⟩ := gbm_mon_mismatch_rate_of_moment r σ s₀ hσ hT hm B one_pos
    (Y := gbmMonEM r σ T s₀ m) (fun hs0 j z k => by rw [gbmMonEM_eq_prod, hs0, zero_mul])
    (fun p hp => ⟨gbmEMMomentConst p r σ T s₀, gbmEMMomentConst_nonneg p r σ s₀ hT.le,
      fun j k hk => ⟨integrable_gbmMon_em_err_pow r σ T s₀ m j (by positivity) k p, by
        rw [one_mul]
        exact gbmMon_em_moment_error r σ s₀ hT.le m j hk hp⟩⟩) hq'
  have e : ∀ j : ℕ, T / (m * 2 ^ j) = T / m / 2 ^ j := fun j => (div_div T m (2 ^ j)).symm
  obtain ⟨C', hC', h⟩ := barrier_rate_of hg hM hA (X := gbmMonExact r σ T s₀ m)
    (Y := gbmMonEM r σ T s₀ m) (fun j => (measurable_memLp_gbmMonExact r σ T s₀ m j).1)
    (fun j => (measurable_memLp_gbmMonEM r σ T s₀ m j).1)
    (fun j => (measurable_memLp_gbmMonExact r σ T s₀ m j).2 m)
    (fun j => (measurable_memLp_gbmMonEM r σ T s₀ m j).2 m)
    (gbmMonExact_pairAvg r σ T s₀ m) hTm (κ := 1) (q := q) (gbmStrongConst_nonneg r σ s₀ hT.le) hC
    (by push_cast; linarith)
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
`V_ℓ = O(h_ℓ^q)` and bias `O(h_ℓ^q)` for every `q < 1`** (Giles 2015, §5.2, p. 35, the natural
estimator of a discontinuous payoff, l. 1525–1532: "small differences in the coarse and fine path
simulations can lead to an `O(1)` difference in the payoff function … giving `V_ℓ = O(h_ℓ)`"; Table
5.2, l. 1430, row "barrier").  In the setting of `gbm_em_barrier_rate` with the Milstein scheme
(`gbmMonMil`): for every `q < 1` there is `C` such that the correction is square integrable with
`V[Φ(Ŝ^f_{j+1}) − Φ(Ŝ^c_j)] ≤ C h_{j+1}^q`, and `|E[Φ(Ŝ_j)] − E[Φ(S)]| ≤ C h_j^q`.  Proof: as
`gbm_em_barrier_rate` with `gbmMon_mil_moment_error` (`κ = 2`) and
`gbm_mil_monitored_strong_error`.

**How close to the paper.**  The Milstein row of Table 5.2 for the barrier (`O(h^{3/2})`,
`o(h^{3/2−δ})`) is for the continuously monitored option with the Brownian-bridge (conditional
expectation) estimator of §5.2 (Giles 2008a; Giles, Debrabant and Rößler 2013), which is not
formalised; for the natural estimator of the discretely monitored option the rate is `O(h_ℓ)` up
to the loss in the exponent, as for the digital option. -/
theorem gbm_mil_barrier_rate (r σ s₀ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {m : ℕ}
    (hm : 0 < m) {g : ℝ → ℝ} {Kg M : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hM : ∀ x, |g x| ≤ M) {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) {q : ℝ}
    (hq : q < 1) :
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
  obtain ⟨C, hC, hmis⟩ := gbm_mon_mismatch_rate_of_moment r σ s₀ hσ hT hm B two_pos
    (Y := gbmMonMil r σ T s₀ m) (fun hs0 j z k => by rw [gbmMonMil_eq_prod, hs0, zero_mul])
    (fun p hp => ⟨gbmMilMomentConst p r σ T s₀, gbmMilMomentConst_nonneg p r σ s₀ hT.le,
      fun j k hk => ⟨integrable_gbmMon_mil_err_pow r σ T s₀ m j (by positivity) k p,
        gbmMon_mil_moment_error r σ s₀ hT.le m j hk hp⟩⟩) hq'
  have e : ∀ j : ℕ, T / (m * 2 ^ j) = T / m / 2 ^ j := fun j => (div_div T m (2 ^ j)).symm
  obtain ⟨C', hC', h⟩ := barrier_rate_of hg hM hA (X := gbmMonExact r σ T s₀ m)
    (Y := gbmMonMil r σ T s₀ m) (fun j => (measurable_memLp_gbmMonExact r σ T s₀ m j).1)
    (fun j => (measurable_memLp_gbmMonMil r σ T s₀ m j).1)
    (fun j => (measurable_memLp_gbmMonExact r σ T s₀ m j).2 m)
    (fun j => (measurable_memLp_gbmMonMil r σ T s₀ m j).2 m)
    (gbmMonExact_pairAvg r σ T s₀ m) hTm (κ := 2) (q := q)
    (gbmMilStrongConst_nonneg r σ s₀ hT.le) hC
    (by push_cast; linarith)
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
(`σ ≠ 0`, `T > 0`, `m ≥ 1` dates, `g` bounded and Lipschitz, up-and-out or down-and-out), level
`j` uses `m 2^j` Euler–Maruyama steps, the coarse path of a sample is driven by the summed
increments, the samples are independent and a level-`j` sample costs `m 2^j`.  Then for every
`η > 0` there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_j ≥ 1` for which
the multilevel estimator of `E[g(S_T) ∏_{k=1}^m 1_A(S_{t_k})]` (`S = gbmMonExact … 0`, the exact
solution at the dates) has a square-integrable error with mean square `< ε²`, at cost
`∑_{j≤L} N_j m 2^j ≤ c₄ ε^{−3−η}`.  No rate is assumed: `α = β = q = 1/(2 + η)` and `γ = 1`
(`gbm_em_barrier_rate`, `theorem1_pairAvg_of_rate`).  As for the digital option
(`gbm_em_digital_theorem1`), the paper's weak order `α = 1` is not proved, and `σ ≠ 0` is needed
(for `m = 1`, `g = 1`, `A = (B, ∞)` the barrier payoff is the digital payoff). -/
theorem gbm_em_barrier_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {m : ℕ}
    (hm : 0 < m) {g : ℝ → ℝ} {Kg M : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hM : ∀ x, |g x| ≤ M) {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) {η : ℝ}
    (hη : 0 < η) :
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
  have hΦm := measurable_barrierPayoff hgc.measurable (measurableSet_barrier hA) m
  obtain ⟨C, -, hC⟩ := gbm_em_barrier_rate r σ s₀ hσ hT hm hg hM hA hq
  have e : ∀ j : ℕ, T / (m * 2 ^ j) = T / m / 2 ^ j := fun j => (div_div T m (2 ^ j)).symm
  obtain ⟨c₄, hc₄, h⟩ := theorem1_pairAvg_of_rate hTm hq0 (by linarith)
    (Pf := fun j z => barrierPayoff g A m (gbmMonEM r σ T s₀ m j z))
    (P := fun z => barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z))
    (fun j => hΦm.comp (measurable_memLp_gbmMonEM r σ T s₀ m j).1)
    (fun j => MemLp.of_bound (hΦm.comp (measurable_memLp_gbmMonEM r σ T s₀ m j).1
      ).aestronglyMeasurable M (Eventually.of_forall fun z => abs_barrierPayoff_le hM A m _))
    (Integrable.of_bound (hΦm.comp (measurable_memLp_gbmMonExact r σ T s₀ m 0).1
      ).aestronglyMeasurable M (Eventually.of_forall fun z => abs_barrierPayoff_le hM A m _))
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
l. 1525–1532, and Table 5.2, row "barrier", with Theorem 1, §2.1, p. 6, and (2.4)).  In the setting
of `gbm_mil_barrier_rate`, with `m 2^j` Milstein steps on level `j` and cost `m 2^j` per sample:
for every `η > 0` there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_j ≥ 1`
with a square-integrable error of mean square `< ε²` and cost `∑_{j≤L} N_j m 2^j ≤ c₄ ε^{−2−η}`.
No rate is assumed: `α = β = q = 1/(1 + η)`, `γ = 1` (`gbm_mil_barrier_rate`,
`theorem1_pairAvg_of_rate`). -/
theorem gbm_mil_barrier_theorem1 (r σ s₀ : ℝ) {T : ℝ} (hσ : σ ≠ 0) (hT : 0 < T) {m : ℕ}
    (hm : 0 < m) {g : ℝ → ℝ} {Kg M : ℝ} (hg : ∀ x y, |g x - g y| ≤ Kg * |x - y|)
    (hM : ∀ x, |g x| ≤ M) {A : Set ℝ} {B : ℝ} (hA : A = Set.Iic B ∨ A = Set.Ioi B) {η : ℝ}
    (hη : 0 < η) :
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
  have hΦm := measurable_barrierPayoff hgc.measurable (measurableSet_barrier hA) m
  obtain ⟨C, -, hC⟩ := gbm_mil_barrier_rate r σ s₀ hσ hT hm hg hM hA hq
  have e : ∀ j : ℕ, T / (m * 2 ^ j) = T / m / 2 ^ j := fun j => (div_div T m (2 ^ j)).symm
  obtain ⟨c₄, hc₄, h⟩ := theorem1_pairAvg_of_rate hTm hq0 hq
    (Pf := fun j z => barrierPayoff g A m (gbmMonMil r σ T s₀ m j z))
    (P := fun z => barrierPayoff g A m (gbmMonExact r σ T s₀ m 0 z))
    (fun j => hΦm.comp (measurable_memLp_gbmMonMil r σ T s₀ m j).1)
    (fun j => MemLp.of_bound (hΦm.comp (measurable_memLp_gbmMonMil r σ T s₀ m j).1
      ).aestronglyMeasurable M (Eventually.of_forall fun z => abs_barrierPayoff_le hM A m _))
    (Integrable.of_bound (hΦm.comp (measurable_memLp_gbmMonExact r σ T s₀ m 0).1
      ).aestronglyMeasurable M (Eventually.of_forall fun z => abs_barrierPayoff_le hM A m _))
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
