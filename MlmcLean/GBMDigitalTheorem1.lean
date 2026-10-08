import MlmcLean.GBMStrongLp
import MlmcLean.GBMPathDependent

/-!
# The digital option for GBM end to end (Giles 2015, §5.1–§5.2)

(module docstring to be written)
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### Generic tools -/

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
  have h3 : h ^ ((p : ℝ) / (2 * m + 1)) ≤ T ^ ((p : ℝ) / (2 * m + 1) - q) * h ^ q := by
    have hd : 0 ≤ (p : ℝ) / (2 * m + 1) - q := sub_nonneg.2 hq
    calc h ^ ((p : ℝ) / (2 * m + 1)) = h ^ q * h ^ ((p : ℝ) / (2 * m + 1) - q) := by
          rw [← Real.rpow_add hh, add_sub_cancel]
      _ ≤ h ^ q * T ^ ((p : ℝ) / (2 * m + 1) - q) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh.le hhT hd) (Real.rpow_nonneg hh.le _)
      _ = _ := mul_comm _ _
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

**How close to the paper.**  The paper's §5.1 does not state the weak order of the digital option;
its complexity `O(ε^{−2.5})` (l. 1447–1449) uses `α = 1`, the weak order one of Euler–Maruyama for
the digital option (Bally and Talay 1995), which is not proved here: the mismatch probability only
gives `α = q < ½`.  `σ ≠ 0` is needed (see `gbm_em_digital_theorem1`). -/
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
Euler–Maruyama for the digital option (Bally and Talay 1995, an Itô–Malliavin result that is out of
scope here) together with `β = ½`.  Here `α` is only the mismatch rate `q < ½`, and `β = q < ½`
(the endpoint `β = ½` is not proved either, `gbm_em_digital_rate`); with `α = ½ − δ'` the bound of
Theorem 1 is `ε^{−3−η}`.  The constant `c₄` depends on `η` and blows up as `η → 0`.

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

/-- **The discretely monitored knock-out (barrier) payoff** (Giles 2015, §5.1, p. 33, l. 1452–1454:
"the barrier is a discontinuous function of the maximum or minimum"; Table 5.2, row "barrier"):
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

end MLMC
