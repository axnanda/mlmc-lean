import MlmcLean.ControlVariate
import MlmcLean.Randomised

/-!
# The error analysis behind the MLMC algorithm (Giles 2015, §2.1, §3.1 and §3.3)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1 (pp. 6–7),
§3.1 (p. 21) and §3.3 (pp. 22–23) of the author's version.

* **§2.1, p. 6.** "To ensure that the MSE is less than `ε²`, it is sufficient to ensure that `V[Y]`
  and `(E[P_L − P])²` are both less than `½ε²`" (`mse_lt_of_half`).
* **§2.1, p. 7.** "If condition iii) is tightened slightly to be a bound on `E[(P_ℓ − P_{ℓ−1})²]` …
  then it would follow immediately that `α ≥ ½β`."  Read literally this is false (`α` can be any
  valid rate in i)); what follows is that condition i) holds with `α = β/2`
  (`weak_rate_of_second_moment`).
* **§3.1, (3.1).** `N_ℓ = ⌈2ε⁻² √(V_ℓ/C_ℓ) ∑_{ℓ'} √(V_ℓ' C_ℓ')⌉` "ensures that the … variance of the
  combined multilevel estimator is less than `½ε²`" (`allocation_eq_3_1`, with `≤`: equality
  occurs when every argument of `⌈·⌉` is an integer).
* **§3.1, p. 21.** "If `E[P_ℓ − P_{ℓ−1}] ∝ 2^{−αℓ}` then the remaining error is
  `E[P − P_L] = ∑_{ℓ=L+1}^∞ E[P_ℓ − P_{ℓ−1}] = E[P_L − P_{L−1}]/(2^α − 1)`", which gives the
  convergence test `|E[P_L − P_{L−1}]|/(2^α − 1) < ε/√2` (`remaining_error`,
  `convergence_test_mse`).
* **§3.3, p. 22.** The consistency check: `E[a − b + c] = 0` when (2.4) holds
  (`consistency_mean`), and "`√V[a − b + c] ≤ √V[a] + √V[b] + √V[c]`" (`consistency_sd`, from
  the Cauchy–Schwarz inequality for covariances, `covariance_sq_le`).
* **§3.3, pp. 22–23.** "The standard deviation of the sample variance for a random variable `X` with
  zero mean is approximately `√((κ − 1)/N) E[X²]` where the kurtosis `κ` is defined as
  `κ = E[X⁴]/(E[X²])²`": exact for the sample variance with known mean (`sampleVariance_sd`).  For
  corrections with values in `{−1, 0, 1}`, "`κ ≈ (p + q)⁻¹`" holds with equality
  (`kurtosis_of_ternary`), and `κ_ℓ → ∞` as `E[X_ℓ²] → 0` (`tendsto_kurtosis_atTop`).
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### §2.1: the MSE budget and the weak rate from second moments -/

/-- Giles 2015, §2.1, p. 6: "To ensure that the MSE is less than `ε²`, it is sufficient to ensure
that `V[Y]` and `(E[P_L − P])²` are both less than `½ε²`."  Here `Y` is a square-integrable
estimator with `E[Y] = E[P_L]` (as in (2.3)). -/
theorem mse_lt_of_half {Y P PL : Ω → ℝ} (hY : MemLp Y 2 μ) (hP : Integrable P μ)
    (hPL : Integrable PL μ) (hmean : μ[Y] = μ[PL]) {ε : ℝ} (hV : variance Y μ < ε ^ 2 / 2)
    (hbias : (∫ ω, PL ω - P ω ∂μ) ^ 2 < ε ^ 2 / 2) :
    μ[fun ω => (Y ω - μ[P]) ^ 2] < ε ^ 2 := by
  rw [mse_eq_variance_add_sq_bias hY (μ[P]), hmean, ← integral_sub hPL hP]
  linarith

/-- Giles 2015, §2.1, p. 7: "if condition iii) is tightened slightly to be a bound on
`E[(P_ℓ − P_{ℓ−1})²]` … then it would follow immediately that `α ≥ ½β`."  Precisely: if
`E[(P_ℓ − P_{ℓ−1})²] ≤ c₂ 2^{−βℓ}` for `ℓ ≥ 1` and `E[P_ℓ] → E[P]`, then condition i) of Theorem 1
holds with `α = β/2`: `|E[P_ℓ − P]| ≤ c₁ 2^{−βℓ/2}` with `c₁ = √c₂ / (2^{β/2} − 1)`. -/
theorem weak_rate_of_second_moment {P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {β c₂ : ℝ} (hβ : 0 < β)
    (hc₂ : 0 ≤ c₂) (hP : Integrable P μ) (hPl : ∀ ℓ, MemLp (Pl ℓ) 2 μ)
    (hlim : Tendsto (fun ℓ => μ[Pl ℓ]) atTop (𝓝 (μ[P])))
    (h_iii : ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∫ ω, levelDiff Pl ℓ ω ^ 2 ∂μ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) (ℓ : ℕ) :
    |∫ ω, Pl ℓ ω - P ω ∂μ| ≤
      Real.sqrt c₂ / ((2 : ℝ) ^ (β / 2) - 1) * (2 : ℝ) ^ (-(β / 2 * (ℓ : ℝ))) := by
  have hPl1 : ∀ ℓ, Integrable (Pl ℓ) μ := fun ℓ => (hPl ℓ).integrable one_le_two
  -- the ratio `r = 2^{−β/2} ∈ (0, 1)`
  set r : ℝ := (2 : ℝ) ^ (-(β / 2)) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos two_pos _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hrpow : ∀ n : ℕ, (2 : ℝ) ^ (-(β / 2 * (n : ℝ))) = r ^ n := fun n => by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), neg_mul]
  have hsq : ∀ m : ℕ, (2 : ℝ) ^ (-(β * (m : ℝ))) = (r ^ m) ^ 2 := fun m => by
    rw [← pow_mul, mul_comm m 2, ← hrpow]
    congr 1
    push_cast
    ring
  -- one step: `|E[P_{k+1}] − E[P_k]| ≤ √E[(P_{k+1} − P_k)²] ≤ √c₂ r^{k+1}`
  have hstep : ∀ k : ℕ, |μ[Pl (k + 1)] - μ[Pl k]| ≤ Real.sqrt c₂ * r ^ (k + 1) := by
    intro k
    have hX : MemLp (levelDiff Pl (k + 1)) 2 μ := memLp_levelDiff hPl (k + 1)
    have hmean : ∫ ω, levelDiff Pl (k + 1) ω ∂μ = μ[Pl (k + 1)] - μ[Pl k] :=
      integral_sub (hPl1 (k + 1)) (hPl1 k)
    have hsq2 : (∫ ω, levelDiff Pl (k + 1) ω ∂μ) ^ 2 ≤ ∫ ω, levelDiff Pl (k + 1) ω ^ 2 ∂μ := by
      rw [integral_sq_eq hX]
      linarith [variance_nonneg (levelDiff Pl (k + 1)) μ]
    have hb := h_iii (k + 1) (Nat.le_add_left 1 k)
    rw [hsq (k + 1)] at hb
    rw [← hmean]
    calc |∫ ω, levelDiff Pl (k + 1) ω ∂μ| ≤ Real.sqrt (∫ ω, levelDiff Pl (k + 1) ω ^ 2 ∂μ) :=
          Real.abs_le_sqrt hsq2
      _ ≤ Real.sqrt (c₂ * (r ^ (k + 1)) ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt c₂ * r ^ (k + 1) := by
          rw [Real.sqrt_mul hc₂, Real.sqrt_sq (pow_nonneg hr0.le _)]
  -- `m` steps from level `ℓ`: `|E[P_{m+ℓ}] − E[P_ℓ]| ≤ √c₂ r^{ℓ+1} ∑_{j<m} r^j`
  have hpartial : ∀ m : ℕ, |μ[Pl (m + ℓ)] - μ[Pl ℓ]| ≤
      Real.sqrt c₂ * r ^ (ℓ + 1) * ∑ j ∈ range m, r ^ j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : μ[Pl (m + 1 + ℓ)] - μ[Pl ℓ] =
          (μ[Pl (m + ℓ + 1)] - μ[Pl (m + ℓ)]) + (μ[Pl (m + ℓ)] - μ[Pl ℓ]) := by
        rw [Nat.add_right_comm m 1 ℓ]
        ring
      rw [e, Finset.sum_range_succ]
      calc |(μ[Pl (m + ℓ + 1)] - μ[Pl (m + ℓ)]) + (μ[Pl (m + ℓ)] - μ[Pl ℓ])|
          ≤ |μ[Pl (m + ℓ + 1)] - μ[Pl (m + ℓ)]| + |μ[Pl (m + ℓ)] - μ[Pl ℓ]| := abs_add_le _ _
        _ ≤ Real.sqrt c₂ * r ^ (m + ℓ + 1) +
              Real.sqrt c₂ * r ^ (ℓ + 1) * ∑ j ∈ range m, r ^ j := add_le_add (hstep (m + ℓ)) ih
        _ = Real.sqrt c₂ * r ^ (ℓ + 1) * (∑ j ∈ range m, r ^ j + r ^ m) := by ring
  -- let `m → ∞`
  have hgeom : ∀ m, Real.sqrt c₂ * r ^ (ℓ + 1) * ∑ j ∈ range m, r ^ j ≤
      Real.sqrt c₂ * r ^ (ℓ + 1) * (1 - r)⁻¹ := fun m =>
    mul_le_mul_of_nonneg_left (geom_sum_le_of_lt_one hr0.le hr1 m)
      (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hr0.le _))
  have hlim' : Tendsto (fun m => |μ[Pl (m + ℓ)] - μ[Pl ℓ]|) atTop (𝓝 |μ[P] - μ[Pl ℓ]|) :=
    ((hlim.comp (tendsto_add_atTop_nat ℓ)).sub_const _).abs
  have hle : |μ[P] - μ[Pl ℓ]| ≤ Real.sqrt c₂ * r ^ (ℓ + 1) * (1 - r)⁻¹ :=
    le_of_tendsto' hlim' fun m => (hpartial m).trans (hgeom m)
  -- rewrite the constant: `√c₂ r^{ℓ+1}/(1 − r) = √c₂/(2^{β/2} − 1) · 2^{−βℓ/2}`
  have h2r : (2 : ℝ) ^ (β / 2) = r⁻¹ := by
    rw [hr_def, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  have hconst : Real.sqrt c₂ / ((2 : ℝ) ^ (β / 2) - 1) * (2 : ℝ) ^ (-(β / 2 * (ℓ : ℝ))) =
      Real.sqrt c₂ * r ^ (ℓ + 1) * (1 - r)⁻¹ := by
    rw [h2r, hrpow ℓ, inv_eq_one_div r, div_sub_one hr0.ne', div_div_eq_mul_div]
    ring
  rw [hconst, integral_sub (hPl1 ℓ) hP, abs_sub_comm]
  exact hle

/-! ### §3.1: the allocation (3.1), the remaining error and the convergence test -/

/-- **Giles (3.1)** (Giles 2015, §3.1, p. 21): the sample sizes
`N_ℓ = ⌈2ε⁻² √(V_ℓ/C_ℓ) ∑_{ℓ'=0}^{L} √(V_ℓ' C_ℓ')⌉` give a multilevel variance
`∑_{ℓ=0}^{L} V_ℓ/N_ℓ ≤ ½ε²` ("this ensures that the … variance of the combined multilevel estimator
is less than `½ε²`"; equality is possible when every argument of `⌈·⌉` is an integer), at a cost
`∑ N_ℓ C_ℓ ≤ 2ε⁻² (∑ √(V_ℓ C_ℓ))² + ∑ C_ℓ`. -/
theorem allocation_eq_3_1 (L : ℕ) {V C : ℕ → ℝ} (hV : ∀ ℓ, 0 < V ℓ) (hC : ∀ ℓ, 0 < C ℓ)
    {ε : ℝ} (hε : 0 < ε) :
    ∑ ℓ ∈ range (L + 1), V ℓ /
        (⌈2 * (ε ^ 2)⁻¹ * Real.sqrt (V ℓ / C ℓ) *
          ∑ k ∈ range (L + 1), Real.sqrt (V k * C k)⌉₊ : ℝ) ≤ ε ^ 2 / 2 ∧
      ∑ ℓ ∈ range (L + 1), (⌈2 * (ε ^ 2)⁻¹ * Real.sqrt (V ℓ / C ℓ) *
          ∑ k ∈ range (L + 1), Real.sqrt (V k * C k)⌉₊ : ℝ) * C ℓ ≤
        2 * (ε ^ 2)⁻¹ * (∑ k ∈ range (L + 1), Real.sqrt (V k * C k)) ^ 2 +
          ∑ ℓ ∈ range (L + 1), C ℓ := by
  have hτ : 0 < ε ^ 2 / 2 := by positivity
  have hτinv : (ε ^ 2 / 2)⁻¹ = 2 * (ε ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  -- the sample sizes (3.1) are `optimalN` for the variance target `τ = ½ε²`
  have hN : ∀ ℓ, ⌈2 * (ε ^ 2)⁻¹ * Real.sqrt (V ℓ / C ℓ) *
      ∑ k ∈ range (L + 1), Real.sqrt (V k * C k)⌉₊ =
      optimalN (range (L + 1)) V C (ε ^ 2 / 2) ℓ := fun ℓ => by
    rw [optimalN, lagrangeN, sumSqrtVC, hτinv]
  have hs : (range (L + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos L)⟩
  simp only [hN]
  constructor
  · exact optimalN_variance hs (fun ℓ _ => hV ℓ) (fun ℓ _ => hC ℓ) hτ
  · have h := optimalN_cost hs (fun ℓ _ => hV ℓ) (fun ℓ _ => hC ℓ) hτ
    rw [hτinv] at h
    exact h

omit [IsProbabilityMeasure μ] in
/-- **The remaining error** (Giles 2015, §3.1, p. 21): "If `E[P_ℓ − P_{ℓ−1}] ∝ 2^{−αℓ}` then the
remaining error is `E[P − P_L] = ∑_{ℓ=L+1}^{∞} E[P_ℓ − P_{ℓ−1}] = E[P_L − P_{L−1}]/(2^α − 1)`."
If `E[P_ℓ − P_{ℓ−1}] = a 2^{−αℓ}` for all `ℓ ≥ L` (with `α > 0`, `P_{−1} ≡ 0`) and
`E[P_ℓ] → E[P]`, then the corrections beyond `L` sum to `E[P − P_L]`, and
`E[P − P_L] = E[P_L − P_{L−1}]/(2^α − 1)`. -/
theorem remaining_error {P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {α a : ℝ} {L : ℕ} (hα : 0 < α)
    (hP : Integrable P μ) (hPl : ∀ ℓ, Integrable (Pl ℓ) μ)
    (hlim : Tendsto (fun ℓ => μ[Pl ℓ]) atTop (𝓝 (μ[P])))
    (hgeo : ∀ ℓ, L ≤ ℓ → ∫ ω, levelDiff Pl ℓ ω ∂μ = a * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) :
    HasSum (fun k => ∫ ω, levelDiff Pl (L + 1 + k) ω ∂μ) (∫ ω, P ω - Pl L ω ∂μ) ∧
      ∫ ω, P ω - Pl L ω ∂μ = (∫ ω, levelDiff Pl L ω ∂μ) / ((2 : ℝ) ^ α - 1) := by
  -- the ratio `r = 2^{−α} ∈ (0, 1)`
  set r : ℝ := (2 : ℝ) ^ (-α) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos two_pos _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hrpow : ∀ n : ℕ, (2 : ℝ) ^ (-(α * (n : ℝ))) = r ^ n := fun n => by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), neg_mul]
  -- the corrections beyond `L` form a geometric series
  have hterm : ∀ k : ℕ, ∫ ω, levelDiff Pl (L + 1 + k) ω ∂μ = a * r ^ (L + 1) * r ^ k := fun k => by
    rw [hgeo (L + 1 + k) (by omega), hrpow, pow_add]
    ring
  have hsum : HasSum (fun k => ∫ ω, levelDiff Pl (L + 1 + k) ω ∂μ)
      (a * r ^ (L + 1) * (1 - r)⁻¹) := by
    simp only [hterm]
    exact (hasSum_geometric_of_lt_one hr0.le hr1).mul_left (a * r ^ (L + 1))
  -- its partial sums telescope to `E[P_{L+n}] − E[P_L] → E[P] − E[P_L]`
  have htel : ∀ n : ℕ, ∑ k ∈ range n, ∫ ω, levelDiff Pl (L + 1 + k) ω ∂μ =
      μ[Pl (n + L)] - μ[Pl L] := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, show L + 1 + n = (n + L) + 1 by omega,
        show n + 1 + L = (n + L) + 1 by omega]
      rw [levelDiff_succ, integral_sub (hPl _) (hPl _)]
      ring
  have hlim' : Tendsto (fun n => ∑ k ∈ range n, ∫ ω, levelDiff Pl (L + 1 + k) ω ∂μ) atTop
      (𝓝 (μ[P] - μ[Pl L])) := by
    simp only [htel]
    exact (hlim.comp (tendsto_add_atTop_nat L)).sub_const _
  have hval : ∫ ω, P ω - Pl L ω ∂μ = a * r ^ (L + 1) * (1 - r)⁻¹ := by
    rw [integral_sub hP (hPl L)]
    exact tendsto_nhds_unique hlim' hsum.tendsto_sum_nat
  refine ⟨by rw [hval]; exact hsum, ?_⟩
  -- `a r^{L+1}/(1 − r) = a r^L/(2^α − 1)`
  have h2r : (2 : ℝ) ^ α = r⁻¹ := by
    rw [hr_def, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  rw [hval, hgeo L le_rfl, hrpow, h2r, inv_eq_one_div r, div_sub_one hr0.ne', div_div_eq_mul_div]
  ring

/-- **The convergence test of Algorithm 1** (Giles 2015, §3.1, p. 21): "The test for weak
convergence tries to ensure that `|E[P − P_L]| < ε/√2`, to achieve an MSE which is less than `ε²`
… This leads to the convergence test `|E[P_L − P_{L−1}]|/(2^α − 1) < ε/√2`."  If the corrections
decay exactly geometrically beyond `L` (as in `remaining_error`), the test passes and the estimator
`Y` has `E[Y] = E[P_L]` and `V[Y] ≤ ½ε²` (as ensured by (3.1)), then `MSE < ε²`. -/
theorem convergence_test_mse {Y P : Ω → ℝ} {Pl : ℕ → Ω → ℝ} {α a ε : ℝ} {L : ℕ} (hα : 0 < α)
    (hY : MemLp Y 2 μ) (hP : Integrable P μ) (hPl : ∀ ℓ, Integrable (Pl ℓ) μ)
    (hlim : Tendsto (fun ℓ => μ[Pl ℓ]) atTop (𝓝 (μ[P])))
    (hgeo : ∀ ℓ, L ≤ ℓ → ∫ ω, levelDiff Pl ℓ ω ∂μ = a * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (hmean : μ[Y] = μ[Pl L]) (hV : variance Y μ ≤ ε ^ 2 / 2)
    (htest : |∫ ω, levelDiff Pl L ω ∂μ| / ((2 : ℝ) ^ α - 1) < ε / Real.sqrt 2) :
    μ[fun ω => (Y ω - μ[P]) ^ 2] < ε ^ 2 := by
  have h2α : 0 < (2 : ℝ) ^ α - 1 := by
    have := Real.one_lt_rpow one_lt_two hα
    linarith
  -- the bias is below `ε/√2`
  have hbias : |∫ ω, P ω - Pl L ω ∂μ| < ε / Real.sqrt 2 := by
    rw [(remaining_error hα hP hPl hlim hgeo).2, abs_div, abs_of_pos h2α]
    exact htest
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hbias2 : (∫ ω, P ω - Pl L ω ∂μ) ^ 2 < ε ^ 2 / 2 := by
    have h0 : 0 ≤ |∫ ω, P ω - Pl L ω ∂μ| := abs_nonneg _
    calc (∫ ω, P ω - Pl L ω ∂μ) ^ 2 = |∫ ω, P ω - Pl L ω ∂μ| ^ 2 := (sq_abs _).symm
      _ < (ε / Real.sqrt 2) ^ 2 := pow_lt_pow_left₀ hbias h0 two_ne_zero
      _ = ε ^ 2 / 2 := by rw [div_pow, hs2]
  rw [mse_eq_variance_add_sq_bias hY (μ[P]), hmean, ← integral_sub (hPl L) hP]
  have e : (∫ ω, Pl L ω - P ω ∂μ) ^ 2 = (∫ ω, P ω - Pl L ω ∂μ) ^ 2 := by
    rw [integral_sub (hPl L) hP, integral_sub hP (hPl L)]
    ring
  rw [e]
  linarith

/-! ### §3.3: the consistency check -/

omit [IsProbabilityMeasure μ] in
/-- The expected consistency check vanishes (Giles 2015, §3.3, p. 22): "If `a, b, c` are estimates
for `E[P^f_{ℓ−1}]`, `E[P^f_ℓ]`, `E[Y_ℓ]`, respectively, then it should be true that
`a − b + c ≈ 0`."  For unbiased estimates of these three quantities, with
`Y_ℓ = P^f_ℓ − P^c_{ℓ−1}` and the identity (2.4) `E[P^f_{ℓ−1}] = E[P^c_{ℓ−1}]`,
`E[a − b + c] = 0` (here with the levels shifted by one, `ℓ − 1 ↦ ℓ`). -/
theorem consistency_mean {a b c : Ω → ℝ} {Pf Pc : ℕ → Ω → ℝ} (ℓ : ℕ) (ha : Integrable a μ)
    (hb : Integrable b μ) (hc : Integrable c μ) (hPf : ∀ k, Integrable (Pf k) μ)
    (hPc : ∀ k, Integrable (Pc k) μ) (h24 : μ[Pf ℓ] = μ[Pc ℓ])
    (hae : μ[a] = μ[Pf ℓ]) (hbe : μ[b] = μ[Pf (ℓ + 1)])
    (hce : μ[c] = ∫ ω, Pf (ℓ + 1) ω - Pc ℓ ω ∂μ) :
    ∫ ω, a ω - b ω + c ω ∂μ = 0 := by
  have hab : Integrable (fun ω => a ω - b ω) μ := ha.sub hb
  rw [integral_add hab hc, integral_sub ha hb, hae, hbe, hce, integral_sub (hPf _) (hPc _), h24]
  ring

/-- **The Cauchy–Schwarz inequality for covariances**: `Cov[X, Y]² ≤ V[X] V[Y]` for
square-integrable `X, Y` (used for the consistency check of Giles 2015, §3.3). -/
theorem covariance_sq_le {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ := by
  -- `0 ≤ V[X − tY] = V[X] − 2t Cov[X, Y] + t² V[Y]` for every `t`
  have hq : ∀ t : ℝ, 0 ≤ variance X μ - 2 * t * covariance X Y μ + t ^ 2 * variance Y μ := by
    intro t
    have hYt : MemLp (fun ω => t * Y ω) 2 μ := hY.const_mul t
    have h := variance_nonneg (fun ω => X ω - t * Y ω) μ
    rw [variance_fun_sub hX hYt, covariance_const_mul_right, variance_const_mul] at h
    linarith
  generalize variance X μ = A at hq ⊢
  generalize covariance X Y μ = B at hq ⊢
  generalize hC : variance Y μ = C at hq ⊢
  have hC0 : 0 ≤ C := by
    rw [← hC]
    exact variance_nonneg Y μ
  rcases hC0.lt_or_eq with hCpos | hCzero
  · -- take `t = B/C`
    have h1 := mul_nonneg hCpos.le (hq (B / C))
    have htC : B / C * C = B := div_mul_cancel₀ B hCpos.ne'
    generalize B / C = q at h1 htC
    subst htC
    nlinarith [h1]
  · -- `C = 0`: the quadratic is affine in `t`, so `B = 0`
    subst hCzero
    by_contra hne
    have hB : B ≠ 0 := by
      rintro rfl
      simp at hne
    have ht := hq ((A + 1) / 2 * B⁻¹)
    have e : 2 * ((A + 1) / 2 * B⁻¹) * B = (A + 1) * (B⁻¹ * B) := by ring
    rw [e, inv_mul_cancel₀ hB, mul_one, mul_zero, add_zero] at ht
    linarith

/-- Minkowski's inequality for standard deviations: `√V[X + Y] ≤ √V[X] + √V[Y]`. -/
theorem sqrt_variance_add_le {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Real.sqrt (variance (fun ω => X ω + Y ω) μ) ≤
      Real.sqrt (variance X μ) + Real.sqrt (variance Y μ) := by
  have habs : |covariance X Y μ| ≤ Real.sqrt (variance X μ) * Real.sqrt (variance Y μ) := by
    rw [← Real.sqrt_mul (variance_nonneg X μ)]
    exact Real.abs_le_sqrt (covariance_sq_le hX hY)
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    variance_fun_add hX hY, add_sq, Real.sq_sqrt (variance_nonneg X μ),
    Real.sq_sqrt (variance_nonneg Y μ)]
  nlinarith [le_abs_self (covariance X Y μ)]

/-- Minkowski's inequality for standard deviations: `√V[X − Y] ≤ √V[X] + √V[Y]`. -/
theorem sqrt_variance_sub_le {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Real.sqrt (variance (fun ω => X ω - Y ω) μ) ≤
      Real.sqrt (variance X μ) + Real.sqrt (variance Y μ) := by
  have habs : |covariance X Y μ| ≤ Real.sqrt (variance X μ) * Real.sqrt (variance Y μ) := by
    rw [← Real.sqrt_mul (variance_nonneg X μ)]
    exact Real.abs_le_sqrt (covariance_sq_le hX hY)
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    variance_fun_sub hX hY, add_sq, Real.sq_sqrt (variance_nonneg X μ),
    Real.sq_sqrt (variance_nonneg Y μ)]
  nlinarith [neg_abs_le (covariance X Y μ)]

/-- **The consistency check** (Giles 2015, §3.3, p. 22): "Since
`√V[a − b + c] ≤ √V[a] + √V[b] + √V[c]` it computes and plots the ratio
`|a − b + c| / (3(√V_a + √V_b + √V_c))`."  The inequality holds for all square-integrable `a, b, c`,
with no independence assumption. -/
theorem consistency_sd {a b c : Ω → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hc : MemLp c 2 μ) :
    Real.sqrt (variance (fun ω => a ω - b ω + c ω) μ) ≤
      Real.sqrt (variance a μ) + Real.sqrt (variance b μ) + Real.sqrt (variance c μ) := by
  have hab : MemLp (fun ω => a ω - b ω) 2 μ := ha.sub hb
  have h1 := sqrt_variance_add_le hab hc
  have h2 := sqrt_variance_sub_le ha hb
  linarith

/-! ### §3.3: the kurtosis and the accuracy of variance estimates -/

section kurt

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- The kurtosis `κ = E[X⁴]/(E[X²])²` of a random variable (Giles 2015, §3.3, p. 23, for `X` with
zero mean). -/
noncomputable def kurtosis (X : Ω₀ → ℝ) (ν : Measure Ω₀) : ℝ :=
  (∫ y, X y ^ 4 ∂ν) / (∫ y, X y ^ 2 ∂ν) ^ 2

end kurt

section sampleVariance

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀}

/-- **The accuracy of a variance estimate** (Giles 2015, §3.3, p. 23): "When the number of samples
`N` is large, the standard deviation of the sample variance for a random variable `X` with zero mean
is approximately `√((κ − 1)/N) E[X²]` where the kurtosis `κ` is defined as `κ = E[X⁴]/(E[X²])²`."
For `N ≥ 1` independent samples `X(ω⁽ⁿ⁾)` of a zero-mean `X` with `E[X⁴] < ∞` and `E[X²] > 0`, the
sample variance with known mean, `N⁻¹ ∑_{n<N} X(ω⁽ⁿ⁾)²`, is unbiased for `V[X] = E[X²]` and its
standard deviation is exactly `√((κ − 1)/N) E[X²]`. -/
theorem sampleVariance_sd (ω : ℕ → Ω → Ω₀)
    (hω : ∀ n, MeasurePreserving (ω n) μ ν) (hind : iIndepFun ω μ) {X : Ω₀ → ℝ}
    (hXm : Measurable X) (hX4 : Integrable (fun y => X y ^ 4) ν) (hX0 : ∫ y, X y ∂ν = 0)
    (hpos : 0 < ∫ y, X y ^ 2 ∂ν) {N : ℕ} (hN : 0 < N) :
    μ[fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, X (ω n x) ^ 2] = variance X ν ∧
      Real.sqrt (variance (fun x => (N : ℝ)⁻¹ * ∑ n ∈ range N, X (ω n x) ^ 2) μ) =
        Real.sqrt ((kurtosis X ν - 1) / N) * ∫ y, X y ^ 2 ∂ν := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω 0).map_eq]
    exact Measure.isProbabilityMeasure_map (hω 0).measurable.aemeasurable
  -- `X²` is square-integrable because `E[X⁴] < ∞`
  have hX2m : Measurable fun y => X y ^ 2 := hXm.pow_const 2
  have hX2 : MemLp (fun y => X y ^ 2) 2 ν :=
    (memLp_two_iff_integrable_sq hX2m.aestronglyMeasurable).2
      (hX4.congr (Filter.Eventually.of_forall fun y => show X y ^ 4 = (X y ^ 2) ^ 2 by ring))
  have hX : MemLp X 2 ν := (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).2
    (hX2.integrable one_le_two)
  obtain ⟨hmean, hvar, -, -⟩ := mc_estimate ω hω hind hX2m hX2 hN
  -- `V[X] = E[X²]` (zero mean) and `V[X²] = E[X⁴] − E[X²]²`
  have hVX : variance X ν = ∫ y, X y ^ 2 ∂ν := by
    rw [integral_sq_eq hX, hX0]
    ring
  have hVX2 : variance (fun y => X y ^ 2) ν = ∫ y, X y ^ 4 ∂ν - (∫ y, X y ^ 2 ∂ν) ^ 2 := by
    have h := integral_sq_eq hX2
    have e : ∫ y, (X y ^ 2) ^ 2 ∂ν = ∫ y, X y ^ 4 ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => show (X y ^ 2) ^ 2 = X y ^ 4 by ring)
    rw [e] at h
    linarith
  refine ⟨hmean.trans hVX.symm, ?_⟩
  rw [hvar, hVX2]
  have hm2 : 0 < (∫ y, X y ^ 2 ∂ν) ^ 2 := pow_pos hpos 2
  have e : (∫ y, X y ^ 4 ∂ν - (∫ y, X y ^ 2 ∂ν) ^ 2) / N =
      (kurtosis X ν - 1) / N * (∫ y, X y ^ 2 ∂ν) ^ 2 := by
    rw [kurtosis, div_sub_one hm2.ne', div_div, div_mul_eq_mul_div,
      mul_comm ((∫ y, X y ^ 2 ∂ν) ^ 2) (N : ℝ), mul_div_mul_right _ _ hm2.ne']
  rw [e, Real.sqrt_mul' _ hm2.le, Real.sqrt_sq hpos.le]

end sampleVariance

omit [IsProbabilityMeasure μ] in
/-- **The kurtosis of a `{−1, 0, 1}`-valued correction** (Giles 2015, §3.3, p. 23): "An extreme,
but important, example is when `P` always takes the value 0 or 1.  In this case we have
`X ≡ P_ℓ − P_{ℓ−1} = 1` with probability `p`, `−1` with probability `q`, `0` with probability
`1 − p − q`.  If `p, q ≪ 1`, then `E[X] ≈ 0`, and `κ ≈ (p + q)⁻¹ ≫ 1`."  For every random variable
with values in `{−1, 0, 1}` and `p + q = P(X ≠ 0) > 0`, the kurtosis is exactly `(p + q)⁻¹`. -/
theorem kurtosis_of_ternary {X : Ω → ℝ} (hXm : Measurable X)
    (hX : ∀ ω, X ω = -1 ∨ X ω = 0 ∨ X ω = 1) (hp : 0 < μ.real {ω | X ω ≠ 0}) :
    kurtosis X μ = (μ.real {ω | X ω ≠ 0})⁻¹ := by
  have hs : MeasurableSet {ω | X ω ≠ 0} := hXm (measurableSet_singleton 0).compl
  -- `X² = X⁴ = 1_{X ≠ 0}`
  have h2 : ∀ ω, X ω ^ 2 = Set.indicator {ω | X ω ≠ 0} 1 ω := by
    intro ω
    rcases hX ω with h | h | h <;> norm_num [Set.indicator, h]
  have h4 : ∀ ω, X ω ^ 4 = Set.indicator {ω | X ω ≠ 0} 1 ω := by
    intro ω
    rcases hX ω with h | h | h <;> norm_num [Set.indicator, h]
  have e2 : ∫ ω, X ω ^ 2 ∂μ = μ.real {ω | X ω ≠ 0} := by
    simp only [h2]
    exact integral_indicator_one hs
  have e4 : ∫ ω, X ω ^ 4 ∂μ = μ.real {ω | X ω ≠ 0} := by
    simp only [h4]
    exact integral_indicator_one hs
  rw [kurtosis, e2, e4, sq, div_mul_eq_div_div, div_self hp.ne', one_div]

/-- Giles 2015, §3.3, p. 23: "the kurtosis will become worse as `ℓ → ∞` since `p, q → 0`".  For
`{−1, 0, 1}`-valued corrections `X_ℓ` with `P(X_ℓ ≠ 0) > 0` and `E[X_ℓ²] → 0` (for example
`V_ℓ → 0` and `E[X_ℓ] → 0`), the kurtosis `κ_ℓ` tends to infinity (for any measure `μ`). -/
omit [IsProbabilityMeasure μ] in
theorem tendsto_kurtosis_atTop {X : ℕ → Ω → ℝ} (hXm : ∀ ℓ, Measurable (X ℓ))
    (hX : ∀ ℓ ω, X ℓ ω = -1 ∨ X ℓ ω = 0 ∨ X ℓ ω = 1)
    (hp : ∀ ℓ, 0 < μ.real {ω | X ℓ ω ≠ 0})
    (hlim : Tendsto (fun ℓ => ∫ ω, X ℓ ω ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun ℓ => kurtosis (X ℓ) μ) atTop atTop := by
  have e2 : ∀ ℓ, ∫ ω, X ℓ ω ^ 2 ∂μ = μ.real {ω | X ℓ ω ≠ 0} := by
    intro ℓ
    have hs : MeasurableSet {ω | X ℓ ω ≠ 0} := hXm ℓ (measurableSet_singleton 0).compl
    have h2 : ∀ ω, X ℓ ω ^ 2 = Set.indicator {ω | X ℓ ω ≠ 0} 1 ω := by
      intro ω
      rcases hX ℓ ω with h | h | h <;> norm_num [Set.indicator, h]
    simp only [h2]
    exact integral_indicator_one hs
  simp only [fun ℓ => kurtosis_of_ternary (hXm ℓ) (hX ℓ) (hp ℓ)]
  simp only [e2] at hlim
  have h : Tendsto (fun ℓ => μ.real {ω | X ℓ ω ≠ 0}) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Filter.Eventually.of_forall hp⟩
  exact tendsto_inv_nhdsGT_zero.comp h

end MLMC
