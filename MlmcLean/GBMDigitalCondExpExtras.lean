import MlmcLean.GBMDigitalCondExp

/-!
# The digital option for GBM: strike zero and Theorem 1 for splitting (Giles 2015, §5.2)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.2, paragraph
"Digital options", pp. 35–36, l. 1525–1600 of `docs/giles2015.txt`.  The setting is that of
`MlmcLean.GBMDigitalCondExp`: geometric Brownian motion `dS = rS dt + σS dW`, Milstein steps of
size `h_ℓ = T 2^{−ℓ}` driven by i.i.d. `Z_i ∼ N(0, 1)` (`stdNormalSeq`), the last Euler–Maruyama
step replaced by its conditional expectation `Φ((m − K)/s)` (`gbmDigitalCondFine`,
`gbmDigitalCondCoarse`) or by an average over sub-samples of the last increment
(`gbmDigitalSplitFine`, `gbmDigitalSplitCoarse`, sampled from `stdNormalSeq.prod stdNormalSeq`).
That module proves the variance rate and Theorem 1 of the conditional-expectation estimator for a
strike `K ≠ 0`, and the variance rate of the splitting estimator, but not Theorem 1 for it.

**What is proved.**
* The strike `K = 0` (`gbm_digital_condExp_variance_rate_zero_strike`).  The Milstein factor of GBM
  is `1 + rh + σ√h z + ½σ²h(z² − 1) = ½(σ√h z + 1)² + ½ + rh − ½σ²h ≥ ¼` for every `z` once
  `(σ² + 2|r|)h ≤ ½` (`quarter_le_gbmMilFactor`), so on the levels with `4(σ² + 2|r|)h_ℓ ≤ 1` the
  fine and the coarse path keep the sign of `s₀` on every sample.  Then
  `P^f = Φ(ς(1 + rh)/(|σ|√h))` and `P^c = Φ(ς(1 + 2rh + σ√h Z_{N−2})/(|σ|√h))` with `ς = s₀/|s₀|`:
  both arguments are of order `h^{−1/2}` with the same sign unless `|Z_{N−2}| ≳ h^{−1/2}`, so
  `E[(P^f_ℓ − P^c_{ℓ−1})²] = O(h_ℓ^q)` for every `q` (super-polynomially small).
* The variance rate for every strike (`gbm_digital_condExp_variance_rate_all`, l. 1575–1577:
  "a variance which is approximately `O(h^{3/2})`"): `E[(P^f_ℓ − P^c_{ℓ−1})²] ≤ C h_ℓ^q` for every
  `q < 3/2` and every `K ∈ ℝ`.
* Theorem 1 for the conditional-expectation estimator for every strike
  (`gbm_digital_condExp_theorem1_all`, l. 1578–1580: "Since `β > γ`, the MLMC complexity is
  `O(ε⁻²)`").
* For splitting with `M` sub-samples, the variance bound `C(h^q + h^{q−1/2}/M)` for every strike
  (`gbm_digital_split_variance_rate_all`) and the weak error: the fine splitting payoff has the
  mean of the conditional-expectation payoff, hence its weak rate `O(h^q)`, `q < 1`
  (`gbm_digital_split_weak_rate`).
* Theorem 1 for the splitting estimator (`gbm_digital_split_theorem1`, l. 1591–1600: "If the
  number of sub-samples is chosen appropriately, the variance is the same, to leading order,
  without any increase in the computational cost, again to leading order"): with
  `M_ℓ = ⌈h_ℓ^{−1/2}⌉` sub-samples on level `ℓ` (`gbmSplitCount`), independent samples of
  `(Z, Y) ∼ stdNormalSeq.prod stdNormalSeq` on every level, any `K`, `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`: the
  error of the multilevel estimator of `P(S_T > K)` is square integrable, its mean square is
  `< ε²`, and the cost `∑_{ℓ≤L} N_ℓ (2^ℓ + M_ℓ) ≤ c₄ ε⁻²` (`theorem1_fineCoarse_of_rate_gt_cost`,
  a version of `theorem1_fineCoarse_of_rate_gt` for any sample space and any cost `O(2^ℓ)`).

**Deviations.**
* The cost model of splitting: a level-`ℓ` sample costs `2^ℓ + M_ℓ`, the `2^ℓ` fine path steps
  plus one unit per sub-sample.  Each sub-sample is one Euler–Maruyama step of the fine and one of
  the coarse path, and the coarse path has `2^{ℓ−1}` steps; like the cost `2^ℓ` of
  `gbm_digital_condExp_theorem1`, the model leaves these out.  Any of these costs is at most a
  constant times `2^ℓ` (`2^ℓ + M_ℓ ≤ (2 + T^{−1/2}) 2^ℓ`, `gbmSplitCount_bounds`), so the
  complexity `O(ε⁻²)` does not depend on the choice.
* The rates are those of `MlmcLean.GBMDigitalCondExp`: `α = 3/4 < 1`, `β = 5/4 < 3/2` in
  Theorem 1 (only the constant `c₄` changes); for `K = 0` the variance is shown to be `O(h^q)` for
  every `q` (that it is exponentially small, as it is numerically, is not proved); the factor
  `25 e^{−rT}` is omitted.
* `s₀ ≠ 0`, `σ ≠ 0`, `T > 0` as in `MlmcLean.GBMDigitalCondExp` (for `s₀ = 0`, `σ = 0` or `T ≤ 0`
  the conditional standard deviation vanishes and `Φ(x/0)` is a junk value).

**What is not proved.**  For splitting, "the variance is the same, to leading order" as an
asymptotic equivalence of the variances: only the same rate `O(h^q)`, `q < 3/2`, as the
conditional-expectation estimator (with `M_ℓ = ⌈h_ℓ^{−1/2}⌉` the excess is of the same order, see
`gbm_digital_split_sqrt_rate`).  An exponential rate for `K = 0`, the endpoint `α = 1`, and the
endpoint `β = 3/2` without a logarithmic factor (`MlmcLean.GBMDigitalCondExpEndpoint` proves
`V_ℓ = O(h^{3/2} (log(1/h))^{5/2})` for the conditional-expectation estimator, not for splitting).
The every-step digital barrier is out of scope.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace MLMC

/-! ### Strike zero: for small steps the Milstein path keeps the sign of `s₀` -/

/-- **The Milstein factor of GBM is at least `¼` for small steps** (Giles 2015, §5.2, p. 35,
l. 1541–1545, the Milstein path of the digital option; the case `K = 0` left out of
`MlmcLean.GBMDigitalCondExp`).  `1 + rk + σ√k x + ½σ²((√k x)² − k) = ½(σ√k x + 1)² + ½ + rk −
½σ²k ≥ ½ − ½(σ² + 2|r|)k ≥ ¼` for every `x` when `k ≥ 0` and `(σ² + 2|r|)k ≤ ½`. -/
lemma quarter_le_gbmMilFactor (r σ : ℝ) {k : ℝ} (hk : 0 ≤ k)
    (hks : (σ ^ 2 + 2 * |r|) * k ≤ 1 / 2) (x : ℝ) : 1 / 4 ≤ gbmMilFactor r σ k x := by
  have e : gbmMilFactor r σ k x =
      (σ * (Real.sqrt k * x) + 1) ^ 2 / 2 + 1 / 2 + r * k - σ ^ 2 * k / 2 := by
    unfold gbmMilFactor
    ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_right (neg_abs_le r) hk
  nlinarith [sq_nonneg (σ * (Real.sqrt k * x) + 1)]

/-- **For small steps the Milstein path of GBM keeps the sign of `s₀`** (Giles 2015, §5.2, p. 35,
l. 1541–1545): the product `∏_{j<n} (1 + rk + σ√k w_j + ½σ²k(w_j² − 1))` of Milstein factors is
positive for every sequence `w` when `(σ² + 2|r|)k ≤ ½` (`quarter_le_gbmMilFactor`). -/
lemma prod_gbmMilFactor_pos (r σ : ℝ) {k : ℝ} (hk : 0 ≤ k)
    (hks : (σ ^ 2 + 2 * |r|) * k ≤ 1 / 2) (w : ℕ → ℝ) (n : ℕ) :
    0 < ∏ j ∈ range n, gbmMilFactor r σ k (w j) :=
  Finset.prod_pos fun _ _ => lt_of_lt_of_le (by norm_num) (quarter_le_gbmMilFactor r σ hk hks _)

/-- **The argument of `Φ` for a path with the sign of `s₀`** (Giles 2015, §5.2, p. 36,
l. 1551–1574, the payoffs `Φ((m − K)/s)` with `K = 0`): if `X = s₀ Q` with `Q > 0`, then
`X c/(|σX| √k) = (s₀/|s₀|) · c/(|σ| √k)`. -/
lemma mul_div_abs_mul_eq_sign {σ s₀ Q c k : ℝ} (hσ : σ ≠ 0) (hs₀ : s₀ ≠ 0) (hQ : 0 < Q)
    (hk : 0 < k) :
    s₀ * Q * c / (|σ * (s₀ * Q)| * Real.sqrt k) = s₀ / |s₀| * (c / (|σ| * Real.sqrt k)) := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  have h1 : 0 < |σ| := abs_pos.2 hσ
  have h2 : 0 < |s₀| := abs_pos.2 hs₀
  rw [abs_mul, abs_mul, abs_of_pos hQ]
  field_simp

/-- **Two values of `Φ` far out in the same tail** (Giles 2015, §5.2, p. 36, l. 1575–1577: both
smoothed payoffs in the same tail of `Φ`).  For `ς = ±1`, `s > 0` and `u, v ≥ s`:
`|Φ(ςu) − Φ(ςv)| ≤ P(|Z| > s/2)`, `Z ∼ N(0,1)` (both lie in `[Φ(s), 1]` or in `[0, Φ(−s)]`). -/
lemma abs_cdf_mul_sub_cdf_mul_le {ς s u v : ℝ} (hς : |ς| = 1) (hs : 0 < s) (hu : s ≤ u)
    (hv : s ≤ v) :
    |cdf (gaussianReal 0 1) (ς * u) - cdf (gaussianReal 0 1) (ς * v)| ≤
      (gaussianReal 0 1).real {w | s / 2 < |w|} := by
  rcases (abs_eq zero_le_one).1 hς with rfl | rfl
  · rw [one_mul, one_mul]
    have hu' := monotone_cdf (gaussianReal 0 1) hu
    have hv' := monotone_cdf (gaussianReal 0 1) hv
    have hu1 := cdf_le_one (gaussianReal 0 1) u
    have hv1 := cdf_le_one (gaussianReal 0 1) v
    have htail : 1 - cdf (gaussianReal 0 1) s ≤ (gaussianReal 0 1).real {w | s / 2 < |w|} := by
      rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]
      refine measureReal_mono fun w hw => ?_
      simp only [Set.mem_Ioi] at hw
      simp only [Set.mem_ofPred_eq]
      rw [abs_of_pos (hs.trans hw)]
      linarith
    rw [abs_sub_le_iff]
    constructor <;> linarith
  · rw [neg_one_mul, neg_one_mul]
    have hu' := monotone_cdf (gaussianReal 0 1) (neg_le_neg hu)
    have hv' := monotone_cdf (gaussianReal 0 1) (neg_le_neg hv)
    have hu0 := cdf_nonneg (gaussianReal 0 1) (-u)
    have hv0 := cdf_nonneg (gaussianReal 0 1) (-v)
    have htail : cdf (gaussianReal 0 1) (-s) ≤ (gaussianReal 0 1).real {w | s / 2 < |w|} := by
      rw [cdf_eq_real]
      refine measureReal_mono fun w hw => ?_
      simp only [Set.mem_Iic] at hw
      simp only [Set.mem_ofPred_eq]
      rw [abs_of_neg (by linarith)]
      linarith
    rw [abs_sub_le_iff]
    constructor <;> linarith

/-- **The squared difference of two values of `Φ` in the same tail, unless an increment is large**
(Giles 2015, §5.2, p. 36, l. 1575–1577).  For `ς = ±1`, `s > 0`, `u ≥ s`, and `v ≥ s` whenever
`|Z| ≤ s`: `(Φ(ςu) − Φ(ςv))² ≤ P(|G| > s/2) + (Z/s)^{2p}` for every `p` (if `|Z| > s` the left side
is at most `1 ≤ (Z/s)^{2p}`; otherwise `abs_cdf_mul_sub_cdf_mul_le`). -/
lemma sq_cdf_mul_sub_le_of_tail {ς s u v Z : ℝ} (hς : |ς| = 1) (hs : 0 < s) (hu : s ≤ u)
    (hv : |Z| ≤ s → s ≤ v) (p : ℕ) :
    (cdf (gaussianReal 0 1) (ς * u) - cdf (gaussianReal 0 1) (ς * v)) ^ 2 ≤
      (gaussianReal 0 1).real {w | s / 2 < |w|} + (Z / s) ^ (2 * p) := by
  have h1 := cdf_nonneg (gaussianReal 0 1) (ς * u)
  have h2 := cdf_le_one (gaussianReal 0 1) (ς * u)
  have h3 := cdf_nonneg (gaussianReal 0 1) (ς * v)
  have h4 := cdf_le_one (gaussianReal 0 1) (ς * v)
  have hb : |cdf (gaussianReal 0 1) (ς * u) - cdf (gaussianReal 0 1) (ς * v)| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hsq : (cdf (gaussianReal 0 1) (ς * u) - cdf (gaussianReal 0 1) (ς * v)) ^ 2 ≤
      |cdf (gaussianReal 0 1) (ς * u) - cdf (gaussianReal 0 1) (ς * v)| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (cdf (gaussianReal 0 1) (ς * u) - cdf (gaussianReal 0 1) (ς * v))]
  have hτ : 0 ≤ (gaussianReal 0 1).real {w | s / 2 < |w|} := measureReal_nonneg
  have hZp : 0 ≤ (Z / s) ^ (2 * p) := (even_two_mul p).pow_nonneg _
  by_cases hZ : |Z| ≤ s
  · exact hsq.trans ((abs_cdf_mul_sub_cdf_mul_le hς hs hu (hv hZ)).trans
      (le_add_of_nonneg_right hZp))
  · rw [not_le] at hZ
    have h5 : 1 ≤ (Z / s) ^ (2 * p) := by
      rw [← (even_two_mul p).pow_abs, abs_div, abs_of_pos hs]
      exact one_le_pow₀ ((one_le_div hs).2 hZ.le)
    linarith

/-- **The pointwise bound for strike zero** (Giles 2015, §5.2, p. 36, l. 1551–1577, with `K = 0`).
On a level `ℓ + 1` with `4(σ² + 2|r|)h ≤ 1` (`h = T 2^{−(ℓ+1)}`), `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, the
fine and the coarse path keep the sign `ς` of `s₀` (`prod_gbmMilFactor_pos`), so
`P^f = Φ(ς(1 + rh)/A)` and `P^c = Φ(ς(1 + 2rh + σ√h Z)/A)` with `A = |σ|√h`, `Z = Z_{N−2}`; with
`s = 1/(4A)`, `(1 + rh)/A ≥ s` and, if `|Z| ≤ s`, `(1 + 2rh + σ√h Z)/A ≥ s`, so
`(P^f − P^c)² ≤ P(|G| > s/2) + (Z/s)^{2p}` (`sq_cdf_mul_sub_le_of_tail`). -/
lemma condDigital_zero_sq_le (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    {ℓ : ℕ} (hsmall : 4 * (σ ^ 2 + 2 * |r|) * (T / 2 ^ (ℓ + 1)) ≤ 1) (p : ℕ) (z : ℕ → ℝ) :
    (gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) ^ 2 ≤
      (gaussianReal 0 1).real {w | 1 / (4 * (|σ| * Real.sqrt (T / 2 ^ (ℓ + 1)))) / 2 < |w|} +
        (z (2 ^ (ℓ + 1) - 2) / (1 / (4 * (|σ| * Real.sqrt (T / 2 ^ (ℓ + 1)))))) ^ (2 * p) := by
  unfold gbmDigitalCondFine gbmDigitalCondCoarse gbmCondMeanFine gbmCondStdFine gbmCondMeanCoarse
    gbmCondStdCoarse
  rw [milsteinPath_gbm, milsteinPath_gbm, div_two_pow_eq_two_mul T ℓ]
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  set h := T / 2 ^ (ℓ + 1) with hh_def
  set Z := z (2 ^ (ℓ + 1) - 2) with hZ_def
  have hσ0 : 0 < |σ| := abs_pos.2 hσ
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hr0 : 0 ≤ (σ ^ 2 + 2 * |r|) * h := by positivity
  have hkf : (σ ^ 2 + 2 * |r|) * h ≤ 1 / 2 := by nlinarith
  have hkc : (σ ^ 2 + 2 * |r|) * (2 * h) ≤ 1 / 2 := by nlinarith
  have hrh : -(1 / 8) ≤ r * h := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le r) hh.le
    nlinarith [sq_nonneg σ, abs_nonneg r]
  have hQf := prod_gbmMilFactor_pos r σ hh.le hkf z (2 ^ (ℓ + 1) - 1)
  have hQc := prod_gbmMilFactor_pos r σ (by positivity) hkc (pairAvg z) (2 ^ ℓ - 1)
  set Qf := ∏ j ∈ range (2 ^ (ℓ + 1) - 1), gbmMilFactor r σ h (z j) with hQf_def
  set Qc := ∏ j ∈ range (2 ^ ℓ - 1), gbmMilFactor r σ (2 * h) (pairAvg z j) with hQc_def
  rw [show s₀ * Qf + r * (s₀ * Qf) * h - 0 = s₀ * Qf * (1 + r * h) by ring,
    show s₀ * Qc + r * (s₀ * Qc) * (2 * h) + σ * (s₀ * Qc) * (Real.sqrt h * Z) - 0 =
      s₀ * Qc * (1 + r * (2 * h) + σ * (Real.sqrt h * Z)) by ring,
    mul_div_abs_mul_eq_sign hσ hs₀ hQf hh, mul_div_abs_mul_eq_sign hσ hs₀ hQc hh]
  have hA : 0 < |σ| * Real.sqrt h := mul_pos hσ0 hsh
  set A := |σ| * Real.sqrt h with hA_def
  have hs : 0 < 1 / (4 * A) := by positivity
  have hsA : 1 / (4 * A) * A = 1 / 4 := by field_simp
  have hς : |(s₀ / |s₀|)| = 1 := by
    rw [abs_div, abs_abs, div_self (abs_ne_zero.2 hs₀)]
  refine sq_cdf_mul_sub_le_of_tail hς hs ?_ ?_ p
  · rw [le_div_iff₀ hA, hsA]
    linarith
  · intro hZ
    rw [le_div_iff₀ hA, hsA]
    have h1 : |σ * (Real.sqrt h * Z)| ≤ 1 / 4 := by
      rw [abs_mul, abs_mul, abs_of_pos hsh, ← mul_assoc, ← hsA, mul_comm (1 / (4 * A)) A]
      exact mul_le_mul_of_nonneg_left hZ hA.le
    have h2 := neg_abs_le (σ * (Real.sqrt h * Z))
    linarith

/-- The conditional-expectation payoffs lie in `[0, 1]`, so the square of the correction is at
most `1` (Giles 2015, §5.2, p. 36, l. 1551–1574). -/
lemma sq_gbmDigitalCond_sub_le_one (r σ T s₀ K : ℝ) (ℓ : ℕ) (z : ℕ → ℝ) :
    (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2 ≤ 1 := by
  unfold gbmDigitalCondFine gbmDigitalCondCoarse
  have h1 := cdf_nonneg (gaussianReal 0 1) ((gbmCondMeanFine r σ T s₀ (ℓ + 1) z - K) /
    gbmCondStdFine r σ T s₀ (ℓ + 1) z)
  have h2 := cdf_le_one (gaussianReal 0 1) ((gbmCondMeanFine r σ T s₀ (ℓ + 1) z - K) /
    gbmCondStdFine r σ T s₀ (ℓ + 1) z)
  have h3 := cdf_nonneg (gaussianReal 0 1) ((gbmCondMeanCoarse r σ T s₀ ℓ z - K) /
    gbmCondStdCoarse r σ T s₀ ℓ z)
  have h4 := cdf_le_one (gaussianReal 0 1) ((gbmCondMeanCoarse r σ T s₀ ℓ z - K) /
    gbmCondStdCoarse r σ T s₀ ℓ z)
  nlinarith

/-- **The second moment for strike zero on the fine levels** (Giles 2015, §5.2, p. 36,
l. 1575–1577, with `K = 0`).  On a level `ℓ + 1` with `4(σ² + 2|r|)h ≤ 1`, the correction is
square integrable and `E[(P^f_{ℓ+1} − P^c_ℓ)²] ≤ 2 (2p − 1)!! (64σ²)^p h^p` for every `p`
(`condDigital_zero_sq_le`, the Gaussian moments `E[Z^{2p}] = (2p − 1)!!` and
`gaussianReal_real_lt_abs_le`). -/
lemma condDigital_zero_integral_le (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0) (hT : 0 < T)
    {ℓ : ℕ} (hsmall : 4 * (σ ^ 2 + 2 * |r|) * (T / 2 ^ (ℓ + 1)) ≤ 1) (p : ℕ) :
    MemLp (fun z => gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) 2 stdNormalSeq ∧
    ∫ z, (gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) ^ 2
        ∂stdNormalSeq ≤
      2 * (Nat.doubleFactorial (2 * p - 1) : ℝ) * (64 * σ ^ 2) ^ p * (T / 2 ^ (ℓ + 1)) ^ p := by
  refine ⟨memLp_gbmDigitalCond_sub r σ T s₀ 0 ℓ, ?_⟩
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have hsh : 0 < Real.sqrt (T / 2 ^ (ℓ + 1)) := Real.sqrt_pos.2 hh
  have hσ0 : 0 < |σ| := abs_pos.2 hσ
  set s := 1 / (4 * (|σ| * Real.sqrt (T / 2 ^ (ℓ + 1)))) with hs_def
  have hs : 0 < s := by positivity
  have hev : MeasurePreserving (fun z : ℕ → ℝ => z (2 ^ (ℓ + 1) - 2)) stdNormalSeq
      (gaussianReal 0 1) := measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) _
  have hgγ : Integrable (fun w : ℝ => (w / s) ^ (2 * p)) (gaussianReal 0 1) := by
    simp_rw [div_pow]
    exact (integrable_pow_gaussian _).div_const _
  have hg : Integrable (fun z : ℕ → ℝ => (z (2 ^ (ℓ + 1) - 2) / s) ^ (2 * p)) stdNormalSeq :=
    (hev.integrable_comp hgγ.aestronglyMeasurable).2 hgγ
  have hI : ∫ z, (z (2 ^ (ℓ + 1) - 2) / s) ^ (2 * p) ∂stdNormalSeq =
      (Nat.doubleFactorial (2 * p - 1) : ℝ) / s ^ (2 * p) := by
    rw [integral_comp_of_measurePreserving hev (f := fun w => (w / s) ^ (2 * p))
      hgγ.aestronglyMeasurable]
    simp_rw [div_pow]
    rw [integral_div, integral_pow_two_mul_gaussian]
  have hf : Integrable (fun z => (gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z -
      gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) ^ 2) stdNormalSeq :=
    (memLp_gbmDigitalCond_sub r σ T s₀ 0 ℓ).integrable_sq
  have hdf : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * p - 1) : ℝ) := Nat.cast_nonneg _
  have hs2 : (s / 2) ^ (2 * p) = 1 / ((64 * σ ^ 2) ^ p * (T / 2 ^ (ℓ + 1)) ^ p) := by
    rw [pow_mul, ← mul_pow, hs_def]
    have h64 : (1 / (4 * (|σ| * Real.sqrt (T / 2 ^ (ℓ + 1)))) / 2) ^ 2 =
        1 / (64 * (|σ| ^ 2 * Real.sqrt (T / 2 ^ (ℓ + 1)) ^ 2)) := by
      field_simp
      ring
    rw [h64, sq_abs, Real.sq_sqrt hh.le, mul_assoc, one_div_pow]
  calc ∫ z, (gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) ^ 2
        ∂stdNormalSeq
      ≤ ∫ z, ((gaussianReal 0 1).real {w | s / 2 < |w|} +
          (z (2 ^ (ℓ + 1) - 2) / s) ^ (2 * p)) ∂stdNormalSeq :=
        integral_mono hf ((integrable_const _).add hg)
          (condDigital_zero_sq_le r σ hs₀ hσ hT hsmall p)
    _ = (gaussianReal 0 1).real {w | s / 2 < |w|} +
          (Nat.doubleFactorial (2 * p - 1) : ℝ) / s ^ (2 * p) := by
        rw [integral_add (integrable_const _) hg, hI]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (Nat.doubleFactorial (2 * p - 1) : ℝ) / (s / 2) ^ (2 * p) +
          (Nat.doubleFactorial (2 * p - 1) : ℝ) / (s / 2) ^ (2 * p) :=
        add_le_add (gaussianReal_real_lt_abs_le p (half_pos hs))
          (div_le_div_of_nonneg_left hdf (by positivity)
            (pow_le_pow_left₀ (by positivity) (half_le_self hs.le) _))
    _ = 2 * (Nat.doubleFactorial (2 * p - 1) : ℝ) * (64 * σ ^ 2) ^ p * (T / 2 ^ (ℓ + 1)) ^ p := by
        rw [hs2]
        field_simp
        ring

/-! ### The variance rate and Theorem 1 for every strike -/

/-- **The conditional-expectation correction for the strike `K = 0` is smaller than every power of
`h`** (Giles 2015, §5.2, p. 36, l. 1575–1577: "Consequently, the difference in payoff between the
coarse and fine paths near the payoff discontinuity is `O(h^{1/2})`, giving a variance which is
approximately `O(h^{3/2})`"; for `K = 0` there are no paths near the discontinuity once `h` is
small).  For GBM `dS = rS dt + σS dW` with `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, the strike `K = 0` and
every real `q` there is `C ≥ 0` such that on every level `ℓ + 1` (`h = T 2^{−(ℓ+1)}`) the
correction `P^f_{ℓ+1} − P^c_ℓ` of the conditional-expectation payoffs (`gbmDigitalCondFine`,
`gbmDigitalCondCoarse`) is square integrable, `E[(P^f_{ℓ+1} − P^c_ℓ)²] ≤ C h^q` and
`V[P^f_{ℓ+1} − P^c_ℓ] ≤ C h^q`.

Proof: on the levels with `4(σ² + 2|r|)h ≤ 1` the Milstein factors are at least `¼`, the paths
keep the sign of `s₀`, both payoffs are `Φ` of arguments of order `h^{−1/2}` with the sign of `s₀`
unless `|Z_{N−2}| > h^{−1/2}/(4|σ|)`, and `E[(P^f − P^c)²] ≤ 2(2p − 1)!!(64σ²)^p h^p`
(`condDigital_zero_integral_le`) with `p = ⌈q⌉`; on the finitely many other levels
`E[(P^f − P^c)²] ≤ 1 ≤ (4(σ² + 2|r|)h)^p`.

**Deviation.**  Super-polynomially small (every power of `h`), not shown to be exponentially
small; the module `MlmcLean.GBMDigitalCondExp` leaves `K = 0` out ("not proved here"). -/
theorem gbm_digital_condExp_variance_rate_zero_strike (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) (q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fun z => gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) 2 stdNormalSeq ∧
      ∫ z, (gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) ^ 2
        ∂stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      variance (fun z => gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ q := by
  set p := ⌈q⌉₊ with hp_def
  have hqp : q ≤ (p : ℝ) := Nat.le_ceil q
  set C₀ := 2 * (Nat.doubleFactorial (2 * p - 1) : ℝ) * (64 * σ ^ 2) ^ p +
    (4 * (σ ^ 2 + 2 * |r|)) ^ p with hC₀_def
  have hC₀ : 0 ≤ C₀ := by positivity
  have key : ∀ ℓ : ℕ, ∫ z, (gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z -
      gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) ^ 2 ∂stdNormalSeq ≤
      C₀ * T ^ ((p : ℝ) - q) * (T / 2 ^ (ℓ + 1)) ^ q := fun ℓ => by
    have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
    have hhT : T / 2 ^ (ℓ + 1) ≤ T := div_le_self hT.le (one_le_pow₀ (by norm_num))
    have hp : ∫ z, (gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) ^ 2 ∂stdNormalSeq ≤ C₀ * (T / 2 ^ (ℓ + 1)) ^ p := by
      have hq0 : 0 ≤ (4 * (σ ^ 2 + 2 * |r|)) ^ p * (T / 2 ^ (ℓ + 1)) ^ p := by positivity
      by_cases hsmall : 4 * (σ ^ 2 + 2 * |r|) * (T / 2 ^ (ℓ + 1)) ≤ 1
      · refine (condDigital_zero_integral_le r σ hs₀ hσ hT hsmall p).2.trans ?_
        rw [hC₀_def, add_mul]
        linarith
      · rw [not_le] at hsmall
        have h1 : ∫ z, (gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1) z -
            gbmDigitalCondCoarse r σ T s₀ 0 ℓ z) ^ 2 ∂stdNormalSeq ≤ 1 := by
          refine (integral_mono (memLp_gbmDigitalCond_sub r σ T s₀ 0 ℓ).integrable_sq
            (integrable_const 1) (sq_gbmDigitalCond_sub_le_one r σ T s₀ 0 ℓ)).trans (le_of_eq ?_)
          simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
        have h2 : 1 ≤ (4 * (σ ^ 2 + 2 * |r|)) ^ p * (T / 2 ^ (ℓ + 1)) ^ p := by
          rw [← mul_pow]
          exact one_le_pow₀ hsmall.le
        have h3 : 0 ≤ 2 * (Nat.doubleFactorial (2 * p - 1) : ℝ) * (64 * σ ^ 2) ^ p *
            (T / 2 ^ (ℓ + 1)) ^ p := by positivity
        rw [hC₀_def, add_mul]
        linarith
    calc _ ≤ C₀ * (T / 2 ^ (ℓ + 1)) ^ p := hp
      _ = C₀ * (T / 2 ^ (ℓ + 1)) ^ (p : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ C₀ * (T ^ ((p : ℝ) - q) * (T / 2 ^ (ℓ + 1)) ^ q) :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow_sub_mul_rpow hh hhT hqp) hC₀
      _ = C₀ * T ^ ((p : ℝ) - q) * (T / 2 ^ (ℓ + 1)) ^ q := by ring
  refine ⟨C₀ * T ^ ((p : ℝ) - q), by positivity, fun ℓ =>
    ⟨memLp_gbmDigitalCond_sub r σ T s₀ 0 ℓ, key ℓ, ?_⟩⟩
  exact (variance_le_expectation_sq ((measurable_gbmDigitalCondFine r σ T s₀ 0 (ℓ + 1)).sub
    (measurable_gbmDigitalCondCoarse r σ T s₀ 0 ℓ)).aestronglyMeasurable).trans (key ℓ)

/-- **G5.2-14/15 for every strike: the variance of the conditional-expectation correction is
`O(h_ℓ^q)` for every `q < 3/2`** (Giles 2015, §5.2, p. 36, l. 1563–1580: "This results in the
conditional distribution for the coarse path underlying at maturity matching that of the fine path
to within `O(h)`, for both the mean and the standard deviation … Consequently, the difference in
payoff between the coarse and fine paths near the payoff discontinuity is `O(h^{1/2})`, giving a
variance which is approximately `O(h^{3/2})`").  For GBM with `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, every
strike `K ∈ ℝ` and every `q < 3/2` there is `C ≥ 0` such that on every level `ℓ + 1` the
correction `P^f_{ℓ+1} − P^c_ℓ` (`gbmDigitalCondFine`, `gbmDigitalCondCoarse`) is square integrable,
`E[(P^f_{ℓ+1} − P^c_ℓ)²] ≤ C h_{ℓ+1}^q` and `V_{ℓ+1} ≤ C h_{ℓ+1}^q`.

Proof: `K ≠ 0` is `gbm_digital_condExp_variance_rate`; `K = 0` is
`gbm_digital_condExp_variance_rate_zero_strike`.

**Deviation.**  The exponent is every `q < 3/2`, not `3/2` (as in
`gbm_digital_condExp_variance_rate`; the endpoint up to a factor `(ℓ + 1)^{5/2}` is
`gbm_digital_condExp_variance_endpoint` in `MlmcLean.GBMDigitalCondExpEndpoint`); the factor
`25 e^{−rT}` is omitted. -/
theorem gbm_digital_condExp_variance_rate_all (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) {q : ℝ} (hq : q < 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ K ℓ z) 2 stdNormalSeq ∧
      ∫ z, (gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z - gbmDigitalCondCoarse r σ T s₀ K ℓ z) ^ 2
        ∂stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      variance (fun z => gbmDigitalCondFine r σ T s₀ K (ℓ + 1) z -
        gbmDigitalCondCoarse r σ T s₀ K ℓ z) stdNormalSeq ≤ C * (T / 2 ^ (ℓ + 1)) ^ q := by
  rcases eq_or_ne K 0 with rfl | hK
  · exact gbm_digital_condExp_variance_rate_zero_strike r σ hs₀ hσ hT q
  · exact gbm_digital_condExp_variance_rate r σ hs₀ hσ hT hK hq

/-- **Theorem 1 end to end for the conditional-expectation estimator of the digital option, for
every strike: mean square error `< ε²` at cost `O(ε⁻²)`** (Giles 2015, §5.2, p. 36, l. 1578–1580:
"This leads to `α = 1`, `β = 3/2` and `γ = 1`. Since `β > γ`, the MLMC complexity is `O(ε⁻²)`",
with Theorem 1, §2.1, p. 6, and (2.4), l. 1584–1590).  For GBM `dS = rS dt + σS dW` with
`s₀ ≠ 0`, `σ ≠ 0`, `T > 0` and any strike `K ∈ ℝ` (`K = 0` included), with the estimator of
`gbm_digital_condExp_theorem1` (level `ℓ`: `2^ℓ` steps, fine payoff `gbmDigitalCondFine`, coarse
payoff `gbmDigitalCondCoarse` of the level below, correction `fineCoarseDiff`, independent samples,
cost `2^ℓ` per sample): there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` for which the multilevel estimator of
`E[H(S_T − K)] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K} dN(0,1)(w)` has a square-integrable error with
mean square `< ε²`, at cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²`.

Proof: Theorem 1 (`theorem1_fineCoarse_of_rate_gt`) with `α = 3/4`
(`gbm_digital_condExp_weak_rate`), `β = 5/4` (`gbm_digital_condExp_variance_rate_all` on the
levels `ℓ ≥ 1`, `gbm_digital_condExp_level_zero` on level `0`), `γ = 1` and (2.4)
(`gbmDigitalCond_integral_eq`).

**Deviation.**  The rates used are smaller than the paper's (`α = 3/4 < 1`, `β = 5/4 < 3/2`),
which only changes the constant `c₄`; the factor `25 e^{−rT}` is omitted. -/
theorem gbm_digital_condExp_theorem1_all (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (gbmDigitalCondFine r σ T s₀ K)
              (gbmDigitalCondCoarse r σ T s₀ K)) (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (gbmDigitalCondFine r σ T s₀ K)
              (gbmDigitalCondCoarse r σ T s₀ K)) (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨C₁, -, hw⟩ := gbm_digital_condExp_weak_rate r σ hs₀ hσ hT K (q := 3 / 4) (by norm_num)
  obtain ⟨C₂, hC₂, hv⟩ := gbm_digital_condExp_variance_rate_all r σ (K := K) hs₀ hσ hT
    (q := 5 / 4) (by norm_num)
  obtain ⟨c₄, hc₄, h⟩ := theorem1_fineCoarse_of_rate_gt hT (α := 3 / 4) (β := 5 / 4)
    (by norm_num) (by norm_num)
    (Pf := gbmDigitalCondFine r σ T s₀ K) (Pc := gbmDigitalCondCoarse r σ T s₀ K)
    (P := fun z => (Set.Ioi K).indicator (1 : ℝ → ℝ) (gbmExact r σ T s₀ 0 z))
    (measurable_gbmDigitalCondFine r σ T s₀ K) (measurable_gbmDigitalCondCoarse r σ T s₀ K)
    (memLp_gbmDigitalCondFine r σ T s₀ K) (memLp_gbmDigitalCondCoarse r σ T s₀ K)
    (integrable_digital (measurable_gbmExact r σ T s₀ 0) K)
    (gbmDigitalCond_integral_eq r σ hs₀ hσ hT K) (c₁ := C₁) (c₂ := C₂)
    (fun ℓ => by rw [integral_digital_gbmExact]; exact (hw ℓ).2)
    (fun ℓ => by
      cases ℓ with
      | zero =>
        rw [fineCoarseDiff, (gbm_digital_condExp_level_zero r σ s₀ K T).2.2]
        positivity
      | succ ℓ => exact (hv ℓ).2.2)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  rw [integral_digital_gbmExact] at hint hmse
  exact ⟨L, N, hN, hint, hmse, hcost⟩

/-! ### Theorem 1 with a general sample law and a cost `O(2^ℓ)` -/

/-- **Theorem 1 for a fine/coarse estimator with `β > γ = 1`, any sample law and any cost
`O(2^ℓ)`** (Giles 2015, §2.1, Theorem 1, p. 6, the case `β > γ`: cost `O(ε⁻²)`, with (2.4), p. 8).
Let `ν` be a probability measure on a sample space `Ω₀`, `T > 0`, `α ≥ ½`, `β > 1`, `P^f_ℓ`,
`P^c_ℓ` measurable functions in `L²(ν)` with `E[P^f_ℓ] = E[P^c_ℓ]` (2.4),
`|E[P^f_ℓ] − m| ≤ c₁ h_ℓ^α` and `V[P^f_ℓ − P^c_{ℓ−1}] ≤ c₂ h_ℓ^β` (`fineCoarseDiff`,
`h_ℓ = T 2^{−ℓ}`), independent samples with law `ν` (the coordinates of `ν^{⊗(ℕ×ℕ)}`) and cost
`κ_ℓ ≤ c₃ 2^ℓ` per level-`ℓ` sample, `c₃ > 0`.  Then there is `c₄ > 0` such that for every
`0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the error of the multilevel estimator of `m`
is square integrable with mean square `< ε²`, at cost `∑_{ℓ≤L} N_ℓ κ_ℓ ≤ c₄ ε⁻²`
(`giles_theorem1_fineCoarse`, `complexityBound_of_lt`; `theorem1_fineCoarse_of_rate_gt` is the
case `ν = stdNormalSeq`, `κ_ℓ = 2^ℓ`). -/
lemma theorem1_fineCoarse_of_rate_gt_cost {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀}
    [IsProbabilityMeasure ν] {T : ℝ} (hT : 0 < T) {α β : ℝ} (hα : 1 / 2 ≤ α) (hβ : 1 < β)
    {Pf Pc : ℕ → Ω₀ → ℝ} {m : ℝ} (hPfm : ∀ ℓ, Measurable (Pf ℓ))
    (hPcm : ∀ ℓ, Measurable (Pc ℓ)) (hPf : ∀ ℓ, MemLp (Pf ℓ) 2 ν) (hPc : ∀ ℓ, MemLp (Pc ℓ) 2 ν)
    (h24 : ∀ ℓ, ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν) {c₁ c₂ c₃ : ℝ} (hc₃ : 0 < c₃)
    (h_i : ∀ ℓ : ℕ, |∫ y, Pf ℓ y ∂ν - m| ≤ c₁ * (T / 2 ^ ℓ) ^ α)
    (h_iii : ∀ ℓ : ℕ, variance (fineCoarseDiff Pf Pc ℓ) ν ≤ c₂ * (T / 2 ^ ℓ) ^ β)
    {κ : ℕ → ℝ} (hκ : ∀ ℓ : ℕ, κ ℓ ≤ c₃ * 2 ^ ℓ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc)
            (fun p x => x p) ℓ (N ℓ) x - m) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => ν) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1), blockMean (fineCoarseDiff Pf Pc)
            (fun p x => x p) ℓ (N ℓ) x - m) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => ν) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * κ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs ν
  have hα0 : 0 < α := by linarith
  have hm : ∫ _y, m ∂ν = m := by simp only [integral_const, probReal_univ, one_smul]
  have hc₁ : 0 < (|c₁| + 1) * T ^ α := by positivity
  have h_i' : ∀ ℓ : ℕ, |∫ y, Pf ℓ y - (fun _ => m) y ∂ν| ≤
      (|c₁| + 1) * T ^ α * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) := fun ℓ => by
    rw [integral_sub ((hPf ℓ).integrable one_le_two) (integrable_const m), hm]
    have h2 : 0 ≤ T ^ α * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) := by positivity
    calc _ ≤ c₁ * (T / 2 ^ ℓ) ^ α := h_i ℓ
      _ = c₁ * (T ^ α * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) := by rw [div_two_pow_rpow hT.le]
      _ ≤ (|c₁| + 1) * (T ^ α * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c₁]) h2
      _ = _ := by ring
  have hc₂ : 0 < (|c₂| + 1) * T ^ β := by positivity
  have h_iii' : ∀ ℓ, variance (fineCoarseDiff Pf Pc ℓ) ν ≤
      (|c₂| + 1) * T ^ β * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) := fun ℓ => by
    have h2 : 0 ≤ T ^ β * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) := by positivity
    calc _ ≤ c₂ * (T / 2 ^ ℓ) ^ β := h_iii ℓ
      _ = c₂ * (T ^ β * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) := by rw [div_two_pow_rpow hT.le]
      _ ≤ (|c₂| + 1) * (T ^ β * (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c₂]) h2
      _ = _ := by ring
  have h_iv : ∀ ℓ : ℕ, κ ℓ ≤ c₃ * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, Real.rpow_natCast]
    exact hκ ℓ
  have hαβγ : min β 1 / 2 ≤ α := by
    rw [min_eq_right hβ.le]
    linarith
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => ν) (fun _ => m) Pf Pc (fun p x => x p)
    (fun ℓ _ _ => κ ℓ) κ (α := α) (β := β) (γ := 1) hα0
    (by linarith) one_pos hc₁ hc₂ hc₃ hαβγ hω hind (integrable_const m) hPfm hPcm hPf hPc h24
    (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i' h_iii' h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  rw [hm] at hmse
  refine ⟨L, N, hN, ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω
    (memLp_fineCoarseDiff hPf hPc) ℓ (N ℓ)).sub (memLp_const _)).integrable_sq, hmse, ?_⟩
  unfold totalCost at hcost
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul] at hcost
  rw [complexityBound_of_lt hβ ε] at hcost
  exact hcost

/-! ### Splitting: the number of sub-samples, the rates and Theorem 1 -/

/-- **The number of sub-samples on level `ℓ`** (Giles 2015, §5.2, p. 36, l. 1594–1600: "for each
set of Brownian increments up to one fine timestep before the end, one uses a number of samples of
the final Brownian increment to produce an average payoff. If the number of sub-samples is chosen
appropriately …"): `M_ℓ = ⌈h_ℓ^{−1/2}⌉` with `h_ℓ = T 2^{−ℓ}`.  This choice keeps the variance rate
of the conditional expectation; it does not give the same variance to leading order. -/
noncomputable def gbmSplitCount (T : ℝ) (ℓ : ℕ) : ℕ := ⌈(T / 2 ^ ℓ) ^ (-(1 / 2 : ℝ))⌉₊

/-- **The sub-samples cost `O(2^ℓ)`** (Giles 2015, §5.2, p. 36, l. 1597–1600: "without any increase
in the computational cost, again to leading order").  For `T > 0`: `M_ℓ ≥ 1`,
`M_ℓ ≥ h_ℓ^{−1/2}` and `2^ℓ + M_ℓ ≤ (2 + T^{−1/2}) 2^ℓ` (`M_ℓ < h_ℓ^{−1/2} + 1` and
`h_ℓ^{−1/2} = T^{−1/2} 2^{ℓ/2}`).  The bound used is `O(2^ℓ)`; the paper's "to leading order"
means `M_ℓ = o(2^ℓ)`, which holds (`M_ℓ ≤ T^{−1/2} 2^{ℓ/2} + 1`) but is not used. -/
lemma gbmSplitCount_bounds {T : ℝ} (hT : 0 < T) (ℓ : ℕ) :
    0 < gbmSplitCount T ℓ ∧ (T / 2 ^ ℓ) ^ (-(1 / 2 : ℝ)) ≤ (gbmSplitCount T ℓ : ℝ) ∧
      (2 : ℝ) ^ ℓ + gbmSplitCount T ℓ ≤ (2 + T ^ (-(1 / 2 : ℝ))) * 2 ^ ℓ := by
  have hh : 0 < T / 2 ^ ℓ := by positivity
  have hx : 0 < (T / 2 ^ ℓ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hh _
  unfold gbmSplitCount
  refine ⟨Nat.ceil_pos.2 hx, Nat.le_ceil _, ?_⟩
  have h1 : (⌈(T / 2 ^ ℓ) ^ (-(1 / 2 : ℝ))⌉₊ : ℝ) < (T / 2 ^ ℓ) ^ (-(1 / 2 : ℝ)) + 1 :=
    Nat.ceil_lt_add_one hx.le
  have h2 : (T / 2 ^ ℓ) ^ (-(1 / 2 : ℝ)) ≤ T ^ (-(1 / 2 : ℝ)) * 2 ^ ℓ := by
    rw [div_two_pow_rpow hT.le, neg_mul, neg_neg]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) ℓ])
  have h3 : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
  nlinarith

/-- The fine splitting payoff is a measurable function of the increments and the sub-samples
(Giles 2015, §5.2, p. 36, l. 1594–1598). -/
lemma measurable_gbmDigitalSplitFine (r σ T s₀ K : ℝ) (M ℓ : ℕ) :
    Measurable (gbmDigitalSplitFine r σ T s₀ K M ℓ) := by
  have hind : Measurable ((Set.Ioi K).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Ioi
  have hXp : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => milsteinPath (fun S => r * S)
      (fun S => σ * S) (T / 2 ^ ℓ) s₀ p.1 (2 ^ ℓ - 1) :=
    (measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _).comp measurable_fst
  unfold gbmDigitalSplitFine
  refine (Finset.measurable_sum _ fun i _ => hind.comp ?_).div_const _
  have hy : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 i :=
    (measurable_pi_apply i).comp measurable_snd
  unfold emStep
  fun_prop

/-- The coarse splitting payoff is a measurable function of the increments and the sub-samples
(Giles 2015, §5.2, p. 36, l. 1594–1598). -/
lemma measurable_gbmDigitalSplitCoarse (r σ T s₀ K : ℝ) (M ℓ : ℕ) :
    Measurable (gbmDigitalSplitCoarse r σ T s₀ K M ℓ) := by
  have hind : Measurable ((Set.Ioi K).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Ioi
  have hYp : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => milsteinPath (fun S => r * S)
      (fun S => σ * S) (T / 2 ^ ℓ) s₀ (pairAvg p.1) (2 ^ ℓ - 1) :=
    ((measurable_milsteinPath_incr (a := fun S => r * S) (b := fun S => σ * S) (by fun_prop)
      (by fun_prop) _ _ _).comp measurable_pairAvg).comp measurable_fst
  have hzp : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 (2 ^ (ℓ + 1) - 2) :=
    (measurable_pi_apply _).comp measurable_fst
  unfold gbmDigitalSplitCoarse
  refine (Finset.measurable_sum _ fun i _ => hind.comp ?_).div_const _
  have hy : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 i :=
    (measurable_pi_apply i).comp measurable_snd
  unfold emStep
  fun_prop

/-- The fine splitting payoff with `M ≥ 1` sub-samples lies in `[0, 1]`, so it is square
integrable (Giles 2015, §5.2, p. 36, l. 1594–1598: "an average payoff"). -/
lemma memLp_gbmDigitalSplitFine (r σ T s₀ K : ℝ) {M : ℕ} (hM : 0 < M) (ℓ : ℕ) :
    MemLp (gbmDigitalSplitFine r σ T s₀ K M ℓ) 2 (stdNormalSeq.prod stdNormalSeq) :=
  memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun _ =>
    sum_indicator_div_mem_Icc hM K _)
    (measurable_gbmDigitalSplitFine r σ T s₀ K M ℓ).aestronglyMeasurable 2

/-- The coarse splitting payoff with `M ≥ 1` sub-samples lies in `[0, 1]`, so it is square
integrable (Giles 2015, §5.2, p. 36, l. 1594–1598: "an average payoff"). -/
lemma memLp_gbmDigitalSplitCoarse (r σ T s₀ K : ℝ) {M : ℕ} (hM : 0 < M) (ℓ : ℕ) :
    MemLp (gbmDigitalSplitCoarse r σ T s₀ K M ℓ) 2 (stdNormalSeq.prod stdNormalSeq) :=
  memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun _ =>
    sum_indicator_div_mem_Icc hM K _)
    (measurable_gbmDigitalSplitCoarse r σ T s₀ K M ℓ).aestronglyMeasurable 2

/-- **The variance of the splitting estimator, for every strike** (Giles 2015, §5.2, p. 36,
l. 1591–1600: "Here the conditional expectation is replaced by a numerical estimate, averaging over
a number of sub-samples … If the number of sub-samples is chosen appropriately, the variance is the
same, to leading order").  For GBM with `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, every strike `K ∈ ℝ` and
every `q < 3/2` there is `C ≥ 0` such that for every level `ℓ + 1` (`h = T 2^{−(ℓ+1)}`) and every
number `M ≥ 1` of sub-samples (independent of the main increments,
`stdNormalSeq.prod stdNormalSeq`) the splitting correction `P^{f,M}_{ℓ+1} − P^{c,M}_ℓ`
(`gbmDigitalSplitFine`, `gbmDigitalSplitCoarse`) is square integrable and its second moment and
variance are at most `C (h^q + h^{q − 1/2}/M)`.

Proof: as `gbm_digital_split_variance_rate` (the case `K ≠ 0`): `gbm_split_sq_le`, the
conditional-expectation rate for every strike (`gbm_digital_condExp_variance_rate_all`) and the
mismatch rate `gbm_split_mismatch_rate` with `q − 1/2 < 1`.

**Deviation.**  The same rate, not the same variance to leading order. -/
theorem gbm_digital_split_variance_rate_all (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0)
    (hσ : σ ≠ 0) (hT : 0 < T) {q : ℝ} (hq : q < 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ M : ℕ), 0 < M →
      MemLp (fun p => gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
        gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) 2 (stdNormalSeq.prod stdNormalSeq) ∧
      ∫ p, (gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) ^ 2 ∂(stdNormalSeq.prod stdNormalSeq) ≤
        C * ((T / 2 ^ (ℓ + 1)) ^ q + (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M) ∧
      variance (fun p => gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) (stdNormalSeq.prod stdNormalSeq) ≤
        C * ((T / 2 ^ (ℓ + 1)) ^ q + (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M) := by
  obtain ⟨C₁, hC₁, hv⟩ := gbm_digital_condExp_variance_rate_all r σ (K := K) hs₀ hσ hT hq
  obtain ⟨C₂, hC₂, hm⟩ := gbm_split_mismatch_rate r σ hs₀ hσ hT K (q := q - 1 / 2)
    (by linarith)
  refine ⟨C₁ + C₂, by positivity, fun ℓ M hM => ?_⟩
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hL := memLp_gbmDigitalSplit_sub r σ T s₀ K ℓ hM
  have key : ∫ p, (gbmDigitalSplitFine r σ T s₀ K M (ℓ + 1) p -
      gbmDigitalSplitCoarse r σ T s₀ K M ℓ p) ^ 2 ∂(stdNormalSeq.prod stdNormalSeq) ≤
      (C₁ + C₂) * ((T / 2 ^ (ℓ + 1)) ^ q + (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M) := by
    refine (gbm_split_sq_le r σ hs₀ hσ hT K ℓ hM).trans ?_
    have h1 := (hv ℓ).2.1
    have h2 : stdNormalSeq.real {z | (Set.Ioi K).indicator (1 : ℝ → ℝ)
        (gbmMilEM r σ T s₀ (ℓ + 1) z) ≠ (Set.Ioi K).indicator 1
          (gbmMilEM r σ T s₀ ℓ (pairAvg z))} / M ≤
        C₂ * ((T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M) := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (hm ℓ) hM'.le
    have h3 : 0 ≤ (T / 2 ^ (ℓ + 1)) ^ q := by positivity
    have h4 : 0 ≤ (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / M := by positivity
    nlinarith
  exact ⟨hL, key, (variance_le_expectation_sq hL.aestronglyMeasurable).trans key⟩

/-- **`M_ℓ = ⌈h_ℓ^{−1/2}⌉` sub-samples keep the variance `O(h^q)`, `q < 3/2`, for every strike**
(Giles 2015, §5.2, p. 36, l. 1597–1600: "If the number of sub-samples is chosen appropriately, the
variance is the same, to leading order").  For `s₀ ≠ 0`, `σ ≠ 0`, `T > 0`, any `K` and `q < 3/2`
there is `C ≥ 0` with, on every level `ℓ + 1` and with `M_{ℓ+1}` sub-samples (`gbmSplitCount`),
`E[(P^{f}_{ℓ+1} − P^{c}_ℓ)²] ≤ C h^q` (square integrable) and `V_{ℓ+1} ≤ C h^q`
(`gbm_digital_split_variance_rate_all` with `h^{q−1/2}/M ≤ h^q`; as `gbm_digital_split_sqrt_rate`
for `K ≠ 0`). -/
lemma gbm_digital_split_count_rate (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) {q : ℝ} (hq : q < 3 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℕ,
      MemLp (fun p => gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T (ℓ + 1)) (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount T (ℓ + 1)) ℓ p) 2
          (stdNormalSeq.prod stdNormalSeq) ∧
      ∫ p, (gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T (ℓ + 1)) (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount T (ℓ + 1)) ℓ p) ^ 2
          ∂(stdNormalSeq.prod stdNormalSeq) ≤ C * (T / 2 ^ (ℓ + 1)) ^ q ∧
      variance (fun p => gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T (ℓ + 1)) (ℓ + 1) p -
          gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount T (ℓ + 1)) ℓ p)
          (stdNormalSeq.prod stdNormalSeq) ≤ C * (T / 2 ^ (ℓ + 1)) ^ q := by
  obtain ⟨C, hC, hb⟩ := gbm_digital_split_variance_rate_all r σ (K := K) hs₀ hσ hT hq
  refine ⟨2 * C, by positivity, fun ℓ => ?_⟩
  have hh : 0 < T / 2 ^ (ℓ + 1) := by positivity
  have hx : 0 < (T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hh _
  obtain ⟨hM, hMx, -⟩ := gbmSplitCount_bounds hT (ℓ + 1)
  obtain ⟨hL, hI, hV⟩ := hb ℓ _ hM
  have hsmall : (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / (gbmSplitCount T (ℓ + 1) : ℝ) ≤
      (T / 2 ^ (ℓ + 1)) ^ q := by
    calc (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / (gbmSplitCount T (ℓ + 1) : ℝ)
        ≤ (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) / (T / 2 ^ (ℓ + 1)) ^ (-(1 / 2 : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) hx hMx
      _ = (T / 2 ^ (ℓ + 1)) ^ q := by
          rw [← Real.rpow_sub hh]
          norm_num
  have hfin : C * ((T / 2 ^ (ℓ + 1)) ^ q + (T / 2 ^ (ℓ + 1)) ^ (q - 1 / 2) /
      (gbmSplitCount T (ℓ + 1) : ℝ)) ≤ 2 * C * (T / 2 ^ (ℓ + 1)) ^ q := by
    have := mul_le_mul_of_nonneg_left hsmall hC
    nlinarith
  exact ⟨hL, hI.trans hfin, hV.trans hfin⟩

/-- **The weak error of the splitting estimator is that of the conditional expectation** (Giles
2015, §5.2, p. 36, l. 1594–1595: "Here the conditional expectation is replaced by a numerical
estimate, averaging over a number of sub-samples", and l. 1578: `α`).  For `s₀ ≠ 0`, `σ ≠ 0`,
`T > 0`, any `K` and `q < 1` there is `C ≥ 0` such that for every level `ℓ` and every `M ≥ 1`
the fine splitting payoff (`gbmDigitalSplitFine`, under `stdNormalSeq.prod stdNormalSeq`) has the
mean of the conditional-expectation payoff `P^f_ℓ` (`gbmDigitalCondFine`), and
`|E[P^{f,M}_ℓ] − E[H(S_T − K)]| ≤ C h_ℓ^q` (`gbmDigitalSplit_integral_eq`,
`gbm_digital_condExp_weak_rate`). -/
theorem gbm_digital_split_weak_rate (r σ : ℝ) {s₀ T : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) (K : ℝ) {q : ℝ} (hq : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ M : ℕ), 0 < M →
      ∫ p, gbmDigitalSplitFine r σ T s₀ K M ℓ p ∂(stdNormalSeq.prod stdNormalSeq) =
        ∫ z, gbmDigitalCondFine r σ T s₀ K ℓ z ∂stdNormalSeq ∧
      |∫ p, gbmDigitalSplitFine r σ T s₀ K M ℓ p ∂(stdNormalSeq.prod stdNormalSeq) -
          ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
            (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1| ≤
        C * (T / 2 ^ ℓ) ^ q := by
  obtain ⟨C, hC, hw⟩ := gbm_digital_condExp_weak_rate r σ hs₀ hσ hT K hq
  refine ⟨C, hC, fun ℓ M hM => ?_⟩
  have e : ∫ p, gbmDigitalSplitFine r σ T s₀ K M ℓ p ∂(stdNormalSeq.prod stdNormalSeq) =
      ∫ z, gbmDigitalCondFine r σ T s₀ K ℓ z ∂stdNormalSeq := by
    rw [(gbmDigitalSplit_integral_eq r σ T s₀ K ℓ hM).1, (hw ℓ).1]
  refine ⟨e, ?_⟩
  rw [e]
  exact (hw ℓ).2

/-- **G5.2-19 (partial): Theorem 1 end to end for the splitting estimator of the digital option:
mean square error `< ε²` at cost `O(ε⁻²)`** (Giles 2015, §5.2, p. 36, l. 1591–1600: "In this case,
one can use the technique of "splitting" … Here the conditional expectation is replaced by a
numerical estimate, averaging over a number of sub-samples. i.e. for each set of Brownian increments
up to one fine timestep before the end, one uses a number of samples of the final Brownian increment
to produce an average payoff. If the number of sub-samples is chosen appropriately, the variance is
the same, to leading order, without any increase in the computational cost, again to leading order",
with l. 1578–1580: "Since `β > γ`, the MLMC complexity is `O(ε⁻²)`", Theorem 1, §2.1, p. 6, and
(2.4), l. 1584–1590).  For GBM `dS = rS dt + σS dW` with `s₀ ≠ 0`, `σ ≠ 0`, `T > 0` and any strike
`K ∈ ℝ`: a level-`ℓ` sample is `(Z, Y) ∼ stdNormalSeq.prod stdNormalSeq` (the path increments and
the sub-samples of the last increment), the samples are independent across samples and levels, level
`ℓ` uses `M_ℓ = ⌈h_ℓ^{−1/2}⌉` sub-samples (`gbmSplitCount`), the fine payoff is
`gbmDigitalSplitFine` with `M_ℓ`, the coarse payoff on level `ℓ + 1` is `gbmDigitalSplitCoarse` with
`M_{ℓ+1}`, the correction is `fineCoarseDiff`, and a level-`ℓ` sample costs `2^ℓ + M_ℓ` (path steps
plus sub-samples).  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ
≥ 1` for which the multilevel estimator of `E[H(S_T − K)] = ∫ 1_{s₀ e^{(r−σ²/2)T + σ√T w} > K}
dN(0,1)(w)` has a square-integrable error with mean square `< ε²`, at cost `∑_{ℓ≤L} N_ℓ (2^ℓ + M_ℓ)
≤ c₄ ε⁻²`.

Proof: `theorem1_fineCoarse_of_rate_gt_cost` with `α = 3/4` (`gbm_digital_split_weak_rate`),
`β = 5/4` (`gbm_digital_split_count_rate` on the levels `ℓ ≥ 1`; the level-`0` payoff lies in
`[0, 1]`, so its variance is at most `1`), `γ = 1` (`2^ℓ + M_ℓ ≤ (2 + T^{−1/2}) 2^ℓ`,
`gbmSplitCount_bounds`) and (2.4) (`gbmDigitalSplit_integral_eq`: both payoffs of level `ℓ` have
mean `P(Ŝ^f_N > K)` whatever the numbers of sub-samples).

**Deviations.**  The cost model counts the `2^ℓ` fine path steps and one unit per sub-sample, not
the coarse path or the coarse sub-sample steps (each a constant factor, so `c₄` alone changes).
"The variance is the same, to leading order" is not proved, only the same rate `O(h^q)`,
`q < 3/2`; the rates used are `α = 3/4`, `β = 5/4`; the factor `25 e^{−rT}` is omitted. -/
theorem gbm_digital_split_theorem1 (r σ : ℝ) {s₀ T K : ℝ} (hs₀ : s₀ ≠ 0) (hσ : σ ≠ 0)
    (hT : 0 < T) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ => gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T ℓ) ℓ)
              (fun ℓ => gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount T (ℓ + 1)) ℓ))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq.prod stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ => gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T ℓ) ℓ)
              (fun ℓ => gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount T (ℓ + 1)) ℓ))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, (Set.Ioi K).indicator (1 : ℝ → ℝ)
              (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq.prod stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (2 ^ ℓ + gbmSplitCount T ℓ) ≤ c₄ * ε ^ (-2 : ℝ) := by
  obtain ⟨C₁, -, hw⟩ := gbm_digital_split_weak_rate r σ hs₀ hσ hT K (q := 3 / 4) (by norm_num)
  obtain ⟨C₂, hC₂, hv⟩ := gbm_digital_split_count_rate r σ (K := K) hs₀ hσ hT (q := 5 / 4)
    (by norm_num)
  have hPfm : ∀ ℓ, Measurable (gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T ℓ) ℓ) :=
    fun ℓ => measurable_gbmDigitalSplitFine r σ T s₀ K _ ℓ
  have hPcm : ∀ ℓ, Measurable (gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount T (ℓ + 1)) ℓ) :=
    fun ℓ => measurable_gbmDigitalSplitCoarse r σ T s₀ K _ ℓ
  have hPf : ∀ ℓ, MemLp (gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T ℓ) ℓ) 2
      (stdNormalSeq.prod stdNormalSeq) := fun ℓ =>
    memLp_gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount_bounds hT ℓ).1 ℓ
  have hPc : ∀ ℓ, MemLp (gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount T (ℓ + 1)) ℓ) 2
      (stdNormalSeq.prod stdNormalSeq) := fun ℓ =>
    memLp_gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount_bounds hT (ℓ + 1)).1 ℓ
  have h24 : ∀ ℓ, ∫ p, gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T ℓ) ℓ p
      ∂(stdNormalSeq.prod stdNormalSeq) =
      ∫ p, gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount T (ℓ + 1)) ℓ p
      ∂(stdNormalSeq.prod stdNormalSeq) := fun ℓ => by
    rw [(gbmDigitalSplit_integral_eq r σ T s₀ K ℓ (gbmSplitCount_bounds hT ℓ).1).1,
      (gbmDigitalSplit_integral_eq r σ T s₀ K ℓ (gbmSplitCount_bounds hT (ℓ + 1)).1).2]
  have hT1 : T ^ (-(5 / 4 : ℝ)) * T ^ (5 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hT]
    norm_num
  have h_iii : ∀ ℓ : ℕ, variance (fineCoarseDiff
      (fun ℓ => gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T ℓ) ℓ)
      (fun ℓ => gbmDigitalSplitCoarse r σ T s₀ K (gbmSplitCount T (ℓ + 1)) ℓ) ℓ)
      (stdNormalSeq.prod stdNormalSeq) ≤ (C₂ + T ^ (-(5 / 4 : ℝ))) * (T / 2 ^ ℓ) ^ (5 / 4 : ℝ) :=
    fun ℓ => by
    cases ℓ with
    | zero =>
      rw [fineCoarseDiff, pow_zero, div_one]
      have hle : ∫ p, gbmDigitalSplitFine r σ T s₀ K (gbmSplitCount T 0) 0 p ^ 2
          ∂(stdNormalSeq.prod stdNormalSeq) ≤ 1 := by
        refine (integral_mono (hPf 0).integrable_sq (integrable_const 1) fun p => ?_).trans
          (le_of_eq ?_)
        · obtain ⟨h1, h2⟩ := sum_indicator_div_mem_Icc (gbmSplitCount_bounds hT 0).1 K
            (fun i => emStep (fun S => r * S) (fun S => σ * S) (T / 2 ^ 0)
              (milsteinPath (fun S => r * S) (fun S => σ * S) (T / 2 ^ 0) s₀ p.1 (2 ^ 0 - 1))
              (Real.sqrt (T / 2 ^ 0) * p.2 i))
          unfold gbmDigitalSplitFine
          dsimp only
          nlinarith
        · simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      have hC : 0 ≤ C₂ * T ^ (5 / 4 : ℝ) := by positivity
      refine (variance_le_expectation_sq (hPfm 0).aestronglyMeasurable).trans ?_
      refine hle.trans ?_
      nlinarith
    | succ ℓ =>
      refine ((hv ℓ).2.2).trans ?_
      have : 0 ≤ T ^ (-(5 / 4 : ℝ)) * (T / 2 ^ (ℓ + 1)) ^ (5 / 4 : ℝ) := by positivity
      nlinarith
  obtain ⟨c₄, hc₄, h⟩ := theorem1_fineCoarse_of_rate_gt_cost hT (α := 3 / 4) (β := 5 / 4)
    (by norm_num) (by norm_num) hPfm hPcm hPf hPc h24 (c₃ := 2 + T ^ (-(1 / 2 : ℝ)))
    (by positivity) (fun ℓ => (hw ℓ _ (gbmSplitCount_bounds hT ℓ).1).2) h_iii
    (κ := fun ℓ => 2 ^ ℓ + (gbmSplitCount T ℓ : ℝ)) (fun ℓ => (gbmSplitCount_bounds hT ℓ).2.2)
  exact ⟨c₄, hc₄, h⟩

end MLMC
