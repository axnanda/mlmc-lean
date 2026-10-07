import MlmcLean.AsymptoticNormal
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# The central limit theorem for multilevel Monte Carlo with a growing number of levels

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.1, p. 8 of
the author's version.

**Giles (2015), §2.1, p. 8.** "Collier, Haji-Ali, Nobile, von Schwerin and Tempone (2014) have
developed a modified version of the Theorem. Instead of bounding the Mean Square Error, they prefer
to use the Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence. This exploits the fact that the multilevel correction `Y_ℓ` on each
level is asymptotically Normally-distributed, and therefore so is `Y`."

The paper only cites Collier et al.; it states neither a theorem nor hypotheses.
`MlmcLean/AsymptoticNormal.lean` proves the statement for a fixed finest level `L` and sample sizes
`N_ℓ = m_ℓ n`, `n → ∞`.  In the algorithm of Collier et al. the finest level grows as the tolerance
decreases, so the number of levels, the laws of the corrections and the sample sizes change
together, and the normality of `Y` is a central limit theorem for a triangular array.  Mathlib only
has the i.i.d. central limit theorem; this file proves the Lindeberg and Lyapunov theorems for
triangular arrays and applies them to the estimator (2.2).  The moment hypotheses (a finite
centred moment of order `2 + δ` on the levels used, and Lyapunov's condition or a bound on the
standardised moments) are this formalisation's, not the paper's.

**The paper's "therefore" needs a hypothesis.**  For a fixed set of levels, independence and the
asymptotic normality of every `Y_ℓ` do give that of `Y` (`tendstoInDistribution_mlmcEstimator`).
When the number of levels grows they do not.  Example: let `ΔP_ℓ = ±a_ℓ` with probability `p_ℓ/2`
each and `ΔP_ℓ = 0` otherwise, where `p_ℓ = 2^{−ℓ}` and `a_ℓ² p_ℓ = 1` (so `E[ΔP_ℓ] = 0`,
`V_ℓ = 1`), and take `L_k = k`, `N_{k,k} = k + 1` and `N_{k,ℓ} = (k + 1)³` for `ℓ < k`.  Then
`min_ℓ N_{k,ℓ} → ∞` and every fixed level is asymptotically normal, but the levels `ℓ < k` carry
only the fraction `k/(k + (k + 1)²) → 0` of `σ_k² = k/(k + 1)³ + 1/(k + 1)`, and with probability
`(1 − 2^{−k})^{k+1} → 1` all `k + 1` samples on the finest level vanish.  So
`(Y_k − E[P_{L_k}])/σ_k → 0` in probability, not to `N(0, 1)`.  The kurtosis of `ΔP_k` is `2^k`,
so the uniform moment bound of `tendstoInDistribution_mlmcEstimator_of_moment_le` cannot be
dropped either.  Lyapunov's condition (or the uniform moment bound together with
`min_ℓ N_{k,ℓ} → ∞`) is what closes this gap in the informal argument.

Notation: the estimator (2.2) is `Y_k = ∑_{ℓ=0}^{L_k} N_{k,ℓ}⁻¹ ∑_{n<N_{k,ℓ}} ΔP_ℓ(ω^{(ℓ,n)})`
(`mlmcEstimator`), built from independent inputs `ω^{(ℓ,n)}` of law `ν`; `ΔP_ℓ = P_ℓ − P_{ℓ−1}`,
`V_ℓ = V[ΔP_ℓ]`, `M_ℓ = E|ΔP_ℓ − E[ΔP_ℓ]|^{2+δ}` and `σ_k² = ∑_{ℓ ≤ L_k} V_ℓ/N_{k,ℓ}`, which is
`V[Y_k]` by (2.3).  Hypotheses on the levels are imposed only on the levels `ℓ ≤ L_k` that are
used, and `N_{k,ℓ} ≥ 1`, `σ_k > 0` only for all large `k` (finitely many rows do not matter).

* `tendstoInDistribution_lindeberg`: the Lindeberg central limit theorem for triangular arrays:
  if the `X_{k,j}`, `j ∈ s_k`, are independent, centred and square integrable with variances
  summing to `1`, and `∑_j E[X_{k,j}²; |X_{k,j}| > ε] → 0` for every `ε > 0`, then
  `∑_j X_{k,j} → N(0, 1)` in distribution (row `k` may live on its own probability space);
* `tendsto_lindeberg_of_lyapunov`, `tendstoInDistribution_lyapunov`: Lyapunov's condition
  `∑_j E|X_{k,j}|^{2+δ} → 0` implies Lindeberg's, hence the Lyapunov central limit theorem;
* `tendstoInDistribution_mlmcEstimator_lyapunov`: if
  `∑_{ℓ ≤ L_k} M_ℓ N_{k,ℓ}^{−1−δ} / σ_k^{2+δ} → 0`, then `(Y_k − E[P_{L_k}]) / σ_k → N(0, 1)` in
  distribution, with no condition on the growth of `L_k`;
* `tendstoInDistribution_mlmcEstimator_of_moment_le`: the same if `M_ℓ ≤ K V_ℓ^{1+δ/2}` on the
  levels used and `min_{ℓ ≤ L_k} N_{k,ℓ} → ∞` (key inequality
  `∑_ℓ (V_ℓ/N_ℓ)^{1+δ/2} ≤ σ^{2+δ}`, `sum_rpow_le_rpow_sum_of_one_le`);
* `tendsto_measureReal_abs_mlmcEstimator_sub_le` and
  `tendsto_measureReal_abs_mlmcEstimator_sub_le_of_moment_le`: the confidence interval,
  `P(|Y_k − E[P_{L_k}]| ≤ z σ_k) → 2Φ(z) − 1` for every `z ≥ 0`, `Φ` the standard normal
  distribution function (`tendsto_measureReal_abs_le_of_tendstoInDistribution`, a consequence of
  the portmanteau theorem);
* `tendstoInDistribution_mlmcEstimator_of_bias`,
  `tendsto_measureReal_abs_mlmcEstimator_sub_le_of_bias`: the same around `E[P]` itself when the
  bias is small against the standard deviation, `(E[P_{L_k}] − E[P])/σ_k → 0` (Slutsky,
  `TendstoInDistribution.add_of_tendstoInMeasure_const`);
* `eventually_lt_measureReal_abs_mlmcEstimator_sub_le_tol`: the tolerance split of Collier et al.:
  if `|E[P_{L_k} − P]| ≤ (1 − θ) TOL_k` and `z σ_k ≤ θ TOL_k`, then
  `liminf_k P(|Y_k − E[P]| ≤ TOL_k) ≥ 2Φ(z) − 1`, i.e. the error is below `TOL_k` with asymptotic
  confidence at least `2Φ(z) − 1`.

The intervals use the exact standard deviation `σ_k`; Collier et al. use estimated variances,
which needs a further Slutsky argument for the consistency of the estimates, not formalised here.

**Method.**  Characteristic functions and Lévy's continuity theorem
(`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`).  With
`R(x) = e^{ix} − (1 + ix − x²/2)`, `|R(x)| ≤ 4x²` for all `x` and `|R(x)| ≤ |x|³` for `|x| ≤ 1`.
For a centred `Z` with `E[Z²] = s²` and `ε ≥ 0`, `|t| ε ≤ 1`, splitting on `|Z| ≤ ε` gives
`|E e^{itZ} − (1 − t²s²/2)| ≤ |t|³ ε s² + 4t² E[Z²; |Z| > ε]`.  For a row with variances `s_j²`
summing to `1`, `|∏ a_j − ∏ b_j| ≤ ∑ |a_j − b_j|` when `|a_j|, |b_j| ≤ 1`,
`|e^{−y} − (1 − y)| ≤ y²` for `y ≥ 0` and `s_j² ≤ ε² + Λ(ε)` give
`|E e^{it∑_j Z_j} − e^{−t²/2}| ≤ |t|³ ε + t⁴ ε²/4 + (4t² + t⁴/4) Λ(ε)`, where
`Λ(ε) = ∑_j E[Z_j²; |Z_j| > ε]` (`norm_charFun_sum_sub_le_lindeberg`); let `k → ∞`, then `ε → 0`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

/-! ### Elementary estimates -/

/-- The second-order Taylor remainder of `x ↦ e^{ix}` is quadratically small everywhere:
`|e^{ix} − (1 + ix − x²/2)| ≤ 4x²` (used for the Lindeberg tail in Giles 2015, §2.1, p. 8). -/
lemma norm_cexp_mul_I_sub_le_sq (x : ℝ) :
    ‖Complex.exp (x * Complex.I) - (1 + x * Complex.I - x ^ 2 / 2)‖ ≤ 4 * x ^ 2 := by
  have h1 : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  have h2 : ‖(x : ℂ) ^ 2 / 2‖ = x ^ 2 / 2 := by simp
  have hsplit : Complex.exp (x * Complex.I) - (1 + x * Complex.I - x ^ 2 / 2) =
      (Complex.exp (x * Complex.I) - 1 - x * Complex.I) + (x : ℂ) ^ 2 / 2 := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [h2]
  rcases le_or_gt |x| 1 with hx | hx
  · have h := Complex.norm_exp_sub_one_sub_id_le (x := x * Complex.I) (by rw [h1]; exact hx)
    rw [h1, sq_abs] at h
    nlinarith [sq_nonneg x]
  · have h3 : ‖Complex.exp (x * Complex.I) - 1 - x * Complex.I‖ ≤ 2 + |x| := by
      calc ‖Complex.exp (x * Complex.I) - 1 - x * Complex.I‖
          ≤ ‖Complex.exp (x * Complex.I)‖ + ‖(1 : ℂ)‖ + ‖(x : ℂ) * Complex.I‖ :=
            (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
        _ = 2 + |x| := by rw [Complex.norm_exp_ofReal_mul_I, h1, norm_one]; ring
    have hx2 : |x| ≤ x ^ 2 := by rw [← sq_abs]; nlinarith
    nlinarith

/-- The second-order Taylor remainder of `x ↦ e^{ix}` is cubically small near `0`:
`|e^{ix} − (1 + ix − x²/2)| ≤ |x|³` for `|x| ≤ 1` (from `Complex.exp_bound`; used for the
truncated part in Giles 2015, §2.1, p. 8). -/
lemma norm_cexp_mul_I_sub_le_cube {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp (x * Complex.I) - (1 + x * Complex.I - x ^ 2 / 2)‖ ≤ |x| ^ 3 := by
  have h1 : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  have h := Complex.exp_bound (x := x * Complex.I) (by rw [h1]; exact hx) (n := 3) (by norm_num)
  have hs : ∑ m ∈ range 3, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
      1 + x * Complex.I - x ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hs, h1] at h
  norm_num [Nat.factorial] at h
  have h0 : (0 : ℝ) ≤ |x| ^ 3 := by positivity
  linarith

/-- Products of complex numbers of modulus at most one are `1`-Lipschitz in each factor:
`|∏ a_i − ∏ b_i| ≤ ∑ |a_i − b_i|` when all `|a_i|, |b_i| ≤ 1` (the characteristic function of a
sum of independent variables is the product of theirs; Giles 2015, §2.1, p. 8). -/
lemma norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) {a b : ι → ℂ}
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hbs : ‖∏ j ∈ s, b j‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun j _ => norm_nonneg _)
        fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hai := ha i (Finset.mem_insert_self i s)
    have ih' := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    have heq : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        a i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) + (a i - b i) * ∏ j ∈ s, b j := by ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hn1 := norm_nonneg (∏ j ∈ s, a j - ∏ j ∈ s, b j)
    have hn2 := norm_nonneg (a i - b i)
    nlinarith [mul_le_mul hai ih' hn1 zero_le_one, mul_le_mul_of_nonneg_left hbs hn2]

/-- `|e^{−y} − (1 − y)| ≤ y²` for `y ≥ 0`: the Gaussian factor `e^{−t² s²/2}` is close to the
second-order expansion `1 − t² s²/2` of a characteristic function (Giles 2015, §2.1, p. 8). -/
lemma abs_exp_neg_sub_le_sq {y : ℝ} (hy : 0 ≤ y) : |Real.exp (-y) - (1 - y)| ≤ y ^ 2 := by
  rcases le_or_gt y 1 with h1 | h1
  · have h := Real.abs_exp_sub_one_sub_id_le (x := -y)
      (by rw [abs_neg, abs_of_nonneg hy]; exact h1)
    rw [neg_sq] at h
    calc |Real.exp (-y) - (1 - y)| = |Real.exp (-y) - 1 - -y| := by ring_nf
      _ ≤ y ^ 2 := h
  · have hlow : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have hup : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [abs_of_nonneg (by linarith)]
    nlinarith

/-- The pointwise Lindeberg split of the Taylor remainder: for `ε ≥ 0` with `|t| ε ≤ 1`,
`|e^{itx} − (1 + itx − (tx)²/2)| ≤ |t|³ ε x² + 4t² x² 𝟙{|x| > ε}` (cubic bound on `|x| ≤ ε`,
quadratic bound on `|x| > ε`; Giles 2015, §2.1, p. 8). -/
lemma norm_cexp_mul_I_sub_le_lindeberg {ε t : ℝ} (hε : 0 ≤ ε) (htε : |t| * ε ≤ 1) (x : ℝ) :
    ‖Complex.exp ((t * x : ℝ) * Complex.I) -
        (1 + (t * x : ℝ) * Complex.I - ((t * x : ℝ) : ℂ) ^ 2 / 2)‖ ≤
      |t| ^ 3 * ε * x ^ 2 + 4 * t ^ 2 * {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) x := by
  by_cases hx : ε < |x|
  · rw [Set.indicator_of_mem (by exact hx)]
    have h := norm_cexp_mul_I_sub_le_sq (t * x)
    have h0 : 0 ≤ |t| ^ 3 * ε * x ^ 2 := by positivity
    calc _ ≤ 4 * (t * x) ^ 2 := h
      _ ≤ _ := by rw [mul_pow]; linarith
  · rw [Set.indicator_of_notMem (by exact hx)]
    replace hx := not_lt.1 hx
    have htx : |t * x| ≤ 1 := by
      rw [abs_mul]
      calc |t| * |x| ≤ |t| * ε := by gcongr
        _ ≤ 1 := htε
    calc _ ≤ |t * x| ^ 3 := norm_cexp_mul_I_sub_le_cube htx
      _ = |t| ^ 3 * |x| * x ^ 2 := by rw [abs_mul, mul_pow, ← sq_abs x]; ring
      _ ≤ |t| ^ 3 * ε * x ^ 2 := by gcongr
      _ = _ := by ring

/-- The key inequality of the multilevel corollary (with `a_ℓ = V_ℓ/N_ℓ`, `p = 1 + δ/2`):
`∑ a_i^p ≤ (∑ a_i)^p` for `a_i ≥ 0` and `p ≥ 1`, since `a_i^{p−1} ≤ (∑ a_j)^{p−1}`. -/
lemma sum_rpow_le_rpow_sum_of_one_le {ι : Type*} (s : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, a i ^ p ≤ (∑ i ∈ s, a i) ^ p := by
  have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  have hp0 : (1 : ℝ) + (p - 1) ≠ 0 := by linarith
  calc ∑ i ∈ s, a i ^ p = ∑ i ∈ s, a i * a i ^ (p - 1) := Finset.sum_congr rfl fun i hi => by
        rw [← Real.rpow_one_add' (ha i hi) hp0]
        ring_nf
    _ ≤ ∑ i ∈ s, a i * (∑ j ∈ s, a j) ^ (p - 1) := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (ha i hi)
          (Finset.single_le_sum ha hi) (by linarith)) (ha i hi)
    _ = (∑ i ∈ s, a i) ^ p := by
        rw [← Finset.sum_mul, ← Real.rpow_one_add' hS hp0]
        ring_nf

/-! ### One row of a triangular array -/

section Row

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The Lindeberg integrand `x ↦ x² 𝟙{|x| > ε}` is measurable (Giles 2015, §2.1, p. 8). -/
lemma measurable_lindebergIntegrand (ε : ℝ) :
    Measurable ({y : ℝ | ε < |y|}.indicator fun y => y ^ 2) :=
  (measurable_id.pow_const 2).indicator
    (measurableSet_lt measurable_const continuous_abs.measurable)

/-- The Lindeberg term `E[X²; |X| > ε]` as the integral of the Lindeberg integrand of `X`
(Giles 2015, §2.1, p. 8). -/
lemma integral_lindebergIntegrand {X : Ω → ℝ} (hX : AEMeasurable X P) (ε : ℝ) :
    ∫ ω, {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) (X ω) ∂P =
      ∫ ω in {ω | ε < |X ω|}, X ω ^ 2 ∂P := by
  have hS : NullMeasurableSet {ω | ε < |X ω|} P :=
    nullMeasurableSet_lt aemeasurable_const (continuous_abs.measurable.comp_aemeasurable hX)
  rw [← integral_indicator₀ hS]
  rfl

/-- The Lindeberg integrand of a square-integrable `X` is integrable (it is at most `X²`; Giles
2015, §2.1, p. 8). -/
lemma integrable_lindebergIntegrand {X : Ω → ℝ} (hX : MemLp X 2 P) (ε : ℝ) :
    Integrable (fun ω => {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) (X ω)) P := by
  refine hX.integrable_sq.mono
    ((measurable_lindebergIntegrand ε).comp_aemeasurable
      hX.aestronglyMeasurable.aemeasurable).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  by_cases h : ε < |X ω|
  · simp [Set.indicator_of_mem (show X ω ∈ {y : ℝ | ε < |y|} from h)]
  · simp [Set.indicator_of_notMem (show X ω ∉ {y : ℝ | ε < |y|} from h), sq_nonneg]

/-- The Lindeberg term `E[X²; |X| > ε]` is nonnegative (Giles 2015, §2.1, p. 8). -/
lemma setIntegral_lindeberg_nonneg (X : Ω → ℝ) (ε : ℝ) :
    0 ≤ ∫ ω in {ω | ε < |X ω|}, X ω ^ 2 ∂P :=
  integral_nonneg fun _ => sq_nonneg _

/-- Lyapunov bounds Lindeberg: `E[X²; |X| > ε] ≤ ε^{−δ} E|X|^{2+δ}` for `ε > 0`, `δ ≥ 0`, since
`x² ≤ ε^{−δ} |x|^{2+δ}` on `|x| > ε` (Giles 2015, §2.1, p. 8). -/
lemma setIntegral_lindeberg_le_lyapunov {X : Ω → ℝ} (hX : AEMeasurable X P) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ) (hint : Integrable (fun ω => |X ω| ^ (2 + δ)) P) :
    ∫ ω in {ω | ε < |X ω|}, X ω ^ 2 ∂P ≤ ε ^ (-δ) * ∫ ω, |X ω| ^ (2 + δ) ∂P := by
  rw [← integral_lindebergIntegrand hX, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun ω => ?_) (hint.const_mul _)
    (ae_of_all _ fun ω => ?_)
  · exact Set.indicator_nonneg (fun y _ => sq_nonneg y) _
  · show {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) (X ω) ≤ ε ^ (-δ) * |X ω| ^ (2 + δ)
    by_cases h : ε < |X ω|
    · rw [Set.indicator_of_mem (show X ω ∈ {y : ℝ | ε < |y|} from h)]
      have hX0 : 0 < |X ω| := hε.trans h
      have h1 : ε ^ δ ≤ |X ω| ^ δ := Real.rpow_le_rpow hε.le h.le hδ
      have h2 : 0 < ε ^ δ := Real.rpow_pos_of_pos hε δ
      calc X ω ^ 2 = X ω ^ 2 * (ε ^ δ * (ε ^ δ)⁻¹) := by rw [mul_inv_cancel₀ h2.ne', mul_one]
        _ ≤ X ω ^ 2 * (|X ω| ^ δ * (ε ^ δ)⁻¹) := by gcongr
        _ = ε ^ (-δ) * |X ω| ^ (2 + δ) := by
          rw [Real.rpow_neg hε.le, Real.rpow_add hX0, Real.rpow_two, sq_abs]
          ring
    · rw [Set.indicator_of_notMem (show X ω ∉ {y : ℝ | ε < |y|} from h)]
      have := Real.rpow_nonneg (abs_nonneg (X ω)) (2 + δ)
      have := Real.rpow_nonneg hε.le (-δ)
      positivity

variable [IsProbabilityMeasure P]

/-- A single variance is controlled by the truncation level and the Lindeberg term: for a centred
square-integrable `X`, `V[X] ≤ ε² + E[X²; |X| > ε]` (Giles 2015, §2.1, p. 8). -/
lemma variance_le_sq_add_lindeberg {X : Ω → ℝ} (hX : MemLp X 2 P) (h0 : P[X] = 0) (ε : ℝ) :
    Var[X; P] ≤ ε ^ 2 + ∫ ω in {ω | ε < |X ω|}, X ω ^ 2 ∂P := by
  have hXm := hX.aestronglyMeasurable.aemeasurable
  have hind := integrable_lindebergIntegrand hX ε
  rw [variance_of_integral_eq_zero hXm h0, ← integral_lindebergIntegrand hXm]
  calc ∫ ω, X ω ^ 2 ∂P
      ≤ ∫ ω, (ε ^ 2 + {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) (X ω)) ∂P :=
        integral_mono hX.integrable_sq ((integrable_const _).add hind) fun ω => ?_
    _ = _ := by rw [integral_add (integrable_const _) hind, integral_const, probReal_univ,
        one_smul]
  by_cases h : ε < |X ω|
  · simp [Set.indicator_of_mem (show X ω ∈ {y : ℝ | ε < |y|} from h), sq_nonneg]
  · rw [Set.indicator_of_notMem (show X ω ∉ {y : ℝ | ε < |y|} from h), add_zero, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (not_lt.1 h) 2

/-- The characteristic function of a centred square-integrable `X` is close to its second-order
expansion: for `ε ≥ 0` with `|t| ε ≤ 1`,
`|E e^{itX} − (1 − t² V[X]/2)| ≤ |t|³ ε V[X] + 4t² E[X²; |X| > ε]` (Giles 2015, §2.1, p. 8). -/
lemma norm_charFun_sub_le_lindeberg {X : Ω → ℝ} (hX : MemLp X 2 P) (h0 : P[X] = 0) {ε t : ℝ}
    (hε : 0 ≤ ε) (htε : |t| * ε ≤ 1) :
    ‖charFun (P.map X) t - ((1 - t ^ 2 * Var[X; P] / 2 : ℝ) : ℂ)‖ ≤
      |t| ^ 3 * ε * Var[X; P] + 4 * t ^ 2 * ∫ ω in {ω | ε < |X ω|}, X ω ^ 2 ∂P := by
  have hXm := hX.aestronglyMeasurable.aemeasurable
  have hX1 : Integrable X P := hX.integrable one_le_two
  have hX2 : Integrable (fun ω => X ω ^ 2) P := hX.integrable_sq
  have hind := integrable_lindebergIntegrand hX ε
  rw [variance_of_integral_eq_zero hXm h0, ← integral_lindebergIntegrand hXm]
  have hcont : Continuous fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I) := by fun_prop
  have hcf : charFun (P.map X) t = ∫ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hXm (by fun_prop)]
    push_cast
    rfl
  have hexp : Integrable (fun ω => Complex.exp ((t * X ω : ℝ) * Complex.I)) P :=
    (integrable_const (1 : ℝ)).mono' (hcont.comp_aestronglyMeasurable hX.aestronglyMeasurable)
      (ae_of_all _ fun ω => (Complex.norm_exp_ofReal_mul_I _).le)
  have e : ∀ ω, (1 + ((t * X ω : ℝ) : ℂ) * Complex.I - ((t * X ω : ℝ) : ℂ) ^ 2 / 2) =
      ((1 - t ^ 2 / 2 * X ω ^ 2 : ℝ) : ℂ) + ((t * X ω : ℝ) : ℂ) * Complex.I := by
    intro ω
    push_cast
    ring
  have hpi1 : Integrable (fun ω => ((1 - t ^ 2 / 2 * X ω ^ 2 : ℝ) : ℂ)) P :=
    ((integrable_const 1).sub (hX2.const_mul _)).ofReal
  have hpi2 : Integrable (fun ω => ((t * X ω : ℝ) : ℂ) * Complex.I) P :=
    (hX1.const_mul t).ofReal.mul_const _
  have hpoly : ∫ ω, (1 + ((t * X ω : ℝ) : ℂ) * Complex.I - ((t * X ω : ℝ) : ℂ) ^ 2 / 2) ∂P =
      ((1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 : ℝ) : ℂ) := by
    simp_rw [e]
    rw [integral_add hpi1 hpi2, integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal, integral_sub (integrable_const 1) (hX2.const_mul _),
      integral_const_mul, integral_const_mul, h0, integral_const, probReal_univ, one_smul]
    push_cast
    ring
  have hpoly_int : Integrable
      (fun ω => (1 + ((t * X ω : ℝ) : ℂ) * Complex.I - ((t * X ω : ℝ) : ℂ) ^ 2 / 2)) P := by
    simp_rw [e]
    exact hpi1.add hpi2
  rw [hcf, ← hpoly, ← integral_sub hexp hpoly_int]
  calc _ ≤ ∫ ω, (|t| ^ 3 * ε * X ω ^ 2 +
        4 * t ^ 2 * {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) (X ω)) ∂P :=
        norm_integral_le_of_norm_le ((hX2.const_mul _).add (hind.const_mul _))
          (ae_of_all _ fun ω => norm_cexp_mul_I_sub_le_lindeberg hε htε (X ω))
    _ = _ := by
      rw [integral_add (hX2.const_mul _) (hind.const_mul _), integral_const_mul,
        integral_const_mul]

/-- **The characteristic-function estimate for one row** (behind Giles 2015, §2.1, p. 8: "the
multilevel correction `Y_ℓ` on each level is asymptotically Normally-distributed, and therefore so
is `Y`").  Let `X_j`, `j ∈ s`, be independent, centred and square integrable with variances
summing to `1`, and let `Λ(ε) = ∑_j E[X_j²; |X_j| > ε]`.  For `ε ≥ 0` with `|t| ε ≤ 1`,
`|E e^{it ∑_j X_j} − e^{−t²/2}| ≤ |t|³ ε + t⁴ ε²/4 + (4t² + t⁴/4) Λ(ε)`. -/
lemma norm_charFun_sum_sub_le_lindeberg {ι : Type*} {s : Finset ι} {X : ι → Ω → ℝ}
    (hind : iIndepFun (s.restrict X) P) (hX : ∀ j ∈ s, MemLp (X j) 2 P)
    (h0 : ∀ j ∈ s, P[X j] = 0) (h1 : ∑ j ∈ s, Var[X j; P] = 1) {ε t : ℝ} (hε : 0 ≤ ε)
    (htε : |t| * ε ≤ 1) :
    ‖charFun (P.map fun ω => ∑ j ∈ s, X j ω) t - Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ)‖ ≤
      |t| ^ 3 * ε + t ^ 4 * ε ^ 2 / 4 +
        (4 * t ^ 2 + t ^ 4 / 4) * ∑ j ∈ s, ∫ ω in {ω | ε < |X j ω|}, X j ω ^ 2 ∂P := by
  set Λ := ∑ j ∈ s, ∫ ω in {ω | ε < |X j ω|}, X j ω ^ 2 ∂P with hΛ
  have hXm : ∀ j ∈ s, AEMeasurable (X j) P := fun j hj =>
    (hX j hj).aestronglyMeasurable.aemeasurable
  rw [hind.charFun_map_fun_finsetSum_eq_prod hXm, Finset.prod_apply]
  have hexp : Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ) =
      ∏ j ∈ s, Complex.exp ((-(t ^ 2 * Var[X j; P] / 2) : ℝ) : ℂ) := by
    rw [← Complex.exp_sum, ← Complex.ofReal_sum, Finset.sum_neg_distrib, ← Finset.sum_div,
      ← Finset.mul_sum, h1, mul_one]
  rw [hexp]
  have hv : ∀ j ∈ s, 0 ≤ Var[X j; P] := fun j _ => variance_nonneg _ _
  have hΛj : ∀ j ∈ s, ∫ ω in {ω | ε < |X j ω|}, X j ω ^ 2 ∂P ≤ Λ := fun j hj =>
    Finset.single_le_sum (f := fun j => ∫ ω in {ω | ε < |X j ω|}, X j ω ^ 2 ∂P)
      (fun i _ => setIntegral_lindeberg_nonneg _ _) hj
  have hvle : ∀ j ∈ s, Var[X j; P] ≤ ε ^ 2 + Λ := fun j hj =>
    (variance_le_sq_add_lindeberg (hX j hj) (h0 j hj) ε).trans (by linarith [hΛj j hj])
  have hsq : ∑ j ∈ s, Var[X j; P] ^ 2 ≤ ε ^ 2 + Λ := by
    calc ∑ j ∈ s, Var[X j; P] ^ 2 ≤ ∑ j ∈ s, Var[X j; P] * (ε ^ 2 + Λ) :=
          Finset.sum_le_sum fun j hj => by
            rw [sq]
            exact mul_le_mul_of_nonneg_left (hvle j hj) (hv j hj)
      _ = ε ^ 2 + Λ := by rw [← Finset.sum_mul, h1, one_mul]
  calc _ ≤ ∑ j ∈ s, ‖charFun (P.map (X j)) t -
        Complex.exp ((-(t ^ 2 * Var[X j; P] / 2) : ℝ) : ℂ)‖ := by
        refine norm_prod_sub_prod_le_sum s (fun j hj => ?_) (fun j hj => ?_)
        · have := Measure.isProbabilityMeasure_map (hXm j hj)
          exact norm_charFun_le_one t
        · rw [Complex.norm_exp_ofReal, Real.exp_le_one_iff, neg_nonpos]
          have := hv j hj
          positivity
    _ ≤ ∑ j ∈ s, ((|t| ^ 3 * ε * Var[X j; P] +
          4 * t ^ 2 * ∫ ω in {ω | ε < |X j ω|}, X j ω ^ 2 ∂P) +
          (t ^ 2 * Var[X j; P] / 2) ^ 2) := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine (norm_sub_le_norm_sub_add_norm_sub _
          (((1 - t ^ 2 * Var[X j; P] / 2 : ℝ) : ℂ)) _).trans (add_le_add
            (norm_charFun_sub_le_lindeberg (hX j hj) (h0 j hj) hε htε) ?_)
        rw [← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_sub_comm]
        exact abs_exp_neg_sub_le_sq (by have := hv j hj; positivity)
    _ = |t| ^ 3 * ε * ∑ j ∈ s, Var[X j; P] + 4 * t ^ 2 * Λ +
          t ^ 4 / 4 * ∑ j ∈ s, Var[X j; P] ^ 2 := by
        rw [hΛ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ _ := by
        rw [h1]
        have ht4 : 0 ≤ t ^ 4 / 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hsq ht4]

end Row

/-! ### The Lindeberg and Lyapunov central limit theorems for triangular arrays -/

section Lindeberg

variable {ι Ω' : Type*} {Ω : ℕ → Type*} {mΩ : ∀ k, MeasurableSpace (Ω k)}
  {mΩ' : MeasurableSpace Ω'} {P : (k : ℕ) → Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
  {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **The Lindeberg central limit theorem for triangular arrays** (the central limit theorem used
in Giles 2015, §2.1, p. 8: "Instead of bounding the Mean Square Error, they prefer to use the
Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence.").  For every row `k` let `X_{k,j}`, `j ∈ s_k` (a finite set), be
independent real random variables on a probability space `(Ω_k, P_k)`, square integrable and
centred, with variances summing to `1`, and assume Lindeberg's condition: for every `ε > 0`,
`∑_{j ∈ s_k} E_k[X_{k,j}²; |X_{k,j}| > ε] → 0` as `k → ∞`.  Then `∑_{j ∈ s_k} X_{k,j} → N(0, 1)`
in distribution: the row sums converge in distribution to every random variable `Z` with law
`N(0, 1)`, on any probability space.  Mathlib only has the i.i.d. case
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`); the rows here may have different
lengths, laws and probability spaces.  The rows are indexed by `ℕ` because Mathlib states Lévy's
continuity theorem (`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`) for
sequences.  Proof: `norm_charFun_sum_sub_le_lindeberg` and Lévy's continuity theorem. -/
theorem tendstoInDistribution_lindeberg {s : ℕ → Finset ι} {X : (k : ℕ) → ι → Ω k → ℝ}
    (hind : ∀ k, iIndepFun ((s k).restrict (X k)) (P k))
    (hX : ∀ k, ∀ j ∈ s k, MemLp (X k j) 2 (P k)) (h0 : ∀ k, ∀ j ∈ s k, (P k)[X k j] = 0)
    (h1 : ∀ k, ∑ j ∈ s k, Var[X k j; P k] = 1)
    (hlin : ∀ ε > 0, Tendsto (fun k => ∑ j ∈ s k,
      ∫ ω in {ω | ε < |X k j ω|}, X k j ω ^ 2 ∂(P k)) atTop (𝓝 0))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω => ∑ j ∈ s k, X k j ω) atTop Z P P' := by
  refine ⟨fun k => Finset.aemeasurable_fun_sum _ fun j hj =>
      (hX k j hj).aestronglyMeasurable.aemeasurable,
    hZ.aemeasurable, ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_⟩
  simp only [ProbabilityMeasure.coe_mk]
  have hg := charFun_gaussianReal_zero (v := 1) zero_le_one t
  rw [Real.toNNReal_one, one_mul] at hg
  rw [hZ.map_eq, hg, Metric.tendsto_atTop]
  intro δ hδ
  -- choose the truncation level `ε`, then the row index
  set ε := min (1 / (|t| + 1)) (δ / (2 * (|t| ^ 3 + t ^ 4 + 1)))
  have hta : 0 < |t| + 1 := by positivity
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ 1 / (|t| + 1) := min_le_left _ _
  have hε2 : ε ≤ δ / (2 * (|t| ^ 3 + t ^ 4 + 1)) := min_le_right _ _
  have hεle1 : ε ≤ 1 := hε1.trans (by rw [div_le_one hta]; linarith [abs_nonneg t])
  have htε : |t| * ε ≤ 1 := by
    rw [le_div_iff₀ hta] at hε1
    nlinarith [abs_nonneg t]
  have hεc : |t| ^ 3 * ε + t ^ 4 * ε ^ 2 / 4 < δ / 2 := by
    rw [le_div_iff₀ (by positivity)] at hε2
    have h4 : 0 ≤ t ^ 4 := by positivity
    have hεε : ε ^ 2 ≤ ε := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hεε h4]
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 (hlin ε hε) (δ / (2 * (4 * t ^ 2 + t ^ 4 / 4 + 1)))
    (by positivity)
  refine ⟨K, fun k hk => ?_⟩
  have hb := norm_charFun_sum_sub_le_lindeberg (hind k) (hX k) (h0 k) (h1 k) hε.le htε
  have hΛ := hK k hk
  rw [Real.dist_eq, sub_zero] at hΛ
  set Λ := ∑ j ∈ s k, ∫ ω in {ω | ε < |X k j ω|}, X k j ω ^ 2 ∂(P k)
  have hΛ' : (4 * t ^ 2 + t ^ 4 / 4) * Λ < δ / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hΛ
    have h1' : (4 * t ^ 2 + t ^ 4 / 4) * Λ ≤ (4 * t ^ 2 + t ^ 4 / 4 + 1) * |Λ| := by
      have : Λ ≤ |Λ| := le_abs_self Λ
      have : 0 ≤ 4 * t ^ 2 + t ^ 4 / 4 := by positivity
      nlinarith [abs_nonneg Λ]
    nlinarith
  rw [dist_eq_norm]
  linarith

omit [∀ k, IsProbabilityMeasure (P k)] in
/-- **Lyapunov's condition implies Lindeberg's** (for the central limit theorem of Giles 2015,
§2.1, p. 8: "they prefer to use the Central Limit Theorem to construct a confidence interval which
bounds `E[P]` with a user-prescribed confidence").  Let `X_{k,j}`, `j ∈ s_k`, be a.e. measurable
on `(Ω_k, P_k)`.  If `δ ≥ 0`, every `|X_{k,j}|^{2+δ}` is integrable and
`∑_{j ∈ s_k} E_k|X_{k,j}|^{2+δ} → 0`, then for every `ε > 0`,
`∑_{j ∈ s_k} E_k[X_{k,j}²; |X_{k,j}| > ε] → 0`, because
`E[X²; |X| > ε] ≤ ε^{−δ} E|X|^{2+δ}` (`setIntegral_lindeberg_le_lyapunov`). -/
theorem tendsto_lindeberg_of_lyapunov {s : ℕ → Finset ι} {X : (k : ℕ) → ι → Ω k → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hXm : ∀ k, ∀ j ∈ s k, AEMeasurable (X k j) (P k))
    (hint : ∀ k, ∀ j ∈ s k, Integrable (fun ω => |X k j ω| ^ (2 + δ)) (P k))
    (hlyap : Tendsto (fun k => ∑ j ∈ s k, ∫ ω, |X k j ω| ^ (2 + δ) ∂(P k)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => ∑ j ∈ s k, ∫ ω in {ω | ε < |X k j ω|}, X k j ω ^ 2 ∂(P k)) atTop
      (𝓝 0) := by
  have hlim : Tendsto (fun k => ε ^ (-δ) * ∑ j ∈ s k, ∫ ω, |X k j ω| ^ (2 + δ) ∂(P k)) atTop
      (𝓝 0) := by
    simpa using hlyap.const_mul (ε ^ (-δ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k => Finset.sum_nonneg fun j _ => setIntegral_lindeberg_nonneg _ _) (fun k => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj =>
    setIntegral_lindeberg_le_lyapunov (hXm k j hj) hε hδ (hint k j hj)

/-- **The Lyapunov central limit theorem for triangular arrays** (the central limit theorem used
in Giles 2015, §2.1, p. 8: "they prefer to use the Central Limit Theorem to construct a
confidence interval which bounds `E[P]` with a user-prescribed confidence").  For every row `k`
let `X_{k,j}`, `j ∈ s_k`, be independent, square integrable and centred on a probability space
`(Ω_k, P_k)`, with variances summing to `1`.  If for some `δ ≥ 0` every `|X_{k,j}|^{2+δ}` is
integrable and `∑_{j ∈ s_k} E_k|X_{k,j}|^{2+δ} → 0`, then `∑_{j ∈ s_k} X_{k,j} → N(0, 1)` in
distribution.  (For `δ = 0` the hypotheses contradict each other, as `∑_j E_k[X_{k,j}²] = 1`.) -/
theorem tendstoInDistribution_lyapunov {s : ℕ → Finset ι} {X : (k : ℕ) → ι → Ω k → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hind : ∀ k, iIndepFun ((s k).restrict (X k)) (P k))
    (hX : ∀ k, ∀ j ∈ s k, MemLp (X k j) 2 (P k)) (h0 : ∀ k, ∀ j ∈ s k, (P k)[X k j] = 0)
    (h1 : ∀ k, ∑ j ∈ s k, Var[X k j; P k] = 1)
    (hint : ∀ k, ∀ j ∈ s k, Integrable (fun ω => |X k j ω| ^ (2 + δ)) (P k))
    (hlyap : Tendsto (fun k => ∑ j ∈ s k, ∫ ω, |X k j ω| ^ (2 + δ) ∂(P k)) atTop (𝓝 0))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω => ∑ j ∈ s k, X k j ω) atTop Z P P' :=
  tendstoInDistribution_lindeberg hind hX h0 h1 (fun _ hε => tendsto_lindeberg_of_lyapunov hδ
    (fun k j hj => (hX k j hj).aestronglyMeasurable.aemeasurable) hint hlyap hε) hZ

end Lindeberg

/-! ### Confidence intervals from asymptotic normality -/

section Confidence

/-- The standard normal law gives `[−z, z]` the mass `Φ(z) − Φ(−z) = 2Φ(z) − 1` for `z ≥ 0`, where
`Φ = cdf (gaussianReal 0 1)` (symmetry `gaussianReal_map_neg`; no atoms). -/
lemma measureReal_gaussianReal_Icc_neg {z : ℝ} (hz : 0 ≤ z) :
    (gaussianReal 0 1).real (Set.Icc (-z) z) = 2 * cdf (gaussianReal 0 1) z - 1 := by
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  have hneg : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  -- `Φ(−z) = 1 − Φ(z)` by symmetry
  have hsym : (gaussianReal 0 1).real (Set.Iic (-z)) = 1 - cdf (gaussianReal 0 1) z := by
    conv_lhs => rw [← hneg]
    rw [measureReal_def, Measure.map_apply measurable_neg measurableSet_Iic, ← measureReal_def,
      cdf_eq_real, ← measureReal_congr (Iio_ae_eq_Iic (μ := gaussianReal 0 1) (a := z)),
      ← probReal_compl_eq_one_sub measurableSet_Iio]
    congr 1
    ext x
    simp
  have hsub : Set.Iic (-z) ⊆ Set.Iic z := Set.Iic_subset_Iic.2 (by linarith)
  have hset : Set.Ioc (-z) z = Set.Iic z \ Set.Iic (-z) := by
    ext x
    simp [and_comm]
  rw [← measureReal_congr (Ioc_ae_eq_Icc (μ := gaussianReal 0 1) (a := -z) (b := z)), hset,
    measureReal_sdiff hsub measurableSet_Iic, hsym, ← cdf_eq_real]
  ring

variable {ι Ω' : Type*} {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {mΩ' : MeasurableSpace Ω'} {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
  {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Asymptotic normality gives asymptotic confidence intervals** (Giles 2015, §2.1, p. 8: "they
prefer to use the Central Limit Theorem to construct a confidence interval which bounds `E[P]`
with a user-prescribed confidence").  If `S_i → N(0, 1)` in distribution along a filter `l`,
where `S_i` lives on a probability space `(Ω_i, P_i)`, then for every `z ≥ 0`,
`P_i(|S_i| ≤ z) → 2Φ(z) − 1`, where `Φ = cdf (gaussianReal 0 1)` is the standard normal
distribution function.  The boundary `{−z, z}` of `[−z, z]` is a null set for `N(0, 1)`, so this
is the portmanteau theorem
(`MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`). -/
theorem tendsto_measureReal_abs_le_of_tendstoInDistribution {l : Filter ι}
    {S : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ} (hS : TendstoInDistribution S l Z P P')
    (hZ : HasLaw Z (gaussianReal 0 1) P') {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun i => (P i).real {x | |S i x| ≤ z}) l
      (𝓝 (2 * cdf (gaussianReal 0 1) z - 1)) := by
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  have hfr : (P'.map Z) (frontier (Set.Icc (-z) z)) = 0 := by
    rw [hZ.map_eq, frontier_Icc (by linarith)]
    exact (Set.toFinite _).measure_zero _
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hS.tendsto hfr
  simp only [ProbabilityMeasure.coe_mk, hZ.map_eq] at h
  have h2 := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  rw [← measureReal_gaussianReal_Icc_neg hz]
  refine h2.congr fun k => ?_
  rw [Function.comp_apply, ← measureReal_def, measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable (hS.forall_aemeasurable k) measurableSet_Icc]
  congr 2
  ext x
  simp [abs_le]

end Confidence

/-! ### Multilevel Monte Carlo with a growing number of levels (Giles 2015, §2.1) -/

section Estimator

variable {Ω₀ Ω Ω' : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω₀} {μ : Measure Ω} {P' : Measure Ω'} {ω : ℕ × ℕ → Ω → Ω₀} {Pl : ℕ → Ω₀ → ℝ}

omit [MeasurableSpace Ω₀] [MeasurableSpace Ω] in
/-- The normalised error of the estimator (2.2) is a sum over its samples: with `N_ℓ ≥ 1` samples
on every level `ℓ ≤ L` and any `m_ℓ`, `σ`,
`(Y − ∑_{ℓ ≤ L} m_ℓ)/σ = ∑_{ℓ ≤ L} ∑_{n < N_ℓ} (N_ℓ σ)⁻¹ (ΔP_ℓ(ω^{(ℓ,n)}) − m_ℓ)`. -/
lemma mlmcEstimator_sub_div_eq_sum (Pl : ℕ → Ω₀ → ℝ) (ω : ℕ × ℕ → Ω → Ω₀) (L : ℕ)
    {N : ℕ → ℕ} (hN : ∀ ℓ ≤ L, 0 < N ℓ) (m : ℕ → ℝ) (σ : ℝ) (x : Ω) :
    (mlmcEstimator Pl ω L N x - ∑ ℓ ∈ range (L + 1), m ℓ) / σ =
      ∑ q ∈ (range (L + 1)).sigma (fun ℓ => range (N ℓ)),
        ((N q.1 : ℝ) * σ)⁻¹ * (levelDiff Pl q.1 (ω (q.1, q.2) x) - m q.1) := by
  rw [Finset.sum_sigma, mlmcEstimator, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hNℓ : (N ℓ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (hN ℓ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ))).ne'
  dsimp only
  rw [levelEstimator, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, card_range,
    nsmul_eq_mul]
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp
  · field_simp

/-- The corrections up to a finest level `L` are square integrable when `P_0, …, P_L` are (Giles
2015, §1.3, p. 4; `memLp_levelDiff` assumes square integrability on every level). -/
lemma memLp_levelDiff_of_le {L : ℕ} (hPl : ∀ ℓ ≤ L, MemLp (Pl ℓ) 2 ν) :
    ∀ ℓ ≤ L, MemLp (levelDiff Pl ℓ) 2 ν
  | 0, _ => hPl 0 (Nat.zero_le L)
  | ℓ + 1, hℓ => (hPl (ℓ + 1) hℓ).sub (hPl ℓ (by omega))

/-- The normalised error `(Y − c)/s` of the estimator (2.2) is a.e. measurable when
`P_0, …, P_L` are square integrable (Giles 2015, §2.1, p. 8). -/
lemma aemeasurable_mlmcEstimator_sub_div (hω : ∀ p, MeasurePreserving (ω p) μ ν) {L : ℕ}
    (hPl : ∀ ℓ ≤ L, MemLp (Pl ℓ) 2 ν) (N : ℕ → ℕ) (c s : ℝ) :
    AEMeasurable (fun x => (mlmcEstimator Pl ω L N x - c) / s) μ := by
  have hD : ∀ ℓ ∈ range (L + 1), AEMeasurable (levelDiff Pl ℓ) ν := fun ℓ hℓ =>
    (memLp_levelDiff_of_le hPl ℓ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ))).1.aemeasurable
  simp only [mlmcEstimator]
  exact ((Finset.aemeasurable_fun_sum _ fun ℓ hℓ =>
    aemeasurable_levelEstimator hω (hD ℓ hℓ) _).sub_const _).div_const _

/-- Convergence in distribution only depends on the tail of a sequence: if every `X_k` is a.e.
measurable and `X_{k+k₀} → Z` in distribution, then `X_k → Z` (so the hypotheses of the theorems
below are needed only for large `k`; Giles 2015, §2.1, p. 8). -/
lemma tendstoInDistribution_of_comp_add [IsProbabilityMeasure μ] [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ} (k₀ : ℕ) (hX : ∀ k, AEMeasurable (X k) μ)
    (h : TendstoInDistribution (fun k => X (k + k₀)) atTop Z (fun _ => μ) P') :
    TendstoInDistribution X atTop Z (fun _ => μ) P' :=
  ⟨hX, h.aemeasurable_limit, (tendsto_add_atTop_iff_nat (f := fun k =>
    (⟨μ.map (X k), Measure.isProbabilityMeasure_map (hX k)⟩ : ProbabilityMeasure ℝ)) k₀).1
    h.tendsto⟩

/-- The multilevel central limit theorem with `N_{k,ℓ} ≥ 1` and `σ_k > 0` for every row `k` (the
core of `tendstoInDistribution_mlmcEstimator_lyapunov`, Giles 2015, §2.1, p. 8). -/
lemma tendstoInDistribution_mlmcEstimator_lyapunov_of_forall [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P'] (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {L : ℕ → ℕ} (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν) {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ)) ν)
    {N : ℕ → ℕ → ℕ} (hN : ∀ k, ∀ ℓ ≤ L k, 0 < N k ℓ)
    (hσ : ∀ k, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    (hlyap : Tendsto (fun k => (∑ ℓ ∈ range (L k + 1),
        (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
          (N k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (2 + δ)) atTop (𝓝 0))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k x => (mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ))
      atTop Z (fun _ => μ) P' := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℝ, ∀ ℓ, ∫ y, levelDiff Pl ℓ y ∂ν = m ℓ := ⟨_, fun _ => rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → ℝ, ∀ k,
      √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) = σ k := ⟨_, fun _ => rfl⟩
  have hσpos : ∀ k, 0 < σ k := fun k => hσdef k ▸ Real.sqrt_pos.2 (hσ k)
  have hσsq : ∀ k, σ k ^ 2 = ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ :=
    fun k => by rw [← hσdef k, Real.sq_sqrt (hσ k).le]
  simp only [hm] at hM hlyap
  simp only [hσdef] at hlyap ⊢
  have hD : ∀ k, ∀ ℓ ≤ L k, MemLp (levelDiff Pl ℓ) 2 ν := fun k => memLp_levelDiff_of_le (hPl k)
  -- the triangular array of normalised samples `g_{k,ℓ}(ω^{(ℓ,n)})`
  set g : ℕ → ℕ → Ω₀ → ℝ := fun k ℓ y => ((N k ℓ : ℝ) * σ k)⁻¹ * (levelDiff Pl ℓ y - m ℓ)
    with hg
  have hgL2 : ∀ k, ∀ ℓ ≤ L k, MemLp (g k ℓ) 2 ν := fun k ℓ hℓ =>
    ((hD k ℓ hℓ).sub (memLp_const _)).const_mul _
  have hgm : ∀ k, ∀ ℓ ≤ L k, AEMeasurable (g k ℓ) ν := fun k ℓ hℓ =>
    (hgL2 k ℓ hℓ).aestronglyMeasurable.aemeasurable
  have hg0 : ∀ k, ∀ ℓ ≤ L k, ∫ y, g k ℓ y ∂ν = 0 := by
    intro k ℓ hℓ
    simp only [hg]
    rw [integral_const_mul, integral_sub ((hD k ℓ hℓ).integrable one_le_two)
      (integrable_const _), integral_const, hm]
    simp
  have hgvar : ∀ k, ∀ ℓ ≤ L k, Var[g k ℓ; ν] =
      ((N k ℓ : ℝ) * σ k)⁻¹ ^ 2 * variance (levelDiff Pl ℓ) ν := by
    intro k ℓ hℓ
    simp only [hg]
    rw [variance_const_mul, variance_sub_const (hD k ℓ hℓ).aestronglyMeasurable]
  have hgabs : ∀ k ℓ, (fun y => |g k ℓ y| ^ (2 + δ)) =
      fun y => |((N k ℓ : ℝ) * σ k)⁻¹| ^ (2 + δ) * |levelDiff Pl ℓ y - m ℓ| ^ (2 + δ) := by
    intro k ℓ
    funext y
    simp only [hg]
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hgint : ∀ k, ∀ ℓ ≤ L k, Integrable (fun y => |g k ℓ y| ^ (2 + δ)) ν := fun k ℓ hℓ => by
    rw [hgabs]
    exact (hM k ℓ hℓ).const_mul _
  have hfun : (fun k x => (mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν) / σ k) =
      fun k x => ∑ q ∈ (range (L k + 1)).sigma (fun ℓ => range (N k ℓ)),
        g k q.1 (ω (q.1, q.2) x) := by
    funext k x
    rw [← sum_integral_levelDiff_of_le fun ℓ hℓ => (hPl k ℓ hℓ).integrable one_le_two]
    simp only [hm]
    exact mlmcEstimator_sub_div_eq_sum Pl ω (L k) (hN k) m (σ k) x
  rw [hfun]
  have hle : ∀ k, ∀ q ∈ (range (L k + 1)).sigma (fun ℓ => range (N k ℓ)), q.1 ≤ L k :=
    fun k q hq => Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_sigma.1 hq).1)
  refine tendstoInDistribution_lyapunov (Ω := fun _ => Ω) (P := fun _ => μ)
    (s := fun k => (range (L k + 1)).sigma fun ℓ => range (N k ℓ))
    (X := fun k q x => g k q.1 (ω (q.1, q.2) x)) hδ (fun k => ?_)
    (fun k q hq => (hgL2 k q.1 (hle k q hq)).comp_measurePreserving (hω (q.1, q.2)))
    (fun k q hq => ?_) (fun k => ?_)
    (fun k q hq => (hω (q.1, q.2)).integrable_comp_of_integrable (hgint k q.1 (hle k q hq)))
    ?_ hZ
  · -- independence: distinct samples use distinct inputs
    refine iIndepFun_comp_inputs hω hind
      (e := fun q : ((range (L k + 1)).sigma fun ℓ => range (N k ℓ)) => (q.1.1, q.1.2)) ?_
      (g := fun q => g k q.1.1) fun q => hgm k q.1.1 (hle k q.1 q.2)
    rintro ⟨⟨a, b⟩, _⟩ ⟨⟨c, d⟩, _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · -- centring
    rw [integral_comp_of_measurePreserving (hω _)
      (hgL2 k q.1 (hle k q hq)).aestronglyMeasurable, hg0 k q.1 (hle k q hq)]
  · -- the variances sum to one
    rw [Finset.sum_congr rfl fun q hq =>
        (hω (q.1, q.2)).variance_fun_comp (hgm k q.1 (hle k q hq)), Finset.sum_sigma,
      ← div_self (pow_pos (hσpos k) 2).ne', hσsq k, Finset.sum_div]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓL : ℓ ≤ L k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    have hNℓ : (N k ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hN k ℓ hℓL).ne'
    have hσk : σ k ≠ 0 := (hσpos k).ne'
    simp only [hgvar k ℓ hℓL, Finset.sum_const, card_range, nsmul_eq_mul]
    rw [← hσsq k]
    field_simp
  · -- the Lyapunov sum of the array is the Lyapunov ratio
    refine hlyap.congr fun k => ?_
    rw [Finset.sum_congr rfl fun (q : Σ _ : ℕ, ℕ) hq =>
      integral_comp_of_measurePreserving (hω (q.1, q.2))
      (hgint k q.1 (hle k q hq)).aestronglyMeasurable, Finset.sum_sigma, Finset.sum_div]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hNpos : (0 : ℝ) < N k ℓ :=
      Nat.cast_pos.2 (hN k ℓ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)))
    have hσk := hσpos k
    simp only [hgabs, integral_const_mul, Finset.sum_const, card_range, nsmul_eq_mul]
    rw [abs_inv, abs_of_pos (mul_pos hNpos hσk), Real.inv_rpow (mul_pos hNpos hσk).le,
      Real.mul_rpow hNpos.le hσk.le, show (-1 - δ : ℝ) = 1 - (2 + δ) by ring,
      Real.rpow_sub hNpos, Real.rpow_one]
    field_simp

/-- **The multilevel estimator is asymptotically normal as the number of levels grows** (Giles
2015, §2.1, p. 8: "Collier, Haji-Ali, Nobile, von Schwerin and Tempone (2014) have developed a
modified version of the Theorem. Instead of bounding the Mean Square Error, they prefer to use the
Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence. This exploits the fact that the multilevel correction `Y_ℓ` on each
level is asymptotically Normally-distributed, and therefore so is `Y`.").  Let the inputs
`ω^{(ℓ,n)}` be independent with law `ν`.  For `k ∈ ℕ` take a finest level `L_k` and `N_{k,ℓ}`
samples on level `ℓ ≤ L_k`; let `P_0, …, P_{L_k}` be in `L²(ν)` and, for some `δ ≥ 0`, let
`M_ℓ = E|ΔP_ℓ − E[ΔP_ℓ]|^{2+δ}` be finite for `ℓ ≤ L_k`.  Assume that for all large `k`,
`N_{k,ℓ} ≥ 1` for `ℓ ≤ L_k` and `σ_k² = ∑_{ℓ ≤ L_k} V_ℓ/N_{k,ℓ} > 0`.  If Lyapunov's condition
`∑_{ℓ ≤ L_k} M_ℓ N_{k,ℓ}^{−1−δ} / σ_k^{2+δ} → 0` holds, then
`(Y_k − E[P_{L_k}]) / σ_k → N(0, 1)` in distribution, where `Y_k` is the estimator (2.2) with
these levels and sample sizes: the sequence converges in distribution to every random variable
`Z` with law `N(0, 1)`.  No condition on the growth of `L_k` is needed.  The samples
`(ΔP_ℓ(ω^{(ℓ,n)}) − E[ΔP_ℓ]) / (N_{k,ℓ} σ_k)` form a triangular array whose Lyapunov sum is
exactly this ratio (`tendstoInDistribution_lyapunov`).  (For `δ = 0` the ratio is `1` whenever
`σ_k > 0`, so only `δ > 0` is of use.)

The paper only cites Collier et al.; the hypotheses (finite `(2+δ)`-th moments, Lyapunov's
condition) are this formalisation's.  Some such hypothesis is needed: when `L_k` grows, the
asymptotic normality of every `Y_ℓ` does not imply that of `Y` (counterexample in the module
docstring).  `σ_k > 0` replaces the stronger `V_ℓ > 0`; finitely many rows do not matter, so
`N_{k,ℓ} ≥ 1` and `σ_k > 0` are assumed only for large `k`.  The centring is
`E[P_{L_k}] = E[Y_k]`; for the centring `E[P]` see `tendstoInDistribution_mlmcEstimator_of_bias`.
For a fixed `L` and `N_ℓ = m_ℓ n` see `tendstoInDistribution_mlmcEstimator`. -/
theorem tendstoInDistribution_mlmcEstimator_lyapunov [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P'] (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {L : ℕ → ℕ} (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν) {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ)) ν)
    {N : ℕ → ℕ → ℕ} (hN : ∀ᶠ k in atTop, ∀ ℓ ≤ L k, 0 < N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    (hlyap : Tendsto (fun k => (∑ ℓ ∈ range (L k + 1),
        (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
          (N k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (2 + δ)) atTop (𝓝 0))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k x => (mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ))
      atTop Z (fun _ => μ) P' := by
  obtain ⟨k₀, hk₀⟩ := (hN.and hσ).exists_forall_of_atTop
  exact tendstoInDistribution_of_comp_add k₀
    (fun k => aemeasurable_mlmcEstimator_sub_div hω (hPl k) _ _ _)
    (tendstoInDistribution_mlmcEstimator_lyapunov_of_forall (L := fun k => L (k + k₀))
      (N := fun k => N (k + k₀)) hω hind (fun k => hPl (k + k₀)) hδ (fun k => hM (k + k₀))
      (fun k => (hk₀ (k + k₀) (Nat.le_add_left _ _)).1)
      (fun k => (hk₀ (k + k₀) (Nat.le_add_left _ _)).2)
      (hlyap.comp (tendsto_add_atTop_nat k₀)) hZ)

/-- Lyapunov's condition for the multilevel estimator follows from a bound on the standardised
moments and growing sample sizes (Giles 2015, §2.1, p. 8): if `δ > 0`, `M_ℓ ≤ K V_ℓ^{1+δ/2}` for
`ℓ ≤ L_k`, `σ_k² > 0` for large `k` and `min_{ℓ ≤ L_k} N_{k,ℓ} → ∞`, then
`∑_{ℓ ≤ L_k} M_ℓ N_{k,ℓ}^{−1−δ} / σ_k^{2+δ} ≤ max(K, 0) (min_ℓ N_{k,ℓ})^{−δ/2} → 0`, using
`∑_ℓ (V_ℓ/N_{k,ℓ})^{1+δ/2} ≤ σ_k^{2+δ}` (`sum_rpow_le_rpow_sum_of_one_le`). -/
lemma tendsto_mlmcLyapunovRatio_of_moment_le {δ : ℝ} (hδ : 0 < δ) {K : ℝ} {L : ℕ → ℕ}
    (hK : ∀ k, ∀ ℓ ≤ L k, ∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν ≤
      K * variance (levelDiff Pl ℓ) ν ^ (1 + δ / 2))
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) :
    Tendsto (fun k => (∑ ℓ ∈ range (L k + 1),
        (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
          (N k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (2 + δ)) atTop
      (𝓝 0) := by
  set K' := max K 0
  -- for `N_ℓ ≥ n₀ ≥ 1` on all levels, the Lyapunov ratio is at most `K' n₀^{−δ/2}`
  have hbound : ∀ (k n₀ : ℕ), 0 < n₀ → (∀ ℓ ≤ L k, n₀ ≤ N k ℓ) →
      0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ →
      (∑ ℓ ∈ range (L k + 1),
        (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
          (N k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (2 + δ) ≤
        K' * (n₀ : ℝ) ^ (-(δ / 2)) := by
    intro k n₀ hn₀ hk hS
    set S := ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ
    have hσp : √S ^ (2 + δ) = S ^ (1 + δ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hS.le]
      ring_nf
    have hSp : 0 < S ^ (1 + δ / 2) := Real.rpow_pos_of_pos hS _
    rw [hσp, div_le_iff₀ hSp]
    calc ∑ ℓ ∈ range (L k + 1),
          (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
            (N k ℓ : ℝ) ^ (-1 - δ)
        ≤ ∑ ℓ ∈ range (L k + 1), K' * (n₀ : ℝ) ^ (-(δ / 2)) *
            (variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (1 + δ / 2) := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          have hℓL : ℓ ≤ L k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
          have hNpos : (0 : ℝ) < N k ℓ := Nat.cast_pos.2 (hn₀.trans_le (hk ℓ hℓL))
          have hn₀pos : (0 : ℝ) < n₀ := Nat.cast_pos.2 hn₀
          have hV := variance_nonneg (levelDiff Pl ℓ) ν
          have hMK : ∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν ≤
              K' * variance (levelDiff Pl ℓ) ν ^ (1 + δ / 2) :=
            (hK k ℓ hℓL).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
              (Real.rpow_nonneg hV _))
          have hNn : (N k ℓ : ℝ) ^ (-(δ / 2)) ≤ (n₀ : ℝ) ^ (-(δ / 2)) :=
            Real.rpow_le_rpow_of_nonpos hn₀pos (by exact_mod_cast hk ℓ hℓL) (by linarith)
          have hsplit : (N k ℓ : ℝ) ^ (-1 - δ) =
              ((N k ℓ : ℝ) ^ (1 + δ / 2))⁻¹ * (N k ℓ : ℝ) ^ (-(δ / 2)) := by
            rw [← Real.rpow_neg hNpos.le, ← Real.rpow_add hNpos]
            ring_nf
          rw [Real.div_rpow hV hNpos.le, hsplit]
          calc (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
                (((N k ℓ : ℝ) ^ (1 + δ / 2))⁻¹ * (N k ℓ : ℝ) ^ (-(δ / 2)))
              ≤ K' * variance (levelDiff Pl ℓ) ν ^ (1 + δ / 2) *
                (((N k ℓ : ℝ) ^ (1 + δ / 2))⁻¹ * (n₀ : ℝ) ^ (-(δ / 2))) := by
                gcongr
            _ = _ := by rw [div_eq_mul_inv]; ring
      _ = K' * (n₀ : ℝ) ^ (-(δ / 2)) *
            ∑ ℓ ∈ range (L k + 1), (variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (1 + δ / 2) := by
          rw [Finset.mul_sum]
      _ ≤ K' * (n₀ : ℝ) ^ (-(δ / 2)) * S ^ (1 + δ / 2) := by
          gcongr
          exact sum_rpow_le_rpow_sum_of_one_le _ (fun ℓ _ => div_nonneg (variance_nonneg _ _)
            (Nat.cast_nonneg _)) (by linarith)
  -- the ratio is nonnegative and eventually below `K' n₀^{−δ/2}` for every `n₀`
  rw [Metric.tendsto_atTop]
  intro η hη
  -- choose `n₀` with `K' n₀^{−δ/2} < η`
  have htend : Tendsto (fun n : ℕ => K' * (n : ℝ) ^ (-(δ / 2))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < δ / 2)).comp
      tendsto_natCast_atTop_atTop |>.const_mul K'
  obtain ⟨n₁, hn₁⟩ := Metric.tendsto_atTop.1 htend η hη
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 ((hNtop (n₁ + 1)).and hσ)
  refine ⟨K₀, fun k hk => ?_⟩
  have hb := hbound k (n₁ + 1) n₁.succ_pos (hK₀ k hk).1 (hK₀ k hk).2
  have hc := hn₁ (n₁ + 1) (Nat.le_succ _)
  rw [Real.dist_eq, sub_zero] at hc ⊢
  have hnn : 0 ≤ (∑ ℓ ∈ range (L k + 1),
        (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
          (N k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (2 + δ) :=
    div_nonneg (Finset.sum_nonneg fun ℓ _ => mul_nonneg
      (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  rw [abs_of_nonneg hnn]
  exact hb.trans_lt ((le_abs_self _).trans_lt hc)

/-- **Asymptotic normality of the multilevel estimator under a moment bound** (Giles 2015, §2.1,
p. 8: "This exploits the fact that the multilevel correction `Y_ℓ` on each level is asymptotically
Normally-distributed, and therefore so is `Y`.").  Let the inputs `ω^{(ℓ,n)}` be independent with
law `ν`, `δ > 0`, and for `k ∈ ℕ` let `P_0, …, P_{L_k}` be in `L²(ν)` and the centred moments of
the corrections satisfy `M_ℓ = E|ΔP_ℓ − E[ΔP_ℓ]|^{2+δ} < ∞` and `M_ℓ ≤ K V_ℓ^{1+δ/2}` for
`ℓ ≤ L_k` (for `δ = 2`: the kurtosis of every `ΔP_ℓ` used is at most `K`).  Use `N_{k,ℓ}` samples
on level `ℓ ≤ L_k` with `min_{ℓ ≤ L_k} N_{k,ℓ} → ∞` and `σ_k² = ∑_{ℓ ≤ L_k} V_ℓ/N_{k,ℓ} > 0` for
large `k`.  Then `(Y_k − E[P_{L_k}]) / σ_k → N(0, 1)` in distribution, however fast `L_k` grows:
Lyapunov's condition holds because `∑_ℓ M_ℓ N_{k,ℓ}^{−1−δ} ≤ K (min_ℓ N_{k,ℓ})^{−δ/2} σ_k^{2+δ}`
(`tendsto_mlmcLyapunovRatio_of_moment_le`).  The hypotheses are this formalisation's; the paper
only cites Collier et al.  The uniform bound `K` cannot be dropped: in the counterexample of the
module docstring `min_ℓ N_{k,ℓ} → ∞`, but the kurtosis of `ΔP_ℓ` is `2^ℓ` and the limit is `0`. -/
theorem tendstoInDistribution_mlmcEstimator_of_moment_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P'] (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {L : ℕ → ℕ} (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν) {δ : ℝ} (hδ : 0 < δ)
    (hM : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ)) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k,
      ∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν ≤
        K * variance (levelDiff Pl ℓ) ν ^ (1 + δ / 2))
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k x => (mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ))
      atTop Z (fun _ => μ) P' :=
  tendstoInDistribution_mlmcEstimator_lyapunov hω hind hPl hδ.le hM
    ((hNtop 1).mono fun _ hk ℓ hℓ => hk ℓ hℓ) hσ
    (tendsto_mlmcLyapunovRatio_of_moment_le hδ hK hNtop hσ) hZ

/-- **The asymptotic confidence interval of Collier et al.** (Giles 2015, §2.1, p. 8: "Instead of
bounding the Mean Square Error, they prefer to use the Central Limit Theorem to construct a
confidence interval which bounds `E[P]` with a user-prescribed confidence.").  Under the
hypotheses of `tendstoInDistribution_mlmcEstimator_lyapunov` (independent inputs of law `ν`;
for `ℓ ≤ L_k`, `P_ℓ ∈ L²(ν)` and finite `M_ℓ = E|ΔP_ℓ − E[ΔP_ℓ]|^{2+δ}`; for large `k`,
`N_{k,ℓ} ≥ 1` and `σ_k > 0`; Lyapunov's condition), for every `z ≥ 0`,
`P(|Y_k − E[P_{L_k}]| ≤ z σ_k) → 2Φ(z) − 1`, `Φ` the standard normal distribution function
(`cdf (gaussianReal 0 1)`): the interval `Y_k ± z σ_k` covers `E[P_{L_k}]` with asymptotic
confidence `2Φ(z) − 1`.  For `E[P]` itself see
`tendsto_measureReal_abs_mlmcEstimator_sub_le_of_bias` and
`eventually_lt_measureReal_abs_mlmcEstimator_sub_le_tol`.  Here `σ_k` is the exact standard
deviation of `Y_k`; replacing it by a consistent estimate (Slutsky's lemma), as Collier et al. do
in practice, is not formalised. -/
theorem tendsto_measureReal_abs_mlmcEstimator_sub_le [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {L : ℕ → ℕ} (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν) {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ)) ν)
    {N : ℕ → ℕ → ℕ} (hN : ∀ᶠ k in atTop, ∀ ℓ ≤ L k, 0 < N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    (hlyap : Tendsto (fun k => (∑ ℓ ∈ range (L k + 1),
        (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
          (N k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (2 + δ)) atTop (𝓝 0))
    {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun k => μ.real {x | |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν| ≤
        z * √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)}) atTop
      (𝓝 (2 * cdf (gaussianReal 0 1) z - 1)) := by
  have h := tendsto_measureReal_abs_le_of_tendstoInDistribution
    (tendstoInDistribution_mlmcEstimator_lyapunov (P' := gaussianReal 0 1) (Z := id) hω hind hPl
      hδ hM hN hσ hlyap HasLaw.id) HasLaw.id hz
  refine h.congr' (hσ.mono fun k hk => ?_)
  show μ.real _ = μ.real _
  congr 1
  ext x
  have hs := Real.sqrt_pos.2 hk
  simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hs, div_le_iff₀ hs]

/-- **The asymptotic confidence interval under a moment bound** (Giles 2015, §2.1, p. 8: "they
prefer to use the Central Limit Theorem to construct a confidence interval which bounds `E[P]`
with a user-prescribed confidence").  Under the hypotheses of
`tendstoInDistribution_mlmcEstimator_of_moment_le` (`δ > 0`; for `ℓ ≤ L_k`, `P_ℓ ∈ L²(ν)`,
`M_ℓ < ∞` and `M_ℓ ≤ K V_ℓ^{1+δ/2}`; `min_{ℓ ≤ L_k} N_{k,ℓ} → ∞`; `σ_k > 0` for large `k`), for
every `z ≥ 0`, `P(|Y_k − E[P_{L_k}]| ≤ z σ_k) → 2Φ(z) − 1`, with no condition on the growth of
`L_k`.  As in `tendsto_measureReal_abs_mlmcEstimator_sub_le`, `σ_k` is the exact standard
deviation. -/
theorem tendsto_measureReal_abs_mlmcEstimator_sub_le_of_moment_le [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {L : ℕ → ℕ} (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν) {δ : ℝ} (hδ : 0 < δ)
    (hM : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ)) ν)
    {K : ℝ} (hK : ∀ k, ∀ ℓ ≤ L k,
      ∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν ≤
        K * variance (levelDiff Pl ℓ) ν ^ (1 + δ / 2))
    {N : ℕ → ℕ → ℕ} (hNtop : ∀ n₀ : ℕ, ∀ᶠ k in atTop, ∀ ℓ ≤ L k, n₀ ≤ N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun k => μ.real {x | |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν| ≤
        z * √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)}) atTop
      (𝓝 (2 * cdf (gaussianReal 0 1) z - 1)) :=
  tendsto_measureReal_abs_mlmcEstimator_sub_le hω hind hPl hδ.le hM
    ((hNtop 1).mono fun _ hk ℓ hℓ => hk ℓ hℓ) hσ
    (tendsto_mlmcLyapunovRatio_of_moment_le hδ hK hNtop hσ) hz

/-- **Asymptotic normality around `E[P]`** (Giles 2015, §2.1, p. 8: "they prefer to use the
Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence").  Under the hypotheses of
`tendstoInDistribution_mlmcEstimator_lyapunov`, let `P` be the exact output, with
`(E[P_{L_k}] − E[P]) / σ_k → 0` (the bias is small against the standard deviation).  Then
`(Y_k − E[P]) / σ_k → N(0, 1)` in distribution (Slutsky's lemma,
`TendstoInDistribution.add_of_tendstoInMeasure_const`, with the deterministic shift
`(E[P_{L_k}] − E[P]) / σ_k → 0`).  Only the number `E[P] = ∫ P dν` enters, so no integrability of
`P` is assumed: the statement holds for any real number in its place. -/
theorem tendstoInDistribution_mlmcEstimator_of_bias [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P'] (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {L : ℕ → ℕ} (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν) {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ)) ν)
    {N : ℕ → ℕ → ℕ} (hN : ∀ᶠ k in atTop, ∀ ℓ ≤ L k, 0 < N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    (hlyap : Tendsto (fun k => (∑ ℓ ∈ range (L k + 1),
        (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
          (N k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (2 + δ)) atTop (𝓝 0))
    {P : Ω₀ → ℝ}
    (hbias : Tendsto (fun k => (∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν) /
      √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)) atTop (𝓝 0))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k x => (mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ))
      atTop Z (fun _ => μ) P' := by
  have h := (tendstoInDistribution_mlmcEstimator_lyapunov hω hind hPl hδ hM hN hσ hlyap
    hZ).add_of_tendstoInMeasure_const (c := 0)
    (Y := fun k (_ : Ω) => (∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν) /
      √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ))
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => hbias)) (fun _ => aemeasurable_const)
  refine h.congr (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => add_zero (Z x))
  simp only [Pi.add_apply]
  rw [← add_div, sub_add_sub_cancel]

/-- **The confidence interval around `E[P]`** (Giles 2015, §2.1, p. 8: "they prefer to use the
Central Limit Theorem to construct a confidence interval which bounds `E[P]` with a
user-prescribed confidence").  Under the hypotheses of
`tendsto_measureReal_abs_mlmcEstimator_sub_le`, if the bias is small against the standard
deviation, `(E[P_{L_k}] − E[P]) / σ_k → 0`, then for every `z ≥ 0`,
`P(|Y_k − E[P]| ≤ z σ_k) → 2Φ(z) − 1`: the interval `Y_k ± z σ_k` covers `E[P]` with asymptotic
confidence `2Φ(z) − 1` (`tendstoInDistribution_mlmcEstimator_of_bias` and
`tendsto_measureReal_abs_le_of_tendstoInDistribution`).  `σ_k` is the exact standard deviation
of `Y_k`; no integrability of `P` is needed, as only the number `∫ P dν` enters. -/
theorem tendsto_measureReal_abs_mlmcEstimator_sub_le_of_bias [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {L : ℕ → ℕ} (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν) {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ)) ν)
    {N : ℕ → ℕ → ℕ} (hN : ∀ᶠ k in atTop, ∀ ℓ ≤ L k, 0 < N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    (hlyap : Tendsto (fun k => (∑ ℓ ∈ range (L k + 1),
        (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
          (N k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (2 + δ)) atTop (𝓝 0))
    {P : Ω₀ → ℝ}
    (hbias : Tendsto (fun k => (∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν) /
      √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)) atTop (𝓝 0))
    {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun k => μ.real {x | |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν| ≤
        z * √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)}) atTop
      (𝓝 (2 * cdf (gaussianReal 0 1) z - 1)) := by
  have h := tendsto_measureReal_abs_le_of_tendstoInDistribution
    (tendstoInDistribution_mlmcEstimator_of_bias (P' := gaussianReal 0 1) (Z := id) hω hind hPl
      hδ hM hN hσ hlyap hbias HasLaw.id) HasLaw.id hz
  refine h.congr' (hσ.mono fun k hk => ?_)
  show μ.real _ = μ.real _
  congr 1
  ext x
  have hs := Real.sqrt_pos.2 hk
  simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hs, div_le_iff₀ hs]

/-- **The tolerance split of Collier et al.** (Giles 2015, §2.1, p. 8: "Instead of bounding the
Mean Square Error, they prefer to use the Central Limit Theorem to construct a confidence interval
which bounds `E[P]` with a user-prescribed confidence.").  Collier et al. split a tolerance
`TOL_k` into a bias part and a statistical part: if `|E[P_{L_k}] − E[P]| ≤ (1 − θ) TOL_k` and
`z σ_k ≤ θ TOL_k` for large `k`, then under the hypotheses of
`tendsto_measureReal_abs_mlmcEstimator_sub_le` the error is below `TOL_k` with asymptotic
confidence at least `2Φ(z) − 1`: for every `η > 0`, eventually
`P(|Y_k − E[P]| ≤ TOL_k) > 2Φ(z) − 1 − η`, i.e. `liminf_k P(|Y_k − E[P]| ≤ TOL_k) ≥ 2Φ(z) − 1`.
(Confidence `1 − α` corresponds to `z = Φ⁻¹(1 − α/2)`.)  The proof is the inclusion
`{|Y_k − E[P_{L_k}]| ≤ z σ_k} ⊆ {|Y_k − E[P]| ≤ TOL_k}`.  Here `σ_k` is the exact standard
deviation of `Y_k`; the variance estimation of Collier et al. is not formalised, and no
integrability of `P` is needed, as only the number `∫ P dν` enters. -/
theorem eventually_lt_measureReal_abs_mlmcEstimator_sub_le_tol [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {L : ℕ → ℕ} (hPl : ∀ k, ∀ ℓ ≤ L k, MemLp (Pl ℓ) 2 ν) {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ k, ∀ ℓ ≤ L k,
      Integrable (fun y => |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ)) ν)
    {N : ℕ → ℕ → ℕ} (hN : ∀ᶠ k in atTop, ∀ ℓ ≤ L k, 0 < N k ℓ)
    (hσ : ∀ᶠ k in atTop, 0 < ∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ)
    (hlyap : Tendsto (fun k => (∑ ℓ ∈ range (L k + 1),
        (∫ y, |levelDiff Pl ℓ y - ∫ z, levelDiff Pl ℓ z ∂ν| ^ (2 + δ) ∂ν) *
          (N k ℓ : ℝ) ^ (-1 - δ)) /
        √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ^ (2 + δ)) atTop (𝓝 0))
    {P : Ω₀ → ℝ} {θ z : ℝ} {TOL : ℕ → ℝ} (hz : 0 ≤ z)
    (hbias : ∀ᶠ k in atTop, |∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν| ≤ (1 - θ) * TOL k)
    (hstat : ∀ᶠ k in atTop,
      z * √(∑ ℓ ∈ range (L k + 1), variance (levelDiff Pl ℓ) ν / N k ℓ) ≤ θ * TOL k)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, 2 * cdf (gaussianReal 0 1) z - 1 - η <
      μ.real {x | |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν| ≤ TOL k} := by
  have h := tendsto_measureReal_abs_mlmcEstimator_sub_le hω hind hPl hδ hM hN hσ hlyap hz
  filter_upwards [h.eventually (lt_mem_nhds (sub_lt_self _ hη)), hbias, hstat] with k hk hb hs
  refine hk.trans_le (measureReal_mono fun x hx => ?_)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  calc |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, P y ∂ν|
      = |(mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν) +
          (∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν)| := by rw [sub_add_sub_cancel]
    _ ≤ |mlmcEstimator Pl ω (L k) (N k) x - ∫ y, Pl (L k) y ∂ν| +
          |∫ y, Pl (L k) y ∂ν - ∫ y, P y ∂ν| := abs_add_le _ _
    _ ≤ θ * TOL k + (1 - θ) * TOL k := add_le_add (hx.trans hs) hb
    _ = TOL k := by ring

end Estimator

end MLMC
