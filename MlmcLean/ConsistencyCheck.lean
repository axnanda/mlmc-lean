import MlmcLean.Implementation
import MlmcLean.MLMCCentralLimit
import MlmcLean.SampleMean
import Mathlib.Probability.StrongLaw

/-!
# The consistency check with empirical variances (Giles 2015, §3.3)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §3.3, p. 22 of
the author's version.

**Giles (2015), §3.3, p. 22.** "If `a, b, c` are estimates for `E[P^f_{ℓ−1}], E[P^f_ℓ], E[Y_ℓ]`,
respectively, then it should be true that `a − b + c ≈ 0`. The consistency check verifies that
this is true, to within the accuracy one would expect due to Monte Carlo sampling error. …
Since `√V[a − b + c] ≤ √V[a] + √V[b] + √V[c]` it computes and plots the ratio
`|a − b + c| / (3(√V_a + √V_b + √V_c))` where `V_a, V_b, V_c` are empirical estimates for the
variances of `a, b, c`. The probability of this ratio being greater than unity is less than
0.3%."

`MlmcLean/Implementation.lean` proves the bound `0.3%` with the true variances when `a − b + c` is
exactly normal (`consistency_check_gaussian`), and the bound `1/9` without normality
(`consistency_check_chebyshev`).  This file treats the empirical variances of the paper.

**Model.**  The paper's levels `ℓ − 1, ℓ` are written `ℓ, ℓ + 1` here (as in `consistency_mean`).
The inputs `ω^{(p)}`, `p ∈ ℕ × ℕ`, are independent with law `ν`, and the sample sizes
`N_a = N_a(k)`, `N_b = N_b(k)` depend on an index `k`.
* `a` is the mean of `P^f_ℓ(ω^{(ℓ,n)})`, `n < N_a` (the samples of the coarser level);
* `b` and `c` are the means of `P^f_{ℓ+1}(ω^{(ℓ+1,n)})` and of `Y = P^f_{ℓ+1} − P^c_ℓ` at the same
  inputs `ω^{(ℓ+1,n)}`, `n < N_b`, so `a − b + c` is the difference of the means of `P^f_ℓ` and
  `P^c_ℓ` (`empMean_sub_add`);
* `V_a = s_a²/N_a`, `V_b = s_b²/N_b`, `V_c = s_c²/N_b`, where `s² = N⁻¹ ∑_{n<N} (x_n − x̄)²` is the
  biased empirical variance of the samples (`empVar`): the formula
  `Vl = max(0, suml(2,:)./Nl - ml.^2)` of the driver in §3.4 (`empVar_eq_powerSum`).  Larger
  estimates, e.g. the unbiased `V_a = S_a²/N_a = s_a²/(N_a − 1)`, where `S² = N s²/(N − 1)` is the
  unbiased sample variance, are covered as well (`consistency_check_of_empVar_le`);
* the check fails when the ratio exceeds unity, stated without division as
  `3(√V_a + √V_b + √V_c) < |a − b + c|` (this includes a zero denominator with `a − b + c ≠ 0`).

**Results.**
* `tendsto_empVar_ae`, `tendstoInMeasure_empVar`: for pairwise independent, identically
  distributed, square-integrable `X_n`, `s_N² → V[X_0]` almost surely and in probability (the strong
  law of large numbers, `ProbabilityTheory.strong_law_ae_real`, for `X_n` and `X_n²`);
* `tendstoInDistribution_twoSample`, `tendstoInDistribution_consistencyStat`: under (2.4) and
  `V[P^f_ℓ] + V[P^c_ℓ] > 0`, `(a − b + c)/σ_k → N(0, 1)` in distribution as `N_a(k), N_b(k) → ∞`
  at arbitrary rates, where `σ_k² = V[P^f_ℓ]/N_a + V[P^c_ℓ]/N_b = V[a − b + c]` (Lindeberg's
  theorem `tendstoInDistribution_lindeberg` for the two independent groups; second moments
  suffice);
* `sqrt_empVar_sub_le`: the paper's inequality `√V[x − y] ≤ √V[x] + √V[y]` holds for the
  empirical variances as well;
* `consistency_check_empirical` (**the main theorem**): under (2.4), with `P^f_ℓ, P^c_ℓ` square
  integrable and `N_a(k), N_b(k) → ∞`, for every `η > 0`, eventually
  `P(the check fails) < P(|Z| ≥ 3) + η` for `Z ~ N(0, 1)`, i.e.
  `limsup_k P(the check fails) ≤ P(|Z| ≥ 3)`;
* `consistency_check_empirical_lt`: eventually `P(the check fails) < 0.003`, the paper's claim
  for all sufficiently large sample sizes (`gaussian_tail_three`);
* `consistency_check_of_variance_estimates`, `consistency_check_of_empVar_le`: the same for any
  variance estimates that do not underestimate asymptotically, resp. that are at least the
  empirical ones;
* `consistency_check_empirical_sharp`: the bound `P(|Z| ≥ 3)` is attained in the limit when
  `P^f_ℓ`, `P^f_{ℓ+1}` are almost surely constant and `V[P^c_ℓ] > 0`.

**Deviations from the paper.**
* *The statement is asymptotic.*  The `0.3%` is `P(|Z| > 3) ≈ 0.0027`.  It presumes that
  `a − b + c` is normal and that `V_a, V_b, V_c` are exact; with empirical variances neither holds
  for a fixed sample size, and the bound can fail.  Example: `P^f_ℓ = P^f_{ℓ+1} = 0` and
  `P^c_ℓ = −Y` with `Y ~ N(0, 1)`, so (2.4) holds.  Then `V_a = V_b = 0`, and with `N = N_b` the
  check fails iff `|t| > 3√((N − 1)/N)`, `t` being Student's statistic of the `N` samples of `Y`
  (`N − 1` degrees of freedom).  For `N = 2` this has probability
  `(2/π) arctan(√2/3) ≈ 0.280`, for `N = 10` about `0.019`, for `N = 100` about `0.0036`, and it
  exceeds `0.003` for every `2 ≤ N ≤ 274` (for `N = 1` it is `1`, as then `s_c² = 0`).  With
  independent `P^f_ℓ ~ N(0, 1)` and
  `P^f_{ℓ+1} = P^c_ℓ ~ N(0, 1)` and `N_a = N_b = N` it is about `0.116` for `N = 2` and `0.0064`
  for `N = 5`.  (These values were checked by numerical integration and by Monte Carlo
  simulation.)  So the correct reading of the paper's claim is the limit statement proved here.
  In the first example the failure probability tends to `P(|Z| ≥ 3) ≈ 0.0027` as `N → ∞`, so the
  bound of the main theorem is attained (`consistency_check_empirical_sharp`, for every
  square-integrable `P^c_ℓ` with `V[P^c_ℓ] > 0` and almost surely constant `P^f_ℓ, P^f_{ℓ+1}`).
* *Hypotheses.*  (2.4) enters as `E[P^f_ℓ] = E[P^c_ℓ]`, the identity the check tests (it gives
  `E[a − b + c] = 0`, `consistency_mean`).  `P^f_ℓ` and `P^c_ℓ` are square integrable and the
  samples of the two levels are independent, as in the test routine.  The main theorems need no
  hypothesis on `P^f_{ℓ+1}`, which cancels from `a − b + c` (the paper's setting has all three
  outputs square integrable; `consistency_check_of_variance_estimates` assumes it, so that its
  hypotheses on `V[P^f_{ℓ+1}]` and `V[Y]` are not junk values).  The sample sizes may grow at
  unrelated rates.  No non-degeneracy is assumed: if `V[P^f_ℓ] = V[P^c_ℓ] = 0` then
  `a − b + c = 0` almost surely and the check never fails.  Both levels draw their inputs from the
  same law `ν` (a product measure covers different input spaces on the two levels).
* *The inequality.*  The paper's `√V[a − b + c] ≤ √V[a] + √V[b] + √V[c]` reduces, as
  `a − b + c` is the difference of the means of `P^f_ℓ` and `P^c_ℓ`, to
  `√V[P^c_ℓ] ≤ √V[P^f_{ℓ+1}] + √V[Y]` (`sqrt_variance_sub_le`, used in
  `consistency_check_of_variance_estimates`).  For the empirical variances the same inequality
  `√(s²[P^c_ℓ]) ≤ √(s²[P^f_{ℓ+1}]) + √(s²[Y])` holds sample by sample (`sqrt_empVar_sub_le`), so
  `√V_b + √V_c ≥ √(s²[P^c_ℓ]/N_b)`.  The empirical sum of standard deviations is then compared
  with `√(V[P^f_ℓ]/N_a) + √(V[P^c_ℓ]/N_b) ≥ σ_k` (`consistency_check_of_sd_estimate`): only
  underestimation can make the check fail more often, and it has vanishing probability by the
  consistency of `s²`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace MLMC

/-! ### Empirical means and variances -/

/-- The empirical mean `x̄_N = N⁻¹ ∑_{n<N} x_n` of the first `N` terms of a sequence (the estimates
`a, b, c` of the consistency check, Giles 2015, §3.3, p. 22, and `suml(1,:)./Nl` in the driver of
§3.4).  It is `0` for `N = 0`.  On the samples `f_i(ω^{(i,n)})` it is the Monte Carlo average
`blockMean` of `MlmcLean/SampleMean.lean` (`empMean_eq_blockMean`); `empVar` needs the mean of an
arbitrary sequence. -/
noncomputable def empMean (x : ℕ → ℝ) (N : ℕ) : ℝ := (∑ n ∈ range N, x n) / N

/-- The empirical variance `s_N² = N⁻¹ ∑_{n<N} (x_n − x̄_N)²` of the first `N` terms of a sequence
(Giles 2015, §3.3, p. 22: "`V_a, V_b, V_c` are empirical estimates for the variances of `a, b, c`";
the estimate of the variance of a mean of `N` samples is `s_N²/N`).  This is the biased form, the
formula `Vl = max(0, suml(2,:)./Nl - ml.^2)` of the driver in §3.4 (`empVar_eq_powerSum`).  The
unbiased sample variance is `S_N² = N s_N²/(N − 1)`, and the corresponding unbiased estimate of
the variance of the mean is `S_N²/N = s_N²/(N − 1)`.  It is `0` for `N = 0`. -/
noncomputable def empVar (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, (x n - empMean x N) ^ 2) / N

/-- The empirical mean of the samples `f_i(ω^{(i,n)})`, `n < N`, is the Monte Carlo average
`blockMean f ω i N` (Giles 2015, §1.1, p. 2; the estimates `a, b, c` of §3.3, p. 22). -/
lemma empMean_eq_blockMean {ι Ω₀ Ω : Type*} (f : ι → Ω₀ → ℝ) (ω : ι × ℕ → Ω → Ω₀) (i : ι)
    (N : ℕ) (x : Ω) : empMean (fun n => f i (ω (i, n) x)) N = blockMean f ω i N x := by
  rw [empMean, blockMean, div_eq_inv_mul]

/-- The empirical mean is linear: `(x − y)‾_N = x̄_N − ȳ_N`. -/
lemma empMean_sub (x y : ℕ → ℝ) (N : ℕ) :
    empMean (fun n => x n - y n) N = empMean x N - empMean y N := by
  rw [empMean, empMean, empMean, Finset.sum_sub_distrib, sub_div]

/-- Minkowski's inequality for finite sums, `√(∑ (u − w)²) ≤ √(∑ u²) + √(∑ w²)` (from the
Cauchy–Schwarz inequality `Finset.sum_mul_sq_le_sq_mul_sq`; for the consistency check of Giles
2015, §3.3, p. 22). -/
lemma sqrt_sum_sub_sq_le (s : Finset ℕ) (u w : ℕ → ℝ) :
    √(∑ n ∈ s, (u n - w n) ^ 2) ≤ √(∑ n ∈ s, u n ^ 2) + √(∑ n ∈ s, w n ^ 2) := by
  have hA : 0 ≤ ∑ n ∈ s, u n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg (u n)
  have hB : 0 ≤ ∑ n ∈ s, w n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg (w n)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s u w
  have hexp : ∑ n ∈ s, (u n - w n) ^ 2 =
      ∑ n ∈ s, u n ^ 2 - 2 * ∑ n ∈ s, u n * w n + ∑ n ∈ s, w n ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [Real.sqrt_le_left (by positivity), hexp]
  set p := √(∑ n ∈ s, u n ^ 2)
  set q := √(∑ n ∈ s, w n ^ 2)
  set t := ∑ n ∈ s, u n * w n
  have hp : p ^ 2 = ∑ n ∈ s, u n ^ 2 := Real.sq_sqrt hA
  have hq : q ^ 2 = ∑ n ∈ s, w n ^ 2 := Real.sq_sqrt hB
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have ht : -(p * q) ≤ t := by
    rw [← hp, ← hq] at hcs
    nlinarith [mul_nonneg hp0 hq0]
  nlinarith

/-- **The empirical standard deviation satisfies the triangle inequality** (Giles 2015, §3.3,
p. 22: "Since `√V[a − b + c] ≤ √V[a] + √V[b] + √V[c]` it computes and plots the ratio
`|a − b + c| / (3(√V_a + √V_b + √V_c))`").  For all sequences `x, y` and every `N`,
`√(s_N²[x − y]) ≤ √(s_N²[x]) + √(s_N²[y])`: the paper's inequality also holds for the empirical
variances, as `s_N` is a seminorm of the sample vector (Minkowski's inequality for the centred
samples, `sqrt_sum_sub_sq_le`). -/
lemma sqrt_empVar_sub_le (x y : ℕ → ℝ) (N : ℕ) :
    √(empVar (fun n => x n - y n) N) ≤ √(empVar x N) + √(empVar y N) := by
  have hc : ∀ n, x n - y n - empMean (fun n => x n - y n) N =
      (x n - empMean x N) - (y n - empMean y N) := fun n => by
    rw [empMean_sub]
    ring
  simp only [empVar, hc]
  rw [Real.sqrt_div' _ (Nat.cast_nonneg N), Real.sqrt_div' _ (Nat.cast_nonneg N),
    Real.sqrt_div' _ (Nat.cast_nonneg N), ← add_div]
  exact div_le_div_of_nonneg_right (sqrt_sum_sub_sq_le _ _ _) (Real.sqrt_nonneg _)

/-- The triangle inequality `sqrt_empVar_sub_le` for the variance estimates `s_N²/N` of the means:
`√(s_N²[x − y]/N) ≤ √(s_N²[x]/N) + √(s_N²[y]/N)`.  With `x = P^f_{ℓ+1}` and
`y = Y = P^f_{ℓ+1} − P^c_ℓ` at the same samples it gives `√V_b + √V_c ≥ √(s²[P^c_ℓ]/N_b)` in the
consistency check of Giles 2015, §3.3, p. 22. -/
lemma sqrt_empVar_div_sub_le (x y : ℕ → ℝ) (N : ℕ) :
    √(empVar (fun n => x n - y n) N / N) ≤ √(empVar x N / N) + √(empVar y N / N) := by
  rw [Real.sqrt_div' _ (Nat.cast_nonneg N), Real.sqrt_div' _ (Nat.cast_nonneg N),
    Real.sqrt_div' _ (Nat.cast_nonneg N), ← add_div]
  exact div_le_div_of_nonneg_right (sqrt_empVar_sub_le _ _ _) (Real.sqrt_nonneg _)

/-- The empirical variance in power-sum form: `s_N² = N⁻¹ ∑ x_n² − (N⁻¹ ∑ x_n)²` for `N ≥ 1` (the
driver's `suml(2,:)./Nl - ml.^2`, Giles 2015, §3.4, p. 25; `powerSum_variance_eq`). -/
lemma empVar_eq_powerSum (x : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    empVar x N = (∑ n ∈ range N, x n ^ 2) / N - ((∑ n ∈ range N, x n) / N) ^ 2 :=
  (powerSum_variance_eq x hN).symm

/-- When `b` and `c` are means over the same samples, of `v` and of `v − w`, then
`a − b + c = ū − w̄` (Giles 2015, §3.3, p. 22: `a − b + c` is the difference of the means of
`P^f_{ℓ−1}` and `P^c_{ℓ−1}`, since `Y_ℓ = P^f_ℓ − P^c_{ℓ−1}`). -/
lemma empMean_sub_add (u v w : ℕ → ℝ) (Na Nb : ℕ) :
    empMean u Na - empMean v Nb + empMean (fun n => v n - w n) Nb =
      empMean u Na - empMean w Nb := by
  simp only [empMean, Finset.sum_sub_distrib, sub_div]
  ring

/-- The empirical mean of a constant sequence of length `N ≥ 1` is the constant. -/
lemma empMean_const (c : ℝ) {N : ℕ} (hN : 0 < N) : empMean (fun _ => c) N = c := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  simp only [empMean, Finset.sum_const, card_range, nsmul_eq_mul]
  field_simp

/-- The empirical variance of a constant sequence is `0`. -/
lemma empVar_const (c : ℝ) (N : ℕ) : empVar (fun _ => c) N = 0 := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [empVar]
  · simp [empVar, empMean_const c hN]

/-! ### Consistency of the empirical variance -/

section Strong

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The empirical variance is strongly consistent** (Giles 2015, §3.3, p. 22: "`V_a, V_b, V_c`
are empirical estimates for the variances of `a, b, c`").  Let `X_0, X_1, …` be pairwise
independent, identically distributed real random variables with `E[X_0²] < ∞`.  Then almost
surely the empirical variance `s_N² = N⁻¹ ∑_{n<N} (X_n − X̄_N)²` of the first `N` of them tends to
`V[X_0]` as `N → ∞`.  Proof: `s_N² = N⁻¹ ∑_{n<N} X_n² − X̄_N²` (`empVar_eq_powerSum`) and the
strong law of large numbers (`ProbabilityTheory.strong_law_ae_real`) for `X_n` and for `X_n²`.
The unbiased sample variance `S_N² = N s_N²/(N − 1)` has the same limit. -/
theorem tendsto_empVar_ae {X : ℕ → Ω → ℝ} (hX : MemLp (X 0) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun N => empVar (fun n => X n x) N) atTop (𝓝 (variance (X 0) μ)) := by
  have h1 := strong_law_ae_real X (hX.integrable one_le_two) hindep hident
  have h2 := strong_law_ae_real (fun n x => X n x ^ 2) hX.integrable_sq
    (fun i j hij => (hindep hij).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2))
    (fun i => (hident i).comp (measurable_id.pow_const 2))
  filter_upwards [h1, h2] with x hx1 hx2
  have e : μ[X 0 ^ 2] = ∫ x, X 0 x ^ 2 ∂μ := rfl
  rw [variance_eq_sub hX, e]
  refine (hx2.sub (hx1.pow 2)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (empVar_eq_powerSum _ hN).symm

/-- **The empirical variance is consistent in probability** (Giles 2015, §3.3, p. 22:
"`V_a, V_b, V_c` are empirical estimates for the variances of `a, b, c`").  Under the hypotheses of
`tendsto_empVar_ae`, `s_N² → V[X_0]` in probability: `P(|s_N² − V[X_0]| ≥ ε) → 0` for every
`ε > 0`, because almost sure convergence implies convergence in measure
(`tendstoInMeasure_of_tendsto_ae`). -/
theorem tendstoInMeasure_empVar {X : ℕ → Ω → ℝ} (hX : MemLp (X 0) 2 μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInMeasure μ (fun N x => empVar (fun n => X n x) N) atTop
      (fun _ => variance (X 0) μ) := by
  have hXm : ∀ n, AEMeasurable (X n) μ := fun n => (hident n).aemeasurable_fst
  refine tendstoInMeasure_of_tendsto_ae (fun N => AEMeasurable.aestronglyMeasurable ?_)
    (tendsto_empVar_ae hX hindep hident)
  unfold empVar empMean
  exact (Finset.aemeasurable_fun_sum _ fun n _ => ((hXm n).sub
    ((Finset.aemeasurable_fun_sum _ fun m _ => hXm m).div_const _)).pow_const 2).div_const _

end Strong

/-! ### Lindeberg tails of square-integrable variables -/

section Tail

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {ν : Measure Ω₀}

/-- The Lindeberg tail `E[g²; |g| > t]` of a square-integrable `g` tends to `0` as `t → ∞`
(dominated convergence; used for the central limit theorem behind the consistency check of Giles
2015, §3.3). -/
lemma tendsto_lindebergTail {g : Ω₀ → ℝ} (hg : MemLp g 2 ν) :
    Tendsto (fun t : ℝ => ∫ y, {z : ℝ | t < |z|}.indicator (fun z => z ^ 2) (g y) ∂ν) atTop
      (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _, (0 : ℝ) ∂ν := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => g y ^ 2)
    (Eventually.of_forall fun t => ((measurable_lindebergIntegrand t).comp_aemeasurable
      hg.aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ fun y => ?_) hg.integrable_sq
    (ae_of_all _ fun y => ?_)
  · by_cases h : t < |g y|
    · simp [Set.indicator_of_mem (show g y ∈ {z : ℝ | t < |z|} from h)]
    · simp [Set.indicator_of_notMem (show g y ∉ {z : ℝ | t < |z|} from h), sq_nonneg]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop |g y|] with t ht
    rw [Set.indicator_of_notMem (show g y ∉ {z : ℝ | t < |z|} from not_lt.2 ht)]

/-- Scaling the Lindeberg integrand: `(cw)² 𝟙{|cw| > ε} = c² w² 𝟙{|w| > ε/c}` for `c > 0`. -/
lemma lindebergIntegrand_const_mul {c : ℝ} (hc : 0 < c) (ε w : ℝ) :
    {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (c * w) =
      c ^ 2 * {z : ℝ | ε / c < |z|}.indicator (fun z => z ^ 2) w := by
  have hiff : ε < |c * w| ↔ ε / c < |w| := by
    rw [abs_mul, abs_of_pos hc, div_lt_iff₀ hc, mul_comm]
  by_cases h : ε / c < |w|
  · rw [Set.indicator_of_mem (show c * w ∈ {z : ℝ | ε < |z|} from hiff.2 h),
      Set.indicator_of_mem (show w ∈ {z : ℝ | ε / c < |z|} from h)]
    ring
  · rw [Set.indicator_of_notMem (show c * w ∉ {z : ℝ | ε < |z|} from fun h' => h (hiff.1 h')),
      Set.indicator_of_notMem (show w ∉ {z : ℝ | ε / c < |z|} from h), mul_zero]

/-- The Lindeberg tail `E[g²; |g| > t]` is nonnegative. -/
lemma lindebergTail_nonneg (g : Ω₀ → ℝ) (t : ℝ) :
    0 ≤ ∫ y, {z : ℝ | t < |z|}.indicator (fun z => z ^ 2) (g y) ∂ν :=
  integral_nonneg fun _ => Set.indicator_nonneg (fun z _ => sq_nonneg z) _

/-- The Lindeberg tail `E[g²; |g| > t]` of a square-integrable `g` decreases in `t`. -/
lemma lindebergTail_anti {g : Ω₀ → ℝ} (hg : MemLp g 2 ν) {t t' : ℝ} (htt : t ≤ t') :
    ∫ y, {z : ℝ | t' < |z|}.indicator (fun z => z ^ 2) (g y) ∂ν ≤
      ∫ y, {z : ℝ | t < |z|}.indicator (fun z => z ^ 2) (g y) ∂ν := by
  refine integral_mono (integrable_lindebergIntegrand hg t') (integrable_lindebergIntegrand hg t)
    fun y => ?_
  by_cases h : t' < |g y|
  · rw [Set.indicator_of_mem (show g y ∈ {z : ℝ | t' < |z|} from h),
      Set.indicator_of_mem (show g y ∈ {z : ℝ | t < |z|} from htt.trans_lt h)]
  · rw [Set.indicator_of_notMem (show g y ∉ {z : ℝ | t' < |z|} from h)]
    exact Set.indicator_nonneg (fun z _ => sq_nonneg z) _

/-- The Lindeberg tail is at most the second moment: `E[g²; |g| > t] ≤ E[g²]`. -/
lemma lindebergTail_le {g : Ω₀ → ℝ} (hg : MemLp g 2 ν) (t : ℝ) :
    ∫ y, {z : ℝ | t < |z|}.indicator (fun z => z ^ 2) (g y) ∂ν ≤ ∫ y, g y ^ 2 ∂ν := by
  refine integral_mono (integrable_lindebergIntegrand hg t) hg.integrable_sq fun y => ?_
  by_cases h : t < |g y|
  · rw [Set.indicator_of_mem (show g y ∈ {z : ℝ | t < |z|} from h)]
  · rw [Set.indicator_of_notMem (show g y ∉ {z : ℝ | t < |z|} from h)]
    exact sq_nonneg _

/-- Lindeberg's condition for one group of i.i.d. samples (for the consistency check of Giles 2015,
§3.3).  If `g` is square integrable, `N_k → ∞`, `σ_k > 0` and `E[g²] ≤ N_k σ_k²`, then
`E[g²; |g| > ε N_k σ_k] / (N_k σ_k²) → 0` for every `ε > 0`; this is the contribution
`N_k E[(g/(N_k σ_k))²; |g/(N_k σ_k)| > ε]` of `N_k` samples of `g/(N_k σ_k)` to the Lindeberg sum.
If `E[g²] = 0` the tails vanish; otherwise `N_k σ_k ≥ √(N_k E[g²]) → ∞`
(`tendsto_lindebergTail`). -/
lemma tendsto_lindebergTail_div {g : Ω₀ → ℝ} (hg : MemLp g 2 ν) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) {σ : ℕ → ℝ} (hσ : ∀ k, 0 < σ k)
    (hle : ∀ k, ∫ y, g y ^ 2 ∂ν ≤ N k * σ k ^ 2) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (∫ y, {z : ℝ | ε * (N k * σ k) < |z|}.indicator (fun z => z ^ 2) (g y) ∂ν)
      / (N k * σ k ^ 2)) atTop (𝓝 0) := by
  set Q := ∫ y, g y ^ 2 ∂ν with hQ
  have hQ0 : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
  rcases hQ0.eq_or_lt with hQe | hQp
  · refine tendsto_const_nhds.congr fun k => ?_
    rw [le_antisymm ((lindebergTail_le hg _).trans hQe.symm.le) (lindebergTail_nonneg g _),
      zero_div]
  · have hlim : Tendsto (fun k => ε * √(N k * Q)) atTop atTop :=
      ((Real.tendsto_sqrt_atTop.comp
        ((tendsto_natCast_atTop_atTop.comp hN).atTop_mul_const hQp)).const_mul_atTop hε)
    have hup := ((tendsto_lindebergTail hg).comp hlim).div_const Q
    rw [zero_div] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_)
      (fun k => ?_)
    · exact div_nonneg (lindebergTail_nonneg g _) ((hQ0.trans (hle k)))
    · have hNσ : 0 ≤ (N k : ℝ) * σ k := mul_nonneg (Nat.cast_nonneg _) (hσ k).le
      have hsq : √(N k * Q) ≤ N k * σ k := by
        rw [Real.sqrt_le_left hNσ]
        have := mul_le_mul_of_nonneg_left (hle k) (Nat.cast_nonneg (N k))
        nlinarith
      calc (∫ y, {z : ℝ | ε * (N k * σ k) < |z|}.indicator (fun z => z ^ 2) (g y) ∂ν)
            / (N k * σ k ^ 2)
          ≤ (∫ y, {z : ℝ | ε * (N k * σ k) < |z|}.indicator (fun z => z ^ 2) (g y) ∂ν) / Q :=
            div_le_div_of_nonneg_left (lindebergTail_nonneg g _) hQp (hle k)
        _ ≤ (∫ y, {z : ℝ | ε * √(N k * Q) < |z|}.indicator (fun z => z ^ 2) (g y) ∂ν) / Q :=
            div_le_div_of_nonneg_right
              (lindebergTail_anti hg (mul_le_mul_of_nonneg_left hsq hε.le)) hQ0
        _ = _ := rfl

end Tail

/-! ### The central limit theorem for the consistency statistic -/

section TwoSample

variable {Ω₀ Ω Ω' : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω₀} {μ : Measure Ω} {P' : Measure Ω'} {ω : ℕ × ℕ → Ω → Ω₀}

/-- The mean of the samples `g(ω^{(i,n)})`, `n < N`, is a.e. measurable when `g` is. -/
lemma aemeasurable_empMean_input (hω : ∀ p, MeasurePreserving (ω p) μ ν) {g : Ω₀ → ℝ}
    (hg : AEMeasurable g ν) (i N : ℕ) :
    AEMeasurable (fun x => empMean (fun n => g (ω (i, n) x)) N) μ := by
  unfold empMean
  exact (Finset.aemeasurable_fun_sum _ fun n _ => aemeasurable_comp_input hω hg (i, n)).div_const _

omit [MeasurableSpace Ω₀] [MeasurableSpace Ω] in
/-- A sum over the samples `{i} × [0, N_a) ∪ {j} × [0, N_b)` of two distinct blocks `i ≠ j` is the
sum of the two block sums. -/
lemma sum_union_blocks {i j : ℕ} (hij : i ≠ j) (Na Nb : ℕ) (φ : ℕ × ℕ → ℝ) :
    ∑ q ∈ ({i} ×ˢ range Na ∪ {j} ×ˢ range Nb), φ q =
      ∑ n ∈ range Na, φ (i, n) + ∑ n ∈ range Nb, φ (j, n) := by
  have hdisj : Disjoint ({i} ×ˢ range Na) ({j} ×ˢ range Nb) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton] at h1 h2
    exact hij (h1.1.symm.trans h2.1)
  rw [Finset.sum_union hdisj, Finset.sum_product, Finset.sum_product, Finset.sum_singleton,
    Finset.sum_singleton]

/-- The two-sample central limit theorem when `N_a(k), N_b(k) ≥ 1` for every `k` (the core of
`tendstoInDistribution_twoSample`). -/
lemma tendstoInDistribution_twoSample_of_forall [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P'] (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {f g : Ω₀ → ℝ} {i j : ℕ} (hij : i ≠ j) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hfg : ∫ y, f y ∂ν = ∫ y, g y ∂ν) (hpos : 0 < variance f ν + variance g ν)
    {Na Nb : ℕ → ℕ} (hNa : Tendsto Na atTop atTop) (hNb : Tendsto Nb atTop atTop)
    (hNa1 : ∀ k, 0 < Na k) (hNb1 : ∀ k, 0 < Nb k) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k x => (empMean (fun n => f (ω (i, n) x)) (Na k) -
        empMean (fun n => g (ω (j, n) x)) (Nb k)) / √(variance f ν / Na k + variance g ν / Nb k))
      atTop Z (fun _ => μ) P' := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  obtain ⟨m, hm⟩ : ∃ m, ∫ y, f y ∂ν = m := ⟨_, rfl⟩
  have hgm : ∫ y, g y ∂ν = m := hfg ▸ hm
  obtain ⟨Vf, hVf⟩ : ∃ V, variance f ν = V := ⟨_, rfl⟩
  obtain ⟨Vg, hVg⟩ : ∃ V, variance g ν = V := ⟨_, rfl⟩
  rw [hVf, hVg] at hpos
  simp only [hVf, hVg]
  have hVf0 : 0 ≤ Vf := hVf ▸ variance_nonneg _ _
  have hVg0 : 0 ≤ Vg := hVg ▸ variance_nonneg _ _
  have hNa0 : ∀ k, (0 : ℝ) < Na k := fun k => Nat.cast_pos.2 (hNa1 k)
  have hNb0 : ∀ k, (0 : ℝ) < Nb k := fun k => Nat.cast_pos.2 (hNb1 k)
  have hs2pos : ∀ k, 0 < Vf / Na k + Vg / Nb k := by
    intro k
    have h1 := div_nonneg hVf0 (hNa0 k).le
    have h2 := div_nonneg hVg0 (hNb0 k).le
    rcases hVf0.eq_or_lt with h | h
    · have := div_pos (show 0 < Vg by linarith) (hNb0 k)
      linarith
    · have := div_pos h (hNa0 k)
      linarith
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → ℝ, ∀ k, √(Vf / Na k + Vg / Nb k) = σ k := ⟨_, fun _ => rfl⟩
  have hσpos : ∀ k, 0 < σ k := fun k => hσdef k ▸ Real.sqrt_pos.2 (hs2pos k)
  have hσsq : ∀ k, σ k ^ 2 = Vf / Na k + Vg / Nb k := fun k => by
    rw [← hσdef k, Real.sq_sqrt (hs2pos k).le]
  simp only [hσdef]
  -- the centred and scaled samples of the two groups
  set F : ℕ → Ω₀ → ℝ := fun k y => ((Na k : ℝ) * σ k)⁻¹ * (f y - m) with hF
  set G : ℕ → Ω₀ → ℝ := fun k y => ((Nb k : ℝ) * σ k)⁻¹ * (m - g y) with hG
  set h : ℕ → ℕ → Ω₀ → ℝ := fun k p => if p = i then F k else G k with hh
  have hhi : ∀ k, h k i = F k := fun k => if_pos rfl
  have hhj : ∀ k, h k j = G k := fun k => if_neg hij.symm
  have hFL2 : ∀ k, MemLp (F k) 2 ν := fun k => (hf.sub (memLp_const m)).const_mul _
  have hGL2 : ∀ k, MemLp (G k) 2 ν := fun k => ((memLp_const m).sub hg).const_mul _
  have hhL2 : ∀ k p, MemLp (h k p) 2 ν := by
    intro k p
    simp only [hh]
    split_ifs
    exacts [hFL2 k, hGL2 k]
  have hhm : ∀ k p, AEMeasurable (h k p) ν := fun k p =>
    (hhL2 k p).aestronglyMeasurable.aemeasurable
  have hh0 : ∀ k p, ∫ y, h k p y ∂ν = 0 := by
    intro k p
    simp only [hh]
    split_ifs
    · simp only [hF]
      rw [integral_const_mul, integral_sub (hf.integrable one_le_two) (integrable_const _),
        integral_const, hm]
      simp
    · simp only [hG]
      rw [integral_const_mul, integral_sub (integrable_const _) (hg.integrable one_le_two),
        integral_const, hgm]
      simp
  have hFvar : ∀ k, Var[F k; ν] = ((Na k : ℝ) * σ k)⁻¹ ^ 2 * Vf := by
    intro k
    simp only [hF]
    rw [variance_const_mul, variance_sub_const hf.aestronglyMeasurable, hVf]
  have hGvar : ∀ k, Var[G k; ν] = ((Nb k : ℝ) * σ k)⁻¹ ^ 2 * Vg := by
    intro k
    simp only [hG]
    rw [variance_const_mul, variance_const_sub hg.aestronglyMeasurable, hVg]
  -- the normalised statistic is the row sum of a triangular array
  set s : ℕ → Finset (ℕ × ℕ) := fun k => {i} ×ˢ range (Na k) ∪ {j} ×ˢ range (Nb k) with hs
  have hfun : (fun k x => (empMean (fun n => f (ω (i, n) x)) (Na k) -
      empMean (fun n => g (ω (j, n) x)) (Nb k)) / σ k) =
      fun k x => ∑ q ∈ s k, h k q.1 (ω q x) := by
    funext k x
    simp only [hs]
    rw [sum_union_blocks hij]
    simp only [hhi, hhj, hF, hG, empMean]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.sum_const, card_range, card_range, nsmul_eq_mul, nsmul_eq_mul]
    have := hNa0 k
    have := hNb0 k
    have := hσpos k
    field_simp
    ring
  rw [hfun]
  refine tendstoInDistribution_lindeberg (Ω := fun _ => Ω) (P := fun _ => μ) (s := s)
    (X := fun k q x => h k q.1 (ω q x)) (fun k => ?_)
    (fun k q _ => (hhL2 k q.1).comp_measurePreserving (hω q)) (fun k q _ => ?_) (fun k => ?_)
    (fun ε hε => ?_) hZ
  · -- independence: distinct samples use distinct inputs
    exact iIndepFun_comp_inputs hω hind (e := fun q : s k => (q : ℕ × ℕ)) Subtype.val_injective
      (g := fun q => h k q.1.1) fun q => hhm k _
  · -- centring
    rw [integral_comp_of_measurePreserving (hω q) (hhL2 k q.1).aestronglyMeasurable]
    exact hh0 k q.1
  · -- the variances sum to one
    rw [Finset.sum_congr rfl fun q _ => (hω q).variance_fun_comp (hhm k q.1)]
    simp only [hs]
    rw [sum_union_blocks hij]
    simp only [hhi, hhj, hFvar, hGvar, Finset.sum_const, card_range, nsmul_eq_mul]
    have := hNa0 k
    have := hNb0 k
    have := hσpos k
    field_simp
    rw [hσsq k]
    field_simp
  · -- Lindeberg's condition, from the tails of the two sample laws
    have hterm : ∀ k (q : ℕ × ℕ), ∫ x in {x | ε < |h k q.1 (ω q x)|}, h k q.1 (ω q x) ^ 2 ∂μ =
        ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (h k q.1 y) ∂ν := by
      intro k q
      rw [← integral_lindebergIntegrand (aemeasurable_comp_input hω (hhm k q.1) q) ε]
      exact integral_comp_of_measurePreserving (hω q)
        (f := fun y => {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (h k q.1 y))
        ((measurable_lindebergIntegrand ε).comp_aemeasurable (hhm k q.1)).aestronglyMeasurable
    have hFt : ∀ k, ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (F k y) ∂ν =
        ((Na k : ℝ) * σ k)⁻¹ ^ 2 * ∫ y, {z : ℝ | ε * (Na k * σ k) < |z|}.indicator
          (fun z => z ^ 2) (f y - m) ∂ν := by
      intro k
      simp only [hF]
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [lindebergIntegrand_const_mul (inv_pos.2 (mul_pos (hNa0 k) (hσpos k))), div_inv_eq_mul]
    have hGt : ∀ k, ∫ y, {z : ℝ | ε < |z|}.indicator (fun z => z ^ 2) (G k y) ∂ν =
        ((Nb k : ℝ) * σ k)⁻¹ ^ 2 * ∫ y, {z : ℝ | ε * (Nb k * σ k) < |z|}.indicator
          (fun z => z ^ 2) (m - g y) ∂ν := by
      intro k
      simp only [hG]
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [lindebergIntegrand_const_mul (inv_pos.2 (mul_pos (hNb0 k) (hσpos k))), div_inv_eq_mul]
    have hf2 : ∫ y, (f y - m) ^ 2 ∂ν = Vf := by
      rw [← hVf, variance_eq_integral hf.aemeasurable, hm]
    have hg2 : ∫ y, (m - g y) ^ 2 ∂ν = Vg := by
      rw [← hVg, variance_eq_integral hg.aemeasurable, hgm]
      congr 1
      funext y
      ring
    have hleF : ∀ k, ∫ y, (f y - m) ^ 2 ∂ν ≤ Na k * σ k ^ 2 := by
      intro k
      rw [hf2, hσsq k, mul_add, mul_div_cancel₀ _ (hNa0 k).ne']
      have := div_nonneg hVg0 (hNb0 k).le
      have := hNa0 k
      nlinarith
    have hleG : ∀ k, ∫ y, (m - g y) ^ 2 ∂ν ≤ Nb k * σ k ^ 2 := by
      intro k
      rw [hg2, hσsq k, mul_add, mul_div_cancel₀ _ (hNb0 k).ne']
      have := div_nonneg hVf0 (hNa0 k).le
      have := hNb0 k
      nlinarith
    have hA := tendsto_lindebergTail_div (g := fun y => f y - m) (hf.sub (memLp_const m)) hNa
      hσpos hleF hε
    have hB := tendsto_lindebergTail_div (g := fun y => m - g y) ((memLp_const m).sub hg) hNb
      hσpos hleG hε
    have hAB := hA.add hB
    rw [add_zero] at hAB
    refine hAB.congr fun k => ?_
    show _ = ∑ q ∈ s k, ∫ x in {x | ε < |h k q.1 (ω q x)|}, h k q.1 (ω q x) ^ 2 ∂μ
    simp only [hterm, hs]
    rw [sum_union_blocks hij]
    simp only [hhi, hhj, hFt, hGt, Finset.sum_const, card_range, nsmul_eq_mul]
    have := hNa0 k
    have := hNb0 k
    have := hσpos k
    field_simp

/-- **The two-sample central limit theorem** (for the consistency check of Giles 2015, §3.3,
p. 22: "to within the accuracy one would expect due to Monte Carlo sampling error").  Let the
inputs `ω^{(p)}` be independent with law `ν`, let `f, g` be square integrable with the same mean
and `V[f] + V[g] > 0`, and let `i ≠ j`.  If `N_a(k), N_b(k) → ∞` (at arbitrary rates), then
`(f̄_k − ḡ_k)/σ_k → N(0, 1)` in distribution, where `f̄_k` is the mean of `f(ω^{(i,n)})`,
`n < N_a(k)`, `ḡ_k` that of `g(ω^{(j,n)})`, `n < N_b(k)`, and `σ_k² = V[f]/N_a(k) + V[g]/N_b(k)`.
Only second moments are needed: the normalised samples form a triangular array that satisfies
Lindeberg's condition (`tendsto_lindebergTail_div`), and `tendstoInDistribution_lindeberg`
applies to the rows with `N_a, N_b ≥ 1`. -/
theorem tendstoInDistribution_twoSample [IsProbabilityMeasure μ] [IsProbabilityMeasure P']
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {f g : Ω₀ → ℝ} {i j : ℕ} (hij : i ≠ j) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hfg : ∫ y, f y ∂ν = ∫ y, g y ∂ν) (hpos : 0 < variance f ν + variance g ν)
    {Na Nb : ℕ → ℕ} (hNa : Tendsto Na atTop atTop) (hNb : Tendsto Nb atTop atTop) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k x => (empMean (fun n => f (ω (i, n) x)) (Na k) -
        empMean (fun n => g (ω (j, n) x)) (Nb k)) / √(variance f ν / Na k + variance g ν / Nb k))
      atTop Z (fun _ => μ) P' := by
  obtain ⟨k₀, hk₀⟩ :=
    ((hNa.eventually_gt_atTop 0).and (hNb.eventually_gt_atTop 0)).exists_forall_of_atTop
  exact tendstoInDistribution_of_comp_add k₀
    (fun k => ((aemeasurable_empMean_input hω hf.aemeasurable i _).sub
      (aemeasurable_empMean_input hω hg.aemeasurable j _)).div_const _)
    (tendstoInDistribution_twoSample_of_forall (Na := fun k => Na (k + k₀))
      (Nb := fun k => Nb (k + k₀)) hω hind hij hf hg hfg hpos
      (hNa.comp (tendsto_add_atTop_nat k₀)) (hNb.comp (tendsto_add_atTop_nat k₀))
      (fun k => (hk₀ (k + k₀) (Nat.le_add_left _ _)).1)
      (fun k => (hk₀ (k + k₀) (Nat.le_add_left _ _)).2) hZ)

/-- **The consistency statistic is asymptotically normal** (Giles 2015, §3.3, p. 22: "If `a, b, c`
are estimates for `E[P^f_{ℓ−1}], E[P^f_ℓ], E[Y_ℓ]`, respectively, then it should be true that
`a − b + c ≈ 0`. The consistency check verifies that this is true, to within the accuracy one
would expect due to Monte Carlo sampling error.").  The paper's levels `ℓ − 1, ℓ` are written
`ℓ, ℓ + 1`.  Let the inputs `ω^{(p)}` be independent with law `ν`; let `a` be the mean of
`P^f_ℓ(ω^{(ℓ,n)})`, `n < N_a(k)`, and `b, c` the means of `P^f_{ℓ+1}(ω^{(ℓ+1,n)})` and of
`Y = P^f_{ℓ+1} − P^c_ℓ` at the same inputs, `n < N_b(k)`.  If `P^f_ℓ, P^c_ℓ` are square
integrable, (2.4) holds (`E[P^f_ℓ] = E[P^c_ℓ]`), `V[P^f_ℓ] + V[P^c_ℓ] > 0` and
`N_a(k), N_b(k) → ∞` at arbitrary rates, then `(a − b + c)/σ_k → N(0, 1)` in distribution, where
`σ_k² = V[P^f_ℓ]/N_a(k) + V[P^c_ℓ]/N_b(k)` is the variance of `a − b + c`.  Indeed `a − b + c` is
the difference of the means of `P^f_ℓ` and `P^c_ℓ` (`empMean_sub_add`), and
`tendstoInDistribution_twoSample` applies.  No moment of `P^f_{ℓ+1}` is needed, and the
positivity of `V[P^f_ℓ] + V[P^c_ℓ]` only excludes `a − b + c = 0` almost surely. -/
theorem tendstoInDistribution_consistencyStat [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P'] (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ)
    {Pf Pc : ℕ → Ω₀ → ℝ} {ℓ : ℕ} (hPf : MemLp (Pf ℓ) 2 ν) (hPc : MemLp (Pc ℓ) 2 ν)
    (h24 : ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν) (hpos : 0 < variance (Pf ℓ) ν + variance (Pc ℓ) ν)
    {Na Nb : ℕ → ℕ} (hNa : Tendsto Na atTop atTop) (hNb : Tendsto Nb atTop atTop) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k x => (empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)) /
        √(variance (Pf ℓ) ν / Na k + variance (Pc ℓ) ν / Nb k))
      atTop Z (fun _ => μ) P' := by
  simp only [empMean_sub_add]
  exact tendstoInDistribution_twoSample hω hind (by omega) hPf hPc h24 hpos hNa hNb hZ

end TwoSample

/-! ### Gaussian tails -/

/-- For every `η > 0` there is `z ∈ (0, 3)` with `P(|Z| > z) < P(|Z| ≥ 3) + η`, `Z ~ N(0, 1)`
(continuity of the measure along `{|x| > 3 − 1/(n + 2)} ↓ {|x| ≥ 3}`; for Giles 2015, §3.3). -/
lemma exists_gaussianReal_lt_abs_lt {η : ℝ} (hη : 0 < η) :
    ∃ z, 0 < z ∧ z < 3 ∧
      (gaussianReal 0 1).real {x | z < |x|} < (gaussianReal 0 1).real {x | 3 ≤ |x|} + η := by
  set s : ℕ → Set ℝ := fun n => {x | 3 - ((n : ℝ) + 2)⁻¹ < |x|} with hs
  have hmeas : ∀ n, MeasurableSet (s n) := fun n =>
    measurableSet_lt measurable_const measurable_abs
  have hanti : Antitone s := by
    intro n n' hnn x hx
    simp only [hs, Set.mem_ofPred_eq] at hx ⊢
    have : ((n' : ℝ) + 2)⁻¹ ≤ ((n : ℝ) + 2)⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn 2)
    linarith
  have hinter : (⋂ n, s n) = {x | 3 ≤ |x|} := by
    ext x
    simp only [hs, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h
      by_contra hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (not_le.1 hx))
      have h1 := h n
      have h2 : ((n : ℝ) + 2)⁻¹ ≤ 1 / ((n : ℝ) + 1) := by
        rw [one_div]
        exact inv_anti₀ (by positivity) (by linarith)
      linarith
    · intro h n
      have : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
      linarith
  have h := tendsto_measure_iInter_atTop (μ := gaussianReal 0 1)
    (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at h
  have h' := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  obtain ⟨n, hn⟩ := (h'.eventually_lt_const (lt_add_of_pos_right _ hη)).exists
  refine ⟨3 - ((n : ℝ) + 2)⁻¹, ?_, ?_, hn⟩
  · have : ((n : ℝ) + 2)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
    linarith
  · have : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
    linarith

/-- `P(|Z| ≥ 3) = P(|Z| > 3)` for `Z ~ N(0, 1)`, which has no atoms (Giles 2015, §3.3: "less than
0.3%"). -/
lemma measureReal_gaussianReal_le_abs_eq :
    (gaussianReal 0 1).real {x | 3 ≤ |x|} = (gaussianReal 0 1).real {x | 3 < |x|} := by
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  refine le_antisymm ?_ (measureReal_mono fun x (hx : (3 : ℝ) < |x|) => (hx.le : (3 : ℝ) ≤ |x|))
  have hsub : {x : ℝ | 3 ≤ |x|} ⊆ {x | 3 < |x|} ∪ {3, -3} := by
    intro x hx
    rcases (show (3 : ℝ) ≤ |x| from hx).lt_or_eq with h | h
    · exact Or.inl h
    · right
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 3) |>.1 h.symm with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
  calc (gaussianReal 0 1).real {x | 3 ≤ |x|}
      ≤ (gaussianReal 0 1).real ({x | 3 < |x|} ∪ {3, -3}) := measureReal_mono hsub
    _ ≤ (gaussianReal 0 1).real {x | 3 < |x|} + (gaussianReal 0 1).real {3, -3} :=
        measureReal_union_le _ _
    _ = (gaussianReal 0 1).real {x | 3 < |x|} := by
        rw [measureReal_def (gaussianReal 0 1) ({3, -3} : Set ℝ),
          (Set.toFinite ({3, -3} : Set ℝ)).measure_zero (gaussianReal 0 1), ENNReal.toReal_zero,
          add_zero]

/-- For every `η > 0` there is `z > 3` with `P(|Z| > z) > P(|Z| ≥ 3) − η`, `Z ~ N(0, 1)`
(continuity of the measure along `{|x| > 3 + 1/(n + 1)} ↑ {|x| > 3}`; for Giles 2015, §3.3). -/
lemma exists_gaussianReal_lt_abs_gt {η : ℝ} (hη : 0 < η) :
    ∃ z, 3 < z ∧
      (gaussianReal 0 1).real {x | 3 ≤ |x|} - η < (gaussianReal 0 1).real {x | z < |x|} := by
  set s : ℕ → Set ℝ := fun n => {x | 3 + ((n : ℝ) + 1)⁻¹ < |x|} with hs
  have hmono : Monotone s := by
    intro n n' hnn x hx
    simp only [hs, Set.mem_ofPred_eq] at hx ⊢
    have : ((n' : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hnn 1)
    linarith
  have hunion : (⋃ n, s n) = {x | 3 < |x|} := by
    ext x
    simp only [hs, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      refine ⟨n, ?_⟩
      rw [one_div] at hn
      linarith
  have h := tendsto_measure_iUnion_atTop (μ := gaussianReal 0 1) hmono
  rw [hunion] at h
  have h' := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  rw [measureReal_gaussianReal_le_abs_eq]
  obtain ⟨n, hn⟩ := (h'.eventually_const_lt (sub_lt_self _ hη)).exists
  have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  exact ⟨3 + ((n : ℝ) + 1)⁻¹, by linarith, hn⟩

/-! ### Limits of probabilities -/

section Limit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- If `S_k → N(0, 1)` in distribution then `P(|S_k| > z) → P(|Z| > z)` for every `z ≥ 0`, where
`Z ~ N(0, 1)` (the complement of `tendsto_measureReal_abs_le_of_tendstoInDistribution`). -/
lemma tendsto_measureReal_lt_abs {S : ℕ → Ω → ℝ}
    (hS : TendstoInDistribution S atTop id (fun _ => μ) (gaussianReal 0 1)) {z : ℝ}
    (hz : 0 ≤ z) :
    Tendsto (fun k => μ.real {x | z < |S k x|}) atTop
      (𝓝 ((gaussianReal 0 1).real {x | z < |x|})) := by
  have h := tendsto_measureReal_abs_le_of_tendstoInDistribution hS HasLaw.id hz
  have hG : (gaussianReal 0 1).real {x | z < |x|} = 1 - (2 * cdf (gaussianReal 0 1) z - 1) := by
    rw [← measureReal_gaussianReal_Icc_neg hz, ← probReal_compl_eq_one_sub measurableSet_Icc]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
  rw [hG]
  refine (tendsto_const_nhds.sub h).congr fun k => ?_
  have hnm : NullMeasurableSet {x | |S k x| ≤ z} μ :=
    nullMeasurableSet_le (hS.forall_aemeasurable k).abs aemeasurable_const
  rw [← probReal_compl_eq_one_sub₀ hnm]
  congr 1
  ext x
  simp

/-- Variance estimates that do not underestimate asymptotically: if `V ≥ 0`, `N_k → ∞` and
`P(N_k W_k < c) → 0` for every `c < V`, then `P(√W_k < θ √(V/N_k)) → 0` for every
`0 ≤ θ < 1`.  For `V = 0` the event is empty; for `V > 0` it is contained in
`{N_k W_k < θ² V}` once `N_k ≥ 1`. -/
lemma tendsto_measureReal_sqrt_lt {W : ℕ → Ω → ℝ} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {V : ℝ} (hV : 0 ≤ V)
    (hW : ∀ c < V, Tendsto (fun k => μ.real {x | N k * W k x < c}) atTop (𝓝 0))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    Tendsto (fun k => μ.real {x | √(W k x) < θ * √(V / N k)}) atTop (𝓝 0) := by
  rcases hV.eq_or_lt with hV0 | hVpos
  · refine tendsto_const_nhds.congr fun k => ?_
    have he : {x | √(W k x) < θ * √(V / N k)} = ∅ := by
      ext x
      simp only [← hV0, zero_div, Real.sqrt_zero, mul_zero, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_lt]
      exact Real.sqrt_nonneg _
    rw [he, measureReal_empty]
  · have hθ2 : θ ^ 2 < 1 := by nlinarith
    have hc : θ ^ 2 * V < V := by
      simpa using mul_lt_mul_of_pos_right hθ2 hVpos
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hW _ hc)
      (Eventually.of_forall fun k => measureReal_nonneg) ?_
    filter_upwards [hN.eventually_gt_atTop 0] with k hk
    refine measureReal_mono fun x hx => ?_
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hNk : (0 : ℝ) < N k := Nat.cast_pos.2 hk
    have ht : 0 < θ * √(V / N k) := (Real.sqrt_nonneg _).trans_lt hx
    rw [Real.sqrt_lt' ht, mul_pow, Real.sq_sqrt (div_nonneg hV hNk.le), mul_div_assoc'] at hx
    rw [lt_div_iff₀ hNk] at hx
    linarith

end Limit

/-! ### The consistency check with estimated variances -/

section Check

variable {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] {ν : Measure Ω₀}
  {μ : Measure Ω} {ω : ℕ × ℕ → Ω → Ω₀}

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
lemma sqrt_add_le_add_sqrt_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), add_sq,
    Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- The two-sample consistency check with an arbitrary estimate `S_k` of the sum of the standard
deviations of the two means (the common core of `consistency_check_of_variance_estimates` and
`consistency_check_of_empVar_le`; Giles 2015, §3.3, p. 22).  Let the inputs `ω^{(p)}` be
independent with law `ν`, let `f, g` be square integrable with the same mean, `i ≠ j` and
`N_a(k), N_b(k) → ∞`; let `f̄_k` be the mean of `f(ω^{(i,n)})`, `n < N_a(k)`, and `ḡ_k` that of
`g(ω^{(j,n)})`, `n < N_b(k)`.  If `S_k` does not underestimate `√(V[f]/N_a) + √(V[g]/N_b)`
asymptotically, `P(S_k < θ(√(V[f]/N_a) + √(V[g]/N_b))) → 0` for every `0 ≤ θ < 1`, then for every
`η > 0`, eventually `P(3 S_k < |f̄_k − ḡ_k|) < P(|Z| ≥ 3) + η`, `Z ~ N(0, 1)`.  If
`V[f] = V[g] = 0` then `f̄_k = ḡ_k` almost surely, and the event needs `S_k < 0` (`θ = 0`).
Otherwise `T_k = (f̄_k − ḡ_k)/σ_k → N(0, 1)` (`tendstoInDistribution_twoSample`), and as
`σ_k ≤ √(V[f]/N_a) + √(V[g]/N_b)` the event is contained in
`{|T_k| > z} ∪ {S_k < θ(√(V[f]/N_a) + √(V[g]/N_b))}` for `θ = z/3 < 1`, with `z < 3` chosen by
`exists_gaussianReal_lt_abs_lt`. -/
lemma consistency_check_of_sd_estimate [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {f g : Ω₀ → ℝ} {i j : ℕ}
    (hij : i ≠ j) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) (hfg : ∫ y, f y ∂ν = ∫ y, g y ∂ν)
    {Na Nb : ℕ → ℕ} (hNa : Tendsto Na atTop atTop) (hNb : Tendsto Nb atTop atTop)
    {S : ℕ → Ω → ℝ}
    (hS : ∀ θ, 0 ≤ θ → θ < 1 → Tendsto (fun k => μ.real
      {x | S k x < θ * (√(variance f ν / Na k) + √(variance g ν / Nb k))}) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, μ.real {x | 3 * S k x <
      |empMean (fun n => f (ω (i, n) x)) (Na k) - empMean (fun n => g (ω (j, n) x)) (Nb k)|} <
      (gaussianReal 0 1).real {z | 3 ≤ |z|} + η := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  have hG0 : 0 ≤ (gaussianReal 0 1).real {z : ℝ | 3 ≤ |z|} := measureReal_nonneg
  obtain ⟨Vf, hVf⟩ : ∃ V, variance f ν = V := ⟨_, rfl⟩
  obtain ⟨Vg, hVg⟩ : ∃ V, variance g ν = V := ⟨_, rfl⟩
  have hVf0 : 0 ≤ Vf := hVf ▸ variance_nonneg _ _
  have hVg0 : 0 ≤ Vg := hVg ▸ variance_nonneg _ _
  rw [hVf, hVg] at hS
  rcases (add_nonneg hVf0 hVg0).eq_or_lt with hdeg | hpos
  · -- degenerate case: `f, g` are a.s. constant, and `f̄_k = ḡ_k` a.s.
    have hfa := ae_eq_integral_of_variance_eq_zero hf (by linarith)
    have hga := ae_eq_integral_of_variance_eq_zero hg (by linarith)
    have hae : ∀ᵐ x ∂μ, ∀ n, f (ω (i, n) x) = ∫ y, f y ∂ν ∧ g (ω (j, n) x) = ∫ y, f y ∂ν := by
      rw [ae_all_iff]
      intro n
      filter_upwards [(hω (i, n)).quasiMeasurePreserving.ae hfa,
        (hω (j, n)).quasiMeasurePreserving.ae hga] with x h1 h2
      exact ⟨h1, h2.trans hfg.symm⟩
    have hbad : μ.real {x | ¬ ∀ n, f (ω (i, n) x) = ∫ y, f y ∂ν ∧
        g (ω (j, n) x) = ∫ y, f y ∂ν} = 0 := by
      rw [measureReal_def, ae_iff.1 hae, ENNReal.toReal_zero]
    filter_upwards [(hS 0 le_rfl one_pos).eventually_lt_const hη, hNa.eventually_gt_atTop 0,
      hNb.eventually_gt_atTop 0] with k hk hka hkb
    have hsub : {x | 3 * S k x <
        |empMean (fun n => f (ω (i, n) x)) (Na k) - empMean (fun n => g (ω (j, n) x)) (Nb k)|} ⊆
        {x | S k x < 0 * (√(Vf / Na k) + √(Vg / Nb k))} ∪
          {x | ¬ ∀ n, f (ω (i, n) x) = ∫ y, f y ∂ν ∧ g (ω (j, n) x) = ∫ y, f y ∂ν} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
      by_cases hgood : ∀ n, f (ω (i, n) x) = ∫ y, f y ∂ν ∧ g (ω (j, n) x) = ∫ y, f y ∂ν
      · left
        have e1 : (fun n => f (ω (i, n) x)) = fun _ => ∫ y, f y ∂ν :=
          funext fun n => (hgood n).1
        have e2 : (fun n => g (ω (j, n) x)) = fun _ => ∫ y, f y ∂ν :=
          funext fun n => (hgood n).2
        rw [e1, e2, empMean_const _ hka, empMean_const _ hkb, sub_self, abs_zero] at hx
        rw [zero_mul]
        linarith
      · exact Or.inr hgood
    have hu := measureReal_union_le (μ := μ) {x | S k x < 0 * (√(Vf / Na k) + √(Vg / Nb k))}
      {x | ¬ ∀ n, f (ω (i, n) x) = ∫ y, f y ∂ν ∧ g (ω (j, n) x) = ∫ y, f y ∂ν}
    have hm := measureReal_mono (μ := μ) hsub
    linarith
  · -- non-degenerate case: the central limit theorem and the estimate `S_k`
    have hη3 : 0 < η / 3 := by positivity
    obtain ⟨z, hz0, hz3, hzG⟩ := exists_gaussianReal_lt_abs_lt hη3
    obtain ⟨θ, hθ⟩ : ∃ θ, θ = z / 3 := ⟨_, rfl⟩
    have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
    have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by norm_num)]; exact hz3
    have hzθ : z = 3 * θ := by rw [hθ]; ring
    obtain ⟨T, hT⟩ : ∃ T : ℕ → Ω → ℝ, T = fun k x => (empMean (fun n => f (ω (i, n) x)) (Na k)
        - empMean (fun n => g (ω (j, n) x)) (Nb k)) / √(Vf / Na k + Vg / Nb k) := ⟨_, rfl⟩
    have hTd : TendstoInDistribution T atTop id (fun _ => μ) (gaussianReal 0 1) := by
      have h := tendstoInDistribution_twoSample hω hind hij hf hg hfg (by rwa [hVf, hVg]) hNa
        hNb (HasLaw.id (μ := gaussianReal 0 1))
      rwa [hVf, hVg, ← hT] at h
    have h1 := tendsto_measureReal_lt_abs hTd hz0.le
    filter_upwards [h1.eventually_lt_const (lt_add_of_pos_right _ hη3),
      (hS θ hθ0 hθ1).eventually_lt_const hη3, hNa.eventually_gt_atTop 0,
      hNb.eventually_gt_atTop 0] with k hk1 hk2 hka hkb
    have hNa0 : (0 : ℝ) < Na k := Nat.cast_pos.2 hka
    have hNb0 : (0 : ℝ) < Nb k := Nat.cast_pos.2 hkb
    have hs2 : 0 < Vf / Na k + Vg / Nb k := by
      have h1 := div_nonneg hVf0 hNa0.le
      have h2 := div_nonneg hVg0 hNb0.le
      rcases hVf0.eq_or_lt with h | h
      · have := div_pos (show 0 < Vg by linarith) hNb0
        linarith
      · have := div_pos h hNa0
        linarith
    have hσ := Real.sqrt_pos.2 hs2
    -- `σ_k ≤ √(V[f]/N_a) + √(V[g]/N_b)`
    have hR := sqrt_add_le_add_sqrt_of_nonneg (div_nonneg hVf0 hNa0.le) (div_nonneg hVg0 hNb0.le)
    have hsub : {x | 3 * S k x <
        |empMean (fun n => f (ω (i, n) x)) (Na k) - empMean (fun n => g (ω (j, n) x)) (Nb k)|} ⊆
        {x | z < |T k x|} ∪ {x | S k x < θ * (√(Vf / Na k) + √(Vg / Nb k))} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
      by_cases hs : S k x < θ * (√(Vf / Na k) + √(Vg / Nb k))
      · exact Or.inr hs
      refine Or.inl ?_
      rw [hT]
      dsimp only
      rw [abs_div, abs_of_pos hσ, lt_div_iff₀ hσ]
      calc z * √(Vf / Na k + Vg / Nb k)
          ≤ z * (√(Vf / Na k) + √(Vg / Nb k)) := mul_le_mul_of_nonneg_left hR hz0.le
        _ = 3 * (θ * (√(Vf / Na k) + √(Vg / Nb k))) := by
            rw [hzθ]
            ring
        _ ≤ 3 * S k x := by linarith [not_lt.1 hs]
        _ < _ := hx
    have hu := measureReal_union_le (μ := μ) {x | z < |T k x|}
      {x | S k x < θ * (√(Vf / Na k) + √(Vg / Nb k))}
    have hm := measureReal_mono (μ := μ) hsub
    linarith

/-- **The consistency check with estimated variances fails with asymptotic probability at most
`P(|Z| ≥ 3)`** (Giles 2015, §3.3, p. 22: "Since `√V[a − b + c] ≤ √V[a] + √V[b] + √V[c]` it computes
and plots the ratio `|a − b + c| / (3(√V_a + √V_b + √V_c))` where `V_a, V_b, V_c` are empirical
estimates for the variances of `a, b, c`. The probability of this ratio being greater than unity
is less than 0.3%.").  Setting of `tendstoInDistribution_consistencyStat` (the paper's levels
`ℓ − 1, ℓ` written `ℓ, ℓ + 1`): `P^f_ℓ, P^f_{ℓ+1}, P^c_ℓ` are square integrable, (2.4)
`E[P^f_ℓ] = E[P^c_ℓ]` holds and `N_a(k), N_b(k) → ∞` at arbitrary rates.  Let `V_a, V_b, V_c` be
any random estimates of the variances `V[P^f_ℓ]/N_a`, `V[P^f_{ℓ+1}]/N_b`, `V[Y]/N_b` of `a, b, c`
that do not underestimate asymptotically: `P(N_a V_a < c') → 0` for every `c' < V[P^f_ℓ]`, and
likewise for `V_b`, `V_c` (this holds if `N_a V_a → V[P^f_ℓ]` in probability, etc.).  Then for
every `η > 0`, eventually in `k` the probability that the check fails,
`P(3(√V_a + √V_b + √V_c) < |a − b + c|)` (the ratio exceeds unity), is less than
`P(|Z| ≥ 3) + η`, `Z ~ N(0, 1)`.  The square integrability of `P^f_{ℓ+1}` makes the targets
`V[P^f_{ℓ+1}]`, `V[Y]` of the hypotheses meaningful (they are not junk values).

No non-degeneracy is assumed.  Proof: `a − b + c` is the difference of the means of `P^f_ℓ` and
`P^c_ℓ` (`empMean_sub_add`), and `consistency_check_of_sd_estimate` applies to
`S_k = √V_a + √V_b + √V_c`: by the paper's inequality for the true variances,
`√V[P^c_ℓ] ≤ √V[P^f_{ℓ+1}] + √V[Y]` (`sqrt_variance_sub_le`), `S_k` can only fall below `θ` times
`√(V[P^f_ℓ]/N_a) + √(V[P^c_ℓ]/N_b)` if one of the estimates is below `θ²` times its target
(`tendsto_measureReal_sqrt_lt`).  The statement is asymptotic: for fixed sample sizes the bound
`0.3%` can fail (module docstring). -/
theorem consistency_check_of_variance_estimates [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {Pf Pc : ℕ → Ω₀ → ℝ}
    {ℓ : ℕ} (hPf₀ : MemLp (Pf ℓ) 2 ν) (hPf₁ : MemLp (Pf (ℓ + 1)) 2 ν) (hPc : MemLp (Pc ℓ) 2 ν)
    (h24 : ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν) {Na Nb : ℕ → ℕ} (hNa : Tendsto Na atTop atTop)
    (hNb : Tendsto Nb atTop atTop) {Va Vb Vc : ℕ → Ω → ℝ}
    (hVa : ∀ c < variance (Pf ℓ) ν,
      Tendsto (fun k => μ.real {x | Na k * Va k x < c}) atTop (𝓝 0))
    (hVb : ∀ c < variance (Pf (ℓ + 1)) ν,
      Tendsto (fun k => μ.real {x | Nb k * Vb k x < c}) atTop (𝓝 0))
    (hVc : ∀ c < variance (fun y => Pf (ℓ + 1) y - Pc ℓ y) ν,
      Tendsto (fun k => μ.real {x | Nb k * Vc k x < c}) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, μ.real {x | 3 * (√(Va k x) + √(Vb k x) + √(Vc k x)) <
      |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)|} <
      (gaussianReal 0 1).real {z | 3 ≤ |z|} + η := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  simp only [empMean_sub_add]
  refine consistency_check_of_sd_estimate (S := fun k x => √(Va k x) + √(Vb k x) + √(Vc k x))
    hω hind (by omega) hPf₀ hPc h24 hNa hNb (fun θ hθ0 hθ1 => ?_) hη
  obtain ⟨Vf, hVf⟩ : ∃ V, variance (Pf ℓ) ν = V := ⟨_, rfl⟩
  obtain ⟨Vc', hVc'⟩ : ∃ V, variance (Pc ℓ) ν = V := ⟨_, rfl⟩
  obtain ⟨Vb', hVb'⟩ : ∃ V, variance (Pf (ℓ + 1)) ν = V := ⟨_, rfl⟩
  obtain ⟨Vy, hVy⟩ : ∃ V, variance (fun y => Pf (ℓ + 1) y - Pc ℓ y) ν = V := ⟨_, rfl⟩
  -- the standard deviations: `√V[P^c_{ℓ−1}] ≤ √V[P^f_ℓ] + √V[Y_ℓ]`
  have hsd : √Vc' ≤ √Vb' + √Vy := by
    have h := sqrt_variance_sub_le (Y := fun y => Pf (ℓ + 1) y - Pc ℓ y) hPf₁ (hPf₁.sub hPc)
    simp only [sub_sub_cancel] at h
    rwa [hVc', hVb', hVy] at h
  rw [hVf, hVc']
  rw [hVf] at hVa
  rw [hVb'] at hVb
  rw [hVy] at hVc
  have hABC := ((tendsto_measureReal_sqrt_lt hNa (hVf ▸ variance_nonneg _ _) hVa hθ0 hθ1).add
    (tendsto_measureReal_sqrt_lt hNb (hVb' ▸ variance_nonneg _ _) hVb hθ0 hθ1)).add
    (tendsto_measureReal_sqrt_lt hNb (hVy ▸ variance_nonneg _ _) hVc hθ0 hθ1)
  rw [add_zero, add_zero] at hABC
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hABC
    (fun k => measureReal_nonneg) (fun k => ?_)
  have hsdk : √(Vc' / Nb k) ≤ √(Vb' / Nb k) + √(Vy / Nb k) := by
    rw [Real.sqrt_div' _ (Nat.cast_nonneg _), Real.sqrt_div' _ (Nat.cast_nonneg _),
      Real.sqrt_div' _ (Nat.cast_nonneg _), ← add_div]
    exact div_le_div_of_nonneg_right hsd (Real.sqrt_nonneg _)
  have hθsd := mul_le_mul_of_nonneg_left hsdk hθ0
  have hsub : {x | √(Va k x) + √(Vb k x) + √(Vc k x) < θ * (√(Vf / Na k) + √(Vc' / Nb k))} ⊆
      ({x | √(Va k x) < θ * √(Vf / Na k)} ∪ {x | √(Vb k x) < θ * √(Vb' / Nb k)}) ∪
        {x | √(Vc k x) < θ * √(Vy / Nb k)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    by_contra hno
    simp only [not_or, not_lt] at hno
    obtain ⟨⟨ha, hb⟩, hc⟩ := hno
    linarith
  have hu1 := measureReal_union_le (μ := μ) {x | √(Va k x) < θ * √(Vf / Na k)}
    {x | √(Vb k x) < θ * √(Vb' / Nb k)}
  have hu2 := measureReal_union_le (μ := μ)
    ({x | √(Va k x) < θ * √(Vf / Na k)} ∪ {x | √(Vb k x) < θ * √(Vb' / Nb k)})
    {x | √(Vc k x) < θ * √(Vy / Nb k)}
  have hm := measureReal_mono (μ := μ) hsub
  dsimp only
  linarith

/-- The empirical variance of `N` independent samples `g(ω^{(i,n)})` with law `ν` tends to `V[g]` in
probability (`tendstoInMeasure_empVar`; Giles 2015, §3.3). -/
lemma tendstoInMeasure_empVar_input [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {g : Ω₀ → ℝ}
    (hg : MemLp g 2 ν) (i : ℕ) :
    TendstoInMeasure μ (fun N x => empVar (fun n => g (ω (i, n) x)) N) atTop
      (fun _ => variance g ν) := by
  have hgm : AEMeasurable g ν := hg.aestronglyMeasurable.aemeasurable
  have hind' : iIndepFun (fun n x => g (ω (i, n) x)) μ :=
    iIndepFun_comp_inputs hω hind (e := fun n => (i, n)) (fun a b h => by simpa using h)
      (g := fun _ => g) fun _ => hgm
  have hgl : HasLaw g (ν.map g) ν := ⟨hgm, rfl⟩
  have hident : ∀ n, IdentDistrib (fun x => g (ω (i, n) x)) (fun x => g (ω (i, 0) x)) μ μ :=
    fun n => (hgl.fun_comp (hω (i, n)).hasLaw).identDistrib (hgl.fun_comp (hω (i, 0)).hasLaw)
  have hvar : variance (fun x => g (ω (i, 0) x)) μ = variance g ν :=
    (hω (i, 0)).variance_fun_comp hgm
  rw [← hvar]
  exact tendstoInMeasure_empVar (X := fun n x => g (ω (i, n) x))
    (hg.comp_measurePreserving (hω (i, 0))) (fun a b hab => hind'.indepFun hab) hident

/-- The empirical variance of `N` independent samples `g(ω^{(i,n)})` underestimates `V[g]` with
vanishing probability: `P(s_N² < c) → 0` for every `c < V[g]` (Giles 2015, §3.3). -/
lemma tendsto_measureReal_empVar_lt [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {g : Ω₀ → ℝ}
    (hg : MemLp g 2 ν) (i : ℕ) {c : ℝ} (hc : c < variance g ν) :
    Tendsto (fun N => μ.real {x | empVar (fun n => g (ω (i, n) x)) N < c}) atTop (𝓝 0) := by
  have hm := tendstoInMeasure_empVar_input hω hind hg i
  rw [tendstoInMeasure_iff_measureReal_dist] at hm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hm (variance g ν - c) (sub_pos.2 hc)) (fun N => measureReal_nonneg)
    (fun N => measureReal_mono fun x hx => ?_)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [Real.dist_eq, abs_sub_comm]
  exact (by linarith : variance g ν - c ≤ variance g ν - empVar (fun n => g (ω (i, n) x)) N).trans
    (le_abs_self _)

/-- The empirical variance of `N` independent samples `g(ω^{(i,n)})` overestimates `V[g]` with
vanishing probability: `P(s_N² > c) → 0` for every `c > V[g]` (Giles 2015, §3.3). -/
lemma tendsto_measureReal_lt_empVar [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {g : Ω₀ → ℝ}
    (hg : MemLp g 2 ν) (i : ℕ) {c : ℝ} (hc : variance g ν < c) :
    Tendsto (fun N => μ.real {x | c < empVar (fun n => g (ω (i, n) x)) N}) atTop (𝓝 0) := by
  have hm := tendstoInMeasure_empVar_input hω hind hg i
  rw [tendstoInMeasure_iff_measureReal_dist] at hm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hm (c - variance g ν) (sub_pos.2 hc)) (fun N => measureReal_nonneg)
    (fun N => measureReal_mono fun x hx => ?_)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [Real.dist_eq]
  exact (by linarith : c - variance g ν ≤ empVar (fun n => g (ω (i, n) x)) N - variance g ν).trans
    (le_abs_self _)

/-- Estimates at least as large as the empirical variance of the mean, `W_k ≥ s²_{N_k}/N_k` almost
surely for all large `k`, do not underestimate asymptotically: `P(N_k W_k < c) → 0` for every
`c < V[g]` when `N_k → ∞` (Giles 2015, §3.3). -/
lemma tendsto_measureReal_mul_lt_of_empVar_le [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {g : Ω₀ → ℝ}
    (hg : MemLp g 2 ν) (i : ℕ) {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {W : ℕ → Ω → ℝ}
    (hW : ∀ᶠ k in atTop, ∀ᵐ x ∂μ, empVar (fun n => g (ω (i, n) x)) (N k) / N k ≤ W k x) :
    ∀ c < variance g ν, Tendsto (fun k => μ.real {x | N k * W k x < c}) atTop (𝓝 0) := by
  intro c hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_measureReal_empVar_lt hω hind hg i hc).comp hN)
    (Eventually.of_forall fun k => measureReal_nonneg) ?_
  filter_upwards [hN.eventually_gt_atTop 0, hW] with k hk hkW
  have hNk : (0 : ℝ) < N k := Nat.cast_pos.2 hk
  have hsub : {x | N k * W k x < c} ⊆ {x | empVar (fun n => g (ω (i, n) x)) (N k) < c} ∪
      {x | ¬ empVar (fun n => g (ω (i, n) x)) (N k) / N k ≤ W k x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    by_cases h : empVar (fun n => g (ω (i, n) x)) (N k) / N k ≤ W k x
    · left
      have h' := mul_le_mul_of_nonneg_left h hNk.le
      rw [mul_div_cancel₀ _ hNk.ne'] at h'
      linarith
    · exact Or.inr h
  have h0 : μ.real {x | ¬ empVar (fun n => g (ω (i, n) x)) (N k) / N k ≤ W k x} = 0 := by
    rw [measureReal_def, ae_iff.1 hkW, ENNReal.toReal_zero]
  have hu := measureReal_union_le (μ := μ) {x | empVar (fun n => g (ω (i, n) x)) (N k) < c}
    {x | ¬ empVar (fun n => g (ω (i, n) x)) (N k) / N k ≤ W k x}
  have hm := measureReal_mono (μ := μ) hsub
  show μ.real _ ≤ μ.real {x | empVar (fun n => g (ω (i, n) x)) (N k) < c}
  linarith

/-- **The consistency check with variance estimates at least the empirical ones** (Giles 2015,
§3.3, p. 22: "it computes and plots the ratio `|a − b + c| / (3(√V_a + √V_b + √V_c))` where
`V_a, V_b, V_c` are empirical estimates for the variances of `a, b, c`. The probability of this
ratio being greater than unity is less than 0.3%.").  The paper's levels `ℓ − 1, ℓ` are written
`ℓ, ℓ + 1`.  Let the inputs `ω^{(p)}` be independent with law `ν`, let `P^f_ℓ, P^c_ℓ` be square
integrable with (2.4), `E[P^f_ℓ] = E[P^c_ℓ]`, and let `N_a(k), N_b(k) → ∞` at arbitrary rates.
Let `V_a ≥ s_a²/N_a`, `V_b ≥ s_b²/N_b` and `V_c ≥ s_c²/N_b` almost surely for all large `k`, where
`s_a², s_b², s_c²` are the empirical variances (`empVar`) of the samples of `P^f_ℓ`, `P^f_{ℓ+1}`
and `Y = P^f_{ℓ+1} − P^c_ℓ`.  Then for every `η > 0`, eventually
`P(3(√V_a + √V_b + √V_c) < |a − b + c|) < P(|Z| ≥ 3) + η`, `Z ~ N(0, 1)`.  This covers the
unbiased estimates `V_a = S_a²/N_a = s_a²/(N_a − 1)`, where `S² = N s²/(N − 1)` is the unbiased
sample variance, and estimates floored from below, as the driver of §3.4 floors `Vl`.

No hypothesis on `P^f_{ℓ+1}` is needed, not even measurability (for a non-measurable `P^f_{ℓ+1}`,
`μ.real` of the event is its outer measure): `P^f_{ℓ+1}` cancels from `a − b + c`
(`empMean_sub_add`), and since `P^c_ℓ = P^f_{ℓ+1} − Y` sample by sample, the triangle inequality
for empirical standard deviations (`sqrt_empVar_div_sub_le`) gives `√V_b + √V_c ≥ √(s_d²/N_b)`,
`s_d²` the empirical variance of the samples of `P^c_ℓ`.  So `consistency_check_of_sd_estimate`
applies, the empirical variances of `P^f_ℓ` and `P^c_ℓ` being consistent
(`tendstoInMeasure_empVar`). -/
theorem consistency_check_of_empVar_le [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {Pf Pc : ℕ → Ω₀ → ℝ}
    {ℓ : ℕ} (hPf₀ : MemLp (Pf ℓ) 2 ν) (hPc : MemLp (Pc ℓ) 2 ν)
    (h24 : ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν) {Na Nb : ℕ → ℕ} (hNa : Tendsto Na atTop atTop)
    (hNb : Tendsto Nb atTop atTop) {Va Vb Vc : ℕ → Ω → ℝ}
    (hVa : ∀ᶠ k in atTop, ∀ᵐ x ∂μ, empVar (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) / Na k ≤ Va k x)
    (hVb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ,
      empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k ≤ Vb k x)
    (hVc : ∀ᶠ k in atTop, ∀ᵐ x ∂μ,
      empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) / Nb k ≤
        Vc k x)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, μ.real {x | 3 * (√(Va k x) + √(Vb k x) + √(Vc k x)) <
      |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)|} <
      (gaussianReal 0 1).real {z | 3 ≤ |z|} + η := by
  simp only [empMean_sub_add]
  refine consistency_check_of_sd_estimate (S := fun k x => √(Va k x) + √(Vb k x) + √(Vc k x))
    hω hind (by omega) hPf₀ hPc h24 hNa hNb (fun θ hθ0 hθ1 => ?_) hη
  have hA := tendsto_measureReal_sqrt_lt hNa (variance_nonneg _ _)
    (tendsto_measureReal_mul_lt_of_empVar_le hω hind hPf₀ ℓ hNa hVa) hθ0 hθ1
  have hD := tendsto_measureReal_sqrt_lt hNb (variance_nonneg _ _)
    (tendsto_measureReal_mul_lt_of_empVar_le hω hind hPc (ℓ + 1) hNb
      (W := fun k x => empVar (fun n => Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) / Nb k)
      (Eventually.of_forall fun _ => ae_of_all _ fun _ => le_rfl)) hθ0 hθ1
  have hAD := hA.add hD
  rw [add_zero] at hAD
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAD
    (Eventually.of_forall fun k => measureReal_nonneg) ?_
  filter_upwards [hVb, hVc] with k hkb hkc
  have hE : μ.real {x | ¬ (empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k ≤ Vb k x ∧
      empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) / Nb k ≤
        Vc k x)} = 0 := by
    rw [measureReal_def, ae_iff.1 (hkb.and hkc), ENNReal.toReal_zero]
  have hsub : {x | √(Va k x) + √(Vb k x) + √(Vc k x) <
      θ * (√(variance (Pf ℓ) ν / Na k) + √(variance (Pc ℓ) ν / Nb k))} ⊆
      ({x | √(Va k x) < θ * √(variance (Pf ℓ) ν / Na k)} ∪
        {x | √(empVar (fun n => Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) / Nb k) <
          θ * √(variance (Pc ℓ) ν / Nb k)}) ∪
      {x | ¬ (empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k ≤ Vb k x ∧
        empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) / Nb k ≤
          Vc k x)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    by_contra hno
    simp only [not_or, not_lt, not_not] at hno
    obtain ⟨⟨ha, hd⟩, hb, hc⟩ := hno
    -- `√(s_d²/N_b) ≤ √(s_b²/N_b) + √(s_c²/N_b) ≤ √V_b + √V_c`
    have htri := sqrt_empVar_div_sub_le (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x))
      (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)
    simp only [sub_sub_cancel] at htri
    have h1 := Real.sqrt_le_sqrt hb
    have h2 := Real.sqrt_le_sqrt hc
    linarith
  have hu1 := measureReal_union_le (μ := μ) {x | √(Va k x) < θ * √(variance (Pf ℓ) ν / Na k)}
    {x | √(empVar (fun n => Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) / Nb k) <
      θ * √(variance (Pc ℓ) ν / Nb k)}
  have hu2 := measureReal_union_le (μ := μ)
    ({x | √(Va k x) < θ * √(variance (Pf ℓ) ν / Na k)} ∪
      {x | √(empVar (fun n => Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) / Nb k) <
        θ * √(variance (Pc ℓ) ν / Nb k)})
    {x | ¬ (empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k ≤ Vb k x ∧
      empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) / Nb k ≤
        Vc k x)}
  have hm := measureReal_mono (μ := μ) hsub
  linarith

/-- **The consistency check with empirical variances, asymptotically** (Giles 2015, §3.3, p. 22: "If
`a, b, c` are estimates for `E[P^f_{ℓ−1}], E[P^f_ℓ], E[Y_ℓ]`, respectively, then it should be true
that `a − b + c ≈ 0`. … Since `√V[a − b + c] ≤ √V[a] + √V[b] + √V[c]` it computes and plots the
ratio `|a − b + c| / (3(√V_a + √V_b + √V_c))` where `V_a, V_b, V_c` are empirical estimates for
the variances of `a, b, c`. The probability of this ratio being greater than unity is less than
0.3%.").  The paper's levels `ℓ − 1, ℓ` are written `ℓ, ℓ + 1`.  Let the inputs `ω^{(p)}` be
independent with law `ν`, let `P^f_ℓ, P^c_ℓ` be square integrable with (2.4),
`E[P^f_ℓ] = E[P^c_ℓ]`, and let `N_a(k), N_b(k) → ∞` at arbitrary rates.  Let `a` be the mean of
the `N_a(k)` samples `P^f_ℓ(ω^{(ℓ,n)})`, and `b, c` the means of `P^f_{ℓ+1}(ω^{(ℓ+1,n)})` and of
`Y = P^f_{ℓ+1} − P^c_ℓ` at the same `N_b(k)` inputs; let `V_a = s_a²/N_a`, `V_b = s_b²/N_b`,
`V_c = s_c²/N_b` with the empirical variances `s² = N⁻¹ ∑ (x_n − x̄)²` of these samples (`empVar`).
Then for every `η > 0`, eventually in `k`,
`P(3(√V_a + √V_b + √V_c) < |a − b + c|) < P(|Z| ≥ 3) + η` for `Z ~ N(0, 1)`: the ratio exceeds
unity with asymptotic probability at most `P(|Z| ≥ 3) ≈ 0.0027`.  The event is stated without
division (a zero denominator with `a − b + c ≠ 0` counts as a failure).  No non-degeneracy
hypothesis is needed, and no hypothesis on `P^f_{ℓ+1}` (`consistency_check_of_empVar_le`; in
the paper all three outputs are square integrable).  The statement is asymptotic, as the bound
fails for small samples (module docstring); the bound is attained in the limit for some outputs
(`consistency_check_empirical_sharp`). -/
theorem consistency_check_empirical [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {Pf Pc : ℕ → Ω₀ → ℝ}
    {ℓ : ℕ} (hPf₀ : MemLp (Pf ℓ) 2 ν) (hPc : MemLp (Pc ℓ) 2 ν)
    (h24 : ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν) {Na Nb : ℕ → ℕ} (hNa : Tendsto Na atTop atTop)
    (hNb : Tendsto Nb atTop atTop) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, μ.real {x | 3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) / Na k) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) /
          Nb k)) <
      |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)|} <
      (gaussianReal 0 1).real {z | 3 ≤ |z|} + η :=
  consistency_check_of_empVar_le hω hind hPf₀ hPc h24 hNa hNb
    (Eventually.of_forall fun _ => ae_of_all _ fun _ => le_rfl)
    (Eventually.of_forall fun _ => ae_of_all _ fun _ => le_rfl)
    (Eventually.of_forall fun _ => ae_of_all _ fun _ => le_rfl) hη

/-- **The probability that the consistency check fails is eventually less than 0.3%** (Giles
2015, §3.3, p. 22: "The probability of this ratio being greater than unity is less than 0.3%.").
In the setting of `consistency_check_empirical` (independent samples, `P^f_ℓ, P^c_ℓ` square
integrable, (2.4), `N_a(k), N_b(k) → ∞` at arbitrary rates, empirical variances), for all
sufficiently large `k`, `P(3(√V_a + √V_b + √V_c) < |a − b + c|) < 0.003`.  Proof:
`consistency_check_empirical` with `η = 0.003 − P(|Z| ≥ 3) > 0` (`gaussian_tail_three`,
`measureReal_gaussianReal_le_abs_eq`).  For a fixed sample size the bound can fail (module
docstring). -/
theorem consistency_check_empirical_lt [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {Pf Pc : ℕ → Ω₀ → ℝ}
    {ℓ : ℕ} (hPf₀ : MemLp (Pf ℓ) 2 ν) (hPc : MemLp (Pc ℓ) 2 ν)
    (h24 : ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν) {Na Nb : ℕ → ℕ} (hNa : Tendsto Na atTop atTop)
    (hNb : Tendsto Nb atTop atTop) :
    ∀ᶠ k in atTop, μ.real {x | 3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) / Na k) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) /
          Nb k)) <
      |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)|} <
      0.003 := by
  have h3 := gaussian_tail_three
  rw [← measureReal_gaussianReal_le_abs_eq] at h3
  filter_upwards [consistency_check_empirical hω hind hPf₀ hPc h24 hNa hNb
    (sub_pos.2 h3)] with k hk
  linarith

/-- **The bound `P(|Z| ≥ 3)` is attained** (Giles 2015, §3.3, p. 22: "The probability of this ratio
being greater than unity is less than 0.3%.").  In the setting of `consistency_check_empirical`,
with `P^f_{ℓ+1}` square integrable as well, suppose that `P^f_ℓ` and `P^f_{ℓ+1}` are almost surely
constant (`V[P^f_ℓ] = V[P^f_{ℓ+1}] = 0`; the square integrability makes these variances
meaningful) and `V[P^c_ℓ] > 0`; for instance `P^f_ℓ = P^f_{ℓ+1} = 0` and `P^c_ℓ = −Y` with
`Y ~ N(0, 1)`.  Then the probability that the check fails tends to `P(|Z| ≥ 3) ≈ 0.0027`,
`Z ~ N(0, 1)`: the asymptotic bound of `consistency_check_empirical` cannot be improved, and the
paper's `0.3%` is close to the worst case.  Here `V_a = V_b = 0` and the check fails iff
`3 s_c/√N_b < |a − b + c|`, where the empirical variance `s_c²` of `Y = P^f_{ℓ+1} − P^c_ℓ` tends to
`V[Y] = V[P^c_ℓ] = N_b σ_k²` (`tendsto_measureReal_lt_empVar`), and `(a − b + c)/σ_k → N(0, 1)`
(`tendstoInDistribution_consistencyStat`); the upper bound is `consistency_check_empirical`.  As
the samples of `P^f_ℓ` are almost surely constant, `N_a(k) → ∞` could be weakened to
`N_a(k) ≥ 1` eventually; it is kept so that the statement stays in the setting of the main
theorem. -/
theorem consistency_check_empirical_sharp [IsProbabilityMeasure μ]
    (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hind : iIndepFun ω μ) {Pf Pc : ℕ → Ω₀ → ℝ}
    {ℓ : ℕ} (hPf₀ : MemLp (Pf ℓ) 2 ν) (hPf₁ : MemLp (Pf (ℓ + 1)) 2 ν) (hPc : MemLp (Pc ℓ) 2 ν)
    (h24 : ∫ y, Pf ℓ y ∂ν = ∫ y, Pc ℓ y ∂ν) (hf0 : variance (Pf ℓ) ν = 0)
    (hf1 : variance (Pf (ℓ + 1)) ν = 0) (hc0 : 0 < variance (Pc ℓ) ν) {Na Nb : ℕ → ℕ}
    (hNa : Tendsto Na atTop atTop) (hNb : Tendsto Nb atTop atTop) :
    Tendsto (fun k => μ.real {x | 3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) / Na k) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k) +
        √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) /
          Nb k)) <
      |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
        empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)|})
      atTop (𝓝 ((gaussianReal 0 1).real {z | 3 ≤ |z|})) := by
  have : IsProbabilityMeasure ν := by
    rw [← (hω (0, 0)).map_eq]
    exact Measure.isProbabilityMeasure_map (hω (0, 0)).measurable.aemeasurable
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- the lower bound
    obtain ⟨z, hz3, hzG⟩ := exists_gaussianReal_lt_abs_gt
      (show 0 < ((gaussianReal 0 1).real {z | 3 ≤ |z|} - a) / 2 by linarith)
    obtain ⟨θ, hθ⟩ : ∃ θ, θ = z / 3 := ⟨_, rfl⟩
    have hθ1 : 1 < θ := by rw [hθ, one_lt_div (by norm_num)]; exact hz3
    have hzθ : z = 3 * θ := by rw [hθ]; ring
    have hθ2 : 1 < θ ^ 2 := by nlinarith
    obtain ⟨Vc, hVc⟩ : ∃ V, variance (Pc ℓ) ν = V := ⟨_, rfl⟩
    rw [hVc] at hc0
    -- `V[Y] = V[P^c_ℓ]`, as `P^f_{ℓ+1}` is a.s. constant
    have hae1 := ae_eq_integral_of_variance_eq_zero hPf₁ hf1
    have hVy : variance (fun y => Pf (ℓ + 1) y - Pc ℓ y) ν = Vc := by
      rw [variance_congr (show (fun y => Pf (ℓ + 1) y - Pc ℓ y) =ᵐ[ν]
          fun y => (∫ y, Pf (ℓ + 1) y ∂ν) - Pc ℓ y from hae1.mono fun y hy => by simp only [hy]),
        variance_const_sub hPc.aestronglyMeasurable, hVc]
    have hTd := tendstoInDistribution_consistencyStat hω hind hPf₀ hPc h24
      (by rw [hf0, hVc, zero_add]; exact hc0) hNa hNb (HasLaw.id (μ := gaussianReal 0 1))
    have h1 := tendsto_measureReal_lt_abs hTd (z := z) (by linarith)
    have hB := (tendsto_measureReal_lt_empVar (g := fun y => Pf (ℓ + 1) y - Pc ℓ y) hω hind
      (hPf₁.sub hPc) (ℓ + 1) (c := θ ^ 2 * Vc)
      (by rw [hVy]; simpa using mul_lt_mul_of_pos_right hθ2 hc0)).comp hNb
    -- almost surely the samples of `P^f_ℓ` and `P^f_{ℓ+1}` are constant
    have hfa := ae_eq_integral_of_variance_eq_zero hPf₀ hf0
    have hae : ∀ᵐ x ∂μ, ∀ n, Pf ℓ (ω (ℓ, n) x) = ∫ y, Pf ℓ y ∂ν ∧
        Pf (ℓ + 1) (ω (ℓ + 1, n) x) = ∫ y, Pf (ℓ + 1) y ∂ν := by
      rw [ae_all_iff]
      intro n
      filter_upwards [(hω (ℓ, n)).quasiMeasurePreserving.ae hfa,
        (hω (ℓ + 1, n)).quasiMeasurePreserving.ae hae1] with x h1 h2
      exact ⟨h1, h2⟩
    have hbad : μ.real {x | ¬ ∀ n, Pf ℓ (ω (ℓ, n) x) = ∫ y, Pf ℓ y ∂ν ∧
        Pf (ℓ + 1) (ω (ℓ + 1, n) x) = ∫ y, Pf (ℓ + 1) y ∂ν} = 0 := by
      rw [measureReal_def, ae_iff.1 hae, ENNReal.toReal_zero]
    have hq : 0 < ((gaussianReal 0 1).real {z | 3 ≤ |z|} - a) / 4 := by linarith
    filter_upwards [h1.eventually_const_lt (sub_lt_self _ hq), hB.eventually_lt_const hq,
      hNa.eventually_gt_atTop 0, hNb.eventually_gt_atTop 0] with k hk1 hk2 hka hkb
    simp only [Function.comp_apply] at hk2
    have hNa0 : (0 : ℝ) < Na k := Nat.cast_pos.2 hka
    have hNb0 : (0 : ℝ) < Nb k := Nat.cast_pos.2 hkb
    obtain ⟨σ, hσ⟩ : ∃ σ, √(variance (Pf ℓ) ν / Na k + variance (Pc ℓ) ν / Nb k) = σ :=
      ⟨_, rfl⟩
    have hσsq : σ ^ 2 = Vc / Nb k := by
      rw [← hσ, Real.sq_sqrt (by rw [hf0, hVc]; positivity), hf0, hVc, zero_div, zero_add]
    have hσpos : 0 < σ := by
      rw [← hσ, hf0, hVc, zero_div, zero_add]
      exact Real.sqrt_pos.2 (div_pos hc0 hNb0)
    have hsub : {x | z < |(empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)) /
          √(variance (Pf ℓ) ν / Na k + variance (Pc ℓ) ν / Nb k)|} ⊆
        ({x | 3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) / Na k) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) /
            Nb k)) <
        |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)|} ∪
        {x | θ ^ 2 * Vc <
          empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)}) ∪
        {x | ¬ ∀ n, Pf ℓ (ω (ℓ, n) x) = ∫ y, Pf ℓ y ∂ν ∧
          Pf (ℓ + 1) (ω (ℓ + 1, n) x) = ∫ y, Pf (ℓ + 1) y ∂ν} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
      by_cases hgood : ∀ n, Pf ℓ (ω (ℓ, n) x) = ∫ y, Pf ℓ y ∂ν ∧
          Pf (ℓ + 1) (ω (ℓ + 1, n) x) = ∫ y, Pf (ℓ + 1) y ∂ν
      swap
      · exact Or.inr hgood
      by_cases hover : θ ^ 2 * Vc <
          empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)
      · exact Or.inl (Or.inr hover)
      refine Or.inl (Or.inl ?_)
      have ha0 : empVar (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) = 0 := by
        rw [show (fun n => Pf ℓ (ω (ℓ, n) x)) = fun _ => ∫ y, Pf ℓ y ∂ν from
          funext fun n => (hgood n).1]
        exact empVar_const _ _
      have hb0 : empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) = 0 := by
        rw [show (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) = fun _ => ∫ y, Pf (ℓ + 1) y ∂ν from
          funext fun n => (hgood n).2]
        exact empVar_const _ _
      rw [hσ, abs_div, abs_of_pos hσpos, lt_div_iff₀ hσpos] at hx
      rw [ha0, hb0, zero_div, zero_div, Real.sqrt_zero, zero_add, zero_add]
      have hle : √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) /
          Nb k) ≤ θ * σ := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ θ * σ)]
        refine Real.sqrt_le_sqrt ?_
        rw [mul_pow, hσsq, div_le_iff₀ hNb0]
        have := not_lt.1 hover
        field_simp
        linarith
      rw [hzθ] at hx
      linarith
    have hu1 := measureReal_union_le (μ := μ)
      ({x | 3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) / Na k) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) /
            Nb k)) <
        |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)|} ∪
        {x | θ ^ 2 * Vc <
          empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)})
      {x | ¬ ∀ n, Pf ℓ (ω (ℓ, n) x) = ∫ y, Pf ℓ y ∂ν ∧
          Pf (ℓ + 1) (ω (ℓ + 1, n) x) = ∫ y, Pf (ℓ + 1) y ∂ν}
    have hu2 := measureReal_union_le (μ := μ)
      {x | 3 * (√(empVar (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) / Na k) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) / Nb k) +
          √(empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k) /
            Nb k)) <
        |empMean (fun n => Pf ℓ (ω (ℓ, n) x)) (Na k) -
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x)) (Nb k) +
          empMean (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)|}
      {x | θ ^ 2 * Vc <
          empVar (fun n => Pf (ℓ + 1) (ω (ℓ + 1, n) x) - Pc ℓ (ω (ℓ + 1, n) x)) (Nb k)}
    have hm := measureReal_mono (μ := μ) hsub
    linarith
  · -- the upper bound
    filter_upwards [consistency_check_empirical hω hind hPf₀ hPc h24 hNa hNb
      (sub_pos.2 ha)] with k hk
    linarith

end Check

end MLMC
