import MlmcLean.EllipticFD
import MlmcLean.GilesCorollaries
import MlmcLean.DriftImplicit
import MlmcLean.ApproxNormal
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Sort

/-!
# End-to-end instances: the elliptic example, the call option, refinement factor `M`, and more

References: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.1 (pp. 29–30),
§5.2 (p. 35), §5.6 (p. 44), §7.1 (pp. 49–51), §10.2 (p. 62); I.-B. Haas and M.B. Giles, *A nested
MLMC framework for efficient simulations on FPGAs*, arXiv:2502.07123 (2025), §3.2, (16).

This file instantiates results of the library end to end where the papers state a conclusion
that was so far only available with assumed rates or as arithmetic, and proves a few small
claims that were missing.  Every complexity theorem here also certifies that the error of the
estimator is square integrable, so its mean square is not a junk value.

* `elliptic_mlmc_theorem1` (Giles §7.1): the multilevel estimator for the 1-D elliptic example
  `(c u′)′ = −50 Z²`, `c(x) = 1 + a x`, with `h_ℓ = 2^{−(ℓ+1)}` and cost `2^{ℓ+1}` per sample, has
  MSE `< ε²` at cost `O(ε⁻²)`: `α = 2`, `β = 4` (`elliptic_fd_rates`), `γ = 1`, Theorem 1 for
  independent samples (`giles_theorem1_iid`); `elliptic_mlmc_theorem1_uniform` is the paper's law
  `a ∼ U(0, 1)`.
* `gbm_call_mlmc_theorem1`, `gbm_mil_call_mlmc_theorem1` (Giles §5.1, §5.2, Figures 5.3, 5.5): the
  paper's payoff `e^{−rT} max(S_T − K, 0)`, which is `e^{−rT}`-Lipschitz
  (`abs_discountedCall_sub_le`), in `gbm_mlmc_theorem1` (cost `O(ε⁻²(log ε)²)`) and
  `gbm_mil_mlmc_theorem1` (cost `O(ε⁻²)`).
* `tamedCubic_fourth_moment_le` (supporting Giles §5.6): for `dS = −S³ dt + dW` the tamed scheme
  with `N ≥ T/54` steps has `E X_N⁴ ≤ x₀⁴ + 6x₀²T + 3T²`, uniformly in `N`.
* Refinement factor `M` and coarsest step `h₀ = T/m` for GBM (Giles §5.1, `h_ℓ = h₀ M^{−ℓ}`): the
  exact solution is consistent across levels under the block sums (`gbmExactM_blockAvg`, the
  analogue of `gbmExact_pairAvg`), the weak error is `≤ K √(C(T) h_ℓ)` (`gbm_weak_error_le_M`), the
  correction variance is `≤ 2K² C(T) h₀ (M + 1) M^{−(ℓ+1)}` (`gbm_correction_variance_le_M`), so
  `β = γ = log₂ M`, and `gbm_mlmc_theorem1_M` gives MSE `< ε²` at cost `O(ε⁻²(log ε)²)` with no
  assumed rate.
* `exists_lsq_minimiser`, `method2_iteration_exists`, `method2_sorting_iteration_exists`
  (Haas–Giles §3.2): the least-squares problem (16) has a minimiser for every permutation, so the
  alternating iteration of method 2, with the paper's sorting step (`exists_ranking`) when the
  targets are sorted, exists, and its objective is eventually constant.
* Giles §10.2, rounded or truncated increments: with independent `N(0, v)` fine increments,
  `roundFixed_coarse_increment_mean` (round to nearest, ties up: the directly rounded coarse
  increment has mean `0`, the rounded sums have positive means),
  `nearestRound_coarse_increment_pos_prob` (round to nearest with any tie rule, after the
  summation: `P(increment > 0)` differs),
  `roundFixed_coarse_increment_pos_prob` (its fixed-point instance) and
  `truncGrid_coarse_increment_mean_lt` (truncation, before and after the summation: the means are
  strictly ordered).  So (2.4) fails in law, not only pathwise
  (`roundFixed_sum_inconsistent_general`).

Deviations from the papers are stated in the docstrings: in §7.1 the independence of `a` and `Z` is
not used; for refinement factor `M` the weak rate is the strong-error rate `α = ½ log₂ M` (the
paper's weak order one, `α = log₂ M`, is not proved; it is not needed for the complexity), and the
coarsest step is `T/m` so that the grid reaches `T`; the general method-2 statement takes any
minimiser of (16) over the permutations, the sorting statement needs sorted targets; in §10.2 the
paper's "truncation" is modelled both by round-to-nearest (`roundFixed`) and by rounding down
(`truncGrid`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MLMC

/-! ### Giles §7.1: the elliptic example end to end -/

/-- **The elliptic MLMC estimator end to end: MSE `< ε²` at cost `O(ε⁻²)`** (Giles 2015, §7.1,
pp. 49–51: "Level `ℓ` uses a uniform grid with spacing `h_ℓ = 2^{−(ℓ+1)}`, so there is just one
interior grid point on the coarsest level. … The uniform second order accuracy means that there is
a constant `K` such that `|P − P_ℓ| < K h_ℓ²` and therefore we have `α = 2`, `β = 4` and `γ = 1`,
resulting in an `O(ε^{−2})` complexity").  Let `(Ω₀, ν)` be a probability space carrying the
coefficient `a` (measurable, `a ∈ [0, 1]` almost surely) and `Z ∼ N(0, 1)` (measurable); let `P`
be the output `∫₀¹ u` of `(c u′)′ = −50 Z²`, `c(x) = 1 + a x`, `u(0) = u(1) = 0` (`ellipticP`), and
`P_ℓ` the trapezoidal output of the central-difference solution with `2^{ℓ+1}` cells
(`ellipticPl`).  The samples `ω^{(ℓ,n)}` are the coordinates of `(Ω₀^{ℕ×ℕ}, ν^{⊗(ℕ×ℕ)})`
(independent, each with law `ν`), and a level-`ℓ` sample costs `2^{ℓ+1}`, the number of cells of
its fine grid (`γ = 1`).  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L`
and `N_ℓ ≥ 1` for which the multilevel estimator (2.2) of `E[P]` has a square-integrable error with
mean square `< ε²`, and cost `∑_{ℓ≤L} N_ℓ 2^{ℓ+1} ≤ c₄ ε⁻²`.  No rate is assumed: `α = 2` and
`β = 4` are `elliptic_fd_rates` (with the random constant `K = (50/3) Z²`; no deterministic `K`
exists, `not_ae_abs_ellipticP_sub_le`), and Theorem 1 for independent samples is
`giles_theorem1_iid`.  Deviations: the uniform law of `a` and the independence of `a` and `Z` are
not used, only `a ∈ [0, 1]` almost surely (the paper's law is the special case
`elliptic_mlmc_theorem1_uniform`); `a` and `Z` are assumed measurable rather than almost everywhere
measurable, as `giles_theorem1_iid` needs measurable `P_ℓ`; the cost of a sample counts the cells
of the fine grid only (the coarse grid adds `2^ℓ` cells, a factor `3/2`). -/
theorem elliptic_mlmc_theorem1 {Ω₀ : Type*} [MeasurableSpace Ω₀] (ν : Measure Ω₀)
    [IsProbabilityMeasure ν] {a Z : Ω₀ → ℝ} (ha : Measurable a)
    (ha01 : ∀ᵐ y ∂ν, a y ∈ Set.Icc (0 : ℝ) 1) (hZm : Measurable Z)
    (hZ : HasLaw Z (gaussianReal 0 1) ν) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (mlmcEstimator (fun ℓ y => ellipticPl (a y) (50 * Z y ^ 2) ℓ)
            (fun p x => x p) L N x - ∫ y, ellipticP (a y) (50 * Z y ^ 2) ∂ν) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => ν) ∧
        ∫ x, (mlmcEstimator (fun ℓ y => ellipticPl (a y) (50 * Z y ^ 2) ℓ) (fun p x => x p) L N x -
            ∫ y, ellipticP (a y) (50 * Z y ^ 2) ∂ν) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => ν) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ (ℓ + 1) ≤ c₄ * ε ^ (-2 : ℝ) := by
  have hrates := fun ℓ => elliptic_fd_rates (μ := ν) (a := a) (Z := Z) ha.aemeasurable ha01 hZ ℓ
  have hPlm : ∀ ℓ, Measurable fun y => ellipticPl (a y) (50 * Z y ^ 2) ℓ := fun ℓ => by
    have h := (measurable_ellipticPl ℓ).comp (ha.prodMk ((hZm.pow_const 2).const_mul 50))
    exact h
  -- (i): `|E[P_ℓ − P]| ≤ (50/3) h_ℓ² = (25/6) 2^{−2ℓ}`
  have h_i : ∀ ℓ : ℕ, |∫ y, ellipticPl (a y) (50 * Z y ^ 2) ℓ - ellipticP (a y) (50 * Z y ^ 2) ∂ν|
      ≤ 25 / 6 * (2 : ℝ) ^ (-(2 * (ℓ : ℝ))) := fun ℓ => by
    obtain ⟨-, -, -, h, -⟩ := hrates ℓ
    rw [two_rpow_neg_two_mul]
    refine h.trans_eq ?_
    rw [← pow_mul, show (ℓ + 1) * 2 = 2 * ℓ + 2 by ring, pow_add, pow_mul]
    simp only [one_div, inv_pow]
    norm_num
    ring
  -- (iii): `V_0 = V[P_0]`, `V_{ℓ+1} ≤ (62500/3) h_{ℓ+1}⁴`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (fun y => ellipticPl (a y) (50 * Z y ^ 2) 0) ν :=
    ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := hV₀ ▸ variance_nonneg _ _
  have h_iii : ∀ ℓ, variance (levelDiff (fun ℓ y => ellipticPl (a y) (50 * Z y ^ 2) ℓ) ℓ) ν ≤
      (V₀ + 1303) * (2 : ℝ) ^ (-(4 * (ℓ : ℝ))) := fun ℓ => by
    have e4 : (2 : ℝ) ^ (-(4 * (ℓ : ℝ))) = ((16 : ℝ) ^ ℓ)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_natCast,
        Real.rpow_ofNat]
      norm_num
    rw [e4]
    cases ℓ with
    | zero =>
      rw [levelDiff_zero, ← hV₀]
      norm_num
    | succ ℓ =>
      obtain ⟨-, -, -, -, -, h2, h3⟩ := hrates ℓ
      rw [levelDiff_succ]
      refine (h2.trans h3).trans ?_
      have hp : 0 < ((16 : ℝ) ^ (ℓ + 1))⁻¹ := by positivity
      have e : 62500 / 3 * ((1 / 2 : ℝ) ^ (ℓ + 2)) ^ 4 = 62500 / 48 * ((16 : ℝ) ^ (ℓ + 1))⁻¹ := by
        rw [← pow_mul, show (ℓ + 2) * 4 = 4 * (ℓ + 1) + 4 by ring, pow_add, pow_mul]
        simp only [one_div, inv_pow]
        norm_num
        ring
      rw [e]
      nlinarith
  have h_iv : ∀ ℓ : ℕ, ∫ _y, (2 : ℝ) ^ (ℓ + 1) ∂ν ≤ 2 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) :=
    fun ℓ => by
    rw [integral_const, probReal_univ, one_smul, one_mul, Real.rpow_natCast, pow_succ, mul_comm]
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_iid ν (fun y => ellipticP (a y) (50 * Z y ^ 2))
    (fun ℓ y => ellipticPl (a y) (50 * Z y ^ 2) ℓ) (fun ℓ _ => (2 : ℝ) ^ (ℓ + 1))
    (α := 2) (β := 4) (γ := 1) two_pos (by norm_num) one_pos (by norm_num) (by positivity)
    two_pos (by norm_num) ((hrates 0).1.integrable one_le_two) hPlm
    (fun ℓ => (hrates ℓ).2.1) (fun _ => integrable_const _) h_i h_iii h_iv
  obtain ⟨-, -, hω⟩ := exists_iid_inputs ν
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  have hY : MemLp (mlmcEstimator (fun ℓ y => ellipticPl (a y) (50 * Z y ^ 2) ℓ)
      (fun p x => x p) L N) 2 (Measure.infinitePi fun _ : ℕ × ℕ => ν) :=
    memLp_finsetSum _ fun ℓ _ => memLp_levelEstimator hω (fun ℓ => (hrates ℓ).2.1) ℓ (N ℓ)
  refine ⟨L, N, hN, (hY.sub (memLp_const _)).integrable_sq, hmse, ?_⟩
  simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul] at hcost
  rw [complexityBound_of_lt (by norm_num : (1 : ℝ) < 4) ε] at hcost
  exact hcost

/-- **The elliptic example with the paper's random coefficient** (Giles 2015, §7.1, p. 49: "`Z` is
a Normal random variable with zero mean and unit variance, and `c(x) = 1 + ax` with `a` being a
uniform random variable on the unit interval `(0, 1)`").  If `a` has the uniform law on `[0, 1]`
(`volume.restrict [0, 1]`, the same law as on `(0, 1)`) and `Z ∼ N(0, 1)`, both measurable, then
the conclusion of `elliptic_mlmc_theorem1` holds: the multilevel estimator has a square-integrable
error with mean square `< ε²` at cost `∑_{ℓ≤L} N_ℓ 2^{ℓ+1} ≤ c₄ ε⁻²`.  The uniform law gives
`a ∈ [0, 1]` almost surely (`ae_restrict_mem`); the independence of `a` and `Z`, part of the
paper's setting, is not needed and so not assumed. -/
theorem elliptic_mlmc_theorem1_uniform {Ω₀ : Type*} [MeasurableSpace Ω₀] (ν : Measure Ω₀)
    [IsProbabilityMeasure ν] {a Z : Ω₀ → ℝ} (ha : Measurable a)
    (haU : HasLaw a (volume.restrict (Set.Icc (0 : ℝ) 1)) ν) (hZm : Measurable Z)
    (hZ : HasLaw Z (gaussianReal 0 1) ν) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (mlmcEstimator (fun ℓ y => ellipticPl (a y) (50 * Z y ^ 2) ℓ)
            (fun p x => x p) L N x - ∫ y, ellipticP (a y) (50 * Z y ^ 2) ∂ν) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => ν) ∧
        ∫ x, (mlmcEstimator (fun ℓ y => ellipticPl (a y) (50 * Z y ^ 2) ℓ) (fun p x => x p) L N x -
            ∫ y, ellipticP (a y) (50 * Z y ^ 2) ∂ν) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => ν) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ (ℓ + 1) ≤ c₄ * ε ^ (-2 : ℝ) := by
  have h : ∀ᵐ x ∂ν.map a, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [haU.map_eq]
    exact ae_restrict_mem measurableSet_Icc
  exact elliptic_mlmc_theorem1 ν ha (ae_of_ae_map haU.aemeasurable h) hZm hZ

/-! ### Giles §5.1–§5.2: the discounted call option -/

/-- The error of a multilevel estimator built from square-integrable corrections is square
integrable (Giles 2015, §2.1, (2.2)): `(∑_{ℓ≤L} N_ℓ⁻¹ ∑_{n<N_ℓ} D_ℓ(ω^{(ℓ,n)}) − c)²` is integrable
when every `D_ℓ ∈ L²` and the inputs have law `ν`. -/
lemma integrable_sq_sum_blockMean_sub {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω]
    {ν : Measure Ω₀} {μ : Measure Ω} [IsFiniteMeasure μ] {D : ℕ → Ω₀ → ℝ}
    {ω : ℕ × ℕ → Ω → Ω₀} (hω : ∀ p, MeasurePreserving (ω p) μ ν) (hD : ∀ ℓ, MemLp (D ℓ) 2 ν)
    (L : ℕ) (N : ℕ → ℕ) (c : ℝ) :
    Integrable (fun x => (∑ ℓ ∈ range (L + 1), blockMean D ω ℓ (N ℓ) x - c) ^ 2) μ :=
  ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω hD ℓ (N ℓ)).sub (memLp_const c)).integrable_sq

/-- **The discounted call payoff is Lipschitz with constant `e^{−rT}`** (Giles 2015, §5.1, p. 30:
"payoff `P(S) ≡ exp(−rT) max(S_T − K, 0)`"):
`|e^{−rT} max(x − K, 0) − e^{−rT} max(y − K, 0)| ≤ e^{−rT} |x − y|`. -/
lemma abs_discountedCall_sub_le (r T K x y : ℝ) :
    |Real.exp (-r * T) * max (x - K) 0 - Real.exp (-r * T) * max (y - K) 0| ≤
      Real.exp (-r * T) * |x - y| := by
  rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h := abs_max_sub_max_le_abs (x - K) (y - K) 0
  rwa [sub_sub_sub_cancel_right] at h

/-- **Theorem 1 for the paper's call option with Euler–Maruyama** (Giles 2015, §5.1, pp. 29–30:
"In either case, Theorem 1 gives the complexity to achieve a root-mean-square error of `ε` to be
`O(ε^{−2}(log ε)²)` … Figure 5.3 shows results for a financial call option with a single
underlying asset satisfying Geometric Brownian Motion SDE, `dS_t = r S_t dt + σ S_t dW`, and payoff
`P(S) ≡ exp(−rT) max(S_T − K, 0)` with `r = 0.05`, `σ = 0.2`, `T = 1`, `S_0 = 100`, `K = 100`").
For all `r, σ, s₀, K` and `T ≥ 0` (in particular the paper's values), level `ℓ` uses `2^ℓ`
Euler–Maruyama steps of size `T 2^{−ℓ}`, the coarse path of a sample is driven by the summed
increments, the samples are independent and a level-`ℓ` sample costs `2^ℓ`.  Then there is
`c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the multilevel
estimator of `E[e^{−rT} max(S_T − K, 0)]`, `S_T = s₀ e^{(r − σ²/2)T + σ√T W}`, `W ∼ N(0, 1)`, has a
square-integrable error with mean square `< ε²`, and cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`.  This
is `gbm_mlmc_theorem1` for the `e^{−rT}`-Lipschitz payoff (`abs_discountedCall_sub_le`); no rate is
assumed. -/
theorem gbm_call_mlmc_theorem1 (r σ s₀ K : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFine (gbmDrift r) (gbmVol σ) T s₀
                (europeanPayoff fun S => Real.exp (-r * T) * max (S - K) 0))
              (emCoarse (gbmDrift r) (gbmVol σ) T s₀
                (europeanPayoff fun S => Real.exp (-r * T) * max (S - K) 0)))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, Real.exp (-r * T) *
              max (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) - K) 0
              ∂gaussianReal 0 1) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFine (gbmDrift r) (gbmVol σ) T s₀
                (europeanPayoff fun S => Real.exp (-r * T) * max (S - K) 0))
              (emCoarse (gbmDrift r) (gbmVol σ) T s₀
                (europeanPayoff fun S => Real.exp (-r * T) * max (S - K) 0)))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, Real.exp (-r * T) *
              max (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) - K) 0
              ∂gaussianReal 0 1) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  have hg := abs_discountedCall_sub_le r T K
  obtain ⟨-, -, hω⟩ := exists_iid_inputs stdNormalSeq
  have hPf : ∀ ℓ, MemLp (emFine (gbmDrift r) (gbmVol σ) T s₀
      (europeanPayoff fun S => Real.exp (-r * T) * max (S - K) 0) ℓ) 2 stdNormalSeq :=
    fun ℓ => memLp_two_comp_of_abs_sub_le hg (memLp_gbmEM r σ T s₀ ℓ)
  have hPc : ∀ ℓ, MemLp (emCoarse (gbmDrift r) (gbmVol σ) T s₀
      (europeanPayoff fun S => Real.exp (-r * T) * max (S - K) 0) ℓ) 2 stdNormalSeq := fun ℓ => by
    rw [show emCoarse (gbmDrift r) (gbmVol σ) T s₀
        (europeanPayoff fun S => Real.exp (-r * T) * max (S - K) 0) ℓ =
        emFine (gbmDrift r) (gbmVol σ) T s₀
        (europeanPayoff fun S => Real.exp (-r * T) * max (S - K) 0) ℓ ∘ pairAvg from
      funext (emCoarse_eq _ _ _ _ _ ℓ)]
    exact (hPf ℓ).comp_measurePreserving measurePreserving_pairAvg
  obtain ⟨c₄, hc₄, h⟩ := gbm_mlmc_theorem1 r σ s₀ hT hg
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  exact ⟨L, N, hN, integrable_sq_sum_blockMean_sub hω (memLp_fineCoarseDiff hPf hPc) L N _,
    hmse, hcost⟩

/-- **Theorem 1 for the paper's call option with the Milstein scheme** (Giles 2015, §5.2, p. 35:
"Figure 5.5 demonstrates the improved results obtained for the call option based on a single
underlying GBM asset. `V_ℓ` is now `O(h_ℓ²)`, leading to `α = 1`, `β = 2`, `γ = 1`"; the payoff
is that of §5.1, p. 30, `P(S) ≡ exp(−rT) max(S_T − K, 0)`).  For all `r, σ, s₀, K` and `T ≥ 0`,
level `ℓ` uses `2^ℓ` Milstein steps of size `T 2^{−ℓ}`, the coarse path is driven by the summed
increments (`pairAvg`), the samples are independent and a level-`ℓ` sample costs `2^ℓ`.  Then
there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` for which the
multilevel estimator of `E[e^{−rT} max(S_T − K, 0)]` has a square-integrable error with mean square
`< ε²`, and cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²`.  This is `gbm_mil_mlmc_theorem1` for the
`e^{−rT}`-Lipschitz payoff (`abs_discountedCall_sub_le`); no rate is assumed. -/
theorem gbm_mil_call_mlmc_theorem1 (r σ s₀ K : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => Real.exp (-r * T) * max (gbmMil r σ T s₀ ℓ z - K) 0)
              (fun ℓ z => Real.exp (-r * T) * max (gbmMil r σ T s₀ ℓ (pairAvg z) - K) 0))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, Real.exp (-r * T) *
              max (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) - K) 0
              ∂gaussianReal 0 1) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (fun ℓ z => Real.exp (-r * T) * max (gbmMil r σ T s₀ ℓ z - K) 0)
              (fun ℓ z => Real.exp (-r * T) * max (gbmMil r σ T s₀ ℓ (pairAvg z) - K) 0))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, Real.exp (-r * T) *
              max (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)) - K) 0
              ∂gaussianReal 0 1) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * ε ^ (-2 : ℝ) := by
  have hg := abs_discountedCall_sub_le r T K
  obtain ⟨-, -, hω⟩ := exists_iid_inputs stdNormalSeq
  have hPf : ∀ ℓ, MemLp (fun z => Real.exp (-r * T) * max (gbmMil r σ T s₀ ℓ z - K) 0) 2
      stdNormalSeq := fun ℓ => memLp_two_comp_of_abs_sub_le hg (memLp_gbmMil r σ T s₀ ℓ)
  have hPc : ∀ ℓ, MemLp (fun z => Real.exp (-r * T) * max (gbmMil r σ T s₀ ℓ (pairAvg z) - K) 0)
      2 stdNormalSeq := fun ℓ => (hPf ℓ).comp_measurePreserving measurePreserving_pairAvg
  obtain ⟨c₄, hc₄, h⟩ := gbm_mil_mlmc_theorem1 r σ s₀ hT
    (g := fun S => Real.exp (-r * T) * max (S - K) 0) hg
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  exact ⟨L, N, hN, integrable_sq_sum_blockMean_sub hω (memLp_fineCoarseDiff hPf hPc) L N _,
    hmse, hcost⟩

/-! ### Giles §5.6: the fourth moment of the tamed scheme -/

/-- **A uniform fourth-moment bound for the tamed scheme** (supporting Giles 2015, §5.6, p. 44: "A
related problem is addressed by Hutzenthaler, Jentzen and Kloeden (2013), who are concerned with
SDEs such as `dS_t = −S_t³ dt + dW_t` … Their solution is to introduce a slight modification to the
Euler-Maruyama discretisation which limits the size of the drift term on each level of
approximation when `S_t` is large, to avoid this instability").  Giles states no moment bound; this
result supports his remark (Hutzenthaler, Jentzen and Kloeden prove bounds on all moments of the
tamed scheme).  For `dS = −S³ dt + dW`, `T ≥ 0` and `N ≥ T/54` steps of size `h = T/N`, driven by
independent `Z_0, …, Z_{N−1}` with law `N(0, 1)` (increments `√h Z_n`), the tamed scheme
`X_{n+1} = X_n − hX_n³/(1 + h|X_n|³) + √h Z_n` (`tamedPath`) has a finite fourth moment and
`E X_N² ≤ x₀² + T`, `E X_N⁴ ≤ x₀⁴ + 6x₀²T + 3T²` (the moments of `x₀ + W_T`), uniformly in `N`; the
second-moment bound is `tamedCubic_second_moment_le` again, carried along in the same induction.
Proof: for `h ≤ 54` the tamed step does not increase `|S|` (`abs_tamedCubic_le`), and `X_n` is
independent of `Z_n` (`indepFun_of_forall_lt`), so `E X_{n+1}⁴ ≤ E X_n⁴ + 6h E X_n² + 3h²`
(`integral_add_mul_pow_four`) and `E X_{n+1}² ≤ E X_n² + h`.  The condition `N ≥ T/54` is that
of `tamedCubic_second_moment_le` (for `h > 54` the tamed step can expand,
`tamedCubic_nonexpansive_iff`).  Moments of order `p > 4` are not formalised. -/
theorem tamedCubic_fourth_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (x₀ : ℝ)
    {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : T ≤ 54 * N) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n < N, μ.map (Z n) = gaussianReal 0 1)
    (hind : iIndepFun (fun n : Fin N => Z n) μ) :
    MemLp (fun ω => tamedPath (fun S => -S ^ 3) (T / N) x₀ (fun n => Z n ω) N) 4 μ ∧
      ∫ ω, tamedPath (fun S => -S ^ 3) (T / N) x₀ (fun n => Z n ω) N ^ 2 ∂μ ≤ x₀ ^ 2 + T ∧
      ∫ ω, tamedPath (fun S => -S ^ 3) (T / N) x₀ (fun n => Z n ω) N ^ 4 ∂μ ≤
        x₀ ^ 4 + 6 * x₀ ^ 2 * T + 3 * T ^ 2 := by
  have hprob : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  set h := T / (N : ℝ) with hhdef
  have hh0 : 0 ≤ h := by positivity
  have hh54 : h ≤ 54 := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [hhdef, h0]
    · rw [hhdef, div_le_iff₀ (by exact_mod_cast h0)]
      linarith
  have hm : ∀ n < N, AEMeasurable (Z n) μ := fun n hn =>
    aemeasurable_of_map_eq_gaussianReal (hZ n hn)
  have hbm : Measurable fun S : ℝ => -S ^ 3 := by fun_prop
  have hstep := measurable_tamedDriftStep hbm h
  have hcontr : ∀ S, |tamedDriftStep (fun S => -S ^ 3) h S| ≤ |S| := abs_tamedCubic_le hh0 hh54
  have hsq : (√h) ^ 2 = h := Real.sq_sqrt hh0
  have key : ∀ n ≤ N, MemLp (fun ω => tamedPath (fun S => -S ^ 3) h x₀ (fun k => Z k ω) n) 4 μ ∧
      ∫ ω, tamedPath (fun S => -S ^ 3) h x₀ (fun k => Z k ω) n ^ 2 ∂μ ≤ x₀ ^ 2 + n * h ∧
      ∫ ω, tamedPath (fun S => -S ^ 3) h x₀ (fun k => Z k ω) n ^ 4 ∂μ ≤
        x₀ ^ 4 + 6 * x₀ ^ 2 * (n * h) + 3 * (n * h) ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨memLp_const x₀, ?_, ?_⟩ <;> simp [tamedPath]
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      obtain ⟨hX4, hX2, hX4'⟩ := ih hn'.le
      set Y := fun ω => tamedDriftStep (fun S => -S ^ 3) h
        (tamedPath (fun S => -S ^ 3) h x₀ (fun k => Z k ω) n) with hYdef
      have hYZ : IndepFun Y (Z n) μ :=
        indepFun_of_forall_lt hn' (hstep.comp (measurable_tamedPath hbm h x₀ n))
          (fun z z' hz => by
            show tamedDriftStep _ h (tamedPath _ h x₀ z n) =
              tamedDriftStep _ h (tamedPath _ h x₀ z' n)
            rw [tamedPath_congr _ h x₀ hz]) hm hind
      have hYm : AEStronglyMeasurable Y μ :=
        (hstep.comp_aemeasurable hX4.aemeasurable).aestronglyMeasurable
      have hY4 : MemLp Y 4 μ := hX4.of_le hYm
        (ae_of_all _ fun ω => by simp only [Real.norm_eq_abs]; exact hcontr _)
      have hZ4 : MemLp (Z n) 4 μ := memLp_of_map_eq_gaussianReal (hZ n hn') 4 (by norm_num)
      have e2 := integral_mul_add_mul_sq (hY4.mono_exponent (by norm_num)) (hZ n hn') hYZ 1 (√h)
      simp only [one_mul, one_pow] at e2
      have e4 := integral_add_mul_pow_four hY4 (hZ n hn') hYZ (√h)
      rw [hsq] at e2
      rw [hsq, show (√h) ^ 4 = h ^ 2 by rw [show 4 = 2 * 2 by rfl, pow_mul, hsq]] at e4
      have b2 : ∫ ω, Y ω ^ 2 ∂μ ≤
          ∫ ω, tamedPath (fun S => -S ^ 3) h x₀ (fun k => Z k ω) n ^ 2 ∂μ :=
        integral_mono (integrable_pow_of_memLp_four hY4 (by norm_num))
          (integrable_pow_of_memLp_four hX4 (by norm_num)) fun ω => sq_le_sq.mpr (hcontr _)
      have b4 : ∫ ω, Y ω ^ 4 ∂μ ≤
          ∫ ω, tamedPath (fun S => -S ^ 3) h x₀ (fun k => Z k ω) n ^ 4 ∂μ := by
        refine integral_mono (integrable_pow_of_memLp_four hY4 le_rfl)
          (integrable_pow_of_memLp_four hX4 le_rfl) fun ω => ?_
        have := pow_le_pow_left₀ (abs_nonneg _) (hcontr
          (tamedPath (fun S => -S ^ 3) h x₀ (fun k => Z k ω) n)) 4
        rwa [Even.pow_abs (⟨2, rfl⟩ : Even 4), Even.pow_abs (⟨2, rfl⟩ : Even 4)] at this
      have h6 : 6 * h * ∫ ω, Y ω ^ 2 ∂μ ≤ 6 * h * (x₀ ^ 2 + n * h) :=
        mul_le_mul_of_nonneg_left (b2.trans hX2) (by positivity)
      refine ⟨hY4.add (hZ4.const_mul _), ?_, ?_⟩
      · show ∫ ω, (Y ω + √h * Z n ω) ^ 2 ∂μ ≤ x₀ ^ 2 + ((n + 1 : ℕ) : ℝ) * h
        rw [e2]
        push_cast
        nlinarith
      · show ∫ ω, (Y ω + √h * Z n ω) ^ 4 ∂μ ≤
          x₀ ^ 4 + 6 * x₀ ^ 2 * (((n + 1 : ℕ) : ℝ) * h) + 3 * (((n + 1 : ℕ) : ℝ) * h) ^ 2
        rw [e4]
        push_cast
        nlinarith
  obtain ⟨h4, h2, h4'⟩ := key N le_rfl
  have hNh : (N : ℝ) * h = T := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp only [h0, Nat.cast_zero, zero_mul] at hN ⊢
      linarith
    · rw [hhdef, mul_div_cancel₀ _ (by exact_mod_cast h0.ne')]
  rw [hNh] at h2 h4'
  exact ⟨h4, h2, h4'⟩

/-! ### Giles §5.1: geometric Brownian motion with refinement factor `M` -/

/-- The exact GBM solution at time `T` on the level-`ℓ` grid for the coarsest step `h₀ = T/m` and
the refinement factor `M` (Giles 2015, §5.1, p. 29, `h_ℓ = h₀ M^{−ℓ}`):
`S_T = s₀ exp((r − σ²/2)T + σ W_T)` with the Brownian value `W_T = √h_ℓ ∑_{i<m M^ℓ} Z_i` built from
the same normal increments `Z_i` as the level-`ℓ` Euler–Maruyama path with `m M^ℓ` steps
(`gbmExact` is the case `m = 1`, `M = 2`). -/
noncomputable def gbmExactM (r σ T s₀ : ℝ) (m M ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  s₀ * Real.exp ((r - σ ^ 2 / 2) * T +
    σ * (Real.sqrt (T / m / (M : ℝ) ^ ℓ) * ∑ i ∈ range (m * M ^ ℓ), z i))

/-- `∑_{j<Mn} f(j) = ∑_{k<n} ∑_{i<M} f(Mk + i)`: the fine steps grouped into blocks of `M`, one
block per coarse step (Giles 2015, §5.1). -/
lemma sum_range_mul_eq (f : ℕ → ℝ) (M n : ℕ) :
    ∑ j ∈ range (M * n), f j = ∑ k ∈ range n, ∑ i ∈ range M, f (M * k + i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- `m M^ℓ` steps of size `h_ℓ = (T/m) M^{−ℓ}` reach `T` (`m, M > 0`; Giles 2015, §5.1). -/
lemma cast_mul_pow_mul_div {m M : ℕ} (hm : 0 < m) (hM : 0 < M) (T : ℝ) (ℓ : ℕ) :
    ((m * M ^ ℓ : ℕ) : ℝ) * (T / m / (M : ℝ) ^ ℓ) = T := by
  have h1 : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have h2 : (0 : ℝ) < (M : ℝ) ^ ℓ := pow_pos (Nat.cast_pos.2 hM) ℓ
  push_cast
  field_simp

/-- **The exact solution is consistent across levels for refinement factor `M`** (Giles 2015,
§5.1, p. 29: "The multilevel coupling is achieved by using the same underlying driving Brownian
path for the coarse and fine paths; this is accomplished by summing the Brownian increments for
the fine path timesteps to obtain the Brownian increments for the coarse timesteps").  The analogue
of `gbmExact_pairAvg` (`m = 1`, `M = 2`): for `M ≥ 1` and every `m`, the exact solution on the
level-`ℓ` grid driven by the block increments `(Z_{Mk} + ⋯ + Z_{Mk+M−1})/√M` (`blockAvg`) equals the
exact solution on the level-`(ℓ+1)` grid driven by the `Z_i`, since both use the same Brownian
value `W_T`. -/
theorem gbmExactM_blockAvg (r σ T s₀ : ℝ) (m : ℕ) {M : ℕ} (hM : 0 < M) (ℓ : ℕ) (z : ℕ → ℝ) :
    gbmExactM r σ T s₀ m M ℓ (blockAvg M z) = gbmExactM r σ T s₀ m M (ℓ + 1) z := by
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hM'
  set h₀ : ℝ := T / m with hh₀
  have key : Real.sqrt (h₀ / (M : ℝ) ^ ℓ) * ∑ k ∈ range (m * M ^ ℓ), blockAvg M z k =
      Real.sqrt (h₀ / (M : ℝ) ^ (ℓ + 1)) * ∑ i ∈ range (m * M ^ (ℓ + 1)), z i := by
    have e1 : h₀ / (M : ℝ) ^ ℓ = h₀ / (M : ℝ) ^ (ℓ + 1) * M := by
      rw [pow_succ]
      field_simp
    rw [show m * M ^ (ℓ + 1) = M * (m * M ^ ℓ) by ring, sum_range_mul_eq _ M (m * M ^ ℓ), e1,
      Real.sqrt_mul' _ hM'.le]
    simp only [blockAvg]
    rw [← Finset.sum_div]
    field_simp
  unfold gbmExactM
  rw [← hh₀, key]

/-- The exact solution of Giles 2015, §5.1 through the normalised sum of all its increments:
`√h_ℓ ∑_{i<n} Z_i = √T (Z_0 + ⋯ + Z_{n−1})/√n = √T · blockAvg n Z 0` with `n = m M^ℓ` and
`h_ℓ = T/n`. -/
lemma gbmExactM_eq_blockAvg (r σ T s₀ : ℝ) (m M ℓ : ℕ) (z : ℕ → ℝ) :
    gbmExactM r σ T s₀ m M ℓ z =
      s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * blockAvg (m * M ^ ℓ) z 0)) := by
  unfold gbmExactM blockAvg
  have e : T / m / (M : ℝ) ^ ℓ = T / ((m * M ^ ℓ : ℕ) : ℝ) := by
    push_cast
    rw [div_div]
  rw [e, Real.sqrt_div' _ (Nat.cast_nonneg _)]
  simp only [mul_zero, zero_add]
  rw [div_mul_eq_mul_div, mul_div_assoc]

/-- The exact solution `gbmExactM` (Giles 2015, §5.1) is a measurable function of the
increments. -/
lemma measurable_gbmExactM (r σ T s₀ : ℝ) (m M ℓ : ℕ) :
    Measurable (gbmExactM r σ T s₀ m M ℓ) := by
  have hs : Measurable fun z : ℕ → ℝ => ∑ i ∈ range (m * M ^ ℓ), z i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact (((hs.const_mul (Real.sqrt (T / m / (M : ℝ) ^ ℓ))).const_mul σ).const_add
    ((r - σ ^ 2 / 2) * T)).exp.const_mul s₀

/-- **`E[F(S_T)]` can be computed from the increments of any level** (Giles 2015, §5.1): for
`m, M ≥ 1`, `∫ F(gbmExactM … ℓ) dN(0,1)^{⊗ℕ} = ∫ F(s₀ e^{(r − σ²/2)T + σ√T w}) dN(0, 1)(w)`, since
`blockAvg n` preserves `N(0,1)^{⊗ℕ}` (`measurePreserving_blockAvg`), so
`(Z_0 + ⋯ + Z_{n−1})/√n ∼ N(0, 1)`. -/
lemma integral_comp_gbmExactM (r σ T s₀ : ℝ) {m M : ℕ} (hm : 0 < m) (hM : 0 < M) (ℓ : ℕ)
    {F : ℝ → ℝ} (hF : Measurable F) :
    ∫ z, F (gbmExactM r σ T s₀ m M ℓ z) ∂stdNormalSeq =
      ∫ w, F (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1 := by
  have hn : 0 < m * M ^ ℓ := Nat.mul_pos hm (pow_pos hM ℓ)
  have hG : Measurable fun w : ℝ =>
      F (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) := hF.comp (by fun_prop)
  simp_rw [gbmExactM_eq_blockAvg]
  exact integral_comp_of_measurePreserving
    ((measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0).comp
      (measurePreserving_blockAvg hn)) hG.aestronglyMeasurable

/-- With one step on level `0` the exact solution of Giles 2015, §5.1 is
`s₀ e^{(r − σ²/2)T + σ√T Z_0}`. -/
lemma gbmExactM_one_zero (r σ T s₀ : ℝ) (M : ℕ) (z : ℕ → ℝ) :
    gbmExactM r σ T s₀ 1 M 0 z =
      s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * z 0)) := by
  unfold gbmExactM
  simp only [Nat.cast_one, div_one, pow_zero, one_mul, Finset.range_one, Finset.sum_singleton]

/-- The exact solution (Giles 2015, §5.1) as a product of the one-step factors
`e^{(r − σ²/2)h + σ√h Z_i}`, `h = (T/m) M^{−ℓ}` (`m, M > 0`). -/
lemma gbmExactM_eq_prod (r σ T s₀ : ℝ) {m M : ℕ} (hm : 0 < m) (hM : 0 < M) (ℓ : ℕ)
    (z : ℕ → ℝ) :
    gbmExactM r σ T s₀ m M ℓ z =
      s₀ * ∏ i ∈ range (m * M ^ ℓ), gbmExpFactor r σ (T / m / (M : ℝ) ^ ℓ) (z i) := by
  unfold gbmExactM
  rw [← gbmExp_eq_prod, cast_mul_pow_mul_div hm hM]

/-- The exact solution of Giles 2015, §5.1 is square integrable under `N(0,1)^{⊗ℕ}`. -/
lemma memLp_gbmExactM (r σ T s₀ : ℝ) {m M : ℕ} (hm : 0 < m) (hM : 0 < M) (ℓ : ℕ) :
    MemLp (gbmExactM r σ T s₀ m M ℓ) 2 stdNormalSeq := by
  refine (memLp_two_iff_integrable_sq
    (measurable_gbmExactM r σ T s₀ m M ℓ).aestronglyMeasurable).2 ?_
  have e : (fun z => gbmExactM r σ T s₀ m M ℓ z ^ 2) = fun z =>
      s₀ ^ 2 * ∏ i ∈ range (m * M ^ ℓ), gbmExpFactor r σ (T / m / (M : ℝ) ^ ℓ) (z i) ^ 2 := by
    funext z
    rw [gbmExactM_eq_prod r σ T s₀ hm hM, mul_pow, ← Finset.prod_pow]
  rw [e]
  exact (integrable_prod_stdNormalSeq ((measurable_gbmExpFactor r σ _).pow_const 2)
    (integrable_gbmExpFactor_sq r σ _) _).const_mul _

/-- The Euler–Maruyama value of GBM after `n` steps of size `h` (Giles 2015, §5.1) is a
measurable function of the increments. -/
lemma measurable_gbmEMn (r σ h s₀ : ℝ) (n : ℕ) :
    Measurable fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z n := by
  have e : (fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z n) =
      fun z => s₀ * ∏ i ∈ range n, gbmEMFactor r σ h (z i) :=
    funext fun z => emPath_gbm r σ h s₀ z n
  rw [e]
  exact (Finset.measurable_prod _ fun i _ =>
    (measurable_gbmEMFactor r σ h).comp (measurable_pi_apply i)).const_mul s₀

/-- The Euler–Maruyama value of GBM after `n` steps of size `h` (Giles 2015, §5.1) is square
integrable under `N(0,1)^{⊗ℕ}`. -/
lemma memLp_gbmEMn (r σ h s₀ : ℝ) (n : ℕ) :
    MemLp (fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z n) 2 stdNormalSeq := by
  refine (memLp_two_iff_integrable_sq (measurable_gbmEMn r σ h s₀ n).aestronglyMeasurable).2 ?_
  have e : (fun z => emPath (gbmDrift r) (gbmVol σ) h s₀ z n ^ 2) =
      fun z => s₀ ^ 2 * ∏ i ∈ range n, gbmEMFactor r σ h (z i) ^ 2 := by
    funext z
    rw [emPath_gbm, mul_pow, ← Finset.prod_pow]
  rw [e]
  exact (integrable_prod_stdNormalSeq ((measurable_gbmEMFactor r σ _).pow_const 2)
    (integrable_gbmEMFactor_sq r σ _) _).const_mul _

/-- **The strong error on level `ℓ` for refinement factor `M`** (Giles 2015, §5.1, p. 29: "the
strong error for the Euler discretisation with timestep `h` is `O(h^{1/2})`, so that
`E[‖S − Ŝ‖²] = O(h)`"): `E[(S_T − Ŝ_ℓ)²] ≤ C(T) h_ℓ` with `h_ℓ = (T/m) M^{−ℓ}`, `m M^ℓ` steps, and
the constant `C(T)` of `gbm_em_strong_error`. -/
lemma gbm_strong_error_M (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m M : ℕ} (hm : 0 < m)
    (hM : 0 < M) (ℓ : ℕ) :
    ∫ z, (gbmExactM r σ T s₀ m M ℓ z -
        emPath (gbmDrift r) (gbmVol σ) (T / m / (M : ℝ) ^ ℓ) s₀ z (m * M ^ ℓ)) ^ 2
        ∂stdNormalSeq ≤
      gbmStrongConst r σ T s₀ * (T / m / (M : ℝ) ^ ℓ) := by
  have hh : 0 ≤ T / m / (M : ℝ) ^ ℓ := by positivity
  have h := gbm_em_strong_error r σ s₀ hh (m * M ^ ℓ)
  rw [cast_mul_pow_mul_div hm hM] at h
  exact h

/-- The squared strong error on level `ℓ` (Giles 2015, §5.1, refinement factor `M`) is
integrable. -/
lemma integrable_sq_gbm_err_M (r σ T s₀ : ℝ) {m M : ℕ} (hm : 0 < m) (hM : 0 < M) (ℓ : ℕ) :
    Integrable (fun z => (gbmExactM r σ T s₀ m M ℓ z -
      emPath (gbmDrift r) (gbmVol σ) (T / m / (M : ℝ) ^ ℓ) s₀ z (m * M ^ ℓ)) ^ 2) stdNormalSeq :=
  ((memLp_gbmExactM r σ T s₀ hm hM ℓ).sub (memLp_gbmEMn r σ _ s₀ _)).integrable_sq

/-- **The weak error for refinement factor `M` is at most `K √(C(T) h_ℓ)`** (Giles 2015, §5.1,
p. 29: "On level `ℓ`, the uniform timestep is taken to be `h_ℓ = h₀ M^ℓ` [read `h₀ M^{−ℓ}`], for
some integer `M`. The timestep `h₀` on the coarsest level is often taken to be the interval length
`T` … but this is not required").  For a `K`-Lipschitz `g`, `T ≥ 0`, `m, M ≥ 1`, `h₀ = T/m` and
`h_ℓ = h₀ M^{−ℓ}`, the Euler–Maruyama payoff after `m M^ℓ` steps of size `h_ℓ` satisfies
`|E[g(Ŝ_ℓ)] − E[g(S_T)]| ≤ K √(C(T) h_ℓ)` with `C(T)` of `gbm_em_strong_error`: the rate
`α = ½ log₂ M` in Theorem 1's base `2`, from the strong error alone.  This is weaker than the
paper's weak rate (p. 30: "If `h_ℓ = 4^{−ℓ}h₀` … then this gives `α = 2`", i.e. weak order one in
`h`, `α = log₂ M`), which is not proved here; the rate proved suffices for the complexity
(`gbm_mlmc_theorem1_M`), since `α ≥ ½ min(β, γ)`. -/
theorem gbm_weak_error_le_M (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m M : ℕ} (hm : 0 < m)
    (hM : 0 < M) {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (ℓ : ℕ) :
    |∫ z, emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))) ℓ z
        ∂stdNormalSeq -
      ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1| ≤
      K * Real.sqrt (gbmStrongConst r σ T s₀ * (T / m / (M : ℝ) ^ ℓ)) := by
  obtain ⟨hK, hgc⟩ := continuous_of_abs_sub_le hg
  have hC := gbmStrongConst_nonneg r σ s₀ hT
  set F : (ℕ → ℝ) → ℝ :=
    fun z => emPath (gbmDrift r) (gbmVol σ) (T / m / (M : ℝ) ^ ℓ) s₀ z (m * M ^ ℓ) with hFdef
  set X : (ℕ → ℝ) → ℝ := gbmExactM r σ T s₀ m M ℓ with hXdef
  have hA : MemLp (fun z => g (F z)) 2 stdNormalSeq :=
    memLp_two_comp_of_abs_sub_le hg (memLp_gbmEMn r σ _ s₀ _)
  have hB : MemLp (fun z => g (X z)) 2 stdNormalSeq :=
    memLp_two_comp_of_abs_sub_le hg (memLp_gbmExactM r σ T s₀ hm hM ℓ)
  have e1 : ∫ z, emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
        (fun ℓ path => g (path (m * M ^ ℓ))) ℓ z ∂stdNormalSeq -
      ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1 =
      ∫ z, g (F z) - g (X z) ∂stdNormalSeq := by
    rw [integral_sub (hA.integrable one_le_two) (hB.integrable one_le_two), hXdef,
      integral_comp_gbmExactM r σ T s₀ hm hM ℓ hgc.measurable]
    rfl
  have hD : MemLp (fun z => g (F z) - g (X z)) 2 stdNormalSeq := hA.sub hB
  have hpt : ∀ z, (g (F z) - g (X z)) ^ 2 ≤ K ^ 2 * (X z - F z) ^ 2 := fun z => by
    have h1 := hg (F z) (X z)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    calc _ ≤ K ^ 2 * (F z - X z) ^ 2 := h2
      _ = _ := by ring
  have hint : ∫ z, (g (F z) - g (X z)) ^ 2 ∂stdNormalSeq ≤
      K ^ 2 * ∫ z, (X z - F z) ^ 2 ∂stdNormalSeq := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
      ((integrable_sq_gbm_err_M r σ T s₀ hm hM ℓ).const_mul _) (Filter.Eventually.of_forall hpt)
  have hstrong := gbm_strong_error_M r σ s₀ hT hm hM ℓ
  have hh : 0 ≤ T / m / (M : ℝ) ^ ℓ := by positivity
  have hsq : (∫ z, g (F z) - g (X z) ∂stdNormalSeq) ^ 2 ≤
      (K * Real.sqrt (gbmStrongConst r σ T s₀ * (T / m / (M : ℝ) ^ ℓ))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hC hh)]
    calc _ ≤ ∫ z, (g (F z) - g (X z)) ^ 2 ∂stdNormalSeq := sq_integral_le_integral_sq_of_memLp hD
      _ ≤ _ := hint.trans (mul_le_mul_of_nonneg_left hstrong (sq_nonneg K))
  rw [e1]
  have := sq_le_sq.1 hsq
  rwa [abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ K * Real.sqrt (gbmStrongConst r σ T s₀ * (T / m / (M : ℝ) ^ ℓ)))] at this

/-- **The variance of the corrections for refinement factor `M`** (Giles 2015, §5.1, p. 29:
"`V_ℓ ≡ V[P_ℓ − P_{ℓ−1}] ≤ 2(V[P − P_ℓ] + V[P − P_{ℓ−1}])`, and hence `V_ℓ = O(h_ℓ)`", and p. 30:
"If `h_ℓ = 4^{−ℓ}h₀` … `β = 2`").  For a `K`-Lipschitz `g`, `T ≥ 0`, `m, M ≥ 1` and `h₀ = T/m`, the
correction on level `ℓ + 1`, the payoff of the fine path with `m M^{ℓ+1}` steps minus the payoff of
the coarse path with `m M^ℓ` steps driven by the block sums of the same increments (`emCoarseM`),
has variance at most `2K² C(T) h₀ (M + 1) M^{−(ℓ+1)}`: `V_ℓ = O(h_ℓ) = O(2^{−ℓ log₂ M})`,
`β = log₂ M`. -/
theorem gbm_correction_variance_le_M (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m M : ℕ} (hm : 0 < m)
    (hM : 0 < M) {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) (ℓ : ℕ) :
    variance (fineCoarseDiff
        (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
        (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
        (ℓ + 1)) stdNormalSeq ≤
      2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) / (M : ℝ) ^ (ℓ + 1) := by
  obtain ⟨-, hgc⟩ := continuous_of_abs_sub_le hg
  have hMp := measurePreserving_blockAvg hM
  have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
  set F : ℕ → (ℕ → ℝ) → ℝ :=
    fun k z => emPath (gbmDrift r) (gbmVol σ) (T / m / (M : ℝ) ^ k) s₀ z (m * M ^ k) with hFdef
  set X : ℕ → (ℕ → ℝ) → ℝ := fun k => gbmExactM r σ T s₀ m M k with hXdef
  have e : fineCoarseDiff
      (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
      (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
      (ℓ + 1) = fun z => g (F (ℓ + 1) z) - g (F ℓ (blockAvg M z)) := by
    funext z
    show emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ)))
        (ℓ + 1) z -
      emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))) ℓ z = _
    rw [emCoarseM_eq _ _ _ _ hM]
    rfl
  rw [e]
  have hm1 : Measurable (F (ℓ + 1)) := measurable_gbmEMn r σ _ s₀ _
  have hm0 : Measurable fun z => F ℓ (blockAvg M z) :=
    (measurable_gbmEMn r σ _ s₀ _).comp hMp.measurable
  have hY : AEStronglyMeasurable (fun z => g (F (ℓ + 1) z) - g (F ℓ (blockAvg M z)))
      stdNormalSeq :=
    ((hgc.measurable.comp hm1).sub (hgc.measurable.comp hm0)).aestronglyMeasurable
  refine (variance_le_expectation_sq hY).trans ?_
  simp only [Pi.pow_apply]
  have hI1 : Integrable (fun z => (X (ℓ + 1) z - F (ℓ + 1) z) ^ 2) stdNormalSeq :=
    integrable_sq_gbm_err_M r σ T s₀ hm hM (ℓ + 1)
  have hI0' : Integrable (fun z => (X ℓ z - F ℓ z) ^ 2) stdNormalSeq :=
    integrable_sq_gbm_err_M r σ T s₀ hm hM ℓ
  have hI0 : Integrable (fun z => (X ℓ (blockAvg M z) - F ℓ (blockAvg M z)) ^ 2) stdNormalSeq :=
    (hMp.integrable_comp hI0'.aestronglyMeasurable).2 hI0'
  have hpt : ∀ z, (g (F (ℓ + 1) z) - g (F ℓ (blockAvg M z))) ^ 2 ≤
      2 * K ^ 2 * (X (ℓ + 1) z - F (ℓ + 1) z) ^ 2 +
        2 * K ^ 2 * (X ℓ (blockAvg M z) - F ℓ (blockAvg M z)) ^ 2 := fun z => by
    have h1 := hg (F (ℓ + 1) z) (F ℓ (blockAvg M z))
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    have hx : X ℓ (blockAvg M z) = X (ℓ + 1) z := gbmExactM_blockAvg r σ T s₀ m hM ℓ z
    rw [hx]
    nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg (X (ℓ + 1) z - F (ℓ + 1) z +
      (X (ℓ + 1) z - F ℓ (blockAvg M z))))]
  have hK2 : (0 : ℝ) ≤ 2 * K ^ 2 := by positivity
  have hs1 := gbm_strong_error_M r σ s₀ hT hm hM (ℓ + 1)
  have hs0 := gbm_strong_error_M r σ s₀ hT hm hM ℓ
  calc ∫ z, (g (F (ℓ + 1) z) - g (F ℓ (blockAvg M z))) ^ 2 ∂stdNormalSeq
      ≤ ∫ z, (2 * K ^ 2 * (X (ℓ + 1) z - F (ℓ + 1) z) ^ 2 +
          2 * K ^ 2 * (X ℓ (blockAvg M z) - F ℓ (blockAvg M z)) ^ 2) ∂stdNormalSeq :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
          ((hI1.const_mul (2 * K ^ 2)).add (hI0.const_mul (2 * K ^ 2)))
          (Filter.Eventually.of_forall hpt)
    _ = 2 * K ^ 2 * ∫ z, (X (ℓ + 1) z - F (ℓ + 1) z) ^ 2 ∂stdNormalSeq +
        2 * K ^ 2 * ∫ z, (X ℓ z - F ℓ z) ^ 2 ∂stdNormalSeq := by
        rw [integral_add (hI1.const_mul _) (hI0.const_mul _), integral_const_mul,
          integral_const_mul, integral_comp_of_measurePreserving hMp hI0'.aestronglyMeasurable]
    _ ≤ 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m / (M : ℝ) ^ (ℓ + 1))) +
        2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m / (M : ℝ) ^ ℓ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hs1 hK2) (mul_le_mul_of_nonneg_left hs0 hK2)
    _ = 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) / (M : ℝ) ^ (ℓ + 1) := by
        rw [pow_succ]
        field_simp
        ring

/-- `2^{ℓ log₂ M} = M^ℓ` (the rates of Giles 2015, §5.1, in Theorem 1's base `2`). -/
lemma two_rpow_logb_mul {M : ℕ} (hM : 0 < M) (ℓ : ℕ) :
    (2 : ℝ) ^ (Real.logb 2 M * (ℓ : ℝ)) = (M : ℝ) ^ ℓ := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num) (by norm_num) (Nat.cast_pos.2 hM), Real.rpow_natCast]

/-- `2^{−ℓ log₂ M} = M^{−ℓ}` (Giles 2015, §5.1). -/
lemma two_rpow_neg_logb_mul {M : ℕ} (hM : 0 < M) (ℓ : ℕ) :
    (2 : ℝ) ^ (-(Real.logb 2 M * (ℓ : ℝ))) = ((M : ℝ) ^ ℓ)⁻¹ := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), two_rpow_logb_mul hM]

/-- `√(M^{−ℓ}) = 2^{−(½ log₂ M) ℓ}` (Giles 2015, §5.1). -/
lemma sqrt_inv_pow_eq_two_rpow {M : ℕ} (hM : 0 < M) (ℓ : ℕ) :
    Real.sqrt (((M : ℝ) ^ ℓ)⁻¹) = (2 : ℝ) ^ (-(Real.logb 2 M / 2 * (ℓ : ℝ))) := by
  rw [← two_rpow_neg_logb_mul hM, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- **Theorem 1 for GBM with refinement factor `M` and any coarsest step `T/m`, with no assumed
rate** (Giles 2015, §5.1, pp. 29–30: "On level `ℓ`, the uniform timestep is taken to be
`h_ℓ = h₀ M^ℓ` [read `h₀ M^{−ℓ}`], for some integer `M`. The timestep `h₀` on the coarsest level is
often taken to be the interval length `T` … but this is not required" … "If `h_ℓ = 4^{−ℓ}h₀`, as in
the numerical examples in (Giles 2008b), then this gives `α = 2`, `β = 2` and `γ = 2`.
Alternatively, if `h_ℓ = 2^{−ℓ}h₀` with twice as many timesteps on each successive level, as used
in the numerical examples in this article, then `α = 1`, `β = 1` and `γ = 1`. In either case,
Theorem 1 gives the complexity to achieve a root-mean-square error of `ε` to be
`O(ε^{−2}(log ε)²)`").  Let `dS = rS dt + σS dW`, `T ≥ 0`, `m ≥ 1`, `M ≥ 2` and `g` `K`-Lipschitz.
Level `ℓ` uses `m M^ℓ` Euler–Maruyama steps of size `h_ℓ = h₀ M^{−ℓ}`, `h₀ = T/m` (`emFineM`); the
coarse path of a level-`(ℓ+1)` sample takes `m M^ℓ` steps of size `M h_{ℓ+1}` driven by the sums of
`M` fine increments (`emCoarseM`, `blockAvg`); the samples are independent and a level-`ℓ` sample
costs `m M^ℓ`.  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and
`N_ℓ ≥ 1` for which the multilevel estimator of
`E[g(S_T)] = E[g(s₀ e^{(r − σ²/2)T + σ√T W})]`, `W ∼ N(0, 1)`, has a square-integrable error with
mean square `< ε²`, and cost `∑_{ℓ≤L} N_ℓ m M^ℓ ≤ c₄ ε⁻²(log ε)²`.  In Theorem 1's base `2` the
rates are `β = γ = log₂ M` (`gbm_correction_variance_le_M`; cost `m M^ℓ = m 2^{ℓ log₂ M}`) and
`α = ½ log₂ M` (`gbm_weak_error_le_M`), and (2.4) holds (`integral_emCoarseM`); this is
`em_mlmc_theorem1_M`.  Deviation: the paper's weak rate (`α = 2` for `M = 4`, `α = 1` for `M = 2`,
weak order one in `h`) is replaced by the strong-error rate `α = ½ log₂ M`, which suffices since
`α ≥ ½ min(β, γ)`; so the paper's `α` is not proved, but its complexity is.  The coarsest step is
`h₀ = T/m` (`m = 1` is the usual `h₀ = T`), the steps for which the grid reaches `T`.  For `M = 2`,
`m = 1` see also `gbm_mlmc_theorem1`. -/
theorem gbm_mlmc_theorem1_M (r σ s₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) {m M : ℕ} (hm : 0 < m)
    (hM : 2 ≤ M) {g : ℝ → ℝ} {K : ℝ} (hg : ∀ x y, |g x - g y| ≤ K * |x - y|) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
              (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
                (fun ℓ path => g (path (m * M ^ ℓ)))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff
              (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
              (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
                (fun ℓ path => g (path (m * M ^ ℓ)))))
              (fun p x => x p) ℓ (N ℓ) x -
            ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w)))
              ∂gaussianReal 0 1) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * (m * (M : ℝ) ^ ℓ) ≤
          c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  have hM0 : 0 < M := by omega
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hβ : 0 < Real.logb 2 M := Real.logb_pos (by norm_num) hM1
  obtain ⟨hK, hgc⟩ := continuous_of_abs_sub_le hg
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs stdNormalSeq
  have hC := gbmStrongConst_nonneg r σ s₀ hT
  have hTm : 0 ≤ T / m := div_nonneg hT hm'.le
  set P : (ℕ → ℝ) → ℝ :=
    fun z => g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * z 0))) with hPdef
  have hPint : ∫ z, P z ∂stdNormalSeq =
      ∫ w, g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) ∂gaussianReal 0 1 := by
    have hF : Measurable fun w : ℝ =>
        g (s₀ * Real.exp ((r - σ ^ 2 / 2) * T + σ * (Real.sqrt T * w))) :=
      hgc.measurable.comp (by fun_prop)
    exact integral_comp_of_measurePreserving
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) 0) hF.aestronglyMeasurable
  have eP : P = fun z => g (gbmExactM r σ T s₀ 1 M 0 z) := funext fun z => by
    rw [hPdef, gbmExactM_one_zero]
  have hP : MemLp P 2 stdNormalSeq := by
    rw [eP]
    exact memLp_two_comp_of_abs_sub_le hg (memLp_gbmExactM r σ T s₀ one_pos hM0 0)
  have hPfm : ∀ ℓ, Measurable (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => g (path (m * M ^ ℓ))) ℓ) := fun ℓ => by
    have h := hgc.measurable.comp (measurable_gbmEMn r σ (T / m / (M : ℝ) ^ ℓ) s₀ (m * M ^ ℓ))
    exact h
  have hPf : ∀ ℓ, MemLp (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => g (path (m * M ^ ℓ))) ℓ) 2 stdNormalSeq := fun ℓ => by
    have h := memLp_two_comp_of_abs_sub_le hg
      (memLp_gbmEMn r σ (T / m / (M : ℝ) ^ ℓ) s₀ (m * M ^ ℓ))
    exact h
  -- (i): the weak rate `α = ½ log₂ M`
  have hc₁ : 0 < K * Real.sqrt (gbmStrongConst r σ T s₀ * (T / m)) + 1 := by positivity
  have h_i : ∀ ℓ : ℕ, |∫ z, emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => g (path (m * M ^ ℓ))) ℓ z - P z ∂stdNormalSeq| ≤
      (K * Real.sqrt (gbmStrongConst r σ T s₀ * (T / m)) + 1) *
        (2 : ℝ) ^ (-(Real.logb 2 M / 2 * (ℓ : ℝ))) := fun ℓ => by
    have h := gbm_weak_error_le_M r σ s₀ hT hm hM0 hg ℓ
    rw [← hPint, ← integral_sub ((hPf ℓ).integrable one_le_two) (hP.integrable one_le_two)] at h
    have e : Real.sqrt (gbmStrongConst r σ T s₀ * (T / m / (M : ℝ) ^ ℓ)) =
        Real.sqrt (gbmStrongConst r σ T s₀ * (T / m)) *
          (2 : ℝ) ^ (-(Real.logb 2 M / 2 * (ℓ : ℝ))) := by
      rw [← sqrt_inv_pow_eq_two_rpow hM0, ← Real.sqrt_mul (mul_nonneg hC hTm), mul_assoc,
        div_eq_mul_inv (T / m)]
    rw [e] at h
    have hpos : 0 < (2 : ℝ) ^ (-(Real.logb 2 M / 2 * (ℓ : ℝ))) := by positivity
    calc _ ≤ K * (Real.sqrt (gbmStrongConst r σ T s₀ * (T / m)) *
          (2 : ℝ) ^ (-(Real.logb 2 M / 2 * (ℓ : ℝ)))) := h
      _ ≤ _ := by nlinarith
  -- (iii): the variance rate `β = log₂ M`
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = variance (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
      (fun ℓ path => g (path (m * M ^ ℓ))) 0) stdNormalSeq := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := hV₀ ▸ variance_nonneg _ _
  have hc₂ : 0 < V₀ + 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) + 1 := by
    positivity
  have h_iii : ∀ ℓ, variance (fineCoarseDiff
      (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ))))
      (emCoarseM (gbmDrift r) (gbmVol σ) (T / m) s₀ M (fun ℓ path => g (path (m * M ^ ℓ)))) ℓ)
      stdNormalSeq ≤
      (V₀ + 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) + 1) *
        (2 : ℝ) ^ (-(Real.logb 2 M * (ℓ : ℝ))) := by
    intro ℓ
    rw [two_rpow_neg_logb_mul hM0]
    cases ℓ with
    | zero =>
      change variance (emFineM (gbmDrift r) (gbmVol σ) (T / m) s₀ M
        (fun ℓ path => g (path (m * M ^ ℓ))) 0) stdNormalSeq ≤ _
      rw [pow_zero, inv_one, mul_one, ← hV₀]
      have : 0 ≤ 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) := by positivity
      linarith
    | succ ℓ =>
      have hv := gbm_correction_variance_le_M r σ s₀ hT hm hM0 hg ℓ
      have hinv : 0 < ((M : ℝ) ^ (ℓ + 1))⁻¹ := by positivity
      calc _ ≤ 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) /
            (M : ℝ) ^ (ℓ + 1) := hv
        _ = 2 * K ^ 2 * (gbmStrongConst r σ T s₀ * (T / m)) * (M + 1) *
            ((M : ℝ) ^ (ℓ + 1))⁻¹ := by
          rw [div_eq_mul_inv]
        _ ≤ _ := by nlinarith
  -- (iv): a level-`ℓ` sample costs `m M^ℓ = m 2^{ℓ log₂ M}`
  have h_iv : ∀ ℓ : ℕ, (m : ℝ) * (M : ℝ) ^ ℓ ≤ m * (2 : ℝ) ^ (Real.logb 2 M * (ℓ : ℝ)) :=
    fun ℓ => by rw [two_rpow_logb_mul hM0]
  obtain ⟨c₄, hc₄, h⟩ := em_mlmc_theorem1_M
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => stdNormalSeq)
    (gbmDrift r) (gbmVol σ) (T / m) s₀ hM0 (fun ℓ path => g (path (m * M ^ ℓ))) P
    (fun p x => x p) (fun ℓ _ _ => (m : ℝ) * (M : ℝ) ^ ℓ)
    (fun ℓ => (m : ℝ) * (M : ℝ) ^ ℓ) (α := Real.logb 2 M / 2) (β := Real.logb 2 M)
    (γ := Real.logb 2 M) (by positivity) hβ hβ hc₁ hc₂ hm' (by rw [min_self]) hω hind
    (hP.integrable one_le_two) hPfm hPf (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i h_iii h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  rw [hPint] at hint hmse
  refine ⟨L, N, hN, hint, hmse, ?_⟩
  simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul] at hcost
  rw [complexityBound_of_eq rfl ε] at hcost
  exact hcost

/-! ### Haas–Giles §3.2: the method-2 iteration is well defined -/

/-- **The least-squares problem (16) of method 2 has a minimiser** (Haas–Giles 2025, §3.2: "Then we
perform a least-squared minimisation of (16) `∑_{j=1}^{2^d} (Z_{π(j)} − Z̃_j)²` … In this
minimisation problem, the variables `Z̃_j` are considered as linear variables of the decision
variables, which are the values `X_j` from the small LUT that we want to optimise").  For a finite
index set `ι`, a real vector space `X` of decision variables, a linear map `A : X → ℝ^ι`
(`Z̃ = A x`) and targets `b ∈ ℝ^ι` (`b_j = Z_{π(j)}`), some `x` minimises `∑_i (b_i − (A x)_i)²`:
the range of `A` in `ℓ²(ι)` is finite-dimensional, hence complete, and the distance from `b` to it
is attained (`Submodule.exists_norm_eq_iInf_of_complete_subspace`).  `X` need not be
finite-dimensional, and the minimiser need not be unique. -/
theorem exists_lsq_minimiser {ι X : Type*} [Fintype ι] [AddCommGroup X] [Module ℝ X]
    (A : X →ₗ[ℝ] ι → ℝ) (b : ι → ℝ) :
    ∃ x : X, ∀ y : X, ∑ i, (b i - A x i) ^ 2 ≤ ∑ i, (b i - A y i) ^ 2 := by
  let e : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap
  let K : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.range (e ∘ₗ A)
  obtain ⟨v, hvK, hv⟩ :=
    K.exists_norm_eq_iInf_of_complete_subspace K.complete_of_finiteDimensional (e b)
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hvK
  have key : ∀ c : ι → ℝ, ‖e b - e c‖ ^ 2 = ∑ i, (b i - c i) ^ 2 := fun c => by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  refine ⟨x, fun y => ?_⟩
  have hbdd : BddBelow (Set.range fun w : (K : Set (EuclideanSpace ℝ ι)) =>
      ‖e b - (w : EuclideanSpace ℝ ι)‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact norm_nonneg _
  have hmem : (e ∘ₗ A) y ∈ (K : Set (EuclideanSpace ℝ ι)) := LinearMap.mem_range_self _ y
  have hle : ‖e b - (e ∘ₗ A) x‖ ≤ ‖e b - (e ∘ₗ A) y‖ := by
    rw [hv]
    exact ciInf_le hbdd (⟨(e ∘ₗ A) y, hmem⟩ : (K : Set (EuclideanSpace ℝ ι)))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rwa [LinearMap.comp_apply, LinearMap.comp_apply, key, key] at h2

/-- **The method-2 iteration is well defined and its objective is eventually constant**
(Haas–Giles 2025, §3.2: "Then we perform a least-squared minimisation of (16) … After this step
update the permutation `π` by ordering the resulting `Z̃_j` and repeat the least-squares
optimisation. The algorithm stops when the permutation has converged").  For the objective (16)
`F(π, x) = ∑_j (Z_{π(j)} − (A x)_j)²` with `A` linear (the `Z̃_j` are linear in the small-LUT
values) and `π` a permutation of the finite index set, and for every initial permutation `π₀`,
there are sequences `π_k`, `x_k` with `π_0 = π₀` such that each `x_k` minimises `F(π_k, ·)`
(`exists_lsq_minimiser`) and each `π_{k+1}` minimises `F(·, x_k)` over the permutations: the
hypotheses `hx`, `hπ` of `alternating_min_antitone` and `alternating_min_eventually_const` can be
met, and along these sequences `F(π_k, x_k)` is constant from some `K` on.  Deviation: the paper's
update orders the `Z̃_j`; that minimises `F(·, x_k)` when the targets `Z` are sorted
(`sorting_minimises`), and here the permutation step is any minimiser; the sorting step itself is
`method2_sorting_iteration_exists`. -/
theorem method2_iteration_exists {ι X : Type*} [Fintype ι] [AddCommGroup X] [Module ℝ X]
    (A : X →ₗ[ℝ] ι → ℝ) (Z : ι → ℝ) (π₀ : Equiv.Perm ι) :
    ∃ (π : ℕ → Equiv.Perm ι) (x : ℕ → X), π 0 = π₀ ∧
      (∀ k y, ∑ j, (Z (π k j) - A (x k) j) ^ 2 ≤ ∑ j, (Z (π k j) - A y j) ^ 2) ∧
      (∀ k (p : Equiv.Perm ι),
        ∑ j, (Z (π (k + 1) j) - A (x k) j) ^ 2 ≤ ∑ j, (Z (p j) - A (x k) j) ^ 2) ∧
      ∃ K, ∀ k, K ≤ k →
        ∑ j, (Z (π k j) - A (x k) j) ^ 2 = ∑ j, (Z (π K j) - A (x K) j) ^ 2 := by
  classical
  choose T hT using fun p : Equiv.Perm ι => exists_lsq_minimiser A (fun j => Z (p j))
  choose S hS using fun x : X => Finite.exists_min fun p : Equiv.Perm ι =>
    ∑ j, (Z (p j) - A x j) ^ 2
  let π : ℕ → Equiv.Perm ι := fun k => Nat.rec π₀ (fun _ p => S (T p)) k
  have hx : ∀ k y, ∑ j, (Z (π k j) - A (T (π k)) j) ^ 2 ≤ ∑ j, (Z (π k j) - A y j) ^ 2 :=
    fun k y => hT (π k) y
  have hπ : ∀ k (p : Equiv.Perm ι),
      ∑ j, (Z (π (k + 1) j) - A (T (π k)) j) ^ 2 ≤ ∑ j, (Z (p j) - A (T (π k)) j) ^ 2 :=
    fun k p => hS (T (π k)) p
  refine ⟨π, fun k => T (π k), rfl, hx, hπ, ?_⟩
  exact alternating_min_eventually_const (fun (p : Equiv.Perm ι) (x : X) =>
    ∑ j, (Z (p j) - A x j) ^ 2) hx hπ

/-- **A ranking permutation exists** (Haas–Giles 2025, §3.2: "ordering the outputs `Z̃_j` in
ascending order. This step defines a permutation `π` such that `π(j)` gives the position of the
random number `Z̃_j` in the ordered list"): for `f : Fin n → ℝ` some permutation `π` satisfies
`f i < f j → π i < π j`, namely the inverse of the sorting permutation `Tuple.sort f`. -/
lemma exists_ranking {n : ℕ} (f : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), ∀ i j, f i < f j → π i < π j := by
  refine ⟨(Tuple.sort f).symm, fun i j hij => ?_⟩
  by_contra h
  have hle := Tuple.monotone_sort f (not_lt.1 h)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hle
  exact absurd hij (not_lt.2 hle)

/-- **The paper's method-2 iteration, with its sorting step, is well defined and its objective is
eventually constant** (Haas–Giles 2025, §3.2: "Then we perform a least-squared minimisation of (16)
… After this step update the permutation `π` by ordering the resulting `Z̃_j` and repeat the
least-squares optimisation. The algorithm stops when the permutation has converged").  Let the
targets be sorted, `Z_1 ≤ ⋯ ≤ Z_n` (`Monotone Z`), and let `A` be linear (`Z̃ = A x`, the `Z̃_j`
are linear in the small-LUT values).  For every initial permutation `π₀` there are sequences with
`π_0 = π₀` such that each `x_k` minimises (16) `∑_j (Z_{π_k(j)} − (A x_k)_j)²` for `π_k`
(`exists_lsq_minimiser`) and each `π_{k+1}` ranks the outputs `Z̃ = A x_k`
(`Z̃_i < Z̃_j → π_{k+1}(i) < π_{k+1}(j)`: `π_{k+1}(j)` is the position of `Z̃_j` in the ordered
list, `exists_ranking`); along them the objective is constant from some `K` on, since the ranking
minimises (16) over the permutations (`sorting_minimises`) and `alternating_min_eventually_const`
applies.  Ties among the `Z̃_j` may be ranked in either order. -/
theorem method2_sorting_iteration_exists {n : ℕ} {X : Type*} [AddCommGroup X] [Module ℝ X]
    (A : X →ₗ[ℝ] Fin n → ℝ) {Z : Fin n → ℝ} (hZ : Monotone Z) (π₀ : Equiv.Perm (Fin n)) :
    ∃ (π : ℕ → Equiv.Perm (Fin n)) (x : ℕ → X), π 0 = π₀ ∧
      (∀ k y, ∑ j, (Z (π k j) - A (x k) j) ^ 2 ≤ ∑ j, (Z (π k j) - A y j) ^ 2) ∧
      (∀ k i j, A (x k) i < A (x k) j → π (k + 1) i < π (k + 1) j) ∧
      ∃ K, ∀ k, K ≤ k →
        ∑ j, (Z (π k j) - A (x k) j) ^ 2 = ∑ j, (Z (π K j) - A (x K) j) ^ 2 := by
  choose T hT using fun p : Equiv.Perm (Fin n) => exists_lsq_minimiser A (fun j => Z (p j))
  choose R hR using fun f : Fin n → ℝ => exists_ranking f
  let π : ℕ → Equiv.Perm (Fin n) := fun k => Nat.rec π₀ (fun _ p => R (A (T p))) k
  have hx : ∀ k y, ∑ j, (Z (π k j) - A (T (π k)) j) ^ 2 ≤ ∑ j, (Z (π k j) - A y j) ^ 2 :=
    fun k y => hT (π k) y
  have hrank : ∀ k i j, A (T (π k)) i < A (T (π k)) j → π (k + 1) i < π (k + 1) j :=
    fun k => hR (A (T (π k)))
  have hπ : ∀ k (p : Equiv.Perm (Fin n)),
      ∑ j, (Z (π (k + 1) j) - A (T (π k)) j) ^ 2 ≤ ∑ j, (Z (p j) - A (T (π k)) j) ^ 2 :=
    fun k p => sorting_minimises hZ (A (T (π k))) (hrank k) p
  refine ⟨π, fun k => T (π k), rfl, hx, hrank, ?_⟩
  exact alternating_min_eventually_const (fun (p : Equiv.Perm (Fin n)) (x : X) =>
    ∑ j, (Z (p j) - A x j) ^ 2) hx hπ

/-! ### Giles §10.2: rounded fine increments change the law of the coarse increment -/

/-- Away from the ties `x ∈ 2^{e−d}(ℤ − ½)`, fixed-point rounding (Haas–Giles 2025, §4.1) is odd:
`round_{e,d}(−x) = −round_{e,d}(x)` (used for Giles 2015, §10.2). -/
lemma roundFixed_neg_of_notMem (e : ℤ) (d : ℕ) {x : ℝ}
    (hx : x ∉ Set.range fun n : ℤ => (2 : ℝ) ^ (e - d) * ((n : ℝ) - 1 / 2)) :
    roundFixed e d (-x) = -roundFixed e d x := by
  have hc : (0 : ℝ) < 2 ^ (e - d) := zpow_pos two_pos _
  set c : ℝ := 2 ^ (e - d) with hcdef
  set n : ℤ := round (x / c) with hn
  have h1 := round_eq_iff.1 hn.symm
  have hne : x / c ≠ (n : ℝ) - 1 / 2 := fun h => hx ⟨n, by
    show c * ((n : ℝ) - 1 / 2) = x
    rw [← h]
    field_simp⟩
  have h2 : round (-x / c) = -n := by
    rw [round_eq_iff]
    obtain ⟨ha, hb⟩ := h1
    have ha' : (n : ℝ) - 1 / 2 < x / c := lt_of_le_of_ne ha (Ne.symm hne)
    rw [neg_div]
    push_cast
    constructor <;> linarith
  unfold roundFixed
  rw [← hcdef, h2, ← hn]
  push_cast
  ring

/-- Fixed-point rounding (Haas–Giles 2025, §4.1) is integrable under `N(0, v)`: it is within
`2^{e−d−1}` of the identity (`abs_sub_roundFixed_le`; used for Giles 2015, §10.2). -/
lemma integrable_roundFixed_gaussianReal (e : ℤ) (d : ℕ) (v : ℝ≥0) :
    Integrable (roundFixed e d) (gaussianReal 0 v) := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))
  refine (hid.abs.add (integrable_const ((2 : ℝ) ^ (e - d - 1)))).mono'
    (measurable_roundFixed e d).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have h := abs_sub_roundFixed_le e d x
  rw [Real.norm_eq_abs]
  show |roundFixed e d x| ≤ |x| + 2 ^ (e - d - 1)
  have := abs_sub_abs_le_abs_sub (roundFixed e d x) x
  rw [abs_sub_comm] at this
  linarith

/-- **Rounding a centred Gaussian variable is unbiased** (used for Giles 2015, §10.2): for
`v ≠ 0`, `∫ round_{e,d}(x) dN(0, v)(x) = 0`, since rounding is odd away from a countable set of
ties (`roundFixed_neg_of_notMem`), which is null for `N(0, v)`, and `N(0, v)` is symmetric. -/
lemma integral_roundFixed_gaussianReal (e : ℤ) (d : ℕ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, roundFixed e d x ∂gaussianReal 0 v = 0 := by
  have hS : gaussianReal 0 v (Set.range fun n : ℤ => (2 : ℝ) ^ (e - d) * ((n : ℝ) - 1 / 2)) = 0 :=
    gaussianReal_absolutelyContinuous 0 hv ((Set.countable_range _).measure_zero volume)
  have hae : ∀ᵐ x ∂gaussianReal 0 v, roundFixed e d (-x) = -roundFixed e d x :=
    ae_iff.2 (measure_mono_null (fun x hx => by
      by_contra hxS
      exact hx (roundFixed_neg_of_notMem e d hxS)) hS)
  have hmap : (gaussianReal 0 v).map (fun x => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have h1 : ∫ x, roundFixed e d x ∂gaussianReal 0 v =
      ∫ x, roundFixed e d (-x) ∂gaussianReal 0 v := by
    conv_lhs => rw [← hmap]
    rw [integral_map measurable_neg.aemeasurable]
    rw [hmap]
    exact (measurable_roundFixed e d).aestronglyMeasurable
  have h2 : ∫ x, roundFixed e d (-x) ∂gaussianReal 0 v =
      -∫ x, roundFixed e d x ∂gaussianReal 0 v := by
    rw [← integral_neg]
    exact integral_congr_ae hae
  linarith

/-- On the fine grid `qℤ`, `q = 2^{e−B−1}`, rounding to the coarse grid `2qℤ` never rounds down
(Giles 2015, §10.2): a grid point `qk` is a coarse grid point (`k` even) or a tie (`k` odd), which
`round` breaks upwards. -/
lemma le_roundFixed_mul_int (e : ℤ) (B : ℕ) (k : ℤ) :
    (2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ)) * k ≤
      roundFixed e B ((2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ)) * k) := by
  have hq : (0 : ℝ) < 2 ^ (e - ((B + 1 : ℕ) : ℤ)) := zpow_pos two_pos _
  have hc : (2 : ℝ) ^ (e - (B : ℤ)) = 2 * 2 ^ (e - ((B + 1 : ℕ) : ℤ)) := by
    rw [← zpow_one_add₀ two_ne_zero]
    congr 1
    push_cast
    ring
  set q : ℝ := 2 ^ (e - ((B + 1 : ℕ) : ℤ)) with hqdef
  unfold roundFixed
  rw [hc, show q * k / (2 * q) = (k : ℝ) / 2 by field_simp]
  set m : ℤ := round ((k : ℝ) / 2) with hm
  have h1 : (k : ℝ) / 2 + 1 / 2 < m + 1 := by
    rw [hm, round_eq]
    exact Int.lt_floor_add_one _
  have h2 : k < 2 * m + 1 := by
    have : (k : ℝ) < 2 * m + 1 := by linarith
    exact_mod_cast this
  have h3 : (k : ℝ) ≤ 2 * m := by exact_mod_cast (by omega : k ≤ 2 * m)
  nlinarith

/-- The fine rounding `round_{e,B+1}(x)` is the fine grid point `q k`, `k = round(x/q)`,
`q = 2^{e−B−1}` (Haas–Giles 2025, §4.1; used for Giles 2015, §10.2). -/
lemma roundFixed_succ_eq (e : ℤ) (B : ℕ) (x : ℝ) :
    roundFixed e (B + 1) x = (2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ)) *
      (round (x / (2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ))) : ℤ) := rfl

/-- Three values of fixed-point rounding (used for Giles 2015, §10.2), with `q = 2^{e−B−1}`:
`round_{e,B+1}(x) = q` for `x ∈ [q/2, 3q/2)`, `round_{e,B+1}(x) = 0` for `x ∈ [−q/2, q/2)`, and
`round_{e,B}(q) = 2q` (a tie, broken upwards). -/
lemma roundFixed_values (e : ℤ) (B : ℕ) :
    (∀ x ∈ Set.Ico ((2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ)) / 2)
        (3 * (2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ)) / 2),
      roundFixed e (B + 1) x = (2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ))) ∧
    (∀ x ∈ Set.Ico (-(2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ)) / 2)
        ((2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ)) / 2), roundFixed e (B + 1) x = 0) ∧
    roundFixed e B ((2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ))) =
      2 * (2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ)) := by
  have hq : (0 : ℝ) < 2 ^ (e - ((B + 1 : ℕ) : ℤ)) := zpow_pos two_pos _
  have hc : (2 : ℝ) ^ (e - (B : ℤ)) = 2 * 2 ^ (e - ((B + 1 : ℕ) : ℤ)) := by
    rw [← zpow_one_add₀ two_ne_zero]
    congr 1
    push_cast
    ring
  set q : ℝ := 2 ^ (e - ((B + 1 : ℕ) : ℤ)) with hqdef
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have hr : round (x / q) = 1 := by
      rw [round_eq_iff]
      obtain ⟨h1, h2⟩ := hx
      constructor
      · rw [le_div_iff₀ hq]
        push_cast
        linarith
      · rw [div_lt_iff₀ hq]
        push_cast
        linarith
    rw [roundFixed_succ_eq, ← hqdef, hr]
    simp
  · have hr : round (x / q) = 0 := by
      rw [round_eq_iff]
      obtain ⟨h1, h2⟩ := hx
      constructor
      · rw [le_div_iff₀ hq]
        push_cast
        linarith
      · rw [div_lt_iff₀ hq]
        push_cast
        linarith
    rw [roundFixed_succ_eq, ← hqdef, hr]
    simp
  · unfold roundFixed
    rw [hc, show q / (2 * q) = 2⁻¹ by field_simp, round_two_inv]
    simp


/-- A non-degenerate Gaussian law gives positive mass to every nonempty interval `[a, b)` (used for
Giles 2015, §10.2). -/
lemma gaussianReal_Ico_ne_zero {v : ℝ≥0} (hv : v ≠ 0) {a b : ℝ} (hab : a < b) :
    gaussianReal 0 v (Set.Ico a b) ≠ 0 := fun h => by
  have := gaussianReal_absolutelyContinuous' 0 hv h
  rw [Real.volume_Ico] at this
  exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne' this

/-- The real-valued form of `gaussianReal_Ico_ne_zero` (used for Giles 2015, §10.2). -/
lemma gaussianReal_real_Ico_pos {v : ℝ≥0} (hv : v ≠ 0) {a b : ℝ} (hab : a < b) :
    0 < (gaussianReal 0 v).real (Set.Ico a b) :=
  ENNReal.toReal_pos (gaussianReal_Ico_ne_zero hv hab) (measure_ne_top _ _)

/-- **Truncating a rounded fine increment is biased upwards** (used for Giles 2015, §10.2): for
`v ≠ 0`, `round_{e,B}(round_{e,B+1}(Z))`, `Z ∼ N(0, v)`, is integrable with mean at least
`q P(Z ∈ [q/2, 3q/2)) > 0`, `q = 2^{e−B−1}`. -/
lemma integral_roundFixed_roundFixed_pos (e : ℤ) (B : ℕ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => roundFixed e B (roundFixed e (B + 1) x)) (gaussianReal 0 v) ∧
      0 < ∫ x, roundFixed e B (roundFixed e (B + 1) x) ∂gaussianReal 0 v := by
  have hq : (0 : ℝ) < 2 ^ (e - ((B + 1 : ℕ) : ℤ)) := zpow_pos two_pos _
  obtain ⟨hv1, -, hv3⟩ := roundFixed_values e B
  set q : ℝ := 2 ^ (e - ((B + 1 : ℕ) : ℤ)) with hqdef
  set I : Set ℝ := Set.Ico (q / 2) (3 * q / 2) with hIdef
  have hm : Measurable fun x => roundFixed e B (roundFixed e (B + 1) x) :=
    (measurable_roundFixed e B).comp (measurable_roundFixed e (B + 1))
  have i1 := integrable_roundFixed_gaussianReal e (B + 1) v
  have iD : Integrable (fun x => roundFixed e B (roundFixed e (B + 1) x) -
      roundFixed e (B + 1) x) (gaussianReal 0 v) := by
    refine Integrable.of_bound (hm.sub (measurable_roundFixed e (B + 1))).aestronglyMeasurable
      ((2 : ℝ) ^ (e - B - 1)) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact abs_sub_roundFixed_le e B _
  have i2 : Integrable (fun x => roundFixed e B (roundFixed e (B + 1) x)) (gaussianReal 0 v) :=
    (i1.add iD).congr (ae_of_all _ fun x => by simp)
  have hpt : ∀ x, I.indicator (fun _ => q) x ≤
      roundFixed e B (roundFixed e (B + 1) x) - roundFixed e (B + 1) x := fun x => by
    by_cases hx : x ∈ I
    · rw [Set.indicator_of_mem hx, hv1 x hx, hv3]
      linarith
    · rw [Set.indicator_of_notMem hx, sub_nonneg, roundFixed_succ_eq]
      exact le_roundFixed_mul_int e B _
  have hI : MeasurableSet I := measurableSet_Ico
  have hlow : (gaussianReal 0 v).real I * q ≤ ∫ x, (roundFixed e B (roundFixed e (B + 1) x) -
      roundFixed e (B + 1) x) ∂gaussianReal 0 v := by
    rw [← smul_eq_mul, ← integral_indicator_const q hI]
    exact integral_mono ((integrable_const q).indicator hI) iD hpt
  have hpos : 0 < (gaussianReal 0 v).real I * q :=
    mul_pos (gaussianReal_real_Ico_pos hv (by linarith)) hq
  refine ⟨i2, ?_⟩
  rw [integral_sub i2 i1, integral_roundFixed_gaussianReal e (B + 1) hv] at hlow
  linarith

/-- Transfer along a random variable with a known law: if `X ∼ ρ` and `F` is measurable and
`ρ`-integrable, then `F ∘ X` is integrable and `E[F(X)] = ∫ F dρ` (used for Giles 2015, §10.2). -/
lemma integrable_integral_comp_of_hasLaw {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} {ρ : Measure α} {X : Ω → α} {F : α → ℝ} (hX : HasLaw X ρ μ)
    (hF : Measurable F) (hFi : Integrable F ρ) :
    Integrable (fun ω => F (X ω)) μ ∧ ∫ ω, F (X ω) ∂μ = ∫ y, F y ∂ρ := by
  refine ⟨?_, hX.integral_comp hF.aestronglyMeasurable⟩
  rw [← hX.map_eq] at hFi
  exact hFi.comp_aemeasurable hX.aemeasurable

/-- Two independent `N(0, v)` variables have the joint law `N(0, v) ⊗ N(0, v)` (used for Giles
2015, §10.2). -/
lemma hasLaw_pair_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {v : ℝ≥0}
    {X₁ X₂ : Ω → ℝ} (h₁ : HasLaw X₁ (gaussianReal 0 v) μ) (h₂ : HasLaw X₂ (gaussianReal 0 v) μ)
    (hind : IndepFun X₁ X₂ μ) :
    HasLaw (fun ω => (X₁ ω, X₂ ω)) ((gaussianReal 0 v).prod (gaussianReal 0 v)) μ := by
  have : IsProbabilityMeasure μ := h₁.isProbabilityMeasure_iff.2 inferInstance
  exact ⟨h₁.aemeasurable.prodMk h₂.aemeasurable, by
    rw [hind.map_prod_eq_prod_map_map h₁.aemeasurable h₂.aemeasurable, h₁.map_eq, h₂.map_eq]⟩

/-- **Rounded fine increments give a coarse increment with a different law, so (2.4) fails in law**
(Giles 2015, §10.2, p. 62: "This ensures that the Brownian increments computed for the coarser path
`ℓ−1` by summing the increments of the finer path `ℓ`, are consistent with the increments which
would be generated on level `ℓ−1` when it is the finer of the two levels.  This would not be the
case if the increments on level `ℓ` were generated with `B_ℓ` bits of accuracy, then summed to give
increments for level `ℓ−1`, regardless of whether the truncation to the lower accuracy `B_{ℓ−1}`
took place before or after the summation").  Let `X₁`, `X₂` be independent fine Brownian
increments with law `N(0, v)`, `v ≠ 0`.  The paper's "truncation to the lower accuracy" is modelled
here by fixed-point round-to-nearest (`roundFixed`, Haas–Giles 2025, §4.1, ties broken upwards as
Mathlib's `round` does) with `B_ℓ = B + 1` and `B_{ℓ−1} = B` bits.  The increment generated on level
`ℓ − 1` as the finer level is `round_B(X₁ + X₂)` (`X₁ + X₂ ∼ N(0, 2v)`): it is integrable with mean
`0`.  Summing the `(B + 1)`-bit fine increments and rounding after the summation gives
`round_B(round_{B+1}(X₁) + round_{B+1}(X₂))`, rounding before gives
`round_B(round_{B+1}(X₁)) + round_B(round_{B+1}(X₂))`; both are integrable with strictly positive
mean.  So the two coarse increments have different laws, and (2.4) `E[P^f_{ℓ−1}] = E[P^c_{ℓ−1}]`
fails for the payoff "the coarse Brownian increment" of a one-step coarse path: the inconsistency
is one of laws, not only pathwise (`roundFixed_sum_inconsistent_general`).  The positive means come
from the ties only: a sum of fine values that is an odd multiple of `q = 2^{e−B−1}` lies halfway
between two `B`-bit numbers and is rounded up (numerically, for `v = 1` and `q = 1`, the means after
and before the summation are `≈ 0.49996` and `≈ 0.99084`).  This mean witness is specific to the
tie rule: under an odd tie rule (round half to even, the IEEE default, or half away from zero) all
three means are `0` by symmetry, and the laws differ in other functionals (numerically, for
`v = 1`, `q = 1/4` and half to even, the second moments are `2.020833` directly, `2.041667` after
and `2.072917` before the summation).  Tie-rule-free witnesses:
`nearestRound_coarse_increment_pos_prob` (after the summation, any tie rule, through
`P(increment > 0)`) and, for truncation in the literal sense of rounding down,
`truncGrid_coarse_increment_mean_lt` (before and after).  Independence is
needed for the "after" case: for `X₂ = −X₁` that increment is `0`. -/
theorem roundFixed_coarse_increment_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (e : ℤ) (B : ℕ) {v : ℝ≥0} (hv : v ≠ 0) {X₁ X₂ : Ω → ℝ}
    (h₁ : HasLaw X₁ (gaussianReal 0 v) μ) (h₂ : HasLaw X₂ (gaussianReal 0 v) μ)
    (hind : IndepFun X₁ X₂ μ) :
    Integrable (fun ω => roundFixed e B (X₁ ω + X₂ ω)) μ ∧
      ∫ ω, roundFixed e B (X₁ ω + X₂ ω) ∂μ = 0 ∧
      Integrable (fun ω => roundFixed e B
        (roundFixed e (B + 1) (X₁ ω) + roundFixed e (B + 1) (X₂ ω))) μ ∧
      0 < ∫ ω, roundFixed e B
        (roundFixed e (B + 1) (X₁ ω) + roundFixed e (B + 1) (X₂ ω)) ∂μ ∧
      Integrable (fun ω => roundFixed e B (roundFixed e (B + 1) (X₁ ω)) +
        roundFixed e B (roundFixed e (B + 1) (X₂ ω))) μ ∧
      0 < ∫ ω, (roundFixed e B (roundFixed e (B + 1) (X₁ ω)) +
        roundFixed e B (roundFixed e (B + 1) (X₂ ω))) ∂μ := by
  have hq : (0 : ℝ) < 2 ^ (e - ((B + 1 : ℕ) : ℤ)) := zpow_pos two_pos _
  obtain ⟨hv1, hv2, hv3⟩ := roundFixed_values e B
  set q : ℝ := 2 ^ (e - ((B + 1 : ℕ) : ℤ)) with hqdef
  -- the direct coarse increment: `X₁ + X₂ ∼ N(0, 2v)` is rounded without bias
  have hsum : HasLaw (fun ω => X₁ ω + X₂ ω) (gaussianReal 0 (v + v)) μ := by
    have h := hind.hasLaw_fun_add h₁ h₂
    rwa [gaussianReal_conv_gaussianReal, add_zero] at h
  have hvv : v + v ≠ 0 := by
    intro h
    exact hv (by simpa using h)
  obtain ⟨i1, e1⟩ := integrable_integral_comp_of_hasLaw hsum (measurable_roundFixed e B)
    (integrable_roundFixed_gaussianReal e B (v + v))
  rw [integral_roundFixed_gaussianReal e B hvv] at e1
  -- truncation before the summation
  obtain ⟨j1, f1⟩ := integral_roundFixed_roundFixed_pos e B hv
  have hm1 : Measurable fun x => roundFixed e B (roundFixed e (B + 1) x) :=
    (measurable_roundFixed e B).comp (measurable_roundFixed e (B + 1))
  obtain ⟨k1, g1⟩ := integrable_integral_comp_of_hasLaw h₁ hm1 j1
  obtain ⟨k2, g2⟩ := integrable_integral_comp_of_hasLaw h₂ hm1 j1
  -- truncation after the summation: the pair `(X₁, X₂)` has law `N(0, v) ⊗ N(0, v)`
  have hpair := hasLaw_pair_gaussianReal h₁ h₂ hind
  set ν := (gaussianReal 0 v).prod (gaussianReal 0 v) with hνdef
  set S : ℝ × ℝ → ℝ := fun p => roundFixed e (B + 1) p.1 + roundFixed e (B + 1) p.2 with hSdef
  set F : ℝ × ℝ → ℝ := fun p => roundFixed e B (S p) with hFdef
  have hSm : Measurable S :=
    ((measurable_roundFixed e (B + 1)).comp measurable_fst).add
      ((measurable_roundFixed e (B + 1)).comp measurable_snd)
  have hFm : Measurable F := (measurable_roundFixed e B).comp hSm
  have iS : Integrable S ν :=
    ((integrable_roundFixed_gaussianReal e (B + 1) v).comp_fst _).add
      ((integrable_roundFixed_gaussianReal e (B + 1) v).comp_snd _)
  have eS : ∫ p, S p ∂ν = 0 := by
    rw [integral_add ((integrable_roundFixed_gaussianReal e (B + 1) v).comp_fst _)
      ((integrable_roundFixed_gaussianReal e (B + 1) v).comp_snd _), integral_fun_fst,
      integral_fun_snd, integral_roundFixed_gaussianReal e (B + 1) hv]
    simp
  have iD : Integrable (fun p => F p - S p) ν := by
    refine Integrable.of_bound (hFm.sub hSm).aestronglyMeasurable
      ((2 : ℝ) ^ (e - B - 1)) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact abs_sub_roundFixed_le e B _
  have iF : Integrable F ν := (iS.add iD).congr (ae_of_all _ fun p => by simp)
  set I : Set (ℝ × ℝ) := Set.Ico (q / 2) (3 * q / 2) ×ˢ Set.Ico (-q / 2) (q / 2) with hIdef
  have hI : MeasurableSet I := measurableSet_Ico.prod measurableSet_Ico
  have hpt : ∀ p, I.indicator (fun _ => q) p ≤ F p - S p := fun p => by
    by_cases hp : p ∈ I
    · rw [Set.indicator_of_mem hp]
      obtain ⟨hp1, hp2⟩ := hp
      have hS : S p = q := by
        show roundFixed e (B + 1) p.1 + roundFixed e (B + 1) p.2 = q
        rw [hv1 _ hp1, hv2 _ hp2, add_zero]
      show q ≤ roundFixed e B (S p) - S p
      rw [hS, hv3]
      linarith
    · rw [Set.indicator_of_notMem hp, sub_nonneg]
      have e2 : S p = q * ((round (p.1 / q) + round (p.2 / q) : ℤ) : ℝ) := by
        show roundFixed e (B + 1) p.1 + roundFixed e (B + 1) p.2 = _
        rw [roundFixed_succ_eq, roundFixed_succ_eq, ← hqdef]
        push_cast
        ring
      show S p ≤ roundFixed e B (S p)
      rw [e2]
      exact le_roundFixed_mul_int e B _
  have hνI : ν.real I = (gaussianReal 0 v).real (Set.Ico (q / 2) (3 * q / 2)) *
      (gaussianReal 0 v).real (Set.Ico (-q / 2) (q / 2)) := by
    rw [hIdef, hνdef, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
    rfl
  have hlow : ν.real I * q ≤ ∫ p, (F p - S p) ∂ν := by
    rw [← smul_eq_mul, ← integral_indicator_const q hI]
    exact integral_mono ((integrable_const q).indicator hI) iD hpt
  have hpos : 0 < ν.real I * q := by
    rw [hνI]
    exact mul_pos (mul_pos (gaussianReal_real_Ico_pos hv (by linarith))
      (gaussianReal_real_Ico_pos hv (by linarith))) hq
  rw [integral_sub iF iS, eS, sub_zero] at hlow
  obtain ⟨l1, m1⟩ := integrable_integral_comp_of_hasLaw hpair hFm iF
  refine ⟨i1, e1, l1, ?_, k1.add k2, ?_⟩
  · rw [m1]
    linarith
  · rw [integral_add k1 k2, g1, g2]
    linarith

/-- For a pair with law `N(0, v) ⊗ N(0, v)`, `v ≠ 0`, the event `X₁ ∈ [a, b), X₂ ∈ [c, d)` (with
`a < b`, `c < d`) is null-measurable and has positive probability (used for Giles 2015, §10.2). -/
lemma measure_preimage_box {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {v : ℝ≥0}
    (hv : v ≠ 0) {X₁ X₂ : Ω → ℝ}
    (hpair : HasLaw (fun ω => (X₁ ω, X₂ ω)) ((gaussianReal 0 v).prod (gaussianReal 0 v)) μ)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    NullMeasurableSet ((fun ω => (X₁ ω, X₂ ω)) ⁻¹' (Set.Ico a b ×ˢ Set.Ico c d)) μ ∧
      μ ((fun ω => (X₁ ω, X₂ ω)) ⁻¹' (Set.Ico a b ×ˢ Set.Ico c d)) ≠ 0 := by
  have hm : MeasurableSet (Set.Ico a b ×ˢ Set.Ico c d) := measurableSet_Ico.prod measurableSet_Ico
  refine ⟨hpair.aemeasurable.nullMeasurableSet_preimage hm, ?_⟩
  rw [← Measure.map_apply_of_aemeasurable hpair.aemeasurable hm, hpair.map_eq,
    Measure.prod_prod]
  exact mul_ne_zero (gaussianReal_Ico_ne_zero hv hab) (gaussianReal_Ico_ne_zero hv hcd)

/-- An integer multiple `q k` of `q > 0` strictly between `q (n − 1)` and `q (n + 1)` is `q n`
(used for Giles 2015, §10.2). -/
lemma int_eq_of_mul_lt_of_lt {q : ℝ} (hq : 0 < q) {k n : ℤ} (h1 : q * (n - 1) < q * k)
    (h2 : q * k < q * (n + 1)) : k = n := by
  have h1' : ((n - 1 : ℤ) : ℝ) < k := by
    push_cast
    exact lt_of_mul_lt_mul_left h1 hq.le
  have h2' : (k : ℝ) < ((n + 1 : ℤ) : ℝ) := by
    push_cast
    exact lt_of_mul_lt_mul_left h2 hq.le
  have := Int.cast_lt.1 h1'
  have := Int.cast_lt.1 h2'
  omega

/-- **After the summation, the coarse increment has a different law under every tie rule**
(Giles 2015, §10.2, p. 62: "This ensures that the Brownian increments computed for the coarser path
`ℓ−1` by summing the increments of the finer path `ℓ`, are consistent with the increments which
would be generated on level `ℓ−1` when it is the finer of the two levels.  This would not be the
case if the increments on level `ℓ` were generated with `B_ℓ` bits of accuracy, then summed to give
increments for level `ℓ−1`, regardless of whether the truncation to the lower accuracy `B_{ℓ−1}`
took place before or after the summation").  Let `q > 0`, let `rf` be any round-to-nearest map
onto the fine grid `qℤ` (values in `qℤ`, `|x − rf x| ≤ q/2`) and `rc` any round-to-nearest map onto
the coarse grid `2qℤ` (values in `2qℤ`, `|x − rc x| ≤ q`), with arbitrary tie rules (and no
measurability assumption).  Let `X₁`, `X₂` be independent with law `N(0, v)`, `v ≠ 0`.  Then the
probability that the coarse increment is positive differs between the increment generated directly,
`rc(X₁ + X₂)`, and the sum of the rounded fine increments rounded after the summation,
`rc(rf X₁ + rf X₂)`: it is larger for the latter if the tie `q` is rounded up (`rc q > 0`, e.g.
Mathlib's `round` or half away from zero) and smaller if it is rounded down (`rc q ≤ 0`, e.g. half
to even).  So the two increments have different laws whatever the tie rule.  Proof:
`{X₁ + X₂ > q} ⊆ {rc(X₁ + X₂) > 0} ⊆ {X₁ + X₂ ≥ q}`, and `X₁ + X₂ = q` has probability `0`; if
`rc q > 0` then `{X₁ + X₂ > q} ⊆ {rc(rf X₁ + rf X₂) > 0}`, which also contains the event
`X₁ ∈ [5q/8, 3q/4)`, `X₂ ∈ [−q/4, 0)` of positive probability on which `X₁ + X₂ < q`; if `rc q ≤ 0`
then `{rc(rf X₁ + rf X₂) > 0} ⊆ {X₁ + X₂ ≥ q}`, and this misses the event `X₁ ∈ [5q/4, 11q/8)`,
`X₂ ∈ [q/8, q/4)` inside `{X₁ + X₂ > q}`.  Numerically, for `v = q = 1`:
`P(rc(X₁ + X₂) > 0) ≈ 0.2398` and `P(rc(rf X₁ + rf X₂) > 0) ≈ 0.3645` (ties up) or `≈ 0.1494`
(ties down or half to even).  The "before" case is covered for ties up by
`roundFixed_coarse_increment_mean` and for truncation by `truncGrid_coarse_increment_mean_lt`, not
for arbitrary tie rules. -/
theorem nearestRound_coarse_increment_pos_prob {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {q : ℝ} (hq : 0 < q) {rc rf : ℝ → ℝ}
    (hrc : ∀ x, ∃ n : ℤ, rc x = 2 * q * n) (hrc' : ∀ x, |x - rc x| ≤ q)
    (hrf : ∀ x, ∃ n : ℤ, rf x = q * n) (hrf' : ∀ x, |x - rf x| ≤ q / 2)
    {v : ℝ≥0} (hv : v ≠ 0) {X₁ X₂ : Ω → ℝ}
    (h₁ : HasLaw X₁ (gaussianReal 0 v) μ) (h₂ : HasLaw X₂ (gaussianReal 0 v) μ)
    (hind : IndepFun X₁ X₂ μ) :
    (0 < rc q → μ {ω | 0 < rc (X₁ ω + X₂ ω)} < μ {ω | 0 < rc (rf (X₁ ω) + rf (X₂ ω))}) ∧
      (rc q ≤ 0 → μ {ω | 0 < rc (rf (X₁ ω) + rf (X₂ ω))} < μ {ω | 0 < rc (X₁ ω + X₂ ω)}) := by
  have : IsProbabilityMeasure μ := h₁.isProbabilityMeasure_iff.2 inferInstance
  -- pathwise facts about the coarse rounding
  have pos_of : ∀ y, q < y → 0 < rc y := fun y hy => by
    have := (abs_le.1 (hrc' y)).2
    linarith
  have ge_of : ∀ y, 0 < rc y → q ≤ y := fun y hy => by
    obtain ⟨n, hn⟩ := hrc y
    have h0 := (abs_le.1 (hrc' y)).1
    rw [hn] at hy h0
    have hn0 : (0 : ℝ) < n := by
      by_contra h
      nlinarith [not_lt.1 h]
    have hn1 : (1 : ℝ) ≤ n := by
      have := Int.cast_pos.1 hn0
      exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    nlinarith
  have rf_eq : ∀ x (n : ℤ), q * n - q / 2 < x → x < q * n + q / 2 → rf x = q * n :=
    fun x n h1 h2 => by
    obtain ⟨k, hk⟩ := hrf x
    have hb := abs_le.1 (hrf' x)
    rw [hk] at hb ⊢
    rw [int_eq_of_mul_lt_of_lt hq (k := k) (n := n) (by nlinarith) (by nlinarith)]
  have hS : ∀ x₁ x₂, ∃ k : ℤ, rf x₁ + rf x₂ = q * k := fun x₁ x₂ => by
    obtain ⟨k₁, hk₁⟩ := hrf x₁
    obtain ⟨k₂, hk₂⟩ := hrf x₂
    exact ⟨k₁ + k₂, by rw [hk₁, hk₂]; push_cast; ring⟩
  have hSY : ∀ x₁ x₂, |(x₁ + x₂) - (rf x₁ + rf x₂)| ≤ q := fun x₁ x₂ => by
    have a1 := abs_le.1 (hrf' x₁)
    have a2 := abs_le.1 (hrf' x₂)
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  -- the laws
  have hsum : HasLaw (fun ω => X₁ ω + X₂ ω) (gaussianReal 0 (v + v)) μ := by
    have h := hind.hasLaw_fun_add h₁ h₂
    rwa [gaussianReal_conv_gaussianReal, add_zero] at h
  have hvv : v + v ≠ 0 := by
    intro h
    exact hv (by simpa using h)
  have hYe : μ {ω | X₁ ω + X₂ ω = q} = 0 := by
    change μ ((fun ω => X₁ ω + X₂ ω) ⁻¹' {q}) = 0
    rw [← Measure.map_apply_of_aemeasurable hsum.aemeasurable (measurableSet_singleton q),
      hsum.map_eq]
    exact gaussianReal_absolutelyContinuous 0 hvv Real.volume_singleton
  have hpair := hasLaw_pair_gaussianReal h₁ h₂ hind
  set Dp := {ω | 0 < rc (X₁ ω + X₂ ω)} with hDp
  set Ap := {ω | 0 < rc (rf (X₁ ω) + rf (X₂ ω))} with hAp
  set Yp := {ω | q < X₁ ω + X₂ ω} with hYp
  set Ye := {ω | X₁ ω + X₂ ω = q} with hYedef
  constructor
  · intro ht
    obtain ⟨hE1m, hE1⟩ := measure_preimage_box hv hpair (a := 5 * q / 8) (b := 3 * q / 4)
      (c := -(q / 4)) (d := 0) (by linarith) (by linarith)
    set E1 := (fun ω => (X₁ ω, X₂ ω)) ⁻¹' (Set.Ico (5 * q / 8) (3 * q / 4) ×ˢ
      Set.Ico (-(q / 4)) 0) with hE1def
    have i1 : Dp ⊆ Yp ∪ Ye := fun ω hω => by
      rcases (ge_of _ hω).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    have i2 : Yp ∪ E1 ⊆ Ap := by
      rintro ω (hω | ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩)
      · have hω' : q < X₁ ω + X₂ ω := hω
        show 0 < rc (rf (X₁ ω) + rf (X₂ ω))
        by_cases hS' : q < rf (X₁ ω) + rf (X₂ ω)
        · exact pos_of _ hS'
        · replace hS' := not_lt.1 hS'
          obtain ⟨k, hk⟩ := hS (X₁ ω) (X₂ ω)
          have hb := abs_le.1 (hSY (X₁ ω) (X₂ ω))
          have hk1 : k = 1 := int_eq_of_mul_lt_of_lt hq (by push_cast; linarith)
            (by push_cast; linarith)
          rw [hk, hk1, Int.cast_one, mul_one]
          exact ht
      · show 0 < rc (rf (X₁ ω) + rf (X₂ ω))
        rw [rf_eq (X₁ ω) 1 (by push_cast; linarith) (by push_cast; linarith),
          rf_eq (X₂ ω) 0 (by push_cast; linarith) (by push_cast; linarith)]
        simpa using ht
    have i3 : Disjoint Yp E1 := by
      rw [Set.disjoint_left]
      rintro ω hω ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
      have hω' : q < X₁ ω + X₂ ω := hω
      linarith
    calc μ Dp ≤ μ (Yp ∪ Ye) := measure_mono i1
      _ ≤ μ Yp + μ Ye := measure_union_le _ _
      _ = μ Yp := by rw [hYe, add_zero]
      _ < μ Yp + μ E1 := ENNReal.lt_add_right (measure_ne_top _ _) hE1
      _ = μ (Yp ∪ E1) := (measure_union₀ hE1m i3.aedisjoint).symm
      _ ≤ μ Ap := measure_mono i2
  · intro ht
    obtain ⟨hE2m, hE2⟩ := measure_preimage_box hv hpair (a := 5 * q / 4) (b := 11 * q / 8)
      (c := q / 8) (d := q / 4) (by linarith) (by linarith)
    set E2 := (fun ω => (X₁ ω, X₂ ω)) ⁻¹' (Set.Ico (5 * q / 4) (11 * q / 8) ×ˢ
      Set.Ico (q / 8) (q / 4)) with hE2def
    have i1 : Ap ⊆ (Ap ∩ Yp) ∪ Ye := fun ω hω => by
      have hω' : 0 < rc (rf (X₁ ω) + rf (X₂ ω)) := hω
      have hq1 := ge_of _ hω'
      obtain ⟨k, hk⟩ := hS (X₁ ω) (X₂ ω)
      have hb := abs_le.1 (hSY (X₁ ω) (X₂ ω))
      have hne : rf (X₁ ω) + rf (X₂ ω) ≠ q := fun h => by
        rw [h] at hω'
        linarith
      have hgt : q < q * k := by
        rw [← hk]
        exact lt_of_le_of_ne hq1 (Ne.symm hne)
      have hk2 : (2 : ℝ) ≤ k := by
        have h1 : (1 : ℝ) < k := by nlinarith
        have := Int.cast_lt.1 (show ((1 : ℤ) : ℝ) < k by exact_mod_cast h1)
        exact_mod_cast (show (2 : ℤ) ≤ k by omega)
      have hY : q ≤ X₁ ω + X₂ ω := by nlinarith
      rcases hY.lt_or_eq with h | h
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr h.symm
    have i2 : (Ap ∩ Yp) ∪ E2 ⊆ Dp := by
      rintro ω (⟨-, hω⟩ | ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩)
      · exact pos_of _ hω
      · exact pos_of _ (by linarith)
    have i3 : Disjoint (Ap ∩ Yp) E2 := by
      rw [Set.disjoint_left]
      rintro ω ⟨hω, -⟩ ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
      have hω' : 0 < rc (rf (X₁ ω) + rf (X₂ ω)) := hω
      rw [rf_eq (X₁ ω) 1 (by push_cast; linarith) (by push_cast; linarith),
        rf_eq (X₂ ω) 0 (by push_cast; linarith) (by push_cast; linarith)] at hω'
      simp only [Int.cast_one, mul_one, Int.cast_zero, mul_zero, add_zero] at hω'
      linarith
    calc μ Ap ≤ μ ((Ap ∩ Yp) ∪ Ye) := measure_mono i1
      _ ≤ μ (Ap ∩ Yp) + μ Ye := measure_union_le _ _
      _ = μ (Ap ∩ Yp) := by rw [hYe, add_zero]
      _ < μ (Ap ∩ Yp) + μ E2 := ENNReal.lt_add_right (measure_ne_top _ _) hE2
      _ = μ ((Ap ∩ Yp) ∪ E2) := (measure_union₀ hE2m i3.aedisjoint).symm
      _ ≤ μ Dp := measure_mono i2

/-- **Fixed-point rounding: the rounded sum of rounded fine increments is more often positive**
(Giles 2015, §10.2, p. 62, with `roundFixed` of Haas–Giles 2025, §4.1, which breaks ties upwards):
for independent `X₁, X₂ ∼ N(0, v)`, `v ≠ 0`, and `B_ℓ = B + 1`, `B_{ℓ−1} = B` bits,
`P(round_B(X₁ + X₂) > 0) < P(round_B(round_{B+1}(X₁) + round_{B+1}(X₂)) > 0)`; the instance
`rc = round_B`, `rf = round_{B+1}`, `q = 2^{e−B−1}` of `nearestRound_coarse_increment_pos_prob`
(`round_B(q) = 2q > 0`, `roundFixed_values`). -/
theorem roundFixed_coarse_increment_pos_prob {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (e : ℤ) (B : ℕ) {v : ℝ≥0} (hv : v ≠ 0) {X₁ X₂ : Ω → ℝ}
    (h₁ : HasLaw X₁ (gaussianReal 0 v) μ) (h₂ : HasLaw X₂ (gaussianReal 0 v) μ)
    (hind : IndepFun X₁ X₂ μ) :
    μ {ω | 0 < roundFixed e B (X₁ ω + X₂ ω)} <
      μ {ω | 0 < roundFixed e B (roundFixed e (B + 1) (X₁ ω) + roundFixed e (B + 1) (X₂ ω))} := by
  have hq : (0 : ℝ) < 2 ^ (e - ((B + 1 : ℕ) : ℤ)) := zpow_pos two_pos _
  have hc : (2 : ℝ) ^ (e - (B : ℤ)) = 2 * 2 ^ (e - ((B + 1 : ℕ) : ℤ)) := by
    rw [← zpow_one_add₀ two_ne_zero]
    congr 1
    push_cast
    ring
  obtain ⟨-, -, hv3⟩ := roundFixed_values e B
  refine (nearestRound_coarse_increment_pos_prob hq
    (fun x => ⟨round (x / (2 : ℝ) ^ (e - (B : ℤ))), by unfold roundFixed; rw [hc]⟩)
    (fun x => ?_) (fun x => ⟨_, roundFixed_succ_eq e B x⟩) (fun x => ?_) hv h₁ h₂ hind).1 ?_
  · have h := abs_sub_roundFixed_le e B x
    rwa [show e - (B : ℤ) - 1 = e - ((B + 1 : ℕ) : ℤ) by push_cast; ring] at h
  · have h := abs_sub_roundFixed_le e (B + 1) x
    rwa [zpow_sub₀ two_ne_zero, zpow_one] at h
  · rw [hv3]
    positivity

/-- Truncation onto the fixed-point grid `cℤ` (Giles 2015, §10.2, p. 62: "the truncation to the
lower accuracy `B_{ℓ−1}`"): `trunc_c x = c ⌊x/c⌋`, the largest multiple of `c` not above `x`; for
`c = 2^{e−B}` this drops the low-order bits of a two's-complement fixed-point number. -/
noncomputable def truncGrid (c x : ℝ) : ℝ := c * ⌊x / c⌋

/-- Truncation onto `cℤ`, `c > 0` (Giles 2015, §10.2), moves down by less than `c`:
`trunc_c x ≤ x < trunc_c x + c`. -/
lemma truncGrid_le_self {c : ℝ} (hc : 0 < c) (x : ℝ) :
    truncGrid c x ≤ x ∧ x < truncGrid c x + c := by
  unfold truncGrid
  constructor
  · calc c * ⌊x / c⌋ ≤ c * (x / c) := mul_le_mul_of_nonneg_left (Int.floor_le _) hc.le
      _ = x := mul_div_cancel₀ x hc.ne'
  · calc x = c * (x / c) := (mul_div_cancel₀ x hc.ne').symm
      _ < c * (⌊x / c⌋ + 1) := mul_lt_mul_of_pos_left (Int.lt_floor_add_one _) hc
      _ = c * ⌊x / c⌋ + c := by ring

/-- Truncation onto `cℤ`, `c > 0` (Giles 2015, §10.2), is monotone. -/
lemma truncGrid_mono {c : ℝ} (hc : 0 < c) : Monotone (truncGrid c) := fun x y hxy => by
  unfold truncGrid
  exact mul_le_mul_of_nonneg_left (Int.cast_le.2 (Int.floor_mono
    (div_le_div_of_nonneg_right hxy hc.le))) hc.le

/-- Truncation onto `cℤ`, `c > 0`, is superadditive (Giles 2015, §10.2):
`trunc_c a + trunc_c b ≤ trunc_c (a + b)`, from `⌊s⌋ + ⌊t⌋ ≤ ⌊s + t⌋`. -/
lemma truncGrid_add_le {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    truncGrid c a + truncGrid c b ≤ truncGrid c (a + b) := by
  unfold truncGrid
  rw [← mul_add, add_div]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Int.le_floor_add _ _) hc.le

/-- If `c n ≤ x < c n + c` with `c > 0`, then `trunc_c x = c n` (Giles 2015, §10.2). -/
lemma truncGrid_eq {c : ℝ} (hc : 0 < c) {x : ℝ} (n : ℤ) (h1 : c * n ≤ x) (h2 : x < c * n + c) :
    truncGrid c x = c * n := by
  unfold truncGrid
  rw [Int.floor_eq_iff.2 ⟨by rwa [le_div_iff₀ hc, mul_comm], by
    rw [div_lt_iff₀ hc]; linarith⟩]

/-- Truncation onto `cℤ` (Giles 2015, §10.2) is measurable. -/
lemma measurable_truncGrid (c : ℝ) : Measurable (truncGrid c) :=
  (measurable_of_countable _ |>.comp (Int.measurable_floor.comp (measurable_id.div_const c))
    |>.const_mul c)

/-- If `F − G ≥ c 1_I` with `c > 0` and `ρ(I) > 0`, for integrable `F`, `G` under a finite measure,
then `∫ G < ∫ F` (used for Giles 2015, §10.2). -/
lemma integral_lt_of_indicator_le {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    [IsFiniteMeasure ρ]
    {F G : α → ℝ} (hF : Integrable F ρ) (hG : Integrable G ρ) {I : Set α} (hI : MeasurableSet I)
    {c : ℝ} (hc : 0 < c) (hIpos : 0 < ρ.real I)
    (hpt : ∀ p, I.indicator (fun _ => c) p ≤ F p - G p) :
    ∫ p, G p ∂ρ < ∫ p, F p ∂ρ := by
  have hlow : ρ.real I * c ≤ ∫ p, (F p - G p) ∂ρ := by
    rw [← smul_eq_mul, ← integral_indicator_const c hI]
    exact integral_mono ((integrable_const c).indicator hI) (hF.sub hG) hpt
  rw [integral_sub hF hG] at hlow
  nlinarith [mul_pos hIpos hc]

/-- **With truncation, the coarse increments are ordered and their means differ, before and after
the summation** (Giles 2015, §10.2, p. 62: "This ensures that the Brownian increments computed for
the coarser path `ℓ−1` by summing the increments of the finer path `ℓ`, are consistent with the
increments which would be generated on level `ℓ−1` when it is the finer of the two levels.  This
would not be the case if the increments on level `ℓ` were generated with `B_ℓ` bits of accuracy,
then summed to give increments for level `ℓ−1`, regardless of whether the truncation to the lower
accuracy `B_{ℓ−1}` took place before or after the summation").  Here "truncation to the lower
accuracy" is read literally as rounding down (`truncGrid`): fine increments are truncated to the
grid `qℤ` (`B_ℓ` bits) and coarse ones to `2qℤ` (`B_{ℓ−1}` bits); for `q = 2^{e−B−1}` this drops the
low-order bits of two's-complement numbers.  Let `X₁`, `X₂` be independent with law `N(0, v)`,
`v ≠ 0`, and `q > 0`.  The increment generated on level `ℓ − 1` as the finer level is
`D = trunc_{2q}(X₁ + X₂)`; truncating after the summation gives
`A = trunc_{2q}(trunc_q X₁ + trunc_q X₂)` and before it
`B = trunc_{2q}(trunc_q X₁) + trunc_{2q}(trunc_q X₂)`.  Then `B ≤ A ≤ D` pathwise, all three are
integrable, and `E[B] < E[A] < E[D]`: both summed increments have laws different from that of `D`,
and (2.4) fails in law.  No tie rule is involved.  (Numerically, and by the symmetry
`⌊−x⌋ = −1 − ⌊x⌋`, `E[D] = −q`, `E[A] = −3q/2` and `E[B] = −2q`; the exact values are not
formalised.)  Truncation towards zero (sign–magnitude) is not covered: then all three means are `0`
by symmetry, while numerically the second moments differ (`0.6858`, `0.4752`, `0.3655` for
`v = q = 1`). -/
theorem truncGrid_coarse_increment_mean_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {q : ℝ} (hq : 0 < q) {v : ℝ≥0} (hv : v ≠ 0) {X₁ X₂ : Ω → ℝ}
    (h₁ : HasLaw X₁ (gaussianReal 0 v) μ) (h₂ : HasLaw X₂ (gaussianReal 0 v) μ)
    (hind : IndepFun X₁ X₂ μ) :
    (∀ ω, truncGrid (2 * q) (truncGrid q (X₁ ω)) + truncGrid (2 * q) (truncGrid q (X₂ ω)) ≤
        truncGrid (2 * q) (truncGrid q (X₁ ω) + truncGrid q (X₂ ω)) ∧
      truncGrid (2 * q) (truncGrid q (X₁ ω) + truncGrid q (X₂ ω)) ≤
        truncGrid (2 * q) (X₁ ω + X₂ ω)) ∧
    Integrable (fun ω => truncGrid (2 * q) (X₁ ω + X₂ ω)) μ ∧
    Integrable (fun ω => truncGrid (2 * q) (truncGrid q (X₁ ω) + truncGrid q (X₂ ω))) μ ∧
    Integrable (fun ω => truncGrid (2 * q) (truncGrid q (X₁ ω)) +
      truncGrid (2 * q) (truncGrid q (X₂ ω))) μ ∧
    ∫ ω, (truncGrid (2 * q) (truncGrid q (X₁ ω)) + truncGrid (2 * q) (truncGrid q (X₂ ω))) ∂μ <
      ∫ ω, truncGrid (2 * q) (truncGrid q (X₁ ω) + truncGrid q (X₂ ω)) ∂μ ∧
    ∫ ω, truncGrid (2 * q) (truncGrid q (X₁ ω) + truncGrid q (X₂ ω)) ∂μ <
      ∫ ω, truncGrid (2 * q) (X₁ ω + X₂ ω) ∂μ := by
  have hq2 : 0 < 2 * q := by linarith
  have hpair := hasLaw_pair_gaussianReal h₁ h₂ hind
  set ν := (gaussianReal 0 v).prod (gaussianReal 0 v) with hνdef
  set FD : ℝ × ℝ → ℝ := fun p => truncGrid (2 * q) (p.1 + p.2) with hFD
  set FA : ℝ × ℝ → ℝ := fun p => truncGrid (2 * q) (truncGrid q p.1 + truncGrid q p.2) with hFA
  set FB : ℝ × ℝ → ℝ := fun p => truncGrid (2 * q) (truncGrid q p.1) +
    truncGrid (2 * q) (truncGrid q p.2) with hFB
  -- pathwise: `B ≤ A ≤ D`, and all three are within `6q` below `X₁ + X₂`
  have hBA : ∀ p, FB p ≤ FA p := fun p => truncGrid_add_le hq2 _ _
  have hAD : ∀ p, FA p ≤ FD p := fun p => truncGrid_mono hq2
    (add_le_add (truncGrid_le_self hq p.1).1 (truncGrid_le_self hq p.2).1)
  have hD1 : ∀ p : ℝ × ℝ, p.1 + p.2 - 2 * q < FD p ∧ FD p ≤ p.1 + p.2 := fun p => by
    have := truncGrid_le_self hq2 (p.1 + p.2)
    exact ⟨by linarith [this.2], this.1⟩
  have hA1 : ∀ p : ℝ × ℝ, p.1 + p.2 - 4 * q < FA p := fun p => by
    have h1 := (truncGrid_le_self hq p.1).2
    have h2 := (truncGrid_le_self hq p.2).2
    have h3 := (truncGrid_le_self hq2 (truncGrid q p.1 + truncGrid q p.2)).2
    show _ < truncGrid (2 * q) (truncGrid q p.1 + truncGrid q p.2)
    linarith
  have hB1 : ∀ p : ℝ × ℝ, p.1 + p.2 - 6 * q < FB p := fun p => by
    have h1 := (truncGrid_le_self hq p.1).2
    have h2 := (truncGrid_le_self hq p.2).2
    have h3 := (truncGrid_le_self hq2 (truncGrid q p.1)).2
    have h4 := (truncGrid_le_self hq2 (truncGrid q p.2)).2
    show _ < truncGrid (2 * q) (truncGrid q p.1) + truncGrid (2 * q) (truncGrid q p.2)
    linarith
  -- integrability under `N(0, v) ⊗ N(0, v)`
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)
  have iY : Integrable (fun p : ℝ × ℝ => p.1 + p.2) ν := (hid.comp_fst _).add (hid.comp_snd _)
  have hmt := measurable_truncGrid
  have mD : Measurable FD := (hmt (2 * q)).comp (measurable_fst.add measurable_snd)
  have mA : Measurable FA :=
    (hmt (2 * q)).comp (((hmt q).comp measurable_fst).add ((hmt q).comp measurable_snd))
  have mB : Measurable FB := ((hmt (2 * q)).comp ((hmt q).comp measurable_fst)).add
    ((hmt (2 * q)).comp ((hmt q).comp measurable_snd))
  have bnd : ∀ (F : ℝ × ℝ → ℝ) (c : ℝ), Measurable F →
      (∀ p, p.1 + p.2 - c < F p ∧ F p ≤ p.1 + p.2) → Integrable F ν := fun F c hF hb => by
    have h : Integrable (fun p => F p - (p.1 + p.2)) ν :=
      Integrable.of_bound (hF.sub (measurable_fst.add measurable_snd)).aestronglyMeasurable c
        (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [(hb p).1, (hb p).2])
    exact (h.add iY).congr (ae_of_all _ fun p => by simp)
  have iD : Integrable FD ν := bnd FD (2 * q) mD hD1
  have iA : Integrable FA ν := bnd FA (4 * q) mA fun p => ⟨hA1 p, (hAD p).trans (hD1 p).2⟩
  have iB : Integrable FB ν :=
    bnd FB (6 * q) mB fun p => ⟨hB1 p, ((hBA p).trans (hAD p)).trans (hD1 p).2⟩
  -- boxes of positive probability on which the inequalities are strict
  have box : ∀ {a b c d : ℝ}, a < b → c < d → 0 < ν.real (Set.Ico a b ×ˢ Set.Ico c d) :=
    fun hab hcd => by
    rw [hνdef, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
    exact mul_pos (gaussianReal_real_Ico_pos hv hab) (gaussianReal_real_Ico_pos hv hcd)
  have hI : MeasurableSet (Set.Ico (3 * q / 2) (2 * q) ×ˢ Set.Ico (q / 2) q) :=
    measurableSet_Ico.prod measurableSet_Ico
  have hJ : MeasurableSet (Set.Ico q (2 * q) ×ˢ Set.Ico q (2 * q)) :=
    measurableSet_Ico.prod measurableSet_Ico
  have hptAD : ∀ p, (Set.Ico (3 * q / 2) (2 * q) ×ˢ Set.Ico (q / 2) q).indicator
      (fun _ => 2 * q) p ≤ FD p - FA p := fun p => by
    by_cases hp : p ∈ Set.Ico (3 * q / 2) (2 * q) ×ˢ Set.Ico (q / 2) q
    · rw [Set.indicator_of_mem hp]
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hp
      have t1 : truncGrid q p.1 = q * (1 : ℤ) := truncGrid_eq hq 1 (by push_cast; linarith)
        (by push_cast; linarith)
      have t2 : truncGrid q p.2 = q * (0 : ℤ) := truncGrid_eq hq 0 (by push_cast; linarith)
        (by push_cast; linarith)
      have tA : truncGrid (2 * q) (q * (1 : ℤ) + q * (0 : ℤ)) = 2 * q * (0 : ℤ) :=
        truncGrid_eq hq2 0 (by push_cast; linarith) (by push_cast; linarith)
      have tD : truncGrid (2 * q) (p.1 + p.2) = 2 * q * (1 : ℤ) :=
        truncGrid_eq hq2 1 (by push_cast; linarith) (by push_cast; linarith)
      show 2 * q ≤ truncGrid (2 * q) (p.1 + p.2) -
        truncGrid (2 * q) (truncGrid q p.1 + truncGrid q p.2)
      rw [t1, t2, tA, tD]
      push_cast
      linarith
    · rw [Set.indicator_of_notMem hp]
      linarith [hAD p]
  have hptBA : ∀ p, (Set.Ico q (2 * q) ×ˢ Set.Ico q (2 * q)).indicator
      (fun _ => 2 * q) p ≤ FA p - FB p := fun p => by
    by_cases hp : p ∈ Set.Ico q (2 * q) ×ˢ Set.Ico q (2 * q)
    · rw [Set.indicator_of_mem hp]
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hp
      have t1 : truncGrid q p.1 = q * (1 : ℤ) := truncGrid_eq hq 1 (by push_cast; linarith)
        (by push_cast; linarith)
      have t2 : truncGrid q p.2 = q * (1 : ℤ) := truncGrid_eq hq 1 (by push_cast; linarith)
        (by push_cast; linarith)
      have tA : truncGrid (2 * q) (q * (1 : ℤ) + q * (1 : ℤ)) = 2 * q * (1 : ℤ) :=
        truncGrid_eq hq2 1 (by push_cast; linarith) (by push_cast; linarith)
      have tB : truncGrid (2 * q) (q * (1 : ℤ)) = 2 * q * (0 : ℤ) :=
        truncGrid_eq hq2 0 (by push_cast; linarith) (by push_cast; linarith)
      show 2 * q ≤ truncGrid (2 * q) (truncGrid q p.1 + truncGrid q p.2) -
        (truncGrid (2 * q) (truncGrid q p.1) + truncGrid (2 * q) (truncGrid q p.2))
      rw [t1, t2, tA, tB]
      push_cast
      linarith
    · rw [Set.indicator_of_notMem hp]
      linarith [hBA p]
  have lt1 := integral_lt_of_indicator_le iA iB hJ hq2 (box (by linarith) (by linarith)) hptBA
  have lt2 := integral_lt_of_indicator_le iD iA hI hq2 (box (by linarith) (by linarith)) hptAD
  -- back to `Ω`
  obtain ⟨jD, eD⟩ := integrable_integral_comp_of_hasLaw hpair mD iD
  obtain ⟨jA, eA⟩ := integrable_integral_comp_of_hasLaw hpair mA iA
  obtain ⟨jB, eB⟩ := integrable_integral_comp_of_hasLaw hpair mB iB
  refine ⟨fun ω => ⟨hBA (X₁ ω, X₂ ω), hAD (X₁ ω, X₂ ω)⟩, jD, jA, jB, ?_, ?_⟩
  · calc _ = ∫ ω, FB (X₁ ω, X₂ ω) ∂μ := rfl
      _ < ∫ ω, FA (X₁ ω, X₂ ω) ∂μ := by rw [eB, eA]; exact lt1
  · calc _ = ∫ ω, FA (X₁ ω, X₂ ω) ∂μ := rfl
      _ < ∫ ω, FD (X₁ ω, X₂ ω) ∂μ := by rw [eA, eD]; exact lt2

end MLMC
