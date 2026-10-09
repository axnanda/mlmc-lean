import MlmcLean.PoissonCoupling
import MlmcLean.Corrections
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Theorem 1 for tau-leaping MLMC with the Poisson coupling (Giles 2015, §8)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §8
"Continuous-time Markov chains", p. 56: the Poisson coupling of Anderson and Higham "leads to a very
effective multilevel algorithm with a correction variance which is `O(h)`, leading to an
`O(ε⁻²(log ε)²)` complexity".

Level `ℓ` uses the time step `h_ℓ = T 2^{−ℓ}`: its fine path makes `2^ℓ` tau-leaping steps of
size `h_ℓ` from `x₀`, and for `ℓ ≥ 1` its coarse path makes `2^{ℓ−1}` steps of size `h_{ℓ−1}`,
coupled with the fine path by the Poisson coupling (`coupledChain`).  The payoff is `Φ(x_T)` for an
`L`-Lipschitz `Φ`, the propensity `λ` is Lipschitz and bounded, and a level-`ℓ` sample costs its
`2^ℓ` fine time steps (`γ = 1`).

* `tauLevelLaw`: the law of the pair of terminal states on level `ℓ` (on level `0` the fine state,
  twice); `tauInputLaw`: one input of the estimator, the pairs of all levels, independent.
* `lintegral_sq_tauChain_lt_top`, `memLp_tauFine`, `memLp_tauCoarse`: for a bounded propensity the
  chain has finite second moments, so the payoffs are square integrable.
* `integral_tauFine`, `integral_tauCoarse`: (2.4), the coarse payoff of level `ℓ + 1` has the mean
  of the fine payoff of level `ℓ` (`tauLeaping_level`).
* `variance_tauCorrection_le`: the correction of every level has variance at most `c₂ 2^{−ℓ}`
  (`β = 1`, from `tauLeaping_level_variance`, finitely many levels with `h_ℓ > 1` aside).
* `tauLeaping_mlmc_theorem1`: **Theorem 1 for tau-leaping MLMC.**  If the weak error of the
  tau-leaping payoff is `|E[Φ(x^{h_ℓ}_T)] − E[P]| ≤ c₁ 2^{−αℓ}` with `α ≥ ½`, then for every
  `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` such that the multilevel estimator with independent
  samples has mean square error `< ε²` at cost `∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`.  The weak rate
  (`α = 1` for tau-leaping) compares with the exact continuous-time chain, which is not
  constructed here, so it is a hypothesis; `β = 1` and `γ = 1` are proved.  The exact chain and
  the weak rate against it are proved elsewhere for bounded propensities, with Theorem 1 and no
  assumed rate for bounded payoffs (`tauLeaping_mlmc_exact`, `MlmcLean.TauLeapingExact`) and for
  Lipschitz payoffs (`tauLeaping_mlmc_exact_lipschitz`, `MlmcLean.TauLeapingExtensions`);
  Lipschitz propensities of linear growth, with the weak rate as a hypothesis, and the linear birth
  rate `λ(x) = cx` with `Φ(x) = x` and no assumed rate, are in `MlmcLean.TauLeapingLinearGrowth`
  (`tauLeaping_mlmc_theorem1_lipschitz`, `tauLeaping_mlmc_linearBirth_mean`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace MLMC

/-! ### The laws of the chains are probability measures -/

/-- One tau-leaping step is a probability measure (Giles 2015, §8). -/
lemma tauStep_univ (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x : ℕ) : tauStep lam h x Set.univ = 1 := by
  rw [tauStep, Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ,
    measure_univ]

/-- The law of the tau-leaping chain is a probability measure (Giles 2015, §8). -/
lemma tauChain_univ (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ n, tauChain lam h x₀ n Set.univ = 1
  | 0 => by rw [tauChain, measure_univ]
  | n + 1 => by
      rw [tauChain, Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable,
        lintegral_congr (tauStep_univ lam h), lintegral_const, one_mul, tauChain_univ lam h x₀ n]

lemma isProbabilityMeasure_tauChain (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ n : ℕ) :
    IsProbabilityMeasure (tauChain lam h x₀ n) :=
  ⟨tauChain_univ lam h x₀ n⟩

/-- **The pair of terminal states on level `ℓ`** (Giles 2015, §8).  On level `0` the fine path
makes one step of size `T` and there is no coarse path (the pair repeats the fine state); on level
`ℓ + 1` the fine path makes `2^{ℓ+1}` steps of size `T/2^{ℓ+1}` and the coarse path `2^ℓ` steps of
size `T/2^ℓ`, coupled by the Poisson coupling. -/
noncomputable def tauLevelLaw (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ : ℕ) : ℕ → Measure (ℕ × ℕ)
  | 0 => (tauChain lam T x₀ 1).map fun x => (x, x)
  | ℓ + 1 => coupledChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ)

lemma tauLevelLaw_zero (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ : ℕ) :
    tauLevelLaw lam T x₀ 0 = (tauChain lam T x₀ 1).map fun x => (x, x) := rfl

lemma tauLevelLaw_succ (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ ℓ : ℕ) :
    tauLevelLaw lam T x₀ (ℓ + 1) = coupledChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ) := rfl

lemma isProbabilityMeasure_tauLevelLaw (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ ℓ : ℕ) :
    IsProbabilityMeasure (tauLevelLaw lam T x₀ ℓ) := by
  cases ℓ with
  | zero =>
    have := isProbabilityMeasure_tauChain lam T x₀ 1
    rw [tauLevelLaw_zero]
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  | succ ℓ =>
    rw [tauLevelLaw_succ]
    exact ⟨coupledChain_univ _ _ _ _⟩

/-- **One input of the tau-leaping estimator** (Giles 2015, §8): the pairs of terminal states of all
levels, independent across levels (a level-`ℓ` sample uses coordinate `ℓ`). -/
noncomputable def tauInputLaw (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ : ℕ) : Measure (ℕ → ℕ × ℕ) :=
  Measure.infinitePi (tauLevelLaw lam T x₀)

lemma isProbabilityMeasure_tauInputLaw (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ : ℕ) :
    IsProbabilityMeasure (tauInputLaw lam T x₀) := by
  have := isProbabilityMeasure_tauLevelLaw lam T x₀
  unfold tauInputLaw
  infer_instance

/-- The coordinate `ℓ` of an input has the law of level `ℓ`. -/
lemma measurePreserving_tauInput (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ ℓ : ℕ) :
    MeasurePreserving (fun y : ℕ → ℕ × ℕ => y ℓ) (tauInputLaw lam T x₀)
      (tauLevelLaw lam T x₀ ℓ) := by
  have := isProbabilityMeasure_tauLevelLaw lam T x₀
  exact measurePreserving_eval_infinitePi (tauLevelLaw lam T x₀) ℓ

/-! ### The payoffs -/

/-- The fine payoff `Φ(x_T)` of level `ℓ` on an input (Giles 2015, §8). -/
def tauFine (Φ : ℕ → ℝ) (ℓ : ℕ) (y : ℕ → ℕ × ℕ) : ℝ := Φ (y ℓ).1

/-- The coarse payoff `Φ(x^c_T)` of level `ℓ + 1` on an input, which (2.4) pairs with the fine
payoff of level `ℓ` (Giles 2015, §8). -/
def tauCoarse (Φ : ℕ → ℝ) (ℓ : ℕ) (y : ℕ → ℕ × ℕ) : ℝ := Φ (y (ℓ + 1)).2

lemma measurable_tauFine (Φ : ℕ → ℝ) (ℓ : ℕ) : Measurable (tauFine Φ ℓ) :=
  (Measurable.of_discrete (f := fun q : ℕ × ℕ => Φ q.1)).comp (measurable_pi_apply ℓ)

lemma measurable_tauCoarse (Φ : ℕ → ℝ) (ℓ : ℕ) : Measurable (tauCoarse Φ ℓ) :=
  (Measurable.of_discrete (f := fun q : ℕ × ℕ => Φ q.2)).comp (measurable_pi_apply (ℓ + 1))

/-! ### Second moments -/

/-- **The tau-leaping chain has finite second moments** for a bounded propensity (Giles 2015, §8):
`E[x_n²] < ∞`, since each step adds a Poisson variate of mean at most `hΛ`. -/
theorem lintegral_sq_tauChain_lt_top {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (x₀ : ℕ) : ∀ n, ∫⁻ x, ENNReal.ofReal ((x : ℝ) ^ 2) ∂(tauChain lam h x₀ n) < ∞
  | 0 => by
      rw [tauChain, lintegral_dirac]
      exact ENNReal.ofReal_lt_top
  | n + 1 => by
      obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * ((h : ℝ) * Λ + ((h : ℝ) * Λ) ^ 2) := ⟨_, rfl⟩
      have hB0 : 0 ≤ B := by
        rw [hB]
        positivity
      have hstep : ∀ a : ℕ, ∫⁻ x, ENNReal.ofReal ((x : ℝ) ^ 2) ∂(tauStep lam h a) ≤
          ENNReal.ofReal (2 * (a : ℝ) ^ 2 + B) := by
        intro a
        have hr : ((h * lam a : ℝ≥0) : ℝ) ≤ (h : ℝ) * Λ := by
          rw [NNReal.coe_mul]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hΛ a) h.coe_nonneg
        have hr0 : (0 : ℝ) ≤ ((h * lam a : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
        rw [tauStep, lintegral_map Measurable.of_discrete Measurable.of_discrete]
        calc ∫⁻ n, ENNReal.ofReal (((a + n : ℕ) : ℝ) ^ 2) ∂(poissonMeasure (h * lam a))
            ≤ ∫⁻ n, ENNReal.ofReal (2 * (a : ℝ) ^ 2 + 0 * (n : ℝ) + 2 * (n : ℝ) ^ 2)
                ∂(poissonMeasure (h * lam a)) := by
              refine lintegral_mono fun n => ENNReal.ofReal_le_ofReal ?_
              push_cast
              nlinarith [sq_nonneg ((a : ℝ) - n)]
          _ = ENNReal.ofReal (2 * (a : ℝ) ^ 2 + 0 * ((h * lam a : ℝ≥0) : ℝ) +
                2 * (((h * lam a : ℝ≥0) : ℝ) + ((h * lam a : ℝ≥0) : ℝ) ^ 2)) :=
              lintegral_poly_poissonMeasure _ (by positivity) le_rfl zero_le_two
          _ ≤ ENNReal.ofReal (2 * (a : ℝ) ^ 2 + B) := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [hB]
              nlinarith [hr, hr0]
      rw [tauChain, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
      calc ∫⁻ a, ∫⁻ x, ENNReal.ofReal ((x : ℝ) ^ 2) ∂(tauStep lam h a) ∂(tauChain lam h x₀ n)
          ≤ ∫⁻ a, ENNReal.ofReal (2 * (a : ℝ) ^ 2 + B) ∂(tauChain lam h x₀ n) :=
            lintegral_mono hstep
        _ = ENNReal.ofReal 2 * ∫⁻ a, ENNReal.ofReal ((a : ℝ) ^ 2) ∂(tauChain lam h x₀ n) +
              ENNReal.ofReal B * tauChain lam h x₀ n Set.univ :=
            lintegral_ofReal_mul_add _ (fun a => sq_nonneg _) zero_le_two hB0
        _ < ∞ := by
            have := isProbabilityMeasure_tauChain lam h x₀ n
            exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (lintegral_sq_tauChain_lt_top hΛ h x₀ n),
              ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

/-- A Lipschitz payoff of a state with finite second moment is square integrable (used in
Giles 2015, §8). -/
lemma memLp_two_of_lipschitz {μ : Measure ℕ} [IsFiniteMeasure μ] {Φ : ℕ → ℝ} {LΦ : ℝ}
    (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|)
    (h2 : ∫⁻ x, ENNReal.ofReal ((x : ℝ) ^ 2) ∂μ < ∞) : MemLp Φ 2 μ := by
  have hnn : 0 ≤ᵐ[μ] fun x : ℕ => (x : ℝ) ^ 2 := ae_of_all _ fun x => sq_nonneg _
  have hint2 : Integrable (fun x : ℕ => (x : ℝ) ^ 2) μ := by
    refine ⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact h2
  have hg : Integrable (fun x : ℕ => 2 * Φ 0 ^ 2 + 2 * LΦ ^ 2 * (x : ℝ) ^ 2) μ :=
    (integrable_const (2 * Φ 0 ^ 2)).add (hint2.const_mul (2 * LΦ ^ 2))
  refine (memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable).2 ?_
  refine Integrable.mono' hg Measurable.of_discrete.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : |Φ x - Φ 0| ≤ LΦ * x := by
    have h := hΦ x 0
    rwa [Nat.cast_zero, sub_zero, Nat.abs_cast] at h
  have h3 : (Φ x - Φ 0) ^ 2 ≤ (LΦ * x) ^ 2 := by
    rw [← sq_abs (Φ x - Φ 0)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [sq_nonneg (Φ x - 2 * Φ 0), h3]

/-- **The payoffs of a level are square integrable** (Giles 2015, §8): for a bounded propensity
and a Lipschitz payoff, `Φ` of the fine and of the coarse terminal state are in `L²`. -/
lemma memLp_tauLevelLaw {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {LΦ : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) (ℓ : ℕ) :
    MemLp (fun q : ℕ × ℕ => Φ q.1) 2 (tauLevelLaw lam T x₀ ℓ) ∧
      MemLp (fun q : ℕ × ℕ => Φ q.2) 2 (tauLevelLaw lam T x₀ ℓ) := by
  have hP : ∀ (h : ℝ≥0) (n : ℕ), IsProbabilityMeasure (tauChain lam h x₀ n) :=
    fun h n => isProbabilityMeasure_tauChain lam h x₀ n
  cases ℓ with
  | zero =>
    rw [tauLevelLaw_zero]
    have h := memLp_two_of_lipschitz hΦ (lintegral_sq_tauChain_lt_top hΛ T x₀ 1)
    exact ⟨(memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
        Measurable.of_discrete.aemeasurable).2 h,
      (memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
        Measurable.of_discrete.aemeasurable).2 h⟩
  | succ ℓ =>
    rw [tauLevelLaw_succ]
    constructor
    · have h := memLp_two_of_lipschitz hΦ
        (lintegral_sq_tauChain_lt_top hΛ (T / 2 ^ (ℓ + 1)) x₀ (2 * 2 ^ ℓ))
      rw [← coupledChain_fst] at h
      exact (memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
        measurable_fst.aemeasurable).1 h
    · have h := memLp_two_of_lipschitz hΦ
        (lintegral_sq_tauChain_lt_top hΛ (2 * (T / 2 ^ (ℓ + 1))) x₀ (2 ^ ℓ))
      rw [← coupledChain_snd] at h
      exact (memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
        measurable_snd.aemeasurable).1 h

lemma memLp_tauFine {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {LΦ : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) (ℓ : ℕ) :
    MemLp (tauFine Φ ℓ) 2 (tauInputLaw lam T x₀) :=
  (memLp_tauLevelLaw hΛ T x₀ hΦ ℓ).1.comp_measurePreserving
    (measurePreserving_tauInput lam T x₀ ℓ)

lemma memLp_tauCoarse {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {LΦ : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) (ℓ : ℕ) :
    MemLp (tauCoarse Φ ℓ) 2 (tauInputLaw lam T x₀) :=
  (memLp_tauLevelLaw hΛ T x₀ hΦ (ℓ + 1)).2.comp_measurePreserving
    (measurePreserving_tauInput lam T x₀ (ℓ + 1))

/-! ### (2.4) and the level variances -/

/-- **The fine payoff of level `ℓ` has the mean of `2^ℓ` tau-leaping steps of size `T 2^{−ℓ}`**
(Giles 2015, §8). -/
theorem integral_tauFine (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ : ℕ) (Φ : ℕ → ℝ) (ℓ : ℕ) :
    ∫ y, tauFine Φ ℓ y ∂(tauInputLaw lam T x₀) =
      ∫ x, Φ x ∂(tauChain lam (T / 2 ^ ℓ) x₀ (2 ^ ℓ)) := by
  have h := integral_comp_of_measurePreserving (measurePreserving_tauInput lam T x₀ ℓ)
    (Measurable.of_discrete (f := fun q : ℕ × ℕ => Φ q.1)).aestronglyMeasurable
  refine h.trans ?_
  cases ℓ with
  | zero =>
    rw [tauLevelLaw_zero, integral_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable]
    simp only [pow_zero, div_one]
  | succ ℓ =>
    rw [tauLevelLaw_succ]
    exact (tauLeaping_level lam T x₀ ℓ Φ).2

/-- **(2.4) for tau-leaping MLMC** (Giles 2015, §2.1, (2.4), and §8): the coarse payoff of level
`ℓ + 1` has the mean of `2^ℓ` tau-leaping steps of size `T 2^{−ℓ}`, that of the fine payoff of
level `ℓ`. -/
theorem integral_tauCoarse (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ : ℕ) (Φ : ℕ → ℝ) (ℓ : ℕ) :
    ∫ y, tauCoarse Φ ℓ y ∂(tauInputLaw lam T x₀) =
      ∫ x, Φ x ∂(tauChain lam (T / 2 ^ ℓ) x₀ (2 ^ ℓ)) := by
  have h := integral_comp_of_measurePreserving (measurePreserving_tauInput lam T x₀ (ℓ + 1))
    (Measurable.of_discrete (f := fun q : ℕ × ℕ => Φ q.2)).aestronglyMeasurable
  refine h.trans ?_
  rw [tauLevelLaw_succ]
  exact (tauLeaping_level lam T x₀ ℓ Φ).1

/-- The variance of the correction of level `ℓ + 1` is that of `Φ(x_T) − Φ(x^c_T)` under the
coupled law (Giles 2015, §8). -/
lemma variance_tauCorrection_succ (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ : ℕ) (Φ : ℕ → ℝ) (ℓ : ℕ) :
    variance (fineCoarseDiff (tauFine Φ) (tauCoarse Φ) (ℓ + 1)) (tauInputLaw lam T x₀) =
      variance (fun q : ℕ × ℕ => Φ q.1 - Φ q.2)
        (coupledChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ)) := by
  have hmp := measurePreserving_tauInput lam T x₀ (ℓ + 1)
  rw [← tauLevelLaw_succ, ← hmp.map_eq, variance_map Measurable.of_discrete.aemeasurable
    hmp.measurable.aemeasurable]
  rfl

/-- **`β = 1` on every level** (Giles 2015, §8, p. 56: "a correction variance which is `O(h)`"):
for a `K`-Lipschitz propensity bounded by `Λ` and a Lipschitz payoff, there is `c₂ > 0` such that
the correction of every level `ℓ` is square integrable and has variance at most `c₂ 2^{−ℓ}`. -/
theorem variance_tauCorrection_le {lam : ℕ → ℝ≥0} {K Λ : ℝ≥0}
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) (x₀ : ℕ) {Φ : ℕ → ℝ} {LΦ : ℝ}
    (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ ℓ : ℕ,
      MemLp (fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ) 2 (tauInputLaw lam T x₀) ∧
      variance (fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ) (tauInputLaw lam T x₀) ≤
        c₂ * (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) := by
  obtain ⟨c, hc, hbd⟩ := tauLeaping_level_variance hK hΛ T hΦ
  obtain ⟨V, hV⟩ : ∃ V : ℕ → ℝ, V = fun ℓ =>
      variance (fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ) (tauInputLaw lam T x₀) := ⟨_, rfl⟩
  have hV0 : ∀ ℓ, 0 ≤ V ℓ := fun ℓ => by
    rw [hV]
    exact variance_nonneg _ _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (T : ℝ) < 2 ^ N := pow_unbounded_of_one_lt (T : ℝ) one_lt_two
  have hS0 : 0 ≤ ∑ ℓ ∈ range (N + 1), V ℓ * 2 ^ ℓ :=
    Finset.sum_nonneg fun ℓ _ => mul_nonneg (hV0 ℓ) (by positivity)
  refine ⟨1 + 2 * c + ∑ ℓ ∈ range (N + 1), V ℓ * 2 ^ ℓ, by linarith, fun ℓ =>
    ⟨memLp_fineCoarseDiff (memLp_tauFine hΛ T x₀ hΦ) (memLp_tauCoarse hΛ T x₀ hΦ) ℓ, ?_⟩⟩
  have hpow : (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) = ((2 : ℝ) ^ ℓ)⁻¹ := by
    rw [one_mul, Real.rpow_neg zero_le_two, Real.rpow_natCast]
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  have hVℓ : variance (fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ) (tauInputLaw lam T x₀) =
      V ℓ := by
    rw [hV]
  rw [hpow, hVℓ, ← div_eq_mul_inv, le_div_iff₀ h2]
  rcases le_or_gt ℓ N with hℓ | hℓ
  · -- the finitely many levels `ℓ ≤ N`
    have hmem : ℓ ∈ range (N + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hℓ)
    have hle : V ℓ * 2 ^ ℓ ≤ ∑ j ∈ range (N + 1), V j * 2 ^ j :=
      Finset.single_le_sum (f := fun j => V j * 2 ^ j)
        (fun j _ => mul_nonneg (hV0 j) (by positivity)) hmem
    linarith
  · -- the levels `ℓ = k + 1 > N`, where `h_ℓ ≤ 1`
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    have hT : (T : ℝ) ≤ 2 ^ (k + 1) :=
      hN.le.trans (pow_le_pow_right₀ one_le_two (by omega))
    have hk := (hbd k x₀ hT).2
    rw [← variance_tauCorrection_succ lam T x₀ Φ k, hVℓ] at hk
    have hk2 : V (k + 1) * 2 ^ k ≤ c := (le_div_iff₀ (by positivity)).1 hk
    have e : V (k + 1) * 2 ^ (k + 1) = 2 * (V (k + 1) * 2 ^ k) := by ring
    linarith

/-! ### Theorem 1 -/

/-- **Theorem 1 for tau-leaping MLMC with the Poisson coupling** (Giles 2015, §8, p. 56: "a very
effective multilevel algorithm with a correction variance which is `O(h)`, leading to an
`O(ε⁻²(log ε)²)` complexity"; Theorem 1 with (2.4), §2.1).  Let the propensity `λ` be `K`-Lipschitz
and bounded by `Λ`, the payoff `Φ` be `L_Φ`-Lipschitz, and level `ℓ` use the time step `T 2^{−ℓ}`
(`2^ℓ` fine steps, the coarse path coupled by the Poisson coupling).  The samples are independent
inputs of law `tauInputLaw` (the coordinates of the infinite product), and a level-`ℓ` sample costs
`2^ℓ`.  If the weak error is `|E[Φ(x^{h_ℓ}_T)] − P| ≤ c₁ 2^{−αℓ}` with `α ≥ ½` (for tau-leaping
`α = 1`; this compares with the exact chain and is assumed), then there is `c₄ > 0` such that for
every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with a square-integrable error, mean square error
`< ε²`, and cost `∑_{ℓ≤L} N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`. -/
theorem tauLeaping_mlmc_theorem1 {lam : ℕ → ℝ≥0} {K Λ : ℝ≥0}
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) (x₀ : ℕ) {Φ : ℕ → ℝ} {LΦ : ℝ}
    (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ LΦ * |(x : ℝ) - y|) (P : ℝ) {α c₁ : ℝ} (hα : 1 / 2 ≤ α)
    (hc₁ : 0 < c₁)
    (hweak : ∀ ℓ : ℕ, |∫ x, Φ x ∂(tauChain lam (T / 2 ^ ℓ) x₀ (2 ^ ℓ)) - P| ≤
      c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ)))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              P) ^ 2) (Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              P) ^ 2 ∂(Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  have hν := isProbabilityMeasure_tauInputLaw lam T x₀
  obtain ⟨-, hind, hω⟩ := exists_iid_inputs (tauInputLaw lam T x₀)
  obtain ⟨c₂, hc₂, hvar⟩ := variance_tauCorrection_le hK hΛ T x₀ hΦ
  have h_i : ∀ ℓ : ℕ, |∫ y, tauFine Φ ℓ y - P ∂(tauInputLaw lam T x₀)| ≤
      c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))) := fun ℓ => by
    rw [integral_sub ((memLp_tauFine hΛ T x₀ hΦ ℓ).integrable one_le_two) (integrable_const _),
      integral_const, probReal_univ, one_smul, integral_tauFine]
    exact hweak ℓ
  have h_iv : ∀ ℓ : ℕ, (2 : ℝ) ^ ℓ ≤ 1 * (2 : ℝ) ^ ((1 : ℝ) * (ℓ : ℝ)) := fun ℓ => by
    rw [one_mul, one_mul, Real.rpow_natCast]
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_fineCoarse
    (μ := Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀)
    (ν := tauInputLaw lam T x₀) (fun _ => P) (tauFine Φ) (tauCoarse Φ) (fun p x => x p)
    (fun ℓ _ _ => (2 : ℝ) ^ ℓ) (fun ℓ => (2 : ℝ) ^ ℓ) (α := α) (β := 1) (γ := 1) (c₁ := c₁)
    (c₂ := c₂) (c₃ := 1) (by linarith) one_pos one_pos hc₁ hc₂ one_pos
    (by rw [min_self]; linarith) hω hind (integrable_const _) (measurable_tauFine Φ)
    (measurable_tauCoarse Φ) (memLp_tauFine hΛ T x₀ hΦ) (memLp_tauCoarse hΛ T x₀ hΦ)
    (fun ℓ => (integral_tauFine lam T x₀ Φ ℓ).trans (integral_tauCoarse lam T x₀ Φ ℓ).symm)
    (fun _ _ => integrable_const _)
    (fun _ _ => by simp only [integral_const, probReal_univ, one_smul]) h_i (fun ℓ => (hvar ℓ).2)
    h_iv
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, N, hN, ?_, ?_, ?_⟩
  · exact ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω (fun ℓ => (hvar ℓ).1) ℓ (N ℓ)).sub
      (memLp_const _)).integrable_sq
  · rw [integral_const, probReal_univ, one_smul] at hmse
    exact hmse
  · simp only [totalCost, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul] at hcost
    rw [complexityBound_of_eq rfl ε] at hcost
    exact hcost

end MLMC
