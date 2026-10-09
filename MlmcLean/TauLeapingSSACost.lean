import MlmcLean.TauLeapingSSA

/-!
# The random cost of the exact SSA level (Giles 2015, §8)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §8
"Continuous-time Markov chains", p. 56 (`docs/giles2015.txt`, l. 2411–2417): "In their paper,
Anderson and Higham (2012) … also include an additional coupling at the finest level to the exact
Stochastic Simulation Algorithm developed by (Gillespie 1976) which updates the reaction rates
after every single reaction.  Hence, their overall multilevel estimator is unbiased, unlike the
estimators discussed earlier for SDEs, and the complexity is reduced to `O(ε⁻²)` because the number
of levels remains fixed as `ε → 0`."  The complexity is meant in the sense of Theorem 1 (§2.1,
p. 6, l. 273–274: "independent estimators `Yℓ` based on `Nℓ` Monte Carlo samples, each with
expected cost `Cℓ` and variance `Vℓ`"; p. 7, l. 294–295: "with a computational complexity `C`
with bound `E[C] ≤` …"): a bound on the expected value of the random total cost.

**What is new here.**  `ssa_mlmc_complexity` (`MlmcLean/TauLeapingSSA.lean`) charges every sample
of the exact level `L + 1` its expected cost `2^L + ΛT`: its `2^L` tau-leaping steps and the
expected number `E[P(ΛT)] = ΛT` of ticks of the rate-`Λ` uniformisation clock that drives the
exact chain.  The number of ticks is random.  This file adds it to the coupled chain and to the
sampling space, so that the cost of every sample is a random variable on the space that carries
the estimator, and bounds the expected total random cost.  Setting and deviations are those of
`MlmcLean/TauLeapingSSA.lean`: one reaction, the state `x ∈ ℕ` counts the reactions, a bounded
propensity `λ ≤ Λ`, a bounded payoff `|Φ| ≤ M`.

**The coupled chain with its tick count.**  `ssaStepCount` is the coupled step `ssaStep` with a
third coordinate that counts the clock ticks: from `((x, z), k)` the clock ticks `n ~ P(Λh)` times,
the `n` coupled ticks `ssaTickPow` (tau-leaping rate frozen at `λ(z)`) move the pair `(x, z)`, and
the count becomes `k + n`.  `ssaChainCount` iterates it from `((x₀, x₀), 0)`.
* `ssaChainCount_map_fst`: forgetting the count gives `ssaChain`, for every step size and number
  of steps, so the augmented chain is the coupling of `TauLeapingSSA.lean` and everything proved
  there holds for its state component.
* `ssaChainCount_map_exact`: after `n` steps of size `h` the joint law of the exact state and the
  count is `P(nΛh).bind (k ↦ J^k(x₀) ⊗ δ_k)`, with `J^k(x₀)` (`jumpPow`) the law after `k`
  uniformised jumps.  So the count is the number of ticks of the uniformisation clock of the exact
  chain, and given `k` ticks the exact state is `k` uniformised jumps from `x₀`.
* `ssaChainCount_marginals`: for `N ≥ 1` steps of size `T/N`, a probability measure with the
  projections `ssaChain` and `P(ΛT)` (the count is the sum of `N` independent `P(ΛT/N)` counts,
  `poissonMeasure_conv_poissonMeasure`), the joint law above with `nΛh = ΛT`, and a count of mean
  `ΛT` and variance `ΛT`.

**The random cost.**  The sampling space is that of `ssa_mlmc_unbiased` with one more coordinate.
`ssaLevelCountLaw` is the level law `ssaLevelLaw` with the count `0` on the tau-leaping levels
`ℓ ≤ L` and the augmented chain (`2^L` steps of size `T 2^{−L}`) on the exact level `L + 1`;
`ssaCountInputLaw` is their product, and the samples are the coordinates of
`Measure.infinitePi fun _ ↦ ssaCountInputLaw …`.  `ssaSampleCost L ℓ` is the cost of one sample:
`2^ℓ` on the tau-leaping levels (deterministic, as in `ssa_mlmc_complexity`) and `2^L + K` on the
exact level, `K` the tick count of that very sample.  The total cost is `totalCost` of these,
`∑_{ℓ ≤ L+1} ∑_{n < N_ℓ}`.
* `ssa_exact_sample_cost`: the exact-level coordinate has the law of the augmented chain, its
  count is `P(ΛT)`, and the sample cost `2^L + K` is square integrable with mean `2^L + ΛT` (the
  deterministic cost of `ssa_mlmc_complexity`) and variance `ΛT`.
* `ssaTotalCost_moments`: for all `N_ℓ` the total random cost is square integrable, its mean is
  exactly the cost `∑_{ℓ ≤ L} N_ℓ 2^ℓ + N_{L+1}(2^L + ΛT)` of `ssa_mlmc_complexity`, and its
  variance is `N_{L+1} ΛT` (the counts of different samples are independent).
* `ssa_mlmc_complexity_random_cost` (**G8-14 with the random cost**): forgetting the counts maps
  the sampling measure onto that of `ssa_mlmc_complexity`, and for every fixed `L` there is `c > 0`
  such that for every `0 < ε ≤ 1` some `N_ℓ ≥ 1` give: the estimator of `ssa_mlmc_complexity`,
  evaluated at the state components of the samples, has a square-integrable error and mean square
  error `< ε²`; the total random cost `C` is integrable with `E[C] ≤ c ε⁻²`; and
  `P(C ≥ 2cε⁻²) ≤ ε²/c` (Chebyshev, from `V[C] = N_{L+1}ΛT ≤ E[C]`).

**Which form is proved.**  The joint one: the cost and the estimator are functions on one
probability space, and the cost of the `n`-th exact-level sample is a function of the same
coordinate `ω^{(L+1, n)}` as its correction `Φ(X_T) − Φ(Z_{2^L})`.

**Deviations.**  Those of `MlmcLean/TauLeapingSSA.lean` (one reaction, bounded propensity and
payoff, the exact chain by uniformisation instead of Gillespie's exponential waiting times, `ε ≤ 1`,
`c` depending on `L`).  The cost model counts one unit per tau-leaping step and one per clock tick
(one uniform and one propensity evaluation): the cost of the uniformised simulation.  Gillespie's
algorithm would simulate only the reactions of the exact path, at most `K` of them; that comparison
is not formalised.  The tau-leaping levels keep their deterministic cost `2^ℓ`.

**Not proved.**  Several reactions, unbounded propensities or payoffs, the cost of Gillespie's
algorithm itself, exponential (Poisson) tail bounds for the cost beyond Chebyshev, and Anderson
and Higham's sharper variance analysis.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace MLMC

/-! ### The coupled chain with its tick count -/

/-- **One coupled step that also counts the clock ticks** (Giles 2015, §8, p. 56, l. 2412–2415:
the coupling "to the exact Stochastic Simulation Algorithm developed by (Gillespie 1976) which
updates the reaction rates after every single reaction", here by uniformisation).  From
`((x, z), k)` (exact state `x`, tau-leaping state `z`, ticks so far `k`), the rate-`Λ` clock ticks
`n ~ P(Λh)` times in the step of length `h`; the `n` coupled ticks `ssaTickPow` (tau-leaping rate
frozen at `λ(z)`) move the pair `(x, z)`, and the count becomes `k + n`.  Forgetting the count
gives the coupled step `ssaStep`. -/
noncomputable def ssaStepCount (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (s : (ℕ × ℕ) × ℕ) :
    Measure ((ℕ × ℕ) × ℕ) :=
  (poissonMeasure (Λ * h)).bind fun n =>
    (ssaTickPow lam Λ s.1.2 n s.1).map fun t => (t, s.2 + n)

/-- **The coupled chain with its tick count** (Giles 2015, §8, p. 56, l. 2411–2415): the joint law
after `n` steps of size `h` of the exact state, the tau-leaping state and the number of ticks of
the uniformisation clock, started at `((x₀, x₀), 0)`. -/
noncomputable def ssaChainCount (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (x₀ : ℕ) :
    ℕ → Measure ((ℕ × ℕ) × ℕ)
  | 0 => Measure.dirac ((x₀, x₀), 0)
  | n + 1 => (ssaChainCount lam Λ h x₀ n).bind (ssaStepCount lam Λ h)

/-- The counting chain starts at `((x₀, x₀), 0)` (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaChainCount_zero (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (x₀ : ℕ) :
    ssaChainCount lam Λ h x₀ 0 = Measure.dirac ((x₀, x₀), 0) := rfl

/-- One more counting step (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaChainCount_succ (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (x₀ n : ℕ) :
    ssaChainCount lam Λ h x₀ (n + 1) =
      (ssaChainCount lam Λ h x₀ n).bind (ssaStepCount lam Λ h) := rfl

/-- Forgetting the count of one counting step gives the coupled step `ssaStep`
(Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaStepCount_map_fst (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (s : (ℕ × ℕ) × ℕ) :
    (ssaStepCount lam Λ h s).map Prod.fst = ssaStep lam Λ h s.1 := by
  rw [ssaStepCount, map_bind_of_discrete _ _ measurable_fst, ssaStep]
  refine congrArg _ (funext fun n => ?_)
  rw [Measure.map_map measurable_fst Measurable.of_discrete]
  exact Measure.map_id

/-- The ticks of one step: the count grows by a `P(Λh)` variate (Giles 2015, §8, p. 56,
l. 2412–2415; p. 55, l. 2377: "`P(t)` represents a unit-rate Poisson random variable"). -/
lemma ssaStepCount_map_snd {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (s : (ℕ × ℕ) × ℕ) :
    (ssaStepCount lam Λ h s).map Prod.snd = (poissonMeasure (Λ * h)).map (s.2 + ·) := by
  rw [ssaStepCount, map_bind_of_discrete _ _ measurable_snd,
    ← Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  refine congrArg _ (funext fun n => ?_)
  rw [Measure.map_map measurable_snd Measurable.of_discrete]
  change (ssaTickPow lam Λ s.1.2 n s.1).map (fun _ => s.2 + n) = _
  rw [Measure.map_const, ssaTickPow_univ hΛ, one_smul]

/-- **Forgetting the tick count gives the coupled chain** (Giles 2015, §8, p. 56, l. 2411–2415:
the coupling of the finest tau-leaping level "to the exact Stochastic Simulation Algorithm").  For
every step size `h` and number of steps `n`, the projection of `ssaChainCount` onto the pair of
the exact and the tau-leaping state is `ssaChain`: the counting chain is the same coupling. -/
theorem ssaChainCount_map_fst (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (x₀ : ℕ) :
    ∀ n, (ssaChainCount lam Λ h x₀ n).map Prod.fst = ssaChain lam Λ h x₀ n
  | 0 => by rw [ssaChainCount_zero, Measure.map_dirac' measurable_fst, ssaChain_zero]
  | n + 1 => by
      rw [ssaChainCount_succ, map_bind_of_discrete _ _ measurable_fst, ssaChain_succ,
        ← ssaChainCount_map_fst lam Λ h x₀ n, bind_map_of_discrete]
      exact congrArg _ (funext fun s => ssaStepCount_map_fst lam Λ h s)

/-- After `n` steps of size `h` the tick count has the law `P(nΛh)`, the sum of `n` independent
`P(Λh)` counts (Giles 2015, §8, p. 55, l. 2387–2389: "the sum of two independent Poisson variates
`P(t₁)`, `P(t₂)` is equivalent in distribution to `P(t₁ + t₂)`"). -/
lemma ssaChainCount_map_snd {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (x₀ : ℕ) :
    ∀ n, (ssaChainCount lam Λ h x₀ n).map Prod.snd = poissonMeasure (n * (Λ * h))
  | 0 => by
      rw [ssaChainCount_zero, Measure.map_dirac' measurable_snd, Nat.cast_zero, zero_mul,
        poissonMeasure_zero]
  | n + 1 => by
      have ih := ssaChainCount_map_snd hΛ h x₀ n
      rw [ssaChainCount_succ, map_bind_of_discrete _ _ measurable_snd]
      have e : (fun s : (ℕ × ℕ) × ℕ => (ssaStepCount lam Λ h s).map Prod.snd) =
          fun s => (fun k : ℕ => (poissonMeasure (Λ * h)).map fun m => 0 + k + m) s.2 := by
        funext s
        rw [ssaStepCount_map_snd hΛ h s]
        simp only [zero_add]
      rw [e, ← bind_map_of_discrete (ssaChainCount lam Λ h x₀ n) Prod.snd
          (fun k : ℕ => (poissonMeasure (Λ * h)).map fun m => 0 + k + m), ih,
        bind_map_add_eq_conv, poissonMeasure_conv_poissonMeasure, Nat.cast_succ, add_one_mul]
      have e2 : (fun k : ℕ => 0 + k) = id := funext fun k => zero_add k
      rw [e2, Measure.map_id]

/-- The exact state and the count after one counting step: `m ~ P(Λh)` ticks, and given them the
exact state has the law `J^m(x)` of `m` uniformised jumps (Giles 2015, §8, p. 56, l. 2412–2415:
the exact SSA "updates the reaction rates after every single reaction"). -/
lemma ssaStepCount_map_exact {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (s : (ℕ × ℕ) × ℕ) :
    (ssaStepCount lam Λ h s).map (fun u => (u.1.1, u.2)) =
      (poissonMeasure (Λ * h)).bind fun m =>
        (jumpPow lam Λ m s.1.1).map fun x => (x, s.2 + m) := by
  rw [ssaStepCount, map_bind_of_discrete _ _ Measurable.of_discrete]
  refine congrArg _ (funext fun m => ?_)
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete, ← ssaTickPow_map_fst hΛ,
    Measure.map_map Measurable.of_discrete measurable_fst]
  rfl

/-- **The count is the tick count of the uniformised exact chain** (Giles 2015, §8, p. 56,
l. 2412–2415: the exact Stochastic Simulation Algorithm "updates the reaction rates after every
single reaction"; here by uniformisation).  For `λ ≤ Λ`, after `n` counting steps of size `h`
the joint law of the exact state and the tick count is `P(nΛh).bind (k ↦ J^k(x₀) ⊗ δ_k)`: the
count has the law `P(nΛh)`, and given `k` ticks the exact state has the law `J^k(x₀)`
(`jumpPow`) of `k` uniformised jumps from `x₀`, as in `exactLaw λ Λ (nh) x₀`. -/
theorem ssaChainCount_map_exact {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (x₀ : ℕ) : ∀ n, (ssaChainCount lam Λ h x₀ n).map (fun u => (u.1.1, u.2)) =
      (poissonMeasure (n * (Λ * h))).bind fun k => (jumpPow lam Λ k x₀).map fun x => (x, k)
  | 0 => by
      rw [ssaChainCount_zero, Measure.map_dirac' Measurable.of_discrete, Nat.cast_zero, zero_mul,
        poissonMeasure_zero, Measure.dirac_bind Measurable.of_discrete, jumpPow_zero,
        Measure.map_dirac' Measurable.of_discrete]
  | n + 1 => by
      have ih := ssaChainCount_map_exact hΛ h x₀ n
      have hJ : ∀ k x, IsProbabilityMeasure (jumpPow lam Λ k x) :=
        fun k x => ⟨jumpPow_univ hΛ k x⟩
      set F : ℕ × ℕ → Measure (ℕ × ℕ) := fun v =>
        (poissonMeasure (Λ * h)).bind fun m => (jumpPow lam Λ m v.1).map fun y => (y, v.2 + m)
        with hF_def
      have e : (fun s : (ℕ × ℕ) × ℕ => (ssaStepCount lam Λ h s).map (fun u => (u.1.1, u.2))) =
          fun s => F (s.1.1, s.2) := by
        funext s
        rw [ssaStepCount_map_exact hΛ h s]
      rw [ssaChainCount_succ, map_bind_of_discrete _ _ Measurable.of_discrete, e,
        ← bind_map_of_discrete (ssaChainCount lam Λ h x₀ n) (fun u => (u.1.1, u.2)) F, ih,
        Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
      have e2 : ∀ k : ℕ, ((jumpPow lam Λ k x₀).map fun x => (x, k)).bind F =
          (poissonMeasure (Λ * h)).bind fun m =>
            (jumpPow lam Λ (k + m) x₀).map fun y => (y, k + m) := by
        intro k
        rw [bind_map_of_discrete]
        simp only [hF_def]
        rw [bind_bind_comm_nat (jumpPow lam Λ k x₀) (poissonMeasure (Λ * h))
          (fun x m => (jumpPow lam Λ m x).map fun y => (y, k + m))]
        refine congrArg _ (funext fun m => ?_)
        rw [jumpPow_add, map_bind_of_discrete _ _ Measurable.of_discrete]
      rw [funext e2, bind_bind_add_eq_bind_conv _ _
          (fun j => (jumpPow lam Λ j x₀).map fun y => (y, j)),
        poissonMeasure_conv_poissonMeasure, Nat.cast_succ, add_one_mul]

/-- The counting chain is a probability measure when `λ ≤ Λ` (Giles 2015, §8, p. 56,
l. 2412–2415). -/
lemma isProbabilityMeasure_ssaChainCount {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (h : ℝ≥0) (x₀ n : ℕ) : IsProbabilityMeasure (ssaChainCount lam Λ h x₀ n) := by
  have hP := isProbabilityMeasure_ssaChain hΛ h x₀ n
  constructor
  rw [← Set.preimage_univ (f := Prod.fst), ← Measure.map_apply measurable_fst MeasurableSet.univ,
    ssaChainCount_map_fst]
  exact measure_univ

/-! ### Moments of the tick count -/

/-- A Poisson variate is square integrable (Giles 2015, §8, p. 55, l. 2377: "`P(t)` represents a
unit-rate Poisson random variable"). -/
lemma memLp_natCast_poissonMeasure (r : ℝ≥0) :
    MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := by
  rw [memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable]
  have hnn : 0 ≤ᵐ[poissonMeasure r] fun n : ℕ => (n : ℝ) ^ 2 := ae_of_all _ fun n => sq_nonneg _
  exact ⟨Measurable.of_discrete.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2
    ((lintegral_sq_poissonMeasure r).trans_lt ENNReal.ofReal_lt_top)⟩

/-- **The variance of a Poisson variate** `V[P(r)] = r` (Giles 2015, §8, p. 55, l. 2377). -/
lemma variance_natCast_poissonMeasure (r : ℝ≥0) :
    variance (fun n : ℕ => (n : ℝ)) (poissonMeasure r) = r := by
  rw [variance_eq_sub (memLp_natCast_poissonMeasure r)]
  simp only [Pi.pow_apply]
  rw [integral_sq_poissonMeasure, integral_poissonMeasure_id]
  ring

/-- A count with the law `P(r)` is square integrable with mean `r` and variance `r` (for the tick
count of Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaCount_moments {μ : Measure ((ℕ × ℕ) × ℕ)} [IsProbabilityMeasure μ] {r : ℝ≥0}
    (h : μ.map Prod.snd = poissonMeasure r) :
    MemLp (fun u : (ℕ × ℕ) × ℕ => (u.2 : ℝ)) 2 μ ∧ ∫ u, (u.2 : ℝ) ∂μ = r ∧
      variance (fun u : (ℕ × ℕ) × ℕ => (u.2 : ℝ)) μ = r := by
  have hm := memLp_natCast_poissonMeasure r
  rw [← h] at hm
  refine ⟨(memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
    measurable_snd.aemeasurable).1 hm, ?_, ?_⟩
  · rw [← integral_poissonMeasure_id r, ← h, integral_map measurable_snd.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable]
  · rw [← variance_natCast_poissonMeasure r, ← h, variance_map Measurable.of_discrete.aemeasurable
      measurable_snd.aemeasurable]
    rfl

/-- **The tick count of `N` coupled steps of size `T/N` is `P(ΛT)`** (Giles 2015, §8, p. 56,
l. 2411–2417: Anderson and Higham couple the finest level "to the exact Stochastic Simulation
Algorithm", and the complexity is `O(ε⁻²)`; the cost of the exact path is its number of clock
ticks).  For `λ ≤ Λ` and `N ≥ 1` counting steps of size `T/N` from `x₀`: the counting chain is a
probability measure; forgetting the count gives `ssaChain λ Λ (T/N) x₀ N`; the count has the law
`P(ΛT)`, the sum of the `N` independent `P(ΛT/N)` tick counts of the steps; the joint law of the
exact state and the count is `P(ΛT).bind (k ↦ J^k(x₀) ⊗ δ_k)` (given `k` ticks the exact state is
`k` uniformised jumps from `x₀`); and the count is square integrable with mean `ΛT` and variance
`ΛT`. -/
theorem ssaChainCount_marginals {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ : ℕ) {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (ssaChainCount lam Λ (T / N) x₀ N) ∧
      (ssaChainCount lam Λ (T / N) x₀ N).map Prod.fst = ssaChain lam Λ (T / N) x₀ N ∧
      (ssaChainCount lam Λ (T / N) x₀ N).map Prod.snd = poissonMeasure (Λ * T) ∧
      (ssaChainCount lam Λ (T / N) x₀ N).map (fun u => (u.1.1, u.2)) =
        (poissonMeasure (Λ * T)).bind (fun k => (jumpPow lam Λ k x₀).map fun x => (x, k)) ∧
      MemLp (fun u : (ℕ × ℕ) × ℕ => (u.2 : ℝ)) 2 (ssaChainCount lam Λ (T / N) x₀ N) ∧
      ∫ u, (u.2 : ℝ) ∂(ssaChainCount lam Λ (T / N) x₀ N) = Λ * T ∧
      variance (fun u : (ℕ × ℕ) × ℕ => (u.2 : ℝ)) (ssaChainCount lam Λ (T / N) x₀ N) =
        Λ * T := by
  have hN0 : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e : (N : ℝ≥0) * (Λ * (T / N)) = Λ * T := by
    rw [mul_left_comm, mul_div_cancel₀ T hN0]
  have hP := isProbabilityMeasure_ssaChainCount hΛ (T / N) x₀ N
  have hsnd : (ssaChainCount lam Λ (T / N) x₀ N).map Prod.snd = poissonMeasure (Λ * T) := by
    rw [ssaChainCount_map_snd hΛ, e]
  obtain ⟨h2, hmean, hvar⟩ := ssaCount_moments hsnd
  rw [NNReal.coe_mul] at hmean hvar
  refine ⟨hP, ssaChainCount_map_fst lam Λ _ x₀ N, hsnd, ?_, h2, hmean, hvar⟩
  rw [ssaChainCount_map_exact hΛ, e]

/-- The `2^L` exact-level steps of size `T 2^{−L}` make `P(ΛT)` ticks (Giles 2015, §8, p. 56,
l. 2412–2415). -/
lemma ssaChainCount_pow_snd {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L : ℕ) :
    (ssaChainCount lam Λ (T / 2 ^ L) x₀ (2 ^ L)).map Prod.snd = poissonMeasure (Λ * T) := by
  rw [ssaChainCount_map_snd hΛ, Nat.cast_pow, Nat.cast_ofNat, mul_left_comm,
    mul_div_cancel₀ T (pow_ne_zero L two_ne_zero)]

/-! ### The sampling space with the tick counts, and the random cost -/

/-- **The law of a level-`ℓ` sample together with its tick count** (Giles 2015, §8, p. 56,
l. 2411–2417).  On the tau-leaping levels `ℓ ≤ L` the pair of `ssaLevelLaw`, the law
`tauLevelLaw` of the Poisson-coupled tau-leaping paths, with the count `0` (no clock); on the exact
level `L + 1` the coupled exact and tau-leaping paths with the tick count of the uniformisation
clock (`ssaChainCount`, `2^L` steps of size `T 2^{−L}`).  (Indices `ℓ > L + 1` are not used.) -/
noncomputable def ssaLevelCountLaw (lam : ℕ → ℝ≥0) (Λ T : ℝ≥0) (x₀ L ℓ : ℕ) :
    Measure ((ℕ × ℕ) × ℕ) :=
  if ℓ ≤ L then (tauLevelLaw lam T x₀ ℓ).map fun q => (q, 0)
  else ssaChainCount lam Λ (T / 2 ^ L) x₀ (2 ^ L)

/-- **One input of the unbiased estimator with its tick counts** (Giles 2015, §8, p. 56,
l. 2411–2415): the samples of all levels `ℓ ≤ L + 1` with their counts, independent across levels
(a level-`ℓ` sample uses coordinate `ℓ`); its state components form an input of law
`ssaInputLaw`. -/
noncomputable def ssaCountInputLaw (lam : ℕ → ℝ≥0) (Λ T : ℝ≥0) (x₀ L : ℕ) :
    Measure (ℕ → (ℕ × ℕ) × ℕ) :=
  Measure.infinitePi (ssaLevelCountLaw lam Λ T x₀ L)

/-- **The random cost of one sample** (Giles 2015, §8, p. 56, l. 2411–2417, and Theorem 1, §2.1,
p. 6, l. 273–274: "each with expected cost `Cℓ`").  A tau-leaping sample of level `ℓ ≤ L` costs
its `2^ℓ` fine steps; an exact-level sample costs its `2^L` tau-leaping steps plus its number of
clock ticks `K` (one uniform and one propensity evaluation each), the count stored in coordinate
`ℓ`: `2^L + K`. -/
noncomputable def ssaSampleCost (L ℓ : ℕ) (y : ℕ → (ℕ × ℕ) × ℕ) : ℝ :=
  if ℓ ≤ L then 2 ^ ℓ else 2 ^ L + ((y ℓ).2 : ℝ)

/-- The level laws with counts are probability measures (Giles 2015, §8, p. 56, l. 2411–2415). -/
lemma isProbabilityMeasure_ssaLevelCountLaw {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) (x₀ L ℓ : ℕ) : IsProbabilityMeasure (ssaLevelCountLaw lam Λ T x₀ L ℓ) := by
  rw [ssaLevelCountLaw]
  split_ifs
  · have := isProbabilityMeasure_tauLevelLaw lam T x₀ ℓ
    exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
  · exact isProbabilityMeasure_ssaChainCount hΛ _ x₀ _

/-- Forgetting the count of a level sample gives the level law `ssaLevelLaw` (Giles 2015, §8,
p. 56, l. 2411–2415). -/
lemma ssaLevelCountLaw_map_fst (lam : ℕ → ℝ≥0) (Λ T : ℝ≥0) (x₀ L ℓ : ℕ) :
    (ssaLevelCountLaw lam Λ T x₀ L ℓ).map Prod.fst = ssaLevelLaw lam Λ T x₀ L ℓ := by
  rw [ssaLevelCountLaw, ssaLevelLaw]
  split_ifs
  · rw [Measure.map_map measurable_fst Measurable.of_discrete]
    exact Measure.map_id
  · exact ssaChainCount_map_fst lam Λ _ x₀ _

/-- The input law with counts is a probability measure (Giles 2015, §8, p. 56, l. 2411–2415). -/
lemma isProbabilityMeasure_ssaCountInputLaw {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) (x₀ L : ℕ) : IsProbabilityMeasure (ssaCountInputLaw lam Λ T x₀ L) := by
  have := isProbabilityMeasure_ssaLevelCountLaw hΛ T x₀ L
  unfold ssaCountInputLaw
  infer_instance

/-- Forgetting the counts of an input gives an input of law `ssaInputLaw` (Giles 2015, §8, p. 56,
l. 2411–2415). -/
lemma ssaCountInputLaw_map {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L : ℕ) :
    (ssaCountInputLaw lam Λ T x₀ L).map (fun y ℓ => (y ℓ).1) = ssaInputLaw lam Λ T x₀ L := by
  have := isProbabilityMeasure_ssaLevelCountLaw hΛ T x₀ L
  rw [ssaCountInputLaw, Measure.infinitePi_map_pi _ fun _ => measurable_fst, ssaInputLaw]
  exact congrArg _ (funext fun ℓ => ssaLevelCountLaw_map_fst lam Λ T x₀ L ℓ)

/-- Forgetting the counts of all samples maps the sampling measure with counts onto the sampling
measure of `ssa_mlmc_unbiased` (Giles 2015, §8, p. 56, l. 2411–2415). -/
lemma ssaCountSampling_map {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L : ℕ) :
    (Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L).map
        (fun x p ℓ => (x p ℓ).1) =
      Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L := by
  have := isProbabilityMeasure_ssaCountInputLaw hΛ T x₀ L
  have hf : ∀ _ : ℕ × ℕ, Measurable fun (y : ℕ → (ℕ × ℕ) × ℕ) (ℓ : ℕ) => (y ℓ).1 :=
    fun _ => measurable_pi_lambda _ fun ℓ => measurable_fst.comp (measurable_pi_apply ℓ)
  rw [Measure.infinitePi_map_pi _ hf]
  exact congrArg _ (funext fun _ => ssaCountInputLaw_map hΛ T x₀ L)

/-- Forgetting the counts is measurable (for the sampling space of Giles 2015, §8, p. 56,
l. 2411–2415). -/
lemma measurable_ssaForgetCount :
    Measurable fun (x : ℕ × ℕ → ℕ → (ℕ × ℕ) × ℕ) (p : ℕ × ℕ) (ℓ : ℕ) => (x p ℓ).1 := by
  fun_prop

/-- The exact-level coordinate of an input has the law of the counting chain (Giles 2015, §8,
p. 56, l. 2412–2415). -/
lemma measurePreserving_ssaCountInput_exact {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) (x₀ L : ℕ) :
    MeasurePreserving (fun y : ℕ → (ℕ × ℕ) × ℕ => y (L + 1)) (ssaCountInputLaw lam Λ T x₀ L)
      (ssaChainCount lam Λ (T / 2 ^ L) x₀ (2 ^ L)) := by
  have := isProbabilityMeasure_ssaLevelCountLaw hΛ T x₀ L
  have e : ssaLevelCountLaw lam Λ T x₀ L (L + 1) =
      ssaChainCount lam Λ (T / 2 ^ L) x₀ (2 ^ L) := by
    rw [ssaLevelCountLaw, if_neg (by omega)]
  have h1 := measurePreserving_eval_infinitePi (ssaLevelCountLaw lam Λ T x₀ L) (L + 1)
  rw [e] at h1
  exact h1

/-- The exact-level coordinate of the `n`-th exact-level sample has the law of the counting chain
(Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma measurePreserving_ssaCountSampling_exact {lam : ℕ → ℝ≥0} {Λ : ℝ≥0}
    (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ L n : ℕ) :
    MeasurePreserving (fun x : ℕ × ℕ → ℕ → (ℕ × ℕ) × ℕ => x (L + 1, n) (L + 1))
      (Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L)
      (ssaChainCount lam Λ (T / 2 ^ L) x₀ (2 ^ L)) := by
  have := isProbabilityMeasure_ssaCountInputLaw hΛ T x₀ L
  exact (measurePreserving_ssaCountInput_exact hΛ T x₀ L).comp (measurePreserving_eval_infinitePi
    (fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L) (L + 1, n))

/-- **The random cost of an exact-level sample** (Giles 2015, §8, p. 56, l. 2411–2417: the exact
Stochastic Simulation Algorithm at the finest level, and "the complexity is reduced to `O(ε⁻²)`";
Theorem 1, §2.1, p. 6, l. 274: "each with expected cost `Cℓ`").  For `λ ≤ Λ`: the input law with
counts is a probability measure, its exact-level coordinate `L + 1` has the law of the counting
chain (`2^L` coupled steps of size `T 2^{−L}`), whose tick count `K` has the law `P(ΛT)`, and the
cost `2^L + K` of an exact-level sample is square integrable with mean `2^L + ΛT` (the deterministic
cost charged in `ssa_mlmc_complexity`) and variance `ΛT`. -/
theorem ssa_exact_sample_cost {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L : ℕ) :
    IsProbabilityMeasure (ssaCountInputLaw lam Λ T x₀ L) ∧
      (ssaCountInputLaw lam Λ T x₀ L).map (fun y => y (L + 1)) =
        ssaChainCount lam Λ (T / 2 ^ L) x₀ (2 ^ L) ∧
      (ssaChainCount lam Λ (T / 2 ^ L) x₀ (2 ^ L)).map Prod.snd = poissonMeasure (Λ * T) ∧
      MemLp (ssaSampleCost L (L + 1)) 2 (ssaCountInputLaw lam Λ T x₀ L) ∧
      ∫ y, ssaSampleCost L (L + 1) y ∂(ssaCountInputLaw lam Λ T x₀ L) = 2 ^ L + Λ * T ∧
      variance (ssaSampleCost L (L + 1)) (ssaCountInputLaw lam Λ T x₀ L) = Λ * T := by
  have hν := isProbabilityMeasure_ssaCountInputLaw hΛ T x₀ L
  have hP := isProbabilityMeasure_ssaChainCount hΛ (T / 2 ^ L) x₀ (2 ^ L)
  have hmp := measurePreserving_ssaCountInput_exact hΛ T x₀ L
  have hsnd := ssaChainCount_pow_snd hΛ T x₀ L
  obtain ⟨hK2, hKint, hKvar⟩ := ssaCount_moments hsnd
  rw [NNReal.coe_mul] at hKint hKvar
  have e : ssaSampleCost L (L + 1) =
      fun y => (fun u : (ℕ × ℕ) × ℕ => (2 : ℝ) ^ L + (u.2 : ℝ)) (y (L + 1)) := by
    funext y
    rw [ssaSampleCost, if_neg (by omega)]
  have hc2 : MemLp (fun u : (ℕ × ℕ) × ℕ => (2 : ℝ) ^ L + (u.2 : ℝ)) 2
      (ssaChainCount lam Λ (T / 2 ^ L) x₀ (2 ^ L)) :=
    (memLp_const ((2 : ℝ) ^ L)).add hK2
  refine ⟨hν, hmp.map_eq, hsnd, ?_, ?_, ?_⟩
  · rw [e]
    exact hc2.comp_measurePreserving hmp
  · rw [e, integral_comp_of_measurePreserving
        (f := fun u : (ℕ × ℕ) × ℕ => (2 : ℝ) ^ L + (u.2 : ℝ)) hmp
        Measurable.of_discrete.aestronglyMeasurable,
      integral_add (integrable_const _) (hK2.integrable one_le_two), integral_const,
      probReal_univ, one_smul, hKint]
  · rw [e, hmp.variance_fun_comp (f := fun u : (ℕ × ℕ) × ℕ => (2 : ℝ) ^ L + (u.2 : ℝ))
      Measurable.of_discrete.aemeasurable, variance_const_add hK2.aestronglyMeasurable, hKvar]

/-- The total random cost is the deterministic part `∑_{ℓ ≤ L} N_ℓ 2^ℓ + N_{L+1} 2^L` plus the
tick counts of the exact-level samples (Giles 2015, §8, p. 56, l. 2411–2417, with the total cost
of Theorem 1, §2.1, p. 7, l. 294–295). -/
lemma ssaTotalCost_eq (L : ℕ) (N : ℕ → ℕ) (x : ℕ × ℕ → ℕ → (ℕ × ℕ) × ℕ) :
    totalCost (fun ℓ n x => ssaSampleCost L ℓ (x (ℓ, n))) (L + 1) N x =
      (∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ + (N (L + 1) : ℝ) * 2 ^ L) +
        ∑ n ∈ range (N (L + 1)), ((x (L + 1, n) (L + 1)).2 : ℝ) := by
  rw [totalCost, Finset.sum_range_succ]
  have h1 : ∀ ℓ ∈ range (L + 1), ∑ n ∈ range (N ℓ), ssaSampleCost L ℓ (x (ℓ, n)) =
      (N ℓ : ℝ) * 2 ^ ℓ := fun ℓ hℓ => by
    have hℓL : ℓ ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    have h0 : ∀ n ∈ range (N ℓ), ssaSampleCost L ℓ (x (ℓ, n)) = 2 ^ ℓ := fun n _ => by
      rw [ssaSampleCost, if_pos hℓL]
    rw [Finset.sum_congr rfl h0, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 : ∀ n ∈ range (N (L + 1)), ssaSampleCost L (L + 1) (x (L + 1, n)) =
      2 ^ L + ((x (L + 1, n) (L + 1)).2 : ℝ) := fun n _ => by
    rw [ssaSampleCost, if_neg (by omega)]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring

/-- **The mean and the variance of the total random cost** (Giles 2015, §8, p. 56, l. 2411–2417;
Theorem 1, §2.1, p. 7, l. 294–295: "with a computational complexity `C` with bound `E[C] ≤` …").
For `λ ≤ Λ` and any sample numbers `N_ℓ`, on the sampling space with counts (the coordinates of
`Measure.infinitePi` of `ssaCountInputLaw`), the total random cost
`C = ∑_{ℓ ≤ L+1} ∑_{n < N_ℓ} ssaSampleCost L ℓ (ω^{(ℓ,n)})` is square integrable, its mean is the
deterministic cost `∑_{ℓ ≤ L} N_ℓ 2^ℓ + N_{L+1}(2^L + ΛT)` of `ssa_mlmc_complexity`, and its
variance is `N_{L+1} ΛT`: the `N_{L+1}` exact-level tick counts are independent `P(ΛT)` variates. -/
theorem ssaTotalCost_moments {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L : ℕ) (N : ℕ → ℕ) :
    MemLp (totalCost (fun ℓ n x => ssaSampleCost L ℓ (x (ℓ, n))) (L + 1) N) 2
        (Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L) ∧
      ∫ x, totalCost (fun ℓ n x => ssaSampleCost L ℓ (x (ℓ, n))) (L + 1) N x
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L) =
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ + (N (L + 1) : ℝ) * (2 ^ L + Λ * T) ∧
      variance (totalCost (fun ℓ n x => ssaSampleCost L ℓ (x (ℓ, n))) (L + 1) N)
          (Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L) =
        (N (L + 1) : ℝ) * (Λ * T) := by
  set μ := Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L with hμ_def
  have hν := isProbabilityMeasure_ssaCountInputLaw hΛ T x₀ L
  obtain ⟨hμ, hind, -⟩ := exists_iid_inputs (ssaCountInputLaw lam Λ T x₀ L)
  have hP := isProbabilityMeasure_ssaChainCount hΛ (T / 2 ^ L) x₀ (2 ^ L)
  obtain ⟨hK2, hKint, hKvar⟩ := ssaCount_moments (ssaChainCount_pow_snd hΛ T x₀ L)
  rw [NNReal.coe_mul] at hKint hKvar
  set A : ℝ := ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ + (N (L + 1) : ℝ) * 2 ^ L with hA_def
  set K : ℕ → (ℕ × ℕ → ℕ → (ℕ × ℕ) × ℕ) → ℝ := fun n x => ((x (L + 1, n) (L + 1)).2 : ℝ)
    with hK_def
  have hmp := measurePreserving_ssaCountSampling_exact hΛ T x₀ L
  have hKm : ∀ n, MemLp (K n) 2 μ := fun n => hK2.comp_measurePreserving (hmp n)
  have hKi : ∀ n, ∫ x, K n x ∂μ = Λ * T := fun n => by
    rw [← hKint]
    exact integral_comp_of_measurePreserving (f := fun u : (ℕ × ℕ) × ℕ => (u.2 : ℝ)) (hmp n)
      Measurable.of_discrete.aestronglyMeasurable
  have hKv : ∀ n, variance (K n) μ = Λ * T := fun n => by
    rw [← hKvar]
    exact (hmp n).variance_fun_comp (f := fun u : (ℕ × ℕ) × ℕ => (u.2 : ℝ))
      Measurable.of_discrete.aemeasurable
  have e : totalCost (fun ℓ n x => ssaSampleCost L ℓ (x (ℓ, n))) (L + 1) N =
      fun x => A + ∑ n ∈ range (N (L + 1)), K n x := funext fun x => ssaTotalCost_eq L N x
  have hS : MemLp (fun x => ∑ n ∈ range (N (L + 1)), K n x) 2 μ :=
    memLp_finsetSum _ fun n _ => hKm n
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact (memLp_const A).add hS
  · rw [e, integral_add (integrable_const A) (hS.integrable one_le_two), integral_const,
      probReal_univ, one_smul, integral_finsetSum _ fun n _ => (hKm n).integrable one_le_two,
      Finset.sum_congr rfl fun n _ => hKi n, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      hA_def]
    ring
  · have e2 : (fun x => ∑ n ∈ range (N (L + 1)), K n x) = ∑ n ∈ range (N (L + 1)), K n := by
      funext x
      rw [Finset.sum_apply]
    have hX := hind.comp (fun _ (y : ℕ → (ℕ × ℕ) × ℕ) => ((y (L + 1)).2 : ℝ))
      (fun _ => (Measurable.of_discrete (f := fun u : (ℕ × ℕ) × ℕ => (u.2 : ℝ))).comp
        (measurable_pi_apply (L + 1)))
    rw [e, variance_const_add hS.aestronglyMeasurable A, e2,
      IndepFun.variance_sum (fun n _ => hKm n) (fun a _ b _ hab =>
        hX.indepFun (i := (L + 1, a)) (j := (L + 1, b)) (by simpa using hab)),
      Finset.sum_congr rfl fun n _ => hKv n, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **(G8-14 with the random cost) With the exact SSA level, a fixed number of levels and the
random number of clock ticks charged, the expected cost is `O(ε⁻²)`** (Giles 2015, §8, p. 56,
l. 2415–2417: "their overall multilevel estimator is unbiased … and the complexity is reduced to
`O(ε⁻²)` because the number of levels remains fixed as `ε → 0`"; complexity in the sense of
Theorem 1, §2.1, p. 7, l. 294–295: "a computational complexity `C` with bound `E[C] ≤` …").  Let
`0 ≤ λ ≤ Λ` and `|Φ| ≤ M`, and fix `L`.  The samples are the coordinates of the product of
`ssaCountInputLaw`: the inputs of `ssa_mlmc_unbiased`, the exact-level coordinate carrying the tick
count of its own uniformisation clock.  This sampling measure is a probability measure, and
forgetting the counts maps it onto the sampling measure of `ssa_mlmc_complexity`.  There is `c > 0`
such that for every `0 < ε ≤ 1` some `N_ℓ ≥ 1` give: the estimator of `ssa_mlmc_complexity`,
evaluated at the state components of the samples, has a square-integrable error and mean square
error `E[(Y − E[Φ(X_T)])²] < ε²`; the total random cost
`C = ∑_{ℓ ≤ L+1} ∑_{n < N_ℓ} ssaSampleCost L ℓ (ω^{(ℓ,n)})` (`2^ℓ` per tau-leaping sample, `2^L + K`
per exact-level sample with `K ~ P(ΛT)` its tick count) is integrable with `E[C] ≤ c ε⁻²`; and
`P(C ≥ 2cε⁻²) ≤ ε²/c` (Chebyshev, since `V[C] = N_{L+1} ΛT ≤ E[C]`, `ssaTotalCost_moments`).  In
the proof `c` and the `N_ℓ` are those of `ssa_mlmc_complexity`, whose deterministic cost equals
`E[C]` (the statement does not record this); `c` depends on `L` (and on `λ`, `Λ`, `T`, `x₀`,
`Φ`).  Deviations: one reaction, bounded propensity and payoff,
exact chain by uniformisation, cost counted in tau-leaping steps and clock ticks. -/
theorem ssa_mlmc_complexity_random_cost {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) (x₀ : ℕ) {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) (L : ℕ) :
    IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L) ∧
    (Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L).map
        (fun x p ℓ => (x p ℓ).1) =
      Measure.infinitePi (fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 2), blockMean (ssaCorrection Φ L)
            (fun p x => x p) ℓ (N ℓ) (fun p ℓ' => (x p ℓ').1) -
              ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L) ∧
        ∫ x, (∑ ℓ ∈ range (L + 2), blockMean (ssaCorrection Φ L) (fun p x => x p) ℓ (N ℓ)
            (fun p ℓ' => (x p ℓ').1) - ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L) < ε ^ 2 ∧
        Integrable (totalCost (fun ℓ n x => ssaSampleCost L ℓ (x (ℓ, n))) (L + 1) N)
          (Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L) ∧
        ∫ x, totalCost (fun ℓ n x => ssaSampleCost L ℓ (x (ℓ, n))) (L + 1) N x
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L) ≤ c / ε ^ 2 ∧
        (Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L)
          {x | 2 * c / ε ^ 2 ≤ totalCost (fun ℓ n x => ssaSampleCost L ℓ (x (ℓ, n))) (L + 1) N x}
          ≤ ENNReal.ofReal (ε ^ 2 / c) := by
  set μ := Measure.infinitePi fun _ : ℕ × ℕ => ssaCountInputLaw lam Λ T x₀ L with hμ_def
  have hν := isProbabilityMeasure_ssaCountInputLaw hΛ T x₀ L
  have hμ : IsProbabilityMeasure μ := (exists_iid_inputs _).1
  have hmap := ssaCountSampling_map hΛ T x₀ L
  obtain ⟨-, c, hc, h⟩ := ssa_mlmc_complexity hΛ T x₀ hΦ L
  refine ⟨hμ, hmap, c, hc, fun ε hε hε1 => ?_⟩
  obtain ⟨N, hN, hint, hmse, hcost⟩ := h ε hε hε1
  set F : (ℕ × ℕ → ℕ → ℕ × ℕ) → ℝ := fun y => (∑ ℓ ∈ range (L + 2),
    blockMean (ssaCorrection Φ L) (fun p x => x p) ℓ (N ℓ) y -
      ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2 with hF_def
  have hFm : AEStronglyMeasurable F (μ.map (fun x p ℓ => (x p ℓ).1)) := by
    rw [hmap]
    exact hint.aestronglyMeasurable
  have hint' : Integrable (fun x => F (fun p ℓ => (x p ℓ).1)) μ := by
    have h1 := hint
    rw [← hmap] at h1
    exact (integrable_map_measure hFm measurable_ssaForgetCount.aemeasurable).1 h1
  have hmse' : ∫ x, F (fun p ℓ => (x p ℓ).1) ∂μ < ε ^ 2 := by
    rw [← integral_map measurable_ssaForgetCount.aemeasurable hFm, hmap]
    exact hmse
  obtain ⟨hC2, hCmean, hCvar⟩ := ssaTotalCost_moments hΛ T x₀ L N
  set C : (ℕ × ℕ → ℕ → (ℕ × ℕ) × ℕ) → ℝ :=
    totalCost (fun ℓ n x => ssaSampleCost L ℓ (x (ℓ, n))) (L + 1) N with hC_def
  have hmean_le : ∫ x, C x ∂μ ≤ c / ε ^ 2 := by
    rw [hCmean]
    exact hcost
  refine ⟨N, hN, hint', hmse', hC2.integrable one_le_two, hmean_le, ?_⟩
  set B := c / ε ^ 2 with hB_def
  have hB : 0 < B := by positivity
  have hvar_le : variance C μ ≤ B := by
    rw [hCvar]
    refine le_trans ?_ (hCmean ▸ hmean_le)
    have h1 : 0 ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ := sum_nonneg fun ℓ _ => by positivity
    have h2 : 0 ≤ (N (L + 1) : ℝ) * 2 ^ L := by positivity
    have h3 : (N (L + 1) : ℝ) * (2 ^ L + Λ * T) = N (L + 1) * 2 ^ L + N (L + 1) * (Λ * T) := by
      ring
    linarith
  have hsub : {x | 2 * c / ε ^ 2 ≤ C x} ⊆ {x | B ≤ |C x - ∫ y, C y ∂μ|} := fun x hx => by
    replace hx : 2 * c / ε ^ 2 ≤ C x := hx
    show B ≤ |C x - ∫ y, C y ∂μ|
    have h2B : 2 * c / ε ^ 2 = 2 * B := by
      rw [hB_def]
      ring
    rw [h2B] at hx
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc μ {x | 2 * c / ε ^ 2 ≤ C x} ≤ μ {x | B ≤ |C x - ∫ y, C y ∂μ|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (variance C μ / B ^ 2) := meas_ge_le_variance_div_sq hC2 hB
    _ ≤ ENNReal.ofReal (ε ^ 2 / c) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ (by positivity)]
        calc variance C μ ≤ B := hvar_le
          _ = ε ^ 2 / c * B ^ 2 := by
              rw [hB_def]
              field_simp

end MLMC
