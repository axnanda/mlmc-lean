import MlmcLean.TauLeapingExact

/-!
# Tau-leaping coupled with the exact SSA: an unbiased multilevel estimator (Giles 2015, §8)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §8
"Continuous-time Markov chains", p. 56 (`docs/giles2015.txt`, l. 2411–2417): "In their paper,
Anderson and Higham (2012) … also include an additional coupling at the finest level to the exact
Stochastic Simulation Algorithm developed by (Gillespie 1976) which updates the reaction rates
after every single reaction.  Hence, their overall multilevel estimator is unbiased, unlike the
estimators discussed earlier for SDEs, and the complexity is reduced to `O(ε⁻²)` because the number
of levels remains fixed as `ε → 0`."

**Setting** (that of `MlmcLean/TauLeapingExact.lean`): one reaction, the state `x ∈ ℕ` counts the
reactions, each reaction moves `x` to `x + 1`, the propensity `λ : ℕ → [0, ∞)` is bounded,
`λ ≤ Λ` (on `ℕ` it is then `Λ`-Lipschitz, `abs_sub_le_mul_of_le_nat`, though nothing here needs
it), and the payoff is bounded, `|Φ| ≤ M`.  The exact chain at time `t` has the law
`exactLaw λ Λ t x`: a rate-`Λ` clock ticks `P(Λt)` times, and at each tick the state jumps with
probability `λ(x)/Λ`, the rate updated after every reaction (uniformisation).

**Poisson thinning.**  `binomialLaw n p` is `Bin(n, p)`, by its masses; `poisson_thinning`:
`P(μ).bind (k ↦ Bin(k, p)) = P(pμ)` for `p ≤ 1` (a standalone statement of the fact behind
`ssaStep_map_snd`, whose proof uses `exactLaw_const` instead).

**The coupling** of a tau-leaping step with the exact chain, by uniformisation with shared
uniforms.  In a step of length `h` from the exact state `x` and the tau-leaping state `z`, the
rate-`Λ` clock ticks `K ~ P(Λh)` times; at each tick a shared uniform `U` decides: the exact chain
jumps iff `U ≤ λ(current exact state)/Λ`, the tau-leaping count increases iff `U ≤ λ(z)/Λ` (`z`
frozen at the start of the step).  `ssaTick` is the joint law of one tick (four outcomes with the
probabilities `min(p, q)`, `(p − q)⁺`, `(q − p)⁺`, `1 − max(p, q)`), `ssaTickPow` iterates it,
`ssaStep` is one coupled step and `ssaChain` the coupled chain over `N` steps.
* `ssaStep_map_fst`, `ssaStep_map_snd`: the exact component of a step has the law
  `exactLaw λ Λ h x`, the tau-leaping component the law `tauStep λ h z` (thinning:
  `exactLaw_eq_of_bound`, `exactLaw_const`).
* `ssaChain_marginals`: after `N` steps of size `T/N` the exact component has the law
  `exactLaw λ Λ T x₀` (Chapman–Kolmogorov, `exactLaw_add`) and the tau-leaping component the law
  `tauChain λ (T/N) x₀ N`.

**The coupling error** (`h = T/N`).
* `ssaChain_ne_le`: `P(X_T ≠ Z_N) ≤ Λ²T²/N = Λ²T h`.  If the paths agree at the start of a step,
  both see the rate `λ(z)` at its first tick, so they separate only at a second tick, which has
  probability at most `(Λh)²`; over `N` steps the probabilities add.
* `ssaChain_abs_le`: `|X_T − Z_N|` is integrable and `P(X_T ≠ Z_N) ≤ E|X_T − Z_N| ≤ (Λ²T + Λ³T²) h`
  (the mean distance grows by at most `Λh` per step once the paths differ, by `(Λh)²` while they
  agree).
* `ssaChain_sq_le`: `Φ(X_T) − Φ(Z_N) ∈ L²` and `E[(Φ(X_T) − Φ(Z_N))²] ≤ 4M² Λ²T h`.

**The unbiased estimator.**  Levels `ℓ ≤ L` are the Poisson-coupled tau-leaping levels of
`tauLeaping_mlmc_exact` (`tauLevelLaw`: `2^ℓ` steps of size `T 2^{−ℓ}`, cost `2^ℓ`); level `L + 1`
couples the `2^L` steps of level `L` with the exact chain (`ssaChain`).  `ssaLevelLaw`,
`ssaInputLaw`, `ssaCorrection`: the level laws, the input law (independent across levels) and the
corrections; the samples are the coordinates of `Measure.infinitePi fun _ ↦ ssaInputLaw …`.
* `ssa_mlmc_unbiased` (**G8-13**): for every `L` and `N_ℓ ≥ 1` the sampling measure is a
  probability measure, the estimator is integrable and its mean is exactly `E[Φ(X_T)]`.
* `variance_ssaCorrection_exact_le`: the exact-level correction has variance `≤ 4M²Λ²T²/2^L`.
* `ssa_mlmc_complexity` (**G8-14**): for every fixed `L` there is `c > 0` such that for every
  `0 < ε ≤ 1` some `N_ℓ ≥ 1` give a square-integrable error, mean square error `< ε²` and cost
  `∑_{ℓ ≤ L} N_ℓ 2^ℓ + N_{L+1}(2^L + ΛT) ≤ c ε⁻²` (allocation of `fixed_levels_cost`), with the
  sampling measure a probability measure.  The rate `ε⁻²` itself needs only unbiasedness and
  finitely many levels of finite variance (it holds for plain Monte Carlo on the exact chain too);
  the coupling makes the exact-level variance small, `O(2^{−L})`.

**Deviations.**  One reaction (Anderson and Higham treat several); bounded propensities and
bounded payoffs.  The exact chain is simulated by uniformisation, a Poisson clock of rate `Λ`
thinned with probabilities `λ(x)/Λ`, not by Gillespie's exponential waiting times; it is the same
Markov chain (`exactLaw_unique`, `exactLaw_eq_of_bound`).  The coupling is constructed by
uniformisation with shared uniforms, not from Anderson and Higham's split coupling of unit-rate
Poisson processes; the shared uniform enters only through the joint law `ssaTick` of one tick, not
as an explicit uniform random variable.  For one reaction the joint process has the jump rates of
their split coupling (common jumps at rate `min(λ(X_t), λ(Z_{t_n}))`, single jumps at the positive
parts of the difference), so it is their coupling in law; this identification is a remark, not
proved here.  The cost of an exact-level sample is its expected value
`2^L + ΛT` (`2^L` tau-leaping steps and `E[P(ΛT)] = ΛT` clock ticks); the random cost is not
modelled here; see `ssa_mlmc_complexity_random_cost` (`MlmcLean.TauLeapingSSACost`), where the
tick count of each exact-level sample is part of the sample and `E[C] ≤ c ε⁻²` for the random total
cost `C`.  `ε ≤ 1`, and `c` depends on `L`.  `Bin(n, p)` is defined here by its masses.

**Not proved.**  Several reactions, unbounded propensities, unbounded (e.g. Lipschitz) payoffs, and
Anderson and Higham's sharper variance analysis (the random cost of the exact level is in
`MlmcLean.TauLeapingSSACost`); the contrast with the biased SDE estimators is only the statement
that the bias here is zero (the tau-leaping estimator alone has the `O(2^{−L})` bias of
`tauLeaping_weak_error_exact`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace MLMC

/-! ### Poisson thinning -/

/-- Pascal's rule for binomial sums (used for the thinning of Giles 2015, §8, p. 56, l. 2412–2415):
`∑_{k ≤ n+1} C(n+1, k) aᵏ b^{n+1−k} f(k) = ∑_{k ≤ n} C(n, k) aᵏ b^{n−k} (a f(k+1) + b f(k))`. -/
lemma sum_range_choose_succ_mul (n : ℕ) (a b : ℝ) (f : ℕ → ℝ) :
    ∑ k ∈ range (n + 2), ((n + 1).choose k : ℝ) * a ^ k * b ^ (n + 1 - k) * f k =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * a ^ k * b ^ (n - k) * (a * f (k + 1) + b * f k) := by
  have e1 : ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) * a ^ (k + 1) *
        b ^ (n + 1 - (k + 1)) * f (k + 1) =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * a ^ (k + 1) * b ^ (n - k) * f (k + 1) +
        ∑ k ∈ range (n + 1), (n.choose (k + 1) : ℝ) * a ^ (k + 1) * b ^ (n + 1 - (k + 1)) *
          f (k + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right]
    ring
  have e2 : ∑ k ∈ range (n + 1), (n.choose (k + 1) : ℝ) * a ^ (k + 1) * b ^ (n + 1 - (k + 1)) *
        f (k + 1) + b ^ (n + 1) * f 0 =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * a ^ k * b ^ (n - k) * (b * f k) := by
    have h := Finset.sum_range_succ' (fun k => (n.choose k : ℝ) * a ^ k * b ^ (n + 1 - k) * f k)
      (n + 1)
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, zero_mul,
      add_zero] at h
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [Nat.sub_add_comm hk', pow_succ]
    ring
  rw [Finset.sum_range_succ', e1, add_assoc]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
  rw [e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The binomial law** `Bin(n, p)` on `ℕ`, by its masses `C(n, k) p^k (1 − p)^{n−k}`, `k ≤ n`
(the number of successes in `n` independent trials of probability `p ≤ 1`; Giles 2015, §8, p. 56,
l. 2412–2415, used for the thinning behind the coupling of tau-leaping with the exact SSA). -/
noncomputable def binomialLaw (n : ℕ) (p : ℝ≥0) : Measure ℕ :=
  ∑ k ∈ range (n + 1), ((n.choose k : ℝ≥0) * p ^ k * (1 - p) ^ (n - k)) • Measure.dirac k

/-- `∫ f dBin(n, p) = ∑_{k ≤ n} C(n, k) p^k (1 − p)^{n−k} f(k)` for `p ≤ 1` (the binomial law of
the thinning in Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma integral_binomialLaw (n : ℕ) {p : ℝ≥0} (hp : p ≤ 1) (f : ℕ → ℝ) :
    ∫ k, f k ∂(binomialLaw n p) =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) * f k := by
  rw [binomialLaw, integral_finsetSum_measure fun k _ =>
    Integrable.smul_measure_nnreal (integrable_dirac enorm_lt_top)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_pow, NNReal.coe_sub hp,
    NNReal.coe_one, NNReal.coe_natCast]

/-- One more Bernoulli trial (Giles 2015, §8, p. 56, l. 2412–2415, thinning): for `p ≤ 1`,
`Bin(n + 1, p)` is `Bin(n, p)` followed by the step `k ↦ p δ_{k+1} + (1 − p) δ_k`, the uniformised
jump kernel `jumpKernel` with the constant rate `p` and the clock rate `1`. -/
lemma binomialLaw_succ (n : ℕ) {p : ℝ≥0} (hp : p ≤ 1)
    (hB : IsProbabilityMeasure (binomialLaw n p)) :
    binomialLaw (n + 1) p = (binomialLaw n p).bind (jumpKernel (fun _ => p) 1) := by
  have hJ : ∀ k, IsProbabilityMeasure (jumpKernel (fun _ => p) 1 k) :=
    fun k => ⟨jumpKernel_univ (fun _ => hp) k⟩
  have hB1 : IsFiniteMeasure (binomialLaw (n + 1) p) := by
    unfold binomialLaw
    infer_instance
  have hbind : IsProbabilityMeasure ((binomialLaw n p).bind (jumpKernel (fun _ => p) 1)) :=
    ⟨measure_univ_bind_of_discrete _ fun k => jumpKernel_univ (fun _ => hp) k⟩
  refine measure_ext_of_integral_bounded_nat fun f hf => ?_
  rw [integral_bind_of_abs_le _ hJ hf]
  simp only [integral_jumpKernel (fun _ => hp), div_one]
  rw [integral_binomialLaw _ hp, integral_binomialLaw _ hp]
  exact sum_range_choose_succ_mul n p (1 - p) f

/-- `Bin(n, p)` is the law after `n` steps of the uniformised jump chain with constant rate `p ≤ 1`
and clock rate `1`, started at `0`: `Bin(n, p) = J^n(0)` (`jumpPow`;
Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma binomialLaw_eq_jumpPow {p : ℝ≥0} (hp : p ≤ 1) :
    ∀ n, binomialLaw n p = jumpPow (fun _ => p) 1 n 0
  | 0 => by
      rw [jumpPow_zero, binomialLaw, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one,
        pow_zero, pow_zero, mul_one, mul_one, one_smul]
  | n + 1 => by
      have ih := binomialLaw_eq_jumpPow hp n
      have hB : IsProbabilityMeasure (binomialLaw n p) := by
        rw [ih]
        exact ⟨jumpPow_univ (fun _ => hp) n 0⟩
      rw [binomialLaw_succ n hp hB, ih, jumpPow_succ]

/-- `Bin(n, p)` is a probability measure for `p ≤ 1` (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma isProbabilityMeasure_binomialLaw (n : ℕ) {p : ℝ≥0} (hp : p ≤ 1) :
    IsProbabilityMeasure (binomialLaw n p) := by
  rw [binomialLaw_eq_jumpPow hp n]
  exact ⟨jumpPow_univ (fun _ => hp) n 0⟩

/-- **Poisson thinning** (Giles 2015, §8, p. 56, l. 2412–2415: Anderson and Higham "include an
additional coupling at the finest level to the exact Stochastic Simulation Algorithm"; in the
uniformised coupling each tick of a rate-`Λ` clock is kept with probability `λ/Λ`, and the kept
ticks form a Poisson variate of mean `hλ`, the tau-leaping increment `P(hλ(x_n))` of p. 55,
l. 2375).  For `p ≤ 1` and `μ ≥ 0`, a `P(μ)` number of independent trials of probability `p` has
`P(pμ)` successes: `P(μ).bind (k ↦ Bin(k, p)) = P(pμ)`. -/
theorem poisson_thinning (μ : ℝ≥0) {p : ℝ≥0} (hp : p ≤ 1) :
    (poissonMeasure μ).bind (fun k => binomialLaw k p) = poissonMeasure (p * μ) := by
  have e : (poissonMeasure μ).bind (fun k => binomialLaw k p) = exactLaw (fun _ => p) 1 μ 0 := by
    rw [exactLaw, one_mul]
    exact congrArg _ (funext fun k => binomialLaw_eq_jumpPow hp k)
  rw [e, exactLaw_eq_of_bound (Λ' := p) (fun _ => hp) (fun _ => le_rfl), exactLaw_const]
  have e2 : (fun k : ℕ => 0 + k) = id := funext fun k => zero_add k
  rw [e2, Measure.map_id]

/-! ### The coupled tick -/

/-- **One tick of the coupled clock** (Giles 2015, §8, p. 56, l. 2412–2415: "an additional coupling
at the finest level to the exact Stochastic Simulation Algorithm developed by (Gillespie 1976)
which updates the reaction rates after every single reaction").  The pair `s = (x, w)` holds the
exact state `x` and the tau-leaping state `w`, whose rate is frozen at `λ(z)` for the step started
at `z`.  At a tick of the rate-`Λ` clock a shared uniform `U` decides: the exact chain jumps iff
`U ≤ p = λ(x)/Λ` (its rate updated after every reaction) and the tau-leaping count increases iff
`U ≤ q = λ(z)/Λ`.  The four outcomes both / only exact / only tau / neither have the probabilities
`min(p, q)`, `(p − q)⁺`, `(q − p)⁺` and `1 − max(p, q)` (truncated subtraction in `ℝ≥0`). -/
noncomputable def ssaTick (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (z : ℕ) (s : ℕ × ℕ) : Measure (ℕ × ℕ) :=
  min (lam s.1 / Λ) (lam z / Λ) • Measure.dirac (s.1 + 1, s.2 + 1) +
    (lam s.1 / Λ - lam z / Λ) • Measure.dirac (s.1 + 1, s.2) +
    (lam z / Λ - lam s.1 / Λ) • Measure.dirac (s.1, s.2 + 1) +
    (1 - max (lam s.1 / Λ) (lam z / Λ)) • Measure.dirac s

/-- The four probabilities of `ssaTick` add up to the marginal probabilities (Giles 2015, §8, p. 56,
l. 2412–2415): `min(p, q) + (p − q)⁺ = p` and `(q − p)⁺ + 1 − max(p, q) = 1 − p` for `q ≤ 1`. -/
lemma min_add_tsub_and_tsub_add_one_sub_max {p q : ℝ≥0} (hq : q ≤ 1) :
    min p q + (p - q) = p ∧ (q - p) + (1 - max p q) = 1 - p := by
  rcases le_total p q with h | h
  · rw [min_eq_left h, tsub_eq_zero_of_le h, add_zero, max_eq_right h, add_comm,
      tsub_add_tsub_cancel hq h]
    exact ⟨rfl, rfl⟩
  · rw [min_eq_right h, add_tsub_cancel_of_le h, tsub_eq_zero_of_le h, zero_add, max_eq_left h]
    exact ⟨rfl, rfl⟩

/-- **The exact component of a coupled tick is the uniformised jump** (Giles 2015, §8, p. 56,
l. 2412–2414: the exact SSA "updates the reaction rates after every single reaction"): for
`λ ≤ Λ`, the first marginal of `ssaTick` is `jumpKernel λ Λ x`, a jump with probability
`λ(x)/Λ`. -/
lemma ssaTick_map_fst {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (z : ℕ) (s : ℕ × ℕ) :
    (ssaTick lam Λ z s).map Prod.fst = jumpKernel lam Λ s.1 := by
  obtain ⟨h1, h2⟩ := min_add_tsub_and_tsub_add_one_sub_max (p := lam s.1 / Λ)
    (rate_div_le_one hΛ z)
  rw [ssaTick, Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
    Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst,
    Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst, jumpKernel]
  calc _ = (min (lam s.1 / Λ) (lam z / Λ) + (lam s.1 / Λ - lam z / Λ)) •
        Measure.dirac (s.1 + 1) +
        ((lam z / Λ - lam s.1 / Λ) + (1 - max (lam s.1 / Λ) (lam z / Λ))) •
          Measure.dirac s.1 := by
        rw [add_smul, add_smul]
        abel
    _ = _ := by rw [h1, h2]

/-- **The tau-leaping component of a coupled tick has the frozen rate** (Giles 2015, §8, p. 55,
l. 2372–2374: tau-leaping approximates "the reaction rate as being constant throughout the
timestep"): for `λ ≤ Λ`, the second marginal of `ssaTick` with frozen state `z` is
`jumpKernel (fun _ ↦ λ(z)) Λ w`, a jump with probability `λ(z)/Λ`. -/
lemma ssaTick_map_snd {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (z : ℕ) (s : ℕ × ℕ) :
    (ssaTick lam Λ z s).map Prod.snd = jumpKernel (fun _ => lam z) Λ s.2 := by
  obtain ⟨h1, h2⟩ := min_add_tsub_and_tsub_add_one_sub_max (p := lam z / Λ)
    (rate_div_le_one hΛ s.1)
  rw [min_comm, max_comm] at *
  rw [ssaTick, Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd,
    Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd,
    Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd, jumpKernel]
  calc _ = (min (lam s.1 / Λ) (lam z / Λ) + (lam z / Λ - lam s.1 / Λ)) •
        Measure.dirac (s.2 + 1) +
        ((lam s.1 / Λ - lam z / Λ) + (1 - max (lam s.1 / Λ) (lam z / Λ))) •
          Measure.dirac s.2 := by
        rw [add_smul, add_smul]
        abel
    _ = _ := by rw [h1, h2]

/-- A coupled tick is a probability measure when `λ ≤ Λ` (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaTick_univ {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (z : ℕ) (s : ℕ × ℕ) :
    ssaTick lam Λ z s Set.univ = 1 := by
  have h := ssaTick_map_fst hΛ z s
  rw [← jumpKernel_univ hΛ s.1, ← h, Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ]

/-- `n` coupled ticks of one step with the tau-leaping rate frozen at `λ(z)` (Giles 2015, §8, p. 56,
l. 2412–2415), from the pair `s` of exact and tau-leaping states. -/
noncomputable def ssaTickPow (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (z : ℕ) : ℕ → ℕ × ℕ → Measure (ℕ × ℕ)
  | 0 => fun s => Measure.dirac s
  | n + 1 => fun s => (ssaTickPow lam Λ z n s).bind (ssaTick lam Λ z)

/-- Zero coupled ticks (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaTickPow_zero (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (z : ℕ) (s : ℕ × ℕ) :
    ssaTickPow lam Λ z 0 s = Measure.dirac s := rfl

/-- One more coupled tick (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaTickPow_succ (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (z n : ℕ) (s : ℕ × ℕ) :
    ssaTickPow lam Λ z (n + 1) s = (ssaTickPow lam Λ z n s).bind (ssaTick lam Λ z) := rfl

/-- After `n` coupled ticks the exact component has the law `J^n(x)` of the uniformised exact chain
(Giles 2015, §8, p. 56, l. 2412–2415: the exact SSA "updates the reaction rates after every single
reaction"). -/
lemma ssaTickPow_map_fst {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (z : ℕ) :
    ∀ n s, (ssaTickPow lam Λ z n s).map Prod.fst = jumpPow lam Λ n s.1
  | 0, s => by rw [ssaTickPow_zero, Measure.map_dirac' measurable_fst, jumpPow_zero]
  | n + 1, s => by
      rw [ssaTickPow_succ, map_bind_of_discrete _ _ measurable_fst, jumpPow_succ,
        ← ssaTickPow_map_fst hΛ z n s, bind_map_of_discrete]
      exact congrArg _ (funext fun t => ssaTick_map_fst hΛ z t)

/-- After `n` coupled ticks the tau-leaping component has the law `J^n(w)` of the jump chain with
the frozen rate `λ(z)` (Giles 2015, §8, p. 55, l. 2372–2374: tau-leaping approximates "the reaction
rate as being constant throughout the timestep"). -/
lemma ssaTickPow_map_snd {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (z : ℕ) :
    ∀ n s, (ssaTickPow lam Λ z n s).map Prod.snd = jumpPow (fun _ => lam z) Λ n s.2
  | 0, s => by rw [ssaTickPow_zero, Measure.map_dirac' measurable_snd, jumpPow_zero]
  | n + 1, s => by
      rw [ssaTickPow_succ, map_bind_of_discrete _ _ measurable_snd, jumpPow_succ,
        ← ssaTickPow_map_snd hΛ z n s, bind_map_of_discrete]
      exact congrArg _ (funext fun t => ssaTick_map_snd hΛ z t)

/-- A measure on pairs whose first marginal has mass one has mass one (used for the coupled laws
of Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma measure_univ_of_map_fst {μ : Measure (ℕ × ℕ)} {ν : Measure ℕ} (h : μ.map Prod.fst = ν)
    (hν : ν Set.univ = 1) : μ Set.univ = 1 := by
  rw [← hν, ← h, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]

/-- `n` coupled ticks form a probability measure for `λ ≤ Λ` (Giles 2015, §8, p. 56,
l. 2412–2415). -/
lemma ssaTickPow_univ {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (z n : ℕ) (s : ℕ × ℕ) :
    ssaTickPow lam Λ z n s Set.univ = 1 :=
  measure_univ_of_map_fst (ssaTickPow_map_fst hΛ z n s) (jumpPow_univ hΛ n s.1)

/-! ### One coupled step and the coupled chain -/

/-- **One time step of the tau-leaping path coupled with the exact SSA** (Giles 2015, §8, p. 56,
l. 2411–2415: Anderson and Higham "include an additional coupling at the finest level to the exact
Stochastic Simulation Algorithm developed by (Gillespie 1976) which updates the reaction rates
after every single reaction").  From the pair `s = (x, z)` of the exact state `x` and the
tau-leaping state `z`, a rate-`Λ` clock ticks `K ~ P(Λh)` times in the step of length `h`, and the
`K` ticks are coupled ticks (`ssaTick`) with the tau-leaping rate frozen at `λ(z)`. -/
noncomputable def ssaStep (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (s : ℕ × ℕ) : Measure (ℕ × ℕ) :=
  (poissonMeasure (Λ * h)).bind fun n => ssaTickPow lam Λ s.2 n s

/-- **The exact component of a coupled step is the exact chain** (Giles 2015, §8, p. 56,
l. 2413–2415): for `λ ≤ Λ`, the first marginal of `ssaStep` from `(x, z)` is
`exactLaw λ Λ h x`. -/
theorem ssaStep_map_fst {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (s : ℕ × ℕ) : (ssaStep lam Λ h s).map Prod.fst = exactLaw lam Λ h s.1 := by
  rw [ssaStep, map_bind_of_discrete _ _ measurable_fst, exactLaw]
  exact congrArg _ (funext fun n => ssaTickPow_map_fst hΛ s.2 n s)

/-- **The tau-leaping component of a coupled step is one tau-leaping step** (Giles 2015, §8, p. 55,
l. 2375: "`x_{n+1} = x_n + P(hλ(x_n))`"): for `λ ≤ Λ`, the second marginal of `ssaStep` from
`(x, z)` is `tauStep λ h z`: the `P(Λh)` ticks kept with probability `λ(z)/Λ` form a `P(hλ(z))`
variate, the content of Poisson thinning (`poisson_thinning`, a standalone statement; this proof
goes through `exactLaw_eq_of_bound` and `exactLaw_const` instead). -/
theorem ssaStep_map_snd {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (s : ℕ × ℕ) : (ssaStep lam Λ h s).map Prod.snd = tauStep lam h s.2 := by
  have e : (ssaStep lam Λ h s).map Prod.snd = exactLaw (fun _ => lam s.2) Λ h s.2 := by
    rw [ssaStep, map_bind_of_discrete _ _ measurable_snd, exactLaw]
    exact congrArg _ (funext fun n => ssaTickPow_map_snd hΛ s.2 n s)
  rw [e, exactLaw_eq_of_bound (Λ' := lam s.2) (fun _ => hΛ s.2) (fun _ => le_rfl),
    exactLaw_const, tauStep, mul_comm]

/-- A coupled step is a probability measure when `λ ≤ Λ` (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaStep_univ {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0) (s : ℕ × ℕ) :
    ssaStep lam Λ h s Set.univ = 1 :=
  measure_univ_of_map_fst (ssaStep_map_fst hΛ h s) (isProbabilityMeasure_exactLaw hΛ h s.1).1

/-- **The tau-leaping path coupled with the exact SSA** (Giles 2015, §8, p. 56, l. 2411–2415): the
joint law after `n` coupled steps of size `h` of the exact chain and the tau-leaping path, both
started at `x₀`. -/
noncomputable def ssaChain (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (x₀ : ℕ) : ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac (x₀, x₀)
  | n + 1 => (ssaChain lam Λ h x₀ n).bind (ssaStep lam Λ h)

/-- The coupled chain starts with both paths at `x₀` (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaChain_zero (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (x₀ : ℕ) :
    ssaChain lam Λ h x₀ 0 = Measure.dirac (x₀, x₀) := rfl

/-- One more coupled step (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaChain_succ (lam : ℕ → ℝ≥0) (Λ h : ℝ≥0) (x₀ n : ℕ) :
    ssaChain lam Λ h x₀ (n + 1) = (ssaChain lam Λ h x₀ n).bind (ssaStep lam Λ h) := rfl

/-- The exact component of the coupled chain after `n` steps is the exact chain at time `nh`
(Chapman–Kolmogorov, `exactLaw_add`; Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaChain_map_fst {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ n, (ssaChain lam Λ h x₀ n).map Prod.fst = exactLaw lam Λ (n * h) x₀
  | 0 => by
      rw [ssaChain_zero, Measure.map_dirac' measurable_fst, Nat.cast_zero, zero_mul,
        exactLaw_zero]
  | n + 1 => by
      rw [ssaChain_succ, map_bind_of_discrete _ _ measurable_fst, Nat.cast_succ, add_one_mul,
        exactLaw_add hΛ, ← ssaChain_map_fst hΛ h x₀ n, bind_map_of_discrete]
      exact congrArg _ (funext fun t => ssaStep_map_fst hΛ h t)

/-- The tau-leaping component of the coupled chain after `n` steps is the tau-leaping chain
(Giles 2015, §8, p. 55, l. 2375: "`x_{n+1} = x_n + P(hλ(x_n))`"). -/
lemma ssaChain_map_snd {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ n, (ssaChain lam Λ h x₀ n).map Prod.snd = tauChain lam h x₀ n
  | 0 => by rw [ssaChain_zero, Measure.map_dirac' measurable_snd, tauChain]
  | n + 1 => by
      rw [ssaChain_succ, map_bind_of_discrete _ _ measurable_snd, tauChain,
        ← ssaChain_map_snd hΛ h x₀ n, bind_map_of_discrete]
      exact congrArg _ (funext fun t => ssaStep_map_snd hΛ h t)

/-- The coupled chain is a probability measure when `λ ≤ Λ` (Giles 2015, §8, p. 56,
l. 2412–2415). -/
lemma isProbabilityMeasure_ssaChain {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (x₀ n : ℕ) : IsProbabilityMeasure (ssaChain lam Λ h x₀ n) :=
  ⟨measure_univ_of_map_fst (ssaChain_map_fst hΛ h x₀ n)
    (isProbabilityMeasure_exactLaw hΛ _ x₀).1⟩

/-- **The marginals of the coupled chain** (Giles 2015, §8, p. 56, l. 2411–2415: the coupling of
the finest tau-leaping level "to the exact Stochastic Simulation Algorithm developed by
(Gillespie 1976) which updates the reaction rates after every single reaction").  For `λ ≤ Λ`,
`N ≥ 1` steps of size `T/N` from `x₀`: the coupled chain is a probability measure, its exact
component has the law `exactLaw λ Λ T x₀` of the exact chain at time `T`, and its tau-leaping
component has the law `tauChain λ (T/N) x₀ N` of `N` tau-leaping steps. -/
theorem ssaChain_marginals {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (ssaChain lam Λ (T / N) x₀ N) ∧
      (ssaChain lam Λ (T / N) x₀ N).map Prod.fst = exactLaw lam Λ T x₀ ∧
      (ssaChain lam Λ (T / N) x₀ N).map Prod.snd = tauChain lam (T / N) x₀ N := by
  have hN0 : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨isProbabilityMeasure_ssaChain hΛ _ x₀ N, ?_, ssaChain_map_snd hΛ _ x₀ N⟩
  rw [ssaChain_map_fst hΛ, mul_div_cancel₀ T hN0]

/-! ### The coupling error -/

/-- `∫ f d(ssaTick λ Λ z s)` is the weighted sum of `f` at the four outcomes of the tick
(Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma integral_ssaTick (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (z : ℕ) (s : ℕ × ℕ) (f : ℕ × ℕ → ℝ) :
    ∫ t, f t ∂(ssaTick lam Λ z s) =
      ((min (lam s.1 / Λ) (lam z / Λ) : ℝ≥0) : ℝ) * f (s.1 + 1, s.2 + 1) +
        ((lam s.1 / Λ - lam z / Λ : ℝ≥0) : ℝ) * f (s.1 + 1, s.2) +
        ((lam z / Λ - lam s.1 / Λ : ℝ≥0) : ℝ) * f (s.1, s.2 + 1) +
        ((1 - max (lam s.1 / Λ) (lam z / Λ) : ℝ≥0) : ℝ) * f s := by
  have hδ : ∀ (c : ℝ≥0) (t : ℕ × ℕ), Integrable f (c • Measure.dirac t) :=
    fun c t => Integrable.smul_measure_nnreal (integrable_dirac enorm_lt_top)
  rw [ssaTick, integral_add_measure (((hδ _ _).add_measure (hδ _ _)).add_measure (hδ _ _))
      (hδ _ _), integral_add_measure ((hδ _ _).add_measure (hδ _ _)) (hδ _ _),
    integral_add_measure (hδ _ _) (hδ _ _), integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_dirac, integral_dirac, integral_dirac, integral_dirac, NNReal.smul_def,
    NNReal.smul_def, NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul]

/-- The indicator of the disagreement set `{(x, w) : x ≠ w}` of the coupled pair is bounded by one
(Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma abs_indicator_ne_le (t : ℕ × ℕ) :
    |Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) t| ≤ 1 := by
  by_cases ht : t ∈ {s : ℕ × ℕ | s.1 ≠ s.2} <;> simp [ht]

/-- **A coupled step from agreeing states disagrees with probability at most `(Λh)²`** (Giles 2015,
§8, p. 56, l. 2412–2415).  If the exact and the tau-leaping state agree at the start of the step,
the first tick sees the same rate `λ(z)` on both paths, so they can only separate at a second
tick, and `P(P(Λh) ≥ 2) ≤ (Λh)²`. -/
lemma ssaStep_disagree_le_of_eq {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (z : ℕ) :
    ∫ t, Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) t ∂(ssaStep lam Λ h (z, z)) ≤
      ((Λ : ℝ) * h) ^ 2 := by
  set g : ℕ × ℕ → ℝ := Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} 1 with hg_def
  have hP : ∀ n t, IsProbabilityMeasure (ssaTickPow lam Λ z n t) :=
    fun n t => ⟨ssaTickPow_univ hΛ z n t⟩
  set u : ℕ → ℝ := fun n => ∫ t, g t ∂(ssaTickPow lam Λ z n (z, z)) with hu_def
  have hu : ∀ n, |u n| ≤ 1 := fun n => by
    have := hP n (z, z)
    exact abs_integral_le_of_abs_le_prob abs_indicator_ne_le
  have hu0 : u 0 = 0 := by
    show ∫ t, g t ∂(ssaTickPow lam Λ z 0 (z, z)) = 0
    rw [ssaTickPow_zero, integral_dirac, hg_def]
    simp
  have hu1 : u 1 = 0 := by
    show ∫ t, g t ∂(ssaTickPow lam Λ z (0 + 1) (z, z)) = 0
    rw [ssaTickPow_succ, ssaTickPow_zero, Measure.dirac_bind Measurable.of_discrete,
      integral_ssaTick, tsub_self, hg_def]
    simp
  have hE : ∫ t, g t ∂(ssaStep lam Λ h (z, z)) = ∫ n, u n ∂(poissonMeasure (Λ * h)) :=
    integral_bind_of_abs_le _ (fun n => hP n (z, z)) abs_indicator_ne_le
  obtain ⟨ρ, hρ, e⟩ := poisson_integral_split (Λ * h) hu
  rw [hE, e, hu0, hu1, mul_zero, mul_zero, zero_add, zero_add]
  have h2 := one_sub_exp_neg_sub_mul_le_sq ((Λ * h : ℝ≥0) : ℝ) (NNReal.coe_nonneg _)
  rw [NNReal.coe_mul] at h2 hρ
  linarith [le_abs_self ρ]

/-- One coupled step adds at most `(Λh)²` to the probability of disagreement (Giles 2015, §8, p. 56,
l. 2412–2415): `∫ 1_{x' ≠ z'} d(ssaStep s) ≤ (Λh)² + 1_{x ≠ z}`. -/
lemma ssaStep_disagree_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (s : ℕ × ℕ) :
    ∫ t, Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) t ∂(ssaStep lam Λ h s) ≤
      ((Λ : ℝ) * h) ^ 2 + Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) s := by
  obtain ⟨x, z⟩ := s
  by_cases hxz : x = z
  · subst hxz
    have h1 := ssaStep_disagree_le_of_eq hΛ h x
    have h0 : Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) (x, x) = 0 :=
      Set.indicator_of_notMem (s := {s : ℕ × ℕ | s.1 ≠ s.2}) (a := (x, x))
        (fun hm => hm rfl) _
    rw [h0, add_zero]
    exact h1
  · have hP : IsProbabilityMeasure (ssaStep lam Λ h (x, z)) := ⟨ssaStep_univ hΛ h (x, z)⟩
    have h1 : ∫ t, Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) t
        ∂(ssaStep lam Λ h (x, z)) ≤ 1 := (le_abs_self _).trans
      (abs_integral_le_of_abs_le_prob abs_indicator_ne_le)
    have h2 : Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) (x, z) = 1 := by
      simp [hxz]
    rw [h2]
    nlinarith [sq_nonneg ((Λ : ℝ) * h)]

/-- **The coupled paths disagree with probability at most `n(Λh)²` after `n` steps** (Giles 2015,
§8, p. 56, l. 2412–2415). -/
lemma ssaChain_disagree_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ n : ℕ, ∫ t, Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) t
      ∂(ssaChain lam Λ h x₀ n) ≤ n * ((Λ : ℝ) * h) ^ 2
  | 0 => by
      rw [ssaChain_zero, integral_dirac, Nat.cast_zero, zero_mul]
      simp
  | n + 1 => by
      have hP := isProbabilityMeasure_ssaChain hΛ h x₀ n
      have ih := ssaChain_disagree_le hΛ h x₀ n
      rw [ssaChain_succ, integral_bind_of_abs_le _ (fun t => ⟨ssaStep_univ hΛ h t⟩)
        abs_indicator_ne_le]
      have hint : Integrable (Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ))
          (ssaChain lam Λ h x₀ n) := integrable_of_abs_le_discrete abs_indicator_ne_le
      have hint2 : Integrable (fun t => ∫ t', Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2}
          (1 : ℕ × ℕ → ℝ) t' ∂(ssaStep lam Λ h t)) (ssaChain lam Λ h x₀ n) :=
        integrable_of_abs_le_discrete (M := 1) fun t => by
          have := (⟨ssaStep_univ hΛ h t⟩ : IsProbabilityMeasure (ssaStep lam Λ h t))
          exact abs_integral_le_of_abs_le_prob abs_indicator_ne_le
      calc ∫ t, ∫ t', Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) t'
            ∂(ssaStep lam Λ h t) ∂(ssaChain lam Λ h x₀ n)
          ≤ ∫ t, (((Λ : ℝ) * h) ^ 2 + Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2}
              (1 : ℕ × ℕ → ℝ) t) ∂(ssaChain lam Λ h x₀ n) :=
            integral_mono hint2 ((integrable_const _).add hint)
              fun t => ssaStep_disagree_le hΛ h t
        _ = ((Λ : ℝ) * h) ^ 2 + ∫ t, Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2}
              (1 : ℕ × ℕ → ℝ) t ∂(ssaChain lam Λ h x₀ n) := by
            rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul]
        _ ≤ ((n + 1 : ℕ) : ℝ) * ((Λ : ℝ) * h) ^ 2 := by
            push_cast
            linarith

/-- **The coupled exact and tau-leaping paths agree at time `T` up to probability `Λ²T h`**
(Giles 2015, §8, p. 56, l. 2412–2415: Anderson and Higham "include an additional coupling at the
finest level to the exact Stochastic Simulation Algorithm"; here the uniformisation coupling).  For
`λ ≤ Λ` and `N ≥ 1` coupled steps of size `h = T/N` from `x₀`, `P(X_T ≠ Z_N) ≤ Λ²T²/N = Λ²T h`: per
step, paths that agree at its start separate only at a second clock tick (probability `≤ (Λh)²`). -/
theorem ssaChain_ne_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {N : ℕ} (hN : 0 < N) :
    (ssaChain lam Λ (T / N) x₀ N).real {s | s.1 ≠ s.2} ≤ (Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 / N := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := ssaChain_disagree_le hΛ (T / N) x₀ N
  rw [integral_indicator_one MeasurableSet.of_discrete] at h
  refine h.trans (le_of_eq ?_)
  rw [NNReal.coe_div, NNReal.coe_natCast]
  field_simp

/-- **The squared payoff difference of the coupled paths is `O(h)`**
(Giles 2015, §8, p. 56, l. 2412–2415: "an additional coupling at the finest level to the exact
Stochastic Simulation Algorithm").  For `λ ≤ Λ`, a payoff `|Φ| ≤ M` and `N ≥ 1` coupled steps of
size `h = T/N` from `x₀`, `Φ(X_T) − Φ(Z_N)` is square integrable and
`E[(Φ(X_T) − Φ(Z_N))²] ≤ 4M²Λ²T²/N = 4M² Λ²T h` (`(Φ(x) − Φ(z))² ≤ 4M² 1_{x ≠ z}` and
`ssaChain_ne_le`). -/
theorem ssaChain_sq_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) {N : ℕ} (hN : 0 < N) :
    MemLp (fun s : ℕ × ℕ => Φ s.1 - Φ s.2) 2 (ssaChain lam Λ (T / N) x₀ N) ∧
      ∫ s, (Φ s.1 - Φ s.2) ^ 2 ∂(ssaChain lam Λ (T / N) x₀ N) ≤
        4 * M ^ 2 * ((Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 / N) := by
  have hP := isProbabilityMeasure_ssaChain hΛ (T / N) x₀ N
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΦ 0)
  have hb : ∀ s : ℕ × ℕ, |Φ s.1 - Φ s.2| ≤ 2 * M := fun s =>
    (abs_sub _ _).trans (by linarith [hΦ s.1, hΦ s.2])
  refine ⟨MemLp.of_bound Measurable.of_discrete.aestronglyMeasurable (2 * M)
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hb s), ?_⟩
  have hpt : ∀ s : ℕ × ℕ, (Φ s.1 - Φ s.2) ^ 2 ≤
      4 * M ^ 2 * Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) s := fun s => by
    by_cases hs : s.1 = s.2
    · have : s ∉ {s : ℕ × ℕ | s.1 ≠ s.2} := fun h => h hs
      rw [Set.indicator_of_notMem this, hs, sub_self]
      simp
    · have : s ∈ {s : ℕ × ℕ | s.1 ≠ s.2} := hs
      rw [Set.indicator_of_mem this, Pi.one_apply, mul_one, ← sq_abs]
      have := hb s
      nlinarith [abs_nonneg (Φ s.1 - Φ s.2)]
  have hsq : Integrable (fun s : ℕ × ℕ => (Φ s.1 - Φ s.2) ^ 2) (ssaChain lam Λ (T / N) x₀ N) :=
    integrable_of_abs_le_discrete (M := (2 * M) ^ 2) fun s => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb s) 2
  have hint : Integrable (Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ))
      (ssaChain lam Λ (T / N) x₀ N) := integrable_of_abs_le_discrete abs_indicator_ne_le
  have h := ssaChain_ne_le hΛ T x₀ hN
  rw [← integral_indicator_one MeasurableSet.of_discrete] at h
  calc ∫ s, (Φ s.1 - Φ s.2) ^ 2 ∂(ssaChain lam Λ (T / N) x₀ N)
      ≤ ∫ s, 4 * M ^ 2 * Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) s
          ∂(ssaChain lam Λ (T / N) x₀ N) := integral_mono hsq (hint.const_mul _) hpt
    _ = 4 * M ^ 2 * ∫ s, Set.indicator {s : ℕ × ℕ | s.1 ≠ s.2} (1 : ℕ × ℕ → ℝ) s
          ∂(ssaChain lam Λ (T / N) x₀ N) := integral_const_mul _ _
    _ ≤ 4 * M ^ 2 * ((Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 / N) :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-! ### The mean distance of the coupled paths -/

/-- `∫⁻ f d(ssaTick λ Λ z s)` is the weighted sum of `f` at the four outcomes of the tick
(Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma lintegral_ssaTick (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (z : ℕ) (s : ℕ × ℕ) (f : ℕ × ℕ → ℝ≥0∞) :
    ∫⁻ t, f t ∂(ssaTick lam Λ z s) =
      ((min (lam s.1 / Λ) (lam z / Λ) : ℝ≥0) : ℝ≥0∞) * f (s.1 + 1, s.2 + 1) +
        ((lam s.1 / Λ - lam z / Λ : ℝ≥0) : ℝ≥0∞) * f (s.1 + 1, s.2) +
        ((lam z / Λ - lam s.1 / Λ : ℝ≥0) : ℝ≥0∞) * f (s.1, s.2 + 1) +
        ((1 - max (lam s.1 / Λ) (lam z / Λ) : ℝ≥0) : ℝ≥0∞) * f s := by
  rw [ssaTick, lintegral_add_measure, lintegral_add_measure, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac, lintegral_dirac, lintegral_dirac, lintegral_dirac,
    ENNReal.smul_def, ENNReal.smul_def, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- A function at most `B` at the four outcomes of a coupled tick integrates to at most `B`
(Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma lintegral_ssaTick_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (z : ℕ) (s : ℕ × ℕ)
    {f : ℕ × ℕ → ℝ≥0∞} {B : ℝ≥0∞} (h1 : f (s.1 + 1, s.2 + 1) ≤ B) (h2 : f (s.1 + 1, s.2) ≤ B)
    (h3 : f (s.1, s.2 + 1) ≤ B) (h4 : f s ≤ B) : ∫⁻ t, f t ∂(ssaTick lam Λ z s) ≤ B := by
  have hsum := lintegral_ssaTick lam Λ z s (fun _ => 1)
  simp only [lintegral_const, ssaTick_univ hΛ, mul_one] at hsum
  rw [lintegral_ssaTick]
  calc _ ≤ ((min (lam s.1 / Λ) (lam z / Λ) : ℝ≥0) : ℝ≥0∞) * B +
        ((lam s.1 / Λ - lam z / Λ : ℝ≥0) : ℝ≥0∞) * B +
        ((lam z / Λ - lam s.1 / Λ : ℝ≥0) : ℝ≥0∞) * B +
        ((1 - max (lam s.1 / Λ) (lam z / Λ) : ℝ≥0) : ℝ≥0∞) * B := by gcongr
    _ = B := by rw [← add_mul, ← add_mul, ← add_mul, ← hsum, one_mul]

/-- `ofReal |a| ≤ ofReal |b| + 1` from `|a| ≤ |b| + 1` (for the coupling of Giles 2015, §8, p. 56,
l. 2412–2415). -/
lemma ofReal_abs_le_add_one {a b : ℝ} (h : |a| ≤ |b| + 1) :
    ENNReal.ofReal |a| ≤ ENNReal.ofReal |b| + 1 := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (abs_nonneg _) zero_le_one]
  exact ENNReal.ofReal_le_ofReal h

/-- `n` coupled ticks change the distance `|x − w|` of the two paths by at most `n` on average
(Giles 2015, §8, p. 56, l. 2412–2415): `∫⁻ |x − w| d(ssaTickPow z n s) ≤ |s.1 − s.2| + n` (each tick
moves each path by at most one). -/
lemma lintegral_dist_ssaTickPow_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (z : ℕ) :
    ∀ n s, ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaTickPow lam Λ z n s) ≤
      ENNReal.ofReal |(s.1 : ℝ) - s.2| + n
  | 0, s => by
      rw [ssaTickPow_zero, lintegral_dirac, Nat.cast_zero, add_zero]
  | n + 1, s => by
      have hP : IsProbabilityMeasure (ssaTickPow lam Λ z n s) := ⟨ssaTickPow_univ hΛ z n s⟩
      have ih := lintegral_dist_ssaTickPow_le hΛ z n s
      rw [ssaTickPow_succ, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
      calc ∫⁻ t, ∫⁻ t', ENNReal.ofReal |(t'.1 : ℝ) - t'.2| ∂(ssaTick lam Λ z t)
            ∂(ssaTickPow lam Λ z n s)
          ≤ ∫⁻ t, (ENNReal.ofReal |(t.1 : ℝ) - t.2| + 1) ∂(ssaTickPow lam Λ z n s) := by
            refine lintegral_mono fun t => lintegral_ssaTick_le hΛ z t ?_ ?_ ?_ ?_
            · refine ofReal_abs_le_add_one ?_
              push_cast
              rw [add_sub_add_right_eq_sub]
              linarith
            · refine ofReal_abs_le_add_one ?_
              push_cast
              rw [add_sub_right_comm]
              exact (abs_add_le _ _).trans (by rw [abs_one])
            · refine ofReal_abs_le_add_one ?_
              push_cast
              rw [← sub_sub]
              exact (abs_sub _ _).trans (by rw [abs_one])
            · exact le_self_add
        _ = ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaTickPow lam Λ z n s) + 1 := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ ENNReal.ofReal |(s.1 : ℝ) - s.2| + n + 1 := by gcongr
        _ = ENNReal.ofReal |(s.1 : ℝ) - s.2| + ((n + 1 : ℕ) : ℝ≥0∞) := by
            rw [Nat.cast_succ, add_assoc]

/-- The coupled ticks form a Markov chain (Giles 2015, §8, p. 56, l. 2412–2415):
`ssaTickPow z (m + n) s = (ssaTickPow z m s).bind (ssaTickPow z n)`. -/
lemma ssaTickPow_add (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (z m : ℕ) :
    ∀ n s, ssaTickPow lam Λ z (m + n) s = (ssaTickPow lam Λ z m s).bind (ssaTickPow lam Λ z n)
  | 0, s => by
      rw [add_zero]
      exact Measure.bind_dirac.symm
  | n + 1, s => by
      rw [← add_assoc, ssaTickPow_succ, ssaTickPow_add lam Λ z m n s,
        Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
      rfl

/-- From agreeing states the paths stay together at the first tick, both seeing the rate `λ(z)`, so
after `n + 1` ticks their mean distance is at most `n` (Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma lintegral_dist_ssaTickPow_diag_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (z n : ℕ) :
    ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaTickPow lam Λ z (n + 1) (z, z)) ≤ n := by
  have hP : IsProbabilityMeasure (ssaTickPow lam Λ z 1 (z, z)) := ⟨ssaTickPow_univ hΛ z 1 (z, z)⟩
  have h1 : ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaTickPow lam Λ z 1 (z, z)) = 0 := by
    rw [ssaTickPow_succ, ssaTickPow_zero, Measure.dirac_bind Measurable.of_discrete,
      lintegral_ssaTick]
    simp
  rw [add_comm n 1, ssaTickPow_add, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable]
  calc ∫⁻ t, ∫⁻ t', ENNReal.ofReal |(t'.1 : ℝ) - t'.2| ∂(ssaTickPow lam Λ z n t)
        ∂(ssaTickPow lam Λ z 1 (z, z))
      ≤ ∫⁻ t, (ENNReal.ofReal |(t.1 : ℝ) - t.2| + n) ∂(ssaTickPow lam Λ z 1 (z, z)) :=
        lintegral_mono fun t => lintegral_dist_ssaTickPow_le hΛ z n t
    _ = n := by
        rw [lintegral_add_right _ measurable_const, h1, lintegral_const, measure_univ, mul_one,
          zero_add]

/-- `E[(P(r) − 1)⁺] ≤ r²` (Giles 2015, §8, p. 55, l. 2377: "`P(t)` represents a unit-rate Poisson
random variable"), from `(n − 1)⁺ + n ≤ n²` and the first two Poisson moments. -/
lemma lintegral_pred_poissonMeasure_le (r : ℝ≥0) :
    ∫⁻ n, ENNReal.ofReal ((n : ℝ) - 1) ∂(poissonMeasure r) ≤ ENNReal.ofReal ((r : ℝ) ^ 2) := by
  have h1 : ∫⁻ n, (ENNReal.ofReal ((n : ℝ) - 1) + ENNReal.ofReal (n : ℝ)) ∂(poissonMeasure r) ≤
      ∫⁻ n, ENNReal.ofReal ((n : ℝ) ^ 2) ∂(poissonMeasure r) := by
    refine lintegral_mono fun n => ?_
    rcases n with _ | m
    · simp
    · push_cast
      rw [add_sub_cancel_right, ← ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
  rw [lintegral_add_left Measurable.of_discrete, lintegral_id_poissonMeasure,
    lintegral_sq_poissonMeasure, ENNReal.ofReal_add (NNReal.coe_nonneg r) (sq_nonneg _),
    add_comm (ENNReal.ofReal (r : ℝ))] at h1
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h1

/-- One coupled step increases the mean distance of the paths by at most `Λh`
(Giles 2015, §8, p. 56, l. 2412–2415): `∫⁻ |x' − z'| d(ssaStep s) ≤ |x − z| + Λh`. -/
lemma lintegral_dist_ssaStep_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (s : ℕ × ℕ) :
    ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaStep lam Λ h s) ≤
      ENNReal.ofReal |(s.1 : ℝ) - s.2| + ENNReal.ofReal ((Λ : ℝ) * h) := by
  rw [ssaStep, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable]
  calc ∫⁻ n, ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaTickPow lam Λ s.2 n s)
        ∂(poissonMeasure (Λ * h))
      ≤ ∫⁻ n, (ENNReal.ofReal |(s.1 : ℝ) - s.2| + ENNReal.ofReal (n : ℝ))
          ∂(poissonMeasure (Λ * h)) := lintegral_mono fun n => by
        rw [ENNReal.ofReal_natCast]
        exact lintegral_dist_ssaTickPow_le hΛ s.2 n s
    _ = ENNReal.ofReal |(s.1 : ℝ) - s.2| + ENNReal.ofReal ((Λ : ℝ) * h) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_id_poissonMeasure, NNReal.coe_mul]

/-- From agreeing states one coupled step separates the paths by at most `(Λh)²` on average
(Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma lintegral_dist_ssaStep_diag_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (z : ℕ) :
    ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaStep lam Λ h (z, z)) ≤
      ENNReal.ofReal (((Λ : ℝ) * h) ^ 2) := by
  rw [ssaStep, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aemeasurable]
  have h1 : ∀ n : ℕ, ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaTickPow lam Λ z n (z, z)) ≤
      ENNReal.ofReal ((n : ℝ) - 1) := by
    intro n
    rcases n with _ | m
    · rw [ssaTickPow_zero, lintegral_dirac]
      simp
    · refine (lintegral_dist_ssaTickPow_diag_le hΛ z m).trans (le_of_eq ?_)
      rw [Nat.cast_succ, add_sub_cancel_right, ENNReal.ofReal_natCast]
  refine (lintegral_mono h1).trans ?_
  have h2 := lintegral_pred_poissonMeasure_le (Λ * h)
  rw [NNReal.coe_mul] at h2
  exact h2

/-- **The mean distance of the coupled paths after `n` steps**: `E|X_{nh} − Z_n| ≤ n(Λh)² + n²(Λh)³`
(Giles 2015, §8, p. 56, l. 2412–2415: "an additional coupling at the finest level to the exact
Stochastic Simulation Algorithm"). -/
lemma lintegral_dist_ssaChain_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (x₀ : ℕ) : ∀ n : ℕ, ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaChain lam Λ h x₀ n) ≤
      ENNReal.ofReal (n * ((Λ : ℝ) * h) ^ 2 + (n : ℝ) ^ 2 * ((Λ : ℝ) * h) ^ 3)
  | 0 => by
      rw [ssaChain_zero, lintegral_dirac]
      simp
  | n + 1 => by
      have hP := isProbabilityMeasure_ssaChain hΛ h x₀ n
      have ih := lintegral_dist_ssaChain_le hΛ h x₀ n
      set r : ℝ := (Λ : ℝ) * h with hr_def
      have hr : 0 ≤ r := by positivity
      set D : Set (ℕ × ℕ) := {s : ℕ × ℕ | s.1 ≠ s.2} with hD_def
      -- the probability of disagreement after `n` steps
      have hD : ssaChain lam Λ h x₀ n D ≤ ENNReal.ofReal (n * r ^ 2) := by
        have h1 := ssaChain_disagree_le hΛ h x₀ n
        rw [integral_indicator_one MeasurableSet.of_discrete] at h1
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ D)]
        exact ENNReal.ofReal_le_ofReal h1
      have hstep : ∀ t : ℕ × ℕ, ∫⁻ t', ENNReal.ofReal |(t'.1 : ℝ) - t'.2| ∂(ssaStep lam Λ h t) ≤
          ENNReal.ofReal |(t.1 : ℝ) - t.2| + ENNReal.ofReal r * D.indicator 1 t +
            ENNReal.ofReal (r ^ 2) := fun t => by
        by_cases ht : t.1 = t.2
        · obtain ⟨x, z⟩ := t
          simp only at ht
          subst ht
          refine (lintegral_dist_ssaStep_diag_le hΛ h x).trans ?_
          exact le_add_self
        · have hm : t ∈ D := ht
          rw [Set.indicator_of_mem hm, Pi.one_apply, mul_one]
          exact (lintegral_dist_ssaStep_le hΛ h t).trans le_self_add
      rw [ssaChain_succ, Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
      calc ∫⁻ t, ∫⁻ t', ENNReal.ofReal |(t'.1 : ℝ) - t'.2| ∂(ssaStep lam Λ h t)
            ∂(ssaChain lam Λ h x₀ n)
          ≤ ∫⁻ t, (ENNReal.ofReal |(t.1 : ℝ) - t.2| + ENNReal.ofReal r * D.indicator 1 t +
              ENNReal.ofReal (r ^ 2)) ∂(ssaChain lam Λ h x₀ n) := lintegral_mono hstep
        _ = ∫⁻ t, ENNReal.ofReal |(t.1 : ℝ) - t.2| ∂(ssaChain lam Λ h x₀ n) +
              ENNReal.ofReal r * ssaChain lam Λ h x₀ n D + ENNReal.ofReal (r ^ 2) := by
            rw [lintegral_add_right _ measurable_const, lintegral_add_left Measurable.of_discrete,
              lintegral_const_mul _ Measurable.of_discrete,
              lintegral_indicator_one MeasurableSet.of_discrete, lintegral_const, measure_univ,
              mul_one]
        _ ≤ ENNReal.ofReal (n * r ^ 2 + (n : ℝ) ^ 2 * r ^ 3) +
              ENNReal.ofReal r * ENNReal.ofReal (n * r ^ 2) + ENNReal.ofReal (r ^ 2) := by
            gcongr
        _ ≤ ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * r ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2 * r ^ 3) := by
            rw [← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            push_cast
            have hr3 : 0 ≤ r ^ 3 := by positivity
            have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            nlinarith [mul_nonneg hn hr3]

/-- **The coupled paths are `O(h)` apart: `P(X_T ≠ Z_N) ≤ E|X_T − Z_N| ≤ (Λ²T + Λ³T²) h`**
(Giles 2015, §8, p. 56, l. 2412–2415: "an additional coupling at the finest level to the exact
Stochastic Simulation Algorithm").  For `λ ≤ Λ` and `N ≥ 1` coupled steps of size `h = T/N` from
`x₀`, the distance `|X_T − Z_N|` of the exact and the tau-leaping state is integrable, bounds the
probability of disagreement, and has mean at most `(Λ²T² + Λ³T³)/N`.  The constant depends on `Λ`
and `T` only: per step the mean distance grows by at most `Λh` once the paths have separated and by
at most `(Λh)²` while they agree. -/
theorem ssaChain_abs_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {N : ℕ} (hN : 0 < N) :
    Integrable (fun s : ℕ × ℕ => |(s.1 : ℝ) - s.2|) (ssaChain lam Λ (T / N) x₀ N) ∧
      (ssaChain lam Λ (T / N) x₀ N).real {s | s.1 ≠ s.2} ≤
        ∫ s, |(s.1 : ℝ) - s.2| ∂(ssaChain lam Λ (T / N) x₀ N) ∧
      ∫ s, |(s.1 : ℝ) - s.2| ∂(ssaChain lam Λ (T / N) x₀ N) ≤
        ((Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 + (Λ : ℝ) ^ 3 * (T : ℝ) ^ 3) / N := by
  have hP := isProbabilityMeasure_ssaChain hΛ (T / N) x₀ N
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hlin := lintegral_dist_ssaChain_le hΛ (T / N) x₀ N
  have e : (N : ℝ) * ((Λ : ℝ) * ((T / N : ℝ≥0) : ℝ)) ^ 2 +
      (N : ℝ) ^ 2 * ((Λ : ℝ) * ((T / N : ℝ≥0) : ℝ)) ^ 3 =
      ((Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 + (Λ : ℝ) ^ 3 * (T : ℝ) ^ 3) / N := by
    rw [NNReal.coe_div, NNReal.coe_natCast]
    field_simp
  rw [e] at hlin
  have hnn : 0 ≤ᵐ[ssaChain lam Λ (T / N) x₀ N] fun s : ℕ × ℕ => |(s.1 : ℝ) - s.2| :=
    ae_of_all _ fun s => abs_nonneg _
  have hint : Integrable (fun s : ℕ × ℕ => |(s.1 : ℝ) - s.2|) (ssaChain lam Λ (T / N) x₀ N) :=
    ⟨Measurable.of_discrete.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2
      (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_, ?_⟩
  · rw [← integral_indicator_one MeasurableSet.of_discrete]
    refine integral_mono (integrable_of_abs_le_discrete abs_indicator_ne_le) hint fun s => ?_
    by_cases hs : s.1 = s.2
    · have : s ∉ {s : ℕ × ℕ | s.1 ≠ s.2} := fun h => h hs
      rw [Set.indicator_of_notMem this]
      exact abs_nonneg _
    · have : s ∈ {s : ℕ × ℕ | s.1 ≠ s.2} := hs
      rw [Set.indicator_of_mem this, Pi.one_apply]
      exact one_le_abs_natCast_sub hs
  · rw [integral_eq_lintegral_of_nonneg_ae hnn Measurable.of_discrete.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

/-! ### The unbiased multilevel estimator -/

/-- **The law of a level-`ℓ` sample of the unbiased estimator** (Giles 2015, §8, p. 56,
l. 2411–2417).  The tau-leaping levels `ℓ ≤ L` are those of `tauLeaping_mlmc_exact`
(`tauLevelLaw`: `2^ℓ` steps of size `T 2^{−ℓ}`, Poisson-coupled with the coarse path); the extra
finest level `L + 1` couples the `2^L` tau-leaping steps of level `L` with the exact SSA
(`ssaChain` with steps of size `T 2^{−L}`).  (Indices `ℓ > L + 1` are not used.) -/
noncomputable def ssaLevelLaw (lam : ℕ → ℝ≥0) (Λ T : ℝ≥0) (x₀ L ℓ : ℕ) : Measure (ℕ × ℕ) :=
  if ℓ ≤ L then tauLevelLaw lam T x₀ ℓ else ssaChain lam Λ (T / 2 ^ L) x₀ (2 ^ L)

/-- **One input of the unbiased estimator** (Giles 2015, §8, p. 56, l. 2411–2415): the samples of
all levels `ℓ ≤ L + 1`, independent across levels (a level-`ℓ` sample uses coordinate `ℓ`). -/
noncomputable def ssaInputLaw (lam : ℕ → ℝ≥0) (Λ T : ℝ≥0) (x₀ L : ℕ) : Measure (ℕ → ℕ × ℕ) :=
  Measure.infinitePi (ssaLevelLaw lam Λ T x₀ L)

/-- **The level corrections of the unbiased estimator** (Giles 2015, §8, p. 56, l. 2411–2417, and
§2.1, (2.4)): on the tau-leaping levels `ℓ ≤ L` the Poisson-coupled corrections
`P^f_ℓ − P^c_{ℓ−1}` of `tauLeaping_mlmc_exact`, and on the finest level `L + 1` the correction
`Φ(X_T) − Φ(Z_{2^L})` of the exact SSA path over the coupled tau-leaping path of level `L`. -/
noncomputable def ssaCorrection (Φ : ℕ → ℝ) (L ℓ : ℕ) : (ℕ → ℕ × ℕ) → ℝ :=
  if ℓ ≤ L then fineCoarseDiff (tauFine Φ) (tauCoarse Φ) ℓ else fun y => Φ (y ℓ).1 - Φ (y ℓ).2

/-- The level laws of the unbiased estimator are probability measures (Giles 2015, §8, p. 56,
l. 2411–2415). -/
lemma isProbabilityMeasure_ssaLevelLaw {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) (x₀ L ℓ : ℕ) : IsProbabilityMeasure (ssaLevelLaw lam Λ T x₀ L ℓ) := by
  rw [ssaLevelLaw]
  split_ifs
  · exact isProbabilityMeasure_tauLevelLaw lam T x₀ ℓ
  · exact isProbabilityMeasure_ssaChain hΛ _ x₀ _

/-- The input law of the unbiased estimator is a probability measure (Giles 2015, §8, p. 56,
l. 2411–2415). -/
lemma isProbabilityMeasure_ssaInputLaw {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) (x₀ L : ℕ) : IsProbabilityMeasure (ssaInputLaw lam Λ T x₀ L) := by
  have := isProbabilityMeasure_ssaLevelLaw hΛ T x₀ L
  unfold ssaInputLaw
  infer_instance

/-- A function of coordinate `ℓ` of an input integrates against the level-`ℓ` law (Giles 2015, §8,
p. 56, l. 2411–2415). -/
lemma integral_ssaInput {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L ℓ : ℕ) (F : ℕ × ℕ → ℝ) :
    ∫ y, F (y ℓ) ∂(ssaInputLaw lam Λ T x₀ L) = ∫ q, F q ∂(ssaLevelLaw lam Λ T x₀ L ℓ) := by
  have := isProbabilityMeasure_ssaLevelLaw hΛ T x₀ L
  exact integral_comp_of_measurePreserving (measurePreserving_eval_infinitePi _ ℓ)
    Measurable.of_discrete.aestronglyMeasurable

/-- The fine payoff of tau-leaping level `ℓ` has the mean of `2^ℓ` steps of size `T 2^{−ℓ}`
(Giles 2015, §8, p. 55, l. 2375–2378). -/
lemma integral_fst_tauLevelLaw (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ : ℕ) (Φ : ℕ → ℝ) (ℓ : ℕ) :
    ∫ q, Φ q.1 ∂(tauLevelLaw lam T x₀ ℓ) = ∫ x, Φ x ∂(tauChain lam (T / 2 ^ ℓ) x₀ (2 ^ ℓ)) :=
  (integral_comp_of_measurePreserving (measurePreserving_tauInput lam T x₀ ℓ)
    (Measurable.of_discrete (f := fun q : ℕ × ℕ => Φ q.1)).aestronglyMeasurable).symm.trans
    (integral_tauFine lam T x₀ Φ ℓ)

/-- The coarse payoff of tau-leaping level `ℓ + 1` has the mean of `2^ℓ` steps of size `T 2^{−ℓ}`,
(Giles 2015, §8, p. 55, l. 2378–2384; identity (2.4), §2.1, p. 8). -/
lemma integral_snd_tauLevelLaw (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ : ℕ) (Φ : ℕ → ℝ) (ℓ : ℕ) :
    ∫ q, Φ q.2 ∂(tauLevelLaw lam T x₀ (ℓ + 1)) =
      ∫ x, Φ x ∂(tauChain lam (T / 2 ^ ℓ) x₀ (2 ^ ℓ)) :=
  (integral_comp_of_measurePreserving (measurePreserving_tauInput lam T x₀ (ℓ + 1))
    (Measurable.of_discrete (f := fun q : ℕ × ℕ => Φ q.2)).aestronglyMeasurable).symm.trans
    (integral_tauCoarse lam T x₀ Φ ℓ)

/-- The exact level: `2^L` coupled steps of size `T 2^{−L}` reach the time `T`, and the coupled
chain has the marginals `exactLaw λ Λ T x₀` and `tauChain λ (T 2^{−L}) x₀ 2^L`
(Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma ssaChain_pow_marginals {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L : ℕ) :
    IsProbabilityMeasure (ssaChain lam Λ (T / 2 ^ L) x₀ (2 ^ L)) ∧
      (ssaChain lam Λ (T / 2 ^ L) x₀ (2 ^ L)).map Prod.fst = exactLaw lam Λ T x₀ ∧
      (ssaChain lam Λ (T / 2 ^ L) x₀ (2 ^ L)).map Prod.snd =
        tauChain lam (T / 2 ^ L) x₀ (2 ^ L) := by
  have e : ((2 ^ L : ℕ) : ℝ≥0) = 2 ^ L := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have h := ssaChain_marginals hΛ T x₀ (N := 2 ^ L) (by positivity)
  rw [e] at h
  exact h

/-- The mean of the exact-level correction is `E[Φ(X_T)] − E[Φ(Z_{2^L})]`
(Giles 2015, §8, p. 56, l. 2412–2415). -/
lemma integral_ssaChain_pow_sub {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L : ℕ) {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) :
    ∫ q, (Φ q.1 - Φ q.2) ∂(ssaChain lam Λ (T / 2 ^ L) x₀ (2 ^ L)) =
      ∫ x, Φ x ∂(exactLaw lam Λ T x₀) - ∫ x, Φ x ∂(tauChain lam (T / 2 ^ L) x₀ (2 ^ L)) := by
  obtain ⟨hP, h1, h2⟩ := ssaChain_pow_marginals hΛ T x₀ L
  have hb1 : ∀ q : ℕ × ℕ, |Φ q.1| ≤ M := fun q => hΦ q.1
  have hb2 : ∀ q : ℕ × ℕ, |Φ q.2| ≤ M := fun q => hΦ q.2
  rw [integral_sub (integrable_of_abs_le_discrete hb1) (integrable_of_abs_le_discrete hb2),
    ← h1, ← h2, integral_map measurable_fst.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable Measurable.of_discrete.aestronglyMeasurable]

/-- The corrections are bounded by `2M` for `|Φ| ≤ M` (Giles 2015, §8, p. 56, l. 2411–2415). -/
lemma abs_ssaCorrection_le {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) (L ℓ : ℕ)
    (y : ℕ → ℕ × ℕ) : |ssaCorrection Φ L ℓ y| ≤ 2 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΦ 0)
  have hd : ∀ a b : ℕ, |Φ a - Φ b| ≤ 2 * M := fun a b =>
    (abs_sub _ _).trans (by linarith [hΦ a, hΦ b])
  rw [ssaCorrection]
  split_ifs
  · cases ℓ with
    | zero => exact (hΦ _).trans (by linarith)
    | succ k => exact hd _ _
  · exact hd _ _

/-- The corrections are measurable (Giles 2015, §8, p. 56, l. 2411–2415). -/
lemma measurable_ssaCorrection (Φ : ℕ → ℝ) (L ℓ : ℕ) : Measurable (ssaCorrection Φ L ℓ) := by
  rw [ssaCorrection]
  split_ifs
  · exact measurable_fineCoarseDiff (measurable_tauFine Φ) (measurable_tauCoarse Φ) ℓ
  · exact (Measurable.of_discrete (f := fun q : ℕ × ℕ => Φ q.1 - Φ q.2)).comp
      (measurable_pi_apply ℓ)

/-- The corrections are square integrable for `|Φ| ≤ M` (Giles 2015, §8, p. 56, l. 2411–2415). -/
lemma memLp_ssaCorrection {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L : ℕ) {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) (ℓ : ℕ) :
    MemLp (ssaCorrection Φ L ℓ) 2 (ssaInputLaw lam Λ T x₀ L) := by
  have := isProbabilityMeasure_ssaInputLaw hΛ T x₀ L
  exact MemLp.of_bound (measurable_ssaCorrection Φ L ℓ).aestronglyMeasurable (2 * M)
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact abs_ssaCorrection_le hΦ L ℓ y)

/-- **The means of the corrections telescope to the exact mean** (Giles 2015, §8, p. 56,
l. 2415: "their overall multilevel estimator is unbiased"): for every `L`,
`∑_{ℓ ≤ L + 1} E[Δ_ℓ] = E[Φ(X_T)]`. -/
lemma sum_integral_ssaCorrection {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ L : ℕ) {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) :
    ∑ ℓ ∈ range (L + 2), ∫ y, ssaCorrection Φ L ℓ y ∂(ssaInputLaw lam Λ T x₀ L) =
      ∫ x, Φ x ∂(exactLaw lam Λ T x₀) := by
  set a : ℕ → ℝ := fun ℓ => ∫ x, Φ x ∂(tauChain lam (T / 2 ^ ℓ) x₀ (2 ^ ℓ)) with ha_def
  have hlow : ∀ ℓ, ℓ ≤ L → ssaLevelLaw lam Λ T x₀ L ℓ = tauLevelLaw lam T x₀ ℓ :=
    fun ℓ hℓ => by rw [ssaLevelLaw, if_pos hℓ]
  have hb1 : ∀ (ν : Measure (ℕ × ℕ)) [IsFiniteMeasure ν], Integrable (fun q : ℕ × ℕ => Φ q.1) ν :=
    fun ν _ => integrable_of_abs_le_discrete (fun q => hΦ q.1)
  have hb2 : ∀ (ν : Measure (ℕ × ℕ)) [IsFiniteMeasure ν], Integrable (fun q : ℕ × ℕ => Φ q.2) ν :=
    fun ν _ => integrable_of_abs_le_discrete (fun q => hΦ q.2)
  -- the tau-leaping levels telescope to `a k`
  have htau : ∀ k, k ≤ L →
      ∑ ℓ ∈ range (k + 1), ∫ y, ssaCorrection Φ L ℓ y ∂(ssaInputLaw lam Λ T x₀ L) = a k := by
    intro k
    induction k with
    | zero =>
      intro h0
      rw [Finset.sum_range_one, ssaCorrection, if_pos h0]
      show ∫ y, Φ (y 0).1 ∂(ssaInputLaw lam Λ T x₀ L) = a 0
      rw [integral_ssaInput hΛ T x₀ L 0 (fun q => Φ q.1), hlow 0 h0, integral_fst_tauLevelLaw]
    | succ k ih =>
      intro hk
      have hP := isProbabilityMeasure_tauLevelLaw lam T x₀ (k + 1)
      rw [Finset.sum_range_succ, ih (by omega), ssaCorrection, if_pos hk]
      show a k + ∫ y, (Φ (y (k + 1)).1 - Φ (y (k + 1)).2) ∂(ssaInputLaw lam Λ T x₀ L) = a (k + 1)
      rw [integral_ssaInput hΛ T x₀ L (k + 1) (fun q => Φ q.1 - Φ q.2), hlow (k + 1) hk,
        integral_sub (hb1 _) (hb2 _), integral_fst_tauLevelLaw, integral_snd_tauLevelLaw]
      ring
  rw [Finset.sum_range_succ, htau L le_rfl, ssaCorrection, if_neg (by omega),
    integral_ssaInput hΛ T x₀ L (L + 1) (fun q => Φ q.1 - Φ q.2), ssaLevelLaw, if_neg (by omega),
    integral_ssaChain_pow_sub hΛ T x₀ L hΦ]
  ring

/-- **(G8-13) The multilevel estimator with the exact SSA level is unbiased, for every number of
levels** (Giles 2015, §8, p. 56, l. 2411–2416: Anderson and Higham "include an additional coupling
at the finest level to the exact Stochastic Simulation Algorithm developed by (Gillespie 1976)
which updates the reaction rates after every single reaction.  Hence, their overall multilevel
estimator is unbiased, unlike the estimators discussed earlier for SDEs").  Let `0 ≤ λ ≤ Λ`,
`|Φ| ≤ M`, and let the estimator have the tau-leaping levels `ℓ ≤ L` of `tauLeaping_mlmc_exact`
(level `ℓ`: `2^ℓ` steps of size `T 2^{−ℓ}`, Poisson-coupled corrections) and the exact level
`L + 1` (the exact SSA coupled with the `2^L` tau-leaping steps of level `L`, `ssaChain`), with
`N_ℓ ≥ 1` independent samples on level `ℓ` (the coordinates of the product measure, each of law
`ssaInputLaw`).  Then the sampling measure is a probability measure, the estimator
`Y = ∑_{ℓ=0}^{L+1} N_ℓ⁻¹ ∑_{n<N_ℓ} Δ_ℓ(ω^{(ℓ,n)})` is integrable, and `E[Y] = E[Φ(X_T)]` exactly,
where `X` is the exact chain (`exactLaw`).  Deviations: one reaction, bounded propensity, bounded
payoff; the exact chain is simulated by uniformisation, not by Gillespie's exponential waiting
times (`exactLaw_unique`: it is the same chain). -/
theorem ssa_mlmc_unbiased {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) (L : ℕ) {N : ℕ → ℕ} (hN : ∀ ℓ, 0 < N ℓ) :
    IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) ∧
      Integrable (fun x => ∑ ℓ ∈ range (L + 2),
          blockMean (ssaCorrection Φ L) (fun p x => x p) ℓ (N ℓ) x)
        (Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) ∧
      ∫ x, ∑ ℓ ∈ range (L + 2), blockMean (ssaCorrection Φ L) (fun p x => x p) ℓ (N ℓ) x
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) =
        ∫ y, Φ y ∂(exactLaw lam Λ T x₀) := by
  have hν := isProbabilityMeasure_ssaInputLaw hΛ T x₀ L
  obtain ⟨hμ, -, hω⟩ := exists_iid_inputs (ssaInputLaw lam Λ T x₀ L)
  have hc := memLp_ssaCorrection hΛ T x₀ L hΦ
  have hY : ∀ ℓ, Integrable (blockMean (ssaCorrection Φ L) (fun p x => x p) ℓ (N ℓ))
      (Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) :=
    fun ℓ => (memLp_blockMean hω hc ℓ (N ℓ)).integrable one_le_two
  refine ⟨hμ, integrable_finsetSum _ fun ℓ _ => hY ℓ, ?_⟩
  rw [integral_finsetSum _ fun ℓ _ => hY ℓ, ← sum_integral_ssaCorrection hΛ T x₀ L hΦ]
  exact Finset.sum_congr rfl fun ℓ _ =>
    integral_blockMean hω (fun k => (hc k).integrable one_le_two) ℓ (hN ℓ)

/-- **The exact level has an `O(h_L)` correction variance** (Giles 2015, §8, p. 56, l. 2412–2415:
"an additional coupling at the finest level to the exact Stochastic Simulation Algorithm").  For
`0 ≤ λ ≤ Λ` and `|Φ| ≤ M`, the input law is a probability measure, and the correction
`Φ(X_T) − Φ(Z_{2^L})` of the exact level `L + 1` is square integrable with variance at most
`4M²Λ²T²/2^L = 4M²Λ²T h_L`, `h_L = T 2^{−L}` (`ssaChain_sq_le`). -/
theorem variance_ssaCorrection_exact_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) (x₀ : ℕ) {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) (L : ℕ) :
    IsProbabilityMeasure (ssaInputLaw lam Λ T x₀ L) ∧
    MemLp (ssaCorrection Φ L (L + 1)) 2 (ssaInputLaw lam Λ T x₀ L) ∧
      variance (ssaCorrection Φ L (L + 1)) (ssaInputLaw lam Λ T x₀ L) ≤
        4 * M ^ 2 * ((Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 / 2 ^ L) := by
  refine ⟨isProbabilityMeasure_ssaInputLaw hΛ T x₀ L,
    memLp_ssaCorrection hΛ T x₀ L hΦ (L + 1), ?_⟩
  have := isProbabilityMeasure_ssaLevelLaw hΛ T x₀ L
  have hP := isProbabilityMeasure_ssaChain hΛ (T / 2 ^ L) x₀ (2 ^ L)
  have e1 : ssaCorrection Φ L (L + 1) = fun y => (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) (y (L + 1)) := by
    rw [ssaCorrection, if_neg (by omega)]
  have e2 : ssaLevelLaw lam Λ T x₀ L (L + 1) = ssaChain lam Λ (T / 2 ^ L) x₀ (2 ^ L) := by
    rw [ssaLevelLaw, if_neg (by omega)]
  have e3 : ((2 ^ L : ℕ) : ℝ≥0) = 2 ^ L := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have e4 : ((2 ^ L : ℕ) : ℝ) = 2 ^ L := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have h := (ssaChain_sq_le hΛ T x₀ hΦ (N := 2 ^ L) (by positivity)).2
  rw [e3, e4] at h
  have hmp : MeasurePreserving (fun y : ℕ → ℕ × ℕ => y (L + 1)) (ssaInputLaw lam Λ T x₀ L)
      (ssaLevelLaw lam Λ T x₀ L (L + 1)) :=
    measurePreserving_eval_infinitePi (ssaLevelLaw lam Λ T x₀ L) (L + 1)
  have hv := hmp.variance_fun_comp (f := fun q : ℕ × ℕ => Φ q.1 - Φ q.2)
    Measurable.of_discrete.aemeasurable
  rw [e2] at hv
  calc variance (ssaCorrection Φ L (L + 1)) (ssaInputLaw lam Λ T x₀ L)
      = variance (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) (ssaChain lam Λ (T / 2 ^ L) x₀ (2 ^ L)) := by
        rw [e1]
        exact hv
    _ ≤ _ := (variance_le_expectation_sq Measurable.of_discrete.aestronglyMeasurable).trans h

/-- **The mean square error of the unbiased estimator is its variance**
`∑_{ℓ ≤ L + 1} V_ℓ / N_ℓ` (Giles 2015, §8, p. 56, l. 2415, with (2.1), (2.3)). -/
lemma ssa_mse_eq {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) (L : ℕ) {N : ℕ → ℕ} (hN : ∀ ℓ, 0 < N ℓ) :
    ∫ x, (∑ ℓ ∈ range (L + 2), blockMean (ssaCorrection Φ L) (fun p x => x p) ℓ (N ℓ) x -
        ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2
        ∂(Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) =
      ∑ ℓ ∈ range (L + 2),
        variance (ssaCorrection Φ L ℓ) (ssaInputLaw lam Λ T x₀ L) / N ℓ := by
  have hν := isProbabilityMeasure_ssaInputLaw hΛ T x₀ L
  obtain ⟨hμ, hind, hω⟩ := exists_iid_inputs (ssaInputLaw lam Λ T x₀ L)
  have hc := memLp_ssaCorrection hΛ T x₀ L hΦ
  set Y : ℕ → (ℕ × ℕ → ℕ → ℕ × ℕ) → ℝ :=
    fun ℓ => blockMean (ssaCorrection Φ L) (fun p x => x p) ℓ (N ℓ) with hY_def
  have hY : ∀ ℓ, MemLp (Y ℓ) 2 (Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) :=
    fun ℓ => memLp_blockMean hω hc ℓ (N ℓ)
  have hS : MemLp (∑ ℓ ∈ range (L + 2), Y ℓ) 2
      (Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) :=
    memLp_finsetSum' _ fun ℓ _ => hY ℓ
  have hmse := mse_eq_variance_add_sq_bias hS (∫ y, Φ y ∂(exactLaw lam Λ T x₀))
  have hmean : ∫ x, (∑ ℓ ∈ range (L + 2), Y ℓ) x
      ∂(Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) =
      ∫ y, Φ y ∂(exactLaw lam Λ T x₀) := by
    simp only [Finset.sum_apply]
    exact (ssa_mlmc_unbiased hΛ T x₀ hΦ L hN).2.2
  have hvar : variance (∑ ℓ ∈ range (L + 2), Y ℓ)
      (Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) =
      ∑ ℓ ∈ range (L + 2), variance (ssaCorrection Φ L ℓ) (ssaInputLaw lam Λ T x₀ L) / N ℓ := by
    rw [IndepFun.variance_sum (fun ℓ _ => hY ℓ) fun i _ j _ hij =>
      indepFun_blockMean (fun p => (hω p).measurable) hind (measurable_ssaCorrection Φ L) hij
        (N i) (N j)]
    exact Finset.sum_congr rfl fun ℓ _ =>
      variance_blockMean hω hind (measurable_ssaCorrection Φ L) hc ℓ (hN ℓ)
  rw [hmean, sub_self, hvar, zero_pow two_ne_zero, add_zero] at hmse
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) hmse
  rw [Finset.sum_apply]

/-- **(G8-14) With the exact SSA level and a fixed number of levels the complexity is `O(ε⁻²)`**
(Giles 2015, §8, p. 56, l. 2415–2417: "their overall multilevel estimator is unbiased … and the
complexity is reduced to `O(ε⁻²)` because the number of levels remains fixed as `ε → 0`").  Let
`0 ≤ λ ≤ Λ` and `|Φ| ≤ M`, and fix the number `L + 1` of tau-leaping levels.  The estimator of
`ssa_mlmc_unbiased` (tau-leaping levels `ℓ ≤ L` and the exact level `L + 1`, independent samples)
is sampled from a probability measure and has, for some `c > 0` and every `0 < ε ≤ 1`, sample
numbers `N_ℓ ≥ 1` (the rounded-up allocation (1.1) of `fixed_levels_cost` for the variances
`V_ℓ + 1` and the target `ε²/4`) with a square-integrable error, mean square error
`E[(Y − E[Φ(X_T)])²] < ε²` and cost `∑_{ℓ ≤ L} N_ℓ 2^ℓ + N_{L+1} (2^L + ΛT) ≤ c ε⁻²`.  Cost model:
a tau-leaping sample of level `ℓ` costs its `2^ℓ` fine steps, as in `tauLeaping_mlmc_exact`; an
exact-level sample costs its `2^L` tau-leaping steps plus the expected number `E[P(ΛT)] = ΛT` of
ticks of the uniformisation clock (the sum of the `2^L` independent `P(ΛT 2^{−L})` tick counts),
each one uniform and one propensity evaluation.  The cost is this expected value; the random cost is
not modelled here; see `ssa_mlmc_complexity_random_cost` (`MlmcLean.TauLeapingSSACost`), whose
expected random cost equals this cost.  Deviations: one reaction, bounded propensity, bounded
payoff, exact chain by uniformisation; the constant `c` depends on `L` (and on `λ`, `Λ`, `T`, `x₀`,
`Φ`).  The rate `ε⁻²` uses only that the estimator is unbiased with finitely many levels of finite
variance and cost; it would hold as well with an independently sampled exact level, or for plain
Monte Carlo on the exact chain.  The coupling affects the constant: the exact-level variance is
`O(2^{−L})` (`variance_ssaCorrection_exact_le`), whose effect on `c` is not tracked here. -/
theorem ssa_mlmc_complexity {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0) (x₀ : ℕ)
    {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) (L : ℕ) :
    IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 2),
            blockMean (ssaCorrection Φ L) (fun p x => x p) ℓ (N ℓ) x -
              ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) ∧
        ∫ x, (∑ ℓ ∈ range (L + 2), blockMean (ssaCorrection Φ L) (fun p x => x p) ℓ (N ℓ) x -
            ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => ssaInputLaw lam Λ T x₀ L) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ + (N (L + 1) : ℝ) * (2 ^ L + Λ * T) ≤
          c / ε ^ 2 := by
  have hν := isProbabilityMeasure_ssaInputLaw hΛ T x₀ L
  obtain ⟨hμ, -, hω⟩ := exists_iid_inputs (ssaInputLaw lam Λ T x₀ L)
  have hc := memLp_ssaCorrection hΛ T x₀ L hΦ
  set V : ℕ → ℝ := fun ℓ => variance (ssaCorrection Φ L ℓ) (ssaInputLaw lam Λ T x₀ L) + 1
    with hV_def
  set C : ℕ → ℝ := fun ℓ => if ℓ ≤ L then (2 : ℝ) ^ ℓ else 2 ^ L + Λ * T with hC_def
  have hV : ∀ ℓ, 0 < V ℓ := fun ℓ => by
    rw [hV_def]
    linarith [variance_nonneg (ssaCorrection Φ L ℓ) (ssaInputLaw lam Λ T x₀ L)]
  have hC : ∀ ℓ, 0 < C ℓ := fun ℓ => by
    rw [hC_def]
    dsimp only
    split_ifs
    · positivity
    · positivity
  have hs : (range (L + 2)).Nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  obtain ⟨c, hc0, hfix⟩ := fixed_levels_cost hs (fun ℓ _ => hV ℓ) (fun ℓ _ => hC ℓ)
  refine ⟨hμ, 4 * c, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨hvar, hcost⟩ := hfix (ε / 2) (by positivity) (by linarith)
  have hτ : 0 < (ε / 2) ^ 2 := by positivity
  set N : ℕ → ℕ := optimalN (range (L + 2)) V C ((ε / 2) ^ 2) with hN_def
  have hN : ∀ ℓ, 0 < N ℓ := optimalN_pos hs hV hC hτ
  refine ⟨N, hN, ?_, ?_, ?_⟩
  · exact ((memLp_finsetSum _ fun ℓ _ => memLp_blockMean hω hc ℓ (N ℓ)).sub
      (memLp_const _)).integrable_sq
  · rw [ssa_mse_eq hΛ T x₀ hΦ L hN]
    calc ∑ ℓ ∈ range (L + 2), variance (ssaCorrection Φ L ℓ) (ssaInputLaw lam Λ T x₀ L) / N ℓ
        ≤ ∑ ℓ ∈ range (L + 2), V ℓ / N ℓ :=
          Finset.sum_le_sum fun ℓ _ =>
            div_le_div_of_nonneg_right (by rw [hV_def]; linarith) (Nat.cast_nonneg _)
      _ ≤ (ε / 2) ^ 2 := hvar
      _ < ε ^ 2 := by nlinarith
  · have e : ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ + (N (L + 1) : ℝ) * (2 ^ L + Λ * T) =
        ∑ ℓ ∈ range (L + 2), (N ℓ : ℝ) * C ℓ := by
      rw [Finset.sum_range_succ (n := L + 1)]
      congr 1
      · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
        rw [hC_def]
        dsimp only
        rw [if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ))]
      · rw [hC_def]
        dsimp only
        rw [if_neg (by omega)]
    rw [e]
    refine hcost.trans (le_of_eq ?_)
    field_simp
    ring

end MLMC
