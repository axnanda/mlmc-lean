import MlmcLean.TauLeapingMLMC
import MlmcLean.PoissonGrids

/-!
# Tau-leaping against the exact continuous-time chain: weak order one (Giles 2015, §8)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §8
"Continuous-time Markov chains", pp. 55–56 (`docs/giles2015.txt`, ll. 2366–2417).

§8, p. 55: "When there is just one chemical reaction, the 'tau-leaping' method (which is
essentially the Euler-Maruyama method, approximating the reaction rate as being constant
throughout the timestep) gives the discrete equation `x_{n+1} = x_n + P(hλ(x_n))`"; p. 56: the
Poisson coupling "leads to a very effective multilevel algorithm with a correction variance which
is `O(h)`, leading to an `O(ε⁻²(log ε)²)` complexity", and "the exact Stochastic Simulation
Algorithm developed by (Gillespie 1976) which updates the reaction rates after every single
reaction".  By Theorem 1 the complexity claim also needs a weak rate `α ≥ ½` of tau-leaping
against the exact chain, which the paper leaves implicit (tau-leaping has weak order `α = 1`);
`tauLeaping_mlmc_theorem1` assumes it.  Here it is proved for bounded propensities and bounded
payoffs, with the exact chain itself constructed.

**The model** is that of `tauStep` and `tauChain`: one reaction, the state `x ∈ ℕ` counts the
reactions, each reaction moves `x` to `x + 1`, and the propensity `λ : ℕ → [0, ∞)` is bounded,
`λ ≤ Λ`.  The exact chain jumps from `x` to `x + 1` at rate `λ(x)`.

**Uniformisation.**  A Poisson clock of rate `Λ` ticks; at each tick the state `x` jumps to `x + 1`
with probability `λ(x)/Λ` and stays put otherwise (`jumpKernel`, `J(x) = (λ(x)/Λ) δ_{x+1} +
(1 − λ(x)/Λ) δ_x`, iterated in `jumpPow`).  The law at time `t` from `x` is
`exactLaw λ Λ t x = P(Λt).bind (n ↦ J^n(x))`.
* `isProbabilityMeasure_exactLaw`, `exactLaw_add`: a probability measure, and the
  **Chapman–Kolmogorov equation** `P_{s+t} = P_s P_t` (from `P(Λs) ∗ P(Λt) = P(Λ(s + t))`, "the
  sum of two independent Poisson variates `P(t₁)`, `P(t₂)` is equivalent in distribution to
  `P(t₁ + t₂)`", p. 55); with the helper `exactLaw_zero` (`P_0 = δ_x`) a Markov semigroup.
* `exactLaw_generator`: `|E_x[f(X_t)] − f(x) − tλ(x)(f(x + 1) − f(x))| ≤ 5(Λt)² sup|f|`, so the
  generator is `Gf(x) = λ(x)(f(x + 1) − f(x))`, the chain with jump rates `λ`.
* `exactLaw_backward_equation`, `exactLaw_forward_equation`, `exactLaw_master_equation`:
  **Kolmogorov's backward and forward equations** at every `t > 0` (two-sided derivatives); for
  the transition probabilities `p_t(y) = P_x(X_t = y)`, `p_t'(0) = −λ(0)p_t(0)` and
  `p_t'(y + 1) = λ(y)p_t(y) − λ(y + 1)p_t(y + 1)`.  `exactLaw_hasDerivWithinAt_zero`: at `t = 0`
  the right derivative of `E_x[f(X_t)]` is the generator `λ(x)(f(x + 1) − f(x))`.
* `exactLaw_unique`: every Markov semigroup on `ℕ` with this generator (in the quantitative sense of
  `exactLaw_generator`) is `exactLaw`; `exactLaw_eq_of_bound`: the law does not depend on the
  uniformisation rate `Λ ≥ sup λ`; `exactLaw_const`: for a constant propensity it is the Poisson
  law `x + P(Λt)`.

**The weak error of tau-leaping.**
* `exactLaw_tauStep_le`: one step, `|E_x[f(X_h)] − E[f(x + P(hλ(x)))]| ≤ 2(Λh)² sup|f|` (with
  at most one clock tick, resp. one jump, the two laws agree to `O((Λh)²)`, and two or more occur
  with probability at most `(Λh)²`).
* the helper `exactLaw_steps_of_one_step`: telescoping, the error after `n` steps is at most `n`
  times the one-step error (both semigroups are sup-norm contractions).
* `tauLeaping_weak_error_exact`: **weak order one**, `|E[Φ(x_N)] − E[Φ(X_T)]| ≤ 2Λ²T² sup|Φ|/N`
  for `N` tau-leaping steps of size `T/N`.
* `tauLeaping_mlmc_exact`: **Theorem 1 for tau-leaping MLMC with the exact chain as target and no
  assumed weak rate**: for a bounded propensity (on `ℕ` automatically Lipschitz,
  `abs_sub_le_mul_of_le_nat`) and a bounded payoff, mean square error `< ε²` about `E[Φ(X_T)]` at
  cost `O(ε⁻²(log ε)²)`.

**Checks.**  The constants were checked numerically (`mpmath`, truncated state space) for
`λ ≡ 2`, `λ(x) = min(x, 3)`, `λ(x) = 1 + (x mod 2)` and `λ = 1_{x even}`: the one-step ratio
`sup_{|f| ≤ 1}|…|/(Λh)²` stays below `1` (it tends to `1` as `h → 0` for `λ = 1_{x even}`, so
the constant `2` is within a factor `2` of optimal), the `N`-step error times `N` stays well
below `2Λ²T²` (about `0.37` against `18` for `λ(x) = min(x, 3)`, `Λ = 3`, `T = 1`, `x₀ = 1`;
for `x₀ = 0`, an absorbing state, and for `x₀ ≥ 3`, where `λ` is constant, it is `0`), and the
semigroup property, the independence of `Λ` and both Kolmogorov equations hold to working
precision.

**Scope.**  Bounded propensities (uniformisation needs `Λ < ∞`) and bounded payoffs; Lipschitz
unbounded payoffs such as `Φ(x) = x` would need moment bounds for the exact chain and weighted
sup norms.  One reaction, as in `tauChain`.  The extra coupling of the finest level to the exact
chain (Anderson–Higham, p. 56, an unbiased estimator) is in `MlmcLean.TauLeapingSSA`
(`ssa_mlmc_unbiased`, `ssa_mlmc_complexity`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace MLMC

section Discrete

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-! ### Compositions of measures on discrete spaces -/

/-- A composition of probability measures on a discrete space has mass one: if `μ` and every `κ a`
are probability measures, so is `μ.bind κ` (used for the laws of Giles 2015, §8). -/
lemma measure_univ_bind_of_discrete [DiscreteMeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {κ : α → Measure β} (hκ : ∀ a, κ a Set.univ = 1) :
    μ.bind κ Set.univ = 1 := by
  rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable,
    lintegral_congr hκ, lintegral_const, one_mul, measure_univ]

/-- Independent compositions commute (Tonelli on `ℕ × ℕ`):
`μ.bind (a ↦ ν.bind (b ↦ κ a b)) = ν.bind (b ↦ μ.bind (a ↦ κ a b))`; used for the
Chapman–Kolmogorov equation of the exact chain (Giles 2015, §8). -/
lemma bind_bind_comm_nat (μ ν : Measure ℕ) [SFinite μ] [SFinite ν]
    (κ : ℕ → ℕ → Measure γ) :
    (μ.bind fun a => ν.bind fun b => κ a b) = ν.bind fun b => μ.bind fun a => κ a b := by
  ext s hs
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
  calc ∫⁻ a, (ν.bind fun b => κ a b) s ∂μ = ∫⁻ a, ∫⁻ b, κ a b s ∂ν ∂μ :=
        lintegral_congr fun a => Measure.bind_apply hs Measurable.of_discrete.aemeasurable
    _ = ∫⁻ b, ∫⁻ a, κ a b s ∂μ ∂ν :=
        lintegral_lintegral_swap Measurable.of_discrete.aemeasurable
    _ = ∫⁻ b, (μ.bind fun a => κ a b) s ∂ν :=
        lintegral_congr fun b => (Measure.bind_apply hs Measurable.of_discrete.aemeasurable).symm

/-- A composition with a function of the sum of two independent counts is a composition with their
convolution: `μ.bind (m ↦ ν.bind (n ↦ F (m + n))) = (μ ∗ ν).bind F` (with
`poissonMeasure_conv_poissonMeasure`, Giles 2015, §8, p. 55). -/
lemma bind_bind_add_eq_bind_conv (μ ν : Measure ℕ) [SFinite ν] (F : ℕ → Measure γ) :
    (μ.bind fun m => ν.bind fun n => F (m + n)) = (μ ∗ ν).bind F := by
  ext s hs
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    Measure.lintegral_conv (Measurable.of_discrete (f := fun k : ℕ => F k s))]
  exact lintegral_congr fun m => Measure.bind_apply hs Measurable.of_discrete.aemeasurable

/-- The Markov property for bounded functions (used throughout Giles 2015, §8): on discrete spaces,
for probability measures `μ`, `κ a` and `|f| ≤ M`, `∫ f d(μ.bind κ) = ∫ (∫ f dκ(a)) dμ(a)`. -/
lemma integral_bind_of_abs_le [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] {κ : α → Measure β}
    (hκ : ∀ a, IsProbabilityMeasure (κ a)) {f : β → ℝ} {M : ℝ} (hf : ∀ b, |f b| ≤ M) :
    ∫ b, f b ∂(μ.bind κ) = ∫ a, ∫ b, f b ∂(κ a) ∂μ := by
  have hP : IsProbabilityMeasure (μ.bind κ) :=
    ⟨measure_univ_bind_of_discrete μ fun a => (hκ a).measure_univ⟩
  have hg0 : ∀ b, 0 ≤ f b + M := fun b => by linarith [neg_abs_le (f b), hf b]
  have hgM : ∀ b, ‖f b + M‖ ≤ 2 * M := fun b => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 b)]
    linarith [le_abs_self (f b), hf b]
  have hint : ∀ ν : Measure β, IsFiniteMeasure ν → Integrable (fun b => f b + M) ν :=
    fun ν _ => Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable (2 * M)
      (ae_of_all _ hgM)
  have hintf : ∀ ν : Measure β, IsFiniteMeasure ν → Integrable f ν := fun ν hν =>
    Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable M
      (ae_of_all _ fun b => by rw [Real.norm_eq_abs]; exact hf b)
  -- the nonnegative function `f + M`
  have key : ∫ b, (f b + M) ∂(μ.bind κ) = ∫ a, ∫ b, (f b + M) ∂(κ a) ∂μ := by
    have hin0 : ∀ a, 0 ≤ ∫ b, (f b + M) ∂(κ a) := fun a => integral_nonneg hg0
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0)
        Measurable.of_discrete.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hin0)
        Measurable.of_discrete.aestronglyMeasurable,
      Measure.lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
    congr 1
    refine lintegral_congr fun a => ?_
    have := hκ a
    rw [ofReal_integral_eq_lintegral_ofReal (hint _ inferInstance) (ae_of_all _ hg0)]
  have e1 : ∫ b, (f b + M) ∂(μ.bind κ) = ∫ b, f b ∂(μ.bind κ) + M := by
    rw [integral_add (hintf _ inferInstance) (integrable_const M), integral_const,
      probReal_univ, one_smul]
  have e2 : ∀ a, ∫ b, (f b + M) ∂(κ a) = ∫ b, f b ∂(κ a) + M := fun a => by
    have := hκ a
    rw [integral_add (hintf _ inferInstance) (integrable_const M), integral_const,
      probReal_univ, one_smul]
  have hin : Integrable (fun a => ∫ b, f b ∂(κ a)) μ :=
    Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable M
      (ae_of_all _ fun a => by
        have := hκ a
        rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ b, |f b| ∂(κ a) ≤ ∫ _b, M ∂(κ a) :=
              integral_mono (hintf _ inferInstance).abs (integrable_const M) hf
          _ = M := by rw [integral_const, probReal_univ, one_smul])
  rw [e1, funext e2, integral_add hin (integrable_const M), integral_const, probReal_univ,
    one_smul] at key
  linarith

end Discrete

/-! ### The exact chain by uniformisation -/

/-- **One step of the uniformised chain** (Giles 2015, §8; the exact chain, which "updates the
reaction rates after every single reaction", p. 56, by uniformisation).  With a rate bound
`Λ ≥ λ`, at each tick of a rate-`Λ` Poisson clock the state `x` jumps to `x + 1` with
probability `λ(x)/Λ` and stays put otherwise: `J(x) = (λ(x)/Λ) δ_{x+1} + (1 − λ(x)/Λ) δ_x`.  The
state space `ℕ` and the jump `x ↦ x + 1` are those of the tau-leaping step `tauStep`. -/
noncomputable def jumpKernel (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (x : ℕ) : Measure ℕ :=
  (lam x / Λ) • Measure.dirac (x + 1) + (1 - lam x / Λ) • Measure.dirac x

/-- The law `J^n(x)` after `n` steps of the uniformised jump chain `jumpKernel` from `x`
(Giles 2015, §8). -/
noncomputable def jumpPow (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) : ℕ → ℕ → Measure ℕ
  | 0 => fun x => Measure.dirac x
  | n + 1 => fun x => (jumpPow lam Λ n x).bind (jumpKernel lam Λ)

/-- **The law at time `t` of the exact continuous-time chain, by uniformisation** (Giles 2015, §8,
pp. 55–56: the exact chain, against which tau-leaping approximates "the reaction rate as being
constant throughout the timestep").  The chain jumps from `x` to `x + 1` at rate `λ(x)`.  With
`λ ≤ Λ`, the number of clock ticks in `[0, t]` is `P(Λt)`, and given `n` ticks the state has law
`J^n(x)`: `exactLaw λ Λ t x = P(Λt).bind (n ↦ J^n(x))`.  It does not depend on `Λ ≥ sup λ`
(`exactLaw_eq_of_bound`), has the generator `Gf(x) = λ(x)(f(x + 1) − f(x))`
(`exactLaw_generator`) and solves Kolmogorov's equations (`exactLaw_backward_equation`,
`exactLaw_master_equation`). -/
noncomputable def exactLaw (lam : ℕ → ℝ≥0) (Λ t : ℝ≥0) (x : ℕ) : Measure ℕ :=
  (poissonMeasure (Λ * t)).bind fun n => jumpPow lam Λ n x

/-- Zero steps of the jump chain: `J^0(x) = δ_x`. -/
lemma jumpPow_zero (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (x : ℕ) : jumpPow lam Λ 0 x = Measure.dirac x :=
  rfl

/-- One more step of the jump chain: `J^{n+1}(x) = J^n(x).bind J`. -/
lemma jumpPow_succ (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (n x : ℕ) :
    jumpPow lam Λ (n + 1) x = (jumpPow lam Λ n x).bind (jumpKernel lam Λ) :=
  rfl

/-- The jump probability `λ(x)/Λ` is at most one when `λ ≤ Λ` (for `Λ = 0` it is `0 / 0 = 0`,
and then `λ = 0`). -/
lemma rate_div_le_one {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (x : ℕ) :
    lam x / Λ ≤ 1 :=
  div_le_one_of_le₀ (hΛ x) zero_le

/-- One step of the uniformised chain is a probability measure when `λ ≤ Λ`. -/
lemma jumpKernel_univ {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (x : ℕ) :
    jumpKernel lam Λ x Set.univ = 1 := by
  rw [jumpKernel, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    measure_univ, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.coe_add, add_tsub_cancel_of_le (rate_div_le_one hΛ x), ENNReal.coe_one]

/-- `J^n(x)` is a probability measure when `λ ≤ Λ`. -/
lemma jumpPow_univ {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) :
    ∀ n x, jumpPow lam Λ n x Set.univ = 1
  | 0, x => by rw [jumpPow_zero, measure_univ]
  | n + 1, x => by
      have : IsProbabilityMeasure (jumpPow lam Λ n x) := ⟨jumpPow_univ hΛ n x⟩
      rw [jumpPow_succ]
      exact measure_univ_bind_of_discrete _ (jumpKernel_univ hΛ)

/-- The jump chain is a Markov chain: `J^{m+n}(x) = J^m(x).bind J^n`. -/
lemma jumpPow_add (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (m : ℕ) :
    ∀ n x, jumpPow lam Λ (m + n) x = (jumpPow lam Λ m x).bind (jumpPow lam Λ n)
  | 0, x => by
      rw [add_zero]
      exact Measure.bind_dirac.symm
  | n + 1, x => by
      rw [← add_assoc, jumpPow_succ, jumpPow_add lam Λ m n x,
        Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
      rfl

/-- **The exact law is a probability measure** (Giles 2015, §8, p. 56: "the exact Stochastic
Simulation Algorithm developed by (Gillespie 1976) which updates the reaction rates after every
single reaction").  For `λ ≤ Λ`, `exactLaw λ Λ t x` has mass one. -/
theorem isProbabilityMeasure_exactLaw {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (t : ℝ≥0) (x : ℕ) :
    IsProbabilityMeasure (exactLaw lam Λ t x) :=
  ⟨measure_univ_bind_of_discrete _ fun n => jumpPow_univ hΛ n x⟩

/-- **The Chapman–Kolmogorov equation of the exact chain** (Giles 2015, §8, p. 55: "for any
`t₁, t₂ > 0`, the sum of two independent Poisson variates `P(t₁)`, `P(t₂)` is equivalent in
distribution to `P(t₁ + t₂)`").  For `λ ≤ Λ`,
`exactLaw λ Λ (s + t) x = (exactLaw λ Λ s x).bind (exactLaw λ Λ t)`: the clock ticks in
`[0, s + t]` are those in `[0, s]` and, independently, those in `(s, s + t]`. -/
theorem exactLaw_add {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (s t : ℝ≥0) (x : ℕ) :
    exactLaw lam Λ (s + t) x = (exactLaw lam Λ s x).bind (exactLaw lam Λ t) := by
  have hP : ∀ m y, IsProbabilityMeasure (jumpPow lam Λ m y) := fun m y => ⟨jumpPow_univ hΛ m y⟩
  have e : ∀ m, (jumpPow lam Λ m x).bind (exactLaw lam Λ t) =
      (poissonMeasure (Λ * t)).bind fun n => jumpPow lam Λ (m + n) x := fun m => by
    have := hP m x
    unfold exactLaw
    rw [bind_bind_comm_nat]
    exact congrArg _ (funext fun n => (jumpPow_add lam Λ m n x).symm)
  symm
  calc (exactLaw lam Λ s x).bind (exactLaw lam Λ t)
      = (poissonMeasure (Λ * s)).bind fun m => (jumpPow lam Λ m x).bind (exactLaw lam Λ t) :=
        Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable
    _ = (poissonMeasure (Λ * s)).bind fun m =>
          (poissonMeasure (Λ * t)).bind fun n => jumpPow lam Λ (m + n) x := by
        rw [funext e]
    _ = (poissonMeasure (Λ * s) ∗ poissonMeasure (Λ * t)).bind fun k => jumpPow lam Λ k x :=
        bind_bind_add_eq_bind_conv _ _ fun k => jumpPow lam Λ k x
    _ = exactLaw lam Λ (s + t) x := by
        rw [poissonMeasure_conv_poissonMeasure, ← mul_add, exactLaw]

/-! ### One tau-leaping step against the exact chain -/

/-- A Poisson average split after its first two terms: for `|u| ≤ M`,
`∫ u dP(r) = e^{−r} u(0) + e^{−r} r u(1) + ρ` with `|ρ| ≤ M (1 − e^{−r} − e^{−r} r)`, `M` times
the probability that `P(r) ≥ 2`. -/
lemma poisson_integral_split (r : ℝ≥0) {u : ℕ → ℝ} {M : ℝ} (hu : ∀ n, |u n| ≤ M) :
    ∃ ρ : ℝ, |ρ| ≤ M * (1 - Real.exp (-r) - Real.exp (-r) * r) ∧
      ∫ n, u n ∂(poissonMeasure r) =
        Real.exp (-r) * u 0 + Real.exp (-r) * r * u 1 + ρ := by
  set w : ℕ → ℝ := fun n => Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) with hw_def
  have hw0 : ∀ n, 0 ≤ w n := fun n => by positivity
  have hw : HasSum w 1 := hasSum_one_poissonMeasure r
  have hw2 : HasSum (fun n => w (n + 2)) (1 - ∑ i ∈ range 2, w i) :=
    (hasSum_nat_add_iff' 2).2 hw
  have hbd : ∀ n, ‖w (n + 2) * u (n + 2)‖ ≤ M * w (n + 2) := fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hu _) (hw0 _)
  have hv : Summable fun n => w (n + 2) * u (n + 2) :=
    Summable.of_norm_bounded (hw2.summable.mul_left M) hbd
  refine ⟨∑' n, w (n + 2) * u (n + 2), ?_, ?_⟩
  · have h := hv.hasSum.norm_le_of_bounded (hw2.mul_left M) hbd
    rw [Real.norm_eq_abs] at h
    have e : ∑ i ∈ range 2, w i = Real.exp (-r) + Real.exp (-r) * r := by
      simp [Finset.sum_range_succ, hw_def]
    rw [e, ← sub_sub] at h
    exact h
  · have hfull : HasSum (fun n => w n * u n)
        ((∑ i ∈ range 2, w i * u i) + ∑' n, w (n + 2) * u (n + 2)) :=
      HasSum.sum_range_add (f := fun n => w n * u n) hv.hasSum
    rw [integral_poissonMeasure]
    simp only [smul_eq_mul]
    rw [hfull.tsum_eq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hw_def]
    norm_num

/-- `P(P(a) ≥ 2) = 1 − e^{−a} − a e^{−a} ≤ a²` for `a ≥ 0` (from `e^{−a} ≥ 1 − a`). -/
lemma one_sub_exp_neg_sub_mul_le_sq (a : ℝ) (ha : 0 ≤ a) :
    1 - Real.exp (-a) - Real.exp (-a) * a ≤ a ^ 2 := by
  have h := Real.add_one_le_exp (-a)
  nlinarith

/-- `∫ f dJ(x) = (λ(x)/Λ) f(x + 1) + (1 − λ(x)/Λ) f(x)` when `λ ≤ Λ`. -/
lemma integral_jumpKernel {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (f : ℕ → ℝ)
    (x : ℕ) : ∫ y, f y ∂(jumpKernel lam Λ x) =
      ((lam x / Λ : ℝ≥0) : ℝ) * f (x + 1) + (1 - ((lam x / Λ : ℝ≥0) : ℝ)) * f x := by
  rw [jumpKernel, integral_add_measure
      (Integrable.smul_measure_nnreal (integrable_dirac enorm_lt_top))
      (Integrable.smul_measure_nnreal (integrable_dirac enorm_lt_top)),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_dirac, integral_dirac,
    NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul,
    NNReal.coe_sub (rate_div_le_one hΛ x), NNReal.coe_one]

/-- `|∫ f dμ| ≤ M` for `|f| ≤ M` and a probability measure `μ`. -/
lemma abs_integral_le_of_abs_le_prob {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) : |∫ y, f y ∂μ| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := M)
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hf y)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h

/-- `(λ(x)/Λ)(Λh) = hλ(x)`: the thinned clock rate is the tau-leaping rate (also for `Λ = 0`, when
`λ = 0`). -/
lemma rate_div_mul_eq {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0) (x : ℕ) :
    ((lam x / Λ : ℝ≥0) : ℝ) * ((Λ : ℝ) * h) = (h : ℝ) * lam x := by
  rcases eq_or_ne Λ 0 with h0 | h0
  · have : lam x = 0 := le_antisymm ((hΛ x).trans h0.le) zero_le
    simp [this, h0]
  · have h0' : (Λ : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 h0
    rw [NNReal.coe_div]
    field_simp

/-- The two coefficients of the one-step error (Giles 2015, §8): for `0 ≤ r ≤ a`,
`|e^{−a}(1 + a − r) − e^{−r}| ≤ (a − r)²` and `|r(e^{−a} − e^{−r})| ≤ r(a − r)`. -/
lemma uniformised_exp_coeff_bounds {a r : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) :
    |Real.exp (-a) * (1 + a - r) - Real.exp (-r)| ≤ (a - r) ^ 2 ∧
      |r * (Real.exp (-a) - Real.exp (-r))| ≤ r * (a - r) := by
  have hA : Real.exp (-a) = Real.exp (-r) * Real.exp (-(a - r)) := by
    rw [← Real.exp_add]
    ring_nf
  have hd : 0 ≤ a - r := sub_nonneg.2 hra
  have hD1 : 1 - (a - r) ≤ Real.exp (-(a - r)) := by linarith [Real.add_one_le_exp (-(a - r))]
  have hD2 : Real.exp (-(a - r)) * (1 + (a - r)) ≤ 1 := by
    have h1 := Real.add_one_le_exp (a - r)
    have h2 : Real.exp (a - r) * Real.exp (-(a - r)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-(a - r))]
  have hD3 : Real.exp (-(a - r)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hR0 : 0 < Real.exp (-r) := Real.exp_pos _
  have hR1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [hA]
  constructor
  · rw [abs_le]
    constructor
    · have h3 : -(a - r) ^ 2 ≤ Real.exp (-(a - r)) * (1 + (a - r)) - 1 := by nlinarith
      have h4 : Real.exp (-r) * (-(a - r) ^ 2) ≥ -(a - r) ^ 2 := by nlinarith
      nlinarith
    · nlinarith
  · rw [abs_le]
    constructor
    · have h3 : Real.exp (-r) * (1 - Real.exp (-(a - r))) ≤ a - r := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 hr]
    · nlinarith [mul_nonneg hr (mul_nonneg hR0.le (sub_nonneg.2 hD3))]

/-- **The local weak error of one tau-leaping step is `O(h²)`** (Giles 2015, §8, p. 55: "the
'tau-leaping' method (which is essentially the Euler-Maruyama method, approximating the reaction
rate as being constant throughout the timestep) gives the discrete equation
`x_{n+1} = x_n + P(hλ(x_n))`").  For `λ ≤ Λ` and `|f| ≤ M`,
`|E_x[f(X_h)] − E[f(x + P(hλ(x)))]| ≤ 2(Λh)² M`.  Both laws are Poisson mixtures: with no clock
tick of `P(Λh)` (resp. no jump of `P(hλ(x))`) or exactly one, they agree up to `O((Λh)²)`, and two
or more occur with probability at most `(Λh)²`.  The constant `2` is within a factor `2` of
optimal: for `λ = 1_{x even}` and `x = 0` the left side is `(1 + o(1))(Λh)² M` as `h → 0`. -/
theorem exactLaw_tauStep_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) {f : ℕ → ℝ}
    {M : ℝ} (hf : ∀ y, |f y| ≤ M) (h : ℝ≥0) (x : ℕ) :
    |∫ y, f y ∂(exactLaw lam Λ h x) - ∫ y, f y ∂(tauStep lam h x)| ≤
      2 * ((Λ : ℝ) * h) ^ 2 * M := by
  have hP : ∀ n y, IsProbabilityMeasure (jumpPow lam Λ n y) := fun n y => ⟨jumpPow_univ hΛ n y⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  set g : ℕ → ℝ := fun n => ∫ y, f y ∂(jumpPow lam Λ n x) with hg_def
  have hg : ∀ n, |g n| ≤ M := fun n => by
    have := hP n x
    exact abs_integral_le_of_abs_le_prob hf
  have hE : ∫ y, f y ∂(exactLaw lam Λ h x) = ∫ n, g n ∂(poissonMeasure (Λ * h)) :=
    integral_bind_of_abs_le _ (fun n => hP n x) hf
  have hT : ∫ y, f y ∂(tauStep lam h x) = ∫ n, f (x + n) ∂(poissonMeasure (h * lam x)) := by
    rw [tauStep, integral_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable]
  have hg0 : g 0 = f x := by
    show ∫ y, f y ∂(jumpPow lam Λ 0 x) = f x
    rw [jumpPow_zero, integral_dirac]
  have hg1 : g 1 = ((lam x / Λ : ℝ≥0) : ℝ) * f (x + 1) + (1 - ((lam x / Λ : ℝ≥0) : ℝ)) * f x := by
    show ∫ y, f y ∂(jumpPow lam Λ (0 + 1) x) = _
    rw [jumpPow_succ, jumpPow_zero, Measure.dirac_bind Measurable.of_discrete,
      integral_jumpKernel hΛ]
  obtain ⟨ρ₁, hρ₁, e₁⟩ := poisson_integral_split (Λ * h) hg
  obtain ⟨ρ₂, hρ₂, e₂⟩ := poisson_integral_split (h * lam x) fun n => hf (x + n)
  have hpa := rate_div_mul_eq hΛ h x
  rw [hE, hT, e₁, e₂, hg0, hg1]
  simp only [NNReal.coe_mul] at hρ₁ hρ₂ ⊢
  set a : ℝ := (Λ : ℝ) * h with ha_def
  set r : ℝ := (h : ℝ) * lam x with hr_def
  set p : ℝ := ((lam x / Λ : ℝ≥0) : ℝ) with hp_def
  have ha0 : 0 ≤ a := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def]
    exact_mod_cast rate_div_le_one hΛ x
  have hp0 : 0 ≤ p := NNReal.coe_nonneg _
  have hra : r ≤ a := by
    rw [← hpa]
    nlinarith
  obtain ⟨hc1, hc2⟩ := uniformised_exp_coeff_bounds hr0 hra
  have key : Real.exp (-a) * f x + Real.exp (-a) * a * (p * f (x + 1) + (1 - p) * f x) + ρ₁ -
      (Real.exp (-r) * f (x + 0) + Real.exp (-r) * r * f (x + 1) + ρ₂) =
      (Real.exp (-a) * (1 + a - r) - Real.exp (-r)) * f x +
        r * (Real.exp (-a) - Real.exp (-r)) * f (x + 1) + (ρ₁ - ρ₂) := by
    rw [add_zero, ← hpa]
    ring
  have h1 : |(Real.exp (-a) * (1 + a - r) - Real.exp (-r)) * f x| ≤ (a - r) ^ 2 * M := by
    rw [abs_mul]
    exact mul_le_mul hc1 (hf x) (abs_nonneg _) (sq_nonneg _)
  have h2 : |r * (Real.exp (-a) - Real.exp (-r)) * f (x + 1)| ≤ r * (a - r) * M := by
    rw [abs_mul]
    exact mul_le_mul hc2 (hf _) (abs_nonneg _) (by nlinarith)
  have h3 : |ρ₁| ≤ M * a ^ 2 :=
    hρ₁.trans (mul_le_mul_of_nonneg_left (one_sub_exp_neg_sub_mul_le_sq a ha0) hM)
  have h4 : |ρ₂| ≤ M * r ^ 2 :=
    hρ₂.trans (mul_le_mul_of_nonneg_left (one_sub_exp_neg_sub_mul_le_sq r hr0) hM)
  have hpoly : ((a - r) ^ 2 + r * (a - r) + a ^ 2 + r ^ 2) * M ≤ 2 * a ^ 2 * M :=
    mul_le_mul_of_nonneg_right (by nlinarith) hM
  rw [key]
  calc |(Real.exp (-a) * (1 + a - r) - Real.exp (-r)) * f x +
        r * (Real.exp (-a) - Real.exp (-r)) * f (x + 1) + (ρ₁ - ρ₂)|
      ≤ |(Real.exp (-a) * (1 + a - r) - Real.exp (-r)) * f x| +
        |r * (Real.exp (-a) - Real.exp (-r)) * f (x + 1)| + (|ρ₁| + |ρ₂|) :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_sub _ _))
    _ ≤ 2 * a ^ 2 * M := by nlinarith

/-! ### Weak order one -/

/-- A bounded function on a discrete space is integrable for a finite measure. -/
lemma integrable_of_abs_le_discrete {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) :
    Integrable f μ :=
  Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable M
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hf y)

/-- The exact chain starts at `x` (Giles 2015, §8): `exactLaw λ Λ 0 x = δ_x`. -/
lemma exactLaw_zero (lam : ℕ → ℝ≥0) (Λ : ℝ≥0) (x : ℕ) :
    exactLaw lam Λ 0 x = Measure.dirac x := by
  rw [exactLaw, mul_zero, poissonMeasure_zero, Measure.dirac_bind Measurable.of_discrete,
    jumpPow_zero]

/-- The Markov property of the exact chain for bounded `f` (Giles 2015, §8):
`∫ f d(μ.bind P_t) = ∫ E_z[f(X_t)] dμ(z)`. -/
lemma integral_exactLaw_bind {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (t : ℝ≥0) {f : ℕ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) :
    ∫ y, f y ∂(μ.bind (exactLaw lam Λ t)) = ∫ z, ∫ y, f y ∂(exactLaw lam Λ t z) ∂μ :=
  integral_bind_of_abs_le μ (fun z => isProbabilityMeasure_exactLaw hΛ t z) hf

/-- `|E_x[f(X_t)]| ≤ M` for `|f| ≤ M`: the exact semigroup is a sup-norm contraction. -/
lemma abs_integral_exactLaw_le {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) {f : ℕ → ℝ}
    {M : ℝ} (hf : ∀ y, |f y| ≤ M) (t : ℝ≥0) (x : ℕ) : |∫ y, f y ∂(exactLaw lam Λ t x)| ≤ M := by
  have := isProbabilityMeasure_exactLaw hΛ t x
  exact abs_integral_le_of_abs_le_prob hf

/-- Telescoping the one-step errors (the argument behind a weak order, for Giles 2015, §8).  Let
`κ` be a Markov kernel on `ℕ` whose one-step weak error against the exact chain over the time `h`
is at most `δ sup|f|`, and let `μ_n` be its `n`-step laws from `x₀`.  Then
`|E_{x₀}[f(X_{nh})] − ∫ f dμ_n| ≤ n δ sup|f|`: `P_{nh} − κ^n = ∑_k κ^k (P_h − κ) P_{(n−1−k)h}`,
and `P_t` and `κ` are sup-norm contractions. -/
lemma exactLaw_steps_of_one_step {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (h : ℝ≥0)
    (x₀ : ℕ) {κ : ℕ → Measure ℕ} (hκ : ∀ x, IsProbabilityMeasure (κ x)) {δ : ℝ}
    (hδ : ∀ (f : ℕ → ℝ) (M : ℝ), (∀ y, |f y| ≤ M) → ∀ x,
      |∫ y, f y ∂(exactLaw lam Λ h x) - ∫ y, f y ∂(κ x)| ≤ δ * M)
    {μ : ℕ → Measure ℕ} (hμ0 : μ 0 = Measure.dirac x₀) (hμ : ∀ n, μ (n + 1) = (μ n).bind κ) :
    ∀ (n : ℕ) (f : ℕ → ℝ) (M : ℝ), (∀ y, |f y| ≤ M) →
      |∫ y, f y ∂(exactLaw lam Λ (n * h) x₀) - ∫ y, f y ∂(μ n)| ≤ n * (δ * M)
  | 0, f, M, hf => by
      rw [Nat.cast_zero, zero_mul, exactLaw_zero, hμ0, sub_self, abs_zero, Nat.cast_zero,
        zero_mul]
  | n + 1, f, M, hf => by
      have hP : ∀ k, IsProbabilityMeasure (μ k) := by
        intro k
        induction k with
        | zero => rw [hμ0]; infer_instance
        | succ k ih => exact ⟨by rw [hμ]; exact measure_univ_bind_of_discrete _ fun x => (hκ x).1⟩
      have hν := isProbabilityMeasure_exactLaw hΛ (n * h) x₀
      have hμn := hP n
      have hE : exactLaw lam Λ ((n + 1 : ℕ) * h) x₀ =
          (exactLaw lam Λ (n * h) x₀).bind (exactLaw lam Λ h) := by
        rw [← exactLaw_add hΛ, Nat.cast_succ, add_mul, one_mul]
      set G : ℕ → ℝ := fun z => ∫ y, f y ∂(exactLaw lam Λ h z) with hG
      set S : ℕ → ℝ := fun z => ∫ y, f y ∂(κ z) with hS_def
      have hGb : ∀ z, |G z| ≤ M := abs_integral_exactLaw_le hΛ hf h
      have hSb : ∀ z, |S z| ≤ M := fun z => by
        have := hκ z
        exact abs_integral_le_of_abs_le_prob hf
      have e1 : ∫ y, f y ∂(exactLaw lam Λ ((n + 1 : ℕ) * h) x₀) =
          ∫ z, G z ∂(exactLaw lam Λ (n * h) x₀) := by
        rw [hE]
        exact integral_exactLaw_bind hΛ _ h hf
      have e2 : ∫ y, f y ∂(μ (n + 1)) = ∫ z, S z ∂(μ n) := by
        rw [hμ]
        exact integral_bind_of_abs_le _ hκ hf
      have ih := exactLaw_steps_of_one_step hΛ h x₀ hκ hδ hμ0 hμ n G M hGb
      have hstep : |∫ z, G z ∂(μ n) - ∫ z, S z ∂(μ n)| ≤ δ * M := by
        rw [← integral_sub (integrable_of_abs_le_discrete hGb) (integrable_of_abs_le_discrete hSb)]
        exact abs_integral_le_of_abs_le_prob (hδ f M hf)
      rw [e1, e2]
      calc |∫ z, G z ∂(exactLaw lam Λ (n * h) x₀) - ∫ z, S z ∂(μ n)|
          ≤ |∫ z, G z ∂(exactLaw lam Λ (n * h) x₀) - ∫ z, G z ∂(μ n)| +
            |∫ z, G z ∂(μ n) - ∫ z, S z ∂(μ n)| := abs_sub_le _ _ _
        _ ≤ n * (δ * M) + δ * M := add_le_add ih hstep
        _ = ((n + 1 : ℕ) : ℝ) * (δ * M) := by
            push_cast
            ring

/-- **Tau-leaping has weak order one against the exact chain** (Giles 2015, §8, pp. 55–56:
tau-leaping, "approximating the reaction rate as being constant throughout the timestep", and the
claimed "`O(ε⁻²(log ε)²)` complexity", which by Theorem 1 needs a weak rate `α ≥ ½`; the weak rate
`α = 1` of tau-leaping is implicit in the paper).  For a propensity `0 ≤ λ ≤ Λ`, a payoff
`|Φ| ≤ M`, a final time `T` and `N ≥ 1` tau-leaping steps of size `T/N` from `x₀`,
`|E[Φ(x_N)] − E[Φ(X_T)]| ≤ 2Λ²T²M/N`, where `X` is the exact chain with jump rates `λ`
(`exactLaw`).  Deviation: bounded payoffs only (the paper does not fix a payoff class). -/
theorem tauLeaping_weak_error_exact {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) (T : ℝ≥0) (x₀ : ℕ) {N : ℕ} (hN : 0 < N) :
    |∫ x, Φ x ∂(tauChain lam (T / N) x₀ N) - ∫ x, Φ x ∂(exactLaw lam Λ T x₀)| ≤
      2 * (Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 * M / N := by
  have hN0 : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := exactLaw_steps_of_one_step hΛ (T / N) x₀ (κ := tauStep lam (T / N))
    (fun z => ⟨tauStep_univ lam (T / N) z⟩) (fun f M hf x => exactLaw_tauStep_le hΛ hf (T / N) x)
    (μ := tauChain lam (T / N) x₀) rfl (fun n => rfl) N Φ M hΦ
  rw [mul_div_cancel₀ T hN0, abs_sub_comm] at h
  refine h.trans (le_of_eq ?_)
  rw [NNReal.coe_div, NNReal.coe_natCast]
  field_simp

/-- Distinct naturals are at distance at least one: `1 ≤ |x − y|` for `x ≠ y`. -/
lemma one_le_abs_natCast_sub {x y : ℕ} (hxy : x ≠ y) : (1 : ℝ) ≤ |(x : ℝ) - y| := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    linarith
  · have : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith

/-- A bounded function on `ℕ` is Lipschitz: `|Φ x − Φ y| ≤ 2M |x − y|` for `|Φ| ≤ M`, since
distinct naturals are at distance at least one. -/
lemma abs_sub_le_two_mul_of_abs_le_nat {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) :
    ∀ x y : ℕ, |Φ x - Φ y| ≤ 2 * M * |(x : ℝ) - y| := by
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · have hM : 0 ≤ M := (abs_nonneg _).trans (hΦ x)
    calc |Φ x - Φ y| ≤ |Φ x| + |Φ y| := abs_sub _ _
      _ ≤ 2 * M * 1 := by linarith [hΦ x, hΦ y]
      _ ≤ 2 * M * |(x : ℝ) - y| :=
          mul_le_mul_of_nonneg_left (one_le_abs_natCast_sub hxy) (by linarith)

/-- A propensity with `0 ≤ λ ≤ Λ` on `ℕ` is `Λ`-Lipschitz, `|λ(x) − λ(y)| ≤ Λ |x − y|`: both values
lie in `[0, Λ]` and distinct naturals are at distance at least one.  So the Lipschitz hypothesis of
`tauLeaping_mlmc_theorem1` (Giles 2015, §8) follows from boundedness. -/
lemma abs_sub_le_mul_of_le_nat {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (x y : ℕ) :
    |(lam x : ℝ) - lam y| ≤ Λ * |(x : ℝ) - y| := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · have hx : (lam x : ℝ) ≤ Λ := by exact_mod_cast hΛ x
    have hy : (lam y : ℝ) ≤ Λ := by exact_mod_cast hΛ y
    have h0x := (lam x).coe_nonneg
    have h0y := (lam y).coe_nonneg
    calc |(lam x : ℝ) - lam y| ≤ Λ * 1 := by
          rw [mul_one, abs_le]
          constructor <;> linarith
      _ ≤ Λ * |(x : ℝ) - y| :=
          mul_le_mul_of_nonneg_left (one_le_abs_natCast_sub hxy) Λ.coe_nonneg

/-- **Theorem 1 for tau-leaping MLMC with the exact chain as target and no assumed weak rate**
(Giles 2015, §8, p. 56: the Poisson coupling "leads to a very effective multilevel algorithm with
a correction variance which is `O(h)`, leading to an `O(ε⁻²(log ε)²)` complexity").  Let the
propensity be bounded, `0 ≤ λ ≤ Λ` (on `ℕ` this implies the Lipschitz condition of
`tauLeaping_mlmc_theorem1`, with constant `Λ`: `abs_sub_le_mul_of_le_nat`), and the payoff
bounded, `|Φ| ≤ M`.  The Poisson-coupled tau-leaping estimator of `tauLeaping_mlmc_theorem1`
(level `ℓ`: `2^ℓ` steps of size `T 2^{−ℓ}`, independent samples of law `tauInputLaw`, cost `2^ℓ`
per sample) estimates `E[Φ(X_T)]` for the exact chain `X` (`exactLaw`): there is `c₄ > 0` such
that for every `0 < ε < e⁻¹` there are `L` and `N_ℓ ≥ 1` with a square-integrable error, mean square
error `< ε²`, and cost `∑_ℓ N_ℓ 2^ℓ ≤ c₄ ε⁻²(log ε)²`.  The weak rate `α = 1`, a hypothesis of
`tauLeaping_mlmc_theorem1`, is proved (`tauLeaping_weak_error_exact`).  Deviation: bounded
propensities and bounded payoffs only (a bounded payoff on `ℕ` is `2M`-Lipschitz, as
`tauLeaping_mlmc_theorem1` requires); the paper fixes neither class. -/
theorem tauLeaping_mlmc_exact {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) (T : ℝ≥0)
    (x₀ : ℕ) {Φ : ℕ → ℝ} {M : ℝ} (hΦ : ∀ x, |Φ x| ≤ M) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        Integrable (fun x => (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2)
            (Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀) ∧
        ∫ x, (∑ ℓ ∈ range (L + 1),
            blockMean (fineCoarseDiff (tauFine Φ) (tauCoarse Φ)) (fun p x => x p) ℓ (N ℓ) x -
              ∫ y, Φ y ∂(exactLaw lam Λ T x₀)) ^ 2
            ∂(Measure.infinitePi fun _ : ℕ × ℕ => tauInputLaw lam T x₀) < ε ^ 2 ∧
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * 2 ^ ℓ ≤ c₄ * (ε ^ (-2 : ℝ) * Real.log ε ^ 2) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΦ 0)
  refine tauLeaping_mlmc_theorem1 (abs_sub_le_mul_of_le_nat hΛ) hΛ T x₀
    (abs_sub_le_two_mul_of_abs_le_nat hΦ) _ (α := 1)
    (c₁ :=2 * (Λ : ℝ) ^ 2 * (T : ℝ) ^ 2 * M + 1) (by norm_num) (by positivity) fun ℓ => ?_
  have h := tauLeaping_weak_error_exact hΛ hΦ T x₀ (N := 2 ^ ℓ) (by positivity)
  have e1 : ((2 ^ ℓ : ℕ) : ℝ≥0) = 2 ^ ℓ := by push_cast; rfl
  have e2 : (2 : ℝ) ^ (-(1 * (ℓ : ℝ))) = ((2 ^ ℓ : ℕ) : ℝ)⁻¹ := by
    rw [one_mul, Real.rpow_neg zero_le_two, Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [e1] at h
  rw [e2, ← div_eq_mul_inv]
  refine h.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-! ### The exact law depends on the rates only -/

/-- If `|a − b| ≤ C/N` for every `N ≥ N₀`, `N > 0`, then `a = b`. -/
lemma eq_of_abs_sub_le_div_nat {a b C : ℝ} (N₀ : ℕ)
    (h : ∀ N : ℕ, N₀ ≤ N → 0 < N → |a - b| ≤ C / N) : a = b := by
  by_contra hne
  have hd : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max (C / |a - b|) 0) N₀)
  have hNr : (0 : ℝ) < N := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hN)
  have hN₀ : N₀ ≤ N := by exact_mod_cast ((le_max_right _ _).trans_lt hN).le
  have h1 := h N hN₀ (by exact_mod_cast hNr)
  have h2 : C / |a - b| < N := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hN)
  rw [div_lt_iff₀ hd] at h2
  rw [le_div_iff₀ hNr] at h1
  nlinarith

/-- Two finite measures on `ℕ` that give every function with `|f| ≤ 1` the same integral are equal
(test with the indicators of points). -/
lemma measure_ext_of_integral_bounded_nat {μ ν : Measure ℕ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : ℕ → ℝ, (∀ y, |f y| ≤ 1) → ∫ y, f y ∂μ = ∫ y, f y ∂ν) : μ = ν := by
  refine Measure.ext_of_singleton fun y => ?_
  have hb : ∀ z, |Set.indicator {y} (1 : ℕ → ℝ) z| ≤ 1 := fun z => by
    by_cases hz : z ∈ ({y} : Set ℕ) <;> simp [hz]
  have h := h _ hb
  rw [integral_indicator_one (measurableSet_singleton y),
    integral_indicator_one (measurableSet_singleton y)] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h

/-- **The exact law does not depend on the uniformisation rate** (Giles 2015, §8, p. 56: the exact
chain "updates the reaction rates after every single reaction", so its law depends on `λ` only).
If `λ ≤ Λ` and `λ ≤ Λ'`, then `exactLaw λ Λ t x = exactLaw λ Λ' t x`.  (This is Poisson thinning;
here it follows from `tauLeaping_weak_error_exact`, both laws being limits of the same
tau-leaping laws.) -/
theorem exactLaw_eq_of_bound {lam : ℕ → ℝ≥0} {Λ Λ' : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (hΛ' : ∀ x, lam x ≤ Λ') (t : ℝ≥0) (x : ℕ) : exactLaw lam Λ t x = exactLaw lam Λ' t x := by
  have hP := isProbabilityMeasure_exactLaw hΛ t x
  have hP' := isProbabilityMeasure_exactLaw hΛ' t x
  refine measure_ext_of_integral_bounded_nat fun f hf => eq_of_abs_sub_le_div_nat 0
    (C := 2 * (Λ : ℝ) ^ 2 * (t : ℝ) ^ 2 * 1 + 2 * (Λ' : ℝ) ^ 2 * (t : ℝ) ^ 2 * 1)
    fun N _ hN => ?_
  have h1 := tauLeaping_weak_error_exact hΛ hf t x hN
  have h2 := tauLeaping_weak_error_exact hΛ' hf t x hN
  rw [abs_sub_comm] at h1
  rw [add_div]
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)

/-- For the constant rate `λ ≡ Λ > 0` every clock tick is a jump: `J^n(y) = δ_{y+n}`. -/
lemma jumpPow_const {Λ : ℝ≥0} (hΛ : Λ ≠ 0) :
    ∀ n y, jumpPow (fun _ => Λ) Λ n y = Measure.dirac (y + n)
  | 0, y => by rw [jumpPow_zero, add_zero]
  | n + 1, y => by
      rw [jumpPow_succ, jumpPow_const hΛ n y, Measure.dirac_bind Measurable.of_discrete,
        jumpKernel, div_self hΛ, tsub_self, one_smul, zero_smul, add_zero, add_assoc]

/-- **With a constant propensity the exact chain is a Poisson process** (Giles 2015, §8, p. 55:
"`P(t)` represents a unit-rate Poisson random variable over time interval `[0, t]`").  For
`λ ≡ Λ`, `exactLaw λ Λ t x` is the law of `x + P(Λt)`; so for a constant propensity tau-leaping,
`x + P(hΛ)` per step, is exact. -/
theorem exactLaw_const (Λ t : ℝ≥0) (x : ℕ) :
    exactLaw (fun _ => Λ) Λ t x = (poissonMeasure (Λ * t)).map (x + ·) := by
  rcases eq_or_ne Λ 0 with rfl | hΛ
  · rw [zero_mul, poissonMeasure_zero, Measure.map_dirac' Measurable.of_discrete, add_zero,
      exactLaw, zero_mul, poissonMeasure_zero, Measure.dirac_bind Measurable.of_discrete,
      jumpPow_zero]
  · rw [exactLaw]
    simp_rw [jumpPow_const hΛ]
    exact Measure.bind_dirac_eq_map _ Measurable.of_discrete

/-! ### The generator and the Kolmogorov equations -/

/-- One tau-leaping step to first order (Giles 2015, §8): for `|f| ≤ M`,
`|E[f(x + P(hλ(x)))] − f(x) − hλ(x)(f(x + 1) − f(x))| ≤ 3(hλ(x))² M`. -/
lemma tauStep_expansion {f : ℕ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) (lam : ℕ → ℝ≥0) (h : ℝ≥0)
    (x : ℕ) : |∫ y, f y ∂(tauStep lam h x) - (f x + (h : ℝ) * lam x * (f (x + 1) - f x))| ≤
      3 * ((h : ℝ) * lam x) ^ 2 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  have hT : ∫ y, f y ∂(tauStep lam h x) = ∫ n, f (x + n) ∂(poissonMeasure (h * lam x)) := by
    rw [tauStep, integral_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable]
  obtain ⟨ρ, hρ, e⟩ := poisson_integral_split (h * lam x) fun n => hf (x + n)
  rw [hT, e, add_zero]
  simp only [NNReal.coe_mul] at hρ ⊢
  set r : ℝ := (h : ℝ) * lam x with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hE1 : 1 - r ≤ Real.exp (-r) := by linarith [Real.add_one_le_exp (-r)]
  have hE2 : Real.exp (-r) * (1 + r) ≤ 1 := by
    have h1 := Real.add_one_le_exp r
    have h2 : Real.exp r * Real.exp (-r) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-r)]
  have hc1 : |Real.exp (-r) - 1 + r| ≤ r ^ 2 := by
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith [pow_nonneg hr0 3]
  have hE3 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hr0)
  have hc2 : |r * (Real.exp (-r) - 1)| ≤ r * r := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) hr0
  have h3 : |ρ| ≤ M * r ^ 2 :=
    hρ.trans (mul_le_mul_of_nonneg_left (one_sub_exp_neg_sub_mul_le_sq r hr0) hM)
  have key : Real.exp (-r) * f x + Real.exp (-r) * r * f (x + 1) + ρ -
      (f x + r * (f (x + 1) - f x)) =
      (Real.exp (-r) - 1 + r) * f x + r * (Real.exp (-r) - 1) * f (x + 1) + ρ := by
    ring
  rw [key]
  have h1 : |(Real.exp (-r) - 1 + r) * f x| ≤ r ^ 2 * M := by
    rw [abs_mul]
    exact mul_le_mul hc1 (hf x) (abs_nonneg _) (sq_nonneg _)
  have h2 : |r * (Real.exp (-r) - 1) * f (x + 1)| ≤ r * r * M := by
    rw [abs_mul]
    exact mul_le_mul hc2 (hf _) (abs_nonneg _) (by positivity)
  calc |(Real.exp (-r) - 1 + r) * f x + r * (Real.exp (-r) - 1) * f (x + 1) + ρ|
      ≤ |(Real.exp (-r) - 1 + r) * f x| + |r * (Real.exp (-r) - 1) * f (x + 1)| + |ρ| :=
        abs_add_three _ _ _
    _ ≤ 3 * r ^ 2 * M := by nlinarith

/-- **The generator of the exact chain** (Giles 2015, §8, p. 55: "`λ(x_n)` is the reaction rate (or
propensity function)", and each reaction moves `x` to `x + 1`).  For `λ ≤ Λ` and `|f| ≤ M`,
`|E_x[f(X_t)] − f(x) − tλ(x)(f(x + 1) − f(x))| ≤ 5(Λt)² M`: the exact chain has the generator
`Gf(x) = λ(x)(f(x + 1) − f(x))`, uniformly in `x`. -/
theorem exactLaw_generator {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) {f : ℕ → ℝ}
    {M : ℝ} (hf : ∀ y, |f y| ≤ M) (t : ℝ≥0) (x : ℕ) :
    |∫ y, f y ∂(exactLaw lam Λ t x) - (f x + (t : ℝ) * lam x * (f (x + 1) - f x))| ≤
      5 * ((Λ : ℝ) * t) ^ 2 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  have h1 := exactLaw_tauStep_le hΛ hf t x
  have h2 := tauStep_expansion hf lam t x
  have hr : ((t : ℝ) * lam x) ^ 2 ≤ ((Λ : ℝ) * t) ^ 2 := by
    have : (t : ℝ) * lam x ≤ (Λ : ℝ) * t := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hΛ x) t.coe_nonneg
    exact pow_le_pow_left₀ (by positivity) this 2
  calc |∫ y, f y ∂(exactLaw lam Λ t x) - (f x + (t : ℝ) * lam x * (f (x + 1) - f x))|
      ≤ |∫ y, f y ∂(exactLaw lam Λ t x) - ∫ y, f y ∂(tauStep lam t x)| +
        |∫ y, f y ∂(tauStep lam t x) - (f x + (t : ℝ) * lam x * (f (x + 1) - f x))| :=
        abs_sub_le _ _ _
    _ ≤ 2 * ((Λ : ℝ) * t) ^ 2 * M + 3 * ((t : ℝ) * lam x) ^ 2 * M := add_le_add h1 h2
    _ ≤ 5 * ((Λ : ℝ) * t) ^ 2 * M := by nlinarith

/-- The backward equation over a short time `s` (Giles 2015, §8), quantitatively: with
`P_t f(x) = E_x[f(X_t)]`, `|P_{t+s} f(x) − P_t f(x) − sλ(x)(P_t f(x + 1) − P_t f(x))| ≤
5(Λs)² M`. -/
lemma exactLaw_backward_step {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) {f : ℕ → ℝ}
    {M : ℝ} (hf : ∀ y, |f y| ≤ M) (t s : ℝ≥0) (x : ℕ) :
    |∫ y, f y ∂(exactLaw lam Λ (t + s) x) - ∫ y, f y ∂(exactLaw lam Λ t x) -
        s * (lam x * (∫ y, f y ∂(exactLaw lam Λ t (x + 1)) - ∫ y, f y ∂(exactLaw lam Λ t x)))| ≤
      5 * ((Λ : ℝ) * s) ^ 2 * M := by
  have hs := isProbabilityMeasure_exactLaw hΛ s x
  have e : ∫ y, f y ∂(exactLaw lam Λ (t + s) x) =
      ∫ z, ∫ y, f y ∂(exactLaw lam Λ t z) ∂(exactLaw lam Λ s x) := by
    rw [add_comm, exactLaw_add hΛ]
    exact integral_exactLaw_bind hΛ _ t hf
  have h := exactLaw_generator hΛ (abs_integral_exactLaw_le hΛ hf t) s x
  rw [e]
  convert h using 2
  ring

/-- `t ↦ E_x[f(X_t)]` is Lipschitz on steps `s ≤ 1` (Giles 2015, §8):
`|P_{t+s} f(x) − P_t f(x)| ≤ (2ΛM + 5Λ²M) s`. -/
lemma exactLaw_time_lipschitz {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) {f : ℕ → ℝ}
    {M : ℝ} (hf : ∀ y, |f y| ≤ M) (t s : ℝ≥0) (hs : (s : ℝ) ≤ 1) (x : ℕ) :
    |∫ y, f y ∂(exactLaw lam Λ (t + s) x) - ∫ y, f y ∂(exactLaw lam Λ t x)| ≤
      (2 * Λ * M + 5 * (Λ : ℝ) ^ 2 * M) * s := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  have h := exactLaw_backward_step hΛ hf t s x
  have hs0 : (0 : ℝ) ≤ s := s.coe_nonneg
  have hl : (lam x : ℝ) ≤ Λ := by exact_mod_cast hΛ x
  have hl0 : (0 : ℝ) ≤ lam x := (lam x).coe_nonneg
  have h1 := abs_integral_exactLaw_le hΛ hf t (x + 1)
  have h2 := abs_integral_exactLaw_le hΛ hf t x
  have h3 : |(s : ℝ) * (lam x * (∫ y, f y ∂(exactLaw lam Λ t (x + 1)) -
      ∫ y, f y ∂(exactLaw lam Λ t x)))| ≤ s * (Λ * (2 * M)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg hl0]
    refine mul_le_mul_of_nonneg_left (mul_le_mul hl ?_ (abs_nonneg _) (by positivity)) hs0
    exact (abs_sub _ _).trans (by linarith)
  have h4 : 5 * ((Λ : ℝ) * s) ^ 2 * M ≤ 5 * (Λ : ℝ) ^ 2 * M * s := by
    have : (s : ℝ) ^ 2 ≤ s := by nlinarith
    have hΛ0 : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
    calc 5 * ((Λ : ℝ) * s) ^ 2 * M = 5 * (Λ : ℝ) ^ 2 * M * (s : ℝ) ^ 2 := by ring
      _ ≤ 5 * (Λ : ℝ) ^ 2 * M * s := mul_le_mul_of_nonneg_left this (by positivity)
  have := abs_sub_abs_le_abs_sub
    (∫ y, f y ∂(exactLaw lam Λ (t + s) x) - ∫ y, f y ∂(exactLaw lam Λ t x))
    ((s : ℝ) * (lam x * (∫ y, f y ∂(exactLaw lam Λ t (x + 1)) - ∫ y, f y ∂(exactLaw lam Λ t x))))
  nlinarith

/-- The forward equation over a short time `s` (Giles 2015, §8), quantitatively:
`|P_{t+s} f(x) − P_t f(x) − s E_x[(Gf)(X_t)]| ≤ 5(Λs)² M` with `Gf(z) = λ(z)(f(z + 1) − f(z))`. -/
lemma exactLaw_forward_step {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ) {f : ℕ → ℝ}
    {M : ℝ} (hf : ∀ y, |f y| ≤ M) (t s : ℝ≥0) (x : ℕ) :
    |∫ y, f y ∂(exactLaw lam Λ (t + s) x) - ∫ y, f y ∂(exactLaw lam Λ t x) -
        s * ∫ z, (lam z : ℝ) * (f (z + 1) - f z) ∂(exactLaw lam Λ t x)| ≤
      5 * ((Λ : ℝ) * s) ^ 2 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  have ht := isProbabilityMeasure_exactLaw hΛ t x
  have hPs : ∀ z, |∫ y, f y ∂(exactLaw lam Λ s z)| ≤ M := abs_integral_exactLaw_le hΛ hf s
  have hG : ∀ z, |(lam z : ℝ) * (f (z + 1) - f z)| ≤ Λ * (2 * M) := fun z => by
    rw [abs_mul, NNReal.abs_eq]
    exact mul_le_mul (by exact_mod_cast hΛ z) ((abs_sub _ _).trans (by linarith [hf z, hf (z + 1)]))
      (abs_nonneg _) Λ.coe_nonneg
  have e : ∫ y, f y ∂(exactLaw lam Λ (t + s) x) =
      ∫ z, ∫ y, f y ∂(exactLaw lam Λ s z) ∂(exactLaw lam Λ t x) := by
    rw [exactLaw_add hΛ]
    exact integral_exactLaw_bind hΛ _ s hf
  have hR : ∀ z, |∫ y, f y ∂(exactLaw lam Λ s z) - f z - s * ((lam z : ℝ) * (f (z + 1) - f z))| ≤
      5 * ((Λ : ℝ) * s) ^ 2 * M := fun z => by
    have h := exactLaw_generator hΛ hf s z
    convert h using 2
    ring
  have hint1 := integrable_of_abs_le_discrete (μ := exactLaw lam Λ t x) hPs
  have hint2 := integrable_of_abs_le_discrete (μ := exactLaw lam Λ t x) hf
  have hint3 := integrable_of_abs_le_discrete (μ := exactLaw lam Λ t x) hG
  have e2 : ∫ z, (∫ y, f y ∂(exactLaw lam Λ s z) - f z -
      s * ((lam z : ℝ) * (f (z + 1) - f z))) ∂(exactLaw lam Λ t x) =
      ∫ z, ∫ y, f y ∂(exactLaw lam Λ s z) ∂(exactLaw lam Λ t x) -
        ∫ y, f y ∂(exactLaw lam Λ t x) -
        s * ∫ z, (lam z : ℝ) * (f (z + 1) - f z) ∂(exactLaw lam Λ t x) := by
    have hint12 : Integrable (fun z => ∫ y, f y ∂(exactLaw lam Λ s z) - f z)
        (exactLaw lam Λ t x) := hint1.sub hint2
    rw [integral_sub hint12 (hint3.const_mul _), integral_sub hint1 hint2, integral_const_mul]
  rw [e, ← e2]
  exact abs_integral_le_of_abs_le_prob hR

/-- A function of time with a uniform second-order expansion from the right,
`|u(τ + s) − u(τ) − s v(τ)| ≤ C₁ s²`, and a Lipschitz slope, `|v(τ + s) − v(τ)| ≤ C₂ s` for
`s ≤ 1`, has the derivative `v(t)` at every `t > 0` (as a function of `t ∈ ℝ`, through
`t ↦ t.toNNReal`). -/
lemma hasDerivAt_toNNReal_of_step_bounds {u v : ℝ≥0 → ℝ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hu : ∀ τ s : ℝ≥0, |u (τ + s) - u τ - s * v τ| ≤ C₁ * (s : ℝ) ^ 2)
    (hv : ∀ τ s : ℝ≥0, (s : ℝ) ≤ 1 → |v (τ + s) - v τ| ≤ C₂ * s) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t' : ℝ => u t'.toNNReal) (v t.toNNReal) t := by
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_sub_sub t one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C₁ + C₂) ?_
  have hδ : 0 < min t 1 := lt_min ht one_pos
  filter_upwards [Metric.ball_mem_nhds t hδ] with t' ht'
  rw [Metric.mem_ball, Real.dist_eq] at ht'
  have hlt1 : |t' - t| < 1 := ht'.trans_le (min_le_right _ _)
  have hltt : |t' - t| < t := ht'.trans_le (min_le_left _ _)
  rw [Real.norm_eq_abs, smul_eq_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  have hsq := sq_abs (t' - t)
  rcases le_total t t' with h | h
  · have e : t'.toNNReal = t.toNNReal + (t' - t).toNNReal := by
      rw [← Real.toNNReal_add ht.le (sub_nonneg.2 h), add_sub_cancel]
    have hs' : (((t' - t).toNNReal : ℝ≥0) : ℝ) = t' - t := Real.coe_toNNReal _ (sub_nonneg.2 h)
    have h1 := hu t.toNNReal (t' - t).toNNReal
    rw [hs'] at h1
    rw [e]
    nlinarith [sq_nonneg (t' - t)]
  · have ht'0 : 0 ≤ t' := by
      have := (abs_sub_lt_iff.1 hltt).2
      linarith
    have e : t.toNNReal = t'.toNNReal + (t - t').toNNReal := by
      rw [← Real.toNNReal_add ht'0 (sub_nonneg.2 h), add_sub_cancel]
    have hs' : (((t - t').toNNReal : ℝ≥0) : ℝ) = t - t' := Real.coe_toNNReal _ (sub_nonneg.2 h)
    have hs1 : (((t - t').toNNReal : ℝ≥0) : ℝ) ≤ 1 := by
      rw [hs']
      have := (abs_sub_lt_iff.1 hlt1).2
      linarith
    have h1 := hu t'.toNNReal (t - t').toNNReal
    have h2 := hv t'.toNNReal (t - t').toNNReal hs1
    rw [hs'] at h1 h2
    rw [e]
    set τ := t'.toNNReal
    set σ := (t - t').toNNReal
    have key : u τ - u (τ + σ) - (t' - t) * v (τ + σ) =
        -(u (τ + σ) - u τ - (t - t') * v τ) + (t - t') * (v (τ + σ) - v τ) := by
      ring
    have hd : 0 ≤ t - t' := sub_nonneg.2 h
    rw [key]
    calc |-(u (τ + σ) - u τ - (t - t') * v τ) + (t - t') * (v (τ + σ) - v τ)|
        ≤ |u (τ + σ) - u τ - (t - t') * v τ| + |(t - t') * (v (τ + σ) - v τ)| := by
          rw [← abs_neg (u (τ + σ) - u τ - (t - t') * v τ)]
          exact abs_add_le _ _
      _ ≤ C₁ * (t - t') ^ 2 + (t - t') * (C₂ * (t - t')) := by
          rw [abs_mul, abs_of_nonneg hd]
          exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hd)
      _ = (C₁ + C₂) * |t' - t| ^ 2 := by
          rw [hsq]
          ring

/-- **The generator as the right derivative at time `0`** (Giles 2015, §8, p. 55: "`λ(x_n)` is the
reaction rate (or propensity function)").  For `λ ≤ Λ` and `|f| ≤ M`, the function
`s ↦ E_x[f(X_{max(s, 0)})]` has the right derivative `λ(x)(f(x + 1) − f(x))` at `0` (within
`[0, ∞)`): Kolmogorov's backward and forward equations (`exactLaw_backward_equation`,
`exactLaw_forward_equation`, stated for `t > 0`) also hold at `t = 0`, where `X_0 = x`. -/
theorem exactLaw_hasDerivWithinAt_zero {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    {f : ℕ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) (x : ℕ) :
    HasDerivWithinAt (fun s : ℝ => ∫ y, f y ∂(exactLaw lam Λ s.toNNReal x))
      (lam x * (f (x + 1) - f x)) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO ?_
    ((Asymptotics.isLittleO_pow_sub_sub (0 : ℝ) one_lt_two).mono nhdsWithin_le_nhds)
  refine Asymptotics.IsBigO.of_bound (5 * (Λ : ℝ) ^ 2 * M) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ici] at hs
  have h := exactLaw_generator hΛ hf s.toNNReal x
  rw [Real.coe_toNNReal _ hs] at h
  have e : ∫ y, f y ∂(exactLaw lam Λ s.toNNReal x) -
      ∫ y, f y ∂(exactLaw lam Λ (0 : ℝ).toNNReal x) - (s - 0) • ((lam x : ℝ) * (f (x + 1) - f x)) =
      ∫ y, f y ∂(exactLaw lam Λ s.toNNReal x) - (f x + s * lam x * (f (x + 1) - f x)) := by
    rw [Real.toNNReal_zero, exactLaw_zero, integral_dirac, smul_eq_mul]
    ring
  rw [e, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, sub_zero,
    abs_of_nonneg hs]
  exact h.trans (le_of_eq (by ring))

/-- **Kolmogorov's backward equation for the exact chain** (Giles 2015, §8, p. 55: "`λ(x_n)` is the
reaction rate (or propensity function)").  For `λ ≤ Λ`, `|f| ≤ M` and `t > 0`,
`d/dt E_x[f(X_t)] = λ(x)(E_{x+1}[f(X_t)] − E_x[f(X_t)])` (a two-sided derivative of
`s ↦ E_x[f(X_{max(s, 0)})]`).  At `t = 0` the right derivative is `λ(x)(f(x + 1) − f(x))`, the
generator (`exactLaw_hasDerivWithinAt_zero`, quantitatively `exactLaw_generator`; `P_0 = id` by
`exactLaw_zero`), so the equation holds on `[0, ∞)` with a one-sided derivative at `0`. -/
theorem exactLaw_backward_equation {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    {f : ℕ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) (x : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ y, f y ∂(exactLaw lam Λ s.toNNReal x))
      (lam x * (∫ y, f y ∂(exactLaw lam Λ t.toNNReal (x + 1)) -
        ∫ y, f y ∂(exactLaw lam Λ t.toNNReal x))) t := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  have hΛ0 : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
  refine hasDerivAt_toNNReal_of_step_bounds (u := fun τ => ∫ y, f y ∂(exactLaw lam Λ τ x))
    (v := fun τ => lam x * (∫ y, f y ∂(exactLaw lam Λ τ (x + 1)) -
      ∫ y, f y ∂(exactLaw lam Λ τ x)))
    (C₁ := 5 * (Λ : ℝ) ^ 2 * M) (C₂ := Λ * (2 * (2 * Λ * M + 5 * (Λ : ℝ) ^ 2 * M)))
    (by positivity) (by positivity) (fun τ s => ?_) (fun τ s hs => ?_) ht
  · refine (exactLaw_backward_step hΛ hf τ s x).trans (le_of_eq ?_)
    ring
  · have h1 := exactLaw_time_lipschitz hΛ hf τ s hs (x + 1)
    have h2 := exactLaw_time_lipschitz hΛ hf τ s hs x
    have hl : (lam x : ℝ) ≤ Λ := by exact_mod_cast hΛ x
    have e : (lam x : ℝ) * (∫ y, f y ∂(exactLaw lam Λ (τ + s) (x + 1)) -
        ∫ y, f y ∂(exactLaw lam Λ (τ + s) x)) - lam x * (∫ y, f y ∂(exactLaw lam Λ τ (x + 1)) -
        ∫ y, f y ∂(exactLaw lam Λ τ x)) =
        lam x * ((∫ y, f y ∂(exactLaw lam Λ (τ + s) (x + 1)) -
          ∫ y, f y ∂(exactLaw lam Λ τ (x + 1))) -
          (∫ y, f y ∂(exactLaw lam Λ (τ + s) x) - ∫ y, f y ∂(exactLaw lam Λ τ x))) := by
      ring
    rw [e, abs_mul, NNReal.abs_eq]
    calc (lam x : ℝ) * |(∫ y, f y ∂(exactLaw lam Λ (τ + s) (x + 1)) -
          ∫ y, f y ∂(exactLaw lam Λ τ (x + 1))) -
          (∫ y, f y ∂(exactLaw lam Λ (τ + s) x) - ∫ y, f y ∂(exactLaw lam Λ τ x))|
        ≤ Λ * ((2 * Λ * M + 5 * (Λ : ℝ) ^ 2 * M) * s + (2 * Λ * M + 5 * (Λ : ℝ) ^ 2 * M) * s) :=
          mul_le_mul hl ((abs_sub _ _).trans (add_le_add h1 h2)) (abs_nonneg _) hΛ0
      _ = Λ * (2 * (2 * Λ * M + 5 * (Λ : ℝ) ^ 2 * M)) * s := by ring

/-- **Kolmogorov's forward equation for the exact chain, weak form** (Giles 2015, §8, p. 55: "When
there is just one chemical reaction, … `λ(x_n)` is the reaction rate (or propensity function)").
For `λ ≤ Λ`, `|f| ≤ M` and `t > 0`, `d/dt E_x[f(X_t)] = E_x[λ(X_t)(f(X_t + 1) − f(X_t))]` (a
two-sided derivative of `s ↦ E_x[f(X_{max(s, 0)})]`).  At `t = 0` the right side is
`λ(x)(f(x + 1) − f(x))` and the right derivative is given by `exactLaw_hasDerivWithinAt_zero`
(quantitatively by `exactLaw_generator`, with `exactLaw_zero`). -/
theorem exactLaw_forward_equation {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    {f : ℕ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) (x : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ y, f y ∂(exactLaw lam Λ s.toNNReal x))
      (∫ z, (lam z : ℝ) * (f (z + 1) - f z) ∂(exactLaw lam Λ t.toNNReal x)) t := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  have hΛ0 : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
  have hG : ∀ z, |(lam z : ℝ) * (f (z + 1) - f z)| ≤ Λ * (2 * M) := fun z => by
    rw [abs_mul, NNReal.abs_eq]
    exact mul_le_mul (by exact_mod_cast hΛ z) ((abs_sub _ _).trans (by linarith [hf z, hf (z + 1)]))
      (abs_nonneg _) hΛ0
  refine hasDerivAt_toNNReal_of_step_bounds (u := fun τ => ∫ y, f y ∂(exactLaw lam Λ τ x))
    (v := fun τ => ∫ z, (lam z : ℝ) * (f (z + 1) - f z) ∂(exactLaw lam Λ τ x))
    (C₁ := 5 * (Λ : ℝ) ^ 2 * M)
    (C₂ := 2 * Λ * (Λ * (2 * M)) + 5 * (Λ : ℝ) ^ 2 * (Λ * (2 * M)))
    (by positivity) (by positivity) (fun τ s => ?_) (fun τ s hs => ?_) ht
  · refine (exactLaw_forward_step hΛ hf τ s x).trans (le_of_eq ?_)
    ring
  · exact exactLaw_time_lipschitz hΛ hG τ s hs x

/-- **The master equation of the exact chain** (Kolmogorov's forward equation for the transition
probabilities; Giles 2015, §8, p. 56: "the exact Stochastic Simulation Algorithm developed by
(Gillespie 1976) which updates the reaction rates after every single reaction"; one reaction with
propensity `λ`, each reaction moving `x` to `x + 1`).  For `λ ≤ Λ` and `t > 0`,
`p_t(y) = P_x(X_t = y)` satisfies `p_t'(0) = −λ(0) p_t(0)` and, for every `y`,
`p_t'(y + 1) = λ(y) p_t(y) − λ(y + 1) p_t(y + 1)`; with `p_0 = δ_x` (`exactLaw_zero`) these are
the equations of the pure-birth chain with rates `λ`.  Stated for `t > 0` (two-sided derivatives
of `s ↦ p_{max(s, 0)}(y)`), as `exactLaw_forward_equation`. -/
theorem exactLaw_master_equation {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    (x : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (exactLaw lam Λ s.toNNReal x).real {0})
        (-(lam 0 * (exactLaw lam Λ t.toNNReal x).real {0})) t ∧
      ∀ y : ℕ, HasDerivAt (fun s : ℝ => (exactLaw lam Λ s.toNNReal x).real {y + 1})
        (lam y * (exactLaw lam Λ t.toNNReal x).real {y} -
          lam (y + 1) * (exactLaw lam Λ t.toNNReal x).real {y + 1}) t := by
  have hb : ∀ y' z : ℕ, |Set.indicator {y'} (1 : ℕ → ℝ) z| ≤ 1 := fun y' z => by
    by_cases hz : z ∈ ({y'} : Set ℕ) <;> simp [hz]
  have hF : ∀ y' : ℕ, (fun s : ℝ => (exactLaw lam Λ s.toNNReal x).real {y'}) =
      fun s => ∫ z, Set.indicator {y'} (1 : ℕ → ℝ) z ∂(exactLaw lam Λ s.toNNReal x) :=
    fun y' => funext fun s => (integral_indicator_one (measurableSet_singleton y')).symm
  constructor
  · have e : (fun z : ℕ => (lam z : ℝ) * (Set.indicator {0} (1 : ℕ → ℝ) (z + 1) -
        Set.indicator {0} (1 : ℕ → ℝ) z)) =
        fun z => -Set.indicator {0} (fun _ => (lam 0 : ℝ)) z := by
      funext z
      rcases eq_or_ne z 0 with rfl | hz
      · simp
      · simp [hz]
    rw [hF]
    refine (exactLaw_forward_equation hΛ (hb 0) x ht).congr_deriv ?_
    rw [e, integral_neg, integral_indicator_const _ (measurableSet_singleton 0), smul_eq_mul,
      mul_comm]
  · intro y
    have e : (fun z : ℕ => (lam z : ℝ) * (Set.indicator {y + 1} (1 : ℕ → ℝ) (z + 1) -
        Set.indicator {y + 1} (1 : ℕ → ℝ) z)) =
        fun z => Set.indicator {y} (fun _ => (lam y : ℝ)) z -
          Set.indicator {y + 1} (fun _ => (lam (y + 1) : ℝ)) z := by
      funext z
      rcases eq_or_ne z y with rfl | hzy
      · simp
      · rcases eq_or_ne z (y + 1) with rfl | hzy1
        · simp
        · simp [hzy, hzy1]
    rw [hF]
    refine (exactLaw_forward_equation hΛ (hb (y + 1)) x ht).congr_deriv ?_
    have := isProbabilityMeasure_exactLaw hΛ t.toNNReal x
    rw [e, integral_sub (integrable_of_abs_le_discrete (M := lam y) fun z => by
        by_cases hz : z ∈ ({y} : Set ℕ) <;> simp [hz])
      (integrable_of_abs_le_discrete (M := lam (y + 1)) fun z => by
        by_cases hz : z ∈ ({y + 1} : Set ℕ) <;> simp [hz]),
      integral_indicator_const _ (measurableSet_singleton y),
      integral_indicator_const _ (measurableSet_singleton (y + 1)), smul_eq_mul, smul_eq_mul,
      mul_comm, mul_comm ((exactLaw lam Λ t.toNNReal x).real {y + 1})]

/-- **The exact law is the only Markov semigroup with the generator of the chain** (Giles 2015, §8,
p. 55: "Anderson and Higham (2012) developed a very interesting application of MLMC to
continuous-time Markov Chain simulation").  Let `Q_t(x)` be probability measures on `ℕ` with
`Q_{s+t}(x) = Q_s(x).bind Q_t` and `|∫ f dQ_t(x) − f(x) − tλ(x)(f(x + 1) − f(x))| ≤ C t² M` for
`|f| ≤ M` and `t ≤ 1`.  Then `Q_t(x) = exactLaw λ Λ t x` for every `Λ ≥ sup λ`: `exactLaw` is the
continuous-time Markov chain with jump rates `λ`, whatever construction of it one prefers.
Deviation: the generator condition is the uniform quantitative `O(t²)` expansion of
`exactLaw_generator`, not merely the derivative at `0`; the classical uniqueness of every
solution of Kolmogorov's equations with bounded rates is not stated. -/
theorem exactLaw_unique {lam : ℕ → ℝ≥0} {Λ : ℝ≥0} (hΛ : ∀ x, lam x ≤ Λ)
    {Q : ℝ≥0 → ℕ → Measure ℕ} (hQ : ∀ t x, IsProbabilityMeasure (Q t x))
    (hQadd : ∀ s t x, Q (s + t) x = (Q s x).bind (Q t)) {C : ℝ}
    (hgen : ∀ (f : ℕ → ℝ) (M : ℝ), (∀ y, |f y| ≤ M) → ∀ (t : ℝ≥0) (x : ℕ), (t : ℝ) ≤ 1 →
      |∫ y, f y ∂(Q t x) - (f x + (t : ℝ) * lam x * (f (x + 1) - f x))| ≤ C * (t : ℝ) ^ 2 * M)
    (t : ℝ≥0) (x : ℕ) : Q t x = exactLaw lam Λ t x := by
  have hQ0 : ∀ y, Q 0 y = Measure.dirac y := fun y => by
    have := hQ 0 y
    refine measure_ext_of_integral_bounded_nat fun f hf => ?_
    have h := hgen f 1 hf 0 y zero_le_one
    rw [NNReal.coe_zero, zero_mul, zero_mul, add_zero, zero_pow two_ne_zero, mul_zero, zero_mul,
      abs_nonpos_iff, sub_eq_zero] at h
    rw [h, integral_dirac]
  have := hQ t x
  have := isProbabilityMeasure_exactLaw hΛ t x
  refine measure_ext_of_integral_bounded_nat fun f hf => eq_of_abs_sub_le_div_nat ⌈(t : ℝ)⌉₊
    (C := (5 * (Λ : ℝ) ^ 2 + C) * (t : ℝ) ^ 2) fun N hNt hN => ?_
  have hN0 : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : ((t / N : ℝ≥0) : ℝ) = t / N := by rw [NNReal.coe_div, NNReal.coe_natCast]
  have hh1 : ((t / N : ℝ≥0) : ℝ) ≤ 1 := by
    rw [hh, div_le_one hNr]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hNt)
  have hone : ∀ (g : ℕ → ℝ) (M : ℝ), (∀ y, |g y| ≤ M) → ∀ y,
      |∫ z, g z ∂(exactLaw lam Λ (t / N) y) - ∫ z, g z ∂(Q (t / N) y)| ≤
        (5 * ((Λ : ℝ) * (t / N : ℝ≥0)) ^ 2 + C * ((t / N : ℝ≥0) : ℝ) ^ 2) * M := by
    intro g M hg y
    have h1 := exactLaw_generator hΛ hg (t / N) y
    have h2 := hgen g M hg (t / N) y hh1
    rw [abs_sub_comm] at h2
    calc |∫ z, g z ∂(exactLaw lam Λ (t / N) y) - ∫ z, g z ∂(Q (t / N) y)|
        ≤ |∫ z, g z ∂(exactLaw lam Λ (t / N) y) -
            (g y + ((t / N : ℝ≥0) : ℝ) * lam y * (g (y + 1) - g y))| +
          |(g y + ((t / N : ℝ≥0) : ℝ) * lam y * (g (y + 1) - g y)) - ∫ z, g z ∂(Q (t / N) y)| :=
          abs_sub_le _ _ _
      _ ≤ 5 * ((Λ : ℝ) * (t / N : ℝ≥0)) ^ 2 * M + C * ((t / N : ℝ≥0) : ℝ) ^ 2 * M :=
          add_le_add h1 h2
      _ = (5 * ((Λ : ℝ) * (t / N : ℝ≥0)) ^ 2 + C * ((t / N : ℝ≥0) : ℝ) ^ 2) * M := by ring
  have h := exactLaw_steps_of_one_step hΛ (t / N) x (κ := Q (t / N)) (hQ _) hone
    (μ := fun n => Q (n * (t / N)) x) (by rw [Nat.cast_zero, zero_mul, hQ0])
    (fun n => by rw [Nat.cast_succ, add_mul, one_mul, hQadd]) N f 1 hf
  rw [mul_div_cancel₀ t hN0, abs_sub_comm] at h
  refine h.trans (le_of_eq ?_)
  rw [hh]
  field_simp

end MLMC
