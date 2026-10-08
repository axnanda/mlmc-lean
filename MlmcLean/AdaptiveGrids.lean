import MlmcLean.BrownianPaths
import MlmcLean.PoissonGrids
import MlmcLean.NestedMLMC
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Path-dependent (adaptive) time steps on a fixed base grid (Giles 2015, §5.6 and §8)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §5.6 "Stiff and
highly nonlinear SDEs" (pp. 43–45, Figure 5.9 and Algorithm 3), §8 "Continuous-time Markov
chains" (p. 56) and §2.1, (2.4) (p. 8).  Line numbers refer to the text `docs/giles2015.txt`.

§5.6, p. 44, lines 1917–1930: "Instead of the time steps on one level being a subdivision of those
on the level above, it uses a completely independent adaptation on each level of refinement, with
an adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)`, where `H(S)` is independent of level. This
results in timesteps which are not naturally nested. It may appear that this would cause
difficulties in the MLMC implementation, but Figure 5.9 tries to illustrate that it does not. The
underlying Brownian path needs to be sampled at a set of times which are the union of the
simulation times used by the coarse and fine path. The independent Brownian increments can be
simulated for each time interval, and summed to give `W(t)` at the required times."  §8, p. 56,
lines 2442–2447: "The non-nested adaptive timestepping approach described in Section 5.6 for SDEs
is equally applicable in this setting … with Poisson variates for each time interval instead of
Brownian increments."

**The model: steps on a fixed base grid.**  All step sizes are multiples of a fixed base spacing
`δ` (e.g. `δ = 2^{−m}T`), and the noise is a sequence of independent base increments
`ξ_0, ξ_1, …`, one per base interval: `N(0, δ)` for Brownian motion, Poisson counts `P(λδ)` for §8.
The path `x_0, x_1, …` of the scheme lives in any measurable space `X`; `y_k = (x_{min(i,k)})_i`
is the path stopped at step `k` (`extendPath`).  Before step `k` the scheme has used the base
increments `ξ_i`, `i < τ_k`.  A predictable rule chooses the number of base intervals of step `k`
from the path so far, `n_k = ν_k(y_k)`; the increment of the step is the sum of the base
increments over it, `ΔW_k = ∑_{τ_k ≤ i < τ_k + n_k} ξ_i` (`adaptiveIncr`); then
`x_{k+1} = G_k(y_k, ΔW_k)` and `τ_{k+1} = τ_k + n_k` (`adaptivePath`, `adaptiveSeq`).  The fine and
the coarse path of an MLMC sample are two such paths with their own rules, computed from the same
base increments: the union of their time grids lies in the base grid, and summing the base
increments gives `W(t)` at all the times either path needs.

**Method: discrete-time conditioning, no Brownian motion.**  The engine
(`map_prod_eq_bind_prod_of_fresh`, `map_noiseChain`): if one step maps (state, remaining noise) to
(new state, remaining noise) so that, for every fixed state, the new state is independent of the
remaining noise and the remaining noise has its original law, then after `k` steps the joint law
of (state, remaining noise) is (law of a Markov chain) ⊗ (law of the noise).  For i.i.d. base
increments the first `n` of them (their sum, or the whole block) are independent of the others,
which are again i.i.d. (`map_blockSum_shiftSeq`, `map_usedSeq_shiftSeq`), for every `n`, hence
also for the predictable `n_k`.

**Results.**
* `map_adaptivePath_prod`: after `k` steps the unused base increments `(ξ_{τ_k + i})_i` are
  independent of the path so far and again i.i.d.; `map_adaptivePath`: the path stopped at step `k`
  has the law `adaptiveLaw` of the scheme in which the `k`-th increment, given the path so far, is
  drawn from the law of a sum of `ν_k(y_k)` base increments.
* (1) `adaptiveIncr_condLaw_gaussian`, `adaptiveIncr_condDistrib_gaussian`: **given the path so
  far, the increment over the chosen step is `N(0, n_k δ)`**; `adaptivePath_law_gaussian`,
  `freshPath_law_gaussian`: the path stopped at step `k` has the same law whether it is driven by
  the summed base increments or by fresh increments `√(h_k) Z_k`; `adaptiveSeq_law_eq_fresh`: the
  same for the law of the whole path; `adaptivePairs_law_eq_fresh`: for the sequence of
  (step, increment) pairs; `adaptiveEM_law_eq_freshEM`: for the adaptive Euler–Maruyama path
  `(t_k, Ŝ_k)`.
* The whole history: in `histPath` the rules and the updates may depend on the whole past
  `(y_k, τ_k, H_k)`, where `H_k = (ξ_i)_{i<τ_k}` (`usedSeq`) records all the base increments used so
  far.  `map_histPath_prod`: the base increments after `τ_k` are independent of this past and again
  i.i.d. (the strong Markov property of an i.i.d. sequence at the predictable times `τ_k`);
  `histIncr_condLaw_gaussian`, `histCount_condLaw`: **given the whole past, the increment over the
  chosen step is `N(0, n_k δ)`**, the count `P(n_k m)`; `adaptiveIncr_condLaw_hist_gaussian`: the
  same for the adaptive scheme of (1) (`histPath_eq_adaptivePath`).
* (2) `adaptiveEM_fine_coarse`: the fine and the coarse path, with independent adaptation rules on
  the same base increments, each have the law of their single-level scheme; `adaptiveEM_2_4`:
  hence (2.4) `E[P^f_ℓ] = E[P^c_ℓ]`; `adaptiveEM_mlmc_theorem1`: Giles' Theorem 1 for the
  non-nested adaptive Euler–Maruyama estimator, with (2.4) derived.
* (3) `adaptiveCount_condLaw`: the counts of a Poisson process over adaptively chosen intervals are
  conditionally Poisson with mean `λ h_k`; `adaptiveCount_law_eq_fresh`: the path built from them
  has the law of the scheme driven by fresh Poisson variates.
* Algorithm 3 itself (`alg3Fresh`: the loop over the union sub-intervals, a fresh `√h Z` for each
  sub-interval, accumulators `∆W^c`, `∆W^f`): `algorithm3_law`, `algorithm3_EM_law`: **the coarse
  and the fine path read off Algorithm 3 each have the law of their single-level scheme**;
  `algorithm3_joint_law`, `algorithm3_EM_joint_law`: **the pair of paths read off Algorithm 3 has
  the law of the two single-level paths computed from one sequence of base increments** (the
  coupling of Figure 5.9).  The proof runs Algorithm 3 on the base increments (it is an adaptive
  scheme whose steps are the union sub-intervals, so it has the same law as with fresh
  increments), where each path is computed exactly as from the base increments directly
  (`alg3CoarseSeq_alg3Path`, `alg3FineSeq_alg3Path`, from the invariant `alg3Path_inv`).
* The generic forms: `map_adaptiveIncr`, `map_freshPath`, `map_adaptiveSeq_eq_freshSeq`.

**Scope.**  Step sizes are multiples of the fixed base spacing `δ`, i.e. the base grid refines the
grids of both levels: in the scheme `h_ℓ = 2^{−ℓ} H(Ŝ_n)` this holds when `H` takes values in
`2^{−m₀}T ℕ` and `δ = 2^{−m₀−ℓ}T` (real-valued path-dependent step sizes would need Brownian motion
at stopping times, which is not formalised).  The paths are defined for all `k ∈ ℕ`; the
truncation `t^c := min(t^c + h^c, T)` is part of the rule.  Outside the `histPath` results, "the
past" is the path `y_k` of the scheme (the σ-algebra `σ(y_k)`): the rule sees the base increments
only through `y_k`, which depends on them only through the step increments `ΔW_j`, `j < k`;
conditioning on the whole history `(ξ_i)_{i<τ_k}`, with rules that may depend on it, is the
`histPath` part.  For Algorithm 3 the steps must be at least one base interval and the loop runs
indefinitely instead of stopping at `T` (a rule that ends a step exactly at `T` and continues with
positive steps afterwards gives the paths of Algorithm 3 up to `T`); the first iteration of the
paper, with `h = 0`, only computes the first steps and is folded into the initial state.  The level
paths are Markov in their own state (`ν(x)`, `F(x, ∆W)`) in Algorithm 3; they may depend on their
whole past in the generic results (`map_adaptivePath_prod` to `adaptivePairs_law_eq_fresh`,
`adaptiveCount_*`), and on the history of the base increments too in the `histPath` results; the
Euler–Maruyama results use a rule `ν(t, S)` of the current state, as in `h_ℓ = 2^{−ℓ} H(Ŝ_n)`.
For Poisson variates the rate is constant (the counts of a Poisson process over the adaptive
intervals); tau-leaping with a state-dependent propensity and the Anderson–Higham coupling on each
union sub-interval (`unionChain` of `PoissonGrids.lean`, deterministic grids) is not covered.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MLMC

/-! ### The engine: discrete-time conditioning on fresh noise -/

section Engine

variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]

/-- The one-step law `x ↦ Q.map (ω ↦ (φ (x, ω)).1)` of a jointly measurable step is a measurable
function of the state (Giles 2015, §5.6: the law of the next state given the current one). -/
lemma measurable_map_fst_noiseStep {Q : Measure Ω} [SFinite Q] {φ : X × Ω → Y × Ω}
    (hφ : Measurable φ) : Measurable fun x => Q.map fun ω => (φ (x, ω)).1 := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have e : ∀ x, (Q.map fun ω => (φ (x, ω)).1) s =
      Q (Prod.mk x ⁻¹' ((fun p => (φ p).1) ⁻¹' s)) :=
    fun x => Measure.map_apply (hφ.fst.comp measurable_prodMk_left) hs
  simp_rw [e]
  exact measurable_measure_prodMk_left (hφ.fst hs)

/-- One step driven by fresh noise (the conditioning argument behind Giles 2015, §5.6, p. 44,
lines 1928–1929: "The independent Brownian increments can be simulated for each time interval").
Let the current state have law `P` and the remaining noise law `Q`, independently.  If one step
`φ` maps (state, noise) to (new state, remaining noise) so that, for each fixed state `x`, the new
state and the remaining noise are independent and the remaining noise has law `Q`
(`Q.map (φ (x, ·)) = κ x ⊗ Q` with `κ x = Q.map (φ (x, ·)).1`), then after the step the new state
has the law `P.bind κ` (the state `x ~ P`, then the new state `~ κ x`) and is again independent
of the remaining noise, which has law `Q`. -/
lemma map_prod_eq_bind_prod_of_fresh (P : Measure X) [IsProbabilityMeasure P] (Q : Measure Ω)
    [IsProbabilityMeasure Q] {φ : X × Ω → Y × Ω} (hφ : Measurable φ)
    (hfresh : ∀ x, Q.map (fun ω => φ (x, ω)) = (Q.map fun ω => (φ (x, ω)).1).prod Q) :
    (P.prod Q).map φ = (P.bind fun x => Q.map fun ω => (φ (x, ω)).1).prod Q := by
  have hκ := measurable_map_fst_noiseStep (Q := Q) hφ
  have hm : ∀ x, Measurable fun ω => φ (x, ω) := fun x => hφ.comp measurable_prodMk_left
  have : IsProbabilityMeasure (P.bind fun x => Q.map fun ω => (φ (x, ω)).1) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ hκ.aemeasurable]
    have h1 : ∀ x, (Q.map fun ω => (φ (x, ω)).1) Set.univ = 1 := fun x => by
      rw [Measure.map_apply (hm x).fst MeasurableSet.univ]
      simp
    simp [h1]
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hφ (hs.prod ht), Measure.prod_apply (hφ (hs.prod ht)),
    Measure.bind_apply hs hκ.aemeasurable, ← lintegral_mul_const' _ _ (measure_ne_top Q t)]
  refine lintegral_congr fun x => ?_
  rw [← Measure.prod_prod, ← hfresh x, Measure.map_apply (hm x) (hs.prod ht)]
  rfl

/-- The law after `k` steps of a chain with the time-dependent transition laws `κ j` started at
`x₀`: `L_0 = δ_{x₀}`, `L_{k+1} = L_k.bind (κ k)` (Giles 2015, §5.6: the law of an adaptive path,
step by step). -/
noncomputable def noiseChainLaw (κ : ℕ → X → Measure X) (x₀ : X) : ℕ → Measure X
  | 0 => Measure.dirac x₀
  | k + 1 => (noiseChainLaw κ x₀ k).bind (κ k)

/-- A chain driven by fresh noise (Giles 2015, §5.6, p. 44, lines 1926–1929).  The state and
the remaining noise evolve by `Ψ (k + 1) = step k ∘ Ψ k` from `Ψ 0 ω = (x₀, ω)`, the noise `ω`
having law `Q`.  If every step leaves the remaining noise fresh (`hfresh`, as in
`map_prod_eq_bind_prod_of_fresh`), then after `k` steps the state has the law `noiseChainLaw` of
the chain with the transition laws `x ↦ Q.map (step j (x, ·)).1`, and it is independent of the
remaining noise, which has law `Q`. -/
lemma map_noiseChain (Q : Measure Ω) [IsProbabilityMeasure Q] (step : ℕ → X × Ω → X × Ω)
    (hstep : ∀ k, Measurable (step k))
    (hfresh : ∀ k x, Q.map (fun ω => step k (x, ω)) =
      (Q.map fun ω => (step k (x, ω)).1).prod Q)
    (x₀ : X) (Ψ : ℕ → Ω → X × Ω) (h0 : ∀ ω, Ψ 0 ω = (x₀, ω))
    (hsucc : ∀ k ω, Ψ (k + 1) ω = step k (Ψ k ω)) (k : ℕ) :
    Measurable (Ψ k) ∧
      Q.map (Ψ k) = (noiseChainLaw (fun j x => Q.map fun ω => (step j (x, ω)).1) x₀ k).prod Q := by
  induction k with
  | zero =>
    have e : Ψ 0 = Prod.mk x₀ := funext h0
    rw [e, noiseChainLaw, Measure.dirac_prod]
    exact ⟨measurable_prodMk_left, rfl⟩
  | succ k ih =>
    have e : Ψ (k + 1) = step k ∘ Ψ k := funext (hsucc k)
    have : IsProbabilityMeasure
        (noiseChainLaw (fun j x => Q.map fun ω => (step j (x, ω)).1) x₀ k) := by
      have h := Measure.isProbabilityMeasure_map ih.1.aemeasurable (μ := Q)
      rw [ih.2] at h
      constructor
      have e := Measure.prod_prod
        (μ := noiseChainLaw (fun j x => Q.map fun ω => (step j (x, ω)).1) x₀ k) (ν := Q)
        Set.univ Set.univ
      rw [Set.univ_prod_univ, measure_univ, measure_univ (μ := Q), mul_one] at e
      exact e.symm
    rw [e]
    refine ⟨(hstep k).comp ih.1, ?_⟩
    rw [← Measure.map_map (hstep k) ih.1, ih.2,
      map_prod_eq_bind_prod_of_fresh _ _ (hstep k) (hfresh k)]
    rfl

end Engine

/-! ### Blocks of base increments -/

section Blocks

variable {E : Type*}

/-- Shifting twice is shifting by the sum: `σ^{m+n} ξ = σⁿ (σ^m ξ)` for the shift
`(σⁿ ξ)_i = ξ_{n+i}` of the base increments (`shiftSeq`; Giles 2015, §5.6: the base increments
not yet used after two steps). -/
lemma shiftSeq_add (m n : ℕ) (ξ : ℕ → E) : shiftSeq (m + n) ξ = shiftSeq n (shiftSeq m ξ) := by
  funext i
  show ξ (m + n + i) = ξ (m + (n + i))
  rw [add_assoc]

/-- The shift by `0` is the identity (Giles 2015, §5.6: before the first step no base increment
has been used). -/
lemma shiftSeq_zero (ξ : ℕ → E) : shiftSeq 0 ξ = ξ := by
  funext i
  show ξ (0 + i) = ξ i
  rw [zero_add]

variable [MeasurableSpace E]

/-- The shift `(n, ξ) ↦ σⁿ ξ` is jointly measurable (Giles 2015, §5.6: the base increments after a
random number `n` of them). -/
lemma measurable_shiftSeq_uncurry : Measurable fun p : ℕ × (ℕ → E) => shiftSeq p.1 p.2 :=
  measurable_from_prod_countable_right fun n => measurable_shiftSeq n

/-- The first `n` base increments are independent of the others (Giles 2015, §5.6, p. 44:
"The independent Brownian increments can be simulated for each time interval"): under the i.i.d.
law `μ^{⊗ℕ}`, the block `(ξ_i)_{i<n}` and the shifted sequence `σⁿ ξ = (ξ_{n+i})_i` are
independent. -/
lemma indepFun_restrict_shiftSeq (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (fun ξ : ℕ → E => fun i : Fin n => ξ i) (shiftSeq n)
      (Measure.infinitePi fun _ => μ) := by
  have h1 := iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ (x : E) => x)
    (fun _ => measurable_id)
  rw [iIndepFun_iff_iIndep] at h1
  have h2 := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) h1
    (S := Set.Iio n) (T := Set.Ici n) (Set.disjoint_left.2 fun i hi hi' => by
      simp only [Set.mem_Iio, Set.mem_Ici] at hi hi'
      omega)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h2 ?_) ?_
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂_of_le (i : ℕ) i.isLt le_rfl
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂_of_le (n + i) (by simp [Set.mem_Ici]) le_rfl

/-- The first base increment and the shifted sequence (Giles 2015, §5.6): under `ρ^{⊗ℕ}` the
pair `(ζ_0, σ¹ζ)` has the law `ρ ⊗ ρ^{⊗ℕ}`; a fresh variate is used and the others stay fresh. -/
lemma map_head_shiftSeq (ρ : Measure E) [IsProbabilityMeasure ρ] :
    (Measure.infinitePi fun _ => ρ).map (fun ζ => (ζ 0, shiftSeq 1 ζ)) =
      ρ.prod (Measure.infinitePi fun _ => ρ) := by
  have hind : IndepFun (fun ζ : ℕ → E => ζ 0) (shiftSeq 1) (Measure.infinitePi fun _ => ρ) := by
    exact (indepFun_restrict_shiftSeq ρ 1).comp
      (φ := fun v : Fin 1 → E => v 0) (ψ := id) (measurable_pi_apply (0 : Fin 1)) measurable_id
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
      (measurable_shiftSeq 1).aemeasurable).1 hind, (measurePreserving_shiftSeq ρ 1).map_eq,
    Measure.infinitePi_map_eval]

variable [AddCommMonoid E]

/-- The law of the sum `ξ_0 + ⋯ + ξ_{n−1}` of `n` i.i.d. base increments with law `μ` (Giles 2015,
§5.6, p. 44: the increments of the base intervals "summed to give `W(t)` at the required times";
for `μ = N(0, δ)` it is `N(0, nδ)`, `blockLaw_gaussianReal`; for `μ = P(m)` it is `P(nm)`,
`blockLaw_poisson`). -/
noncomputable def blockLaw (μ : Measure E) (n : ℕ) : Measure E :=
  (Measure.infinitePi fun _ => μ).map fun ξ => ∑ i ∈ range n, ξ i

variable [MeasurableAdd₂ E]

/-- The sum of the first `n` base increments is measurable (Giles 2015, §5.6). -/
lemma measurable_blockSum (n : ℕ) : Measurable fun ξ : ℕ → E => ∑ i ∈ range n, ξ i :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- The law of a block sum is a probability measure (Giles 2015, §5.6). -/
lemma isProbabilityMeasure_blockLaw (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (blockLaw μ n) :=
  Measure.isProbabilityMeasure_map (measurable_blockSum n).aemeasurable

/-- A block sum is independent of the base increments after the block (Giles 2015, §5.6,
p. 44, lines 1927–1929: "The independent Brownian increments can be simulated for each time
interval, and summed"): under `μ^{⊗ℕ}` the pair `(∑_{i<n} ξ_i, σⁿ ξ)` has the law
`blockLaw μ n ⊗ μ^{⊗ℕ}`. -/
lemma map_blockSum_shiftSeq (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    (Measure.infinitePi fun _ => μ).map (fun ξ => (∑ i ∈ range n, ξ i, shiftSeq n ξ)) =
      (blockLaw μ n).prod (Measure.infinitePi fun _ => μ) := by
  have hind : IndepFun (fun ξ : ℕ → E => ∑ i ∈ range n, ξ i) (shiftSeq n)
      (Measure.infinitePi fun _ => μ) := by
    have h := (indepFun_restrict_shiftSeq μ n).comp
      (φ := fun v : Fin n → E => ∑ i, v i) (ψ := id)
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_id
    have e : ((fun v : Fin n → E => ∑ i, v i) ∘ fun ξ : ℕ → E => fun i : Fin n => ξ i) =
        fun ξ => ∑ i ∈ range n, ξ i := by
      funext ξ
      exact Fin.sum_univ_eq_sum_range (fun i => ξ i) n
    rwa [e, Function.id_comp] at h
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_blockSum n).aemeasurable
      (measurable_shiftSeq n).aemeasurable).1 hind, (measurePreserving_shiftSeq μ n).map_eq]
  rfl

end Blocks

/-! ### The adaptive path driven by summed base increments -/

section Adaptive

variable {X E : Type*}

/-- The path stopped at step `k`, extended by the value `x` at step `k + 1` (Giles 2015, §5.6):
`extendPath k y x i = y_i` for `i ≤ k` and `= x` for `i > k`.  A path stopped at step `k` is
`y = (x_{min(i,k)})_i`; it records the values `x_0, …, x_k` of the path so far. -/
def extendPath (k : ℕ) (y : ℕ → X) (x : X) : ℕ → X := fun i => if i ≤ k then y i else x

/-- `extendPath` keeps the values up to step `k` (Giles 2015, §5.6). -/
lemma extendPath_of_le {k i : ℕ} (y : ℕ → X) (x : X) (h : i ≤ k) : extendPath k y x i = y i :=
  if_pos h

/-- `extendPath` puts the new value after step `k` (Giles 2015, §5.6). -/
lemma extendPath_of_lt {k i : ℕ} (y : ℕ → X) (x : X) (h : k < i) : extendPath k y x i = x :=
  if_neg (Nat.not_le.2 h)

/-- **The adaptive path on the base grid** (Giles 2015, §5.6, p. 44, lines 1917–1929: an
"adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)`", the Brownian increments of the base
intervals "summed to give `W(t)` at the required times").  The base increments are `ξ_0, ξ_1, …`,
one per interval of a fixed base grid.  The value at step `k` is the pair `(y_k, τ_k)`: the path
stopped at step `k`, `y_k = (x_{min(i,k)})_i`, and the number `τ_k` of base intervals used so far.
Step `k` takes `n_k = ν k y_k` base intervals, chosen from the path so far (a predictable rule);
its increment is `∑_{τ_k ≤ i < τ_k + n_k} ξ_i`, and `x_{k+1} = G k y_k (increment)`.  Step sizes
are multiples of the base spacing. -/
def adaptivePath [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ) (G : ℕ → (ℕ → X) → E → X) (x₀ : X)
    (ξ : ℕ → E) : ℕ → (ℕ → X) × ℕ
  | 0 => (fun _ => x₀, 0)
  | k + 1 =>
    let y := (adaptivePath ν G x₀ ξ k).1
    let τ := (adaptivePath ν G x₀ ξ k).2
    (extendPath k y (G k y (∑ i ∈ Ico τ (τ + ν k y), ξ i)), τ + ν k y)

/-- The increment of step `k` (Giles 2015, §5.6, p. 44, lines 1928–1929: "The independent
Brownian increments can be simulated for each time interval, and summed"): the sum
`ΔW_k = ∑_{τ_k ≤ i < τ_k + n_k} ξ_i` of the base increments over the `n_k = ν k y_k` base
intervals of the step. -/
def adaptiveIncr [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ) (G : ℕ → (ℕ → X) → E → X) (x₀ : X)
    (ξ : ℕ → E) (k : ℕ) : E :=
  ∑ i ∈ Ico (adaptivePath ν G x₀ ξ k).2
    ((adaptivePath ν G x₀ ξ k).2 + ν k (adaptivePath ν G x₀ ξ k).1), ξ i

/-- One step of the adaptive path, in terms of `adaptiveIncr` (Giles 2015, §5.6). -/
lemma adaptivePath_succ [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ) (G : ℕ → (ℕ → X) → E → X)
    (x₀ : X) (ξ : ℕ → E) (k : ℕ) :
    adaptivePath ν G x₀ ξ (k + 1) =
      (extendPath k (adaptivePath ν G x₀ ξ k).1
        (G k (adaptivePath ν G x₀ ξ k).1 (adaptiveIncr ν G x₀ ξ k)),
        (adaptivePath ν G x₀ ξ k).2 + ν k (adaptivePath ν G x₀ ξ k).1) := rfl

/-- The stopped path after one more step (Giles 2015, §5.6). -/
lemma adaptivePath_succ_fst [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ)
    (G : ℕ → (ℕ → X) → E → X) (x₀ : X) (ξ : ℕ → E) (k : ℕ) :
    (adaptivePath ν G x₀ ξ (k + 1)).1 = extendPath k (adaptivePath ν G x₀ ξ k).1
      (G k (adaptivePath ν G x₀ ξ k).1 (adaptiveIncr ν G x₀ ξ k)) := rfl

/-- The increment of step `k` is the sum of the first `n_k` base increments not used yet
(Giles 2015, §5.6): `ΔW_k = ∑_{i<n_k} (σ^{τ_k} ξ)_i`. -/
lemma adaptiveIncr_eq [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ) (G : ℕ → (ℕ → X) → E → X)
    (x₀ : X) (ξ : ℕ → E) (k : ℕ) :
    adaptiveIncr ν G x₀ ξ k = ∑ i ∈ range (ν k (adaptivePath ν G x₀ ξ k).1),
      shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ i := by
  rw [adaptiveIncr, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  rfl

/-- One step acting on (stopped path, unused base increments) (Giles 2015, §5.6): the step uses
the first `ν k y` unused base increments and leaves the others. -/
def adaptiveStep [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ) (G : ℕ → (ℕ → X) → E → X) (k : ℕ)
    (p : (ℕ → X) × (ℕ → E)) : (ℕ → X) × (ℕ → E) :=
  (extendPath k p.1 (G k p.1 (∑ i ∈ range (ν k p.1), p.2 i)), shiftSeq (ν k p.1) p.2)

/-- The adaptive path with its unused base increments evolves by `adaptiveStep` (Giles 2015,
§5.6). -/
lemma adaptivePath_step [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ) (G : ℕ → (ℕ → X) → E → X)
    (x₀ : X) (ξ : ℕ → E) (k : ℕ) :
    ((adaptivePath ν G x₀ ξ (k + 1)).1, shiftSeq (adaptivePath ν G x₀ ξ (k + 1)).2 ξ) =
      adaptiveStep ν G k ((adaptivePath ν G x₀ ξ k).1, shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ) := by
  rw [adaptivePath_succ, adaptiveIncr_eq, shiftSeq_add]
  rfl

variable [MeasurableSpace X] [MeasurableSpace E]

/-- The law of an adaptive scheme (Giles 2015, §5.6): the law of the path stopped at step `k`
when, given the path `y` so far, the `k`-th increment is drawn from `κ k y` and
`x_{k+1} = G k y (increment)`.  For `κ k y = N(0, h_k(y))` this is the law of the adaptive
scheme driven by fresh Brownian increments over its steps `h_k`. -/
noncomputable def adaptiveLaw (κ : ℕ → (ℕ → X) → Measure E) (G : ℕ → (ℕ → X) → E → X)
    (x₀ : X) : ℕ → Measure (ℕ → X) :=
  noiseChainLaw (fun k y => (κ k y).map fun e => extendPath k y (G k y e)) (fun _ => x₀)

omit [MeasurableSpace E] in
/-- `extendPath k` is jointly measurable (Giles 2015, §5.6). -/
lemma measurable_extendPath (k : ℕ) :
    Measurable fun p : (ℕ → X) × X => extendPath k p.1 p.2 := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ≤ k
  · simp only [extendPath, h, ↓reduceIte]
    fun_prop
  · simp only [extendPath, h, ↓reduceIte]
    fun_prop

variable [AddCommMonoid E] [MeasurableAdd₂ E]

omit [MeasurableSpace X] in
/-- The block sum `(n, ξ) ↦ ∑_{i<n} ξ_i` with a random length is measurable (Giles 2015,
§5.6). -/
lemma measurable_blockSum_uncurry :
    Measurable fun p : ℕ × (ℕ → E) => ∑ i ∈ range p.1, p.2 i :=
  measurable_from_prod_countable_right fun n => measurable_blockSum n

/-- One adaptive step is measurable for a measurable rule and update (Giles 2015, §5.6). -/
lemma measurable_adaptiveStep {ν : ℕ → (ℕ → X) → ℕ} {G : ℕ → (ℕ → X) → E → X} {k : ℕ}
    (hν : Measurable (ν k)) (hG : Measurable fun p : (ℕ → X) × E => G k p.1 p.2) :
    Measurable (adaptiveStep ν G k) := by
  have h0 : Measurable fun p : (ℕ → X) × (ℕ → E) => (ν k p.1, p.2) :=
    (hν.comp measurable_fst).prodMk measurable_snd
  have h1 : Measurable fun p : (ℕ → X) × (ℕ → E) => ∑ i ∈ range (ν k p.1), p.2 i :=
    measurable_blockSum_uncurry.comp h0
  have h2 : Measurable fun p : (ℕ → X) × (ℕ → E) => shiftSeq (ν k p.1) p.2 :=
    measurable_shiftSeq_uncurry.comp h0
  exact ((measurable_extendPath k).comp
    (measurable_fst.prodMk (hG.comp (measurable_fst.prodMk h1)))).prodMk h2

/-- For a fixed path so far, the new stopped path after one step has the law of the update
applied to a block sum (Giles 2015, §5.6). -/
lemma map_adaptiveStep_fst (μ : Measure E) {ν : ℕ → (ℕ → X) → ℕ} {G : ℕ → (ℕ → X) → E → X}
    {k : ℕ} (hG : Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (y : ℕ → X) :
    (Measure.infinitePi fun _ => μ).map (fun ω => (adaptiveStep ν G k (y, ω)).1) =
      (blockLaw μ (ν k y)).map fun e => extendPath k y (G k y e) := by
  have hg : Measurable fun e => extendPath k y (G k y e) :=
    (measurable_extendPath k).comp (measurable_const.prodMk
      (hG.comp (measurable_const.prodMk measurable_id)))
  rw [blockLaw, Measure.map_map hg (measurable_blockSum _)]
  rfl

/-- For a fixed path so far, one adaptive step leaves the unused base increments fresh and
independent of the new path (Giles 2015, §5.6). -/
lemma map_adaptiveStep (μ : Measure E) [IsProbabilityMeasure μ] {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → E → X} {k : ℕ} (hG : Measurable fun p : (ℕ → X) × E => G k p.1 p.2)
    (y : ℕ → X) :
    (Measure.infinitePi fun _ => μ).map (fun ω => adaptiveStep ν G k (y, ω)) =
      ((Measure.infinitePi fun _ => μ).map fun ω => (adaptiveStep ν G k (y, ω)).1).prod
        (Measure.infinitePi fun _ => μ) := by
  have hg : Measurable fun e => extendPath k y (G k y e) :=
    (measurable_extendPath k).comp (measurable_const.prodMk
      (hG.comp (measurable_const.prodMk measurable_id)))
  rw [map_adaptiveStep_fst μ hG y]
  have := isProbabilityMeasure_blockLaw μ (ν k y)
  have e : (fun ω => adaptiveStep ν G k (y, ω)) =
      Prod.map (fun e => extendPath k y (G k y e)) id ∘
        fun ω : ℕ → E => (∑ i ∈ range (ν k y), ω i, shiftSeq (ν k y) ω) := rfl
  rw [e, ← Measure.map_map (hg.prodMap measurable_id)
      ((measurable_blockSum _).prodMk (measurable_shiftSeq _)), map_blockSum_shiftSeq,
    ← Measure.map_prod_map _ _ hg measurable_id, Measure.map_id]

/-- **The unused base increments are fresh at the adaptive times** (Giles 2015, §5.6, p. 44,
lines 1926–1929: "The underlying Brownian path needs to be sampled at a set of times which are the
union of the simulation times used by the coarse and fine path. The independent Brownian
increments can be simulated for each time interval, and summed to give `W(t)` at the required
times").  Let the base increments be i.i.d. with law `μ`, the rules `ν k` and the updates `G k`
measurable.  After `k` steps of the adaptive path the pair (path so far `y_k`, unused base
increments `σ^{τ_k} ξ`) has the law `L_k ⊗ μ^{⊗ℕ}`: the base increments after the random time
`τ_k` are independent of the path so far and again i.i.d. with law `μ`.  Here
`L_k = adaptiveLaw (fun j y => blockLaw μ (ν j y)) G x₀ k`: given the path so far, the next
increment is a sum of `ν_j(y)` fresh base increments.  The map is also measurable.  "The path so
far" is the path `y_k` of the scheme (the σ-algebra `σ(y_k)`): the rule sees the base increments
only through `y_k`, i.e. through the step increments `ΔW_j`, `j < k`.  Independence from the
whole history `(ξ_i)_{i<τ_k}`, also for rules that depend on it, is `map_histPath_prod` (with
`histPath_eq_adaptivePath`). -/
theorem map_adaptivePath_prod (μ : Measure E) [IsProbabilityMeasure μ]
    {ν : ℕ → (ℕ → X) → ℕ} {G : ℕ → (ℕ → X) → E → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    Measurable (fun ξ => ((adaptivePath ν G x₀ ξ k).1, shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ)) ∧
    (Measure.infinitePi fun _ => μ).map
        (fun ξ => ((adaptivePath ν G x₀ ξ k).1, shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ)) =
      (adaptiveLaw (fun j y => blockLaw μ (ν j y)) G x₀ k).prod
        (Measure.infinitePi fun _ => μ) := by
  have h := map_noiseChain (Measure.infinitePi fun _ => μ) (adaptiveStep ν G)
    (fun j => measurable_adaptiveStep (hν j) (hG j)) (fun j y => map_adaptiveStep μ (hG j) y)
    (fun _ => x₀)
    (fun k ξ => ((adaptivePath ν G x₀ ξ k).1, shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ))
    (fun ξ => by
      show ((fun _ => x₀), shiftSeq 0 ξ) = ((fun _ => x₀), ξ)
      rw [shiftSeq_zero]) (fun j ξ => adaptivePath_step ν G x₀ ξ j) k
  refine ⟨h.1, ?_⟩
  rw [h.2]
  congr 2
  funext j y
  exact map_adaptiveStep_fst μ (hG j) y

/-- **The law of the adaptive path built from summed base increments** (Giles 2015, §5.6, p. 44,
lines 1917–1929: "it uses a completely independent adaptation on each level of refinement, with an
adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)` … The independent Brownian increments can be
simulated for each time interval, and summed to give `W(t)` at the required times").  With i.i.d.
base increments of law `μ` and measurable rules and updates, the path stopped at step `k` has the
law `adaptiveLaw (fun j y => blockLaw μ (ν j y)) G x₀ k` of the scheme in which, given the path `y`
so far, the next increment is drawn afresh from the law of a sum of `ν_j(y)` base increments.
Step sizes are multiples of the base spacing. -/
theorem map_adaptivePath (μ : Measure E) [IsProbabilityMeasure μ]
    {ν : ℕ → (ℕ → X) → ℕ} {G : ℕ → (ℕ → X) → E → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    (Measure.infinitePi fun _ => μ).map (fun ξ => (adaptivePath ν G x₀ ξ k).1) =
      adaptiveLaw (fun j y => blockLaw μ (ν j y)) G x₀ k := by
  obtain ⟨hm, h⟩ := map_adaptivePath_prod μ hν hG x₀ k
  have e : (fun ξ => (adaptivePath ν G x₀ ξ k).1) =
      Prod.fst ∘ fun ξ => ((adaptivePath ν G x₀ ξ k).1, shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ) :=
    rfl
  rw [e, ← Measure.map_map measurable_fst hm, h, Measure.map_fst_prod, measure_univ, one_smul]

end Adaptive

/-! ### The conditional law of the increment given the path so far -/

section CondLaw

variable {X Ω E : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace E]

/-- A function of an independent pair: if `Q.map (f (x, ·)) = κ x` for every `x`, then the pair
`(x, f (x, ω))` under `P ⊗ Q` has the law `P ⊗ₘ κ` (Giles 2015, §5.6: the increment given the
past). -/
lemma map_pair_prod_eq_compProd (P : Measure X) [SFinite P] (Q : Measure Ω) [SFinite Q]
    (κ : Kernel X E) [IsSFiniteKernel κ] {f : X × Ω → E} (hf : Measurable f)
    (hκ : ∀ x, Q.map (fun ω => f (x, ω)) = κ x) :
    (P.prod Q).map (fun p => (p.1, f p)) = P ⊗ₘ κ := by
  ext s hs
  have hm : Measurable fun p : X × Ω => (p.1, f p) := measurable_fst.prodMk hf
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs), Measure.compProd_apply hs]
  refine lintegral_congr fun x => ?_
  have hfx : Measurable fun ω => f (x, ω) := hf.comp measurable_prodMk_left
  rw [← hκ x, Measure.map_apply hfx (measurable_prodMk_left hs)]
  rfl

end CondLaw

section Kernels

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E]

/-- The kernel `n ↦ blockLaw μ n`: the law of a sum of `n` i.i.d. base increments (Giles 2015,
§5.6). -/
noncomputable def blockKernel (μ : Measure E) : Kernel ℕ E :=
  Kernel.ofFunOfCountable (blockLaw μ)

/-- `blockKernel μ` is a Markov kernel (Giles 2015, §5.6). -/
lemma isMarkovKernel_blockKernel [MeasurableAdd₂ E] (μ : Measure E) [IsProbabilityMeasure μ] :
    IsMarkovKernel (blockKernel μ) :=
  ⟨fun n => isProbabilityMeasure_blockLaw μ n⟩

end Kernels

section AdaptiveCond

variable {X E : Type*} [MeasurableSpace X] [MeasurableSpace E] [AddCommMonoid E]
  [MeasurableAdd₂ E]

/-- **The conditional law of the increment of an adaptive step** (Giles 2015, §5.6, p. 44,
lines 1928–1929: "The independent Brownian increments can be simulated for each time interval,
and summed to give `W(t)` at the required times").  With i.i.d. base increments of law `μ`, the
pair (path stopped at step `k`, increment `ΔW_k` of step `k`) has the law `L ⊗ₘ κ`, where `L` is
the law of the path so far and `κ y = blockLaw μ (ν k y)`: given the path so far, the increment
over the chosen step is distributed as a sum of `ν_k(y)` fresh base increments.  (This is
Mathlib's `HasCondDistrib`, unfolded.)  "The path so far" is the path `y_k` of the scheme (the
σ-algebra `σ(y_k)`): the rule sees the base increments only through `y_k`, i.e. through the step
increments `ΔW_j`, `j < k`; conditioning on the whole history `(ξ_i)_{i<τ_k}` is
`map_histIncr`. -/
theorem map_adaptiveIncr (μ : Measure E) [IsProbabilityMeasure μ]
    {ν : ℕ → (ℕ → X) → ℕ} {G : ℕ → (ℕ → X) → E → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    (Measure.infinitePi fun _ => μ).map
        (fun ξ => ((adaptivePath ν G x₀ ξ k).1, adaptiveIncr ν G x₀ ξ k)) =
      ((Measure.infinitePi fun _ => μ).map fun ξ => (adaptivePath ν G x₀ ξ k).1) ⊗ₘ
        (blockKernel μ).comap (ν k) (hν k) := by
  obtain ⟨hm, h⟩ := map_adaptivePath_prod μ hν hG x₀ k
  have := isMarkovKernel_blockKernel μ
  have hP : IsProbabilityMeasure (adaptiveLaw (fun j y => blockLaw μ (ν j y)) G x₀ k) := by
    rw [← map_adaptivePath μ hν hG x₀ k]
    exact Measure.isProbabilityMeasure_map (measurable_fst.comp hm).aemeasurable
  have hf : Measurable fun p : (ℕ → X) × (ℕ → E) => ∑ i ∈ range (ν k p.1), p.2 i :=
    measurable_blockSum_uncurry.comp (((hν k).comp measurable_fst).prodMk measurable_snd)
  have e : (fun ξ => ((adaptivePath ν G x₀ ξ k).1, adaptiveIncr ν G x₀ ξ k)) =
      (fun p : (ℕ → X) × (ℕ → E) => (p.1, ∑ i ∈ range (ν k p.1), p.2 i)) ∘
        fun ξ => ((adaptivePath ν G x₀ ξ k).1, shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ) := by
    funext ξ
    rw [adaptiveIncr_eq]
    rfl
  rw [e, ← Measure.map_map (measurable_fst.prodMk hf) hm, h,
    map_pair_prod_eq_compProd _ _ ((blockKernel μ).comap (ν k) (hν k)) hf
      (fun y => by rw [Kernel.comap_apply]; rfl),
    map_adaptivePath μ hν hG x₀ k]

end AdaptiveCond

/-! ### The scheme driven by fresh increments -/

section Fresh

variable {X E : Type*}

/-- The adaptive scheme driven by fresh variates (Giles 2015, §5.6, Algorithm 3, p. 45:
"`∆W := √h Z`"): `x_{k+1} = G k y_k (ζ_k)` with a fresh variate `ζ_k` for each step, where `y_k`
is the path stopped at step `k`.  For the Brownian case the update applies `G` to `√(h_k) ζ_k`
with `ζ_k ~ N(0, 1)`. -/
def freshPath (G : ℕ → (ℕ → X) → E → X) (x₀ : X) (ζ : ℕ → E) : ℕ → ℕ → X
  | 0 => fun _ => x₀
  | k + 1 => extendPath k (freshPath G x₀ ζ k) (G k (freshPath G x₀ ζ k) (ζ k))

/-- One step of the scheme driven by fresh variates (Giles 2015, §5.6). -/
lemma freshPath_succ (G : ℕ → (ℕ → X) → E → X) (x₀ : X) (ζ : ℕ → E) (k : ℕ) :
    freshPath G x₀ ζ (k + 1) =
      extendPath k (freshPath G x₀ ζ k) (G k (freshPath G x₀ ζ k) (ζ k)) := rfl

/-- One fresh step acting on (stopped path, unused variates) (Giles 2015, §5.6). -/
def freshStep (G : ℕ → (ℕ → X) → E → X) (k : ℕ) (p : (ℕ → X) × (ℕ → E)) :
    (ℕ → X) × (ℕ → E) :=
  (extendPath k p.1 (G k p.1 (p.2 0)), shiftSeq 1 p.2)

/-- The scheme driven by fresh variates, with its unused variates, evolves by `freshStep`
(Giles 2015, §5.6). -/
lemma freshPath_step (G : ℕ → (ℕ → X) → E → X) (x₀ : X) (ζ : ℕ → E) (k : ℕ) :
    (freshPath G x₀ ζ (k + 1), shiftSeq (k + 1) ζ) =
      freshStep G k (freshPath G x₀ ζ k, shiftSeq k ζ) := by
  rw [freshPath_succ, shiftSeq_add]
  rfl

variable [MeasurableSpace X] [MeasurableSpace E]

/-- One fresh step is measurable (Giles 2015, §5.6). -/
lemma measurable_freshStep {G : ℕ → (ℕ → X) → E → X} {k : ℕ}
    (hG : Measurable fun p : (ℕ → X) × E => G k p.1 p.2) : Measurable (freshStep G k) :=
  ((measurable_extendPath k).comp (measurable_fst.prodMk
    (hG.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))))).prodMk
    ((measurable_shiftSeq 1).comp measurable_snd)

/-- For a fixed path so far, the new stopped path after a fresh step has the law of the update
applied to one fresh variate (Giles 2015, §5.6). -/
lemma map_freshStep_fst (ρ : Measure E) [IsProbabilityMeasure ρ] {G : ℕ → (ℕ → X) → E → X}
    {k : ℕ} (hG : Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (y : ℕ → X) :
    (Measure.infinitePi fun _ => ρ).map (fun ζ => (freshStep G k (y, ζ)).1) =
      ρ.map fun e => extendPath k y (G k y e) := by
  have hg : Measurable fun e => extendPath k y (G k y e) :=
    (measurable_extendPath k).comp (measurable_const.prodMk
      (hG.comp (measurable_const.prodMk measurable_id)))
  have e : (fun ζ => (freshStep G k (y, ζ)).1) =
      (fun e => extendPath k y (G k y e)) ∘ fun ζ : ℕ → E => ζ 0 := rfl
  rw [e, ← Measure.map_map hg (measurable_pi_apply 0), Measure.infinitePi_map_eval]

/-- For a fixed path so far, a fresh step leaves the unused variates fresh and independent of the
new path (Giles 2015, §5.6). -/
lemma map_freshStep (ρ : Measure E) [IsProbabilityMeasure ρ] {G : ℕ → (ℕ → X) → E → X}
    {k : ℕ} (hG : Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (y : ℕ → X) :
    (Measure.infinitePi fun _ => ρ).map (fun ζ => freshStep G k (y, ζ)) =
      ((Measure.infinitePi fun _ => ρ).map fun ζ => (freshStep G k (y, ζ)).1).prod
        (Measure.infinitePi fun _ => ρ) := by
  have hg : Measurable fun e => extendPath k y (G k y e) :=
    (measurable_extendPath k).comp (measurable_const.prodMk
      (hG.comp (measurable_const.prodMk measurable_id)))
  rw [map_freshStep_fst ρ hG y]
  have e : (fun ζ => freshStep G k (y, ζ)) =
      Prod.map (fun e => extendPath k y (G k y e)) id ∘
        fun ζ : ℕ → E => (ζ 0, shiftSeq 1 ζ) := rfl
  rw [e, ← Measure.map_map (hg.prodMap measurable_id)
      ((measurable_pi_apply 0).prodMk (measurable_shiftSeq 1)), map_head_shiftSeq,
    ← Measure.map_prod_map _ _ hg measurable_id, Measure.map_id]

/-- **The law of the scheme driven by fresh variates** (Giles 2015, §5.6, Algorithm 3, p. 45:
"`∆W := √h Z`").  If the variates `ζ_0, ζ_1, …` are i.i.d. with law `ρ` and the updates `G k` are
measurable, the path stopped at step `k` has the law `adaptiveLaw (fun _ _ => ρ) G x₀ k`. -/
theorem map_freshPath (ρ : Measure E) [IsProbabilityMeasure ρ] {G : ℕ → (ℕ → X) → E → X}
    (hG : ∀ k, Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    (Measure.infinitePi fun _ => ρ).map (fun ζ => freshPath G x₀ ζ k) =
      adaptiveLaw (fun _ _ => ρ) G x₀ k := by
  have h := map_noiseChain (Measure.infinitePi fun _ => ρ) (freshStep G)
    (fun j => measurable_freshStep (hG j)) (fun j y => map_freshStep ρ (hG j) y)
    (fun _ => x₀) (fun k ζ => (freshPath G x₀ ζ k, shiftSeq k ζ))
    (fun ζ => by
      show ((fun _ => x₀), shiftSeq 0 ζ) = ((fun _ => x₀), ζ)
      rw [shiftSeq_zero]) (fun j ζ => freshPath_step G x₀ ζ j) k
  have e : (fun ζ => freshPath G x₀ ζ k) =
      Prod.fst ∘ fun ζ => (freshPath G x₀ ζ k, shiftSeq k ζ) := rfl
  rw [e, ← Measure.map_map measurable_fst h.1, h.2, Measure.map_fst_prod, measure_univ, one_smul]
  unfold adaptiveLaw
  congr 1
  funext j y
  exact map_freshStep_fst ρ (hG j) y

/-- Reparametrising the increments inside the update: `G k y (s k y e)` with `e ~ κ k y` gives the
same law as `G k y` applied to an increment of law `(κ k y).map (s k y)` (Giles 2015, §5.6:
`∆W := √h Z` with `Z ~ N(0, 1)` is an `N(0, h)` increment). -/
lemma adaptiveLaw_comp {E' : Type*} [MeasurableSpace E'] (κ : ℕ → (ℕ → X) → Measure E')
    {G : ℕ → (ℕ → X) → E → X} (hG : ∀ k, Measurable fun p : (ℕ → X) × E => G k p.1 p.2)
    (s : ℕ → (ℕ → X) → E' → E) (hs : ∀ k y, Measurable (s k y)) (x₀ : X) :
    adaptiveLaw κ (fun k y e => G k y (s k y e)) x₀ =
      adaptiveLaw (fun k y => (κ k y).map (s k y)) G x₀ := by
  unfold adaptiveLaw
  congr 1
  funext k y
  have hg : Measurable fun e => extendPath k y (G k y e) :=
    (measurable_extendPath k).comp (measurable_const.prodMk
      ((hG k).comp (measurable_const.prodMk measurable_id)))
  rw [Measure.map_map hg (hs k y)]
  rfl

end Fresh

/-! ### The whole path -/

section WholePath

variable {X E : Type*}

/-- The values `x_0, x_1, …` of the adaptive path built from summed base increments (Giles
2015, §5.6): `x_k` is the last value of the path stopped at step `k`. -/
def adaptiveSeq [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ) (G : ℕ → (ℕ → X) → E → X) (x₀ : X)
    (ξ : ℕ → E) : ℕ → X :=
  fun k => (adaptivePath ν G x₀ ξ k).1 k

/-- The values of the scheme driven by fresh variates (Giles 2015, §5.6, Algorithm 3). -/
def freshSeq (G : ℕ → (ℕ → X) → E → X) (x₀ : X) (ζ : ℕ → E) : ℕ → X :=
  fun k => freshPath G x₀ ζ k k

/-- The path stopped at step `k` is `(x_{min(i,k)})_i` (Giles 2015, §5.6). -/
lemma adaptivePath_fst_apply [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ)
    (G : ℕ → (ℕ → X) → E → X) (x₀ : X) (ξ : ℕ → E) :
    ∀ k i, (adaptivePath ν G x₀ ξ k).1 i = adaptiveSeq ν G x₀ ξ (min i k)
  | 0, i => by rw [Nat.min_zero]; rfl
  | k + 1, i => by
    by_cases h : i ≤ k
    · rw [adaptivePath_succ_fst, extendPath_of_le _ _ h, adaptivePath_fst_apply ν G x₀ ξ k i,
        min_eq_left h, min_eq_left (h.trans (Nat.le_succ k))]
    · have hki : k < i := Nat.lt_of_not_le h
      have hm : min i (k + 1) = k + 1 := by omega
      rw [hm, adaptiveSeq, adaptivePath_succ_fst, extendPath_of_lt _ _ hki,
        extendPath_of_lt _ _ (Nat.lt_succ_self k)]

/-- The fresh path stopped at step `k` is `(x_{min(i,k)})_i` (Giles 2015, §5.6). -/
lemma freshPath_apply (G : ℕ → (ℕ → X) → E → X) (x₀ : X) (ζ : ℕ → E) :
    ∀ k i, freshPath G x₀ ζ k i = freshSeq G x₀ ζ (min i k)
  | 0, i => by rw [Nat.min_zero]; rfl
  | k + 1, i => by
    by_cases h : i ≤ k
    · rw [freshPath_succ, extendPath_of_le _ _ h, freshPath_apply G x₀ ζ k i,
        min_eq_left h, min_eq_left (h.trans (Nat.le_succ k))]
    · have hki : k < i := Nat.lt_of_not_le h
      have hm : min i (k + 1) = k + 1 := by omega
      rw [hm, freshSeq, freshPath_succ, extendPath_of_lt _ _ hki,
        extendPath_of_lt _ _ (Nat.lt_succ_self k)]

variable [MeasurableSpace X]

/-- The values of a path at finitely many indices are those of the path stopped at the largest of
them (Giles 2015, §5.6: a payoff of the path up to step `K` only sees the stopped path). -/
lemma map_restrict_eq_map_stop {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {S : Ω → ℕ → X} (hS : Measurable S) (I : Finset ℕ) :
    (P.map S).map I.restrict =
      (P.map (fun ω i => S ω (min i (I.sup id)))).map fun (y : ℕ → X) (i : I) => y i := by
  have hr : Measurable fun (y : ℕ → X) (i : I) => y i :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hSK : Measurable fun ω (i : ℕ) => S ω (min i (I.sup id)) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp hS
  rw [Measure.map_map (Finset.measurable_restrict I) hS, Measure.map_map hr hSK]
  congr 1
  funext ω i
  have hi : (i : ℕ) ≤ I.sup id := Finset.le_sup (f := id) i.2
  simp only [Function.comp_apply, Finset.restrict]
  rw [min_eq_left hi]

/-- Two random sequences whose stopped versions `(S_{min(i,k)})_i` have the same law for every
`k` have the same law (Giles 2015, §5.6: the law of a whole path is determined by the laws of its
finite pieces; Kolmogorov's uniqueness, `IsProjectiveLimit.unique`). -/
lemma map_eq_of_forall_map_stop_eq {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsFiniteMeasure P₁] [IsFiniteMeasure P₂]
    {S₁ : Ω₁ → ℕ → X} {S₂ : Ω₂ → ℕ → X} (h₁ : Measurable S₁) (h₂ : Measurable S₂)
    (h : ∀ k, P₁.map (fun ω i => S₁ ω (min i k)) = P₂.map (fun ω i => S₂ ω (min i k))) :
    P₁.map S₁ = P₂.map S₂ := by
  refine IsProjectiveLimit.unique (P := fun I => (P₂.map S₂).map I.restrict)
    (fun I => ?_) (fun I => rfl)
  show (P₁.map S₁).map I.restrict = (P₂.map S₂).map I.restrict
  rw [map_restrict_eq_map_stop P₁ h₁, map_restrict_eq_map_stop P₂ h₂, h]

end WholePath

section Measurability

variable {X E E' : Type*} [MeasurableSpace X] [MeasurableSpace E] [MeasurableSpace E']

/-- The adaptive path with its unused base increments is a measurable function of the base
increments (Giles 2015, §5.6). -/
lemma measurable_adaptivePath [AddCommMonoid E] [MeasurableAdd₂ E] {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → E → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (x₀ : X) :
    ∀ k, Measurable fun ξ : ℕ → E =>
      ((adaptivePath ν G x₀ ξ k).1, shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ)
  | 0 => by
    have e : (fun ξ : ℕ → E =>
        ((adaptivePath ν G x₀ ξ 0).1, shiftSeq (adaptivePath ν G x₀ ξ 0).2 ξ)) =
        fun ξ => ((fun _ => x₀), ξ) := by
      funext ξ
      show ((fun _ => x₀), shiftSeq 0 ξ) = ((fun _ => x₀), ξ)
      rw [shiftSeq_zero]
    rw [e]
    exact measurable_const.prodMk measurable_id
  | k + 1 => by
    have e : (fun ξ : ℕ → E =>
        ((adaptivePath ν G x₀ ξ (k + 1)).1, shiftSeq (adaptivePath ν G x₀ ξ (k + 1)).2 ξ)) =
        adaptiveStep ν G k ∘ fun ξ =>
          ((adaptivePath ν G x₀ ξ k).1, shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ) :=
      funext fun ξ => adaptivePath_step ν G x₀ ξ k
    rw [e]
    exact (measurable_adaptiveStep (hν k) (hG k)).comp (measurable_adaptivePath hν hG x₀ k)

/-- The values of the adaptive path are a measurable function of the base increments (Giles 2015,
§5.6). -/
lemma measurable_adaptiveSeq [AddCommMonoid E] [MeasurableAdd₂ E] {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → E → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (x₀ : X) :
    Measurable (adaptiveSeq ν G x₀) :=
  measurable_pi_lambda _ fun k => by
    have h := measurable_fst.comp (measurable_adaptivePath hν hG x₀ k)
    exact (measurable_pi_apply k).comp h

/-- The increment of step `k` is a measurable function of the base increments (Giles 2015,
§5.6). -/
lemma measurable_adaptiveIncr [AddCommMonoid E] [MeasurableAdd₂ E] {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → E → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × E => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    Measurable fun ξ => adaptiveIncr ν G x₀ ξ k := by
  have hf : Measurable fun p : (ℕ → X) × (ℕ → E) => ∑ i ∈ range (ν k p.1), p.2 i :=
    measurable_blockSum_uncurry.comp (((hν k).comp measurable_fst).prodMk measurable_snd)
  have e : (fun ξ => adaptiveIncr ν G x₀ ξ k) =
      (fun p : (ℕ → X) × (ℕ → E) => ∑ i ∈ range (ν k p.1), p.2 i) ∘
        fun ξ => ((adaptivePath ν G x₀ ξ k).1, shiftSeq (adaptivePath ν G x₀ ξ k).2 ξ) :=
    funext fun ξ => adaptiveIncr_eq ν G x₀ ξ k
  rw [e]
  exact hf.comp (measurable_adaptivePath hν hG x₀ k)

/-- The fresh path stopped at step `k` is a measurable function of the variates (Giles 2015,
§5.6). -/
lemma measurable_freshPath {G : ℕ → (ℕ → X) → E' → X}
    (hG : ∀ k, Measurable fun p : (ℕ → X) × E' => G k p.1 p.2) (x₀ : X) :
    ∀ k, Measurable fun ζ : ℕ → E' => freshPath G x₀ ζ k
  | 0 => measurable_const
  | k + 1 => by
    have e : (fun ζ : ℕ → E' => freshPath G x₀ ζ (k + 1)) =
        (fun p : (ℕ → X) × E' => extendPath k p.1 (G k p.1 p.2)) ∘
          fun ζ => (freshPath G x₀ ζ k, ζ k) :=
      funext fun ζ => freshPath_succ G x₀ ζ k
    rw [e]
    exact ((measurable_extendPath k).comp (measurable_fst.prodMk (hG k))).comp
      ((measurable_freshPath hG x₀ k).prodMk (measurable_pi_apply k))

/-- The values of the fresh path are a measurable function of the variates (Giles 2015, §5.6). -/
lemma measurable_freshSeq {G : ℕ → (ℕ → X) → E' → X}
    (hG : ∀ k, Measurable fun p : (ℕ → X) × E' => G k p.1 p.2) (x₀ : X) :
    Measurable (freshSeq G x₀) :=
  measurable_pi_lambda _ fun k => (measurable_pi_apply k).comp (measurable_freshPath hG x₀ k)

end Measurability

section Comparison

variable {X E E' : Type*} [MeasurableSpace X] [MeasurableSpace E] [MeasurableSpace E']
  [AddCommMonoid E] [MeasurableAdd₂ E]

/-- **Summed base increments or fresh variates: the same law of the whole path** (Giles 2015,
§5.6, p. 44, lines 1924–1929, and Algorithm 3: "It may appear that this would cause difficulties
in the MLMC implementation, but Figure 5.9 tries to illustrate that it does not. … The independent
Brownian increments can be simulated for each time interval, and summed to give `W(t)` at the
required times").  The base increments `ξ_i` are i.i.d. with law `μ`, the variates `ζ_k` i.i.d.
with law `ρ`, and the fresh scheme applies the update to `s k y (ζ_k)`.  If `s k y (ζ)` has, for
every path `y` so far, the law of a sum of `ν_k(y)` base increments (`hρ`), then the whole
adaptive path `(x_k)_{k∈ℕ}` built from the summed base increments and the whole path of the fresh
scheme have the same law (a measure on `ℕ → X`). -/
theorem map_adaptiveSeq_eq_freshSeq (μ : Measure E) [IsProbabilityMeasure μ] (ρ : Measure E')
    [IsProbabilityMeasure ρ] {ν : ℕ → (ℕ → X) → ℕ} {G : ℕ → (ℕ → X) → E → X}
    (hν : ∀ k, Measurable (ν k)) (hG : ∀ k, Measurable fun p : (ℕ → X) × E => G k p.1 p.2)
    {s : ℕ → (ℕ → X) → E' → E} (hs : ∀ k, Measurable fun p : (ℕ → X) × E' => s k p.1 p.2)
    (hρ : ∀ k y, ρ.map (s k y) = blockLaw μ (ν k y)) (x₀ : X) :
    (Measure.infinitePi fun _ => μ).map (adaptiveSeq ν G x₀) =
      (Measure.infinitePi fun _ => ρ).map (freshSeq (fun k y z => G k y (s k y z)) x₀) := by
  have hG' : ∀ k, Measurable fun p : (ℕ → X) × E' => G k p.1 (s k p.1 p.2) :=
    fun k => (hG k).comp (measurable_fst.prodMk (hs k))
  have hsk : ∀ k y, Measurable (s k y) :=
    fun k y => (hs k).comp (measurable_const.prodMk measurable_id)
  refine map_eq_of_forall_map_stop_eq (measurable_adaptiveSeq hν hG x₀)
    (measurable_freshSeq hG' x₀) fun k => ?_
  have e₁ : (fun ξ (i : ℕ) => adaptiveSeq ν G x₀ ξ (min i k)) =
      fun ξ => (adaptivePath ν G x₀ ξ k).1 := by
    funext ξ i
    exact (adaptivePath_fst_apply ν G x₀ ξ k i).symm
  have e₂ : (fun ζ (i : ℕ) => freshSeq (fun k y z => G k y (s k y z)) x₀ ζ (min i k)) =
      fun ζ => freshPath (fun k y z => G k y (s k y z)) x₀ ζ k := by
    funext ζ i
    exact (freshPath_apply _ x₀ ζ k i).symm
  rw [e₁, e₂, map_adaptivePath μ hν hG x₀ k, map_freshPath ρ hG' x₀ k,
    adaptiveLaw_comp (fun _ _ => ρ) hG s hsk x₀]
  congr 1
  funext j y
  exact (hρ j y).symm

end Comparison

/-! ### Random variables on any probability space -/

section Transfer

variable {Ω E Z : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace Z]

/-- A measurable function of an i.i.d. sequence has the law it has under the product measure
(Giles 2015, §5.6: the base increments may live on any probability space). -/
lemma map_comp_of_iid {P : Measure Ω} {μ : Measure E} {ξ : ℕ → Ω → E}
    (hind : iIndepFun ξ P) (hξ : ∀ i, HasLaw (ξ i) μ P) {F : (ℕ → E) → Z} (hF : Measurable F) :
    P.map (fun ω => F fun i => ξ i ω) = (Measure.infinitePi fun _ => μ).map F := by
  have hΞ : HasLaw (fun ω i => ξ i ω) (Measure.infinitePi fun _ => μ) P :=
    hind.hasLaw_infinitePi hξ (aemeasurable_pi_iff.2 fun i => (hξ i).aemeasurable)
  exact ((⟨hF.aemeasurable, rfl⟩ :
    HasLaw F ((Measure.infinitePi fun _ => μ).map F) (Measure.infinitePi fun _ => μ)).comp
      hΞ).map_eq

end Transfer

section IntegralTransfer

variable {Ω₁ Ω₂ Z : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Z]

/-- Payoffs of two random variables with the same law have the same expectation, and one is
integrable iff the other is (Giles 2015, §2.1, (2.4)). -/
lemma integral_comp_eq_of_map_eq_map {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {f₁ : Ω₁ → Z}
    {f₂ : Ω₂ → Z} (hf₁ : AEMeasurable f₁ P₁) (hf₂ : AEMeasurable f₂ P₂)
    (h : P₁.map f₁ = P₂.map f₂) {Φ : Z → ℝ} (hΦ : AEStronglyMeasurable Φ (P₁.map f₁)) :
    (Integrable (fun ω => Φ (f₁ ω)) P₁ ↔ Integrable (fun ω => Φ (f₂ ω)) P₂) ∧
      ∫ ω, Φ (f₁ ω) ∂P₁ = ∫ ω, Φ (f₂ ω) ∂P₂ := by
  have hΦ₂ : AEStronglyMeasurable Φ (P₂.map f₂) := h ▸ hΦ
  constructor
  · show Integrable (Φ ∘ f₁) P₁ ↔ Integrable (Φ ∘ f₂) P₂
    rw [← integrable_map_measure hΦ hf₁, ← integrable_map_measure hΦ₂ hf₂, h]
  · rw [← integral_map hf₁ hΦ, ← integral_map hf₂ hΦ₂, h]

end IntegralTransfer

/-! ### Brownian increments: (1) the conditional law and the law of the path -/

section Gaussian

/-- A sum of `n` independent `N(0, δ)` base increments is `N(0, nδ)` (Giles 2015, §5.6, p. 44,
lines 1928–1929: the Brownian increments of the base intervals "summed to give `W(t)`"). -/
lemma blockLaw_gaussianReal (δ : ℝ≥0) (n : ℕ) :
    blockLaw (gaussianReal 0 δ) n = gaussianReal 0 (n * δ) := by
  have hind : iIndepFun (fun i (ξ : ℕ → ℝ) => ξ i)
      (Measure.infinitePi fun _ => gaussianReal 0 δ) :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) fun _ => measurable_id
  have hX : ∀ i, HasLaw (fun ξ : ℕ → ℝ => ξ i) (gaussianReal 0 δ)
      (Measure.infinitePi fun _ => gaussianReal 0 δ) := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  rw [blockLaw, (hasLaw_finsetSum_gaussianReal hX hind (range n)).map_eq]
  simp

/-- `√h Z ~ N(0, h)` for `Z ~ N(0, 1)` (Giles 2015, §5.6, Algorithm 3: "`∆W := √h Z`"). -/
lemma gaussianReal_map_sqrt_mul (h : ℝ≥0) :
    (gaussianReal 0 1).map (fun z => Real.sqrt h * z) = gaussianReal 0 h := by
  have hY : HasLaw (fun z : ℝ => z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have h1 := (hasLaw_sqrt_mul (μ := gaussianReal 0 1) (h.coe_nonneg) hY).map_eq
  rwa [Real.toNNReal_coe] at h1

/-- The Gaussian kernel `n ↦ N(0, nδ)`: the law of the Brownian increment over `n` base intervals
of length `δ` (Giles 2015, §5.6). -/
noncomputable def gaussianStepKernel (δ : ℝ≥0) : Kernel ℕ ℝ :=
  Kernel.ofFunOfCountable fun n => gaussianReal 0 (n * δ)

/-- The block-sum kernel of `N(0, δ)` base increments is `n ↦ N(0, nδ)` (Giles 2015, §5.6). -/
lemma blockKernel_gaussianReal (δ : ℝ≥0) :
    blockKernel (gaussianReal 0 δ) = gaussianStepKernel δ :=
  Kernel.ext fun n => blockLaw_gaussianReal δ n

/-- `n ↦ N(0, nδ)` is a Markov kernel (Giles 2015, §5.6). -/
lemma isMarkovKernel_gaussianStepKernel (δ : ℝ≥0) : IsMarkovKernel (gaussianStepKernel δ) :=
  ⟨fun n => by
    show IsProbabilityMeasure (gaussianReal 0 (n * δ))
    infer_instance⟩

variable {X : Type*} [MeasurableSpace X] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {δ : ℝ≥0} {ξ : ℕ → Ω → ℝ} {ζ : ℕ → Ω' → ℝ}

/-- **Given the path so far, the Brownian increment over an adaptively chosen step is
`N(0, n_k δ)`** (Giles 2015, §5.6, p. 44, lines 1917–1929: steps "`h_ℓ = 2^{−ℓ} H(Ŝ_n)`" that
depend on the path, and "The independent Brownian increments can be simulated for each time
interval, and summed").  The base increments `ξ_0, ξ_1, …` are independent `N(0, δ)` (the
Brownian increments over a fixed base grid of spacing `δ`), and step `k` takes `n_k = ν_k(y_k)`
base intervals chosen from the path `y_k` so far (any measurable rule `ν_k`; the update `G_k` is
any measurable function).  Then the pair (path so far, increment `ΔW_k` over the chosen step) has
the law `L_k ⊗ₘ κ_k`, where `L_k` is the law of the path so far and `κ_k(y) = N(0, ν_k(y) δ)`:
given the path so far, `ΔW_k ~ N(0, h_k)` with `h_k = n_k δ` the chosen step.  (This is
Mathlib's `HasCondDistrib ΔW_k y_k κ_k P`, unfolded; `adaptiveIncr_condDistrib_gaussian` states
it with `condDistrib`.)  Step sizes are multiples of the base spacing `δ`.  "The path so far" is
the path `y_k` of the scheme (the σ-algebra `σ(y_k)`): the rule sees the base increments only
through `y_k`, i.e. through the step increments `ΔW_j`, `j < k`.  Given the whole history
`(ξ_i)_{i<τ_k}` of the base increments the increment is still `N(0, n_k δ)`
(`adaptiveIncr_condLaw_hist_gaussian`), also for rules that depend on that history
(`histIncr_condLaw_gaussian`). -/
theorem adaptiveIncr_condLaw_gaussian (hind : iIndepFun ξ P)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P) {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → ℝ → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × ℝ => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    P.map (fun ω => ((adaptivePath ν G x₀ (fun i => ξ i ω) k).1,
        adaptiveIncr ν G x₀ (fun i => ξ i ω) k)) =
      (P.map fun ω => (adaptivePath ν G x₀ (fun i => ξ i ω) k).1) ⊗ₘ
        (gaussianStepKernel δ).comap (ν k) (hν k) := by
  have h1 : Measurable fun ξ : ℕ → ℝ => (adaptivePath ν G x₀ ξ k).1 :=
    (measurable_adaptivePath hν hG x₀ k).fst
  have h2 : Measurable fun ξ : ℕ → ℝ =>
      ((adaptivePath ν G x₀ ξ k).1, adaptiveIncr ν G x₀ ξ k) :=
    h1.prodMk (measurable_adaptiveIncr hν hG x₀ k)
  rw [map_comp_of_iid hind hξ h2, map_comp_of_iid hind hξ h1,
    map_adaptiveIncr _ hν hG x₀ k, blockKernel_gaussianReal]

/-- **The conditional distribution of an adaptive Brownian increment** (Giles 2015, §5.6, p. 44,
lines 1917–1929: "an adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)` … The independent Brownian
increments can be simulated for each time interval").  In the setting of
`adaptiveIncr_condLaw_gaussian`, the conditional distribution of the increment `ΔW_k` over the
chosen step given the path `y_k` so far is, for almost every `y` (under the law of `y_k`), the
normal law `N(0, ν_k(y) δ)`.  The conditioning is on the path `y_k` of the scheme (the σ-algebra
`σ(y_k)`), through which alone the rule sees the base increments; for the whole history
`(ξ_i)_{i<τ_k}` see `adaptiveIncr_condLaw_hist_gaussian`. -/
theorem adaptiveIncr_condDistrib_gaussian [IsProbabilityMeasure P] (hind : iIndepFun ξ P)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P) {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → ℝ → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × ℝ => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    condDistrib (fun ω => adaptiveIncr ν G x₀ (fun i => ξ i ω) k)
        (fun ω => (adaptivePath ν G x₀ (fun i => ξ i ω) k).1) P
      =ᵐ[P.map fun ω => (adaptivePath ν G x₀ (fun i => ξ i ω) k).1]
        (gaussianStepKernel δ).comap (ν k) (hν k) := by
  have := isMarkovKernel_gaussianStepKernel δ
  have hΞ : AEMeasurable (fun ω i => ξ i ω) P :=
    aemeasurable_pi_iff.2 fun i => (hξ i).aemeasurable
  exact condDistrib_ae_eq_of_measure_eq_compProd _
    ((measurable_adaptiveIncr hν hG x₀ k).comp_aemeasurable hΞ)
    (adaptiveIncr_condLaw_gaussian hind hξ hν hG x₀ k)

/-- **The law of the adaptive path built from summed Brownian increments** (Giles 2015, §5.6,
p. 44, lines 1917–1929: "with an adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)` … The
independent Brownian increments can be simulated for each time interval, and summed to give
`W(t)` at the required times").  With independent `N(0, δ)` base increments, the path stopped at
step `k` has the law `adaptiveLaw (fun j y => N(0, ν_j(y) δ)) G x₀ k` of the scheme whose `j`-th
increment, given the path `y` so far, is `N(0, h_j)` with the chosen step `h_j = ν_j(y) δ`. -/
theorem adaptivePath_law_gaussian (hind : iIndepFun ξ P)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P) {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → ℝ → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × ℝ => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    P.map (fun ω => (adaptivePath ν G x₀ (fun i => ξ i ω) k).1) =
      adaptiveLaw (fun j y => gaussianReal 0 (ν j y * δ)) G x₀ k := by
  have h1 : Measurable fun ξ : ℕ → ℝ => (adaptivePath ν G x₀ ξ k).1 :=
    (measurable_adaptivePath hν hG x₀ k).fst
  rw [map_comp_of_iid hind hξ h1, map_adaptivePath _ hν hG x₀ k]
  congr 1
  funext j y
  exact blockLaw_gaussianReal δ (ν j y)

/-- **The law of the adaptive scheme driven by fresh Brownian increments** (Giles 2015, §5.6,
Algorithm 3, p. 45: "`h := t − t_old`, `∆W := √h Z`").  With independent standard normal
`ζ_0, ζ_1, …` and a measurable step rule `h_j(y) ≥ 0`, the scheme
`x_{j+1} = G_j(y_j, √(h_j(y_j)) ζ_j)` stopped at step `k` has the law
`adaptiveLaw (fun j y => N(0, h_j(y))) G x₀ k` — the law of `adaptivePath_law_gaussian` when
`h_j = ν_j δ`. -/
theorem freshPath_law_gaussian (hζind : iIndepFun ζ P')
    (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P') {G : ℕ → (ℕ → X) → ℝ → X}
    (hG : ∀ k, Measurable fun p : (ℕ → X) × ℝ => G k p.1 p.2) {h : ℕ → (ℕ → X) → ℝ≥0}
    (hh : ∀ k, Measurable (h k)) (x₀ : X) (k : ℕ) :
    P'.map (fun ω => freshPath (fun j y z => G j y (Real.sqrt (h j y) * z)) x₀
        (fun i => ζ i ω) k) =
      adaptiveLaw (fun j y => gaussianReal 0 (h j y)) G x₀ k := by
  have hG' : ∀ j, Measurable fun p : (ℕ → X) × ℝ => G j p.1 (Real.sqrt (h j p.1) * p.2) :=
    fun j => (hG j).comp (measurable_fst.prodMk
      ((measurable_coe_nnreal_real.comp ((hh j).comp measurable_fst)).sqrt.mul
        measurable_snd))
  rw [map_comp_of_iid hζind hζ (measurable_freshPath hG' x₀ k),
    map_freshPath (gaussianReal 0 1) hG' x₀ k,
    adaptiveLaw_comp (fun _ _ => gaussianReal 0 1) hG (fun j y z => Real.sqrt (h j y) * z)
      (fun j y => measurable_const.mul measurable_id) x₀]
  congr 1
  funext j y
  exact gaussianReal_map_sqrt_mul (h j y)

/-- **The adaptive path built from summed base increments has the law of the adaptive scheme
driven by fresh Brownian increments** (Giles 2015, §5.6, p. 44, lines 1917–1930: "It may appear
that this would cause difficulties in the MLMC implementation, but Figure 5.9 tries to
illustrate that it does not. The underlying Brownian path needs to be sampled at a set of times
which are the union of the simulation times used by the coarse and fine path. The independent
Brownian increments can be simulated for each time interval, and summed to give `W(t)` at the
required times").  The base increments `ξ_i` are independent `N(0, δ)` on `(Ω, P)`; step `k` takes
`ν_k(y_k)` base intervals, chosen by a measurable rule from the path `y_k` so far, and its
increment is the sum of the base increments over them.  The `ζ_k` are independent `N(0, 1)` on
`(Ω', P')`, and the fresh scheme uses `√(ν_k(y_k) δ) ζ_k` for step `k`.  Then the whole paths
`(x_k)_{k∈ℕ}` of the two schemes have the same law.  Step sizes are multiples of `δ`. -/
theorem adaptiveSeq_law_eq_fresh (hind : iIndepFun ξ P)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P) (hζind : iIndepFun ζ P')
    (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P') {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → ℝ → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × ℝ => G k p.1 p.2) (x₀ : X) :
    P.map (fun ω => adaptiveSeq ν G x₀ (fun i => ξ i ω)) =
      P'.map (fun ω => freshSeq (fun k y z => G k y (Real.sqrt (ν k y * δ) * z)) x₀
        (fun i => ζ i ω)) := by
  have hs : ∀ k, Measurable fun p : (ℕ → X) × ℝ => Real.sqrt (ν k p.1 * δ) * p.2 := fun k =>
    (((measurable_from_nat.comp ((hν k).comp measurable_fst)).mul_const _).sqrt).mul
      measurable_snd
  have hG' : ∀ k, Measurable fun p : (ℕ → X) × ℝ =>
      G k p.1 (Real.sqrt (ν k p.1 * δ) * p.2) :=
    fun k => (hG k).comp (measurable_fst.prodMk (hs k))
  rw [map_comp_of_iid hind hξ (measurable_adaptiveSeq hν hG x₀),
    map_comp_of_iid hζind hζ (measurable_freshSeq hG' x₀)]
  refine map_adaptiveSeq_eq_freshSeq (gaussianReal 0 δ) (gaussianReal 0 1) hν hG hs
    (fun k y => ?_) x₀
  have h := gaussianReal_map_sqrt_mul ((ν k y : ℝ≥0) * δ)
  rw [NNReal.coe_mul, NNReal.coe_natCast] at h
  rw [h, blockLaw_gaussianReal]

/-- **The (step, increment) pairs of an adaptive scheme** (Giles 2015, §5.6, p. 44,
lines 1917–1929: "an adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)` … The independent Brownian
increments can be simulated for each time interval, and summed to give `W(t)` at the required
times").  Here the path records the pairs: `x_0 = (0, 0)` and `x_{j+1} = (n_j, ΔW_j)`, where the
number `n_j = ν_j(y_j)` of base intervals of step `j` is chosen by a measurable rule from the
earlier pairs.  Built from independent `N(0, δ)` base increments (`ΔW_j` the sum over the step) or
from fresh increments `ΔW_j = √(n_j δ) ζ_j` with independent standard normal `ζ_j`, the sequences
of pairs have the same law; in particular so do the first `K` pairs, for every `K`. -/
theorem adaptivePairs_law_eq_fresh (hind : iIndepFun ξ P)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P) (hζind : iIndepFun ζ P')
    (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P') {ν : ℕ → (ℕ → ℕ × ℝ) → ℕ}
    (hν : ∀ k, Measurable (ν k)) :
    P.map (fun ω => adaptiveSeq ν (fun k y e => (ν k y, e)) (0, 0) (fun i => ξ i ω)) =
      P'.map (fun ω => freshSeq (fun k y z => (ν k y, Real.sqrt (ν k y * δ) * z)) (0, 0)
        (fun i => ζ i ω)) :=
  adaptiveSeq_law_eq_fresh hind hξ hζind hζ hν
    (fun k => ((hν k).comp measurable_fst).prodMk measurable_snd) (0, 0)

end Gaussian

/-! ### The adaptive Euler–Maruyama scheme: (1) and (2), with (2.4) -/

section EulerMaruyama

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {δ : ℝ≥0} {ξ : ℕ → Ω → ℝ} {ζ : ℕ → Ω' → ℝ}

/-- One Euler–Maruyama step of the time–state pair `x = (t, S)` with step `h` and Brownian
increment `ΔW` (Giles 2015, §5.1 and §5.6; Haas–Giles 2025, (2)):
`(t + h, S + a(S, t) h + b(S, t) ΔW)`. -/
def adaptiveEMStep (a b : ℝ → ℝ → ℝ) (h : ℝ) (x : ℝ × ℝ) (dW : ℝ) : ℝ × ℝ :=
  (x.1 + h, x.2 + a x.2 x.1 * h + b x.2 x.1 * dW)

/-- **The adaptive Euler–Maruyama path on the base grid** (Giles 2015, §5.6, p. 44,
lines 1917–1929: "an adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)`").  The state is the
pair `(t_k, Ŝ_k)`, started at `(0, S₀)`; step `k` has `ν(t_k, Ŝ_k)` base intervals of length `δ`,
i.e. the step `h_k = ν(t_k, Ŝ_k) δ`, and its Brownian increment is the sum of the base increments
`ξ_i` over it.  (The rule `ν` may include the truncation at `T`: for the scheme of the paper on
level `ℓ`, `ν(t, S) δ = min(2^{−ℓ} H(S), T − t)`, provided `2^{−ℓ} H(S)` and `T` are multiples of
`δ`.) -/
noncomputable def adaptiveEM (a b : ℝ → ℝ → ℝ) (ν : ℝ × ℝ → ℕ) (δ : ℝ≥0) (S₀ : ℝ)
    (ξ : ℕ → ℝ) : ℕ → ℝ × ℝ :=
  adaptiveSeq (fun k y => ν (y k)) (fun k y dW => adaptiveEMStep a b (ν (y k) * δ) (y k) dW)
    (0, S₀) ξ

/-- The adaptive Euler–Maruyama scheme with fresh Brownian increments (Giles 2015, §5.6 and
Algorithm 3: "`∆W := √h Z`"): the step from `(t_k, Ŝ_k)` is `h_k = H(t_k, Ŝ_k)` and its Brownian
increment is `√(h_k) Z_k` with a fresh `Z_k`. -/
noncomputable def freshEM (a b : ℝ → ℝ → ℝ) (H : ℝ × ℝ → ℝ≥0) (S₀ : ℝ) (ζ : ℕ → ℝ) :
    ℕ → ℝ × ℝ :=
  freshSeq (fun k y z => adaptiveEMStep a b (H (y k)) (y k) (Real.sqrt (H (y k)) * z)) (0, S₀) ζ

/-- The Euler–Maruyama step is jointly measurable in the step, the state and the increment
(Giles 2015, §5.6). -/
lemma measurable_adaptiveEMStep {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) :
    Measurable fun p : ℝ × (ℝ × ℝ) × ℝ => adaptiveEMStep a b p.1 p.2.1 p.2.2 := by
  have ha' : Measurable fun p : ℝ × (ℝ × ℝ) × ℝ => a p.2.1.2 p.2.1.1 :=
    ha.comp ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd)))
  have hb' : Measurable fun p : ℝ × (ℝ × ℝ) × ℝ => b p.2.1.2 p.2.1.1 :=
    hb.comp ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd)))
  exact ((measurable_fst.comp (measurable_fst.comp measurable_snd)).add measurable_fst).prodMk
    (((measurable_snd.comp (measurable_fst.comp measurable_snd)).add
      (ha'.mul measurable_fst)).add (hb'.mul (measurable_snd.comp measurable_snd)))

/-- The adaptive Euler–Maruyama path is a measurable function of the base increments (Giles 2015,
§5.6). -/
lemma measurable_adaptiveEM {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {ν : ℝ × ℝ → ℕ} (hν : Measurable ν) (δ : ℝ≥0)
    (S₀ : ℝ) : Measurable (adaptiveEM a b ν δ S₀) := by
  have hν' : ∀ k, Measurable fun y : ℕ → ℝ × ℝ => ν (y k) :=
    fun k => hν.comp (measurable_pi_apply k)
  have hG : ∀ k, Measurable fun p : (ℕ → ℝ × ℝ) × ℝ =>
      adaptiveEMStep a b (ν (p.1 k) * δ) (p.1 k) p.2 := fun k =>
    (measurable_adaptiveEMStep ha hb).comp
      (((measurable_from_nat.comp ((hν' k).comp measurable_fst)).mul_const _).prodMk
        (((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd))
  exact measurable_adaptiveSeq hν' hG (0, S₀)

/-- **The adaptive Euler–Maruyama path has the law of the single-level adaptive scheme** (Giles
2015, §5.6, p. 44, lines 1917–1930, Figure 5.9 and Algorithm 3: "with an adaptive timestep of the
form `h_ℓ = 2^{−ℓ} H(Ŝ_n)`, where `H(S)` is independent of level … The independent Brownian
increments can be simulated for each time interval, and summed to give `W(t)` at the required
times").  The drift `a(S, t)` and the volatility `b(S, t)` are measurable, the base increments
`ξ_i` independent `N(0, δ)`, the rule `ν` measurable, and `H = ν δ` is the step as a function of
`(t, S)`.  Then the whole adaptive Euler–Maruyama path `(t_k, Ŝ_k)_{k∈ℕ}` built from the summed
base increments has the law of the adaptive scheme with steps `H(t_k, Ŝ_k)` driven by fresh
increments `√(H(t_k, Ŝ_k)) ζ_k`, with independent standard normal `ζ_k`.  Step sizes are
multiples of `δ`. -/
theorem adaptiveEM_law_eq_freshEM {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {ν : ℝ × ℝ → ℕ} (hν : Measurable ν)
    {H : ℝ × ℝ → ℝ≥0} (hH : ∀ x, H x = ν x * δ) (hind : iIndepFun ξ P)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P) (hζind : iIndepFun ζ P')
    (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P') (S₀ : ℝ) :
    P.map (fun ω => adaptiveEM a b ν δ S₀ (fun i => ξ i ω)) =
      P'.map (fun ω => freshEM a b H S₀ (fun i => ζ i ω)) := by
  have hν' : ∀ k, Measurable fun y : ℕ → ℝ × ℝ => ν (y k) :=
    fun k => hν.comp (measurable_pi_apply k)
  have hG : ∀ k, Measurable fun p : (ℕ → ℝ × ℝ) × ℝ =>
      adaptiveEMStep a b (ν (p.1 k) * δ) (p.1 k) p.2 := fun k =>
    (measurable_adaptiveEMStep ha hb).comp
      (((measurable_from_nat.comp ((hν' k).comp measurable_fst)).mul_const _).prodMk
        (((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd))
  have e : (fun k (y : ℕ → ℝ × ℝ) z =>
      adaptiveEMStep a b (H (y k)) (y k) (Real.sqrt (H (y k)) * z)) =
      fun k y z => adaptiveEMStep a b (ν (y k) * δ) (y k) (Real.sqrt (ν (y k) * δ) * z) := by
    funext k y z
    rw [hH, NNReal.coe_mul, NNReal.coe_natCast]
  unfold adaptiveEM freshEM
  rw [e]
  exact adaptiveSeq_law_eq_fresh hind hξ hζind hζ hν' hG (0, S₀)

/-- **Fine and coarse paths with independent adaptation on the same base increments each have
their single-level law** (Giles 2015, §5.6, p. 44, lines 1917–1930: "it uses a completely
independent adaptation on each level of refinement … This results in timesteps which are not
naturally nested. It may appear that this would cause difficulties in the MLMC implementation,
but Figure 5.9 tries to illustrate that it does not").  The fine path uses the rule `νf` and the
coarse path the rule `νc` (steps `Hf = νf δ`, `Hc = νc δ`), both computed from the same
independent `N(0, δ)` base increments `ξ_i` (this is the coupling of the two levels).  Each of the
two paths has the law of its own adaptive scheme driven by fresh Brownian increments.  The
statement gives each path's own law; their joint law is the law of the pair computed from the
same `ξ`, which Algorithm 3 produces (`algorithm3_EM_joint_law`). -/
theorem adaptiveEM_fine_coarse {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {νf νc : ℝ × ℝ → ℕ} (hνf : Measurable νf)
    (hνc : Measurable νc) {Hf Hc : ℝ × ℝ → ℝ≥0} (hHf : ∀ x, Hf x = νf x * δ)
    (hHc : ∀ x, Hc x = νc x * δ) (hind : iIndepFun ξ P)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P) (hζind : iIndepFun ζ P')
    (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P') (S₀ : ℝ) :
    P.map (fun ω => adaptiveEM a b νf δ S₀ (fun i => ξ i ω)) =
        P'.map (fun ω => freshEM a b Hf S₀ (fun i => ζ i ω)) ∧
      P.map (fun ω => adaptiveEM a b νc δ S₀ (fun i => ξ i ω)) =
        P'.map (fun ω => freshEM a b Hc S₀ (fun i => ζ i ω)) :=
  ⟨adaptiveEM_law_eq_freshEM ha hb hνf hHf hind hξ hζind hζ S₀,
    adaptiveEM_law_eq_freshEM ha hb hνc hHc hind hξ hζind hζ S₀⟩

/-- **The identity (2.4) for non-nested adaptive time steps** (Giles 2015, §2.1, p. 8, line 381:
"Provided we maintain the identity `E[P^f_ℓ] = E[P^c_ℓ]` (2.4) so that the expectation on level `ℓ`
is the same for the two approximations"; §5.6, p. 44, lines 1917–1930).  The level-`ℓ` path is
computed as the fine path of a level-`ℓ` sample, on a base grid of spacing `δ₁` with the rule
`ν₁`, and as the coarse path of a level-`(ℓ + 1)` sample, on a finer base grid `δ₂` (fine enough
for level `ℓ + 1` too) with the rule `ν₂`.  Both rules give the same step, `ν₁ δ₁ = ν₂ δ₂`.  Then
for every payoff `Φ` of the level-`ℓ` path (a.e.-strongly measurable for its law),
`P^f_ℓ = Φ(path₁)` is integrable iff `P^c_ℓ = Φ(path₂)` is, and `E[P^f_ℓ] = E[P^c_ℓ]`. -/
theorem adaptiveEM_2_4 {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {a b : ℝ → ℝ → ℝ}
    (ha : Measurable (Function.uncurry a)) (hb : Measurable (Function.uncurry b))
    {ν₁ ν₂ : ℝ × ℝ → ℕ} (hν₁ : Measurable ν₁) (hν₂ : Measurable ν₂) {δ₁ δ₂ : ℝ≥0}
    (hδ : ∀ x, (ν₁ x : ℝ≥0) * δ₁ = ν₂ x * δ₂) {ξ₁ : ℕ → Ω₁ → ℝ} {ξ₂ : ℕ → Ω₂ → ℝ}
    (hind₁ : iIndepFun ξ₁ P₁) (hξ₁ : ∀ i, HasLaw (ξ₁ i) (gaussianReal 0 δ₁) P₁)
    (hind₂ : iIndepFun ξ₂ P₂) (hξ₂ : ∀ i, HasLaw (ξ₂ i) (gaussianReal 0 δ₂) P₂) (S₀ : ℝ)
    {Φ : (ℕ → ℝ × ℝ) → ℝ}
    (hΦ : AEStronglyMeasurable Φ (P₁.map fun ω => adaptiveEM a b ν₁ δ₁ S₀ (fun i => ξ₁ i ω))) :
    (Integrable (fun ω => Φ (adaptiveEM a b ν₁ δ₁ S₀ (fun i => ξ₁ i ω))) P₁ ↔
        Integrable (fun ω => Φ (adaptiveEM a b ν₂ δ₂ S₀ (fun i => ξ₂ i ω))) P₂) ∧
      ∫ ω, Φ (adaptiveEM a b ν₁ δ₁ S₀ (fun i => ξ₁ i ω)) ∂P₁ =
        ∫ ω, Φ (adaptiveEM a b ν₂ δ₂ S₀ (fun i => ξ₂ i ω)) ∂P₂ := by
  have hZ : iIndepFun (fun i (z : ℕ → ℝ) => z i) stdNormalSeq :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) fun _ => measurable_id
  have hZ1 : ∀ i, HasLaw (fun z : ℕ → ℝ => z i) (gaussianReal 0 1) stdNormalSeq := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have h₁ := adaptiveEM_law_eq_freshEM ha hb hν₁ (H := fun x => ν₁ x * δ₁) (fun x => rfl)
    hind₁ hξ₁ hZ hZ1 S₀
  have h₂ := adaptiveEM_law_eq_freshEM ha hb hν₂ (H := fun x => ν₁ x * δ₁) hδ
    hind₂ hξ₂ hZ hZ1 S₀
  have hm₁ : AEMeasurable (fun ω => adaptiveEM a b ν₁ δ₁ S₀ (fun i => ξ₁ i ω)) P₁ :=
    (measurable_adaptiveEM ha hb hν₁ δ₁ S₀).comp_aemeasurable
      (aemeasurable_pi_iff.2 fun i => (hξ₁ i).aemeasurable)
  have hm₂ : AEMeasurable (fun ω => adaptiveEM a b ν₂ δ₂ S₀ (fun i => ξ₂ i ω)) P₂ :=
    (measurable_adaptiveEM ha hb hν₂ δ₂ S₀).comp_aemeasurable
      (aemeasurable_pi_iff.2 fun i => (hξ₂ i).aemeasurable)
  exact integral_comp_eq_of_map_eq_map hm₁ hm₂ (h₁.trans h₂.symm) hΦ

end EulerMaruyama

/-! ### Theorem 1 for the non-nested adaptive Euler–Maruyama estimator -/

section Theorem1

/-- Scaled standard normal coordinates `√δ Z_i` are independent `N(0, δ)` under `stdNormalSeq`
(Giles 2015, §5.6, Algorithm 3: "`∆W := √h Z`"). -/
lemma iIndepFun_sqrt_mul_coord (δ : ℝ≥0) :
    iIndepFun (fun i (z : ℕ → ℝ) => Real.sqrt δ * z i) stdNormalSeq ∧
      ∀ i, HasLaw (fun z : ℕ → ℝ => Real.sqrt δ * z i) (gaussianReal 0 δ) stdNormalSeq := by
  have hZ : iIndepFun (fun i (z : ℕ → ℝ) => z i) stdNormalSeq :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) fun _ => measurable_id
  have hZ1 : ∀ i, HasLaw (fun z : ℕ → ℝ => z i) (gaussianReal 0 1) stdNormalSeq := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  refine ⟨hZ.comp (fun _ x => Real.sqrt δ * x) fun _ => measurable_const.mul measurable_id,
    fun i => ?_⟩
  have h := hasLaw_sqrt_mul δ.coe_nonneg (hZ1 i)
  rwa [Real.toNNReal_coe] at h

/-- The fine payoff on level `ℓ` (Giles 2015, §5.6 and §2.1): the payoff `Φ ℓ` of the
level-`ℓ` adaptive Euler–Maruyama path in the level-`ℓ` sample, computed on the base grid of
spacing `δ ℓ` (fine enough for levels `ℓ` and `ℓ − 1`) with the level-`ℓ` rule `νf ℓ` in units of
`δ ℓ`, from the base increments `√(δ ℓ) z_i`, `z ~ stdNormalSeq`. -/
noncomputable def adaptiveEMFine (a b : ℝ → ℝ → ℝ) (νf : ℕ → ℝ × ℝ → ℕ) (δ : ℕ → ℝ≥0)
    (S₀ : ℝ) (Φ : ℕ → (ℕ → ℝ × ℝ) → ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  Φ ℓ (adaptiveEM a b (νf ℓ) (δ ℓ) S₀ fun i => Real.sqrt (δ ℓ) * z i)

/-- The coarse payoff on level `ℓ` (Giles 2015, §5.6 and §2.1): the payoff `Φ ℓ` of the
level-`ℓ` adaptive Euler–Maruyama path in the level-`(ℓ + 1)` sample, computed on the finer base
grid `δ (ℓ + 1)` with the level-`ℓ` rule `νc ℓ` in units of `δ (ℓ + 1)`, from the same inputs `z`
as the fine path of level `ℓ + 1`. -/
noncomputable def adaptiveEMCoarse (a b : ℝ → ℝ → ℝ) (νc : ℕ → ℝ × ℝ → ℕ) (δ : ℕ → ℝ≥0)
    (S₀ : ℝ) (Φ : ℕ → (ℕ → ℝ × ℝ) → ℝ) (ℓ : ℕ) (z : ℕ → ℝ) : ℝ :=
  Φ ℓ (adaptiveEM a b (νc ℓ) (δ (ℓ + 1)) S₀ fun i => Real.sqrt (δ (ℓ + 1)) * z i)

/-- The adaptive Euler–Maruyama path from scaled inputs is measurable (Giles 2015, §5.6). -/
lemma measurable_adaptiveEM_scaled {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {ν : ℝ × ℝ → ℕ} (hν : Measurable ν) (δ : ℝ≥0)
    (S₀ : ℝ) : Measurable fun z : ℕ → ℝ => adaptiveEM a b ν δ S₀ fun i => Real.sqrt δ * z i :=
  (measurable_adaptiveEM ha hb hν δ S₀).comp
    (measurable_pi_lambda _ fun i => measurable_const.mul (measurable_pi_apply i))

/-- The fine and the coarse payoff of level `ℓ` have the same law (Giles 2015, §5.6 and (2.4)),
when the two rules of level `ℓ` give the same step on the two base grids. -/
lemma map_adaptiveEMFine_eq_coarse {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {νf νc : ℕ → ℝ × ℝ → ℕ} {δ : ℕ → ℝ≥0} {ℓ : ℕ}
    (hνf : Measurable (νf ℓ)) (hνc : Measurable (νc ℓ))
    (hcons : ∀ x, (νf ℓ x : ℝ≥0) * δ ℓ = νc ℓ x * δ (ℓ + 1)) (S₀ : ℝ)
    {Φ : ℕ → (ℕ → ℝ × ℝ) → ℝ} (hΦ : Measurable (Φ ℓ)) :
    stdNormalSeq.map (adaptiveEMFine a b νf δ S₀ Φ ℓ) =
      stdNormalSeq.map (adaptiveEMCoarse a b νc δ S₀ Φ ℓ) := by
  have hZ : iIndepFun (fun i (z : ℕ → ℝ) => z i) stdNormalSeq :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) fun _ => measurable_id
  have hZ1 : ∀ i, HasLaw (fun z : ℕ → ℝ => z i) (gaussianReal 0 1) stdNormalSeq := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  obtain ⟨hi₁, hl₁⟩ := iIndepFun_sqrt_mul_coord (δ ℓ)
  obtain ⟨hi₂, hl₂⟩ := iIndepFun_sqrt_mul_coord (δ (ℓ + 1))
  have h₁ := adaptiveEM_law_eq_freshEM ha hb hνf (H := fun x => νf ℓ x * δ ℓ)
    (fun x => rfl) hi₁ hl₁ hZ hZ1 S₀
  have h₂ := adaptiveEM_law_eq_freshEM ha hb hνc (H := fun x => νf ℓ x * δ ℓ)
    hcons hi₂ hl₂ hZ hZ1 S₀
  have e₁ : adaptiveEMFine a b νf δ S₀ Φ ℓ =
      Φ ℓ ∘ fun z => adaptiveEM a b (νf ℓ) (δ ℓ) S₀ fun i => Real.sqrt (δ ℓ) * z i := rfl
  have e₂ : adaptiveEMCoarse a b νc δ S₀ Φ ℓ =
      Φ ℓ ∘ fun z => adaptiveEM a b (νc ℓ) (δ (ℓ + 1)) S₀
        fun i => Real.sqrt (δ (ℓ + 1)) * z i := rfl
  rw [e₁, e₂, ← Measure.map_map hΦ (measurable_adaptiveEM_scaled ha hb hνf _ S₀),
    ← Measure.map_map hΦ (measurable_adaptiveEM_scaled ha hb hνc _ S₀), h₁, h₂]

/-- **Theorem 1 for the non-nested adaptive Euler–Maruyama estimator** (Giles 2015, §2.1, (2.4)
and Theorem 1; §5.6, p. 44, lines 1917–1930: "a completely independent adaptation on each level
of refinement … It may appear that this would cause difficulties in the MLMC implementation, but
Figure 5.9 tries to illustrate that it does not").  The level-`ℓ` correction is
`P^f_ℓ − P^c_{ℓ−1}` on one input `z ~ stdNormalSeq`: the level-`ℓ` path (rule `νf ℓ`) and the
level-`(ℓ−1)` path (rule `νc (ℓ−1)`) are both built from the base increments `√(δ ℓ) z_i` of the
level-`ℓ` base grid; the inputs `ω^{(ℓ,n)}` of the samples are independent with law
`stdNormalSeq`.  The two rules of level `ℓ` give the same step on the base grids of the samples
`ℓ` and `ℓ + 1` (`hcons`: `νf ℓ x · δ ℓ = νc ℓ x · δ (ℓ + 1)`), so (2.4) holds (proved, not
assumed), and the coarse payoffs are square integrable when the fine ones are.  Hence under (i),
(iii), (iv) with `α ≥ ½ min(β, γ)` there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are
`L` and `N_ℓ ≥ 1` with `MSE < ε²` and `E[C] ≤ c₄ · bound(ε)`.  The rates (i), (iii), (iv) are
assumed; step sizes are multiples of the base spacings. -/
theorem adaptiveEM_mlmc_theorem1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {νf νc : ℕ → ℝ × ℝ → ℕ}
    (hνf : ∀ ℓ, Measurable (νf ℓ)) (hνc : ∀ ℓ, Measurable (νc ℓ)) {δ : ℕ → ℝ≥0}
    (hcons : ∀ ℓ x, (νf ℓ x : ℝ≥0) * δ ℓ = νc ℓ x * δ (ℓ + 1)) (S₀ : ℝ)
    {Φ : ℕ → (ℕ → ℝ × ℝ) → ℝ} (hΦ : ∀ ℓ, Measurable (Φ ℓ)) (P : (ℕ → ℝ) → ℝ)
    (ω : ℕ × ℕ → Ω → ℕ → ℝ) (cost : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hω : ∀ p, MeasurePreserving (ω p) μ stdNormalSeq) (hind : iIndepFun ω μ)
    (hP : Integrable P stdNormalSeq)
    (hPf : ∀ ℓ, MemLp (adaptiveEMFine a b νf δ S₀ Φ ℓ) 2 stdNormalSeq)
    (hcost : ∀ ℓ n, Integrable (cost ℓ n) μ) (hcostC : ∀ ℓ n, μ[cost ℓ n] = C ℓ)
    (h_i : ∀ ℓ : ℕ, |∫ z, adaptiveEMFine a b νf δ S₀ Φ ℓ z - P z ∂stdNormalSeq| ≤
      c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_iii : ∀ ℓ, variance (fineCoarseDiff (adaptiveEMFine a b νf δ S₀ Φ)
      (adaptiveEMCoarse a b νc δ S₀ Φ) ℓ) stdNormalSeq ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        μ[fun x => (∑ ℓ ∈ range (L + 1),
          blockMean (fineCoarseDiff (adaptiveEMFine a b νf δ S₀ Φ)
            (adaptiveEMCoarse a b νc δ S₀ Φ)) ω ℓ (N ℓ) x -
            ∫ z, P z ∂stdNormalSeq) ^ 2] < ε ^ 2 ∧
        μ[totalCost cost L N] ≤ c₄ * complexityBound α β γ ε := by
  have hPfm : ∀ ℓ, Measurable (adaptiveEMFine a b νf δ S₀ Φ ℓ) := fun ℓ =>
    (hΦ ℓ).comp (measurable_adaptiveEM_scaled ha hb (hνf ℓ) _ S₀)
  have hPcm : ∀ ℓ, Measurable (adaptiveEMCoarse a b νc δ S₀ Φ ℓ) := fun ℓ =>
    (hΦ ℓ).comp (measurable_adaptiveEM_scaled ha hb (hνc ℓ) _ S₀)
  have hid : ∀ ℓ, IdentDistrib (adaptiveEMFine a b νf δ S₀ Φ ℓ)
      (adaptiveEMCoarse a b νc δ S₀ Φ ℓ) stdNormalSeq stdNormalSeq := fun ℓ =>
    ⟨(hPfm ℓ).aemeasurable, (hPcm ℓ).aemeasurable,
      map_adaptiveEMFine_eq_coarse ha hb (hνf ℓ) (hνc ℓ) (hcons ℓ) S₀ (hΦ ℓ)⟩
  exact giles_theorem1_fineCoarse P (adaptiveEMFine a b νf δ S₀ Φ)
    (adaptiveEMCoarse a b νc δ S₀ Φ) ω cost C hα hβ hγ hc₁ hc₂ hc₃ hαβγ hω hind hP hPfm hPcm
    hPf (fun ℓ => (hid ℓ).memLp_snd (hPf ℓ)) (fun ℓ => (hid ℓ).integral_eq) hcost hcostC h_i
    h_iii h_iv

end Theorem1

/-! ### (3) Poisson counts over adaptively chosen intervals (Giles 2015, §8) -/

section Poisson

/-- A sum of `n` independent `P(m)` counts is `P(nm)` (Giles 2015, §8, p. 55: "the sum of two
independent Poisson variates `P(t₁)`, `P(t₂)` is equivalent in distribution to `P(t₁ + t₂)`"). -/
lemma blockLaw_poisson (m : ℝ≥0) (n : ℕ) :
    blockLaw (poissonMeasure m) n = poissonMeasure (n * m) := by
  have hind : iIndepFun (fun i (N : ℕ → ℕ) => N i)
      (Measure.infinitePi fun _ => poissonMeasure m) :=
    iIndepFun_infinitePi (X := fun _ (x : ℕ) => x) fun _ => measurable_id
  have hX : ∀ i, HasLaw (fun N : ℕ → ℕ => N i) (poissonMeasure m)
      (Measure.infinitePi fun _ => poissonMeasure m) := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  rw [blockLaw, (hasLaw_finsetSum_poisson hind hX (range n)).map_eq]
  simp

/-- The Poisson kernel `n ↦ P(nm)`: the law of the count of a Poisson process over `n` base
intervals, each with mean count `m` (Giles 2015, §8). -/
noncomputable def poissonStepKernel (m : ℝ≥0) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun n => poissonMeasure (n * m)

/-- The block-sum kernel of `P(m)` base counts is `n ↦ P(nm)` (Giles 2015, §8). -/
lemma blockKernel_poisson (m : ℝ≥0) : blockKernel (poissonMeasure m) = poissonStepKernel m :=
  Kernel.ext fun n => blockLaw_poisson m n

variable {X : Type*} [MeasurableSpace X] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {m : ℝ≥0} {N : ℕ → Ω → ℕ}

/-- **The counts over adaptively chosen intervals are conditionally Poisson** (Giles 2015, §8,
p. 56, lines 2442–2447: "The non-nested adaptive timestepping approach described in Section 5.6
for SDEs is equally applicable in this setting … the construction is exactly the same as
illustrated in Figure 5.9, but with Poisson variates for each time interval instead of Brownian
increments").  The base counts `N_i` of a Poisson process of rate `λ` over the base intervals of
length `δ` are independent `P(m)`, `m = λδ`; step `k` takes `ν_k(y_k)` base intervals chosen from
the path `y_k` so far, and its count is the sum of the base counts over them.  Then the pair
(path so far, count of step `k`) has the law `L_k ⊗ₘ κ_k` with `κ_k(y) = P(ν_k(y) m)`: given the
path so far, the count over the chosen step `h_k = n_k δ` is Poisson with mean `λ h_k`.  The rate
`λ` is constant; step sizes are multiples of `δ`.  "The path so far" is the path `y_k` of the
scheme (the σ-algebra `σ(y_k)`), through which alone the rule sees the base counts; given the
whole history `(N_i)_{i<τ_k}` of the base counts the count is still `P(λ h_k)`, also for rules
that depend on that history (`histCount_condLaw`). -/
theorem adaptiveCount_condLaw (hind : iIndepFun N P)
    (hN : ∀ i, HasLaw (N i) (poissonMeasure m) P) {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → ℕ → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × ℕ => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    P.map (fun ω => ((adaptivePath ν G x₀ (fun i => N i ω) k).1,
        adaptiveIncr ν G x₀ (fun i => N i ω) k)) =
      (P.map fun ω => (adaptivePath ν G x₀ (fun i => N i ω) k).1) ⊗ₘ
        (poissonStepKernel m).comap (ν k) (hν k) := by
  have h1 : Measurable fun N : ℕ → ℕ => (adaptivePath ν G x₀ N k).1 :=
    (measurable_adaptivePath hν hG x₀ k).fst
  have h2 : Measurable fun N : ℕ → ℕ =>
      ((adaptivePath ν G x₀ N k).1, adaptiveIncr ν G x₀ N k) :=
    h1.prodMk (measurable_adaptiveIncr hν hG x₀ k)
  rw [map_comp_of_iid hind hN h2, map_comp_of_iid hind hN h1,
    map_adaptiveIncr _ hν hG x₀ k, blockKernel_poisson]

/-- **The path built from counts over adaptive intervals has the law of the scheme driven by
fresh Poisson variates** (Giles 2015, §8, p. 56, lines 2442–2447, and §5.6: "the construction is
exactly the same as illustrated in Figure 5.9, but with Poisson variates for each time interval
instead of Brownian increments").  The base counts `N_i` are independent `P(m)`.  For the fresh
scheme, each step `k` has its own independent family `ζ_k = (ζ_k(n))_n` of independent Poisson
variates `ζ_k(n) ~ P(nm)`, and step `k` uses `ζ_k(ν_k(y_k))`: a fresh Poisson variate with the
mean of the chosen step.  The whole paths of the two schemes have the same law. -/
theorem adaptiveCount_law_eq_fresh (hind : iIndepFun N P)
    (hN : ∀ i, HasLaw (N i) (poissonMeasure m) P) {ζ : ℕ → Ω' → ℕ → ℕ}
    (hζind : iIndepFun ζ P')
    (hζ : ∀ k, HasLaw (ζ k) (Measure.infinitePi fun n : ℕ => poissonMeasure (n * m)) P')
    {ν : ℕ → (ℕ → X) → ℕ} {G : ℕ → (ℕ → X) → ℕ → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × ℕ => G k p.1 p.2) (x₀ : X) :
    P.map (fun ω => adaptiveSeq ν G x₀ (fun i => N i ω)) =
      P'.map (fun ω => freshSeq (fun k y z => G k y (z (ν k y))) x₀ (fun i => ζ i ω)) := by
  have hev : Measurable fun p : ℕ × (ℕ → ℕ) => p.2 p.1 :=
    measurable_from_prod_countable_right fun n => measurable_pi_apply n
  have hs : ∀ k, Measurable fun p : (ℕ → X) × (ℕ → ℕ) => p.2 (ν k p.1) := fun k =>
    hev.comp (((hν k).comp measurable_fst).prodMk measurable_snd)
  have hG' : ∀ k, Measurable fun p : (ℕ → X) × (ℕ → ℕ) => G k p.1 (p.2 (ν k p.1)) :=
    fun k => (hG k).comp (measurable_fst.prodMk (hs k))
  rw [map_comp_of_iid hind hN (measurable_adaptiveSeq hν hG x₀),
    map_comp_of_iid hζind hζ (measurable_freshSeq hG' x₀)]
  refine map_adaptiveSeq_eq_freshSeq (poissonMeasure m)
    (Measure.infinitePi fun n : ℕ => poissonMeasure (n * m)) hν hG hs (fun k y => ?_) x₀
  rw [Measure.infinitePi_map_eval, blockLaw_poisson]

end Poisson

/-! ### Conditioning on the whole history of the base increments

The results above condition on the path `y_k` of the scheme.  Here the past at step `k` is
`(y_k, τ_k, H_k)` with the history `H_k = (ξ_i)_{i<τ_k}` of all the base increments used so far
(padded with zeros, `usedSeq`), the rules and the updates may depend on it (`histPath`), and the
base increments after `τ_k` are independent of it (`map_histPath_prod`, the strong Markov property
of an i.i.d. sequence at the predictable times `τ_k`). -/

section History

variable {X E : Type*}

/-- The base increments used before base interval `τ`, padded with zeros (Giles 2015, §5.6, p. 44,
lines 1928–1929: the Brownian increments "simulated for each time interval" so far):
`usedSeq τ ξ i = ξ_i` for `i < τ` and `= 0` for `i ≥ τ`.  With `τ`, it is the history
`(ξ_i)_{i<τ}`. -/
def usedSeq [Zero E] (τ : ℕ) (ξ : ℕ → E) : ℕ → E := fun i => if i < τ then ξ i else 0

/-- The history `H` of the first `τ` base increments, continued by the first `n` entries of `ω`
(Giles 2015, §5.6): `usedSeq (τ + n) ξ = appendBlock τ (usedSeq τ ξ) n (σ^τ ξ)`
(`usedSeq_add`). -/
def appendBlock [Zero E] (τ : ℕ) (H : ℕ → E) (n : ℕ) (ω : ℕ → E) : ℕ → E :=
  fun i => if i < τ then H i else usedSeq n ω (i - τ)

/-- Before the first step no base increment has been used (Giles 2015, §5.6). -/
lemma usedSeq_zero [Zero E] (ξ : ℕ → E) : usedSeq 0 ξ = 0 := by
  funext i
  exact if_neg (Nat.not_lt_zero i)

/-- The history after a step of `n` base intervals (Giles 2015, §5.6). -/
lemma usedSeq_add [Zero E] (τ n : ℕ) (ξ : ℕ → E) :
    usedSeq (τ + n) ξ = appendBlock τ (usedSeq τ ξ) n (shiftSeq τ ξ) := by
  funext i
  show (if i < τ + n then ξ i else 0) =
    if i < τ then (if i < τ then ξ i else 0) else if i - τ < n then ξ (τ + (i - τ)) else 0
  by_cases h : i < τ
  · rw [if_pos (by omega), if_pos h, if_pos h]
  · rw [if_neg h]
    by_cases h' : i < τ + n
    · rw [if_pos h', if_pos (by omega), Nat.add_sub_of_le (by omega)]
    · rw [if_neg h', if_neg (by omega)]

/-- Padding the padded block again changes nothing (Giles 2015, §5.6). -/
lemma usedSeq_usedSeq [Zero E] (n : ℕ) (ω : ℕ → E) : usedSeq n (usedSeq n ω) = usedSeq n ω := by
  funext i
  show (if i < n then (if i < n then ω i else 0) else 0) = if i < n then ω i else 0
  by_cases h : i < n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- **The adaptive path with rules that see the whole history** (Giles 2015, §5.6, p. 44,
lines 1917–1929: "an adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)`"; "The independent
Brownian increments can be simulated for each time interval, and summed to give `W(t)` at the
required times").  As `adaptivePath`, but the value at step `k` is the whole past
`p_k = (y_k, τ_k, H_k)`: the path stopped at step `k`, the number `τ_k` of base intervals used so
far, and the history `H_k = usedSeq τ_k ξ` of the base increments used so far.  Step `k` takes
`n_k = ν k p_k` base intervals; its increment is `ΔW_k = ∑_{τ_k ≤ i < τ_k + n_k} ξ_i`
(`histIncr`), and `x_{k+1} = G k p_k ΔW_k`.  Step sizes are multiples of the base spacing. -/
def histPath [AddCommMonoid E] (ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ)
    (G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X) (x₀ : X) (ξ : ℕ → E) :
    ℕ → (ℕ → X) × ℕ × (ℕ → E)
  | 0 => (fun _ => x₀, 0, 0)
  | k + 1 =>
    let p := histPath ν G x₀ ξ k
    (extendPath k p.1 (G k p (∑ i ∈ Ico p.2.1 (p.2.1 + ν k p), ξ i)), p.2.1 + ν k p,
      usedSeq (p.2.1 + ν k p) ξ)

/-- The increment of step `k` of `histPath` (Giles 2015, §5.6, p. 44, lines 1928–1929): the sum
`ΔW_k = ∑_{τ_k ≤ i < τ_k + n_k} ξ_i` of the base increments over the `n_k` base intervals of the
step. -/
def histIncr [AddCommMonoid E] (ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ)
    (G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X) (x₀ : X) (ξ : ℕ → E) (k : ℕ) : E :=
  ∑ i ∈ Ico (histPath ν G x₀ ξ k).2.1
    ((histPath ν G x₀ ξ k).2.1 + ν k (histPath ν G x₀ ξ k)), ξ i

/-- One step of `histPath`, in terms of `histIncr` (Giles 2015, §5.6). -/
lemma histPath_succ [AddCommMonoid E] (ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ)
    (G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X) (x₀ : X) (ξ : ℕ → E) (k : ℕ) :
    histPath ν G x₀ ξ (k + 1) =
      (extendPath k (histPath ν G x₀ ξ k).1 (G k (histPath ν G x₀ ξ k) (histIncr ν G x₀ ξ k)),
        (histPath ν G x₀ ξ k).2.1 + ν k (histPath ν G x₀ ξ k),
        usedSeq ((histPath ν G x₀ ξ k).2.1 + ν k (histPath ν G x₀ ξ k)) ξ) := rfl

/-- The third component of `histPath` is the history of the base increments used so far (Giles
2015, §5.6): `H_k = usedSeq τ_k ξ`. -/
lemma histPath_hist [AddCommMonoid E] (ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ)
    (G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X) (x₀ : X) (ξ : ℕ → E) :
    ∀ k, (histPath ν G x₀ ξ k).2.2 = usedSeq (histPath ν G x₀ ξ k).2.1 ξ
  | 0 => (usedSeq_zero ξ).symm
  | _ + 1 => rfl

/-- The increment of step `k` of `histPath` is the sum of the first `n_k` base increments not used
yet (Giles 2015, §5.6): `ΔW_k = ∑_{i<n_k} (σ^{τ_k} ξ)_i`. -/
lemma histIncr_eq [AddCommMonoid E] (ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ)
    (G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X) (x₀ : X) (ξ : ℕ → E) (k : ℕ) :
    histIncr ν G x₀ ξ k = ∑ i ∈ range (ν k (histPath ν G x₀ ξ k)),
      shiftSeq (histPath ν G x₀ ξ k).2.1 ξ i := by
  rw [histIncr, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  rfl

/-- `adaptivePath` is `histPath` with rules and updates that ignore the history (Giles 2015,
§5.6): its past `(y_k, τ_k, usedSeq τ_k ξ)` is the value of `histPath`. -/
lemma histPath_eq_adaptivePath [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ)
    (G : ℕ → (ℕ → X) → E → X) (x₀ : X) (ξ : ℕ → E) :
    ∀ k, histPath (fun k p => ν k p.1) (fun k p e => G k p.1 e) x₀ ξ k =
      ((adaptivePath ν G x₀ ξ k).1, (adaptivePath ν G x₀ ξ k).2,
        usedSeq (adaptivePath ν G x₀ ξ k).2 ξ)
  | 0 => by
    show ((fun _ => x₀, 0, 0) : (ℕ → X) × ℕ × (ℕ → E)) = (fun _ => x₀, 0, usedSeq 0 ξ)
    rw [usedSeq_zero]
  | k + 1 => by
    rw [histPath_succ, histIncr, histPath_eq_adaptivePath ν G x₀ ξ k]
    rfl

/-- The increment of `adaptivePath` is that of `histPath` with rules and updates that ignore the
history (Giles 2015, §5.6). -/
lemma histIncr_eq_adaptiveIncr [AddCommMonoid E] (ν : ℕ → (ℕ → X) → ℕ)
    (G : ℕ → (ℕ → X) → E → X) (x₀ : X) (ξ : ℕ → E) (k : ℕ) :
    histIncr (fun k p => ν k p.1) (fun k p e => G k p.1 e) x₀ ξ k = adaptiveIncr ν G x₀ ξ k := by
  rw [histIncr, histPath_eq_adaptivePath]
  rfl

/-- One step of `histPath` acting on (past, unused base increments) (Giles 2015, §5.6): the step
uses the first `ν k p` unused base increments, appends them to the history and leaves the
others. -/
def histStep [AddCommMonoid E] (ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ)
    (G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X) (k : ℕ)
    (p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E)) : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) :=
  ((extendPath k p.1.1 (G k p.1 (∑ i ∈ range (ν k p.1), p.2 i)), p.1.2.1 + ν k p.1,
    appendBlock p.1.2.1 p.1.2.2 (ν k p.1) p.2), shiftSeq (ν k p.1) p.2)

/-- `histPath` with its unused base increments evolves by `histStep` (Giles 2015, §5.6). -/
lemma histPath_step [AddCommMonoid E] (ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ)
    (G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X) (x₀ : X) (ξ : ℕ → E) (k : ℕ) :
    (histPath ν G x₀ ξ (k + 1), shiftSeq (histPath ν G x₀ ξ (k + 1)).2.1 ξ) =
      histStep ν G k (histPath ν G x₀ ξ k, shiftSeq (histPath ν G x₀ ξ k).2.1 ξ) := by
  have h1 : (histPath ν G x₀ ξ (k + 1)).2.1 =
      (histPath ν G x₀ ξ k).2.1 + ν k (histPath ν G x₀ ξ k) := rfl
  rw [h1, histPath_succ, histIncr_eq, shiftSeq_add, usedSeq_add, ← histPath_hist]
  rfl

variable [MeasurableSpace X] [MeasurableSpace E]

omit [MeasurableSpace X] in
/-- The padded block `ω ↦ usedSeq n ω` is measurable (Giles 2015, §5.6). -/
lemma measurable_usedSeq [Zero E] (n : ℕ) : Measurable (usedSeq (E := E) n) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i < n
  · simp only [usedSeq, h, ↓reduceIte]
    exact measurable_pi_apply i
  · simp only [usedSeq, h, ↓reduceIte]
    exact measurable_const

omit [MeasurableSpace X] in
/-- `appendBlock` is jointly measurable in the two lengths, the history and the remaining base
increments (Giles 2015, §5.6). -/
lemma measurable_appendBlock [Zero E] :
    Measurable fun q : (ℕ × ℕ) × (ℕ → E) × (ℕ → E) => appendBlock q.1.1 q.2.1 q.1.2 q.2.2 := by
  refine measurable_from_prod_countable_right fun p => measurable_pi_lambda _ fun i => ?_
  by_cases h : i < p.1
  · simp only [appendBlock, h, ↓reduceIte]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [appendBlock, h, ↓reduceIte]
    exact (measurable_pi_apply (i - p.1)).comp ((measurable_usedSeq p.2).comp measurable_snd)

omit [MeasurableSpace X] in
/-- The padded block of the first `n` base increments is independent of the base increments after
it, which are again i.i.d. (Giles 2015, §5.6, p. 44, lines 1928–1929): under `μ^{⊗ℕ}`, the pair
`(g(usedSeq n ξ), σⁿ ξ)` has the law `Law(g(usedSeq n ξ)) ⊗ μ^{⊗ℕ}`. -/
lemma map_usedSeq_shiftSeq [Zero E] (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) {Y : Type*}
    [MeasurableSpace Y] {g : (ℕ → E) → Y} (hg : Measurable g) :
    (Measure.infinitePi fun _ => μ).map (fun ω => (g (usedSeq n ω), shiftSeq n ω)) =
      ((Measure.infinitePi fun _ => μ).map fun ω => g (usedSeq n ω)).prod
        (Measure.infinitePi fun _ => μ) := by
  have hpad : Measurable fun v : Fin n → E => fun i : ℕ => if h : i < n then v ⟨i, h⟩ else 0 := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i < n
    · simp only [h, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [h, ↓reduceDIte]
      exact measurable_const
  have hind : IndepFun (fun ω : ℕ → E => g (usedSeq n ω)) (shiftSeq n)
      (Measure.infinitePi fun _ => μ) :=
    (indepFun_restrict_shiftSeq μ n).comp (hg.comp hpad) measurable_id
  have hm : Measurable fun ω : ℕ → E => g (usedSeq n ω) := hg.comp (measurable_usedSeq n)
  rw [(indepFun_iff_map_prod_eq_prod_map_map hm.aemeasurable
      (measurable_shiftSeq n).aemeasurable).1 hind, (measurePreserving_shiftSeq μ n).map_eq]

variable [AddCommMonoid E] [MeasurableAdd₂ E]

/-- One step of `histPath` is measurable for a measurable rule and update (Giles 2015, §5.6). -/
lemma measurable_histStep {ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ}
    {G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X} {k : ℕ} (hν : Measurable (ν k))
    (hG : Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × E => G k p.1 p.2) :
    Measurable (histStep ν G k) := by
  have hn : Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) => ν k p.1 :=
    hν.comp measurable_fst
  have h0 : Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) => (ν k p.1, p.2) :=
    hn.prodMk measurable_snd
  have h1 : Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) =>
      ∑ i ∈ range (ν k p.1), p.2 i :=
    measurable_blockSum_uncurry.comp h0
  have hτ : Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) => p.1.2.1 :=
    measurable_fst.snd.fst
  have h3 : Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) =>
      appendBlock p.1.2.1 p.1.2.2 (ν k p.1) p.2 :=
    measurable_appendBlock.comp ((hτ.prodMk hn).prodMk (measurable_fst.snd.snd.prodMk
      measurable_snd))
  exact (((measurable_extendPath k).comp (measurable_fst.fst.prodMk
    (hG.comp (measurable_fst.prodMk h1)))).prodMk ((hτ.add hn).prodMk h3)).prodMk
    (measurable_shiftSeq_uncurry.comp h0)

/-- For a fixed past, one step of `histPath` leaves the unused base increments fresh and
independent of the new past (Giles 2015, §5.6). -/
lemma map_histStep (μ : Measure E) [IsProbabilityMeasure μ]
    {ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ} {G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X} {k : ℕ}
    (hG : Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × E => G k p.1 p.2)
    (s : (ℕ → X) × ℕ × (ℕ → E)) :
    (Measure.infinitePi fun _ => μ).map (fun ω => histStep ν G k (s, ω)) =
      ((Measure.infinitePi fun _ => μ).map fun ω => (histStep ν G k (s, ω)).1).prod
        (Measure.infinitePi fun _ => μ) := by
  have hg : Measurable fun b : ℕ → E =>
      ((extendPath k s.1 (G k s (∑ i ∈ range (ν k s), b i)), s.2.1 + ν k s,
        appendBlock s.2.1 s.2.2 (ν k s) b) : (ℕ → X) × ℕ × (ℕ → E)) :=
    ((measurable_extendPath k).comp (measurable_const.prodMk (hG.comp
      (measurable_const.prodMk (measurable_blockSum (ν k s)))))).prodMk
      (measurable_const.prodMk (measurable_appendBlock.comp
        (f := fun b => ((s.2.1, ν k s), (s.2.2, b)))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))))
  have e : ∀ ω : ℕ → E, histStep ν G k (s, ω) =
      ((extendPath k s.1 (G k s (∑ i ∈ range (ν k s), usedSeq (ν k s) ω i)), s.2.1 + ν k s,
        appendBlock s.2.1 s.2.2 (ν k s) (usedSeq (ν k s) ω)), shiftSeq (ν k s) ω) := fun ω => by
    have h1 : ∑ i ∈ range (ν k s), ω i = ∑ i ∈ range (ν k s), usedSeq (ν k s) ω i :=
      Finset.sum_congr rfl fun i hi => (if_pos (Finset.mem_range.1 hi)).symm
    have h2 : appendBlock s.2.1 s.2.2 (ν k s) ω =
        appendBlock s.2.1 s.2.2 (ν k s) (usedSeq (ν k s) ω) := by
      unfold appendBlock
      rw [usedSeq_usedSeq]
    rw [← h1, ← h2]
    rfl
  simp_rw [e]
  exact map_usedSeq_shiftSeq μ (ν k s) hg

/-- **The base increments after the adaptive times are independent of the whole past** (Giles
2015, §5.6, p. 44, lines 1926–1929: "The underlying Brownian path needs to be sampled at a set of
times which are the union of the simulation times used by the coarse and fine path. The
independent Brownian increments can be simulated for each time interval, and summed to give
`W(t)` at the required times").  Let the base increments be i.i.d. with law `μ`, and let the
rules `ν k` and the updates `G k` of `histPath` be measurable functions of the whole past
`p_k = (y_k, τ_k, H_k)` (path so far, base intervals used so far, history `H_k = (ξ_i)_{i<τ_k}`
padded with zeros).  Then the unused base increments `σ^{τ_k} ξ = (ξ_{τ_k + i})_i` are independent
of `p_k` and again i.i.d. with law `μ`: `Law(p_k, σ^{τ_k} ξ) = Law(p_k) ⊗ μ^{⊗ℕ}`.  This is the
strong Markov property of an i.i.d. sequence at the predictable times `τ_k` (the stopping time
`τ_k` and the history `H_k` generate the σ-algebra of the base increments before `τ_k`).  For rules
that ignore the history, `histPath` is `adaptivePath` (`histPath_eq_adaptivePath`). -/
theorem map_histPath_prod (μ : Measure E) [IsProbabilityMeasure μ]
    {ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ} {G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X}
    (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × E => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    (Measure.infinitePi fun _ => μ).map
        (fun ξ => (histPath ν G x₀ ξ k, shiftSeq (histPath ν G x₀ ξ k).2.1 ξ)) =
      ((Measure.infinitePi fun _ => μ).map fun ξ => histPath ν G x₀ ξ k).prod
        (Measure.infinitePi fun _ => μ) := by
  have h := map_noiseChain (Measure.infinitePi fun _ => μ) (histStep ν G)
    (fun j => measurable_histStep (hν j) (hG j)) (fun j s => map_histStep μ (hG j) s)
    ((fun _ => x₀, 0, 0) : (ℕ → X) × ℕ × (ℕ → E))
    (fun k ξ => (histPath ν G x₀ ξ k, shiftSeq (histPath ν G x₀ ξ k).2.1 ξ))
    (fun ξ => by
      show ((fun _ => x₀, 0, 0), shiftSeq 0 ξ) = ((fun _ => x₀, 0, 0), ξ)
      rw [shiftSeq_zero]) (fun j ξ => histPath_step ν G x₀ ξ j) k
  have e : (fun ξ => histPath ν G x₀ ξ k) =
      Prod.fst ∘ fun ξ => (histPath ν G x₀ ξ k, shiftSeq (histPath ν G x₀ ξ k).2.1 ξ) := rfl
  rw [h.2, e, ← Measure.map_map measurable_fst h.1, h.2, Measure.map_fst_prod, measure_univ,
    one_smul]

/-- `histPath` with its unused base increments is a measurable function of the base increments
(Giles 2015, §5.6). -/
lemma measurable_histPath {ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ}
    {G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × E => G k p.1 p.2) (x₀ : X) :
    ∀ k, Measurable fun ξ : ℕ → E =>
      (histPath ν G x₀ ξ k, shiftSeq (histPath ν G x₀ ξ k).2.1 ξ)
  | 0 => by
    have e : (fun ξ : ℕ → E => (histPath ν G x₀ ξ 0, shiftSeq (histPath ν G x₀ ξ 0).2.1 ξ)) =
        fun ξ => (((fun _ => x₀, 0, 0) : (ℕ → X) × ℕ × (ℕ → E)), ξ) := by
      funext ξ
      show ((fun _ => x₀, 0, 0), shiftSeq 0 ξ) = ((fun _ => x₀, 0, 0), ξ)
      rw [shiftSeq_zero]
    rw [e]
    exact measurable_const.prodMk measurable_id
  | k + 1 => by
    have e : (fun ξ : ℕ → E =>
        (histPath ν G x₀ ξ (k + 1), shiftSeq (histPath ν G x₀ ξ (k + 1)).2.1 ξ)) =
        histStep ν G k ∘ fun ξ => (histPath ν G x₀ ξ k, shiftSeq (histPath ν G x₀ ξ k).2.1 ξ) :=
      funext fun ξ => histPath_step ν G x₀ ξ k
    rw [e]
    exact (measurable_histStep (hν k) (hG k)).comp (measurable_histPath hν hG x₀ k)

/-- The increment of step `k` of `histPath` is a measurable function of the base increments (Giles
2015, §5.6). -/
lemma measurable_histIncr {ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ}
    {G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × E => G k p.1 p.2) (x₀ : X)
    (k : ℕ) : Measurable fun ξ => histIncr ν G x₀ ξ k := by
  have hf : Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) =>
      ∑ i ∈ range (ν k p.1), p.2 i :=
    measurable_blockSum_uncurry.comp (((hν k).comp measurable_fst).prodMk measurable_snd)
  have e : (fun ξ => histIncr ν G x₀ ξ k) =
      (fun p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) => ∑ i ∈ range (ν k p.1), p.2 i) ∘
        fun ξ => (histPath ν G x₀ ξ k, shiftSeq (histPath ν G x₀ ξ k).2.1 ξ) :=
    funext fun ξ => histIncr_eq ν G x₀ ξ k
  rw [e]
  exact hf.comp (measurable_histPath hν hG x₀ k)

/-- Given the whole past, the increment of a step of `histPath` is distributed as a sum of
`ν_k(p_k)` fresh base increments (Giles 2015, §5.6, p. 44, lines 1926–1929): the pair (past,
increment) has the law `Law(p_k) ⊗ₘ κ` with `κ p = blockLaw μ (ν k p)`. -/
lemma map_histIncr (μ : Measure E) [IsProbabilityMeasure μ]
    {ν : ℕ → (ℕ → X) × ℕ × (ℕ → E) → ℕ} {G : ℕ → (ℕ → X) × ℕ × (ℕ → E) → E → X}
    (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × E => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    (Measure.infinitePi fun _ => μ).map (fun ξ => (histPath ν G x₀ ξ k, histIncr ν G x₀ ξ k)) =
      ((Measure.infinitePi fun _ => μ).map fun ξ => histPath ν G x₀ ξ k) ⊗ₘ
        (blockKernel μ).comap (ν k) (hν k) := by
  have := isMarkovKernel_blockKernel μ
  have hf : Measurable fun p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) =>
      ∑ i ∈ range (ν k p.1), p.2 i :=
    measurable_blockSum_uncurry.comp (((hν k).comp measurable_fst).prodMk measurable_snd)
  have e : (fun ξ => (histPath ν G x₀ ξ k, histIncr ν G x₀ ξ k)) =
      (fun p : ((ℕ → X) × ℕ × (ℕ → E)) × (ℕ → E) => (p.1, ∑ i ∈ range (ν k p.1), p.2 i)) ∘
        fun ξ => (histPath ν G x₀ ξ k, shiftSeq (histPath ν G x₀ ξ k).2.1 ξ) := by
    funext ξ
    rw [histIncr_eq]
    rfl
  rw [e, ← Measure.map_map (measurable_fst.prodMk hf) (measurable_histPath hν hG x₀ k),
    map_histPath_prod μ hν hG x₀ k,
    map_pair_prod_eq_compProd _ _ ((blockKernel μ).comap (ν k) (hν k)) hf
      (fun y => by rw [Kernel.comap_apply]; rfl)]

end History

section HistoryLaws

variable {X : Type*} [MeasurableSpace X] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Given the whole history, the Brownian increment over an adaptively chosen step is
`N(0, n_k δ)`** (Giles 2015, §5.6, p. 44, lines 1917–1929: "an adaptive timestep of the form
`h_ℓ = 2^{−ℓ} H(Ŝ_n)`"; "The independent Brownian increments can be simulated for each time
interval, and summed to give `W(t)` at the required times").  The base increments `ξ_0, ξ_1, …`
are independent `N(0, δ)`, and the rule `ν_k` and the update `G_k` of `histPath` are measurable
functions of the whole past `p_k = (y_k, τ_k, H_k)`: the path so far, the number of base intervals
used so far and the history `H_k = (ξ_i)_{i<τ_k}` of all the base increments used so far.  Then
the pair (past, increment `ΔW_k` over the chosen step) has the law `Law(p_k) ⊗ₘ κ_k` with
`κ_k(p) = N(0, ν_k(p) δ)`: given the whole past, `ΔW_k ~ N(0, h_k)` with `h_k = n_k δ`.  Step
sizes are multiples of the base spacing `δ`. -/
theorem histIncr_condLaw_gaussian {δ : ℝ≥0} {ξ : ℕ → Ω → ℝ} (hind : iIndepFun ξ P)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P) {ν : ℕ → (ℕ → X) × ℕ × (ℕ → ℝ) → ℕ}
    {G : ℕ → (ℕ → X) × ℕ × (ℕ → ℝ) → ℝ → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : ((ℕ → X) × ℕ × (ℕ → ℝ)) × ℝ => G k p.1 p.2) (x₀ : X)
    (k : ℕ) :
    P.map (fun ω => (histPath ν G x₀ (fun i => ξ i ω) k, histIncr ν G x₀ (fun i => ξ i ω) k)) =
      (P.map fun ω => histPath ν G x₀ (fun i => ξ i ω) k) ⊗ₘ
        (gaussianStepKernel δ).comap (ν k) (hν k) := by
  have h1 : Measurable fun ξ : ℕ → ℝ => histPath ν G x₀ ξ k :=
    (measurable_histPath hν hG x₀ k).fst
  have h2 : Measurable fun ξ : ℕ → ℝ => (histPath ν G x₀ ξ k, histIncr ν G x₀ ξ k) :=
    h1.prodMk (measurable_histIncr hν hG x₀ k)
  rw [map_comp_of_iid hind hξ h2, map_comp_of_iid hind hξ h1, map_histIncr _ hν hG x₀ k,
    blockKernel_gaussianReal]

/-- **Given the whole history, the increment of the adaptive scheme over its chosen step is
`N(0, n_k δ)`** (Giles 2015, §5.6, p. 44, lines 1917–1929: "an adaptive timestep of the form
`h_ℓ = 2^{−ℓ} H(Ŝ_n)`"; "The independent Brownian increments can be simulated for each time
interval, and summed to give `W(t)` at the required times").  In the setting of
`adaptiveIncr_condLaw_gaussian` (independent `N(0, δ)` base increments, measurable rules
`ν_k(y_k)` of the path so far and measurable updates), the increment `ΔW_k` over the chosen step
is `N(0, ν_k(y_k) δ)` given the whole past `(y_k, τ_k, H_k)`, where `H_k = (ξ_i)_{i<τ_k}` is the
history of all the base increments used so far, not only given the path `y_k`: the pair has the
law `Law(y_k, τ_k, H_k) ⊗ₘ κ_k` with the kernel `κ_k(y, τ, H) = N(0, ν_k(y) δ)`. -/
theorem adaptiveIncr_condLaw_hist_gaussian {δ : ℝ≥0} {ξ : ℕ → Ω → ℝ} (hind : iIndepFun ξ P)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P) {ν : ℕ → (ℕ → X) → ℕ}
    {G : ℕ → (ℕ → X) → ℝ → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : (ℕ → X) × ℝ => G k p.1 p.2) (x₀ : X) (k : ℕ) :
    P.map (fun ω => (((adaptivePath ν G x₀ (fun i => ξ i ω) k).1,
        (adaptivePath ν G x₀ (fun i => ξ i ω) k).2,
        usedSeq (adaptivePath ν G x₀ (fun i => ξ i ω) k).2 (fun i => ξ i ω)),
        adaptiveIncr ν G x₀ (fun i => ξ i ω) k)) =
      (P.map fun ω => ((adaptivePath ν G x₀ (fun i => ξ i ω) k).1,
        (adaptivePath ν G x₀ (fun i => ξ i ω) k).2,
        usedSeq (adaptivePath ν G x₀ (fun i => ξ i ω) k).2 (fun i => ξ i ω))) ⊗ₘ
        ((gaussianStepKernel δ).comap (ν k) (hν k)).prodMkRight (ℕ × (ℕ → ℝ)) := by
  have hν' : ∀ k, Measurable fun p : (ℕ → X) × ℕ × (ℕ → ℝ) => ν k p.1 :=
    fun k => (hν k).comp measurable_fst
  have hG' : ∀ k, Measurable fun p : ((ℕ → X) × ℕ × (ℕ → ℝ)) × ℝ => G k p.1.1 p.2 :=
    fun k => (hG k).comp (measurable_fst.fst.prodMk measurable_snd)
  have h := histIncr_condLaw_gaussian (ν := fun k p => ν k p.1) (G := fun k p e => G k p.1 e)
    hind hξ hν' hG' x₀ k
  have e1 : (fun ω => histPath (fun k p => ν k p.1) (fun k p e => G k p.1 e) x₀
      (fun i => ξ i ω) k) = fun ω => ((adaptivePath ν G x₀ (fun i => ξ i ω) k).1,
        (adaptivePath ν G x₀ (fun i => ξ i ω) k).2,
        usedSeq (adaptivePath ν G x₀ (fun i => ξ i ω) k).2 (fun i => ξ i ω)) :=
    funext fun ω => histPath_eq_adaptivePath ν G x₀ _ k
  have e2 : (fun ω => (histPath (fun k p => ν k p.1) (fun k p e => G k p.1 e) x₀
      (fun i => ξ i ω) k, histIncr (fun k p => ν k p.1) (fun k p e => G k p.1 e) x₀
      (fun i => ξ i ω) k)) = fun ω => (((adaptivePath ν G x₀ (fun i => ξ i ω) k).1,
        (adaptivePath ν G x₀ (fun i => ξ i ω) k).2,
        usedSeq (adaptivePath ν G x₀ (fun i => ξ i ω) k).2 (fun i => ξ i ω)),
        adaptiveIncr ν G x₀ (fun i => ξ i ω) k) :=
    funext fun ω => by rw [histPath_eq_adaptivePath, histIncr_eq_adaptiveIncr]
  rw [e2, e1] at h
  exact h

/-- **The counts over adaptively chosen intervals are Poisson given the whole history** (Giles
2015, §8, p. 56, lines 2442–2447: "The non-nested adaptive timestepping approach described in
Section 5.6 for SDEs is equally applicable in this setting … the construction is exactly the same
as illustrated in Figure 5.9, but with Poisson variates for each time interval instead of Brownian
increments").  The base counts `N_i` of a Poisson process of rate `λ` over the base intervals of
length `δ` are independent `P(m)`, `m = λδ`, and the rule `ν_k` and the update `G_k` of
`histPath` are measurable functions of the whole past `p_k = (y_k, τ_k, H_k)` (with the history
`H_k = (N_i)_{i<τ_k}` of all the base counts so far).  Then the pair (past, count of step `k`) has
the law `Law(p_k) ⊗ₘ κ_k` with `κ_k(p) = P(ν_k(p) m)`: given the whole past, the count over the
chosen step `h_k = n_k δ` is Poisson with mean `λ h_k`.  The rate `λ` is constant; step sizes are
multiples of `δ`. -/
theorem histCount_condLaw {m : ℝ≥0} {N : ℕ → Ω → ℕ} (hind : iIndepFun N P)
    (hN : ∀ i, HasLaw (N i) (poissonMeasure m) P) {ν : ℕ → (ℕ → X) × ℕ × (ℕ → ℕ) → ℕ}
    {G : ℕ → (ℕ → X) × ℕ × (ℕ → ℕ) → ℕ → X} (hν : ∀ k, Measurable (ν k))
    (hG : ∀ k, Measurable fun p : ((ℕ → X) × ℕ × (ℕ → ℕ)) × ℕ => G k p.1 p.2) (x₀ : X)
    (k : ℕ) :
    P.map (fun ω => (histPath ν G x₀ (fun i => N i ω) k, histIncr ν G x₀ (fun i => N i ω) k)) =
      (P.map fun ω => histPath ν G x₀ (fun i => N i ω) k) ⊗ₘ
        (poissonStepKernel m).comap (ν k) (hν k) := by
  have h1 : Measurable fun N : ℕ → ℕ => histPath ν G x₀ N k :=
    (measurable_histPath hν hG x₀ k).fst
  have h2 : Measurable fun N : ℕ → ℕ => (histPath ν G x₀ N k, histIncr ν G x₀ N k) :=
    h1.prodMk (measurable_histIncr hν hG x₀ k)
  rw [map_comp_of_iid hind hN h2, map_comp_of_iid hind hN h1, map_histIncr _ hν hG x₀ k,
    blockKernel_poisson]

end HistoryLaws

/-! ### Algorithm 3: the loop over the union sub-intervals

Giles 2015, §5.6, Algorithm 3 (p. 45, lines 1938–1966): "`t := min(t^c, t^f)`, `h := t − t_old`,
`∆W := √h Z`, `∆W^c := ∆W^c + ∆W`, `∆W^f := ∆W^f + ∆W`; if `t = t^c` then update coarse path using
`∆W^c`, compute adapted coarse path timestep `h^c`, `t^c := min(t^c + h^c, T)`, `∆W^c := 0`; [the
same for the fine path]".  Times are counted in base intervals of length `δ`; each level keeps the
part `(y, k, A, r)`: its path stopped at its current step `y`, its number of steps `k`, the
Brownian increment `A` accumulated since its last update (`∆W^c` or `∆W^f`) and the number `r` of
base intervals left until its next update (`t^c − t` or `t^f − t`).  The first iteration of the
paper, with `h = 0`, only computes the first steps; `alg3Init` starts after it. -/

section Algorithm3

/-- One level's part `(y, k, A, r)` of the state of Algorithm 3 (Giles 2015, §5.6): the level's
path stopped at its current step, its number of steps, its accumulated Brownian increment and
the number of base intervals left until its next update. -/
abbrev Alg3Part (X : Type*) := (ℕ → X) × ℕ × ℝ × ℕ

/-- The state of Algorithm 3: the coarse part and the fine part (Giles 2015, §5.6). -/
abbrev Alg3State (X : Type*) := Alg3Part X × Alg3Part X

variable {X : Type*}

/-- One level over one union sub-interval (Giles 2015, §5.6, Algorithm 3, p. 45,
lines 1951–1957: "`∆W^c := ∆W^c + ∆W` … if `t = t^c` then update coarse path using `∆W^c`, compute
adapted coarse path timestep `h^c`, `t^c := min(t^c + h^c, T)`, `∆W^c := 0`"; here the truncation
at `T` is part of the rule `ν`, see the module docstring).  The sub-interval has `n` base
intervals and the Brownian increment `e`.  If it reaches the level's next update time (`r ≤ n`),
the level's state `x = y_k` is updated to `F(x, A + e)`, its next step `ν(F(x, A + e))` is
computed and the accumulator is reset; otherwise `e` is accumulated and `r` decreases by `n`. -/
def alg3Level (ν : X → ℕ) (F : X → ℝ → X) (n : ℕ) (e : ℝ) (p : Alg3Part X) : Alg3Part X :=
  if p.2.2.2 ≤ n then
    (extendPath p.2.1 p.1 (F (p.1 p.2.1) (p.2.2.1 + e)), p.2.1 + 1, 0,
      ν (F (p.1 p.2.1) (p.2.2.1 + e)))
  else (p.1, p.2.1, p.2.2.1 + e, p.2.2.2 - n)

/-- The number of base intervals of the next union sub-interval, up to the next update of either
path (Giles 2015, §5.6, Algorithm 3: "`t := min(t^c, t^f)`, `h := t − t_old`"). -/
def alg3Len (s : Alg3State X) : ℕ :=
  min s.1.2.2.2 s.2.2.2.2

/-- One iteration of Algorithm 3 (Giles 2015, §5.6): both levels see the same Brownian
increment `e` of the union sub-interval. -/
def alg3Update (νc νf : X → ℕ) (Fc Ff : X → ℝ → X) (s : Alg3State X) (e : ℝ) : Alg3State X :=
  (alg3Level νc Fc (alg3Len s) e s.1, alg3Level νf Ff (alg3Len s) e s.2)

/-- The state of Algorithm 3 after its first iteration (Giles 2015, §5.6): both paths at their
initial states `xc₀`, `xf₀`, no step made, empty accumulators, the first steps computed. -/
def alg3Init (νc νf : X → ℕ) (xc₀ xf₀ : X) : Alg3State X :=
  ((fun _ => xc₀, 0, 0, νc xc₀), (fun _ => xf₀, 0, 0, νf xf₀))

/-- **Algorithm 3** (Giles 2015, §5.6, p. 45: "`h := t − t_old`, `∆W := √h Z`"): its states after
each iteration, the `j`-th union sub-interval of `n_j` base intervals receiving the fresh Brownian
increment `√(n_j δ) ζ_j`.  The coarse path makes steps of `νc` base intervals with the update
`Fc`, the fine path steps of `νf` base intervals with `Ff`. -/
noncomputable def alg3Fresh (νc νf : X → ℕ) (Fc Ff : X → ℝ → X) (δ : ℝ≥0) (xc₀ xf₀ : X)
    (ζ : ℕ → ℝ) : ℕ → Alg3State X :=
  freshSeq (fun j z w => alg3Update νc νf Fc Ff (z j) (Real.sqrt (alg3Len (z j) * δ) * w))
    (alg3Init νc νf xc₀ xf₀) ζ

/-- Algorithm 3 driven by the base increments (Giles 2015, §5.6, p. 44: "The independent Brownian
increments can be simulated for each time interval, and summed"): the increment of each union
sub-interval is the sum of the base increments over it. -/
def alg3Path (νc νf : X → ℕ) (Fc Ff : X → ℝ → X) (xc₀ xf₀ : X) (ξ : ℕ → ℝ) :
    ℕ → (ℕ → Alg3State X) × ℕ :=
  adaptivePath (fun j z => alg3Len (z j)) (fun j z e => alg3Update νc νf Fc Ff (z j) e)
    (alg3Init νc νf xc₀ xf₀) ξ

/-- The single-level path of one level on the base grid (Giles 2015, §5.6): steps of `ν(x)` base
intervals from the state `x`, updated by `F`. -/
def levelPath (ν : X → ℕ) (F : X → ℝ → X) (x₀ : X) (ξ : ℕ → ℝ) : ℕ → (ℕ → X) × ℕ :=
  adaptivePath (fun k y => ν (y k)) (fun k y e => F (y k) e) x₀ ξ

/-- One step of the single-level path (Giles 2015, §5.6). -/
lemma levelPath_succ (ν : X → ℕ) (F : X → ℝ → X) (x₀ : X) (ξ : ℕ → ℝ) (k : ℕ) :
    levelPath ν F x₀ ξ (k + 1) =
      (extendPath k (levelPath ν F x₀ ξ k).1 (F ((levelPath ν F x₀ ξ k).1 k)
        (∑ i ∈ Ico (levelPath ν F x₀ ξ k).2
          ((levelPath ν F x₀ ξ k).2 + ν ((levelPath ν F x₀ ξ k).1 k)), ξ i)),
        (levelPath ν F x₀ ξ k).2 + ν ((levelPath ν F x₀ ξ k).1 k)) := rfl

/-- The invariant of Algorithm 3 for one level after `τ` base intervals (Giles 2015, §5.6): the
level's part `(y, k, A, r)` holds the single-level path stopped at step `k`; its last update time
`τ_k` is at most `τ`; `τ + r = τ_{k+1}` is its next update time; and `A` is the sum of the base
increments since `τ_k`. -/
def alg3Inv (ν : X → ℕ) (F : X → ℝ → X) (x₀ : X) (ξ : ℕ → ℝ) (τ : ℕ) (p : Alg3Part X) : Prop :=
  p.1 = (levelPath ν F x₀ ξ p.2.1).1 ∧ (levelPath ν F x₀ ξ p.2.1).2 ≤ τ ∧
    τ + p.2.2.2 = (levelPath ν F x₀ ξ p.2.1).2 + ν ((levelPath ν F x₀ ξ p.2.1).1 p.2.1) ∧
    p.2.2.1 = ∑ i ∈ Ico (levelPath ν F x₀ ξ p.2.1).2 τ, ξ i

/-- The invariant holds at the start (Giles 2015, §5.6). -/
lemma alg3Inv_init (ν : X → ℕ) (F : X → ℝ → X) (x₀ : X) (ξ : ℕ → ℝ) :
    alg3Inv ν F x₀ ξ 0 (fun _ => x₀, 0, 0, ν x₀) := by
  refine ⟨rfl, le_rfl, ?_, ?_⟩
  · show 0 + ν x₀ = 0 + ν x₀
    rfl
  · show (0 : ℝ) = ∑ i ∈ Ico 0 0, ξ i
    simp

/-- The invariant is preserved by a union sub-interval (Giles 2015, §5.6, Algorithm 3): if the
sub-interval of `n` base intervals does not pass the level's next update time, then after adding
the sum of the base increments over it the invariant holds again; when the update time is
reached, the accumulated increment is the increment of the level's step, so the level's update is
the single-level step. -/
lemma alg3Inv_step {ν : X → ℕ} {F : X → ℝ → X} {x₀ : X} {ξ : ℕ → ℝ} {τ n : ℕ}
    {p : Alg3Part X} (h : alg3Inv ν F x₀ ξ τ p) (hn : n ≤ p.2.2.2) :
    alg3Inv ν F x₀ ξ (τ + n) (alg3Level ν F n (∑ i ∈ Ico τ (τ + n), ξ i) p) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hsum : p.2.2.1 + ∑ i ∈ Ico τ (τ + n), ξ i =
      ∑ i ∈ Ico (levelPath ν F x₀ ξ p.2.1).2 (τ + n), ξ i := by
    rw [h4, Finset.sum_Ico_consecutive _ h2 (Nat.le_add_right τ n)]
  unfold alg3Level
  split_ifs with hr
  · have hrn : p.2.2.2 = n := le_antisymm hr hn
    have hend : (levelPath ν F x₀ ξ p.2.1).2 + ν ((levelPath ν F x₀ ξ p.2.1).1 p.2.1) =
        τ + n := by
      rw [← h3, hrn]
    have hincr : p.2.2.1 + ∑ i ∈ Ico τ (τ + n), ξ i =
        ∑ i ∈ Ico (levelPath ν F x₀ ξ p.2.1).2
          ((levelPath ν F x₀ ξ p.2.1).2 + ν ((levelPath ν F x₀ ξ p.2.1).1 p.2.1)), ξ i := by
      rw [hsum, hend]
    have hnew : (levelPath ν F x₀ ξ (p.2.1 + 1)).1 =
        extendPath p.2.1 p.1 (F (p.1 p.2.1) (p.2.2.1 + ∑ i ∈ Ico τ (τ + n), ξ i)) := by
      rw [levelPath_succ, hincr, h1]
    have hnew2 : (levelPath ν F x₀ ξ (p.2.1 + 1)).2 = τ + n := by
      rw [levelPath_succ]
      exact hend
    refine ⟨hnew.symm, hnew2.le, ?_, ?_⟩
    · show τ + n + ν (F (p.1 p.2.1) (p.2.2.1 + ∑ i ∈ Ico τ (τ + n), ξ i)) =
        (levelPath ν F x₀ ξ (p.2.1 + 1)).2 +
          ν ((levelPath ν F x₀ ξ (p.2.1 + 1)).1 (p.2.1 + 1))
      rw [hnew2, hnew, extendPath_of_lt _ _ (Nat.lt_succ_self _)]
    · show (0 : ℝ) = ∑ i ∈ Ico (levelPath ν F x₀ ξ (p.2.1 + 1)).2 (τ + n), ξ i
      rw [hnew2, Finset.Ico_self, Finset.sum_empty]
  · refine ⟨h1, h2.trans (Nat.le_add_right τ n), ?_, hsum⟩
    show τ + n + (p.2.2.2 - n) =
      (levelPath ν F x₀ ξ p.2.1).2 + ν ((levelPath ν F x₀ ξ p.2.1).1 p.2.1)
    rw [← h3]
    omega

/-- The state of Algorithm 3 driven by the base increments after one more iteration (Giles 2015,
§5.6). -/
lemma alg3Path_succ_state (νc νf : X → ℕ) (Fc Ff : X → ℝ → X) (xc₀ xf₀ : X) (ξ : ℕ → ℝ)
    (j : ℕ) :
    (alg3Path νc νf Fc Ff xc₀ xf₀ ξ (j + 1)).1 (j + 1) =
      alg3Update νc νf Fc Ff ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j)
        (∑ i ∈ Ico (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).2
          ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).2 +
            alg3Len ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j)), ξ i) := by
  rw [alg3Path, adaptivePath_succ_fst, extendPath_of_lt _ _ (Nat.lt_succ_self j)]
  rfl

/-- The base interval reached by Algorithm 3 after one more iteration (Giles 2015, §5.6). -/
lemma alg3Path_succ_snd (νc νf : X → ℕ) (Fc Ff : X → ℝ → X) (xc₀ xf₀ : X) (ξ : ℕ → ℝ)
    (j : ℕ) :
    (alg3Path νc νf Fc Ff xc₀ xf₀ ξ (j + 1)).2 = (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).2 +
      alg3Len ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j) := rfl

/-- Algorithm 3 keeps the invariant (Giles 2015, §5.6, p. 44, lines 1928–1929: "The independent
Brownian increments can be simulated for each time interval, and summed to give `W(t)` at the
required times"): driven by the base increments, after every iteration both levels' parts satisfy
the invariant; in particular each level's path is its single-level path on the base grid, stopped
at its current step. -/
lemma alg3Path_inv (νc νf : X → ℕ) (Fc Ff : X → ℝ → X) (xc₀ xf₀ : X) (ξ : ℕ → ℝ) :
    ∀ j, alg3Inv νc Fc xc₀ ξ (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).2
        ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j).1 ∧
      alg3Inv νf Ff xf₀ ξ (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).2
        ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j).2
  | 0 => ⟨alg3Inv_init νc Fc xc₀ ξ, alg3Inv_init νf Ff xf₀ ξ⟩
  | j + 1 => by
    obtain ⟨hc, hf⟩ := alg3Path_inv νc νf Fc Ff xc₀ xf₀ ξ j
    rw [alg3Path_succ_state, alg3Path_succ_snd]
    exact ⟨alg3Inv_step hc (min_le_left _ _), alg3Inv_step hf (min_le_right _ _)⟩

/-- With positive steps, a level has at least one base interval left before its next update
after every union sub-interval (Giles 2015, §5.6). -/
lemma alg3Level_pos {ν : X → ℕ} {F : X → ℝ → X} (hν : ∀ x, 1 ≤ ν x) (n : ℕ) (e : ℝ)
    (p : Alg3Part X) : 1 ≤ (alg3Level ν F n e p).2.2.2 := by
  unfold alg3Level
  split_ifs with hr
  · exact hν _
  · exact Nat.sub_pos_of_lt (Nat.lt_of_not_le hr)

/-- With positive steps, both levels always have a base interval left before their next update
(Giles 2015, §5.6). -/
lemma alg3Path_pos {νc νf : X → ℕ} {Fc Ff : X → ℝ → X} (hνc : ∀ x, 1 ≤ νc x)
    (hνf : ∀ x, 1 ≤ νf x) (xc₀ xf₀ : X) (ξ : ℕ → ℝ) :
    ∀ j, 1 ≤ ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j).1.2.2.2 ∧
      1 ≤ ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j).2.2.2.2
  | 0 => ⟨hνc xc₀, hνf xf₀⟩
  | j + 1 => by
    rw [alg3Path_succ_state]
    exact ⟨alg3Level_pos hνc _ _ _, alg3Level_pos hνf _ _ _⟩

/-- With positive steps, Algorithm 3 advances by at least one base interval per iteration (Giles
2015, §5.6). -/
lemma alg3Path_time {νc νf : X → ℕ} {Fc Ff : X → ℝ → X} (hνc : ∀ x, 1 ≤ νc x)
    (hνf : ∀ x, 1 ≤ νf x) (xc₀ xf₀ : X) (ξ : ℕ → ℝ) :
    ∀ j, j ≤ (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).2
  | 0 => Nat.zero_le _
  | j + 1 => by
    have h := alg3Path_time hνc hνf (Fc := Fc) (Ff := Ff) xc₀ xf₀ ξ j
    obtain ⟨hc, hf⟩ := alg3Path_pos hνc hνf (Fc := Fc) (Ff := Ff) xc₀ xf₀ ξ j
    have hl : 1 ≤ alg3Len ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j) := le_min hc hf
    rw [alg3Path_succ_snd]
    omega

/-- The update times of a single-level path increase (Giles 2015, §5.6). -/
lemma levelPath_snd_mono (ν : X → ℕ) (F : X → ℝ → X) (x₀ : X) (ξ : ℕ → ℝ) :
    Monotone fun k => (levelPath ν F x₀ ξ k).2 :=
  monotone_nat_of_le_succ fun k => by
    rw [levelPath_succ]
    exact Nat.le_add_right _ _

/-- Under the invariant, the current base interval is at most the level's next update time (Giles
2015, §5.6). -/
lemma alg3Inv_time_le {ν : X → ℕ} {F : X → ℝ → X} {x₀ : X} {ξ : ℕ → ℝ} {τ : ℕ}
    {p : Alg3Part X} (h : alg3Inv ν F x₀ ξ τ p) :
    τ ≤ (levelPath ν F x₀ ξ (p.2.1 + 1)).2 := by
  rw [levelPath_succ]
  show τ ≤ (levelPath ν F x₀ ξ p.2.1).2 + ν ((levelPath ν F x₀ ξ p.2.1).1 p.2.1)
  rw [← h.2.2.1]
  exact Nat.le_add_right _ _

/-- With positive steps, the coarse path of Algorithm 3 eventually makes any number `k` of steps
(Giles 2015, §5.6). -/
lemma alg3Path_reach_coarse {νc νf : X → ℕ} {Fc Ff : X → ℝ → X} (hνc : ∀ x, 1 ≤ νc x)
    (hνf : ∀ x, 1 ≤ νf x) (xc₀ xf₀ : X) (ξ : ℕ → ℝ) (k : ℕ) :
    ∃ j, k ≤ ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j).1.2.1 := by
  by_contra hne
  set J := (levelPath νc Fc xc₀ ξ k).2 + 1
  have hJ : ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ J).1 J).1.2.1 + 1 ≤ k :=
    Nat.lt_of_not_le fun hj => hne ⟨J, hj⟩
  have h1 := (alg3Path_inv νc νf Fc Ff xc₀ xf₀ ξ J).1
  have h2 := alg3Inv_time_le h1
  have h3 := levelPath_snd_mono νc Fc xc₀ ξ hJ
  have h4 := alg3Path_time hνc hνf (Fc := Fc) (Ff := Ff) xc₀ xf₀ ξ J
  simp only at h3
  omega

/-- With positive steps, the fine path of Algorithm 3 eventually makes any number `k` of steps
(Giles 2015, §5.6). -/
lemma alg3Path_reach_fine {νc νf : X → ℕ} {Fc Ff : X → ℝ → X} (hνc : ∀ x, 1 ≤ νc x)
    (hνf : ∀ x, 1 ≤ νf x) (xc₀ xf₀ : X) (ξ : ℕ → ℝ) (k : ℕ) :
    ∃ j, k ≤ ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j).2.2.1 := by
  by_contra hne
  set J := (levelPath νf Ff xf₀ ξ k).2 + 1
  have hJ : ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ J).1 J).2.2.1 + 1 ≤ k :=
    Nat.lt_of_not_le fun hj => hne ⟨J, hj⟩
  have h1 := (alg3Path_inv νc νf Fc Ff xc₀ xf₀ ξ J).2
  have h2 := alg3Inv_time_le h1
  have h3 := levelPath_snd_mono νf Ff xf₀ ξ hJ
  have h4 := alg3Path_time hνc hνf (Fc := Fc) (Ff := Ff) xc₀ xf₀ ξ J
  simp only at h3
  omega

/-- A counter `κ` either reaches `k` or stays below it forever (Giles 2015, §5.6: reading a path
off Algorithm 3). -/
lemma alg3_exists_reach (κ : ℕ → ℕ) (k : ℕ) : ∃ n, k ≤ κ n ∨ ∀ j, κ j < k := by
  by_cases h : ∃ j, k ≤ κ j
  · obtain ⟨j, hj⟩ := h
    exact ⟨j, Or.inl hj⟩
  · exact ⟨0, Or.inr fun j => Nat.lt_of_not_le fun hj => h ⟨j, hj⟩⟩

/-- The first iteration after which the counter `κ` has reached `k` (`0` if it never does)
(Giles 2015, §5.6). -/
noncomputable def alg3FirstReach (κ : ℕ → ℕ) (k : ℕ) : ℕ :=
  @Nat.find (fun n => k ≤ κ n ∨ ∀ j, κ j < k) (fun _ => Classical.propDecidable _)
    (alg3_exists_reach κ k)

/-- If the counter reaches `k`, it has reached it at `alg3FirstReach` (Giles 2015, §5.6). -/
lemma le_alg3FirstReach {κ : ℕ → ℕ} {k : ℕ} (h : ∃ j, k ≤ κ j) :
    k ≤ κ (alg3FirstReach κ k) := by
  rcases @Nat.find_spec (fun n => k ≤ κ n ∨ ∀ j, κ j < k) (fun _ => Classical.propDecidable _)
    (alg3_exists_reach κ k) with h1 | h1
  · exact h1
  · obtain ⟨j, hj⟩ := h
    exact absurd hj (Nat.not_le.2 (h1 j))

/-- The coarse path read off Algorithm 3 (Giles 2015, §5.6): its `k`-th value is the coarse
state after the coarse path's `k`-th update, read at the first iteration after that update (if the
coarse path never makes `k` steps, which positive steps exclude, it is read at iteration `0`). -/
noncomputable def alg3CoarseSeq (traj : ℕ → Alg3State X) (k : ℕ) : X :=
  (traj (alg3FirstReach (fun j => (traj j).1.2.1) k)).1.1 k

/-- The fine path read off Algorithm 3 (Giles 2015, §5.6): its `k`-th value is the fine state
after the fine path's `k`-th update, read at the first iteration after that update. -/
noncomputable def alg3FineSeq (traj : ℕ → Alg3State X) (k : ℕ) : X :=
  (traj (alg3FirstReach (fun j => (traj j).2.2.1) k)).2.1 k

/-- **Run on the base increments, Algorithm 3 computes the single-level coarse path** (Giles 2015,
§5.6, p. 44, lines 1926–1929: "The underlying Brownian path needs to be sampled at a set of times
which are the union of the simulation times used by the coarse and fine path. The independent
Brownian increments can be simulated for each time interval, and summed to give `W(t)` at the
required times").  Let each union sub-interval of Algorithm 3 receive the sum of the base
increments `ξ_i` over it (`alg3Path`), and let the steps of both levels be at least one base
interval.  Then, for every `ξ`, the coarse path read off Algorithm 3 (`alg3CoarseSeq`, its state
after each of its updates) is the single-level coarse path on the base grid: steps of `νc(x_k)`
base intervals, each updated by `Fc` with the sum of the base increments over the step. -/
theorem alg3CoarseSeq_alg3Path {νc νf : X → ℕ} {Fc Ff : X → ℝ → X} (hνc : ∀ x, 1 ≤ νc x)
    (hνf : ∀ x, 1 ≤ νf x) (xc₀ xf₀ : X) (ξ : ℕ → ℝ) :
    alg3CoarseSeq (fun j => (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j) =
      adaptiveSeq (fun k y => νc (y k)) (fun k y e => Fc (y k) e) xc₀ ξ := by
  funext k
  have hJ := le_alg3FirstReach
    (alg3Path_reach_coarse hνc hνf (Fc := Fc) (Ff := Ff) xc₀ xf₀ ξ k)
  set J := alg3FirstReach (fun j => ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j).1.2.1) k
  have h1 := (alg3Path_inv νc νf Fc Ff xc₀ xf₀ ξ J).1.1
  show ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ J).1 J).1.1 k = _
  rw [h1]
  show (adaptivePath (fun k y => νc (y k)) (fun k y e => Fc (y k) e) xc₀ ξ _).1 k = _
  rw [adaptivePath_fst_apply, min_eq_left hJ]

/-- **Run on the base increments, Algorithm 3 computes the single-level fine path** (Giles 2015,
§5.6, p. 44, lines 1926–1929: "The underlying Brownian path needs to be sampled at a set of times
which are the union of the simulation times used by the coarse and fine path. The independent
Brownian increments can be simulated for each time interval, and summed to give `W(t)` at the
required times").  As `alg3CoarseSeq_alg3Path`, for the fine path: driven by the base increments
`ξ_i` (`alg3Path`), with steps of at least one base interval, the fine path read off Algorithm 3
(`alg3FineSeq`) is, for every `ξ`, the single-level fine path on the base grid: steps of `νf(x_k)`
base intervals, each updated by `Ff` with the sum of the base increments over the step. -/
theorem alg3FineSeq_alg3Path {νc νf : X → ℕ} {Fc Ff : X → ℝ → X} (hνc : ∀ x, 1 ≤ νc x)
    (hνf : ∀ x, 1 ≤ νf x) (xc₀ xf₀ : X) (ξ : ℕ → ℝ) :
    alg3FineSeq (fun j => (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j) =
      adaptiveSeq (fun k y => νf (y k)) (fun k y e => Ff (y k) e) xf₀ ξ := by
  funext k
  have hJ := le_alg3FirstReach
    (alg3Path_reach_fine hνc hνf (Fc := Fc) (Ff := Ff) xc₀ xf₀ ξ k)
  set J := alg3FirstReach (fun j => ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j).2.2.1) k
  have h1 := (alg3Path_inv νc νf Fc Ff xc₀ xf₀ ξ J).2.1
  show ((alg3Path νc νf Fc Ff xc₀ xf₀ ξ J).1 J).2.1 k = _
  rw [h1]
  show (adaptivePath (fun k y => νf (y k)) (fun k y e => Ff (y k) e) xf₀ ξ _).1 k = _
  rw [adaptivePath_fst_apply, min_eq_left hJ]

end Algorithm3

section Algorithm3Law

variable {X : Type*} [MeasurableSpace X]

/-- Evaluation at a random index is measurable (Giles 2015, §5.6). -/
lemma measurable_eval_natIndex : Measurable fun q : ℕ × (ℕ → X) => q.2 q.1 :=
  measurable_from_prod_countable_right fun n => measurable_pi_apply n

/-- `extendPath` at a random step is measurable (Giles 2015, §5.6). -/
lemma measurable_extendPath_uncurry :
    Measurable fun q : ℕ × (ℕ → X) × X => extendPath q.1 q.2.1 q.2.2 :=
  measurable_from_prod_countable_right fun k => measurable_extendPath k

/-- One level's update over a union sub-interval is measurable (Giles 2015, §5.6). -/
lemma measurable_alg3Level {ν : X → ℕ} {F : X → ℝ → X} (hν : Measurable ν)
    (hF : Measurable (Function.uncurry F)) :
    Measurable fun q : ℕ × ℝ × Alg3Part X => alg3Level ν F q.1 q.2.1 q.2.2 := by
  have hn : Measurable fun q : ℕ × ℝ × Alg3Part X => q.1 := measurable_fst
  have he : Measurable fun q : ℕ × ℝ × Alg3Part X => q.2.1 := measurable_snd.fst
  have hy : Measurable fun q : ℕ × ℝ × Alg3Part X => q.2.2.1 := measurable_snd.snd.fst
  have hk : Measurable fun q : ℕ × ℝ × Alg3Part X => q.2.2.2.1 := measurable_snd.snd.snd.fst
  have hA : Measurable fun q : ℕ × ℝ × Alg3Part X => q.2.2.2.2.1 :=
    measurable_snd.snd.snd.snd.fst
  have hr : Measurable fun q : ℕ × ℝ × Alg3Part X => q.2.2.2.2.2 :=
    measurable_snd.snd.snd.snd.snd
  have hx : Measurable fun q : ℕ × ℝ × Alg3Part X => q.2.2.1 q.2.2.2.1 :=
    measurable_eval_natIndex.comp (hk.prodMk hy)
  have hFx : Measurable fun q : ℕ × ℝ × Alg3Part X =>
      F (q.2.2.1 q.2.2.2.1) (q.2.2.2.2.1 + q.2.1) :=
    hF.comp (hx.prodMk (hA.add he))
  have hset : MeasurableSet {q : ℕ × ℝ × Alg3Part X | q.2.2.2.2.2 ≤ q.1} :=
    (hr.prodMk hn) (MeasurableSet.of_discrete (s := {p : ℕ × ℕ | p.1 ≤ p.2}))
  have hsub : Measurable fun q : ℕ × ℝ × Alg3Part X => q.2.2.2.2.2 - q.1 :=
    (measurable_of_countable fun p : ℕ × ℕ => p.1 - p.2).comp (hr.prodMk hn)
  unfold alg3Level
  exact Measurable.ite hset
    ((measurable_extendPath_uncurry.comp (hk.prodMk (hy.prodMk hFx))).prodMk
      ((hk.add_const 1).prodMk (measurable_const.prodMk (hν.comp hFx))))
    (hy.prodMk (hk.prodMk ((hA.add he).prodMk hsub)))

/-- The length of the union sub-interval is measurable (Giles 2015, §5.6). -/
lemma measurable_alg3Len : Measurable (alg3Len : Alg3State X → ℕ) :=
  (measurable_of_countable fun p : ℕ × ℕ => min p.1 p.2).comp
    (measurable_fst.snd.snd.snd.prodMk measurable_snd.snd.snd.snd)

/-- One iteration of Algorithm 3 is measurable (Giles 2015, §5.6). -/
lemma measurable_alg3Update {νc νf : X → ℕ} {Fc Ff : X → ℝ → X} (hνc : Measurable νc)
    (hνf : Measurable νf) (hFc : Measurable (Function.uncurry Fc))
    (hFf : Measurable (Function.uncurry Ff)) (j : ℕ) :
    Measurable fun p : (ℕ → Alg3State X) × ℝ => alg3Update νc νf Fc Ff (p.1 j) p.2 := by
  have hs : Measurable fun p : (ℕ → Alg3State X) × ℝ => p.1 j :=
    (measurable_pi_apply j).comp measurable_fst
  have hl := measurable_alg3Len.comp hs
  exact ((measurable_alg3Level hνc hFc).comp (hl.prodMk (measurable_snd.prodMk hs.fst))).prodMk
    ((measurable_alg3Level hνf hFf).comp (hl.prodMk (measurable_snd.prodMk hs.snd)))

/-- Reading the coarse path off the states of Algorithm 3 is measurable (Giles 2015, §5.6). -/
lemma measurable_alg3CoarseSeq : Measurable (alg3CoarseSeq : (ℕ → Alg3State X) → ℕ → X) := by
  refine measurable_pi_lambda _ fun k => ?_
  have hκ : ∀ n, Measurable fun traj : ℕ → Alg3State X => (traj n).1.2.1 := fun n =>
    (measurable_pi_apply n).fst.snd.fst
  have hp : ∀ n, MeasurableSet {traj : ℕ → Alg3State X |
      k ≤ (traj n).1.2.1 ∨ ∀ j, (traj j).1.2.1 < k} := fun n => by
    have h1 : MeasurableSet {traj : ℕ → Alg3State X | k ≤ (traj n).1.2.1} :=
      (hκ n) (MeasurableSet.of_discrete (s := {m : ℕ | k ≤ m}))
    have h2 : MeasurableSet {traj : ℕ → Alg3State X | ∀ j, (traj j).1.2.1 < k} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j =>
        (hκ j) (MeasurableSet.of_discrete (s := {m : ℕ | m < k}))
    exact h1.union h2
  have hf : ∀ n, Measurable fun traj : ℕ → Alg3State X => (traj n).1.1 k := fun n =>
    (measurable_pi_apply k).comp (measurable_pi_apply n).fst.fst
  exact @Measurable.find (ℕ → Alg3State X) X _ _ (fun n traj => (traj n).1.1 k)
    (fun n traj => k ≤ (traj n).1.2.1 ∨ ∀ j, (traj j).1.2.1 < k)
    (fun _ _ => Classical.propDecidable _) hf hp (fun traj => alg3_exists_reach _ k)

/-- Reading the fine path off the states of Algorithm 3 is measurable (Giles 2015, §5.6). -/
lemma measurable_alg3FineSeq : Measurable (alg3FineSeq : (ℕ → Alg3State X) → ℕ → X) := by
  refine measurable_pi_lambda _ fun k => ?_
  have hκ : ∀ n, Measurable fun traj : ℕ → Alg3State X => (traj n).2.2.1 := fun n =>
    (measurable_pi_apply n).snd.snd.fst
  have hp : ∀ n, MeasurableSet {traj : ℕ → Alg3State X |
      k ≤ (traj n).2.2.1 ∨ ∀ j, (traj j).2.2.1 < k} := fun n => by
    have h1 : MeasurableSet {traj : ℕ → Alg3State X | k ≤ (traj n).2.2.1} :=
      (hκ n) (MeasurableSet.of_discrete (s := {m : ℕ | k ≤ m}))
    have h2 : MeasurableSet {traj : ℕ → Alg3State X | ∀ j, (traj j).2.2.1 < k} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j =>
        (hκ j) (MeasurableSet.of_discrete (s := {m : ℕ | m < k}))
    exact h1.union h2
  have hf : ∀ n, Measurable fun traj : ℕ → Alg3State X => (traj n).2.1 k := fun n =>
    (measurable_pi_apply k).comp (measurable_pi_apply n).snd.fst
  exact @Measurable.find (ℕ → Alg3State X) X _ _ (fun n traj => (traj n).2.1 k)
    (fun n traj => k ≤ (traj n).2.2.1 ∨ ∀ j, (traj j).2.2.1 < k)
    (fun _ _ => Classical.propDecidable _) hf hp (fun traj => alg3_exists_reach _ k)

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {ζ : ℕ → Ω' → ℝ}

/-- A measurable read-out of the states of Algorithm 3 has the same law whether the union
sub-intervals receive fresh increments `√h ζ_j` (`alg3Fresh`) or the sums of i.i.d. `N(0, δ)` base
increments over them (`alg3Path`) (Giles 2015, §5.6, p. 44, lines 1928–1929: "The independent
Brownian increments can be simulated for each time interval"): Algorithm 3 is itself an adaptive
scheme on the base grid whose steps are the union sub-intervals (`adaptiveSeq_law_eq_fresh`). -/
lemma map_alg3Fresh_readout (hζind : iIndepFun ζ P')
    (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P') {νc νf : X → ℕ} {Fc Ff : X → ℝ → X}
    (hνc : Measurable νc) (hνf : Measurable νf) (hFc : Measurable (Function.uncurry Fc))
    (hFf : Measurable (Function.uncurry Ff)) (δ : ℝ≥0) (xc₀ xf₀ : X) {Z : Type*}
    [MeasurableSpace Z] {R : (ℕ → Alg3State X) → Z} (hR : Measurable R) :
    P'.map (fun ω => R (alg3Fresh νc νf Fc Ff δ xc₀ xf₀ fun i => ζ i ω)) =
      (Measure.infinitePi fun _ => gaussianReal 0 δ).map fun ξ =>
        R fun j => (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j := by
  have hξind : iIndepFun (fun i (ξ : ℕ → ℝ) => ξ i)
      (Measure.infinitePi fun _ => gaussianReal 0 δ) :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) fun _ => measurable_id
  have hξ : ∀ i, HasLaw (fun ξ : ℕ → ℝ => ξ i) (gaussianReal 0 δ)
      (Measure.infinitePi fun _ => gaussianReal 0 δ) := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have hlen : ∀ j, Measurable fun z : ℕ → Alg3State X => alg3Len (z j) := fun j =>
    measurable_alg3Len.comp (measurable_pi_apply j)
  have hupd := measurable_alg3Update hνc hνf hFc hFf
  have hA := adaptiveSeq_law_eq_fresh hξind hξ hζind hζ (ν := fun j z => alg3Len (z j))
    (G := fun j z e => alg3Update νc νf Fc Ff (z j) e) hlen hupd (alg3Init νc νf xc₀ xf₀)
  have hupd' : ∀ j, Measurable fun p : (ℕ → Alg3State X) × ℝ =>
      alg3Update νc νf Fc Ff (p.1 j) (Real.sqrt (alg3Len (p.1 j) * δ) * p.2) := fun j =>
    (hupd j).comp (measurable_fst.prodMk
      ((((measurable_from_nat.comp ((hlen j).comp measurable_fst)).mul_const _).sqrt).mul
        measurable_snd))
  have hmF : Measurable (alg3Fresh νc νf Fc Ff δ xc₀ xf₀) := measurable_freshSeq hupd' _
  have hmB : Measurable fun ξ : ℕ → ℝ => fun j => (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j :=
    measurable_adaptiveSeq (ν := fun j z => alg3Len (z j))
      (G := fun j z e => alg3Update νc νf Fc Ff (z j) e) hlen hupd _
  have hlaw : P'.map (fun ω => alg3Fresh νc νf Fc Ff δ xc₀ xf₀ fun i => ζ i ω) =
      (Measure.infinitePi fun _ => gaussianReal 0 δ).map fun ξ =>
        fun j => (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j := hA.symm
  have hmζ : AEMeasurable (fun ω i => ζ i ω) P' :=
    aemeasurable_pi_iff.2 fun i => (hζ i).aemeasurable
  have e1 : (fun ω => R (alg3Fresh νc νf Fc Ff δ xc₀ xf₀ fun i => ζ i ω)) =
      R ∘ fun ω => alg3Fresh νc νf Fc Ff δ xc₀ xf₀ fun i => ζ i ω := rfl
  have e2 : (fun ξ : ℕ → ℝ => R fun j => (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j) =
      R ∘ fun ξ : ℕ → ℝ => fun j => (alg3Path νc νf Fc Ff xc₀ xf₀ ξ j).1 j := rfl
  rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable (g := R)
    (f := fun ω => alg3Fresh νc νf Fc Ff δ xc₀ xf₀ fun i => ζ i ω) hR.aemeasurable
    (hmF.comp_aemeasurable hmζ), hlaw, Measure.map_map hR hmB]

/-- **Algorithm 3 is correct: each path read off the union-grid loop has its single-level law**
(Giles 2015, §5.6, pp. 44–45, lines 1924–1966: "It may appear that this would cause difficulties
in the MLMC implementation, but Figure 5.9 tries to illustrate that it does not. The underlying
Brownian path needs to be sampled at a set of times which are the union of the simulation times
used by the coarse and fine path. The independent Brownian increments can be simulated for each
time interval, and summed to give `W(t)` at the required times. An outline algorithm to implement
this is given in Algorithm 3").  `alg3Fresh` runs Algorithm 3: each union sub-interval runs to the
next update time of either path, `h = n δ`, and receives a fresh increment `∆W = √h ζ_j`
(`ζ_0, ζ_1, …` independent standard normal); `∆W` is added to both accumulators, and a path whose
update time is reached is updated with its accumulator (`Fc`, `Ff`), computes its next step (`νc`,
`νf` base intervals of length `δ`, at least one, from its new state) and resets its accumulator.
Then the coarse path read off the loop (`alg3CoarseSeq`, its state after each of its updates) has
the law of the single-level adaptive scheme `x_{k+1} = Fc(x_k, √(νc(x_k) δ) Z_k)` driven by fresh
standard normal `Z_k`, and likewise the fine path, which gives (2.4).  The joint law of the two
paths is `algorithm3_joint_law`.  Step sizes are positive multiples of `δ`, and the loop runs
indefinitely (a rule that ends a step exactly at `T` and continues with positive steps afterwards
gives the paths of Algorithm 3 up to `T`). -/
theorem algorithm3_law (hζind : iIndepFun ζ P') (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P')
    {νc νf : X → ℕ} {Fc Ff : X → ℝ → X} (hνc : Measurable νc) (hνf : Measurable νf)
    (hFc : Measurable (Function.uncurry Fc)) (hFf : Measurable (Function.uncurry Ff))
    (hposc : ∀ x, 1 ≤ νc x) (hposf : ∀ x, 1 ≤ νf x) (δ : ℝ≥0) (xc₀ xf₀ : X) :
    P'.map (fun ω => alg3CoarseSeq (alg3Fresh νc νf Fc Ff δ xc₀ xf₀ fun i => ζ i ω)) =
        P'.map (fun ω => freshSeq (fun k y z => Fc (y k) (Real.sqrt (νc (y k) * δ) * z)) xc₀
          fun i => ζ i ω) ∧
      P'.map (fun ω => alg3FineSeq (alg3Fresh νc νf Fc Ff δ xc₀ xf₀ fun i => ζ i ω)) =
        P'.map (fun ω => freshSeq (fun k y z => Ff (y k) (Real.sqrt (νf (y k) * δ) * z)) xf₀
          fun i => ζ i ω) := by
  have hξind : iIndepFun (fun i (ξ : ℕ → ℝ) => ξ i)
      (Measure.infinitePi fun _ => gaussianReal 0 δ) :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) fun _ => measurable_id
  have hξ : ∀ i, HasLaw (fun ξ : ℕ → ℝ => ξ i) (gaussianReal 0 δ)
      (Measure.infinitePi fun _ => gaussianReal 0 δ) := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have hνc' : ∀ k, Measurable fun y : ℕ → X => νc (y k) :=
    fun k => hνc.comp (measurable_pi_apply k)
  have hνf' : ∀ k, Measurable fun y : ℕ → X => νf (y k) :=
    fun k => hνf.comp (measurable_pi_apply k)
  have hpk : ∀ k, Measurable fun p : (ℕ → X) × ℝ => (p.1 k, p.2) :=
    fun k => ((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd
  have hFc' : ∀ k, Measurable fun p : (ℕ → X) × ℝ => Fc (p.1 k) p.2 :=
    fun k => hFc.comp (hpk k)
  have hFf' : ∀ k, Measurable fun p : (ℕ → X) × ℝ => Ff (p.1 k) p.2 :=
    fun k => hFf.comp (hpk k)
  constructor
  · rw [map_alg3Fresh_readout hζind hζ hνc hνf hFc hFf δ xc₀ xf₀ measurable_alg3CoarseSeq,
      ← adaptiveSeq_law_eq_fresh hξind hξ hζind hζ hνc' hFc' xc₀]
    congr 1
    funext ξ
    exact alg3CoarseSeq_alg3Path hposc hposf xc₀ xf₀ ξ
  · rw [map_alg3Fresh_readout hζind hζ hνc hνf hFc hFf δ xc₀ xf₀ measurable_alg3FineSeq,
      ← adaptiveSeq_law_eq_fresh hξind hξ hζind hζ hνf' hFf' xf₀]
    congr 1
    funext ξ
    exact alg3FineSeq_alg3Path hposc hposf xc₀ xf₀ ξ

/-- **Algorithm 3 produces the coupling of Figure 5.9: the pair of paths it computes has the law
of the two single-level paths driven by one Brownian path sampled on the base grid** (Giles 2015,
§5.6, pp. 44–45, lines 1926–1966, Figure 5.9 "Generation of Brownian increments for a multilevel
simulation with adaptive timestepping": "The underlying Brownian path needs to be sampled at a set
of times which are the union of the simulation times used by the coarse and fine path. The
independent Brownian increments can be simulated for each time interval, and summed to give `W(t)`
at the required times").  Algorithm 3 (`alg3Fresh`) is driven by independent standard normal
`ζ_j` on `(Ω', P')`, as in `algorithm3_law`.  On `(Ω, P)`, let `ξ_0, ξ_1, …` be independent
`N(0, δ)` (the Brownian increments over the base grid), and run both single-level paths on them:
the coarse path with steps of `νc(x_k)` base intervals and the update `Fc`, the fine path with
steps of `νf(x_k)` base intervals and `Ff`, each step's increment being the sum of the base
increments over it.  Then the pair (coarse path, fine path) read off Algorithm 3 has the same law
as this pair (a law on `(ℕ → X) × (ℕ → X)`).  Step sizes are positive multiples of `δ`, and the
loop runs indefinitely. -/
theorem algorithm3_joint_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {δ : ℝ≥0}
    {ξ : ℕ → Ω → ℝ} (hind : iIndepFun ξ P) (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P)
    (hζind : iIndepFun ζ P') (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P')
    {νc νf : X → ℕ} {Fc Ff : X → ℝ → X} (hνc : Measurable νc) (hνf : Measurable νf)
    (hFc : Measurable (Function.uncurry Fc)) (hFf : Measurable (Function.uncurry Ff))
    (hposc : ∀ x, 1 ≤ νc x) (hposf : ∀ x, 1 ≤ νf x) (xc₀ xf₀ : X) :
    P'.map (fun ω => (alg3CoarseSeq (alg3Fresh νc νf Fc Ff δ xc₀ xf₀ fun i => ζ i ω),
        alg3FineSeq (alg3Fresh νc νf Fc Ff δ xc₀ xf₀ fun i => ζ i ω))) =
      P.map (fun ω => (adaptiveSeq (fun k y => νc (y k)) (fun k y e => Fc (y k) e) xc₀
          (fun i => ξ i ω),
        adaptiveSeq (fun k y => νf (y k)) (fun k y e => Ff (y k) e) xf₀ (fun i => ξ i ω))) := by
  have hpk : ∀ k, Measurable fun p : (ℕ → X) × ℝ => (p.1 k, p.2) :=
    fun k => ((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd
  have hS : Measurable fun ξ : ℕ → ℝ =>
      (adaptiveSeq (fun k y => νc (y k)) (fun k y e => Fc (y k) e) xc₀ ξ,
        adaptiveSeq (fun k y => νf (y k)) (fun k y e => Ff (y k) e) xf₀ ξ) :=
    (measurable_adaptiveSeq (fun k => hνc.comp (measurable_pi_apply k))
      (fun k => hFc.comp (hpk k)) xc₀).prodMk
      (measurable_adaptiveSeq (fun k => hνf.comp (measurable_pi_apply k))
        (fun k => hFf.comp (hpk k)) xf₀)
  rw [map_alg3Fresh_readout hζind hζ hνc hνf hFc hFf δ xc₀ xf₀
      (measurable_alg3CoarseSeq.prodMk measurable_alg3FineSeq), map_comp_of_iid hind hξ hS]
  congr 1
  funext ξ
  exact Prod.ext (alg3CoarseSeq_alg3Path hposc hposf xc₀ xf₀ ξ)
    (alg3FineSeq_alg3Path hposc hposf xc₀ xf₀ ξ)

end Algorithm3Law

section Algorithm3EM

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {ζ : ℕ → Ω' → ℝ}

/-- The Euler–Maruyama update `(x, ∆W) ↦ adaptiveEMStep a b (ν(x) δ) x ∆W` of a level with the
step rule `ν` is jointly measurable (Giles 2015, §5.6, Algorithm 3: "update coarse path using
`∆W^c`"). -/
lemma measurable_adaptiveEMStep_rule {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {ν : ℝ × ℝ → ℕ} (hν : Measurable ν) (δ : ℝ≥0) :
    Measurable (Function.uncurry fun x dW => adaptiveEMStep a b (ν x * δ) x dW) :=
  (measurable_adaptiveEMStep ha hb).comp
    (((measurable_from_nat.comp (hν.comp measurable_fst)).mul_const _).prodMk
      (measurable_fst.prodMk measurable_snd))

/-- **Algorithm 3 for the adaptive Euler–Maruyama scheme** (Giles 2015, §5.6, pp. 44–45,
lines 1917–1966: "a completely independent adaptation on each level of refinement, with an
adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)` … An outline algorithm to implement this is
given in Algorithm 3").  The coarse and the fine Euler–Maruyama paths `(t, Ŝ)` take steps of
`νc(t, Ŝ)` and `νf(t, Ŝ)` base intervals of length `δ` (at least one), each updated by
`Ŝ ↦ Ŝ + a(Ŝ, t) h + b(Ŝ, t) ∆W` with its own step `h` and its accumulated increment `∆W`, inside
Algorithm 3 driven by fresh normals on the union sub-intervals.  The coarse path read off the loop
has the law of the single-level adaptive Euler–Maruyama scheme `freshEM` with steps `νc δ`, the
fine path that with steps `νf δ`.  Step sizes are positive multiples of `δ`. -/
theorem algorithm3_EM_law (hζind : iIndepFun ζ P') (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P')
    {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {νc νf : ℝ × ℝ → ℕ} (hνc : Measurable νc)
    (hνf : Measurable νf) (hposc : ∀ x, 1 ≤ νc x) (hposf : ∀ x, 1 ≤ νf x) (δ : ℝ≥0)
    (S₀ : ℝ) :
    P'.map (fun ω => alg3CoarseSeq (alg3Fresh νc νf
        (fun x dW => adaptiveEMStep a b (νc x * δ) x dW)
        (fun x dW => adaptiveEMStep a b (νf x * δ) x dW) δ (0, S₀) (0, S₀) fun i => ζ i ω)) =
        P'.map (fun ω => freshEM a b (fun x => νc x * δ) S₀ fun i => ζ i ω) ∧
      P'.map (fun ω => alg3FineSeq (alg3Fresh νc νf
        (fun x dW => adaptiveEMStep a b (νc x * δ) x dW)
        (fun x dW => adaptiveEMStep a b (νf x * δ) x dW) δ (0, S₀) (0, S₀) fun i => ζ i ω)) =
        P'.map (fun ω => freshEM a b (fun x => νf x * δ) S₀ fun i => ζ i ω) := by
  obtain ⟨h1, h2⟩ := algorithm3_law hζind hζ hνc hνf
    (measurable_adaptiveEMStep_rule ha hb hνc δ) (measurable_adaptiveEMStep_rule ha hb hνf δ)
    hposc hposf δ (0, S₀) (0, S₀)
  have e : ∀ ν : ℝ × ℝ → ℕ, (fun k (y : ℕ → ℝ × ℝ) z =>
      adaptiveEMStep a b (ν (y k) * δ) (y k) (Real.sqrt (ν (y k) * δ) * z)) =
      fun k y z => adaptiveEMStep a b ((fun x => (ν x : ℝ≥0) * δ) (y k)) (y k)
        (Real.sqrt ((fun x => (ν x : ℝ≥0) * δ) (y k)) * z) := by
    intro ν
    funext k y z
    rw [NNReal.coe_mul, NNReal.coe_natCast]
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · unfold freshEM
    rw [e νc]
  · unfold freshEM
    rw [e νf]

/-- **Algorithm 3 computes the MLMC coupling of the adaptive Euler–Maruyama paths** (Giles 2015,
§5.6, pp. 44–45, lines 1917–1966: "a completely independent adaptation on each level of
refinement, with an adaptive timestep of the form `h_ℓ = 2^{−ℓ} H(Ŝ_n)` … The underlying Brownian
path needs to be sampled at a set of times which are the union of the simulation times used by the
coarse and fine path. The independent Brownian increments can be simulated for each time interval,
and summed to give `W(t)` at the required times").  In the setting of `algorithm3_EM_law`, the
pair (coarse, fine) of Euler–Maruyama paths `(t, Ŝ)` read off Algorithm 3 has the law of the pair
`(adaptiveEM` with `νc`, `adaptiveEM` with `νf)` of adaptive Euler–Maruyama paths computed from the
same independent `N(0, δ)` base increments `ξ_i`, i.e. from one Brownian path sampled on the base
grid.  Step sizes are positive multiples of `δ`. -/
theorem algorithm3_EM_joint_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {δ : ℝ≥0}
    {ξ : ℕ → Ω → ℝ} (hind : iIndepFun ξ P) (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 δ) P)
    (hζind : iIndepFun ζ P') (hζ : ∀ i, HasLaw (ζ i) (gaussianReal 0 1) P')
    {a b : ℝ → ℝ → ℝ} (ha : Measurable (Function.uncurry a))
    (hb : Measurable (Function.uncurry b)) {νc νf : ℝ × ℝ → ℕ} (hνc : Measurable νc)
    (hνf : Measurable νf) (hposc : ∀ x, 1 ≤ νc x) (hposf : ∀ x, 1 ≤ νf x) (S₀ : ℝ) :
    P'.map (fun ω => (alg3CoarseSeq (alg3Fresh νc νf
        (fun x dW => adaptiveEMStep a b (νc x * δ) x dW)
        (fun x dW => adaptiveEMStep a b (νf x * δ) x dW) δ (0, S₀) (0, S₀) fun i => ζ i ω),
      alg3FineSeq (alg3Fresh νc νf
        (fun x dW => adaptiveEMStep a b (νc x * δ) x dW)
        (fun x dW => adaptiveEMStep a b (νf x * δ) x dW) δ (0, S₀) (0, S₀) fun i => ζ i ω))) =
      P.map (fun ω => (adaptiveEM a b νc δ S₀ (fun i => ξ i ω),
        adaptiveEM a b νf δ S₀ (fun i => ξ i ω))) :=
  algorithm3_joint_law hind hξ hζind hζ hνc hνf (measurable_adaptiveEMStep_rule ha hb hνc δ)
    (measurable_adaptiveEMStep_rule ha hb hνf δ) hposc hposf (0, S₀) (0, S₀)

end Algorithm3EM

end MLMC
