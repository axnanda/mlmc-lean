import MlmcLean.PoissonCoupling
import MlmcLean.RoundingError
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

/-!
# Poisson variates on the union of two time grids (Giles 2015, §8 and §5.6)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §8
"Continuous-time Markov chains" (pp. 55–56), §5.6 "Stiff and highly nonlinear SDEs" (pp. 43–45,
Figure 5.9 and Algorithm 3) and, in the last section, §10.2 "Variable precision arithmetic" (p. 62).

§8, p. 56: "The non-nested adaptive timestepping approach described in Section 5.6 for SDEs is
equally applicable in this setting. As described in (Giles, Lester and Whittle 2015, Lester, Yates,
Giles and Baker 2015), the construction is exactly the same as illustrated in Figure 5.9, but with
Poisson variates for each time interval instead of Brownian increments."  §5.6, p. 44: when the
timesteps of the two levels "are not naturally nested", "The underlying Brownian path needs to be
sampled at a set of times which are the union of the simulation times used by the coarse and fine
path. The independent Brownian increments can be simulated for each time interval, and summed to
give `W(t)` at the required times."

**Poisson noise on a union grid.**  The sub-intervals of the union grid are indexed by a finite type
`ι`, the steps of one of the two paths by a finite type `κ`, and `b : ι → κ` sends each sub-interval
to the step of the path that contains it; any deterministic partition is allowed, so the grids of
the fine and the coarse path need not be nested.  The counts `X_i` on the sub-intervals are
independent Poisson variates with means `m_i` (for a Poisson process of rate `λ`, `m_i = λ h_i` with
`h_i` the length of sub-interval `i`), and the path uses the counts on its own steps,
`N_k = ∑_{b(i) = k} X_i` (`stepCounts`), as the SDE paths of §5.6 sum the Brownian increments.
* `hasLaw_finsetSum_poisson`: a finite sum of independent Poisson variates is Poisson with the
  summed mean (the `n`-fold form of `poisson_add_hasLaw`, §8, p. 55).
* `map_stepCounts_pi_poisson`, `stepCounts_hasLaw`, `iIndepFun_stepCounts`: **the counts on the
  steps of the path are independent Poisson variates with the summed means**; their joint law is
  `⊗_k P(∑_{b(i)=k} m_i)`, the law of the counts simulated directly on the path's own grid.
  `unionGrid_hasLaw`: for a Poisson process of rate `λ`, the fine and the coarse path, both driven
  by the counts on the union grid, see independent counts `P(λ H_k)` on their own steps of lengths
  `H_k`.
* `map_comp_stepCounts_eq`, `integral_comp_stepCounts_eq`: hence the path built from the summed
  counts has exactly the law of the path simulated on its own grid, and every payoff has the same
  mean (and is integrable in one simulation iff in the other).
* `unionGrid_2_4`: **the identity (2.4)** `E[P^f_ℓ] = E[P^c_ℓ]` (§2.1, p. 8): the level-`ℓ` path
  as the coarse path of a level-`(ℓ + 1)` sample (on the union of the grids of levels `ℓ + 1`
  and `ℓ`) and as the fine path of a level-`ℓ` sample (on the union of the grids of levels `ℓ`
  and `ℓ − 1`) has the same law, so the telescoping sum is respected.

**Tau-leaping on non-nested grids.**  In tau-leaping, `x_{n+1} = x_n + P(hλ(x_n))` (§8, p. 55), the
Poisson mean depends on the state.  On the union grid each path freezes its propensity at the start
of its own current step, and on every sub-interval the Poisson variates of the two paths are coupled
as in §8 (`coupledIncr`); each path's grid is given by its step boundaries `t 0 = 0 < t 1 < …` in
union-grid indices (`unionChain`).
* `unionChain_fine`, `unionChain_coarse`: **each path of the coupled simulation is tau-leaping on
  its own grid** — at the end of its `k`-th step its state has the law of `k` tau-leaping steps
  with its own (variable) step lengths (`tauChainVar`, `gridStepLength`).  `unionChain_nested`: for
  nested uniform grids this is the case `h^c = 2h` of `coupledChain_fst`, `coupledChain_snd`.
* `unionChain_2_4`: **(2.4) for tau-leaping on non-nested grids**, for payoffs of the terminal
  state (the chain theorems compare the laws of the state at one grid time, not the laws of whole
  paths; path functionals are covered by `unionGrid_2_4` when the rate does not depend on the
  state).

**Scope.**  All grids here are deterministic.  In the adaptive approach of §5.6 the timesteps
`h_ℓ = 2^{−ℓ} H(Ŝ_n)` depend on the path, so the union grid is random and the sub-intervals seen by
one path depend on the other path; identifying the law of each path then needs a conditional
(martingale) argument given the past of the simulation, which is not formalised here.

**§10.2** (last section, independent of the rest).  "This would not be the case if the increments on
level `ℓ` were generated with `B_ℓ` bits of accuracy, then summed to give increments for level
`ℓ−1`, regardless of whether the truncation to the lower accuracy `B_{ℓ−1}` took place before or
after the summation" (`roundFixed_sum_inconsistent_general`: for every exponent and bit-width, an
explicit region of fine increments on which all three ways of forming the coarse increment from the
rounded fine increments differ from the coarse increment rounded directly).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MLMC

/-! ### Sums of independent Poisson variates -/

/-- The Poisson law with mean `0` is the point mass at `0` (the empty sum in Giles 2015, §8). -/
lemma poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun n => ?_
  rw [poissonMeasure_singleton]
  rcases n with _ | n <;> simp

/-- **A finite sum of independent Poisson variates is Poisson** (Giles 2015, §8, p. 55: "for any
`t₁, t₂ > 0`, the sum of two independent Poisson variates `P(t₁)`, `P(t₂)` is equivalent in
distribution to `P(t₁ + t₂)`", applied repeatedly).  If the `X_i` are independent with laws
`P(m_i)`, then `∑_{i ∈ s} X_i` has law `P(∑_{i ∈ s} m_i)` for every finite set `s`. -/
theorem hasLaw_finsetSum_poisson {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ι → Ω → ℕ} {m : ι → ℝ≥0} (hind : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure (m i)) μ) (s : Finset ι) :
    HasLaw (fun ω => ∑ i ∈ s, X i ω) (poissonMeasure (∑ i ∈ s, m i)) μ := by
  classical
  have := hind.isProbabilityMeasure
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨aemeasurable_const, by
      rw [Measure.map_const, measure_univ, one_smul, poissonMeasure_zero]⟩
  | insert i s hi ih =>
    have hindep : IndepFun (∑ j ∈ s, X j) (X i) μ :=
      hind.indepFun_finsetSum_of_notMem₀ (fun j => (hX j).aemeasurable) hi
    have ih' : HasLaw (∑ j ∈ s, X j) (poissonMeasure (∑ j ∈ s, m j)) μ := by
      convert ih using 1
      funext ω
      simp
    have h := poisson_add_hasLaw hindep ih' (hX i)
    rw [Finset.sum_insert hi, add_comm (m i)]
    convert h using 1
    funext ω
    simp [Finset.sum_insert hi, add_comm]

/-- The sum of the coordinates under a product of Poisson laws is Poisson with the summed mean
(Giles 2015, §8). -/
lemma infinitePi_poisson_map_sum {J : Type*} [Fintype J] (m : J → ℝ≥0) :
    (Measure.infinitePi fun j => poissonMeasure (m j)).map (fun z => ∑ j, z j) =
      poissonMeasure (∑ j, m j) := by
  have hind : iIndepFun (fun j (z : J → ℕ) => z j)
      (Measure.infinitePi fun j => poissonMeasure (m j)) :=
    iIndepFun_infinitePi (X := fun _ (n : ℕ) => n) fun _ => measurable_id
  have hX : ∀ j, HasLaw (fun z : J → ℕ => z j) (poissonMeasure (m j))
      (Measure.infinitePi fun j => poissonMeasure (m j)) := fun j =>
    ⟨(measurable_pi_apply j).aemeasurable, Measure.infinitePi_map_eval _ j⟩
  exact (hasLaw_finsetSum_poisson hind hX Finset.univ).map_eq

/-! ### The counts on the steps of a path -/

/-- A sum over the sub-intervals in step `k` as a sum over the subtype `{i // b i = k}`. -/
lemma sum_filter_eq_sum_subtype {ι κ M : Type*} [Fintype ι] [DecidableEq κ] [AddCommMonoid M]
    (b : ι → κ) (k : κ) (f : ι → M) : ∑ i with b i = k, f i = ∑ j : {i // b i = k}, f j :=
  Finset.sum_subtype (univ.filter fun i => b i = k) (p := fun i => b i = k) (by simp) f

/-- **The counts on the steps of a path** (Giles 2015, §5.6, p. 44, and §8, p. 56): the union grid
has the sub-intervals `i : ι`, the path has the steps `k : κ`, and `b i` is the step containing
sub-interval `i`; from the counts `x i` on the sub-intervals, the count on step `k` is
`∑_{b(i) = k} x_i`, as "The independent Brownian increments can be simulated for each time
interval, and summed". -/
def stepCounts {ι κ : Type*} [Fintype ι] [DecidableEq κ] (b : ι → κ) (x : ι → ℕ) (k : κ) : ℕ :=
  ∑ i with b i = k, x i

/-- **The step counts of independent Poisson counts** (Giles 2015, §8, p. 56, with §5.6, p. 44):
under the product of the Poisson laws `P(m_i)` of the counts on the sub-intervals, the counts on
the steps have the product law `⊗_k P(∑_{b(i)=k} m_i)`. -/
theorem map_stepCounts_pi_poisson {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (b : ι → κ) (m : ι → ℝ≥0) :
    (Measure.pi fun i => poissonMeasure (m i)).map (stepCounts b) =
      Measure.pi fun k => poissonMeasure (∑ i with b i = k, m i) := by
  -- regroup the sub-intervals by step, `ι ≃ Σ k, {i // b i = k}`, and curry
  set e := Equiv.sigmaFiberEquiv b
  have hR : Measurable fun (x : ι → ℕ) (p : Σ k, {i // b i = k}) => x (e p) := by fun_prop
  have hC := (MeasurableEquiv.piCurry (fun (k : κ) (_ : {i // b i = k}) => ℕ)).measurable
  have hS : Measurable fun (y : (k : κ) → {i // b i = k} → ℕ) (k : κ) => ∑ j, y k j := by
    fun_prop
  have hcomp : stepCounts b = (fun (y : (k : κ) → {i // b i = k} → ℕ) (k : κ) => ∑ j, y k j) ∘
      (MeasurableEquiv.piCurry (fun (k : κ) (_ : {i // b i = k}) => ℕ)) ∘
      (fun (x : ι → ℕ) (p : Σ k, {i // b i = k}) => x (e p)) := by
    funext x k
    rw [stepCounts, sum_filter_eq_sum_subtype]
    rfl
  have h1 := Measure.infinitePi_map_piCurry
    (fun (k : κ) (j : {i // b i = k}) => poissonMeasure (m j))
  have h2 : (fun p : Σ k, {i // b i = k} => poissonMeasure (m (e p))) =
      fun p => poissonMeasure (m p.2) := rfl
  have h3 := Measure.infinitePi_map_pi
    (fun (k : κ) => Measure.infinitePi fun (j : {i // b i = k}) => poissonMeasure (m j))
    (f := fun (k : κ) (z : {i // b i = k} → ℕ) => ∑ j, z j) (fun k => by fun_prop)
  rw [← Measure.infinitePi_eq_pi, hcomp, ← Measure.map_map hS (hC.comp hR),
    ← Measure.map_map hC hR, Measure.map_infinitePi_infinitePi_of_inj e.injective, h2, h1, h3,
    ← Measure.infinitePi_eq_pi]
  congr 1
  funext k
  rw [infinitePi_poisson_map_sum, sum_filter_eq_sum_subtype]

section RandomVariables

variable {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype ι] [Fintype κ]
  [DecidableEq κ] {X : ι → Ω → ℕ} {m : ι → ℝ≥0}

/-- **The counts on the steps of a path are independent Poisson variates with the summed means**
(Giles 2015, §8, p. 56: "the construction is exactly the same as illustrated in Figure 5.9, but with
Poisson variates for each time interval instead of Brownian increments"; §5.6, p. 44: "The
independent Brownian increments can be simulated for each time interval, and summed").  If the
counts `X_i` on the sub-intervals of the union grid are independent with laws `P(m_i)`, the vector
of the counts on the steps of the path, `N_k = ∑_{b(i)=k} X_i`, has the joint law
`⊗_k P(∑_{b(i)=k} m_i)`: the law of independent counts simulated directly on the path's grid.  The
partition `b` is deterministic; the adaptive grids of §5.6, which depend on the path, are not
covered. -/
theorem stepCounts_hasLaw (hind : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure (m i)) μ) (b : ι → κ) :
    HasLaw (fun ω => stepCounts b fun i => X i ω)
      (Measure.pi fun k => poissonMeasure (∑ i with b i = k, m i)) μ :=
  (⟨Measurable.of_discrete.aemeasurable, map_stepCounts_pi_poisson b m⟩ :
    HasLaw (stepCounts b) (Measure.pi fun k => poissonMeasure (∑ i with b i = k, m i))
      (Measure.pi fun i => poissonMeasure (m i))).comp (hind.hasLaw_pi hX)

/-- **The step counts are independent, each Poisson with the summed mean** (Giles 2015, §8, p. 56,
and §5.6, p. 44): the counts `N_k = ∑_{b(i)=k} X_i` on the steps `k` of the path are independent,
and `N_k` has law `P(∑_{b(i)=k} m_i)`. -/
theorem iIndepFun_stepCounts (hind : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure (m i)) μ) (b : ι → κ) :
    iIndepFun (fun k ω => stepCounts b (fun i => X i ω) k) μ ∧
      ∀ k, HasLaw (fun ω => stepCounts b (fun i => X i ω) k)
        (poissonMeasure (∑ i with b i = k, m i)) μ := by
  have hk : ∀ k, HasLaw (fun ω => stepCounts b (fun i => X i ω) k)
      (poissonMeasure (∑ i with b i = k, m i)) μ := fun k =>
    hasLaw_finsetSum_poisson hind hX _
  have := hind.isProbabilityMeasure
  exact ⟨(iIndepFun_iff_hasLaw_pi_pi hk).2 (stepCounts_hasLaw hind hX b), hk⟩

/-- **Both paths see Poisson counts on their own steps** (Giles 2015, §8, p. 56, and §5.6, p. 44,
Figure 5.9).  The counts of a Poisson process of rate `λ` on the sub-intervals of the union grid,
of lengths `h_i`, are independent `P(λ h_i)`.  Summed over the steps of the fine grid (`bf`) and of
the coarse grid (`bc`), they give the fine path independent counts `P(λ H^f_k)` and the coarse path
independent counts `P(λ H^c_k)`, where `H^f_k = ∑_{bf(i)=k} h_i` and `H^c_k = ∑_{bc(i)=k} h_i` are
the lengths of their steps: the laws of the counts simulated on each grid alone.  The two paths
are coupled by being functions of the same counts `X`; the statement gives each path's own law,
not their joint law. -/
theorem unionGrid_hasLaw {κf κc : Type*} [Fintype κf] [Fintype κc] [DecidableEq κf]
    [DecidableEq κc] {lam : ℝ≥0} {h : ι → ℝ≥0} (hind : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure (lam * h i)) μ) (bf : ι → κf) (bc : ι → κc) :
    HasLaw (fun ω => stepCounts bf fun i => X i ω)
        (Measure.pi fun k => poissonMeasure (lam * ∑ i with bf i = k, h i)) μ ∧
      HasLaw (fun ω => stepCounts bc fun i => X i ω)
        (Measure.pi fun k => poissonMeasure (lam * ∑ i with bc i = k, h i)) μ := by
  simp_rw [Finset.mul_sum]
  exact ⟨stepCounts_hasLaw hind hX bf, stepCounts_hasLaw hind hX bc⟩

variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] {ν : Measure Ω'}
  {Z : κ → Ω' → ℕ}

/-- **The path built from the summed counts has the law of the path simulated on its own grid**
(Giles 2015, §8, p. 56, and §5.6, p. 44).  `F` maps the counts on the steps of the path to the path,
or to anything computed from it; `Z_k` are independent counts `P(∑_{b(i)=k} m_i)` simulated
directly on the path's grid.  Then `F(N)`, computed from the counts on the union grid, and `F(Z)`
have the same law. -/
theorem map_comp_stepCounts_eq (hind : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure (m i)) μ) (b : ι → κ) (hZind : iIndepFun Z ν)
    (hZ : ∀ k, HasLaw (Z k) (poissonMeasure (∑ i with b i = k, m i)) ν) (F : (κ → ℕ) → α) :
    μ.map (fun ω => F (stepCounts b fun i => X i ω)) = ν.map (fun ω => F fun k => Z k ω) := by
  have hF : HasLaw F ((Measure.pi fun k => poissonMeasure (∑ i with b i = k, m i)).map F)
      (Measure.pi fun k => poissonMeasure (∑ i with b i = k, m i)) :=
    ⟨Measurable.of_discrete.aemeasurable, rfl⟩
  rw [(hF.fun_comp (stepCounts_hasLaw hind hX b)).map_eq,
    (hF.fun_comp (hZind.hasLaw_pi hZ)).map_eq]

/-- **Every payoff of the path has the same mean on the union grid as on its own grid** (Giles 2015,
§8, p. 56, and §5.6, p. 44).  For every real payoff `F` of the counts on the steps of the path,
`F(N)` is integrable iff `F(Z)` is, and `E[F(N)] = E[F(Z)]`, where `N` are the counts summed from
the union grid and `Z` independent counts `P(∑_{b(i)=k} m_i)` simulated on the path's own grid. -/
theorem integral_comp_stepCounts_eq (hind : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure (m i)) μ) (b : ι → κ) (hZind : iIndepFun Z ν)
    (hZ : ∀ k, HasLaw (Z k) (poissonMeasure (∑ i with b i = k, m i)) ν) (F : (κ → ℕ) → ℝ) :
    (Integrable (fun ω => F (stepCounts b fun i => X i ω)) μ ↔
        Integrable (fun ω => F fun k => Z k ω) ν) ∧
      ∫ ω, F (stepCounts b fun i => X i ω) ∂μ = ∫ ω, F (fun k => Z k ω) ∂ν := by
  have hN := stepCounts_hasLaw hind hX b
  have hZ' := hZind.hasLaw_pi hZ
  have hFm : Measurable F := Measurable.of_discrete
  constructor
  · have e₁ := integrable_map_measure (μ := μ) hFm.aestronglyMeasurable hN.aemeasurable
    have e₂ := integrable_map_measure (μ := ν) hFm.aestronglyMeasurable hZ'.aemeasurable
    rw [hN.map_eq] at e₁
    rw [hZ'.map_eq] at e₂
    exact e₁.symm.trans e₂
  · exact (hN.integral_comp hFm.aestronglyMeasurable).trans
      (hZ'.integral_comp hFm.aestronglyMeasurable).symm

end RandomVariables

/-- **The identity (2.4) for Poisson variates on non-nested grids** (Giles 2015, §2.1, p. 8:
"Provided we maintain the identity `E[P^f_ℓ] = E[P^c_ℓ]` (2.4) so that the expectation on level `ℓ`
is the same for the two approximations"; §8, p. 56: "The non-nested adaptive timestepping approach
described in Section 5.6 for SDEs is equally applicable in this setting").  The level-`ℓ` path has
the steps `k : κ`.  As the coarse path of a level-`(ℓ + 1)` sample it is simulated on the union of
the grids of levels `ℓ + 1` and `ℓ`: sub-intervals `ι₁`, independent counts `X₁ i ~ P(m₁ i)`,
grouped into its steps by `b₁`.  As the fine path of a level-`ℓ` sample it is simulated on the union
of the grids of levels `ℓ` and `ℓ − 1`: sub-intervals `ι₂`, counts `X₂ i ~ P(m₂ i)`, grouped by
`b₂`.  Both union grids cut the same steps, so the summed means agree,
`∑_{b₁(i)=k} m₁ i = ∑_{b₂(i)=k} m₂ i` (for a Poisson process of rate `λ` both are `λ` times the
length of step `k`).  Then for every payoff `F` of the level-`ℓ` path, `P^c_ℓ = F(N¹)` is
integrable iff `P^f_ℓ = F(N²)` is, and `E[P^c_ℓ] = E[P^f_ℓ]`.  The grids are deterministic here;
the adaptive grids of §5.6, which depend on the path, are not covered. -/
theorem unionGrid_2_4 {Ω₁ Ω₂ ι₁ ι₂ κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [Fintype ι₁] [Fintype ι₂] [Fintype κ] [DecidableEq κ]
    {X₁ : ι₁ → Ω₁ → ℕ} {X₂ : ι₂ → Ω₂ → ℕ} {m₁ : ι₁ → ℝ≥0} {m₂ : ι₂ → ℝ≥0}
    (hind₁ : iIndepFun X₁ μ₁) (hX₁ : ∀ i, HasLaw (X₁ i) (poissonMeasure (m₁ i)) μ₁)
    (hind₂ : iIndepFun X₂ μ₂) (hX₂ : ∀ i, HasLaw (X₂ i) (poissonMeasure (m₂ i)) μ₂)
    (b₁ : ι₁ → κ) (b₂ : ι₂ → κ) (hm : ∀ k, ∑ i with b₁ i = k, m₁ i = ∑ i with b₂ i = k, m₂ i)
    (F : (κ → ℕ) → ℝ) :
    (Integrable (fun ω => F (stepCounts b₁ fun i => X₁ i ω)) μ₁ ↔
        Integrable (fun ω => F (stepCounts b₂ fun i => X₂ i ω)) μ₂) ∧
      ∫ ω, F (stepCounts b₁ fun i => X₁ i ω) ∂μ₁ =
        ∫ ω, F (stepCounts b₂ fun i => X₂ i ω) ∂μ₂ := by
  obtain ⟨hind, hlaw⟩ := iIndepFun_stepCounts hind₂ hX₂ b₂
  exact integral_comp_stepCounts_eq hind₁ hX₁ b₁ hind (fun k => (hm k).symm ▸ hlaw k) F

/-! ### Tau-leaping on two non-nested deterministic grids

Giles 2015, §8, p. 55: tau-leaping `x_{n+1} = x_n + P(hλ(x_n))`, where the Poisson mean depends on
the state.  The union grid has the sub-intervals `j = 0, 1, …` of lengths `h j`; a path's grid is
given by its step boundaries `t 0 = 0 < t 1 < …` in union-grid indices, so its step `k` is made of
the sub-intervals `t k ≤ j < t (k + 1)`.  The state of one path on the union grid is a pair
`(x, a)`: its current state `x` and its state `a` at the start of its current step, whose propensity
`λ(a)` is frozen during the step. -/

/-- The tau-leaping chain with the timesteps `H 0, H 1, …` (Giles 2015, §8, p. 55:
"`x_{n+1} = x_n + P(hλ(x_n))`", with a timestep that varies from step to step): its law after `k`
steps from `x₀`. -/
noncomputable def tauChainVar (lam : ℕ → ℝ≥0) (H : ℕ → ℝ≥0) (x₀ : ℕ) : ℕ → Measure ℕ
  | 0 => Measure.dirac x₀
  | k + 1 => (tauChainVar lam H x₀ k).bind (tauStep lam (H k))

/-- With a constant timestep, `tauChainVar` is the tau-leaping chain `tauChain` (Giles 2015, §8). -/
lemma tauChainVar_const (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ k, tauChainVar lam (fun _ => h) x₀ k = tauChain lam h x₀ k
  | 0 => rfl
  | k + 1 => by rw [tauChainVar, tauChain, tauChainVar_const lam h x₀ k]

/-- `tauChainVar` after `K` steps depends only on the first `K` timesteps (Giles 2015, §8). -/
lemma tauChainVar_congr (lam : ℕ → ℝ≥0) {H H' : ℕ → ℝ≥0} (x₀ : ℕ) :
    ∀ K, (∀ k < K, H k = H' k) → tauChainVar lam H x₀ K = tauChainVar lam H' x₀ K
  | 0, _ => rfl
  | K + 1, hH => by
    rw [tauChainVar, tauChainVar, tauChainVar_congr lam x₀ K fun k hk => hH k (by omega),
      hH K (by omega)]

/-- The length `∑_{t k ≤ j < t (k+1)} h j` of step `k` of the grid with the boundaries `t` on the
union grid with the sub-interval lengths `h` (Giles 2015, §5.6, Figure 5.9). -/
def gridStepLength (h : ℕ → ℝ≥0) (t : ℕ → ℕ) (k : ℕ) : ℝ≥0 := ∑ j ∈ Ico (t k) (t (k + 1)), h j

/-- Whether sub-interval `j` of the union grid is the last one of a step of the grid with the
boundaries `t` (Giles 2015, §5.6, Algorithm 3: "if `t = t^c` then update coarse path …"). -/
noncomputable def gridStepEnd (t : ℕ → ℕ) (j : ℕ) : Bool := by
  classical exact decide (∃ k, t (k + 1) = j + 1)

/-- Sub-interval `j` ends a step iff `j + 1` is one of the step boundaries `t 1, t 2, …`. -/
lemma gridStepEnd_eq_true_iff (t : ℕ → ℕ) (j : ℕ) :
    gridStepEnd t j = true ↔ ∃ k, t (k + 1) = j + 1 := by
  classical
  simp [gridStepEnd]

/-- One path over one sub-interval with count `i`: the state `(x, a)` becomes `(x + i, a)`, or
`(x + i, x + i)` if the sub-interval ends a step of the path (Giles 2015, §5.6, Algorithm 3). -/
def pathAdvance (e : Bool) (p : ℕ × ℕ) (i : ℕ) : ℕ × ℕ :=
  (p.1 + i, if e then p.1 + i else p.2)

/-- The law of one path after one sub-interval of length `h`: the count is `P(hλ(a))`, with the
propensity frozen at the start `a` of the current step (Giles 2015, §8, p. 55). -/
noncomputable def pathSubStep (lam : ℕ → ℝ≥0) (h : ℝ≥0) (e : Bool) (p : ℕ × ℕ) :
    Measure (ℕ × ℕ) :=
  (poissonMeasure (h * lam p.2)).map (pathAdvance e p)

/-- **The coupled step on one sub-interval of the union grid** (Giles 2015, §8, p. 56: "Poisson
variates for each time interval", coupled as on p. 55 by "`P₁ = P(h min(λ(x_n), λ(x^c_n)))`,
`P₂ = P(h|λ(x_n) − λ(x^c_n)|)`, and then using `P₁` as the Poisson variate for the path with the
smaller rate, and `P₁ + P₂` for the path with the larger rate").  The state `((x, a), (y, c))`
holds the fine and the coarse path, each with the start of its current step; `ef`, `ec` say
whether the sub-interval ends a fine, a coarse step.  (For non-nested grids the paper does not spell
out the coupling on each sub-interval; the laws of the two paths proved below do not depend
on it.) -/
noncomputable def unionStep (lam : ℕ → ℝ≥0) (h : ℝ≥0) (ef ec : Bool)
    (s : (ℕ × ℕ) × (ℕ × ℕ)) : Measure ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (coupledIncr (h * lam s.1.2) (h * lam s.2.2)).map fun ij =>
    (pathAdvance ef s.1 ij.1, pathAdvance ec s.2 ij.2)

/-- **The coupled simulation on the union of two grids** (Giles 2015, §8, p. 56, and §5.6, p. 44,
Figure 5.9 and Algorithm 3): the law of the state after the first `n` sub-intervals of the union
grid (lengths `h`), for the fine grid with the boundaries `tf` and the coarse grid with the
boundaries `tc`, both paths started at `x₀`. -/
noncomputable def unionChain (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) (tf tc : ℕ → ℕ) (x₀ : ℕ) :
    ℕ → Measure ((ℕ × ℕ) × (ℕ × ℕ))
  | 0 => Measure.dirac ((x₀, x₀), (x₀, x₀))
  | n + 1 => (unionChain lam h tf tc x₀ n).bind
      (unionStep lam (h n) (gridStepEnd tf n) (gridStepEnd tc n))

/-- One path alone on the union grid (Giles 2015, §8 and §5.6): the law of its state `(x, a)`
after the first `n` sub-intervals. -/
noncomputable def pathChain (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) (t : ℕ → ℕ) (x₀ : ℕ) :
    ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac (x₀, x₀)
  | n + 1 => (pathChain lam h t x₀ n).bind (pathSubStep lam (h n) (gridStepEnd t n))

/-- One path over the sub-intervals `n, …, n + r − 1`, started from the state `p`. -/
noncomputable def pathRun (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) (t : ℕ → ℕ) (n : ℕ) :
    ℕ → ℕ × ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac
  | r + 1 => fun p =>
      (pathRun lam h t n r p).bind (pathSubStep lam (h (n + r)) (gridStepEnd t (n + r)))

/-- The fine component of the coupled step is the fine path's own step: the coupling gives it a
`P(hλ(a))` count (`coupledIncr_fst`; Giles 2015, §8, p. 55). -/
lemma unionStep_fst (lam : ℕ → ℝ≥0) (h : ℝ≥0) (ef ec : Bool) (s : (ℕ × ℕ) × (ℕ × ℕ)) :
    (unionStep lam h ef ec s).map Prod.fst = pathSubStep lam h ef s.1 := by
  rw [unionStep, Measure.map_map measurable_fst Measurable.of_discrete, pathSubStep,
    ← coupledIncr_fst (h * lam s.1.2) (h * lam s.2.2),
    Measure.map_map Measurable.of_discrete measurable_fst]
  rfl

/-- The coarse component of the coupled step is the coarse path's own step: the coupling gives it
a `P(hλ(c))` count (`coupledIncr_snd`; Giles 2015, §8, p. 55). -/
lemma unionStep_snd (lam : ℕ → ℝ≥0) (h : ℝ≥0) (ef ec : Bool) (s : (ℕ × ℕ) × (ℕ × ℕ)) :
    (unionStep lam h ef ec s).map Prod.snd = pathSubStep lam h ec s.2 := by
  rw [unionStep, Measure.map_map measurable_snd Measurable.of_discrete, pathSubStep,
    ← coupledIncr_snd (h * lam s.1.2) (h * lam s.2.2),
    Measure.map_map Measurable.of_discrete measurable_snd]
  rfl

/-- The fine path of the coupled simulation is the fine path alone (Giles 2015, §8): its marginal
does not depend on the coarse path, since the coupling gives it `P(hλ(a))` counts. -/
lemma unionChain_fst (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) (tf tc : ℕ → ℕ) (x₀ : ℕ) :
    ∀ n, (unionChain lam h tf tc x₀ n).map Prod.fst = pathChain lam h tf x₀ n
  | 0 => Measure.map_dirac' measurable_fst _
  | n + 1 => by
      rw [unionChain, map_bind_of_discrete _ _ measurable_fst]
      simp_rw [unionStep_fst]
      rw [← bind_map_of_discrete (unionChain lam h tf tc x₀ n) Prod.fst,
        unionChain_fst lam h tf tc x₀ n]
      rfl

/-- The coarse path of the coupled simulation is the coarse path alone (Giles 2015, §8). -/
lemma unionChain_snd (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) (tf tc : ℕ → ℕ) (x₀ : ℕ) :
    ∀ n, (unionChain lam h tf tc x₀ n).map Prod.snd = pathChain lam h tc x₀ n
  | 0 => Measure.map_dirac' measurable_snd _
  | n + 1 => by
      rw [unionChain, map_bind_of_discrete _ _ measurable_snd]
      simp_rw [unionStep_snd]
      rw [← bind_map_of_discrete (unionChain lam h tf tc x₀ n) Prod.snd,
        unionChain_snd lam h tf tc x₀ n]
      rfl

/-- Running a path for `n + r` sub-intervals is running it for `n`, then for `r` more. -/
lemma pathChain_add (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) (t : ℕ → ℕ) (x₀ n : ℕ) :
    ∀ r, pathChain lam h t x₀ (n + r) = (pathChain lam h t x₀ n).bind (pathRun lam h t n r)
  | 0 => Measure.bind_dirac.symm
  | r + 1 => by
      rw [← add_assoc, pathChain, pathChain_add lam h t x₀ n r,
        Measure.bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
      rfl

/-- Adding an independent variate inside a function: `μ.bind (i ↦ ν.map (i' ↦ g(i + i')))` is the
image of the convolution `μ ∗ ν` under `g`. -/
lemma bind_map_comp_add {β : Type*} [MeasurableSpace β] (μ ν : Measure ℕ) [SFinite ν]
    (g : ℕ → β) : (μ.bind fun i => ν.map fun i' => g (i + i')) = (μ ∗ ν).map g := by
  have e1 : ∀ i, (ν.map fun i' => g (i + i')) = (ν.map fun k => 0 + i + k).map g := fun i => by
    rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    congr 1
    funext k
    simp
  simp_rw [e1]
  rw [← map_bind_of_discrete _ _ Measurable.of_discrete, bind_map_add_eq_conv,
    Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  congr 1
  funext n
  simp

/-- Advancing by `i` within a step (the step does not end), then by `i'`, is advancing by
`i + i'`. -/
lemma pathAdvance_pathAdvance_false (e : Bool) (x a i i' : ℕ) :
    pathAdvance e (pathAdvance false (x, a) i) i' = pathAdvance e (x, a) (i + i') := by
  cases e <;> simp [pathAdvance, add_assoc]

/-- **Within one step the counts add up** (Giles 2015, §8, p. 55: "the sum of two independent
Poisson variates `P(t₁)`, `P(t₂)` is equivalent in distribution to `P(t₁ + t₂)`"): if none of the
sub-intervals `n, …, n + r − 1` ends a step, then over the sub-intervals `n, …, n + r` the path
from `(x, a)` receives one count `P((h_n + ⋯ + h_{n+r}) λ(a))`. -/
lemma pathRun_succ_eq (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) (t : ℕ → ℕ) (n x a : ℕ) :
    ∀ r, (∀ r' < r, gridStepEnd t (n + r') = false) →
      pathRun lam h t n (r + 1) (x, a) =
        (poissonMeasure ((∑ r' ∈ range (r + 1), h (n + r')) * lam a)).map
          (pathAdvance (gridStepEnd t (n + r)) (x, a))
  | 0, _ => by
      simp only [pathRun, zero_add, add_zero, Finset.sum_range_one]
      rw [Measure.dirac_bind Measurable.of_discrete, pathSubStep]
  | r + 1, hr => by
      have ih := pathRun_succ_eq lam h t n x a r fun r' hr' => hr r' (by omega)
      rw [hr r (by omega)] at ih
      rw [pathRun]
      dsimp only
      rw [ih, bind_map_of_discrete]
      have e2 : ∀ i, pathSubStep lam (h (n + (r + 1))) (gridStepEnd t (n + (r + 1)))
          (pathAdvance false (x, a) i) =
          (poissonMeasure (h (n + (r + 1)) * lam a)).map fun i' =>
            pathAdvance (gridStepEnd t (n + (r + 1))) (x, a) (i + i') := fun i => by
        rw [pathSubStep]
        congr 1
        funext i'
        exact pathAdvance_pathAdvance_false _ x a i i'
      simp_rw [e2]
      rw [bind_map_comp_add, poissonMeasure_conv_poissonMeasure, Finset.sum_range_succ _ (r + 1),
        add_mul]

/-- **A path on the union grid, at the ends of its steps, is tau-leaping on its own grid** (Giles
2015, §8, p. 55, and §5.6): at the end of its `k`-th step (union index `t k`) the path's state is
`(x, x)` with `x` distributed as `k` tau-leaping steps with the step lengths
`gridStepLength h t`. -/
lemma pathChain_boundary (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) {t : ℕ → ℕ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (x₀ : ℕ) :
    ∀ k, pathChain lam h t x₀ (t k) =
      (tauChainVar lam (gridStepLength h t) x₀ k).map fun x => (x, x)
  | 0 => by
      rw [ht0, pathChain, tauChainVar, Measure.map_dirac' Measurable.of_discrete]
  | k + 1 => by
      obtain ⟨r, hr⟩ : ∃ r, t (k + 1) = t k + (r + 1) :=
        ⟨t (k + 1) - t k - 1, by have := ht (Nat.lt_add_one k); omega⟩
      -- no sub-interval strictly inside step `k` ends a step, the last one does
      have hflags : ∀ r' < r, gridStepEnd t (t k + r') = false := by
        intro r' hr'
        rw [← Bool.not_eq_true, gridStepEnd_eq_true_iff]
        rintro ⟨k', hk'⟩
        have h1 : t k < t (k' + 1) := by omega
        have h2 : t (k' + 1) < t (k + 1) := by omega
        rw [ht.lt_iff_lt] at h1 h2
        omega
      have hlast : gridStepEnd t (t k + r) = true :=
        (gridStepEnd_eq_true_iff t _).2 ⟨k, by omega⟩
      have hlen : ∑ r' ∈ range (r + 1), h (t k + r') = gridStepLength h t k := by
        rw [gridStepLength, hr, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      rw [hr, pathChain_add, pathChain_boundary lam h ht ht0 x₀ k, bind_map_of_discrete]
      simp_rw [pathRun_succ_eq lam h t (t k) _ _ r hflags, hlast, hlen]
      rw [tauChainVar, map_bind_of_discrete _ _ Measurable.of_discrete]
      congr 1
      funext x
      rw [tauStep, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
      rfl

/-- **The fine path of the non-nested coupled simulation is tau-leaping on the fine grid** (Giles
2015, §8, p. 56: "The non-nested adaptive timestepping approach described in Section 5.6 for SDEs
is equally applicable in this setting … the construction is exactly the same as illustrated in
Figure 5.9, but with Poisson variates for each time interval instead of Brownian increments", with
the tau-leaping "`x_{n+1} = x_n + P(hλ(x_n))`" of p. 55).  For any union grid (lengths `h`), any
fine grid with the boundaries `tf 0 = 0 < tf 1 < …` and any coarse grid `tc` (not necessarily
nested), at the end of its `k`-th step (union index `tf k`) the fine state has the law of `k`
tau-leaping steps with the fine step lengths `H^f_n = ∑_{tf n ≤ j < tf (n+1)} h j`.  The grids are
deterministic here; the adaptive grids of §5.6, which depend on the path, are not covered. -/
theorem unionChain_fine (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) {tf : ℕ → ℕ} (tc : ℕ → ℕ)
    (htf : StrictMono tf) (htf0 : tf 0 = 0) (x₀ k : ℕ) :
    (unionChain lam h tf tc x₀ (tf k)).map (fun s => s.1.1) =
      tauChainVar lam (gridStepLength h tf) x₀ k := by
  rw [show (fun s : (ℕ × ℕ) × (ℕ × ℕ) => s.1.1) = Prod.fst ∘ Prod.fst from rfl,
    ← Measure.map_map measurable_fst measurable_fst, unionChain_fst,
    pathChain_boundary lam h htf htf0, Measure.map_map measurable_fst Measurable.of_discrete]
  exact Measure.map_id

/-- **The coarse path of the non-nested coupled simulation is tau-leaping on the coarse grid**
(Giles 2015, §8, p. 56, as `unionChain_fine`).  At the end of its `k`-th step (union index `tc k`)
the coarse state has the law of `k` tau-leaping steps with the coarse step lengths
`H^c_n = ∑_{tc n ≤ j < tc (n+1)} h j`, whatever the fine grid `tf`. -/
theorem unionChain_coarse (lam : ℕ → ℝ≥0) (h : ℕ → ℝ≥0) (tf : ℕ → ℕ) {tc : ℕ → ℕ}
    (htc : StrictMono tc) (htc0 : tc 0 = 0) (x₀ k : ℕ) :
    (unionChain lam h tf tc x₀ (tc k)).map (fun s => s.2.1) =
      tauChainVar lam (gridStepLength h tc) x₀ k := by
  rw [show (fun s : (ℕ × ℕ) × (ℕ × ℕ) => s.2.1) = Prod.fst ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_fst measurable_snd, unionChain_snd,
    pathChain_boundary lam h htc htc0, Measure.map_map measurable_fst Measurable.of_discrete]
  exact Measure.map_id

/-- **The nested case** (Giles 2015, §8, p. 55: "the coarse path, with double the timestep, is
given by `x^c_{n+2} = x^c_n + P(2hλ(x^c_n))`").  With the uniform union grid `h_j = h`, the fine
grid equal to it (`tf k = k`) and the coarse grid made of pairs of sub-intervals (`tc k = 2k`), the
fine path after `k` steps is the tau-leaping chain with step `h`, and the coarse path after `k`
steps the chain with step `2h` — the laws of `coupledChain_fst` and `coupledChain_snd`. -/
theorem unionChain_nested (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ k : ℕ) :
    (unionChain lam (fun _ => h) id (2 * ·) x₀ k).map (fun s => s.1.1) = tauChain lam h x₀ k ∧
      (unionChain lam (fun _ => h) id (2 * ·) x₀ (2 * k)).map (fun s => s.2.1) =
        tauChain lam (2 * h) x₀ k := by
  have hf : gridStepLength (fun _ => h) id = fun _ => h := by
    funext n
    simp [gridStepLength]
  have hc : gridStepLength (fun _ => h) (2 * ·) = fun _ => 2 * h := by
    funext n
    simp [gridStepLength, mul_add]
  have hfine := unionChain_fine lam (fun _ => h) (2 * ·) strictMono_id rfl x₀ k
  have hcoarse :=
    unionChain_coarse lam (fun _ => h) id (strictMono_mul_left_of_pos two_pos) rfl x₀ k
  rw [hf, tauChainVar_const] at hfine
  rw [hc, tauChainVar_const] at hcoarse
  exact ⟨hfine, hcoarse⟩

/-- **(2.4) for tau-leaping on non-nested grids** (Giles 2015, §2.1, p. 8: "Provided we maintain
the identity `E[P^f_ℓ] = E[P^c_ℓ]` (2.4) so that the expectation on level `ℓ` is the same for the
two approximations"; §8, p. 56: "The non-nested adaptive timestepping approach described in Section
5.6 for SDEs is equally applicable in this setting").  The level-`ℓ` path is simulated as the coarse
path of a level-`(ℓ + 1)` sample, on a union grid `h₁` where its steps have the boundaries `tc₁`
(the fine grid `tf₁` of level `ℓ + 1` is arbitrary), and as the fine path of a level-`ℓ` sample, on
a union grid `h₂` where its steps have the boundaries `tf₂` (the coarse grid `tc₂` of level `ℓ − 1`
is arbitrary).  If both union grids cut the first `K` level-`ℓ` steps into sub-intervals of the
same total lengths, the lengths of those steps, then after `K` steps the two level-`ℓ` states have
the same law; so every payoff `Φ` of the terminal state has the same mean,
`E[P^c_ℓ] = E[P^f_ℓ]`.  The grids are deterministic here; the adaptive grids of §5.6, which depend
on the path, are not covered. -/
theorem unionChain_2_4 (lam : ℕ → ℝ≥0) {h₁ h₂ : ℕ → ℝ≥0} (tf₁ : ℕ → ℕ) {tc₁ tf₂ : ℕ → ℕ}
    (tc₂ : ℕ → ℕ) (hc₁ : StrictMono tc₁) (hc₁0 : tc₁ 0 = 0) (hf₂ : StrictMono tf₂)
    (hf₂0 : tf₂ 0 = 0) (x₀ K : ℕ)
    (hH : ∀ k < K, gridStepLength h₁ tc₁ k = gridStepLength h₂ tf₂ k) :
    (unionChain lam h₁ tf₁ tc₁ x₀ (tc₁ K)).map (fun s => s.2.1) =
        (unionChain lam h₂ tf₂ tc₂ x₀ (tf₂ K)).map (fun s => s.1.1) ∧
      ∀ Φ : ℕ → ℝ, ∫ s, Φ s.2.1 ∂(unionChain lam h₁ tf₁ tc₁ x₀ (tc₁ K)) =
        ∫ s, Φ s.1.1 ∂(unionChain lam h₂ tf₂ tc₂ x₀ (tf₂ K)) := by
  have hlaw : (unionChain lam h₁ tf₁ tc₁ x₀ (tc₁ K)).map (fun s => s.2.1) =
      (unionChain lam h₂ tf₂ tc₂ x₀ (tf₂ K)).map (fun s => s.1.1) := by
    rw [unionChain_coarse lam h₁ tf₁ hc₁ hc₁0, unionChain_fine lam h₂ tc₂ hf₂ hf₂0,
      tauChainVar_congr lam x₀ K hH]
  refine ⟨hlaw, fun Φ => ?_⟩
  rw [← integral_map (Measurable.of_discrete (f := fun s : (ℕ × ℕ) × (ℕ × ℕ) => s.2.1)).aemeasurable
      (Measurable.of_discrete (f := Φ)).aestronglyMeasurable, hlaw,
    integral_map (Measurable.of_discrete (f := fun s : (ℕ × ℕ) × (ℕ × ℕ) => s.1.1)).aemeasurable
      (Measurable.of_discrete (f := Φ)).aestronglyMeasurable]

/-! ### Variable precision arithmetic (Giles 2015, §10.2)

This section is independent of the rest of the file. -/

/-- **Rounded fine increments do not give the rounded coarse increment** (Giles 2015, §10.2, p. 62:
Brugger et al. "use full precision in the generation of the random numbers for the Brownian
increments … This ensures that the Brownian increments computed for the coarser path `ℓ−1` by
summing the increments of the finer path `ℓ`, are consistent with the increments which would be
generated on level `ℓ−1` when it is the finer of the two levels. This would not be the case if the
increments on level `ℓ` were generated with `B_ℓ` bits of accuracy, then summed to give increments
for level `ℓ−1`, regardless of whether the truncation to the lower accuracy `B_{ℓ−1}` took place
before or after the summation.").  Fixed-point rounding `roundFixed e d` (Haas–Giles 2025, §4.1)
with `B_ℓ = B + 1` and `B_{ℓ−1} = B` bits; `q = 2^{e−B−1}` is the fine resolution.  For
full-precision fine increments `x, y` with `q/2 ≤ x`, `−q/2 ≤ y` and `x + y < q` (a region with
non-empty interior, e.g. around `x = 0.52 q`, `y = 0.4 q`), the level-`(ℓ−1)` increment generated
from the full-precision sum is `round_B(x + y) = 0`, whereas from the rounded fine increments
`x̃ = round_{B+1}(x)`, `ỹ = round_{B+1}(y)` it is `x̃ + ỹ = q` (no truncation),
`round_B(x̃ + ỹ) = 2q` (truncation after the summation) and `round_B(x̃) + round_B(ỹ) = 2q`
(truncation before the summation).

This is the inconsistency the paper describes: the level-`(ℓ−1)` path is not the same function of
the Brownian increments in its two roles, which the paper's Brownian Bridge construction restores.
The statement is pathwise; that the resulting laws differ, so that (2.4) fails for some payoff, is
not proved here.  (The rounded sum `x̃ + ỹ = q` lies halfway between two `B`-bit numbers, a tie
that `round` breaks upwards; if ties were broken downwards, the fine increments with the same `x̃`,
`ỹ` and `q < x + y` would show the same inconsistency.) -/
theorem roundFixed_sum_inconsistent_general (e : ℤ) (B : ℕ) {x y : ℝ}
    (hx : (2 : ℝ) ^ (e - B - 2) ≤ x) (hy : -(2 : ℝ) ^ (e - B - 2) ≤ y)
    (hxy : x + y < (2 : ℝ) ^ (e - B - 1)) :
    roundFixed e B (x + y) = 0 ∧
      roundFixed e (B + 1) x + roundFixed e (B + 1) y = (2 : ℝ) ^ (e - B - 1) ∧
      roundFixed e B (roundFixed e (B + 1) x + roundFixed e (B + 1) y) = (2 : ℝ) ^ (e - B) ∧
      roundFixed e B (roundFixed e (B + 1) x) + roundFixed e B (roundFixed e (B + 1) y) =
        (2 : ℝ) ^ (e - B) := by
  set q := (2 : ℝ) ^ (e - B - 1) with hq_def
  have hq : 0 < q := zpow_pos two_pos _
  have h2 : (2 : ℝ) ^ (e - B - 2) = q / 2 := by
    rw [hq_def, show e - B - 2 = (e - B - 1) - 1 by ring, zpow_sub₀ two_ne_zero, zpow_one]
  have hB : (2 : ℝ) ^ (e - (B : ℤ)) = 2 * q := by
    rw [hq_def, ← zpow_one_add₀ two_ne_zero]
    congr 1
    ring
  have hB1 : (2 : ℝ) ^ (e - ((B + 1 : ℕ) : ℤ)) = q := by
    rw [hq_def]
    congr 1
    push_cast
    ring
  rw [h2] at hx hy
  -- the fine roundings: `x̃ = q`, `ỹ = 0`
  have rx : roundFixed e (B + 1) x = q := by
    have hr : round (x / q) = 1 := by
      rw [round_eq_iff]
      constructor
      · rw [le_div_iff₀ hq]
        push_cast
        linarith
      · rw [div_lt_iff₀ hq]
        push_cast
        linarith
    rw [roundFixed, hB1, hr]
    simp
  have ry : roundFixed e (B + 1) y = 0 := by
    have hr : round (y / q) = 0 := by
      rw [round_eq_iff]
      constructor
      · rw [le_div_iff₀ hq]
        push_cast
        linarith
      · rw [div_lt_iff₀ hq]
        push_cast
        linarith
    rw [roundFixed, hB1, hr]
    simp
  -- the coarse roundings: `round_B(x + y) = 0`, `round_B(q) = 2q`, `round_B(0) = 0`
  have rxy : roundFixed e B (x + y) = 0 := by
    have hr : round ((x + y) / (2 * q)) = 0 := by
      rw [round_eq_iff]
      constructor
      · rw [le_div_iff₀ (by positivity)]
        push_cast
        linarith
      · rw [div_lt_iff₀ (by positivity)]
        push_cast
        linarith
    rw [roundFixed, hB, hr]
    simp
  have rq : roundFixed e B q = 2 * q := by
    have hr : round (q / (2 * q)) = 1 := by
      rw [show q / (2 * q) = 2⁻¹ by field_simp, round_two_inv]
    rw [roundFixed, hB, hr]
    simp
  have r0 : roundFixed e B 0 = 0 := by
    simp [roundFixed]
  refine ⟨rxy, ?_, ?_, ?_⟩
  · rw [rx, ry, add_zero]
  · rw [rx, ry, add_zero, rq, hB]
  · rw [rx, ry, rq, r0, add_zero, hB]

end MLMC
