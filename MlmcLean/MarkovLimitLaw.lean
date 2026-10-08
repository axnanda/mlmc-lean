import MlmcLean.MarkovLimit
import MlmcLean.Randomised
import MlmcLean.StandardEstimator
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# The limit law of a contracting Markov chain, and the bias of the levels (Giles 2015, §10.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §10.1 "Markov
chains and limiting distributions" (pp. 60–61, Figure 10.12), after Glynn and Rhee (2014):
"Under these conditions, it is known that the distribution of `X_n` converges weakly to that of a
limit random variable `X_∞`, and their objective is to estimate expectations of the form
`E[f(X_∞)]`, where `f` is Hölder continuous with exponent `γ`, so that `|f(y) − f(x)| ≤ d(x, y)^γ`.
An example they offer of a chain satisfying the required conditions is `X_0 = 0`,
`X_{n+1} = ½ X_n + ξ_n`, `n ≥ 0` where `P(ξ_n = 0) = P(ξ_n = 1) = ½`.  The invariant distribution
in this case is the uniform distribution on `[0, 2]`.  In the standard MC approach, one would
approximate `E[f(X_∞)]` by estimating `E[f(X_N)]` for some large value of `N`, but this would be a
biased estimate.  Glynn and Rhee (2014) circumvent this problem by making `N` increase with level,
starting a level `ℓ` simulation at `n = −N_ℓ` and terminating it at `n = 0` … Because the decay is
exponential in `N_ℓ − N_{ℓ−1}`, it is appropriate to choose `N_ℓ` to increase linearly with level."

The model is that of `MlmcLean/MarkovChain.lean` and `MlmcLean/MarkovLimit.lean`: `φ_n = φ(·, ξ_n)`
with a jointly measurable `φ : α × E → α` and independent noises `ξ_n` of law `ν`; the contraction
on average `E[d(φ(x, ξ), φ(y, ξ))^p] ≤ ρ d(x, y)^p` for all `x, y` (the paper's condition with
`p = 2γ` and `ρ` the supremum, `0 ≤ ρ < 1`); a finite moment `c = E[d(x₀, φ(x₀, ξ))^p]` of the
first step; a complete separable metric space `α`.  `Z_n = backIter φ n ξ x₀` is the chain started
`n` steps in the past at `x₀` (the level sample of Glynn and Rhee, with `n = N_ℓ`), which has the
law of `X_n` (`map_backIter_eq_map_fwdIter`), and `X_∞` is its almost sure limit
(`ae_tendsto_backIter`, `tendstoInDistribution_fwdIter`).

**The limit law is the invariant law.**
* `map_limit_invariant`: the law `μ_∞` of `X_∞` is invariant, `(μ_∞ ⊗ ν) ∘ φ⁻¹ = μ_∞`: in law
  `X_∞ = φ(X'_∞, ξ_0)` with `X'_∞` the limit driven by `ξ_1, ξ_2, …` (for `p = 2γ`, `γ ≤ 1`).
* `map_limit_eq_of_invariant`: every invariant probability measure `π` is the law of `X_∞`: the
  chain started from `U ~ π` keeps the law `π` (`map_backIter_of_invariant`) and merges in
  probability with the chain started at `x₀` driven by the same noises
  (`tendsto_measure_dist_backIter`; no moment of `π` is needed).
* `invariant_unique`, `existsUnique_invariant`: so "the" invariant distribution is well defined:
  there is exactly one invariant probability measure, and it has a finite `2γ`-th moment.
* `map_limit_halfStep`, `halfStep_limit_uniform`, `halfStep_invariant_unique`: for the example
  `X_{n+1} = X_n/2 + ξ_n` the limit `X_∞` is uniformly distributed on `[0, 2]`, the chain started
  at `0` converges in distribution to `U[0, 2]`, and `U[0, 2]` is its only invariant distribution.

**The bias of the levels, and multilevel Monte Carlo for `E[f(X_∞)]`.**
* `lintegral_dist_limit_le`: `E[d(Z_n, X_∞)^{2γ}] ≤ ρ^n · 4c/(1 − ρ)²`.
* `sq_integral_sub_limit_le`, `abs_integral_sub_limit_le`, `abs_integral_fwdIter_sub_limit_le`:
  for `γ`-Hölder `f`, the bias of the standard approach decays geometrically,
  `|E[f(X_N)] − E[f(X_∞)]| ≤ 2√c/(1 − ρ) · (√ρ)^N`.
* `markov_mlmc_rates`: with `aℓ ≤ N_ℓ` nondecreasing and `ρ^a ≤ 2^{−β}`, conditions (i) and (iii)
  of Theorem 1 hold with `α = β/2` and `β`.
* `markov_randomised_mlmc`: with `N_ℓ` linear, Glynn and Rhee's single-term randomised estimator is
  an unbiased estimator of `E[f(X_∞)]` with finite variance and finite expected cost.
* `markov_mlmc_theorem1`: with `N_ℓ` linear, the standard multilevel estimator of `E[f(X_∞)]` has
  mean square error `< ε²` at cost `O(ε⁻²)` (Theorem 1: the variance rate `β` exceeds the cost
  rate, which is any `δ > 0` since the cost `N_ℓ` grows linearly).

**Deviations from the paper.**  The bias and multilevel results and the invariance of the limit law
use the paper's exponent `p = 2γ`, with the paper's `γ ∈ (0, 1)` relaxed to `0 < γ ≤ 1`; the
identification and the uniqueness of the invariant law, and the example, hold for every `p > 0`.
The variance `V_ℓ` of the correction decays exponentially in the number
`N_{ℓ−1}` of shared steps, not in `N_ℓ − N_{ℓ−1}` as the paper says: for the example with
`x₀ = 0` and `f(x) = x`, `Z_{N_ℓ} − Z_{N_{ℓ−1}} = ∑_{N_{ℓ−1} ≤ k < N_ℓ} 2^{−k} ξ_k` has variance
`(4^{−N_{ℓ−1}} − 4^{−N_ℓ})/3 ≥ 4^{−N_{ℓ−1}}/4` whenever `N_ℓ > N_{ℓ−1}`, which does not become
small when `N_ℓ − N_{ℓ−1}` is large and `N_{ℓ−1}` is not.  With `N_ℓ` linear in `ℓ` both are linear
in `ℓ`, so the paper's conclusion stands.  The multilevel theorems are consequences of §10.1 with
§2.1–2.2 that the paper does not state.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace MLMC

/-! ### The noises: independence, joint law, and stationary starting points -/

section noise

/-- A step that ignores part of its noise: `backIter` of `(x, q) ↦ φ(x, g(q))` is `backIter` of
`φ` driven by the noises `g(q_k)`. -/
lemma backIter_comp_noise {α E E' : Type*} (φ : α → E → α) (g : E' → E) (n : ℕ) (e : ℕ → E')
    (x : α) : backIter (fun y q => φ y (g q)) n e x = backIter φ n (fun k => g (e k)) x := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih => exact congrArg (fun y => φ y (g (e 0))) (ih fun k => e (k + 1))

variable {Ω E β : Type*} [MeasurableSpace Ω] [mE : MeasurableSpace E] [MeasurableSpace β]
  {μ : Measure Ω} {ξ : ℕ → Ω → E}

/-- A random variable determined by the noises `ξ_{m+1}, ξ_{m+2}, …` is independent of `ξ_m`. -/
lemma indepFun_noise (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) {m : ℕ} {W : Ω → β}
    (hW : Measurable[noiseFrom ξ (m + 1)] W) : IndepFun W (ξ m) μ := by
  rw [IndepFun_iff_Indep]
  have h := indep_iSup_of_disjoint (fun i => (hξm i).comap_le) hξ.iIndep
    (S := Set.Ici (m + 1)) (T := {m}) (Set.disjoint_singleton_right.2 (by simp))
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h hW.comap_le) ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ ({m} : Set ℕ)) =>
    MeasurableSpace.comap (ξ i) inferInstance) m (Set.mem_singleton m)

/-- The chain started in the past is a measurable function of the noise sequence. -/
lemma measurable_backIter_pi {α : Type*} [MeasurableSpace α] {φ : α → E → α}
    (hφm : Measurable fun q : α × E => φ q.1 q.2) (n : ℕ) (x : α) :
    Measurable fun e : ℕ → E => backIter φ n e x := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hs : Measurable fun e : ℕ → E => fun k => e (k + 1) :=
      measurable_pi_lambda _ fun k => measurable_pi_apply (k + 1)
    exact hφm.comp ((ih.comp hs).prodMk (measurable_pi_apply 0))

variable {ν : Measure E}

/-- The joint law of independent noises of law `ν` is the product law `ν^ℕ`. -/
lemma map_noise_eq_infinitePi (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = ν) :
    μ.map (fun ω k => ξ k ω) = Measure.infinitePi fun _ : ℕ => ν := by
  have hΞ : Measurable fun ω (k : ℕ) => ξ k ω := measurable_pi_lambda _ hξm
  rw [hξ.map_fun_eq_infinitePi_map₀ hΞ.aemeasurable]
  simp only [hlaw]

/-- The law of the chain started `n` steps in the past depends only on the law `ν` of the
noises. -/
lemma map_backIter_eq_infinitePi {α : Type*} [MeasurableSpace α] {φ : α → E → α}
    (hφm : Measurable fun q : α × E => φ q.1 q.2) (hξ : iIndepFun ξ μ)
    (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν) (n : ℕ) (x₀ : α) :
    μ.map (fun ω => backIter φ n (fun k => ξ k ω) x₀) =
      (Measure.infinitePi fun _ : ℕ => ν).map fun e => backIter φ n e x₀ := by
  have hΞ : Measurable fun ω (k : ℕ) => ξ k ω := measurable_pi_lambda _ hξm
  rw [← map_noise_eq_infinitePi hξ hξm hlaw, Measure.map_map (measurable_backIter_pi hφm n x₀) hΞ]
  rfl

/-- The canonical noise space `(E^ℕ, ν^ℕ)`: its coordinates are independent noises of law `ν`. -/
lemma canonical_noise [IsProbabilityMeasure ν] :
    iIndepFun (fun k (e : ℕ → E) => e k) (Measure.infinitePi fun _ => ν) ∧
      (∀ k, Measurable fun e : ℕ → E => e k) ∧
      ∀ k, (Measure.infinitePi fun _ => ν).map (fun e : ℕ → E => e k) = ν :=
  ⟨iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ e => e) fun _ => measurable_id,
    fun k => measurable_pi_apply k, fun k => Measure.infinitePi_map_eval _ k⟩

variable [IsProbabilityMeasure μ]

/-- **Started from an invariant law, the chain keeps it.**  If `π` is invariant,
`(π ⊗ ν) ∘ φ⁻¹ = π`, and the starting point `U` has law `π` and is determined by the noises
before time `−(m + n)`, then the chain started `n` steps before time `−m` at `U` has law `π`. -/
lemma map_backIter_of_invariant {α : Type*} [MeasurableSpace α] {φ : α → E → α}
    (hφm : Measurable fun q : α × E => φ q.1 q.2) (hξ : iIndepFun ξ μ)
    (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν) {π : Measure α}
    (hπ : (π.prod ν).map (fun q => φ q.1 q.2) = π) (n : ℕ) :
    ∀ (m : ℕ) {U : Ω → α}, Measurable[noiseFrom ξ (m + n)] U → μ.map U = π →
      μ.map (fun ω => backIter φ n (fun k => ξ (k + m) ω) (U ω)) = π := by
  induction n with
  | zero =>
    intro m U _ hUπ
    exact hUπ
  | succ n ih =>
    intro m U hU hUπ
    have hU' : Measurable[noiseFrom ξ (m + 1 + n)] U := by
      rwa [show m + 1 + n = m + (n + 1) by omega]
    have hW := measurable_backIter_shift hφm ξ n (m + 1) hU'
    have hW' := hW.mono (noiseFrom_le hξm _) le_rfl
    have hWπ := ih (m + 1) hU' hUπ
    have hind := indepFun_noise hξ hξm hW
    have hjoint : μ.map (fun ω => (backIter φ n (fun k => ξ (k + (m + 1)) ω) (U ω), ξ m ω)) =
        π.prod ν := by
      rw [← hWπ, ← hlaw m]
      exact (indepFun_iff_map_prod_eq_prod_map_map hW'.aemeasurable
        (hξm m).aemeasurable).1 hind
    have e : (fun ω => backIter φ (n + 1) (fun k => ξ (k + m) ω) (U ω)) =
        (fun q : α × E => φ q.1 q.2) ∘
          fun ω => (backIter φ n (fun k => ξ (k + (m + 1)) ω) (U ω), ξ m ω) :=
      funext fun ω => backIter_succ_shift φ n m (fun k => ξ k ω) (U ω)
    rw [e, ← Measure.map_map hφm (hW'.prodMk (hξm m)), hjoint, hπ]

end noise

/-! ### Laws of almost sure limits -/

section laws

variable {α Ω Ω' : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- **The law of an almost sure limit is determined by the laws of the approximants.**  If
`Z_n → X` almost surely on one probability space, `Z'_n → X'` almost surely on another, and
`Z_n` and `Z'_n` have the same law for every `n`, then `X` and `X'` have the same law (both are
the weak limit of the same sequence of laws). -/
lemma map_eq_map_of_ae_tendsto {Z : ℕ → Ω → α} {Z' : ℕ → Ω' → α} {X : Ω → α} {X' : Ω' → α}
    (hZ : ∀ n, AEMeasurable (Z n) μ) (hZ' : ∀ n, AEMeasurable (Z' n) μ')
    (h : ∀ᵐ ω ∂μ, Tendsto (fun n => Z n ω) atTop (𝓝 (X ω)))
    (h' : ∀ᵐ ω ∂μ', Tendsto (fun n => Z' n ω) atTop (𝓝 (X' ω)))
    (hlaw : ∀ n, μ.map (Z n) = μ'.map (Z' n)) : μ.map X = μ'.map X' := by
  have hX := aemeasurable_of_tendsto_metrizable_ae' hZ h
  have hX' := aemeasurable_of_tendsto_metrizable_ae' hZ' h'
  have h1 : Tendsto (β := ProbabilityMeasure α)
      (fun n => ⟨μ'.map (Z' n), Measure.isProbabilityMeasure_map (hZ' n)⟩) atTop
      (𝓝 ⟨μ.map X, Measure.isProbabilityMeasure_map hX⟩) :=
    (tendstoInDistribution_of_ae_tendsto hZ hX h).tendsto.congr fun n => Subtype.ext (hlaw n)
  have h2 : Tendsto (β := ProbabilityMeasure α)
      (fun n => ⟨μ'.map (Z' n), Measure.isProbabilityMeasure_map (hZ' n)⟩) atTop
      (𝓝 ⟨μ'.map X', Measure.isProbabilityMeasure_map hX'⟩) :=
    (tendstoInDistribution_of_ae_tendsto hZ' hX' h').tendsto
  have h3 : (⟨μ.map X, Measure.isProbabilityMeasure_map hX⟩ : ProbabilityMeasure α) =
      ⟨μ'.map X', Measure.isProbabilityMeasure_map hX'⟩ :=
    tendsto_nhds_unique (X := ProbabilityMeasure α) h1 h2
  exact congrArg Subtype.val h3

omit [MeasurableSpace α] [BorelSpace α] in
/-- `ofReal(d(a_m, b)^p) → ofReal(d(a, b)^p)` when `a_m → a` and `p ≥ 0`. -/
lemma tendsto_ofReal_dist_rpow {a : ℕ → α} {a₀ b : α} (h : Tendsto a atTop (𝓝 a₀)) {p : ℝ}
    (hp : 0 ≤ p) :
    Tendsto (fun m => ENNReal.ofReal (dist (a m) b ^ p)) atTop
      (𝓝 (ENNReal.ofReal (dist a₀ b ^ p))) :=
  ENNReal.tendsto_ofReal ((h.dist tendsto_const_nhds).rpow_const (Or.inr hp))

end laws

/-! ### The rate of convergence to the limit, and the bias of the levels -/

section rate

variable {α E Ω : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [MeasurableSpace E] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ν : Measure E} {φ : α → E → α} {ξ : ℕ → Ω → E}

/-- **The chains started in the past converge to their limit geometrically fast** (Giles 2015,
§10.1, p. 61: "Because of the contraction property, the effect of the initial evolution of the
level `ℓ` path for `n < −N_{ℓ−1}` decays exponentially").  With the hypotheses of
`lintegral_dist_start_le` (the contraction `E[d(φ(x, ξ), φ(y, ξ))^{2γ}] ≤ ρ d(x, y)^{2γ}`,
`0 < γ ≤ 1`, `0 ≤ ρ < 1`, independent noises of law `ν`), if the chains `Z_n` started `n` steps in
the past at `x₀` converge almost surely to `X_∞`, then
`E[d(Z_n, X_∞)^{2γ}] ≤ ρ^n · 4c/(1 − ρ)²` with `c = E[d(x₀, φ(x₀, ξ))^{2γ}]` (Fatou's lemma
applied to `lintegral_dist_levels_le`). -/
theorem lintegral_dist_limit_le (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω)))
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀) (X ω) ^ (2 * γ)) ∂μ ≤
      ENNReal.ofReal ρ ^ n * (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
        ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν) := by
  have hZm : ∀ m, Measurable fun ω => backIter φ m (fun k => ξ k ω) x₀ := fun m =>
    (measurable_backIter_pi hφm m x₀).comp (measurable_pi_lambda _ hξm)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun m => ENNReal.ofReal (dist (backIter φ m (fun k => ξ k ω) x₀)
      (backIter φ n (fun k => ξ k ω) x₀) ^ (2 * γ))) atTop
      (𝓝 (ENNReal.ofReal (dist (X ω) (backIter φ n (fun k => ξ k ω) x₀) ^ (2 * γ)))) :=
    hX.mono fun ω hω => tendsto_ofReal_dist_rpow hω (by linarith)
  calc ∫⁻ ω, ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀) (X ω) ^ (2 * γ)) ∂μ
      = ∫⁻ ω, liminf (fun m => ENNReal.ofReal (dist (backIter φ m (fun k => ξ k ω) x₀)
          (backIter φ n (fun k => ξ k ω) x₀) ^ (2 * γ))) atTop ∂μ := by
        refine lintegral_congr_ae (hlim.mono fun ω hω => ?_)
        dsimp only
        rw [hω.liminf_eq, dist_comm]
    _ ≤ liminf (fun m => ∫⁻ ω, ENNReal.ofReal (dist (backIter φ m (fun k => ξ k ω) x₀)
          (backIter φ n (fun k => ξ k ω) x₀) ^ (2 * γ)) ∂μ) atTop :=
        lintegral_liminf_le fun m => (((hZm m).dist (hZm n)).pow_const _).ennreal_ofReal
    _ ≤ _ := liminf_le_of_frequently_le' ((eventually_ge_atTop n).frequently.mono fun m hm =>
        lintegral_dist_levels_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hm)

omit [IsProbabilityMeasure μ] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] in
/-- `(f(x) − f(y))² ≤ d(x, y)^{2γ}` for `γ`-Hölder `f`. -/
lemma sq_sub_le_of_holder {γ : ℝ} {f : α → ℝ} (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ)
    (x y : α) : (f x - f y) ^ 2 ≤ dist x y ^ (2 * γ) := by
  rw [mul_comm, Real.rpow_mul dist_nonneg, Real.rpow_two, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hf x y) 2

omit [IsProbabilityMeasure μ] [BorelSpace α] [SecondCountableTopology α] in
/-- `E[(f(A) − f(B))²] ≤ M` when `E[d(A, B)^{2γ}] ≤ M < ∞` and `f` is `γ`-Hölder. -/
lemma integral_sq_sub_le {A B : Ω → α} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    {γ : ℝ} {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ)
    {M : ℝ≥0∞} (hM : M ≠ ∞)
    (h : ∫⁻ ω, ENNReal.ofReal (dist (A ω) (B ω) ^ (2 * γ)) ∂μ ≤ M) :
    ∫ ω, (f (A ω) - f (B ω)) ^ 2 ∂μ ≤ M.toReal := by
  have hD : AEMeasurable (fun ω => f (A ω) - f (B ω)) μ :=
    (hfm.comp_aemeasurable hA).sub (hfm.comp_aemeasurable hB)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
    (hD.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_mono hM ((lintegral_mono fun ω =>
    ENNReal.ofReal_le_ofReal (sq_sub_le_of_holder hf (A ω) (B ω))).trans h)

/-- `f ∘ Y` is square integrable when `f` is `γ`-Hölder and `E[d(Y, x₀)^{2γ}] < ∞`. -/
lemma memLp_comp_of_holder {Y : Ω → α} (hY : AEMeasurable Y μ) {γ : ℝ} {f : α → ℝ}
    (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) (x₀ : α)
    (hmom : ∫⁻ ω, ENNReal.ofReal (dist (Y ω) x₀ ^ (2 * γ)) ∂μ ≠ ∞) :
    MemLp (fun ω => f (Y ω)) 2 μ := by
  have hd : AEStronglyMeasurable (fun ω => dist (Y ω) x₀ ^ γ) μ :=
    ((hY.dist aemeasurable_const).pow_const γ).aestronglyMeasurable
  have hdL2 : MemLp (fun ω => dist (Y ω) x₀ ^ γ) 2 μ := by
    rw [memLp_two_iff_integrable_sq hd]
    have heq : (fun ω => (dist (Y ω) x₀ ^ γ) ^ 2) = fun ω => dist (Y ω) x₀ ^ (2 * γ) := by
      funext ω
      rw [mul_comm, Real.rpow_mul dist_nonneg, Real.rpow_two]
    rw [heq]
    refine ⟨((hY.dist aemeasurable_const).pow_const _).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω =>
      Real.rpow_nonneg dist_nonneg _)).2 (lt_top_iff_ne_top.2 hmom)
  have hsub : MemLp (fun ω => f (Y ω) - f x₀) 2 μ := by
    refine hdL2.of_le ((hfm.comp_aemeasurable hY).sub aemeasurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)]
    exact hf (Y ω) x₀
  convert hsub.add (memLp_const (f x₀)) using 1
  funext ω
  simp

/-- The chain started `n` steps in the past has a bounded `2γ`-th moment about `x₀`
(`lintegral_dist_start_le`). -/
lemma lintegral_dist_backIter_start_le (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (dist (backIter φ n (fun k => ξ k ω) x₀) x₀ ^ (2 * γ)) ∂μ ≤
      ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
        ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν := by
  refine le_of_eq_of_le (lintegral_congr fun ω => ?_)
    (lintegral_dist_start_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ n 0)
  simp only [add_zero, dist_comm]

/-- The level approximation `f(Z_n)` is square integrable (`f` is `γ`-Hölder). -/
lemma memLp_level (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) (n : ℕ) :
    MemLp (fun ω => f (backIter φ n (fun k => ξ k ω) x₀)) 2 μ :=
  memLp_comp_of_holder ((measurable_backIter_pi hφm n x₀).comp
    (measurable_pi_lambda _ hξm)).aemeasurable hfm hf x₀
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc)
      (lintegral_dist_backIter_start_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ n))

/-- The limit `f(X_∞)` is square integrable (`f` is `γ`-Hölder). -/
lemma memLp_limit (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω))) :
    MemLp (fun ω => f (X ω)) 2 μ := by
  have hXm : AEMeasurable X μ := aemeasurable_of_tendsto_metrizable_ae' (fun n =>
    ((measurable_backIter_pi hφm n x₀).comp (measurable_pi_lambda _ hξm)).aemeasurable) hX
  have h0 := lintegral_dist_limit_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hX 0
  refine memLp_comp_of_holder hXm hfm hf x₀ (ne_top_of_le_ne_top (ENNReal.mul_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc))
    (le_of_eq_of_le (lintegral_congr fun ω => ?_) h0))
  rw [backIter_zero, dist_comm]

/-- **The bias of the level approximation decays geometrically** (Giles 2015, §10.1, p. 61: "In
the standard MC approach, one would approximate `E[f(X_∞)]` by estimating `E[f(X_N)]` for some
large value of `N`, but this would be a biased estimate").  With the hypotheses of
`lintegral_dist_limit_le`, `c = E[d(x₀, φ(x₀, ξ))^{2γ}] < ∞`, and `f` Hölder continuous with
exponent `γ`, `|f(y) − f(x)| ≤ d(x, y)^γ` (as in the paper), `f(Z_n)` and `f(X_∞)` are square
integrable and the chain `Z_n` started `n` steps in the past at `x₀` has
`(E[f(Z_n)] − E[f(X_∞)])² ≤ 4c/(1 − ρ)² · ρ^n`. -/
theorem sq_integral_sub_limit_le (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω)))
    (n : ℕ) :
    (∫ ω, f (backIter φ n (fun k => ξ k ω) x₀) ∂μ - ∫ ω, f (X ω) ∂μ) ^ 2 ≤
      4 / (1 - ρ) ^ 2 * (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal *
        ρ ^ n := by
  have hZm : ∀ m, Measurable fun ω => backIter φ m (fun k => ξ k ω) x₀ := fun m =>
    (measurable_backIter_pi hφm m x₀).comp (measurable_pi_lambda _ hξm)
  have hXm : AEMeasurable X μ :=
    aemeasurable_of_tendsto_metrizable_ae' (fun m => (hZm m).aemeasurable) hX
  have h4 : 0 ≤ 4 / (1 - ρ) ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  have hB : ∀ m, ENNReal.ofReal ρ ^ m * (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
      ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν) ≠ ∞ := fun m =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc)
  have hlim := lintegral_dist_limit_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hX
  have hLZ := memLp_level hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf n (μ := μ)
  have hLX := memLp_limit hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf hX
  -- `(E[D])² ≤ E[D²]` for `D = f(Z_n) − f(X)`
  have hD : MemLp (fun ω => f (backIter φ n (fun k => ξ k ω) x₀) - f (X ω)) 2 μ := hLZ.sub hLX
  have hvar := variance_nonneg (fun ω => f (backIter φ n (fun k => ξ k ω) x₀) - f (X ω)) μ
  rw [variance_eq_sub hD] at hvar
  rw [← integral_sub (hLZ.integrable one_le_two) (hLX.integrable one_le_two)]
  calc (∫ ω, (f (backIter φ n (fun k => ξ k ω) x₀) - f (X ω)) ∂μ) ^ 2
      ≤ ∫ ω, (f (backIter φ n (fun k => ξ k ω) x₀) - f (X ω)) ^ 2 ∂μ := by
        simp only [Pi.pow_apply] at hvar
        linarith
    _ ≤ (ENNReal.ofReal ρ ^ n * (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
          ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν)).toReal :=
        integral_sq_sub_le (hZm n).aemeasurable hXm hfm hf (hB n) (hlim n)
    _ = 4 / (1 - ρ) ^ 2 * (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal *
          ρ ^ n := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal hρ0, ENNReal.toReal_ofReal h4]
        ring

/-- **The bias of the level approximation decays geometrically** (Giles 2015, §10.1, p. 61: "In
the standard MC approach, one would approximate `E[f(X_∞)]` by estimating `E[f(X_N)]` for some
large value of `N`, but this would be a biased estimate").  With the hypotheses of
`sq_integral_sub_limit_le`, the chain `Z_n` started `n` steps in the past at `x₀` has
`|E[f(Z_n)] − E[f(X_∞)]| ≤ 2√c/(1 − ρ) · (√ρ)^n`, `c = E[d(x₀, φ(x₀, ξ))^{2γ}]`. -/
theorem abs_integral_sub_limit_le (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω)))
    (n : ℕ) :
    |∫ ω, f (backIter φ n (fun k => ξ k ω) x₀) ∂μ - ∫ ω, f (X ω) ∂μ| ≤
      2 / (1 - ρ) * Real.sqrt (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal *
        Real.sqrt ρ ^ n := by
  have h1ρ : 0 < 1 - ρ := by linarith
  refine abs_le_of_sq_le_sq ((sq_integral_sub_limit_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀
    hc hfm hf hX n).trans (le_of_eq ?_)) ?_
  · rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt ENNReal.toReal_nonneg, ← pow_mul, mul_comm n 2,
      pow_mul, Real.sq_sqrt hρ0]
    norm_num
  · exact mul_nonneg (mul_nonneg (div_nonneg zero_le_two h1ρ.le) (Real.sqrt_nonneg _))
      (pow_nonneg (Real.sqrt_nonneg _) _)

/-- **The bias of the standard Monte Carlo approach** (Giles 2015, §10.1, p. 61: "In the standard
MC approach, one would approximate `E[f(X_∞)]` by estimating `E[f(X_N)]` for some large value of
`N`, but this would be a biased estimate").  With the hypotheses of `sq_integral_sub_limit_le`, the
chain `X_0 = x₀`, `X_{n+1} = φ(X_n, ξ_n)` has `|E[f(X_N)] − E[f(X_∞)]| ≤ 2√c/(1 − ρ) · (√ρ)^N`,
`c = E[d(x₀, φ(x₀, ξ))^{2γ}]`: the bias decays geometrically in `N` (`X_N` has the law of the
chain started `N` steps in the past, `map_backIter_eq_map_fwdIter`). -/
theorem abs_integral_fwdIter_sub_limit_le (hφm : Measurable fun q : α × E => φ q.1 q.2)
    {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω)))
    (N : ℕ) :
    |∫ ω, f (fwdIter φ N (fun k => ξ k ω) x₀) ∂μ - ∫ ω, f (X ω) ∂μ| ≤
      2 / (1 - ρ) * Real.sqrt (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal *
        Real.sqrt ρ ^ N := by
  have hZm : Measurable fun ω => backIter φ N (fun k => ξ k ω) x₀ :=
    (measurable_backIter_pi hφm N x₀).comp (measurable_pi_lambda _ hξm)
  have hFm : Measurable fun ω => fwdIter φ N (fun k => ξ k ω) x₀ :=
    (measurable_fwdIter hφm N x₀).comp (measurable_pi_lambda _ hξm)
  have e : ∫ ω, f (fwdIter φ N (fun k => ξ k ω) x₀) ∂μ =
      ∫ ω, f (backIter φ N (fun k => ξ k ω) x₀) ∂μ := by
    rw [← integral_map hFm.aemeasurable hfm.aestronglyMeasurable,
      ← map_backIter_eq_map_fwdIter hφm hξ hξm hlaw N x₀,
      integral_map hZm.aemeasurable hfm.aestronglyMeasurable]
  rw [e]
  exact abs_integral_sub_limit_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf hX N

end rate

/-! ### The limit law is the unique invariant law -/

section invariant

variable {α E Ω : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [MeasurableSpace E] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ν : Measure E} {φ : α → E → α} {ξ : ℕ → Ω → E}

/-- **The limit law is invariant** (Giles 2015, §10.1, p. 61: "Under these conditions, it is
known that the distribution of `X_n` converges weakly to that of a limit random variable `X_∞`";
"The invariant distribution in this case is the uniform distribution on `[0, 2]`").  With the
hypotheses of `tendstoInDistribution_fwdIter` for the paper's exponent `p = 2γ`, `0 < γ ≤ 1`, the
law `μ_∞` of the almost sure limit `X_∞` of the chains started in the past is invariant for the
chain: if `X ~ μ_∞` and `ξ ~ ν` are independent, then `φ(X, ξ) ~ μ_∞`, i.e.
`(μ_∞ ⊗ ν) ∘ φ⁻¹ = μ_∞`.  Indeed `X_∞ = φ(X'_∞, ξ_0)` almost surely, where `X'_∞` is the limit of
the chains driven by `ξ_1, ξ_2, …`, which has the law of `X_∞` and is independent of `ξ_0`. -/
theorem map_limit_invariant [CompleteSpace α] (hφm : Measurable fun q : α × E => φ q.1 q.2)
    {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω))) :
    ((μ.map X).prod ν).map (fun q => φ q.1 q.2) = μ.map X := by
  have hp : 0 < 2 * γ := by linarith
  -- the chains driven by the shifted noises `ξ_1, ξ_2, …`
  have hξ' : iIndepFun (fun k => ξ (k + 1)) μ := hξ.precomp (add_left_injective 1)
  have hξm' : ∀ k, Measurable (ξ (k + 1)) := fun k => hξm (k + 1)
  have hlaw' : ∀ k, μ.map (ξ (k + 1)) = ν := fun k => hlaw (k + 1)
  have hZm : ∀ n, Measurable fun ω => backIter φ n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_backIter_pi hφm n x₀).comp (measurable_pi_lambda _ hξm)
  have hZ'm : ∀ n, Measurable[noiseFrom ξ 1]
      fun ω => backIter φ n (fun k => ξ (k + 1) ω) x₀ := fun n =>
    measurable_backIter_shift hφm ξ n 1 (U := fun _ => x₀) measurable_const
  have hZ'm' : ∀ n, Measurable fun ω => backIter φ n (fun k => ξ (k + 1) ω) x₀ := fun n =>
    (hZ'm n).mono (noiseFrom_le hξm 1) le_rfl
  -- their limit `V`, a function of `ξ_1, ξ_2, …`
  have : Nonempty α := ⟨x₀⟩
  obtain ⟨V, hV_def⟩ : ∃ V : Ω → α,
      V = fun ω => limUnder atTop fun n => backIter φ n (fun k => ξ (k + 1) ω) x₀ := ⟨_, rfl⟩
  have hVm : Measurable[noiseFrom ξ 1] V := by
    rw [hV_def]
    exact (@StronglyMeasurable.limUnder ℕ Ω α (noiseFrom ξ 1) _ _ atTop _
      (fun n ω => backIter φ n (fun k => ξ (k + 1) ω) x₀) _ _
      fun n => (hZ'm n).stronglyMeasurable).measurable
  have hVm' : Measurable V := hVm.mono (noiseFrom_le hξm 1) le_rfl
  have hV : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ (k + 1) ω) x₀) atTop
      (𝓝 (V ω)) := by
    rw [hV_def]
    exact (ae_tendsto_backIter hφm hp hρ0 hρ1 hφ hξ' hξm' hlaw' x₀ hc).mono fun ω h =>
      tendsto_nhds_limUnder h
  -- `V` has the law of `X`
  have hlawV : μ.map V = μ.map X :=
    map_eq_map_of_ae_tendsto (fun n => (hZ'm' n).aemeasurable) (fun n => (hZm n).aemeasurable)
      hV hX fun n => by
        rw [map_backIter_eq_infinitePi hφm hξ' hξm' hlaw' n x₀,
          map_backIter_eq_infinitePi hφm hξ hξm hlaw n x₀]
  -- `X = φ(V, ξ_0)` almost surely
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ≥0∞, B = ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
      ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν := ⟨_, rfl⟩
  have hB : B ≠ ∞ := by
    rw [hB_def]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc
  have hstep : ∀ n, ∫⁻ ω, ENNReal.ofReal (dist (backIter φ (n + 1) (fun k => ξ k ω) x₀)
      (φ (V ω) (ξ 0 ω)) ^ (2 * γ)) ∂μ ≤ ENNReal.ofReal ρ * (ENNReal.ofReal ρ ^ n * B) := by
    intro n
    have h1 := lintegral_dist_backIter_le hφm hφ hξ hξm hlaw 1 0 (hZ'm n) hVm
    have h2 := lintegral_dist_limit_le hφm hφ hξ' hξm' hlaw' hγ0 hγ1 hρ0 hρ1 x₀ hV n
    rw [pow_one] at h1
    rw [hB_def]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)
  have hXW : X =ᵐ[μ] fun ω => φ (V ω) (ξ 0 ω) := by
    have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => ENNReal.ofReal (dist (backIter φ (n + 1)
        (fun k => ξ k ω) x₀) (φ (V ω) (ξ 0 ω)) ^ (2 * γ))) atTop
        (𝓝 (ENNReal.ofReal (dist (X ω) (φ (V ω) (ξ 0 ω)) ^ (2 * γ)))) :=
      hX.mono fun ω hω => tendsto_ofReal_dist_rpow (hω.comp (tendsto_add_atTop_nat 1)) hp.le
    have hr : Tendsto (fun n => ENNReal.ofReal ρ * (ENNReal.ofReal ρ ^ n * B)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ρ)
        (ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
          (ENNReal.ofReal_lt_one.2 hρ1)) (Or.inr hB)) (Or.inr ENNReal.ofReal_ne_top)
      rwa [zero_mul, mul_zero] at h
    have hWm : Measurable fun ω => φ (V ω) (ξ 0 ω) := hφm.comp (hVm'.prodMk (hξm 0))
    have hzero : ∫⁻ ω, ENNReal.ofReal (dist (X ω) (φ (V ω) (ξ 0 ω)) ^ (2 * γ)) ∂μ = 0 := by
      refine le_antisymm ?_ zero_le
      calc ∫⁻ ω, ENNReal.ofReal (dist (X ω) (φ (V ω) (ξ 0 ω)) ^ (2 * γ)) ∂μ
          = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (dist (backIter φ (n + 1)
              (fun k => ξ k ω) x₀) (φ (V ω) (ξ 0 ω)) ^ (2 * γ))) atTop ∂μ :=
            lintegral_congr_ae (hlim.mono fun ω hω => hω.liminf_eq.symm)
        _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (dist (backIter φ (n + 1)
              (fun k => ξ k ω) x₀) (φ (V ω) (ξ 0 ω)) ^ (2 * γ)) ∂μ) atTop :=
            lintegral_liminf_le fun n => (((hZm (n + 1)).dist hWm).pow_const _).ennreal_ofReal
        _ ≤ liminf (fun n => ENNReal.ofReal ρ * (ENNReal.ofReal ρ ^ n * B)) atTop :=
            liminf_le_liminf (Eventually.of_forall hstep)
        _ = 0 := hr.liminf_eq
    have hXm : AEMeasurable X μ :=
      aemeasurable_of_tendsto_metrizable_ae' (fun n => (hZm n).aemeasurable) hX
    have hae := (lintegral_eq_zero_iff' ((hXm.dist hWm.aemeasurable).pow_const _).ennreal_ofReal).1
      hzero
    filter_upwards [hae] with ω hω
    have h1 : dist (X ω) (φ (V ω) (ξ 0 ω)) ^ (2 * γ) ≤ 0 := ENNReal.ofReal_eq_zero.1 hω
    have h2 : dist (X ω) (φ (V ω) (ξ 0 ω)) ^ (2 * γ) = 0 :=
      le_antisymm h1 (Real.rpow_nonneg dist_nonneg _)
    rw [Real.rpow_eq_zero_iff_of_nonneg dist_nonneg] at h2
    exact dist_eq_zero.1 h2.1
  -- `V` is independent of `ξ_0`
  have hjoint : μ.map (fun ω => (V ω, ξ 0 ω)) = (μ.map V).prod ν := by
    rw [← hlaw 0]
    exact (indepFun_iff_map_prod_eq_prod_map_map hVm'.aemeasurable (hξm 0).aemeasurable).1
      (indepFun_noise hξ hξm (m := 0) hVm)
  calc ((μ.map X).prod ν).map (fun q => φ q.1 q.2)
      = (μ.map (fun ω => (V ω, ξ 0 ω))).map (fun q => φ q.1 q.2) := by rw [hjoint, hlawV]
    _ = μ.map (fun ω => φ (V ω) (ξ 0 ω)) := Measure.map_map hφm (hVm'.prodMk (hξm 0))
    _ = μ.map X := (Measure.map_congr hXW).symm

/-- **A chain started at a random point merges in probability with the chain started at `x₀`.**
Let `φ` contract on average, `E[d(φ(x, ξ), φ(y, ξ))^p] ≤ ρ d(x, y)^p` with `p > 0`, `ρ < 1`, and
let the starting points `U_n` have a common law `π` and be determined by the noises before time
`−n`.  Then `P(d(Z_n^{U_n}, Z_n^{x₀}) ≥ ε) → 0` for every `ε > 0`, where `Z_n^{u}` is the chain
started `n` steps in the past at `u`, driven by the same noises.  No moment of `π` is needed:
truncate `U_n` at distance `R` from `x₀`, where the contraction gives
`E[d(Z_n^{U_n^R}, Z_n^{x₀})^p] ≤ ρ^n R^p`, and let `R → ∞`. -/
lemma tendsto_measure_dist_backIter (hφm : Measurable fun q : α × E => φ q.1 q.2) {p ρ : ℝ}
    (hp : 0 < p) (hρ1 : ρ < 1)
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ p) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν) (x₀ : α)
    {π : Measure α} [IsFiniteMeasure π] {U : ℕ → Ω → α}
    (hU : ∀ n, Measurable[noiseFrom ξ (0 + n)] (U n)) (hUπ : ∀ n, μ.map (U n) = π) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ε ≤ dist (backIter φ n (fun k => ξ (k + 0) ω) (U n ω))
      (backIter φ n (fun k => ξ (k + 0) ω) x₀)}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  -- the tail `π(d(·, x₀) > R)` is small for a large `R`
  have hanti : Antitone fun R : ℕ => {y : α | (R : ℝ) < dist y x₀} := by
    intro i j hij y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    exact lt_of_le_of_lt (Nat.cast_le.2 hij) hy
  have hempty : (⋂ R : ℕ, {y : α | (R : ℝ) < dist y x₀}) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
    obtain ⟨R, hR⟩ := exists_nat_ge (dist y x₀)
    have := Set.mem_iInter.1 hy R
    simp only [Set.mem_ofPred_eq] at this
    linarith
  have htail := tendsto_measure_iInter_atTop (μ := π)
    (s := fun R : ℕ => {y : α | (R : ℝ) < dist y x₀}) (fun R =>
    (measurableSet_lt measurable_const (measurable_id.dist measurable_const)).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at htail
  obtain ⟨R, hR⟩ := ENNReal.tendsto_atTop_zero.1 htail (δ / 2) hδ2
  -- the truncated chains merge geometrically fast
  have hεp : ENNReal.ofReal (ε ^ p) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hε p)).ne'
  have hgeo : Tendsto (fun n : ℕ => ENNReal.ofReal ρ ^ n * ENNReal.ofReal ((R : ℝ) ^ p) /
      ENNReal.ofReal (ε ^ p)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.ofReal_lt_one.2 hρ1))
      (Or.inr (ENNReal.ofReal_ne_top (r := (R : ℝ) ^ p))))
      (Or.inr (ENNReal.inv_ne_top.2 hεp))
    simpa only [zero_mul, div_eq_mul_inv] using h
  obtain ⟨n₀, hn₀⟩ := ENNReal.tendsto_atTop_zero.1 hgeo (δ / 2) hδ2
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨V, hV_def⟩ : ∃ V : Ω → α, V = fun ω => if dist (U n ω) x₀ ≤ R then U n ω else x₀ :=
    ⟨_, rfl⟩
  have hVm : Measurable[noiseFrom ξ (0 + n)] V := by
    have hd : Measurable[noiseFrom ξ (0 + n)] fun ω => dist (U n ω) x₀ :=
      measurable_dist.comp ((hU n).prodMk measurable_const)
    have hs : MeasurableSet[noiseFrom ξ (0 + n)] {ω | dist (U n ω) x₀ ≤ R} :=
      measurableSet_Iic.preimage hd
    rw [hV_def]
    exact Measurable.ite hs (hU n) measurable_const
  have hVR : ∀ ω, dist (V ω) x₀ ≤ R := by
    intro ω
    rw [hV_def]
    by_cases h : dist (U n ω) x₀ ≤ R
    · simp only [h, if_true]
    · simp only [h, if_false, dist_self, Nat.cast_nonneg]
  have hZm : ∀ W : Ω → α, Measurable[noiseFrom ξ (0 + n)] W →
      Measurable fun ω => backIter φ n (fun k => ξ (k + 0) ω) (W ω) := fun W hW =>
    (measurable_backIter_shift hφm ξ n 0 hW).mono (noiseFrom_le hξm _) le_rfl
  have hcontr := lintegral_dist_backIter_le hφm hφ hξ hξm hlaw n 0 hVm (V := fun _ => x₀)
    measurable_const
  have hVp : ∫⁻ ω, ENNReal.ofReal (dist (V ω) x₀ ^ p) ∂μ ≤ ENNReal.ofReal ((R : ℝ) ^ p) := by
    calc ∫⁻ ω, ENNReal.ofReal (dist (V ω) x₀ ^ p) ∂μ ≤ ∫⁻ _, ENNReal.ofReal ((R : ℝ) ^ p) ∂μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow dist_nonneg (hVR ω) hp.le)
      _ = ENNReal.ofReal ((R : ℝ) ^ p) := by rw [lintegral_const, measure_univ, mul_one]
  -- Markov's inequality for the truncated chains
  have hmarkov : μ {ω | ε ≤ dist (backIter φ n (fun k => ξ (k + 0) ω) (V ω))
      (backIter φ n (fun k => ξ (k + 0) ω) x₀)} ≤ δ / 2 := by
    refine (measure_mono fun ω (hω : ε ≤ _) => ?_).trans ((meas_ge_le_lintegral_div
      ((((hZm V hVm).dist (hZm _ measurable_const)).pow_const p).ennreal_ofReal.aemeasurable)
      hεp ENNReal.ofReal_ne_top).trans ((ENNReal.div_le_div_right (hcontr.trans
        (mul_le_mul_of_nonneg_left hVp zero_le)) _).trans (hn₀ n hn)))
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hε.le hω hp.le)
  -- `Z_n^{U_n} = Z_n^{V}` unless `d(U_n, x₀) > R`
  have hsub : {ω | ε ≤ dist (backIter φ n (fun k => ξ (k + 0) ω) (U n ω))
      (backIter φ n (fun k => ξ (k + 0) ω) x₀)} ⊆ {ω | (R : ℝ) < dist (U n ω) x₀} ∪
      {ω | ε ≤ dist (backIter φ n (fun k => ξ (k + 0) ω) (V ω))
        (backIter φ n (fun k => ξ (k + 0) ω) x₀)} := by
    intro ω hω
    by_cases h : dist (U n ω) x₀ ≤ R
    · refine Or.inr ?_
      have hVω : V ω = U n ω := by rw [hV_def]; simp only [h, if_true]
      simp only [Set.mem_ofPred_eq, hVω] at hω ⊢
      exact hω
    · exact Or.inl (not_le.1 h)
  have hUm : Measurable (U n) := (hU n).mono (noiseFrom_le hξm _) le_rfl
  have hS : MeasurableSet {y : α | (R : ℝ) < dist y x₀} :=
    measurableSet_lt measurable_const (measurable_id.dist measurable_const)
  have hUR : μ {ω | (R : ℝ) < dist (U n ω) x₀} = π {y | (R : ℝ) < dist y x₀} := by
    rw [← hUπ n, Measure.map_apply hUm hS]
    rfl
  calc μ {ω | ε ≤ dist (backIter φ n (fun k => ξ (k + 0) ω) (U n ω))
        (backIter φ n (fun k => ξ (k + 0) ω) x₀)}
      ≤ μ {ω | (R : ℝ) < dist (U n ω) x₀} + μ {ω | ε ≤ dist
          (backIter φ n (fun k => ξ (k + 0) ω) (V ω)) (backIter φ n (fun k => ξ (k + 0) ω) x₀)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ δ / 2 + δ / 2 := add_le_add (hUR ▸ hR R le_rfl) hmarkov
    _ = δ := ENNReal.add_halves δ

/-- **The limit law is the invariant law** (Giles 2015, §10.1, p. 61: "Under these conditions, it
is known that the distribution of `X_n` converges weakly to that of a limit random variable `X_∞`";
"The invariant distribution in this case is the uniform distribution on `[0, 2]`").  With the
hypotheses of `tendstoInDistribution_fwdIter` (any exponent `p > 0`), let `π` be any invariant
probability measure, `(π ⊗ ν) ∘ φ⁻¹ = π`.  Then the almost sure limit `X_∞` of the chains started
in the past has law `π`.  The proof runs the chain from a point `U_n ~ π` independent of the noises
(on the product space `(α × E)^ℕ` with `(π ⊗ ν)^ℕ`; this chain keeps the law `π`) and couples it
with the chain from `x₀` driven by the same noises: they merge in probability
(`tendsto_measure_dist_backIter`), so along a subsequence both have the limit `X_∞`. -/
theorem map_limit_eq_of_invariant [CompleteSpace α]
    (hφm : Measurable fun q : α × E => φ q.1 q.2) {p ρ : ℝ} (hp : 0 < p) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ p) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν ≠ ∞) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω)))
    {π : Measure α} [IsProbabilityMeasure π] (hπ : (π.prod ν).map (fun q => φ q.1 q.2) = π) :
    μ.map X = π := by
  have : IsProbabilityMeasure ν :=
    hlaw 0 ▸ Measure.isProbabilityMeasure_map (hξm 0).aemeasurable
  have : Nonempty α := ⟨x₀⟩
  -- the augmented noises `ζ_k = (U_k, ξ'_k)`: independent, with law `π ⊗ ν`
  obtain ⟨μ', hμ'⟩ : ∃ μ' : Measure (ℕ → α × E), μ' = Measure.infinitePi fun _ => π.prod ν :=
    ⟨_, rfl⟩
  have : IsProbabilityMeasure μ' := by rw [hμ']; infer_instance
  have hζ : iIndepFun (fun k (ω' : ℕ → α × E) => ω' k) μ' := by
    rw [hμ']
    exact iIndepFun_infinitePi (P := fun _ : ℕ => π.prod ν) (X := fun _ q => q)
      fun _ => measurable_id
  have hζm : ∀ k, Measurable fun ω' : ℕ → α × E => ω' k := fun k => measurable_pi_apply k
  have hζlaw : ∀ k, μ'.map (fun ω' : ℕ → α × E => ω' k) = π.prod ν := fun k => by
    rw [hμ']
    exact Measure.infinitePi_map_eval _ k
  -- the second components are independent noises of law `ν`
  have hη : iIndepFun (fun k (ω' : ℕ → α × E) => (ω' k).2) μ' :=
    hζ.comp (fun _ => Prod.snd) fun _ => measurable_snd
  have hηm : ∀ k, Measurable fun ω' : ℕ → α × E => (ω' k).2 := fun k =>
    measurable_snd.comp (hζm k)
  have hηlaw : ∀ k, μ'.map (fun ω' : ℕ → α × E => (ω' k).2) = ν := fun k => by
    show μ'.map (Prod.snd ∘ fun ω' : ℕ → α × E => ω' k) = ν
    rw [← Measure.map_map measurable_snd (hζm k), hζlaw k, Measure.map_snd_prod, measure_univ,
      one_smul]
  -- the augmented step `(x, (u, e)) ↦ φ(x, e)` contracts and keeps `π`
  have hsnd : ∀ {g : E → ℝ≥0∞}, Measurable g → ∫⁻ q, g q.2 ∂(π.prod ν) = ∫⁻ e, g e ∂ν := by
    intro g hg
    rw [← lintegral_map hg measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  have hφx : ∀ x, Measurable fun e : E => φ x e := fun x => hφm.comp measurable_prodMk_left
  have hφm' : Measurable fun r : α × (α × E) => φ r.1 r.2.2 :=
    hφm.comp (measurable_fst.prodMk measurable_snd.snd)
  have hφ' : ∀ x y, ∫⁻ q : α × E, ENNReal.ofReal (dist (φ x q.2) (φ y q.2) ^ p) ∂(π.prod ν) ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p) := fun x y => by
    rw [hsnd (((hφx x).dist (hφx y)).pow_const p).ennreal_ofReal]
    exact hφ x y
  have hc' : ∫⁻ q : α × E, ENNReal.ofReal (dist x₀ (φ x₀ q.2) ^ p) ∂(π.prod ν) ≠ ∞ := by
    rw [hsnd ((measurable_const.dist (hφx x₀)).pow_const p).ennreal_ofReal]
    exact hc
  have hπ' : (π.prod (π.prod ν)).map (fun r : α × (α × E) => φ r.1 r.2.2) = π := by
    have h1 : (fun r : α × (α × E) => φ r.1 r.2.2) =
        (fun q : α × E => φ q.1 q.2) ∘ Prod.map id Prod.snd := rfl
    rw [h1, ← Measure.map_map hφm (measurable_id.prodMap measurable_snd),
      ← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
      Measure.map_snd_prod, measure_univ, one_smul, hπ]
  -- the stationary chain `A_n`, started at `U_n = (ζ_n).1 ~ π`, keeps the law `π`
  have hU : ∀ n, Measurable[noiseFrom (fun k (ω' : ℕ → α × E) => ω' k) (0 + n)]
      fun ω' : ℕ → α × E => (ω' n).1 := fun n =>
    measurable_fst.comp (measurable_noise _ (by omega))
  have hUlaw : ∀ n, μ'.map (fun ω' : ℕ → α × E => (ω' n).1) = π := fun n => by
    show μ'.map (Prod.fst ∘ fun ω' : ℕ → α × E => ω' n) = π
    rw [← Measure.map_map measurable_fst (hζm n), hζlaw n, Measure.map_fst_prod, measure_univ,
      one_smul]
  have hA : ∀ n, μ'.map (fun ω' : ℕ → α × E =>
      backIter (fun x (q : α × E) => φ x q.2) n (fun k => ω' (k + 0)) (ω' n).1) = π := fun n =>
    map_backIter_of_invariant (φ := fun x (q : α × E) => φ x q.2) hφm' hζ hζm hζlaw hπ' n 0
      (hU n) (hUlaw n)
  have hAm : ∀ n, Measurable fun ω' : ℕ → α × E =>
      backIter (fun x (q : α × E) => φ x q.2) n (fun k => ω' (k + 0)) (ω' n).1 := fun n =>
    (measurable_backIter_shift hφm' _ n 0 (hU n)).mono (noiseFrom_le hζm _) le_rfl
  have hZ'm : ∀ n, Measurable fun ω' : ℕ → α × E =>
      backIter (fun x (q : α × E) => φ x q.2) n (fun k => ω' (k + 0)) x₀ := fun n =>
    (measurable_backIter_pi hφm' n x₀).comp (measurable_pi_lambda _ fun k => hζm (k + 0))
  -- the stationary chain merges in probability with the chain started at `x₀` …
  have hmerge : TendstoInMeasure μ' (fun n ω' => dist
      (backIter (fun x (q : α × E) => φ x q.2) n (fun k => ω' (k + 0)) (ω' n).1)
      (backIter (fun x (q : α × E) => φ x q.2) n (fun k => ω' (k + 0)) x₀)) atTop
      fun _ => 0 := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine (tendsto_measure_dist_backIter (φ := fun x (q : α × E) => φ x q.2) hφm' hp hρ1 hφ'
      hζ hζm hζlaw x₀ hU hUlaw hε).congr fun n => ?_
    congr 1
    ext ω'
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  -- … so, along a subsequence, almost surely
  obtain ⟨ns, hns, hd⟩ := hmerge.exists_seq_tendsto_ae
  -- the chain started at `x₀` converges almost surely to `X'`
  have hconv := ae_tendsto_backIter (φ := fun x (q : α × E) => φ x q.2) hφm' hp hρ0 hρ1 hφ' hζ
    hζm hζlaw x₀ hc'
  obtain ⟨X', hX'_def⟩ : ∃ X' : (ℕ → α × E) → α, X' = fun ω' =>
      limUnder atTop fun n => backIter (fun x (q : α × E) => φ x q.2) n (fun k => ω' k) x₀ :=
    ⟨_, rfl⟩
  have hX' : ∀ᵐ ω' ∂μ', Tendsto (fun n =>
      backIter (fun x (q : α × E) => φ x q.2) n (fun k => ω' (k + 0)) x₀) atTop (𝓝 (X' ω')) := by
    rw [hX'_def]
    exact hconv.mono fun ω' h => tendsto_nhds_limUnder h
  -- so does the stationary chain; hence `X'` has law `π`
  have hAX : ∀ᵐ ω' ∂μ', Tendsto (fun j =>
      backIter (fun x (q : α × E) => φ x q.2) (ns j) (fun k => ω' (k + 0)) (ω' (ns j)).1) atTop
      (𝓝 (X' ω')) := by
    filter_upwards [hd, hX'] with ω' h1 h2
    have h2' := h2.comp hns.tendsto_atTop
    rw [tendsto_iff_dist_tendsto_zero] at h2' ⊢
    have h3 := h1.add h2'
    rw [add_zero] at h3
    exact squeeze_zero (fun j => dist_nonneg) (fun j => dist_triangle _ _ _) h3
  have h1 : μ'.map X' = π := by
    have h := map_eq_map_of_ae_tendsto (μ' := π) (Z' := fun _ y => y) (X' := fun y => y)
      (fun j => (hAm (ns j)).aemeasurable) (fun _ => aemeasurable_id) hAX
      (ae_of_all _ fun _ => tendsto_const_nhds) fun j => by rw [hA (ns j), Measure.map_id']
    rwa [Measure.map_id'] at h
  -- `X` and `X'` have the same law
  have hZm : ∀ n, Measurable fun ω => backIter φ n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_backIter_pi hφm n x₀).comp (measurable_pi_lambda _ hξm)
  have h2 : μ.map X = μ'.map X' := by
    refine map_eq_map_of_ae_tendsto (fun n => (hZm n).aemeasurable)
      (fun n => (hZ'm n).aemeasurable) hX hX' fun n => ?_
    rw [map_backIter_eq_infinitePi hφm hξ hξm hlaw n x₀]
    have e : (fun ω' : ℕ → α × E =>
        backIter (fun x (q : α × E) => φ x q.2) n (fun k => ω' (k + 0)) x₀) =
        fun ω' => backIter φ n (fun k => (ω' k).2) x₀ :=
      funext fun ω' => backIter_comp_noise φ Prod.snd n (fun k => ω' (k + 0)) x₀
    rw [e, map_backIter_eq_infinitePi hφm hη hηm hηlaw n x₀]
  rw [h2, h1]

/-- **The invariant distribution is unique** (Giles 2015, §10.1, p. 61: "The invariant
distribution in this case is the uniform distribution on `[0, 2]`"; "the" invariant distribution
is well defined).  Let `φ` contract on average, `E[d(φ(x, ξ), φ(y, ξ))^p] ≤ ρ d(x, y)^p` with
`p > 0` and `0 ≤ ρ < 1`, for noises of law `ν`, and let `E[d(x₀, φ(x₀, ξ))^p] < ∞` for some `x₀`,
in a complete separable metric space.  Then any two invariant probability measures `π₁`, `π₂`,
`(πᵢ ⊗ ν) ∘ φ⁻¹ = πᵢ`, are equal: both are the law of the limit `X_∞` on the canonical noise space
(`map_limit_eq_of_invariant`).  No moment condition on `π₁`, `π₂` is needed. -/
theorem invariant_unique [CompleteSpace α] (hφm : Measurable fun q : α × E => φ q.1 q.2)
    {p ρ : ℝ} (hp : 0 < p) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ p) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p))
    [IsProbabilityMeasure ν] (x₀ : α) (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ p) ∂ν ≠ ∞)
    {π₁ π₂ : Measure α} [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (h₁ : (π₁.prod ν).map (fun q => φ q.1 q.2) = π₁)
    (h₂ : (π₂.prod ν).map (fun q => φ q.1 q.2) = π₂) :
    π₁ = π₂ := by
  obtain ⟨hind, hm, hl⟩ := canonical_noise (ν := ν)
  have : Nonempty α := ⟨x₀⟩
  have hX : ∀ᵐ e ∂(Measure.infinitePi fun _ => ν), Tendsto
      (fun n => backIter φ n (fun k => e k) x₀) atTop
      (𝓝 (limUnder atTop fun n => backIter φ n (fun k => e k) x₀)) :=
    (ae_tendsto_backIter hφm hp hρ0 hρ1 hφ hind hm hl x₀ hc).mono fun e h =>
      tendsto_nhds_limUnder h
  rw [← map_limit_eq_of_invariant hφm hp hρ0 hρ1 hφ hind hm hl x₀ hc hX h₁,
    map_limit_eq_of_invariant hφm hp hρ0 hρ1 hφ hind hm hl x₀ hc hX h₂]

/-- **There is exactly one invariant distribution** (Giles 2015, §10.1, p. 61: "Under these
conditions, it is known that the distribution of `X_n` converges weakly to that of a limit random
variable `X_∞`"; "The invariant distribution in this case is the uniform distribution on
`[0, 2]`").  With the hypotheses of `tendstoInDistribution_fwdIter` for the paper's exponent
`p = 2γ`, `0 < γ ≤ 1`, there is an invariant probability measure `π`, `(π ⊗ ν) ∘ φ⁻¹ = π`, it has
a finite `2γ`-th moment `∫ d(y, x₀)^{2γ} dπ(y) < ∞`, and every invariant probability measure equals
`π`.  It is the law of the limit `X_∞` (`map_limit_invariant`, `map_limit_eq_of_invariant`). -/
theorem existsUnique_invariant [CompleteSpace α] (hφm : Measurable fun q : α × E => φ q.1 q.2)
    {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    [IsProbabilityMeasure ν] (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞) :
    ∃ π : ProbabilityMeasure α, ((π : Measure α).prod ν).map (fun q => φ q.1 q.2) = π ∧
      ∫⁻ y, ENNReal.ofReal (dist y x₀ ^ (2 * γ)) ∂(π : Measure α) ≠ ∞ ∧
      ∀ π' : ProbabilityMeasure α,
        ((π' : Measure α).prod ν).map (fun q => φ q.1 q.2) = π' → π' = π := by
  obtain ⟨hind, hm, hl⟩ := canonical_noise (ν := ν)
  have : Nonempty α := ⟨x₀⟩
  have hp : 0 < 2 * γ := by linarith
  have hX : ∀ᵐ e ∂(Measure.infinitePi fun _ => ν), Tendsto
      (fun n => backIter φ n (fun k => e k) x₀) atTop
      (𝓝 (limUnder atTop fun n => backIter φ n (fun k => e k) x₀)) :=
    (ae_tendsto_backIter hφm hp hρ0 hρ1 hφ hind hm hl x₀ hc).mono fun e h =>
      tendsto_nhds_limUnder h
  have hZm : ∀ n, Measurable fun e : ℕ → E => backIter φ n (fun k => e k) x₀ := fun n =>
    measurable_backIter_pi hφm n x₀
  have hXm := aemeasurable_of_tendsto_metrizable_ae' (fun n => (hZm n).aemeasurable) hX
  have hinv := map_limit_invariant hφm hφ hind hm hl hγ0 hγ1 hρ0 hρ1 x₀ hc hX
  have hg : Measurable fun y : α => ENNReal.ofReal (dist y x₀ ^ (2 * γ)) :=
    ((measurable_id.dist measurable_const).pow_const _).ennreal_ofReal
  have hmom : ∫⁻ y, ENNReal.ofReal (dist y x₀ ^ (2 * γ))
      ∂((Measure.infinitePi fun _ => ν).map fun e =>
        limUnder atTop fun n => backIter φ n (fun k => e k) x₀) ≠ ∞ := by
    rw [lintegral_map' hg.aemeasurable hXm]
    have h0 := lintegral_dist_limit_le hφm hφ hind hm hl hγ0 hγ1 hρ0 hρ1 x₀ hX 0
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc))
      (le_of_eq_of_le (lintegral_congr fun e => ?_) h0)
    rw [backIter_zero, dist_comm]
  refine ⟨⟨_, Measure.isProbabilityMeasure_map hXm⟩, hinv, hmom, ?_⟩
  rintro ⟨π, hπP⟩ hπ
  have : IsProbabilityMeasure ((Measure.infinitePi fun _ => ν).map fun e =>
      limUnder atTop fun n => backIter φ n (fun k => e k) x₀) :=
    Measure.isProbabilityMeasure_map hXm
  have key : π = (Measure.infinitePi fun _ => ν).map fun e =>
      limUnder atTop fun n => backIter φ n (fun k => e k) x₀ :=
    invariant_unique hφm hp hρ0 hρ1 hφ x₀ hc hπ hinv
  exact Subtype.ext key

end invariant

/-! ### The example `X_{n+1} = X_n/2 + ξ_n`: the limit is uniform on `[0, 2]` -/

section halfStepLimit

/-- The invariance of `U[0, 2]` (`map_halfStep`) in the form `(π ⊗ ν) ∘ φ⁻¹ = π`. -/
lemma halfStep_invariant_prod :
    (uniform02.prod fairCoin).map (fun q => halfStep q.1 q.2) = uniform02 := by
  have : IsProbabilityMeasure uniform02 := ⟨uniform02_univ⟩
  have : IsProbabilityMeasure fairCoin := ⟨fairCoin_univ⟩
  exact map_halfStep measurable_fst measurable_snd
    (indepFun_prod measurable_id measurable_id).symm
    (by rw [Measure.map_fst_prod, measure_univ, one_smul])
    (by rw [Measure.map_snd_prod, measure_univ, one_smul])

/-- A function of the noise has a finite `fairCoin`-integral when its values at `0` and `1` are
finite. -/
lemma lintegral_fairCoin_ne_top {g : ℝ → ℝ≥0∞} (h0 : g 0 ≠ ∞) (h1 : g 1 ≠ ∞) :
    ∫⁻ e, g e ∂fairCoin ≠ ∞ := by
  rw [fairCoin, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, smul_eq_mul, smul_eq_mul]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) h0, ENNReal.mul_ne_top (by simp) h1⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : ℕ → Ω → ℝ}

/-- **The limit of the example chain is uniform on `[0, 2]`** (Giles 2015, §10.1, p. 61: "An
example they offer of a chain satisfying the required conditions is `X_0 = 0`,
`X_{n+1} = ½ X_n + ξ_n`, `n ≥ 0` where `P(ξ_n = 0) = P(ξ_n = 1) = ½`.  The invariant distribution
in this case is the uniform distribution on `[0, 2]`").  Let the `ξ_n` be independent with
`P(ξ_n = 0) = P(ξ_n = 1) = ½` (law `fairCoin`), and let `X` be the almost sure limit of the chains
`Z_n = ξ_0 + ξ_1/2 + ⋯ + ξ_{n−1}/2^{n−1} + x₀/2^n` started `n` steps in the past at `x₀` (any
`x₀`; the paper's `x₀ = 0` included).  Then `X` is uniformly distributed on `[0, 2]`
(`uniform02`): `U[0, 2]` is invariant (`map_halfStep`), so it is the law of the limit
(`map_limit_eq_of_invariant` with `p = 1`, `ρ = ½`). -/
theorem map_limit_halfStep (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = fairCoin) (x₀ : ℝ) {X : Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter halfStep n (fun k => ξ k ω) x₀) atTop
      (𝓝 (X ω))) :
    μ.map X = uniform02 := by
  have : IsProbabilityMeasure uniform02 := ⟨uniform02_univ⟩
  exact map_limit_eq_of_invariant measurable_halfStep one_pos (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one (by norm_num) (by norm_num) one_pos)
    (fun x y => (lintegral_dist_halfStep 1 x y).le) hξ hξm hlaw x₀
    (lintegral_fairCoin_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hX
    halfStep_invariant_prod

/-- **The example chain converges in distribution to the uniform law on `[0, 2]`** (Giles 2015,
§10.1, p. 61: "Under these conditions, it is known that the distribution of `X_n` converges weakly
to that of a limit random variable `X_∞`"; "An example they offer of a chain satisfying the
required conditions is `X_0 = 0`, `X_{n+1} = ½ X_n + ξ_n`, `n ≥ 0` where
`P(ξ_n = 0) = P(ξ_n = 1) = ½`.  The invariant distribution in this case is the uniform distribution
on `[0, 2]`").  For independent `ξ_n` with `P(ξ_n = 0) = P(ξ_n = 1) = ½` there is a random variable
`X_∞`, uniformly distributed on `[0, 2]`, such that the chains started in the past at `0` converge
to `X_∞` almost surely and the chain `X_0 = 0`, `X_{n+1} = X_n/2 + ξ_n` converges to `X_∞` in
distribution. -/
theorem halfStep_limit_uniform (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = fairCoin) :
    ∃ X : Ω → ℝ, μ.map X = uniform02 ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => backIter halfStep n (fun k => ξ k ω) 0) atTop (𝓝 (X ω))) ∧
      TendstoInDistribution (fun n ω => fwdIter halfStep n (fun k => ξ k ω) 0) atTop X
        (fun _ => μ) μ := by
  obtain ⟨X, -, hX, hD⟩ := tendstoInDistribution_fwdIter measurable_halfStep one_pos
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_lt_one (by norm_num) (by norm_num) one_pos)
    (fun x y => (lintegral_dist_halfStep 1 x y).le) hξ hξm hlaw 0
    (lintegral_fairCoin_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  exact ⟨X, map_limit_halfStep hξ hξm hlaw 0 hX, hX, hD⟩

omit [IsProbabilityMeasure μ] in
/-- **`U[0, 2]` is the only invariant distribution of the example** (Giles 2015, §10.1, p. 61:
"The invariant distribution in this case is the uniform distribution on `[0, 2]`").  If a
probability measure `π` on `ℝ` is invariant for `X_{n+1} = ½ X_n + ξ_n` with
`P(ξ_n = 0) = P(ξ_n = 1) = ½`, i.e. `X/2 + ξ ~ π` whenever `X ~ π` and `ξ` are independent, then
`π` is the uniform distribution on `[0, 2]`.  Together with `map_halfStep` (`U[0, 2]` is
invariant) this is the paper's claim. -/
theorem halfStep_invariant_unique {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (π.prod fairCoin).map (fun q => halfStep q.1 q.2) = π) : π = uniform02 := by
  have : IsProbabilityMeasure uniform02 := ⟨uniform02_univ⟩
  have : IsProbabilityMeasure fairCoin := ⟨fairCoin_univ⟩
  exact invariant_unique measurable_halfStep one_pos (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one (by norm_num) (by norm_num) one_pos)
    (fun x y => (lintegral_dist_halfStep 1 x y).le) 0
    (lintegral_fairCoin_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hπ
    halfStep_invariant_prod

end halfStepLimit

/-! ### Multilevel Monte Carlo for `E[f(X_∞)]`: the levels `N_ℓ` increase linearly -/

section mlmc

variable {α E Ω : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [MeasurableSpace E] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ν : Measure E} {φ : α → E → α} {ξ : ℕ → Ω → E}

/-- `ρ^n ≤ 2^{−βℓ}` when `aℓ ≤ n`, `0 ≤ ρ ≤ 1` and `ρ^a ≤ 2^{−β}`. -/
lemma pow_le_two_rpow_of_le {ρ β : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {a : ℕ}
    (hρβ : ρ ^ a ≤ (2 : ℝ) ^ (-β)) {ℓ n : ℕ} (h : a * ℓ ≤ n) :
    ρ ^ n ≤ (2 : ℝ) ^ (-(β * ℓ)) :=
  calc ρ ^ n ≤ ρ ^ (a * ℓ) := pow_le_pow_of_le_one hρ0 hρ1 h
    _ = (ρ ^ a) ^ ℓ := pow_mul ρ a ℓ
    _ ≤ ((2 : ℝ) ^ (-β)) ^ ℓ := pow_le_pow_left₀ (pow_nonneg hρ0 a) hρβ ℓ
    _ = (2 : ℝ) ^ (-(β * ℓ)) := by rw [← two_rpow_mul_nat, neg_mul]

/-- `ℓ + 1 ≤ (1 + (2^δ − 1)⁻¹) 2^{δℓ}` for `δ > 0`: a linearly growing cost satisfies condition
(iv) of Theorem 1 for every `δ > 0`. -/
lemma succ_le_two_rpow {δ : ℝ} (hδ : 0 < δ) (ℓ : ℕ) :
    (ℓ : ℝ) + 1 ≤ (1 + ((2 : ℝ) ^ δ - 1)⁻¹) * (2 : ℝ) ^ (δ * ℓ) := by
  have hq : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have hq1 : 0 < (2 : ℝ) ^ δ - 1 := by linarith
  rw [two_rpow_mul_nat]
  have h1 : 1 + (ℓ : ℝ) * ((2 : ℝ) ^ δ - 1) ≤ ((2 : ℝ) ^ δ) ^ ℓ := by
    have h := one_add_mul_le_pow (a := (2 : ℝ) ^ δ - 1) (by linarith) ℓ
    rwa [add_sub_cancel] at h
  have h2 : (1 : ℝ) ≤ ((2 : ℝ) ^ δ) ^ ℓ := one_le_pow₀ hq.le
  have h3 : (ℓ : ℝ) ≤ ((2 : ℝ) ^ δ - 1)⁻¹ * ((2 : ℝ) ^ δ) ^ ℓ := by
    rw [inv_mul_eq_div, le_div_iff₀ hq1]
    linarith
  rw [add_mul, one_mul]
  linarith

/-- A level length growing at most linearly, `N_ℓ ≤ b(ℓ + 1)`, satisfies condition (iv) of
Theorem 1 for every rate `δ > 0`: `N_ℓ ≤ b (1 + (2^δ − 1)⁻¹) 2^{δℓ}`. -/
lemma natCast_le_two_rpow_of_linear {N : ℕ → ℕ} {b : ℕ} (hNb : ∀ ℓ, N ℓ ≤ b * (ℓ + 1)) {δ : ℝ}
    (hδ : 0 < δ) (ℓ : ℕ) :
    (N ℓ : ℝ) ≤ b * (1 + ((2 : ℝ) ^ δ - 1)⁻¹) * (2 : ℝ) ^ (δ * (ℓ : ℝ)) :=
  calc (N ℓ : ℝ) ≤ b * ((ℓ : ℝ) + 1) := by exact_mod_cast hNb ℓ
    _ ≤ b * ((1 + ((2 : ℝ) ^ δ - 1)⁻¹) * (2 : ℝ) ^ (δ * (ℓ : ℝ))) :=
        mul_le_mul_of_nonneg_left (succ_le_two_rpow hδ ℓ) (Nat.cast_nonneg b)
    _ = b * (1 + ((2 : ℝ) ^ δ - 1)⁻¹) * (2 : ℝ) ^ (δ * (ℓ : ℝ)) := by ring

/-- **Conditions (i) and (iii) of Theorem 1 hold with geometric rates when `N_ℓ` grows linearly**
(Giles 2015, §10.1, p. 61: "Glynn and Rhee (2014) circumvent this problem by making `N` increase
with level, starting a level `ℓ` simulation at `n = −N_ℓ` and terminating it at `n = 0` … This
gives a coupling with a multilevel correction variance which decays as `ℓ` increases.  Because the
decay is exponential in `N_ℓ − N_{ℓ−1}`, it is appropriate to choose `N_ℓ` to increase linearly
with level").  With the hypotheses of `sq_integral_sub_limit_le`, let `N` be nondecreasing with
`a ℓ ≤ N_ℓ` for all `ℓ`, and let `β ≥ 0` with `ρ^a ≤ 2^{−β}` (for `ρ > 0`, `β = a log₂(1/ρ)`).
Write `c = E[d(x₀, φ(x₀, ξ))^{2γ}]`, `C = 4c/(1 − ρ)²`.  The level-`ℓ` approximation
`P_ℓ = f(Z_{N_ℓ})` of `P = f(X_∞)` (the chain started `N_ℓ` steps in the past) satisfies
condition (i) with `α = β/2`, `|E[P_ℓ − P]| ≤ 2√c/(1 − ρ) · 2^{−(β/2)ℓ}`, and condition (iii),
`V[P_ℓ − P_{ℓ−1}] ≤ 2^β C 2^{−βℓ}` (with `P_{−1} ≡ 0`); the second moments satisfy
`E[(P_ℓ − P_{ℓ−1})²] ≤ (2f(x₀)² + (2 + 2^β) C) 2^{−βℓ}`.  Correction to the paper: `V_ℓ` decays
like `ρ^{N_{ℓ−1}}`, exponentially in the number `N_{ℓ−1}` of shared steps, not in `N_ℓ − N_{ℓ−1}`
(see the module docstring for the example); with `N_ℓ` linear in `ℓ` both are linear in `ℓ`. -/
theorem markov_mlmc_rates (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω)))
    {N : ℕ → ℕ} (hN : Monotone N) {a : ℕ} (haN : ∀ ℓ, a * ℓ ≤ N ℓ) {β : ℝ} (hβ : 0 ≤ β)
    (hρβ : ρ ^ a ≤ (2 : ℝ) ^ (-β)) :
    (∀ ℓ : ℕ, |∫ ω, f (backIter φ (N ℓ) (fun k => ξ k ω) x₀) - f (X ω) ∂μ| ≤
      2 / (1 - ρ) * Real.sqrt (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal *
        (2 : ℝ) ^ (-(β / 2 * (ℓ : ℝ)))) ∧
    (∀ ℓ : ℕ, variance (levelDiff (fun ℓ ω => f (backIter φ (N ℓ) (fun k => ξ k ω) x₀)) ℓ) μ ≤
      2 ^ β * (4 / (1 - ρ) ^ 2 *
        (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal) *
        (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) ∧
    (∀ ℓ : ℕ, ∫ ω, levelDiff (fun ℓ ω => f (backIter φ (N ℓ) (fun k => ξ k ω) x₀)) ℓ ω ^ 2 ∂μ ≤
      (2 * f x₀ ^ 2 + (2 + 2 ^ β) * (4 / (1 - ρ) ^ 2 *
        (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal)) *
        (2 : ℝ) ^ (-(β * (ℓ : ℝ)))) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 4 / (1 - ρ) ^ 2 *
      (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal := ⟨_, rfl⟩
  rw [← hC]
  have h4 : 0 ≤ 4 / (1 - ρ) ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  have hC0 : 0 ≤ C := hC ▸ mul_nonneg h4 ENNReal.toReal_nonneg
  have h2β : 1 ≤ (2 : ℝ) ^ β := Real.one_le_rpow (by norm_num) hβ
  have hZm : ∀ n, Measurable fun ω => backIter φ n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_backIter_pi hφm n x₀).comp (measurable_pi_lambda _ hξm)
  have hXm : AEMeasurable X μ :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n => (hZm n).aemeasurable) hX
  have hstart := lintegral_dist_backIter_start_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ (μ := μ)
  have hMfin : ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
      ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc
  have hMreal : (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
      ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal = C := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h4, hC]
  have hLZ := memLp_level hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf (μ := μ)
  have hLX := memLp_limit hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf hX
  have hshift : ∀ ℓ : ℕ, (2 : ℝ) ^ (-(β * (ℓ : ℝ))) =
      2 ^ β * (2 : ℝ) ^ (-(β * ((ℓ + 1 : ℕ) : ℝ))) := fun ℓ => by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  refine ⟨fun ℓ => ?_, fun ℓ => ?_, fun ℓ => ?_⟩
  · -- condition (i)
    rw [integral_sub ((hLZ _).integrable one_le_two) (hLX.integrable one_le_two)]
    refine abs_le_of_sq_le_sq ?_ (mul_nonneg (mul_nonneg (div_nonneg zero_le_two (by linarith))
      (Real.sqrt_nonneg _)) (Real.rpow_nonneg zero_le_two _))
    have e1 : ((2 : ℝ) ^ (-(β / 2 * (ℓ : ℝ)))) ^ 2 = (2 : ℝ) ^ (-(β * (ℓ : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    calc (∫ ω, f (backIter φ (N ℓ) (fun k => ξ k ω) x₀) ∂μ - ∫ ω, f (X ω) ∂μ) ^ 2
        ≤ C * ρ ^ N ℓ := by
          rw [hC]
          exact sq_integral_sub_limit_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf hX _
      _ ≤ C * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) :=
          mul_le_mul_of_nonneg_left (pow_le_two_rpow_of_le hρ0 hρ1.le hρβ (haN ℓ)) hC0
      _ = (2 / (1 - ρ) * Real.sqrt (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal *
            (2 : ℝ) ^ (-(β / 2 * (ℓ : ℝ)))) ^ 2 := by
          rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt ENNReal.toReal_nonneg, e1, hC]
          norm_num
  · -- condition (iii)
    cases ℓ with
    | zero =>
      simp only [levelDiff_zero, Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one]
      calc variance (fun ω => f (backIter φ (N 0) (fun k => ξ k ω) x₀)) μ
          = variance (fun ω => f (backIter φ (N 0) (fun k => ξ k ω) x₀) - f x₀) μ :=
            (variance_sub_const (hfm.comp (hZm _)).aestronglyMeasurable _).symm
        _ ≤ ∫ ω, (f (backIter φ (N 0) (fun k => ξ k ω) x₀) - f x₀) ^ 2 ∂μ := by
            have hm0 : AEStronglyMeasurable
                (fun ω => f (backIter φ (N 0) (fun k => ξ k ω) x₀) - f x₀) μ :=
              ((hfm.comp (hZm _)).sub measurable_const).aestronglyMeasurable
            exact variance_le_expectation_sq hm0
        _ ≤ C := hMreal ▸ integral_sq_sub_le (hZm _).aemeasurable aemeasurable_const hfm hf hMfin
            (hstart _)
        _ ≤ 2 ^ β * C := le_mul_of_one_le_left hC0 h2β
    | succ ℓ =>
      simp only [levelDiff_succ]
      calc variance (fun ω => f (backIter φ (N (ℓ + 1)) (fun k => ξ k ω) x₀) -
            f (backIter φ (N ℓ) (fun k => ξ k ω) x₀)) μ
          ≤ C * ρ ^ N ℓ := by
            rw [hC]
            exact (variance_levels_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf
              (hN (Nat.le_succ ℓ))).2
        _ ≤ C * (2 : ℝ) ^ (-(β * (ℓ : ℝ))) :=
            mul_le_mul_of_nonneg_left (pow_le_two_rpow_of_le hρ0 hρ1.le hρβ (haN ℓ)) hC0
        _ = 2 ^ β * C * (2 : ℝ) ^ (-(β * ((ℓ + 1 : ℕ) : ℝ))) := by
            rw [hshift ℓ]
            ring
  · -- second moments
    have hK0 : 0 ≤ 2 * f x₀ ^ 2 := by positivity
    have hβC : 0 ≤ 2 ^ β * C := mul_nonneg (by positivity) hC0
    cases ℓ with
    | zero =>
      simp only [levelDiff_zero, Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one]
      have hint1 : Integrable (fun ω => (f (backIter φ (N 0) (fun k => ξ k ω) x₀) - f x₀) ^ 2)
          μ := ((hLZ _).sub (memLp_const (f x₀))).integrable_sq
      have hle : ∫ ω, (f (backIter φ (N 0) (fun k => ξ k ω) x₀) - f x₀) ^ 2 ∂μ ≤ C :=
        hMreal ▸ integral_sq_sub_le (hZm _).aemeasurable aemeasurable_const hfm hf hMfin (hstart _)
      calc ∫ ω, f (backIter φ (N 0) (fun k => ξ k ω) x₀) ^ 2 ∂μ
          ≤ ∫ ω, (2 * (f (backIter φ (N 0) (fun k => ξ k ω) x₀) - f x₀) ^ 2 +
              2 * f x₀ ^ 2) ∂μ := by
            refine integral_mono (hLZ _).integrable_sq ((hint1.const_mul 2).add
              (integrable_const _)) fun ω => ?_
            nlinarith [sq_nonneg (f (backIter φ (N 0) (fun k => ξ k ω) x₀) - 2 * f x₀)]
        _ = 2 * ∫ ω, (f (backIter φ (N 0) (fun k => ξ k ω) x₀) - f x₀) ^ 2 ∂μ +
              2 * f x₀ ^ 2 := by
            rw [integral_add (hint1.const_mul 2) (integrable_const _), integral_const_mul,
              integral_const, probReal_univ, one_smul]
        _ ≤ 2 * f x₀ ^ 2 + (2 + 2 ^ β) * C := by nlinarith
    | succ ℓ =>
      simp only [levelDiff_succ]
      have hlev := lintegral_dist_levels_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀
        (hN (Nat.le_succ ℓ)) (μ := μ)
      have hfin : ENNReal.ofReal ρ ^ N ℓ * (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
          ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hMfin
      calc ∫ ω, (f (backIter φ (N (ℓ + 1)) (fun k => ξ k ω) x₀) -
            f (backIter φ (N ℓ) (fun k => ξ k ω) x₀)) ^ 2 ∂μ
          ≤ (ENNReal.ofReal ρ ^ N ℓ * (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
              ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν)).toReal :=
            integral_sq_sub_le (hZm _).aemeasurable (hZm _).aemeasurable hfm hf hfin hlev
        _ = ρ ^ N ℓ * C := by
            rw [ENNReal.toReal_mul, hMreal, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ0]
        _ ≤ (2 : ℝ) ^ (-(β * (ℓ : ℝ))) * C :=
            mul_le_mul_of_nonneg_right (pow_le_two_rpow_of_le hρ0 hρ1.le hρβ (haN ℓ)) hC0
        _ = 2 ^ β * C * (2 : ℝ) ^ (-(β * ((ℓ + 1 : ℕ) : ℝ))) := by
            rw [hshift ℓ]
            ring
        _ ≤ (2 * f x₀ ^ 2 + (2 + 2 ^ β) * C) * (2 : ℝ) ^ (-(β * ((ℓ + 1 : ℕ) : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg zero_le_two _)
            nlinarith

/-- **Glynn and Rhee's unbiased estimator of `E[f(X_∞)]`** (Giles 2015, §10.1, pp. 60–61: "In new
research, Glynn and Rhee (2014) consider the application of their randomised version of MLMC to
Markov chains … In the standard MC approach, one would approximate `E[f(X_∞)]` by estimating
`E[f(X_N)]` for some large value of `N`, but this would be a biased estimate.  Glynn and Rhee
(2014) circumvent this problem by making `N` increase with level"; the single-term estimator of
§2.2).  With the hypotheses of `markov_mlmc_rates`, let also `N_ℓ ≤ b(ℓ + 1)`, let `0 < δ < β`
(`δ` is the cost rate called `γ` in Theorem 1 and §2.2; here `γ` is the Hölder exponent of §10.1),
and let the random level `K` be independent of the noise sequence with
`P(K = ℓ) = p_ℓ ∝ 2^{−(β+δ)ℓ/2}` (`geomLevelProb β δ`).  Then one sample
`Y = p_K⁻¹ (f(Z_{N_K}) − f(Z_{N_{K−1}}))` of the single-term estimator (`P_{−1} ≡ 0`) is an unbiased
estimator of `E[f(X_∞)]` with finite variance, and the length `N_K` of the simulated path has
finite expectation `E[N_K] = ∑_ℓ p_ℓ N_ℓ` (a sample costs at most `2 N_K` steps). -/
theorem markov_randomised_mlmc (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω)))
    {N : ℕ → ℕ} (hN : Monotone N) {a b : ℕ} (haN : ∀ ℓ, a * ℓ ≤ N ℓ)
    (hNb : ∀ ℓ, N ℓ ≤ b * (ℓ + 1)) {β δ : ℝ} (hδ : 0 < δ) (hδβ : δ < β)
    (hρβ : ρ ^ a ≤ (2 : ℝ) ^ (-β)) {K : Ω → ℕ} (hK : Measurable K)
    (hKind : IndepFun K (fun ω k => ξ k ω) μ)
    (hp : ∀ ℓ, μ.real {ω | K ω = ℓ} = geomLevelProb β δ ℓ) :
    Integrable (singleTerm (fun ℓ ω => f (backIter φ (N ℓ) (fun k => ξ k ω) x₀)) K
      (geomLevelProb β δ)) μ ∧
    ∫ ω, singleTerm (fun ℓ ω => f (backIter φ (N ℓ) (fun k => ξ k ω) x₀)) K
      (geomLevelProb β δ) ω ∂μ = ∫ ω, f (X ω) ∂μ ∧
    MemLp (singleTerm (fun ℓ ω => f (backIter φ (N ℓ) (fun k => ξ k ω) x₀)) K
      (geomLevelProb β δ)) 2 μ ∧
    Integrable (fun ω => (N (K ω) : ℝ)) μ ∧
    ∫ ω, (N (K ω) : ℝ) ∂μ = ∑' ℓ, geomLevelProb β δ ℓ * N ℓ := by
  obtain ⟨h_i, -, h_iii⟩ := markov_mlmc_rates hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf hX
    hN haN (by linarith) hρβ
  have hPlm : ∀ ℓ, Measurable fun ω => f (backIter φ (N ℓ) (fun k => ξ k ω) x₀) := fun ℓ =>
    hfm.comp ((measurable_backIter_pi hφm (N ℓ) x₀).comp (measurable_pi_lambda _ hξm))
  have hind : ∀ ℓ, IndepFun K
      (levelDiff (fun ℓ ω => f (backIter φ (N ℓ) (fun k => ξ k ω) x₀)) ℓ) μ := fun ℓ => by
    have h := hKind.comp measurable_id (measurable_levelDiff (fun ℓ =>
      hfm.comp (measurable_backIter_pi hφm (N ℓ) x₀)) ℓ)
    cases ℓ <;> exact h
  have hcost : ∀ ℓ : ℕ, ∫ _ω, (N ℓ : ℝ) ∂μ ≤
      b * (1 + ((2 : ℝ) ^ δ - 1)⁻¹) * (2 : ℝ) ^ (δ * (ℓ : ℝ)) := fun ℓ => by
    rw [integral_const, probReal_univ, one_smul]
    exact natCast_le_two_rpow_of_linear hNb hδ ℓ
  obtain ⟨h1, h2, h3, h4, h5⟩ := randomised_mlmc_finite (μ := μ) (K := K)
    (Pl := fun ℓ ω => f (backIter φ (N ℓ) (fun k => ξ k ω) x₀)) (fun ω => f (X ω))
    (κ := fun ℓ _ => (N ℓ : ℝ)) (α := β / 2) (by linarith) hδ hδβ hK hPlm
    (memLp_level hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf <| N ·)
    ((memLp_limit hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf hX).integrable one_le_two)
    hp hind h_i h_iii (fun _ => measurable_const) (fun _ _ => Nat.cast_nonneg _)
    (fun _ => integrable_const _) (fun _ => indepFun_const_right K _) hcost
  refine ⟨h1, h2, h3, h4, h5.trans (tsum_congr fun ℓ => ?_)⟩
  rw [integral_const, probReal_univ, one_smul]

/-- **Theorem 1 for the multilevel estimator of `E[f(X_∞)]`** (Giles 2015, §10.1, p. 61, with
§2.1, Theorem 1: "Glynn and Rhee (2014) circumvent this problem by making `N` increase with level,
starting a level `ℓ` simulation at `n = −N_ℓ` and terminating it at `n = 0` … This gives a coupling
with a multilevel correction variance which decays as `ℓ` increases.  Because the decay is
exponential in `N_ℓ − N_{ℓ−1}`, it is appropriate to choose `N_ℓ` to increase linearly with
level").  With the hypotheses of `markov_randomised_mlmc` on `φ`, `f`, the level lengths
`a ℓ ≤ N_ℓ ≤ b(ℓ + 1)` and the rates `0 < δ < β`, `ρ^a ≤ 2^{−β}`, in a complete separable metric
space: consider the standard multilevel estimator whose `n`-th level-`ℓ` sample is
`f(Z_{N_ℓ}) − f(Z_{N_{ℓ−1}})` (`P_{−1} ≡ 0`) computed from its own independent copy `e^{(ℓ,n)}` of
the noise sequence (the coordinates of `(E^ℕ)^{ℕ×ℕ}` under `(ν^ℕ)^{ℕ×ℕ}`) and costs `N_ℓ`.  There
is `c₄ > 0` such that for every `0 < ε < e⁻¹` there are `L` and sample sizes `M_ℓ ≥ 1` for which
this estimator of `E[f(X_∞)]` has a square-integrable error with mean square `< ε²`, and cost
`∑_{ℓ≤L} M_ℓ N_ℓ ≤ c₄ ε⁻²` (Theorem 1 with `α = β/2`, variance rate `β` and cost rate `δ < β`).  The
target `E[f(X_∞)]` is computed on any probability space carrying the noises and the limit `X_∞`. -/
theorem markov_mlmc_theorem1 [CompleteSpace α] (hφm : Measurable fun q : α × E => φ q.1 q.2)
    {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) {X : Ω → α}
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun n => backIter φ n (fun k => ξ k ω) x₀) atTop (𝓝 (X ω)))
    {N : ℕ → ℕ} (hN : Monotone N) {a b : ℕ} (haN : ∀ ℓ, a * ℓ ≤ N ℓ)
    (hNb : ∀ ℓ, N ℓ ≤ b * (ℓ + 1)) {β δ : ℝ} (hδ : 0 < δ) (hδβ : δ < β)
    (hρβ : ρ ^ a ≤ (2 : ℝ) ^ (-β)) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (M : ℕ → ℕ), (∀ ℓ, 0 < M ℓ) ∧
        Integrable (fun x => (mlmcEstimator (fun ℓ (e : ℕ → E) => f (backIter φ (N ℓ) e x₀))
            (fun p x => x p) L M x - ∫ ω, f (X ω) ∂μ) ^ 2)
          (Measure.infinitePi fun _ : ℕ × ℕ => Measure.infinitePi fun _ : ℕ => ν) ∧
        ∫ x, (mlmcEstimator (fun ℓ (e : ℕ → E) => f (backIter φ (N ℓ) e x₀)) (fun p x => x p) L M
            x - ∫ ω, f (X ω) ∂μ) ^ 2
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => Measure.infinitePi fun _ : ℕ => ν) < ε ^ 2 ∧
        ∫ x, totalCost (fun ℓ _ _ => (N ℓ : ℝ)) L M x
          ∂(Measure.infinitePi fun _ : ℕ × ℕ => Measure.infinitePi fun _ : ℕ => ν) ≤
          c₄ * ε ^ (-2 : ℝ) := by
  have : IsProbabilityMeasure ν :=
    hlaw 0 ▸ Measure.isProbabilityMeasure_map (hξm 0).aemeasurable
  have : Nonempty α := ⟨x₀⟩
  obtain ⟨hind, hm, hl⟩ := canonical_noise (ν := ν)
  -- the limit on the canonical noise space `(E^ℕ, ν^ℕ)`
  have hF : ∀ᵐ e ∂(Measure.infinitePi fun _ => ν), Tendsto
      (fun n => backIter φ n (fun k => e k) x₀) atTop
      (𝓝 (limUnder atTop fun n => backIter φ n (fun k => e k) x₀)) :=
    (ae_tendsto_backIter hφm (by linarith) hρ0 hρ1 hφ hind hm hl x₀ hc).mono fun e h =>
      tendsto_nhds_limUnder h
  obtain ⟨h_i, h_iii, -⟩ := markov_mlmc_rates hφm hφ hind hm hl hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf hF
    hN haN (by linarith) hρβ
  -- `E[f(X_∞)]` does not depend on the probability space
  have hZm : ∀ n, Measurable fun ω => backIter φ n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_backIter_pi hφm n x₀).comp (measurable_pi_lambda _ hξm)
  have hZm' : ∀ n, Measurable fun e : ℕ → E => backIter φ n (fun k => e k) x₀ := fun n =>
    measurable_backIter_pi hφm n x₀
  have hlawX : μ.map X = (Measure.infinitePi fun _ => ν).map
      (fun e => limUnder atTop fun n => backIter φ n (fun k => e k) x₀) :=
    map_eq_map_of_ae_tendsto (fun n => (hZm n).aemeasurable) (fun n => (hZm' n).aemeasurable) hX
      hF fun n => by
        rw [map_backIter_eq_infinitePi hφm hξ hξm hlaw n x₀,
          map_backIter_eq_infinitePi hφm hind hm hl n x₀]
  have htarget : ∫ ω, f (X ω) ∂μ = ∫ e, f (limUnder atTop fun n =>
      backIter φ n (fun k => e k) x₀) ∂(Measure.infinitePi fun _ => ν) := by
    rw [← integral_map (aemeasurable_of_tendsto_metrizable_ae' (fun n => (hZm n).aemeasurable) hX)
      hfm.aestronglyMeasurable, hlawX, integral_map (aemeasurable_of_tendsto_metrizable_ae'
        (fun n => (hZm' n).aemeasurable) hF) hfm.aestronglyMeasurable]
  -- Theorem 1 on the canonical space
  have h1ρ : 0 < 1 - ρ := by linarith
  have hc₁ : 0 ≤ 2 / (1 - ρ) *
      Real.sqrt (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal :=
    mul_nonneg (div_nonneg zero_le_two h1ρ.le) (Real.sqrt_nonneg _)
  have hc₂ : 0 ≤ 2 ^ β * (4 / (1 - ρ) ^ 2 *
      (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal) :=
    mul_nonneg (Real.rpow_nonneg zero_le_two _)
      (mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _)) ENNReal.toReal_nonneg)
  have h2δ : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have hc₃ : 0 ≤ (b : ℝ) * (1 + ((2 : ℝ) ^ δ - 1)⁻¹) := mul_nonneg (Nat.cast_nonneg b)
    (add_nonneg zero_le_one (inv_nonneg.2 (by linarith)))
  obtain ⟨c₄, hc₄, h⟩ := giles_theorem1_iid (Measure.infinitePi fun _ : ℕ => ν)
    (fun e => f (limUnder atTop fun n => backIter φ n (fun k => e k) x₀))
    (fun ℓ e => f (backIter φ (N ℓ) e x₀)) (fun ℓ _ => (N ℓ : ℝ)) (α := β / 2) (β := β) (γ := δ)
    (c₁ := 2 / (1 - ρ) *
      Real.sqrt (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal + 1)
    (c₂ := 2 ^ β * (4 / (1 - ρ) ^ 2 *
      (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal) + 1)
    (c₃ := (b : ℝ) * (1 + ((2 : ℝ) ^ δ - 1)⁻¹) + 1)
    (by linarith) (by linarith) hδ (by linarith) (by linarith) (by linarith)
    (by linarith [min_le_left β δ])
    ((memLp_limit hφm hφ hind hm hl hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf hF).integrable one_le_two)
    (fun ℓ => hfm.comp (hZm' (N ℓ)))
    (memLp_level hφm hφ hind hm hl hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf <| N ·)
    (fun _ => integrable_const _)
    (fun ℓ => (h_i ℓ).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (Real.rpow_nonneg zero_le_two _)))
    (fun ℓ => (h_iii ℓ).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (Real.rpow_nonneg zero_le_two _)))
    (fun ℓ => by
      rw [integral_const, probReal_univ, one_smul]
      exact (natCast_le_two_rpow_of_linear hNb hδ ℓ).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) (Real.rpow_nonneg zero_le_two _)))
  obtain ⟨-, -, hω⟩ := exists_iid_inputs (Measure.infinitePi fun _ : ℕ => ν)
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, M, hM, hmse, hcost⟩ := h ε hε hε1
  refine ⟨L, M, hM, ?_, ?_, ?_⟩
  · exact ((memLp_finsetSum _ fun ℓ _ => memLp_levelEstimator hω
      (memLp_level hφm hφ hind hm hl hγ0 hγ1 hρ0 hρ1 x₀ hc hfm hf <| N ·) ℓ (M ℓ)).sub
      (memLp_const _)).integrable_sq
  · rw [htarget]
    exact hmse
  · rw [complexityBound_of_lt hδβ] at hcost
    exact hcost

end mlmc

end MLMC
