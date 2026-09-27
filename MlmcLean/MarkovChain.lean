import MlmcLean.Complexity
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Markov chains and limiting distributions (Giles 2015, §10.1)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §10.1 "Markov
chains and limiting distributions" (p. 61, Figure 10.12), after Glynn and Rhee (2014).

"The Markov chain `{X_n}` in a metric space with metric `d` is defined by `X_0 = x`,
`X_{n+1} = φ_n(X_n)`, where `{φ_n}` is a sequence of iid random functions.  Furthermore, it is
assumed that the `φ`'s are contracting on average in the sense that
`sup_{x≠y} E[(d(φ_n(x), φ_n(y))/d(x, y))^{2γ}] < 1` for some `γ ∈ (0, 1)`. … `f` is Hölder
continuous with exponent `γ`, so that `|f(y) − f(x)| ≤ d(x, y)^γ`.  An example … is
`X_0 = 0`, `X_{n+1} = ½ X_n + ξ_n` where `P(ξ_n = 0) = P(ξ_n = 1) = ½`.  The invariant
distribution in this case is the uniform distribution on `[0, 2]`.  … starting a level `ℓ`
simulation at `n = −N_ℓ` and terminating it at `n = 0` … the level `ℓ` and `ℓ − 1` simulations
share the same random `φ_n` for `n ≥ −N_{ℓ−1}`.  Because of the contraction property, the effect of
the initial evolution of the level `ℓ` path for `n < −N_{ℓ−1}` decays exponentially.  This gives a
coupling with a multilevel correction variance which decays as `ℓ` increases."

**Model.**  The random functions are `φ_n = φ(·, e)` with a jointly measurable `φ : α × E → α` and
i.i.d. noises of law `ν`; the noise `ξ_k` drives the step that ends at time `−k`.  So the level
`ℓ` sample is `backIter φ N_ℓ ξ x₀`, the value at time `0` of the chain started at time `−N_ℓ`
at `x₀`, and the level `ℓ − 1` sample `backIter φ N_{ℓ−1} ξ x₀` uses the same `ξ_0, …,
ξ_{N_{ℓ−1}−1}`.  The contraction hypothesis is Giles' condition with `ρ` the supremum:
`E[d(φ(x, ξ), φ(y, ξ))^p] ≤ ρ d(x, y)^p` for all `x, y`, `p = 2γ`, `ρ < 1`.

* `backIter_add`: the level `ℓ` path is the level `ℓ − 1` path started from the random point
  reached after the first `N_ℓ − N_{ℓ−1}` steps, which depends only on the noises that the
  level `ℓ − 1` path does not use.
* `lintegral_dist_backIter_le`: `n` shared steps contract the `p`-th moment of the distance
  by `ρ^n`, from any starting points that are independent of the shared noises.
* `lintegral_dist_start_le`: the distance travelled from `x₀`, `E[d(x₀, X)^{2γ}]`, is bounded
  uniformly in the number of steps by `4c/(1 − ρ)²`, `c = E[d(x₀, φ(x₀, ξ))^{2γ}]`.
* `lintegral_dist_levels_le`, `variance_levels_le`: hence
  `V_ℓ = V[f(X^{(ℓ)}) − f(X^{(ℓ−1)})] ≤ 4c/(1 − ρ)² · ρ^{N_{ℓ−1}}` for `γ`-Hölder `f`.  The decay is
  exponential in the number `N_{ℓ−1}` of shared steps (the paper says `N_ℓ − N_{ℓ−1}`); with
  `N_ℓ` increasing linearly in `ℓ`, both are linear in `ℓ` and `V_ℓ` decays geometrically.
* `lintegral_dist_halfStep`, `halfStep_invariant`, `map_halfStep`: the example
  `X_{n+1} = X_n/2 + ξ_n` contracts with `ρ = 2^{−2γ} < 1`, and the uniform distribution on
  `[0, 2]` is invariant.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace MLMC

/-! ### The chain started in the past -/

section backward

variable {α E : Type*}

/-- **The level `ℓ` path of Giles 2015, §10.1 (Figure 10.12)**: `backIter φ n e x` is the value at
time `0` of the chain started at time `−n` at `x`, whose step ending at time `−k` applies
`φ(·, e_k)`, i.e. `φ(·, e_0) ∘ φ(·, e_1) ∘ ⋯ ∘ φ(·, e_{n−1})` applied to `x`. -/
def backIter (φ : α → E → α) : ℕ → (ℕ → E) → α → α
  | 0, _, x => x
  | n + 1, e, x => φ (backIter φ n (fun k => e (k + 1)) x) (e 0)

lemma backIter_zero (φ : α → E → α) (e : ℕ → E) (x : α) : backIter φ 0 e x = x := rfl

lemma backIter_succ (φ : α → E → α) (n : ℕ) (e : ℕ → E) (x : α) :
    backIter φ (n + 1) e x = φ (backIter φ n (fun k => e (k + 1)) x) (e 0) := rfl

/-- The first step of the chain started at time `−(n + 1)` applies `φ(·, e_n)`. -/
lemma backIter_succ' (φ : α → E → α) (n : ℕ) (e : ℕ → E) (x : α) :
    backIter φ (n + 1) e x = backIter φ n e (φ x (e n)) := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    rw [backIter_succ, ih (fun k => e (k + 1)), backIter_succ φ n e]

/-- The last step with shifted noises: `backIter φ (n + 1) (e_{m+·}) x` applies `φ(·, e_m)` to the
chain driven by `e_{m+1+·}`. -/
lemma backIter_succ_shift (φ : α → E → α) (n m : ℕ) (e : ℕ → E) (x : α) :
    backIter φ (n + 1) (fun k => e (k + m)) x =
      φ (backIter φ n (fun k => e (k + (m + 1))) x) (e m) := by
  have h : (fun k => e (k + 1 + m)) = fun k => e (k + (m + 1)) := by
    funext k
    congr 1
    omega
  show φ (backIter φ n (fun k => e (k + 1 + m)) x) (e (0 + m)) = _
  rw [h, zero_add]

/-- **The multilevel coupling of Giles 2015, §10.1**: the chain started `n + m` steps in the past is
the chain started `m` steps in the past from the random point that the first `n` steps reach, and
those steps use only the noises `e_m, e_{m+1}, …` that the shorter chain does not use. -/
lemma backIter_add (φ : α → E → α) (n m : ℕ) (e : ℕ → E) (x : α) :
    backIter φ (n + m) e x = backIter φ m e (backIter φ n (fun k => e (k + m)) x) := by
  induction m generalizing e with
  | zero => rfl
  | succ m ih =>
    rw [← Nat.add_assoc, backIter_succ, ih (fun k => e (k + 1)), backIter_succ φ m e]
    rfl

end backward

/-! ### The σ-algebras of the noises -/

section noise

variable {Ω E α : Type*} [MeasurableSpace Ω] [mE : MeasurableSpace E]

/-- The σ-algebra generated by the noises `ξ_m, ξ_{m+1}, …`: the information used by the steps of
the chain before time `−m` (Giles 2015, §10.1). -/
def noiseFrom (ξ : ℕ → Ω → E) (m : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ Set.Ici m, MeasurableSpace.comap (ξ i) mE

lemma noiseFrom_le {ξ : ℕ → Ω → E} (hξm : ∀ i, Measurable (ξ i)) (m : ℕ) :
    noiseFrom ξ m ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun i _ => (hξm i).comap_le

omit [MeasurableSpace Ω] in
lemma noiseFrom_anti (ξ : ℕ → Ω → E) {m m' : ℕ} (h : m ≤ m') : noiseFrom ξ m' ≤ noiseFrom ξ m :=
  iSup₂_mono' fun i hi => ⟨i, Set.mem_Ici.2 (h.trans (Set.mem_Ici.1 hi)), le_rfl⟩

omit [MeasurableSpace Ω] in
lemma measurable_noise (ξ : ℕ → Ω → E) {m i : ℕ} (h : m ≤ i) : Measurable[noiseFrom ξ m] (ξ i) :=
  (comap_measurable (ξ i)).mono
    (le_iSup₂ (f := fun j (_ : j ∈ Set.Ici m) => MeasurableSpace.comap (ξ j) mE) i
      (Set.mem_Ici.2 h)) le_rfl

variable [MeasurableSpace α]

/-- The chain started `n` steps before time `−m`, from a starting point determined by the noises
before time `−(m + n)`, is determined by the noises before time `−m`. -/
lemma measurable_backIter_shift {φ : α → E → α} (hφm : Measurable fun q : α × E => φ q.1 q.2)
    (ξ : ℕ → Ω → E) (n : ℕ) :
    ∀ (m : ℕ) {U : Ω → α}, Measurable[noiseFrom ξ (m + n)] U →
      Measurable[noiseFrom ξ m] fun ω => backIter φ n (fun k => ξ (k + m) ω) (U ω) := by
  induction n with
  | zero =>
    intro m U hU
    exact hU
  | succ n ih =>
    intro m U hU
    have h1 : Measurable[noiseFrom ξ (m + 1)]
        fun ω => backIter φ n (fun k => ξ (k + (m + 1)) ω) (U ω) :=
      ih (m + 1) (by rwa [show m + 1 + n = m + (n + 1) by omega])
    have h2 := h1.mono (noiseFrom_anti ξ (Nat.le_succ m)) le_rfl
    have h3 : Measurable[noiseFrom ξ m] (ξ m) := measurable_noise ξ le_rfl
    have e : (fun ω => backIter φ (n + 1) (fun k => ξ (k + m) ω) (U ω)) =
        fun ω => φ (backIter φ n (fun k => ξ (k + (m + 1)) ω) (U ω)) (ξ m ω) :=
      funext fun ω => backIter_succ_shift φ n m (fun k => ξ k ω) (U ω)
    rw [e]
    exact hφm.comp (h2.prodMk h3)

end noise

/-! ### Contraction of the coupled chains -/

section contraction

variable {α E Ω : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [SecondCountableTopology α] [MeasurableSpace E] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ν : Measure E} {φ : α → E → α} {ξ : ℕ → Ω → E}

/-- **Giles 2015, §10.1: the coupled chains contract.**  Let the noises `ξ_k` be independent with
law `ν`, and let `φ` contract on average: `E[d(φ(x, ξ), φ(y, ξ))^p] ≤ ρ d(x, y)^p` for all `x, y`.
Two copies of the chain that share the `n` noises `ξ_m, …, ξ_{m+n−1}` and start from points `U`,
`V` determined by the later noises `ξ_{m+n}, ξ_{m+n+1}, …` satisfy
`E[d(X_U, X_V)^p] ≤ ρ^n E[d(U, V)^p]`. -/
theorem lintegral_dist_backIter_le (hφm : Measurable fun q : α × E => φ q.1 q.2) {p ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ p) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ p))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν) (n : ℕ) :
    ∀ (m : ℕ) {U V : Ω → α}, Measurable[noiseFrom ξ (m + n)] U →
      Measurable[noiseFrom ξ (m + n)] V →
      ∫⁻ ω, ENNReal.ofReal (dist (backIter φ n (fun k => ξ (k + m) ω) (U ω))
          (backIter φ n (fun k => ξ (k + m) ω) (V ω)) ^ p) ∂μ ≤
        ENNReal.ofReal ρ ^ n * ∫⁻ ω, ENNReal.ofReal (dist (U ω) (V ω) ^ p) ∂μ := by
  induction n with
  | zero =>
    intro m U V _ _
    simp only [backIter_zero, pow_zero, one_mul, le_refl]
  | succ n ih =>
    intro m U V hU hV
    have hU' : Measurable[noiseFrom ξ (m + 1 + n)] U := by
      rwa [show m + 1 + n = m + (n + 1) by omega]
    have hV' : Measurable[noiseFrom ξ (m + 1 + n)] V := by
      rwa [show m + 1 + n = m + (n + 1) by omega]
    have hA := measurable_backIter_shift hφm ξ n (m + 1) hU'
    have hB := measurable_backIter_shift hφm ξ n (m + 1) hV'
    obtain ⟨A, hA_def⟩ : ∃ A : Ω → α,
        A = fun ω => backIter φ n (fun k => ξ (k + (m + 1)) ω) (U ω) := ⟨_, rfl⟩
    obtain ⟨B, hB_def⟩ : ∃ B : Ω → α,
        B = fun ω => backIter φ n (fun k => ξ (k + (m + 1)) ω) (V ω) := ⟨_, rfl⟩
    rw [← hA_def] at hA
    rw [← hB_def] at hB
    have hAB : Measurable[noiseFrom ξ (m + 1)] fun ω => (A ω, B ω) := hA.prodMk hB
    have hAB' : Measurable fun ω => (A ω, B ω) := hAB.mono (noiseFrom_le hξm _) le_rfl
    -- the pair after the first `n` steps is independent of the noise of the last step
    have hind : IndepFun (fun ω => (A ω, B ω)) (ξ m) μ := by
      rw [IndepFun_iff_Indep]
      have h := indep_iSup_of_disjoint (fun i => (hξm i).comap_le) hξ.iIndep
        (S := Set.Ici (m + 1)) (T := {m}) (Set.disjoint_singleton_right.2 (by simp))
      refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h hAB.comap_le) ?_
      exact le_iSup₂ (f := fun i (_ : i ∈ ({m} : Set ℕ)) =>
        MeasurableSpace.comap (ξ i) inferInstance) m (Set.mem_singleton m)
    have hmap : μ.map (fun ω => ((A ω, B ω), ξ m ω)) = (μ.map fun ω => (A ω, B ω)).prod ν := by
      rw [← hlaw m]
      exact (indepFun_iff_map_prod_eq_prod_map_map hAB'.aemeasurable (hξm m).aemeasurable).1 hind
    have hg : Measurable fun q : (α × α) × E =>
        ENNReal.ofReal (dist (φ q.1.1 q.2) (φ q.1.2 q.2) ^ p) := by
      have h1 : Measurable fun q : (α × α) × E => φ q.1.1 q.2 :=
        hφm.comp (measurable_fst.fst.prodMk measurable_snd)
      have h2 : Measurable fun q : (α × α) × E => φ q.1.2 q.2 :=
        hφm.comp (measurable_fst.snd.prodMk measurable_snd)
      exact ((h1.dist h2).pow_const p).ennreal_ofReal
    have hd : Measurable fun z : α × α => ENNReal.ofReal (dist z.1 z.2 ^ p) :=
      (measurable_dist.pow_const p).ennreal_ofReal
    have hstep : ∀ ω, ENNReal.ofReal (dist (backIter φ (n + 1) (fun k => ξ (k + m) ω) (U ω))
        (backIter φ (n + 1) (fun k => ξ (k + m) ω) (V ω)) ^ p) =
        ENNReal.ofReal (dist (φ (A ω) (ξ m ω)) (φ (B ω) (ξ m ω)) ^ p) := by
      intro ω
      rw [backIter_succ_shift φ n m (fun k => ξ k ω) (U ω),
        backIter_succ_shift φ n m (fun k => ξ k ω) (V ω), hA_def, hB_def]
    calc ∫⁻ ω, ENNReal.ofReal (dist (backIter φ (n + 1) (fun k => ξ (k + m) ω) (U ω))
            (backIter φ (n + 1) (fun k => ξ (k + m) ω) (V ω)) ^ p) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (dist (φ (A ω) (ξ m ω)) (φ (B ω) (ξ m ω)) ^ p) ∂μ :=
          lintegral_congr hstep
      _ = ∫⁻ q, ENNReal.ofReal (dist (φ q.1.1 q.2) (φ q.1.2 q.2) ^ p)
            ∂(μ.map fun ω => ((A ω, B ω), ξ m ω)) :=
          (lintegral_map hg (hAB'.prodMk (hξm m))).symm
      _ = ∫⁻ q, ENNReal.ofReal (dist (φ q.1.1 q.2) (φ q.1.2 q.2) ^ p)
            ∂((μ.map fun ω => (A ω, B ω)).prod ν) := by rw [hmap]
      _ ≤ ∫⁻ z, ∫⁻ e, ENNReal.ofReal (dist (φ z.1 e) (φ z.2 e) ^ p) ∂ν
            ∂(μ.map fun ω => (A ω, B ω)) := lintegral_prod_le _
      _ ≤ ∫⁻ z, ENNReal.ofReal ρ * ENNReal.ofReal (dist z.1 z.2 ^ p)
            ∂(μ.map fun ω => (A ω, B ω)) := lintegral_mono fun z => hφ z.1 z.2
      _ = ENNReal.ofReal ρ * ∫⁻ z, ENNReal.ofReal (dist z.1 z.2 ^ p)
            ∂(μ.map fun ω => (A ω, B ω)) := lintegral_const_mul _ hd
      _ = ENNReal.ofReal ρ * ∫⁻ ω, ENNReal.ofReal (dist (A ω) (B ω) ^ p) ∂μ :=
          congrArg (ENNReal.ofReal ρ * ·) (lintegral_map hd hAB')
      _ ≤ ENNReal.ofReal ρ * (ENNReal.ofReal ρ ^ n *
            ∫⁻ ω, ENNReal.ofReal (dist (U ω) (V ω) ^ p) ∂μ) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [hA_def, hB_def]
          exact ih (m + 1) hU' hV'
      _ = ENNReal.ofReal ρ ^ (n + 1) * ∫⁻ ω, ENNReal.ofReal (dist (U ω) (V ω) ^ p) ∂μ := by
          ring

/-- `(∑_j a_j)^γ ≤ ∑_j a_j^γ` for `a_j ≥ 0` and `0 < γ ≤ 1`. -/
lemma rpow_sum_le_sum_rpow {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (k : ℕ) : (∑ j ∈ range k, a j) ^ γ ≤ ∑ j ∈ range k, a j ^ γ := by
  induction k with
  | zero => simp [Real.zero_rpow hγ0.ne']
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    calc (∑ j ∈ range k, a j + a k) ^ γ ≤ (∑ j ∈ range k, a j) ^ γ + a k ^ γ :=
          Real.rpow_add_le_add_rpow (Finset.sum_nonneg fun j _ => ha j) (ha k) hγ0.le hγ1
      _ ≤ ∑ j ∈ range k, a j ^ γ + a k ^ γ := by linarith

/-- If `d ≤ ∑_{j<k} D_j` with `D_j ≥ 0`, `0 < γ ≤ 1` and `0 < r < 1`, then
`d^{2γ} ≤ ∑_{j<k} (1 − r)⁻¹ r^{−j} D_j^{2γ}`: `t ↦ t^γ` is subadditive, and the Cauchy–Schwarz
inequality with the weights `r^j` bounds the square of the sum. -/
lemma rpow_two_mul_le_sum {γ r d : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hr0 : 0 < r) (hr1 : r < 1)
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) (k : ℕ) (hd0 : 0 ≤ d) (hd : d ≤ ∑ j ∈ range k, D j) :
    d ^ (2 * γ) ≤ ∑ j ∈ range k, (1 - r)⁻¹ * (r ^ j)⁻¹ * D j ^ (2 * γ) := by
  have hsq : ∀ x : ℝ, 0 ≤ x → x ^ (2 * γ) = (x ^ γ) ^ 2 := fun x hx => by
    rw [mul_comm, Real.rpow_mul hx, Real.rpow_two]
  have h1 : d ^ γ ≤ ∑ j ∈ range k, D j ^ γ :=
    (Real.rpow_le_rpow hd0 hd hγ0.le).trans (rpow_sum_le_sum_rpow hγ0 hγ1 D hD k)
  have hT0 : 0 ≤ ∑ j ∈ range k, (D j ^ γ) ^ 2 / r ^ j :=
    Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (pow_pos hr0 j).le
  have h2 : (∑ j ∈ range k, D j ^ γ) ^ 2 ≤
      (1 - r)⁻¹ * ∑ j ∈ range k, (D j ^ γ) ^ 2 / r ^ j := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hS0 : 0 < ∑ j ∈ range k, r ^ j :=
      Finset.sum_pos (fun j _ => pow_pos hr0 j) ⟨0, Finset.mem_range.2 hk⟩
    have h := Finset.sq_sum_div_le_sum_sq_div (range k) (fun j => D j ^ γ)
      (fun j _ => pow_pos hr0 j)
    rw [div_le_iff₀ hS0] at h
    calc (∑ j ∈ range k, D j ^ γ) ^ 2
        ≤ (∑ j ∈ range k, (D j ^ γ) ^ 2 / r ^ j) * ∑ j ∈ range k, r ^ j := h
      _ ≤ (∑ j ∈ range k, (D j ^ γ) ^ 2 / r ^ j) * (1 - r)⁻¹ :=
          mul_le_mul_of_nonneg_left (geom_sum_le_of_lt_one hr0.le hr1 k) hT0
      _ = (1 - r)⁻¹ * ∑ j ∈ range k, (D j ^ γ) ^ 2 / r ^ j := mul_comm _ _
  calc d ^ (2 * γ) = (d ^ γ) ^ 2 := hsq d hd0
    _ ≤ (∑ j ∈ range k, D j ^ γ) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hd0 γ) h1 2
    _ ≤ (1 - r)⁻¹ * ∑ j ∈ range k, (D j ^ γ) ^ 2 / r ^ j := h2
    _ = ∑ j ∈ range k, (1 - r)⁻¹ * (r ^ j)⁻¹ * D j ^ (2 * γ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsq (D j) (hD j), div_eq_mul_inv]
        ring

/-- `∑_{j<k} (1 − r)⁻¹ r^{−j} ρ^j ≤ 4/(1 − ρ)²` for `0 ≤ ρ < 1` and `r = (1 + ρ)/2`. -/
lemma sum_weight_pow_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (k : ℕ) :
    ∑ j ∈ range k, (1 - (1 + ρ) / 2)⁻¹ * (((1 + ρ) / 2) ^ j)⁻¹ * ρ ^ j ≤ 4 / (1 - ρ) ^ 2 := by
  have hr0 : 0 < (1 + ρ) / 2 := by linarith
  have hr1 : (1 + ρ) / 2 < 1 := by linarith
  have hρr : ρ ≤ ((1 + ρ) / 2) ^ 2 := by nlinarith [sq_nonneg (1 - ρ)]
  have h1r : 0 < 1 - (1 + ρ) / 2 := by linarith
  calc ∑ j ∈ range k, (1 - (1 + ρ) / 2)⁻¹ * (((1 + ρ) / 2) ^ j)⁻¹ * ρ ^ j
      ≤ ∑ j ∈ range k, (1 - (1 + ρ) / 2)⁻¹ * ((1 + ρ) / 2) ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 h1r.le)
        have hpj : 0 < ((1 + ρ) / 2) ^ j := pow_pos hr0 j
        rw [inv_mul_le_iff₀ hpj, ← pow_add, ← two_mul, pow_mul]
        exact pow_le_pow_left₀ hρ0 hρr j
    _ = (1 - (1 + ρ) / 2)⁻¹ * ∑ j ∈ range k, ((1 + ρ) / 2) ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ (1 - (1 + ρ) / 2)⁻¹ * (1 - (1 + ρ) / 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (geom_sum_le_of_lt_one hr0.le hr1 k) (inv_nonneg.2 h1r.le)
    _ = 4 / (1 - ρ) ^ 2 := by
        have h2 : (1 - (1 + ρ) / 2)⁻¹ = 2 / (1 - ρ) := by
          rw [show 1 - (1 + ρ) / 2 = (1 - ρ) / 2 by ring, inv_div]
        rw [h2, div_mul_div_comm, sq]
        norm_num

/-- **The distance travelled from the start is bounded uniformly** (Giles 2015, §10.1).  With the
hypotheses of `lintegral_dist_backIter_le` for `p = 2γ`, `0 < γ ≤ 1` and `0 ≤ ρ < 1`, the chain
started `k` steps before time `−m` at `x₀` satisfies
`E[d(x₀, X)^{2γ}] ≤ 4c/(1 − ρ)²` with `c = E[d(x₀, φ(x₀, ξ))^{2γ}]`, whatever `k` and `m`. -/
theorem lintegral_dist_start_le (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α) (k m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (dist x₀ (backIter φ k (fun j => ξ (j + m) ω) x₀) ^ (2 * γ)) ∂μ ≤
      ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
        ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν := by
  have hr0 : 0 < (1 + ρ) / 2 := by linarith
  have hr1 : (1 + ρ) / 2 < 1 := by linarith
  have h1r : 0 < 1 - (1 + ρ) / 2 := by linarith
  -- the weights `c_j = (1 − r)⁻¹ r^{−j}`
  have hc : ∀ j : ℕ, 0 ≤ (1 - (1 + ρ) / 2)⁻¹ * (((1 + ρ) / 2) ^ j)⁻¹ := fun j =>
    mul_nonneg (inv_nonneg.2 h1r.le) (inv_nonneg.2 (pow_pos hr0 j).le)
  -- the path started at `x₀`, and its increments
  have hY : ∀ j, Measurable fun ω => backIter φ j (fun i => ξ (i + m) ω) x₀ := fun j =>
    (measurable_backIter_shift hφm ξ j m (U := fun _ => x₀) measurable_const).mono
      (noiseFrom_le hξm _) le_rfl
  have hDm : ∀ j, Measurable fun ω => ENNReal.ofReal
      (dist (backIter φ j (fun i => ξ (i + m) ω) x₀)
        (backIter φ (j + 1) (fun i => ξ (i + m) ω) x₀) ^ (2 * γ)) := fun j =>
    (((hY j).dist (hY (j + 1))).pow_const _).ennreal_ofReal
  have hφx : Measurable fun e : E => φ x₀ e := hφm.comp measurable_prodMk_left
  -- each increment contracts: `E[D_j^{2γ}] ≤ ρ^j c`
  have hDj : ∀ j, ∫⁻ ω, ENNReal.ofReal (dist (backIter φ j (fun i => ξ (i + m) ω) x₀)
      (backIter φ (j + 1) (fun i => ξ (i + m) ω) x₀) ^ (2 * γ)) ∂μ ≤
      ENNReal.ofReal ρ ^ j * ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν := by
    intro j
    have hV : Measurable[noiseFrom ξ (m + j)] fun ω => φ x₀ (ξ (j + m) ω) :=
      hφx.comp (measurable_noise ξ (by omega : m + j ≤ j + m))
    have h := lintegral_dist_backIter_le hφm hφ hξ hξm hlaw j m (U := fun _ => x₀)
      measurable_const hV
    have hlaw' : ∫⁻ ω, ENNReal.ofReal (dist x₀ (φ x₀ (ξ (j + m) ω)) ^ (2 * γ)) ∂μ =
        ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν := by
      rw [← hlaw (j + m), lintegral_map _ (hξm (j + m))]
      exact ((measurable_const.dist hφx).pow_const _).ennreal_ofReal
    rw [← hlaw']
    refine (lintegral_congr fun ω => ?_).trans_le h
    rw [backIter_succ' φ j (fun i => ξ (i + m) ω) x₀]
  -- the pointwise bound, integrated
  have hpt : ∀ ω, ENNReal.ofReal (dist x₀ (backIter φ k (fun j => ξ (j + m) ω) x₀) ^ (2 * γ)) ≤
      ∑ j ∈ range k, ENNReal.ofReal ((1 - (1 + ρ) / 2)⁻¹ * (((1 + ρ) / 2) ^ j)⁻¹) *
        ENNReal.ofReal (dist (backIter φ j (fun i => ξ (i + m) ω) x₀)
          (backIter φ (j + 1) (fun i => ξ (i + m) ω) x₀) ^ (2 * γ)) := by
    intro ω
    have hsum := dist_le_range_sum_dist (fun j => backIter φ j (fun i => ξ (i + m) ω) x₀) k
    have h := rpow_two_mul_le_sum hγ0 hγ1 hr0 hr1
      (fun j => dist (backIter φ j (fun i => ξ (i + m) ω) x₀)
        (backIter φ (j + 1) (fun i => ξ (i + m) ω) x₀))
      (fun j => dist_nonneg) k dist_nonneg hsum
    refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg]
    · exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_mul (hc j)
    · exact fun j _ => mul_nonneg (hc j) (Real.rpow_nonneg dist_nonneg _)
  calc ∫⁻ ω, ENNReal.ofReal (dist x₀ (backIter φ k (fun j => ξ (j + m) ω) x₀) ^ (2 * γ)) ∂μ
      ≤ ∫⁻ ω, ∑ j ∈ range k, ENNReal.ofReal ((1 - (1 + ρ) / 2)⁻¹ * (((1 + ρ) / 2) ^ j)⁻¹) *
          ENNReal.ofReal (dist (backIter φ j (fun i => ξ (i + m) ω) x₀)
            (backIter φ (j + 1) (fun i => ξ (i + m) ω) x₀) ^ (2 * γ)) ∂μ := lintegral_mono hpt
    _ = ∑ j ∈ range k, ENNReal.ofReal ((1 - (1 + ρ) / 2)⁻¹ * (((1 + ρ) / 2) ^ j)⁻¹) *
          ∫⁻ ω, ENNReal.ofReal (dist (backIter φ j (fun i => ξ (i + m) ω) x₀)
            (backIter φ (j + 1) (fun i => ξ (i + m) ω) x₀) ^ (2 * γ)) ∂μ := by
        rw [lintegral_finsetSum]
        · exact Finset.sum_congr rfl fun j _ => lintegral_const_mul _ (hDm j)
        · exact fun j _ => (hDm j).const_mul _
    _ ≤ ∑ j ∈ range k, ENNReal.ofReal ((1 - (1 + ρ) / 2)⁻¹ * (((1 + ρ) / 2) ^ j)⁻¹) *
          (ENNReal.ofReal ρ ^ j * ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hDj j) zero_le
    _ = ENNReal.ofReal (∑ j ∈ range k,
          (1 - (1 + ρ) / 2)⁻¹ * (((1 + ρ) / 2) ^ j)⁻¹ * ρ ^ j) *
          ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν := by
        rw [ENNReal.ofReal_sum_of_nonneg, Finset.sum_mul]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_mul (hc j), ENNReal.ofReal_pow hρ0, mul_assoc]
        · exact fun j _ => mul_nonneg (hc j) (pow_nonneg hρ0 j)
    _ ≤ ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
          ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (sum_weight_pow_le hρ0 hρ1 k))
          zero_le

/-- **The multilevel correction of Giles 2015, §10.1 is small** (in the `2γ`-th moment of the
distance).  With the hypotheses of `lintegral_dist_start_le`, let the level `ℓ` path start
`N ≥ N'` steps in the past and the level `ℓ − 1` path `N'` steps in the past, both at `x₀` and
sharing the noises `ξ_0, …, ξ_{N'−1}`.  Then
`E[d(X^{(ℓ)}, X^{(ℓ−1)})^{2γ}] ≤ ρ^{N'} · 4c/(1 − ρ)²`, `c = E[d(x₀, φ(x₀, ξ))^{2γ}]`. -/
theorem lintegral_dist_levels_le (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α) {N N' : ℕ}
    (hN : N' ≤ N) :
    ∫⁻ ω, ENNReal.ofReal (dist (backIter φ N (fun k => ξ k ω) x₀)
        (backIter φ N' (fun k => ξ k ω) x₀) ^ (2 * γ)) ∂μ ≤
      ENNReal.ofReal ρ ^ N' * (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
        ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν) := by
  -- the level `ℓ` path is the level `ℓ − 1` path started from `Y`
  have hsplit : ∀ ω, backIter φ N (fun k => ξ k ω) x₀ =
      backIter φ N' (fun k => ξ k ω) (backIter φ (N - N') (fun k => ξ (k + N') ω) x₀) := by
    intro ω
    have h := backIter_add φ (N - N') N' (fun k => ξ k ω) x₀
    rw [Nat.sub_add_cancel hN] at h
    exact h
  have hY : Measurable[noiseFrom ξ (0 + N')]
      fun ω => backIter φ (N - N') (fun k => ξ (k + N') ω) x₀ := by
    rw [zero_add]
    exact measurable_backIter_shift hφm ξ (N - N') N' (U := fun _ => x₀) measurable_const
  have h := lintegral_dist_backIter_le hφm hφ hξ hξm hlaw N' 0 hY (V := fun _ => x₀)
    measurable_const
  have hstart := lintegral_dist_start_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ (N - N') N'
  calc ∫⁻ ω, ENNReal.ofReal (dist (backIter φ N (fun k => ξ k ω) x₀)
          (backIter φ N' (fun k => ξ k ω) x₀) ^ (2 * γ)) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (dist (backIter φ N' (fun k => ξ k ω)
            (backIter φ (N - N') (fun k => ξ (k + N') ω) x₀))
          (backIter φ N' (fun k => ξ k ω) x₀) ^ (2 * γ)) ∂μ :=
        lintegral_congr fun ω => by rw [hsplit ω]
    _ ≤ ENNReal.ofReal ρ ^ N' * ∫⁻ ω, ENNReal.ofReal
          (dist (backIter φ (N - N') (fun k => ξ (k + N') ω) x₀) x₀ ^ (2 * γ)) ∂μ := h
    _ = ENNReal.ofReal ρ ^ N' * ∫⁻ ω, ENNReal.ofReal
          (dist x₀ (backIter φ (N - N') (fun k => ξ (k + N') ω) x₀) ^ (2 * γ)) ∂μ := by
        congr 1
        exact lintegral_congr fun ω => by rw [dist_comm]
    _ ≤ ENNReal.ofReal ρ ^ N' * (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
          ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν) :=
        mul_le_mul_of_nonneg_left hstart zero_le

/-- **Giles 2015, §10.1: "a coupling with a multilevel correction variance which decays as `ℓ`
increases".**  With the hypotheses of `lintegral_dist_levels_le`, let `f` be Hölder continuous with
exponent `γ`, `|f(y) − f(x)| ≤ d(x, y)^γ`, and `c = E[d(x₀, φ(x₀, ξ))^{2γ}] < ∞`.  The multilevel
correction `P_ℓ − P_{ℓ−1} = f(X^{(ℓ)}) − f(X^{(ℓ−1)})`, with the level `ℓ` path started `N` steps
and the level `ℓ − 1` path `N' ≤ N` steps in the past, has variance at most
`4c/(1 − ρ)² · ρ^{N'}`: it decays exponentially in the number `N'` of shared steps. -/
theorem variance_levels_le (hφm : Measurable fun q : α × E => φ q.1 q.2) {γ ρ : ℝ}
    (hφ : ∀ x y, ∫⁻ e, ENNReal.ofReal (dist (φ x e) (φ y e) ^ (2 * γ)) ∂ν ≤
      ENNReal.ofReal ρ * ENNReal.ofReal (dist x y ^ (2 * γ)))
    (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, μ.map (ξ i) = ν)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x₀ : α)
    (hc : ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν ≠ ∞)
    {f : α → ℝ} (hfm : Measurable f) (hf : ∀ x y, |f x - f y| ≤ dist x y ^ γ) {N N' : ℕ}
    (hN : N' ≤ N) :
    variance (fun ω => f (backIter φ N (fun k => ξ k ω) x₀) -
        f (backIter φ N' (fun k => ξ k ω) x₀)) μ ≤
      4 / (1 - ρ) ^ 2 * (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal *
        ρ ^ N' := by
  have hX : ∀ n, Measurable fun ω => backIter φ n (fun k => ξ k ω) x₀ := fun n =>
    (measurable_backIter_shift hφm ξ n 0 (U := fun _ => x₀) measurable_const).mono
      (noiseFrom_le hξm _) le_rfl
  have hΔm : Measurable fun ω => f (backIter φ N (fun k => ξ k ω) x₀) -
      f (backIter φ N' (fun k => ξ k ω) x₀) := (hfm.comp (hX N)).sub (hfm.comp (hX N'))
  have hlev := lintegral_dist_levels_le hφm hφ hξ hξm hlaw hγ0 hγ1 hρ0 hρ1 x₀ hN
  have hfin : ENNReal.ofReal ρ ^ N' * (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
      ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc)
  have hpt : ∀ ω, ENNReal.ofReal ((f (backIter φ N (fun k => ξ k ω) x₀) -
      f (backIter φ N' (fun k => ξ k ω) x₀)) ^ 2) ≤
      ENNReal.ofReal (dist (backIter φ N (fun k => ξ k ω) x₀)
        (backIter φ N' (fun k => ξ k ω) x₀) ^ (2 * γ)) := by
    intro ω
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hf (backIter φ N (fun k => ξ k ω) x₀) (backIter φ N' (fun k => ξ k ω) x₀)
    rw [mul_comm, Real.rpow_mul dist_nonneg, Real.rpow_two, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc variance (fun ω => f (backIter φ N (fun k => ξ k ω) x₀) -
        f (backIter φ N' (fun k => ξ k ω) x₀)) μ
      ≤ ∫ ω, (f (backIter φ N (fun k => ξ k ω) x₀) -
          f (backIter φ N' (fun k => ξ k ω) x₀)) ^ 2 ∂μ :=
        variance_le_expectation_sq hΔm.aestronglyMeasurable
    _ = (∫⁻ ω, ENNReal.ofReal ((f (backIter φ N (fun k => ξ k ω) x₀) -
          f (backIter φ N' (fun k => ξ k ω) x₀)) ^ 2) ∂μ).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
          (hΔm.pow_const 2).aestronglyMeasurable
    _ ≤ (ENNReal.ofReal ρ ^ N' * (ENNReal.ofReal (4 / (1 - ρ) ^ 2) *
          ∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν)).toReal :=
        ENNReal.toReal_mono hfin ((lintegral_mono hpt).trans hlev)
    _ = 4 / (1 - ρ) ^ 2 * (∫⁻ e, ENNReal.ofReal (dist x₀ (φ x₀ e) ^ (2 * γ)) ∂ν).toReal *
          ρ ^ N' := by
        have h4 : 0 ≤ 4 / (1 - ρ) ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal hρ0, ENNReal.toReal_ofReal h4]
        ring

end contraction

/-! ### The example `X_{n+1} = X_n/2 + ξ_n` -/

section halfStepChain

/-- One step of the example chain of Giles 2015, §10.1: `φ(x, ξ) = x/2 + ξ`. -/
noncomputable def halfStep (x e : ℝ) : ℝ := x / 2 + e

/-- The law of `ξ_n` in the example of Giles 2015, §10.1: `P(ξ_n = 0) = P(ξ_n = 1) = ½`. -/
noncomputable def fairCoin : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 + (2⁻¹ : ℝ≥0∞) • Measure.dirac 1

/-- The uniform distribution on `[0, 2]` (Giles 2015, §10.1), with density `½` on `(0, 2]`. -/
noncomputable def uniform02 : Measure ℝ := (2⁻¹ : ℝ≥0∞) • volume.restrict (Set.Ioc 0 2)

/-- `fairCoin` is a probability measure. -/
lemma fairCoin_univ : fairCoin Set.univ = 1 := by
  rw [fairCoin, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    measure_univ, smul_eq_mul, mul_one, ENNReal.inv_two_add_inv_two]

/-- `uniform02` is a probability measure. -/
lemma uniform02_univ : uniform02 Set.univ = 1 := by
  rw [uniform02, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul,
    sub_zero, ENNReal.ofReal_ofNat, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

lemma measurable_halfStep : Measurable fun q : ℝ × ℝ => halfStep q.1 q.2 := by
  unfold halfStep
  fun_prop

/-- **The example contracts on average** (Giles 2015, §10.1: "An example they offer of a chain
satisfying the required conditions"): `d(φ(x, ξ), φ(y, ξ)) = d(x, y)/2` for every `ξ`, so
`E[d(φ(x, ξ), φ(y, ξ))^p] = 2^{−p} d(x, y)^p` and the condition holds with `ρ = 2^{−2γ} < 1`. -/
theorem lintegral_dist_halfStep (p x y : ℝ) :
    ∫⁻ e, ENNReal.ofReal (dist (halfStep x e) (halfStep y e) ^ p) ∂fairCoin =
      ENNReal.ofReal ((1 / 2) ^ p) * ENNReal.ofReal (dist x y ^ p) := by
  have h : ∀ e, dist (halfStep x e) (halfStep y e) = 1 / 2 * dist x y := by
    intro e
    rw [Real.dist_eq, Real.dist_eq, halfStep, halfStep,
      show x / 2 + e - (y / 2 + e) = 1 / 2 * (x - y) by ring, abs_mul, abs_of_pos (by norm_num)]
  simp only [h]
  rw [lintegral_const, fairCoin_univ, mul_one, Real.mul_rpow (by norm_num) dist_nonneg,
    ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]

/-- The rate of the example: `2^{−2γ} < 1` for `γ > 0`. -/
lemma half_rpow_lt_one {γ : ℝ} (hγ : 0 < γ) : ((1 : ℝ) / 2) ^ (2 * γ) < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)

/-- `(vol|(0, 2]) ∘ (x ↦ x/2 + b)⁻¹ = 2 vol|(b, b + 1]`. -/
lemma map_restrict_halfStep (b : ℝ) :
    (volume.restrict (Set.Ioc (0 : ℝ) 2)).map (fun x => halfStep x b) =
      (2 : ℝ≥0∞) • volume.restrict (Set.Ioc b (b + 1)) := by
  have hm : Measurable fun x : ℝ => halfStep x b := by
    unfold halfStep
    fun_prop
  ext s hs
  rw [Measure.map_apply hm hs, Measure.restrict_apply (hm hs), Measure.smul_apply,
    Measure.restrict_apply hs, smul_eq_mul]
  have hset : (fun x => halfStep x b) ⁻¹' s ∩ Set.Ioc 0 2 =
      (fun x : ℝ => 2⁻¹ * x) ⁻¹' ((fun y => y + b) ⁻¹' (s ∩ Set.Ioc b (b + 1))) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc, halfStep]
    constructor
    · rintro ⟨hx, h0, h2⟩
      refine ⟨by rwa [show 2⁻¹ * x + b = x / 2 + b by ring], by linarith, by linarith⟩
    · rintro ⟨hx, h0, h2⟩
      refine ⟨by rwa [show x / 2 + b = 2⁻¹ * x + b by ring], by linarith, by linarith⟩
  rw [hset, Real.volume_preimage_mul_left (by norm_num), measure_preimage_add_right]
  norm_num

/-- **The invariant distribution of the example is uniform on `[0, 2]`** (Giles 2015, §10.1: "The
invariant distribution in this case is the uniform distribution on `[0, 2]`"): mixing the images
of `U[0, 2]` under `x ↦ x/2` and `x ↦ x/2 + 1` with weights `½, ½` gives back `U[0, 2]`. -/
theorem halfStep_invariant :
    (2⁻¹ : ℝ≥0∞) • uniform02.map (fun x => halfStep x 0) +
      (2⁻¹ : ℝ≥0∞) • uniform02.map (fun x => halfStep x 1) = uniform02 := by
  have hb : ∀ b : ℝ,
      uniform02.map (fun x => halfStep x b) = volume.restrict (Set.Ioc b (b + 1)) := by
    intro b
    rw [uniform02, Measure.map_smul, map_restrict_halfStep, smul_smul,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_smul]
  rw [hb, hb, zero_add, show (1 : ℝ) + 1 = 2 by norm_num, ← smul_add,
    ← Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
    Set.Ioc_union_Ioc_eq_Ioc zero_le_one one_le_two, uniform02]

/-- **The uniform distribution on `[0, 2]` is invariant for `X_{n+1} = X_n/2 + ξ_n`** (Giles 2015,
§10.1): if `X` has the law `U[0, 2]` and `ξ`, independent of `X`, takes the values `0` and `1`
with probability `½` each, then `X/2 + ξ` again has the law `U[0, 2]`. -/
theorem map_halfStep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X ξ : Ω → ℝ} (hX : Measurable X) (hξ : Measurable ξ) (hind : IndepFun ξ X μ)
    (hlawX : μ.map X = uniform02) (hlawξ : μ.map ξ = fairCoin) :
    μ.map (fun ω => halfStep (X ω) (ξ ω)) = uniform02 := by
  have : IsProbabilityMeasure uniform02 := ⟨uniform02_univ⟩
  have hg : Measurable fun q : ℝ × ℝ => halfStep q.2 q.1 :=
    measurable_halfStep.comp (measurable_snd.prodMk measurable_fst)
  have hjoint : μ.map (fun ω => (ξ ω, X ω)) = fairCoin.prod uniform02 := by
    rw [← hlawX, ← hlawξ]
    exact (indepFun_iff_map_prod_eq_prod_map_map hξ.aemeasurable hX.aemeasurable).1 hind
  have hcomp : (fun ω => halfStep (X ω) (ξ ω)) =
      (fun q : ℝ × ℝ => halfStep q.2 q.1) ∘ fun ω => (ξ ω, X ω) := rfl
  have hd : ∀ b : ℝ, ((Measure.dirac b).prod uniform02).map (fun q : ℝ × ℝ => halfStep q.2 q.1) =
      uniform02.map (fun x => halfStep x b) := by
    intro b
    rw [Measure.dirac_prod, Measure.map_map hg measurable_prodMk_left]
    rfl
  rw [hcomp, ← Measure.map_map hg (hξ.prodMk hX), hjoint, fairCoin, Measure.add_prod,
    Measure.prod_smul_left, Measure.prod_smul_left, Measure.map_add _ _ hg, Measure.map_smul,
    Measure.map_smul, hd, hd, halfStep_invariant]

end halfStepChain

end MLMC
