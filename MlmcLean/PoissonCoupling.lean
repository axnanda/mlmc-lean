import MlmcLean.Allocation
import MlmcLean.Complexity
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.LinearCombination

/-!
# Continuous-time Markov chains: the Poisson coupling of tau-leaping (Giles 2015, §8)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §8
"Continuous-time Markov chains" (pp. 55–56 of the author's version), after Anderson and Higham
(2012).

**The scheme.**  With one reaction, "the 'tau-leaping' method … gives the discrete equation
`x_{n+1} = x_n + P(hλ(x_n))`, where `h` is the timestep, `λ(x_n)` is the reaction rate (or
propensity function), and `P(t)` represents a unit-rate Poisson random variable over time interval
`[0, t]`.  If this equation defines the fine path in the multilevel simulation, then the coarse
path, with double the timestep, is given by `x^c_{n+2} = x^c_n + P(2hλ(x^c_n))` for even
timesteps `n`."  Here the state is a count `x ∈ ℕ` and `λ : ℕ → [0, ∞)`; the law of the chain after
`n` steps is `tauChain λ h x₀ n` (each step `tauStep`).

**The coupling.**  "for any `t₁, t₂ > 0`, the sum of two independent Poisson variates `P(t₁)`,
`P(t₂)` is equivalent in distribution to `P(t₁ + t₂)`" (`poisson_add_hasLaw`).  "the first step is
to express the coarse path Poisson variate as the sum of two Poisson variates, `P(hλ(x^c_n))`
corresponding to the first and second fine path timesteps.  For the first of the two fine
timesteps, the coarse and fine path Poisson variates are coupled by defining two Poisson variates
based on the minimum of the two reactions rates, and the absolute difference,
`P₁ = P(h min(λ(x_n), λ(x^c_n)))`, `P₂ = P(h|λ(x_n) − λ(x^c_n)|)`, and then using `P₁` as the
Poisson variate for the path with the smaller rate, and `P₁ + P₂` for the path with the larger
rate."
* `couplePair`, `coupledIncr`: the coupled increments and their joint law; each path gets the
  correct Poisson increment (`coupledIncr_fst`, `coupledIncr_snd`, `coupled_increments_hasLaw`),
  and "This elegant approach naturally gives a small difference in the Poisson variates when the
  difference in rates is small": the increments differ by `P₂`, so
  `E[(I − I^c)²] = h|Δλ| + (h|Δλ|)²` (`integral_sq_coupledIncr_sub`, from the Poisson moments
  `integral_poissonMeasure_id`, `integral_sq_poissonMeasure`).
* `coupledTwoStep`: two coupled fine steps from `(x_n, x^c_n)`, the coarse rate frozen at
  `λ(x^c_n)`.  The fine component makes two fine steps (`coupledTwoStep_fst`), and the coarse
  component makes exactly one coarse step `x^c_n + P(2hλ(x^c_n))` (`coupledTwoStep_snd`).
* `coupledChain`: the coupled pair of paths.  Its fine path has the law of the fine tau-leaping
  chain and its coarse path the law of the coarse chain with double the timestep
  (`coupledChain_fst`, `coupledChain_snd`); hence (2.4), `E[P^f_ℓ] = E[P^c_ℓ]`, for every payoff
  of the terminal state (`tauLeaping_2_4`, `tauLeaping_level`).

**The correction variance.**  "a very effective multilevel algorithm with a correction variance
which is `O(h)`": for a Lipschitz, bounded propensity the coupled paths are `O(h)` apart in mean
square (`lintegral_sq_coupledIncr_le`, `lintegral_sq_coupledTwoStep_le`,
`lintegral_sq_coupledChain_le`, `coupledChain_sq_le`), so the correction of a Lipschitz payoff has
variance `O(h)` (`variance_coupledChain_le`), `O(2^{−ℓ})` on level `ℓ + 1`
(`tauLeaping_level_variance`): `β = 1`.

**Complexity.**  "a correction variance which is `O(h)`, leading to an `O(ε⁻²(log ε)²)` complexity"
(`tauLeaping_complexity`: `α = β = γ = 1`); with an exact finest level "their overall multilevel
estimator is unbiased … and the complexity is reduced to `O(ε⁻²)` because the number of levels
remains fixed as `ε → 0`" (`fixed_levels_cost`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace MLMC

/-! ### Measures on discrete spaces -/

section Discrete

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Pushing forward a composition of measures: on a discrete space of states,
`(μ.bind κ).map f = μ.bind (fun a ↦ (κ a).map f)`. -/
lemma map_bind_of_discrete [DiscreteMeasurableSpace α] (μ : Measure α) (κ : α → Measure β)
    {f : β → γ} (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind fun a => (κ a).map f := by
  ext s hs
  rw [Measure.map_apply hf hs,
    Measure.bind_apply (hf hs) (Measurable.of_discrete (f := κ)).aemeasurable,
    Measure.bind_apply hs (Measurable.of_discrete (f := fun a => (κ a).map f)).aemeasurable]
  exact lintegral_congr fun a => (Measure.map_apply hf hs).symm

/-- Composition after a push-forward on discrete spaces:
`(μ.map g).bind κ = μ.bind (fun a ↦ κ (g a))`. -/
lemma bind_map_of_discrete [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    (μ : Measure α) (g : α → β) (κ : β → Measure γ) :
    (μ.map g).bind κ = μ.bind fun a => κ (g a) := by
  ext s hs
  rw [Measure.bind_apply hs (Measurable.of_discrete (f := κ)).aemeasurable,
    Measure.bind_apply hs (Measurable.of_discrete (f := fun a => κ (g a))).aemeasurable,
    lintegral_map (Measurable.of_discrete (f := fun b => κ b s)) (Measurable.of_discrete (f := g))]

/-- Adding an independent variate: `μ.bind (j ↦ ν.map (k ↦ c + j + k))` is the convolution
`μ ∗ ν` shifted by `c`. -/
lemma bind_map_add_eq_conv (μ ν : Measure ℕ) [SFinite ν] (c : ℕ) :
    (μ.bind fun j => ν.map fun k => c + j + k) = (μ ∗ ν).map (c + ·) := by
  ext s hs
  rw [Measure.bind_apply hs
      (Measurable.of_discrete (f := fun j : ℕ => ν.map fun k => c + j + k)).aemeasurable,
    Measure.map_apply (Measurable.of_discrete (f := fun n : ℕ => c + n)) hs, Measure.conv,
    Measure.map_apply (Measurable.of_discrete (f := fun x : ℕ × ℕ => x.1 + x.2))
      MeasurableSet.of_discrete,
    Measure.prod_apply MeasurableSet.of_discrete]
  refine lintegral_congr fun j => ?_
  rw [Measure.map_apply (Measurable.of_discrete (f := fun k : ℕ => c + j + k)) hs]
  congr 1
  ext k
  simp [add_assoc]

end Discrete

/-! ### Poisson variates -/

/-- **The sum of independent Poisson variates** (Giles 2015, §8, p. 55: "for any `t₁, t₂ > 0`, the
sum of two independent Poisson variates `P(t₁)`, `P(t₂)` is equivalent in distribution to
`P(t₁ + t₂)`"). -/
theorem poisson_add_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {t₁ t₂ : ℝ≥0}
    {X Y : Ω → ℕ} (hXY : IndepFun X Y μ) (hX : HasLaw X (poissonMeasure t₁) μ)
    (hY : HasLaw Y (poissonMeasure t₂) μ) : HasLaw (X + Y) (poissonMeasure (t₁ + t₂)) μ :=
  hXY.hasLaw_add_poissonMeasure hX hY

/-- Two independent Poisson variates added, shifted by `c` (Giles 2015, §8). -/
lemma poisson_bind_shift (r : ℝ≥0) (c : ℕ) :
    ((poissonMeasure r).bind fun j => (poissonMeasure r).map fun k => c + j + k) =
      (poissonMeasure (r + r)).map (c + ·) := by
  rw [bind_map_add_eq_conv, poissonMeasure_conv_poissonMeasure]

/-- `P(n + 1) (n + 1) = r P(n)` for the Poisson weights `P(n) = e^{−r} rⁿ/n!`. -/
lemma poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    Real.exp (-r) * (r : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n : ℝ) + 1) =
      r * (Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ)) := by
  have h1 : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) = 1 := inv_mul_cancel₀ (by positivity)
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (Real.exp (-r) * (r : ℝ) ^ (n + 1) * ((n.factorial : ℝ))⁻¹) * h1

lemma hasSum_poissonWeight_mul_id (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) * n) r := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero,
    Nat.cast_add, Nat.cast_one]
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [mul_one] at h
  exact h.congr_fun fun n => poissonWeight_succ_mul r n

lemma hasSum_poissonWeight_mul_descFactorial (r : ℝ≥0) :
    HasSum (fun n : ℕ =>
      Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) * ((n : ℝ) * ((n : ℝ) - 1)))
      ((r : ℝ) ^ 2) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, mul_zero, sub_zero,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have h := (hasSum_poissonWeight_mul_id r).mul_left (r : ℝ)
  rw [show (r : ℝ) * r = (r : ℝ) ^ 2 by ring] at h
  exact h.congr_fun fun n => by linear_combination (n : ℝ) * poissonWeight_succ_mul r n

/-- **The mean of a Poisson variate**: `E[P(r)] = r` (used in Giles 2015, §8). -/
theorem integral_poissonMeasure_id (r : ℝ≥0) : ∫ n, (n : ℝ) ∂(poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact (hasSum_poissonWeight_mul_id r).tsum_eq

/-- **The second moment of a Poisson variate**: `E[P(r)²] = r + r²` (used in Giles 2015, §8). -/
theorem integral_sq_poissonMeasure (r : ℝ≥0) :
    ∫ n, (n : ℝ) ^ 2 ∂(poissonMeasure r) = r + (r : ℝ) ^ 2 := by
  have h : HasSum (fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2)
      ((r : ℝ) + (r : ℝ) ^ 2) := by
    convert (hasSum_poissonWeight_mul_id r).add (hasSum_poissonWeight_mul_descFactorial r) using 1
    funext n
    ring
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact h.tsum_eq

/-! ### The coupled increments -/

/-- **The coupled increments** (Giles 2015, §8, p. 55, after Anderson and Higham): from
`P₁ ~ P(min(a, b))` and `P₂ ~ P(|a − b|)`, "using `P₁` as the Poisson variate for the path with the
smaller rate, and `P₁ + P₂` for the path with the larger rate".  `couplePair a b (P₁, P₂)` is the
pair of increments of the paths with rates `a` and `b`. -/
noncomputable def couplePair (a b : ℝ≥0) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + (if b < a then p.2 else 0), p.1 + (if a < b then p.2 else 0))

/-- The joint law of the coupled increments (Giles 2015, §8): the image of
`P(min(a, b)) ⊗ P(|a − b|)` under `couplePair a b` (for rates in `ℝ≥0`, `|a − b| = max − min`). -/
noncomputable def coupledIncr (a b : ℝ≥0) : Measure (ℕ × ℕ) :=
  ((poissonMeasure (min a b)).prod (poissonMeasure (max a b - min a b))).map (couplePair a b)

/-- `max a b − min a b = |a − b|` for rates. -/
lemma coe_max_sub_min (a b : ℝ≥0) : ((max a b - min a b : ℝ≥0) : ℝ) = |(a : ℝ) - b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, NNReal.coe_sub h, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))]
  · rw [max_eq_left h, min_eq_right h, NNReal.coe_sub h,
      abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))]

/-- **The path with rate `a` gets a `P(a)` increment** (Giles 2015, §8): the first marginal of the
coupled increments is `P(a)`. -/
theorem coupledIncr_fst (a b : ℝ≥0) : (coupledIncr a b).map Prod.fst = poissonMeasure a := by
  unfold coupledIncr
  rw [Measure.map_map measurable_fst Measurable.of_discrete]
  by_cases h : b < a
  · have e : Prod.fst ∘ couplePair a b = fun p : ℕ × ℕ => p.1 + p.2 := by
      funext p
      simp [couplePair, h]
    rw [e, min_eq_right h.le, max_eq_left h.le]
    have hconv := poissonMeasure_conv_poissonMeasure b (a - b)
    rw [add_tsub_cancel_of_le h.le] at hconv
    exact hconv
  · have e : Prod.fst ∘ couplePair a b = Prod.fst := by
      funext p
      simp [couplePair, h]
    push Not at h
    rw [e, Measure.map_fst_prod, measure_univ, one_smul, min_eq_left h]

/-- **The path with rate `b` gets a `P(b)` increment** (Giles 2015, §8): the second marginal of the
coupled increments is `P(b)`. -/
theorem coupledIncr_snd (a b : ℝ≥0) : (coupledIncr a b).map Prod.snd = poissonMeasure b := by
  unfold coupledIncr
  rw [Measure.map_map measurable_snd Measurable.of_discrete]
  by_cases h : a < b
  · have e : Prod.snd ∘ couplePair a b = fun p : ℕ × ℕ => p.1 + p.2 := by
      funext p
      simp [couplePair, h]
    rw [e, min_eq_left h.le, max_eq_right h.le]
    have hconv := poissonMeasure_conv_poissonMeasure a (b - a)
    rw [add_tsub_cancel_of_le h.le] at hconv
    exact hconv
  · have e : Prod.snd ∘ couplePair a b = Prod.fst := by
      funext p
      simp [couplePair, h]
    push Not at h
    rw [e, Measure.map_fst_prod, measure_univ, one_smul, min_eq_right h]

/-- **The coupling in terms of random variables** (Giles 2015, §8, p. 55: "`P₁ = P(h min(λ(x_n),
λ(x^c_n)))`, `P₂ = P(h|λ(x_n) − λ(x^c_n)|)`, and then using `P₁` as the Poisson variate for the
path with the smaller rate, and `P₁ + P₂` for the path with the larger rate").  For independent
`P₁ ~ P(min(a, b))` and `P₂ ~ P(|a − b|)`, the increment of the path with rate `a` has law `P(a)`
and that of the path with rate `b` has law `P(b)`. -/
theorem coupled_increments_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {P₁ P₂ : Ω → ℕ} {a b : ℝ≥0} (hind : IndepFun P₁ P₂ μ)
    (h₁ : HasLaw P₁ (poissonMeasure (min a b)) μ)
    (h₂ : HasLaw P₂ (poissonMeasure (max a b - min a b)) μ) :
    HasLaw (fun ω => (couplePair a b (P₁ ω, P₂ ω)).1) (poissonMeasure a) μ ∧
      HasLaw (fun ω => (couplePair a b (P₁ ω, P₂ ω)).2) (poissonMeasure b) μ := by
  have hpair : HasLaw (fun ω => (P₁ ω, P₂ ω))
      ((poissonMeasure (min a b)).prod (poissonMeasure (max a b - min a b))) μ :=
    ⟨h₁.aemeasurable.prodMk h₂.aemeasurable, by
      rw [(indepFun_iff_map_prod_eq_prod_map_map h₁.aemeasurable h₂.aemeasurable).1 hind,
        h₁.map_eq, h₂.map_eq]⟩
  have hfst : HasLaw (fun p : ℕ × ℕ => (couplePair a b p).1) (poissonMeasure a)
      ((poissonMeasure (min a b)).prod (poissonMeasure (max a b - min a b))) :=
    ⟨Measurable.of_discrete.aemeasurable, by
      rw [← coupledIncr_fst a b, coupledIncr, Measure.map_map measurable_fst Measurable.of_discrete]
      rfl⟩
  have hsnd : HasLaw (fun p : ℕ × ℕ => (couplePair a b p).2) (poissonMeasure b)
      ((poissonMeasure (min a b)).prod (poissonMeasure (max a b - min a b))) :=
    ⟨Measurable.of_discrete.aemeasurable, by
      rw [← coupledIncr_snd a b, coupledIncr, Measure.map_map measurable_snd Measurable.of_discrete]
      rfl⟩
  exact ⟨hfst.comp hpair, hsnd.comp hpair⟩

/-- **The coupled increments differ little when the rates differ little** (Giles 2015, §8, p. 56:
"This elegant approach naturally gives a small difference in the Poisson variates when the
difference in rates is small").  The two increments differ by `P₂ ~ P(|a − b|)`, so
`E[(I_a − I_b)²] = |a − b| + |a − b|²`. -/
theorem integral_sq_coupledIncr_sub (a b : ℝ≥0) :
    ∫ p, ((p.1 : ℝ) - p.2) ^ 2 ∂(coupledIncr a b) = |(a : ℝ) - b| + |(a : ℝ) - b| ^ 2 := by
  rw [← coe_max_sub_min]
  have hmap : ∫ p, ((p.1 : ℝ) - p.2) ^ 2 ∂(coupledIncr a b) =
      ∫ p, (((couplePair a b p).1 : ℝ) - (couplePair a b p).2) ^ 2
        ∂((poissonMeasure (min a b)).prod (poissonMeasure (max a b - min a b))) :=
    integral_map Measurable.of_discrete.aemeasurable
      (Measurable.of_discrete (f := fun p : ℕ × ℕ => ((p.1 : ℝ) - p.2) ^ 2)).aestronglyMeasurable
  rw [hmap]
  by_cases hab : a = b
  · have e : ∀ p : ℕ × ℕ, (((couplePair a b p).1 : ℝ) - (couplePair a b p).2) ^ 2 = 0 := by
      intro p
      simp [couplePair, hab]
    have hd : max a b - min a b = 0 := by simp [hab]
    simp only [e, integral_zero, hd, NNReal.coe_zero]
    norm_num
  · have e : ∀ p : ℕ × ℕ,
        (((couplePair a b p).1 : ℝ) - (couplePair a b p).2) ^ 2 = ((p.2 : ℕ) : ℝ) ^ 2 := by
      intro p
      rcases lt_or_gt_of_ne hab with h | h
      · simp only [couplePair, if_neg (not_lt.2 h.le), if_pos h, add_zero, Nat.cast_add]
        ring
      · simp only [couplePair, if_pos h, if_neg (not_lt.2 h.le), add_zero, Nat.cast_add]
        ring
    simp_rw [e]
    have h2 : ∫ n : ℕ, (n : ℝ) ^ 2
        ∂(((poissonMeasure (min a b)).prod (poissonMeasure (max a b - min a b))).map Prod.snd) =
        ∫ p : ℕ × ℕ, ((p.2 : ℕ) : ℝ) ^ 2
          ∂((poissonMeasure (min a b)).prod (poissonMeasure (max a b - min a b))) :=
      integral_map measurable_snd.aemeasurable
        (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ) ^ 2)).aestronglyMeasurable
    rw [Measure.map_snd_prod, measure_univ, one_smul] at h2
    rw [← h2, integral_sq_poissonMeasure]

/-! ### Tau-leaping and two coupled fine steps -/

/-- **One tau-leaping step** (Giles 2015, §8, p. 55: "`x_{n+1} = x_n + P(hλ(x_n))`"): the law of
the next state from the state `x`, with time step `h` and rate function `λ`. -/
noncomputable def tauStep (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x : ℕ) : Measure ℕ :=
  (poissonMeasure (h * lam x)).map (x + ·)

/-- The law of the tau-leaping chain with time step `h` after `n` steps, started at `x₀`
(Giles 2015, §8). -/
noncomputable def tauChain (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ : ℕ) : ℕ → Measure ℕ
  | 0 => Measure.dirac x₀
  | n + 1 => (tauChain lam h x₀ n).bind (tauStep lam h)

/-- **Two coupled fine steps** (Giles 2015, §8, p. 55): from the fine state `x` and the coarse
state `y` (the pair `s = (x, y)`), the first fine step couples the rates `hλ(x)` and `hλ(y)`, and
the second couples `hλ(x')` at the new fine state `x'` with the same coarse rate `hλ(y)` — the
coarse path uses "the drift" `λ(x^c_n)` for both halves of its step. -/
noncomputable def coupledTwoStep (lam : ℕ → ℝ≥0) (h : ℝ≥0) (s : ℕ × ℕ) : Measure (ℕ × ℕ) :=
  (coupledIncr (h * lam s.1) (h * lam s.2)).bind fun ij =>
    (coupledIncr (h * lam (s.1 + ij.1)) (h * lam s.2)).map fun ij' =>
      (s.1 + ij.1 + ij'.1, s.2 + ij.2 + ij'.2)

/-- **The fine component of two coupled steps is two fine steps** (Giles 2015, §8). -/
theorem coupledTwoStep_fst (lam : ℕ → ℝ≥0) (h : ℝ≥0) (s : ℕ × ℕ) :
    (coupledTwoStep lam h s).map Prod.fst = (tauStep lam h s.1).bind (tauStep lam h) := by
  have e : ∀ ij : ℕ × ℕ,
      ((coupledIncr (h * lam (s.1 + ij.1)) (h * lam s.2)).map fun ij' =>
        (s.1 + ij.1 + ij'.1, s.2 + ij.2 + ij'.2)).map Prod.fst =
      tauStep lam h (s.1 + ij.1) := by
    intro ij
    rw [Measure.map_map measurable_fst Measurable.of_discrete, tauStep,
      ← coupledIncr_fst (h * lam (s.1 + ij.1)) (h * lam s.2),
      Measure.map_map Measurable.of_discrete measurable_fst]
    rfl
  calc (coupledTwoStep lam h s).map Prod.fst
      = (coupledIncr (h * lam s.1) (h * lam s.2)).bind fun ij => tauStep lam h (s.1 + ij.1) := by
        rw [coupledTwoStep, map_bind_of_discrete _ _ measurable_fst]
        exact congrArg (Measure.bind _) (funext e)
    _ = ((coupledIncr (h * lam s.1) (h * lam s.2)).map Prod.fst).bind fun i =>
          tauStep lam h (s.1 + i) :=
        (bind_map_of_discrete (coupledIncr (h * lam s.1) (h * lam s.2)) Prod.fst
          fun i => tauStep lam h (s.1 + i)).symm
    _ = (tauStep lam h s.1).bind (tauStep lam h) := by
        rw [coupledIncr_fst]
        exact (bind_map_of_discrete (poissonMeasure (h * lam s.1)) (s.1 + ·) (tauStep lam h)).symm

/-- **The coarse component of two coupled steps is one coarse step** (Giles 2015, §8, p. 55: "the
first step is to express the coarse path Poisson variate as the sum of two Poisson variates,
`P(hλ(x^c_n))` corresponding to the first and second fine path timesteps"): the coarse state moves
by `P(hλ(y)) + P(hλ(y)) ~ P(2hλ(y))`, the step `x^c_{n+2} = x^c_n + P(2hλ(x^c_n))` of the coarse
path. -/
theorem coupledTwoStep_snd (lam : ℕ → ℝ≥0) (h : ℝ≥0) (s : ℕ × ℕ) :
    (coupledTwoStep lam h s).map Prod.snd = tauStep lam (2 * h) s.2 := by
  have e : ∀ ij : ℕ × ℕ,
      ((coupledIncr (h * lam (s.1 + ij.1)) (h * lam s.2)).map fun ij' =>
        (s.1 + ij.1 + ij'.1, s.2 + ij.2 + ij'.2)).map Prod.snd =
      (poissonMeasure (h * lam s.2)).map fun k => s.2 + ij.2 + k := by
    intro ij
    rw [Measure.map_map measurable_snd Measurable.of_discrete,
      ← coupledIncr_snd (h * lam (s.1 + ij.1)) (h * lam s.2),
      Measure.map_map Measurable.of_discrete measurable_snd]
    rfl
  calc (coupledTwoStep lam h s).map Prod.snd
      = (coupledIncr (h * lam s.1) (h * lam s.2)).bind fun ij =>
          (poissonMeasure (h * lam s.2)).map fun k => s.2 + ij.2 + k := by
        rw [coupledTwoStep, map_bind_of_discrete _ _ measurable_snd]
        exact congrArg (Measure.bind _) (funext e)
    _ = ((coupledIncr (h * lam s.1) (h * lam s.2)).map Prod.snd).bind fun j =>
          (poissonMeasure (h * lam s.2)).map fun k => s.2 + j + k :=
        (bind_map_of_discrete (coupledIncr (h * lam s.1) (h * lam s.2)) Prod.snd
          fun j => (poissonMeasure (h * lam s.2)).map fun k => s.2 + j + k).symm
    _ = (poissonMeasure (h * lam s.2 + h * lam s.2)).map (s.2 + ·) := by
        rw [coupledIncr_snd, poisson_bind_shift]
    _ = tauStep lam (2 * h) s.2 := by
        rw [tauStep, two_mul, add_mul]

/-! ### The coupled paths and (2.4) -/

/-- The law of the coupled pair `(x_{2k}, x^c_{2k})` after `k` pairs of coupled fine steps from
`(x₀, x₀)` (Giles 2015, §8). -/
noncomputable def coupledChain (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ : ℕ) : ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac (x₀, x₀)
  | k + 1 => (coupledChain lam h x₀ k).bind (coupledTwoStep lam h)

/-- **The fine path of the coupled simulation is the fine tau-leaping chain** (Giles 2015, §8):
after `k` pairs of steps, the fine component has the law of `2k` tau-leaping steps of size `h`. -/
theorem coupledChain_fst (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ k, (coupledChain lam h x₀ k).map Prod.fst = tauChain lam h x₀ (2 * k)
  | 0 => Measure.map_dirac' measurable_fst _
  | k + 1 => by
      calc (coupledChain lam h x₀ (k + 1)).map Prod.fst
          = (coupledChain lam h x₀ k).bind fun s => (coupledTwoStep lam h s).map Prod.fst := by
            rw [coupledChain, map_bind_of_discrete _ _ measurable_fst]
        _ = (coupledChain lam h x₀ k).bind fun s => (tauStep lam h s.1).bind (tauStep lam h) := by
            simp_rw [coupledTwoStep_fst]
        _ = ((coupledChain lam h x₀ k).map Prod.fst).bind fun x =>
              (tauStep lam h x).bind (tauStep lam h) :=
            (bind_map_of_discrete (coupledChain lam h x₀ k) Prod.fst
              fun x => (tauStep lam h x).bind (tauStep lam h)).symm
        _ = ((tauChain lam h x₀ (2 * k)).bind (tauStep lam h)).bind (tauStep lam h) := by
            rw [coupledChain_fst lam h x₀ k,
              Measure.bind_bind (Measurable.of_discrete (f := tauStep lam h)).aemeasurable
                (Measurable.of_discrete (f := tauStep lam h)).aemeasurable]
        _ = tauChain lam h x₀ (2 * (k + 1)) := by
            rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
            rfl

/-- **The coarse path of the coupled simulation is the coarse tau-leaping chain** (Giles 2015, §8,
p. 55: "the coarse path, with double the timestep, is given by
`x^c_{n+2} = x^c_n + P(2hλ(x^c_n))`"):
after `k` pairs of fine steps, the coarse component has the law of `k` tau-leaping steps of size
`2h`. -/
theorem coupledChain_snd (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ k, (coupledChain lam h x₀ k).map Prod.snd = tauChain lam (2 * h) x₀ k
  | 0 => Measure.map_dirac' measurable_snd _
  | k + 1 => by
      calc (coupledChain lam h x₀ (k + 1)).map Prod.snd
          = (coupledChain lam h x₀ k).bind fun s => (coupledTwoStep lam h s).map Prod.snd := by
            rw [coupledChain, map_bind_of_discrete _ _ measurable_snd]
        _ = (coupledChain lam h x₀ k).bind fun s => tauStep lam (2 * h) s.2 := by
            simp_rw [coupledTwoStep_snd]
        _ = ((coupledChain lam h x₀ k).map Prod.snd).bind (tauStep lam (2 * h)) :=
            (bind_map_of_discrete (coupledChain lam h x₀ k) Prod.snd (tauStep lam (2 * h))).symm
        _ = tauChain lam (2 * h) x₀ (k + 1) := by
            rw [coupledChain_snd lam h x₀ k]
            rfl

/-- **The Poisson coupling respects (2.4)** (Giles 2015, §2.1, (2.4), and §8).  For every payoff
`Φ` of the terminal state, the coarse path of the coupled simulation has the expectation of the
coarse chain (time step `2h`, `k` steps), and the fine path that of the fine chain (time step `h`,
`2k` steps).  So the coarse payoff on level `ℓ` has the mean of the fine payoff on level `ℓ − 1`,
and the multilevel telescoping sum is respected. -/
theorem tauLeaping_2_4 (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ k : ℕ) (Φ : ℕ → ℝ) :
    ∫ s, Φ s.2 ∂(coupledChain lam h x₀ k) = ∫ x, Φ x ∂(tauChain lam (2 * h) x₀ k) ∧
      ∫ s, Φ s.1 ∂(coupledChain lam h x₀ k) = ∫ x, Φ x ∂(tauChain lam h x₀ (2 * k)) := by
  constructor
  · rw [← coupledChain_snd, integral_map measurable_snd.aemeasurable
      (Measurable.of_discrete (f := Φ)).aestronglyMeasurable]
  · rw [← coupledChain_fst, integral_map measurable_fst.aemeasurable
      (Measurable.of_discrete (f := Φ)).aestronglyMeasurable]

/-- **(2.4) level by level** (Giles 2015, §8): on level `ℓ + 1` the fine path makes `2^{ℓ+1}` steps
of size `h_{ℓ+1} = T 2^{−(ℓ+1)}` and the coarse path `2^ℓ` steps of size `2h_{ℓ+1} = h_ℓ`, so the
coarse payoff has the law of the level-`ℓ` payoff and the fine payoff that of the level-`(ℓ+1)`
payoff. -/
theorem tauLeaping_level (lam : ℕ → ℝ≥0) (T : ℝ≥0) (x₀ ℓ : ℕ) (Φ : ℕ → ℝ) :
    ∫ s, Φ s.2 ∂(coupledChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ)) =
        ∫ x, Φ x ∂(tauChain lam (T / 2 ^ ℓ) x₀ (2 ^ ℓ)) ∧
      ∫ s, Φ s.1 ∂(coupledChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ)) =
        ∫ x, Φ x ∂(tauChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ (ℓ + 1))) := by
  have hT : 2 * (T / 2 ^ (ℓ + 1)) = T / 2 ^ ℓ := by
    rw [pow_succ (2 : ℝ≥0) ℓ, ← div_div, mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ≥0) ≠ 0)]
  have hk : 2 * 2 ^ ℓ = 2 ^ (ℓ + 1) := (pow_succ' 2 ℓ).symm
  obtain ⟨h1, h2⟩ := tauLeaping_2_4 lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ) Φ
  rw [hT] at h1
  rw [hk] at h2
  exact ⟨h1, h2⟩

/-! ### Complexity -/

/-- **The complexity of tau-leaping MLMC** (Giles 2015, §8, p. 56: "a very effective multilevel
algorithm with a correction variance which is `O(h)`, leading to an `O(ε⁻²(log ε)²)` complexity"):
with `α = β = γ = 1` the bound of Theorem 1 is `ε⁻² (log ε)²`. -/
theorem tauLeaping_complexity (ε : ℝ) :
    complexityBound 1 1 1 ε = ε ^ (-2 : ℝ) * Real.log ε ^ 2 :=
  complexityBound_of_eq rfl ε

/-- **A fixed number of levels gives `O(ε⁻²)`** (Giles 2015, §8, p. 56: with an exact finest level
"their overall multilevel estimator is unbiased … and the complexity is reduced to `O(ε⁻²)` because
the number of levels remains fixed as `ε → 0`").  For a fixed finite set of levels with `V_ℓ > 0`,
`C_ℓ > 0`, there is `c > 0` such that for every `0 < ε ≤ 1` the allocation (1.1), rounded up, has
variance `∑ V_ℓ/N_ℓ ≤ ε²` (the MSE of an unbiased estimator) and cost `∑ N_ℓ C_ℓ ≤ c ε⁻²`. -/
theorem fixed_levels_cost {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {V C : ι → ℝ}
    (hV : ∀ i ∈ s, 0 < V i) (hC : ∀ i ∈ s, 0 < C i) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∑ i ∈ s, V i / (optimalN s V C (ε ^ 2) i : ℝ) ≤ ε ^ 2 ∧
        ∑ i ∈ s, (optimalN s V C (ε ^ 2) i : ℝ) * C i ≤ c / ε ^ 2 := by
  have hCsum : 0 < ∑ i ∈ s, C i := Finset.sum_pos hC hs
  refine ⟨(∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 + ∑ i ∈ s, C i,
    add_pos_of_nonneg_of_pos (sq_nonneg _) hCsum, fun ε hε hε1 => ?_⟩
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε21 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
  refine ⟨optimalN_variance hs hV hC hε2, ?_⟩
  calc ∑ i ∈ s, (optimalN s V C (ε ^ 2) i : ℝ) * C i
      ≤ (ε ^ 2)⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 + ∑ i ∈ s, C i :=
        optimalN_cost hs hV hC hε2
    _ ≤ (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 / ε ^ 2 + (∑ i ∈ s, C i) / ε ^ 2 := by
        rw [inv_mul_eq_div]
        gcongr
        exact le_div_self hCsum.le hε2 hε21
    _ = ((∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 + ∑ i ∈ s, C i) / ε ^ 2 := by
        rw [add_div]


/-! ### The correction variance of the coupled paths

Giles 2015, §8, p. 56: the coupling "leads to a very effective multilevel algorithm with a
correction variance which is `O(h)`" (after Anderson and Higham 2012).  Here the propensity `λ`
is `K`-Lipschitz and bounded by `Λ`.  In one coupled fine step the increments of the two paths
differ by at most `P₂ ~ P(h|λ(x) − λ(x^c)|)` (`lintegral_sq_coupledIncr_le`); over the two fine
steps of one coarse step, the coarse rate frozen, the mean square difference of the paths grows by
a factor `1 + O(h)` and an additive `O(h²)` (`lintegral_sq_coupledTwoStep_le`,
`lintegral_sq_coupledChain_le`); so after the `T/(2h)` coarse steps to the final time `T` it is
`O(h)` (`coupledChain_sq_le`), and so is the variance of the correction `Φ(x_T) − Φ(x^c_T)` for
a Lipschitz payoff `Φ` (`variance_coupledChain_le`), which is `O(2^{−ℓ})` on level `ℓ + 1`
(`tauLeaping_level_variance`): `β = 1`. -/

/-- The difference of two natural numbers is an integer: `|m − n| ≤ (m − n)²` (used in Giles 2015,
§8). -/
lemma abs_natCast_sub_le_sq (m n : ℕ) : |(m : ℝ) - n| ≤ ((m : ℝ) - n) ^ 2 := by
  rcases lt_trichotomy m n with h | rfl | h
  · have h1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_neg (by linarith)]
    nlinarith
  · simp
  · have h1 : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_pos (by linarith)]
    nlinarith

/-- The first two moments of a Poisson variate as lower integrals (used in Giles 2015, §8):
`∫⁻ (c₀ + c₁ n + c₂ n²) dP(r) = c₀ + c₁ r + c₂ (r + r²)` for `c₀, c₁, c₂ ≥ 0`. -/
lemma lintegral_poly_poissonMeasure (r : ℝ≥0) {c₀ c₁ c₂ : ℝ} (h₀ : 0 ≤ c₀) (h₁ : 0 ≤ c₁)
    (h₂ : 0 ≤ c₂) :
    ∫⁻ n, ENNReal.ofReal (c₀ + c₁ * n + c₂ * (n : ℝ) ^ 2) ∂(poissonMeasure r) =
      ENNReal.ofReal (c₀ + c₁ * r + c₂ * ((r : ℝ) + (r : ℝ) ^ 2)) := by
  have hs2 : HasSum (fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2)
      ((r : ℝ) + (r : ℝ) ^ 2) := by
    convert (hasSum_poissonWeight_mul_id r).add (hasSum_poissonWeight_mul_descFactorial r) using 1
    funext n
    ring
  have hi1 : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) :=
    integrable_poissonMeasure_iff.2 ((hasSum_poissonWeight_mul_id r).summable.congr fun n => by
      rw [Real.norm_natCast])
  have hi2 : Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) :=
    integrable_poissonMeasure_iff.2 (hs2.summable.congr fun n => by
      rw [norm_pow, Real.norm_natCast])
  have hA : Integrable (fun n : ℕ => c₀ + c₁ * n) (poissonMeasure r) :=
    (integrable_const c₀).add (hi1.const_mul c₁)
  have hB : Integrable (fun n : ℕ => c₂ * (n : ℝ) ^ 2) (poissonMeasure r) := hi2.const_mul c₂
  have hint : Integrable (fun n : ℕ => c₀ + c₁ * n + c₂ * (n : ℝ) ^ 2) (poissonMeasure r) :=
    hA.add hB
  have hnn : 0 ≤ᵐ[poissonMeasure r] fun n : ℕ => c₀ + c₁ * n + c₂ * (n : ℝ) ^ 2 :=
    ae_of_all _ fun n => add_nonneg (add_nonneg h₀ (mul_nonneg h₁ (Nat.cast_nonneg n)))
      (mul_nonneg h₂ (sq_nonneg _))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_add hA hB,
    integral_add (integrable_const c₀) (hi1.const_mul c₁), integral_const, probReal_univ,
    one_smul, integral_const_mul, integral_const_mul, integral_poissonMeasure_id,
    integral_sq_poissonMeasure]

/-- The mean of a Poisson variate as a lower integral: `∫⁻ n dP(r) = r`. -/
lemma lintegral_id_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n, ENNReal.ofReal (n : ℝ) ∂(poissonMeasure r) = ENNReal.ofReal r := by
  have h := lintegral_poly_poissonMeasure r le_rfl zero_le_one le_rfl
  simp only [zero_add, one_mul, zero_mul, add_zero] at h
  exact h

/-- The second moment of a Poisson variate as a lower integral: `∫⁻ n² dP(r) = r + r²`. -/
lemma lintegral_sq_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n, ENNReal.ofReal ((n : ℝ) ^ 2) ∂(poissonMeasure r) = ENNReal.ofReal (r + (r : ℝ) ^ 2) := by
  have h := lintegral_poly_poissonMeasure r le_rfl le_rfl zero_le_one
  simp only [zero_add, one_mul, zero_mul] at h
  exact h

/-- A function of the second factor, integrated against a product whose first factor is a
probability measure. -/
lemma lintegral_prod_snd_eq {μ ν : Measure ℕ} [IsProbabilityMeasure μ] [SFinite ν]
    (f : ℕ → ℝ≥0∞) : ∫⁻ p, f p.2 ∂(μ.prod ν) = ∫⁻ n, f n ∂ν := by
  have h := lintegral_map (μ := μ.prod ν) (Measurable.of_discrete (f := f)) measurable_snd
  rw [Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h.symm

/-- The increment of the path with rate `b` has the law `P(b)` (`coupledIncr_snd`): lower
integrals of functions of it. -/
lemma lintegral_coupledIncr_snd (a b : ℝ≥0) (f : ℕ → ℝ≥0∞) :
    ∫⁻ ij, f ij.2 ∂(coupledIncr a b) = ∫⁻ n, f n ∂(poissonMeasure b) := by
  rw [← coupledIncr_snd a b, lintegral_map Measurable.of_discrete measurable_snd]

/-- **One coupled fine step** (Giles 2015, §8, p. 55: "using `P₁` as the Poisson variate for the
path with the smaller rate, and `P₁ + P₂` for the path with the larger rate"): the increments of
the paths with rates `a` and `b` differ by at most `P₂ ~ P(|a − b|)`, so from the states `x`, `y`,
`E[(x + I_a − (y + I_b))²] ≤ (x − y)² + 2|x − y| |a − b| + |a − b| + |a − b|²`. -/
lemma lintegral_sq_coupledIncr_le (a b : ℝ≥0) (x y : ℕ) :
    ∫⁻ ij, ENNReal.ofReal ((((x + ij.1 : ℕ) : ℝ) - ((y + ij.2 : ℕ) : ℝ)) ^ 2)
        ∂(coupledIncr a b) ≤
      ENNReal.ofReal (((x : ℝ) - y) ^ 2 + 2 * |(x : ℝ) - y| * |(a : ℝ) - b| +
        1 * (|(a : ℝ) - b| + |(a : ℝ) - b| ^ 2)) := by
  have hpt : ∀ p : ℕ × ℕ,
      (((x + (couplePair a b p).1 : ℕ) : ℝ) - ((y + (couplePair a b p).2 : ℕ) : ℝ)) ^ 2 ≤
        ((x : ℝ) - y) ^ 2 + 2 * |(x : ℝ) - y| * (p.2 : ℝ) + 1 * (p.2 : ℝ) ^ 2 := by
    intro p
    have hp : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
    have hδ : |((couplePair a b p).1 : ℝ) - (couplePair a b p).2| ≤ p.2 := by
      rw [abs_le]
      simp only [couplePair]
      constructor <;> split_ifs <;> push_cast <;> linarith
    have e : (((x + (couplePair a b p).1 : ℕ) : ℝ) - ((y + (couplePair a b p).2 : ℕ) : ℝ)) =
        ((x : ℝ) - y) + (((couplePair a b p).1 : ℝ) - (couplePair a b p).2) := by
      push_cast
      ring
    rw [e]
    have h1 : ((x : ℝ) - y) * (((couplePair a b p).1 : ℝ) - (couplePair a b p).2) ≤
        |(x : ℝ) - y| * p.2 :=
      (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hδ (abs_nonneg _))
    have h2 : (((couplePair a b p).1 : ℝ) - (couplePair a b p).2) ^ 2 ≤ (p.2 : ℝ) ^ 2 :=
      sq_le_sq' (abs_le.1 hδ).1 (abs_le.1 hδ).2
    nlinarith [h1, h2]
  rw [← coe_max_sub_min]
  calc ∫⁻ ij, ENNReal.ofReal ((((x + ij.1 : ℕ) : ℝ) - ((y + ij.2 : ℕ) : ℝ)) ^ 2)
          ∂(coupledIncr a b)
      = ∫⁻ p, ENNReal.ofReal ((((x + (couplePair a b p).1 : ℕ) : ℝ) -
            ((y + (couplePair a b p).2 : ℕ) : ℝ)) ^ 2)
          ∂((poissonMeasure (min a b)).prod (poissonMeasure (max a b - min a b))) :=
        lintegral_map Measurable.of_discrete Measurable.of_discrete
    _ ≤ ∫⁻ p, ENNReal.ofReal (((x : ℝ) - y) ^ 2 + 2 * |(x : ℝ) - y| * ((p.2 : ℕ) : ℝ) +
            1 * ((p.2 : ℕ) : ℝ) ^ 2)
          ∂((poissonMeasure (min a b)).prod (poissonMeasure (max a b - min a b))) :=
        lintegral_mono fun p => ENNReal.ofReal_le_ofReal (hpt p)
    _ = ∫⁻ n, ENNReal.ofReal (((x : ℝ) - y) ^ 2 + 2 * |(x : ℝ) - y| * (n : ℝ) + 1 * (n : ℝ) ^ 2)
          ∂(poissonMeasure (max a b - min a b)) :=
        lintegral_prod_snd_eq fun n : ℕ =>
          ENNReal.ofReal (((x : ℝ) - y) ^ 2 + 2 * |(x : ℝ) - y| * (n : ℝ) + 1 * (n : ℝ) ^ 2)
    _ = ENNReal.ofReal (((x : ℝ) - y) ^ 2 + 2 * |(x : ℝ) - y| * ((max a b - min a b : ℝ≥0) : ℝ) +
          1 * (((max a b - min a b : ℝ≥0) : ℝ) + ((max a b - min a b : ℝ≥0) : ℝ) ^ 2)) :=
        lintegral_poly_poissonMeasure _ (sq_nonneg _) (by positivity) zero_le_one

/-- The polynomial bound behind one coupled fine step at a frozen coarse rate (Giles 2015, §8): if
`0 ≤ R ≤ κ (|d| + j)` and `|d| ≤ d²`, then
`d² + 2|d| R + R + R² ≤ (1 + 4κ + 2κ²) d² + (κ + 2κ²) j² + κ j`. -/
lemma coupled_step_bound {d j R κ : ℝ} (hκ : 0 ≤ κ) (hR0 : 0 ≤ R)
    (hR : R ≤ κ * (|d| + j)) (hd : |d| ≤ d ^ 2) :
    d ^ 2 + 2 * |d| * R + 1 * (R + R ^ 2) ≤
      (1 + 4 * κ + 2 * κ ^ 2) * d ^ 2 + (κ + 2 * κ ^ 2) * j ^ 2 + κ * j := by
  rw [← sq_abs d] at hd ⊢
  have hu : 0 ≤ |d| := abs_nonneg d
  have h1 : 2 * |d| * R ≤ 2 * |d| * (κ * (|d| + j)) :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have h2 : R ^ 2 ≤ (κ * (|d| + j)) ^ 2 := pow_le_pow_left₀ hR0 hR 2
  have h3 : 0 ≤ κ * (|d| - j) ^ 2 := mul_nonneg hκ (sq_nonneg _)
  have h4 : 0 ≤ κ ^ 2 * (|d| - j) ^ 2 := mul_nonneg (sq_nonneg κ) (sq_nonneg _)
  have h5 : κ * |d| ≤ κ * |d| ^ 2 := mul_le_mul_of_nonneg_left hd hκ
  nlinarith [h1, h2, h3, h4, h5, hR]

/-- Splitting a lower integral of `a X + b Y + c Z` on a discrete space. -/
lemma lintegral_ofReal_add3 {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : Measure α) {X Y Z : α → ℝ} (hX : ∀ x, 0 ≤ X x) (hY : ∀ x, 0 ≤ Y x)
    (hZ : ∀ x, 0 ≤ Z x) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∫⁻ x, ENNReal.ofReal (a * X x + b * Y x + c * Z x) ∂μ =
      ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal (X x) ∂μ +
        ENNReal.ofReal b * ∫⁻ x, ENNReal.ofReal (Y x) ∂μ +
        ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (Z x) ∂μ := by
  have e : ∀ x, ENNReal.ofReal (a * X x + b * Y x + c * Z x) =
      ENNReal.ofReal a * ENNReal.ofReal (X x) + ENNReal.ofReal b * ENNReal.ofReal (Y x) +
        ENNReal.ofReal c * ENNReal.ofReal (Z x) := fun x => by
    rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg ha (hX x)) (mul_nonneg hb (hY x)))
        (mul_nonneg hc (hZ x)),
      ENNReal.ofReal_add (mul_nonneg ha (hX x)) (mul_nonneg hb (hY x)), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul hb, ENNReal.ofReal_mul hc]
  rw [lintegral_congr e, lintegral_add_left Measurable.of_discrete,
    lintegral_add_left Measurable.of_discrete, lintegral_const_mul _ Measurable.of_discrete,
    lintegral_const_mul _ Measurable.of_discrete, lintegral_const_mul _ Measurable.of_discrete]

/-- Splitting a lower integral of `a X + b` on a discrete space. -/
lemma lintegral_ofReal_mul_add {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : Measure α) {X : α → ℝ} (hX : ∀ x, 0 ≤ X x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ x, ENNReal.ofReal (a * X x + b) ∂μ =
      ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal (X x) ∂μ + ENNReal.ofReal b * μ Set.univ := by
  have e : ∀ x, ENNReal.ofReal (a * X x + b) =
      ENNReal.ofReal a * ENNReal.ofReal (X x) + ENNReal.ofReal b := fun x => by
    rw [ENNReal.ofReal_add (mul_nonneg ha (hX x)) hb, ENNReal.ofReal_mul ha]
  rw [lintegral_congr e, lintegral_add_left Measurable.of_discrete,
    lintegral_const_mul _ Measurable.of_discrete, lintegral_const]

/-- The coupled increments form a probability measure. -/
lemma coupledIncr_univ (a b : ℝ≥0) : coupledIncr a b Set.univ = 1 := by
  rw [coupledIncr, Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ,
    measure_univ]

/-- Two coupled fine steps form a probability measure. -/
lemma coupledTwoStep_univ (lam : ℕ → ℝ≥0) (h : ℝ≥0) (s : ℕ × ℕ) :
    coupledTwoStep lam h s Set.univ = 1 := by
  have e : ∀ ij : ℕ × ℕ, ((coupledIncr (h * lam (s.1 + ij.1)) (h * lam s.2)).map fun ij' =>
      (s.1 + ij.1 + ij'.1, s.2 + ij.2 + ij'.2)) Set.univ = 1 := fun ij => by
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ, Set.preimage_univ,
      coupledIncr_univ]
  rw [coupledTwoStep, Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable,
    lintegral_congr e, lintegral_const, one_mul, coupledIncr_univ]

/-- The law of the coupled pair of paths is a probability measure (Giles 2015, §8). -/
lemma coupledChain_univ (lam : ℕ → ℝ≥0) (h : ℝ≥0) (x₀ : ℕ) :
    ∀ k, coupledChain lam h x₀ k Set.univ = 1
  | 0 => by rw [coupledChain, measure_univ]
  | k + 1 => by
      rw [coupledChain, Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable,
        lintegral_congr (coupledTwoStep_univ lam h), lintegral_const, one_mul,
        coupledChain_univ lam h x₀ k]

/-- **The difference of the coupled paths over one coarse step** (Giles 2015, §8, p. 55: the
coarse Poisson variate is expressed "as the sum of two Poisson variates, `P(hλ(x^c_n))`
corresponding to the first and second fine path timesteps", each coupled with the fine one).  If
the scaled rates satisfy `|hλ(x) − hλ(y)| ≤ κ |x − y|` and `hλ ≤ ℓ`, then over the two fine steps
from `(x, x^c)`, the coarse rate frozen at `λ(x^c)`,
`E[(x₂ − x^c₂)²] ≤ (1 + 4κ + 2κ²)² (x − x^c)² + (κ + 2κ²)(ℓ + ℓ²) + κℓ`. -/
theorem lintegral_sq_coupledTwoStep_le {lam : ℕ → ℝ≥0} {h : ℝ≥0} {κ ℓ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ x y : ℕ, |((h * lam x : ℝ≥0) : ℝ) - ((h * lam y : ℝ≥0) : ℝ)| ≤ κ * |(x : ℝ) - y|)
    (hb : ∀ y : ℕ, ((h * lam y : ℝ≥0) : ℝ) ≤ ℓ) (s : ℕ × ℕ) :
    ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledTwoStep lam h s) ≤
      ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2 * ((s.1 : ℝ) - s.2) ^ 2 +
        ((κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ)) := by
  have hℓ : 0 ≤ ℓ := (NNReal.coe_nonneg _).trans (hb 0)
  have hα : 0 ≤ 1 + 4 * κ + 2 * κ ^ 2 := by positivity
  -- the second fine step, from the states after the first: the fine rate `hλ(x + i)` against the
  -- frozen coarse rate `hλ(x^c)`
  have hin : ∀ ij : ℕ × ℕ,
      ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2)
          ∂((coupledIncr (h * lam (s.1 + ij.1)) (h * lam s.2)).map fun ij' =>
            (s.1 + ij.1 + ij'.1, s.2 + ij.2 + ij'.2)) ≤
        ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) *
            (((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) ^ 2 +
          (κ + 2 * κ ^ 2) * (ij.2 : ℝ) ^ 2 + κ * ij.2) := by
    intro ij
    rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
    refine (lintegral_sq_coupledIncr_le _ _ (s.1 + ij.1) (s.2 + ij.2)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    refine coupled_step_bound hκ (abs_nonneg _) ?_ (abs_natCast_sub_le_sq _ _)
    refine (hr _ _).trans (mul_le_mul_of_nonneg_left ?_ hκ)
    have e : ((s.1 + ij.1 : ℕ) : ℝ) - (s.2 : ℝ) =
        (((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) + ij.2 := by
      push_cast
      ring
    rw [e]
    exact (abs_add_le _ _).trans (by rw [Nat.abs_cast])
  -- the first fine step and the moments of the first coarse increment
  have hd1 : ∫⁻ ij, ENNReal.ofReal ((((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) ^ 2)
      ∂(coupledIncr (h * lam s.1) (h * lam s.2)) ≤
      ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) * ((s.1 : ℝ) - s.2) ^ 2) := by
    refine (lintegral_sq_coupledIncr_le _ _ s.1 s.2).trans (ENNReal.ofReal_le_ofReal ?_)
    have h0 := coupled_step_bound (d := (s.1 : ℝ) - s.2) (j := 0)
      (R := |((h * lam s.1 : ℝ≥0) : ℝ) - ((h * lam s.2 : ℝ≥0) : ℝ)|) hκ (abs_nonneg _)
      (by rw [add_zero]; exact hr _ _) (abs_natCast_sub_le_sq _ _)
    linarith
  have hj2 : ∫⁻ ij, ENNReal.ofReal ((ij.2 : ℝ) ^ 2) ∂(coupledIncr (h * lam s.1) (h * lam s.2)) ≤
      ENNReal.ofReal (ℓ + ℓ ^ 2) := by
    rw [lintegral_coupledIncr_snd _ _ fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ 2),
      lintegral_sq_poissonMeasure]
    have hb' := hb s.2
    have h0 : (0 : ℝ) ≤ ((h * lam s.2 : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hj1 : ∫⁻ ij, ENNReal.ofReal (ij.2 : ℝ) ∂(coupledIncr (h * lam s.1) (h * lam s.2)) ≤
      ENNReal.ofReal ℓ := by
    rw [lintegral_coupledIncr_snd _ _ fun n : ℕ => ENNReal.ofReal (n : ℝ),
      lintegral_id_poissonMeasure]
    exact ENNReal.ofReal_le_ofReal (hb s.2)
  calc ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledTwoStep lam h s)
      ≤ ∫⁻ ij, ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2)
          ∂((coupledIncr (h * lam (s.1 + ij.1)) (h * lam s.2)).map fun ij' =>
            (s.1 + ij.1 + ij'.1, s.2 + ij.2 + ij'.2))
          ∂(coupledIncr (h * lam s.1) (h * lam s.2)) := by
        rw [coupledTwoStep]
        exact Measure.lintegral_bind_le _ _ _
    _ ≤ ∫⁻ ij, ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) *
            (((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) ^ 2 +
          (κ + 2 * κ ^ 2) * (ij.2 : ℝ) ^ 2 + κ * ij.2)
          ∂(coupledIncr (h * lam s.1) (h * lam s.2)) :=
        lintegral_mono hin
    _ = ENNReal.ofReal (1 + 4 * κ + 2 * κ ^ 2) *
            ∫⁻ ij, ENNReal.ofReal ((((s.1 + ij.1 : ℕ) : ℝ) - ((s.2 + ij.2 : ℕ) : ℝ)) ^ 2)
              ∂(coupledIncr (h * lam s.1) (h * lam s.2)) +
          ENNReal.ofReal (κ + 2 * κ ^ 2) *
            ∫⁻ ij, ENNReal.ofReal ((ij.2 : ℝ) ^ 2) ∂(coupledIncr (h * lam s.1) (h * lam s.2)) +
          ENNReal.ofReal κ *
            ∫⁻ ij, ENNReal.ofReal (ij.2 : ℝ) ∂(coupledIncr (h * lam s.1) (h * lam s.2)) :=
        lintegral_ofReal_add3 _ (fun _ => by positivity) (fun _ => by positivity)
          (fun _ => by positivity) hα (by positivity) hκ
    _ ≤ ENNReal.ofReal (1 + 4 * κ + 2 * κ ^ 2) *
            ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) * ((s.1 : ℝ) - s.2) ^ 2) +
          ENNReal.ofReal (κ + 2 * κ ^ 2) * ENNReal.ofReal (ℓ + ℓ ^ 2) +
          ENNReal.ofReal κ * ENNReal.ofReal ℓ := by
        gcongr
    _ = ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2 * ((s.1 : ℝ) - s.2) ^ 2 +
          ((κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ)) := by
        rw [← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hκ,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The mean square difference of the coupled paths** (Giles 2015, §8): with the bounds of
`lintegral_sq_coupledTwoStep_le`, after `k` coarse steps from `(x₀, x₀)`,
`E[(x_{2k} − x^c_{2k})²] ≤ B ∑_{i<k} Aⁱ`, where `A = (1 + 4κ + 2κ²)²` and
`B = (κ + 2κ²)(ℓ + ℓ²) + κℓ`. -/
theorem lintegral_sq_coupledChain_le {lam : ℕ → ℝ≥0} {h : ℝ≥0} {κ ℓ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ x y : ℕ, |((h * lam x : ℝ≥0) : ℝ) - ((h * lam y : ℝ≥0) : ℝ)| ≤ κ * |(x : ℝ) - y|)
    (hb : ∀ y : ℕ, ((h * lam y : ℝ≥0) : ℝ) ≤ ℓ) (x₀ : ℕ) :
    ∀ k, ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledChain lam h x₀ k) ≤
      ENNReal.ofReal (((κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ) *
        ∑ i ∈ Finset.range k, ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) ^ i)
  | 0 => by
      rw [coupledChain, lintegral_dirac]
      simp
  | k + 1 => by
      have hℓ : 0 ≤ ℓ := (NNReal.coe_nonneg _).trans (hb 0)
      have hA : 0 ≤ (1 + 4 * κ + 2 * κ ^ 2) ^ 2 := by positivity
      have hB : 0 ≤ (κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ := by positivity
      have hS : 0 ≤ ∑ i ∈ Finset.range k, ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) ^ i :=
        Finset.sum_nonneg fun i _ => pow_nonneg hA i
      calc ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledChain lam h x₀ (k + 1))
          ≤ ∫⁻ s, ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledTwoStep lam h s)
              ∂(coupledChain lam h x₀ k) := by
            rw [coupledChain]
            exact Measure.lintegral_bind_le _ _ _
        _ ≤ ∫⁻ s, ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2 * ((s.1 : ℝ) - s.2) ^ 2 +
              ((κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ)) ∂(coupledChain lam h x₀ k) :=
            lintegral_mono fun s => lintegral_sq_coupledTwoStep_le hκ hr hb s
        _ = ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) *
              ∫⁻ s, ENNReal.ofReal (((s.1 : ℝ) - s.2) ^ 2) ∂(coupledChain lam h x₀ k) +
            ENNReal.ofReal ((κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ) := by
            rw [lintegral_ofReal_mul_add _ (fun _ => by positivity) hA hB, coupledChain_univ,
              mul_one]
        _ ≤ ENNReal.ofReal ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) *
              ENNReal.ofReal (((κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ) *
                ∑ i ∈ Finset.range k, ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) ^ i) +
            ENNReal.ofReal ((κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ) := by
            gcongr
            exact lintegral_sq_coupledChain_le hκ hr hb x₀ k
        _ = ENNReal.ofReal (((κ + 2 * κ ^ 2) * (ℓ + ℓ ^ 2) + κ * ℓ) *
              ∑ i ∈ Finset.range (k + 1), ((1 + 4 * κ + 2 * κ ^ 2) ^ 2) ^ i) := by
            rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (mul_nonneg hA (mul_nonneg hB hS)) hB,
              geom_sum_succ]
            congr 1
            ring

/-- **The coupled fine and coarse paths are `O(h)` apart in mean square** (Giles 2015, §8, p. 56:
the Poisson coupling "leads to a very effective multilevel algorithm with a correction variance
which is `O(h)`", after Anderson and Higham 2012).  Let the propensity `λ` be `K`-Lipschitz and
bounded by `Λ`, and let `T ≥ 0` be the final time.  There is `c ≥ 0`, depending only on `K`, `Λ`
and `T`, such that for every time step `0 ≤ h ≤ 1` and every number `k` of coarse steps with
`2kh ≤ T`, the coupled paths from `x₀` satisfy `E[(x_{2k} − x^c_{2k})²] ≤ c h`, the square
difference being integrable. -/
theorem coupledChain_sq_le {lam : ℕ → ℝ≥0} {K Λ : ℝ≥0}
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (hΛ : ∀ x, lam x ≤ Λ)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (h : ℝ≥0) (k x₀ : ℕ), (h : ℝ) ≤ 1 → 2 * k * (h : ℝ) ≤ T →
      Integrable (fun q : ℕ × ℕ => ((q.1 : ℝ) - q.2) ^ 2) (coupledChain lam h x₀ k) ∧
        ∫ q, ((q.1 : ℝ) - q.2) ^ 2 ∂(coupledChain lam h x₀ k) ≤ c * h := by
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  have hΛ0 : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
  refine ⟨(((K : ℝ) + 2 * (K : ℝ) ^ 2) * ((Λ : ℝ) + (Λ : ℝ) ^ 2) + (K : ℝ) * Λ) * T *
      Real.exp (T * (4 * (K : ℝ) + 2 * (K : ℝ) ^ 2)), by positivity,
      fun h k x₀ hh1 hkT => ?_⟩
  have hh0 : (0 : ℝ) ≤ h := h.coe_nonneg
  have hκ : 0 ≤ (h : ℝ) * K := mul_nonneg hh0 hK0
  have hr : ∀ x y : ℕ, |((h * lam x : ℝ≥0) : ℝ) - ((h * lam y : ℝ≥0) : ℝ)| ≤
      (h : ℝ) * K * |(x : ℝ) - y| := by
    intro x y
    rw [NNReal.coe_mul, NNReal.coe_mul, ← mul_sub, abs_mul, NNReal.abs_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK x y) hh0
  have hb : ∀ y : ℕ, ((h * lam y : ℝ≥0) : ℝ) ≤ (h : ℝ) * Λ := by
    intro y
    rw [NNReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hΛ y) hh0
  have hl := lintegral_sq_coupledChain_le hκ hr hb x₀ k
  -- `B ∑_{i<k} Aⁱ ≤ c h`: `B ≤ h² B₀`, `∑_{i<k} Aⁱ ≤ k Aᵏ` and `Aᵏ ≤ e^{T(4K + 2K²)}`
  have h1 : (h : ℝ) ^ 2 ≤ h := by nlinarith
  have hA1 : (1 : ℝ) ≤ (1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2 :=
    one_le_pow₀ (by nlinarith)
  have hsum : ∑ i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ i ≤
      k * ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ k := by
    calc ∑ i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ i
        ≤ ∑ _i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ k :=
          Finset.sum_le_sum fun i hi => pow_le_pow_right₀ hA1 (Finset.mem_range.1 hi).le
      _ = k * ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ k := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hAk : ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ k ≤
      Real.exp (T * (4 * (K : ℝ) + 2 * (K : ℝ) ^ 2)) := by
    rw [← pow_mul]
    calc (1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ (2 * k)
        ≤ Real.exp (4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ (2 * k) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          linarith [Real.add_one_le_exp (4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2)]
      _ = Real.exp (((2 * k : ℕ) : ℝ) * (4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2)) :=
          (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (T * (4 * (K : ℝ) + 2 * (K : ℝ) ^ 2)) := by
          rw [Real.exp_le_exp]
          push_cast
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          have e1 : (k : ℝ) * ((h : ℝ) ^ 2 * (K : ℝ) ^ 2) ≤ k * ((h : ℝ) * (K : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) hk0
          have e2 := mul_le_mul_of_nonneg_right hkT
            (by positivity : (0 : ℝ) ≤ 4 * (K : ℝ) + 2 * (K : ℝ) ^ 2)
          nlinarith [e1, e2]
  have hBh : ((h : ℝ) * K + 2 * ((h : ℝ) * K) ^ 2) * ((h : ℝ) * Λ + ((h : ℝ) * Λ) ^ 2) +
      (h : ℝ) * K * ((h : ℝ) * Λ) ≤
      (h : ℝ) ^ 2 * (((K : ℝ) + 2 * (K : ℝ) ^ 2) * ((Λ : ℝ) + (Λ : ℝ) ^ 2) + (K : ℝ) * Λ) := by
    have e1 : (h : ℝ) * K + 2 * ((h : ℝ) * K) ^ 2 ≤ (h : ℝ) * ((K : ℝ) + 2 * (K : ℝ) ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg (K : ℝ))]
    have e2 : (h : ℝ) * Λ + ((h : ℝ) * Λ) ^ 2 ≤ (h : ℝ) * ((Λ : ℝ) + (Λ : ℝ) ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg (Λ : ℝ))]
    calc ((h : ℝ) * K + 2 * ((h : ℝ) * K) ^ 2) * ((h : ℝ) * Λ + ((h : ℝ) * Λ) ^ 2) +
          (h : ℝ) * K * ((h : ℝ) * Λ)
        ≤ ((h : ℝ) * ((K : ℝ) + 2 * (K : ℝ) ^ 2)) * ((h : ℝ) * ((Λ : ℝ) + (Λ : ℝ) ^ 2)) +
          (h : ℝ) * K * ((h : ℝ) * Λ) := by
          gcongr
      _ = (h : ℝ) ^ 2 * (((K : ℝ) + 2 * (K : ℝ) ^ 2) * ((Λ : ℝ) + (Λ : ℝ) ^ 2) + (K : ℝ) * Λ) := by
          ring
  have hS0 : 0 ≤ ∑ i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ i :=
    Finset.sum_nonneg fun i _ => by positivity
  have hkh : (k : ℝ) * h ≤ T := by
    have := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hh0
    linarith
  have hbound : (((h : ℝ) * K + 2 * ((h : ℝ) * K) ^ 2) * ((h : ℝ) * Λ + ((h : ℝ) * Λ) ^ 2) +
      (h : ℝ) * K * ((h : ℝ) * Λ)) *
        ∑ i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ i ≤
      (((K : ℝ) + 2 * (K : ℝ) ^ 2) * ((Λ : ℝ) + (Λ : ℝ) ^ 2) + (K : ℝ) * Λ) * T *
        Real.exp (T * (4 * (K : ℝ) + 2 * (K : ℝ) ^ 2)) * h := by
    calc (((h : ℝ) * K + 2 * ((h : ℝ) * K) ^ 2) * ((h : ℝ) * Λ + ((h : ℝ) * Λ) ^ 2) +
          (h : ℝ) * K * ((h : ℝ) * Λ)) *
            ∑ i ∈ Finset.range k, ((1 + 4 * ((h : ℝ) * K) + 2 * ((h : ℝ) * K) ^ 2) ^ 2) ^ i
        ≤ ((h : ℝ) ^ 2 * (((K : ℝ) + 2 * (K : ℝ) ^ 2) * ((Λ : ℝ) + (Λ : ℝ) ^ 2) + (K : ℝ) * Λ)) *
            (k * Real.exp (T * (4 * (K : ℝ) + 2 * (K : ℝ) ^ 2))) :=
          mul_le_mul hBh (hsum.trans (mul_le_mul_of_nonneg_left hAk (Nat.cast_nonneg k))) hS0
            (by positivity)
      _ = (((K : ℝ) + 2 * (K : ℝ) ^ 2) * ((Λ : ℝ) + (Λ : ℝ) ^ 2) + (K : ℝ) * Λ) * ((k : ℝ) * h) *
            Real.exp (T * (4 * (K : ℝ) + 2 * (K : ℝ) ^ 2)) * h := by
          ring
      _ ≤ (((K : ℝ) + 2 * (K : ℝ) ^ 2) * ((Λ : ℝ) + (Λ : ℝ) ^ 2) + (K : ℝ) * Λ) * T *
            Real.exp (T * (4 * (K : ℝ) + 2 * (K : ℝ) ^ 2)) * h := by
          gcongr
  have hfin : ∫⁻ q, ENNReal.ofReal (((q.1 : ℝ) - q.2) ^ 2) ∂(coupledChain lam h x₀ k) ≤
      ENNReal.ofReal ((((K : ℝ) + 2 * (K : ℝ) ^ 2) * ((Λ : ℝ) + (Λ : ℝ) ^ 2) + (K : ℝ) * Λ) * T *
        Real.exp (T * (4 * (K : ℝ) + 2 * (K : ℝ) ^ 2)) * h) :=
    hl.trans (ENNReal.ofReal_le_ofReal hbound)
  have hnn : 0 ≤ᵐ[coupledChain lam h x₀ k] fun q : ℕ × ℕ => ((q.1 : ℝ) - q.2) ^ 2 :=
    ae_of_all _ fun q => sq_nonneg _
  refine ⟨⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn]
    exact hfin.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn Measurable.of_discrete.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hfin

/-- **The correction variance of tau-leaping MLMC is `O(h)`** (Giles 2015, §8, p. 56: "a very
effective multilevel algorithm with a correction variance which is `O(h)`").  For a
`K`-Lipschitz propensity bounded by `Λ`, a final time `T ≥ 0` and an `L`-Lipschitz payoff `Φ`
of the terminal state, there is `c ≥ 0` such that for every time step `0 ≤ h ≤ 1` and `k` coarse
steps with `2kh ≤ T`, the correction `Φ(x_{2k}) − Φ(x^c_{2k})` of the coupled paths has variance
at most `c h`. -/
theorem variance_coupledChain_le {lam : ℕ → ℝ≥0} {K Λ : ℝ≥0}
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (hΛ : ∀ x, lam x ≤ Λ)
    {T : ℝ} (hT : 0 ≤ T) {Φ : ℕ → ℝ} {L : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ L * |(x : ℝ) - y|) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (h : ℝ≥0) (k x₀ : ℕ), (h : ℝ) ≤ 1 → 2 * k * (h : ℝ) ≤ T →
      variance (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) (coupledChain lam h x₀ k) ≤ c * h := by
  obtain ⟨c, hc, hbd⟩ := coupledChain_sq_le hK hΛ hT
  refine ⟨L ^ 2 * c, by positivity, fun h k x₀ hh1 hkT => ?_⟩
  obtain ⟨hint, hle⟩ := hbd h k x₀ hh1 hkT
  have : IsProbabilityMeasure (coupledChain lam h x₀ k) := ⟨coupledChain_univ lam h x₀ k⟩
  have hpt : ∀ q : ℕ × ℕ, (Φ q.1 - Φ q.2) ^ 2 ≤ L ^ 2 * ((q.1 : ℝ) - q.2) ^ 2 := fun q => by
    have h1 := hΦ q.1 q.2
    calc (Φ q.1 - Φ q.2) ^ 2 = |Φ q.1 - Φ q.2| ^ 2 := (sq_abs _).symm
      _ ≤ (L * |(q.1 : ℝ) - q.2|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = L ^ 2 * ((q.1 : ℝ) - q.2) ^ 2 := by rw [mul_pow, sq_abs]
  calc variance (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) (coupledChain lam h x₀ k)
      ≤ ∫ q, (Φ q.1 - Φ q.2) ^ 2 ∂(coupledChain lam h x₀ k) :=
        variance_le_expectation_sq Measurable.of_discrete.aestronglyMeasurable
    _ ≤ ∫ q, L ^ 2 * ((q.1 : ℝ) - q.2) ^ 2 ∂(coupledChain lam h x₀ k) :=
        integral_mono_of_nonneg (ae_of_all _ fun q => sq_nonneg _) (hint.const_mul _)
          (ae_of_all _ hpt)
    _ = L ^ 2 * ∫ q, ((q.1 : ℝ) - q.2) ^ 2 ∂(coupledChain lam h x₀ k) := integral_const_mul _ _
    _ ≤ L ^ 2 * (c * h) := mul_le_mul_of_nonneg_left hle (sq_nonneg L)
    _ = L ^ 2 * c * h := by ring

/-- **`β = 1` for tau-leaping MLMC** (Giles 2015, §8, p. 56, with the level structure of
`tauLeaping_level`): on level `ℓ + 1` the fine path makes `2^{ℓ+1}` steps of size
`h_{ℓ+1} = T/2^{ℓ+1}` and the coarse path `2^ℓ` steps of size `h_ℓ`, and for a `K`-Lipschitz
propensity bounded by `Λ` and an `L`-Lipschitz payoff the correction `Φ(x_T) − Φ(x^c_T)` is square
integrable and its variance is at most `c 2^{−ℓ}`, as soon as `h_{ℓ+1} ≤ 1`.  With the weak rate
`α = 1` and the cost rate `γ = 1` this is the regime `β = γ` of Theorem 1, hence the complexity
`O(ε⁻²(log ε)²)` (`tauLeaping_complexity`). -/
theorem tauLeaping_level_variance {lam : ℕ → ℝ≥0} {K Λ : ℝ≥0}
    (hK : ∀ x y : ℕ, |(lam x : ℝ) - lam y| ≤ K * |(x : ℝ) - y|) (hΛ : ∀ x, lam x ≤ Λ)
    (T : ℝ≥0) {Φ : ℕ → ℝ} {L : ℝ} (hΦ : ∀ x y : ℕ, |Φ x - Φ y| ≤ L * |(x : ℝ) - y|) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ ℓ x₀ : ℕ, (T : ℝ) ≤ 2 ^ (ℓ + 1) →
      MemLp (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) 2
        (coupledChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ)) ∧
      variance (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) (coupledChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ)) ≤
        c / 2 ^ ℓ := by
  obtain ⟨c, hc, hbd⟩ := variance_coupledChain_le hK hΛ T.coe_nonneg hΦ
  obtain ⟨_, -, hsq⟩ := coupledChain_sq_le hK hΛ T.coe_nonneg
  refine ⟨c * T / 2, by positivity, fun ℓ x₀ hℓ => ?_⟩
  have hh : ((T / 2 ^ (ℓ + 1) : ℝ≥0) : ℝ) = (T : ℝ) / 2 ^ (ℓ + 1) := by
    rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  have hpow : (0 : ℝ) < 2 ^ (ℓ + 1) := by positivity
  have hh1 : ((T / 2 ^ (ℓ + 1) : ℝ≥0) : ℝ) ≤ 1 := by
    rw [hh]
    exact div_le_one_of_le₀ hℓ hpow.le
  have hkT : 2 * ((2 ^ ℓ : ℕ) : ℝ) * ((T / 2 ^ (ℓ + 1) : ℝ≥0) : ℝ) ≤ T := by
    rw [hh]
    push_cast
    rw [pow_succ', mul_div_cancel₀ _ (by positivity)]
  have hm : AEStronglyMeasurable (fun q : ℕ × ℕ => Φ q.1 - Φ q.2)
      (coupledChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ)) :=
    Measurable.of_discrete.aestronglyMeasurable
  refine ⟨(memLp_two_iff_integrable_sq hm).2 ((((hsq _ _ x₀ hh1 hkT).1).const_mul (L ^ 2)).mono'
    (hm.pow 2) (ae_of_all _ fun q => ?_)), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (Φ q.1 - Φ q.2),
      ← sq_abs ((q.1 : ℝ) - q.2), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hΦ q.1 q.2) 2
  calc variance (fun q : ℕ × ℕ => Φ q.1 - Φ q.2) (coupledChain lam (T / 2 ^ (ℓ + 1)) x₀ (2 ^ ℓ))
      ≤ c * ((T / 2 ^ (ℓ + 1) : ℝ≥0) : ℝ) := hbd _ _ _ hh1 hkT
    _ = c * T / 2 / 2 ^ ℓ := by
        rw [hh, pow_succ]
        ring

end MLMC
