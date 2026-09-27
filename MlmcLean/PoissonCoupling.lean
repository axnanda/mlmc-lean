import MlmcLean.Allocation
import MlmcLean.Complexity
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
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

end MLMC
