import MlmcLean.Theorem1
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Multi-dimensional output functionals (Giles 2015, §2.5)

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.5
(pp. 16–18 of the author's version).

* **A finite set of outputs.**  "If there is a desired accuracy `ε_m` for the `m`-th output, then
  a simple approach … is to define `V_ℓ ≡ max_m V_{ℓ,m}/ε_m²` … Enforcing the constraint
  `∑_{ℓ=0}^{L} N_ℓ⁻¹ V_ℓ ≤ ½` is then sufficient to ensure that all of the individual variance
  constraints are satisfied, and the standard Lagrange multiplier approach … can be used to
  determine the optimal number of samples" (`multiOutput_variance`, `multiOutput_optimal`).
* **Outputs in a Hilbert space.**  "If `a` and `b` are two independent scalar random variables
  with zero mean then `E[(a+b)²] = E[a²] + E[b²]`.  When using the 2-norm, this extends to
  independent random vectors `a` and `b`, each with zero mean, since
  `E[‖a+b‖²] = E[‖a‖²] + E[‖b‖²]`, and similarly to random functions with a 2-norm based on an
  inner product" (`integral_add_sq_of_indepFun`, `integral_norm_add_sq_of_indepFun`).  "However
  this does not necessarily apply for other norms" (`sq_norm_add_of_indepFun_fails_sup`, with
  the sup norm of `ℝ × ℝ`).
* **The theory carries over.**  With "the substitutions `|E[P_ℓ] − E[P]| → ‖E[P_ℓ] − E[P]‖`,
  `V[P_ℓ − P_{ℓ−1}] → E[‖P_ℓ − P_{ℓ−1} − E[P_ℓ − P_{ℓ−1}]‖²]`" Theorem 1 holds for outputs in any
  real Hilbert space (`giles_theorem1_hilbert`), through the Hilbert-space forms of (2.1) and
  (2.3) (`integral_norm_sub_sq_eq`, `integral_norm_sum_sq_of_indepFun`, `mlmc_mse_hilbert`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped InnerProductSpace

namespace MLMC

/-! ### A finite set of outputs -/

section finite

variable {κ : Type*}

/-- **Several outputs with individual accuracies** (Giles 2015, §2.5, pp. 16–17): with
`V_ℓ = max_{m ∈ M} V_{ℓ,m}/ε_m²`, "enforcing the constraint `∑_{ℓ=0}^{L} N_ℓ⁻¹ V_ℓ ≤ ½` is then
sufficient to ensure that all of the individual variance constraints are satisfied": for every
output `m`, `∑_{ℓ=0}^{L} N_ℓ⁻¹ V_{ℓ,m} ≤ ½ ε_m²`.  Here `V ℓ m` is the variance of output `m` on
level `ℓ`, and the sample numbers `N ℓ > 0` are real (integer sample numbers are a special
case). -/
theorem multiOutput_variance {M : Finset κ} (hM : M.Nonempty) (V : ℕ → κ → ℝ) {ε : κ → ℝ}
    (hε : ∀ m ∈ M, 0 < ε m) (L : ℕ) {N : ℕ → ℝ} (hN : ∀ ℓ ∈ range (L + 1), 0 < N ℓ)
    (h : ∑ ℓ ∈ range (L + 1), M.sup' hM (fun m => V ℓ m / ε m ^ 2) / N ℓ ≤ 1 / 2) :
    ∀ m ∈ M, ∑ ℓ ∈ range (L + 1), V ℓ m / N ℓ ≤ ε m ^ 2 / 2 := by
  intro m hm
  have hε2 : 0 < ε m ^ 2 := pow_pos (hε m hm) 2
  calc ∑ ℓ ∈ range (L + 1), V ℓ m / N ℓ
      = ε m ^ 2 * ∑ ℓ ∈ range (L + 1), V ℓ m / ε m ^ 2 / N ℓ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [div_div, ← mul_div_assoc, mul_div_mul_left _ _ hε2.ne']
    _ ≤ ε m ^ 2 * ∑ ℓ ∈ range (L + 1), M.sup' hM (fun m => V ℓ m / ε m ^ 2) / N ℓ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ hℓ => ?_) hε2.le
        exact div_le_div_of_nonneg_right (Finset.le_sup' (fun m => V ℓ m / ε m ^ 2) hm)
          (hN ℓ hℓ).le
    _ ≤ ε m ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left h hε2.le
    _ = ε m ^ 2 / 2 := by ring

/-- **The optimal allocation for several outputs** (Giles 2015, §2.5, p. 17): with
`V_ℓ = max_{m ∈ M} V_{ℓ,m}/ε_m²`, "the standard Lagrange multiplier approach outlined in
Section 1.3 can be used to determine the optimal number of samples to use on each level".
Among real allocations `N_ℓ > 0` with `∑_{ℓ=0}^{L} N_ℓ⁻¹ V_ℓ ≤ ½` the least cost `∑ N_ℓ C_ℓ` is
`2 (∑_{ℓ=0}^{L} √(V_ℓ C_ℓ))²`, and the Lagrange allocation that attains it (`lagrangeN` with
`τ = ½`) satisfies every individual constraint `∑_ℓ N_ℓ⁻¹ V_{ℓ,m} ≤ ½ ε_m²`. -/
theorem multiOutput_optimal {M : Finset κ} (hM : M.Nonempty) (V : ℕ → κ → ℝ) (C : ℕ → ℝ)
    {ε : κ → ℝ} (hε : ∀ m ∈ M, 0 < ε m) (hV : ∀ ℓ, ∀ m ∈ M, 0 < V ℓ m) (hC : ∀ ℓ, 0 < C ℓ)
    (L : ℕ) :
    IsLeast {c | ∃ n : ℕ → ℝ, (∀ ℓ ∈ range (L + 1), 0 < n ℓ) ∧
        ∑ ℓ ∈ range (L + 1), M.sup' hM (fun m => V ℓ m / ε m ^ 2) / n ℓ ≤ 1 / 2 ∧
        c = ∑ ℓ ∈ range (L + 1), n ℓ * C ℓ}
      (2 * (∑ ℓ ∈ range (L + 1), Real.sqrt (M.sup' hM (fun m => V ℓ m / ε m ^ 2) * C ℓ)) ^ 2) ∧
    ∀ m ∈ M, ∑ ℓ ∈ range (L + 1), V ℓ m /
      lagrangeN (range (L + 1)) (fun ℓ => M.sup' hM fun m => V ℓ m / ε m ^ 2) C (1 / 2) ℓ ≤
        ε m ^ 2 / 2 := by
  obtain ⟨m₀, hm₀⟩ := hM
  have hVmax : ∀ ℓ, 0 < M.sup' ⟨m₀, hm₀⟩ (fun m => V ℓ m / ε m ^ 2) := fun ℓ =>
    lt_of_lt_of_le (div_pos (hV ℓ m₀ hm₀) (pow_pos (hε m₀ hm₀) 2))
      (Finset.le_sup' (fun m => V ℓ m / ε m ^ 2) hm₀)
  have hs : (range (L + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos L)⟩
  have h := optimal_cost_isLeast (range (L + 1))
    (fun ℓ => M.sup' ⟨m₀, hm₀⟩ fun m => V ℓ m / ε m ^ 2) C (τ := 1 / 2) (by norm_num) hs
    (fun ℓ _ => hVmax ℓ) (fun ℓ _ => hC ℓ)
  have h2 : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
  rw [h2] at h
  refine ⟨h.1, fun m hm => multiOutput_variance ⟨m₀, hm₀⟩ V hε L h.2.1.1 h.2.1.2.1.le m hm⟩

end finite

/-! ### Outputs in a Hilbert space -/

section hilbert

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product of two square-integrable random vectors is integrable. -/
lemma integrable_inner_of_memLp {X Y : Ω → E} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => ⟪X ω, Y ω⟫_ℝ) μ := by
  have hg : Integrable (fun ω => (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / 2) μ :=
    (hX.norm.integrable_sq.add hY.norm.integrable_sq).div_const 2
  refine hg.mono' (hX.1.inner hY.1) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm (X ω) (Y ω)
  have h2 := two_mul_le_add_sq ‖X ω‖ ‖Y ω‖
  linarith

/-- For independent integrable random vectors, `E⟪a, b⟫ = ⟪E a, E b⟫` (the step behind Giles 2015,
§2.5, p. 17). -/
lemma integral_inner_of_indepFun [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {a b : Ω → E} (hab : IndepFun a b μ) (ha : Integrable a μ) (hb : Integrable b μ) :
    ∫ ω, ⟪a ω, b ω⟫_ℝ ∂μ = ⟪∫ ω, a ω ∂μ, ∫ ω, b ω ∂μ⟫_ℝ :=
  hab.integral_bilin ha hb (innerSL ℝ)

/-- **Giles 2015, §2.5, p. 17** ("when using the 2-norm, this extends to independent random
vectors `a` and `b`, each with zero mean, since `E[‖a+b‖²] = E[‖a‖²] + E[‖b‖²]`, and similarly to
random functions with a 2-norm based on an inner product"): for independent, square-integrable,
zero-mean random variables `a`, `b` with values in a real Hilbert space,
`E[‖a + b‖²] = E[‖a‖²] + E[‖b‖²]`. -/
theorem integral_norm_add_sq_of_indepFun [IsProbabilityMeasure μ] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] {a b : Ω → E} (hab : IndepFun a b μ)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (ha0 : ∫ ω, a ω ∂μ = 0) (hb0 : ∫ ω, b ω ∂μ = 0) :
    ∫ ω, ‖a ω + b ω‖ ^ 2 ∂μ = ∫ ω, ‖a ω‖ ^ 2 ∂μ + ∫ ω, ‖b ω‖ ^ 2 ∂μ := by
  have hcross : ∫ ω, ⟪a ω, b ω⟫_ℝ ∂μ = 0 := by
    rw [integral_inner_of_indepFun hab (ha.integrable one_le_two) (hb.integrable one_le_two), ha0,
      inner_zero_left]
  have h1 : Integrable (fun ω => ‖a ω‖ ^ 2) μ := ha.norm.integrable_sq
  have h2 : Integrable (fun ω => 2 * ⟪a ω, b ω⟫_ℝ) μ :=
    (integrable_inner_of_memLp ha hb).const_mul 2
  have h3 : Integrable (fun ω => ‖b ω‖ ^ 2) μ := hb.norm.integrable_sq
  have h12 : Integrable (fun ω => ‖a ω‖ ^ 2 + 2 * ⟪a ω, b ω⟫_ℝ) μ := h1.add h2
  have hexp : ∀ ω, ‖a ω + b ω‖ ^ 2 = ‖a ω‖ ^ 2 + 2 * ⟪a ω, b ω⟫_ℝ + ‖b ω‖ ^ 2 := fun ω =>
    norm_add_sq_real (a ω) (b ω)
  simp only [hexp]
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul, hcross, mul_zero, add_zero]

/-- **Giles 2015, §2.5, p. 17**: "if `a` and `b` are two independent scalar random variables with
zero mean then `E[(a+b)²] = E[a²] + E[b²]`" (square-integrable, the case `E = ℝ` of
`integral_norm_add_sq_of_indepFun`). -/
theorem integral_add_sq_of_indepFun [IsProbabilityMeasure μ] {a b : Ω → ℝ}
    (hab : IndepFun a b μ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (ha0 : ∫ ω, a ω ∂μ = 0)
    (hb0 : ∫ ω, b ω ∂μ = 0) :
    ∫ ω, (a ω + b ω) ^ 2 ∂μ = ∫ ω, a ω ^ 2 ∂μ + ∫ ω, b ω ^ 2 ∂μ := by
  have h := integral_norm_add_sq_of_indepFun hab ha hb ha0 hb0
  simp only [Real.norm_eq_abs, sq_abs] at h
  exact h

/-- **The variance of a sum of independent random vectors** (Giles 2015, §2.5, p. 17, for any
finite number of terms): for pairwise independent, square-integrable, zero-mean random variables
`X_i` with values in a real Hilbert space, `E[‖∑_i X_i‖²] = ∑_i E[‖X_i‖²]`.  This is what makes
the variance of the multilevel estimator `∑_ℓ N_ℓ⁻¹ V_ℓ` in the 2-norm. -/
theorem integral_norm_sum_sq_of_indepFun [IsProbabilityMeasure μ] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} (s : Finset ι) {X : ι → Ω → E}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hX0 : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hind : Set.Pairwise ↑s fun i j => IndepFun (X i) (X j) μ) :
    ∫ ω, ‖∑ i ∈ s, X i ω‖ ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
  have hexp : ∀ ω, ‖∑ i ∈ s, X i ω‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, ⟪X i ω, X j ω⟫_ℝ := fun ω => by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    exact Finset.sum_congr rfl fun i _ => inner_sum _ _ _
  have hint : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => ⟪X i ω, X j ω⟫_ℝ) μ :=
    fun i hi j hj => integrable_inner_of_memLp (hX i hi) (hX j hj)
  have hterm : ∀ i ∈ s, ∑ j ∈ s, ∫ ω, ⟪X i ω, X j ω⟫_ℝ ∂μ = ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp only [real_inner_self_eq_norm_sq]
    · intro j hj hji
      rw [integral_inner_of_indepFun (hind hi hj (Ne.symm hji))
        ((hX i hi).integrable one_le_two) ((hX j hj).integrable one_le_two), hX0 i hi,
        inner_zero_left]
    · intro h
      exact absurd hi h
  simp only [hexp]
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => hint i hi j hj]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun j hj => hint i hi j hj]
  exact hterm i hi

/-- **Giles (2.1) in a Hilbert space** (Giles 2015, §2.5, p. 17, with the substitution
`V[·] → E[‖· − E[·]‖²]`): for a square-integrable random variable `Z` with values in a real
Hilbert space and any `m`, `E[‖Z − m‖²] = E[‖Z − E[Z]‖²] + ‖E[Z] − m‖²`. -/
theorem integral_norm_sub_sq_eq [IsProbabilityMeasure μ] [CompleteSpace E] {Z : Ω → E}
    (hZ : MemLp Z 2 μ) (m : E) :
    ∫ ω, ‖Z ω - m‖ ^ 2 ∂μ =
      ∫ ω, ‖Z ω - ∫ ω', Z ω' ∂μ‖ ^ 2 ∂μ + ‖(∫ ω, Z ω ∂μ) - m‖ ^ 2 := by
  set c : E := ∫ ω, Z ω ∂μ with hc
  have hW : MemLp (fun ω => Z ω - c) 2 μ := hZ.sub (memLp_const c)
  have hW1 : Integrable (fun ω => Z ω - c) μ := hW.integrable one_le_two
  have hW0 : ∫ ω, (Z ω - c) ∂μ = 0 := by
    rw [integral_sub (hZ.integrable one_le_two) (integrable_const c), integral_const, ← hc]
    simp
  have hcross : ∫ ω, ⟪c - m, Z ω - c⟫_ℝ ∂μ = 0 := by
    rw [integral_inner (𝕜 := ℝ) hW1 (c - m), hW0, inner_zero_right]
  have hexp : ∀ ω, ‖Z ω - m‖ ^ 2 = ‖Z ω - c‖ ^ 2 + 2 * ⟪c - m, Z ω - c⟫_ℝ + ‖c - m‖ ^ 2 :=
    fun ω => by
      have h := norm_add_sq_real (Z ω - c) (c - m)
      rw [sub_add_sub_cancel, real_inner_comm] at h
      exact h
  have h1 : Integrable (fun ω => ‖Z ω - c‖ ^ 2) μ := hW.norm.integrable_sq
  have h2 : Integrable (fun ω => 2 * ⟪c - m, Z ω - c⟫_ℝ) μ :=
    (hW1.const_inner (𝕜 := ℝ) (c - m)).const_mul 2
  have h12 : Integrable (fun ω => ‖Z ω - c‖ ^ 2 + 2 * ⟪c - m, Z ω - c⟫_ℝ) μ := h1.add h2
  simp only [hexp]
  rw [integral_add h12 (integrable_const _), integral_add h1 h2, integral_const_mul, hcross,
    integral_const]
  simp

/-- Telescoping of the level means in a Banach space (Giles 2015, §1.3 and §2.5): if
`E[Y_0] = E[P_0]` and `E[Y_{ℓ+1}] = E[P_{ℓ+1} − P_ℓ]`, then `∑_{ℓ=0}^{L} E[Y_ℓ] = E[P_L]`. -/
lemma sum_integral_eq_of_telescope {Pℓ Y : ℕ → Ω → E} (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (h_ii₀ : ∫ ω, Y 0 ω ∂μ = ∫ ω, Pℓ 0 ω ∂μ)
    (h_ii : ∀ ℓ, ∫ ω, Y (ℓ + 1) ω ∂μ = ∫ ω, (Pℓ (ℓ + 1) ω - Pℓ ℓ ω) ∂μ) :
    ∀ L : ℕ, ∑ ℓ ∈ range (L + 1), ∫ ω, Y ℓ ω ∂μ = ∫ ω, Pℓ L ω ∂μ
  | 0 => by simp [h_ii₀]
  | L + 1 => by
    rw [Finset.sum_range_succ, sum_integral_eq_of_telescope hPℓ h_ii₀ h_ii L, h_ii L,
      integral_sub (hPℓ _) (hPℓ _)]
    abel

/-- **The MSE of the multilevel estimator in a Hilbert space** (Giles 2015, §2.5, p. 17, with
(2.1) and (2.3)): for pairwise independent square-integrable level estimators `Y_ℓ` with values
in a real Hilbert space satisfying condition ii), `E[‖∑_{ℓ=0}^{L} Y_ℓ − m‖²] =
∑_{ℓ=0}^{L} E[‖Y_ℓ − E[Y_ℓ]‖²] + ‖E[P_L] − m‖²` for any `m` (Giles: `m = E[P]`). -/
theorem mlmc_mse_hilbert [IsProbabilityMeasure μ] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] (Pℓ : ℕ → Ω → E) (Y : ℕ → Ω → E) (L : ℕ) (m : E)
    (hY : ∀ ℓ, MemLp (Y ℓ) 2 μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hind : Set.Pairwise ↑(range (L + 1)) fun i j => IndepFun (Y i) (Y j) μ)
    (h_ii₀ : ∫ ω, Y 0 ω ∂μ = ∫ ω, Pℓ 0 ω ∂μ)
    (h_ii : ∀ ℓ, ∫ ω, Y (ℓ + 1) ω ∂μ = ∫ ω, (Pℓ (ℓ + 1) ω - Pℓ ℓ ω) ∂μ) :
    ∫ ω, ‖∑ ℓ ∈ range (L + 1), Y ℓ ω - m‖ ^ 2 ∂μ =
      ∑ ℓ ∈ range (L + 1), ∫ ω, ‖Y ℓ ω - ∫ ω', Y ℓ ω' ∂μ‖ ^ 2 ∂μ +
        ‖(∫ ω, Pℓ L ω ∂μ) - m‖ ^ 2 := by
  have htel := sum_integral_eq_of_telescope hPℓ h_ii₀ h_ii L
  have hsum : MemLp (fun ω => ∑ ℓ ∈ range (L + 1), Y ℓ ω) 2 μ :=
    memLp_finsetSum _ fun ℓ _ => hY ℓ
  have hmean : ∫ ω, ∑ ℓ ∈ range (L + 1), Y ℓ ω ∂μ = ∫ ω, Pℓ L ω ∂μ := by
    rw [integral_finsetSum _ fun ℓ _ => (hY ℓ).integrable one_le_two]
    exact htel
  rw [integral_norm_sub_sq_eq hsum m, hmean]
  congr 1
  have hc : ∀ ω, ∑ ℓ ∈ range (L + 1), Y ℓ ω - ∫ ω', Pℓ L ω' ∂μ =
      ∑ ℓ ∈ range (L + 1), (Y ℓ ω - ∫ ω', Y ℓ ω' ∂μ) := fun ω => by
    rw [Finset.sum_sub_distrib, htel]
  simp only [hc]
  refine integral_norm_sum_sq_of_indepFun (range (L + 1))
    (X := fun ℓ ω => Y ℓ ω - ∫ ω', Y ℓ ω' ∂μ) (fun ℓ _ => (hY ℓ).sub (memLp_const _))
    (fun ℓ _ => ?_)
    (fun i hi j hj hij => (hind hi hj hij).comp (continuous_sub_right _).measurable
      (continuous_sub_right _).measurable)
  show ∫ ω, (Y ℓ ω - ∫ ω', Y ℓ ω' ∂μ) ∂μ = 0
  rw [integral_sub ((hY ℓ).integrable one_le_two) (integrable_const _), integral_const]
  simp

/-- **Giles' Theorem 1 for outputs in a Hilbert space** (Giles 2015, §2.5, p. 17: "the extension
of the theory to infinite-dimensional outputs requires the definition of an appropriate norm
`‖·‖`, and then to a large extent the theory carries over by making the substitutions
`|E[P_ℓ] − E[P]| → ‖E[P_ℓ] − E[P]‖`, `V[P_ℓ − P_{ℓ−1}] → E[‖P_ℓ − P_{ℓ−1} − E[P_ℓ − P_{ℓ−1}]‖²]`",
with Theorem 1 of §2.1).  Hypotheses as in `giles_theorem1`, for random variables with values in
a real Hilbert space `E` and with these substitutions in (i) and in the variance identity
`E[‖Y_ℓ − E[Y_ℓ]‖²] = V_ℓ / n`.  Then there is `c₄ > 0` such that for every `0 < ε < e⁻¹` there
are `L` and `N_ℓ ≥ 1` with `E[‖Y − E[P]‖²] < ε²` for `Y = ∑_{ℓ=0}^{L} Y_ℓ(N_ℓ)`, and expected
total cost `E[C] ≤ c₄ ε⁻²` if `β > γ`, `c₄ ε⁻² (log ε)²` if `β = γ`, `c₄ ε^{−2−(γ−β)/α}` if
`β < γ`. -/
theorem giles_theorem1_hilbert [IsProbabilityMeasure μ] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] (P : Ω → E) (Pℓ : ℕ → Ω → E) (Y : ℕ → ℕ → Ω → E) (Cost : ℕ → ℕ → Ω → ℝ)
    (V C : ℕ → ℝ)
    {α β γ c₁ c₂ c₃ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hαβγ : min β γ / 2 ≤ α)
    (hP : Integrable P μ) (hPℓ : ∀ ℓ, Integrable (Pℓ ℓ) μ)
    (hY : ∀ ℓ n, 0 < n → MemLp (Y ℓ n) 2 μ)
    (hind : ∀ N : ℕ → ℕ, (∀ ℓ, 0 < N ℓ) →
      Pairwise fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ)
    (hCost_int : ∀ ℓ n, 0 < n → Integrable (Cost ℓ n) μ)
    (hCost_mean : ∀ ℓ (n : ℕ), 0 < n → μ[Cost ℓ n] = n * C ℓ)
    (h_i : ∀ ℓ : ℕ, ‖∫ ω, (Pℓ ℓ ω - P ω) ∂μ‖ ≤ c₁ * (2 : ℝ) ^ (-(α * (ℓ : ℝ))))
    (h_ii₀ : ∀ n, 0 < n → ∫ ω, Y 0 n ω ∂μ = ∫ ω, Pℓ 0 ω ∂μ)
    (h_ii : ∀ ℓ n, 0 < n → ∫ ω, Y (ℓ + 1) n ω ∂μ = ∫ ω, (Pℓ (ℓ + 1) ω - Pℓ ℓ ω) ∂μ)
    (h_var : ∀ ℓ n, 0 < n → ∫ ω, ‖Y ℓ n ω - ∫ ω', Y ℓ n ω' ∂μ‖ ^ 2 ∂μ = V ℓ / n)
    (h_iii : ∀ ℓ, V ℓ ≤ c₂ * (2 : ℝ) ^ (-(β * (ℓ : ℝ))))
    (h_iv : ∀ ℓ, C ℓ ≤ c₃ * (2 : ℝ) ^ (γ * (ℓ : ℝ))) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ ℓ, 0 < N ℓ) ∧
        ∫ ω, ‖∑ ℓ ∈ range (L + 1), Y ℓ (N ℓ) ω - ∫ ω', P ω' ∂μ‖ ^ 2 ∂μ < ε ^ 2 ∧
        μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] ≤ c₄ * complexityBound α β γ ε := by
  obtain ⟨c₄, hc₄, hcore⟩ :=
    mlmc_complexity_core (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) hα hβ hγ hc₁ hc₂ hc₃ hαβγ
  refine ⟨c₄, hc₄, fun ε hε hε1 => ?_⟩
  obtain ⟨L, N, hN, hmse, hcost⟩ := hcore ε hε hε1
  refine ⟨L, N, hN, ?_, ?_⟩
  · -- mean-square error
    have hind' : Set.Pairwise ↑(range (L + 1)) fun i j => IndepFun (Y i (N i)) (Y j (N j)) μ :=
      fun i _ j _ hij => hind N hN hij
    rw [mlmc_mse_hilbert Pℓ (fun ℓ => Y ℓ (N ℓ)) L (∫ ω', P ω' ∂μ) (fun ℓ => hY ℓ (N ℓ) (hN ℓ))
      hPℓ hind' (h_ii₀ (N 0) (hN 0)) (fun ℓ => h_ii ℓ (N (ℓ + 1)) (hN (ℓ + 1)))]
    have hb : ‖(∫ ω, Pℓ L ω ∂μ) - ∫ ω', P ω' ∂μ‖ ^ 2 ≤
        (c₁ * (2 : ℝ) ^ (-(α * (L : ℝ)))) ^ 2 := by
      have h := h_i L
      rw [integral_sub (hPℓ L) hP] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    have hv : ∑ ℓ ∈ range (L + 1), ∫ ω, ‖Y ℓ (N ℓ) ω - ∫ ω', Y ℓ (N ℓ) ω' ∂μ‖ ^ 2 ∂μ ≤
        ∑ ℓ ∈ range (L + 1), Vb β c₂ ℓ / (N ℓ : ℝ) := by
      apply Finset.sum_le_sum
      intro ℓ _
      rw [h_var ℓ (N ℓ) (hN ℓ)]
      exact div_le_div_of_nonneg_right (h_iii ℓ) (by positivity)
    linarith
  · -- cost
    have hE : μ[fun ω => ∑ ℓ ∈ range (L + 1), Cost ℓ (N ℓ) ω] =
        ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ := by
      rw [integral_finsetSum _ fun ℓ _ => hCost_int ℓ (N ℓ) (hN ℓ)]
      exact Finset.sum_congr rfl fun ℓ _ => hCost_mean ℓ (N ℓ) (hN ℓ)
    rw [hE]
    calc ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * C ℓ
        ≤ ∑ ℓ ∈ range (L + 1), (N ℓ : ℝ) * Cb γ c₃ ℓ := by
          apply Finset.sum_le_sum
          intro ℓ _
          exact mul_le_mul_of_nonneg_left (h_iv ℓ) (by positivity)
      _ ≤ c₄ * complexityBound α β γ ε := hcost

end hilbert

/-! ### Other norms -/

/-- **The 2-norm identity fails for other norms** (Giles 2015, §2.5, p. 17: "However this does
not necessarily apply for other norms, and so the variance for the combined multilevel estimator
can not necessarily be expressed in the usual form as `∑_ℓ N_ℓ⁻¹ V_ℓ`").  In `ℝ × ℝ` with its
sup norm `‖(x, y)‖ = max |x| |y|` there are independent, square-integrable, zero-mean random
vectors `a`, `b` on a probability space with `E[‖a + b‖²] = 1` but `E[‖a‖²] + E[‖b‖²] = 2`:
`a = (s₁, 0)`, `b = (0, s₂)` for two independent fair signs `s₁, s₂ = ±1`. -/
theorem sq_norm_add_of_indepFun_fails_sup :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (a b : Ω → ℝ × ℝ),
      IsProbabilityMeasure μ ∧ IndepFun a b μ ∧ MemLp a 2 μ ∧ MemLp b 2 μ ∧
      ∫ ω, a ω ∂μ = 0 ∧ ∫ ω, b ω ∂μ = 0 ∧
      ∫ ω, ‖a ω + b ω‖ ^ 2 ∂μ = 1 ∧ ∫ ω, ‖a ω‖ ^ 2 ∂μ + ∫ ω, ‖b ω‖ ^ 2 ∂μ = 2 := by
  -- a fair coin `ν` on `Bool` and the sign `s`
  obtain ⟨p, hp⟩ : ∃ p : unitInterval, (p : ℝ) = 1 / 2 := ⟨⟨1 / 2, by norm_num⟩, rfl⟩
  obtain ⟨s, hs1, hs2⟩ : ∃ s : Bool → ℝ, s true = 1 ∧ s false = -1 :=
    ⟨fun c => if c then 1 else -1, rfl, rfl⟩
  have habs : ∀ c, |s c| = 1 := by
    intro c
    cases c
    · rw [hs2, abs_neg, abs_one]
    · rw [hs1, abs_one]
  obtain ⟨ν, hν⟩ : ∃ ν : Measure Bool, ν = bernoulliMeasure true false p := ⟨_, rfl⟩
  have hν1 : IsProbabilityMeasure ν := by
    rw [hν]
    infer_instance
  have hsν : ∫ c, s c ∂ν = 0 := by
    rw [hν, integral_bernoulliMeasure, hs1, hs2, hp]
    norm_num
  -- the two random vectors
  obtain ⟨a, ha⟩ : ∃ a : Bool × Bool → ℝ × ℝ, ∀ ω, a ω = (s ω.1, 0) :=
    ⟨fun ω => (s ω.1, 0), fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Bool × Bool → ℝ × ℝ, ∀ ω, b ω = (0, s ω.2) :=
    ⟨fun ω => (0, s ω.2), fun _ => rfl⟩
  have hna : ∀ ω, ‖a ω‖ = 1 := fun ω => by
    rw [ha, Prod.norm_mk, norm_zero, Real.norm_eq_abs, habs]
    exact max_eq_left zero_le_one
  have hnb : ∀ ω, ‖b ω‖ = 1 := fun ω => by
    rw [hb, Prod.norm_mk, norm_zero, Real.norm_eq_abs, habs]
    exact max_eq_right zero_le_one
  have hnab : ∀ ω, ‖a ω + b ω‖ = 1 := fun ω => by
    rw [ha, hb, Prod.mk_add_mk, add_zero, zero_add, Prod.norm_mk, Real.norm_eq_abs,
      Real.norm_eq_abs, habs, habs, max_self]
  have hmeas : ∀ f : Bool × Bool → ℝ × ℝ, AEStronglyMeasurable f (ν.prod ν) := fun f =>
    (measurable_of_finite f).aestronglyMeasurable
  refine ⟨Bool × Bool, inferInstance, ν.prod ν, a, b, inferInstance, ?_,
    MemLp.of_bound (hmeas a) 1 (Filter.Eventually.of_forall fun ω => (hna ω).le),
    MemLp.of_bound (hmeas b) 1 (Filter.Eventually.of_forall fun ω => (hnb ω).le), ?_, ?_, ?_, ?_⟩
  · -- `a` depends only on the first coin and `b` only on the second
    rw [show a = fun ω => (s ω.1, (0 : ℝ)) from funext ha,
      show b = fun ω => ((0 : ℝ), s ω.2) from funext hb]
    exact indepFun_prod (X := fun c => (s c, (0 : ℝ))) (Y := fun c => ((0 : ℝ), s c))
      (measurable_of_finite _) (measurable_of_finite _)
  · rw [show a = fun ω => (s ω.1, (0 : ℝ)) from funext ha,
      integral_pair Integrable.of_finite Integrable.of_finite, integral_zero, integral_fun_fst, hsν,
      smul_zero, Prod.mk_zero_zero]
  · rw [show b = fun ω => ((0 : ℝ), s ω.2) from funext hb,
      integral_pair Integrable.of_finite Integrable.of_finite, integral_zero, integral_fun_snd, hsν,
      smul_zero, Prod.mk_zero_zero]
  · simp [hnab]
  · norm_num [hna, hnb]

end MLMC
