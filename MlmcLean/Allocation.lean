import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Optimal sample allocation for (nested) multilevel Monte Carlo

References:
* M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §1.3 (p. 4 of the
  author's version): the Lagrange-multiplier allocation `N_ℓ = μ √(V_ℓ/C_ℓ)`,
  `μ = ε⁻² ∑ √(V_ℓ C_ℓ)` (unnumbered) and the resulting cost (1.1); §1.2 (p. 3): for two levels,
  "the variance is minimised for a fixed cost by choosing `N₁/N₀ = √(V₁/C₁)/√(V₀/C₀)`".
* I.-B. Haas, M.B. Giles, *A nested MLMC framework for efficient simulations on FPGAs*,
  arXiv:2502.07123 (2025), eq. (6)–(8) and (10)–(12).

Setting.  A finite family of independent estimators indexed by `i ∈ s`; the estimator `i`
uses `n i` samples, each sample having variance `V i` and cost `C i`.  Then

* total variance `= ∑ i ∈ s, V i / n i`      (Giles (2.3), Haas–Giles (7),(11)),
* total cost     `= ∑ i ∈ s, n i * C i`      (Haas–Giles (6),(10)).

The papers minimise the cost for a fixed total variance, treating the sample numbers as real
variables: Giles §1.3 and Haas–Giles (8) take `variance = ε²`; the proof sketch of Giles'
Theorem 1 (p. 7) asks for `V[Y] < ½ε²`.  We use the constraint `variance ≤ τ`, which has the same
minimum.  The Lagrange-multiplier allocation is `lagrangeN`:
`n i = τ⁻¹ √(V i / C i) · ∑ j √(V j C j)`, and the optimal cost is `τ⁻¹ (∑ j √(V j C j))²`.

Here we prove this rigorously:

* `cost_lower_bound` — for **every** real allocation with variance `≤ τ` the cost is at least
  `τ⁻¹ (∑ √(V i C i))²` (Cauchy–Schwarz);
* `optimal_cost_isLeast` — Giles (1.1): this value is the least cost; it is attained by the
  Lagrange-multiplier allocation `lagrangeN`, which meets the variance constraint with equality, and
  by no other allocation (`lagrangeN_unique`);
* `optimal_variance_isLeast`, `twoLevel_optimal_ratio` — the dual problem of Giles §1.2: for a
  fixed cost the least variance, its unique minimiser and, for two levels, the optimal ratio
  `N₁/N₀ = √(V₁/C₁)/√(V₀/C₀)`;
* `optimalN_variance`, `optimalN_cost` — the rounded-up integer allocation
  `⌈lagrangeN⌉₊` meets the variance target and costs at most `τ⁻¹ (∑ √(V i C i))² + ∑ C i`;
  the extra `∑ C i` bounds the rounding-up overhead that Giles' proof sketch of Theorem 1 mentions
  (p. 7).

The nested estimator of Haas–Giles is the special case where the index set is
`(levels) × {low precision, correction}`; see `MlmcLean/Nested.lean`.
-/

open Finset

namespace MLMC

variable {ι : Type*}

/-! ### Two square-root identities -/

lemma sqrt_div_mul_sqrt_mul {V C : ℝ} (hV : 0 ≤ V) (hC : 0 < C) :
    Real.sqrt (V / C) * Real.sqrt (V * C) = V := by
  rw [← Real.sqrt_mul (div_nonneg hV hC.le)]
  have h : V / C * (V * C) = V ^ 2 := by
    calc V / C * (V * C) = V * V * (C / C) := by ring
      _ = V ^ 2 := by rw [div_self hC.ne', mul_one, sq]
  rw [h, Real.sqrt_sq hV]

lemma sqrt_div_mul {V C : ℝ} (hV : 0 ≤ V) (hC : 0 < C) :
    Real.sqrt (V / C) * C = Real.sqrt (V * C) := by
  have h : V * C = V / C * C ^ 2 := by
    calc V * C = V * C * (C / C) := by rw [div_self hC.ne', mul_one]
      _ = V / C * C ^ 2 := by ring
  rw [h, Real.sqrt_mul (div_nonneg hV hC.le), Real.sqrt_sq hC.le]

/-! ### The Lagrange-multiplier value is a lower bound (Cauchy–Schwarz) -/

/-- **Cost lower bound.**  If a (real) allocation `n i > 0` achieves total variance
`∑ V i / n i ≤ τ`, then its total cost satisfies `τ⁻¹ (∑ √(V i C i))² ≤ ∑ n i C i`.
This is Giles (1.1) / Haas–Giles (8),(12) read as an inequality valid for *all* allocations. -/
theorem cost_lower_bound (s : Finset ι) (V C n : ι → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hV : ∀ i ∈ s, 0 ≤ V i) (hC : ∀ i ∈ s, 0 ≤ C i) (hn : ∀ i ∈ s, 0 < n i)
    (hvar : ∑ i ∈ s, V i / n i ≤ τ) :
    τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 ≤ ∑ i ∈ s, n i * C i := by
  have hcs : (∑ i ∈ s, Real.sqrt (n i * C i) * Real.sqrt (V i / n i)) ^ 2 ≤
      (∑ i ∈ s, Real.sqrt (n i * C i) ^ 2) * ∑ i ∈ s, Real.sqrt (V i / n i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s _ _
  have e1 : ∑ i ∈ s, Real.sqrt (n i * C i) * Real.sqrt (V i / n i) =
      ∑ i ∈ s, Real.sqrt (V i * C i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Real.sqrt_mul (mul_nonneg (hn i hi).le (hC i hi))]
    congr 1
    calc n i * C i * (V i / n i) = V i * C i * (n i / n i) := by ring
      _ = V i * C i := by rw [div_self (hn i hi).ne', mul_one]
  have e2 : ∑ i ∈ s, Real.sqrt (n i * C i) ^ 2 = ∑ i ∈ s, n i * C i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (mul_nonneg (hn i hi).le (hC i hi))
  have e3 : ∑ i ∈ s, Real.sqrt (V i / n i) ^ 2 = ∑ i ∈ s, V i / n i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (div_nonneg (hV i hi) (hn i hi).le)
  rw [e1, e2, e3] at hcs
  have hcost : 0 ≤ ∑ i ∈ s, n i * C i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hn i hi).le (hC i hi)
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  calc τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2
      ≤ τ⁻¹ * ((∑ i ∈ s, n i * C i) * ∑ i ∈ s, V i / n i) :=
        mul_le_mul_of_nonneg_left hcs hτi.le
    _ ≤ τ⁻¹ * ((∑ i ∈ s, n i * C i) * τ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvar hcost) hτi.le
    _ = ∑ i ∈ s, n i * C i := by
        rw [mul_comm, mul_assoc, mul_inv_cancel₀ hτ.ne', mul_one]

/-- One term of the Lagrange-multiplier allocation: with `n = τ⁻¹ √(V/C) S`,
`V / n = τ √(V C) / S`. -/
lemma lagrange_variance_term {V C τ S : ℝ} (hV : 0 < V) (hC : 0 < C) (hτ : 0 < τ) (hS : 0 < S) :
    V / (τ⁻¹ * Real.sqrt (V / C) * S) = τ * Real.sqrt (V * C) / S := by
  have harg : 0 < τ⁻¹ * Real.sqrt (V / C) * S :=
    mul_pos (mul_pos (inv_pos.2 hτ) (Real.sqrt_pos.2 (div_pos hV hC))) hS
  rw [div_eq_div_iff harg.ne' hS.ne']
  have hid := sqrt_div_mul_sqrt_mul hV.le hC
  have hττ : τ * τ⁻¹ = 1 := mul_inv_cancel₀ hτ.ne'
  calc V * S
      = (Real.sqrt (V / C) * Real.sqrt (V * C)) * S := by rw [hid]
    _ = (τ * τ⁻¹) * ((Real.sqrt (V / C) * Real.sqrt (V * C)) * S) := by rw [hττ, one_mul]
    _ = τ * Real.sqrt (V * C) * (τ⁻¹ * Real.sqrt (V / C) * S) := by ring

/-! ### The Lagrange-multiplier allocation -/

/-- `∑_{i∈s} √(V_i C_i)`, whose square divided by the variance target is the optimal cost
(Giles 2015, (1.1)). -/
noncomputable def sumSqrtVC (s : Finset ι) (V C : ι → ℝ) : ℝ := ∑ i ∈ s, Real.sqrt (V i * C i)

/-- The Lagrange-multiplier allocation of Giles (2015), §1.3 (p. 4 of the author's version):
`N_i = μ √(V_i/C_i)` with `μ = τ⁻¹ ∑_{j∈s} √(V_j C_j)` (Giles: `τ = ε²`). -/
noncomputable def lagrangeN (s : Finset ι) (V C : ι → ℝ) (τ : ℝ) (i : ι) : ℝ :=
  τ⁻¹ * Real.sqrt (V i / C i) * sumSqrtVC s V C

/-- For `n > 0`: `n (n C + κ² V/n − 2κ√(VC)) = (n√C − κ√V)²`, the defect in the
arithmetic–geometric mean inequality `n C + κ² V/n ≥ 2κ√(VC)` behind the Lagrange-multiplier
allocation (Giles 2015, §1.3, p. 4). -/
lemma lagrange_term {V C n : ℝ} (κ : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C) (hn : 0 < n) :
    n * (n * C + κ ^ 2 * (V / n) - 2 * κ * Real.sqrt (V * C)) =
      (n * Real.sqrt C - κ * Real.sqrt V) ^ 2 := by
  have h1 : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC
  have h2 : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV
  have h3 : n * (V / n) = V := mul_div_cancel₀ V hn.ne'
  rw [Real.sqrt_mul hV C]
  linear_combination (-(n ^ 2)) * h1 + (-(κ ^ 2)) * h2 + κ ^ 2 * h3

section lagrange

variable {s : Finset ι} {V C : ι → ℝ} {τ : ℝ}

lemma sumSqrtVC_pos (hs : s.Nonempty) (hV : ∀ i ∈ s, 0 < V i) (hC : ∀ i ∈ s, 0 < C i) :
    0 < sumSqrtVC s V C :=
  Finset.sum_pos (fun i hi => Real.sqrt_pos.2 (mul_pos (hV i hi) (hC i hi))) hs

lemma lagrangeN_pos (hs : s.Nonempty) (hV : ∀ i ∈ s, 0 < V i) (hC : ∀ i ∈ s, 0 < C i)
    (hτ : 0 < τ) {i : ι} (hVi : 0 < V i) (hCi : 0 < C i) : 0 < lagrangeN s V C τ i :=
  mul_pos (mul_pos (inv_pos.2 hτ) (Real.sqrt_pos.2 (div_pos hVi hCi))) (sumSqrtVC_pos hs hV hC)

/-- The Lagrange-multiplier allocation meets the variance target with equality and costs
`τ⁻¹ (∑ √(V_i C_i))²` (Giles 2015, §1.3, p. 4: "This gives `N_ℓ = μ √(V_ℓ/C_ℓ)`. To achieve an
overall variance of `ε²` then requires that `μ = ε⁻² ∑ √(V_ℓ C_ℓ)`", and (1.1)). -/
theorem lagrangeN_variance_cost (hs : s.Nonempty) (hV : ∀ i ∈ s, 0 < V i)
    (hC : ∀ i ∈ s, 0 < C i) (hτ : 0 < τ) :
    ∑ i ∈ s, V i / lagrangeN s V C τ i = τ ∧
      ∑ i ∈ s, lagrangeN s V C τ i * C i = τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 := by
  have hS := sumSqrtVC_pos hs hV hC
  constructor
  · unfold lagrangeN
    rw [Finset.sum_congr rfl fun i hi => lagrange_variance_term (hV i hi) (hC i hi) hτ hS,
      ← Finset.sum_div, ← Finset.mul_sum]
    change τ * sumSqrtVC s V C / sumSqrtVC s V C = τ
    rw [mul_div_assoc, div_self hS.ne', mul_one]
  · have hterm : ∀ i ∈ s, lagrangeN s V C τ i * C i =
        τ⁻¹ * sumSqrtVC s V C * Real.sqrt (V i * C i) := fun i hi => by
      unfold lagrangeN
      rw [← sqrt_div_mul (hV i hi).le (hC i hi)]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    change τ⁻¹ * sumSqrtVC s V C * sumSqrtVC s V C = τ⁻¹ * sumSqrtVC s V C ^ 2
    ring

/-- **Uniqueness of the optimal allocation.**  An allocation `n_i > 0` with variance `≤ τ` whose
cost equals the optimal cost `τ⁻¹ (∑ √(V_i C_i))²` is the Lagrange-multiplier allocation
(Giles 2015, §1.3, p. 4). -/
theorem lagrangeN_unique (hτ : 0 < τ) (hV : ∀ i ∈ s, 0 < V i) (hC : ∀ i ∈ s, 0 < C i)
    (n : ι → ℝ) (hn : ∀ i ∈ s, 0 < n i) (hvar : ∑ i ∈ s, V i / n i ≤ τ)
    (hcost : ∑ i ∈ s, n i * C i = τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2) :
    ∀ i ∈ s, n i = lagrangeN s V C τ i := by
  have key : ∀ i ∈ s, n i * Real.sqrt (C i) =
      τ⁻¹ * (∑ j ∈ s, Real.sqrt (V j * C j)) * Real.sqrt (V i) := by
    generalize hS : ∑ j ∈ s, Real.sqrt (V j * C j) = S at hcost ⊢
    have hterm : ∀ i ∈ s, n i * (n i * C i + (τ⁻¹ * S) ^ 2 * (V i / n i) -
        2 * (τ⁻¹ * S) * Real.sqrt (V i * C i)) =
        (n i * Real.sqrt (C i) - τ⁻¹ * S * Real.sqrt (V i)) ^ 2 :=
      fun i hi => lagrange_term (τ⁻¹ * S) (hV i hi).le (hC i hi).le (hn i hi)
    have hd0 : ∀ i ∈ s, 0 ≤ n i * C i + (τ⁻¹ * S) ^ 2 * (V i / n i) -
        2 * (τ⁻¹ * S) * Real.sqrt (V i * C i) := by
      intro i hi
      have h2 := sq_nonneg (n i * Real.sqrt (C i) - τ⁻¹ * S * Real.sqrt (V i))
      rw [← hterm i hi] at h2
      exact nonneg_of_mul_nonneg_right h2 (hn i hi)
    have hsum : ∑ i ∈ s, (n i * C i + (τ⁻¹ * S) ^ 2 * (V i / n i) -
        2 * (τ⁻¹ * S) * Real.sqrt (V i * C i)) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg hd0)
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hcost, hS]
      have h3 : (τ⁻¹ * S) ^ 2 * ∑ i ∈ s, V i / n i ≤ (τ⁻¹ * S) ^ 2 * τ :=
        mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
      have h4 : τ⁻¹ * S ^ 2 + (τ⁻¹ * S) ^ 2 * τ - 2 * (τ⁻¹ * S) * S = 0 := by
        have hττ : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ.ne'
        linear_combination (τ⁻¹ * S ^ 2) * hττ
      linarith
    intro i hi
    have h1 := hterm i hi
    rw [(Finset.sum_eq_zero_iff_of_nonneg hd0).1 hsum i hi, mul_zero] at h1
    have h5 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h1.symm
    linarith
  intro i hi
  have hsC : Real.sqrt (C i) ≠ 0 := (Real.sqrt_pos.2 (hC i hi)).ne'
  calc n i = n i * Real.sqrt (C i) / Real.sqrt (C i) := by
        rw [mul_div_assoc, div_self hsC, mul_one]
    _ = τ⁻¹ * (∑ j ∈ s, Real.sqrt (V j * C j)) * Real.sqrt (V i) / Real.sqrt (C i) := by
        rw [key i hi]
    _ = lagrangeN s V C τ i := by
        unfold lagrangeN sumSqrtVC
        rw [Real.sqrt_div (hV i hi).le]
        ring

end lagrange

/-- **Giles (1.1)**, **Haas–Giles (8)**: the optimal cost and the optimal allocation.
Among all real allocations `n i > 0` (`i ∈ s`) with total variance `∑ V i / n i ≤ τ`, the least
cost `∑ n i C i` is `τ⁻¹ (∑ √(V i C i))²`; it is attained by the Lagrange-multiplier allocation
`lagrangeN` (`n i = μ √(V i / C i)`, `μ = τ⁻¹ ∑ j √(V j C j)`; Giles 2015, §1.3, p. 4 of the
author's version, with `τ = ε²`), which meets the variance constraint with equality, and by no
other allocation. -/
theorem optimal_cost_isLeast (s : Finset ι) (V C : ι → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hs : s.Nonempty) (hV : ∀ i ∈ s, 0 < V i) (hC : ∀ i ∈ s, 0 < C i) :
    IsLeast {c | ∃ n : ι → ℝ, (∀ i ∈ s, 0 < n i) ∧ ∑ i ∈ s, V i / n i ≤ τ ∧
        c = ∑ i ∈ s, n i * C i}
      (τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2) ∧
    ((∀ i ∈ s, 0 < lagrangeN s V C τ i) ∧ ∑ i ∈ s, V i / lagrangeN s V C τ i = τ ∧
      ∑ i ∈ s, lagrangeN s V C τ i * C i = τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2) ∧
    ∀ n : ι → ℝ, (∀ i ∈ s, 0 < n i) → ∑ i ∈ s, V i / n i ≤ τ →
      ∑ i ∈ s, n i * C i = τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 →
      ∀ i ∈ s, n i = lagrangeN s V C τ i := by
  have hpos : ∀ i ∈ s, 0 < lagrangeN s V C τ i :=
    fun i hi => lagrangeN_pos hs hV hC hτ (hV i hi) (hC i hi)
  obtain ⟨hvarL, hcostL⟩ := lagrangeN_variance_cost hs hV hC hτ
  refine ⟨⟨⟨lagrangeN s V C τ, hpos, hvarL.le, hcostL.symm⟩, ?_⟩, ⟨hpos, hvarL, hcostL⟩,
    fun n hn hvar hcost => lagrangeN_unique hτ hV hC n hn hvar hcost⟩
  -- every admissible allocation costs at least `τ⁻¹ S²` (Cauchy–Schwarz)
  rintro c ⟨n, hn, hvar, rfl⟩
  exact cost_lower_bound s V C n hτ (fun i hi => (hV i hi).le) (fun i hi => (hC i hi).le) hn hvar

/-- **The dual problem: least variance for a given cost** (Giles 2015, §1.2, p. 3, where "the
variance is minimised for a fixed cost"; the dual of (1.1)).  Among all real allocations
`n i > 0` (`i ∈ s`) with cost `∑ n i C i ≤ B`, the least variance `∑ V i / n i` is
`B⁻¹ (∑ √(V i C i))²`; it is attained by `n i = B √(V i / C i) / ∑ j √(V j C j)`, which costs
exactly `B`, and by no other allocation. -/
theorem optimal_variance_isLeast (s : Finset ι) (V C : ι → ℝ) {B : ℝ} (hB : 0 < B)
    (hs : s.Nonempty) (hV : ∀ i ∈ s, 0 < V i) (hC : ∀ i ∈ s, 0 < C i) :
    IsLeast {v | ∃ n : ι → ℝ, (∀ i ∈ s, 0 < n i) ∧ ∑ i ∈ s, n i * C i ≤ B ∧
        v = ∑ i ∈ s, V i / n i}
      (B⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2) ∧
    ∑ i ∈ s, B * Real.sqrt (V i / C i) / (∑ j ∈ s, Real.sqrt (V j * C j)) * C i = B ∧
    ∀ n : ι → ℝ, (∀ i ∈ s, 0 < n i) → ∑ i ∈ s, n i * C i ≤ B →
      ∑ i ∈ s, V i / n i = B⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 →
      ∀ i ∈ s, n i = B * Real.sqrt (V i / C i) / ∑ j ∈ s, Real.sqrt (V j * C j) := by
  have hS : 0 < ∑ i ∈ s, Real.sqrt (V i * C i) := sumSqrtVC_pos hs hV hC
  set S := ∑ i ∈ s, Real.sqrt (V i * C i) with hS_def
  -- the dual allocation is the Lagrange allocation for the variance target `τ = S² / B`
  set τ : ℝ := S ^ 2 / B with hτ_def
  have hτ : 0 < τ := div_pos (pow_pos hS 2) hB
  have hτinv : τ⁻¹ * S ^ 2 = B := by
    rw [hτ_def, inv_div, div_mul_cancel₀ _ (pow_pos hS 2).ne']
  have hdual : ∀ i, lagrangeN s V C τ i = B * Real.sqrt (V i / C i) / S := fun i => by
    unfold lagrangeN sumSqrtVC
    rw [← hS_def, hτ_def, inv_div, sq S, div_mul_eq_mul_div, div_mul_eq_mul_div,
      mul_div_mul_right _ _ hS.ne']
  obtain ⟨hvarL, hcostL⟩ := lagrangeN_variance_cost hs hV hC hτ
  rw [← hS_def, hτinv] at hcostL
  have hpos : ∀ i ∈ s, 0 < lagrangeN s V C τ i :=
    fun i hi => lagrangeN_pos hs hV hC hτ (hV i hi) (hC i hi)
  have hval : B⁻¹ * S ^ 2 = τ := by
    rw [hτ_def]
    ring
  -- the variance of any allocation of cost `≤ B` is at least `S² / B`
  have hlow : ∀ n : ι → ℝ, (∀ i ∈ s, 0 < n i) → ∑ i ∈ s, n i * C i ≤ B →
      τ ≤ ∑ i ∈ s, V i / n i := by
    intro n hn hcost
    have hv : 0 < ∑ i ∈ s, V i / n i :=
      Finset.sum_pos (fun i hi => div_pos (hV i hi) (hn i hi)) hs
    have h := cost_lower_bound s V C n hv (fun i hi => (hV i hi).le) (fun i hi => (hC i hi).le)
      hn le_rfl
    rw [← hS_def] at h
    have h2 : (∑ i ∈ s, V i / n i)⁻¹ * S ^ 2 ≤ B := h.trans hcost
    rw [inv_mul_le_iff₀ hv] at h2
    rw [hτ_def, div_le_iff₀ hB]
    exact h2
  refine ⟨⟨⟨lagrangeN s V C τ, hpos, hcostL.le, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [hvarL, hval]
  · rintro v ⟨n, hn, hcost, rfl⟩
    rw [hval]
    exact hlow n hn hcost
  · calc ∑ i ∈ s, B * Real.sqrt (V i / C i) / S * C i = ∑ i ∈ s, lagrangeN s V C τ i * C i :=
          Finset.sum_congr rfl fun i _ => by rw [hdual]
      _ = B := hcostL
  · intro n hn hcost hvar i hi
    rw [hval] at hvar
    -- `n` has variance `τ` and cost `≤ B = τ⁻¹ S²`, so its cost is the optimal cost
    have hcost' : ∑ i ∈ s, n i * C i = τ⁻¹ * S ^ 2 := by
      refine le_antisymm (hcost.trans_eq hτinv.symm) ?_
      have h := cost_lower_bound s V C n hτ (fun i hi => (hV i hi).le)
        (fun i hi => (hC i hi).le) hn hvar.le
      rw [← hS_def] at h
      exact h
    rw [← hdual]
    exact lagrangeN_unique hτ hV hC n hn hvar.le hcost' i hi

/-- **Two-level MLMC, the optimal ratio** (Giles 2015, §1.2, p. 3): "treating the integers
`N₀, N₁` as real variables and performing a constrained minimisation using a Lagrange multiplier,
the variance is minimised for a fixed cost by choosing `N₁/N₀ = √(V₁/C₁)/√(V₀/C₀)`".  For positive
variances `V₀, V₁` and costs `C₀, C₁`, and `n₀, n₁ > 0` with cost `n₀ C₀ + n₁ C₁ = B`, the pair
`(n₀, n₁)` has the least variance `V₀/n₀ + V₁/n₁` among all pairs of cost `B` if and only if
`n₁/n₀ = √(V₁/C₁)/√(V₀/C₀)`. -/
theorem twoLevel_optimal_ratio {V₀ V₁ C₀ C₁ B : ℝ} (hV₀ : 0 < V₀) (hV₁ : 0 < V₁)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hB : 0 < B) {n₀ n₁ : ℝ} (hn₀ : 0 < n₀) (hn₁ : 0 < n₁)
    (hcost : n₀ * C₀ + n₁ * C₁ = B) :
    (∀ m₀ m₁ : ℝ, 0 < m₀ → 0 < m₁ → m₀ * C₀ + m₁ * C₁ = B →
        V₀ / n₀ + V₁ / n₁ ≤ V₀ / m₀ + V₁ / m₁) ↔
      n₁ / n₀ = Real.sqrt (V₁ / C₁) / Real.sqrt (V₀ / C₀) := by
  -- the two levels as the index set `Fin 2`
  have hV : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < (![V₀, V₁] : Fin 2 → ℝ) i :=
    fun i _ => Fin.forall_fin_two.2 ⟨hV₀, hV₁⟩ i
  have hC : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < (![C₀, C₁] : Fin 2 → ℝ) i :=
    fun i _ => Fin.forall_fin_two.2 ⟨hC₀, hC₁⟩ i
  obtain ⟨⟨-, hleast⟩, -, huniq⟩ :=
    optimal_variance_isLeast Finset.univ ![V₀, V₁] ![C₀, C₁] hB Finset.univ_nonempty hV hC
  have hr₀ : 0 < Real.sqrt (V₀ / C₀) := Real.sqrt_pos.2 (div_pos hV₀ hC₀)
  have hr₁ : 0 < Real.sqrt (V₁ / C₁) := Real.sqrt_pos.2 (div_pos hV₁ hC₁)
  have hS : 0 < Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁) :=
    add_pos (Real.sqrt_pos.2 (mul_pos hV₀ hC₀)) (Real.sqrt_pos.2 (mul_pos hV₁ hC₁))
  have hc0 := sqrt_div_mul hV₀.le hC₀
  have hc1 := sqrt_div_mul hV₁.le hC₁
  have hv0 := sqrt_div_mul_sqrt_mul hV₀.le hC₀
  have hv1 := sqrt_div_mul_sqrt_mul hV₁.le hC₁
  -- the lower bound `B⁻¹ S²` and the uniqueness of the optimum, for two levels
  have hlow : ∀ m₀ m₁ : ℝ, 0 < m₀ → 0 < m₁ → m₀ * C₀ + m₁ * C₁ ≤ B →
      B⁻¹ * (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) ^ 2 ≤ V₀ / m₀ + V₁ / m₁ := by
    intro m₀ m₁ hm₀ hm₁ hmc
    have h := (mem_lowerBounds.1 hleast)
      (∑ i : Fin 2, (![V₀, V₁] : Fin 2 → ℝ) i / (![m₀, m₁] : Fin 2 → ℝ) i)
      ⟨![m₀, m₁], fun i _ => Fin.forall_fin_two.2 ⟨hm₀, hm₁⟩ i,
        by rw [Fin.sum_univ_two]; exact hmc, rfl⟩
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
    exact h
  have hopt : ∀ m₀ m₁ : ℝ, 0 < m₀ → 0 < m₁ → m₀ * C₀ + m₁ * C₁ ≤ B →
      V₀ / m₀ + V₁ / m₁ = B⁻¹ * (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) ^ 2 →
      m₀ = B * Real.sqrt (V₀ / C₀) / (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) ∧
        m₁ = B * Real.sqrt (V₁ / C₁) / (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) := by
    intro m₀ m₁ hm₀ hm₁ hmc hmv
    have hpos : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < (![m₀, m₁] : Fin 2 → ℝ) i :=
      fun i _ => Fin.forall_fin_two.2 ⟨hm₀, hm₁⟩ i
    have hc' : ∑ i : Fin 2, (![m₀, m₁] : Fin 2 → ℝ) i * (![C₀, C₁] : Fin 2 → ℝ) i ≤ B := by
      rw [Fin.sum_univ_two]
      exact hmc
    have hv' : ∑ i : Fin 2, (![V₀, V₁] : Fin 2 → ℝ) i / (![m₀, m₁] : Fin 2 → ℝ) i =
        B⁻¹ * (∑ i : Fin 2,
          Real.sqrt ((![V₀, V₁] : Fin 2 → ℝ) i * (![C₀, C₁] : Fin 2 → ℝ) i)) ^ 2 := by
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      exact hmv
    have h0 := huniq ![m₀, m₁] hpos hc' hv' 0 (Finset.mem_univ _)
    have h1 := huniq ![m₀, m₁] hpos hc' hv' 1 (Finset.mem_univ _)
    rw [Fin.sum_univ_two] at h0 h1
    exact ⟨h0, h1⟩
  -- the optimal pair has cost `B` and variance `B⁻¹ S²`
  have hcostOpt : B * Real.sqrt (V₀ / C₀) / (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) * C₀ +
      B * Real.sqrt (V₁ / C₁) / (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) * C₁ = B := by
    calc _ = B / (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) *
          (Real.sqrt (V₀ / C₀) * C₀ + Real.sqrt (V₁ / C₁) * C₁) := by ring
      _ = B := by rw [hc0, hc1, div_mul_cancel₀ _ hS.ne']
  have hvarOpt : V₀ / (B * Real.sqrt (V₀ / C₀) / (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁))) +
      V₁ / (B * Real.sqrt (V₁ / C₁) / (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁))) =
      B⁻¹ * (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) ^ 2 := by
    have e0 : V₀ / Real.sqrt (V₀ / C₀) = Real.sqrt (V₀ * C₀) := by
      rw [div_eq_iff hr₀.ne']
      linear_combination -hv0
    have e1 : V₁ / Real.sqrt (V₁ / C₁) = Real.sqrt (V₁ * C₁) := by
      rw [div_eq_iff hr₁.ne']
      linear_combination -hv1
    calc _ = (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) / B *
          (V₀ / Real.sqrt (V₀ / C₀) + V₁ / Real.sqrt (V₁ / C₁)) := by ring
      _ = B⁻¹ * (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) ^ 2 := by
          rw [e0, e1]
          ring
  constructor
  · -- a minimiser has the least variance, hence is the optimal pair
    intro hmin
    have hle := hmin _ _ (div_pos (mul_pos hB hr₀) hS) (div_pos (mul_pos hB hr₁) hS) hcostOpt
    rw [hvarOpt] at hle
    obtain ⟨h0, h1⟩ := hopt n₀ n₁ hn₀ hn₁ hcost.le
      (le_antisymm hle (hlow n₀ n₁ hn₀ hn₁ hcost.le))
    rw [h0, h1, div_div_div_cancel_right₀ hS.ne', mul_div_mul_left _ _ hB.ne']
  · -- the ratio and the cost determine the optimal pair
    intro hratio
    rw [div_eq_div_iff hn₀.ne' hr₀.ne'] at hratio
    have h0 : n₀ = B * Real.sqrt (V₀ / C₀) / (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) := by
      rw [eq_div_iff hS.ne', ← hc0, ← hc1]
      linear_combination Real.sqrt (V₀ / C₀) * hcost - C₁ * hratio
    have h1 : n₁ = B * Real.sqrt (V₁ / C₁) / (Real.sqrt (V₀ * C₀) + Real.sqrt (V₁ * C₁)) := by
      rw [eq_div_iff hS.ne', ← hc0, ← hc1]
      linear_combination Real.sqrt (V₁ / C₁) * hcost + C₀ * hratio
    intro m₀ m₁ hm₀ hm₁ hmc
    rw [h0, h1, hvarOpt]
    exact hlow m₀ m₁ hm₀ hm₁ hmc.le

/-! ### The rounded-up optimal allocation -/

/-- The optimal number of samples `lagrangeN s V C τ i = τ⁻¹ √(V i / C i) · ∑ √(V j C j)`
(Giles 2015, §1.3, p. 4: `N_ℓ = μ √(V_ℓ/C_ℓ)` with `μ = ε⁻² ∑ √(V_ℓ C_ℓ)`), rounded **up** to an
integer (Giles, proof sketch of Theorem 1, p. 7: "the optimal value is rounded up to the nearest
integer"). -/
noncomputable def optimalN (s : Finset ι) (V C : ι → ℝ) (τ : ℝ) (i : ι) : ℕ :=
  ⌈lagrangeN s V C τ i⌉₊

section positive

variable {s : Finset ι} {V C : ι → ℝ} {τ : ℝ}

/-- The rounded-up allocation is positive at every index (Giles 2015, proof sketch of Theorem 1,
p. 7: every level in use gets at least one sample). -/
lemma optimalN_pos (hs : s.Nonempty) (hV : ∀ i, 0 < V i) (hC : ∀ i, 0 < C i)
    (hτ : 0 < τ) (i : ι) : 0 < optimalN s V C τ i :=
  Nat.ceil_pos.2 (lagrangeN_pos hs (fun j _ => hV j) (fun j _ => hC j) hτ (hV i) (hC i))

/-- The rounded-up optimal allocation meets the variance target `τ` (Giles 2015, §1.3, p. 4, and
the proof sketch of Theorem 1, p. 7, with `τ = ½ε²`). -/
theorem optimalN_variance (hs : s.Nonempty) (hV : ∀ i ∈ s, 0 < V i) (hC : ∀ i ∈ s, 0 < C i)
    (hτ : 0 < τ) :
    ∑ i ∈ s, V i / (optimalN s V C τ i : ℝ) ≤ τ := by
  calc ∑ i ∈ s, V i / (optimalN s V C τ i : ℝ)
      ≤ ∑ i ∈ s, V i / lagrangeN s V C τ i :=
        Finset.sum_le_sum fun i hi => div_le_div_of_nonneg_left (hV i hi).le
          (lagrangeN_pos hs hV hC hτ (hV i hi) (hC i hi)) (Nat.le_ceil _)
    _ = τ := (lagrangeN_variance_cost hs hV hC hτ).1

/-- The rounded-up optimal allocation costs at most the Lagrange value `τ⁻¹ (∑ √(V i C i))²` plus
`∑ C i` (at most one extra sample per index), which bounds the rounding-up overhead that Giles'
proof sketch of Theorem 1 mentions (Giles 2015, p. 7). -/
theorem optimalN_cost (hs : s.Nonempty) (hV : ∀ i ∈ s, 0 < V i) (hC : ∀ i ∈ s, 0 < C i)
    (hτ : 0 < τ) :
    ∑ i ∈ s, (optimalN s V C τ i : ℝ) * C i ≤
      τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 + ∑ i ∈ s, C i := by
  have h1 : ∀ i ∈ s, (optimalN s V C τ i : ℝ) * C i ≤ lagrangeN s V C τ i * C i + C i := by
    intro i hi
    have hceil : (optimalN s V C τ i : ℝ) ≤ lagrangeN s V C τ i + 1 :=
      (Nat.ceil_lt_add_one (lagrangeN_pos hs hV hC hτ (hV i hi) (hC i hi)).le).le
    calc (optimalN s V C τ i : ℝ) * C i ≤ (lagrangeN s V C τ i + 1) * C i :=
          mul_le_mul_of_nonneg_right hceil (hC i hi).le
      _ = lagrangeN s V C τ i * C i + C i := by ring
  calc ∑ i ∈ s, (optimalN s V C τ i : ℝ) * C i
      ≤ ∑ i ∈ s, (lagrangeN s V C τ i * C i + C i) := Finset.sum_le_sum h1
    _ = τ⁻¹ * (∑ i ∈ s, Real.sqrt (V i * C i)) ^ 2 + ∑ i ∈ s, C i := by
        rw [Finset.sum_add_distrib, (lagrangeN_variance_cost hs hV hC hτ).2]

end positive

end MLMC
