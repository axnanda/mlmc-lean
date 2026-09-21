import Mathlib

/-!
# Optimal sample allocation for (nested) multilevel Monte Carlo

References:
* M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §1.3, eq. (1.1)–(1.2).
* I.-B. Haas, M.B. Giles, *A nested MLMC framework for efficient simulations on FPGAs*,
  arXiv:2502.07123 (2025), eq. (6)–(8) and (10)–(12).

Setting.  A finite family of independent estimators indexed by `i ∈ s`; the estimator `i`
uses `n i` samples, each sample having variance `V i` and cost `C i`.  Then

* total variance `= ∑ i ∈ s, V i / n i`      (Giles (2.3), Haas–Giles (7),(11)),
* total cost     `= ∑ i ∈ s, n i * C i`      (Haas–Giles (6),(10)).

The papers minimise the cost subject to `variance ≤ τ` (Giles takes `τ = ε²/2`, Haas–Giles take
`τ = ε²`) with a Lagrange multiplier and obtain the optimal allocation
`n i = τ⁻¹ √(V i / C i) · ∑ j √(V j C j)` and the optimal cost `τ⁻¹ (∑ j √(V j C j))²`.

Here we prove this rigorously:

* `cost_lower_bound` — for **every** real allocation with variance `≤ τ` the cost is at least
  `τ⁻¹ (∑ √(V i C i))²` (Cauchy–Schwarz), so the Lagrange value is a true minimum;
* `optimalN_variance`, `optimalN_cost` — the rounded-up integer allocation
  `⌈τ⁻¹ √(V i / C i) · S⌉₊` meets the variance target and costs at most
  `τ⁻¹ (∑ √(V i C i))² + ∑ C i`; the extra `∑ C i` is exactly the rounding-up effect Giles
  mentions in the proof of his Theorem 1.

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

/-! ### The rounded-up optimal allocation -/

/-- `S = ∑ i ∈ s, √(V i C i)`, the quantity whose square gives the optimal cost. -/
noncomputable def S (s : Finset ι) (V C : ι → ℝ) : ℝ := ∑ i ∈ s, Real.sqrt (V i * C i)

/-- Giles (1.2): the optimal number of samples `τ⁻¹ √(V i / C i) · S`, rounded **up** to an
integer (Giles: "the optimal value is rounded up to the nearest integer"). -/
noncomputable def optimalN (s : Finset ι) (V C : ι → ℝ) (τ : ℝ) (i : ι) : ℕ :=
  ⌈τ⁻¹ * Real.sqrt (V i / C i) * S s V C⌉₊

section positive

variable {s : Finset ι} {V C : ι → ℝ} {τ : ℝ}

lemma S_pos (hs : s.Nonempty) (hV : ∀ i, 0 < V i) (hC : ∀ i, 0 < C i) : 0 < S s V C :=
  Finset.sum_pos (fun i _ => Real.sqrt_pos.2 (mul_pos (hV i) (hC i))) hs

lemma optimalN_arg_pos (hs : s.Nonempty) (hV : ∀ i, 0 < V i) (hC : ∀ i, 0 < C i)
    (hτ : 0 < τ) (i : ι) : 0 < τ⁻¹ * Real.sqrt (V i / C i) * S s V C :=
  mul_pos (mul_pos (inv_pos.2 hτ) (Real.sqrt_pos.2 (div_pos (hV i) (hC i)))) (S_pos hs hV hC)

lemma optimalN_pos (hs : s.Nonempty) (hV : ∀ i, 0 < V i) (hC : ∀ i, 0 < C i)
    (hτ : 0 < τ) (i : ι) : 0 < optimalN s V C τ i :=
  Nat.ceil_pos.2 (optimalN_arg_pos hs hV hC hτ i)

/-- The rounded-up optimal allocation meets the variance target `τ`. -/
theorem optimalN_variance (hs : s.Nonempty) (hV : ∀ i, 0 < V i) (hC : ∀ i, 0 < C i)
    (hτ : 0 < τ) :
    ∑ i ∈ s, V i / (optimalN s V C τ i : ℝ) ≤ τ := by
  have hS := S_pos hs hV hC
  have h1 : ∀ i ∈ s, V i / (optimalN s V C τ i : ℝ) ≤ τ * Real.sqrt (V i * C i) / S s V C := by
    intro i _
    have harg := optimalN_arg_pos hs hV hC hτ i
    calc V i / (optimalN s V C τ i : ℝ)
        ≤ V i / (τ⁻¹ * Real.sqrt (V i / C i) * S s V C) :=
          div_le_div_of_nonneg_left (hV i).le harg (Nat.le_ceil _)
      _ = τ * Real.sqrt (V i * C i) / S s V C := by
          rw [div_eq_div_iff harg.ne' hS.ne']
          have hid := sqrt_div_mul_sqrt_mul (hV i).le (hC i)
          have hττ : τ * τ⁻¹ = 1 := mul_inv_cancel₀ hτ.ne'
          calc V i * S s V C
              = (Real.sqrt (V i / C i) * Real.sqrt (V i * C i)) * S s V C := by rw [hid]
            _ = (τ * τ⁻¹) * ((Real.sqrt (V i / C i) * Real.sqrt (V i * C i)) * S s V C) := by
                rw [hττ, one_mul]
            _ = τ * Real.sqrt (V i * C i) * (τ⁻¹ * Real.sqrt (V i / C i) * S s V C) := by ring
  calc ∑ i ∈ s, V i / (optimalN s V C τ i : ℝ)
      ≤ ∑ i ∈ s, τ * Real.sqrt (V i * C i) / S s V C := Finset.sum_le_sum h1
    _ = τ := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
        change τ * S s V C / S s V C = τ
        rw [mul_div_assoc, div_self hS.ne', mul_one]

/-- The rounded-up optimal allocation costs at most the Lagrange value `τ⁻¹ S²` plus the
rounding-up overhead `∑ C i` (one extra sample per index). -/
theorem optimalN_cost (hs : s.Nonempty) (hV : ∀ i, 0 < V i) (hC : ∀ i, 0 < C i) (hτ : 0 < τ) :
    ∑ i ∈ s, (optimalN s V C τ i : ℝ) * C i ≤ τ⁻¹ * (S s V C) ^ 2 + ∑ i ∈ s, C i := by
  have h1 : ∀ i ∈ s, (optimalN s V C τ i : ℝ) * C i ≤
      τ⁻¹ * Real.sqrt (V i * C i) * S s V C + C i := by
    intro i _
    have harg := (optimalN_arg_pos hs hV hC hτ i).le
    have hceil : (optimalN s V C τ i : ℝ) ≤ τ⁻¹ * Real.sqrt (V i / C i) * S s V C + 1 :=
      (Nat.ceil_lt_add_one harg).le
    calc (optimalN s V C τ i : ℝ) * C i
        ≤ (τ⁻¹ * Real.sqrt (V i / C i) * S s V C + 1) * C i :=
          mul_le_mul_of_nonneg_right hceil (hC i).le
      _ = τ⁻¹ * (Real.sqrt (V i / C i) * C i) * S s V C + C i := by ring
      _ = τ⁻¹ * Real.sqrt (V i * C i) * S s V C + C i := by
          rw [sqrt_div_mul (hV i).le (hC i)]
  calc ∑ i ∈ s, (optimalN s V C τ i : ℝ) * C i
      ≤ ∑ i ∈ s, (τ⁻¹ * Real.sqrt (V i * C i) * S s V C + C i) := Finset.sum_le_sum h1
    _ = τ⁻¹ * (S s V C) ^ 2 + ∑ i ∈ s, C i := by
        rw [Finset.sum_add_distrib]
        congr 1
        have : ∑ i ∈ s, τ⁻¹ * Real.sqrt (V i * C i) * S s V C =
            τ⁻¹ * S s V C * ∑ i ∈ s, Real.sqrt (V i * C i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this]
        change τ⁻¹ * S s V C * S s V C = τ⁻¹ * S s V C ^ 2
        ring

end positive

end MLMC
