import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Multi-indices, cross-differences and box telescoping

Reference: M.B. Giles, *Multilevel Monte Carlo methods*, Acta Numerica 24 (2015), §2.4
("Multi-Index Monte Carlo", after Haji-Ali, Nobile & Tempone 2014a), p. 12–13.

In MIMC the level `ℓ = (ℓ_1, …, ℓ_D)` is a vector of non-negative integers.  Giles defines the
backward difference in direction `d`, `Δ_d P_ℓ ≡ P_ℓ − P_{ℓ−e_d}`, the cross-difference

  `ΔP_ℓ ≡ (∏_{d=1}^{D} Δ_d) P_ℓ`,

and states the telescoping sum `E[P] = ∑_{ℓ ≥ 0} E[ΔP_ℓ]`.  As in the one-dimensional case
(`P_{−1} ≡ 0`), `P_ℓ` is taken to be `0` when `ℓ` has a negative entry.

This file defines the cross-difference (`crossDiff`) and proves the finite form of the telescoping
sum behind that identity: summing `ΔP` over the box `{ℓ : ℓ_d ≤ k_d for all d}` gives `P_k`
(`sum_crossDiff`).  The infinite form is proved in `MlmcLean/Theorem2.lean`: along boxes from
condition i) of Theorem 2 (`tendsto_sum_box_integral_crossDiff`), and as an absolutely convergent
series under conditions i)–iii) (`hasSum_integral_crossDiff`).
-/

open Finset

namespace MLMC

variable {D : ℕ}

/-- Splitting a sum over a box `∏_d t_d ⊆ ℕ^{D+1}` into the first coordinate and the rest. -/
lemma sum_piFinset_succ (t : Fin (D + 1) → Finset ℕ) (f : (Fin (D + 1) → ℕ) → ℝ) :
    ∑ ℓ ∈ Fintype.piFinset t, f ℓ =
      ∑ j ∈ t 0, ∑ m ∈ Fintype.piFinset (Fin.tail t), f (Fin.cons j m) := by
  rw [← Finset.sum_product (s := t 0) (t := Fintype.piFinset (Fin.tail t))
    (f := fun q : ℕ × (Fin D → ℕ) => f (Fin.cons q.1 q.2))]
  refine Finset.sum_nbij' (fun ℓ => (ℓ 0, Fin.tail ℓ)) (fun q => Fin.cons q.1 q.2)
    ?_ ?_ ?_ ?_ ?_
  · intro ℓ hℓ
    rw [Fintype.mem_piFinset] at hℓ
    simp only [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨hℓ 0, fun i => hℓ i.succ⟩
  · rintro ⟨j, m⟩ hq
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hq
    rw [Fintype.mem_piFinset]
    intro i
    induction i using Fin.cases with
    | zero => simpa using hq.1
    | succ i => simpa [Fin.tail] using hq.2 i
  · intro ℓ _
    exact Fin.cons_self_tail ℓ
  · rintro ⟨j, m⟩ _
    simp
  · intro ℓ _
    exact congrArg f (Fin.cons_self_tail ℓ).symm

/-- The **cross-difference** `ΔP_ℓ = (∏_{d=1}^{D} Δ_d) P_ℓ` of Giles (2015), §2.4, with
`Δ_d P_ℓ = P_ℓ − P_{ℓ−e_d}` and `P ≡ 0` at indices with a negative entry.  It is computed by
peeling off the first direction: `ΔP_ℓ = Δ_1 (Δ_2 ⋯ Δ_D P)_ℓ`, i.e. the cross-difference in the
remaining directions at `ℓ_1`, minus the same at `ℓ_1 − 1` (absent when `ℓ_1 = 0`). -/
noncomputable def crossDiff : {D : ℕ} → ((Fin D → ℕ) → ℝ) → (Fin D → ℕ) → ℝ
  | 0, p, ℓ => p ℓ
  | _ + 1, p, ℓ =>
      crossDiff (fun m => p (Fin.cons (ℓ 0) m)) (Fin.tail ℓ) -
        if ℓ 0 = 0 then 0 else crossDiff (fun m => p (Fin.cons (ℓ 0 - 1) m)) (Fin.tail ℓ)

lemma crossDiff_zero (p : (Fin 0 → ℕ) → ℝ) (ℓ : Fin 0 → ℕ) : crossDiff p ℓ = p ℓ := rfl

lemma crossDiff_succ (p : (Fin (D + 1) → ℕ) → ℝ) (ℓ : Fin (D + 1) → ℕ) :
    crossDiff p ℓ = crossDiff (fun m => p (Fin.cons (ℓ 0) m)) (Fin.tail ℓ) -
      if ℓ 0 = 0 then 0 else crossDiff (fun m => p (Fin.cons (ℓ 0 - 1) m)) (Fin.tail ℓ) := rfl

/-- In one dimension the cross-difference is the MLMC correction `P_ℓ − P_{ℓ−1}` (`P_{−1} ≡ 0`). -/
lemma crossDiff_one (p : (Fin 1 → ℕ) → ℝ) (ℓ : Fin 1 → ℕ) :
    crossDiff p ℓ =
      p ℓ - if ℓ 0 = 0 then 0 else p (Fin.cons (ℓ 0 - 1) (Fin.tail ℓ)) := by
  simp only [crossDiff_succ, crossDiff_zero, Fin.cons_self_tail]

/-- **Giles 2015, §2.4 and Figure 2.1: the cross-difference in two dimensions.**  For
`ℓ₁, ℓ₂ ≥ 1`, `ΔP_{(ℓ₁,ℓ₂)} = P_{(ℓ₁,ℓ₂)} − P_{(ℓ₁−1,ℓ₂)} − P_{(ℓ₁,ℓ₂−1)} + P_{(ℓ₁−1,ℓ₂−1)}`: one
MIMC sample on level `(ℓ₁, ℓ₂)` needs the four evaluations at the corners of the unit square below
`(ℓ₁, ℓ₂)` shown in Figure 2.1 (here `(a, b)` is `Fin.cons a (Fin.cons b e)`). -/
theorem crossDiff_two (p : (Fin 2 → ℕ) → ℝ) (e : Fin 0 → ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    crossDiff p (Fin.cons a (Fin.cons b e)) =
      p (Fin.cons a (Fin.cons b e)) - p (Fin.cons (a - 1) (Fin.cons b e)) -
        p (Fin.cons a (Fin.cons (b - 1) e)) + p (Fin.cons (a - 1) (Fin.cons (b - 1) e)) := by
  rw [crossDiff_succ, Fin.cons_zero, Fin.tail_cons, if_neg ha, crossDiff_succ, crossDiff_succ,
    Fin.cons_zero, Fin.tail_cons, if_neg hb, if_neg hb, crossDiff_zero, crossDiff_zero,
    crossDiff_zero, crossDiff_zero]
  ring

/-- Giles' Figure 2.1: in two dimensions `ΔP_{(5,4)}` needs the four evaluations
`P_{(5,4)} − P_{(4,4)} − P_{(5,3)} + P_{(4,3)}` (here `(a, b)` is `Fin.cons a (Fin.cons b e)`). -/
example (p : (Fin 2 → ℕ) → ℝ) (e : Fin 0 → ℕ) :
    crossDiff p (Fin.cons 5 (Fin.cons 4 e)) =
      p (Fin.cons 5 (Fin.cons 4 e)) - p (Fin.cons 4 (Fin.cons 4 e)) -
        p (Fin.cons 5 (Fin.cons 3 e)) + p (Fin.cons 4 (Fin.cons 3 e)) := by
  simp only [crossDiff_succ, crossDiff_zero, Fin.cons_zero, Fin.tail_cons,
    show (5 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 0 by decide, if_false,
    show (5 : ℕ) - 1 = 4 from rfl, show (4 : ℕ) - 1 = 3 from rfl]
  ring

/-- **Telescoping over boxes** (Giles 2015, §2.4): the cross-differences summed over the box
`{ℓ : 0 ≤ ℓ_d ≤ k_d for all d}` give `P_k`. -/
theorem sum_crossDiff : ∀ {D : ℕ} (p : (Fin D → ℕ) → ℝ) (k : Fin D → ℕ),
    ∑ ℓ ∈ Fintype.piFinset (fun d => range (k d + 1)), crossDiff p ℓ = p k
  | 0, p, k => by
    have hk : k ∈ Fintype.piFinset (fun d : Fin 0 => range (k d + 1)) :=
      Fintype.mem_piFinset.2 fun d => d.elim0
    rw [Finset.sum_eq_single_of_mem k hk fun b _ hb => absurd (Subsingleton.elim b k) hb]
    rfl
  | D + 1, p, k => by
    rw [sum_piFinset_succ]
    -- the inner sums are cross-differences in the remaining `D` directions
    have htail : (Fin.tail fun d : Fin (D + 1) => range (k d + 1)) =
        fun d : Fin D => range (Fin.tail k d + 1) := rfl
    rw [htail]
    have hinner : ∀ j, ∑ m ∈ Fintype.piFinset (fun d : Fin D => range (Fin.tail k d + 1)),
        crossDiff p (Fin.cons j m) =
          p (Fin.cons j (Fin.tail k)) -
            if j = 0 then 0 else p (Fin.cons (j - 1) (Fin.tail k)) := by
      intro j
      have h1 : ∀ m : Fin D → ℕ, crossDiff p (Fin.cons j m) =
          crossDiff (fun m' => p (Fin.cons j m')) m -
            if j = 0 then 0 else crossDiff (fun m' => p (Fin.cons (j - 1) m')) m := by
        intro m
        rw [crossDiff_succ, Fin.cons_zero, Fin.tail_cons]
      rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_sub_distrib,
        sum_crossDiff (fun m => p (Fin.cons j m)) (Fin.tail k)]
      by_cases hj : j = 0
      · simp [hj]
      · simp only [hj, if_false]
        rw [sum_crossDiff (fun m => p (Fin.cons (j - 1) m)) (Fin.tail k)]
    rw [Finset.sum_congr rfl fun j _ => hinner j]
    -- one-dimensional telescoping in the first direction
    have htel : ∀ n : ℕ, ∑ j ∈ range (n + 1), (p (Fin.cons j (Fin.tail k)) -
        if j = 0 then 0 else p (Fin.cons (j - 1) (Fin.tail k))) = p (Fin.cons n (Fin.tail k)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, if_neg (Nat.add_one_ne_zero n), Nat.add_sub_cancel]
        ring
    rw [htel (k 0), Fin.cons_self_tail]

end MLMC
