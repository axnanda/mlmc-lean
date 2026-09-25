import Fix.Defs

/-!
# Fixture: lemmas with scope features
-/

open Nat

namespace FX

variable {α : Type} [Inhabited α] (xs : List α)

/-- A short helper (inline). -/
theorem sq_pos {n : Nat} (h : 0 < n) : 0 < sq n := Nat.mul_pos h h

omit [Inhabited α] in
/-- Uses a section variable (xs) without the instance. -/
theorem length_nonneg : 0 ≤ xs.length := Nat.zero_le _

/-- Uses the instance variable. -/
theorem default_mem_or : xs = [] ∨ xs ≠ [] := by
  have _h : Inhabited α := inferInstance
  by_cases h : xs = []
  · exact Or.inl h
  · exact Or.inr h

section Inner

variable (k : Nat)

set_option linter.unusedVariables false in
/-- A longer lemma (node by size): `sumSq` is monotone. -/
theorem sumSq_le_succ (hk : 0 < k) : sumSq k ≤ sumSq (k + 1) := by
  show sumSq k ≤ sumSq k + sq (k + 1)
  have h1 : 0 ≤ sq (k + 1) := Nat.zero_le _
  have h2 : sumSq k ≤ sumSq k + sq (k + 1) := Nat.le_add_right _ _
  have h3 : sumSq k + 0 ≤ sumSq k + sq (k + 1) := by
    rw [Nat.add_zero]
    exact h2
  have h4 : sumSq k = sumSq k + 0 := (Nat.add_zero _).symm
  have h5 : sumSq k ≤ sumSq k := Nat.le_refl _
  have h6 : sq (k + 1) = (k + 1) * (k + 1) := rfl
  have h7 : 0 < k + 1 := Nat.succ_pos k
  have h8 : 0 < sq (k + 1) := sq_pos h7
  have h9 : sumSq k < sumSq k + sq (k + 1) := Nat.lt_add_of_pos_right h8
  exact Nat.le_of_lt h9

end Inner

end FX
