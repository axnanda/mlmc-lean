import Fix.Defs

/-!
# Fixture: a recursive target and a proof relying on a `@[simp]` rfl-lemma implicitly
-/

namespace FX

/-- A recursive theorem (structural recursion calls itself by name). -/
theorem sumSq_mono : ∀ n : Nat, sumSq n ≤ sumSq (n + 1)
  | 0 => Nat.zero_le _
  | n + 1 => by
    have _ih := sumSq_mono n
    show sumSq (n + 1) ≤ sumSq (n + 1) + sq (n + 2)
    exact Nat.le_add_right _ _

/-- Uses the `@[simp]` lemma `sq_zero` only implicitly, through `simp`. -/
theorem sq_zero_add (n : Nat) : sq 0 + n = n := by simp

end FX
