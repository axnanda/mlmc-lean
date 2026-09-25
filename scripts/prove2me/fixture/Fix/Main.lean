import Fix.Lemmas

namespace FX

/-- The target: `sumSq` is monotone along successors, twice. -/
theorem sumSq_le_add_two (k : Nat) (hk : 0 < k) : sumSq k ≤ sumSq (k + 2) := by
  have h1 := sumSq_le_succ k hk
  have h2 := sumSq_le_succ (k + 1) (Nat.succ_pos k)
  exact Nat.le_trans h1 h2

/-- A second target using a variable-scoped lemma. -/
theorem length_nonneg_two (xs : List Nat) : 0 ≤ xs.length := length_nonneg xs

end FX
