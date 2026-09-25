/-!
# Fixture: definitions
-/

namespace FX

/-- A definition used in theorem statements. -/
def sq (n : Nat) : Nat := n * n

/-- A second definition, depending on the first. -/
def sumSq : Nat → Nat
  | 0 => 0
  | n + 1 => sumSq n + sq (n + 1)

@[simp] theorem sq_zero : sq 0 = 0 := rfl

end FX
