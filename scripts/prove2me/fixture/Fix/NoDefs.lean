/-!
# Fixture: a module with no project imports and no definitions
-/

namespace FX

/-- A target whose stub imports no project module. -/
theorem add_comm_swap (a b : Nat) : a + b = b + a := Nat.add_comm a b

end FX
