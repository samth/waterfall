/-!
Theorems for Tests/PremisesImport.lean, which imports this module: a public theorem
it may be offered and a private one it cannot cite.
-/

namespace PremisesBase

inductive M where
  | z
  | s (n : M)

def add : M → M → M
  | .z, m => m
  | .s n, m => .s (add n m)

theorem add_z (n : M) : add n .z = n := by
  induction n <;> simp_all [add]

theorem add_s (n m : M) : add n (.s m) = .s (add n m) := by
  induction n <;> simp_all [add]

theorem add_comm (n m : M) : add n m = add m n := by
  induction n <;> simp_all [add, add_z, add_s]

private theorem add_z_private (n : M) : add n .z = n := add_z n

end PremisesBase
