/-! Cross-root premise fixture: a package may expose several module roots. -/
namespace CrossRootPremises
inductive N where
  | z
  | s (n : N)
def add : N → N → N
  | .z, m => m
  | .s n, m => .s (add n m)
theorem add_z (n : N) : add n .z = n := by
  induction n <;> simp_all [add]
theorem add_s (n m : N) : add n (.s m) = .s (add n m) := by
  induction n <;> simp_all [add]
theorem add_comm (n m : N) : add n m = add m n := by
  induction n <;> simp_all [add, add_z, add_s]
end CrossRootPremises
