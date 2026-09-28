import waterfall

/-!
Relevant earlier theorems. With `premises := n`, the `simp` closer retries with up
to `n` earlier theorems of the current module that share vocabulary with the goal,
restricted at each node to those relevant to it. The option is off by default.
-/

namespace PremisesTest

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

theorem add_assoc (n m p : N) : add (add n m) p = add n (add m p) := by
  induction n <;> simp_all [add]

theorem unrelated (xs : List Nat) : xs ++ [] = xs := List.append_nil xs

set_option warn.sorry false in
theorem admitted_add (n : N) : add n n = add n .z := sorry

-- By default the search does not find this proof; with the earlier lemmas the
-- `simp` closer uses `add_comm` and `add_assoc`. `waterfall?` renders that proof.
example (n m p : N) : add (add n m) p = add (add n p) m := by
  fail_if_success waterfall
  waterfall (premises := 64)

example (n m p : N) : add (add n m) p = add (add n p) m := by
  waterfall? (report := true) (premises := 64)

-- Selection keeps the theorems about `add`, skips generated constructor lemmas
-- and theorems sharing no constant with the goal, and respects the limit.
open Lean Elab Tactic in
example (n m p : N) : add (add n m) p = add (add n p) m := by
  run_tac do
    let goals ← getUnsolvedGoals
    let chosen ← waterfall.Premises.select goals 64
    unless chosen.size == 4 && #[``add_z, ``add_s, ``add_comm, ``add_assoc].all chosen.contains do
      throwError "unexpected premises {chosen}"
    unless (← waterfall.Premises.select goals 2).size == 2 do throwError "the limit was ignored"
    unless (← waterfall.Premises.select goals 0).isEmpty do throwError "a zero limit must select nothing"
    let node ← waterfall.Premises.relevantAt goals.head! chosen 1
    unless node.size == 1 do throwError "per-node filtering ignored its limit"
  waterfall (premises := 64)

-- Goals sharing no vocabulary with earlier theorems search as before.
example (P : Prop) (h : P) : P := by waterfall (premises := 64)
example (P : Prop) (h : P) : P ∨ False := by
  fail_if_success waterfall (effort := 0) (premises := 64)
  exact Or.inl h

end PremisesTest
