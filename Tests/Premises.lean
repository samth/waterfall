import waterfall

/-!
Relevant earlier theorems. With `premises := n`, the `simp` closer retries with up
to `n` earlier theorems that share vocabulary with the goal, restricted at each node
to those relevant to it. The option is off by default. Tests/PremisesImport.lean
covers theorems from imported modules.
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

-- Private theorems are candidates like any other earlier theorem.
def dbl : N → N
  | .z => .z
  | .s n => .s (.s (dbl n))

private theorem dbl_add (n : N) : dbl n = add n n := by
  induction n <;> simp_all [dbl, add, add_s]

example (n m : N) : add (dbl n) m = add (add n n) m := by
  fail_if_success waterfall
  waterfall (premises := 4)

open Lean Elab Tactic in
example (n : N) : dbl n = add n n := by
  run_tac do
    let chosen ← waterfall.Premises.select (← getUnsolvedGoals) 64
    unless chosen.contains ``dbl_add do
      throwError "the private theorem was not offered: {chosen}"
    let env ← getEnv
    if chosen.any (isAuxRecursor env) then
      throwError "an auxiliary recursor was offered: {chosen}"
    if chosen.any (·.toString.contains "match_") then
      throwError "a generated matcher lemma was offered: {chosen}"
  exact dbl_add n

-- Goals sharing no vocabulary with earlier theorems search as before.
example (P : Prop) (h : P) : P := by waterfall (premises := 64)
example (P : Prop) (h : P) : P ∨ False := by
  fail_if_success waterfall (effort := 0) (premises := 64)
  exact Or.inl h


-- A caller may retain a larger theory than sixteen names. These equivalent
-- equations model a crowded lemma pool; commutativity and associativity must
-- remain usable at the end of it.
private theorem padding1 (n : N) : add n .z = n := add_z n
private theorem padding2 (n : N) : add n .z = n := add_z n
private theorem padding3 (n : N) : add n .z = n := add_z n
private theorem padding4 (n : N) : add n .z = n := add_z n
private theorem padding5 (n : N) : add n .z = n := add_z n
private theorem padding6 (n : N) : add n .z = n := add_z n
private theorem padding7 (n : N) : add n .z = n := add_z n
private theorem padding8 (n : N) : add n .z = n := add_z n
private theorem padding9 (n : N) : add n .z = n := add_z n
private theorem padding10 (n : N) : add n .z = n := add_z n
private theorem padding11 (n : N) : add n .z = n := add_z n
private theorem padding12 (n : N) : add n .z = n := add_z n
private theorem padding13 (n : N) : add n .z = n := add_z n
private theorem padding14 (n : N) : add n .z = n := add_z n
private theorem padding15 (n : N) : add n .z = n := add_z n
private theorem padding16 (n : N) : add n .z = n := add_z n

open Lean Elab Tactic in
example (n m p : N) : add (add n m) p = add (add n p) m := by
  run_tac do
    let names := #[``padding1, ``padding2, ``padding3, ``padding4, ``padding5, ``padding6, ``padding7, ``padding8, ``padding9, ``padding10, ``padding11, ``padding12, ``padding13, ``padding14, ``padding15, ``padding16,
      ``add_comm, ``add_assoc]
    discard <| waterfall.run {} #[] (waterfall.Mode.search.hooks #[] names)

-- Generated recursion theorems for propositions must not occupy premise slots.
inductive Reach : N → Prop where
  | zero : Reach .z
  | step {n} : Reach n → Reach (.s n)

open Lean Elab Tactic in
example : Reach .z := by
  run_tac do
    let chosen ← waterfall.Premises.select (← getUnsolvedGoals) 64
    if chosen.contains ``Reach.brecOn then
      throwError "the generated Prop recursor was offered: {chosen}"
  exact Reach.zero

end PremisesTest
