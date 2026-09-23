import waterfall

open Lean Elab Tactic

/-! Exercise the same parameter syntax that `grind` receives at Waterfall's
leaf boundary. These examples check proofs and failures through the public
adapter, including the branches delegated to Lean's elaborator. -/

elab "leaf_grind" "[" ps:Lean.Parser.Tactic.grindParam,* "]" : tactic => do
  waterfall.Leaf.grind (← getMainGoal) {} ps.getElems

elab "leaf_grind_lax" "[" ps:Lean.Parser.Tactic.grindParam,* "]" : tactic => do
  waterfall.Leaf.grind (← getMainGoal) { lax := true } ps.getElems

elab "leaf_grind_suggestions" "[" ps:Lean.Parser.Tactic.grindParam,* "]" : tactic => do
  waterfall.Leaf.grind (← getMainGoal) { suggestions := true } ps.getElems

set_option maxHeartbeats 300000

namespace LeafTests

inductive Reach : Nat → Prop where
  | zero : Reach 0
  | next : Reach n → Reach (n + 1)

theorem reach_two (n : Nat) : Reach n → Reach (n + 2) := by
  intro h
  exact Reach.next (Reach.next h)

-- A plain global theorem takes the optimized path. Both solvers must accept
-- the same ordinary rule and close the resulting quantified goal.
example (n : Nat) (h : Reach n) : Reach (n + 2) := by grind [reach_two]
example (n : Nat) (h : Reach n) : Reach (n + 2) := by leaf_grind [reach_two]

-- Parenthesized local proof terms, definitions, and explicit modifiers are
-- elaborated by Lean's maintained parameter elaborator.
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 3) : Q 3 := by
  leaf_grind [(fun n => h n)]

def decode : Nat → Nat
  | 0 => 9
  | n + 1 => n

example : decode 0 = 9 := by grind [decode]
example : decode 0 = 9 := by leaf_grind [decode]

example (n : Nat) (h : Reach n) : Reach (n + 2) := by grind [→ reach_two]
example (n : Nat) (h : Reach n) : Reach (n + 2) := by leaf_grind [→ reach_two]

@[grind] theorem reach_two_registered (n : Nat) : Reach n → Reach (n + 2) := reach_two n
example (n : Nat) (h : Reach n) : Reach (n + 2) := by leaf_grind [reach_two_registered]

-- Lean's old pattern inference and requested editor actions use the original
-- elaborator. The latter has no separate syntax in the Waterfall frontend.
set_option backward.grind.inferPattern true in
example (n : Nat) (h : Reach n) : Reach (n + 2) := by leaf_grind [reach_two]

set_option grind.param.codeAction true in
example (n : Nat) (h : Reach n) : Reach (n + 2) := by leaf_grind [reach_two]

example (n : Nat) (h : Reach n) : Reach (n + 2) := by
  leaf_grind_suggestions [reach_two]

-- Invalid input must fail strictly, while lax mode may ignore that parameter.
example : True := by
  fail_if_success leaf_grind [noSuchLeafRule]
  leaf_grind_lax [noSuchLeafRule]

end LeafTests
