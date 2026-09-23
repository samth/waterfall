import waterfall

namespace Tests.Focusing

open Lean Elab Tactic

elab "test_focus" : tactic => do
  let goal ← getMainGoal
  let moves ← waterfall.movesFor goal #[] 1 2 .basic
  let some move := moves.find? (·.label == "focus indexed hypothesis")
    | throwError "missing indexed focus move"
  move.run

elab "test_no_focus" : tactic => do
  let moves ← waterfall.movesFor (← getMainGoal) #[] 1 2 .basic
  if moves.any (·.label == "focus indexed hypothesis") then
    throwError "unexpected indexed focus move"

inductive Shape where
  | leaf
  | wrap : Shape → Shape

inductive Derives : Shape → Prop where
  | leaf : Derives .leaf
  | wrap : Derives s → Derives (.wrap s)

-- Multiple singleton inversions are retained in one search move.
example : Derives (.wrap (.wrap .leaf)) → Derives .leaf := by
  test_focus
  exact .leaf

inductive Branch : Shape → Prop where
  | left : Branch (.wrap .leaf)
  | right : Branch (.wrap .leaf)
  | next : Branch s → Branch (.wrap s)

-- Every constructor branch, including the recursive branch, remains a goal.
example : Branch (.wrap .leaf) → True := by
  test_focus
  run_tac do
    unless (← getGoals).length == 3 do
      throwError "indexed focus lost a constructor branch"
  all_goals trivial

-- A constructor in a parameter is not an indexed inversion opportunity.
inductive Parameter (s : Shape) : Nat → Prop where
  | zero : Parameter s 0
  | step : Parameter s n → Parameter s (n + 1)

example : Parameter (.wrap .leaf) n → True := by
  test_no_focus
  intro _
  trivial

-- A target without any exposed indexed hypothesis offers no focus move.
example : Shape → True := by
  test_no_focus
  intro _
  trivial

inductive Loop : Shape → Prop where
  | done : Loop (.wrap .leaf)
  | again : Loop (.wrap .leaf) → Loop (.wrap .leaf)

-- A rejected inversion restores its original goal and local hypothesis.
example (h : Loop (.wrap .leaf)) : Loop (.wrap .leaf) := by
  fail_if_success test_focus
  exact h

inductive Carries : Shape → Nat → Prop where
  | leaf : Carries .leaf 7
  | wrap : Carries s n → Carries (.wrap s) n

-- The checked suggestion must close the shared `n` witness after inversion.
example (n : Nat) (h : Carries (.wrap .leaf) n) : n = 7 := by
  waterfall?

end Tests.Focusing
