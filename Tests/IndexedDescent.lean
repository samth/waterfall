import waterfall

open Lean Meta Elab Tactic
namespace Tests.IndexedDescent

elab "focus_once" : tactic => do
  let moves ← waterfall.movesFor (← getMainGoal) #[] 1 2 .basic
  let some move := moves.find? (·.label == "focus indexed hypothesis")
    | throwError "missing indexed focusing move"
  move.run

inductive Shape where
  | leaf
  | wrap : Shape → Shape

inductive Classified : Shape → Bool → Prop where
  | leaf (b : Bool) : Classified .leaf b
  | wrap : Classified s true → Classified (.wrap s) false

-- A classification index alone is not evidence of structural descent.
example (s : Shape) (h : Classified s true) : Classified s true := by
  run_tac do
    let moves ← waterfall.movesFor (← getMainGoal) #[] 1 2 .basic
    if moves.any (·.label == "focus indexed hypothesis") then
      throwError "classification was treated as a structural index"
  exact h

-- After one useful inversion, retain the child instead of splitting its color.
example (s : Shape) : Classified (.wrap s) false → Classified s true := by
  focus_once
  assumption

inductive Related : Shape → Shape → Prop where
  | leaf : Related .leaf .leaf
  | wrap : Related s .leaf → Related (.wrap s) (.wrap .leaf)

-- Even two recursive indices are different descent measures. Do not switch
-- to the second one when the first becomes a variable.
example (s : Shape) : Related (.wrap s) (.wrap .leaf) → Related s .leaf := by
  focus_once
  assumption

inductive Carries : Shape → Nat → Prop where
  | leaf : Carries .leaf 7
  | wrap : Carries s n → Carries (.wrap s) n

-- Constructor application can leave an assigned metavariable as the type of
-- the later introduced hypothesis. Eligibility must inspect its assignment.
example (n : Nat) : True ∧ (Carries (.wrap .leaf) n → n = 7) := by
  constructor
  · trivial
  · focus_once
    rfl

-- A generic closure does not inspect constructor-shaped endpoints.
inductive Closure : Shape → Shape → Prop where
  | refl : Closure s s
  | trans : Closure s t → Closure t u → Closure s u

example (s : Shape) (h : Closure (.wrap s) .leaf) : Closure (.wrap s) .leaf := by
  run_tac do
    let moves ← waterfall.movesFor (← getMainGoal) #[] 1 2 .basic
    if moves.any (·.label == "focus indexed hypothesis") then
      throwError "generic closure was treated as structural evidence"
  exact h

end Tests.IndexedDescent
