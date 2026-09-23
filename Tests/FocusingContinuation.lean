import waterfall

open Lean Meta Elab Tactic
namespace FocusingContinuation
inductive Shape where
  | leaf
  | wrap : Shape → Shape
inductive Chain : Shape → Prop where
  | stop : Chain (.wrap .leaf)
  | spin : Chain (.wrap .leaf) → Chain (.wrap .leaf)
  | step : Chain s → Chain (.wrap s)

-- The outer singleton inversion descends; the next one is cyclic. Its rejected
-- case split must restore the goal retained by the successful outer inversion.
example (h : Chain (.wrap (.wrap .leaf))) : Chain (.wrap .leaf) := by
  run_tac do
    let moves ← waterfall.movesFor (← getMainGoal) #[] 1 2 .basic
    let some move := moves.find? (·.label == "focus indexed hypothesis")
      | throwError "missing focusing move"
    move.run
    let goals ← getUnsolvedGoals
    unless goals.length == 1 do throwError "rejected inner inversion lost its obligation"
  assumption
end FocusingContinuation
