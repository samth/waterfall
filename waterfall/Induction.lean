module
public import waterfall.Protocol
public meta import Lean.Elab.Tactic.Induction

meta section

open Lean Meta Elab Tactic
namespace waterfall.Induction

/-- Execute ordinary Lean induction on an already-prepared major premise.
The elaborator handles registered eliminators and index preparation that the
lower-level `MVarId.induction` API alone does not supply. After induction,
reintroduce the full dependency closure returned by the caller's `revert`.
Selecting which variables or expressions to generalize belongs to the caller. -/
public def perform (goal : MVarId) (major : Expr) (reintroduce : Nat) : TacticM Unit := do
  setGoals [goal]
  let majorSyntax ← goal.withContext <| Term.exprToSyntax major
  evalTactic (← `(tactic| induction $majorSyntax:term))
  let children ← (← getUnsolvedGoals).mapM fun child => do
    return (← child.introNP reintroduce).2
  setGoals children

end waterfall.Induction
