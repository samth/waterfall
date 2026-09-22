module
public import waterfall.Generalization
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

/-- Apply a motive plan and continue with structural or functional induction.
Functional induction keeps reverted parameters quantified, matching Lean's
`fun_induction`; ordinary induction reintroduces the dependency closure. -/
public def withPlan (goal : MVarId) (subject : Expr) (plan : Generalization.Plan)
    (functional : Bool := false) : TacticM Unit := do
  let prepared ← Generalization.prepare goal plan
  let subject := prepared.substitution.apply subject
  if functional then
    setGoals [prepared.goal]
    let term ← prepared.goal.withContext <| Term.exprToSyntax subject
    evalTactic (← `(tactic| fun_induction $term))
  else
    perform prepared.goal subject prepared.reverted.size

/-- The same exact plan supplies the ordinary proof commands. No parameter
selection is repeated by the suggestion frontend. -/
public def command (subject : Expr) (plan : Generalization.Plan)
    (functional : Bool := false) : TacticM (TSyntax `tactic) := do
  let commands ← Generalization.commands plan
  let term ← PrettyPrinter.delab subject
  let induction ← if functional then `(tactic| fun_induction $term)
    else `(tactic| induction $term:term)
  let induction ← if !functional && !plan.parameters.isEmpty then
    `(tactic| $induction <;> intros) else pure induction
  let commands := commands.push induction
  `(tactic| ($commands:tactic*))

end waterfall.Induction
