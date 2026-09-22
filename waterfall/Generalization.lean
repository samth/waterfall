module
public import waterfall.Protocol
public meta import Lean.Meta.Tactic.Generalize

meta section

open Lean Meta Elab Tactic Parser.Tactic
namespace waterfall.Generalization

/-- A prepared goal and the information needed to continue its elimination.
`substitution` translates hypotheses changed by abstraction. `reverted` includes
all dependent declarations, not just the explicitly selected parameters. -/
public structure Prepared where
  goal : MVarId
  substitution : FVarSubst
  reverted : Array FVarId

/-- Execute a selected plan without choosing a strategy or an induction scheme.
The caller owns rollback, as for any other proof operation. -/
public def prepare (goal : MVarId) (plan : Plan) : MetaM Prepared := goal.withContext do
  let (reverted, goal) ← goal.revert plan.parameters
  if plan.abstractions.isEmpty then return {goal, reverted, substitution := {}}
  goal.withContext do
    let args ← plan.abstractions.mapM fun abstraction => do
      let hName? ← if abstraction.retainEquation then
        pure (some (← mkFreshUserName `index_eq)) else pure none
      pure ({expr := abstraction.expression, hName?} : GeneralizeArg)
    let (substitution, _, goal) ← goal.generalizeHyp args plan.hypotheses
    return {goal, substitution, reverted}

/-- Render precisely the selected preparation in its input context. The consumer
adds the continuation and independently checks the complete printed proof. -/
public def commands (plan : Plan) : TacticM (Array (TSyntax `tactic)) := do
  let mut out := #[]
  unless plan.parameters.isEmpty do
    let names ← plan.parameters.mapM fun id => return mkIdent (← id.getDecl).userName
    out := out.push (← `(tactic| revert $names*))
  unless plan.abstractions.isEmpty do
    let mut args : Array (TSyntax ``generalizeArg) := #[]
    for i in [:plan.abstractions.size] do
      let abstraction := plan.abstractions[i]!
      let expression ← PrettyPrinter.delab abstraction.expression
      let variableName := mkIdent ((← getLCtx).getUnusedName (Name.mkSimple s!"wf_index{i}"))
      if abstraction.retainEquation then
        let equation := mkIdent ((← getLCtx).getUnusedName (Name.mkSimple s!"wf_index_eq{i}"))
        args := args.push (← `(generalizeArg| $equation:ident : $expression = $variableName:ident))
      else
        args := args.push (← `(generalizeArg| $expression = $variableName:ident))
    let hypotheses ← plan.hypotheses.mapM fun id => return mkIdent (← id.getDecl).userName
    out := out.push (← if hypotheses.isEmpty then `(tactic| generalize $args,*)
      else `(tactic| generalize $args,* at $hypotheses* ⊢))
  return out

end waterfall.Generalization
