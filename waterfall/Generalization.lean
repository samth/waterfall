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

/-- Plan equation-free abstraction of selected results. Preserve hypotheses
about those results, and clear premises that still depend on their inputs.
Reject conclusions that use an input independently of the selected results.

Assigned metavariables must be instantiated before dependency analysis: an
assigned induction motive can discard an argument or hide a useful invariant.
This selects a plan only; the caller chooses results, execution and continuation. -/
public def abstractIndependent (goal : MVarId) (results : Array Expr) : MetaM (Option Plan) :=
    goal.withContext do
  if results.isEmpty then return none
  let results ← results.mapM instantiateMVars
  let lctx ← getLCtx
  let mut inputs := #[]
  for d in lctx do
    unless d.isImplementationDetail || d.binderInfo.isInstImplicit ||
        (← isProp d.type) || (← isType (mkFVar d.fvarId)) do
      inputs := inputs.push d.fvarId
  let dependsOnInput := fun expression =>
    -- The replacement is only an occurrence marker; no synthetic proposition
    -- is submitted to the kernel or used to construct the generalized goal.
    let residual := expression.replace fun term =>
      if results.contains term then some (mkConst ``True) else none
    inputs.any fun id => residual.containsFVar id && results.any (·.containsFVar id)
  if dependsOnInput (← instantiateMVars (← goal.getType)) then return none
  let mut hypotheses := #[]
  let mut clearBefore := #[]
  for d in lctx do
    if d.isImplementationDetail || !(← isProp d.type) then continue
    let hypothesis ← instantiateMVars d.type
    if dependsOnInput hypothesis then
      clearBefore := #[d.fvarId] ++ clearBefore
    else if results.any (fun result => (hypothesis.find? (· == result)).isSome) then
      hypotheses := hypotheses.push d.fvarId
  return some {
    abstractions := results.map (fun expression => {expression, retainEquation := false})
    hypotheses, clearBefore, clearAfter := inputs.reverse }

/-- Execute a selected plan without choosing a strategy or an induction scheme.
The caller owns rollback, as for any other proof operation. -/
public def prepare (goal : MVarId) (plan : Plan) : MetaM Prepared := goal.withContext do
  -- Allocate display names in the input context, just like commands. Clearing
  -- or reverting a same-named local must not change the abstraction recipe.
  let lctx ← getLCtx
  let names := plan.abstractions.mapIdx fun i _ =>
    lctx.getUnusedName (Name.mkSimple s!"wf_index{i}")
  let mut initial := goal
  for id in plan.clearBefore do initial ← initial.tryClear id
  let (reverted, goal) ← initial.revert plan.parameters
  let prepared ← if plan.abstractions.isEmpty then
    pure ({goal, reverted, substitution := {}} : Prepared)
  else goal.withContext do
    let args ← plan.abstractions.mapIdxM fun i abstraction => do
      let hName? ← if abstraction.retainEquation then
        pure (some (← mkFreshUserName `index_eq)) else pure none
      let xName := names[i]!
      pure ({expr := abstraction.expression, hName?, xName? := some xName} : GeneralizeArg)
    let (substitution, _, goal) ← goal.generalizeHyp args plan.hypotheses
    return {goal, substitution, reverted}
  let mut result := prepared.goal
  for id in plan.clearAfter do
    let mapped := prepared.substitution.apply (mkFVar id)
    if mapped.isFVar then result ← result.tryClear mapped.fvarId!
  return {prepared with goal := result}

/-- Render precisely the selected preparation in its input context. The consumer
adds the continuation and independently checks the complete printed proof. -/
public def commands (plan : Plan) : TacticM (Array (TSyntax `tactic)) := do
  let mut out := #[]
  for id in plan.clearBefore do
    let name := mkIdent (← id.getDecl).userName
    out := out.push (← `(tactic| try clear $name:ident))
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
  for id in plan.clearAfter do
    let name := mkIdent (← id.getDecl).userName
    out := out.push (← `(tactic| try clear $name:ident))
  return out

end waterfall.Generalization
