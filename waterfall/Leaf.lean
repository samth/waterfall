module
public meta import Lean.Elab.Tactic.Grind.Main
public meta import Lean.Elab.Tactic.Grind.Param

meta section
open Lean Meta Elab Tactic
namespace waterfall.Leaf

/-!
Grind parameter compilation for speculative proof search. Lean's interactive
parameter elaborator computes several pattern suggestions and then uses only
the first. This adapter keeps that selection order, stopping after its first
success. It does not cache proof states or change inference budgets.
-/

/-- Match the first pattern selected by Lean's parameter suggestion search,
without computing or formatting the unused later suggestions. -/
private def firstParameterPattern (name : Name) (prios : Grind.SymbolPriorities) : MetaM Grind.EMatchTheorem := do
  if Grind.backward.grind.inferPattern.get (← getOptions) then
    return ← Grind.mkEMatchTheoremForDecl name (.default false) prios
  for kind in #[Grind.EMatchTheoremKind.default false, .bwd false, .fwd, .rightLeft, .leftRight] do
    try
      let minimal ← Grind.mkEMatchTheoremForDecl name kind prios (minIndexable := true)
      let regular ← Grind.mkEMatchTheoremForDecl name kind prios (minIndexable := false)
      return if minimal.patterns == regular.patterns then regular else minimal
    catch _ => pure ()
  for kind in #[Grind.EMatchTheoremKind.eqLhs false, .eqRhs false] do
    try return ← Grind.mkEMatchTheoremForDecl name kind prios
    catch _ => pure ()
  throwError "invalid `grind` theorem, failed to find an usable pattern using different modifiers"

private def firstGlobalParam? (params : Grind.Params)
    (p : TSyntax ``Lean.Parser.Tactic.grindParam) : TacticM (Option Grind.Params) := do
  let `(Lean.Parser.Tactic.grindParam| $id:ident) := p | return none
  if (← resolveLocalName id.getId).isSome then return none
  let name ← try realizeGlobalConstNoOverloadWithInfo id catch _ => return none
  let info ← getConstInfo name
  unless info matches .thmInfo _ | .axiomInfo _ | .ctorInfo _ do return none
  let thm ← firstParameterPattern name params.symPrios
  if params.extensions.containsWithSamePatterns thm.origin thm.patterns thm.cnstrs then return none
  Linter.checkDeprecated name
  return some { params with extra := params.extra.push thm }

/-- The ordinary protected grind boundary, with first-result compilation of
plain global theorem parameters. Definitions, local terms, explicit modifiers,
attributes and requested editor suggestions retain Lean's own elaborator.
This is the interface used by Waterfall's leaf move, not a replacement for the
interactive `grind` tactic. -/
public def grind (goal : MVarId) (config : Grind.Config)
    (rules : TSyntaxArray ``Lean.Parser.Tactic.grindParam) : TacticM Unit := do
  if Grind.grind.param.codeAction.get (← getOptions) || config.suggestions || config.locals then
    return ← Lean.Elab.Tactic.grind goal config false rules none
  if (← checkTerminalAsSorry goal) then return
  goal.withContext do
    let mut params ← mkGrindParams config false #[] goal
    for rule in rules do
      try
        if let some updated ← firstGlobalParam? params rule then params := updated
        else params ← elabGrindParams params #[rule] (only := false) (lax := config.lax)
      catch ex => if !config.lax then throw ex
    if params.anchorRefs?.isSome then params := { params with config.clean := false }
    if Grind.grind.unusedLemmaThreshold.get (← getOptions) > 0 then
      params := { params with config.markInstances := true }
    Grind.withProtectedMCtx config goal fun protectedGoal => do
      let result ← Grind.main protectedGoal params
      if result.hasFailed then throwError "`grind` failed\n{← result.toMessageData}"
      replaceMainGoal []

end waterfall.Leaf
