module
public import waterfall.Repair
public import waterfall.Induction

meta section

open Lean Meta Elab Tactic
open Lean.Parser.Tactic
namespace waterfall.Critics

/-- The major type's nonvariable indices, in their original order.
Execution deduplicates expressions; metadata retains the original index count. -/
private structure FixedIndices where
  indices : Array Expr

private def indexArguments (indices : Array Expr) : CoreM (Array GeneralizeArg) := do
  let mut args := #[]
  for index in indices do
    unless args.any (·.expr == index) do
      args := args.push {expr := index, hName? := some (← mkFreshUserName `index_eq)}
  return args

private def indexCommand (major : FVarId) (indices : Array Expr)
    (generalize : Array FVarId) : TacticM (TSyntax `tactic) := do
  let target := mkIdent (← major.getDecl).userName
  let mut commands : Array (TSyntax `tactic) := #[]
  unless generalize.isEmpty do
    let names ← generalize.mapM fun id => return mkIdent (← id.getDecl).userName
    commands := commands.push (← `(tactic| revert $names*))
  let mut seen := #[]
  let mut args : Array (TSyntax ``generalizeArg) := #[]
  for index in indices do
    unless seen.contains index do
      let n := seen.size
      seen := seen.push index
      let expression ← PrettyPrinter.delab index
      let variableName := mkIdent ((← getLCtx).getUnusedName (Name.mkSimple s!"wf_index{n}"))
      let equationName := mkIdent ((← getLCtx).getUnusedName (Name.mkSimple s!"wf_index_eq{n}"))
      args := args.push (← `(generalizeArg| $equationName:ident : $expression = $variableName:ident))
  commands := commands.push (← `(tactic| generalize $args,* at $target:ident))
  let induction ← `(tactic| induction $target:ident)
  commands := commands.push (← if generalize.isEmpty then pure induction
    else `(tactic| $induction <;> intros))
  `(tactic| ($commands:tactic*))

/-- Nonvariable indices can obstruct ordinary induction. Abstract them while
retaining their equations, then induct. Offer the same repair both with the
current motive and with the caller's proposed parameter generalization.
Preparation and induction form one move: their original cost and continuation
are preserved, including all dependent hypotheses reintroduced into each case. -/
public def fixedIndices (major : FVarId) (generalize : Array FVarId)
    (summary : InductionSummary) : Critic := {
  Evidence := FixedIndices
  observe := fun _ => do
    let type ← whnf (← major.getDecl).type
    let .const name _ := type.getAppFn | return #[]
    let some (.inductInfo info) := (← getEnv).find? name | return #[]
    let indices := type.getAppArgs[info.numParams:].toArray.filter (!·.isFVar)
    return if indices.isEmpty then #[] else #[⟨indices⟩]
  repair := fun goal evidence => do
    let kind : InductionKind := if ← isProp (← major.getDecl).type then .evidence else .data
    let variants := if generalize.isEmpty then #[#[]] else #[#[], generalize]
    variants.mapM fun variables => do
      let generalized := !variables.isEmpty
      -- A failed presentation recipe must not suppress a proof operation.
      -- Suggestions can still validate and print the resulting proof term.
      let command? ← try pure (some (← indexCommand major evidence.indices variables))
        catch _ => pure none
      return {
        cost := 1, induction := kind, major := some major,
        inductionSummary := some {summary with
          generalized := variables.size, abstractedIndices := evidence.indices.size},
        label := s!"induction {(← major.getDecl).userName}" ++
          (if generalized then " generalized" else "") ++ " abstract indices",
        motive := if generalized then .localGeneralizationAndIndexAbstraction else .indexAbstraction,
        command?,
        run := goal.withContext do
          let (reverted, goal) ← goal.revert variables
          let (substitution, _, prepared) ← goal.withContext <|
            goal.generalizeHyp (← indexArguments evidence.indices) #[major]
          Induction.perform prepared (substitution.apply (mkFVar major)) reverted.size } }

end waterfall.Critics
