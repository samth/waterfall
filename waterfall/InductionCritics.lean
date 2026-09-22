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
      let abstractions := evidence.indices.foldl (fun out expression =>
        if out.any (fun a : Generalization.Abstraction => a.expression == expression) then out
        else out.push {expression}) #[]
      let plan : Generalization.Plan := {
        parameters := variables, abstractions, hypotheses := #[major] }
      return {
        cost := 1, induction := kind, major := some major,
        inductionSummary := some {summary with
          generalized := variables.size, abstractedIndices := evidence.indices.size},
        label := s!"induction {(← major.getDecl).userName}" ++
          (if generalized then " generalized" else "") ++ " abstract indices",
        motive := if generalized then .localGeneralizationAndIndexAbstraction else .indexAbstraction,
        generalization := plan,
        run := Induction.withPlan goal (mkFVar major) plan } }

/-- Select eligible data parameters outside a protected expression. Excluding
propositions and type variables preserves the existing motive strategy. Lean's
reversion supplies the dependent hypotheses automatically. -/
private def parametersOutside (protectedExpr : Expr) (major? : Option FVarId := none) :
    MetaM (Array FVarId) := do
  let mut parameters := #[]
  for d in (← getLCtx) do
    unless d.isImplementationDetail || major? == some d.fvarId ||
        protectedExpr.containsFVar d.fvarId || (← isProp d.type) ||
        (← isType (mkFVar d.fvarId)) do
      parameters := parameters.push d.fvarId
  return parameters

/-- The existing structural-induction motives: eligible parameters first, then
the direct motive, then fixed-index repairs of both. Keeping these proposals
adjacent preserves the operation ordinals used by search and recorded replay. -/
public def inductionMotives (major : FVarId) (summary : InductionSummary) : Critic := {
  Evidence := Array FVarId
  observe := fun _ => return #[← parametersOutside (← major.getDecl).type (some major)]
  repair := fun goal parameters => do
    let kind : InductionKind := if ← isProp (← major.getDecl).type then .evidence else .data
    let variants := if parameters.isEmpty then #[#[]] else #[parameters, #[]]
    let mut moves ← variants.mapM fun variables => do
      let plan : Generalization.Plan := {parameters := variables}
      return {
        cost := 1, induction := kind, major := some major,
        inductionSummary := some {summary with generalized := variables.size},
        label := s!"induction {(← major.getDecl).userName}" ++
          (if variables.isEmpty then "" else " generalized"),
        motive := if variables.isEmpty then .direct else .localGeneralization,
        generalization := plan,
        run := Induction.withPlan goal (mkFVar major) plan }
    moves := moves ++ (← ((fixedIndices major parameters summary).propose goal).collect)
    return moves }

/-- Functional induction quantifies data outside the chosen recursive call.
Selection is a critic concern; execution and rendering share the resulting plan.
Keep the historic summary and motive tags, which scheduling already consumes. -/
public def functionalInduction (call : Expr) (summary : InductionSummary) : Critic := {
  Evidence := Generalization.Plan
  observe := fun _ => return #[{parameters := ← parametersOutside call}]
  repair := fun goal plan => pure #[{
    cost := 1, label := "function induction", subject := some call,
    induction := .functional, inductionSummary := some summary,
    generalization := plan,
    run := Induction.withPlan goal call plan true }] }

end waterfall.Critics
