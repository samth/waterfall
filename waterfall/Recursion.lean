module
public import waterfall.InductionCritics

meta section
open Lean Meta Elab Tactic
namespace waterfall.Recursion

/-- Only definitions originating in the current module are unfolded implicitly.
Imported theories can supply their definitions and laws through the rule list.
Inspect async metadata first; never wait for the current theorem's proof body.
-/
public def goalDefinitions (g : MVarId) : MetaM (Array Name) := g.withContext do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut exprs := #[(← instantiateMVars (← g.getType))]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push d.type
  for e in exprs do
    for n in e.getUsedConstants do
      if !names.contains n && !env.isImportedConst n then
        if let some c := env.findAsync? n then
          -- Reducible aliases are unfolded by Lean already; grind rejects
          -- them as explicit theorem arguments.
          if c.kind == .defn && (← getReducibilityStatus n) != .reducible then
            names := names.push n
  return names

public def recursiveResults (g : MVarId) (rules : Array (TSyntax `term))
    (e : Expr) (includeImported := false) : TacticM (Array Expr) := g.withContext do
  let mut definitions ← goalDefinitions g
  for r in rules do
    if !r.raw.isIdent then continue
    try
      let n ← resolveGlobalConstNoOverload r
      if !definitions.contains n then definitions := definitions.push n
    catch _ => pure ()
  let calls ← IO.mkRef (#[] : Array Expr)
  e.forEach fun call => do
    unless call.isApp && call.hasFVar && !call.hasLooseBVars && !call.hasMVar do return
    let .const n _ := call.getAppFn | return
    unless includeImported || definitions.contains n do return
    let type ← whnf (← inferType call)
    let .const typeName _ := type.getAppFn | return
    let some (.inductInfo info) := (← getEnv).find? typeName | return
    unless info.isRec && !(← isProp call) do return
    unless ← isRecursiveDefinition n do return
    unless (← calls.get).contains call do calls.modify (·.push call)
  return ← calls.get

public def occurs (term expression : Expr) : Bool :=
  (expression.find? (· == term)).isSome

-- Forward instantiation draws arguments from terms already present in the goal
-- and hypotheses. Bound-variable fragments cannot be reused outside their binder.
private structure TermCollection where
  seen : Std.HashSet Expr := {}
  terms : Array Expr := #[]

private partial def collectTerm (e : Expr) (collection : TermCollection) : TermCollection :=
  if collection.seen.contains e then collection else
  let collection := {
    seen := collection.seen.insert e
    terms := if e.hasLooseBVars then collection.terms else collection.terms.push e }
  match e with
  | .forallE _ domain body _ | .lam _ domain body _ =>
      collectTerm body (collectTerm domain collection)
  | .letE _ type value body _ =>
      collectTerm body (collectTerm value (collectTerm type collection))
  | .app fn arg => collectTerm arg (collectTerm fn collection)
  | .mdata _ body | .proj _ _ body => collectTerm body collection
  | _ => collection

private partial def collectApplication (e : Expr)
    (collection : TermCollection) : TermCollection :=
  if collection.seen.contains e then collection else
  let collection := {
    seen := collection.seen.insert e
    terms := if e.isApp && !e.hasLooseBVars then collection.terms.push e else collection.terms }
  match e with
  | .forallE _ domain body _ | .lam _ domain body _ =>
      collectApplication body (collectApplication domain collection)
  | .letE _ type value body _ =>
      collectApplication body (collectApplication value (collectApplication type collection))
  | .app fn arg => collectApplication arg (collectApplication fn collection)
  | .mdata _ body | .proj _ _ body => collectApplication body collection
  | _ => collection

public def contextTerms (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut collection := collectTerm (← instantiateMVars (← g.getType)) {}
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      collection := collectTerm (← instantiateMVars d.type) collection
      collection := { collection with terms := collection.terms.push (mkFVar d.fvarId) }
  return collection.terms

public def contextApplications (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let mut collection := collectApplication (← instantiateMVars (← g.getType)) {}
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      collection := collectApplication (← instantiateMVars d.type) collection
  return collection.terms

/-- Complete calls in the current theory, with stable scheme summaries. -/
public def calls (g : MVarId) (rules : Array (TSyntax `term)) :
    TacticM (Array (Expr × InductionSummary)) := do
  let mut out := #[]
  let ts ← contextTerms g
  -- Functional induction/cases follow the recursion of calls occurring in the
  -- current problem. An explicit definition rule may expose imported recursion.
  let mut definitions ← goalDefinitions g
  for r in rules do
    if !r.raw.isIdent then continue
    let some n ← (try pure (some (← resolveGlobalConstNoOverload r)) catch _ => pure none)
      | continue
    if let some info := (← getEnv).findAsync? n then
      if info.kind == .defn && !definitions.contains n then
        definitions := definitions.push n
  let calls ← ts.filterM fun call => do
    let .const n _ := call.getAppFn | return false
    if !call.isApp || !definitions.contains n then return false
    return !(← whnf (← inferType call)).isForall
  -- Prefer computation calls before predicates, but retain both in the search.
  -- A call whose result is still a function is not a complete elimination target.
  let dataCalls ← calls.filterM fun c => return !(← isProp c)
  let propCalls ← calls.filterM fun c => isProp c
  for call in dataCalls ++ propCalls do
    let definition := match call.getAppFn with | .const n _ => some n | _ => none
    let related := calls.filter fun other => other.getAppFn == call.getAppFn
    let args := call.getAppArgs
    let mut changingArguments := #[]
    for i in [:args.size] do
      if related.any (fun other =>
          let otherArgs := other.getAppArgs
          i < otherArgs.size && otherArgs[i]! != args[i]!) then
        changingArguments := changingArguments.push i
    let summary : InductionSummary := {
      definition, coveredCalls := related.size, changingArguments }
    out := out.push (call, summary)
  return out

end waterfall.Recursion
