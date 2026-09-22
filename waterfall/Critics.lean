module
public import waterfall.Core
public import waterfall.Repair
public meta import Lean.Meta.Tactic.Rewrite

meta section

/-!
Small ACL2-style proof critics implemented through the public engine hooks.
They add proposals and ordering information, but own no traversal, rollback,
resource accounting or proof validation.
-/

open Lean Meta Elab Tactic
namespace waterfall.Critics

/-- Evidence from matching a local rule to the target. No metavariables from
that speculative application survive in this description. -/
private structure MissingPremise where
  rule : FVarId
  proposition : Expr

private def missingPremises (g : MVarId) : TacticM (Array MissingPremise) := g.withContext do
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail || !(← isProp d.type) then continue
    let blocker? ← withoutModifyingState do
      try
        let premises ← g.apply (mkFVar d.fvarId)
        let mut known := 0
        let mut unknown : Array Expr := #[]
        for premise in premises do
          let type ← instantiateMVars (← premise.getType)
          if type.hasMVar then return none
          if (← findLocalDeclWithType? type).isSome then known := known + 1
          else unknown := unknown.push type
        if known == 0 || unknown.size != 1 then return none
        let type := unknown[0]!
        let blocker := if type.isAppOfArity ``Not 1 then type.getAppArgs[0]! else type
        if blocker.hasMVar || !(← isProp blocker) then return none
        if (← findLocalDeclWithType? blocker).isSome ||
            (← findLocalDeclWithType? (mkNot blocker)).isSome then return none
        return some blocker
      catch _ => return none
    let some blocker := blocker? | continue
    unless out.any (fun evidence : MissingPremise => evidence.proposition == blocker) do
      out := out.push ⟨d.fvarId, blocker⟩
  return out

/-- A local rule almost applies. Splitting its one unknown premise exposes the
positive application and a negative branch which must independently be proved.
This critic proposes the split; it never commits to it or starts another search.

The heuristic requires at least one premise already present in the local
context and exactly one unknown premise after applying the rule to the target.
It misses useful rules with no known premises or several missing premises,
and premises that are provable but not already available as hypotheses.
Generalizing it would require proposing several possible blockers (or sequences
of splits), and optionally checking whether premises can be discharged cheaply.
That could generate irrelevant splits, exponentially many case combinations,
and extra premise-solving work before any useful repair is tried. -/
public def blockedPremise : Critic := {
  Evidence := MissingPremise
  observe := missingPremises
  repair := fun g evidence => do
    let proposition ← PrettyPrinter.delab evidence.proposition
    let name := mkIdent ((← getLCtx).getUnusedName `wf_blocker)
    let command ← `(tactic| by_cases $name:ident : $proposition)
    return #[{
      cost := 1, label := "split blocked rule premise", role := `critic,
      preparation := .targetSplit,
      major := some evidence.rule, subject := some evidence.proposition,
      command? := some command,
      run := g.withContext do
        let (positive, negative) ← g.byCases evidence.proposition `wf_blocker
        setGoals [positive.mvarId, negative.mvarId] }] }

/-- Convenience enumeration for consumers that need a finite batch. -/
public def blockedPremises (g : MVarId) : TacticM (Array Move) :=
  (blockedPremise.propose g).collect

/-- A quantified equality matches a subexpression of the goal, but cannot be
used by backward application to the entire conclusion. Only the stable rule
and direction survive probing; execution reconstructs all instantiations. -/
private structure RewriteMatch where
  rule : FVarId
  reverse : Bool

private def rewriteMatches (g : MVarId) : TacticM (Array RewriteMatch) := g.withContext do
  let target ← instantiateMVars (← g.getType)
  -- Introductions belong to the ordinary preparation moves. Do not match
  -- expressions under unintroduced binders or guess their eventual arguments.
  if target.isForall then return #[]
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail || !d.type.isForall then continue
    let equality ← forallTelescopeReducing d.type fun _ body => pure body.eq?.isSome
    unless equality do continue
    for reverse in [false, true] do
      let useful ← withoutModifyingState do
        try
          let result ← g.rewrite target (mkFVar d.fvarId) (symm := reverse)
          if result.eNew.hasMVar || result.eNew == target then return false
          -- No ordering by function names or chosen theory. Prefer a contracting
          -- rewrite, or one which exposes an exact/reflexive conclusion.
          if result.eNew.sizeWithoutSharing < target.sizeWithoutSharing then return true
          if (← findLocalDeclWithType? result.eNew).isSome then return true
          if let some (_, lhs, rhs) := result.eNew.eq? then return ← isDefEq lhs rhs
          return false
        catch _ => return false
      if useful then out := out.push ⟨d.fvarId, reverse⟩
  return out

/-- Goal-directed specialization of a quantified equality. Conditional rules
leave *all* remaining premises in the agenda; rewriting is never evidence that
those premises hold. The source hypothesis is retained, including dependencies.

The heuristic accepts only rewrites that strictly reduce expression-tree size,
match an existing hypothesis, or expose a reflexive equality. It misses useful
size-preserving rearrangements and expansions that enable a later rewrite or
induction step. Generalizing it would require admitting those intermediate
forms, with a search budget and cycle control rather than contraction as the
filter. This can introduce inverse-rewrite loops, larger intermediate terms,
and many redundant alternatives to proofs already found by simplification. -/
public def quantifiedRewrite : Critic := {
  Evidence := RewriteMatch
  observe := rewriteMatches
  repair := fun g evidence => do
    let h := mkIdent (← evidence.rule.getDecl).userName
    let command ← if evidence.reverse then `(tactic| rewrite [← $h:ident])
      else `(tactic| rewrite [$h:ident])
    return #[{
      cost := 1, label := "specialize equality at target", role := `rewrite,
      preparation := .normalization, major := some evidence.rule,
      command? := some command,
      run := g.withContext do
        let result ← g.rewrite (← g.getType) (mkFVar evidence.rule) (symm := evidence.reverse)
        let child ← g.replaceTargetEq result.eNew result.eqProof
        setGoals (child :: result.mvarIds) }] }

-- Targeted rewriting is opt-in: it can avoid saturation, but can also duplicate
-- a cheap simplifier proof. The standard tactic preserves its existing provider.
private def defaults : Array Critic := #[blockedPremise]

/-- The same repairs without an engine adapter, for lookahead or other search
consumers. Visiting a proposal does not execute it. -/
public def propose (goal : MVarId) : Choices Move := fun visit => do
  for critic in defaults do
    if ← critic.propose goal visit then return true
  return false

/-- Default repair providers; traversal and scheduling are independent hooks. -/
public def hooks (inner : Hooks := {}) : Hooks := Critic.hooks defaults inner

end waterfall.Critics
