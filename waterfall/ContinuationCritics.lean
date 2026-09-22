module
public import waterfall.Recursion
public meta import Lean.Meta.Tactic.Rewrite

meta section
open Lean Meta Elab Tactic
namespace waterfall.Critics
open Recursion

/-- A conditional local fact can be useful even when its premises need search.
Every premise remains a sibling obligation; observations retain only a local ID. -/
public def conditionalFacts : Critic := {
  Evidence := FVarId
  observe := fun _ => do
    let mut evidence := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || !(← isProp d.type) then continue
      let useful ← withoutModifyingState <| forallTelescopeReducing d.type fun xs body => do
        if body.isConstOf ``False || body.isConstOf ``True then return false
        if xs.isEmpty || body.hasAnyFVar (fun id => xs.any (·.containsFVar id)) then return false
        for x in xs do unless ← isProp (← inferType x) do return false
        return (← findLocalDeclWithType? body).isNone
      if useful then evidence := evidence.push d.fvarId
    return evidence
  repair := fun goal id => pure #[{
    cost := 1, label := "combine conditional hypothesis", role := `combine,
    major := some id,
    run := goal.withContext do
      let (args, _, _) ← forallMetaTelescopeReducing (← id.getDecl).type
      let proof := mkAppN (mkFVar id) args
      let (_, next) ← goal.note (← mkFreshUserName `derived) proof
      setGoals (args.toList.map (·.mvarId!) ++ [next]) }] }

private structure ContinuationEvidence where
  call : Expr
  plan : Generalization.Plan

/-- Keep the recursive call's parameters fixed. A second variant drops foreign
recursive propositions and rediscovers the call in that stronger context. -/
public def inductionContinuations (rules : Array (TSyntax `term)) : Critic := {
  Evidence := ContinuationEvidence
  observe := fun goal => do
    let targetNames := (← instantiateMVars (← goal.getType)).getUsedConstants
    let mut discardIds := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || !(← isProp d.type) then continue
      let foreign ← IO.mkRef false
      d.type.forEach fun e => do
        if e.isApp && !e.hasLooseBVars then
          if let .const n _ := e.getAppFn then
            if !targetNames.contains n && (← isProp e) && (← isRecursiveDefinition n) then
              foreign.set true
      if ← foreign.get then discardIds := discardIds.push d.fvarId
    let mut evidence := #[]
    for prune in [false, true] do
      if prune && discardIds.isEmpty then continue
      let plan : Generalization.Plan := {
        clearBefore := if prune then discardIds.reverse else #[] }
      let calls ← withoutModifyingState do
        let prepared ← Generalization.prepare goal plan
        prepared.goal.withContext <| Recursion.calls prepared.goal rules
      for (call, _) in calls do
        let .const n _ := call.getAppFn | continue
        let some info ← getFunIndInfo? false false n | continue
        let args := call.getAppArgs
        unless args.size == info.params.size do continue
        let targets := (args.zip info.params).filter (fun (_, k) => k == .target)
        unless !targets.isEmpty && targets.all (fun (a, _) => a.isFVar) do continue
        evidence := evidence.push ⟨call, plan⟩
    return evidence
  repair := fun goal evidence => do
    let pruned := !evidence.plan.clearBefore.isEmpty
    return #[{
      cost := 1, induction := .functional, subject := some evidence.call,
      generalization := evidence.plan,
      role := if pruned then `prunedFunction else `directFunction,
      label := if pruned then "prune recursive premises and induct" else "function induction fixed parameters",
      run := Induction.withPlan goal evidence.call evidence.plan true }] }

/-- A supplied equation blocked only by a semireducible wrapper. Conditions
must already be available; execution nevertheless retains all rewrite premises. -/
public def transparentRules (rules : Array (TSyntax `term)) : Critic := {
  Evidence := TSyntax `term
  observe := fun g => do
    let mut out := #[]
    let targetNames := (← instantiateMVars (← g.getType)).getUsedConstants
    let mut recursiveNames := #[]
    for rule in rules do
      if rule.raw.isIdent then
        try
          let n ← resolveGlobalConstNoOverload rule
          if ← isRecursiveDefinition n then recursiveNames := recursiveNames.push n
        catch _ => pure ()
    for rule in rules do
      let equation ← withoutModifyingState do
        try
          let proof ← Term.elabTerm rule none
          unless ← isProp (← inferType proof) do return false
          forallTelescopeReducing (← inferType proof) fun _ body => do
            let lhs ← if let some (_, lhs, _) := body.eq? then pure lhs
              else if body.isAppOfArity ``Iff 2 then
                -- Existential/universal expansions are elimination rules, not
                -- local simplifications. Keep them in ordinary theorem search.
                let rhs := body.getAppArgs[1]!
                if (rhs.find? fun e => e.isForall || e.isAppOf ``Exists).isSome then
                  return false
                pure body.getAppArgs[0]!
              else return false
            -- Default transparency must not invent a recursive input by reducing
            -- a pattern such as f (remove ?a ?xs) against an unrelated call.
            return !recursiveNames.any (fun n =>
              lhs.getUsedConstants.contains n && !targetNames.contains n)
        catch _ => return false
      unless equation do continue
      out := out.push rule
    return out
  repair := fun g rule => do
    let command ← `(tactic| (erw [$rule:term]; all_goals try assumption))
    return #[{
      label := s!"rewrite supplied equation {rule}", command? := some command,
      run := evalTactic command,
      role := `ruleRewrite
      check := some do
        try
          let proof ← Term.elabTerm rule none
          -- This is a transparency fallback, not another copy of an ordinary
          -- rewrite already available to simplification and theorem search.
          let ordinary ← withoutModifyingState do
            try
              discard <| g.rewrite (← g.getType) proof
                (config := { transparency := .reducible })
              return true
            catch _ => return false
          if ordinary then return false
          let r ← g.rewrite (← g.getType) proof (config := { transparency := .default })
          -- Restrict this shortcut to already known conditions. Other theorem
          -- applications remain available through ordinary proof search.
          for premise in r.mvarIds do
            unless ← premise.isAssigned do premise.assumption
          return true
        catch _ => return false }] }

private structure RecursiveRewrite where
  rule : FVarId
  reverse : Bool

/-- Orient a local equality toward an already-present recursive result. -/
public def recursiveEquality (rules : Array (TSyntax `term)) : Critic := {
  Evidence := RecursiveRewrite
  observe := fun g => do
    let target ← instantiateMVars (← g.getType)
    if target.isForall then return #[]
    let rewriteCalls ← recursiveResults g rules target (includeImported := true)
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || !(← isProp d.type) then continue
      let orientations ← withoutModifyingState do
        forallTelescopeReducing d.type fun _ body => do
          let some (_, lhs, rhs) := body.eq? | return #[]
          let mut orientations := #[]
          for reverse in [false, true] do
            let into := if reverse then lhs else rhs
            unless rewriteCalls.any (fun call =>
                into.getUsedConstants.contains call.getAppFn.constName!) do continue
            let useful ← withoutModifyingState do
              try
                let (args, _, body) ← forallMetaTelescopeReducing d.type
                let some (_, lhs, rhs) := body.eq? | return false
                discard <| g.rewrite target (mkAppN (mkFVar d.fvarId) args) (symm := reverse)
                let source ← instantiateMVars (if reverse then rhs else lhs)
                let into ← instantiateMVars (if reverse then lhs else rhs)
                return rewriteCalls.any fun call => occurs call into && !occurs call source
              catch _ => return false
            if useful then orientations := orientations.push reverse
          return orientations
      for reverse in orientations do out := out.push ⟨d.fvarId, reverse⟩
    return out
  repair := fun g evidence => do
    let id := evidence.rule
    let reverse := evidence.reverse
    let h := mkIdent (← id.getDecl).userName
    let rewrite ← if reverse then `(tactic| rewrite [← $h:ident])
      else `(tactic| rewrite [$h:ident])
    let command ← `(tactic| ($rewrite; try clear $h:ident))
    return #[{
      cost := 1, label := "rewrite recursive hypothesis", major := some id,
      role := `recursiveRewrite,
      command? := some command
      run := g.withContext do
        let r ← g.rewrite (← g.getType) (mkFVar id) (symm := reverse)
        let next ← g.replaceTargetEq r.eNew r.eqProof
        setGoals ((← next.tryClear id) :: r.mvarIds) }] }

private structure SharedResult where
  plan : Generalization.Plan

private def functionalMoves (goal : MVarId) (rules : Array (TSyntax `term)) :
    TacticM (Array Move) := do
  let mut moves := #[]
  for (call, summary) in ← Recursion.calls goal rules do
    moves := moves ++ (← ((functionalInduction call summary).propose goal).collect)
  return moves

/-- Shared recursive outputs suggest a stronger invariant. Target/premise
sharing is the default; deeper search also considers two distinct premises. -/
public def sharedResults (rules : Array (TSyntax `term)) (includePremises := false) : Critic := {
  Evidence := SharedResult
  observe := fun goal => do
    let target ← instantiateMVars (← goal.getType)
    if target.isForall then return #[]
    let mut calls ← recursiveResults goal rules target
    if includePremises then
      let mut counts : Array (Expr × Nat) := #[]
      for d in (← getLCtx) do
        if d.isImplementationDetail || !(← isProp d.type) then continue
        for call in ← recursiveResults goal rules (← instantiateMVars d.type) do
          if let some i := counts.findIdx? (·.1 == call) then
            counts := counts.modify i fun (e, n) => (e, n + 1)
          else counts := counts.push (call, 1)
      for (call, count) in counts do
        if count >= 2 && !calls.contains call then calls := calls.push call
    let mut shared := #[]
    let mut hyps := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || !(← isProp d.type) then continue
      hyps := hyps.push d.fvarId
      let type ← instantiateMVars d.type
      for call in calls do
        if occurs call type && !shared.contains call then shared := shared.push call
    shared := shared.filter fun call => !shared.any (fun other => other != call && occurs call other)
    let mut selections := shared.map fun call => #[call]
    if shared.size > 1 && shared.size <= 2 then selections := #[shared] ++ selections
    let lctx ← getLCtx
    return selections.map fun selected => {
      plan := {
        abstractions := selected.map fun expression => {expression, retainEquation := false}
        hypotheses := hyps
        clearAfter := (lctx.foldl (init := #[]) fun ids d =>
          if selected.any (·.containsFVar d.fvarId) then ids.push d.fvarId else ids).reverse } }
  repair := fun goal evidence => do
    let plan := evidence.plan
    let prepare : TacticM MVarId := do
      let prepared ← Generalization.prepare goal plan
      setGoals [prepared.goal]
      return prepared.goal
    let commands ← Generalization.commands plan
    let command ← `(tactic| ($commands:tactic*))
    -- Only ordinals and ordinary syntax leave the speculative checkpoint.
    -- Rebuild the induction from the prepared goal at execution time.
    let choices ← withoutModifyingState do
      try
        let next ← prepare
        next.withContext do
          let moves ← functionalMoves next rules
          moves.mapIdxM fun i move => do
            let induct ← Induction.command move.subject.get! move.generalization true
            return (i, ← `(tactic| ($command; $induct)))
      catch _ => return #[]
    let role := if plan.abstractions.size > 1 then `jointGeneralization else `generalization
    let mut out := #[]
    for (index, recipe) in choices do
      out := out.push {
        cost := 1, induction := .functional, generalization := plan,
        role, subject := plan.abstractions[0]?.map (·.expression),
        label := s!"generalize recursive results and induct {index}", command? := some recipe,
        run := do
          let next ← prepare
          next.withContext do
            let moves ← functionalMoves next rules
            let some move := moves[index]? | throwError "missing generalized induction"
            move.run }
    out := out.push {
      cost := 1, generalization := plan, role,
      subject := plan.abstractions[0]?.map (·.expression),
      label := "generalize recursive results", command? := some command,
      run := do discard prepare }
    return out }

end waterfall.Critics
