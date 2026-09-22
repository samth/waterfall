module
public import waterfall.Core
public meta import Lean.Elab.Tactic.RenameInaccessibles

meta section

/-!
Compile a retained proof path into ordinary Lean tactics. This module is a
frontend: it neither adds proof operations nor changes the engine's scheduling.

A command recipe is only a proposal. The entire printed replacement is parsed
and elaborated from the original checkpoint, with recovery disabled, before it
can become a suggestion. Unsupported operations or different elaborator naming
fall back to the completed proof term. Neither route calls waterfall again.
-/

open Lean Meta Elab Tactic Parser.Tactic
namespace waterfall.Suggestions

initialize registerTraceClass `waterfall.suggestions

/-- Only accepted steps are recorded, so failed alternatives never enter a hint.
Allocate this recorder inside each parallel worker, just like other middleware. -/
public abbrev Path := Array (Selection × Tactic.SavedState)

/-- A checked replacement and whether it required the proof-term fallback. -/
public structure Script where
  tactic : TSyntax `tactic
  text : String
  usedTerm : Bool

private def sequence (commands : Array (TSyntax `tactic)) : TacticM (TSyntax `tactic) := do
  if commands.size == 1 then return commands[0]!
  `(tactic| ($commands:tactic*))

private def grindCommand (rules : Array (TSyntax `term)) (strength : Nat)
    (constructors : Bool) : TacticM (TSyntax `tactic) := do
  let mut rules := rules
  if constructors then
    let extra ← forallTelescopeReducing (← (← getMainGoal).getType) fun _ target => do
      let .const name _ := target.getAppFn | throwError "no target predicate"
      let info ← getConstInfoInduct name
      return info.ctors.toArray.map fun n => (⟨mkIdent n⟩ : TSyntax `term)
    rules := rules ++ extra
  let rs ← rules.mapM fun t => `(grindParam| $t:term)
  if strength == 1 then return ← `(tactic| grind +lax [$rs,*])
  let c : Grind.Config := {}
  let splits := quote (c.splits * strength)
  let gen := quote (c.gen * strength)
  let instances := quote (c.instances * strength)
  let ematch := quote (c.ematch * strength)
  let ringSteps := quote (c.ringSteps * strength)
  let acSteps := quote (c.acSteps * strength)
  let canon := quote (c.canonHeartbeats * strength)
  `(tactic| grind (config := {lax := true, splits := $splits, gen := $gen,
                              instances := $instances, ematch := $ematch, ringSteps := $ringSteps,
                              acSteps := $acSteps, canonHeartbeats := $canon}) [$rs,*])

/-- The subject is semantic metadata, not elaborator syntax containing named
holes. Generalized variables are printed before Lean's ordinary elimination
command. No inference is rerun merely to recover what it acted upon. -/
private def functionalCommand (move : Move) : TacticM (TSyntax `tactic) := do
  let some call := move.subject | throwError "missing functional elimination subject"
  let target ← PrettyPrinter.delab call
  if move.induction == .none then return ← `(tactic| fun_cases $target)
  Induction.command call move.generalization true

/-- Render the common proof vocabulary. Display labels only select proposed
recipes; they are never trusted as replay identifiers or evidence of correctness.
The final independent elaboration is mandatory even for an all-tactic script. -/
private def command (step : Selection) (rules : Array (TSyntax `term)) (hooks : Hooks)
    (forwardProof? : Option Expr) :
    TacticM (TSyntax `tactic) := withMainContext do
  let g ← getMainGoal
  let rules ← prepareRules g rules
  let moves ← movesFor g rules step.strength step.remaining step.action.group
  let moves := moves ++ (← hooks.extraMoves g rules step.strength step.remaining step.action.group)
  let some move := moves[step.action.index]? | throwError "unknown proof operation"
  if let some command := move.command? then
    -- The engine runs an operation with its siblings outside the goal list.
    -- In particular, a closing `done` must not inspect those pending siblings.
    if step.action.group == .close then return ← `(tactic| focus ($command:tactic))
    return command
  if step.action.group == .functions || move.induction == .functional then
    return ← functionalCommand move
  -- Resolve constructor names from the target's declaration, avoiding parsing
  -- a display name back into a Lean identifier (which can contain quoted dots).
  let type ← whnf (← g.getType)
  if let .const name _ := type.getAppFn then
    if let some (.inductInfo info) := (← getEnv).find? name then
      for ctor in info.ctors do
        if step.label == s!"close constructor {ctor}" || step.label == s!"constructor {ctor}" then
          return ← `(tactic| apply $(mkIdent ctor))
  match step.label with
  | "forward hypothesis" => do
    let some proof := forwardProof? | throwError "missing forward derivation"
    let term ← PrettyPrinter.delab proof
    let name := mkIdent ((← getLCtx).getUnusedName `derived)
    `(tactic| have $name:ident := $term)
  | "grind" => grindCommand rules step.strength false
  | "grind constructors" => grindCommand rules step.strength true
  | "intro" => `(tactic| intro _)
  | "introduce binders" => `(tactic| intros)
  | "function extensionality" => `(tactic| (apply funext; intros))
  | "split target" => `(tactic| split)
  | _ =>
    let some major := move.major | throwError "operation requires proof-term rendering"
    let target : TSyntax `term := ⟨mkIdent (← major.getDecl).userName⟩
    if step.induction == .none then
      if step.label.endsWith " registered" then
        `(tactic| cases $target:term)
      else
        `(tactic| set_option tactic.customEliminators false in cases $target:term)
    else
      Induction.command (mkFVar major) move.generalization

/-- Reparse the displayed text, so validation checks exactly what the editor
will insert, rather than syntax carrying hidden elaborator references. -/
private def checkText (initial : Tactic.SavedState) (roots : List MVarId)
    (tactic : TSyntax `tactic) (usedTerm : Bool) : TacticM Script := do
  let raw := if usedTerm then tactic.raw else tactic.raw.rewriteBottomUp fun stx => match stx with
    | .ident info raw name _ => .ident info raw name.eraseMacroScopes []
    | other => other
  let text := (← PrettyPrinter.ppTactic ⟨raw⟩).pretty
  let stx ← match Parser.runParserCategory (← getEnv) `tactic text with
    | .ok stx => pure stx
    | .error error => throwError "could not parse the printed proof: {error}\n{text}"
  initial.restore true
  Term.withoutErrToSorry <| withoutRecover <| evalTactic stx
  checkComplete roots
  unless (← getUnsolvedGoals).isEmpty do throwError "replacement left obligations"
  return ⟨⟨stx⟩, text, usedTerm⟩

/-- The retained search trace is an agenda traversal, not a proof script. Recover
its parent/child structure before printing: a policy can visit siblings in any
order. Shared obligations that do not form a tree keep the checked trace fallback. -/
private inductive ProofTree where
  | step (selection : Selection) (saved : Tactic.SavedState) (children : Array ProofTree)

private def proofForest (roots : List MVarId) (path : Path) : TacticM (Array ProofTree) := do
  let mut forest : Array (MVarId × ProofTree) := #[]
  for (step, saved) in path do
    let some goal := step.agenda[step.focus]? | throwError "missing recorded goal"
    let siblings := step.agenda.eraseIdx step.focus
    let children := forest.filter (fun entry => !siblings.contains entry.1)
    unless children.size == step.children do throwError "retained path is not a complete proof tree"
    let parent := ProofTree.step step saved (children.map (·.2))
    let available := (forest.filter fun entry => siblings.contains entry.1).push (goal, parent)
    forest := step.agenda.toArray.filterMap fun g => available.find? (·.1 == g)
  unless forest.map (·.1) == roots.toArray do throwError "retained path does not cover the roots"
  return forest.map (·.2)

/-- Flatten only syntactic grouping, not tacticals such as `first` or `<;>`.
Every structured branch is already focused, so the trace's `focus` is redundant. -/
private partial def commandsOf (tac : TSyntax `tactic) : Array (TSyntax `tactic) :=
  match tac with
  | `(tactic| ($commands:tactic*)) => commands.getElems.flatMap commandsOf
  | `(tactic| focus ($body:tactic)) => commandsOf body
  | _ => #[tac]

/-- Pretty-printing must use names visible in the replayed branch, not fresh
names from the search checkpoint. Corresponding declarations retain their order;
if a recipe changes that context shape, abandon this rendering and check the
faithful trace instead. The final parsed proof remains the correctness check. -/
private def inRecordedContext (step : Selection) (saved winning : Tactic.SavedState)
    (body : Option Expr → TacticM α) : TacticM α := do
  let live ← Tactic.saveState
  let names ← (← getMainGoal).withContext do
    return (← getLCtx).foldl (fun out d => out.push d.userName) (#[] : Array Name)
  try
    let some goal := step.agenda[step.focus]? | throwError "missing recorded goal"
    let forwardProof? ← if step.action.group == .forward then do
      winning.restore true
      let some (.app _ value) ← getExprMVarAssignment? goal
        | throwError "missing forward-step assignment"
      pure (some (← instantiateMVars value))
    else pure none
    saved.restore true
    let decl ← goal.getDecl
    let locals := decl.lctx.foldl (fun out d => out.push d) (#[] : Array LocalDecl)
    unless locals.size == names.size do throwError "replay changed the local context shape"
    let mut lctx := decl.lctx
    for d in locals, name in names do lctx := lctx.setUserName d.fvarId name
    let renamed ← mkFreshExprMVarAt lctx decl.localInstances decl.type .syntheticOpaque decl.userName
    setGoals [renamed.mvarId!]
    body forwardProof?
  finally live.restore true

/-- Keep each supplied/discovered rule once. Identifier aliases often name the
same definition; elaboration is used only for deduplication, never inference. -/
private def distinctRules (rules : Array (TSyntax `term)) : TacticM (Array (TSyntax `term)) := do
  let mut seen : Array Expr := #[]
  let mut out := #[]
  for rule in rules do
    let value ← withoutModifyingState <| Term.elabTerm rule none
    -- A bare polymorphic identifier gets fresh implicit arguments/levels on
    -- elaboration. Its declaration, not those temporary holes, identifies it.
    let key := if rule.raw.isIdent then
      match value.consumeMData.getAppFn with
      | .const name _ => mkConst name
      | head => head
      else value
    if seen.contains key then continue
    seen := seen.push key
    out := out.push rule
  return out

/-- Concise recipes are proposals. Try ordinary solver defaults before retaining
scaled settings from discovery. Leaves must close and normalization must retain
the expected branches; final replay checks the continuation and shared holes. -/
private def conciseRecipes (step : Selection) (rules : Array (TSyntax `term)) :
    TacticM (Array (TSyntax `tactic)) := withMainContext do
  if step.closure == .simplification || step.label == "normalize" then
    let rules ← distinctRules (← prepareRules (← getMainGoal) rules)
    let rs ← rules.mapM fun t => `(simpLemma| $t:term)
    if rs.isEmpty then return #[← `(tactic| simp_all)]
    return #[← `(tactic| simp_all [$rs,*])]
  match step.closure with
  | .exact =>
    let mut out := #[]
    if let some id ← findLocalDeclWithType? (← (← getMainGoal).getType) then
      let name := mkIdent (← id.getDecl).userName
      out := out.push (← `(tactic| exact $name:ident))
    return out ++ #[← `(tactic| rfl), ← `(tactic| contradiction)]
  | .saturation =>
    if step.label != "grind" then return #[]
    let rules ← distinctRules (← prepareRules (← getMainGoal) rules)
    let rs ← rules.mapM fun t => `(grindParam| $t:term)
    if rs.isEmpty then return #[← `(tactic| grind)]
    return #[← `(tactic| grind [$rs,*])]
  | _ => return #[]

/-- Introduce variables with ordinary, collision-free names at their binder.
This runs only while rendering a known proof and does not add engine moves. -/
private def namedIntros (all : Bool) : TacticM (TSyntax `tactic) := do
  let saved ← Tactic.saveState
  let mut names : Array (TSyntax `term) := #[]
  try
    repeat
      let goal ← getMainGoal
      let type ← goal.withContext <| whnf (← goal.getType)
      let .forallE binder domain _ _ := type | break
      let name ← goal.withContext do
        let base ← if binder.isAnonymous || binder == `_ || binder.hasMacroScopes then do
          if ← isProp domain then pure `h else pure `x
        else pure binder
        return (← getLCtx).getUnusedName base
      names := names.push ⟨mkIdent name⟩
      setGoals [(← goal.intro name).2]
      unless all do break
    unless !names.isEmpty do throwError "no binders to introduce"
    `(tactic| intro $names*)
  finally saved.restore true

/-- Name only inaccessible/shadowed locals, at a case boundary when possible.
Existing user names are preserved. Unlike `expose_names`, the emitted names
are explicit in the proof text and independent of subsequent elaborator choices. -/
private def branchNames (goal : MVarId) : TacticM (Array (TSyntax ``binderIdent)) := goal.withContext do
  let original ← getLCtx
  let exposed ← withExposedNames getLCtx
  let mut names := #[]
  for d in exposed do
    unless d.isImplementationDetail || (original.get! d.fvarId).userName == d.userName do
      names := names.push (← `(binderIdent| $(mkIdent d.userName):ident))
  return names

/-- A branch has an explicit binding site and a complete body. Prefer native
eliminator alternatives; ordinary splits and applications need only bullets. -/
private structure Branch where
  tag : Name
  allFields : Bool := false
  names : Array (TSyntax ``binderIdent)
  body : Array (TSyntax `tactic)

private def nestBranches (commands : Array (TSyntax `tactic)) (branches : Array Branch) :
    TacticM (Array (TSyntax `tactic)) := do
  let mut alts : Array (TSyntax ``inductionAlt) := #[]
  for branch in branches do
    let names ← branch.names.mapM fun name => do
      let `(binderIdent| $id:ident) := name | throwError "missing branch binder"
      pure (⟨id.raw⟩ : TSyntax [`ident, ``Lean.Parser.Term.hole])
    let tag := mkIdent branch.tag
    alts := alts.push (← if branch.allFields then
      `(inductionAlt| | @$tag:ident $names* => $branch.body:tactic*)
      else `(inductionAlt| | $tag:ident $names* => $branch.body:tactic*))
  if let some last := commands.back? then
    let nested? ← match last with
      | `(tactic| induction $major:term) =>
        pure <| some (← `(tactic| induction $major:term with $alts:inductionAlt*))
      | `(tactic| fun_induction $call:term) =>
        pure <| some (← `(tactic| fun_induction $call:term with $alts:inductionAlt*))
      | `(tactic| cases $major:term) =>
        pure <| some (← `(tactic| cases $major:term with $alts:inductionAlt*))
      | _ => pure none
    if let some nested := nested? then return commands.pop.push nested
  let mut out := commands
  for branch in branches do
    let body := branch.body
    if branch.names.isEmpty then
      out := out.push (← `(tactic| · $body:tactic*))
    else if branch.tag.isAnonymous then
      let body := #[← `(tactic| rename_i $branch.names*)] ++ body
      out := out.push (← `(tactic| · $body:tactic*))
    else
      let tag ← `(binderIdent| $(mkIdent branch.tag):ident)
      out := out.push (← `(tactic| case $tag:binderIdent $branch.names* => $body:tactic*))
  return out

/-- Replay the tree in proof order while constructing nested branch syntax.
The renderer owns no search state: every operation comes from the winning path. -/
private partial def renderTree (tree : ProofTree) (rules : Array (TSyntax `term))
    (hooks : Hooks) (winning : Tactic.SavedState) (compact : Bool) :
    TacticM (Array (TSyntax `tactic)) := do
  let .step step saved children := tree
  let roots ← getUnsolvedGoals
  let mut recipes ← inRecordedContext step saved winning fun forward => do
    let simple ← if compact then conciseRecipes step rules else pure #[]
    let original ← command step rules hooks forward
    let ordinaryCases ← match original with
      | `(tactic| set_option tactic.customEliminators false in cases $major:term) =>
        if compact then pure #[← `(tactic| cases $major:term)] else pure #[]
      | _ => pure #[]
    return simple ++ ordinaryCases ++ #[original]
  if step.preparation == .oneBinder || step.preparation == .allBinders then
    recipes := #[← namedIntros (step.preparation == .allBinders)]
  let checkpoint ← Tactic.saveState
  let mut selected := none
  for recipe in recipes do
    checkpoint.restore true
    try
      let commands := commandsOf recipe
      for tac in commands do Term.withoutErrToSorry <| withoutRecover <| evalTactic tac
      unless (← getUnsolvedGoals).length == children.size do
        throwError "recipe changed the number of branches"
      selected := some commands
      break
    catch _ => pure ()
  let some commands := selected | throwError "no replayable recipe"
  let mut out := commands
  let mut branches := #[]
  let goals ← getUnsolvedGoals
  for child in children, goal in goals do
    setGoals [goal]
    let names ← branchNames goal
    if children.size == 1 && names.isEmpty then
      out := out ++ (← renderTree child rules hooks winning compact)
    else
      let tag ← goal.getTag
      let allFields ← goal.withContext do
        let original ← getLCtx
        let exposed ← withExposedNames getLCtx
        return exposed.any fun d =>
          !d.isImplementationDetail && d.binderInfo != .default &&
          (original.get! d.fvarId).userName != d.userName
      let renamed ← renameInaccessibles goal names
      setGoals [renamed]
      renamed.setTag .anonymous
      let body ← renderTree child rules hooks winning compact
      branches := branches.push {tag, allFields, names, body}
  unless branches.isEmpty do out ← nestBranches commands branches
  checkComplete roots
  setGoals []
  return out

private def structuredScript (initial winning : Tactic.SavedState) (roots : List MVarId)
    (forest : Array ProofTree) (rules : Array (TSyntax `term)) (hooks : Hooks)
    (compact : Bool) : TacticM Script := do
  initial.restore true
  let mut out := #[]
  for tree in forest, goal in roots do
    setGoals [goal]
    let names ← branchNames goal
    let renamed ← renameInaccessibles goal names
    setGoals [renamed]
    let mut body ← renderTree tree rules hooks winning compact
    unless names.isEmpty do body := #[← `(tactic| rename_i $names*)] ++ body
    if roots.length == 1 then out := out ++ body
    else out := out.push (← `(tactic| · $body:tactic*))
  checkText initial roots (← sequence out) false

/-- Leaf solvers may create private auxiliary declarations. A pasted proof
cannot refer to declarations that existed only after the search. Inline those
new constants, retaining existing named lemmas from the original environment. -/
private partial def inlineAuxiliaries (original : Environment) (proof : Expr) : MetaM Expr :=
  withIncRecDepth do
    Core.checkSystem "waterfall proof rendering"
    let mut result := proof
    for name in proof.getUsedConstants do
      if original.contains name then continue
      let info ← getConstInfo name
      let some value := info.value? (allowOpaque := true)
        | throwError "proof uses an unavailable auxiliary declaration {name}"
      result := result.replace fun expr => match expr with
        | .const n levels => if n == name then some (value.instantiateLevelParams info.levelParams levels) else none
        | _ => none
    if result == proof then return result.headBeta
    inlineAuxiliaries original result.headBeta

/-- Produce a checked standalone script, restoring the winning proof afterward.
The saved final expressions are fully instantiated before restoring the input:
no worker-local metavariable or elaborator hole may escape into the suggestion. -/
public def compile (initial : Tactic.SavedState) (roots : List MVarId)
    (path : Path) (rules : Array (TSyntax `term)) (hooks : Hooks := {}) : TacticM Script := do
  let winning ← Tactic.saveState
  let proofs ← roots.mapM fun g => instantiateMVars (mkMVar g)
  try
    let forest? ← tryCatch (some <$> proofForest roots path) (fun ex => do
      trace[waterfall.suggestions] "proof tree reconstruction failed: {ex.toMessageData}"
      pure none)
    if let some forest := forest? then
      for compact in [true, false] do
        let script? ← tryCatch
          (some <$> structuredScript initial winning roots forest rules hooks compact)
          (fun ex => do
            trace[waterfall.suggestions] "structured rendering failed: {ex.toMessageData}"
            pure none)
        if let some script := script? then return script
    tryCatch (do
      let mut commands := #[]
      for (step, saved) in path.reverse do
        let some g := step.agenda[step.focus]? | throwError "missing recorded goal"
        -- note assigns the input goal to `newGoal derivedProof`. Read that
        -- small proof from the winner, without rerunning forward enumeration
        -- or delaborating the surrounding proof and its private auxiliaries.
        let forwardProof? ← if step.action.group == .forward then do
          winning.restore true
          let some (.app _ value) ← getExprMVarAssignment? g
            | throwError "missing forward-step assignment"
          pure (some (← instantiateMVars value))
        else pure none
        saved.restore true
        setGoals [g]
        let tag ← g.getTag
        -- case' puts the selected goal's children before the other siblings,
        -- exactly as Space.expand does. A cyclic rotation would reorder them.
        evalTactic (← `(tactic| expose_names))
        let tac ← command step rules hooks forwardProof?
        if step.focus == 0 then
          commands := commands.push (← `(tactic| expose_names))
          commands := commands.push tac
        else
          if tag.isAnonymous then throwError "unnamed non-head goal"
          let tagIdent ← `(binderIdent| $(mkIdent tag):ident)
          let caseTag ← `(Lean.Parser.Tactic.caseArg| $tagIdent:binderIdent)
          commands := commands.push (← `(tactic| case' $caseTag => (expose_names; $tac)))
      winning.restore true
      return ← checkText initial roots (← sequence commands) false
    ) (fun ex => do
      trace[waterfall.suggestions] "command rendering failed: {ex.toMessageData}"
      winning.restore true
      let original ← withoutModifyingState do
        initial.restore true
        getEnv
      let mut commands := #[← `(tactic| expose_names)]
      for (g, proof) in roots.zip proofs do
        let term ← g.withContext <| withExposedNames do
          PrettyPrinter.delab (← inlineAuxiliaries original proof)
        commands := commands.push (← `(tactic| exact $term))
      return ← checkText initial roots (← sequence commands) true)
  finally
    winning.restore true

/-- Install the standard Lean editor hint after checking its literal replacement.
The span is the whole invocation, including configuration and rule arguments. -/
public def run (ref : Syntax) (rules : Array (TSyntax `term))
    (hooks : Hooks) (use : Hooks → TacticM Stats) : TacticM Stats := do
  let initial ← Tactic.saveState
  let roots ← getUnsolvedGoals
  let path ← IO.mkRef (#[] : Path)
  let stats ← use { hooks with accepted := fun step saved => do
    hooks.accepted step saved
    path.modify (·.push (step, saved)) }
  let script ← Term.withoutTacticIncrementality true <| compile initial roots (← path.get) rules hooks
  Meta.Tactic.TryThis.addSuggestion ref script.tactic (origSpan? := ref)
  return stats

end waterfall.Suggestions
