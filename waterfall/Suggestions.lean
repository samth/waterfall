module
public import waterfall.Core

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

private def sequence (commands : Array (TSyntax `tactic)) : TacticM (TSyntax `tactic) :=
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
  let mut others : Array (TSyntax `ident) := #[]
  for d in (← getLCtx) do
    unless d.isImplementationDetail || call.containsFVar d.fvarId ||
        (← isProp d.type) || (← isType (mkFVar d.fvarId)) do
      others := others.push (mkIdent d.userName)
  let tactic ← `(tactic| fun_induction $target)
  if others.isEmpty then return tactic
  `(tactic| (revert $others*; $tactic))

/-- Ordinary induction, including the equation-preserving abstraction needed
when an indexed relation is applied to a fixed expression. These are standard
`revert`, `generalize`, and `induction` commands; search still owns the motive. -/
private def inductionCommand (step : Selection) (major : FVarId) :
    TacticM (TSyntax `tactic) := do
  let target := mkIdent (← major.getDecl).userName
  let declaredType ← inferType (mkFVar major)
  let majorType ← whnf declaredType
  let mut commands := #[]
  let generalized := step.motive == InductionMotive.localGeneralization ||
    step.motive == InductionMotive.localGeneralizationAndIndexAbstraction
  if generalized then
    let mut others : Array (TSyntax `ident) := #[]
    for d in (← getLCtx) do
      unless d.isImplementationDetail || d.fvarId == major ||
          (← isProp d.type) || (← isType (mkFVar d.fvarId)) || declaredType.containsFVar d.fvarId do
        others := others.push (mkIdent d.userName)
    unless others.isEmpty do commands := commands.push (← `(tactic| revert $others*))
  if step.motive == InductionMotive.indexAbstraction ||
      step.motive == InductionMotive.localGeneralizationAndIndexAbstraction then
    let .const name _ := majorType.getAppFn | throwError "missing indexed relation"
    let info ← getConstInfoInduct name
    let mut indices : Array Expr := #[]
    let mut args : Array (TSyntax ``generalizeArg) := #[]
    for index in majorType.getAppArgs[info.numParams:] do
      unless index.isFVar || indices.contains index do
        let n := indices.size
        indices := indices.push index
        let expr ← PrettyPrinter.delab index
        let x := mkIdent ((← getLCtx).getUnusedName (Name.mkSimple s!"wf_index{n}"))
        let h := mkIdent ((← getLCtx).getUnusedName (Name.mkSimple s!"wf_index_eq{n}"))
        args := args.push (← `(generalizeArg| $h:ident : $expr = $x:ident))
    commands := commands.push (← `(tactic| generalize $args,* at $target:ident))
  let induction ← `(tactic| induction $target:ident)
  let induction ← if generalized then `(tactic| $induction <;> intros) else pure induction
  sequence (commands.push induction)

/-- Render the common proof vocabulary. Display labels only select proposed
recipes; they are never trusted as replay identifiers or evidence of correctness.
The final independent elaboration is mandatory even for an all-tactic script. -/
private def command (step : Selection) (rules : Array (TSyntax `term))
    (forwardProof? : Option Expr) :
    TacticM (TSyntax `tactic) := withMainContext do
  let g ← getMainGoal
  let rules ← prepareRules g rules
  let moves ← movesFor g rules step.strength step.remaining step.action.group
  let some move := moves[step.action.index]? | throwError "unknown proof operation"
  if let some command := move.command? then
    -- The engine runs an operation with its siblings outside the goal list.
    -- In particular, a closing `done` must not inspect those pending siblings.
    if step.action.group == .close then return ← `(tactic| focus ($command:tactic))
    return command
  if step.action.group == .functions then return ← functionalCommand move
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
      inductionCommand step major

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
    (path : Path) (rules : Array (TSyntax `term)) : TacticM Script := do
  let winning ← Tactic.saveState
  let proofs ← roots.mapM fun g => instantiateMVars (mkMVar g)
  try
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
        let tac ← command step rules forwardProof?
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
  let script ← Term.withoutTacticIncrementality true <| compile initial roots (← path.get) rules
  Meta.Tactic.TryThis.addSuggestion ref script.tactic (origSpan? := ref)
  return stats

end waterfall.Suggestions
