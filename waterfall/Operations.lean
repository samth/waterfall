module
public import waterfall.Execution
public import waterfall.InductionPlan
public import waterfall.ConstructorCritics
public import waterfall.FocusingCritics
public import waterfall.ContinuationCritics
public meta import Lean.Elab.Tactic.Induction
public import waterfall.Leaf
public meta import Lean.Elab.Tactic.Grind.Main
public meta import Lean.Meta.Tactic.Grind.Types
public meta import Lean.Meta.Tactic.LibrarySearch
public meta import Lean.Meta.Tactic.Split

meta section

/-!
Lean-native inductive proof search. This engine imports only its protocol and
Lean; tactic syntax and optional search policies live in separate modules.

Read `movesFor` for the proof vocabulary: close a leaf, prepare a conjecture,
analyze assumptions, apply a rule backward, derive a fact forward, or induct.
Each named generator returns deferred `Move`s, not already-changed proof states.
The driver in `Core` schedules these operations and owns their continuations.
Resource controls, counters and checkpoint data are declared in `Protocol`.

Generators must capture only values valid in their input checkpoint. In
particular, elaborator holes and fresh witnesses are created when a move runs,
after restoring that checkpoint. Case/induction alternatives stay separate
even when they share a helper: their order is part of recorded-plan replay.

The default search uses iterative deepening over Lean proof operations. Every
alternative owns its *entire continuation*, including sibling goals: a later
failure can undo an earlier witness choice. Optional policies select among these
transitions. Only fully closed proofs are returned. The per-run effort counter
and actual heartbeat counter live outside rollback; failed work is never refunded.
-/

open Lean Meta Elab Tactic

namespace waterfall

private def tacticMove (label : String) (stx : TSyntax `tactic) : Move :=
  { cost := 1, label := label, command? := some stx, run := evalTactic stx }

open Recursion

private def terms (names : Array Name) : Array (TSyntax `term) :=
  names.map fun n => ⟨mkIdent n⟩

/-- Shared simplifier configuration. Closing requires `done`; normalization
leaves its changed obligations available to the continuation. -/
private def simplification (rules : Array (TSyntax `term)) (strength : Nat) : TacticM (TSyntax `tactic) := do
  let simpRules ← rules.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let steps := quote (Simp.defaultMaxSteps * strength)
  -- Discharging a conditional simp lemma recursively invokes the simplifier.
  -- Let every depth remain reachable at higher strengths without multiplying
  -- this branching limit at each effort increase. Rewrite steps still scale
  -- linearly with strength.
  let discharge := quote (({} : Simp.Config).maxDischargeDepth + Nat.log2 strength / 2)
  `(tactic| simp_all (config := {maxSteps := $steps, maxDischargeDepth := $discharge}) [$simpRules,*])

/-- The leaves delegate inference to Lean. Progressing normalization and case
analysis are separate moves, so a destructive normalization can be undone.
-/

private def closeGoal (rules : Array (TSyntax `term)) (strength : Nat) :
    TacticM (Array Move) := do
  -- Scale the leaf solver's own limits as well as its surrounding heartbeat
  -- slice. Extra outer time cannot help a solver stopped by an internal cap.
  let c : Grind.Config := {}
  let grindConfig : Grind.Config := { c with
    verbose := (← isTracingEnabledFor `waterfall.search) || (← isDiagnosticsEnabled),
    lax := true, splits := c.splits * strength, gen := c.gen * strength,
    instances := c.instances * strength, ematch := c.ematch * strength,
    ringSteps := c.ringSteps * strength, acSteps := c.acSteps * strength,
    canonHeartbeats := c.canonHeartbeats * strength }
  let simp ← simplification rules strength
  -- Recursive predicate constructors are also forward laws for the leaf solver.
  -- Keep this separate: recursive relation constructors can be expensive.
  -- After ordinary grind, try constructors of the recursive Prop at the target
  -- head, looking through leading binders. Ignore other predicates and data.
  let grind (constructors : Bool) : Move :=
    { cost := 1, label := if constructors then "grind constructors" else "grind", run := do
      let mut extra := #[]
      if constructors then
        extra ← withMainContext do
          forallTelescopeReducing (← (← getMainGoal).getType) fun _ target => do
            unless ← isProp target do return #[]
            let .const n _ := target.getAppFn | return #[]
            let some (.inductInfo info) := (← getEnv).find? n | return #[]
            unless info.isRec do return #[]
            return info.ctors.toArray
        if extra.isEmpty then throwError "no target constructors"
      let rs ← (rules ++ terms extra).mapM fun t => `(Lean.Parser.Tactic.grindParam| $t:term)
      -- Lean's maintained entry keeps rule elaboration and protected metavariables;
      -- passing Config directly avoids constructing and elaborating a tactic call.
      recordExtraModUse (isMeta := false) `Init.Grind.Tactics
      if Grind.grind.warning.get (← getOptions) then
        logWarning "The `grind` tactic is new and its behavior may change in the future. This project has used `set_option grind.warning true` to discourage its use."
      Leaf.grind (← getMainGoal) grindConfig rs }
  -- Closers are accepted only with zero remaining goals. Even then, sibling
  -- obligations can force rollback: a closer may have instantiated a shared hole.
  -- Constructor applications can close a leaf outright, even when their data
  -- arguments are inferred from the target. Enumerate only this target's finite
  -- constructor list. Each application remains separately metered and rollback
  -- includes pending siblings; a constructor leaving premises is not a closer.
  let g ← getMainGoal
  let mut constructors : Array Move := #[]
  let target ← g.withContext <| whnf (← g.getType)
  if let .const n _ := target.getAppFn then
    if let some (.inductInfo info) := (← getEnv).find? n then
      for ctor in info.ctors do
        constructors := constructors.push { cost := 1, label := s!"close constructor {ctor}", run := g.withContext do
          setGoals (← g.apply (← mkConstWithFreshMVarLevels ctor)) }
  return #[
    { tacticMove "assumption/rfl" (← `(tactic| first | assumption | rfl | contradiction)) with
      -- Contradiction contains its own recursive inversion search. Start with
      -- one visited case-analysis goal and scale that hidden search with the
      -- same strength as every other leaf solver; fuel 16 remains reachable.
      closure := .exact, run :=
        evalTactic (← `(tactic| first | assumption | rfl)) <|>
        liftMetaTactic (fun goal => do
          -- Direct refutation is the goal here, rather than a speculative
          -- attempt to prove an arbitrary conclusion from an empty context.
          let refuting ← goal.withContext do
            return (← whnf (← goal.getType)).isConstOf ``False
          let baseFuel := if refuting then ({} : Contradiction.Config).searchFuel else 1
          goal.contradiction { searchFuel := baseFuel * strength }
          return []) },
    { tacticMove "omega" (← `(tactic| omega)) with closure := .arithmetic },
    { tacticMove "simp" (← `(tactic| ($simp:tactic; done))) with closure := .simplification },
    { grind false with closure := .saturation },
    { grind true with closure := .saturation }].map (fun m => { m with cost := 0 }) ++
      constructors.map (fun m => { m with closure := .constructor })

private def customElim? (id : FVarId) (induction : Bool) : TacticM (Option Name) := do
  if tactic.customEliminators.get (← getOptions) then
    getCustomEliminator? #[mkFVar id] induction
  else pure none

-- A registered view may expose recursion hidden by a nonrecursive wrapper.
-- Keep raw cases as an alternative; only the registered path needs elaboration.
private def caseAlternatives (g : MVarId) (id : FVarId) (majorType : Expr)
    (recursive : Bool) (label : String) : TacticM (Array Move) := do
  let recursive := recursive || (← customElim? id true).isSome
  -- Equality elimination substitutes throughout the conjecture and is usually
  -- more constraining than an arbitrary case split. Record that semantic fact
  -- for policies instead of recovering it from names or display text.
  let substitution := majorType.isAppOfArity ``Eq 3 || majorType.isAppOfArity ``HEq 4
  let raw : Move := {
    cost := 1, major := some id, label := label
    role := if substitution then `substitution else if recursive then `inversion else `shape
    run := do
      setGoals ((← g.cases id).toList.map (·.mvarId)) }
  let some name ← customElim? id false | return #[raw]
  return #[{ raw with label := label ++ " registered", run := g.withContext do
    setGoals [g]
    let target ← Term.exprToSyntax (mkFVar id)
    let eliminator := mkIdent name
    evalTactic (← `(tactic| cases $target:term using $eliminator:ident)) }, raw]

/-- Introduce binders, expose pointwise equality, normalize, or split the target. -/
private def prepareGoal (g : MVarId) (rules : Array (TSyntax `term)) (strength : Nat) : TacticM (Array Move) := do
  let target ← whnf (← g.getType)
  let mut out : Array Move := #[]
  if target.isForall then
    out := out.push {
      cost := 1, preparation := .oneBinder, role := `prepare,
      label := "intro", run := liftMetaTactic fun goal => do return [(← goal.intro `_).2] }
    out := out.push {
      cost := 1, preparation := .allBinders, role := `prepare,
      label := "introduce binders", run := liftMetaTactic fun goal => do return [(← goal.intros).2] }
  -- Expose a pointwise obligation to the outer search. A failed leaf solver
  -- cannot return its internal extensionality steps for later induction/cases.
  if let some (_, lhs, _) := target.eq? then
    if (← whnf (← inferType lhs)).isForall then
      out := out.push { cost := 1, preparation := PreparationKind.pointwise, role := `prepare, label := "function extensionality", run := do
        let [child] ← g.apply (← mkConstWithFreshMVarLevels ``funext)
          | throwError "not a function equality"
        setGoals [(← child.intros).2] }
  -- Normalization is also a structural alternative. Unlike the closing simp
  -- above, it may leave changed goals for further planning and be rolled back.
  out := out.push { (tacticMove "normalize" (← simplification rules strength)) with
    preparation := .normalization, role := `prepare }
  out := out.push { cost := 1, preparation := .targetSplit, label := "split target", run := liftMetaTactic fun goal => do
    let some children ← splitTarget? goal | throwError "no target split"
    return children }
  return out

private def analyzeHypotheses (g : MVarId) : TacticM (Array Move) := do
  let mut out : Array Move := #[]
  -- Decompose propositions before speculative induction on data.
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if ← isProp d.type then
      out := out.push { cost := 1, label := "split hypothesis", run := do
        let some cs ← splitLocalDecl? g d.fvarId | throwError "no hypothesis split"
        setGoals cs }
      let ty ← whnf d.type
      if let .const n _ := ty.getAppFn then
        if let some (.inductInfo info) := (← getEnv).find? n then
          out := out ++ (← caseAlternatives g d.fvarId ty info.isRec "cases hypothesis").map
            (fun m => if ty.isAppOf ``And then {m with role := `conjunction} else m)
  return out

/-- Reason backward using local hypotheses, supplied rules, and target constructors. -/
private def applyRules (g : MVarId) (rules : Array (TSyntax `term)) (maxCost : Nat) : TacticM (Array Move) := do
  let mut out : Array Move := #[]
  -- Applying a rule also exposes metavariable-bearing premises. The search
  -- continuation retains all of them, allowing later premises to infer data.
  let provingProp ← isProp (← g.getType)
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    -- Type-valued IHs construct derivations too. Avoid adding these irrelevant
    -- applications to Prop goals; non-function values are handled by assumption.
    if (← isProp d.type) || (!provingProp && (← whnf d.type).isForall) then
      out := out.push { cost := 1, label := "apply hypothesis", run := do
        setGoals (← g.apply (mkFVar d.fvarId)) }
  -- User rules remain syntax until this branch runs. Their local references
  -- must be elaborated in the restored goal's context, not a discarded branch.
  for t in rules do
    out := out.push <| tacticMove "apply rule" (← `(tactic| apply $t))
  -- Backward construction can leave data metavariables shared by its premises.
  -- Trying each constructor separately lets later premises reject a witness.
  let ty ← whnf (← g.getType)
  if let .const n _ := ty.getAppFn then
    if let some (.inductInfo info) := (← getEnv).find? n then
      for ctor in info.ctors do
        out := out.push { cost := 1, role := `targetConstructor, label := s!"constructor {ctor}", run := do
          setGoals (← g.apply (← mkConstWithFreshMVarLevels ctor)) }
      if maxCost >= 2 then
        for ctor in info.ctors do
          out := out ++ (← ((Critics.implicitWitnesses ctor).propose g).collect)
  return out

/-- Retrieve indexed library theorems and offer their individual applications. -/
private def applyLibraryTheorems (g : MVarId) (maxCost : Nat) : TacticM (Array Move) := do
  let mut out : Array Move := #[]
  -- Library search remains available at cost two; direct operations cost one.
  if maxCost >= 2 then
    -- Reuse Lean's indexed theorem retrieval, including iff directions. Keep
    -- each application in the same continuation search as explicit user rules.
    for (name, direction) in ← LibrarySearch.libSearchFindDecls (← g.getType) do
      -- Index matches are approximate. A deferred probe avoids checking
      -- unused later matches. Failed probes never consume an attempt.
      out := out.push {
        cost := 2, label := s!"apply library {name}",
        check := some <| g.withContext do
          try
            discard <| g.apply (← LibrarySearch.mkLibrarySearchLemma name direction)
            pure true
          catch _ => pure false
        run := do setGoals (← g.apply (← LibrarySearch.mkLibrarySearchLemma name direction)) }
  return out

/-- Derive new facts by instantiating quantified hypotheses with available terms. -/
private def instantiateHypotheses (g : MVarId) (strength : Nat) : TacticM (Array Move) := do
  let mut out : Array Move := #[]
  let ts ← contextTerms g
  for d in (← getLCtx) do
    if d.isImplementationDetail || !(← isProp d.type) then continue
    let .forallE _ domain _ _ ← whnf d.type | continue
    -- Besides existing terms, try bounded unary-constructor chains. This adds
    -- useful instances such as h (succ n), without an unbounded term generator.
    let mut wrappers := #[none]
    if !(← isProp domain) then
      if let .const n _ := (← whnf domain).getAppFn then
        if let some (.inductInfo info) := (← getEnv).find? n then
          for c in info.ctors do
            if (← getConstInfoCtor c).numFields == 1 then
              wrappers := wrappers.push (some c)
    for t in ts do
      unless ← withoutModifyingState (isDefEq (← inferType t) domain) do continue
      for wrapper in wrappers do
        for depth in [:if wrapper.isSome then strength + 1 else 1] do
          out := out.push {
            cost := 1, label := "forward hypothesis",
            major := some d.fvarId, subject := some t,
            forward? := some {
              hypothesis := d.fvarId
              argumentSeed := t
              wrapper
              wrapperApplications := if wrapper.isSome then depth + 1 else 0 },
            run := g.withContext do
              let mut arg := t
              if let some c := wrapper then
                for _ in [:depth + 1] do arg ← mkAppM c #[arg]
              -- Apply one binder at a time; any remaining binders stay quantified
              -- in the new fact and may be instantiated by a later search step.
              let proof := mkApp (mkFVar d.fvarId) arg
              check proof
              let conclusion ← instantiateMVars (← inferType proof)
              for h in (← getLCtx) do
                if h.type == conclusion then throwError "duplicate forward fact"
              let (_, goal) ← g.note (← mkFreshUserName `derived) proof
              setGoals [goal] }
  return out

/-- Offer functional induction and case analysis for calls in the conjecture. -/
private def followRecursion (g : MVarId) (rules : Array (TSyntax `term)) : TacticM (Array Move) := do
  let mut out : Array Move := #[]
  for (call, summary) in ← Recursion.calls g rules do
    out := out ++ (← ((Critics.functionalInduction call summary).propose g).collect)
    -- Cases retain the current assumptions; there is no motive to strengthen.
    out := out.push {
      cost := 1, subject := some call, label := "function cases", run := g.withContext do
        let (_, goal) ← g.revert #[]
        setGoals [goal]
        let t ← goal.withContext <| Term.exprToSyntax call
        evalTactic (← `(tactic| fun_cases $t)) }
  return out

/-- Induct on data or evidence, varying the motive; also retain ordinary data cases. -/
private def inductOrAnalyzeData (g : MVarId) : TacticM (Array Move) := do
  let mut out : Array Move := #[]
  let lctx ← getLCtx
  let calls ← contextApplications g
  let exposed ← Critics.constructorObstructions calls
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← whnf d.type
    let .const n _ := ty.getAppFn | continue
    let some (.inductInfo info) := (← getEnv).find? n | continue
    if info.isRec || (← customElim? d.fvarId true).isSome then
      let covered := calls.filter fun call => call.isApp && call.containsFVar d.fvarId
      let mut changingArguments := #[]
      for call in covered do
        for i in [:call.getAppArgs.size] do
          if call.getAppArgs[i]!.containsFVar d.fvarId &&
              !changingArguments.contains i then
            changingArguments := changingArguments.push i
      let summary : InductionSummary := {
        coveredCalls := covered.size,
        changingArguments,
        expectedCases := info.ctors.length }
      out := out ++ (← ((Critics.inductionMotives d.fvarId summary).propose g).collect)
    -- Noninductive case analysis is another alternative, useful for tests and
    -- discriminants where induction would introduce irrelevant hypotheses.
    if !(← isProp d.type) then
      let cases ← caseAlternatives g d.fvarId ty info.isRec s!"cases {d.userName}"
      out := out ++ (← ((Critics.exposeConstructors exposed d.fvarId cases).propose g).collect)
  return out

/-- Generating one group never requires enumerating a later group. Values captured
by its moves belong to this input snapshot, exactly as for eager enumeration. -/
public def movesFor (g : MVarId) (rules : Array (TSyntax `term)) (strength remaining : Nat)
    (group : Group) : TacticM (Array Move) := do
  let moves ← match group with
  | .close => closeGoal rules strength
  | .basic => g.withContext do
      let preparation ← prepareGoal g rules strength
      return (← (Critics.indexedFocus.propose g).collect) ++
        preparation.filter (·.preparation != .targetSplit) ++
        (← ((Critics.transparentRules rules).propose g).collect) ++
        (← ((Critics.recursiveEquality rules).propose g).collect) ++
        (← ((Critics.sharedResults rules (strength > 1)).propose g).collect) ++
        preparation.filter (·.preparation == .targetSplit)
  | .hypotheses => g.withContext <| analyzeHypotheses g
  | .rules => g.withContext <| applyRules g rules remaining
  | .library => g.withContext <| applyLibraryTheorems g remaining
  | .forward => g.withContext do
      let repairs ← if strength > 1 then Critics.conditionalFacts.propose g |>.collect else pure #[]
      return repairs ++ (← instantiateHypotheses g strength)
  | .functions => g.withContext do
      let ordinary ← followRecursion g rules
      let repairs ← if strength > 1 then
        (Critics.inductionContinuations rules).propose g |>.collect else pure #[]
      return ordinary ++ repairs
  | .induction => g.withContext <| inductOrAnalyzeData g
  return moves.map fun move => { move with checkLocalChange := true }

public def prepareRules (g : MVarId) (rules : Array (TSyntax `term)) : TacticM (Array (TSyntax `term)) := do
  return rules ++ terms (← goalDefinitions g)

/-- Compatibility interface for callers inspecting all structural moves. -/
public def operations (g : MVarId) (rules : Array (TSyntax `term)) (strength : Nat := 1)
    (maxCost : Nat := 2) : TacticM (Array Move) :=
  structuralGroups.flatMapM fun group => do
    (← movesFor g rules strength maxCost group).filterM Move.applicable

end waterfall
