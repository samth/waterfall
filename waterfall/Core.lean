module
public import waterfall.Protocol
public meta import Lean.Elab.Tactic.Induction
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
`expand` tries one step; `proveAll` owns its entire continuation; `run` increases
the available depth and solver strength until all original obligations close.
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

initialize registerTraceClass `waterfall.search

private def tacticMove (label : String) (stx : TSyntax `tactic) : Move :=
  { cost := 1, label := label, command? := some stx, run := evalTactic stx }

/-- Applicability never commits a probe's assignments or refunds its work. -/
public def Move.applicable (move : Move) : TacticM Bool :=
  match move.check with
  | none => pure true
  | some probe => withoutModifyingState probe

/-- Only definitions originating in the current module are unfolded implicitly.
Imported theories can supply their definitions and laws through the rule list.
Inspect async metadata first; never wait for the current theorem's proof body.
-/
private def goalDefinitions (g : MVarId) : MetaM (Array Name) := g.withContext do
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

private def terms (names : Array Name) : Array (TSyntax `term) :=
  names.map fun n => ⟨mkIdent n⟩

-- Forward instantiation draws arguments from terms already present in the goal
-- and hypotheses. Bound-variable fragments cannot be reused outside their binder.
-- The temporary refs below only collect this call's result; they cache no proofs.
private def contextTerms (g : MVarId) : MetaM (Array Expr) := g.withContext do
  let found ← IO.mkRef (#[] : Array Expr)
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let collect (e : Expr) := e.forEach fun t => do
    unless t.hasLooseBVars || (← seen.get).contains t do
      seen.modify (·.insert t)
      found.modify (·.push t)
  collect (← instantiateMVars (← g.getType))
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      collect (← instantiateMVars d.type)
      found.modify (·.push (mkFVar d.fvarId))
  return ← found.get

/-- Shared simplifier configuration. Closing requires `done`; normalization
leaves its changed obligations available to the continuation. -/
private def simplification (rules : Array (TSyntax `term)) (strength : Nat) : TacticM (TSyntax `tactic) := do
  let simpRules ← rules.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let steps := quote (Simp.defaultMaxSteps * strength)
  let discharge := quote (({} : Simp.Config).maxDischargeDepth * strength)
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
      Lean.Elab.Tactic.grind (← getMainGoal) grindConfig false rs none }
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
    tacticMove "assumption/rfl" (← `(tactic| first | assumption | rfl | contradiction)),
    tacticMove "omega" (← `(tactic| omega)),
    tacticMove "simp" (← `(tactic| ($simp:tactic; done))),
    grind false, grind true].map (fun m => { m with cost := 0 }) ++ constructors

-- Propose one constructor layer for an implicit data argument before unification.
-- Enumeration retains only binder positions and declaration names, never fresh
-- metavariables. Unification fills fields where possible; every unresolved field
-- remains an obligation. Nested witnesses blocked by reduction need more search
-- machinery than this fallback, which chooses only the outer constructor.
private def chooseImplicitWitnesses (g : MVarId) (ctor : Name) : TacticM (Array Move) := do
  let choices ← withoutModifyingState do
    forallTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels ctor)) fun xs _ => do
      let mut choices := #[]
      for i in [:xs.size] do
        let d ← getFVarLocalDecl xs[i]!
        if d.binderInfo.isExplicit || d.binderInfo.isInstImplicit || (← isProp d.type) then continue
        let .const n _ := (← whnf d.type).getAppFn | continue
        let some (.inductInfo info) := (← getEnv).find? n | continue
        for c in info.ctors do choices := choices.push (i, c)
      return choices
  return choices.map fun (i, witness) => {
    cost := 2, label := s!"constructor {ctor} witness {i} {witness}"
    run := g.withContext do
      let fn ← mkConstWithFreshMVarLevels ctor
      let (xs, _, _) ← forallMetaTelescopeReducing (← inferType fn)
      discard <| xs[i]!.mvarId!.apply (← mkConstWithFreshMVarLevels witness)
      setGoals (← g.apply (mkAppN fn xs)) }

private def customElim? (id : FVarId) (induction : Bool) : TacticM (Option Name) := do
  if tactic.customEliminators.get (← getOptions) then
    getCustomEliminator? #[mkFVar id] induction
  else pure none

-- A registered view may expose recursion hidden by a nonrecursive wrapper.
-- Keep raw cases as an alternative; only the registered path needs elaboration.
private def caseAlternatives (g : MVarId) (id : FVarId) (recursive : Bool)
    (label : String) : TacticM (Array Move) := do
  let recursive := recursive || (← customElim? id true).isSome
  let raw : Move := {
    cost := 1, major := some id, label := label
    role := if recursive then `inversion else `shape
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
  let mut out : Array Move := #[
    { cost := 1, role := `prepare, label := "intro", run := liftMetaTactic fun goal => do return [(← goal.intro `_).2] },
    { cost := 1, role := `prepare, label := "introduce binders", run := liftMetaTactic fun goal => do return [(← goal.intros).2] }]
  -- Expose a pointwise obligation to the outer search. A failed leaf solver
  -- cannot return its internal extensionality steps for later induction/cases.
  let target ← whnf (← g.getType)
  if let some (_, lhs, _) := target.eq? then
    if (← whnf (← inferType lhs)).isForall then
      out := out.push { cost := 1, role := `prepare, label := "function extensionality", run := do
        let [child] ← g.apply (← mkConstWithFreshMVarLevels ``funext)
          | throwError "not a function equality"
        setGoals [(← child.intros).2] }
  -- Normalization is also a structural alternative. Unlike the closing simp
  -- above, it may leave changed goals for further planning and be rolled back.
  out := out.push { (tacticMove "normalize" (← simplification rules strength)) with role := `prepare }
  out := out.push { cost := 1, label := "split target", run := liftMetaTactic fun goal => do
    let some children ← splitTarget? goal | throwError "no target split"
    return children }
  return out

/-- Split hypothesis expressions and invert inductive evidence. -/
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
          out := out ++ (← caseAlternatives g d.fvarId info.isRec "cases hypothesis")
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
        out := out.push { cost := 1, label := s!"constructor {ctor}", run := do
          setGoals (← g.apply (← mkConstWithFreshMVarLevels ctor)) }
      if maxCost >= 2 then
        for ctor in info.ctors do out := out ++ (← chooseImplicitWitnesses g ctor)
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
          let mut arg := t
          if let some c := wrapper then
            for _ in [:depth + 1] do arg ← mkAppM c #[arg]
          out := out.push {
            cost := 1, label := "forward hypothesis",
            major := some d.fvarId, subject := some arg,
            run := g.withContext do
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
    for casesOnly in [false, true] do
      out := out.push {
        cost := 1, subject := some call,
        induction := if casesOnly then .none else .functional,
        label := if casesOnly then "function cases" else "function induction", run := g.withContext do
          let mut others := #[]
          for d in (← getLCtx) do
            unless d.isImplementationDetail || call.containsFVar d.fvarId ||
                (← isProp d.type) || (← isType (mkFVar d.fvarId)) do
              others := others.push d.fvarId
          -- Cases need the current assumptions, not a generalized motive.
          let (_, goal) ← g.revert (if casesOnly then #[] else others)
          setGoals [goal]
          -- exprToSyntax can allocate elaborator holes: create them only here,
          -- after this alternative's snapshot has been restored.
          let t ← goal.withContext <| Term.exprToSyntax call
          evalTactic (← if casesOnly then `(tactic| fun_cases $t)
            else `(tactic| fun_induction $t)) }
  return out

/-- How to prepare the induction motive. Generalized variables are universally
quantified in the cases; abstracting fixed indices retains their equations. The
major premise and its induction kind belong to the enclosing proposed move. -/
private structure MotivePlan where
  generalize : Array FVarId := #[]
  abstractIndices : Bool := false

/-- Induct on data or evidence, varying the motive; also retain ordinary data cases. -/
private def inductOrAnalyzeData (g : MVarId) : TacticM (Array Move) := do
  let mut out : Array Move := #[]
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← whnf d.type
    let .const n _ := ty.getAppFn | continue
    let some (.inductInfo info) := (← getEnv).find? n | continue
    if info.isRec || (← customElim? d.fvarId true).isSome then
      let kind : InductionKind := if (← isProp d.type) then .evidence else .data
      -- Generalize data not occurring in the major premise's type. Lean's
      -- revert closes over dependencies and builds the quantified motive.
      let mut others : Array FVarId := #[]
      for other in lctx do
        if other.isImplementationDetail || other.fvarId == d.fvarId then continue
        if !(← isProp other.type) && !(← isType (mkFVar other.fvarId)) &&
            !d.type.containsFVar other.fvarId then
          others := others.push other.fvarId
      -- Ordinary Lean induction handles indexed relations as well as data.
      -- The lower-level MVarId.induction API alone does not perform all of its
      -- index preparation, so replacing this adapter needs equivalent handling.
      let inductWithMotive (motive : MotivePlan) : TacticM Unit := do
        let (reverted, goal) ← g.revert motive.generalize
        let mut goal := goal
        let mut major := mkFVar d.fvarId
        if motive.abstractIndices then
          -- Fixed indices must become variables before ordinary induction.
          -- Keep equations, so the motive and IH retain their original meaning.
          let mut args : Array GeneralizeArg := #[]
          for index in ty.getAppArgs[info.numParams:] do
            unless index.isFVar || args.any (·.expr == index) do
              args := args.push {expr := index, hName? := some (← mkFreshUserName `index_eq)}
          if args.isEmpty then throwError "no fixed induction indices"
          let (subst, _, prepared) ← goal.withContext <| goal.generalizeHyp args #[d.fvarId]
          goal := prepared
          major := subst.apply major
        setGoals [goal]
        let majorSyntax ← goal.withContext <| Term.exprToSyntax major
        evalTactic (← `(tactic| induction $majorSyntax:term))
        -- Revert closes over dependent hypotheses too. Reintroduce the full
        -- returned list, not merely the variables explicitly selected above.
        let children ← (← getUnsolvedGoals).mapM fun child => do
          return (← child.introNP reverted.size).2
        setGoals children
      if !others.isEmpty then
        out := out.push { cost := 1, induction := kind, major := some d.fvarId, label := s!"induction {d.userName} generalized", run := inductWithMotive {generalize := others}, motive := InductionMotive.localGeneralization }
      out := out.push { cost := 1, induction := kind, major := some d.fvarId, label := s!"induction {d.userName}", run := inductWithMotive {} }
      if ty.getAppArgs[info.numParams:].any (fun index => !index.isFVar) then
        out := out.push { cost := 1, induction := kind, major := some d.fvarId, label := s!"induction {d.userName} abstract indices", run := inductWithMotive {abstractIndices := true}, motive := InductionMotive.indexAbstraction }
        if !others.isEmpty then
          out := out.push { cost := 1, induction := kind, major := some d.fvarId, label := s!"induction {d.userName} generalized abstract indices", run := inductWithMotive {generalize := others, abstractIndices := true}, motive := InductionMotive.localGeneralizationAndIndexAbstraction }
    -- Noninductive case analysis is another alternative, useful for tests and
    -- discriminants where induction would introduce irrelevant hypotheses.
    if !(← isProp d.type) then
      out := out ++ (← caseAlternatives g d.fvarId info.isRec s!"cases {d.userName}")
  return out

/-- Generating one group never requires enumerating a later group. Values captured
by its moves belong to this input snapshot, exactly as for eager enumeration. -/
public def movesFor (g : MVarId) (rules : Array (TSyntax `term)) (strength remaining : Nat)
    (group : Group) : TacticM (Array Move) := do
  let moves ← match group with
  | .close => closeGoal rules strength
  | .basic => g.withContext <| prepareGoal g rules strength
  | .hypotheses => g.withContext <| analyzeHypotheses g
  | .rules => g.withContext <| applyRules g rules remaining
  | .library => g.withContext <| applyLibraryTheorems g remaining
  | .forward => g.withContext <| instantiateHypotheses g strength
  | .functions => g.withContext <| followRecursion g rules
  | .induction => g.withContext <| inductOrAnalyzeData g
  return moves.map fun move => { move with checkLocalChange := true }

public def prepareRules (g : MVarId) (rules : Array (TSyntax `term)) : TacticM (Array (TSyntax `term)) := do
  return rules ++ terms (← goalDefinitions g)

/-- Compatibility interface for callers inspecting all structural moves. -/
public def operations (g : MVarId) (rules : Array (TSyntax `term)) (strength : Nat := 1)
    (maxCost : Nat := 2) : TacticM (Array Move) :=
  structuralGroups.flatMapM fun group => do
    (← movesFor g rules strength maxCost group).filterM Move.applicable

/-- Reject no-op normalization without a global memo. Including local types
matters: a useful rewrite can change only a hypothesis. Fvar identity is safe
here because this conjecture shape is compared only across a single local operation.
-/
private def conjectureShape (g : MVarId) : MetaM (List Expr) := g.withContext do
  let mut es := [(← instantiateMVars (← g.getType))]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then es := (← instantiateMVars d.type) :: es
  return es

/-- An attempt has a strength-scaled heartbeat slice, capped by the ambient remaining
allowance. It cannot create a fresh budget after the parent is exhausted.
-/
public def attempt (cfg : Config) (stats : IO.Ref Stats) (m : Move)
    (charge : TacticM Unit := pure ()) : TacticM Bool := do
  let s ← stats.get
  if s.attempts >= cfg.effort then return false
  charge
  -- Count the attempt before running it, including failures and exhausted slices.
  -- Enumeration itself is charged to the ambient heartbeat budget, not this count.
  -- One Move is one attempt; its internal alternatives are not counted separately.
  stats.modify fun s => { s with attempts := s.attempts + 1 }
  let ctx ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  let allowance := cfg.attemptHeartbeats * s.strength
  let remaining := if ctx.maxHeartbeats == 0 then allowance
    else (ctx.initHeartbeats + ctx.maxHeartbeats - now)
  let cap := min remaining allowance
  if cap == 0 then return false
  tryCatchRuntimeEx (do
    -- Runtime resource exceptions are normal failed alternatives. Error-to-sorry
    -- recovery is disabled so a partial or admitted result cannot pass as success.
    withTheReader Core.Context (fun c => { c with initHeartbeats := now, maxHeartbeats := cap }) do
      Term.withoutErrToSorry <| withoutRecover m.run
    trace[waterfall.search] "{m.label}: goals={(← getUnsolvedGoals).length}"
    -- The final check also catches operations that return after overspending.
    return decide ((← IO.getNumHeartbeats) - now <= cap)) fun ex => do
    trace[waterfall.search] "{m.label}: {ex.toMessageData}"
    return false

/-- Expand one selected goal. The visitor sees a successful local transition,
not a completed proof. Failed visitors restore the same input before the next
proposal; costs and candidate ordinals are shared by every search policy. -/
public def expand (cfg : Config) (stats : IO.Ref Stats) (hooks : Hooks)
    (rules : Array (TSyntax `term)) (node : Node σ) (focus : Nat)
    (requested : Array (Array Group)) (admit : Candidate → Bool) : Choices (Node σ) := fun visit => do
  -- Exhaustion blocks new transitions, not selection of already-funded nodes.
  -- Return before preparation, generators or applicability probes do any work.
  if (← stats.get).attempts >= cfg.effort then return false
  let some job := node.jobs[focus]? | return false
  node.saved.restore true
  if ← job.goal.isAssigned then return false
  let strength := (← stats.get).strength
  let span : Span := { phase := .node, depth := job.remaining, strength }
  setGoals [job.goal]
  let saved ← Tactic.saveState
  let before ← conjectureShape job.goal
  let localRules ← prepareRules job.goal rules
  let probe (candidate : Candidate) : TacticM Bool := do
    if candidate.move.check.isNone then return true
    hooks.bool { span with
      phase := .enumerate, group := some candidate.action.group,
      action := some candidate.action, label := "applicability" } candidate.move.applicable
  let generate (group : Group) := hooks.array { span with phase := .enumerate, group := some group } do
    let original ← movesFor job.goal localRules strength job.remaining group
    let extra ← hooks.extraMoves job.goal localRules strength job.remaining group
    let candidates := (original ++ extra).mapIdx fun i m => Candidate.mk (ActionId.mk group i) m
    -- Assign selectors before filtering, so eager and deferred checks agree.
    if cfg.deferChecks then pure candidates else candidates.filterM probe
  let batch (groups : Array Group) : TacticM (Array Candidate) := do
    let mut candidates ← groups.flatMapM generate
    -- Preserve the cheap strength-one order. Stronger trials try grind before
    -- simp, retaining every action and assigning selectors before permutation.
    if strength > 1 && groups == #[Group.close] then
      candidates := candidates.swapIfInBounds 2 3
    -- Inspect the node input, then restore the state left by generation.
    let requested ← withoutModifyingState do
      saved.restore true
      job.goal.withContext <| hooks.order job.goal span candidates
    let some order := requested | return candidates
    unless order.size == candidates.size && candidates.all (fun c => order.contains c.action) do
      throwError "waterfall order must preserve every action exactly once"
    order.mapM fun id => do
      let some c := candidates.find? (·.action == id) | throwError "unknown action selector"
      return c
  let phases := if requested.isEmpty then #[#[#[Group.close]], hooks.batches]
    else #[requested]
  for groups in phases do
    -- A previous phase may have spent the last attempt. Eager enumeration must
    -- respect the same boundary as lazy enumeration before materializing a phase.
    if (← stats.get).attempts >= cfg.effort then break
    let closing := groups == #[#[Group.close]]
    if !closing && requested.isEmpty && job.remaining == 0 then continue
    saved.restore true
    let eager ← if cfg.lazy then pure #[] else groups.mapM batch
    for k in [:groups.size] do
      if (← stats.get).attempts >= cfg.effort then break
      saved.restore true
      let moves ← if cfg.lazy then batch groups[k]! else pure eager[k]!
      for candidate in moves do
        if (← stats.get).attempts >= cfg.effort then break
        if !admit candidate then continue
        saved.restore true
        let closing := candidate.action.group == .close
        let m := candidate.move
        -- Restore before consulting policy: a failed preceding action may have
        -- assigned this goal or changed its context. Policy mutations stay local.
        let cost ← withoutModifyingState (job.goal.withContext <| hooks.cost job.goal span candidate)
        if !closing && cost < max 1 m.cost then
          throwError "waterfall structural cost is below its intrinsic floor"
        if cost > job.remaining then continue
        if cfg.deferChecks && !(← probe candidate) then continue
        let action := candidate.action
        let step : Span := { span with
          phase := .action, group := some action.group, action := some action,
          induction := m.induction, label := m.label }
        if ← hooks.bool step (attempt cfg stats m hooks.charge) then
          let children ← getUnsolvedGoals
          if closing && !children.isEmpty then continue
          -- Local shape is only an opt-in pruning heuristic. A provider can
          -- advance another obligation or hidden witness without changing this
          -- goal; depth/cost accounting remains authoritative for those moves.
          if let [child] := children then
            if m.checkLocalChange && (← conjectureShape child) == before then continue
          let next := children.map fun g => { job with
            goal := g, remaining := job.remaining - cost, ancestors := candidate :: job.ancestors }
          let selected : Selection := {
            replayable := m.replayable, action, induction := m.induction,
            label := m.label, role := m.role,
            strength, remaining := job.remaining, cost, children := children.length,
            agenda := node.jobs.map (·.goal), focus, motive := m.motive }
          let successor : Node σ := { node with
            saved := ← Tactic.saveState,
            jobs := next ++ node.jobs.eraseIdx focus, plan := (selected, saved) :: node.plan }
          if ← visit successor then return true
  saved.restore true
  return false

/-- The traversal knows no tactic families or policy phases. Its expansion
interface can also feed an explicit frontier, beam, or best-first traversal.
Every checkpoint restores the whole compatible state; only a complete agenda
can become a winning plan. -/
private partial def proveAll (cfg : Config) (stats : IO.Ref Stats) (hooks : Hooks)
    (rules : Array (TSyntax `term)) (root : Node hooks.policy.State)
    (node : Node hooks.policy.State) (win : IO.Ref (List (Selection × Tactic.SavedState))) : TacticM Bool := do
  node.saved.restore true
  let mut jobs := node.jobs
  while !jobs.isEmpty do
    if !(← jobs.head!.goal.isAssigned) then break
    jobs := jobs.tail!
  let node := { node with jobs }
  if jobs.isEmpty then win.set node.plan; return true
  -- A frontier may still contain a complete proof when no new attempt is
  -- affordable. Let the policy drain those checkpoints; expand/restart enforce
  -- the work limit, while Lean's ambient limits still bound policy execution.
  let span : Span := { phase := .node, depth := jobs.head!.remaining, strength := (← stats.get).strength }
  hooks.bool span do
    stats.modify fun s => { s with nodes := s.nodes + 1 }
    let space : Space hooks.policy.State := {
      current := node, root,
      expand := expand cfg stats hooks rules node,
      restart := fun checkpoint state visit => do
        if (← stats.get).attempts >= cfg.effort then return false
        hooks.charge
        stats.modify fun s => { s with attempts := s.attempts + 1 }
        checkpoint.saved.restore true
        visit { checkpoint with state } }
    let ok ← hooks.policy.choose space fun next => do
      let step := next.plan.head?.map (·.1)
      hooks.bool { span with
        phase := .continuation,
        action := step.map (·.action), group := step.map (·.action.group),
        depth := step.map (·.remaining) |>.getD span.depth,
        induction := step.map (·.induction) |>.getD .none,
        label := step.map (·.label) |>.getD "restart checkpoint" }
        (proveAll cfg stats hooks rules root next win)
    unless ok do node.saved.restore true
    return ok

/-- Shared by search and the optional exact-plan interpreter. Empty displayed
goals alone are insufficient when a witness or another root remains unassigned. -/
public def checkComplete (original : List MVarId) : TacticM Unit := do
  for g in original do
    unless ← g.isAssigned do throwError "waterfall left an unassigned root"
    let proof ← instantiateMVars (mkMVar g)
    if proof.hasMVar || proof.hasSorry then throwError "waterfall produced an incomplete proof"

/-- Public proof interface. Under the default policy, additional effort extends
the same deterministic sequence without a top-k veto. Custom policies can prune.
The ambient Lean heartbeat and recursion limits remain authoritative.
-/
public def run (cfg : Config) (rules : Array (TSyntax `term) := #[])
    (hooks : Hooks := {}) : TacticM Stats := do
  let groups := hooks.batches.foldl (· ++ ·) #[]
  unless groups.size == structuralGroups.size && structuralGroups.all groups.contains do
    throwError "waterfall batches must contain every structural group exactly once"
  let saved ← Tactic.saveState
  let original ← getUnsolvedGoals
  let stats ← IO.mkRef ({} : Stats)
  let start ← IO.getNumHeartbeats
  tryCatchRuntimeEx (hooks.around { phase := .run } (fun _ => { success := some true }) do
    let proveAtDepthAndStrength (depth strength : Nat) : TacticM Bool := do
      saved.restore true
      stats.modify fun s => { s with depth, strength }
      let root : Node hooks.policy.State := {
        saved, jobs := original.map (Job.mk · depth []),
        state := hooks.policy.initial }
      let win ← IO.mkRef []
      let ok ← hooks.bool { phase := .trial, depth, strength } (proveAll cfg stats hooks rules root root win)
      if ok then
        for (selection, snapshot) in ← win.get do
          hooks.accepted selection snapshot
          stats.modify fun s => { s with choices := s.choices.push selection.label }
      return ok
    let mut success := false
    -- One policy enumerates the entire run. Every trial spends the same global
    -- allowance; neither a new round nor a failed branch refunds earlier work.
    -- A fair policy visits every finite (depth, positive strength) pair as the
    -- effort bound grows. Policies are callbacks, not separate prover runs.
    for round in [:cfg.effort + 1] do
      if success || (← stats.get).attempts >= cfg.effort then break
      for (depth, strength) in hooks.trials round do
        if (← stats.get).attempts >= cfg.effort then break
        unless strength > 0 do throwError "waterfall trial strength must be positive"
        if ← proveAtDepthAndStrength depth strength then
          success := true
          break
    let s ← stats.get
    let spent := (← IO.getNumHeartbeats) - start
    if cfg.report then
      logInfo m!"COMPACT success={success} attempts={s.attempts} nodes={s.nodes} depth={s.depth} rawHeartbeats={spent} strength={s.strength} moves={s.choices.toList}"
    unless success do throwError "waterfall exhausted {s.attempts} attempts at depth {s.depth}"
    -- Trust the original goals, not just an empty tactic goal list. Reject roots
    -- with unresolved metavariables or direct sorry terms. This is a final tactic
    -- check; Lean still elaborates and kernel-checks the enclosing declaration.
    checkComplete original
    setGoals []
    return s) fun ex => do
    saved.restore true
    -- Only error reporting runs without a heartbeat cap. Proof search never
    -- renews an exhausted parent budget. User interrupts still propagate.
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
      if cfg.report then
        let s ← stats.get
        logInfo m!"COMPACT success=false attempts={s.attempts} nodes={s.nodes} depth={s.depth} rawHeartbeats={(← IO.getNumHeartbeats) - start}"
      if ex.isRuntime then throwError "waterfall reached the ambient resource limit"
      throw ex

end waterfall
