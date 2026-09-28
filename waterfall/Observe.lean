module
public import waterfall.Core
public import waterfall.Canonical

meta section

/-!
Opt-in experiment middleware and exact-plan replay. The proof engine neither
imports this module nor knows about files, clocks, cost records or stored plans.
All mutable observation state lives outside Lean's rollback snapshots.
-/

open Lean Meta Elab Tactic
namespace waterfall.Observe

public structure Cost where
  nanos : Nat := 0
  heartbeats : Nat := 0
  deriving Repr, Inhabited, ToJson, FromJson

private def clock : BaseIO Cost := do
  return ⟨(← IO.monoNanosNow), ← IO.getNumHeartbeats⟩

private def subtract (a b : Cost) : Cost :=
  ⟨a.nanos - b.nanos, a.heartbeats - b.heartbeats⟩

private def add (a b : Cost) : Cost :=
  ⟨a.nanos + b.nanos, a.heartbeats + b.heartbeats⟩

public structure Row where
  id : Nat
  parent : Option Nat
  span : Span
  outcome : Outcome
  exception : Bool
  inclusive : Cost
  exclusive : Cost
  deriving Repr, Inhabited, ToJson, FromJson

public structure Step where
  action : ActionId
  induction : InductionKind := .none
  inductionSummary : Option InductionSummary := none
  preparation : PreparationKind := .none
  closure : ClosureKind := .none
  label : String -- diagnostic only; fresh user names are deliberately not keys
  input : String
  strength : Nat
  remaining : Nat
  cost : Nat
  children : Nat
  focus : Nat := 0
  deriving Repr, Inhabited, ToJson, FromJson

public structure Plan where
  -- Version 3 records agenda selection; version 2 implicitly selects the head.
  version : Nat := 3
  /-- Caller-supplied immutable source/theory identity, e.g. a manifest digest.
  Kernel validation remains mandatory; this key protects experimental provenance. -/
  key : String
  rules : Array String
  input : String
  attemptHeartbeats : Nat
  steps : Array Step
  deriving Repr, Inhabited, ToJson, FromJson

public structure Report where
  success : Bool := false
  error : Option String := none
  rows : Array Row := #[]
  plan : Option Plan := none
  deriving Repr, Inhabited, ToJson, FromJson

/-- Limits are middleware, not another engine scheduler. A per-span cap can
only reduce the parent allowance. Deadlines are cooperative: checked between
spans, with hard process timeouts still owned by the benchmark executor. -/
public structure Control where
  slice : Span → TacticM (Option Nat) := fun _ => pure none
  deadlineNanos : Option Nat := none

public def Control.around (control : Control) (span : Span) (_ : α → Outcome)
    (body : TacticM α) : TacticM α := do
  if let some deadline := control.deadlineNanos then
    if (← IO.monoNanosNow) >= deadline then throwError "waterfall experiment deadline"
  let result ← if let some requested ← control.slice span then do
    let ctx ← readThe Core.Context
    let now ← IO.getNumHeartbeats
    let remaining := if ctx.maxHeartbeats == 0 then requested
      else ctx.initHeartbeats + ctx.maxHeartbeats - now
    let cap := min requested remaining
    if cap == 0 then throwError "waterfall experiment allowance exhausted"
    withTheReader Core.Context (fun c => { c with initHeartbeats := now, maxHeartbeats := cap }) body
  else body
  if let some deadline := control.deadlineNanos then
    if (← IO.monoNanosNow) >= deadline then throwError "waterfall experiment deadline"
  return result

public structure Recorder where
  rows : IO.Ref (Array Row)
  stack : IO.Ref (List (Nat × Cost))
  nextId : IO.Ref Nat
  accepted : IO.Ref (Array Step)
  costs : Bool := true
  plans : Bool := true

public def Recorder.create (costs := true) (plans := true) : BaseIO Recorder := do
  return ⟨← IO.mkRef #[], ← IO.mkRef [], ← IO.mkRef 0, ← IO.mkRef #[], costs, plans⟩

private def Recorder.around (recorder : Recorder) (span : Span) (outcome : α → Outcome)
    (body : TacticM α) : TacticM α := do
  if !recorder.costs then return ← body
  let id ← recorder.nextId.get
  recorder.nextId.modify (· + 1)
  let parent := (← recorder.stack.get).head?.map (·.1)
  recorder.stack.modify ((id, {}) :: ·)
  let start ← clock
  let finish (value : Outcome) (exception : Bool) : TacticM Unit := do
    let elapsed := subtract (← clock) start
    -- Finalization only updates IO records. It never executes proof operations
    -- with a renewed allowance, including after a runtime resource exception.
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
      let (frameId, children) :: rest ← recorder.stack.get | throwError "unbalanced cost spans"
      unless frameId == id do throwError "misnested cost spans"
      recorder.stack.set (match rest with
        | [] => []
        | (parentId, parentChildren) :: ps => (parentId, add parentChildren elapsed) :: ps)
      recorder.rows.modify (·.push {
        id, parent, span, outcome := value, exception,
        inclusive := elapsed, exclusive := subtract elapsed children })
  let result ← tryCatchRuntimeEx (Except.ok <$> body) fun ex => pure (.error ex)
  match result with
  | .ok value => finish (outcome value) false; return value
  | .error ex => finish {} true; throw ex

public def Recorder.hooks (recorder : Recorder) (control : Control := {}) (inner : Hooks := {}) : Hooks := { inner with
  around := fun span outcome body =>
    recorder.around span outcome (control.around span outcome (inner.around span outcome body))
  accepted := fun selection saved => do
    inner.accepted selection saved
    unless recorder.plans do return
    unless selection.replayable do
      throwError "waterfall plan capture unsupported for selected stateful extension: {selection.label}"
    let input ← withoutModifyingState do
      saved.restore true
      Canonical.snapshot selection.agenda
    recorder.accepted.modify (·.push {
      action := selection.action, induction := selection.induction, label := selection.label, input,
      inductionSummary := selection.inductionSummary,
      preparation := selection.preparation, closure := selection.closure,
      strength := selection.strength, remaining := selection.remaining,
      cost := selection.cost, children := selection.children, focus := selection.focus }) }

private def ruleKeys (rules : Array (TSyntax `term)) : Array String :=
  rules.map (fun r => r.raw.reprint.getD (toString r.raw))

/-- Capture a complete run, including failure. Callers deciding to use this as a
closing tactic must reject `success = false`; no error is converted to a proof. -/
public def capture (cfg : Config) (rules : Array (TSyntax `term)) (key : String)
    (costs := true) (plans := true) (control : Control := {}) (hooks : Hooks := {}) : TacticM Report := do
  let recorder ← Recorder.create costs plans
  let input ← if plans then Canonical.snapshot (← getUnsolvedGoals) else pure ""
  let error ← tryCatchRuntimeEx (do
    discard <| waterfall.run cfg rules (recorder.hooks control hooks)
    pure none) fun ex => withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
      return some (← ex.toMessageData.toString)
  -- Assemble data after a failed run without renewing any proof computation.
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
    let steps ← recorder.accepted.get
    let plan := if error.isNone && plans then some {
      key, rules := ruleKeys rules, input, attemptHeartbeats := cfg.attemptHeartbeats,
      steps := steps.reverse : Plan } else none
    return { success := error.isNone, error, plan, rows := ← recorder.rows.get }


/-- Execute only the recorded moves, preserving the conjunctive agenda and
original strengths. No alternative is tried if a guard or selected move fails.
Every failure restores the caller's entire proof/elaborator snapshot. -/
public def replay (plan : Plan) (rules : Array (TSyntax `term)) (key : String)
    (hooks : Hooks := {}) : TacticM Unit := do
  let saved ← Tactic.saveState
  let roots ← getUnsolvedGoals
  tryCatchRuntimeEx (do
    unless (plan.version == 2 || plan.version == 3) && plan.key == key && plan.rules == ruleKeys rules do
      throwError "waterfall plan source/theory mismatch"
    unless (← Canonical.snapshot roots) == plan.input do throwError "waterfall plan root mismatch"
    let stats ← IO.mkRef ({} : Stats)
    let mut agenda := roots
    for step in plan.steps do
      -- Search skips assigned heads, but retains assigned later siblings until
      -- their turn. Preserve that exact agenda for the structural input guard.
      while !agenda.isEmpty do
        if !(← agenda.head!.isAssigned) then break
        agenda := agenda.tail!
      if plan.version == 2 && step.focus != 0 then throwError "waterfall legacy plan has non-head focus"
      let some g := agenda[step.focus]? | throwError "waterfall plan has extra steps or invalid focus"
      let rest := agenda.eraseIdx step.focus
      unless (← Canonical.snapshot agenda) == step.input do throwError "waterfall plan input mismatch"
      setGoals [g]
      let inputState ← Tactic.saveState
      let localRules ← prepareRules g rules
      let span : Span := {
        phase := .enumerate, depth := step.remaining,
        strength := step.strength, group := some step.action.group }
      let moves ← hooks.array span do
        let original ← movesFor g localRules step.strength step.remaining step.action.group hooks.leafLemmas
        return original ++ (← hooks.extraMoves g localRules step.strength step.remaining step.action.group)
      let some move := moves[step.action.index]? | throwError "waterfall plan action unavailable"
      unless move.replayable do throwError "waterfall plan replay unsupported for stateful extension"
      -- Cost sees the same node snapshot/span as search, not generation state.
      let cost ← withoutModifyingState do
        inputState.restore true
        g.withContext <| hooks.cost g
          { phase := .node, depth := step.remaining, strength := step.strength }
          { action := step.action, move }
      unless step.induction == move.induction &&
          step.inductionSummary == move.inductionSummary &&
          step.preparation == move.preparation &&
          step.closure == move.closure && step.cost == cost &&
          (step.action.group == .close || step.cost >= max 1 move.cost) &&
          step.cost <= step.remaining && step.strength > 0 do
        throwError "waterfall plan cost mismatch"
      if move.check.isSome then
        unless ← hooks.bool { span with action := some step.action, label := "applicability" }
            move.applicable do throwError "waterfall plan applicability failed"
      inputState.restore true
      stats.modify fun s => { s with strength := step.strength }
      unless ← hooks.bool { span with
          phase := .action, action := some step.action, induction := move.induction,
          closure := move.closure, label := move.label }
          (attempt { effort := plan.steps.size, attemptHeartbeats := plan.attemptHeartbeats } stats move hooks.charge) do
        throwError "waterfall plan action failed"
      let children ← getUnsolvedGoals
      unless children.length == step.children do throwError "waterfall plan child-count mismatch"
      if step.action.group == .close && !children.isEmpty then throwError "waterfall plan closer left goals"
      agenda := children ++ rest
    for g in agenda do
      unless ← g.isAssigned do throwError "waterfall plan left an obligation"
    checkComplete roots
    setGoals []) fun ex => do
      saved.restore true
      throw ex

end waterfall.Observe
