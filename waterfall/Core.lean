module
public import waterfall.Operations

meta section

/-!
The proof-search driver. Proof operations and induction analysis live in
`Operations`; this module owns proposal enumeration, rollback, traversal,
resource accounting, trial scheduling and final validation.
-/

open Lean Meta Elab Tactic
namespace waterfall

/-- Reject no-op normalization without a global memo. Including local types
matters: a useful rewrite can change only a hypothesis. Fvar identity is safe
here because this conjecture shape is compared only across a single local operation.
-/
private def conjectureShape (g : MVarId) : MetaM (List Expr) := g.withContext do
  let mut es := [(← instantiateMVars (← g.getType))]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then es := (← instantiateMVars d.type) :: es
  return es

/-- Analyze the focused node once before one or more candidate families are
enumerated. The result contains no executed tactic or changed proof state. -/
public def prepareProposals (cfg : Config) (stats : IO.Ref Stats)
    (rules : Array (TSyntax `term)) (node : Node σ) (focus : Nat) :
    TacticM (Option (Prepared σ)) := do
  -- Exhaustion blocks new transitions, not selection of already-funded nodes.
  -- Return before preparation, generators or applicability probes do any work.
  if (← stats.get).attempts >= cfg.effort then return none
  let some job := node.jobs[focus]? | return none
  node.saved.restore true
  if ← job.goal.isAssigned then return none
  setGoals [job.goal]
  return some {
    source := node, focus,
    inputShape := ← conjectureShape job.goal,
    rules := ← prepareRules job.goal rules }

/-- Enumerate ordered operations from shared node analysis without executing
them. Each proposal retains the compatible checkpoint for a delayed frontier. -/
public def proposePrepared (cfg : Config) (stats : IO.Ref Stats) (hooks : Hooks)
    (prepared : Prepared σ) (requested : Array (Array Group))
    (admit : Candidate → Bool) : Choices (Proposal σ) := fun visit => do
  if (← stats.get).attempts >= cfg.effort then return false
  let node := prepared.source
  let some job := node.jobs[prepared.focus]? | return false
  node.saved.restore true
  if ← job.goal.isAssigned then return false
  let strength := (← stats.get).strength
  let span : Span := { phase := .node, depth := job.remaining, strength }
  setGoals [job.goal]
  let saved ← Tactic.saveState
  let probe (candidate : Candidate) : TacticM Bool := do
    if candidate.move.check.isNone then return true
    hooks.bool { span with
      phase := .enumerate, group := some candidate.action.group,
      action := some candidate.action, label := "applicability" } candidate.move.applicable
  let generate (group : Group) := hooks.array { span with phase := .enumerate, group := some group } do
    let original ← movesFor job.goal prepared.rules strength job.remaining group
    let extra ← hooks.extraMoves job.goal prepared.rules strength job.remaining group
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
        let proposal : Proposal σ := {
          source := node
          focus := prepared.focus
          candidate := candidate
          cost := cost
          inputShape := prepared.inputShape }
        if ← visit proposal then return true
  saved.restore true
  return false

/-- Analyze and enumerate in one call. Policies scheduling several finite
families should reuse `prepareProposals` with `proposePrepared`. -/
public def propose (cfg : Config) (stats : IO.Ref Stats) (hooks : Hooks)
    (rules : Array (TSyntax `term)) (node : Node σ) (focus : Nat)
    (requested : Array (Array Group)) (admit : Candidate → Bool) : Choices (Proposal σ) :=
  fun visit => do
    let some prepared ← prepareProposals cfg stats rules node focus | return false
    proposePrepared cfg stats hooks prepared requested admit visit

/-- Execute one retained proposal and yield its successful successor. -/
public def executeProposal (cfg : Config) (stats : IO.Ref Stats) (hooks : Hooks)
    (proposal : Proposal σ) : Choices (Node σ) := fun visit => do
  if (← stats.get).attempts >= cfg.effort then return false
  let node := proposal.source
  let some job := node.jobs[proposal.focus]? | return false
  node.saved.restore true
  if ← job.goal.isAssigned then return false
  setGoals [job.goal]
  let saved ← Tactic.saveState
  let strength := (← stats.get).strength
  let candidate := proposal.candidate
  let m := candidate.move
  let action := candidate.action
  let closing := action.group == .close
  let span : Span := {
    phase := .action, depth := job.remaining, strength,
    group := some action.group, action := some action,
    induction := m.induction, closure := m.closure, label := m.label }
  if ← hooks.bool span (attempt cfg stats m hooks.charge) then
    let children ← getUnsolvedGoals
    if closing && !children.isEmpty then saved.restore true; return false
    -- Local shape is only an opt-in pruning heuristic. A provider can advance
    -- another obligation or hidden witness without changing this goal.
    if let [child] := children then
      if m.checkLocalChange && (← conjectureShape child) == proposal.inputShape then
        saved.restore true
        return false
    let next := children.map fun g => { job with
      goal := g, remaining := job.remaining - proposal.cost,
      ancestors := candidate :: job.ancestors }
    let selected : Selection := {
      replayable := m.replayable, action, induction := m.induction,
      inductionSummary := m.inductionSummary,
      preparation := m.preparation, closure := m.closure,
      label := m.label, role := m.role,
      strength, remaining := job.remaining, cost := proposal.cost,
      children := children.length, agenda := node.jobs.map (·.goal),
      focus := proposal.focus, motive := m.motive }
    let successor : Node σ := { node with
      saved := ← Tactic.saveState,
      jobs := next ++ node.jobs.eraseIdx proposal.focus,
      plan := (selected, saved) :: node.plan }
    if ← visit successor then return true
  saved.restore true
  return false

/-- Expand one selected goal. This compatibility operation executes proposals
lazily in their generated order. -/
public def expand (cfg : Config) (stats : IO.Ref Stats) (hooks : Hooks)
    (rules : Array (TSyntax `term)) (node : Node σ) (focus : Nat)
    (requested : Array (Array Group)) (admit : Candidate → Bool) : Choices (Node σ) :=
  fun visit => propose cfg stats hooks rules node focus requested admit fun proposal =>
    executeProposal cfg stats hooks proposal visit

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
      prepare := prepareProposals cfg stats rules,
      propose := proposePrepared cfg stats hooks,
      execute := executeProposal cfg stats hooks,
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
    let proveAtDepthAndStrength (trialCfg : Config) (origin : TrialOrigin)
        (depth strength : Nat) (heartbeatBudget? : Option Nat := none)
        (trialTag : Name := .anonymous) : TacticM Bool := do
      saved.restore true
      stats.modify fun s => { s with depth, strength }
      let root : Node hooks.policy.State := {
        saved, jobs := original.map (Job.mk · depth []),
        state := hooks.policy.initial, origin, trialTag }
      let win ← IO.mkRef []
      let search := hooks.bool { phase := .trial, depth, strength }
        (proveAll trialCfg stats hooks rules root root win)
      let ok ← match heartbeatBudget? with
        | none => search
        | some requested => do
          let ctx ← readThe Core.Context
          let now ← IO.getNumHeartbeats
          let cap := if ctx.maxHeartbeats == 0 then requested
            else min requested (ctx.initHeartbeats + ctx.maxHeartbeats - now)
          if cap == 0 then pure false else
            tryCatchRuntimeEx (do
              let ok ← withTheReader Core.Context
                (fun c => { c with initHeartbeats := now, maxHeartbeats := cap }) search
              return ok && (← IO.getNumHeartbeats) - now <= cap) fun ex => do
                if ex.isInterrupt || !ex.isRuntime then throw ex
                return false
      if ok then
        for (selection, snapshot) in ← win.get do
          hooks.accepted selection snapshot
          stats.modify fun s => { s with choices := s.choices.push selection.label }
      return ok
    let mut success := false
    -- Prelude work is deliberately bounded twice: by its own request and by a
    -- quarter of the remaining effort. Each failed speculative trial therefore
    -- leaves most of its starting allowance for the rest of the schedule.
    for trial in ← hooks.prelude cfg original do
      if success || (← stats.get).attempts >= cfg.effort then break
      unless trial.strength > 0 do throwError "waterfall prelude strength must be positive"
      let spent := (← stats.get).attempts
      let allowance := min trial.attempts ((cfg.effort - spent) / 4)
      if allowance == 0 then continue
      let trialCfg := { cfg with effort := min cfg.effort (spent + allowance) }
      -- Speculation receives the same share of remaining heartbeats as of
      -- effort, with room for one ordinary action slice. Cap the entire trial,
      -- including proposal generation. Failed trial work remains charged globally.
      let ctx ← readThe Core.Context
      let now ← IO.getNumHeartbeats
      let remaining := ctx.initHeartbeats + ctx.maxHeartbeats - now
      let cap := if ctx.maxHeartbeats == 0 then cfg.attemptHeartbeats * allowance
        else min remaining (max cfg.attemptHeartbeats (remaining * allowance / cfg.effort))
      if cap == 0 then continue
      let ok ← proveAtDepthAndStrength trialCfg .prelude trial.depth trial.strength (some cap) trial.tag
      if ok then success := true
    -- One policy enumerates the entire run. Every trial spends the same global
    -- allowance; neither a new round nor a failed branch refunds earlier work.
    -- A fair policy visits every finite (depth, positive strength) pair as the
    -- effort bound grows. Policies are callbacks, not separate prover runs.
    for round in [:cfg.effort + 1] do
      if success || (← stats.get).attempts >= cfg.effort then break
      for (depth, strength) in hooks.trials round do
        if (← stats.get).attempts >= cfg.effort then break
        unless strength > 0 do throwError "waterfall trial strength must be positive"
        if ← proveAtDepthAndStrength cfg .fair depth strength then
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
