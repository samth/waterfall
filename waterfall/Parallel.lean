module
public import waterfall.Core
public import Std.Sync.Mutex

meta section

/-!
Parallel execution of one policy's existing depth/strength schedule. Round i
belongs to worker i % cpus: trials are neither duplicated nor pruned. Each worker
runs the ordinary sequential engine with its own proof state and counters.

The first observed complete proof wins. Finite-budget results and retained plans
can therefore differ from sequential execution. Increasing effort and heartbeats
retains eventual availability of every trial in a fair underlying schedule.
-/

open Lean Meta Elab Tactic
namespace waterfall.Parallel

private structure Result where
  value : Except Exception Stats
  saved : Tactic.SavedState

/-- One worker owns its cost cell. The parent reads it only after joining, even
when the task exits with an interrupt instead of returning a proof result. -/
private structure Worker where
  task : Task (Except Exception Result)
  heartbeats : IO.Ref Nat

/-- Fork all elaboration state, splitting fresh names through Lean's own async
boundary. Incremental tactic snapshots contain promises and must not be shared.
Only the returned whole checkpoint can later be adopted by the parent. -/
private def fork (cancel : IO.CancelToken) (cap : Nat) (body : TacticM Stats) :
    TacticM Worker := do
  let heartbeats ← IO.mkRef 0
  let tc ← read
  let ts ← get
  let ec := { (← readThe Term.Context) with tacSnap? := none }
  let es ← getThe Term.State
  let mc ← readThe Meta.Context
  let ms ← getThe Meta.State
  let worker : TacticM Result := do
    let start ← IO.getNumHeartbeats
    try
      let value ← tryCatchRuntimeEx (Except.ok <$> withTheReader Core.Context
        (fun c => { c with initHeartbeats := start, maxHeartbeats := cap }) body)
        (pure ∘ Except.error)
      return ⟨value, ← Tactic.saveState⟩
    finally
      -- tryCatchRuntimeEx deliberately rethrows interrupts. Measure independently
      -- of Result so cancellation cannot erase work that has already been spent.
      heartbeats.set ((← IO.getNumHeartbeats) - start)
  let core : CoreM Result := (((worker tc).run' ts ec).run' es mc).run' ms
  let action ← Core.wrapAsync (fun (_ : Unit) => core) (some cancel)
  -- A coordinator can itself run in Lean's task pool. Dedicated proof workers
  -- cannot be starved by coordinators occupying all of that pool's threads.
  return ⟨← EIO.asTask (action ()) Task.Priority.dedicated, heartbeats⟩

/-- Execute with at most `cpus` workers. `withHooks` supplies callbacks separately inside each
worker: allocate mutable recorders there, never share ordinary IO.Ref callbacks.
The supplied policy and schedule should otherwise be the same in every worker.

Effort is shared atomically. The enclosing remaining heartbeat allowance is
reserved equally, and every worker's actual usage is added to the parent counter,
including cancellation and failure. An unlimited parent remains unlimited.
Reservations are conservative: unused heartbeat shares are not redistributed.
Cancellation is cooperative; this function drains all workers before returning.
Workers have dedicated threads; operating-system affinity can limit CPU use. -/
public def run (cpus : Nat) (cfg : Config) (rules : Array (TSyntax `term) := #[])
    (withHooks : (Hooks → TacticM Stats) → TacticM Stats := fun use => use {}) : TacticM Stats := do
  if cpus == 0 then throwError "waterfall cpus must be positive"
  if cpus == 1 || cfg.effort == 0 then return ← withHooks (fun hooks => waterfall.run cfg rules hooks)
  let cpus := min cpus cfg.effort
  let saved ← Tactic.saveState
  let original ← getUnsolvedGoals
  let parent ← readThe Core.Context
  let start ← IO.getNumHeartbeats
  let cap := if parent.maxHeartbeats == 0 then 0
    else (parent.initHeartbeats + parent.maxHeartbeats - start) / cpus
  if parent.maxHeartbeats != 0 && cap == 0 then
    throwError "waterfall has insufficient ambient heartbeats for its workers"
  let ledger ← Std.Mutex.new ({} : Stats)
  let cancel ← IO.CancelToken.new
  let tasks ← IO.mkRef #[]
  let winner ← IO.mkRef (none : Option Result)
  -- Cleanup must also run if spawning or the waiting parent is interrupted.
  let result ← tryCatchRuntimeEx (do
    try
      for lane in [:cpus] do
        let task ← fork cancel cap <| withHooks fun inner => do
          let hooks : Hooks := { inner with
            trials := fun round => if round % cpus == lane then inner.trials round else #[]
            prelude := fun cfg goals => if lane == 0 then inner.prelude cfg goals else pure #[]
            postlude := fun cfg goals => if lane == 0 then inner.postlude cfg goals else pure #[]
            charge := do
              Core.checkInterrupted
              let admitted ← ledger.atomically do
                let s ← get
                if s.attempts >= cfg.effort then return false
                set { s with attempts := s.attempts + 1 }
                return true
              unless admitted do throwError "waterfall shared effort exhausted"
              inner.charge
            around := fun span outcome body => do
              Core.checkSystem "waterfall parallel"
              if span.phase == .node then
                ledger.atomically <| modify fun s => { s with nodes := s.nodes + 1 }
              inner.around span outcome body }
          let stats ← waterfall.run { cfg with report := false } rules hooks
          Core.checkSystem "waterfall worker result"
          return stats
        tasks.modify (·.push task)
      -- Wait on a dedicated monitor task. Blocking via IO.wait tells Lean's
      -- task pool that this elaborator is idle, so workers can also await queued
      -- elaboration/kernel tasks. Polling here would occupy that pool and deadlock.
      let pending := (← tasks.get).map (·.task)
      let monitor ← BaseIO.asTask (prio := Task.Priority.dedicated) do
        repeat
          if let some token := parent.cancelTk? then
            if ← token.isSet then return none
          let mut finished := 0
          for task in pending do
            if ← IO.hasFinished task then
              finished := finished + 1
              if let .ok r := task.get then
                if r.value.isOk then return some r
          if finished == pending.size then return none
          IO.sleep 1
        return none
      winner.set (← IO.wait monitor)
      pure (Except.ok ())
    finally
      cancel.set
      -- Join and charge every registered worker, regardless of its result.
      -- No cancellation/resource checks interrupt this cleanup. Restore the
      -- parent before either rethrowing an exception or adopting the winner.
      for worker in ← tasks.get do
        discard <| IO.wait worker.task
        IO.addHeartbeats (← worker.heartbeats.get)
      saved.restore true) (pure ∘ Except.error)
  let totals ← ledger.atomically get
  let spent := (← IO.getNumHeartbeats) - start
  tryCatchRuntimeEx (do
    if let .error ex := result then throw ex
    Core.checkSystem "waterfall parallel result"
    let some winning ← winner.get | throwError "waterfall parallel exhausted {totals.attempts} attempts"
    let .ok stats := winning.value | throwError "waterfall worker failed"
    winning.saved.restore true
    checkComplete original
    setGoals []
    let stats := { stats with attempts := totals.attempts, nodes := totals.nodes }
    if cfg.report then
      logInfo m!"PARALLEL success=true cpus={cpus} attempts={stats.attempts} nodes={stats.nodes} depth={stats.depth} rawHeartbeats={spent} strength={stats.strength} moves={stats.choices.toList}"
    return stats) fun ex => do
      saved.restore true
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
        if cfg.report then
          logInfo m!"PARALLEL success=false cpus={cpus} attempts={totals.attempts} nodes={totals.nodes} rawHeartbeats={spent}"
        throw ex

end waterfall.Parallel
