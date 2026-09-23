module
public import waterfall.Protocol

meta section

/-! Metered execution of one deferred proof operation. -/

open Lean Meta Elab Tactic
namespace waterfall

initialize registerTraceClass `waterfall.search

/-- Applicability probes never commit assignments. -/
public def Move.applicable (move : Move) : TacticM Bool :=
  match move.check with
  | none => pure true
  | some probe => withoutModifyingState probe

/-- Run one move with a strength-scaled heartbeat slice. Runtime resource
failure rejects the alternative; all proof-state rollback remains with the
search engine that owns the move's input checkpoint. -/
public def attempt (cfg : Config) (stats : IO.Ref Stats) (m : Move)
    (charge : TacticM Unit := pure ()) : TacticM Bool := do
  let s ← stats.get
  if s.attempts >= cfg.effort then return false
  charge
  stats.modify fun s => { s with attempts := s.attempts + 1 }
  let ctx ← readThe Core.Context
  let now ← IO.getNumHeartbeats
  let allowance := cfg.attemptHeartbeats * s.strength / max 1 m.heartbeatDivisor
  let remaining := if ctx.maxHeartbeats == 0 then allowance
    else ctx.initHeartbeats + ctx.maxHeartbeats - now
  let cap := min remaining allowance
  if cap == 0 then return false
  tryCatchRuntimeEx (do
    withTheReader Core.Context (fun c => { c with initHeartbeats := now, maxHeartbeats := cap }) do
      Term.withoutErrToSorry <| withoutRecover m.run
    trace[waterfall.search] "{m.label}: goals={(← getUnsolvedGoals).length}"
    return decide ((← IO.getNumHeartbeats) - now <= cap)) fun ex => do
    trace[waterfall.search] "{m.label}: {ex.toMessageData}"
    return false

/-- Validate every original root, including hidden shared witnesses. -/
public def checkComplete (original : List MVarId) : TacticM Unit := do
  for g in original do
    unless ← g.isAssigned do throwError "waterfall left an unassigned root"
    let proof ← instantiateMVars (mkMVar g)
    if proof.hasMVar || proof.hasSorry then throwError "waterfall produced an incomplete proof"

end waterfall
