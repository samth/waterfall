module
public import waterfall.Protocol
meta section
register_option waterfall.experimentalEvidence : Bool := { defValue := false }
register_option waterfall.experimentalTiming : Bool := { defValue := true }
open Lean Meta Elab Tactic
namespace waterfall.ExperimentalOrder
public def evidenceFirst (base : Hooks) : Hooks := Id.run do
  return { base with order := fun g span cs => do
    let ids ← base.order g span cs
    let ordered := match ids with
      | none => cs
      | some ids => ids.filterMap fun id => cs.find? (·.action == id)
    let scored ← ordered.mapIdxM fun i c => do
      let mut preferred := false
      if c.move.induction == .evidence then
        if let some id := c.move.major then
          let .const n _ := (← whnf (← inferType (mkFVar id))).getAppFn | pure ()
          preferred := (← g.getType).getUsedConstants.contains n
      return (if preferred then 0 else 1, i, c.action)
    return some ((scored.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).map (·.2.2)) }


-- Experiment-only instrumentation. Ordering is off by default; timing is on
-- so ordinary corpus calls are measured without changing their proof scripts.
public def adapt {α : Type} (hooks : Hooks) (use : Hooks → TacticM α) : TacticM α := do
  let hooks := if waterfall.experimentalEvidence.get (← getOptions) then
    evidenceFirst hooks else hooks
  if !waterfall.experimentalTiming.get (← getOptions) then return ← use hooks
  let pos := (← getRef).getPos?.getD 0
  let line := (← getFileMap).toPosition pos |>.line
  use { hooks with around := fun span classify body => do
    if span.phase != .run then return ← hooks.around span classify body
    let start ← IO.monoNanosNow
    let hb ← IO.getNumHeartbeats
    let ok ← IO.mkRef false
    try
      let result ← hooks.around span classify body
      ok.set true
      return result
    finally
      IO.println s!"SEARCH_TIME line={line} ok={← ok.get} nanos={(← IO.monoNanosNow)-start} heartbeats={(← IO.getNumHeartbeats)-hb}" }
end waterfall.ExperimentalOrder
