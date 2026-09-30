import ProbeTiming
import waterfall.Observe
open Lean Meta Elab Tactic waterfall

-- Experiment-only adapter; the core engine and its policy are unchanged.
elab "penn_record " label:str mode:ident effort:num " [" rules:term,* "]" : tactic => do
  let mode : Mode := if mode.getId == `committed then .committed else .search
  let rs := rules.getElems
  let report ← Observe.capture { effort := effort.getNat, report := true } rs label.getString
    (hooks := mode.hooks rs)
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
    let directory := (← IO.getEnv "PENN_REPORT_DIR").getD "/tmp/penn-pr5-project"
    IO.FS.writeFile (directory ++ "/" ++ label.getString ++ ".json") (toJson report).compress
  unless report.success do throwError "recorded search failed: {report.error}"

-- Same primitives and complete backtracking, but deeper cheap contours are
-- interleaved with the ordinary diagonal trials. No alternatives are deleted.
elab "penn_deeper " effort:num " [" rules:term,* "]" : tactic => do
  let rs := rules.getElems
  let base := Mode.search.hooks rs
  let hooks := { base with trials := fun round =>
    #[(2 * (round + 1), 1)] ++ base.trials round }
  discard <| waterfall.run { effort := effort.getNat, report := true } rs hooks

elab "penn_candidates " limit:num : tactic => do
  let goals ← getUnsolvedGoals
  let names ← waterfall.Premises.select goals limit.getNat #[`LF]
  IO.println s!"PENN_CANDIDATES {names.toList}"

-- Compare retrieval with using exactly the same names as explicit hints.
elab "penn_retrieved " consumer:ident effort:num limit:num : tactic => do
  let names ← waterfall.Premises.select (← getUnsolvedGoals) limit.getNat #[`LF]
  IO.println s!"PENN_CANDIDATES {names.toList}"
  let rules := if consumer.getId == `rules then waterfall.Premises.rules names else #[]
  discard <| waterfall.run { effort := effort.getNat, report := true } rules
    (Mode.search.hooks rules names)

-- Diagnostic: include the immediate definitions of the goal vocabulary in
-- the retrieval query. The synthetic equality goals are never proved or kept.
elab "penn_expand " limit:num : tactic => do
  let names ← withoutModifyingState do
    let goals ← getUnsolvedGoals
    let mut extra := []
    let mut seen : Std.HashSet Name := {}
    for g in goals do
      let es ← g.withContext do
        let mut es := #[← g.getType]
        for d in ← getLCtx do
          unless d.isImplementationDetail do es := es.push d.type
        return es
      for e in es do
        for n in e.getUsedConstants do
          if seen.contains n then continue
          seen := seen.insert n
          let some (.defnInfo info) := (← getEnv).find? n | continue
          if isInstanceCore (← getEnv) n then continue
          let v := info.value
          let probe ← mkFreshExprMVar (← mkEq v v)
          extra := probe.mvarId! :: extra
    waterfall.Premises.select (goals ++ extra) limit.getNat #[`LF]
  IO.println s!"PENN_EXPANDED {names.toList}"
  discard <| waterfall.run { report := true } #[] (Mode.search.hooks #[] names)

-- Ordering experiment: prefer induction on evidence for a predicate that also
-- occurs in the target. Keep every original candidate and the base trial schedule.
elab "penn_evidence " effort:num " [" rules:term,* "]" : tactic => do
  let rs := rules.getElems
  let base := Mode.search.hooks rs
  let hooks := { base with order := fun g span cs => do
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
  discard <| waterfall.run { effort := effort.getNat, report := true } rs hooks

-- Execute a named existing preparation move; this adds no inference capability.
elab "penn_step " stage:ident " [" rules:term,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let rules ← prepareRules g rules.getElems
  let moves ← movesFor g rules 1 8 .basic
  let kind := if stage.getId == `normalize then PreparationKind.normalization else .targetSplit
  let some move := moves.find? (·.preparation == kind) | throwError "missing preparation"
  move.run

-- A stable permutation, reusing the earlier evidence-order experiment.
def evidenceFirst (base : Hooks) : Hooks := Id.run do
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

-- Dovetail three independent bounds. For every finite required depth, solver
-- strength and work allowance, some later round dominates all three. Retrying
-- only deeper contours with a fixed work cap would not provide that property.
def boundedContours (base : Hooks) (slice : Nat) : Hooks := { base with
  trials := fun round => Id.run do
    let mut trials := #[]
    for di in [:round + 1] do
      let d := round - di
      for s in [:round - d + 1] do
        trials := trials.push (2^d - 1, 2^s)
    return trials
  trialAllowance := fun round depth strength =>
    some (slice * 2^(round - (depth + 1).log2 - strength.log2)) }

elab "penn_search " evidence:num slice:num effort:num " [" rules:term,* "]" : tactic => do
  let rs := rules.getElems
  let mut hooks := Mode.search.hooks rs
  if evidence.getNat > 0 then hooks := evidenceFirst hooks
  if slice.getNat > 0 then hooks := boundedContours hooks slice.getNat
  discard <| waterfall.run { effort := effort.getNat, report := true } rs hooks

-- Conservative dovetail: every exact depth/strength pair is revisited with
-- unbounded allowances. This also covers custom generators that are not
-- monotone in these bounds, unlike the geometric contour variant above.
elab "penn_fair " evidence:num slice:num effort:num " [" rules:term,* "]" : tactic => do
  let rs := rules.getElems
  let mut hooks := Mode.search.hooks rs
  if evidence.getNat > 0 then hooks := evidenceFirst hooks
  hooks := { hooks with
    trials := fun round => Id.run do
      let mut trials := #[]
      for di in [:round + 1] do
        let d := round - di
        for s in [:round - d + 1] do
          trials := trials.push (d, s + 1)
      return trials
    trialAllowance := fun round depth strength =>
      some (slice.getNat * 2^(round - depth - (strength - 1))) }
  discard <| waterfall.run { effort := effort.getNat, report := true } rs hooks
