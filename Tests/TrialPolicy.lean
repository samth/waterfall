import waterfall
import waterfall.Observe

open Lean Meta Elab Tactic waterfall waterfall.Observe
namespace SinglePolicyFixture

private def weightedHooks (rootPrefix : Nat) (weight : Group → Nat) : Hooks :=
  {
    trials := diagonalTrials rootPrefix
    cost := fun _ _ candidate => pure (candidate.move.cost * weight candidate.action.group) }

-- Check the policy itself over a finite rectangle, including no duplicates.
-- Actual dispatch below independently checks that the engine uses the callback.
example : True := by
  run_tac
    let flatten (rootTrials rounds : Nat) := (List.range rounds).toArray.foldl
      (fun out round => out ++ diagonalTrials rootTrials round) #[]
    unless flatten 3 4 == #[(0,1),(0,2),(0,3),(1,1),(2,1),(1,2),
        (3,1),(2,2),(1,3),(0,4)] do
      throwError "default trial prefix changed"
    unless flatten 1 3 == #[(0,1),(1,1),(0,2),(2,1),(1,2),(0,3)] do
      throwError "diagonal trial prefix changed"
    for rootTrials in [1, 3, 5] do
      let pairs := flatten rootTrials 13
      for depth in [:7] do
        for strength in [1:8] do
          unless (pairs.filter (· == (depth, strength))).size == 1 do
            throwError "trial policy omitted or repeated a finite pair"
  trivial

elab "check_trial_dispatch" : tactic => do
  let outer ← Tactic.saveState
  for rootTrials in [1, 3] do
    let root ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
    setGoals [root.mvarId!]
    let trials ← IO.mkRef (#[] : Array (Nat × Nat))
    let actions ← IO.mkRef 0
    let hooks : Hooks := {
      trials := diagonalTrials rootTrials
      around := fun span _ body => do
        if span.phase == .trial then trials.modify (·.push (span.depth, span.strength))
        if span.phase == .action then actions.modify (· + 1)
        body }
    let closed ← tryCatchRuntimeEx (do
      discard <| run {effort := 6, attemptHeartbeats := 2000000} #[] hooks
      pure true) fun _ => pure false
    unless !closed && !(← root.mvarId!.isAssigned) && (← actions.get) == 6 do
      throwError "trial fixture failed to exhaust its intended allowance"
    let expected := if rootTrials == 1 then #[(0,1),(1,1)] else #[(0,1),(0,2)]
    unless (← trials.get) == expected do throwError "engine ignored trial policy"
    outer.restore true

example : True := by check_trial_dispatch; trivial

-- The scheduled prelude scales with effort instead of stopping at 64 attempts.
-- A second trial receives a share of the remaining budget; tiny budgets skip
-- preludes altogether. Failed trials leave the ordinary fair search available.
elab "check_bounded_prelude" : tactic => do
  let outer ← Tactic.saveState
  for effort in [3, 40, 400] do
    let root ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
    setGoals [root.mvarId!]
    let current ← IO.mkRef 0
    let counts ← IO.mkRef (#[] : Array Nat)
    let hooks := Scheduling.hooks {
      prelude := fun cfg _ => pure #[{ depth := 1, attempts := cfg.effort }]
      extraMoves := fun _ _ _ _ group => do
        if group != .basic then return #[]
        return (List.range effort).toArray.map fun _ => {
          cost := 1, label := "failed prelude fixture", run := throwError "fixture" }
      around := fun span _ body => do
        if span.phase == .trial then
          current.set 0
          try
            return ← body
          finally counts.modify (·.push (← current.get))
        if span.phase == .action then current.modify (· + 1)
        body }
    let closed ← tryCatchRuntimeEx (do
      discard <| run { effort, attemptHeartbeats := 2000000 } #[] hooks
      pure true) fun _ => pure false
    let observed ← counts.get
    let first := effort / 4
    let second := (effort - first) / 4
    let expected := (#[first, second]).filter (· > 0)
    unless !closed && !(← root.mvarId!.isAssigned) &&
        observed.take expected.size == expected && observed.size > expected.size &&
        observed.foldl (· + ·) 0 == effort do
      throwError "prelude or subsequent fair-search allowance changed: {observed}"
    outer.restore true

example : True := by check_bounded_prelude; trivial

-- Intrinsic closer costs distinguish ordinary leaves from constructor leaves
-- without parsing diagnostic names or depending on action ordinals in a policy.
example : True := by
  run_tac
    let moves ← movesFor (← getMainGoal) #[] 1 0 .close
    unless (moves.take 5).all (·.cost == 0) &&
        (moves.extract 5 moves.size).all (·.cost == 1) && moves.size > 5 do
      throwError "closer cost metadata changed"
    let control := weightedHooks 3 (fun group => if group == .close then 0 else 1)
    let weighted := weightedHooks 1 (fun group => if group == .library then 2 else 1)
    for group in structuralGroups.push .close do
      let move : Move := {
        cost := if group == .library then 2 else 1
        label := "synthetic cost metadata", run := pure () }
      let candidate : Candidate := { action := {group, index := 0}, move }
      let g ← getMainGoal
      let span : Span := { phase := .node }
      unless (← control.cost g span candidate) == (if group == .close then 0 else move.cost) &&
          (← weighted.cost g span candidate) == (if group == .library then 4 else move.cost) do
        throwError "finite group weights changed another move's cost"
  trivial

-- No zero-depth closer can run under this test policy. At depth one, the two
-- reflexivity leaves consume exactly the last two permitted actions. Their
-- accepted callbacks, complete sibling agenda and cost-aware replay must survive.
elab "check_weighted_siblings" : tactic => do
  let root ← getMainGoal
  let sibling ← mkFreshExprSyntheticOpaqueMVar (← root.getType)
  setGoals [root, sibling.mvarId!]
  let saved ← Tactic.saveState
  let accepted ← IO.mkRef 0
  let hooks : Hooks := {
    cost := fun _ _ c => pure (if c.action.group == .close then c.move.cost + 1 else c.move.cost)
    accepted := fun _ _ => accepted.modify (· + 1) }
  let report ← capture {effort := 2} #[] "weighted-siblings" true true {} hooks
  let some plan := report.plan | throwError "weighted proof produced no plan: {report.error}"
  unless report.success && plan.steps.size == 2 && (← accepted.get) == 2 &&
      plan.steps.all (fun s => s.remaining == 1 && s.cost == 1 && s.children == 0) do
    throwError "weighted admission or final-action sibling acceptance changed"
  checkComplete [root, sibling.mvarId!]
  saved.restore true
  let before ← Canonical.snapshot (← getUnsolvedGoals)
  let rejected ← tryCatchRuntimeEx (do
    replay plan #[] "weighted-siblings"
    pure false) fun _ => pure true
  unless rejected && (← Canonical.snapshot (← getUnsolvedGoals)) == before do
    throwError "replay accepted a different cost policy or damaged its caller"
  let .ok roundtrip := fromJson? (α := Plan) (toJson plan)
    | throwError "weighted plan failed JSON round-trip"
  replay roundtrip #[] "weighted-siblings" hooks
  checkComplete [root, sibling.mvarId!]

example : (0 : Nat) = 0 := by check_weighted_siblings

def append : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

-- Give structural edges cost two and check actual child depths in the accepted
-- plan. Original operations, their strengths and the conjunctive continuation
-- remain intact; the interpreter must use the same weights.
elab "check_weighted_structure" : tactic => do
  let saved ← Tactic.saveState
  let hooks := weightedHooks 1 (fun group => if group == .close then 0 else 2)
  let report ← capture {effort := 4000} #[] "weighted-structure" false true {} hooks
  let some plan := report.plan | throwError "weighted structural proof failed: {report.error}"
  let some first := plan.steps[0]? | throwError "missing first structural step"
  let some child := plan.steps[1]? | throwError "missing structural child"
  unless first.action.group != .close && first.cost == 2 && first.children > 0 &&
      child.remaining + first.cost == first.remaining do
    throwError "structural path did not debit its effective cost"
  saved.restore true
  replay plan #[] "weighted-structure" hooks

example (xs : List Nat) : append xs [] = xs := by check_weighted_structure

-- A malformed trial cannot renew a primitive's strength or leave a partial
-- proof behind. Invalid zero strength is rejected before any proof operation.
example : True := by
  run_tac
    let before ← Canonical.snapshot (← getUnsolvedGoals)
    let error ← tryCatchRuntimeEx (do
      discard <| run {effort := 20} #[] {trials := fun _ => #[(0,0)]}
      pure none) fun ex => return some (← ex.toMessageData.toString)
    unless error == some "waterfall trial strength must be positive" &&
        (← Canonical.snapshot (← getUnsolvedGoals)) == before do
      throwError "invalid trial policy was accepted or damaged its caller"
  trivial

-- Invalid costs are rejected at the engine boundary, including a library-like
-- provider whose declared intrinsic floor is two. No attempted action or partial
-- assignment may escape either rejection. Ordinary alternatives remain present.
example : True := by
  run_tac
    let outer ← Tactic.saveState
    for libraryFloor in [false, true] do
      let root ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
      setGoals [root.mvarId!]
      let before ← Canonical.snapshot (← getUnsolvedGoals)
      let actions ← IO.mkRef 0
      let hooks : Hooks := {
        cost := fun _ _ c => pure <| if libraryFloor then
            (if c.action.group == .library then 1 else 100)
          else if c.action.group == .close then 100 else 0
        extraMoves := fun _ _ _ _ group => pure <|
          if libraryFloor && group == .library then
            #[{ cost := 2, label := "declared cost floor", run := pure () }]
          else #[]
        around := fun span _ body => do
          if span.phase == .action then actions.modify (· + 1)
          body }
      let error ← tryCatchRuntimeEx (do
        discard <| run {effort := 20} #[] hooks
        pure none) fun ex => return some (← ex.toMessageData.toString)
      unless error == some "waterfall structural cost is below its intrinsic floor" &&
          (← actions.get) == 0 && (← Canonical.snapshot (← getUnsolvedGoals)) == before do
        throwError "invalid structural cost was accepted or damaged its caller"
      outer.restore true
  trivial

end SinglePolicyFixture
