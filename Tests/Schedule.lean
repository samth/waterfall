import waterfall

open Lean Meta Elab Tactic waterfall

namespace LeafCompositionFixture

-- Check actual dispatch order and stable ActionIds, not merely array labels.
-- False has five closers at every strength; only their dispatch order changes.
elab "check_leaf_schedule" : tactic => withMainContext do
  let outer ← Tactic.saveState
  let conjunction ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``And) (mkConst ``True) (mkConst ``True))
  setGoals [conjunction.mvarId!]
  let moves ← movesFor conjunction.mvarId! #[] 1 0 .close
  let labels := moves.map (·.label)
  unless labels == #["assumption/rfl", "omega", "simp", "grind", "grind constructors",
      "close constructor And.intro"] do
    throwError "original constructors or cheap leaf order changed"
  let stronger ← movesFor conjunction.mvarId! #[] 2 0 .close
  unless stronger.map (·.label) == labels do
    throwError "stronger trial changed the original closer set"
  outer.restore true
  let root ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
  setGoals [root.mvarId!]
  let events ← IO.mkRef (#[] : Array (Nat × Nat))
  let hooks : Hooks := { trials := diagonalTrials 3, around := fun span _ body => do
    if let .action := span.phase then
      if let some action := span.action then
        if action.group == .close then
          events.modify (·.push (span.strength, action.index))
    body }
  let closed ← tryCatchRuntimeEx (do
    discard <| run { effort := 12, attemptHeartbeats := 2000000 } #[] hooks
    pure true) fun _ => pure false
  let observed ← events.get
  let assigned ← root.mvarId!.isAssigned
  outer.restore true
  if closed || assigned then throwError "failed search retained a proof of False"
  let first := (#[0, 1, 2, 3, 4] : Array Nat).map (1, ·)
  let second := (#[0, 1, 3, 2, 4] : Array Nat).map (2, ·)
  unless observed == first ++ second ++ #[(3, 0), (3, 1)] do
    throwError "unexpected leaf schedule or changed selectors: {repr observed}"

example : True := by
  check_leaf_schedule
  trivial

-- Successful existential siblings share a witness; false siblings must never
-- become an admitted or partially closed success after the reordered search.
example : ∃ n : Nat, n = 1 ∧ n ≠ 0 := by
  waterfall (effort := 400)

example : True := by
  fail_if_success
    have : ∃ n : Nat, n = 0 ∧ n = 1 := by
      waterfall (effort := 40)
  trivial

end LeafCompositionFixture
