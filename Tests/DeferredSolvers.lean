import waterfall
import waterfall.Observe
open Lean Meta Elab Tactic waterfall waterfall.Observe

-- A tiny alternative can fail without spending a whole ordinary slice. Its
-- later full-budget copy must still execute after restoring the checkpoint.
elab "check_move_budgets" : tactic => do
  let saved ← Tactic.saveState
  let stats ← IO.mkRef ({} : Stats)
  let move : Move := { label := "allocate then close", run := do
    for _ in [:1000] do discard <| mkFreshExprMVar (mkConst ``Nat)
    evalTactic (← `(tactic| trivial)) }
  let cheap ← attempt { effort := 10, attemptHeartbeats := 1000000 } stats
    { move with heartbeatDivisor := 1000000 }
  saved.restore true
  let full ← attempt { effort := 10, attemptHeartbeats := 1000000 } stats move
  unless !cheap && full && (← stats.get).attempts == 2 do
    throwError "incorrect bounded-attempt fallback/accounting"
example : True := by check_move_budgets

set_option waterfall.deferSolvers true
set_option waterfall.cheapSolverDivisor 64

elab "deferred_replay" : tactic => do
  let saved ← Tactic.saveState
  let hooks := Mode.search.hooks #[]
  let result ← capture {effort := 4000} #[] "deferred-fixture" true true {} hooks
  unless result.success do throwError "deferred search failed: {result.error}"
  let some plan := result.plan | throwError "missing deferred plan"
  let .ok plan := fromJson? (α := Plan) (toJson plan) | throwError "plan JSON failed"
  saved.restore true
  replay plan #[] "deferred-fixture" hooks

example (xs : List Nat) : xs ++ [] = xs := by deferred_replay
inductive Mark : Nat → Prop where | zero : Mark 0 | one : Mark 1
inductive Allowed : Nat → Prop where | one : Allowed 1
example : ∃ n, Mark n ∧ Allowed n := by deferred_replay

-- With cheap calls disabled, full inference still remains reachable.
set_option waterfall.cheapSolverDivisor 0 in
example (xs : List Nat) : xs ++ [] = xs := by deferred_replay

-- Incomplete siblings cannot be accepted even with bounded solver alternatives.
example : True := by
  run_tac
    let saved ← Tactic.saveState
    let root ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
    setGoals [root.mvarId!]
    let result ← capture {effort := 30} #[] "deferred-false" false true {} (Mode.search.hooks #[])
    let assigned ← root.mvarId!.isAssigned
    saved.restore true
    unless !result.success && result.plan.isNone && !assigned do
      throwError "incomplete proof accepted"
  trivial
