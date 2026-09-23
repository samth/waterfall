import waterfall.Operations
import waterfall

open Lean Meta Elab Tactic

inductive EmptyChain : Nat → Prop where
  | step : EmptyChain n → EmptyChain (n + 1)

-- Exercise the actual generated closer, with rollback after the shallow miss.
-- The stronger invocation must recover recursive inversion beyond one layer.
example (h : EmptyChain 5) : (0 : Nat) = 1 := by
  run_tac do
    let goal ← getMainGoal
    let saved ← Tactic.saveState
    let shallow ← waterfall.movesFor goal #[] 1 0 .close
    let some shallowMove := shallow[0]? | throwError "missing shallow closer"
    let closed ← try
      shallowMove.run
      pure true
    catch _ => pure false
    saved.restore true
    if closed then throwError "expected fuel-one contradiction to stop before closing"
    let strong ← waterfall.movesFor goal #[] 16 0 .close
    let some strongMove := strong[0]? | throwError "missing strong closer"
    strongMove.run

-- Suggestions must still replay and elaborate independently.
example (h : EmptyChain 0) : False := by waterfall?

-- Direct refutations keep the ordinary inversion allowance immediately.
example (h : EmptyChain 5) : False := by waterfall (effort := 1)
