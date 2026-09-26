import waterfall
import waterfall.Observe
open Lean Meta Elab Tactic waterfall
namespace CoordinationTests
set_option maxHeartbeats 400000

-- Preserve a successful ordinary prefix, including its recorded choices.
example (xs : List Nat) : [] ++ xs = xs := by
  run_tac do
    let initial ← saveState
    let hooks := Mode.search.hooks #[]
    let reference ← run {} #[] {hooks with postlude := fun _ _ => pure #[]}
    initial.restore true
    let coordinated ← run {} #[] hooks
    unless reference.attempts == coordinated.attempts && reference.choices == coordinated.choices do
      throwError "changed an ordinary successful prefix"

-- Both phases share the same attempt ledger and ambient heartbeat deadline.
-- Failure restores the original agenda even after entering a final trial.
example : True := by
  run_tac do
    let outer ← saveState
    for effort in [0, 1, 3, 40] do
      let pending ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
      setGoals [pending.mvarId!]
      let before ← Canonical.snapshot (← getUnsolvedGoals)
      let deadline ← readThe Core.Context
      let final ← IO.mkRef false
      let counts ← IO.mkRef (0, 0)
      let hooks : Hooks := {
        postlude := fun _ _ => pure #[{tag := `budgetTest, depth := 1, attempts := 1000}]
        policy := ⟨Unit, (), fun space visit => do
          final.set (space.root.origin == .postlude)
          let ctx ← readThe Core.Context
          unless ctx.initHeartbeats + ctx.maxHeartbeats ≤ deadline.initHeartbeats + deadline.maxHeartbeats do
            throwError "renewed the ambient heartbeat allowance"
          space.expand 0 #[#[.close]] (fun c => c.move.role == `fixture) visit⟩
        charge := do
          if ← final.get then counts.modify fun (a,b) => (a,b+1)
          else counts.modify fun (a,b) => (a+1,b)
        extraMoves := fun _ _ _ _ group => do
          if group != .close then return #[]
          return (List.range 40).toArray.map fun _ => {
            role := `fixture, label := "failing budget fixture", run := throwError "expected failure" } }
      let ok ← tryCatchRuntimeEx (do discard <| run {effort} #[] hooks; pure true)
        (fun ex => if ex.isInterrupt then throw ex else pure false)
      unless !ok && (← counts.get) == (effort - effort / 4, effort / 4) do
        throwError "phase work escaped aggregate accounting: {← counts.get}"
      unless (← Canonical.snapshot (← getUnsolvedGoals)) == before do
        throwError "failed final trial did not restore its input"
      outer.restore true
  trivial

-- This fixture uses recursive structure, not names from any benchmark theory.
inductive Chain where
  | empty : Chain
  | link : Nat → Chain → Chain
@[simp, grind] def size : Chain → Nat
  | .empty => 0
  | .link _ xs => size xs + 1
@[simp, grind] def initialSegment : Chain → Chain → Prop
  | .empty, _ => True
  | .link _ _, .empty => False
  | .link a xs, .link b ys => a = b ∧ initialSegment xs ys

-- Force coordination, then replay the recorded plan without policy-local options.
-- Also independently elaborate the ordinary-command editor suggestion.
example (xs ys : Chain) : initialSegment xs ys ∧ size xs = size ys → xs = ys := by
  run_tac do
    let initial ← saveState
    let roots ← getUnsolvedGoals
    let base := Mode.search.hooks #[]
    let hooks := {base with prelude := fun _ _ => pure #[], trials := fun _ => #[]}
    let report ← Observe.capture {effort := 1000} #[] "coordination" true true {} hooks
    unless report.success do throwError "coordination failed: {report.error}"
    let some plan := report.plan | throwError "no coordinated plan"
    initial.restore true
    for _ in [:7] do discard <| mkFreshUserName `perturb
    Observe.replay (← ofExcept (fromJson? (toJson plan))) #[] "coordination" hooks
    checkComplete roots
    initial.restore true
    let path ← IO.mkRef (#[] : Suggestions.Path)
    discard <| run {effort := 1000} #[] {hooks with
      accepted := fun step state => path.modify (·.push (step,state))}
    let script ← Suggestions.compile initial roots (← path.get) #[] hooks
    if script.usedTerm then throwError "coordination suggestion lost ordinary commands"
    checkComplete roots

-- A solved head never licenses dropping a false sibling.
example : True := by
  run_tac do
    let initial ← saveState
    let a ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
    let b ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
    setGoals [a.mvarId!, b.mvarId!]
    let before ← Canonical.snapshot (← getUnsolvedGoals)
    let base := Mode.search.hooks #[]
    let ok ← tryCatchRuntimeEx (do
      discard <| run {effort := 40} #[] {base with
        postlude := fun _ _ => pure #[{tag := `coordinated, depth := 16, strength := 2, attempts := 256}]
        prelude := fun _ _ => pure #[], trials := fun _ => #[]}
      pure true) (fun ex => if ex.isInterrupt then throw ex else pure false)
    unless !ok && (← Canonical.snapshot (← getUnsolvedGoals)) == before do
      throwError "coordination lost a sibling or failed to roll back"
    initial.restore true
  trivial
end CoordinationTests
