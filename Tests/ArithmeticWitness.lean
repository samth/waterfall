import waterfall
import waterfall.ArithmeticWitness
import waterfall.Observe

open Lean Meta Elab Tactic waterfall

namespace ArithmeticWitnessTests

private meta def witnessHooks (mode : Mode := .search) : Hooks :=
  Critic.hooks #[Critics.arithmeticWitness] mode.hooks

-- Every successful example below must actually use the provider. Check both
-- machine replay and the printed ordinary Lean script at a fresh checkpoint.
elab "witness_search" committed:(" committed")? : tactic => do
  let hooks := witnessHooks (if committed.isSome then .committed else .search)
  let saved ← saveState
  let roots ← getUnsolvedGoals
  let report ← Observe.capture {effort := 1000} #[] "arithmetic-witness" true true {} hooks
  unless report.success do throwError "{report.error}"
  let some plan := report.plan | throwError "missing plan"
  unless plan.steps.any (·.label == "arithmetic existential witness") do
    throwError "proof did not use the critic"
  saved.restore true
  let roundtrip ← ofExcept (fromJson? (toJson plan) : Except String Observe.Plan)
  for _ in [:9] do discard <| mkFreshUserName `perturb
  Observe.replay roundtrip #[] "arithmetic-witness" hooks
  checkComplete roots
  saved.restore true
  let path ← IO.mkRef (#[] : Suggestions.Path)
  discard <| run {effort := 1000} #[] {hooks with
    accepted := fun step state => path.modify (·.push (step, state))}
  let script ← Suggestions.compile saved roots (← path.get) #[] hooks
  if script.usedTerm then throwError "witness suggestion fell back to a proof term"
  checkComplete roots

-- Small copies of the definitions used by SF Logic and IndProp. No result being
-- tested, or equivalent bridging lemma, is available from an imported corpus.
@[simp] def In {α : Type} (x : α) : List α → Prop
  | [] => False
  | y :: ys => y = x ∨ In x ys

example (n : Nat) : In n [2, 4] → ∃ k, n = 2 * k := by witness_search
example (n : Nat) :
    ∃ k, n = if n % 2 = 0 then 2 * k else 2 * k + 1 := by witness_search

def Even (n : Nat) : Prop := ∃ k, n = 2 * k
example (n : Nat) : (n % 2 = 0) ↔ Even n := by witness_search

inductive ev : Nat → Prop where
  | ev_0 : ev 0
  | ev_SS : ∀ n, ev n → ev (n + 2)
example (n : Nat) : ev n → Even n := by witness_search

-- Different coefficients, offsets and orientations test the general operation.
example (n : Nat) : ∃ k, n = 3 * k + n % 3 := by witness_search
example (n : Nat) : ∃ k, k * 5 + n % 5 = n := by witness_search
example (n : Nat) : ∃ k, k - 2 = n := by witness_search
example (n : Nat) : ∃ k, n = 3 * k + n % 3 := by witness_search committed
-- The first proposed witness (5 / 2) fails; search must retain the second.
example : ∃ k : Nat, 5 = 2 * k ∨ 6 = 2 * k := by witness_search

-- Inverse expressions are guesses, not equivalences over natural numbers.
-- A repair must preserve the entire body even when its equation has a solution.
elab "reject_witness " proposition:term : tactic => do
  let original ← saveState
  let type ← Term.elabTerm proposition (some (mkSort .zero))
  let root := (← mkFreshExprSyntheticOpaqueMVar type).mvarId!
  setGoals [root]
  let saved ← saveState
  let moves ← (Critics.arithmeticWitness.propose root).collect
  unless !moves.isEmpty do throwError "negative test had no witness proposal"
  for move in moves do
    saved.restore true
    move.run
    let children ← getUnsolvedGoals
    unless children.length == 1 do throwError "repair discarded its obligation"
    let body := (← whnf (← root.getType)).getAppArgs[1]!
    let some witness := move.subject | throwError "missing proposed witness"
    unless ← isDefEq (← children.head!.getType) (mkApp body witness).headBeta do
      throwError "repair changed the existential body"
    let report ← Observe.capture {effort := 30} #[] "invalid-witness" false false {} (witnessHooks .search)
    if report.success then throwError "proved an invalid witness"
  original.restore true

example : True := by
  reject_witness (∃ k : Nat, 3 = 2 * k)
  reject_witness (∃ k : Nat, 1 = 2 + k)
  reject_witness (∃ k : Nat, 1 = 0 * k)
  reject_witness (∃ k : Nat, 4 = 2 * k ∧ False)
  trivial

end ArithmeticWitnessTests
