import waterfall
import waterfall.Observe
open Lean Meta Elab Tactic waterfall

namespace ContinuationTests

def copy : List Nat → List Nat
  | [] => []
  | a :: xs => a :: copy xs

-- Extra attempt effort alone must not enable an unaffordable deep portfolio.
example (xs : List Nat) : copy xs = copy xs := by
  run_tac withMainContext do
    let goals ← getGoals
    let check (budget : Nat) (expected : Bool) : TacticM Unit := do
      let now ← IO.getNumHeartbeats
      let trials ← withTheReader Core.Context
        (fun c => { c with initHeartbeats := now, maxHeartbeats := budget }) do
          (Mode.search.hooks #[]).prelude {effort := 10000} goals
      let found := trials.any fun t => match t.tag with
        | .num `inductionContinuations _ => true
        | _ => false
      unless found == expected do throwError "incorrect continuation budget gate"
    check 200000000 false
    check 2000000000 true
  rfl

-- The recursive result occurs in two premises, never in the conclusion.
-- Enumeration and execution must survive rollback, and clear only unused data.
example (xs : List Nat) (P Q : List Nat → Prop)
    (h : P (copy xs)) (k : Q (copy xs))
    (combine : ∀ ys, P ys → Q ys → False) : False := by
  run_tac withMainContext do
    let saved ← saveState
    let moves ← movesFor (← getMainGoal) #[] 2 3 .basic
    saved.restore true
    let some move := moves.find? (·.label == "generalize recursive results")
      | throwError "missing hypothesis-only generalization"
    unless move.generalization.abstractions.size == 1 &&
        move.generalization.abstractions.all (!·.retainEquation) &&
        !move.generalization.clearAfter.isEmpty do
      throwError "repair did not retain its exact strengthening plan"
    move.run
    let expected ← Canonical.snapshot (← getUnsolvedGoals)
    saved.restore true
    let commands ← Generalization.commands move.generalization
    for command in commands do
      let text := (← PrettyPrinter.ppTactic command).pretty
      evalTactic (← ofExcept (Parser.runParserCategory (← getEnv) `tactic text))
    unless (← Canonical.snapshot (← getUnsolvedGoals)) == expected do
      throwError "strengthening command differs from plan execution"
  exact combine _ h k

-- Conditional combination exposes the unproved premise as a sibling, rather
-- than admitting it. It also retains a continuation which can use the new fact.
example (P Q R : Prop) (h : P → Q) (p : P) (q : Q → R) : R := by
  run_tac withMainContext do
    let g ← getMainGoal
    let hid := (← getLCtx).findFromUserName? `h |>.get! |>.fvarId
    let saved ← saveState
    let moves ← movesFor g #[] 2 3 .forward
    saved.restore true
    let some move := moves.find? (fun m => m.role == `combine && m.major == some hid)
      | throwError "missing conditional combination"
    move.run
    unless (← getUnsolvedGoals).length == 2 do throwError "lost conditional premise"
  · exact p
  · apply q
    assumption

set_option linter.unusedVariables false in
example (P : Prop) (h : False → P) : True := by
  run_tac withMainContext do
    let g ← getMainGoal
    let hid := (← getLCtx).findFromUserName? `h |>.get! |>.fvarId
    let saved ← saveState
    let moves ← movesFor g #[] 2 3 .forward
    let some move := moves.find? (fun m => m.role == `combine && m.major == some hid)
      | throwError "missing conditional combination"
    move.run
    unless (← getUnsolvedGoals).length == 2 do throwError "lost false premise"
    unless (← (← getMainGoal).getType).isConstOf ``False do
      throwError "failed to retain false premise"
    saved.restore true
  trivial

-- Merely enumerating conditional facts must not instantiate a shared data
-- hole while looking for a definitionally equal fact in the local context.
set_option linter.unusedVariables false in
example (P : Nat → Prop) (n : Nat) (h : True → P n) : True := by
  run_tac withMainContext do
    let saved ← saveState
    let p := mkFVar ((← getLCtx).findFromUserName? `P |>.get! |>.fvarId)
    let unknown ← mkFreshExprMVar (mkConst ``Nat)
    withLocalDeclD `known (mkApp p unknown) fun _ => do
      let goal ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
      setGoals [goal.mvarId!]
      discard <| movesFor goal.mvarId! #[] 2 3 .forward
      if ← unknown.mvarId!.isAssigned then
        throwError "enumeration instantiated a shared argument"
    saved.restore true
  trivial

-- Context pruning is part of the exact plan and its identity, including when
-- clearing a dependent hypothesis is impossible. Rendering uses the same order.
example (n : Nat) (h : n = n) : n = n := by
  run_tac withMainContext do
    let some h := (← getLCtx).findFromUserName? `h | throwError "missing h"
    let goal ← getMainGoal
    let saved ← saveState
    let plan : Generalization.Plan := {clearBefore := #[h.fvarId]}
    let result ← Generalization.prepare goal plan
    setGoals [result.goal]
    let expected ← Canonical.snapshot (← getUnsolvedGoals)
    saved.restore true
    for command in ← Generalization.commands plan do
      let text := (← PrettyPrinter.ppTactic command).pretty
      evalTactic (← ofExcept (Parser.runParserCategory (← getEnv) `tactic text))
    unless (← Canonical.snapshot (← getUnsolvedGoals)) == expected do
      throwError "context pruning command differs from execution"
    saved.restore true
    let move : Move := {label := "same", run := pure ()}
    let a : InductionPlan.Plan := {move, summary := {}, ordinal := 0}
    let b := {a with move := {move with generalization := plan}}
    unless (InductionPlan.deduplicate #[a, b, a]).size == 2 do
      throwError "different pruning plans were conflated"
  rfl

-- Recursive removal/permutation fixtures follow the ACL2 sorting definitions:
-- OathTech/ACL2Lean 5ec2a4b85f87424c86cf434cf7f304498ec9ec6d, Mirrors/Sorting.
-- Source-specific laws are explicit hypotheses, never globally assumed facts.
def member (a : Nat) : List Nat → Bool
  | [] => false
  | b :: xs => if a = b then true else member a xs

def remove (a : Nat) : List Nat → List Nat
  | [] => []
  | b :: xs => if a = b then xs else b :: remove a xs

def rearrange : List Nat → List Nat → Prop
  | [], [] => True
  | [], _ :: _ => False
  | a :: xs, ys => member a ys = true ∧ rearrange xs (remove a ys)

def ordered : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: xs => a ≤ b ∧ ordered (b :: xs)

set_option maxHeartbeats 2000000

-- Full automatic continuation: split the removal guard, keep membership,
-- prune the unrelated recursive invariant, and perform a second induction.
example (comm : ∀ a b xs, remove a (remove b xs) = remove b (remove a xs))
    (symmetric : ∀ xs ys, rearrange xs ys → rearrange ys xs)
    (xs ys : List Nat) (a : Nat) :
    rearrange xs ys → rearrange (remove a xs) (remove a ys) := by
  waterfall (effort := 10000) [member, remove, rearrange, comm, symmetric]

-- Conditional source laws combine after exposing the constructor fields which
-- block equation matching; neither the induction nor the list cases are hints.
example (stable : ∀ xs a, ordered xs → ordered (remove a xs))
    (excludes : ∀ xs a, ordered xs ∧ a ≠ xs.headD 0 ∧ a ≤ xs.headD 0 →
      ¬ member a xs = true)
    (xs ys : List Nat) : ordered xs → ordered ys → rearrange xs ys → xs = ys := by
  waterfall (effort := 10000) [member, remove, rearrange, ordered, stable, excludes]

end ContinuationTests
