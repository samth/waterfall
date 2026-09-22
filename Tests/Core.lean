import waterfall

open Lean Meta Elab Tactic waterfall

namespace waterfallTest

-- A resource exception after partial success must be contained; the caller
-- restores the whole snapshot before trying the next alternative. Work spent
-- on the rejected attempt is not refunded. Use Lean's real timeout exception.
elab "check_timeout_recovery" : tactic => do
  let saved ← Tactic.saveState
  let stats ← IO.mkRef ({} : Stats)
  let timed : Move := { cost := 1, label := "timeout after assignment", run := do
    evalTactic (← `(tactic| trivial))
    Core.throwMaxHeartbeat `wfCoreTest `maxHeartbeats 1 }
  if ← attempt {} stats timed then throwError "timeout was accepted"
  saved.restore true
  unless (← getUnsolvedGoals).length == 1 do throwError "lost original goal"
  let closes : Move := { cost := 1, label := "following alternative", run := evalTactic (← `(tactic| trivial)) }
  unless ← attempt {} stats closes do throwError "search did not recover"
  unless (← stats.get).attempts == 2 do throwError "refunded a failed attempt"

example : True := by check_timeout_recovery

abbrev Counter := Nat

-- This needs quantified fact instantiation. An alias in the binder type must
-- not poison the grind rule list, even with just the four root closer attempts.
example (f : Counter → Counter) (h : ∀ k, f (f k) = k)
    (a b : Counter) (hab : f a = f b) : a = b := by
  waterfall? (effort := 4)

-- Exercise an operation *after* restoring the snapshot from before its
-- enumeration. Local Expr-to-Syntax holes must not survive across this boundary.
elab "check_local_operation " label:str : tactic => withMainContext do
  let g ← getMainGoal
  let saved ← Tactic.saveState
  let ops ← operations g #[]
  saved.restore true
  let some op := ops.find? (·.label == label.getString)
    | throwError "missing local operation"
  op.run

example (p : Prop) (h : p) : p := by
  check_local_operation "apply hypothesis"

-- Extensionality creates a pointwise goal in the restored context, including
-- dependent codomains. It must not leave the fresh function argument unbound.
example (α : Type) (β : α → Type) (f g : (a : α) → β a)
    (h : ∀ a, f a = g a) : f = g := by
  check_local_operation "function extensionality"
  exact h _

-- A false pointwise equality cannot close by extensionality alone. Both the
-- function equality and its surrounding sibling must survive failed search.
example : True := by
  fail_if_success have : (fun n : Nat => n) = (fun n => n + 1) ∧ True := by waterfall (effort := 50)
  trivial

example (p q : Prop) (b : Bool) (h : if b then p else q) : p ∨ q := by
  check_local_operation "split hypothesis"
  all_goals simp_all

-- A local rule whose conclusion matches the goal modulo one missing premise
-- suggests that premise as a case split. The negative rule closes the branch
-- in which the first rule remains blocked.
example (p q r : Prop) (hp : p) (positive : p → q → r)
    (negative : ¬q → r) : r := by
  run_tac
    let g ← getMainGoal
    let moves ← Critics.blockedPremises g
    let some critic := moves.find? (·.role == `critic)
      | throwError "missing blocked-premise critic"
    unless critic.major == some (← getFVarId (mkIdent `positive)) &&
        critic.subject == some (mkFVar (← getFVarId (mkIdent `q))) do
      throwError "critic lost its source rule or stable blocker"
    critic.run
  all_goals grind

-- Preparation metadata is semantic policy input. The base generator retains
-- its historical one-binder-first order; scheduling hooks may reorder typed moves.
example : ∀ p : Prop, p → p := by
  run_tac
    let moves ← movesFor (← getMainGoal) #[] 1 1 .basic
    unless moves[0]?.any (·.preparation == .oneBinder) &&
        moves[1]?.any (·.preparation == .allBinders) do
      throwError "introduction metadata or order changed"
  intro p hp
  exact hp

-- Critics only contribute moves. Adding them preserves a consumer's trial
-- schedule; scheduling no longer recognizes a particular critic's evidence.
example : True := by
  run_tac
    let root ← getMainGoal
    let inner : Hooks := { prelude := fun _ _ => pure #[{depth := 3, attempts := 7}] }
    let trials ← (Critics.hooks inner).prelude {} [root]
    unless trials.size == 1 && trials[0]!.depth == 3 && trials[0]!.attempts == 7 do
      throwError "critic changed its consumer's trial schedule"
  trivial

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  check_local_operation "forward hypothesis"
  assumption

-- A definition hiding a binder must not cause a no-progress cycle. A rejected
-- eager-introduction experiment exposed this regression during development.
def Universal (P : Nat → Prop) : Prop := ∀ n, P n

example (P : Nat → Prop) (h : ∀ n, P n) : Universal P := by
  waterfall (effort := 20)

def append : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

theorem append_nil (xs : List Nat) : append xs [] = xs := by
  waterfall?

theorem append_assoc (xs ys zs : List Nat) :
    append (append xs ys) zs = append xs (append ys zs) := by
  waterfall? (effort := 2000)

-- Generalized variables and their dependent hypotheses must be reintroduced
-- into each case. Leaving quantified goals here wastes later search depth.
example (xs ys : List Nat) : (append xs ys).length = xs.length + ys.length := by
  check_local_operation "induction xs generalized"
  all_goals
    run_tac
      if (← (← getMainGoal).getType).isForall then
        throwError "generalized parameter was not reintroduced"
    simp_all [append] <;> omega

-- The function-call syntax is elaborated inside the selected alternative,
-- after rollback. Its induction hypotheses must remain in the right context.
example (xs ys : List Nat) : (append xs ys).length = xs.length + ys.length := by
  check_local_operation "function induction"
  all_goals (simp_all <;> omega)

def rev : List Nat → List Nat
  | [] => []
  | x :: xs => append (rev xs) [x]

example (xs ys : List Nat) : rev (append xs ys) = append (rev ys) (rev xs) := by
  waterfall? (effort := 4000) [append_assoc, append_nil]

inductive Reach : Nat → Nat → Prop where
  | stay (a : Nat) : Reach a a
  | next (a b : Nat) : Reach a b → Reach a (b + 1)

def advance (b : Nat) (flag : Bool) : Nat := if flag then b + 1 else b

-- Leaf construction of an inductive predicate, including beneath a binder.
-- Five attempts allow only the root closers, not backward search operations.
theorem advance_reachable (a b : Nat) (flag : Bool) :
    Reach a b → Reach a (advance b flag) := by
  fail_if_success grind +lax [advance]
  waterfall? (effort := 5)

-- Lean's elaborated induction handles non-variable indices of a relation.
example (bound n : Nat) (h : Reach (bound + 1) n) : bound < n := by
  check_local_operation "induction h"
  all_goals omega

inductive Shape where
  | atom
  | nest (inner : Shape)

inductive Checked : Shape → Nat → Prop where
  | atom : Checked .atom 0
  | nest {t n} : Checked t n → Checked (.nest t) (n + 1)

-- Keep the fixed index equation: it rules out the recursive constructor.
example (n : Nat) (h : Checked .atom n) : n = 0 := by
  check_local_operation "induction h abstract indices"
  all_goals simp_all

-- Generalizing k also reverts its dependent value and proof. Reintroduce the
-- complete dependency closure after preparing indices and forming the IH.
example (n k : Nat) (payload : Fin (k + 1)) (hp : payload.val = k)
    (h : Checked .atom n) : payload.val = k ∧ n = 0 := by
  check_local_operation "induction h generalized abstract indices"
  all_goals
    run_tac
      if (← (← getMainGoal).getType).isForall then
        throwError "generalized dependency remained quantified"
    simp_all

-- A function argument introduced in one move can occur in an evidence index
-- prepared by a later move. Both moves must use the restored local context.
example (f : Nat → Nat) (h : ∀ x, Checked .atom (f x)) : f = fun _ => 0 := by
  check_local_operation "function extensionality"
  rename_i x
  have hx := h x
  check_local_operation "induction hx abstract indices"
  all_goals simp_all

inductive Token : Nat → Prop where
  | doubled (n : Nat) : Token (n + n)

theorem doubled_token (n : Nat) : Token (n + n) := Token.doubled n

-- Retrieve a previously proved theorem without adding it to the explicit rule
-- list. Selecting this label distinguishes retrieval from constructor search.
example (n : Nat) : Token (n + n) := by
  check_local_operation "apply library waterfallTest.doubled_token"

inductive Packet where
  | empty
  | payload (value : Nat)

def bounded (bound : Nat) : Packet → Prop
  | .empty => False
  | .payload value => value ≤ bound

def combine : Packet → Packet → Packet
  | .payload a, .payload b => .payload (a + b)
  | .empty, _ => .empty
  | _, .empty => .empty

-- Function cases preserve unrelated parameters and the assumptions depending
-- on them. These are useful case facts, not induction-generalization targets.
theorem combine_bounded (bound : Nat) (left right : Packet)
    (hl : bounded bound left) (hr : bounded bound right) :
    bounded (bound + bound) (combine left right) := by
  run_tac
    let g ← getMainGoal
    let external ← getFVarId (mkIdent `bound)
    let saved ← Tactic.saveState
    let moves ← operations g #[(← `(term| combine))]
    saved.restore true
    let some chosen := moves.find? (·.label == "function cases")
      | throwError "missing function case operation"
    chosen.run
    for child in ← getUnsolvedGoals do
      child.withContext do
        unless (← getLCtx).find? external |>.isSome do
          throwError "function cases reverted its external parameter"
  all_goals grind +lax [bounded, combine]

-- Witness choices affect later conjuncts. No earlier theorem has this target.
inductive Mark : Nat → Prop
  | zero : Mark 0
  | one : Mark 1

example : ∃ n, Mark n ∧ n = 1 := by
  waterfall? (effort := 1000)

inductive Allowed : Nat → Prop
  | one : Allowed 1

-- The first Mark constructor chooses 0; the later Allowed obligation refutes
-- that choice. Search must revisit the earlier branch and choose Mark.one.
theorem shared_witness : ∃ n, Mark n ∧ Allowed n := by
  waterfall? (effort := 4000)

-- Failure must restore the original goal and all local state.
example (p : Prop) (h : p) : p := by
  fail_if_success waterfall (effort := 0)
  exact h

-- Closing one conjunct never licenses dropping another.
example : True := by
  fail_if_success have : True ∧ False := by waterfall (effort := 50)
  trivial

example : True := by
  fail_if_success have : False := by waterfall (effort := 50)
  trivial

-- The same frozen choice sequence must become reachable with more effort.
example (xs : List Nat) : append xs [] = xs := by
  fail_if_success waterfall (effort := 1)
  waterfall? (effort := 1000)

-- A deliberately tiny initial step slice cannot close even this hypothesis.
-- Extra effort must increase step strength, not only repeat bounded steps.
example (p : Prop) (h : p) : p := by
  fail_if_success run_tac discard <| (← run {effort := 4, attemptHeartbeats := 20})
  run_tac
    let s ← run {effort := 2000, attemptHeartbeats := 20}
    unless s.strength > 1 do throwError "did not increase individual step effort"

end waterfallTest

#print axioms waterfallTest.append_nil
#print axioms waterfallTest.append_assoc
#print axioms waterfallTest.shared_witness
#print axioms waterfallTest.advance_reachable
#print axioms waterfallTest.combine_bounded
namespace waterfallTest
-- The free-closer policy retains the original leaf-admission contract. This is
-- a general callback, not a special case for the fixture or constructor names.
private def freeClosingPolicy : Hooks := {
  cost := fun g span candidate =>
    if candidate.action.group == .close then pure 0
    else ({} : Hooks).cost g span candidate }

-- The constructor has an inferred data field, but no unproved premise. Preserve
-- the original twenty-attempt/depth-zero check under explicit free admission,
-- then separately check the actual default's charged admission and same proof.
example (n : Nat) : Token (n + n) := by
  run_tac
    let saved ← Tactic.saveState
    let s ← run {effort := 20} #[] freeClosingPolicy
    unless s.depth == 0 && s.choices.contains "close constructor waterfallTest.Token.doubled" do
      throwError "free constructor required structural search"
    saved.restore true
    let s ← run {effort := 30}
    unless s.depth == 1 && s.choices.contains "close constructor waterfallTest.Token.doubled" do
      throwError "default constructor admission changed its proof or charged depth"

-- Expose two obligations sharing an unknown witness. Mark.zero is tried first;
-- Allowed 0 then fails, so even a fully closed earlier branch must be undone.
example : ∃ n, Mark n ∧ Allowed n := by
  check_local_operation "constructor Exists.intro"
  check_local_operation "constructor And.intro"
  run_tac
    let saved ← Tactic.saveState
    let s ← run {effort := 100} #[] freeClosingPolicy
    unless s.depth == 0 &&
        s.choices.contains "close constructor waterfallTest.Mark.one" &&
        s.choices.contains "close constructor waterfallTest.Allowed.one" do
      throwError "free constructor closure lost the shared-witness continuation"
    saved.restore true
    -- Keep the same hundred-attempt bound for the actual default. Both closing
    -- labels must survive rollback of the earlier, incompatible zero witness.
    let s ← run {effort := 100}
    unless s.depth == 1 &&
        s.choices.contains "close constructor waterfallTest.Mark.one" &&
        s.choices.contains "close constructor waterfallTest.Allowed.one" do
      throwError "default constructor closure lost the shared-witness continuation"
end waterfallTest

#eval IO.println "WF_CORE_TEST_EOF"
