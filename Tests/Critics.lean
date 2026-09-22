import waterfall
import waterfall.Observe
import waterfall.Repair

open Lean Meta Elab Tactic waterfall

namespace CriticTests

-- A consumer supplies its own evidence type and functions. Both construction
-- phases are transactional, but yielding a move must not roll back its execution.
-- Stopping after one move must not construct repairs for later observations.
example : True := by
  run_tac
    let g ← getMainGoal
    let repairs ← IO.mkRef (0 : Nat)
    let critic : Critic := {
      Evidence := Nat
      observe := fun goal => do
        goal.assign (mkConst ``True.intro)
        setGoals []
        return #[7, 11]
      repair := fun goal evidence => do
        if ← goal.isAssigned then throwError "observation escaped rollback"
        unless (← getGoals) == [goal] do throwError "observation changed the agenda"
        unless evidence == 7 do throwError "constructed an unrequested repair"
        repairs.modify (· + 1)
        setGoals []
        goal.assign (mkConst ``True.intro)
        return #[{ label := "consumer repair", run := do
          if ← goal.isAssigned then throwError "repair construction escaped rollback"
          unless (← getGoals) == [goal] do throwError "repair construction changed the agenda"
          goal.assign (mkConst ``True.intro)
          setGoals [] }] }
    let accepted ← critic.propose g fun move => do move.run; return true
    unless accepted && (← repairs.get) == 1 do throwError "critic did not stop lazily"
    checkComplete [g]

-- Lookahead accepts an ordinary move producer unrelated to Critic. Temporary
-- introductions and even changes made by that producer must be rolled back.
example : ∀ p : Prop, p → p := by
  run_tac
    let root ← getMainGoal
    let original ← getGoals
    let producer : MVarId → Choices Move := fun goal visit => do
      unless (← goal.getType).isFVar do throwError "binders were not exposed"
      setGoals []
      visit { label := "lookahead fixture", run := pure () }
    unless ← Scheduling.exposesMoves producer original do
      throwError "generic move lookahead failed"
    unless (← getGoals) == original && !(← root.isAssigned) do
      throwError "lookahead changed the root checkpoint"
  intro p hp
  exact hp

-- Rewriting must preserve the side condition rather than admitting the
-- premise created by specialization. The returned recipe must survive rollback.
elab "conditional_repair" : tactic => withMainContext do
  let root ← getMainGoal
  let saved ← saveState
  let moves ← (Critics.quantifiedRewrite.propose root).collect
  let some move := moves[0]? | throwError "no quantified rewrite"
  saved.restore true
  move.run
  unless (← getUnsolvedGoals).length == 2 do throwError "lost conditional rewrite premise"
  evalTactic (← `(tactic| all_goals first | rfl | assumption))
  checkComplete [root]
  saved.restore true
  for _ in [:12] do discard <| mkFreshUserName `perturb
  let some command := move.command? | throwError "missing ordinary proof command"
  evalTactic command
  unless (← getUnsolvedGoals).length == 2 do throwError "recipe lost conditional premise"

example (f : Nat → Nat) (p : Nat → Prop) (k : Nat) (hp : p k)
    (h : ∀ a, p a → f a = a) : f k + 1 = k + 1 := by
  conditional_repair
  · rfl
  · exact hp

-- The second critic composes with an unrelated search policy. Expensive
-- closers are intentionally absent so they cannot mask a broken rewrite path.
private meta def rewriteHooks : Hooks := Critic.hooks #[Critics.quantifiedRewrite] {
  trials := fun _ => #[(3, 1)]
  policy := ⟨Unit, (), fun space => space.expand 0 #[] fun c =>
    c.move.closure == .exact || c.move.role == `rewrite⟩ }

elab "checked_rewrite_search" : tactic => do
  let saved ← saveState
  let roots ← getUnsolvedGoals
  let report ← Observe.capture {effort := 30} #[] "quantified-rewrite" true true {} rewriteHooks
  unless report.success do throwError "{report.error}"
  let some plan := report.plan | throwError "missing plan"
  unless plan.steps.any (·.label == "specialize equality at target") do
    throwError "did not use the repair"
  let roundtrip ← ofExcept (fromJson? (toJson plan) : Except String Observe.Plan)
  saved.restore true
  for _ in [:12] do discard <| mkFreshUserName `perturb
  Observe.replay roundtrip #[] "quantified-rewrite" rewriteHooks
  checkComplete roots
  saved.restore true
  let path ← IO.mkRef (#[] : Suggestions.Path)
  discard <| run {effort := 30} #[] { rewriteHooks with
    accepted := fun step state => path.modify (·.push (step, state)) }
  let script ← Suggestions.compile saved roots (← path.get) #[] rewriteHooks
  if script.usedTerm || (script.text.splitOn "rewrite").length <= 1 then
    throwError "repair did not produce an ordinary rewrite command"
  checkComplete roots

example (f : Nat → Nat) (k : Nat) (h : ∀ a, f a = a) :
    f k + 1 = k + 1 := by checked_rewrite_search

-- The standard modes still solve these goals with their existing closers.
example (f : Nat → Nat) (h : ∀ a, f a = a) : ∀ k, f k + 1 = k + 1 := by
  waterfall (effort := 100)

example (f : Nat → Nat) (h : ∀ a, f a = a) : ∀ k, f k + 1 = k + 1 := by
  waterfall (mode := .committed) (effort := 100)

-- The optional provider also composes with the committed policy. Bypass its
-- saturation/simplification closers here so its ordinary rewrite path is tested.
example (f : Nat → Nat) (k : Nat) (h : ∀ a, f a = a) :
    f k + 1 = k + 1 := by
  run_tac
    let policy : SearchPolicy := ⟨Committed.State, {}, fun space =>
      let expand := fun idx batches admit =>
        space.expand idx batches (fun c => admit c &&
          (c.move.closure == .exact || c.move.role == `rewrite))
      Committed.choose { space with expand }⟩
    let hooks := Critic.hooks #[Critics.quantifiedRewrite] { Committed.hooks with policy }
    discard <| run {effort := 30} #[] hooks

-- Preparation lookahead also guides ordinary ordering. This abstract semantic
-- rule needs a repair before introducing away the rule's matching conclusion;
-- indiscriminate bulk introduction lost the corresponding SF Hoare proof.
private abbrev Triple {S C : Type} (eval : C → S → S → Prop)
    (P : S → Prop) (c : C) (Q : S → Prop) := ∀ s t, eval c s t → P s → Q t

example {S C B : Type} (eval : C → S → S → Prop)
    (loop : C → B → C) (guard : S → B → Bool) :
    (∀ P Q b c, Triple eval P c Q →
      Triple eval (fun s => Q s ∧ guard s b = false) c Q →
      Triple eval P (loop c b) (fun s => Q s ∧ guard s b = true)) →
    (∀ P b c, Triple eval P c P →
      Triple eval P (loop c b) (fun s => P s ∧ guard s b = true)) := by
  run_tac
    let stats ← run {effort := 1000} #[] Mode.search.hooks
    unless stats.choices.contains "split blocked rule premise" do
      throwError "preparation ordering failed to retain the semantic-rule repair"

-- An unprovable condition must remain an unprovable sibling, including after
-- the rewritten main goal has closed. No partial proof can count as success.
example : True := by
  fail_if_success
    have : Nat.succ 0 = 0 := by
      have h : ∀ a : Nat, False → Nat.succ a = a := fun _ h => h.elim
      run_tac discard <| run {effort := 20} #[] rewriteHooks
  trivial

end CriticTests
