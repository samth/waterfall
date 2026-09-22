import waterfall
import waterfall.Observe

open Lean Meta Elab Tactic waterfall

namespace InductionCriticTests

-- Force the repaired induction before any closer can mask a missing repair.
-- Thereafter ordinary closers discharge all cases. This exercises recording,
-- replay, dependent reintroduction and the critic-owned printed command.
elab "checked_index_repair" generalized:(" generalized")? : tactic => do
  let motive := if generalized.isSome then InductionMotive.localGeneralizationAndIndexAbstraction
    else InductionMotive.indexAbstraction
  let policy : SearchPolicy := ⟨Bool, false, fun space =>
    if space.current.state then
      space.expand 0 #[#[.close]] (fun _ => true)
    else
      Choices.map (fun node => {node with state := true})
        (space.expand 0 #[#[.induction]] (fun c => c.move.motive == motive))⟩
  let hooks : Hooks := {policy, trials := fun _ => #[(1, 1)]}
  let initial ← saveState
  let roots ← getUnsolvedGoals
  let report ← Observe.capture {effort := 100} #[] "index-repair" true true {} hooks
  unless report.success do throwError "{report.error}"
  let some plan := report.plan | throwError "missing plan"
  unless plan.steps[0]?.any (·.inductionSummary.any (·.abstractedIndices > 0)) do
    throwError "did not retain repaired induction"
  initial.restore true
  for _ in [:11] do discard <| mkFreshUserName `perturb
  let roundtrip ← ofExcept (fromJson? (toJson plan) : Except String Observe.Plan)
  Observe.replay roundtrip #[] "index-repair" hooks
  checkComplete roots
  initial.restore true
  let path ← IO.mkRef (#[] : Suggestions.Path)
  discard <| run {effort := 100} #[] {hooks with
    accepted := fun step state => path.modify (·.push (step, state))}
  let script ← Suggestions.compile initial roots (← path.get) #[] hooks
  if script.usedTerm || (script.text.splitOn "generalize").length < 2 then
    throwError "index repair lost its ordinary command"
  checkComplete roots

inductive Shape where
  | atom
  | nest (inner : Shape)
inductive Checked : Shape → Nat → Prop where
  | atom : Checked .atom 0
  | nest {t n} : Checked t n → Checked (.nest t) (n + 1)

example (n : Nat) (h : Checked .atom n) : n = 0 := by checked_index_repair
example (n k : Nat) (payload : Fin (k + 1)) (hp : payload.val = k)
    (h : Checked .atom n) : payload.val = k ∧ n = 0 := by
  checked_index_repair generalized

-- Keep the equality: dropping it would leave a recursive case with no reason
-- for its index to equal the fixed atom in the original statement.
inductive Mirror : Shape → Shape → Prop where
  | atom : Mirror .atom .atom
  | nest {a b} : Mirror a b → Mirror (.nest a) (.nest b)
example (h : Mirror .atom (.nest .atom)) : False := by checked_index_repair

-- A consumer-defined parameter critic can use different selection functions
-- without a second policy interface. The common executor does not choose the
-- generalization. Keep this experiment out of the default move enumeration.
private meta def parameterCritic (major : FVarId)
    (select : MVarId → TacticM (Array FVarId)) : Critic := {
  Evidence := Array FVarId
  observe := fun goal => return #[← select goal]
  repair := fun goal variables => pure #[{
    label := "parameter generalization", cost := 1,
    induction := .data, motive := .localGeneralization, major := some major,
    run := do
      let (reverted, goal) ← goal.revert variables
      Induction.perform goal (mkFVar major) reverted.size }] }

elab "parameter_repair" broad:(" broad")? : tactic => withMainContext do
  let some major := (← getLCtx).findFromUserName? `n | throwError "missing major"
  let select := fun _ => do
    let mut variables := #[]
    for d in (← getLCtx) do
      if d.fvarId != major.fvarId && (broad.isSome || d.userName == `acc) &&
          (← isDefEq d.type (mkConst ``Nat)) then
        variables := variables.push d.fvarId
    unless variables.size == (if broad.isSome then 2 else 1) do
      throwError "parameter strategies did not differ"
    pure variables
  let goal ← getMainGoal
  let moves ← ((parameterCritic major.fvarId select).propose goal).collect
  let some move := moves[0]? | throwError "missing parameter repair"
  move.run

def advance : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => advance n (acc + 1)

example (n acc extra : Nat) : advance n acc + extra = n + acc + extra := by
  fail_if_success (induction n <;> simp_all [advance] <;> omega)
  parameter_repair
  all_goals simp_all [advance] <;> omega

example (n acc extra : Nat) : advance n acc + extra = n + acc + extra := by
  parameter_repair broad
  all_goals simp_all [advance] <;> omega

end InductionCriticTests
