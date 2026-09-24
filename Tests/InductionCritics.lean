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
    generalization := {parameters := variables},
    run := Induction.withPlan goal (mkFVar major) {parameters := variables} }] }

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
  let initial ← saveState
  move.run
  let expected ← Canonical.snapshot (← getUnsolvedGoals)
  initial.restore true
  -- Compare native execution with the independently reparsed command. The
  -- narrow selector must not silently print the default broad generalization.
  let command ← Induction.command (mkFVar major.fvarId) move.generalization
  let text := (← PrettyPrinter.ppTactic command).pretty
  if broad.isNone && (text.splitOn "extra").length > 1 then
    throwError "renderer generalized a parameter absent from the plan"
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `tactic text)
  evalTactic stx
  unless (← Canonical.snapshot (← getUnsolvedGoals)) == expected do
    throwError "generalization recipe differs from native execution"

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

-- Equal counts and labels must not conflate different motive choices.
example (n acc extra : Nat) : n + acc + extra = n + acc + extra := by
  run_tac
    let ctx ← getLCtx
    let some accDecl := ctx.findFromUserName? `acc | throwError "missing acc"
    let some extraDecl := ctx.findFromUserName? `extra | throwError "missing extra"
    let goal ← getMainGoal
    let some major := ctx.findFromUserName? `n | throwError "missing major"
    let mk := fun parameter => do
      let moves ← ((parameterCritic major.fvarId (fun _ => pure #[parameter])).propose goal).collect
      let some move := moves[0]? | throwError "missing move"
      pure ({move, summary := {«generalized» := 1}, ordinal := 0} : InductionPlan.Plan)
    let a ← mk accDecl.fvarId
    let b ← mk extraDecl.fvarId
    unless (InductionPlan.deduplicate #[a, b, a]).size == 2 do
      throwError "different generalization plans were conflated"
  rfl

-- Expression abstraction deliberately distinguishes equation-preserving repair
-- from conjecture strengthening. Both execute and print from the same plan.
elab "check_abstraction " retain:ident : tactic => withMainContext do
  let some n := (← getLCtx).findFromUserName? `n | throwError "missing n"
  let some h := (← getLCtx).findFromUserName? `h | throwError "missing h"
  let expression ← mkAppM ``Nat.succ #[mkFVar n.fvarId]
  let plan : Generalization.Plan := {
    abstractions := #[{expression, retainEquation := retain.getId == `keep}],
    hypotheses := #[h.fvarId] }
  let saved ← saveState
  let prepared ← Generalization.prepare (← getMainGoal) plan
  setGoals [prepared.goal]
  let expected ← Canonical.snapshot (← getUnsolvedGoals)
  saved.restore true
  let commands ← Generalization.commands plan
  for command in commands do
    let text := (← PrettyPrinter.ppTactic command).pretty
    evalTactic (← ofExcept (Parser.runParserCategory (← getEnv) `tactic text))
  unless (← Canonical.snapshot (← getUnsolvedGoals)) == expected do
    throwError "abstraction scope or equations differ in rendering"

example (n : Nat) (h : n.succ > 0) : n.succ > 0 := by
  check_abstraction keep
  assumption
example (n : Nat) (h : n.succ > 0) : n.succ > 0 := by
  check_abstraction drop
  assumption

-- Assigned induction motives can discard producer arguments. Dependency checks
-- must inspect the instantiated target and invariant, not the raw application.
example (n : Nat) : n = n := by
  run_tac withMainContext do
    let saved ← saveState
    let some n := (← getLCtx).findFromUserName? `n | throwError "missing input"
    let input := mkFVar n.fvarId
    let result ← mkAppM ``Nat.succ #[input]
    let motiveType ← Term.elabTerm (← `(Nat → Nat → Prop)) none
    let motive ← mkFreshExprMVar motiveType
    let value ← Term.elabTerm (← `(fun (_ result : Nat) => result > 0)) (some motiveType)
    motive.mvarId!.assign value
    let proposition := mkApp2 motive input result
    unless proposition.hasMVar && proposition.containsFVar n.fvarId do
      throwError "fixture lost its assigned motive"
    withLocalDeclD `ih proposition fun ih => do
      -- A genuine relation to the producer input must be cleared, not silently
      -- generalized as though it constrained the selected result alone.
      let relation ← mkEq result input
      withLocalDeclD `producer_relation relation fun relationProof => do
        let target ← mkFreshExprSyntheticOpaqueMVar proposition
        let goal := target.mvarId!
        let some plan ← Generalization.abstractIndependent goal #[result]
          | throwError "assigned target motive concealed independent result"
        unless plan.hypotheses == #[ih.fvarId!] &&
            plan.clearBefore == #[relationProof.fvarId!] do
          throwError "assigned hypothesis motive lost its invariant"
        let before ← saveState
        let commands ← Generalization.commands plan
        let prepared ← Generalization.prepare goal plan
        setGoals [prepared.goal]
        let expected ← Canonical.snapshot (← getUnsolvedGoals)
        prepared.goal.withContext do
          if (← getLCtx).contains n.fvarId then
            throwError "obsolete producer input survived abstraction"
        evalTactic (← `(tactic| assumption))
        checkComplete [goal]
        before.restore true
        setGoals [goal]
        for command in commands do
          let text := (← PrettyPrinter.ppTactic command).pretty
          evalTactic (← ofExcept (Parser.runParserCategory (← getEnv) `tactic text))
        unless (← Canonical.snapshot (← getUnsolvedGoals)) == expected do
          throwError "dependency-aware plan changed during command replay"
        evalTactic (← `(tactic| assumption))
        checkComplete [goal]
        let dependent ← mkFreshExprSyntheticOpaqueMVar relation
        unless (← Generalization.abstractIndependent dependent.mvarId! #[result]).isNone do
          throwError "independent abstraction discarded a target relation"
    saved.restore true
  rfl

end InductionCriticTests
