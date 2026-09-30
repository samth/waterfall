import waterfall
import waterfall.InductionPlan

open Lean Elab Tactic waterfall

namespace waterfallInductionPlanTest

private meta def fixture (coverage generalized cases ordinal : Nat) : InductionPlan.Plan :=
  { move := {
      label := "induction fixture"
      induction := .data
      motive := if generalized == 0 then .direct else .localGeneralization
      run := pure () }
    summary := {
      coveredCalls := coverage
      generalized
      expectedCases := cases }
    ordinal }

private meta def candidate (index coverage generalized : Nat) (positions : Array Nat)
    (motive : InductionMotive) : Candidate :=
  { action := { group := .induction, index }
    move := {
      label := s!"candidate {index}"
      induction := .data
      inductionSummary := some {
        coveredCalls := coverage
        changingArguments := positions
        generalized }
      motive
      run := pure () } }

-- Coverage dominates optional motive strengthening, while exact duplicate
-- schemes alone may be removed. Lower-quality alternatives remain reachable.
example : True := by
  run_tac
    let broad := fixture 3 0 2 2
    let narrow := fixture 1 0 2 0
    let generalized := fixture 3 2 2 1
    let duplicate := { broad with ordinal := 9 }
    let plans := InductionPlan.ordered #[narrow, generalized, duplicate, broad]
    unless plans.size == 3 && plans[0]?.map (·.ordinal) == some 9 &&
        plans[1]?.map (·.ordinal) == some 1 &&
        plans[2]?.map (·.ordinal) == some 0 do
      throwError "induction-plan dominance or conservative deduplication changed"
  trivial

-- Goal analysis attaches a summary to each actual induction operation.
elab "check_induction_metadata" : tactic => do
  let moves ← waterfall.movesFor (← getMainGoal) #[] 1 2 .induction
  let inductions := moves.filter (fun move : Move => move.induction != .none)
  unless !inductions.isEmpty && inductions.all (·.inductionSummary.isSome) do
    throwError "an induction operation lacks typed plan metadata"
  evalTactic (← `(tactic| simp))

example (xs : List Nat) : xs.length = xs.length := by check_induction_metadata

-- Incomparable schemes retain generator order, including generalized motives.
-- A strict coverage superset may lead, with its direct motive first.
example : True := by
  run_tac
    let nGen := candidate 0 4 1 #[0, 1] .localGeneralization
    let nDirect := candidate 1 4 0 #[0, 1] .direct
    let mGen := candidate 2 3 1 #[1, 2] .localGeneralization
    let mDirect := candidate 3 3 0 #[1, 2] .direct
    let mindGen := candidate 4 9 3 #[0, 1, 2] .localGeneralization
    let mindDirect := candidate 5 9 0 #[0, 1, 2] .direct
    let hooks := InductionPlan.hooks
    let span : Span := { phase := .enumerate, group := some .induction }
    let some incomparable ← hooks.order (← getMainGoal) span #[nGen, nDirect, mGen, mDirect]
      | throwError "induction planner returned no permutation"
    unless incomparable == #[nGen.action, nDirect.action, mGen.action, mDirect.action] do
      throwError "incomparable induction schemes lost stable generator order"
    let some dominant ← hooks.order (← getMainGoal) span
        #[nGen, nDirect, mindGen, mindDirect]
      | throwError "induction planner returned no dominance permutation"
    unless dominant == #[mindDirect.action, mindGen.action, nGen.action, nDirect.action] do
      throwError "strict induction dominance was not selected"
  trivial

-- Evidence relevance is a stable partition, including when another middleware
-- has already changed the order. It retains unrelated evidence, data induction,
-- candidates without a major premise, and multiple motives on the same premise.
inductive Related : Nat → Prop where
  | zero : Related 0
  | step : Related n → Related (n + 1)

inductive Unrelated : Nat → Prop where
  | zero : Unrelated 0

example (n : Nat) (h : Related n) (_other : Unrelated n)
    (p : Nat → Prop) (_abstract : p n) : Related n := by
  run_tac
    let goal ← getMainGoal
    let h ← getFVarId (mkIdent `h)
    let other ← getFVarId (mkIdent `_other)
    let abstract ← getFVarId (mkIdent `_abstract)
    let mk (index : Nat) (kind : InductionKind) (major : Option FVarId) : Candidate :=
      { action := { group := .induction, index }
        move := {
          label := s!"evidence fixture {index}"
          induction := kind
          major
          run := pure () } }
    let candidates := #[mk 0 .data (some h), mk 1 .evidence (some other),
      mk 2 .evidence (some h), mk 3 .evidence none, mk 4 .evidence (some h),
      mk 5 .evidence (some abstract)]
    let span : Span := { phase := .enumerate, group := some .induction }
    let check (hooks : Hooks) (expected : Array Nat) := do
      let some actions ← hooks.order goal span candidates
        | throwError "evidence ordering returned no permutation"
      unless actions.map (·.index) == expected do
        throwError "unexpected evidence order: {repr actions}"
    check InductionPlan.evidenceFirst #[2, 4, 0, 1, 3, 5]
    check (InductionPlan.evidenceFirst {
      order := fun _ _ cs => pure (some (cs.reverse.map (·.action))) }) #[4, 2, 5, 3, 1, 0]
    check Mode.search.hooks #[2, 4, 0, 1, 3, 5]
    let dataOnly := #[mk 0 .data (some h)]
    unless (← InductionPlan.evidenceFirst.order goal span dataOnly).isNone do
      throwError "a batch without evidence should preserve the default order"
  exact h

-- The tactic still uses ordinary theorem hints with the new default ordering.
example (n : Nat) (h : Related n) : Related (n + 1) := by
  waterfall [Related.step]

end waterfallInductionPlanTest
