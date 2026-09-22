module
public import waterfall.Core
public import waterfall.Choices

meta section

/-!
A bounded closer-scheduling experiment. The ordinary fair search is unchanged.
On a bounded prelude contour, cheap closure and proof shaping precede expensive
saturation; every operation remains in a finite stage.
-/

open Lean Meta Elab Tactic
namespace waterfall.Scheduling

public abbrev State := Unit

/-- A conservative depth supported by a branching work budget. Dividing the
binary logarithm by two models an effective branching factor near four. -/
public def depthForEffort (effort : Nat) : Nat :=
  max 1 ((Nat.log2 effort + 1) / 2)

private def tryStage (space : Space State) (prepared : Prepared State)
    (groups : Array Group) (admit : Candidate → Bool) : Choices (Node State) :=
  fun visit => space.propose prepared #[groups] admit fun proposal =>
    space.execute proposal visit

private def tryProposals (space : Space State) (proposals : Array (Proposal State)) :
    Choices (Node State) := fun visit => do
  for proposal in proposals do
    if ← space.execute proposal visit then return true
  return false

/-- A complete staged depth-first traversal. Cheap closure precedes local
shaping. A conservatively dominant induction scheme runs before saturation;
otherwise saturation gets the earlier slot. Theorem search and all remaining
operations stay in later finite stages. -/
public def choose (space : Space State) : Choices (Node State) := fun visit => do
  let some prepared ← space.prepare space.current 0 | return false
  if ← tryStage space prepared #[.close]
      (fun c => c.move.closure != .simplification &&
        c.move.closure != .saturation) visit then return true
  if ← tryStage space prepared #[.basic, .hypotheses]
      (fun c => c.action.group == .basic || c.move.preparation != .none) visit then return true
  let inductions ← (space.propose prepared #[#[.induction]]
    (fun c => c.move.induction != .none)).collect
  let dominant := inductions.any fun a =>
    inductions.any fun b => InductionPlan.dominates a.candidate b.candidate
  if dominant && (← tryProposals space inductions visit) then return true
  if ← tryStage space prepared #[.hypotheses]
      (fun c => c.move.preparation == .none) visit then return true
  if ← tryStage space prepared #[.close]
      (fun c => c.move.closure == .simplification) visit then return true
  if ← tryStage space prepared #[.close]
      (fun c => c.move.closure == .saturation) visit then return true
  if !dominant && (← tryProposals space inductions visit) then return true
  if ← tryStage space prepared #[.functions]
      (fun c => c.move.induction != .none) visit then return true
  if ← tryStage space prepared #[.rules, .library, .forward]
      (fun _ => true) visit then return true
  tryStage space prepared #[.functions, .induction]
    (fun c => c.move.induction == .none) visit

/-- Read-only lookahead for a bounded preparation trial. Any move producer can
supply the continuation; scheduling knows neither its evidence nor its rules.
Already exposed goals use the ordinary schedule. -/
public def exposesMoves (propose : MVarId → Choices Move)
    (goals : List MVarId) : TacticM Bool := do
  let saved ← Tactic.saveState
  try
    for goal in goals do
      saved.restore true
      let (introduced, child) ← goal.withContext goal.intros
      if introduced.isEmpty then continue
      if ← propose child (fun _ => pure true) then return true
    return false
  finally saved.restore true

/-- Prefer contextual preparation over ordinary operations in a batch. Bulk
introduction gets priority only when the supplied lookahead exposes useful work.
This is ordering middleware, independent of the move producer and traversal. -/
public def preparations (inner : Hooks := {})
    (exposes : List MVarId → TacticM Bool := fun _ => pure false) : Hooks := { inner with
  order := fun goal span candidates => do
    let requested ← inner.order goal span candidates
    let ordered ← match requested with
      | none => pure candidates
      | some actions => actions.mapM fun action => do
          let some candidate := candidates.find? (·.action == action)
            | throwError "preparation ordering received an unknown action"
          return candidate
    let preparatory := fun c : Candidate =>
      c.action.group == .hypotheses && c.move.preparation != .none
    let repairs := ordered.filter preparatory
    let others := ordered.filter (fun c => !preparatory c)
    let bulkFirst ← if others.any (·.move.preparation == .allBinders) then
      exposes [goal] else pure false
    let others := if bulkFirst then
      others.filter (·.move.preparation == .allBinders) ++
        others.filter (·.move.preparation != .allBinders)
      else others
    return some ((repairs ++ others).map (·.action)) }

public def hooks (inner : Hooks := {})
    (activate : List MVarId → TacticM Bool := fun _ => pure true) : Hooks := preparations { inner with
  policy := ⟨State, (), fun space =>
    if space.root.origin == .prelude then
      choose space
    else space.expand 0 #[] (fun _ => true)⟩
  -- In a branching search, the depth supported by a node budget grows
  -- logarithmically. This budget-derived contour bounds attractive wrong
  -- branches without reinstating a feature-specific magic depth. Request the
  -- available effort; the engine caps this trial to a quarter of what remains
  -- when it starts, leaving the ordinary fair schedule room to run.
  prelude := fun cfg goals => do
    let scheduled := if ← activate goals then
      #[{ depth := depthForEffort cfg.effort, attempts := cfg.effort }] else #[]
    return scheduled ++ (← inner.prelude cfg goals)
} activate

end waterfall.Scheduling
