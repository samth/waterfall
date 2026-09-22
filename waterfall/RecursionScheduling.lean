module
public import waterfall.Scheduling
public import waterfall.Choices

meta section

/-!
A bounded closer-scheduling experiment. The ordinary fair search is unchanged.
On an activated prelude contour, cheap closure and proof shaping precede expensive
saturation; every operation remains in a finite stage.
-/

open Lean Meta Elab Tactic
namespace waterfall.RecursionScheduling

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

/-- Nested recursive computations can require several shaping operations before
an induction hypothesis becomes useful. Request a bounded trial for that shape. -/
public def needsRecursionPrelude (goals : List MVarId) : TacticM Bool := do
  for g in goals do
    let found ← g.withContext do
      let calls ← forallTelescopeReducing (← g.getType) fun _ target => do
        let calls ← IO.mkRef (#[] : Array Expr)
        target.forEach fun e => do
          if e.isApp && e.hasFVar && !e.hasLooseBVars then
            if let .const n _ := e.getAppFn then
              if (← isRecursiveDefinition n) && !(← whnf (← inferType e)).isForall then
                calls.modify (·.push e)
        return ← calls.get
      return calls.any fun outer => calls.any fun inner =>
        inner != outer && (outer.find? (· == inner)).isSome
    if found then return true
  return false

/-- Prefer a producer whose recursive result occurs inside another candidate.
Do not repeatedly promote a definition already inducted on in this ancestry.
All other candidates retain their original relative order and remain available. -/
private def producerPlans (prepared : Prepared State)
    (proposals : Array (Proposal State)) : Array (Proposal State) := Id.run do
  let ancestors := (prepared.source.jobs[prepared.focus]!).ancestors
  let producers := proposals.filter fun p =>
    match p.candidate.move.subject with
    | none => false
    | some call =>
      !(ancestors.any fun a => a.move.induction == .functional &&
        a.move.subject.any (fun prior => prior.getAppFn == call.getAppFn)) &&
      proposals.any fun q => q.candidate.move.subject.any fun outer =>
        outer != call && (outer.find? (· == call)).isSome
  return producers

/-- A complete staged depth-first traversal. Cheap closure precedes local
shaping. A conservatively dominant induction scheme runs before saturation;
otherwise saturation gets the earlier slot. Theorem search and all remaining
operations stay in later finite stages. -/
public def choose (space : Space State) (exposeFields := false) : Choices (Node State) := fun visit => do
  let some prepared ← space.prepare space.current 0 | return false
  if ← tryStage space prepared #[.close]
      (fun c => c.move.closure != .simplification &&
        c.move.closure != .saturation) visit then return true
  if ← tryStage space prepared #[.basic]
      (fun c => c.move.role == `ruleRewrite) visit then return true
  let ancestors := (prepared.source.jobs[prepared.focus]!).ancestors
  -- Rewriting or coordinated abstraction can expose a short closing proof.
  -- The second contour also tries constructor exposure after induction; keep
  -- it separate because case analysis can otherwise preempt a useful invariant.
  if ancestors.any (fun a => a.move.role == `ruleRewrite || a.move.role == `jointGeneralization ||
      (exposeFields && a.move.induction == .functional)) then
    if ← tryStage space prepared #[.close]
        (fun c => c.move.closure == .simplification || c.move.closure == .saturation) visit then return true
  if ancestors.any (fun a => a.move.role == `jointGeneralization ||
      (exposeFields && a.move.induction == .functional)) then
    if ← tryStage space prepared #[.basic]
        (fun c => c.move.preparation == .targetSplit) visit then return true
    if ← tryStage space prepared #[.induction]
        (fun c => c.move.role == `blockedMatch) visit then return true
    if exposeFields then
      if ← tryStage space prepared #[.induction]
          (fun c => c.move.role == `constructorField) visit then return true
  if ← tryStage space prepared #[.basic, .hypotheses]
      (fun c => c.action.group == .basic || c.move.role == `critic) visit then return true
  let functions ← (space.propose prepared #[#[.functions]]
    (fun c => c.move.induction == .functional)).collect
  let producers := producerPlans prepared functions
  if ← tryProposals space producers visit then return true
  let inductions ← (space.propose prepared #[#[.induction]]
    (fun c => c.move.induction != .none)).collect
  let dominant := inductions.any fun a =>
    inductions.any fun b => InductionPlan.dominates a.candidate b.candidate
  if dominant && (← tryProposals space inductions visit) then return true
  if ← tryStage space prepared #[.hypotheses]
      (fun c => c.move.role != `critic) visit then return true
  if ← tryStage space prepared #[.close]
      (fun c => c.move.closure == .simplification) visit then return true
  if ← tryStage space prepared #[.close]
      (fun c => c.move.closure == .saturation) visit then return true
  if !dominant && (← tryProposals space inductions visit) then return true
  if ← tryProposals space (functions.filter fun p =>
      !producers.any (fun q => p.candidate.action == q.candidate.action)) visit then return true
  if ← tryStage space prepared #[.rules, .library, .forward]
      (fun _ => true) visit then return true
  tryStage space prepared #[.functions, .induction]
    (fun c => c.move.induction == .none) visit

public def hooks (inner : Hooks := {})
    (activate : List MVarId → TacticM Bool := fun _ => pure true) : Hooks := { inner with
  policy := ⟨State, (), fun space =>
    if space.root.origin == .prelude then
      choose space (space.root.trialTag == `constructorExposure)
    else space.expand 0 #[] (fun _ => true)⟩
  -- In a branching search, the depth supported by a node budget grows
  -- logarithmically. This budget-derived contour bounds attractive wrong
  -- branches without reinstating a feature-specific magic depth. Both finite
  -- contours share the engine's quarter-effort reserve and ambient heartbeat cap.
  prelude := fun cfg goals => do
    let scheduled := if ← activate goals then
      #[{ depth := depthForEffort cfg.effort, attempts := 64 },
        { tag := `constructorExposure, depth := depthForEffort cfg.effort, attempts := 64 }] else #[]
    return scheduled ++ (← inner.prelude cfg goals)
}

end waterfall.RecursionScheduling
