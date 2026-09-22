module
public import waterfall.Protocol

meta section

/-!
Typed induction plans, kept separate from proof traversal. Goal analysis builds
these values, this module removes only literal duplicates and orders them, and
the engine later executes the retained `Move` in its restored checkpoint.
-/

open Lean Meta
namespace waterfall.InductionPlan

/-- A local induction proposal plus its stable analysis. `ordinal` preserves
generator order when two schemes have the same structural quality. -/
public structure Plan where
  move : Move
  summary : InductionSummary
  ordinal : Nat

private def sameSubject (a b : Option Expr) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => x == y
  | _, _ => false

/-- Conservative identity: deletion is allowed only when execution-relevant
scheme and motive data agree. Heuristic dominance is ordering only. -/
public def equivalent (a b : Plan) : Bool :=
  a.move.induction == b.move.induction &&
  a.move.motive == b.move.motive &&
  a.move.generalization == b.move.generalization &&
  a.move.major == b.move.major &&
  a.move.role == b.move.role &&
  a.move.label == b.move.label &&
  sameSubject a.move.subject b.move.subject &&
  a.summary == b.summary

public def deduplicate (plans : Array Plan) : Array Plan :=
  plans.foldl (fun kept plan =>
    if kept.any (equivalent plan) then kept else kept.push plan) #[]

private def motivePenalty : InductionMotive → Nat
  | .direct => 0
  | .indexAbstraction => 1
  | .localGeneralization => 2
  | .localGeneralizationAndIndexAbstraction => 3

/-- ACL2-style quality key. Greater recursive-call coverage wins; extra
generalization, fixed-index work, and cases are increasingly costly. No plan is
discarded because these dominance judgments are heuristic. -/
public def quality (plan : Plan) : Nat × Nat × Nat × Nat × Nat :=
  (plan.summary.coveredCalls,
    motivePenalty plan.move.motive,
    plan.summary.generalized,
    plan.summary.abstractedIndices,
    plan.summary.expectedCases)

public def ordered (plans : Array Plan) : Array Plan :=
  (deduplicate plans).qsort fun a b =>
    let ka := quality a
    let kb := quality b
    if ka.1 != kb.1 then ka.1 > kb.1
    else if ka.2.1 != kb.2.1 then ka.2.1 < kb.2.1
    else if ka.2.2.1 != kb.2.2.1 then ka.2.2.1 < kb.2.2.1
    else if ka.2.2.2.1 != kb.2.2.2.1 then ka.2.2.2.1 < kb.2.2.2.1
    else if ka.2.2.2.2 != kb.2.2.2.2 then ka.2.2.2.2 < kb.2.2.2.2
    else a.ordinal < b.ordinal

/-- Attach the public summary while retaining the rollback-local executor. -/
public def toMoves (plans : Array Plan) : Array Move :=
  plans.map fun plan => { plan.move with inductionSummary := some plan.summary }

private def strictlyCovers (a b : InductionSummary) : Bool :=
  a.coveredCalls > b.coveredCalls &&
    b.changingArguments.all fun position => a.changingArguments.contains position

/-- A conservative ACL2-style preference between generated candidates. It
requires the same induction kind, more covered calls, and no lost changing
argument position. -/
public def dominates (a b : Candidate) : Bool :=
  a.move.induction != .functional && a.move.induction == b.move.induction &&
    match a.move.inductionSummary, b.move.inductionSummary with
    | some sa, some sb => strictlyCovers sa sb
    | _, _ => false

private def dominance (candidates : Array Candidate) (candidate : Candidate) : Nat :=
  if candidate.move.induction == .functional then 0 else
  candidates.foldl (init := 0) fun score other =>
    if dominates candidate other then score + 1 else score

private def hasBroadGeneralization (candidates : Array Candidate)
    (candidate : Candidate) : Bool :=
  match candidate.move.inductionSummary with
  | none => false
  | some summary => candidates.any fun other =>
      other.move.induction == candidate.move.induction &&
        other.move.inductionSummary.any fun otherSummary =>
          otherSummary.coveredCalls == summary.coveredCalls &&
          otherSummary.changingArguments == summary.changingArguments &&
          otherSummary.generalized > 1

private def lessCandidate (candidates : Array Candidate)
    (a b : Candidate × Nat) : Bool :=
  let da := dominance candidates a.1
  let db := dominance candidates b.1
  if da != db then da > db
  else
    let ma := if da > 0 && hasBroadGeneralization candidates a.1 then
      motivePenalty a.1.move.motive else 0
    let mb := if db > 0 && hasBroadGeneralization candidates b.1 then
      motivePenalty b.1.move.motive else 0
    if ma != mb then ma < mb else a.2 < b.2

/-- Reorder only the induction slots in another policy's permutation. A scheme
is dominant only when it covers more calls and contains every changing argument
position of another scheme. Functional schemes retain their generator order.
Direct motives lead only when the alternative would broadly generalize multiple
locals; a focused one-variable strengthening retains generator order. This
general middleware adapter neither chooses a traversal nor removes a
heuristically dominated scheme. -/
public def hooks (inner : Hooks := {}) : Hooks := { inner with
  order := fun g span candidates => do
    let requested ← inner.order g span candidates
    let ordered ← match requested with
      | none => pure candidates
      | some actions => actions.mapM fun action => do
          let some candidate := candidates.find? (·.action == action)
            | throwError "induction planner received an unknown ordered action"
          return candidate
    let plans := ordered.mapIdx (fun i candidate => (candidate, i))
      |>.filter (·.1.move.inductionSummary.isSome)
      |>.qsort (lessCandidate ordered)
      |>.map (·.1)
    let mut nextPlan := 0
    let mut result := #[]
    for candidate in ordered do
      if candidate.move.inductionSummary.isSome then
        let some selected := plans[nextPlan]?
          | throwError "induction planner lost a plan slot"
        nextPlan := nextPlan + 1
        result := result.push selected
      else result := result.push candidate
    return some (result.map (·.action)) }

end waterfall.InductionPlan
