module
public import waterfall.Choices

meta section

/-!
A critic observes a proof obstruction and proposes repairs. Its evidence type is
private to that critic: adding a new analysis never extends an engine-wide sum
type. Observations and repair construction run under rollback; only the returned
moves may change the proof, when the ordinary engine executes them.

Evidence and moves must refer only to values valid in the input checkpoint.
In particular, an applicability probe must instantiate its temporary metavariables
before returning evidence, or record a recipe that reconstructs them on execution.
-/

open Lean Meta Elab Tactic
namespace waterfall

/-- Typed obstruction analysis followed by independently executable repairs. -/
public structure Critic where
  Evidence : Type
  observe : MVarId → TacticM (Array Evidence)
  repair : MVarId → Evidence → TacticM (Array Move)

private def observing (action : TacticM α) : TacticM α := do
  let saved ← Tactic.saveState
  try action finally saved.restore true

/-- Repair construction is delayed until its observation is visited. Consumers
may stop early, combine producers, or explicitly materialize them for ordering. -/
public def Critic.propose (critic : Critic) (goal : MVarId) : Choices Move := fun visit => do
  let evidence ← observing <| goal.withContext <| critic.observe goal
  for obstruction in evidence do
    let moves ← observing <| goal.withContext <| critic.repair goal obstruction
    for move in moves do
      if ← visit move then return true
  return false

/-- The existing engine orders finite batches. Materialization happens only at
this adapter; critics themselves have no policy, trial or execution callback. -/
public def Critic.hooks (critics : Array Critic) (inner : Hooks := {}) : Hooks := { inner with
  extraMoves := fun goal rules strength remaining group => do
    let original ← inner.extraMoves goal rules strength remaining group
    if group != .hypotheses then return original
    let mut moves := original
    for critic in critics do
      moves := moves ++ (← (critic.propose goal).collect)
    return moves }

end waterfall
