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

/-- Install context-dependent critics in one operation group. The factory sees
the same supplied rules, strength and remaining depth as ordinary generators.
It chooses providers, not search order; existing moves retain their selectors.
For interleaving repairs with individual basic operations, call `propose` at the
required generation point instead of appending a second copy through hooks. -/
public def Critic.hooksFor (group : Group)
    (critics : Array (TSyntax `term) → Nat → Nat → Array Critic)
    (inner : Hooks := {}) : Hooks := { inner with
  extraMoves := fun goal rules strength remaining requested => do
    let original ← inner.extraMoves goal rules strength remaining requested
    if requested != group then return original
    let mut moves := original
    for critic in critics rules strength remaining do
      moves := moves ++ (← (critic.propose goal).collect)
    return moves }

/-- A fixed set of providers, normally in the hypotheses group. Materialization
happens at this adapter; critics own no traversal or resource accounting. -/
public def Critic.hooks (critics : Array Critic) (inner : Hooks := {})
    (group : Group := .hypotheses) : Hooks :=
  Critic.hooksFor group (fun _ _ _ => critics) inner

end waterfall
