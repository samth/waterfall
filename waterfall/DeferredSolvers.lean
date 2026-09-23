module
public import waterfall.Core

meta section
open Lean Meta Elab Tactic
namespace waterfall.DeferredSolvers

public register_option waterfall.deferSolvers : Bool := {
  defValue := false, descr := "Experimental deferred inference scheduling" }
public register_option waterfall.cheapSolverDivisor : Nat := {
  defValue := 8, descr := "Cheap solver slice divisor; zero disables cheap copies" }
public register_option waterfall.solverCost : Nat := {
  defValue := 1, descr := "Path cost of full solver calls" }

/-- Classify inference by its operation metadata, including simplification
that leaves subgoals rather than closing them. No theorem names are inspected. -/
private def expensive (move : Move) : Bool :=
  move.heartbeatDivisor == 1 &&
    (move.closure == .simplification || move.closure == .saturation ||
      move.preparation == .normalization)

/-- Add independently backtrackable bounded calls. A timeout rejects only that
alternative. Ordinary full-strength calls retain their original selectors.
The target simplifier also uses local hypotheses, but does not normalize them. -/
private def cheapMoves (g : MVarId) (rules : Array (TSyntax `term))
    (strength remaining divisor : Nat) (group : Group) : TacticM (Array Move) := do
  if divisor == 0 || group != .close then return #[]
  -- Earlier, cheaper contours try bounded calls at their frontier. Once the
  -- full operation fits, dispatch it directly instead of paying for both.
  if remaining >= waterfall.solverCost.get (← getOptions) then return #[]
  let original ← movesFor g rules strength remaining group
  let copies := original.filterMap fun move =>
    if move.closure == .simplification || move.closure == .saturation then
      some { move with
        heartbeatDivisor := max 2 divisor
        label := "bounded " ++ move.label, role := `boundedSolver }
    else none
  let rs ← rules.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let steps := quote (Simp.defaultMaxSteps * strength)
  let discharge := quote (({} : Simp.Config).maxDischargeDepth + Nat.log2 strength / 2)
  let command ← `(tactic| (simp (config := {maxSteps := $steps, maxDischargeDepth := $discharge}) [*, $rs,*]; done))
  return #[{
    cost := 0, label := "bounded target simp", closure := .simplification,
    heartbeatDivisor := max 2 divisor, role := `boundedSolver,
    command? := some command, run := evalTactic command }] ++ copies

/-- Middleware retains the existing critics, induction ordering, and specialized
prelude continuations. The same traversal uses positive full-solver costs and cheap-first ordering. -/
public def hooks (inner : Hooks) : Hooks := { inner with
  order := fun g span candidates => do
    let prior ← inner.order g span candidates
    if !(waterfall.deferSolvers.get (← getOptions)) then return prior
    let ordered ← match prior with
      | none => pure candidates
      | some ids => ids.mapM fun id => do
        let some candidate := candidates.find? (·.action == id)
          | throwError "unknown ordering selector"
        pure candidate
    let exact := ordered.filter (fun c => c.move.closure == .exact || c.move.closure == .arithmetic)
    let rest := ordered.filter (fun c => c.move.closure != .exact && c.move.closure != .arithmetic)
    return some ((exact ++ rest.filter (fun c => c.move.heartbeatDivisor > 1) ++
      rest.filter (fun c => c.move.heartbeatDivisor == 1)).map (·.action))
  cost := fun g span candidate => do
    let original ← inner.cost g span candidate
    if waterfall.deferSolvers.get (← getOptions) && expensive candidate.move then
      return max original (waterfall.solverCost.get (← getOptions))
    return original
  extraMoves := fun g rules strength remaining group => do
    let original ← inner.extraMoves g rules strength remaining group
    if !(waterfall.deferSolvers.get (← getOptions)) then return original
    return original ++ (← cheapMoves g rules strength remaining
      (waterfall.cheapSolverDivisor.get (← getOptions)) group) }

end waterfall.DeferredSolvers
