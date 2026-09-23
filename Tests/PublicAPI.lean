module
import waterfall
import waterfall.Canonical
import waterfall.Choices
import waterfall.Committed
import waterfall.Core
import waterfall.Critics
import waterfall.FocusingCritics
import waterfall.ArithmeticWitness
import waterfall.ConstructorCritics
import waterfall.InductionCritics
import waterfall.Induction
import waterfall.InductionPlan
import waterfall.Observe
import waterfall.Operations
import waterfall.Parallel
import waterfall.Protocol
import waterfall.Repair
import waterfall.Suggestions
import waterfall.Scheduling

open Lean Elab Command

-- This list is the supported declaration-level interface. Most entries are
-- exercised behaviorally elsewhere; keeping the complete inventory here makes
-- module visibility changes deliberate.
run_cmd do
  for name in [
      `waterfall.Config, `waterfall.Stats, `waterfall.Group,
      `waterfall.structuralGroups, `waterfall.InductionKind,
      `waterfall.PreparationKind, `waterfall.ClosureKind, `waterfall.InductionMotive,
      `waterfall.InductionSummary,
      `waterfall.ForwardInstantiation, `waterfall.Move,
      `waterfall.Move.applicable, `waterfall.ActionId, `waterfall.Candidate,
      `waterfall.Phase, `waterfall.Span, `waterfall.Outcome,
      `waterfall.Selection, `waterfall.Choices, `waterfall.Job, `waterfall.TrialOrigin,
      `waterfall.Node, `waterfall.Prepared, `waterfall.Proposal,
      `waterfall.Space, `waterfall.SearchPolicy,
      `waterfall.SearchPolicy.default, `waterfall.PreludeTrial,
      `waterfall.diagonalTrials,
      `waterfall.Hooks, `waterfall.Hooks.bool, `waterfall.Hooks.array,
      `waterfall.Canonical.snapshot,
      `waterfall.Choices.first, `waterfall.Choices.filter,
      `waterfall.Choices.map, `waterfall.Choices.append,
      `waterfall.Choices.collect, `waterfall.Node.mapState,
      `waterfall.Proposal.mapState,
      `waterfall.Committed.State, `waterfall.Committed.choose,
      `waterfall.Committed.hooks,
      `waterfall.movesFor, `waterfall.prepareRules, `waterfall.operations,
      `waterfall.Critic, `waterfall.Critic.propose, `waterfall.Critic.hooks,
      `waterfall.Critic.hooksFor,
      `waterfall.Critics.propose, `waterfall.Critics.blockedPremise, `waterfall.Critics.blockedPremises,
      `waterfall.Critics.quantifiedRewrite, `waterfall.Critics.indexedFocus,
      `waterfall.Critics.arithmeticWitness,
      `waterfall.Critics.implicitWitnesses, `waterfall.Critics.fixedIndices,
      `waterfall.Induction.perform, `waterfall.Induction.withPlan, `waterfall.Induction.command,
      `waterfall.Generalization.Abstraction, `waterfall.Generalization.Plan,
      `waterfall.Generalization.Prepared, `waterfall.Generalization.prepare,
      `waterfall.Generalization.commands,
      `waterfall.Critics.inductionMotives, `waterfall.Critics.functionalInduction,
      `waterfall.Critics.hooks,
      `waterfall.InductionPlan.Plan, `waterfall.InductionPlan.equivalent,
      `waterfall.InductionPlan.deduplicate, `waterfall.InductionPlan.quality,
      `waterfall.InductionPlan.ordered, `waterfall.InductionPlan.toMoves,
      `waterfall.InductionPlan.dominates,
      `waterfall.InductionPlan.hooks,
      `waterfall.Scheduling.State, `waterfall.Scheduling.depthForEffort,
      `waterfall.Scheduling.preparations, `waterfall.Scheduling.choose, `waterfall.Scheduling.exposesMoves, `waterfall.Scheduling.hooks,
      `waterfall.attempt, `waterfall.prepareProposals, `waterfall.proposePrepared,
      `waterfall.propose, `waterfall.executeProposal,
      `waterfall.expand, `waterfall.checkComplete,
      `waterfall.run,
      `waterfall.Observe.Cost, `waterfall.Observe.Row,
      `waterfall.Observe.Step, `waterfall.Observe.Plan,
      `waterfall.Observe.Report, `waterfall.Observe.Control,
      `waterfall.Observe.Control.around, `waterfall.Observe.Recorder,
      `waterfall.Observe.Recorder.create, `waterfall.Observe.Recorder.hooks,
      `waterfall.Observe.capture, `waterfall.Observe.replay,
      `waterfall.Parallel.run,
      `waterfall.Suggestions.Path, `waterfall.Suggestions.Script,
      `waterfall.Suggestions.compile, `waterfall.Suggestions.run,
      `waterfall.Mode, `waterfall.Mode.hooks, `waterfall.Options] do
    unless (← getEnv).contains name do
      throwError "missing public declaration: {name}"

  for name in [
      `waterfall.Canonical.node, `waterfall.simplification,
      `waterfall.Observe.Frame, `waterfall.Observe.Recorder.around,
      `waterfall.Parallel.fork, `waterfall.Suggestions.command,
      `waterfall.execute, `waterfall.elabOptions] do
    if (← getEnv).contains name then
      throwError "unexpected implementation declaration: {name}"

-- A module consumer can use the same facade and tactic as an ordinary source
-- file. Tests.Import covers the ordinary-file side of this compatibility.
example (P : Prop) (h : P) : P := by waterfall
