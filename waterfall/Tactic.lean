module
public import waterfall.Parallel
public import waterfall.Committed
public import waterfall.Critics
public import waterfall.Scheduling
public import waterfall.Continuations
public import waterfall.Suggestions
public import waterfall.Premises

meta section

/-! # The `waterfall` tactic

`waterfall [definitions, lemmas]` searches for a complete proof. Standard Lean
configuration items select effort, enumeration and search behavior. Import
`waterfall.Observe` separately for timing, action recording and plan replay.
-/

open Lean Elab Tactic Parser.Tactic
namespace waterfall

/-- Two configurations of the same proof engine. `committed` discards alternatives
after local progress; `search` retains backtracking over the full continuation. -/
public inductive Mode where
  | search
  | committed
  deriving Inhabited, BEq, Repr

/-- The standard callbacks for a mode, available for programmatic adaptation.
`leafLemmas` are candidate lemmas for the `simp` closer (see `Hooks.leafLemmas`). -/
public def Mode.hooks (mode : Mode) (rules : Array (TSyntax `term) := #[])
    (leafLemmas : Array Name := #[]) : Hooks :=
  match mode with
  | .search => Continuations.hooks rules <| Critics.hooks
      (InductionPlan.hooks
        (Scheduling.preparations (RecursionScheduling.hooks (inner := { leafLemmas })
          (activate := fun goals => do
            return (← Scheduling.exposesMoves Critics.propose goals) ||
              (← RecursionScheduling.needsRecursionPrelude goals)))
          (Scheduling.exposesMoves Critics.propose)))
  | .committed => Critics.hooks (Scheduling.preparations { Committed.hooks with leafLemmas })

/-- User-facing tactic options. The inherited `Config` fields control resources
and enumeration. For custom search, ordering, costs and observation, adapt
`Mode.hooks` and pass the callbacks to `waterfall.run`. -/
public structure Options extends Config where
  /-- Backtracking search by default; commitment is an explicit choice. -/
  mode : Mode := .search
  /-- Maximum concurrent workers. One uses the original sequential traversal.
  Effort and ambient heartbeats remain aggregate limits across all workers. -/
  cpus : Nat := 1
  /-- Consider up to this many of the most relevant earlier theorems of the current
  module as `simp` lemmas. Relevance is the constants a theorem's statement shares
  with the goals. At each node the `simp` closer tries them, restricted to those
  relevant to that node, only after its ordinary simplifier fails. Off by default:
  the extra simplifier calls cost heartbeats, and a closure they find changes the
  order of the search, so a proof found without them can be lost. -/
  premises : Nat := 0

declare_config_elab elabOptions Options

/-- Search for a complete Lean proof using simplification, theorem application,
case splitting and induction. Examples:
```
waterfall
waterfall (effort := 3000) [myDefinition, helper]
waterfall (mode := .committed) (effort := 3000) [myDefinition]
```
Every successful proof is checked by Lean. Failure restores the input proof state.
`effort` counts attempted operations globally, including failed branches.
-/
syntax (name := waterfallTac) "waterfall" optConfig (" [" term,* "]")? : tactic

/-- Like `waterfall`, with a checked editor suggestion containing ordinary Lean
proof commands. Use `(report := true)` to also print search statistics. -/
syntax (name := waterfallReportTac) "waterfall?" optConfig (" [" term,* "]")? : tactic

/-- The most relevant earlier theorems for a call. -/
private def leafPremises (options : Options) : TacticM (Array Name) := do
  let names ← Premises.select (← getUnsolvedGoals) options.premises
  if options.report && !names.isEmpty then
    logInfo m!"PREMISES {names.size} candidate lemmas: {names.toList}"
  return names

private def execute (options : Options) (rules : Array (TSyntax `term)) : TacticM Unit := do
  let leafLemmas ← leafPremises options
  discard <| Parallel.run options.cpus options.toConfig rules
    (fun use => use (options.mode.hooks rules leafLemmas))

elab_rules : tactic
  | `(tactic| waterfall $cfg:optConfig $[[$rules,*]]?) => do
    execute (← elabOptions cfg) (rules.map (·.getElems) |>.getD #[])
  | `(tactic| waterfall? $cfg:optConfig $[[$rules,*]]?) => do
    let options ← elabOptions cfg
    let rules := rules.map (·.getElems) |>.getD #[]
    let ref ← getRef
    let leafLemmas ← leafPremises options
    discard <| Parallel.run options.cpus options.toConfig rules
      (Suggestions.run ref rules (options.mode.hooks rules leafLemmas))

end waterfall
