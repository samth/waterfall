module
public import waterfall.Parallel
public import waterfall.Committed
public import waterfall.Critics
public import waterfall.Scheduling
public import waterfall.Suggestions

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

/-- The standard callbacks for a mode, available for programmatic adaptation. -/
public def Mode.hooks : Mode → Hooks
  | .search => Critics.hooks
      (InductionPlan.hooks
        (Scheduling.hooks (activate := Scheduling.exposesMoves Critics.propose)))
  | .committed => Critics.hooks (Scheduling.preparations Committed.hooks)

/-- User-facing tactic options. The inherited `Config` fields control resources
and enumeration. For custom search, ordering, costs and observation, adapt
`Mode.hooks` and pass the callbacks to `waterfall.run`. -/
public structure Options extends Config where
  /-- Backtracking search by default; commitment is an explicit choice. -/
  mode : Mode := .search
  /-- Maximum concurrent workers. One uses the original sequential traversal.
  Effort and ambient heartbeats remain aggregate limits across all workers. -/
  cpus : Nat := 1

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

private def execute (options : Options) (rules : Array (TSyntax `term)) : TacticM Unit := do
  discard <| Parallel.run options.cpus options.toConfig rules (fun use => use options.mode.hooks)

elab_rules : tactic
  | `(tactic| waterfall $cfg:optConfig $[[$rules,*]]?) => do
    execute (← elabOptions cfg) (rules.map (·.getElems) |>.getD #[])
  | `(tactic| waterfall? $cfg:optConfig $[[$rules,*]]?) => do
    let options ← elabOptions cfg
    let rules := rules.map (·.getElems) |>.getD #[]
    let ref ← getRef
    discard <| Parallel.run options.cpus options.toConfig rules
      (Suggestions.run ref rules options.mode.hooks)

end waterfall
