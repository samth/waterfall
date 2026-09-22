import waterfall
open Lean Elab Tactic Parser.Tactic waterfall

/-! The original opt-in induction experiment now uses the integrated search.
Historical measurements refer to the earlier pinned implementation. -/
namespace waterfall.InductionContinuations

def hooks (rules : Array (TSyntax `term)) : Hooks := Mode.search.hooks rules

declare_config_elab elabContinuationConfig Config
syntax (name := continuationTac) "waterfall_induction" optConfig
  " [" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| waterfall_induction $cfg:optConfig [$rs,*]) => do
    discard <| run (← elabContinuationConfig cfg) rs.getElems (hooks rs.getElems)
end waterfall.InductionContinuations
