import waterfall
open Lean Meta Elab Tactic Parser.Tactic waterfall

/-!
An opt-in experiment in functional-induction continuation search. Each grounded
root scheme gets a finite contour and a direct motive, while nested induction
keeps the existing generalized alternative. The ordinary engine owns rollback,
proof validation, and the aggregate quarter-effort reserve. This module is not
imported by `waterfall` and does not change its default search.
-/
namespace waterfall.InductionContinuations

def plans (g : MVarId) (rules : Array (TSyntax `term)) : TacticM (Array Move) := g.withContext do
  let moves ← movesFor g rules 1 12 .functions
  let selected ← moves.filterM fun m => do
    unless m.induction == .functional do return false
    let some call := m.subject | return false
    let .const n _ := call.getAppFn | return false
    let some info ← getFunIndInfo? false false n | return false
    let args := call.getAppArgs
    unless args.size == info.params.size do return false
    let targets := (args.zip info.params).filter (fun (_, k) => k == .target)
    return !targets.isEmpty && targets.all (fun (a, _) => a.isFVar)

  return selected

def rootPlans (g : MVarId) (rules : Array (TSyntax `term)) : TacticM (Array Move) := g.withContext do
  let ps ← plans g rules
  let ranked ← ps.mapIdxM fun i m => do
    let call := m.subject.get!
    let .const n _ := call.getAppFn | return (m, 0, i)
    let some info ← getFunIndInfo? false false n | return (m, 0, i)
    let mut score := 0
    for (arg, kind) in call.getAppArgs.zip info.params do
      if kind != .target then continue
      let .const tn _ := (← whnf (← inferType arg)).getAppFn | continue
      let some (.inductInfo ti) := (← getEnv).find? tn | continue
      if ti.isRec then score := score + 1
    return (m, score, i)
  return (ranked.qsort fun a b => a.2.1 > b.2.1 ||
    (a.2.1 == b.2.1 && a.2.2 < b.2.2)).map (·.1)

def hooks (rules : Array (TSyntax `term)) : Hooks := Id.run do
  let base := Mode.search.hooks
  return { base with
    extraMoves := fun g rules strength remaining group => do
      let baseMoves ← base.extraMoves g rules strength remaining group
      if group != .functions then return baseMoves
      let direct ← (← plans g rules).mapM fun m => g.withContext do
        let some call := m.subject | throwError "missing subject"
        let exprSyntax ← PrettyPrinter.delab call
        let command ← `(tactic| fun_induction $exprSyntax)
        return { m with
          role := `directFunction
          command? := some command
          run := g.withContext do
            let exprSyntax ← Term.exprToSyntax call
            evalTactic (← `(tactic| fun_induction $exprSyntax)) }
      return baseMoves ++ direct
    prelude := fun cfg goals => do
      if goals.length != 1 then return ← base.prelude cfg goals
      let mut trials : Array PreludeTrial := #[]
      for g in goals do
        let ps ← rootPlans g (← prepareRules g rules)
        for i in [:ps.size] do
          trials := trials.push {
            tag := Name.num `inductionContinuations i
            depth := Scheduling.depthForEffort cfg.effort + 2,
            attempts := cfg.effort / (4 * max 1 ps.size)}
      return trials
    policy := { base.policy with choose := fun space => fun visit => do
      let .num `inductionContinuations idx := space.root.trialTag |
        base.policy.choose space visit
      let some prepared ← space.prepare space.current 0 | return false
      let job := (prepared.source.jobs[prepared.focus]!)
      if job.ancestors.isEmpty then
        let ps ← rootPlans job.goal prepared.rules
        let some chosen := ps[idx]? | return false
        return ← space.propose prepared #[#[.functions]]
          (fun c => c.move.induction == .functional && c.move.subject == chosen.subject && c.move.role == `directFunction)
          fun proposal => space.execute proposal visit
      if ← space.propose prepared #[#[.close]] (fun _ => true)
          (fun p => space.execute p visit) then return true
      if ← space.propose prepared #[#[.basic]]
          (fun c => c.move.preparation == .allBinders || c.move.preparation == .normalization)
          (fun p => space.execute p visit) then return true
      let ps ← plans job.goal prepared.rules
      if (job.ancestors.filter (·.move.induction == .functional)).length >= 2 then
        return ← space.expand 0 #[] (fun c => c.move.induction == .none) visit
      if ← space.propose prepared #[#[.functions]]
          (fun c => ps.any (fun p => p.subject == c.move.subject) && c.move.induction == .functional &&
            !job.ancestors.any (fun a => a.move.subject == c.move.subject))
          (fun p => space.execute p visit) then return true
      space.expand 0 #[] (fun _ => true) visit } }

declare_config_elab elabContinuationConfig Config
syntax (name := continuationTac) "waterfall_induction" optConfig
  " [" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| waterfall_induction $cfg:optConfig [$rs,*]) => do
    discard <| run (← elabContinuationConfig cfg) rs.getElems (hooks rs.getElems)
end waterfall.InductionContinuations
