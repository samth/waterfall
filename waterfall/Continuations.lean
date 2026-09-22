module
public import waterfall.RecursionScheduling

meta section

/-!
Bounded induction continuations. Root schemes retain fixed parameters; two
finite contours try constructor exposure and normalization in different orders.
Nested residual problems may discard foreign recursive premises before induction.
The engine owns all rollback, proof validation and aggregate resource budgets.
-/
open Lean Meta Elab Tactic Parser.Tactic

namespace waterfall.Continuations

private def plans (g : MVarId) (rules : Array (TSyntax `term)) : TacticM (Array Move) := g.withContext do
  let moves ← movesFor g rules 2 12 .functions
  let selected ← moves.filterM fun m => do
    unless m.induction == .functional && m.role == `directFunction do return false
    let some call := m.subject | return false
    let .const n _ := call.getAppFn | return false
    let some info ← getFunIndInfo? false false n | return false
    let args := call.getAppArgs
    unless args.size == info.params.size do return false
    let targets := (args.zip info.params).filter (fun (_, k) => k == .target)
    return !targets.isEmpty && targets.all (fun (a, _) => a.isFVar)

  return selected

private def rootPlans (g : MVarId) (rules : Array (TSyntax `term)) : TacticM (Array Move) := g.withContext do
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

public def hooks (rules : Array (TSyntax `term)) (base : Hooks := {}) : Hooks := Id.run do
  return { base with
    extraMoves := fun g rules strength remaining group => do
      let original ← base.extraMoves g rules strength remaining group
      if group != .close || strength <= 1 then return original
      -- More structural alternatives need not force more eager saturation.
      -- Keep the cheap leaf configuration available inside the deeper contour.
      return original ++ (← movesFor g rules 1 remaining .close).map
        (fun m => {m with role := `continuationClose})
    prelude := fun cfg goals => do
      -- Preserve the ordinary default-budget search. Extra effort buys the
      -- deeper continuation portfolio, rather than taking its budget away.
      if goals.length != 1 || cfg.effort <= ({} : Config).effort then
        return ← base.prelude cfg goals
      -- A deeper contour needs room for several operations, not just more
      -- attempts. Do not spend a small declaration budget on a portfolio whose
      -- quarter-budget reserve cannot cover one ordinary slice per depth step.
      let depth := Scheduling.depthForEffort cfg.effort + 2
      let ctx ← readThe Core.Context
      let remaining := ctx.initHeartbeats + ctx.maxHeartbeats - (← IO.getNumHeartbeats)
      if ctx.maxHeartbeats != 0 && remaining / 4 < cfg.attemptHeartbeats * depth then
        return ← base.prelude cfg goals
      let mut trials : Array PreludeTrial := #[]
      for g in goals do
        let ps ← rootPlans g (← prepareRules g rules)
        for i in [:2 * ps.size] do
          trials := trials.push {
            tag := Name.num `inductionContinuations i
            depth := depth, strength := 2,
            attempts := cfg.effort / (8 * max 1 ps.size)}
      let legacy := if trials.isEmpty then #[] else
        #[{tag := `continuationLegacy, depth := 2, attempts := cfg.effort / 10}]
      return (← base.prelude cfg goals) ++ legacy ++ trials
    policy := { base.policy with choose := fun space => fun visit => do
      if space.root.trialTag == `continuationLegacy then
        return ← space.expand 0 #[] (fun _ => true) visit
      let .num `inductionContinuations idx := space.root.trialTag | do
        let ordinary := { space with
          expand := fun focus groups admit => space.expand focus groups
            (fun c => admit c && c.move.role != `continuationClose)
          propose := fun prepared groups admit => space.propose prepared groups
            (fun c => admit c && c.move.role != `continuationClose) }
        base.policy.choose ordinary visit
      let some prepared ← space.prepare space.current 0 | return false
      let job := (prepared.source.jobs[prepared.focus]!)
      if job.ancestors.isEmpty then
        let ps ← rootPlans job.goal prepared.rules
        let some chosen := ps[idx / 2]? | return false
        return ← space.propose prepared #[#[.functions]]
          (fun c => c.move.induction == .functional && c.move.subject == chosen.subject && c.move.role == `directFunction)
          fun proposal => space.execute proposal visit
      if ← space.propose prepared #[#[.close]] (fun c => c.move.role == `continuationClose && c.move.closure != .saturation)
          (fun p => space.execute p visit) then return true
      if ← space.propose prepared #[#[.close]] (fun c => c.move.role == `continuationClose && c.move.closure == .saturation)
          (fun p => space.execute p visit) then return true
      if ← space.propose prepared #[#[.basic]]
          (fun c => c.move.preparation == .allBinders)
          (fun p => space.execute p visit) then return true
      let expose := space.propose prepared #[#[.induction]]
          (fun c => c.move.induction == .none &&
            (c.move.role == `blockedMatch || c.move.role == `constructorField) &&
            (job.ancestors.filter (fun a => a.move.induction == .none && a.move.major.isSome)).length < 2 &&
            !job.ancestors.any (fun a => a.move.induction == .none && a.move.major == c.move.major))
          (fun p => space.execute p visit)
      if idx % 2 == 0 then
        if ← expose then return true
      if ← space.propose prepared #[#[.basic]]
          (fun c => c.move.preparation == .normalization || c.move.preparation == .targetSplit)
          (fun p => space.execute p visit) then return true
      if ← space.propose prepared #[#[.rules]]
          (fun c => c.move.role == `targetConstructor)
          (fun p => space.execute p visit) then return true
      if ← space.propose prepared #[#[.forward]]
          (fun c => c.move.role == `combine &&
            !job.ancestors.any (fun a => a.move.role == `combine && a.move.major == c.move.major))
          (fun p => space.execute p visit) then return true
      if ← space.propose prepared #[#[.hypotheses]]
          (fun c => c.move.role == `conjunction)
          (fun p => space.execute p visit) then return true
      if (job.ancestors.filter (·.move.induction == .functional)).length < 3 then
        for role in [`prunedFunction, `directFunction] do
          if ← space.propose prepared #[#[.functions]]
              (fun c => c.move.induction == .functional && c.move.role == role &&
                !job.ancestors.any (fun a => a.move.subject == c.move.subject))
              (fun p => space.execute p visit) then return true
      if idx % 2 == 1 then
        if ← expose then return true
      space.propose prepared #[#[.basic]]
          (fun c => c.move.role == `recursiveRewrite ||
            ((c.move.role == `generalization || c.move.role == `jointGeneralization) &&
              !job.ancestors.any (fun a => a.move.role == `generalization || a.move.role == `jointGeneralization)))
          (fun p => space.execute p visit) } }


end waterfall.Continuations
