module
public import waterfall.Continuations
public import waterfall.Critics

meta section

/-! A bounded final trial coordinates functional induction, interface reduction,
and cases at blocked computations. All moves use the ordinary search engine;
failed work remains charged and every original goal must close. -/
open Lean Meta Elab Tactic Parser.Tactic
namespace waterfall.Coordination

private def blockedMajors (term : Expr) (fuel : Nat := 8) : MetaM (Array Expr) := do
  let fuel + 1 := fuel | return #[]
  withOptions (fun o => o.setBool `smartUnfolding false) do
    let reduced ← withTransparency .default <| whnf term
    if let some matcher ← matchMatcherApp? reduced (alsoCasesOn := true) then
      return matcher.discrs
    if let .const n _ := reduced.getAppFn then
      if let some (.recInfo info) := (← getEnv).find? n then
        if let some major := reduced.getAppArgs[info.getMajorIdx]? then return #[major]
    if let .proj _ _ base := reduced then return ← blockedMajors base fuel
    return #[]

/-- Observe the recursor hidden by a stuck recursive call. Smart unfolding
normally keeps such calls folded. Its temporary disabling affects observation
only; proof-state normalization remains a separately checked engine move. -/
private def exposedConsumer (term : Expr) (fuel : Nat := 8) : MetaM Bool := do
  let fuel + 1 := fuel | return false
  if !(← blockedMajors term).isEmpty then return true
  -- Course-of-values recursion projects its result from a recursor pair.
  if let .proj _ _ base := (← withTransparency .default <| whnf term) then
    return ← exposedConsumer base fuel
  return false

private def hasBlockedConsumer (g : MVarId) : MetaM Bool :=
  withoutModifyingState <| g.withContext do
    withOptions (fun o => o.setBool `smartUnfolding false) do
      for term in ← Recursion.contextApplications g do
        unless term.hasLooseBVars || term.hasMVar do
          if ← exposedConsumer term then return true
      return false

/-- Case analysis is directed at an actual blocked matcher or recursor,
including the ones exposed by weak-head reduction of supplied definitions. -/
private def blockedComputations : Critic := {
  Evidence := FVarId
  observe := fun g => do
    let mut out := #[]
    for term in ← Recursion.contextApplications g do
      if term.hasLooseBVars || term.hasMVar then continue
      let reduced ← withTransparency .default <| whnf term
      let mut majors := #[]
      if let some matcher ← matchMatcherApp? reduced (alsoCasesOn := true) then
        majors := matcher.discrs
      else if let .const n _ := reduced.getAppFn then
        if let some (.recInfo info) := (← getEnv).find? n then
          if let some major := reduced.getAppArgs[info.getMajorIdx]? then
            majors := #[major]
      for major in majors do
        let .const tn _ := (← whnf (← inferType major)).getAppFn | continue
        let some (.inductInfo ti) := (← getEnv).find? tn | continue
        if ti.isRec then
          if let .const fn _ := term.getAppFn then
            if ← isRecursiveDefinition fn then continue
        if major.isFVar && !(← isProp (← inferType major)) &&
            !out.contains major.fvarId! then
          out := if ti.isRec then #[major.fvarId!] ++ out else out.push major.fvarId!
    return out
  repair := fun g id => do
    let term ← Term.exprToSyntax (mkFVar id)
    let command ← `(tactic| cases $term:term)
    return #[{
      role := `blockedComputation, major := some id,
      label := "expose blocked computation", command? := some command,
      run := do setGoals ((← g.cases id).toList.map (·.mvarId)) }] }

/-- Keep recursive expansion separate from the nonrecursive interface and
supplied facts. This lets constructor equations simplify before the next split. -/
private def interfaceRules (rules : Array (TSyntax `term)) : TacticM (Array (TSyntax `term)) := do
  rules.filterM fun r => withoutModifyingState do
    try
      let e ← Term.elabTerm r none
      if ← isProp (← inferType e) then return true
      let .const n _ := e.getAppFn | return false
      return !(← isRecursiveDefinition n)
    catch _ => return false

/-- Prefer schemes covering several changing data arguments. A constructor
already visible at a function's input calls for reduction before fresh induction. -/
private def rootSchemes (g : MVarId) (rules : Array (TSyntax `term)) : TacticM (Array Expr) := g.withContext do
  let apps ← Recursion.contextApplications g
  let mut ranked : Array (Expr × Nat) := #[]
  for m in ← movesFor g rules 2 16 .functions do
    if m.role != `directFunction then continue
    let some call := m.subject | continue
    let .const n _ := call.getAppFn | continue
    let some info ← getFunIndInfo? false false n | continue
    let mut reducedInput := false
    let mut score := 0
    for (arg, kind) in call.getAppArgs.zip info.params do
      if kind != .target then continue
      let .const tn _ := (← whnf (← inferType arg)).getAppFn | continue
      if let some (.inductInfo ti) := (← getEnv).find? tn then
        if ti.isRec then score := score + 1
    for app in apps do
      if app.getAppFn != call.getAppFn || app.getAppArgs.size != info.params.size then continue
      for (arg, kind) in app.getAppArgs.zip info.params do
        if kind != .target then continue
        if let .const cn _ := arg.getAppFn then
          if let some (.ctorInfo _) := (← getEnv).find? cn then reducedInput := true
    if !reducedInput then ranked := ranked.push (call, score)
  return (ranked.qsort (fun a b => a.2 > b.2)).map (·.1)

/-- Reserve coordination only for a recursive theory visible in the goals or
explicit definition arguments. Pure evidence induction and arithmetic retain
all ordinary effort. This is an environment/term test, never a theorem-name test. -/
private def needsCoordination (rules : Array (TSyntax `term)) (goals : List MVarId) :
    TacticM Bool := withoutModifyingState do
  for g in goals do
    if ← g.withContext do
      let mut definitions ← Recursion.goalDefinitions g
      for r in rules do
        if !r.raw.isIdent then continue
        try
          let n ← resolveGlobalConstNoOverload r
          if !definitions.contains n then definitions := definitions.push n
        catch _ => pure ()
      definitions.anyM (fun n => return ← isRecursiveDefinition n)
    then return true
  return false

/-- Append a final coordination trial. The engine reserves at most one quarter
of total effort for all final trials, preserving the caller's aggregate cap.
Ordinary successful prefixes run before the coordinated policy is entered. -/
public def hooks (rules : Array (TSyntax `term)) (base : Hooks := {}) : Hooks := Id.run do
  return { base with
    postlude := fun cfg goals => do
      let original ← base.postlude cfg goals
      -- The reserved fraction must support at least the contour's depth.
      if cfg.effort / 4 < 16 || !(← needsCoordination rules goals) then return original
      return original ++ #[{tag := `coordinated, depth := 16, strength := 2, attempts := 256}]
    extraMoves := fun g rs strength remaining group => do
      let mut out ← base.extraMoves g rs strength remaining group
      if group == .induction then
        out := out ++ (← (blockedComputations.propose g).collect)
      if (group == .close || group == .basic) then
        let facts ← (← interfaceRules rs).mapM fun r => `(Lean.Parser.Tactic.simpLemma| $r:term)
        if group == .close then
          let command ← `(tactic| (simp_all [$facts,*]; first | done | omega))
          out := out.push {
            cost := 0, role := `lightClose, closure := .simplification,
            label := "facts then arithmetic", command? := some command, run := evalTactic command }
        else
          let command ← `(tactic| simp_all [$facts,*])
          out := out.push {
            cost := 1, role := `lightNormalize, checkLocalChange := true,
            label := "normalize nonrecursive interface", command? := some command,
            run := evalTactic command }
      return out
    policy := { base.policy with choose := fun space visit => do
      if space.root.trialTag != `coordinated then
        -- Keep enumeration stable for recording/replay, but admit the extra
        -- moves only in their trial. Do not change the ordinary move ordering.
        let ordinaryMove := fun (c : Candidate) =>
          c.move.role != `lightClose && c.move.role != `lightNormalize &&
            c.move.role != `blockedComputation
        let ordinary := {space with
          expand := fun focus groups admit => space.expand focus groups
            (fun c => admit c && ordinaryMove c)
          propose := fun prepared groups admit => space.propose prepared groups
            (fun c => admit c && ordinaryMove c)}
        return ← base.policy.choose ordinary visit
      let some prepared ← space.prepare space.current 0 | return false
      let job := prepared.source.jobs[prepared.focus]!
      let pick := fun groups admit => space.propose prepared groups admit
        (fun p => space.execute p visit)
      if ← pick #[#[.close]] (fun c => c.move.closure == .exact ||
          c.move.closure == .arithmetic || c.move.role == `lightClose) then return true
      -- A changed interface can unlock saturation without more induction or
      -- Boolean splitting. Use the existing strength-one leaf configuration.
      if job.ancestors.isEmpty || job.ancestors.head?.any (fun a =>
          a.move.role == `lightNormalize || a.move.role == `blockedComputation) then
        if ← pick #[#[.close]] (fun c => c.move.role == `continuationClose &&
            c.move.closure == .saturation) then return true
      if ← pick #[#[.basic]] (fun c => c.move.preparation == .allBinders) then return true
      let obstructed ← hasBlockedConsumer job.goal
      if obstructed then
        if ← pick #[#[.basic]] (fun c => c.move.role == `lightNormalize) then return true
      if job.ancestors.all (fun a => a.move.induction != .functional) then
        for call in ← rootSchemes job.goal prepared.rules do
          if ← pick #[#[.functions]] (fun c => c.move.role == `directFunction &&
              c.move.subject == some call) then return true
      if ← pick #[#[.basic]] (fun c => c.move.role == `recursiveRewrite) then return true
      if ← pick #[#[.hypotheses]] (fun c => c.move.role == `substitution ||
          c.move.role == `conjunction) then return true
      if (job.ancestors.filter (fun a => a.move.role == `blockedComputation)).length < 6 then
        if ← pick #[#[.induction]] (fun c => c.move.role == `blockedComputation &&
            !job.ancestors.any (fun a => a.move.major == c.move.major)) then return true
      if ← pick #[#[.basic]] (fun c => c.move.preparation == .normalization ||
          c.move.preparation == .targetSplit) then return true
      if (job.ancestors.filter (fun a => a.move.induction == .none &&
          a.move.major.isSome && a.move.role != `shape)).length < 3 then
        if ← pick #[#[.induction]] (fun c => c.move.induction == .none &&
            c.move.major.isSome && c.move.role != `shape &&
            !job.ancestors.any (fun a => a.move.induction == .none &&
              a.move.major == c.move.major)) then return true
      if (job.ancestors.filter (fun a => a.move.induction != .none)).length < 3 then
        if ← pick #[#[.functions], #[.induction]] (fun c => c.move.induction != .none)
          then return true
      pick #[#[.close]] (fun c => c.move.closure == .simplification ||
        c.move.closure == .saturation)
    } }
end waterfall.Coordination
