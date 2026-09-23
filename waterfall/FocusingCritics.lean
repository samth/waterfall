module
public import waterfall.Repair

meta section

open Lean Meta Elab Tactic
namespace waterfall.Critics

/-- An indexed proposition whose actual index has a visible constructor. -/
private structure IndexedMajor where
  id : FVarId
  relation : Name
  index : Expr
  position : Nat
  size : Nat

/-- Read a constructor result without creating metavariables or running cases. -/
private def constructorResult : Expr → Expr
  | .forallE _ _ body _ => constructorResult body
  | .mdata _ body => constructorResult body
  | expr => expr

/-- A constructor-shaped index is useful only if the relation inspects that
index. Generic closures such as reflexive-transitive closure relate arbitrary
indices; inverting them does not exploit the visible term structure. -/
private def constrainsIndex (info : InductiveVal) (position : Nat) : MetaM Bool := do
  for name in info.ctors do
    let result := constructorResult (← getConstInfoCtor name).type
    let some index := result.getAppArgs[info.numParams + position]? | continue
    let .const head _ := index.consumeMData.getAppFn | continue
    if let some (.ctorInfo _) := (← getEnv).find? head then return true
  return false

private def indexedMajor? (previous : Option IndexedMajor := none) : MetaM (Option IndexedMajor) := do
  let mut best : Option IndexedMajor := none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    -- Applications can leave an assigned metavariable as a hypothesis type.
    -- Resolve those assignments without unfolding arbitrary definitions.
    let type := (← instantiateMVars d.type).consumeMData
    let .const relation _ := type.getAppFn | continue
    let some (.inductInfo info) := (← getEnv).find? relation | continue
    unless info.isRec && (← isProp type) do continue
    if previous.any (·.relation != relation) then continue
    for position in [:type.getAppArgs.size - info.numParams] do
      if previous.any (·.position != position) then continue
      unless ← constrainsIndex info position do continue
      let index := type.getAppArgs[info.numParams + position]!
      let some ctor ← isConstructorApp? index | continue
      -- A finite classification (such as a color or base type) provides no
      -- structural descent. Its ordinary case alternatives remain available.
      unless (← getConstInfoInduct ctor.induct).isRec do continue
      let size := index.sizeWithoutSharing
      if size > (best.map (·.size)).getD 0 then
        best := some ⟨d.fvarId, relation, index, position, size⟩
  return best

/-- Only constructor fields produced by this inversion can make it cyclic.
Preexisting hypotheses do not veto a useful case split. -/
private def repeatsIndex (alternatives : Array CasesSubgoal) (major : IndexedMajor) : MetaM Bool := do
  for alt in alternatives do
    let cyclic ← alt.mvarId.withContext do
      for field in alt.fields do
        let type := (← instantiateMVars (← inferType field)).consumeMData
        let .const relation _ := type.getAppFn | continue
        if relation != major.relation then continue
        let some (.inductInfo info) := (← getEnv).find? relation | continue
        if type.getAppArgs[info.numParams + major.position]? == some major.index then
          return true
      return false
    if cyclic then return true
  return false

/-- A failed candidate is rolled back by the ordinary search continuation.
Every branch of the final inversion remains a pending goal, including branches
sharing metavariable witnesses. -/
private def runIndexedFocus (goal : MVarId) : TacticM Unit := do
  let (_, first) ← goal.withContext goal.intros
  let mut current := first
  let mut children : List MVarId := [first]
  let mut previous : Option IndexedMajor := none
  let mut progressed := false
  repeat
    let some major ← current.withContext (indexedMajor? previous) | break
    if previous.any (major.size >= ·.size) then break
    let saved ← Tactic.saveState
    let alternatives ← current.withContext <| current.cases major.id
    if ← repeatsIndex alternatives major then
      -- Keep the last accepted inversion, not the assignments and hidden
      -- branch obligations created by this rejected continuation.
      saved.restore true
      if !progressed then throwError "indexed inversion does not descend"
      break
    progressed := true
    children := alternatives.toList.map (·.mvarId)
    previous := some major
    if let [child] := children then current := child else break
  unless progressed do throwError "no constructor-indexed hypothesis"
  setGoals children

/-- Visible constructors of the selected recursive datatype give a structural
cost for the fused chain. Count the introduction block separately, as ordinary
preparation does. Undercharging a fused proof lets it repeatedly solve one
sibling at depths where the other siblings cannot yet succeed. -/
private def constructorCount (constructors : List Name) : Expr → Nat
  | .const name _ => if constructors.contains name then 1 else 0
  | .app fn arg => constructorCount constructors fn + constructorCount constructors arg
  | .mdata _ expr => constructorCount constructors expr
  | _ => 0

/-- Observe cheap index metadata after exposing binders. Execution reconstructs
the local IDs in its own checkpoint and charges inversion to the move slice. -/
public def indexedFocus : Critic := {
  Evidence := Nat
  observe := fun goal => do
    let (introduced, child) ← goal.withContext goal.intros
    let some major ← child.withContext indexedMajor? | return #[]
    let some ctor ← isConstructorApp? major.index | return #[]
    let constructors := (← getConstInfoInduct ctor.induct).ctors
    let inversions := max 1 (constructorCount constructors major.index)
    return #[inversions + if introduced.isEmpty then 0 else 1]
  repair := fun goal cost => pure #[{
    cost, role := `prepare, label := "focus indexed hypothesis",
    run := runIndexedFocus goal }] }

end waterfall.Critics
