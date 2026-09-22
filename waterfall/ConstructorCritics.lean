module
public import waterfall.Repair

meta section

open Lean Meta Elab Tactic
namespace waterfall.Critics

/-- Only stable names and a binder position survive the observation checkpoint. -/
private structure ImplicitWitness where
  binder : Nat
  constructor : Name

/-- A constructor's conclusion may not reduce until an implicit data argument
has a known outer constructor. Propose that one layer, allowing unification to
infer its fields. Every unresolved field remains an obligation. This retains
the original finite enumeration, including candidates that ordinary application
could already infer; narrowing that enumeration would be a separate experiment. -/
public def implicitWitnesses (constructor : Name) : Critic := {
  Evidence := ImplicitWitness
  observe := fun _ => do
    forallTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels constructor)) fun xs _ => do
      let mut choices := #[]
      for i in [:xs.size] do
        let d ← getFVarLocalDecl xs[i]!
        if d.binderInfo.isExplicit || d.binderInfo.isInstImplicit || (← isProp d.type) then continue
        let .const n _ := (← whnf d.type).getAppFn | continue
        let some (.inductInfo info) := (← getEnv).find? n | continue
        for c in info.ctors do choices := choices.push ⟨i, c⟩
      return choices
  repair := fun goal evidence => pure #[{
    cost := 2,
    label := s!"constructor {constructor} witness {evidence.binder} {evidence.constructor}"
    run := goal.withContext do
      let fn ← mkConstWithFreshMVarLevels constructor
      let (xs, _, _) ← forallMetaTelescopeReducing (← inferType fn)
      discard <| xs[evidence.binder]!.mvarId!.apply
        (← mkConstWithFreshMVarLevels evidence.constructor)
      setGoals (← goal.apply (mkAppN fn xs)) }] }

/-- Traverse constructor fields without descending into unrelated computations. -/
private partial def constructorFields (e : Expr) : MetaM (Array FVarId) := do
  if e.isFVar then return #[e.fvarId!]
  let .const n _ := e.getAppFn | return #[]
  let some (.ctorInfo _) := (← getEnv).find? n | return #[]
  e.getAppArgs.foldlM (fun ids arg => return ids ++ (← constructorFields arg)) #[]

/-- Constructor patterns in related arguments expose potential blocked matches. -/
public def constructorObstructions (calls : Array Expr) : MetaM (Array FVarId × Array FVarId) := do
  let mut blocked : Array FVarId := #[]
  let mut fields : Array FVarId := #[]
  for call in calls do
    for arg in call.getAppArgs do
      let .const n _ := arg.getAppFn | continue
      let some (.ctorInfo _) := (← getEnv).find? n | continue
      let type ← inferType arg
      let .const typeName _ := (← whnf type).getAppFn | continue
      let some (.inductInfo info) := (← getEnv).find? typeName | continue
      unless info.isRec do continue
      for other in call.getAppArgs do
        for id in ← constructorFields other do
          if ← withoutModifyingState (isDefEq (← id.getDecl).type type) then
            if other.isFVar then
              if !blocked.contains id then blocked := blocked.push id
            else if !fields.contains id then fields := fields.push id
  return (blocked, fields)

/-- Annotate ordinary case alternatives using observed constructor obstructions.
No new case executor or traversal is introduced. -/
public def exposeConstructors (obstructions : Array FVarId × Array FVarId)
    (major : FVarId) (alternatives : Array Move) : Critic := {
  Evidence := Name
  observe := fun _ => pure #[if obstructions.1.contains major then `blockedMatch
    else if obstructions.2.contains major then `constructorField else .anonymous]
  repair := fun _ role => pure (alternatives.map fun move => {move with role}) }

end waterfall.Critics
