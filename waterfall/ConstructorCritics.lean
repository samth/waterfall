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

end waterfall.Critics
