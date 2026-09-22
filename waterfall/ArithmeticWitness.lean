module
public import waterfall.Repair

meta section

open Lean Meta Elab Tactic
namespace waterfall.Critics

/-!
An optional witness critic for natural-number arithmetic. An existential's
equality constrains its witness, but unification cannot invert multiplication
or addition. Work backwards through that expression to propose an explicit
term. These are candidates, not algebraic equivalences: division can truncate,
subtraction can saturate, and a conditional's other branch may disagree. The
ordinary search must prove the entire existential body after substitution.
-/

private partial def invertNat (unknownId : FVarId) (expression value : Expr) :
    MetaM (Array Expr) := do
  if expression == mkFVar unknownId then return #[value]
  unless expression.containsFVar unknownId do return #[]
  let args := expression.getAppArgs
  let name := expression.getAppFn.constName?
  if name == some ``ite && args.size == 5 then
    return (← invertNat unknownId args[3]! value) ++
      (← invertNat unknownId args[4]! value)
  if name == some ``Nat.succ && args.size == 1 then
    return ← invertNat unknownId args[0]! (← mkAppM ``HSub.hSub #[value, mkNatLit 1])
  unless args.size ≥ 2 do return #[]
  let lhs := args[args.size - 2]!
  let rhs := args[args.size - 1]!
  let left := lhs.containsFVar unknownId
  let right := rhs.containsFVar unknownId
  if left == right then return #[]
  let unknown := if left then lhs else rhs
  let known := if left then rhs else lhs
  -- Construct the same overloaded expressions as source notation. The arithmetic
  -- closers recognize these forms; a bare Nat.div application can be left opaque.
  if name == some ``Nat.add || name == some ``HAdd.hAdd then
    return ← invertNat unknownId unknown (← mkAppM ``HSub.hSub #[value, known])
  if name == some ``Nat.mul || name == some ``HMul.hMul then
    return ← invertNat unknownId unknown (← mkAppM ``HDiv.hDiv #[value, known])
  if left && (name == some ``Nat.sub || name == some ``HSub.hSub) then
    return ← invertNat unknownId unknown (← mkAppM ``HAdd.hAdd #[value, known])
  return #[]

private partial def equationsIn (e : Expr) : Array Expr :=
  if e.eq?.isSome then #[e] else
  match e with
  | .app fn arg => equationsIn fn ++ equationsIn arg
  | .mdata _ body => equationsIn body
  | _ => #[]

private def arithmeticWitnesses (goal : MVarId) : TacticM (Array Expr) := goal.withContext do
  let target ← whnf (← goal.getType)
  unless target.isAppOfArity ``Exists 2 do return #[]
  let args := target.getAppArgs
  unless ← isDefEq args[0]! (mkConst ``Nat) do return #[]
  withLocalDeclD `witness (mkConst ``Nat) fun witness => do
    let body := (mkApp args[1]! witness).headBeta
    let mut candidates := #[]
    -- Inspect equations in conjunctions, disjunctions and conditional branches.
    -- Do not inspect below binders: their variables cannot escape into a witness.
    let equations := equationsIn body
    for equation in equations do
      let some (type, lhs, rhs) := equation.eq? | continue
      unless ← isDefEq type (mkConst ``Nat) do continue
      for (unknown, value) in [(lhs, rhs), (rhs, lhs)] do
        -- Direct equality already exposes its witness to ordinary unification.
        if unknown == witness then continue
        if value.containsFVar witness.fvarId! then continue
        for candidate in ← invertNat witness.fvarId! unknown value do
          unless candidate.hasMVar || candidate.containsFVar witness.fvarId! ||
              candidates.contains candidate do
            candidates := candidates.push candidate
    return candidates

/-- Propose witnesses obtained by syntactically inverting natural arithmetic.
No fact is admitted and no arithmetic side condition is discarded. -/
public def arithmeticWitness : Critic := {
  Evidence := Expr
  observe := arithmeticWitnesses
  repair := fun goal witness => do
    let term ← PrettyPrinter.delab witness
    let command ← `(tactic| refine Exists.intro $term ?_)
    return #[{
      cost := 1, label := "arithmetic existential witness", role := `witness,
      subject := some witness,
      command? := some command,
      run := goal.withContext do
        let target ← whnf (← goal.getType)
        let body := (mkApp target.getAppArgs[1]! witness).headBeta
        let proof ← mkFreshExprSyntheticOpaqueMVar body
        let result ← mkAppOptM ``Exists.intro
          #[some target.getAppArgs[0]!, some target.getAppArgs[1]!, some witness, some proof]
        goal.assign result
        setGoals [proof.mvarId!] }] }

end waterfall.Critics
