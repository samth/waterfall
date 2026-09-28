module
public import Lean

meta section
open Lean Meta Elab Tactic
namespace waterfall.Premises

/-!
Relevant earlier theorems for the `simp` closer. Proofs in a development often
cite a lemma proved earlier in the same file, and Waterfall's simplifier cannot use
such a lemma unless it is registered or supplied. At entry the tactic selects the
most relevant earlier theorems of the current module; at each node the `simp`
closer retries with those relevant to that node when its ordinary run fails.

Relevance is shared vocabulary: each candidate is scored by the constants its
statement shares with the goals, weighting a constant by how rare it is among
the candidates. Only theorems declared in the current module are candidates,
matching the policy that implicitly unfolds only current-module definitions, and
theorems whose proofs use `sorry` are excluded.
-/

/-- `pre` followed by one or more digits, as in generated names like `eq_1`. -/
private def numbered (s pre : String) : Bool :=
  s.startsWith pre && s.length > pre.length && (s.drop pre.length).all Char.isDigit

/-- Generated declarations that are not user lemmas: equation, unfolding and
induction principles, abstracted proofs, matcher lemmas, and the theorems Lean
derives for inductive types, their constructors and auxiliary recursors. -/
private def generated (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || n.hasMacroScopes ||
    match n with
    | .str parent s =>
      numbered s "eq_" || numbered s "proof_" || numbered s "match_" || s.startsWith "_" ||
        s == "eq_def" || s == "eq_unfold" || s == "induct" || s == "induct_unfolding" ||
        s == "fun_cases" || s == "mutual_induct" || s == "inj" || s == "injEq" ||
        s == "sizeOf_spec" || isAuxRecursor env parent || isNoConfusion env parent ||
        (env.find? parent).any (·.isCtor)
    | _ => false

/-- Logical vocabulary shared by almost every statement; it says nothing about
relevance. Instances are excluded separately. -/
private def logical : List Name :=
  [``Eq, ``Ne, ``Iff, ``And, ``Or, ``Not, ``True, ``False, ``Exists, ``HEq, ``ite, ``dite,
   ``Decidable, ``OfNat.ofNat]

/-- The constants of an expression that can indicate relevance. -/
private def vocabulary (env : Environment) (e : Expr) : Array Name :=
  (e.getUsedConstants.toList.eraseDups.filter fun c =>
    !logical.contains c && !Meta.isInstanceCore env c).toArray

/-- Vocabulary of every unsolved goal: its target and its visible hypotheses. -/
private def goalConstants (goals : List MVarId) : MetaM (Std.HashSet Name) := do
  let env ← getEnv
  let mut names : Std.HashSet Name := {}
  for g in goals do
    names ← g.withContext do
      let mut acc := names
      for n in vocabulary env (← instantiateMVars (← g.getType)) do acc := acc.insert n
      for d in (← getLCtx) do
        unless d.isImplementationDetail do
          for n in vocabulary env (← instantiateMVars d.type) do acc := acc.insert n
      return acc
  return names

/-- Whether a theorem's proof uses `sorry`, cached: a declared proof never changes. -/
private initialize admittedCache : IO.Ref (Std.HashMap Name Bool) ← IO.mkRef {}

private def admitted (name : Name) (value : Expr) : BaseIO Bool := do
  if let some known := (← admittedCache.get).get? name then return known
  let result := (value.find? (·.isConstOf ``sorryAx)).isSome
  admittedCache.modify (·.insert name result)
  return result

/-- Theorems of the current module, most relevant first, at most `limit`. Only
candidates sharing at least one constant with the goals are returned. Ties keep a
deterministic name order. -/
public def select (goals : List MVarId) (limit : Nat) : MetaM (Array Name) := do
  if limit == 0 then return #[]
  let env ← getEnv
  let mut candidates : Array (Name × Array Name) := #[]
  for (name, info) in env.constants.map₂.toList do
    let .thmInfo val := info | continue
    -- An admitted theorem would make any proof that cites it depend on `sorry`.
    if generated env name || (← admitted name val.value) then continue
    candidates := candidates.push (name, vocabulary env val.type)
  if candidates.isEmpty then return #[]
  -- Document frequency over the candidate statements.
  let mut df : Std.HashMap Name Nat := {}
  for (_, consts) in candidates do
    for c in consts do df := df.insert c (df.getD c 0 + 1)
  let wanted ← goalConstants goals
  let total := candidates.size.toFloat
  let scored := candidates.filterMap fun (name, consts) =>
    let shared := consts.toList.filter wanted.contains
    if shared.isEmpty then none
    else some (name, shared.foldl (fun s c => s + Float.log (total / (1 + (df.getD c 0).toFloat)) + 1) 0)
  let ranked := scored.qsort fun (a, x) (b, y) => x > y || (x == y && a.toString < b.toString)
  return (ranked.extract 0 limit).map (·.1)

/-- The candidates, in order, whose statements share vocabulary with the goal `g`,
at most `limit`. Used at each search node to restrict the candidates chosen at entry. -/
public def relevantAt (g : MVarId) (candidates : Array Name) (limit : Nat) : MetaM (Array Name) := do
  if candidates.isEmpty || limit == 0 then return #[]
  let env ← getEnv
  let wanted ← goalConstants [g]
  let mut out := #[]
  for name in candidates do
    if out.size >= limit then break
    let some info := env.find? name | continue
    if (vocabulary env info.type).any wanted.contains then out := out.push name
  return out

/-- Rule syntax that denotes each theorem wherever it is elaborated. -/
public def rules (names : Array Name) : Array (TSyntax `term) :=
  names.map fun n => ⟨mkCIdent n⟩

end waterfall.Premises
