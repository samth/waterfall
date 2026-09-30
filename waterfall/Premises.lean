module
public import Lean

meta section
open Lean Meta Elab Tactic
namespace waterfall.Premises

/-!
Relevant earlier theorems for the `simp` closer. Proofs in a development often
cite a lemma proved earlier in the same file, and Waterfall's simplifier cannot use
such a lemma unless it is registered or supplied. At entry the tactic selects the
most relevant earlier theorems; at each node the `simp` closer retries with those
relevant to that node when its ordinary run fails.

Relevance is shared vocabulary: each candidate is scored by the constants its
statement shares with the goals, weighting a constant by how rare it is among
the candidates. The candidates are the theorems declared earlier in the current
module, private ones included, and the public theorems of imported modules from
the current module's root or one of the explicitly supplied module prefixes.
Module roots are a default search scope, not an identification of Lake packages.
Theorems whose proofs use `sorry` are excluded.
-/

/-- `pre` followed by one or more digits, as in generated names like `eq_1`. -/
private def numbered (s pre : String) : Bool :=
  s.startsWith pre && s.length > pre.length && (s.drop pre.length).all Char.isDigit

/-- Generated declarations that are not user lemmas: equation, unfolding and
induction principles, abstracted proofs, matchers and their congruence equations,
and the theorems Lean derives for inductive types, their constructors and
auxiliary recursors. A private theorem is judged by the name its user wrote. -/
private def generated (env : Environment) (n : Name) : Bool :=
  let n' := privateToUserName n
  isAuxRecursor env n || isNoConfusion env n ||
    n'.isInternalDetail || n.hasMacroScopes || n'.anyS (numbered · "match_") ||
    match n' with
    | .str parent s =>
      numbered s "eq_" || numbered s "proof_" || numbered s "match_" || s.startsWith "_" ||
        s == "eq_def" || s == "eq_unfold" || s == "induct" || s == "induct_unfolding" ||
        s == "fun_cases" || s == "mutual_induct" || s == "inj" || s == "injEq" ||
        s == "sizeOf_spec" || s.startsWith "congr_eq_" ||
        -- Prop-valued `brecOn` theorems are not always tagged as auxiliary
        -- recursors. Check the generated name and its inductive parent too.
        (s == "brecOn" && (env.find? parent).any (fun info => match info with
          | .inductInfo _ => true | _ => false)) || isAuxRecursor env parent ||
        isNoConfusion env parent ||
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

/-- Public user theorems in the imported module scope, with their vocabulary.
The imports do not change during elaboration; cache this per module and scope. -/
-- Include the scope in the cache key: separate calls in one file can search
-- different imported developments.
private initialize importedCache : IO.Ref (Option ((Name × Array Name) × Array (Name × Array Name))) ←
  IO.mkRef none

private def importedCandidates (modules : Array Name) : MetaM (Array (Name × Array Name)) := do
  let env ← getEnv
  let main := env.mainModule
  if let some (m, cached) := ← importedCache.get then
    if m == (main, modules) then return cached
  let root := main.getRoot
  let mut out := #[]
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless (!root.isAnonymous && root.isPrefixOf modName) ||
        modules.any (·.isPrefixOf modName) do continue
    for info in data.constants do
      let .thmInfo val := info | continue
      -- A private theorem of another module cannot be cited here.
      if isPrivateName val.name || generated env val.name then continue
      out := out.push (val.name, vocabulary env val.type)
  importedCache.set (some ((main, modules), out))
  return out

/-- Rank a finite candidate pool against the current obligations. Collection
and scoring stay separate so callers can control the module scope. -/
private def rank (goals : List MVarId) (candidates : Array (Name × Array Name))
    (limit : Nat) : MetaM (Array Name) := do
  if limit == 0 || candidates.isEmpty then return #[]
  let env ← getEnv
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
  -- Checking a proof for `sorry` walks the whole proof, so only the leaders are checked.
  -- An admitted theorem would make any proof that cites it depend on `sorry`.
  let mut chosen := #[]
  for (name, _) in ranked do
    if chosen.size >= limit then break
    let some (.thmInfo val) := env.find? name | continue
    unless ← admitted name val.value do chosen := chosen.push name
  return chosen

/-- Earlier theorems of the current module and theorems of imported modules from
the same root or an explicit `modules` prefix, most relevant first, at most
`limit`. Only candidates sharing at least one constant with the goals are
returned. Ties keep a deterministic name order. -/
public def select (goals : List MVarId) (limit : Nat)
    (modules : Array Name := #[]) : MetaM (Array Name) := do
  if limit == 0 then return #[]
  let env ← getEnv
  let mut candidates := (← importedCandidates modules)
  for (name, info) in env.constants.map₂.toList do
    let .thmInfo val := info | continue
    unless generated env name do candidates := candidates.push (name, vocabulary env val.type)
  rank goals candidates limit

/-- Keep entry order while filtering names whose statements share vocabulary
with the residual goal. The caller controls the number of offered premises. -/
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
