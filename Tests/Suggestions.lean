import waterfall

open Lean Elab Tactic Meta

private partial def hintEdits (ref : Syntax) : InfoTree → Array Meta.Tactic.TryThis.TryThisInfo
  | .context _ tree => hintEdits ref tree
  | .hole _ => #[]
  | .node info children => Id.run do
    let nested := children.toArray.flatMap (hintEdits ref)
    let .ofCustomInfo {stx, value} := info | return nested
    if stx.getRange? != ref.getRange? then return nested
    let some hint := value.get? Meta.Tactic.TryThis.TryThisInfo | return nested
    return nested.push hint

/-- Observe the actual TryThis editor edit, not a separately generated script. -/
elab "check_hint " expected:str " => " tac:tactic : tactic => withEnableInfoTree true do
  let initial ← saveState
  let roots ← getUnsolvedGoals
  Term.withoutTacticIncrementality true <| evalTactic tac
  let info ← getInfoState
  let hints := (← getInfoTrees).toArray.flatMap fun tree =>
    hintEdits tac.raw (tree.substitute info.assignment)
  unless hints.size == 1 do throwError "expected exactly one replacement, got {hints.size}"
  let some hint := hints[0]? | throwError "missing replacement"
  let text := hint.edit.newText
  for forbidden in ["expose_names", "case'", "focus", "maxSteps", "canonHeartbeats", "first"] do
    if (text.splitOn forbidden).length > 1 then
      throwError "unnecessary trace detail {forbidden} in the replacement: {text}"
  unless (text.splitOn expected.getString).length > 1 do
    throwError "expected {expected.getString} in the replacement: {text}"
  let some range := tac.raw.getRange? | throwError "missing invocation span"
  unless hint.edit.range == (← getFileMap).utf8RangeToLspRange range do
    throwError "hint does not replace the entire invocation"
  let .ok stx := Parser.runParserCategory (← getEnv) `tactic text
    | throwError "editor replacement did not parse"
  let winning ← saveState
  try
    initial.restore true
    Term.withoutErrToSorry <| withoutRecover <| evalTactic stx
    waterfall.checkComplete roots
    unless (← getUnsolvedGoals).isEmpty do throwError "editor replacement left goals"
  finally
    winning.restore true


set_option maxHeartbeats 1000000

example (P : Prop) (h : P) : P := by check_hint "exact" => waterfall?
example (P : Prop) (h : P) : P := by check_hint "exact" => waterfall? (mode := .committed)
example (P : Prop) (h : P) : P := by check_hint "exact" => waterfall? (cpus := 2)

def append (xs ys : List Nat) : List Nat :=
  match xs with
  | [] => ys
  | x :: xs => x :: append xs ys

example (xs : List Nat) : append xs [] = xs := by check_hint "fun_induction" => waterfall? [append]
example (xs : List Nat) : append xs [] = xs := by check_hint "induction" => waterfall? (mode := .committed) [append]

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by check_hint "simp_all" => waterfall?
example (P : Prop) : P → P := by check_hint "simp_all" => waterfall?
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by check_hint "grind" => waterfall?

-- One invocation can close an entire pending agenda. Its editor replacement
-- must do the same, rather than merely proving the first conjunct.
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  check_hint "exact" => waterfall?

-- Failed discovery does not produce a suggestion or consume the input goal.
example (P : Prop) (h : P) : P := by
  fail_if_success waterfall? (effort := 0)
  exact h

-- Exercise the generic proof-term renderer independently of recipe coverage.
-- grind creates a private auxiliary proof here; it must not leak into the text.
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  run_tac
    let initial ← saveState
    let roots ← getUnsolvedGoals
    evalTactic (← `(tactic| grind))
    let script ← waterfall.Suggestions.compile initial roots #[] #[]
    unless script.usedTerm do throwError "expected proof-term fallback"
    initial.restore true
    Term.withoutErrToSorry <| withoutRecover <| evalTactic script.tactic
    waterfall.checkComplete roots

-- A policy may select any sibling. Rendering reconstructs the proof forest
-- and presents these independent roots in their original order using bullets.
elab "last_goal_hint" : tactic => do
  let hooks : waterfall.Hooks := { policy := ⟨Unit, (), fun space =>
    space.expand (space.current.jobs.length - 1) #[] (fun _ => true)⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : P ∧ Q ∧ R := by
  refine ⟨?first, ?middle, ?last⟩
  check_hint "·" => last_goal_hint

-- Discovery used scaled solver configurations, but these examples replay
-- with ordinary defaults. The hints should omit the unnecessary settings.
elab "strong_hint " label:str : tactic => do
  let hooks : waterfall.Hooks := {
    trials := fun _ => #[(4, 2)]
    policy := ⟨Unit, (), fun space =>
      space.expand 0 #[] (fun c => c.move.label == label.getString)⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  check_hint "simp_all" => strong_hint "simp"
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  check_hint "grind" => strong_hint "grind"

-- Extension moves are regenerated through the same hooks during compilation.
-- A blocked-premise critic prints a checked ordinary `by_cases` command.
elab "critic_hint" : tactic => do
  let base : waterfall.Hooks := {
    trials := fun _ => #[(4, 1)]
    policy := ⟨Unit, (), fun space =>
      if space.current.plan.isEmpty then
        space.expand 0 #[#[.hypotheses]] (fun c => c.move.role == `critic)
      else space.expand 0 #[] (fun _ => true)⟩ }
  let hooks := waterfall.Critics.hooks base
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks
    (fun h => waterfall.run { effort := 100 } #[] h)

example (p q r : Prop) (hp : p) (positive : p → q → r)
    (negative : ¬q → r) : r := by
  check_hint "by_cases" => critic_hint

-- A constructor that closes a data goal is an ordinary application, not a
-- reason to print the entire proof term of a surrounding induction.
inductive HintToken where
  | one
  | two
example : HintToken := by check_hint "apply" => waterfall?

-- Force the fixed-index operation to test its equation-preserving recipe.
-- This tests rendering, not a claim that induction is needed to prove True.
inductive HintChain : Nat → Prop where
  | zero : HintChain 0
  | step : HintChain n → HintChain (n + 1)

elab "indexed_hint" : tactic => do
  let hooks : waterfall.Hooks := {
    trials := fun _ => #[(2, 1)]
    policy := ⟨Unit, (), fun space =>
      if space.current.plan.isEmpty then
        space.expand 0 #[#[.induction]]
          (fun c => c.move.motive == .indexAbstraction)
      else space.expand 0 #[] (fun _ => true)⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (n : Nat) (h : HintChain (n + 1)) : True := by
  check_hint "generalize" => indexed_hint

-- Adapters can share an ordinary command proposal with the hint frontend;
-- rule applications must not require delaborating the enclosing proof term.
elab "rule_hint" : tactic => do
  let rules := #[← `(term| And.intro)]
  let hooks : waterfall.Hooks := {
    trials := fun _ => #[(2, 1)]
    policy := ⟨Unit, (), fun space =>
      if space.current.plan.isEmpty then
        space.expand 0 #[#[.rules]] (fun c => c.move.label == "apply rule")
      else space.expand 0 #[] (fun _ => true)⟩ }
  discard <| waterfall.Suggestions.run (← getRef) rules hooks (fun h => waterfall.run {} rules h)

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  check_hint "apply And.intro" => rule_hint

-- A forward step prints the instantiated local fact, including constructor
-- arguments, rather than delaborating the complete proof built after it.
elab "forward_hint" : tactic => do
  let hooks : waterfall.Hooks := {
    trials := fun _ => #[(2, 1)]
    policy := ⟨Unit, (), fun space =>
      if space.current.plan.isEmpty then
        space.expand 0 #[#[.forward]]
          (fun c => c.move.major.isSome && c.move.subject.isSome && c.move.forward?.isSome)
      else space.expand 0 #[] (fun _ => true)⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (P : Nat → Prop) (h : ∀ n, P n) (n : Nat) : P (n + 1) := by
  check_hint "have derived" => forward_hint

-- Introduction names belong at the binder, including collision avoidance and
-- both one-at-a-time and bulk preparation. No `expose_names` is needed later.
elab "intro_hint " bulk:term : tactic => do
  let all := bulk.raw.isIdent && bulk.raw.getId == `true
  let hooks : waterfall.Hooks := {
    trials := fun _ => #[(6, 1)]
    policy := ⟨Unit, (), fun space => space.expand 0 #[] fun c =>
      c.move.closure == .exact || c.move.preparation ==
        (if all then .allBinders else .oneBinder)⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (P : Prop) : ∀ _x : Nat, P → P := by
  check_hint "intro" => intro_hint true

example (P : Prop) : ∀ _x : Nat, P → P := by
  check_hint "intro" => intro_hint false

example (x : Nat) : ∀ x : Fin (x + 1), x = x := by
  check_hint "intro x_1" => intro_hint true

-- A nested tree visited right-to-left still prints nested bullets in proof
-- order. This checks ancestry, not just a reordering of independent roots.
elab "nested_hint" : tactic => do
  let rules := #[← `(term| And.intro)]
  let hooks : waterfall.Hooks := {
    trials := fun _ => #[(6, 1)]
    policy := ⟨Unit, (), fun space =>
      space.expand (space.current.jobs.length - 1) #[] fun c =>
        c.move.closure == .exact || c.action.group == .rules⟩ }
  discard <| waterfall.Suggestions.run (← getRef) rules hooks (fun h => waterfall.run {} rules h)

example (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : (P ∧ Q) ∧ R := by
  check_hint "·" => nested_hint

-- A case split with one constructor still binds its fields explicitly.
elab "decompose_hint" : tactic => do
  let hooks : waterfall.Hooks := {
    trials := fun _ => #[(3, 1)]
    policy := ⟨Unit, (), fun space => space.expand 0 #[] fun c =>
      c.move.closure == .exact || c.action.group == .hypotheses⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (P Q : Prop) (h : P ∧ Q) : P := by
  check_hint "cases" => decompose_hint

-- A later root can assign an earlier witness without a recorded step for it.
-- Such a graph need not be a tree: preserve a checked fallback and the winner.
example : ∃ n : Nat, n = 1 := by
  refine ⟨?_, ?_⟩
  run_tac
    let initial ← saveState
    let roots ← getUnsolvedGoals
    let path ← IO.mkRef (#[] : waterfall.Suggestions.Path)
    let hooks : waterfall.Hooks := {
      policy := ⟨Unit, (), fun space => space.expand (space.current.jobs.length - 1) #[]
        (fun c => c.move.closure == .exact)⟩
      accepted := fun step saved => path.modify (·.push (step, saved)) }
    discard <| waterfall.run {} #[] hooks
    let script ← waterfall.Suggestions.compile initial roots (← path.get) #[] hooks
    waterfall.checkComplete roots
    initial.restore true
    Term.withoutErrToSorry <| withoutRecover <| evalTactic script.tactic
    waterfall.checkComplete roots


-- If ordinary simplification cannot close a leaf, retain the adapter's recipe.
-- The required lemma is deliberately supplied only by the command metadata.
elab "required_recipe_hint" : tactic => do
  let recipe ← `(tactic| simp_all only [Nat.add_comm])
  let hooks : waterfall.Hooks := {
    extraMoves := fun _ _ _ _ group => pure <| if group == .close then #[{
      cost := 0, label := "commutativity recipe", closure := .simplification,
      command? := some recipe, run := evalTactic recipe }] else #[]
    policy := ⟨Unit, (), fun space => space.expand 0 #[]
      (fun c => c.move.label == "commutativity recipe")⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (a b : Nat) : a + b = b + a := by
  check_hint "Nat.add_comm" => required_recipe_hint
