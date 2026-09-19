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

example (P : Prop) (h : P) : P := by check_hint "first" => waterfall?
example (P : Prop) (h : P) : P := by check_hint "first" => waterfall? (mode := .committed)
example (P : Prop) (h : P) : P := by check_hint "first" => waterfall? (cpus := 2)

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
  check_hint "first" => waterfall?

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

-- A policy may select any sibling. case' must preserve the relative order of
-- the other goals; rotation alone is not the engine's agenda operation.
elab "last_goal_hint" : tactic => do
  let hooks : waterfall.Hooks := { policy := ⟨Unit, (), fun space =>
    space.expand (space.current.jobs.length - 1) #[] (fun _ => true)⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (P Q R : Prop) (hp : P) (hq : Q) (hr : R) : P ∧ Q ∧ R := by
  refine ⟨?first, ?middle, ?last⟩
  check_hint "case'" => last_goal_hint

-- Scaled solver configurations must print ordinary field names and numerals,
-- without quotation hygiene marks or hidden elaborator references.
elab "strong_hint " label:str : tactic => do
  let hooks : waterfall.Hooks := {
    trials := fun _ => #[(4, 2)]
    policy := ⟨Unit, (), fun space =>
      space.expand 0 #[] (fun c => c.move.label == label.getString)⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  check_hint "maxSteps" => strong_hint "simp"
example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  check_hint "canonHeartbeats" => strong_hint "grind"

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
          (fun c => c.move.major.isSome && c.move.subject.isSome)
      else space.expand 0 #[] (fun _ => true)⟩ }
  discard <| waterfall.Suggestions.run (← getRef) #[] hooks (fun h => waterfall.run {} #[] h)

example (P : Nat → Prop) (h : ∀ n, P n) (n : Nat) : P (n + 1) := by
  check_hint "have derived" => forward_hint
