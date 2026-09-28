import waterfall

/-!
# Using waterfall

Import `waterfall` and try `waterfall` on a complete goal or a remaining branch.
Supply imported definitions and useful lemmas in brackets. The search inspects
local hypotheses and discovers definitions from the current module; it does not
unfold every imported definition automatically.

The following examples are compiled by `lake test`.
-/

namespace waterfall.Guide

/-- A recursive function used to illustrate induction and supplied definitions. -/
def append {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

example (xs : List Nat) : append xs [] = xs := by
  waterfall [append]

example (xs : List Nat) : append xs [] = xs := by
  waterfall (mode := .committed) [append]

example (xs ys zs : List Nat) : append (append xs ys) zs = append xs (append ys zs) := by
  waterfall (effort := 3000) [append]

/-!
## Replacing automation with proof commands

Click the “Try this” hint from `waterfall?` to replace it with a checked script.
The same configuration and rule arguments are accepted in either mode.
-/
example (xs : List Nat) : append xs [] = xs := by
  waterfall? [append]

/-!
## Configuration

`effort` is the main knob. It funds more attempted operations, deeper structural
plans and stronger individual solvers. Failed operations still consume effort.
The enclosing Lean heartbeat and recursion limits also apply.

`lazy := false` generates a whole phase's batches eagerly. `deferChecks := true`
postpones applicability checks until a candidate is considered. Both settings
keep candidates available, but change work ordering within a finite allowance.

`premises := n` lets the `simp` closer retry, when its ordinary run fails, with up
to `n` earlier theorems of the current module that share vocabulary with the goal.
It helps when a proof needs an earlier lemma, such as commutativity of a function
defined in the same file. It is off by default because the extra simplifier calls
cost time and can change which proof the search reaches first.
-/
example (P : Prop) (h : P) : P := by
  waterfall (effort := 1000) (lazy := true) (deferChecks := false)

example (P : Prop) (h : P) : P := by
  waterfall (config := {mode := .committed, effort := 1000})

/-!
## Parallel execution

`cpus` limits concurrent trials of the selected policy. Workers use dedicated threads, including
when called from an asynchronous Lean elaborator. Attempts and heartbeats remain aggregate
budgets; the first completed proof wins. One CPU retains sequential execution.
-/
example (P : Prop) (h : P) : P := by
  waterfall (cpus := 2)

/-!
## Extending search

`Mode.hooks` supplies ordinary callback functions for a mode. Adapt the
`Hooks` structure through the programmatic `waterfall.run` interface. Keep the default mode unless a measured alternative helps your goals.
-/
example (P : Prop) (h : P) : P := by
  run_tac discard <| waterfall.run {} #[] { waterfall.Mode.search.hooks with
    trials := waterfall.diagonalTrials 1 }

end waterfall.Guide
