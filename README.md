# waterfall

Small, configurable proof search for inductive Lean goals, inspired by ACL2. waterfall combines simplification, theorem application, case analysis, and induction in one search tactic.

```lean
import waterfall

inductive Tree (V : Type) where
  | empty
  | node (left : Tree V) (key : Nat) (value : V) (right : Tree V)

def elements : Tree V → List (Nat × V)
  | .empty => []
  | .node left key value right => elements left ++ (key, value) :: elements right

def fastElements : Tree V → List (Nat × V) → List (Nat × V)
  | .empty, acc => acc
  | .node left key value right, acc =>
      fastElements left ((key, value) :: fastElements right acc)

theorem fast_elements_helper (t : Tree V) (acc : List (Nat × V)) :
    fastElements t acc = elements t ++ acc := by
  waterfall
```

This example proves the equivalence of two tree traversal functions: `elements` uses list append, while `fastElements` uses an accumulator. `waterfall` completes the entire proof by itself. 

The current release is **waterfall 0.2.0**. You can find the website at
[Website and documentation](https://samth.github.io/waterfall/).


## Software Foundations

The table covers the same 2,190 theorem and example goal IDs from the Software Foundations corpus.
The VFA portion has 509 goals across 15 chapters.

| Volume | Goals | Baseline | Search | Committed |
| --- | ---: | ---: | ---: | ---: |
| LF | 937 | 659 | 788 | 739 |
| PLF | 744 | 230 | 314 | 354 |
| VFA | 509 | 315 | 341 | 354 |
| Total | 2,190 | 1,204 | 1,443 | 1,447 |

The baseline and Committed values are the previously recorded measurements. Search was rerun
with Waterfall 0.2.0 on the same goal IDs; its source snapshot is newer than those earlier runs.

For small examples you can read and run, see [Tutorial/Examples.lean](Tutorial/Examples.lean):

- **LF / Imp:** prove that eliminating `0 + e` preserves expression evaluation.
- **VFA / Sort:** insertion-sort correctness, including sortedness and permutation
  preservation. Every theorem uses waterfall; one helper has an explicit `grind`
  matching pattern.
- **VFA / SearchTree:** prove accumulator-based tree traversal equivalent to
  the simple implementation, as shown above.


## Install with Lake

A `lakefile.toml` dependency can use the public Git repository:

```toml
[[require]]
name = "waterfall"
git = "https://github.com/samth/waterfall.git"
rev = "v0.2.0"
```

`waterfall` is a Lean module. The same import works from module files and
ordinary Lean source files.

## Usage and configuration options

```lean
import waterfall

namespace waterfallReadme

def append : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

example (xs : List Nat) : append xs [] = xs := by
  waterfall [append]

example (xs : List Nat) : append xs [] = xs := by
  waterfall (mode := .committed) (effort := 3000) [append]

example (P : Prop) (h : P) : P := by
  waterfall (config := {mode := .search, effort := 1000, lazy := true})

end waterfallReadme
```

The default `mode := .search` is the default backtracking mode. `mode := .committed` is a simpler forward search that never backtracks after it makes progress.

`effort` configures how hard the search works: more effort permits more attempts, deeper plans and stronger operations. Lean's enclosing resource limits still apply. 
`waterfall?` provides a “Try this” editor hint that replaces the invocation
with ordinary Lean proof commands. Use `(report := true)` for search statistics.
Local hypotheses, registered `simp` and `grind` rules, and definitions from the
current module are used automatically. When a local rule matches the target
except for one missing proposition, waterfall can split on that blocked premise
and continue each case. waterfall also retrieves library theorems
for backward application. Imported definitions and additional rewrite or
instantiation rules can be supplied in brackets.

| Option | Default | Meaning |
| --- | --- | --- |
| `mode` | `.search` | Backtracking search or `.committed` |
| `cpus` | `1` | Maximum concurrent workers; total budgets remain shared |
| `effort` | `1000` | Global attempted-operation allowance |
| `attemptHeartbeats` | `20000000` | Base raw heartbeat slice per operation; strength scales it |
| `lazy` | `true` | Enumerate batches only when reached |
| `deferChecks` | `false` | Delay candidate applicability probes |
| `report` | `false` | Print search statistics |

See the [compiled Lean tutorial](Tutorial/Guide.lean) and
[API reference](docs/API.md). For a guided source review, read the
[proof architecture](docs/IMPLEMENTATION.md). The website includes usage examples and an option reference.

Use `waterfall (cpus := 4)` to explore different depth/strength trials of the
same policy concurrently on at most four dedicated worker threads. The first completed proof wins; timings,
retained plans and finite-budget coverage can vary. Workers share the attempt
allowance and divide the remaining heartbeat allowance. Operating-system CPU affinity can further limit concurrency. Cancellation is
cooperative, and all workers are joined before returning. The default of one
CPU uses the existing sequential path. See [parallel execution](docs/API.md#parallel-execution).

## Build and check

```sh
lake build
lake test
lake -d site build
lake -d site test
lake -d site exe site check-docs
```

## AI Use

Waterfall was primarily developed by GPT-6 Astra. This README was written by me.
