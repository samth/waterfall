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

The current release is **waterfall 0.1** You can find the website at
[Website and documentation](https://samth.github.io/waterfall/).


## Benchmark results

On the full 2,645-entry inductive-bench selection, `waterfall` proves **1,615 of
2,631 theorem goals**, up from **1,594**: 22 gains and 1 loss on the same
inputs. The remaining 14 entries are executable definitions, excluded from the
goal counts below.

| Suite | Goals | Previous main | Current main |
| --- | ---: | ---: | ---: |
| Software Foundations: LF | 949 | 799 | 800 |
| Software Foundations: PLF | 744 | 314 | 314 |
| Software Foundations: VFA | 509 | 338 | 341 |
| TIP/CLAM | 173 | 77 | 87 |
| Leon | 87 | 30 | 31 |
| MiniF2F induction | 13 | 11 | 11 |
| VProver (IndBen-156) | 156 | 25 | 31 |
| Total | 2,631 | 1,594 | 1,615 |

Measured on 2026-09-22 with Lean 4.30.0, default search, effort 1,000, and one
Lean thread, comparing `dde8f2e` with `8d7d84b` through the unchanged benchmark
infrastructure. VProver includes only the established IndBen-156 subset.
These are individual-goal results with the source theory available; earlier
benchmark lemmas may be supplied as assumptions. The comparison measures proof
coverage, with no speedup claim.

[Measurement details and per-suite results](https://github.com/samth/waterfall/blob/main/docs/benchmarks/2026-09-22.md).

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
rev = "main"
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
