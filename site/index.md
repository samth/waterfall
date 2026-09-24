# waterfall

<nav aria-label="On this page">

[Usage](#usage) · [Search](#how-it-works) · [Options](#configure) · [Results](#results) · [Lake package](#install)

</nav>

waterfall is an automated theorem prover for Lean 4, inspired by ACL2. It can automatically
discharge many goals that require induction, case analysis, and simplification, and lemma application,
and uses `simp_all` and `grind` as leaf solvers. It's designed to work well for the kinds of recursive definitions and proofs that arise in programming language semantics and program verification, but is generally applicable to any Lean goal.

The accumulator invariant for an in-order traversal, adapted from Software Foundations’ VFA
SearchTree chapter:

```lean
theorem fast_elements_helper (t : Tree V) (acc : List (Nat × V)) :
    fastElements t acc = elements t ++ acc := by
  waterfall
```

`waterfall` selects an induction scheme and searches for the case proofs. The
definitions are found automatically in this module; associativity of `++` is already a standard
simplification rule. This proof also succeeds with `waterfall (mode := .committed)`.

<details id="tree-proof">

<summary>Definitions and complete proof</summary>

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

</details>

<section id="usage">

## Usage

`waterfall` closes the complete displayed proof state. If search fails, it restores the input
proof state, so it can also be tried as the last tactic in an existing branch.

`waterfall` uses local hypotheses, Lean’s registered `simp` and `grind` rules, and definitions
referenced in the goal or hypotheses that originate in the current module. Local hypotheses support both
backward application and forward instantiation.

An optional rule list, as in `waterfall [f, h]`, supplies additional definitions and facts to
`simp_all`, `grind` and backward theorem application. This is useful for imported definitions
and lemmas that are not registered for rewriting or instantiation. Supplied recursive
definitions also expose candidates for `fun_induction` and `fun_cases`. Library theorem
application does not search for arbitrary rewrite rules.

The [compiled tutorial](../Tutorial/Guide.lean) gives invocation examples; the [SF
examples](examples.md) show some complete proofs.

<a id="proof-hints"></a>

### Proof scripts

`waterfall?` records the accepted proof path, renders it as tactic syntax, and validates the
replacement from the original checkpoint. Backtracked branches are omitted. Leaf calls to
`simp_all` and `grind` remain in the generated script.

Operations without a tactic rendering fall back to an explicit proof term. Rendering and
re-elaboration add overhead beyond discovery; both modes and parallel execution support hints.

</section>

<section id="how-it-works">

## Search and commitment

The goal of `waterfall` is to combine Lean-style proofs with ACL2-style search. It automatically considers induction, case analysis, and simplification, and if one of those fails, it backtracks and tries another. When a local rule is blocked by one missing proposition, it can use that proposition as a focused case split.

The default policy performs depth-first search over complete proof continuations, with iterative
deepening in structural cost and solver strength. A checkpoint includes all sibling obligations
and their shared metavariable context, so even a successful local closure remains backtrackable
until the entire continuation succeeds.

`(mode := .committed)` instead commits to the first locally progressing transition. It exhausts
non-inductive processing across the agenda before considering induction, with one permitted
return to the original conjecture at that boundary per trial. Stalled goals are reconsidered
after progress in a sibling, since shared metavariable assignments may have changed. Discarded
alternatives are not recovered by increasing the budget.


</section>

<section id="configure">

## Options

```lean
waterfall (mode := .committed) (effort := 3000)
```

Both `waterfall` and `waterfall?` accept individual options or a structure such as `(config :=
{mode := .search, effort := 3000})`.

<div class="table-scroll">

| Option | Default | Effect |
| --- | --- | --- |
| `mode` | `.search` | `.committed` disables backtracking after local progress. |
| `effort` | `1000` | Global budget for dispatched operations and charged restarts, including failed attempts. |
| `cpus` | `1` | Maximum concurrent depth/strength trials, sharing the total attempt and heartbeat budgets. |
| `attemptHeartbeats` | `20000000` | Base raw-heartbeat slice per operation, scaled by trial strength. |
| `lazy` | `true` | Generate each candidate batch when reached. False enumerates all batches in a phase up front. |
| `deferChecks` | `false` | True postpones applicability checks until a candidate is considered. |
| `report` | `false` | `true` prints search statistics. |

</div>

<a id="budgets"></a>

### Effort and time limits

`effort` controls both how such search is performed, and how much effort leaf tactics like `grind` apply. Effort is consumed by attempted proof plans, even if they fail and backtrack. The default of 1,000 is good for interactive use, but bigger budgets will be needed in some cases.

`attemptHeartbeats` is the base raw-heartbeat slice per operation, scaled by trial strength and
capped by the enclosing remaining allowance. Lean’s `maxHeartbeats` uses thousands of raw
heartbeats. These limits are independent of the attempt budget and of `maxRecDepth`. A proof
that needs more total work also needs a larger enclosing `set_option maxHeartbeats ... in` limit.

`report := true` prints the attempts, visited nodes, successful trial depth and strength, raw
heartbeat use, and the retained operation labels.

<a id="parallel"></a>

### Parallel execution

```lean
waterfall (cpus := 4) (effort := 3000)
```

Specifying `cpus` allows multiple paths to be explored concurrently. Each worker shares the total budget, and the first successful proof wins.  `cpus := 1` selects sequential operation.

</section>

<section id="results">

## Benchmark results

On the full 2,645-entry inductive-bench selection, `waterfall` proves **1,615 of
2,631 theorem goals**, up from **1,594**: 22 gains and 1 loss on the same
inputs. The remaining 14 entries are executable definitions, excluded from the
goal counts below.

<div class="table-scroll">

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

</div>

Measured on 2026-09-24 with Lean 4.30.0, default search, effort 1,000, and one
Lean thread, comparing `dde8f2e` with `f3c5ca3` through the unchanged benchmark
infrastructure. VProver includes only the established IndBen-156 subset.
These are individual-goal results with the source theory available; earlier
benchmark lemmas may be supplied as assumptions. The comparison measures proof
coverage, with no speedup claim.

[Measurement details and per-suite results](https://github.com/samth/waterfall/blob/main/docs/benchmarks/2026-09-24.md).

</section>

<section id="install">

## Lake package

waterfall 0.2.0 is available from [samth/waterfall](https://github.com/samth/waterfall).
A Lean project's `lakefile.toml` can depend on the Git repository:

```toml
[[require]]
name = "waterfall"
git = "https://github.com/samth/waterfall.git"
rev = "v0.2.0"
```

The package depends only on Lean, targets 4.33.1, and is also tested on 4.30.0. A dependent
project must use a matching toolchain. Its tactics are exported by `import waterfall`.
Lake records the resolved Git commit in `lake-manifest.json`. 

[Lean tutorial](../Tutorial/Guide.lean)

</section>
