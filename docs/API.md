# API reference

Lean doc comments provide hover documentation in the editor. `Tutorial/Guide.lean`
is a compiled tutorial. `Tests/PublicAPI.lean` checks the declaration-level
interface below, while `Tests/ModuleImport.lean` and `Tests/Import.lean` check
module and ordinary source-file consumers. The library exports the following
small interfaces.

| Module | Responsibility |
| --- | --- |
| `waterfall` / `waterfall.Tactic` | `waterfall`, `waterfall?`, `Mode`, `Options` |
| `waterfall.Core` | `run` and engine transitions |
| `waterfall.Protocol` | `Config`, `Stats`, `Move`, `Candidate`, `Job`, `Node`, `Space`, `SearchPolicy`, `Hooks` |
| `waterfall.Execution` | Metered move execution and final root validation |
| `waterfall.Repair` | Typed obstruction analysis and deferred repair proposals |
| `waterfall.Critics` | Blocked-premise splitting and quantified-equality specialization |
| `waterfall.ArithmeticWitness` | Optional arithmetic witness synthesis through `Critic` |
| `waterfall.ConstructorCritics` | Built-in implicit constructor-witness repairs |
| `waterfall.InductionCritics` | Built-in equation-preserving fixed-index repairs |
| `waterfall.Induction` | Ordinary induction on an already-prepared major premise |
| `waterfall.Scheduling` | Bounded preparation lookahead and staged search |
| `waterfall.Choices` | Generic lazy selection, filtering, collection and commitment |
| `waterfall.Parallel` | Isolated concurrent trials, shared work accounting and cancellation |
| `waterfall.Committed` | ACL2-inspired callbacks over the shared engine |
| `waterfall.Suggestions` | Checked standalone scripts and editor hints from retained paths |
| `waterfall.Observe` | Optional timing, control middleware, action recording and replay |
| `waterfall.Canonical` | Optional canonical goal encoding for replay checks |

The [proof architecture walkthrough](IMPLEMENTATION.md) maps these interfaces to
the named proof-stage generators and explains how their child obligations form
one compatible proof continuation. Generator helpers are private; extensions
use `movesFor`, `operations`, and `Hooks`.

## Tactic interface

`Options` extends engine `Config` with `mode : Mode := .search` and `cpus : Nat := 1`. Standard Lean configuration syntax accepts
individual fields or `(config := { ... })`. The adapter passes
`mode.hooks` and `Options.toConfig` to `Parallel.run`; one CPU calls `run` directly. Custom callback functions are
configured through `run`, preserving the arbitrary typed policy state interface.
It adds no proof-search algorithm.

`run (cfg : Config) (rules : Array (TSyntax term) := #[]) (hooks : Hooks := {})`
runs in `TacticM` and returns `Stats` after closing all original goals. Failure
restores Lean's original proof state. Effort and external observer effects are
not rolled back. `Stats.choices` contains retained labels in reverse proof order.

`waterfall?` installs `Suggestions.run` inside each worker. It records only
accepted steps and gives the winning proof a checked editor replacement.
Suggestions prefer explicit `intro` names, native induction/case alternatives,
and nested bullets. Solver configurations are omitted when ordinary defaults
replay successfully. Shared-goal dependencies or unsupported structured recipes
can require an execution-order script or proof-term fallback.
`Suggestions.compile` accepts the input checkpoint, original goals, retained
path, rules and optional hooks; it returns `Script` (`tactic`, `text`, `usedTerm`) while restoring
the completed proof. It reparses the printed text and requires all original
obligations to close with error recovery disabled. The inference operations and
accepted-step hook contract are unchanged. `Move.subject` identifies the
expression acted upon; `Move.command?` optionally shares a command an adapter
already constructs. These are presentation metadata, independent of dispatch,
cost and policy selection. A command proposal is always checked as printed text.

## Search and checkpoints

`Choices α = (α → TacticM Bool) → TacticM Bool` is effectful lazy enumeration.
Returning `true` from a visitor stops it. `Choices.first` commits to the first
emitted choice even if its downstream continuation fails; `filter` retains a
subsequence; `collect` eagerly materializes all emitted choices and pays their
cost.

A `Node σ` contains a saved Lean proof state, all pending `Job`s, typed policy
state and the retained plan. Each job has its own remaining structural allowance
and ancestry. Never combine jobs from one checkpoint with Lean state from another.

A `SearchPolicy` supplies its state type, initial state and
`choose : Space State → Choices (Node State)`. `Space.expand` enumerates metered
transitions for a selected goal and operation batches. `Space.restart` restores
a compatible checkpoint, installs new policy state and charges an attempt.
Already funded frontier entries remain selectable at attempt exhaustion; new
expansion and restart are refused. Ambient limits still constrain traversal.

## Hooks

- `charge`: reserve one operation before dispatch, including checkpoint restarts.
  Exceptions stop the run; reservations and external effects are not rolled back.
- `policy`: choose transitions, agenda order and traversal.
- `prelude`: infer bounded depth/strength trials from the original goals. Each
  request has its own attempt cap and the engine also limits all such work to
  one quarter of the effort remaining when that trial starts. The ordinary `trials` schedule remains intact.
- `trials`: finite batches of depth/positive-strength pairs by round.
- `batches`: lazy structural groups; each original group must occur exactly once.
- `order`: a permutation of candidate selectors within a batch; validated.
- `cost`: effective path cost under the goal's context and rollback. Structural
  costs must respect the engine's positive intrinsic floor.
- `extraMoves`: append general operations without renumbering the originals.
- `around`: polymorphic middleware around a span and continuation.
- `accepted`: observe only the retained complete proof's selections, in reverse order.

`Move.preparation` distinguishes one-binder introduction, bulk introduction,
pointwise equality, normalization and target splitting. Policies should use
this typed field rather than diagnostic labels. Scheduling consumes this
metadata independently of the providers that produced it.

## Proof critics

A `Critic` supplies three things: its own `Evidence` type, an `observe` function
from a goal to evidence, and a `repair` function from evidence to deferred
`Move`s. Neither function executes the proposed proof search. `Critic.propose`
runs both under full tactic-state rollback and exposes a `Choices Move` producer;
repair construction stops when its consumer accepts a proposal. Evidence and
returned moves must refer only to the input checkpoint. Temporary metavariables
created while probing cannot escape; a recipe can reconstruct them on execution.
External IO effects are not rolled back.

`Critic.hooks critics inner group` appends repairs in the selected group (by
default, hypotheses), preserving all existing moves and the consumer's policy,
ordering, trials and middleware.
This batch adapter materializes proposals; the producer interface itself can be
consumed lazily. Custom operations remain available through `Hooks.extraMoves`.

`Critic.hooksFor group factory inner` accepts a factory of type
`Array (TSyntax term) → Nat → Nat → Array Critic`. Its arguments are the supplied
rules, current strength and remaining structural depth. The factory is called
only for the selected group. It can specialize a provider's analysis without
adding effort accounting or search decisions to the critic itself.

The built-in `Critics.implicitWitnesses constructor` remains in the rules group
at cost two. `Critics.inductionMotives major summary` proposes parameter
generalization, direct induction, and `Critics.fixedIndices` repairs, in that
order, for each major premise. `Critics.functionalInduction call summary` selects
the parameters outside a recursive call. These critics are consumed through
`propose` at their original generation points, preserving costs and action
selectors. Installing them again through hooks would duplicate proposals.

`Move.generalization : Generalization.Plan` records exact preparation choices:

- `clearBefore`: declarations to try clearing before motive preparation;
- `clearAfter`: obsolete inputs to try clearing after abstraction;
- `parameters`: local declarations to revert, including their dependency closure;
- `abstractions`: expressions and whether to retain each defining equation;
- `hypotheses`: where to abstract in addition to the target (empty means target only).

The plan refers to the move's input checkpoint. Clearing is speculative context
strengthening: dependent declarations can prevent it, and every resulting goal
still needs a proof. The renderer uses the same order of `try clear` commands.
Parameters are reverted before
expression abstraction, so abstraction expressions and hypothesis identifiers
must remain valid after reversion. `Generalization.prepare goal plan` returns
the prepared goal, the substitution for changed hypotheses, and the complete
reverted dependency closure. `Generalization.commands plan` renders the same
preparation; it does not select parameters again. Dropping an abstraction's
equation strengthens the conjecture and can lose provability; built-in index
repair retains equations.

`Induction.withPlan goal subject plan functional` combines preparation with
ordinary or functional induction. Ordinary induction reintroduces the complete
reverted dependency closure into each case; functional induction keeps those
parameters quantified. `Induction.perform` remains the lower-level ordinary
induction executor. `Induction.command` renders the plan and its continuation.
All displayed scripts are independently checked by the suggestion frontend.

A new generalization strategy can be an ordinary selector inside a critic. It
sets the resulting move's `generalization` and uses `Induction.withPlan`; no
additional strategy registry or search policy is needed. `InductionPlan.equivalent`
compares exact plans as well as summaries, so equal-size selections of different
variables remain distinct. It is still not an equality test for arbitrary
executable closures: extensions must distinguish any other execution choices
in their metadata before using deduplication. Recorded JSON plans retain action
selectors rather than checkpoint-local expressions; replay regenerates the moves.

`ContinuationCritics` supplies typed providers for conditional fact composition,
transparent supplied equations, recursive equality orientation, shared recursive
results, and fixed-parameter induction continuations. Their evidence consists of
input-local IDs, expressions, syntax, and explicit generalization plans. They are
consumed at their operation-group insertion points; stronger trials enable the
additional premise-only and conditional-composition variants.
`Recursion` shares context/call analysis without choosing a traversal.
`RecursionScheduling` and `Continuations` select bounded contours independently;
main's `Scheduling.preparations` middleware still orders contextual preparations.
Each trial receives at most one quarter of its starting remaining effort and a
bounded share of remaining heartbeats. `PreludeTrial.tag` is an opaque policy selector,
carried by `Node.trialTag`; it has no interpretation in the engine. The combined
recursion portfolio requests at most one eighth of effort for its two early
orders, one tenth for its ordinary prefix, and one quarter for deeper repairs.
Thus at least half remains for the fair schedule, independently of the generic
engine's per-trial cap.

The default hypothesis provider is `Critics.blockedPremise`: case-split the sole unknown
premise of an otherwise applicable local rule. The optional
`Critics.quantifiedRewrite` specializes a quantified equality at a target
subexpression. It offers
contracting rewrites or rewrites exposing reflexivity/an existing assumption.
It retains every conditional premise as an obligation. Both provide ordinary
proof commands for checked suggestions; neither controls search or commitment.

Importing `waterfall.ArithmeticWitness` makes `Critics.arithmeticWitness`
available without enabling it in the default tactic. It reads equations in an
existential over `Nat`, works backward through addition, multiplication,
successor and subtraction, and proposes a witness. For example, `n = 2 * k`
suggests `n / 2`. The original body remains an obligation, so truncation, a
failed divisibility condition, or an incompatible conjunct cannot be ignored.
The provider handles a single occurrence along an arithmetic expression; it is
not a complete arithmetic solver or a generator of arbitrary terms.

```lean
import waterfall
import waterfall.ArithmeticWitness

open waterfall in
example (n : Nat) : ∃ k, n = 3 * k + n % 3 := by
  run_tac
    discard <| run {} #[]
      (Critic.hooks #[Critics.arithmeticWitness] Mode.search.hooks)
```

The same adapter accepts `Mode.committed.hooks`; a committed search can retain
an unsuccessful witness choice, whereas search mode can backtrack over it.
`Tests/ArithmeticWitness.lean` checks corpus-shaped goals, invalid witnesses,
plan replay and standalone suggestions.

`Scheduling.exposesMoves producer` performs read-only lookahead after root
introductions. Search mode uses it with `Critics.propose` to decide whether to
request a bounded preparation trial. Any move producer can supply this lookahead.
`Scheduling.preparations` orders contextual repairs first within a batch and
prefers bulk introduction only when the supplied lookahead exposes a repair.
This ordering also applies in ordinary search; eager introduction elsewhere can
hide a useful whole-goal rule. `Scheduling.choose` separately places preparation
before expensive closers in the bounded trial, retaining all remaining stages.
Committed mode uses the same repair providers and contextual preparation ordering
with its own existing traversal.

An observer calls its continuation once and leaves proof state alone. Resource
control middleware can reduce allowances or abort spans. The engine owns proof
acceptance and rollback. Ordering and cost callbacks see temporary state;
external IO side effects remain the callback author's responsibility.

## Progress and extension operations

`Move.checkLocalChange` defaults to `false`. A structural extension may assign a
shared witness, change another obligation, or update local values while leaving
the selected target and assumption types unchanged. The engine accepts such a
transition and charges its positive structural cost. Final root validation is
unchanged; accepting a transition is not accepting a complete proof.

Built-in generators set `checkLocalChange := true` to preserve their existing
local stutter pruning. An extension can opt into this heuristic explicitly, or
implement its own progress checks in `Move.run`. The heuristic compares the
single child's target and assumption types with the input; it is deliberately
not a general test of proof-state equality. The engine's positive cost floor and
global attempt allowance still bound steps that leave a goal unchanged.

## Observation and replay

Import `waterfall.Observe` explicitly. `capture` returns a `Report` with success,
error, optional timing rows and an optional `Plan`. Timing rows distinguish
inclusive and exclusive wall-clock nanoseconds and raw heartbeats. A `Control`
can supply smaller per-span slices and a cooperative deadline. Deadlines are
checked between spans; a process timeout belongs to the calling harness.

Plans store versioned action selectors, goal/agenda encodings, selected focus,
strength, costs and generated-child counts. Replay validates these against the
same operations and supplied rules; it does not search for another route. Pass
a stable source/theory key and retain the exact source version. Changed
operations, selector order, costs or unrecorded provider state can invalidate a
plan. Final root validation and Lean's kernel remain authoritative.

See `Tests/SearchPolicy.lean` for a FIFO frontier, scored successors, commitment,
sibling dependencies and charged checkpoint recovery; see `Tests/Observe.lean`
for timing and replay examples.

## Parallel execution

`Parallel.run cpus cfg rules withHooks` runs the same engine in isolated workers.
`withHooks` receives a continuation accepting `Hooks`; call it once. Allocate
mutable observers inside this function so each worker owns separate IO references:

```lean
import waterfall
import waterfall.Observe

open Lean Elab Tactic waterfall
example (P : Prop) (h : P) : P := by
  run_tac
    discard <| Parallel.run 2 {} #[] fun use => do
      let recorder ← Observe.Recorder.create
      use (recorder.hooks {} Mode.search.hooks)
```

Round `i` of `Hooks.trials` belongs to worker `i % cpus`; bounded prelude trials
belong to worker zero. No trial is duplicated,
and all callbacks otherwise describe one policy. The first observed complete
proof wins; ordering among simultaneous completions is unspecified. This
parallelizes iterative deepening, not sibling proof obligations or branches
inside a single trial. Committed mode retains its local commitment semantics.

A mutex reserves attempts across workers, including restarts. Each worker has
its own engine counters and elaboration state. The enclosing remaining heartbeat
allowance is divided equally; unused shares are currently not redistributed.
Each worker records its spent heartbeats in a `finally` block, independently
of whether it returns a proof result or an interrupt. The parent always cancels,
joins, and reads these costs before adopting the winner. Actual child
heartbeats, including failed and cancelled work, are charged to the
parent's thread counter before acceptance. Aggregate overruns reject the result.
Workers use dedicated threads so a caller running inside Lean's elaboration
pool cannot starve them. Operating-system CPU affinity can impose lower CPU
concurrency than `cpus`; zero is rejected. No process or CPU affinity is created
by the tactic itself. The limit is per invocation, not a global limit on
concurrent theorem elaboration.

Parent cancellation and a completed proof signal cancellation to workers, which
are always joined. Cancellation remains cooperative inside Lean operations.
Increasing both work and heartbeat limits keeps every trial eventually available
when the underlying schedule is fair. A fixed total budget can produce different
coverage from sequential execution: speculation competes for the same resources.
Custom callbacks must not share mutable IO references unless synchronized; use
`withHooks` for per-worker recorders and other local state. Observer callbacks in
an unsuccessful worker may already have run and are not undone by cancellation.
`Stats.attempts` and `nodes` are aggregate counts; depth, strength and choices
identify the winning worker. `Observe.capture` remains a sequential convenience
API; use the initializer above for parallel observation.

### Indexed inversion preparation

`waterfall.FocusingCritics` exports `Critics.indexedFocus`. The built-in basic
operation group includes this critic before ordinary introductions. It fuses
introductions and shrinking constructor-indexed inversions into one backtrackable
move, keeping every resulting case as an obligation. It declines cycles rather
than committing to an unrolling, and retains the ordinary case-analysis moves.


### Experimental deferred solver budgets

This branch keeps the experiment disabled by default. The current frontend integration wraps search mode; committed mode keeps its existing hooks. `Move.heartbeatDivisor`
divides an operation's ordinary strength-scaled heartbeat slice; one preserves
the existing allowance. Zero is treated as one. Work spent on rejected or
resource-limited calls remains charged, and the engine retains rollback ownership.

`waterfall.DeferredSolvers.hooks` composes with existing hooks rather than replacing
the proof engine. The temporary options `waterfall.deferSolvers`,
`waterfall.solverCost`, and `waterfall.cheapSolverDivisor` enable weighted solver
admission, set the path cost for full solver operations, and bound their cheap
copies. A divisor of zero disables the copies. Target `simp`, full-context
`simp_all`, and both ordinary grind variants have independent bounded alternatives.
Exact and arithmetic closure precede these calls. Bounded copies appear only
when the full operation does not fit the current contour, avoiding two calls
at that same node. Full normalization is classified as solver work too.

Increasing search depth eventually admits every original full solver operation;
strength and the enclosing global limits still control runtime. This is a
reachability property, not a promise to preserve successes at a fixed effort or
heartbeat budget. The measured settings regress existing case-study proofs and
are not recommended as the default. The options are for further experiments.
Plans must be replayed with the same source, hooks and option settings.
