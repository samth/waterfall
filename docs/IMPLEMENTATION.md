# Reading the proof engine

Start with `movesFor` in [Operations.lean](../waterfall/Operations.lean). Its eight cases are
the proof vocabulary. Each calls a named generator that **proposes** proof steps;
it does not yet apply them. A `Move` holds the deferred inference, its intrinsic
cost, and semantic metadata for scheduling. Array order matters: recorded plans
identify a step by its group and its original ordinal.

| Generator | What it contributes to a proof |
| --- | --- |
| `closeGoal` | Assumption/reflexivity/contradiction, arithmetic, simplification, grind, and constructors that can close a leaf |
| `prepareGoal` | Introduce binders, turn function equality into pointwise equality, normalize, or split the target |
| `analyzeHypotheses` | Split expressions in assumptions and invert inductive evidence, including registered case views |
| `applyRules` | Apply an assumption or supplied theorem backward; construct the target with premises left as obligations |
| `applyLibraryTheorems` | Retrieve indexed library theorems and propose each applicable direction separately |
| `instantiateHypotheses` | Apply a quantified assumption to an existing term or bounded constructor chain, adding a derived fact |
| `followRecursion` | Perform functional induction or case analysis on a recursive call appearing in the problem |
| `inductOrAnalyzeData` | Induct on data or evidence with several motives, or try ordinary data case analysis |

Smaller proof operations have their own names too. `simplification` configures
the same strength-scaled simplifier for closure and normalization. `caseAlternatives`
offers the registered view before raw cases and respects Lean's
`tactic.customEliminators` option. `Critics.implicitWitnesses` proposes one
constructor layer for one implicit argument whose type visibly reduces to an
inductive type; it does not synthesize nested terms, multiple witnesses, or
arbitrary lemma arguments. Every unresolved constructor field remains an
obligation. Local functions can also be applied to data-valued goals, including
Type-valued induction hypotheses. `Critics.fixedIndices` proposes equation-preserving
index abstraction, optionally combined with the caller's parameter generalization.
`Critics.inductionMotives` selects the structural-induction parameters and
composes those alternatives with fixed-index repair; `Critics.functionalInduction`
selects parameters outside a recursive call. `Operations` chooses subjects and
computes their scheduling summaries, but does not select generalizations.

[FocusingCritics.lean](../waterfall/FocusingCritics.lean) supplies
`Critics.indexedFocus`: introductions followed by constructor-constrained
inversion of recursive evidence. It uses actual inductive indices, combines
strictly shrinking singleton inversions along the same index of the same relation,
and retains all branching obligations. Classification indices such as colors do
not drive this structural preparation. The relation must constrain that index
in its own constructors; generic transitive closures do not qualify. Assigned hypothesis types are resolved
before their index metadata is inspected.
A rejected later inversion restores the last accepted child. The introduction
block and visible constructors contribute to structural cost, so a fused proof
does not prematurely finish one sibling at depths too small for the others. This is an ordinary
backtrackable move; separate introduction, cases and induction moves remain.

[Generalization.lean](../waterfall/Generalization.lean) executes and renders the
exact plan stored on a move: parameter reversion followed by expression
abstraction in the target and selected hypotheses, with explicit equation
retention. [Induction.lean](../waterfall/Induction.lean) adds the continuation.
Ordinary induction reintroduces the complete reverted dependency closure;
functional induction leaves it quantified. Candidate identity compares the same
plan, so different selections cannot be conflated solely because their counts
agree. Selection stays in critics; these shared operations choose no strategy.

## From a proposed step to a complete proof

`expand` selects one `Job` from a `Node`, prepares rules, and lazily enumerates
the requested stages. Each candidate receives its stable identifier before
applicability filtering or policy reordering. `Execution.attempt` charges the global work
allowance and runs one inference inside a bounded heartbeat slice. A closer is
accepted only if it leaves no children. Built-in steps request local stutter
pruning: a single unchanged conjecture is rejected by `conjectureShape`.
Extensions default to allowing local stutter because a step may advance a
shared witness or another obligation. `Move.checkLocalChange` makes this
heuristic explicit; every structural transition still spends positive depth.

Successful local inference is still only a proposal. The successor checkpoint
contains its new child obligations **and every pending sibling**, under the same
Lean metavariable assignments. `proveAll` passes these whole checkpoints to the
policy and follows the selected continuations. For example, choosing a witness
for an existential may make its first premise true and its second false. The
default policy can restore the entire earlier state and try another witness.
Proving siblings independently and combining their assignments would be wrong.

At the `grind` leaf, [Leaf.lean](../waterfall/Leaf.lean) compiles plain global
theorem parameters using Lean's first successful pattern choice. It skips the
later pattern suggestions that Lean computes for an interactive parameter, then
passes the resulting parameters to Lean's protected `grind` context. Other
parameters, requested suggestions, local declarations, and editor code actions
use Lean's parameter elaborator. The adapter changes neither the scaled `grind`
limits nor Waterfall's search order. Routine leaves keep `grind`'s verbose
diagnostics off; Waterfall tracing or diagnostics turns them on.

`run` first executes any bounded `PreludeTrial`s requested by the installed
hooks, then calls `proveAtDepthAndStrength` along the configured fair trial schedule. A
failed prelude can use at most one quarter of the remaining effort and cannot remove a
later trial. Depth
limits structural proof steps; strength increases solver limits and their
heartbeat slices. The default diagonal schedule reaches structural depth after
one shallow solver trial. Simplifier rewrite steps grow linearly with strength;
recursive discharge depth grows more slowly, avoiding a large branching increase
on every trial. Both limits remain unbounded as strength increases.

Contradiction also contains recursive case analysis. Direct `False` goals receive
Lean's ordinary fuel multiplied by strength; speculative contradiction on other
targets starts with fuel equal to strength. Thus recursive refutation remains
available without charging its full initial cost at every search node.

Effort counts attempts across every failed branch and trial.
Only after the whole agenda closes are retained `Selection`s delivered to
observers. `Execution.checkComplete` verifies every original root has a proof without
unresolved metavariables or direct sorry terms. Lean checks the declarations.

## Where the other pieces belong

[Protocol.lean](../waterfall/Protocol.lean) defines the shared data and callbacks:
resource `Config`, spent-work `Stats`, proof `Move`s and `Selection`s, pending
`Job`s, compatible `Node`s, and the policy's `Space`. Moving Config and Stats here
keeps these interfaces together; it does not reduce the total implementation.

[Execution.lean](../waterfall/Execution.lean) meters one deferred move and
performs final root validation. [Repair.lean](../waterfall/Repair.lean) defines
`Critic`: an evidence type and two functions, observation and repair construction.
Each runs under tactic-state rollback. Its lazy producer hands ordinary `Move`s
to its consumer; a small adapter appends them through `Hooks.extraMoves`.

[Critics.lean](../waterfall/Critics.lean) implements two consumers of that
interface. The blocked-premise critic proposes a split when a local rule matches
the target except for one proposition and another premise is present. The
quantified-rewrite critic matches a local equality at a target subexpression,
records the rule and direction, then reconstructs the specialization during
execution. Conditional premises become sibling obligations. Quantified rewriting is
opt-in through `Critic.hooks`; the default hypothesis hook installs the
blocked-premise provider. [ConstructorCritics.lean](../waterfall/ConstructorCritics.lean)
and [InductionCritics.lean](../waterfall/InductionCritics.lean) supply the built-in
implicit-witness and fixed-index repairs directly at their existing generation
points. [ArithmeticWitness.lean](../waterfall/ArithmeticWitness.lean) supplies an
optional arithmetic provider. None owns a search loop, trial schedule, or proof
acceptance path.

`Critic.hooksFor` selects an operation group and passes rules, strength and
remaining depth to a provider factory. Appending through this adapter preserves
existing selectors. Embedded uses of `Critic.propose` also preserve the placement
of repairs relative to each ordinary operation, such as a major premise's direct
and generalized induction alternatives.

[Scheduling.lean](../waterfall/Scheduling.lean) independently performs bounded
lookahead after introductions and orders preparatory moves before expensive
closure. It accepts an arbitrary move producer, without inspecting obstruction
types or critic names. Search mode composes this scheduler with the default
critics; committed mode uses the same repairs with its own traversal.

The default policy follows every continuation in order. [Committed.lean](../waterfall/Committed.lean)
uses the same operations with first-progress commitment, ordinary work before
induction, and one return to the original conjecture per trial. It deliberately
discards alternatives. [Parallel.lean](../waterfall/Parallel.lean) distributes
depth/strength trials of either policy across isolated workers; it shares work
accounting and adopts only a whole completed proof. These modules do not add
inference rules.

[Observe.lean](../waterfall/Observe.lean) adds optional timing, resource control,
recording, and exact-plan replay through middleware. [Tactic.lean](../waterfall/Tactic.lean)
parses the public options. The proof engine owns rollback and acceptance; IO
counters and other external callback effects cannot be rolled back.

[Suggestions.lean](../waterfall/Suggestions.lean) records only the accepted path,
renders ordinary proof commands, and checks the printed text from the original
checkpoint. Tactic adapters share existing commands through optional metadata;
Meta operations have frontend recipes for induction, cases and constructors.
Generalization and induction commands come from the move's exact preparation
plan, including fixed-index repair. The frontend does not reconstruct parameter
selection from the context or infer it from motive tags.
Forward instantiation prints `have` using the small derivation supplied to
`MVarId.note`, recovered from the winning assignment. The renderer reconstructs
a proof tree from the recorded agendas, independently of the order in which
search visited siblings. It replays that tree with explicit introduction names,
native induction/case alternatives, and nested bullets. Names in command recipes
are translated from the recorded context to the replayed context.

Ordinary `simp_all` and `grind` calls are tried before the scaled configurations
used during search; repeated rule arguments are removed. Exact leaves use
`exact`, `rfl`, or `contradiction` when possible. Each proposed replacement is
checked by parsing and elaborating its displayed text with recovery disabled.
This is presentation work and does not change proof discovery.

Extension moves are regenerated with their installed hooks; critics supply
ordinary proof commands through `Move.command?`. Shared witness dependencies or
an adapter's context changes may prevent tree rendering. In that case the
frontend retains the checked execution-order script; if recipes also fail, it
prints the completed proof term, inlining solver-generated auxiliary declarations.
These fallbacks can still contain explicit naming or goal-navigation commands.
Each parallel worker has its own recorder; only the winning worker's hint is
retained.

## Refactoring boundary

The core proof engine and metered move execution are unchanged by the critic
interface. Proof search, speculative analysis and individual repair operations
remain independently reviewable. The hint frontend adds no inference family,
search policy, or external dependency.
