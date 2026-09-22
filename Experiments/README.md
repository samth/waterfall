# Functional induction continuations

The experiment's continuation critics now live in `waterfall/ContinuationCritics.lean`
and its bounded scheduling policy lives in `waterfall/Continuations.lean`.
`waterfall (effort := 10000) [definitions, lemmas]` enables the deeper portfolio.
The old `waterfall_induction` spelling delegates to the integrated search.

Relative to the pre-rebase prototype, the ordinary strength-one operation sequence
is preserved. Generalization execution and rendering now share main's explicit
`Generalization.Plan`; scheduling remains separate from typed repair evidence. Stronger trials add
fixed-parameter functional induction, speculative pruning of unrelated recursive
premises, generalization of recursive results shared only among hypotheses, and
conditional-hypothesis combination with explicit premise obligations.

Above the default effort budget, a bounded ordinary-search prefix precedes
separate constructor-first and normalization-first induction continuations.
Grounded root schemes are ranked using Lean's induction metadata. Deeper
structural exploration retains the cheap leaf-solver configuration: increasing
saturation limits at the same time can make a previously short proof expensive.
Each trial is capped at a quarter of its starting remaining effort and a share
of remaining heartbeats. Speculation uses rollback and complete kernel validation. The ordinary fair search
remains available. No theorem names or corpus-specific definitions occur in the
implementation.

The original opt-in measurements are historical results at `7b64217`, recorded
in the companion `lean-waterfall` repository's
`docs/reviews/2026-09-21/acl2-induction-continuations.md`. Later results, budgets,
regression controls and source/runtime hashes are recorded separately there.
