# Functional induction continuations

`InductionContinuations.lean` is an opt-in search-policy experiment. It uses the
existing Waterfall engine and does not change the default `waterfall` tactic.

```lean
import Experiments.InductionContinuations

-- Supply the same definitions and lemmas as the ordinary tactic.
-- waterfall_induction (effort := 10000) (report := true) [definitions, lemmas]
```

The experiment enumerates grounded functional-induction schemes, ranks the
number of recursive datatype targets using Lean's induction metadata, and gives
each root alternative a separate bounded contour. A direct root motive keeps
unrelated parameters fixed. The existing generalized motive remains available
for continuation search. This distinction matters: ordinary functional moves
always revert unrelated data parameters before induction.

A contour tries closure and normalization before a second functional induction.
It allows at most two functional inductions per branch before falling back to
other operations; the ordinary fair search still follows the finite contours.
All contours share the engine's existing quarter-effort reserve and proportional
heartbeat budget. No theorem names or corpus-specific definitions occur here.

Development checks use the exact ACL2 source-book goals and Lean 4.30 from the
companion experiment repository. The prototype finds ordered append and
permutation preservation of bounds automatically. Witness completeness still
needs the separately recorded guided plan, including removal of hypotheses
consumed by rewriting. Merely preferring Boolean guards did not fix the bounds
case; the direct motive did.

This is not enabled by default and has not been compared across the 111-goal
panel. The previous panel results therefore continue to describe the unchanged
default prover, not this optional policy. Proofs, failed controls, costs, and
source/runtime hashes are recorded in `lean-waterfall`'s
`docs/reviews/2026-09-21/acl2-induction-continuations.md` and its linked evidence.
