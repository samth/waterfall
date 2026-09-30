import waterfall
import Tests.PremisesBase
import Fixtures.Premises

/-!
Theorems from imported modules of the same project. This module and
Tests/PremisesBase.lean share the root `Tests`, so the public theorems proved there
are candidates here; its private theorems are not, since they cannot be cited here.
-/

namespace PremisesImport
open PremisesBase

-- `add_comm` comes from the imported module.
example (n m : M) : add n (add m .z) = add m n := by
  fail_if_success waterfall
  waterfall (premises := 4)

open Lean Elab Tactic in
example (n m : M) : add n m = add m n := by
  run_tac do
    let chosen ← waterfall.Premises.select (← getUnsolvedGoals) 64
    unless chosen.contains ``PremisesBase.add_comm do
      throwError "the imported theorem was not offered: {chosen}"
    if chosen.any isPrivateName then
      throwError "an imported private theorem was offered: {chosen}"
  exact add_comm n m

end PremisesImport

-- Explicit scope can cross module roots without admitting every library lemma.
-- Alternate scopes in one file to exercise the imported-candidate cache key.
open Lean Elab Tactic CrossRootPremises in
example (n m : N) : add n (add m .z) = add m n := by
  run_tac do
    let goals ← getUnsolvedGoals
    let narrow ← waterfall.Premises.select goals 64
    if narrow.contains ``CrossRootPremises.add_comm then
      throwError "cross-root lemma escaped the default scope"
    let broad ← waterfall.Premises.select goals 64 #[`Fixtures]
    unless broad.contains ``CrossRootPremises.add_comm do
      throwError "cross-root lemma was not offered"
    let narrowAgain ← waterfall.Premises.select goals 64
    if narrowAgain.contains ``CrossRootPremises.add_comm then
      throwError "candidate cache ignored the scope"
  waterfall (premises := 4) (premiseModules := #[`Fixtures])
