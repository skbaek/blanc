-- ProrataWethVaultRevertSteps.lean : the vault's revert-cause vocabulary, its
-- terminal inventory, and the revert-aware walk adapters the nonrevert cores use.

import Blanc.RevertCause
import Blanc.Composition.ProrataWethVaultBoundary

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-- A compiled step that is a `CALL` or `STATICCALL` to the configured WETH
account whose pushed status word is zero: the child reverted or halted, or the
call was refused at the call-depth limit.  Nothing else about the child is
assumed, and nothing about the parent is concluded here. -/
def WethChildRefused (_sevm : Sevm) (callPre : Devm) (instruction : Ninst)
    (callPost : Devm) : Prop :=
  (instruction = Ninst.call ∨ instruction = Ninst.staticcall) ∧
    callPre.stack[1]? = some wethAccount.toB256 ∧
    callPost.stack.head? = some (0 : B256)

end Blanc.Composition.ProrataWethVault
