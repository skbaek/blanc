-- ProrataWethVaultTerminals.lean : whole-program static checks of the vault
-- used by the revert-cause headlines: its terminal inventory and pc-freedom.
--
-- Kept in its own leaf so that no language-server session elaborates the
-- whole-program kernel checks while the neighbouring proof modules are edited.

import Blanc.RevertCause
import Blanc.ProrataWethVault

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-! ## Terminal inventory

The revert-cause statements speak only about `EvmError.revert`.  This is their
structural companion: every terminal of the vault's source tree is `RETURN` or
the `REVERT` of a `Func.revert` node, so no vault guard is coded as some other
terminal (`STOP`, `SELFDESTRUCT`, or a bare `REVERT` whose garbage operands
could halt instead) that a revert-only statement would not see. -/

/-- **Every vault terminal is `RETURN` or a `Func.revert`.**  Checked over the
whole table `vault.main :: vault.aux`; a `.call` leaf is a table index and is
covered by the entry it names. -/
theorem vault_terminals_return_or_revert :
    ∀ f ∈ Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux,
      Func.TerminalsReturnOrRevert f := by
  have checked : (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux).all
        Func.terminalsReturnOrRevert = true := by
    decide +kernel
  intro f member
  exact Func.terminalsReturnOrRevert_sound (List.all_eq_true.mp checked f member)

/-- The vault program contains no `PC`, so its reverting frames invert to
gas-exact walks (`Prog.runCompiledTo_of_exec_revert`). -/
theorem vault_prog_pcFree :
    Prog.pcFree Blanc.ProrataWethVault.vault = true := by
  decide +kernel

end Blanc.Composition.ProrataWethVault
