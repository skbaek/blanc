-- ProrataWethVaultMessage.lean : one message preserves the vault's ledger.

import Blanc.Composition.ProrataWethVaultInbound
import Blanc.Composition.ProrataWethVaultOutbound
import Blanc.ProrataWethVaultLedgerSpec

/-!
# One vault message preserves the share ledger

The first rung above the frame.  A successful compiled run of the whole vault
program lands in exactly one of the twenty-five dispatch targets — that is
`selector_mem_vaultFuncs_of_ok`, and it is what makes the case analysis
complete rather than merely exhaustive-looking — and each target preserves
`LedgerConserved`.

Twenty-one of the branches are unconditional: the eighteen read-only targets
reach their obligation through `Func.SilentIn` at `Devm.storageView`, and the
three share writers through their body proofs.  The four ERC-4626 flows need
`DirectWethConfiguration`, because each snapshots the supply before its WETH
child and writes it after; `Blanc/ProrataWethVaultLedgerSpec.lean` records why
that premise is not removable.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-- A read-only target, entered at its endpoint and discharged by the
source-level obligation.  The dispatch entry moves no storage. -/
private theorem readOnly_message
    {sevm : Sevm} {pre post : Devm} {sig : B256} {words : Nat} {body : Func}
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = sig)
    (memberAll : (sig, Blanc.ProrataWethVault.routed words body) ∈ Blanc.ProrataWethVault.vaultFuncs)
    (memberRO : (sig, Blanc.ProrataWethVault.routed words body) ∈ Blanc.ProrataWethVault.readOnlyFuncs)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨endpointPre, entryState, -, -, -, endpointRun⟩ :=
    Blanc.ProrataWethVault.runCompiled_enters_endpoint_compiled_logs run selectorEq memberAll
  rw [congrFun (funext (getStor_eq_of_state_eq entryState))
    sevm.currentTarget] at conserved
  exact Blanc.ProrataWethVault.readOnly_preserves_conserved _ memberRO
    (Func.WalkInv.toRun (R := Func.RunOk) endpointRun) conserved

/-- **One message preserves the ledger.**  Twenty-five branches, one per
dispatch target, plus the impossibility of an unmatched selector. -/
theorem vault_message_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (depositResources : InboundCompiledResources sevm Blanc.ProrataWethVault.amountWord)
    (mintResources : InboundCompiledResources sevm Blanc.ProrataWethVault.quoteWord)
    (withdrawResources : OutboundCompiledResources sevm Blanc.ProrataWethVault.amountWord)
    (redeemResources : OutboundCompiledResources sevm Blanc.ProrataWethVault.quoteWord)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨body, member⟩ := Blanc.ProrataWethVault.selector_mem_vaultFuncs_of_ok run
  simp only [Blanc.ProrataWethVault.vaultFuncs, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at member
  rcases member with ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩
  · exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.totalAssets) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.name) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.convertToAssets) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact Blanc.ProrataWethVault.approve_preserves_conserved memoryWf run sel
      conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.previewWithdraw) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.totalSupply) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact Blanc.ProrataWethVault.transferFrom_preserves_conserved memoryWf run sel
      conserved
  · exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.decimals) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.asset) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.maxDeposit) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.previewRedeem) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact deposit_preserves_conserved config memoryWf depositResources run sel
      conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.balanceOf) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact mint_preserves_conserved config memoryWf mintResources run sel
      conserved
  · exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.symbol) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact Blanc.ProrataWethVault.transfer_preserves_conserved memoryWf run sel
      conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.previewMint) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact withdraw_preserves_conserved config memoryWf withdrawResources run sel
      conserved
  · exact redeem_preserves_conserved config memoryWf redeemResources run sel
      conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.maxMint) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.convertToShares) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.maxWithdraw) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.maxRedeem) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 2)
      (body := Blanc.ProrataWethVault.allowance) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.previewDeposit) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
end Blanc.Composition.ProrataWethVault
