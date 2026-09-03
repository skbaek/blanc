-- ProrataWethVaultMessage.lean : one message preserves the vault's ledger.

import Blanc.Composition.ProrataWethVaultInbound
import Blanc.Composition.ProrataWethVaultOutbound
import Blanc.Composition.ProrataWethVaultBacking
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

/-- **The unconditional part.**  Every target except the four ERC-4626 flows
preserves the ledger with no premise about the asset at all — no configuration,
no child-call resources.  Those twenty-one are exactly the targets that make no
external call, and stating them separately marks where the configuration
genuinely enters rather than leaving it bundled with everything else. -/
theorem vault_nonflow_message_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (notDeposit :
      Sevm.selector sevm ≠ selector "deposit" [.uint256, .address])
    (notMint : Sevm.selector sevm ≠ selector "mint" [.uint256, .address])
    (notWithdraw : Sevm.selector sevm ≠
      selector "withdraw" [.uint256, .address, .address])
    (notRedeem : Sevm.selector sevm ≠
      selector "redeem" [.uint256, .address, .address])
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨body, member⟩ :=
    Blanc.ProrataWethVault.selector_mem_vaultFuncs_of_ok run
  simp only [Blanc.ProrataWethVault.vaultFuncs, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at member
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
  · exact absurd sel notDeposit
  · exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.balanceOf) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · exact absurd sel notMint
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
  · exact absurd sel notWithdraw
  · exact absurd sel notRedeem
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


/-! ## The configured two-runtime root

The state a configured history starts from: both runtimes installed at their
own accounts, distinct and non-precompile, and the vault's storage empty.  The
joint invariant holds there for the reason genesis always does — an empty
ledger is conserved and cannot exceed any bound — and the point of naming it is
that everything above this rung may then reason forward from it rather than
assuming an invariant out of the air. -/

/-- Both runtimes installed, the asset pinned, and the vault untouched. -/
structure ConfiguredRoot (vault : Adr) (sevm : Sevm) (pre : Devm) : Prop where
  /-- The asset account holds the exact WETH runtime, is distinct from the
  vault and is not a precompile. -/
  configured : DirectWethConfiguration vault sevm pre
  /-- The vault account holds the exact vault runtime. -/
  installed : some (pre.getCode vault).toList =
    Prog.compile Blanc.ProrataWethVault.vault
  /-- The vault's storage reads zero everywhere: no shares, no supply, no
  allowances. -/
  untouched : ∀ key, (Devm.getStor pre vault).get key = 0

/-- The root conserves the share ledger. -/
theorem ConfiguredRoot.conserved {vault : Adr} {sevm : Sevm} {pre : Devm}
    (root : ConfiguredRoot vault sevm pre) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre vault) :=
  LedgerConserved.of_get_eq_zero root.untouched

/-- The root satisfies the joint two-contract invariant, at any WETH row. -/
theorem ConfiguredRoot.backed {vault : Adr} {sevm : Sevm} {pre : Devm}
    (root : ConfiguredRoot vault sevm pre) :
    PairBacked vault (Devm.getStor pre vault)
      (Devm.getStor pre wethAccount) :=
  PairBacked.of_vault_empty root.untouched

/-- The vault's own code at the root is the compiled program, in the form the
frame-level obligations consume. -/
theorem ConfiguredRoot.vaultInstalled {vault : Adr} {sevm : Sevm} {pre : Devm}
    (root : ConfiguredRoot vault sevm pre) :
    ProgramInstalledAt pre.state vault Blanc.ProrataWethVault.vault := by
  unfold ProgramInstalledAt
  exact root.installed



/-! ## Chained messages

Conservation from a configured root across any number of vault messages.

**What this is and is not.** It is the ladder's history rung restricted to the
vault's *own* messages: each step is a message at the vault, and the invariant
survives all of them. It is not yet a block or chain history, because it does
not say that a message to some *other* account leaves the vault's storage
alone. That claim needs the other account's code, and the generic
`ContractSpec` ladder — which supplies exactly that reasoning through
`Exec.InvDepth` — cannot carry this vault's flows, for the reason recorded in
`Blanc/ProrataWethVaultLedgerSpec.lean`. Naming the restriction here is the
point: an unqualified "history" claim would be broader than the evidence. -/

/-- A sequence of vault messages, each configured and resourced at its own
entry state. -/
inductive ConfiguredMessages (vault : Adr) : Devm → Devm → Prop
  | refl (s : Devm) : ConfiguredMessages vault s s
  | step {s t u : Devm} {sevm : Sevm} :
      ConfiguredMessages vault s t →
      sevm.currentTarget = vault →
      DirectWethConfiguration vault sevm t →
      Mem.Wf t.memory →
      InboundCompiledResources sevm Blanc.ProrataWethVault.amountWord →
      InboundCompiledResources sevm Blanc.ProrataWethVault.quoteWord →
      OutboundCompiledResources sevm Blanc.ProrataWethVault.amountWord →
      OutboundCompiledResources sevm Blanc.ProrataWethVault.quoteWord →
      Prog.RunCompiled sevm t Blanc.ProrataWethVault.vault u →
      ConfiguredMessages vault s u

/-- **Chained preservation.**  Every message in the chain preserves the ledger,
so the chain does. -/
theorem ConfiguredMessages.preserves_conserved {vault : Adr} {s t : Devm}
    (chain : ConfiguredMessages vault s t)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor s vault)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor t vault) := by
  induction chain with
  | refl => exact conserved
  | step _ target config memoryWf depositR mintR withdrawR redeemR run ih =>
      subst target
      exact vault_message_preserves_conserved config memoryWf depositR mintR
        withdrawR redeemR run ih

/-- **From the root.**  A configured two-runtime root conserves the ledger, and
every reachable state along a chain of vault messages still does. -/
theorem ConfiguredRoot.chain_conserved {vault : Adr} {sevm : Sevm}
    {pre post : Devm}
    (root : ConfiguredRoot vault sevm pre)
    (chain : ConfiguredMessages vault pre post) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post vault) :=
  chain.preserves_conserved root.conserved


end Blanc.Composition.ProrataWethVault
