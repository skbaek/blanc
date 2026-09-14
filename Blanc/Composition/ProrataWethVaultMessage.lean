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

/-! ## Configured flow obligations and the target bundle

The four ERC-4626 flows, stated as body-level configured obligations, plus
the uniform 25-target bundle they feed.  Each flow obligation is its
`Func.RunCompiledTo` body effect followed by the shared
inbound/outbound conservation step: no new premise beyond the SF, D9
(unused at this boundary — no allowance attribution here), and
`DirectWethConfiguration` threading.  The bundle holds the 25-way case
split once, so the one-message rung below becomes a soundness corollary
with an unchanged statement.
-/

-- Aux-table lookups, restated: the Inbound/Outbound copies are `private`.
private theorem depositAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.depositAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.depositAfterQuote := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.depositAfterQuoteSlot]

private theorem mintAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.mintAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.mintAfterQuote := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.mintAfterQuoteSlot]

private theorem withdrawAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.withdrawAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.withdrawAfterQuote := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.withdrawAfterQuoteSlot]

private theorem redeemAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.redeemAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.redeemAfterQuote := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.redeemAfterQuoteSlot]

private theorem withdrawBurn_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.withdrawBurnSlot]? =
      some Blanc.ProrataWethVault.withdrawBurn := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.withdrawBurnSlot]

private theorem redeemBurn_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.redeemBurnSlot]? =
      some Blanc.ProrataWethVault.redeemBurn := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.redeemBurnSlot]

-- Dispatch-table membership, restated: the Inbound/Outbound copies are `private`.
private theorem deposit_mem_vaultFuncs :
    (selector "deposit" [.uint256, .address],
      Blanc.ProrataWethVault.routed 2 Blanc.ProrataWethVault.deposit) ∈
      Blanc.ProrataWethVault.vaultFuncs := by
  simp [Blanc.ProrataWethVault.vaultFuncs]

private theorem mint_mem_vaultFuncs :
    (selector "mint" [.uint256, .address],
      Blanc.ProrataWethVault.routed 2 Blanc.ProrataWethVault.mint) ∈
      Blanc.ProrataWethVault.vaultFuncs := by
  simp [Blanc.ProrataWethVault.vaultFuncs]

private theorem withdraw_mem_vaultFuncs :
    (selector "withdraw" [.uint256, .address, .address],
      Blanc.ProrataWethVault.routed 3 Blanc.ProrataWethVault.withdraw) ∈
      Blanc.ProrataWethVault.vaultFuncs := by
  simp [Blanc.ProrataWethVault.vaultFuncs]

private theorem redeem_mem_vaultFuncs :
    (selector "redeem" [.uint256, .address, .address],
      Blanc.ProrataWethVault.routed 3 Blanc.ProrataWethVault.redeem) ∈
      Blanc.ProrataWethVault.vaultFuncs := by
  simp [Blanc.ProrataWethVault.vaultFuncs]

/-- Body-level configured obligation for `deposit`: the compiled body effect
is an `InboundEffect`, and every inbound effect preserves conservation. -/
theorem deposit_body_obligation
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (lookup : fs[Blanc.ProrataWethVault.depositAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.depositAfterQuote)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry
      Blanc.ProrataWethVault.deposit (.ok post))
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor entry sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨supply, supplyEq, stable, -, -, receiverValid, -, roomFits,
      effect⟩ :=
    deposit_body_effect config memoryWf lookup stack run
  exact inboundEffect_preserves_conserved receiverValid supplyEq stable
    roomFits effect conserved

/-- Body-level configured obligation for `mint`: mirror of `deposit`. -/
theorem mint_body_obligation
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (lookup : fs[Blanc.ProrataWethVault.mintAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.mintAfterQuote)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry
      Blanc.ProrataWethVault.mint (.ok post))
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor entry sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨supply, supplyEq, stable, -, -, receiverValid, -, roomFits,
      effect⟩ :=
    mint_body_effect config memoryWf lookup stack run
  exact inboundEffect_preserves_conserved receiverValid supplyEq stable
    roomFits effect conserved

/-- Body-level configured obligation for `withdraw`: the compiled body effect
is an `OutboundEffect` with the burnt shares covered by the owner, and every
covered outbound effect preserves conservation. -/
theorem withdraw_body_obligation
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (afterLookup : fs[Blanc.ProrataWethVault.withdrawAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.withdrawAfterQuote)
    (burnLookup : fs[Blanc.ProrataWethVault.withdrawBurnSlot]? =
      some Blanc.ProrataWethVault.withdrawBurn)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry
      Blanc.ProrataWethVault.withdraw (.ok post))
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor entry sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨_supply, _supplyEq, _stable, -, -, -, -, ownerValid, -, covered, -,
      effect⟩ :=
    withdraw_body_effect config memoryWf afterLookup burnLookup stack run
  exact outboundEffect_preserves_conserved ownerValid covered effect conserved

/-- Body-level configured obligation for `redeem`: mirror of `withdraw`. -/
theorem redeem_body_obligation
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (afterLookup : fs[Blanc.ProrataWethVault.redeemAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.redeemAfterQuote)
    (burnLookup : fs[Blanc.ProrataWethVault.redeemBurnSlot]? =
      some Blanc.ProrataWethVault.redeemBurn)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry
      Blanc.ProrataWethVault.redeem (.ok post))
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor entry sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨_supply, _supplyEq, _stable, -, -, -, -, ownerValid, -, covered, -,
      effect⟩ :=
    redeem_body_effect config memoryWf afterLookup burnLookup stack run
  exact outboundEffect_preserves_conserved ownerValid covered effect conserved

/-- Enter a flow body from a message run, carrying configuration, memory
well-formedness, and the conservation hypothesis from message entry to body
entry.  The dispatch entry moves no state, memory, or logs, so all three
transport by rewriting. -/
private theorem enter_flow_body
    {sevm : Sevm} {pre post : Devm} {sig : B256} {words : Nat} {body : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = sig)
    (member : (sig, Blanc.ProrataWethVault.routed words body) ∈
      Blanc.ProrataWethVault.vaultFuncs)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    ∃ bodyPre,
      DirectWethConfiguration sevm.currentTarget sevm bodyPre ∧
      Mem.Wf bodyPre.memory ∧
      Func.RunCompiledTo (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux) sevm bodyPre body (.ok post) ∧
      LedgerConserved Blanc.ProrataWethVault.supplySlot
        (Devm.getStor bodyPre sevm.currentTarget) := by
  obtain ⟨bodyPre, -, -, entryState, entryMemory, -, -, bodyRun⟩ :=
    Blanc.ProrataWethVault.runCompiled_enters_body_compiled_logs run
      selectorEq member
  have bodyConfig :
      DirectWethConfiguration sevm.currentTarget sevm bodyPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← getCode_eq_of_state_eq entryState wethAccount]
    exact config.code
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  have storEq : Devm.getStor pre sevm.currentTarget =
      Devm.getStor bodyPre sevm.currentTarget :=
    congrFun (funext (getStor_eq_of_state_eq entryState)) sevm.currentTarget
  rw [storEq] at conserved
  exact ⟨bodyPre, bodyConfig, bodyWf, bodyRun, conserved⟩

/-- Uniform per-target configured obligation: from a configured entry, a
successful compiled run selecting `sig` preserves the ledger.  Generic
targets ignore the configuration; the four flows need it.  The statement is per-selector; per-target indexing lives in the bundle's membership hypothesis. -/
def TargetPreservesConserved (sig : B256) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm},
    DirectWethConfiguration sevm.currentTarget sevm pre →
    Mem.Wf pre.memory →
    Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post →
    Sevm.selector sevm = sig →
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget) →
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget)

/-- **The 25-target bundle.**  Every dispatch target preserves the ledger:
the eighteen read-only targets through their source-level obligation, the
three share writers through their body proofs, and the four flows through
the body obligations above.  The case split lives here, once. -/
theorem vault_target_obligations :
    ∀ (sig : B256) (target : Func),
      (sig, target) ∈ Blanc.ProrataWethVault.vaultFuncs →
      TargetPreservesConserved sig := by
  intro sig target member
  simp only [Blanc.ProrataWethVault.vaultFuncs, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.totalAssets) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.name) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.convertToAssets) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact Blanc.ProrataWethVault.approve_preserves_conserved memoryWf run selectorEq
      conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.previewWithdraw) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.totalSupply) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact Blanc.ProrataWethVault.transferFrom_preserves_conserved memoryWf run selectorEq
      conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.decimals) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.asset) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.maxDeposit) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.previewRedeem) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post config memoryWf run selectorEq conserved
    obtain ⟨bodyPre, bodyConfig, bodyWf, bodyRun, conservedBody⟩ :=
      enter_flow_body config memoryWf run selectorEq deposit_mem_vaultFuncs
        conserved
    exact deposit_body_obligation bodyConfig bodyWf depositAfterQuote_lookup
      nil_pref bodyRun conservedBody
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.balanceOf) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post config memoryWf run selectorEq conserved
    obtain ⟨bodyPre, bodyConfig, bodyWf, bodyRun, conservedBody⟩ :=
      enter_flow_body config memoryWf run selectorEq mint_mem_vaultFuncs
        conserved
    exact mint_body_obligation bodyConfig bodyWf mintAfterQuote_lookup
      nil_pref bodyRun conservedBody
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 0)
      (body := Blanc.ProrataWethVault.symbol) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact Blanc.ProrataWethVault.transfer_preserves_conserved memoryWf run selectorEq
      conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.previewMint) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post config memoryWf run selectorEq conserved
    obtain ⟨bodyPre, bodyConfig, bodyWf, bodyRun, conservedBody⟩ :=
      enter_flow_body config memoryWf run selectorEq withdraw_mem_vaultFuncs
        conserved
    exact withdraw_body_obligation bodyConfig bodyWf withdrawAfterQuote_lookup
      withdrawBurn_lookup nil_pref bodyRun conservedBody
  · intro _sevm _pre _post config memoryWf run selectorEq conserved
    obtain ⟨bodyPre, bodyConfig, bodyWf, bodyRun, conservedBody⟩ :=
      enter_flow_body config memoryWf run selectorEq redeem_mem_vaultFuncs
        conserved
    exact redeem_body_obligation bodyConfig bodyWf redeemAfterQuote_lookup
      redeemBurn_lookup nil_pref bodyRun conservedBody
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.maxMint) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.convertToShares) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.maxWithdraw) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.maxRedeem) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 2)
      (body := Blanc.ProrataWethVault.allowance) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved
  · intro _sevm _pre _post _config memoryWf run selectorEq conserved
    exact readOnly_message (words := 1)
      (body := Blanc.ProrataWethVault.previewDeposit) run selectorEq
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs]) conserved

/-- **Soundness.**  The bundle plus dispatch exhaustiveness discharges the
one-message rung: a successful run lands in the table, and the table entry
carries exactly the obligation the rung concludes.  No case split — the
bundle is universally quantified. -/
theorem vault_soundness
    {sevm : Sevm} {pre post : Devm}
    (bundle : ∀ (sig : B256) (target : Func),
      (sig, target) ∈ Blanc.ProrataWethVault.vaultFuncs →
      TargetPreservesConserved sig)
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨body, member⟩ :=
    Blanc.ProrataWethVault.selector_mem_vaultFuncs_of_ok run
  exact bundle _ _ member config memoryWf run rfl conserved

/-- **One message preserves the ledger.**  Twenty-five branches, one per
dispatch target, plus the impossibility of an unmatched selector. -/
theorem vault_message_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot (Devm.getStor post sevm.currentTarget) := by
  exact vault_soundness vault_target_obligations config memoryWf run conserved

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

/-- A sequence of vault messages, each configured at its own entry state. -/
inductive ConfiguredMessages (vault : Adr) : Devm → Devm → Prop
  | refl (s : Devm) : ConfiguredMessages vault s s
  | step {s t u : Devm} {sevm : Sevm} :
      ConfiguredMessages vault s t →
      sevm.currentTarget = vault →
      DirectWethConfiguration vault sevm t →
      Mem.Wf t.memory →
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
  | step _ target config memoryWf run ih =>
      subst target
      exact vault_message_preserves_conserved config memoryWf run ih

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
