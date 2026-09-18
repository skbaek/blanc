-- ProrataWethVaultPairVaultSegment.lean : the vault-frame pair segment.

import Blanc.Composition.ProrataWethVaultHistory
import Blanc.StaticCallStorage

/-!
# The vault frame as a pair-history segment

`VaultFramePairSegment vault` (History) asks every committed compiled vault run
entered by a caller other than the vault to be a provenance-tagged pair replay
between its own endpoints.  This module proves it by the vault's 25-way
selector split:

* the eighteen read-only targets leave both storages equal as `Stor` trees —
  the live-quoting ones through `Ninst.staticcall_inv_getStor_exact` — and
  replay with no record;
* the three share writers (`approve`, `transfer`, `transferFrom`) emit one
  accepted `.operation` record that owns no allowance invocation: WETH's
  storage is untouched;
* `deposit` and `mint` emit one `.operation` record that owns their exact WETH
  `transferFrom` child, linked at both endpoints and staged by the vault;
* `withdraw` and `redeem` emit one `.operation` record that owns nothing: the
  exact WETH `transfer` child writes balance rows only.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Source

/-! ## The eighteen read-only targets keep both storages -/

private theorem silentIn_returnWord_getStor :
    Func.SilentIn Devm.getStor Blanc.ProrataWethVault.ReadOnlySilentSlot
      Blanc.ProrataWethVault.returnWord := by
  silent_structure

private theorem silentIn_maxMintAfterAssetCap_getStor :
    Func.SilentIn Devm.getStor Blanc.ProrataWethVault.ReadOnlySilentSlot
      Blanc.ProrataWethVault.maxMintAfterAssetCap := by
  silent_structure with readOnly_slot

private theorem readOnlySilentSlot_closed_getStor :
    ∀ k g, Blanc.ProrataWethVault.ReadOnlySilentSlot k →
      (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vaultAux)[k]? = some g →
      Func.SilentIn Devm.getStor Blanc.ProrataWethVault.ReadOnlySilentSlot g := by
  intro k g allowed lookup
  rcases allowed with h | h <;> subst k
  · obtain rfl : Blanc.ProrataWethVault.returnWord = g := Option.some.inj
      ((show (Blanc.ProrataWethVault.vault.main ::
          Blanc.ProrataWethVault.vaultAux)[
            Blanc.ProrataWethVault.returnWordSlot]? =
          some Blanc.ProrataWethVault.returnWord from rfl).symm.trans lookup)
    exact silentIn_returnWord_getStor
  · obtain rfl : Blanc.ProrataWethVault.maxMintAfterAssetCap = g :=
      Option.some.inj
        ((show (Blanc.ProrataWethVault.vault.main ::
            Blanc.ProrataWethVault.vaultAux)[
              Blanc.ProrataWethVault.maxMintAfterAssetCapSlot]? =
            some Blanc.ProrataWethVault.maxMintAfterAssetCap from rfl).symm.trans
          lookup)
    exact silentIn_maxMintAfterAssetCap_getStor

/-- Every read-only dispatch target keeps every `Stor` tree. -/
private theorem readOnly_silent_getStor :
    ∀ p ∈ Blanc.ProrataWethVault.readOnlyFuncs,
      Func.SilentIn Devm.getStor Blanc.ProrataWethVault.ReadOnlySilentSlot p.2 := by
  intro p member
  simp only [Blanc.ProrataWethVault.readOnlyFuncs, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h <;> (cases h) <;>
    silent_structure with readOnly_slot

/-- A compiled run of one read-only target keeps every `Stor` tree. -/
private theorem readOnly_message_getStor
    {sevm : Sevm} {pre post : Devm} {sig : B256} {words : Nat} {body : Func}
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = sig)
    (memberAll : (sig, Blanc.ProrataWethVault.routed words body) ∈
      Blanc.ProrataWethVault.vaultFuncs)
    (memberRO : (sig, Blanc.ProrataWethVault.routed words body) ∈
      Blanc.ProrataWethVault.readOnlyFuncs) :
    Devm.getStor post = Devm.getStor pre := by
  obtain ⟨endpointPre, entryState, -, -, -, endpointRun⟩ :=
    Blanc.ProrataWethVault.runCompiled_enters_endpoint_compiled_logs run
      selectorEq memberAll
  have walk := Func.observe_eq_of_run_silentIn
    readOnlySilentSlot_closed_getStor
    (Func.WalkInv.toRun (R := Func.RunOk) endpointRun)
    (readOnly_silent_getStor _ memberRO)
  exact walk.trans (funext (getStor_eq_of_state_eq entryState)).symm

/-- A compiled vault run whose selector is none of the seven writers keeps
every `Stor` tree. -/
private theorem view_message_getStor
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (notDeposit :
      Sevm.selector sevm ≠ selector "deposit" [.uint256, .address])
    (notMint : Sevm.selector sevm ≠ selector "mint" [.uint256, .address])
    (notWithdraw : Sevm.selector sevm ≠
      selector "withdraw" [.uint256, .address, .address])
    (notRedeem : Sevm.selector sevm ≠
      selector "redeem" [.uint256, .address, .address])
    (notApprove : Sevm.selector sevm ≠ selector "approve" [.address, .uint256])
    (notTransfer :
      Sevm.selector sevm ≠ selector "transfer" [.address, .uint256])
    (notTransferFrom : Sevm.selector sevm ≠
      selector "transferFrom" [.address, .address, .uint256]) :
    Devm.getStor post = Devm.getStor pre := by
  obtain ⟨body, member⟩ :=
    Blanc.ProrataWethVault.selector_mem_vaultFuncs_of_ok run
  simp only [Blanc.ProrataWethVault.vaultFuncs, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ |
    ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ |
    ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ |
    ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ |
    ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ | ⟨sel, rfl⟩ |
    ⟨sel, rfl⟩
  · exact readOnly_message_getStor (words := 0)
      (body := Blanc.ProrataWethVault.totalAssets) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 0)
      (body := Blanc.ProrataWethVault.name) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.convertToAssets) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact absurd sel notApprove
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.previewWithdraw) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 0)
      (body := Blanc.ProrataWethVault.totalSupply) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact absurd sel notTransferFrom
  · exact readOnly_message_getStor (words := 0)
      (body := Blanc.ProrataWethVault.decimals) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 0)
      (body := Blanc.ProrataWethVault.asset) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.maxDeposit) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.previewRedeem) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact absurd sel notDeposit
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.balanceOf) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact absurd sel notMint
  · exact readOnly_message_getStor (words := 0)
      (body := Blanc.ProrataWethVault.symbol) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact absurd sel notTransfer
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.previewMint) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact absurd sel notWithdraw
  · exact absurd sel notRedeem
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.maxMint) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.convertToShares) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.maxWithdraw) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.maxRedeem) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 2)
      (body := Blanc.ProrataWethVault.allowance) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])
  · exact readOnly_message_getStor (words := 1)
      (body := Blanc.ProrataWethVault.previewDeposit) run sel
      (by simp [Blanc.ProrataWethVault.vaultFuncs])
      (by simp [Blanc.ProrataWethVault.readOnlyFuncs])

/-! ## One accepted vault operation as one record -/

/-- The single record a vault operation emits: its real endpoint states, the
accepted operation with its share evidence, and the allowance invocation it
owns, if any. -/
private def vaultRecord {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (op : FourQuote.FourQuoteOperation vault sevm pre post)
    (evidence : FourQuote.FourQuoteShareEvidence op)
    (own : Option WethAllowanceInvocation)
    (linked : ∀ call, own = some call →
      call.pre.state.getStor wethAccount = pre.state.getStor wethAccount ∧
      call.post.state.getStor wethAccount = post.state.getStor wethAccount ∧
      (call.sevm.caller = vault → VaultStagedCalldata call))
    (quiet : own = none → ∀ key, ¬ ValidAdr key →
      (post.state.getStor wethAccount).get key =
        (pre.state.getStor wethAccount).get key)
    (provenance : Blanc.Prorata.ProrataAccountingProvenance)
    (actor : provenance.actor = some sevm.caller) : PairStepRecord vault where
  before := pre.state
  after := post.state
  step := .operation ⟨sevm, pre, post, rfl, rfl, op⟩ evidence
  own := own
  linked := linked
  quiet := quiet
  debitOwn := by
    intro _ _ _ _ _ _ impossible
    cases impossible
  provenance := provenance
  actor := actor

/-- One record replays between the run's own endpoints with its provenance. -/
private theorem vaultRecord_segment {vault : Adr} {sevm : Sevm} {pre post : Devm}
    {op : FourQuote.FourQuoteOperation vault sevm pre post}
    {evidence : FourQuote.FourQuoteShareEvidence op}
    {own : Option WethAllowanceInvocation}
    {linked : ∀ call, own = some call →
      call.pre.state.getStor wethAccount = pre.state.getStor wethAccount ∧
      call.post.state.getStor wethAccount = post.state.getStor wethAccount ∧
      (call.sevm.caller = vault → VaultStagedCalldata call)}
    {quiet : own = none → ∀ key, ¬ ValidAdr key →
      (post.state.getStor wethAccount).get key =
        (pre.state.getStor wethAccount).get key}
    {provenance : Blanc.Prorata.ProrataAccountingProvenance}
    {actor : provenance.actor = some sevm.caller} :
    ∃ steps : List (PairStepRecord vault),
      PairReplay vault (PairBoundary.ofState vault pre.state) steps
        (PairBoundary.ofState vault post.state) ∧
      ∀ r ∈ steps, r.provenance = provenance := by
  have replay := PairReplay.singleton
    (vaultRecord op evidence own linked quiet provenance actor)
  refine ⟨_, replay, ?_⟩
  intro r member
  simp only [List.mem_singleton] at member
  subst member
  rfl

/-- A record that owns no invocation has nothing to link. -/
private theorem linked_none {vault : Adr} {pre post : Devm} :
    ∀ call, (none : Option WethAllowanceInvocation) = some call →
      call.pre.state.getStor wethAccount = pre.state.getStor wethAccount ∧
      call.post.state.getStor wethAccount = post.state.getStor wethAccount ∧
      (call.sevm.caller = vault → VaultStagedCalldata call) := by
  intro _ impossible
  cases impossible

/-- A record that owns an invocation owes no silence. -/
private theorem quiet_some {pre post : Devm} {call : WethAllowanceInvocation} :
    (some call : Option WethAllowanceInvocation) = none → ∀ key, ¬ ValidAdr key →
      (post.state.getStor wethAccount).get key =
        (pre.state.getStor wethAccount).get key := by
  intro impossible
  cases impossible

/-- Equal WETH storage is silent at every key. -/
private theorem quiet_of_eq {pre post : Devm}
    (kept : Devm.getStor post wethAccount = Devm.getStor pre wethAccount) :
    (none : Option WethAllowanceInvocation) = none → ∀ key, ¬ ValidAdr key →
      (post.state.getStor wethAccount).get key =
        (pre.state.getStor wethAccount).get key := by
  intro _ key _
  change (Devm.getStor post wethAccount).get key =
    (Devm.getStor pre wethAccount).get key
  rw [kept]

/-- WETH storage that agrees off address keys is silent at every non-address
key. -/
private theorem quiet_of_agree {pre post : Devm}
    (agree : Stor.AgreeOffAdr (Devm.getStor pre wethAccount)
      (Devm.getStor post wethAccount)) :
    (none : Option WethAllowanceInvocation) = none → ∀ key, ¬ ValidAdr key →
      (post.state.getStor wethAccount).get key =
        (pre.state.getStor wethAccount).get key := by
  intro _ key notAdr
  exact (agree key notAdr).symm

/-- The linked `transferFrom` child of an inbound flow is one owned allowance
invocation, linked at both endpoints and staged by the vault. -/
private theorem inbound_owned {vault : Adr} {sevm : Sevm} {pre post : Devm}
    {assets : B256}
    (child : LinkedWethChild sevm.currentTarget
      (transferFromCalldata sevm.caller sevm.currentTarget assets) pre post) :
    ∃ call : WethAllowanceInvocation,
      ∀ c, some call = some c →
        c.pre.state.getStor wethAccount = pre.state.getStor wethAccount ∧
        c.post.state.getStor wethAccount = post.state.getStor wethAccount ∧
        (c.sevm.caller = vault → VaultStagedCalldata c) := by
  obtain ⟨childSevm, childPre, rawPost, target, -, dataEq, memoryEmpty, run,
    entryLinked, exitLinked⟩ := child
  have selected := (transferFromCalldata_facts dataEq).1
  obtain ⟨call, -, sevmEq, preEq, postEq⟩ :=
    weth_run_mkTransferFromInvocation target memoryEmpty run selected
  refine ⟨call, fun c same => ?_⟩
  cases same
  refine ⟨?_, ?_, fun _ => ?_⟩
  · rw [preEq]
    exact entryLinked
  · rw [postEq]
    exact exitLinked
  · refine Or.inr (Or.inl ⟨sevm.caller, sevm.currentTarget, assets, ?_⟩)
    rw [sevmEq]
    exact dataEq

/-! ## The segment -/

/-- WETH's booked rows cannot overflow at a frame that is not WETH's own. -/
private theorem wethRowSumNof_of_pre {sevm : Sevm} {pre : Devm}
    (weth : wethSpec.Pre wethAccount sevm pre)
    (notWeth : sevm.currentTarget ≠ wethAccount) :
    SumNof (Stor.rest (Devm.getStor pre wethAccount)) := by
  have precond := wethSpec_pre_iff.mp weth
  have solvent : balSum (Devm.getStor pre wethAccount) + (0 : B256).toNat ≤
      (pre.getBal wethAccount).toNat := precond.solvent.2 notWeth
  have bound : (pre.getBal wethAccount).toNat < 2 ^ 256 :=
    B256.toNat_lt (pre.getBal wethAccount)
  show sum (Stor.rest (Devm.getStor pre wethAccount)) < 2 ^ 256
  have expand : balSum (Devm.getStor pre wethAccount) =
      sum (Stor.rest (Devm.getStor pre wethAccount)) := rfl
  omega

/-- **The vault-frame pair segment.**  Every committed compiled vault run
entered by a caller other than the vault is a provenance-tagged pair replay
between its own endpoints: no record for a view, one accepted operation record
for each writer. -/
theorem vaultFramePairSegment (vault : Adr) : VaultFramePairSegment vault := by
  intro sevm pre post run target direct callerNe inv provenance actor
  have config : DirectWethConfiguration sevm.currentTarget sevm pre := by
    rw [target]
    exact inv.vault.config
  have memoryWf : Mem.Wf pre.memory := inv.vault.preWf.wf target
  have callerNotVault : sevm.caller ≠ sevm.currentTarget := by
    rw [target]
    exact callerNe
  have wethSumNof : SumNof (Stor.rest (Devm.getStor pre wethAccount)) :=
    wethRowSumNof_of_pre inv.weth (fun h => config.distinct h.symm)
  by_cases isDeposit :
      Sevm.selector sevm = selector "deposit" [.uint256, .address]
  · obtain ⟨-, _, -, -, -, -, -, -, -, effect, child⟩ :=
      deposit_compiled_effect_linked config memoryWf run isDeposit
    have wethRowNof : B256.Nof
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget)
        (Sevm.argWord sevm 0) := by
      obtain ⟨-, movement, -⟩ := effect
      unfold B256.Nof
      have pairLe := add_le_sum_of_ne
        (Stor.rest (Devm.getStor pre wethAccount)) callerNotVault
      have movedLe := B256.toNat_le_toNat movement.1
      have sumLt : sum (Stor.rest (Devm.getStor pre wethAccount)) < 2 ^ 256 :=
        wethSumNof
      omega
    obtain ⟨_, _, _, _, evidence⟩ :=
      FourQuote.deposit_compiled_share_evidence target callerNotVault wethRowNof
        config memoryWf run isDeposit
    obtain ⟨call, linked⟩ := inbound_owned (vault := vault) child
    exact vaultRecord_segment (evidence := evidence) (own := some call)
      (linked := linked) (quiet := quiet_some) (actor := actor)
  by_cases isMint : Sevm.selector sevm = selector "mint" [.uint256, .address]
  · obtain ⟨-, supply, supplyEq, -, quoteFits, -, -, -, -, effect, child⟩ :=
      mint_compiled_effect_linked config memoryWf run isMint
    have wethRowNof : ∀ charged : B256,
        charged.toNat = Blanc.ProrataWethVault.previewMintN
          (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply →
        B256.Nof (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget)
          charged := by
      intro charged chargedEq
      obtain ⟨-, movement, -⟩ := effect
      have movedLe := B256.toNat_le_toNat movement.1
      rw [B256.toNat_toB256_of_lt quoteFits] at movedLe
      have snapshotEq : Blanc.ProrataWethVault.previewMintN
          (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply =
        Blanc.ProrataWethVault.previewMintN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat
          supply.toNat := by
        simp [snapshotAt, vaultSnapshot, supplyEq]
        rfl
      unfold B256.Nof
      have pairLe := add_le_sum_of_ne
        (Stor.rest (Devm.getStor pre wethAccount)) callerNotVault
      have sumLt : sum (Stor.rest (Devm.getStor pre wethAccount)) < 2 ^ 256 :=
        wethSumNof
      have rowEq : ((pre.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat =
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat := rfl
      omega
    obtain ⟨_, _, _, _, _, evidence⟩ :=
      FourQuote.mint_compiled_share_evidence target callerNotVault wethRowNof
        config memoryWf run isMint
    obtain ⟨call, linked⟩ := inbound_owned (vault := vault) child
    exact vaultRecord_segment (evidence := evidence) (own := some call)
      (linked := linked) (quiet := quiet_some) (actor := actor)
  by_cases isWithdraw : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, quiet⟩ :=
      withdraw_compiled_effect_quiet config memoryWf run isWithdraw
    by_cases self : (Sevm.argWord sevm 1).toAdr = sevm.currentTarget
    · obtain ⟨_, _, _, _, evidence⟩ :=
        FourQuote.withdrawSelf_compiled_share_evidence target self config
          memoryWf run isWithdraw
      exact vaultRecord_segment (evidence := evidence) (own := none)
        (linked := linked_none) (quiet := quiet_of_agree quiet) (actor := actor)
    · obtain ⟨_, _, _, _, evidence⟩ :=
        FourQuote.withdrawNormal_compiled_share_evidence target
          (fun h => self h.symm) config memoryWf run isWithdraw
      exact vaultRecord_segment (evidence := evidence) (own := none)
        (linked := linked_none) (quiet := quiet_of_agree quiet) (actor := actor)
  by_cases isRedeem : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, quiet⟩ :=
      redeem_compiled_effect_quiet config memoryWf run isRedeem
    by_cases self : (Sevm.argWord sevm 1).toAdr = sevm.currentTarget
    · obtain ⟨_, _, _, _, evidence⟩ :=
        FourQuote.redeemSelf_compiled_share_evidence target self config
          memoryWf run isRedeem
      exact vaultRecord_segment (evidence := evidence) (own := none)
        (linked := linked_none) (quiet := quiet_of_agree quiet) (actor := actor)
    · obtain ⟨_, _, _, _, evidence⟩ :=
        FourQuote.redeemNormal_compiled_share_evidence target
          (fun h => self h.symm) config memoryWf run isRedeem
      exact vaultRecord_segment (evidence := evidence) (own := none)
        (linked := linked_none) (quiet := quiet_of_agree quiet) (actor := actor)
  have notWeth : sevm.currentTarget ≠ wethAccount := fun h => config.distinct h.symm
  by_cases isApprove :
      Sevm.selector sevm = selector "approve" [.address, .uint256]
  · obtain ⟨-, -, -, -, -, -, -, -, foreign, -⟩ :=
      Blanc.ProrataWethVault.approve_compiled_effect memoryWf run isApprove
    exact vaultRecord_segment
      (evidence := FourQuote.approve_compiled_share_evidence target config
        memoryWf run isApprove)
      (own := none) (linked := linked_none)
      (quiet := quiet_of_eq (foreign wethAccount notWeth)) (actor := actor)
  by_cases isTransfer :
      Sevm.selector sevm = selector "transfer" [.address, .uint256]
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, foreign, -⟩ :=
      Blanc.ProrataWethVault.transfer_compiled_effect memoryWf run isTransfer
    exact vaultRecord_segment
      (evidence := FourQuote.transfer_compiled_share_evidence target config
        memoryWf run isTransfer)
      (own := none) (linked := linked_none)
      (quiet := quiet_of_eq (foreign wethAccount notWeth)) (actor := actor)
  by_cases isTransferFrom : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        foreign, -⟩ :=
      Blanc.ProrataWethVault.transferFrom_compiled_effect memoryWf run
        isTransferFrom
    exact vaultRecord_segment
      (evidence := FourQuote.transferFrom_compiled_share_evidence target config
        memoryWf run isTransferFrom)
      (own := none) (linked := linked_none)
      (quiet := quiet_of_eq (foreign wethAccount notWeth)) (actor := actor)
  have kept := view_message_getStor run isDeposit isMint isWithdraw isRedeem
    isApprove isTransfer isTransferFrom
  exact ⟨[], PairReplay.nil_of_eq
    (PairBoundary.ofState_eq (congrFun kept vault) (congrFun kept wethAccount)),
    by simp⟩

end Blanc.Composition.ProrataWethVault
