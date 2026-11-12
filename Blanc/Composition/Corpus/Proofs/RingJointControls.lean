import Blanc.BlockForward
import Blanc.Lift.SystemExecution.BeaconRoots.SystemWalk
import Blanc.Lift.SystemExecution.HistoryStorage.SystemWalk
import Blanc.Lift.WithdrawalRequest.SystemProtocol
import Blanc.Lift.WithdrawalRequest.SystemFrameEffects
import Blanc.Lift.ConsolidationRequest.System
import Blanc.Lift.RequestSystem.Effects
import Blanc.ConcreteRunKept
import Blanc.KeptCreateAvoid
import Blanc.ExecutionTraceSystemCode
import Blanc.SyntheticBpo2Envelope
import Blanc.BalanceAlgebra
import Blanc.Composition.Corpus.Proofs.RingTotality
import Blanc.Corpus.Freeze.BeaconRoots
import Blanc.Corpus.Freeze.HistoryStorage

/-! Negative controls for the Wave 2 EIP-4788 / EIP-2935 S8/S9 corpus entries:
- `r_s8_time_control`: exact 8191-second wraparound collision overwrites the
  prior beacon root on a valid 2-block Prague chain with empty `systemAddress`.
- `r_s9_control`: mutating `parentBeaconBlockRoot` in `NewPayloadRequest` changes
  what `beaconRootsCall` stores and returns.
- `h_s9_control`: mutating `blockHashes` in `historyStorageCall` changes what is
  stored and read for the parent block number.
- `h_s9_joint_control`: mutating `blockHashes` in `historyStorageCall` for a
  converted `NewPayloadRequest` breaks equality with the beacon state's
  `latest_execution_payload_header.block_hash`. -/

namespace Blanc.Composition.Corpus.Proofs.RingJointControls

open Jaune Blanc Blanc.Lift
open Blanc.Corpus.Freeze

private theorem nat_toB256_sub_one (n : Nat) (h0 : 0 < n) (hn : n < 2 ^ 256) :
    (n.toB256 - 1 : B256) = (n - 1).toB256 := by
  apply B256.toNat_inj
  have h1le : (1 : B256) ≤ n.toB256 := by
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_one, B256.toNat_toB256_of_lt hn]
    exact h0
  rw [B256.toNat_sub_eq_of_le n.toB256 1 h1le, B256.toNat_toB256_of_lt hn,
    B256.toNat_one, B256.toNat_toB256_of_lt (by omega)]

private theorem b256_mod_ring_toNat (x : B256) :
    (x % ring).toNat = x.toNat % 8191 := by
  have hring : ring = 0x1fff := rfl
  have hnz : (0x1fff : B256) ≠ 0 := by decide
  rw [hring, B256.toNat_mod hnz]
  rfl

private theorem rootKey_ne_timeKey (t : B256) :
    BeaconRoots.rootKey t ≠ BeaconRoots.timeKey t := by
  unfold BeaconRoots.rootKey BeaconRoots.timeKey
  intro h
  have h1 := congrArg B256.toNat h
  have ht : (t % ring).toNat < 8191 := by
    rw [b256_mod_ring_toNat]
    exact Nat.mod_lt t.toNat (by omega)
  have hring : ring.toNat = 8191 := rfl
  rw [B256.toNat_add, hring] at h1
  rw [Nat.lo_eq_of_lt (by omega)] at h1
  omega

/-- Local negative control for **R-S9**: mutating `parentBeaconBlockRoot` in the
payload request causes `beaconRootsCall` to record and return `mutatedRoot` rather
than `block.parent_root`. -/
theorem r_s9_control : BeaconRoots.R_S9_control := by
  intro P f block req mutatedRoot fork parent _hreq hne hfork hinst
  dsimp only
  let mutatedReq : JauneConsensus.NewPayloadRequest P :=
    { req with parentBeaconBlockRoot := mutatedRoot }
  let hdr := (JauneConsensus.payloadToBlock mutatedReq).header
  let benv := initBenv fork parent hdr
  obtain ⟨_, _, _, _, bal, hcall⟩ := Blanc.Corpus.Proofs.R.r_s1 benv hfork hinst
  have htime : benv.stat.time = hdr.timestamp.toB256 := rfl
  have hroot : benv.stat.parentBeaconBlockRoot = mutatedRoot := rfl
  rw [htime, hroot] at hcall
  refine ⟨_, bal, hcall, ?_, ?_, ?_⟩
  · unfold storOf BeaconRoots.writeState
    rw [State.getStor_setStorVal_self, Stor.get_set_self]
  · unfold storOf BeaconRoots.writeState
    rw [State.getStor_setStorVal_self, Stor.get_set_self]
    exact hne
  · intro hnz
    have htimeWord : storOf (BeaconRoots.writeState parent.state hdr.timestamp.toB256 mutatedRoot)
        BeaconRoots.addr (BeaconRoots.timeKey hdr.timestamp.toB256) = hdr.timestamp.toB256 := by
      unfold storOf BeaconRoots.writeState
      rw [State.getStor_setStorVal_self, State.getStor_setStorVal_self,
        Stor.get_set_ne _ (rootKey_ne_timeKey _), Stor.get_set_self]
    have hrootWord : storOf (BeaconRoots.writeState parent.state hdr.timestamp.toB256 mutatedRoot)
        BeaconRoots.addr (BeaconRoots.rootKey hdr.timestamp.toB256) = mutatedRoot := by
      unfold storOf BeaconRoots.writeState
      rw [State.getStor_setStorVal_self, Stor.get_set_self]
    have hst : benv.state = parent.state := rfl
    have hread : BeaconRoots.read
        (storOf (BeaconRoots.writeState benv.state hdr.timestamp.toB256 mutatedRoot) BeaconRoots.addr)
        hdr.timestamp.toB256 = some mutatedRoot := by
      unfold BeaconRoots.read
      rw [hst, ite_eq_left ⟨hnz, htimeWord⟩, hrootWord]
    refine ⟨hread, ?_⟩
    rw [hread]
    intro heq
    exact hne (Option.some.inj heq)

/-- Local negative control for **H-S9** (chain form): mutating `blockHashes`
passed to `historyStorageCall` writes `mutatedHash ≠ t.header.hash` and returns
`some mutatedHash` for `t.header.number`. -/
theorem h_s9_control : HistoryStorage.H_S9_control := by
  intro parent t fork header bal mutatedHash _htip hnum hfit hfork hinst hne
  dsimp only
  let benv := initBenv fork parent header
  let mutatedBenv : Benv := { benv with stat := { benv.stat with blockHashes := [mutatedHash] } }
  have hlast : mutatedBenv.stat.blockHashes.getLast? = some mutatedHash := rfl
  obtain ⟨_, _, _, _, bal', hcall⟩ := Blanc.Corpus.Proofs.H.h_s1 mutatedBenv bal hfork hinst hlast
  have hnum_eq : mutatedBenv.stat.number = header.number := rfl
  have hst_eq : mutatedBenv.state = parent.state := rfl
  rw [hnum_eq, hst_eq] at hcall
  have hstored : storOf (parent.state.setStorVal HistoryStorage.addr
      (HistoryStorage.key header.number.toB256) mutatedHash)
      HistoryStorage.addr (HistoryStorage.key header.number.toB256) = mutatedHash := by
    simp only [storOf, State.getStor_setStorVal_self, Stor.get_set_self]
  have hpos : 0 < header.number := by omega
  have hlt : header.number < 2 ^ 256 := by omega
  have ht_lt : t.header.number < 2 ^ 256 := by omega
  have hsub : header.number.toB256 - 1 = t.header.number.toB256 := by
    rw [nat_toB256_sub_one header.number hpos hlt, hnum, Nat.add_sub_cancel]
  have hwin : HistoryStorage.InWindow header.number.toB256 t.header.number.toB256 := by
    unfold HistoryStorage.InWindow
    rw [hsub]
    have hle : t.header.number.toB256 ≤ header.number.toB256 := by
      rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt ht_lt, B256.toNat_toB256_of_lt hlt]
      omega
    refine ⟨Nat.le_refl _, ?_⟩
    rw [B256.toNat_sub_eq_of_le _ _ hle, B256.toNat_toB256_of_lt hlt, B256.toNat_toB256_of_lt ht_lt]
    omega
  have hkey : HistoryStorage.key header.number.toB256 = t.header.number.toB256 % ring := by
    unfold HistoryStorage.key
    rw [hsub]
  have hread : HistoryStorage.read
      (storOf (parent.state.setStorVal HistoryStorage.addr (HistoryStorage.key header.number.toB256) mutatedHash)
        HistoryStorage.addr) header.number.toB256 t.header.number.toB256 = some mutatedHash := by
    unfold HistoryStorage.read
    rw [ite_eq_left hwin, ← hkey, hstored]
  refine ⟨_, bal', hcall, hstored, ?_, hread, ?_⟩
  · rw [hstored]; exact hne
  · rw [hread]; intro heq; exact hne (Option.some.inj heq)

/-- Local negative control for **H-S9** (joint form): mutating `blockHashes`
breaks equality with `beacon.latest_execution_payload_header.block_hash`. -/
theorem h_s9_joint_control : HistoryStorage.H_S9_joint_control := by
  intro P f beacon req fork parent bal mutatedHash hfork hinst hne
  dsimp only
  let hdr := (JauneConsensus.payloadToBlock req).header
  let benv := initBenv fork parent hdr
  let mutatedBenv : Benv := { benv with stat := { benv.stat with blockHashes := [mutatedHash] } }
  have hlast : mutatedBenv.stat.blockHashes.getLast? = some mutatedHash := rfl
  obtain ⟨_, _, _, _, bal', hcall⟩ := Blanc.Corpus.Proofs.H.h_s1 mutatedBenv bal hfork hinst hlast
  have hnum_eq : mutatedBenv.stat.number = req.executionPayload.block_number.toNat := rfl
  have hst_eq : mutatedBenv.state = parent.state := rfl
  rw [hnum_eq, hst_eq] at hcall
  have hstored : storOf (parent.state.setStorVal HistoryStorage.addr
      (HistoryStorage.key req.executionPayload.block_number.toNat.toB256) mutatedHash)
      HistoryStorage.addr (HistoryStorage.key req.executionPayload.block_number.toNat.toB256) = mutatedHash := by
    simp only [storOf, State.getStor_setStorVal_self, Stor.get_set_self]
  refine ⟨_, bal', hcall, hstored, ?_⟩
  rw [hstored]
  exact hne

/-! ## `r_s8_time_control`: 2-block empty-tx Prague chain with 8191s timestamp collision -/

private theorem MessageRoots.system_noCreateAt_of_spawnFree
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots (ExecutionTrace.systemTransactionMessage benv target data) state out rs)
    (hreach : SpawnFreeReach (benv.state.getCode target))
    (hne : (benv.state.getCode target).toList ≠ [])
    (hnd : ¬ isValidDelegation (benv.state.getCode target))
    (haddr : target ≠ systemAddress) :
    NoCreateAt systemAddress rs := by
  intro f member
  obtain ⟨r, hr, hf⟩ := List.mem_flatMap.mp member
  unfold Root.frames at hf
  split at hf
  · have hpc : r.evm.pc = 0 := (h.entry_machine hr).1
    have htarget : (ExecutionTrace.systemTransactionMessage benv target data).target.isNone = false := by
      simp only [ExecutionTrace.systemTransactionMessage, processSystemTransactionMsg, Option.isNone_some]
    have hca : (ExecutionTrace.systemTransactionMessage benv target data).codeAddress = some target := rfl
    have hcd : (ExecutionTrace.systemTransactionMessage benv target data).code = benv.state.getCode target := rfl
    have hcode : r.evm.sta.code = benv.state.getCode target := (h.entry_call_code hr htarget hca hcd).1 hne hnd
    have hraw := Blanc.Exec.rawFrameRoots_of_reach r.run
      (by rw [hpc]; exact noPushBefore_zero _ _) (by rw [hcode]; exact hreach)
      (Blanc.Exec.Frame.rootDeriv f) (Exec.mem_rawFrameRoots_of_mem_committedFrames r.run f hf)
    have hct : f.sevm.currentTarget = r.evm.sta.currentTarget := congrArg (fun s => s.currentTarget) hraw
    have hrct : r.evm.sta.currentTarget = target := (h.entry_routing hr).2.1
    intro _
    rw [hct, hrct]
    exact haddr
  · cases hf

private def contracts : State :=
  (((State.setPresent .empty beaconRootsAddress { Acct.nil with nonce := 1, code := beaconRootsCode }).setPresent
    historyStorageAddress { Acct.nil with nonce := 1, code := historyStorageCode }).setPresent
    withdrawalRequestPredeployAddress { Acct.nil with nonce := 1, code := withdrawalRequestCode }).setPresent
    consolidationRequestPredeployAddress { Acct.nil with nonce := 1, code := consolidationRequestCode }

private theorem contracts_installed : SystemCodeInstalled contracts := by
  intro p hp
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · change contracts.getCode beaconRootsAddress = beaconRootsCode
    unfold contracts State.getCode
    rw [State.get_setPresent_ne _ (by decide), State.get_setPresent_ne _ (by decide),
      State.get_setPresent_ne _ (by decide), State.get_setPresent_self]
  · change contracts.getCode historyStorageAddress = historyStorageCode
    unfold contracts State.getCode
    rw [State.get_setPresent_ne _ (by decide), State.get_setPresent_ne _ (by decide),
      State.get_setPresent_self]
  · change contracts.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode
    unfold contracts State.getCode
    rw [State.get_setPresent_ne _ (by decide), State.get_setPresent_self]
  · change contracts.getCode consolidationRequestPredeployAddress = consolidationRequestCode
    unfold contracts State.getCode
    rw [State.get_setPresent_self]

private theorem contracts_systemEmpty : contracts.getCode systemAddress = ByteArray.empty := by
  unfold contracts State.getCode
  rw [State.get_setPresent_ne _ (by decide : consolidationRequestPredeployAddress ≠ systemAddress),
    State.get_setPresent_ne _ (by decide : withdrawalRequestPredeployAddress ≠ systemAddress),
    State.get_setPresent_ne _ (by decide : historyStorageAddress ≠ systemAddress),
    State.get_setPresent_ne _ (by decide : beaconRootsAddress ≠ systemAddress)]
  rfl

private theorem contracts_sum : sum contracts.bal = 0 := by
  have hbal : contracts.bal = fun _ => (0 : B256) := by
    funext a
    unfold contracts State.bal
    by_cases h1 : consolidationRequestPredeployAddress = a
    · subst h1; rw [State.get_setPresent_self]; rfl
    · rw [State.get_setPresent_ne _ h1]
      by_cases h2 : withdrawalRequestPredeployAddress = a
      · subst h2; rw [State.get_setPresent_self]; rfl
      · rw [State.get_setPresent_ne _ h2]
        by_cases h3 : historyStorageAddress = a
        · subst h3; rw [State.get_setPresent_self]; rfl
        · rw [State.get_setPresent_ne _ h3]
          by_cases h4 : beaconRootsAddress = a
          · subst h4; rw [State.get_setPresent_self]; rfl
          · rw [State.get_setPresent_ne _ h4]; rfl
  unfold sum
  rw [hbal]
  exact sumBelow_zero _

private def parentHeader : Header :=
  { SyntheticBpo2Envelope.checkpointHeader contracts with
    number := 0
    timestamp := 0
    gasLimit := 2 ^ 21
    gasUsed := 0
    baseFeePerGas := some 1 }

private def parentBlock : Block :=
  { header := parentHeader, txs := [], wds := [], ommers := [] }

private def controlStart : BlockChain := ⟨[parentBlock], contracts, 1⟩

private def templateOf (parent : Block) (ts : Nat) : Header :=
  { parentHeader with
    number := parent.header.number + 1
    timestamp := ts
    gasLimit := 2 ^ 21
    baseFeePerGas := some 1
    excessBlobGas := some (calculateExcessBlobGas Fork.prague.ruleSet.blob parent.header)
    parentBeaconBlockRoot := some 0 }

private def commitHeaderTs (parent : Block) (ts : Nat) (st : State) (bout : BlockOutput) : Header :=
  { BlockForward.commitHeader Fork.prague.ruleSet parent (templateOf parent ts) st bout with
    timestamp := ts }

private theorem requestRoots_prague_noCreateAt {idx : Nat} {benv : Benv} {acc acc' : List Bytes}
    {bal bal' : BalBuilder} {final : State} {steps : List RequestStep}
    (fold : RequestRoots idx pragueRequests benv acc bal final acc' bal' steps)
    (hW : benv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode)
    (hC : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode) :
    NoCreateAt systemAddress (requestRootsOf steps) := by
  cases fold with
  | @cons tW aW restW benvW accW accW' balW balW' postW finalW outW rsW stepsW _ wRoots later =>
    cases later with
    | cons _ cRoots later2 =>
      cases later2
      have factsW := systemContracts_facts (withdrawalRequestPredeployAddress, withdrawalRequestCode)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have factsC := systemContracts_facts (consolidationRequestPredeployAddress, consolidationRequestCode)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      have hcodeC_eq : postW.getCode consolidationRequestPredeployAddress =
          consolidationRequestCode := by
        have hC' : (benv.state.getCode consolidationRequestPredeployAddress).toList ≠ [] := by
          rw [hC]; exact factsC.2.2
        have hndC : ¬ isValidDelegation (benv.state.getCode consolidationRequestPredeployAddress) := by
          rw [hC]; exact factsC.2.1
        have hc := (wRoots.chain (a := consolidationRequestPredeployAddress) hC' hndC).2
        change postW.getCode consolidationRequestPredeployAddress =
          benv.state.getCode consolidationRequestPredeployAddress at hc
        rw [hc]; exact hC
      have havoidW : NoCreateAt systemAddress rsW := by
        refine MessageRoots.system_noCreateAt_of_spawnFree wRoots ?_ ?_ ?_
          (by change withdrawalRequestPredeployAddress ≠ systemAddress; decide)
        · change SpawnFreeReach (benv.state.getCode withdrawalRequestPredeployAddress)
          rw [hW]; exact factsW.1
        · change (benv.state.getCode withdrawalRequestPredeployAddress).toList ≠ []
          rw [hW]; exact factsW.2.2
        · change ¬ isValidDelegation (benv.state.getCode withdrawalRequestPredeployAddress)
          rw [hW]; exact factsW.2.1
      intro f member
      simp only [requestRootsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        keptAll, List.flatMap_append, List.mem_append] at member
      rcases member with member | member
      · exact havoidW f member
      · refine MessageRoots.system_noCreateAt_of_spawnFree cRoots ?_ ?_ ?_
          (by change consolidationRequestPredeployAddress ≠ systemAddress; decide) f member
        · change SpawnFreeReach (postW.getCode consolidationRequestPredeployAddress)
          rw [hcodeC_eq]; exact factsC.1
        · change (postW.getCode consolidationRequestPredeployAddress).toList ≠ []
          rw [hcodeC_eq]; exact factsC.2.2
        · change ¬ isValidDelegation (postW.getCode consolidationRequestPredeployAddress)
          rw [hcodeC_eq]; exact factsC.2.1

private theorem empty_step (chain : BlockChain) (parent : Block) (ts : Nat)
    (htip : chain.blocks.getLast? = some parent)
    (hcid : chain.chainId = 1)
    (hgl : parent.header.gasLimit = 2 ^ 21)
    (hgu : parent.header.gasUsed = 0)
    (hbf : parent.header.baseFeePerGas = some 1)
    (hts : parent.header.timestamp < ts)
    (hbound : sum chain.state.bal < 2 ^ 256)
    (hinst : SystemCodeInstalled chain.state) :
    ∃ block st bout run next,
      next = ⟨appendBlock chain.blocks block, st, 1⟩ ∧
      KeptStep (ChainConfig.single 1 .prague) ⟨chain, block, .prague, bout, run⟩ next ∧
      SystemCodeInstalled st ∧
      NoSenderAt systemAddress run.senders ∧
      NoAuthorityAt systemAddress run.senders ∧
      NoCreateAt systemAddress run.roots ∧
      st.getStor beaconRootsAddress =
        (BeaconRoots.writeState chain.state ts.toB256 0).getStor beaconRootsAddress ∧
      block.header.timestamp = ts ∧
      block.header.gasLimit = 2 ^ 21 ∧
      block.header.gasUsed = 0 ∧
      block.header.baseFeePerGas = some 1 ∧
      sum st.bal < 2 ^ 256 ∧
      next.blocks.getLast? = some block := by
  let benv := initBenv .prague chain (templateOf parent ts)
  have hcodeR : benv.state.getCode beaconRootsAddress = beaconRootsCode :=
    hinst _ List.mem_cons_self
  have rFull := Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := benv) CoveredFork.prague hcodeR
  let stateR := (Blanc.Lift.SystemExecution.BeaconRoots.systemPost benv).state
  have rRun : processUncheckedSystemTransaction benv beaconRootsAddress benv.stat.parentBeaconBlockRoot.toBytes =
      .ok (stateR, systemCallOutput (Blanc.Lift.SystemExecution.BeaconRoots.systemPost benv)) := rFull.1
  have rState : stateR = _ := rFull.2.1
  have hwriteR : stateR = BeaconRoots.writeState chain.state ts.toB256 0 := by
    rw [rState]
    have hval : Blanc.Lift.SystemExecution.BeaconRoots.systemValue benv = 0 := by
      apply dataWord_of_append (pre := []) (post := []) rfl
      simp only [Blanc.Lift.SystemExecution.BeaconRoots.systemSevm,
        Blanc.Lift.SystemExecution.BeaconRoots.systemMsg, systemCallMsg,
        List.nil_append, List.append_nil]
      rfl
    rw [hval]
    rfl
  have rCodeAll (a : Adr) : stateR.getCode a = chain.state.getCode a := by
    rw [rState, State.getCode_setStorVal, State.getCode_setStorVal]
    rfl
  generalize hsR : stateR = sR at rRun rCodeAll hwriteR
  let historyEnv := benv.withState sR
  have hcodeH : historyEnv.state.getCode historyStorageAddress = historyStorageCode :=
    (rCodeAll _).trans (hinst _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨lastHash, hlast⟩ := BlockForward.blockHashes_getLast_of_ne (chain := chain)
    (by intro hnil; rw [hnil] at htip; cases htip)
  have hlastH : historyEnv.stat.blockHashes.getLast? = some lastHash := hlast
  have hFull := Blanc.Lift.SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnv) CoveredFork.prague hcodeH hlastH
  let stateH := (Blanc.Lift.SystemExecution.HistoryStorage.systemPost historyEnv).state
  have hRun : processUncheckedSystemTransaction historyEnv historyStorageAddress lastHash.toBytes =
      .ok (stateH, systemCallOutput (Blanc.Lift.SystemExecution.HistoryStorage.systemPost historyEnv)) := hFull.1
  have hState : stateH = _ := hFull.2.1
  have hStorR_H : stateH.getStor beaconRootsAddress = sR.getStor beaconRootsAddress :=
    congrArg Acct.stor (hFull.2.2 beaconRootsAddress (by decide))
  have hCodeAll (a : Adr) : stateH.getCode a = chain.state.getCode a := by
    rw [hState, State.getCode_setStorVal]
    exact rCodeAll a
  generalize hsH : stateH = sH at hRun hStorR_H hCodeAll
  let txEnv := benv.withState sH
  have hcodeW : txEnv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode :=
    (hCodeAll _).trans (hinst _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  let stateW := (Blanc.Lift.WithdrawalRequest.systemProtocolPost txEnv).state
  let outputW := Blanc.Lift.WithdrawalRequest.systemProtocolOutput txEnv
  have wRun : processCheckedSystemTransaction txEnv withdrawalRequestPredeployAddress [] = .ok (stateW, outputW) :=
    Blanc.Lift.WithdrawalRequest.processCheckedSystemTransaction_withdrawal
      (benv := txEnv) CoveredFork.prague hcodeW
  have wCodeAll (a : Adr) : stateW.getCode a = chain.state.getCode a := by
    trans sH.getCode a
    · change (Blanc.Lift.WithdrawalRequest.systemProtocolPost txEnv).getCode a =
        (Blanc.Lift.WithdrawalRequest.systemProtocolBase txEnv).getCode a
      unfold Blanc.Lift.WithdrawalRequest.systemProtocolPost
      exact Blanc.Lift.WithdrawalRequest.systemFramePost_getCode _ _ _ _ _
    · exact hCodeAll a
  have wStorR : stateW.getStor beaconRootsAddress = sH.getStor beaconRootsAddress :=
    Blanc.Lift.WithdrawalRequest.systemFramePost_other_storage
      (Blanc.Lift.WithdrawalRequest.systemProtocolSevm txEnv)
      (Blanc.Lift.WithdrawalRequest.systemProtocolBase txEnv) .empty
      (systemTransactionGas - Blanc.Lift.WithdrawalRequest.systemProtocolGas txEnv) beaconRootsAddress
      (by change withdrawalRequestPredeployAddress ≠ beaconRootsAddress; decide)
  generalize hsW : stateW = sW at wRun wCodeAll wStorR
  generalize hoW : outputW = outW at wRun
  have hcodeC : (txEnv.withState sW).state.getCode consolidationRequestPredeployAddress = consolidationRequestCode :=
    (wCodeAll _).trans (hinst _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  obtain ⟨outC, cRun, _, _, _⟩ := Blanc.Lift.ConsolidationRequest.system_call_ok
    (benv := txEnv.withState sW) CoveredFork.prague hcodeC
  let stateC := RequestSystem.sysState SystemExecution.ConsolidationRequest.Amsterdam.sysShape sW
    consolidationRequestPredeployAddress
  have cCodeAll (a : Adr) : stateC.getCode a = chain.state.getCode a := by
    rw [RequestSystem.sysState_getCode]
    exact wCodeAll a
  have cStorR : stateC.getStor beaconRootsAddress = sW.getStor beaconRootsAddress :=
    RequestSystem.sysState_getStor_other _ _ (by decide)
  generalize hsC : stateC = sC at cCodeAll cStorR
  let boutC := BlockForward.requestsOutput .init outW.returnData outC.returnData
  have hActual : applyBody benv [] [] [] = .ok (sC, boutC) := by
    rw [← hsC]
    exact BlockForward.applyBody_forward (benv := benv) (txs := []) CoveredFork.prague
      rRun hlast hRun rfl rfl rfl wRun cRun
  obtain ⟨run, body⟩ := exists_bodyRoots hActual
  let hdr := commitHeaderTs parent ts sC boutC
  let block : Block := { header := hdr, txs := [], wds := [], ommers := [] }
  let next : BlockChain := ⟨appendBlock chain.blocks block, sC, 1⟩
  have hbenv_eq : initBenv .prague chain block.header = benv := by rfl
  have hB : beaconRootsCall benv.stat.rules benv = .ok (sR, ({} : BalBuilder)) := by
    unfold beaconRootsCall
    simp only [show benv.stat.rules.sys.beaconRoots = true from rfl, ite_true, Except.mapError, rRun, bind, Except.bind]
    rfl
  have hH : historyStorageCall benv.stat.rules historyEnv {} = .ok (sH, ({} : BalBuilder)) := by
    unfold historyStorageCall
    simp only [show benv.stat.rules.sys.historyStorage = true from rfl, ite_true, hlastH,
      Option.toExcept, Except.mapError, hRun, bind, Except.bind]
    rfl
  have hpre_eq : run.preState = sH := by
    obtain ⟨beacon, bbal, br, hr, hb, _, hh, _, _⟩ := body.pre
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hb.symm.trans hB))
    exact (Prod.mk.inj (Except.ok.inj (hh.symm.trans hH))).1
  have hpre_avoid : NoCreateAt systemAddress run.preRoots := by
    obtain ⟨beacon, bbal, br, hr, _, cb, _, ch, hpreR⟩ := body.pre
    unfold PreCall at cb ch
    rw [ite_eq_left (by rfl : benv.stat.rules.sys.beaconRoots = true)] at cb
    rw [ite_eq_left (by rfl : benv.stat.rules.sys.historyStorage = true)] at ch
    obtain ⟨_, rootsB⟩ := cb
    obtain ⟨_, rootsH⟩ := ch
    have factsR := systemContracts_facts (beaconRootsAddress, beaconRootsCode) List.mem_cons_self
    have factsH := systemContracts_facts (historyStorageAddress, historyStorageCode)
      (List.mem_cons_of_mem _ List.mem_cons_self)
    have hcodeH0 : benv.state.getCode historyStorageAddress = historyStorageCode :=
      hinst _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hcodeB_eq : beacon.getCode historyStorageAddress = historyStorageCode := by
      have hc := (rootsB.chain (a := historyStorageAddress)
        (by change (benv.state.getCode historyStorageAddress).toList ≠ []; rw [hcodeH0]; exact factsH.2.2)
        (by change ¬ isValidDelegation (benv.state.getCode historyStorageAddress); rw [hcodeH0]; exact factsH.2.1)).2
      change beacon.getCode historyStorageAddress = benv.state.getCode historyStorageAddress at hc
      rw [hc, hcodeH0]
    have havoidB : NoCreateAt systemAddress br := by
      refine MessageRoots.system_noCreateAt_of_spawnFree rootsB ?_ ?_ ?_ (by decide)
      · rw [hcodeR]; exact factsR.1
      · rw [hcodeR]; exact factsR.2.2
      · rw [hcodeR]; exact factsR.2.1
    have havoidH : NoCreateAt systemAddress hr := by
      refine MessageRoots.system_noCreateAt_of_spawnFree rootsH ?_ ?_ ?_ (by decide)
      · change SpawnFreeReach (beacon.getCode historyStorageAddress)
        rw [hcodeB_eq]; exact factsH.1
      · change (beacon.getCode historyStorageAddress).toList ≠ []
        rw [hcodeB_eq]; exact factsH.2.2
      · change ¬ isValidDelegation (beacon.getCode historyStorageAddress)
        rw [hcodeB_eq]; exact factsH.2.1
    intro f hf
    rw [hpreR, keptAll, List.flatMap_append, List.mem_append] at hf
    rcases hf with hf | hf
    · exact havoidB f hf
    · exact havoidH f hf
  obtain ⟨decoded, decode, transactions⟩ := body.transactions
  have decodeEmpty : ([] : List (Bytes ⊕ Tx)).mapM (decodeTx benv.stat.rules) = .ok [] := rfl
  obtain rfl := (Except.ok.inj (decode.symm.trans decodeEmpty)).symm
  have txSame := transactions.unique (TransactionsRoots.nil _ _)
  have htxEnv_st : run.txEnv.state = sH := by rw [txSame.1, hpre_eq]; rfl
  have noWd : withdrawalsPass benv.stat.rules run.txEnv run.txOut [] = (run.txEnv.state, run.txOut) := by
    unfold withdrawalsPass
    rw [show benv.stat.rules.header.withdrawalsRoot = true from rfl]
    simp only [ite_true]
    unfold BalBuilder.incorporateSystem
    rw [show benv.stat.rules.bal = none from rfl]
    rfl
  obtain ⟨reqSt, reqOut, pass⟩ := body.requests
  rw [noWd] at pass
  have self : run.txEnv.withState run.txEnv.state = run.txEnv := by cases run.txEnv; rfl
  rw [self] at pass
  unfold RequestPass at pass
  have enabled : run.txEnv.stat.rules.header.requestsHash = true := by rw [body.txEnv_stat]; rfl
  rw [ite_eq_left enabled] at pass
  obtain ⟨deps, acc, bal, _, fold, _⟩ := pass
  have reqs : run.txEnv.stat.rules.requests = pragueRequests := by rw [body.txEnv_stat]; rfl
  rw [reqs] at fold
  have hreq_avoid : NoCreateAt systemAddress (requestRootsOf run.requests) := by
    refine requestRoots_prague_noCreateAt fold ?_ ?_
    · rw [htxEnv_st]
      exact (hCodeAll _).trans (hinst _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    · rw [htxEnv_st]
      exact (hCodeAll _).trans (hinst _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hfork : (ChainConfig.single 1 .prague).forkAt block.header.number block.header.timestamp = .ok .prague :=
    ChainConfig.single_forkAt 1 .prague _ _
  have hgas0 : boutC.blockGasUsed = 0 := rfl
  have hhdrOK : validateHeader Fork.prague.ruleSet chain block.header = .ok () := by
    refine BlockForward.validateHeader_ok_of_facts CoveredFork.prague htip rfl hbf rfl ?_ rfl rfl rfl rfl ?_ hts rfl
      (by change (0 : Nat) ≤ 32; decide) rfl rfl rfl rfl rfl
    · rw [show block.header.gasLimit = 2 ^ 21 from rfl, hgl, hgu]
      exact BlockForward.calculateBaseFeePerGas_unit (by decide) (by decide) (by decide) (Nat.zero_le _)
    · change hdr.gasUsed ≤ 2 ^ 21
      rw [show hdr.gasUsed = boutC.blockGasUsed from rfl, hgas0]
      exact Nat.zero_le _
  have htrans : stateTransitionUsing (ChainConfig.single 1 .prague) chain block =
      .ok ⟨appendBlock chain.blocks block, sC, chain.chainId⟩ := by
    apply BlockForward.stateTransitionUsing_forward (by rw [hcid]; rfl) hfork CoveredFork.prague hhdrOK rfl
    · change applyBody (initBenv .prague chain block.header) [] [] [] = .ok (sC, boutC)
      rw [hbenv_eq]
      exact hActual
    all_goals rfl
  have htrans1 : stateTransitionUsing (ChainConfig.single 1 .prague) chain block = .ok next := by
    rw [htrans]
    exact congrArg Except.ok (by simp only [next, hcid])
  have hstep : KeptStep (ChainConfig.single 1 .prague) ⟨chain, block, .prague, boutC, run⟩ next := by
    refine ⟨htrans1, hfork, Or.inl CoveredFork.prague, ?_⟩
    change BodyRoots (initBenv .prague chain block.header) [] [] [] sC boutC run
    rw [hbenv_eq]
    exact body
  have hbound' : sum sC.bal < 2 ^ 256 := by
    obtain ⟨tr⟩ := BlockForward.configuredBlockTrace_forward hbound rfl hfork CoveredFork.prague htrans
    have hbwds : tr.block.wds = [] := by
      rw [BlockForward.ConfiguredBlockTrace.block_eq tr rfl]
    have hle := BlockForward.ConfiguredBlockTrace.sum_post_le tr hbwds
    change sum sC.bal ≤ sum chain.state.bal at hle
    exact Nat.lt_of_le_of_lt hle hbound
  refine ⟨block, sC, boutC, run, next, rfl, hstep, ?_, ?_, ?_, ?_, ?_, rfl, rfl, hgas0, rfl, hbound', ?_⟩
  · intro p hp
    rw [cCodeAll p.1]
    exact hinst p hp
  · rw [txSame.2.2.1]
    intro p hp
    cases hp
  · rw [txSame.2.2.1]
    intro p hp
    cases hp
  · intro f member
    change f ∈ keptAll (run.preRoots ++ run.txRoots ++ requestRootsOf run.requests) at member
    rw [txSame.2.2.2] at member
    simp only [List.append_nil, keptAll, List.flatMap_append, List.mem_append] at member
    rcases member with member | member
    · exact hpre_avoid f member
    · exact hreq_avoid f member
  · rw [cStorR, wStorR, hStorR_H, hwriteR]
  · exact appendBlock_getLast? chain.blocks block

/-- Negative control for **R-S8 (time-window)**: two empty-tx Prague blocks on an
installed ring starting with empty `systemAddress` at timestamps `1` and `8192`
collide at `timeKey 1 = timeKey 8192`, overwriting slot `timeKey 1` from `1` to
`8192` so `BeaconRoots.read` returns `none` for timestamp `1`. -/
theorem r_s8_time_control : BeaconRoots.R_S8_time_control := by
  have hsum0 : sum controlStart.state.bal < 2 ^ 256 := by
    change sum contracts.bal < 2 ^ 256
    rw [contracts_sum]
    decide
  obtain ⟨block1, st1, bout1, run1, middle, hmid_eq, step1, inst1, s1, a1, c1, stor1,
      hts1, hgl1, hgu1, hbf1, hbound1, htip1⟩ :=
    empty_step controlStart parentBlock 1 rfl rfl rfl rfl rfl (by decide) hsum0 contracts_installed
  have hmid_cid : middle.chainId = 1 := by rw [hmid_eq]
  have hts1_lt : block1.header.timestamp < 8192 := by
    rw [hts1]
    exact Nat.lt_of_sub_eq_succ rfl
  have hmid_bound : sum middle.state.bal < 2 ^ 256 := by
    rw [hmid_eq]
    exact hbound1
  have hmid_inst : SystemCodeInstalled middle.state := by
    rw [hmid_eq]
    exact inst1
  obtain ⟨block2, st2, bout2, run2, stop, hstop_eq, step2, _, s2, a2, c2, stor2,
      hts2, _, _, _, _, _⟩ :=
    empty_step middle block1 8192 htip1 hmid_cid hgl1 hgu1 hbf1
      hts1_lt hmid_bound hmid_inst
  let kb1 : KeptBlock := ⟨controlStart, block1, .prague, bout1, run1⟩
  let kb2 : KeptBlock := ⟨middle, block2, .prague, bout2, run2⟩
  have hhist : KeptHistory (ChainConfig.single 1 .prague) controlStart [kb1, kb2] stop :=
    KeptHistory.step (KeptHistory.step KeptHistory.refl step1) step2
  have hcov : ∀ b ∈ [kb1, kb2], CoveredFork b.fork := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact CoveredFork.prague
    · obtain rfl := List.mem_singleton.mp hb
      exact CoveredFork.prague
  have hclean : HistoryClean [kb1, kb2] := by
    refine ⟨?_, ?_, ?_⟩
    all_goals intro b hb; rcases List.mem_cons.mp hb with rfl | hb
    · exact s1
    · obtain rfl := List.mem_singleton.mp hb; exact s2
    · exact a1
    · obtain rfl := List.mem_singleton.mp hb; exact a2
    · exact c1
    · obtain rfl := List.mem_singleton.mp hb; exact c2
  have hfit : HistoryTimestampsFit [kb1, kb2] := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · change block1.header.timestamp + 8191 < 2 ^ 256
      rw [hts1]; decide
    · obtain rfl := List.mem_singleton.mp hb
      change block2.header.timestamp + 8191 < 2 ^ 256
      rw [hts2]; decide
  have hstor2_eq : storOf stop.state BeaconRoots.addr (BeaconRoots.timeKey 1) = (8192 : B256) := by
    have hstop_st : stop.state = st2 := by rw [hstop_eq]
    have htk : BeaconRoots.timeKey (8192 : B256) = BeaconRoots.timeKey (1 : B256) := by decide
    have h8192 : (8192 : Nat).toB256 = (8192 : B256) := rfl
    change (stop.state.getStor BeaconRoots.addr).get (BeaconRoots.timeKey 1) = 8192
    rw [hstop_st, stor2, ← htk, h8192]
    unfold BeaconRoots.writeState
    rw [State.getStor_setStorVal_self, State.getStor_setStorVal_self,
      Stor.get_set_ne _ (rootKey_ne_timeKey _), Stor.get_set_self]
  have hread_none : BeaconRoots.read (storOf stop.state BeaconRoots.addr) 1 = none := by
    unfold BeaconRoots.read
    rw [hstor2_eq, ite_eq_right]
    intro hcond
    exact absurd hcond.2 (by decide)
  refine ⟨ChainConfig.single 1 .prague, controlStart, stop, [kb1, kb2], hhist, hcov, rfl,
    contracts_systemEmpty, hclean, hfit, 0, 1,
    (by simp only [List.length_cons, List.length_nil]; decide),
    (by simp only [List.length_cons, List.length_nil]; decide),
    (by decide), ?_⟩
  change (BeaconRoots.blockWrite kb1).1 ≠ 0 ∧
    block1.header.timestamp + 8191 ≤ 2 ^ 256 ∧
    block2.header.timestamp = block1.header.timestamp + 8191 ∧
    BeaconRoots.timeKey (BeaconRoots.blockWrite kb2).1 = BeaconRoots.timeKey (BeaconRoots.blockWrite kb1).1 ∧
    storOf stop.state BeaconRoots.addr (BeaconRoots.timeKey (BeaconRoots.blockWrite kb1).1) =
      (BeaconRoots.blockWrite kb2).1 ∧
    (BeaconRoots.blockWrite kb2).1 ≠ (BeaconRoots.blockWrite kb1).1 ∧
    BeaconRoots.read (storOf stop.state BeaconRoots.addr) (BeaconRoots.blockWrite kb1).1 = none
  have hbw1 : (BeaconRoots.blockWrite kb1).1 = (1 : B256) := by
    change block1.header.timestamp.toB256 = 1; rw [hts1]; rfl
  have hbw2 : (BeaconRoots.blockWrite kb2).1 = (8192 : B256) := by
    change block2.header.timestamp.toB256 = 8192; rw [hts2]; rfl
  rw [hbw1, hbw2, hts1, hts2]
  exact ⟨by decide, by decide, by decide, by decide, hstor2_eq, by decide, hread_none⟩

end Blanc.Composition.Corpus.Proofs.RingJointControls
