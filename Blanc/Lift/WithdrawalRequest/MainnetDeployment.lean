import Blanc.Lift.WithdrawalRequest.HistoryFifo
import Blanc.Lift.WithdrawalRequest.WordDelivery
import Blanc.Lift.WithdrawalRequest.DeploymentHistory
import Blanc.Lift.WithdrawalRequest.Creation.HistoricalTxTrace
import Blanc.ExecutionBodyTransactionCut
import Blanc.ExecutionSettledReceiptLogs
import Blanc.ExecutionHistoryInSystemOpenings
import Blanc.ExecutionHistoryInCodeAt
import Blanc.ExecutionHistoryInCreateAvoid

/-!
# EIP-7002 at its actual mainnet deployment

`WithdrawalDeploymentObservation` holds the one-block observations of the actual deployment
(mainnet block 21,881,389): its header number and timestamp (with hash and state root as
identity), the signed keyless creation transaction `Creation.HistoricalTx.tx` at body slot 0
(its bytes, hash and kernel-recovered sender are proved in `Creation.HistoricalTx`), a
succeeded receipt at key 0, empty SYSTEM code and canonical beacon-roots code at the parent
block 21,881,388, and the last pre-Prague checkpoint 22,431,083 with its beacon-roots,
history-storage and consolidation code (the adopted Beacon seam anchor values). All values
are unadopted candidate observations, not consensus or trie authentication.

From them, the retained configured trace of that block and the following Cancun blocks to
the checkpoint form a `DeploymentHistory`: the canonical deployment input, the Cancun forks of
the whole prefix, beacon code at every later opening, and SYSTEM emptiness at the
post-deployment boundary are all derived. The remaining premises are the generic theorems'
SYSTEM-sender, 7702-authority and CREATE-avoidance exclusions, stated over the same actual
traces; CREATE avoidance at beacon roots is derived from its present code.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.ExecutionTrace Blanc.WithdrawalRequest

/-- No positive transaction index shares the receipt key of index 0 (the RLP empty string). -/
theorem receipt_key_ne_zero {other : Nat} (positive : 0 < other) :
    (BLT.bytes other.toBytes).toBytes ≠ (BLT.bytes (0 : Nat).toBytes).toBytes := by
  intro same
  have zero : (BLT.bytes (0 : Nat).toBytes).toBytes = [0x80] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, BLT.toBytes]
    rfl
  rw [zero] at same
  have nonempty : other.toBytes ≠ [] := by
    intro empty
    have roundtrip := RlpConcrete.nat_bytes_roundtrip other
    rw [empty] at roundtrip
    change 0 = other at roundtrip
    omega
  rcases bytes : other.toBytes with _ | ⟨a, rest⟩
  · exact nonempty bytes
  · rw [bytes] at same
    cases rest with
    | nil =>
        rw [BLT.toBytes] at same
        split at same
        · rename_i small
          have equal := (List.cons.inj same).1
          rw [equal] at small
          exact (by decide : ¬ (0x80 : UInt8) < 0x80) small
        · have lengths := congrArg List.length same
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at lengths
          omega
    | cons c rest =>
        rw [BLT.toBytes] at same <;>
          try simp only [List.cons.injEq, reduceCtorEq, and_false, imp_self, implies_true]
        have lengths := congrArg List.length same
        split at lengths <;>
          simp only [List.length_cons, List.length_nil, List.length_append] at lengths <;> omega

/-- One-block observations of the actual EIP-7002 deployment and of the last pre-Prague
checkpoint (candidate values; see the module header). -/
structure WithdrawalDeploymentObservation {before after : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (checkpoint : BlockChain) : Prop where
  number : block.block.header.number = 21881389
  timestamp : block.block.header.timestamp = 1739979863
  hash : block.block.header.hash =
    0xbffb31041b1839dbdd4cd4531b55f979f1b4f58665ee8de987329b30038ed283
  stateRoot : block.block.header.stateRoot =
    0x0c5d1c80666c4f618c2d07b4d87c45e5a8e9e601b6745373e223ea8ba3b8843a
  slotZero : block.block.txs[0]? = some (.inr Creation.HistoricalTx.tx)
  receipt : ∃ r : Fin 5 × Receipt,
    block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (0 : Nat).toBytes)]? = some r ∧
      r.2.succeeded = true
  parentSystemEmpty : before.state.getCode systemAddress = ByteArray.empty
  parentBeacon : before.state.getCode beaconRootsAddress = beaconRootsCode
  checkpointTip : ∃ tip, checkpoint.blocks.getLast? = some tip ∧
    tip.header.number = 22431083 ∧ tip.header.timestamp = 1746612299 ∧
    tip.header.hash = 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237 ∧
    tip.header.stateRoot = 0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3
  beaconAtP : checkpoint.state.getCode beaconRootsAddress = beaconRootsCode
  historyAtP : checkpoint.state.getCode historyStorageAddress = historyStorageCode
  consolidationAtP :
    checkpoint.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode

namespace WithdrawalDeploymentObservation

variable {before after checkpoint : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after}

/-- The observed header selects Cancun. -/
theorem fork (obs : WithdrawalDeploymentObservation block checkpoint) : block.fork = .cancun := by
  have selected : mainnetChainConfig.forkAt block.block.header.number
      block.block.header.timestamp = .ok .cancun := by
    rw [obs.number, obs.timestamp]
    decide +kernel
  exact Except.ok.inj (block.forkAt.symm.trans selected)

/-- The retained transaction at position 0 is the observed signed creation transaction, and
the observed receipt makes its message succeed. -/
theorem slot_success (obs : WithdrawalDeploymentObservation block checkpoint)
    (cut : block.bodyTrace.transactions.TxSplit 0) :
    cut.tx = Creation.HistoricalTx.tx ∧ cut.head.messageOut.error = none := by
  have sameTx := (block.bodyTrace.txSplit_tx_eq_of_slot cut obs.slotZero rfl).2
  refine ⟨sameTx, ?_⟩
  obtain ⟨receipt, atIndex, success⟩ := obs.receipt
  have indexEq : cut.index = 0 := cut.putIndex_eq.1
  have fork : HistFork cut.benv.stat.fork := by
    change HistFork cut.afterBenv.stat.fork
    rw [block.txSplit_stat cut]
    exact block.forkIn
  have later : ∀ item ∈ block.bodyTrace.decodedTxs.putIndex.drop (0 + 1),
      cut.index < item.1 := by
    intro item member
    obtain ⟨j, bound, itemEq⟩ := List.mem_iff_getElem.mp member
    have split := List.drop_eq_getElem_cons bound
    rw [itemEq] at split
    simp only [List.drop_drop] at split
    have position := (putIndex_aux_drop_eq_cons block.bodyTrace.decodedTxs 0 _ split).1
    omega
  have actual := cut.head.receipt_of_settledRoots_after_suffix cut.after
    fork.stateGas_none (fun item member => by
      rw [indexEq]
      exact receipt_key_ne_zero (by have := later item member; omega))
  rw [block.bodyTrace.receiptsTrie_eq_transactionBout, ← indexEq] at atIndex
  have receiptEq := Option.some.inj (atIndex.symm.trans actual)
  have succeeded := congrArg (fun r : Fin 5 × Receipt => r.2.succeeded) receiptEq
  change receipt.2.succeeded = cut.head.messageOut.error.isNone at succeeded
  rw [success] at succeeded
  exact Option.isNone_iff_eq_none.mp succeeded.symm

/-- The observed slot, receipt and header identify the canonical EIP-7002 deployment at
position 0 of the retained block. -/
def deploymentCut (obs : WithdrawalDeploymentObservation block checkpoint)
    (cut : block.bodyTrace.transactions.TxSplit 0) : Creation.DeploymentCut block where
  position := 0
  cut := cut
  input := by
    obtain ⟨sameTx, success⟩ := obs.slot_success cut
    have hfork : cut.benv.stat.fork = .cancun := by
      have selected := congrArg BenvStat.fork (block.txSplit_stat cut)
      change cut.benv.stat.fork = block.fork at selected
      exact selected.trans obs.fork
    revert success
    generalize cut.head = head
    revert head
    rw [sameTx]
    intro head success
    exact Creation.HistoricalTx.actual_input head hfork success
  fork := obs.fork

/-- The following blocks to the observed checkpoint all select Cancun. -/
theorem following_cancun (obs : WithdrawalDeploymentObservation block checkpoint)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint) :
    following.ForksSatisfy (fun f => f = .cancun) := by
  obtain ⟨tip, tipLast, tipNumber, tipTime, -, -⟩ := obs.checkpointTip
  have afterLast : after.blocks.getLast? = some block.block :=
    (congrArg (fun chain : BlockChain => chain.blocks.getLast?) block.postEq).trans
      (appendBlock_getLast? _ _)
  have startFork : mainnetChainConfig.forkAt block.block.header.number
      block.block.header.timestamp = .ok .cancun := by
    rw [obs.number, obs.timestamp]
    decide +kernel
  have finishFork : mainnetChainConfig.forkAt tip.header.number tip.header.timestamp =
      .ok .cancun := by
    rw [tipNumber, tipTime]
    decide +kernel
  exact (following.forksSatisfy_between afterLast startFork tipLast finishFork).mono (by
    intro f bounded
    cases f <;> simp only [Fork.index] at bounded <;> first | rfl | omega)

/-- SYSTEM code, empty at the parent block, stays empty through the deployment block's
opening system call and its position-0 transaction. -/
theorem cut_systemEmpty (obs : WithdrawalDeploymentObservation block checkpoint)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (avoid : ∀ root ∈ block.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress) :
    cut.afterBenv.state.getCode systemAddress = ByteArray.empty := by
  have fork := obs.fork
  rw [block.rawFrames_txSplit cut] at avoid
  have member : ∀ {xs : List Exec.Deriv}, (∀ root ∈ xs, root ∈ block.bodyTrace.beacon.rawFrames ++
      block.bodyTrace.history.rawFrames ++ cut.before.rawFrames ++ cut.head.rawFrames ++
      (MidHistoryTraceIn.tail block cut).rawFrames) →
      ∀ root ∈ xs, root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress :=
    fun sub root inXs => avoid root (sub root inXs)
  have hsg : (initBenv block.fork before block.block.header).stat.rules.stateGas = none := by
    change block.fork.ruleSet.stateGas = none
    rw [fork]
    rfl
  obtain ⟨beaconEmpty, -⟩ := block.bodyTrace.beacon.codeAt_empty_noStateGas hsg
    obs.parentSystemEmpty (member (fun root inner => by simp only [List.mem_append]; tauto))
  obtain ⟨historyEmpty, -⟩ := block.bodyTrace.history.codeAt_empty_noStateGas hsg
    beaconEmpty (member (fun root inner => by simp only [List.mem_append]; tauto))
  have cutStat : cut.benv.stat = (initBenv block.fork before block.block.header).stat :=
    block.txSplit_stat cut
  obtain ⟨-, beforeEmpty⟩ := cut.before.codeAt_empty_noStateGas hsg
    (Or.inl (by change block.fork.ruleSet.delegationEnabled = false; rw [fork]; rfl))
    (member (fun root inner => by simp only [List.mem_append]; tauto)) historyEmpty
  obtain ⟨-, headEmpty⟩ := cut.head.codeAt_empty_noStateGas (by rw [cutStat]; exact hsg)
    (Or.inl (by
      rw [cutStat]
      change block.fork.ruleSet.delegationEnabled = false
      rw [fork]
      rfl))
    (member (fun root inner => by simp only [List.mem_append]; tauto)) beforeEmpty
  exact headEmpty

end WithdrawalDeploymentObservation

/-- Cancun selection of a mid history extends along appended Cancun blocks. -/
theorem MidHistoryTraceIn.allCancun_append {cfg : ChainConfig} {start : Benv}
    {current future : BlockChain} {mid : MidHistoryTraceIn HistFork cfg start current}
    (hmid : mid.AllCancun) (following : ConfiguredHistoryTraceIn HistFork cfg current future)
    (forks : following.ForksSatisfy (fun f => f = .cancun)) :
    (mid.append following).AllCancun := by
  induction following with
  | refl => exact hmid
  | step prior block ih => exact ⟨ih forks.1, forks.2⟩

/-- Cancun opening installations of appended blocks are beacon code at each opening. -/
theorem MidHistoryTraceIn.beaconCodeInstalled_append {cfg : ChainConfig} {start : Benv}
    {current future : BlockChain} {mid : MidHistoryTraceIn HistFork cfg start current}
    (hmid : mid.BeaconCodeInstalled)
    (following : ConfiguredHistoryTraceIn HistFork cfg current future)
    (forks : following.ForksSatisfy (fun f => f = .cancun))
    (openings : following.SystemCodeAtOpenings) :
    (mid.append following).BeaconCodeInstalled := by
  induction following with
  | refl => exact hmid
  | step prior block ih =>
      refine ⟨ih forks.1 openings.1, ?_⟩
      apply openings.2 (beaconRootsAddress, beaconRootsCode)
      rw [HistFork.installedAt_beacon_of_cancun block.forkIn forks.2]
      exact List.mem_cons_self

/-- The actual deployment block, its position-0 cut and the following configured blocks to
the checkpoint, as the deployment history rooted at the observed transaction. -/
def mainnetDeploymentHistory {before after checkpoint : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint) :
    DeploymentHistory mainnetChainConfig checkpoint where
  before := before
  after := after
  block := block
  deployment := obs.deploymentCut cut
  following := following

/-- The observations derive the prefix's Cancun forks, beacon code at every later opening and
SYSTEM emptiness at the post-deployment boundary. Beacon code present at the parent excludes
CREATE at beacon roots by collision, so it is kept through the deployment block and every
following block. The remaining inputs are the SYSTEM-sender exclusion over the prefix and
CREATE avoidance at SYSTEM (empty code, so collision does not apply) over the deployment
block and the following blocks. -/
theorem mainnetDeploymentHistory_admission {before after checkpoint : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (senders : ((MidHistoryTraceIn.tail block cut).append following).NoSenderAt systemAddress)
    (systemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress) :
    (mainnetDeploymentHistory block cut following obs).Admission := by
  have fork := obs.fork
  have forks := obs.following_cancun following
  have afterBeacon : after.state.getCode beaconRootsAddress = beaconRootsCode := by
    have facts := systemContracts_facts _ beaconRoots_mem_systemContracts
    exact block.codeAt_keep_of_cancunOnwards BodyStageCapabilities.historical block.forkIn
      (by rw [fork]; decide) (Or.inl (by rw [fork]; rfl))
      (block.createAvoid_of_cancunOnwards BodyStageCapabilities.historical block.forkIn
        (by rw [fork]; decide) (Or.inl (by rw [fork]; rfl)) obs.parentBeacon facts.2.2 facts.2.1)
      obs.parentBeacon facts.2.2 facts.2.1
  have openings := (following.systemCodeAtOpenings_of_cancun_present forks afterBeacon).1
  exact {
    forks := MidHistoryTraceIn.allCancun_append (mid := MidHistoryTraceIn.tail block cut)
      fork following forks
    senders := senders
    beacon := MidHistoryTraceIn.beaconCodeInstalled_append
      (mid := MidHistoryTraceIn.tail block cut) trivial following forks openings
    avoid := by
      intro root member
      change root ∈ ((MidHistoryTraceIn.tail block cut).append following).rawFrames at member
      rw [MidHistoryTraceIn.append_rawFrames] at member
      apply systemAvoid root
      rcases List.mem_append.mp member with inner | inner
      · rw [block.rawFrames_txSplit cut]
        exact List.mem_append_left _ (List.mem_append_right _ inner)
      · exact List.mem_append_right _ inner
    systemEmpty := obs.cut_systemEmpty cut
      (fun root member => systemAvoid root (List.mem_append_left _ member)) }

/-- **EIP-7002 FIFO from the actual mainnet deployment.** For the retained configured trace
of the observed deployment block (its position-0 cut) and the following Cancun blocks to the
observed last pre-Prague checkpoint, and any configured history after it, every committed
submission is, in order, either a withdrawal record published by its blocks or a record still
in the final concrete queue. Deployment input, Cancun selection, beacon code at the prefix's
openings, SYSTEM emptiness, EIP-7002 code and INIT at the checkpoint, and the other three
system installations there all come from the observations. The remaining premises are the
SYSTEM-sender, 7702-authority and CREATE-avoidance exclusions over these same traces, and the
cumulative submission cap. -/
theorem history_fifo_mainnet {before after checkpoint final : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (history : ConfiguredHistoryTrace mainnetChainConfig checkpoint final)
    (prefixSenders :
      ((MidHistoryTraceIn.tail block cut).append following).NoSenderAt systemAddress)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (senders : history.NoSenderAt systemAddress)
    (authorities : history.NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions history).length ≤ wordOccurrenceCap) :
    HistoryFifo history :=
  history_fifo (mainnetDeploymentHistory block cut following obs)
    (mainnetDeploymentHistory_admission block cut following obs prefixSenders
      prefixSystemAvoid)
    history ⟨obs.beaconAtP, obs.historyAtP, obs.consolidationAtP⟩ senders authorities avoid
    occurrences

/-- **Exact EIP-7002 delivery from the actual mainnet deployment.** Over the same observed
deployment block, Cancun prefix and checkpoint as `history_fifo_mainnet`, a queue entry at
index `q` at block B's request boundary is emitted by block D at position `q % 16` when the
actual post-checkpoint history extension from B to D has depth `q / 16`, after exactly the
entries ahead of it. -/
theorem block_word_delivery_mainnet
    {before after checkpoint preB postB preD postD : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig before after)
    (cut : block.bodyTrace.transactions.TxSplit 0)
    (following : ConfiguredHistoryTraceIn HistFork mainnetChainConfig after checkpoint)
    (obs : WithdrawalDeploymentObservation block checkpoint)
    (prefixSenders :
      ((MidHistoryTraceIn.tail block cut).append following).NoSenderAt systemAddress)
    (prefixSystemAvoid : ∀ root ∈ block.rawFrames ++ following.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (historyB : ConfiguredHistoryTrace mainnetChainConfig checkpoint preB)
    (blockB : ConfiguredBlockTrace mainnetChainConfig preB postB)
    (historyD : ConfiguredHistoryTrace mainnetChainConfig checkpoint preD)
    (blockD : ConfiguredBlockTrace mainnetChainConfig preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : ((ConfiguredHistoryTrace.step historyD blockD).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap)
    (modelB : Blanc.WithdrawalRequest.State)
    (repB : RepresentsStorage (blockB.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get modelB)
    {q : Nat} {entry : Blanc.WithdrawalRequest.Entry} (queued : modelB.queue[q]? = some entry)
    (exactDepth : depth = q / 16) :
    ∃ modelD : Blanc.WithdrawalRequest.State,
      RepresentsStorage (blockD.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get modelD ∧
      blockD.bodyTrace.requests.withdrawalOut.returnData = systemOutput modelD ∧
      (emitted modelD)[q % 16]? = some entry ∧
      (emitted modelD).take (q % 16 + 1) =
        (modelB.queue.drop (16 * depth)).take (q % 16 + 1) :=
  block_word_delivery_from_deployment (mainnetDeploymentHistory block cut following obs)
    (mainnetDeploymentHistory_admission block cut following obs prefixSenders
      prefixSystemAvoid)
    historyB blockB historyD blockD extension
    ⟨obs.beaconAtP, obs.historyAtP, obs.consolidationAtP⟩ senders authorities avoid
    occurrences modelB repB queued exactDepth

end Blanc.Lift.WithdrawalRequest
