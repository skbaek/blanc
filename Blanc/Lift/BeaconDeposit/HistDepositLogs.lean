import Blanc.Lift.BeaconDeposit.HistDepositEntries
import Blanc.ExecutionRetainedLogMembership
import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionCellProvenance
import Blanc.ExecutionHistoryInWarmth
import Blanc.ExecutionStagedFrameEnv
import Blanc.Lift.BeaconDeposit.Creation.HistoricalTxTrace

/-! Each extracted deposit node produces a target log in the same actual transaction/block output. -/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace

/-- The exact producing frame's event survives complete settlement and the actual suffix. -/
theorem transactionListIn_node_block_log_of_rules
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntryRules)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat)
    {node : B256} (accepted : node ∈ trace.settledFrames.flatMap (committedFrameNodes ca)) :
    ∃ log ∈ finalBout.blockLogs, log.address = ca := by
  obtain ⟨frame, member, accepted⟩ := List.mem_flatMap.mp accepted
  obtain ⟨log, address, appended⟩ := transactionListIn_node_frame_log_of_rules trace admitted
    installed invariant notCreated sumNof fork blockIndex member accepted
  have frameFork := (trace.rootEntryIn fork _
    (trace.mem_rawFrames_of_mem_settledFrames frame member)).2
  have logs : frame.post.logs = frame.pre.logs ++
      (Exec.committedStateBoundaries frame.run).flatMap Exec.boundaryOwnLogs :=
    Exec.committed_logs_noStateGas frame.run frame.committed frameFork.stateGas_none rfl rfl
  have ledger : (Exec.committedStateBoundaries frame.run).flatMap Exec.boundaryOwnLogs = [log] :=
    List.append_cancel_left (logs.symm.trans appended)
  refine ⟨log, trace.retained_log_mem fork.stateGas_none fork.bal_none member ?_, address⟩
  rw [ledger]
  exact List.mem_singleton.mpr rfl

/-- Empty target-filtered logs exclude every extracted node of this same retained suffix. -/
theorem transactionListIn_nodes_eq_nil_of_empty_logs_of_rules
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntryRules)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat)
    (emptyLogs : finalBout.blockLogs.filter (fun log => log.address == ca) = []) :
    trace.settledFrames.flatMap (committedFrameNodes ca) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro node accepted
  obtain ⟨log, logged, address⟩ := transactionListIn_node_block_log_of_rules trace admitted
    installed invariant notCreated sumNof fork blockIndex accepted
  have filtered : log ∈ finalBout.blockLogs.filter (fun log => log.address == ca) :=
    List.mem_filter.mpr ⟨logged, by rw [address]; exact beq_self_eq_true ca⟩
  rw [emptyLogs] at filtered
  exact List.not_mem_nil filtered

/-- Empty target logs of this actual block exclude deposit nodes in its actual suffix.
Entry code and storage are at the transaction cut; fork, capacity and no-created facts
come from the retained block, and admission remains an explicit intermediate obligation. -/
theorem configuredBlockIn_suffix_no_deposit_of_empty_logs_of_rules
    {ca : Adr} {cfg : ChainConfig} {pre post : BlockChain} {i : Nat}
    {initialHistory : List B256}
    (block : ConfiguredBlockTraceIn HistFork cfg pre post)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (admitted : cut.after.FrameAdmitted ca beaconEntryRules)
    (installed : cut.afterBenv.state.getCode ca = code)
    (invariant : SolInv (cut.afterBenv.state.getStor ca) initialHistory)
    (emptyLogs : block.blockOutput.blockLogs.filter (fun log => log.address == ca) = []) :
    cut.after.settledFrames.flatMap (committedFrameNodes ca) = [] ∧
      block.bodyTrace.transactionBenv.state.getCode ca = code ∧
      SolInv (block.bodyTrace.transactionBenv.state.getStor ca) initialHistory := by
  have fork : HistFork cut.afterBenv.stat.fork := by
    rw [block.txSplit_stat cut]
    exact block.forkIn
  have bound := block.txSplit_bound cut BodyStageCapabilities.historical
  have sumNof : sum cut.afterBenv.state.bal < 2 ^ 256 := by omega
  have emptyTransactionLogs : block.bodyTrace.transactionBout.blockLogs.filter
      (fun log => log.address == ca) = [] := by
    rw [← block.bodyTrace.blockLogs_eq_transactionBout]
    exact emptyLogs
  have nodes := transactionListIn_nodes_eq_nil_of_empty_logs_of_rules cut.after admitted
    installed invariant (block.txSplit_notCreated cut ca) sumNof fork
    block.block.header.number emptyTransactionLogs
  have final := transactionListIn_code_solInv_admitted_of_rules cut.after admitted
    installed invariant (block.txSplit_notCreated cut ca) sumNof fork block.block.header.number
  rw [nodes, List.append_nil] at final
  exact ⟨nodes, final⟩

/-- The actual Muir suffix and proof-of-work rewards preserve the cut's deposit history
when this block has no target logs. Admission remains explicit until readiness is derived. -/
theorem muirBlock_suffix_solInv_of_empty_logs_admitted_of_rules
    {ca : Adr} {cfg : ChainConfig} {pre post : BlockChain} {i : Nat}
    {initialHistory : List B256}
    (block : ConfiguredBlockTraceIn HistFork cfg pre post)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (muir : block.fork = .muirGlacier)
    (admitted : cut.after.FrameAdmitted ca beaconEntryRules)
    (installed : cut.afterBenv.state.getCode ca = code)
    (invariant : SolInv (cut.afterBenv.state.getStor ca) initialHistory)
    (emptyLogs : block.blockOutput.blockLogs.filter (fun log => log.address == ca) = []) :
    cut.after.settledFrames.flatMap (committedFrameNodes ca) = [] ∧
      post.state.getCode ca = code ∧ SolInv (post.state.getStor ca) initialHistory := by
  obtain ⟨nodes, finalCode, finalInv⟩ := configuredBlockIn_suffix_no_deposit_of_empty_logs_of_rules
    block cut admitted installed invariant emptyLogs
  have withdrawalsDisabled : (initBenv block.fork pre block.block.header).stat.rules.header.withdrawalsRoot = false := by
    rw [muir]
    rfl
  have requestsDisabled : (initBenv block.fork pre block.block.header).stat.rules.header.requestsHash = false := by
    rw [muir]
    rfl
  have requestState : block.bodyTrace.requestState = block.bodyTrace.transactionBenv.state :=
    (block.bodyTrace.requests.disabled_endpoints requestsDisabled).1.trans
      (block.bodyTrace.withdrawals_disabled withdrawalsDisabled).1
  have rewards := block.bodyTrace.rewardState_eq
  rw [requestState] at rewards
  have finalState : post.state = block.bodyTrace.rewardState :=
    (congrArg BlockChain.state block.postEq).trans block.bodyTrace.finalState_eq
  have nonempty : (block.bodyTrace.transactionBenv.state.getCode ca).toList ≠ [] := by
    rw [finalCode]
    exact beaconInstalledCertH.nonempty
  refine ⟨nodes, ?_⟩
  rw [finalState, rewards]
  split
  · exact ⟨finalCode, finalInv⟩
  · rw [Blanc.payRewards_getCode, Blanc.payRewards_getStor _ _ _ _ _ nonempty]
    exact ⟨finalCode, finalInv⟩

/-- Compatibility form for the original Beacon admission. -/
theorem transactionListIn_node_block_log
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat)
    {node : B256} (accepted : node ∈ trace.settledFrames.flatMap (committedFrameNodes ca)) :
    ∃ log ∈ finalBout.blockLogs, log.address = ca :=
  transactionListIn_node_block_log_of_rules trace
    (transactionListIn_beaconEntry_toRules trace admitted) installed invariant notCreated sumNof fork blockIndex accepted

/-- Compatibility form for the original Beacon admission. -/
theorem transactionListIn_nodes_eq_nil_of_empty_logs
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat)
    (emptyLogs : finalBout.blockLogs.filter (fun log => log.address == ca) = []) :
    trace.settledFrames.flatMap (committedFrameNodes ca) = [] :=
  transactionListIn_nodes_eq_nil_of_empty_logs_of_rules trace
    (transactionListIn_beaconEntry_toRules trace admitted) installed invariant notCreated sumNof fork blockIndex emptyLogs

/-- Compatibility form for the original Beacon admission. -/
theorem configuredBlockIn_suffix_no_deposit_of_empty_logs
    {ca : Adr} {cfg : ChainConfig} {pre post : BlockChain} {i : Nat}
    {initialHistory : List B256}
    (block : ConfiguredBlockTraceIn HistFork cfg pre post)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (admitted : cut.after.FrameAdmitted ca beaconEntry)
    (installed : cut.afterBenv.state.getCode ca = code)
    (invariant : SolInv (cut.afterBenv.state.getStor ca) initialHistory)
    (emptyLogs : block.blockOutput.blockLogs.filter (fun log => log.address == ca) = []) :
    cut.after.settledFrames.flatMap (committedFrameNodes ca) = [] ∧
      block.bodyTrace.transactionBenv.state.getCode ca = code ∧
      SolInv (block.bodyTrace.transactionBenv.state.getStor ca) initialHistory :=
  configuredBlockIn_suffix_no_deposit_of_empty_logs_of_rules block cut
    (transactionListIn_beaconEntry_toRules cut.after admitted) installed invariant emptyLogs

/-- Compatibility form for the original Beacon admission. -/
theorem muirBlock_suffix_solInv_of_empty_logs_admitted
    {ca : Adr} {cfg : ChainConfig} {pre post : BlockChain} {i : Nat}
    {initialHistory : List B256}
    (block : ConfiguredBlockTraceIn HistFork cfg pre post)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (muir : block.fork = .muirGlacier)
    (admitted : cut.after.FrameAdmitted ca beaconEntry)
    (installed : cut.afterBenv.state.getCode ca = code)
    (invariant : SolInv (cut.afterBenv.state.getStor ca) initialHistory)
    (emptyLogs : block.blockOutput.blockLogs.filter (fun log => log.address == ca) = []) :
    cut.after.settledFrames.flatMap (committedFrameNodes ca) = [] ∧
      post.state.getCode ca = code ∧ SolInv (post.state.getStor ca) initialHistory :=
  muirBlock_suffix_solInv_of_empty_logs_admitted_of_rules block cut muir
    (transactionListIn_beaconEntry_toRules cut.after admitted) installed invariant emptyLogs

/-- Every actual suffix frame in a Muir block supplies the selected-rule Beacon entry.
Calldata and warmth come from the same block; delegation is disabled by its selected fork. -/
theorem muirBlock_suffix_beaconEntryRules
    {ca : Adr} {cfg : ChainConfig} {pre post : BlockChain} {i : Nat}
    (block : ConfiguredBlockTraceIn HistFork cfg pre post)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (muir : block.fork = .muirGlacier) :
    cut.after.FrameAdmitted ca beaconEntryRules := by
  rw [cut.after.frameAdmitted_iff_rawFrames]
  intro root member _
  have transactionMember : root ∈ block.bodyTrace.transactions.rawFrames := by
    rw [cut.rawFrames_eq]
    exact List.mem_append_right _ member
  have blockMember : root ∈ block.rawFrames := by
    simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames, List.mem_append]
    exact Or.inl (Or.inr transactionMember)
  have cutFork : cut.afterBenv.stat.fork = .muirGlacier := by
    rw [block.txSplit_stat cut]
    exact muir
  have frameFork := (cut.after.rootEntryIn (F := fun f => f = .muirGlacier)
    cutFork root member).2
  refine ⟨block.calldata_bound BodyStageCapabilities.historical
    (fun _ hf => hf.dataNonZero_ge) root blockMember, ?_,
    block.transactions_rawFrames_warmIn BodyStageCapabilities.historical
      (fun _ hf => hf.two_mem_precompiles) root transactionMember⟩
  intro enabled
  change root.sevm.benvStat.fork.ruleSet.delegationEnabled = true at enabled
  rw [frameFork] at enabled
  cases enabled

/-- The same Muir suffix and rewards preserve the cut's history, with entry readiness derived. -/
theorem muirBlock_suffix_solInv_of_empty_logs
    {ca : Adr} {cfg : ChainConfig} {pre post : BlockChain} {i : Nat}
    {initialHistory : List B256}
    (block : ConfiguredBlockTraceIn HistFork cfg pre post)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (muir : block.fork = .muirGlacier)
    (installed : cut.afterBenv.state.getCode ca = code)
    (invariant : SolInv (cut.afterBenv.state.getStor ca) initialHistory)
    (emptyLogs : block.blockOutput.blockLogs.filter (fun log => log.address == ca) = []) :
    cut.after.settledFrames.flatMap (committedFrameNodes ca) = [] ∧
      post.state.getCode ca = code ∧ SolInv (post.state.getStor ca) initialHistory :=
  muirBlock_suffix_solInv_of_empty_logs_admitted_of_rules block cut muir
    (muirBlock_suffix_beaconEntryRules block cut muir) installed invariant emptyLogs

/-- The actual signed index-2 creation and actual remaining block reach D with empty history.
The body identity, creation success and empty target logs are concrete-binding inputs;
frame readiness, installation and the cut invariant are derived on this same trace. -/
theorem actual_muir_deployment_to_D {pre D : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D)
    (cut : block.bodyTrace.transactions.TxSplit 2)
    (number : block.block.header.number = 11052984)
    (timestamp : block.block.header.timestamp = 1602667372)
    (atTwo : block.bodyTrace.decodedTxs[2]? = some Creation.HistoricalTx.tx)
    (success : cut.head.messageOut.error = none)
    (emptyLogs : block.blockOutput.blockLogs.filter
      (fun log => log.address == Creation.depositAddress) = []) :
    cut.after.settledFrames.flatMap (committedFrameNodes Creation.depositAddress) = [] ∧
      D.state.getCode Creation.depositAddress = code ∧
      SolInv (D.state.getStor Creation.depositAddress) [] := by
  have selected : mainnetChainConfig.forkAt block.block.header.number
      block.block.header.timestamp = .ok .muirGlacier := by
    rw [number, timestamp]
    decide +kernel
  have muir : block.fork = .muirGlacier := Except.ok.inj (block.forkAt.symm.trans selected)
  obtain ⟨installed, invariant, _⟩ :=
    Creation.HistoricalTx.actual_block_cut block cut number timestamp atTwo success
  exact muirBlock_suffix_solInv_of_empty_logs block cut muir
    (bytes_eq_of_image (congrArg some installed)) invariant emptyLogs

/-- A successful receipt bound at key 2 of the actual final block output supplies
creation success. Later indexed transactions and body finalization preserve that key. -/
theorem actual_muir_deployment_to_D_of_receipt {pre D : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D)
    (cut : block.bodyTrace.transactions.TxSplit 2)
    (number : block.block.header.number = 11052984)
    (timestamp : block.block.header.timestamp = 1602667372)
    (atTwo : block.bodyTrace.decodedTxs[2]? = some Creation.HistoricalTx.tx)
    (receipt : Fin 5 × Receipt)
    (atIndex : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (2 : Nat).toBytes)]? = some receipt)
    (success : receipt.2.succeeded = true)
    (emptyLogs : block.blockOutput.blockLogs.filter
      (fun log => log.address == Creation.depositAddress) = []) :
    cut.after.settledFrames.flatMap (committedFrameNodes Creation.depositAddress) = [] ∧
      D.state.getCode Creation.depositAddress = code ∧
      SolInv (D.state.getStor Creation.depositAddress) [] := by
  have indexEq : cut.index = 2 := cut.putIndex_eq.1
  have fork : HistFork cut.benv.stat.fork := by
    change HistFork cut.afterBenv.stat.fork
    rw [block.txSplit_stat cut]
    exact block.forkIn
  have later : ∀ item ∈ block.bodyTrace.decodedTxs.putIndex.drop (2 + 1),
      cut.index < item.1 := by
    intro item member
    obtain ⟨j, bound, itemEq⟩ := List.mem_iff_getElem.mp member
    have split := List.drop_eq_getElem_cons bound
    rw [itemEq] at split
    simp only [List.drop_drop] at split
    have position := (putIndex_aux_drop_eq_cons block.bodyTrace.decodedTxs 0 _ split).1
    omega
  have actual := cut.head.receipt_of_settledRoots_after_later_indices cut.after
    fork.stateGas_none (by omega) (by omega) later
  rw [block.bodyTrace.receiptsTrie_eq_transactionBout, ← indexEq] at atIndex
  have receiptEq := Option.some.inj (atIndex.symm.trans actual)
  have succeeded := congrArg (fun r : Fin 5 × Receipt => r.2.succeeded) receiptEq
  change receipt.2.succeeded = cut.head.messageOut.error.isNone at succeeded
  rw [success] at succeeded
  exact actual_muir_deployment_to_D block cut number timestamp atTwo
    (Option.isNone_iff_eq_none.mp succeeded.symm) emptyLogs

end Blanc.Lift.BeaconDeposit
