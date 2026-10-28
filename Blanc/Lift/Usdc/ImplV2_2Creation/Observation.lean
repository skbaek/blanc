import Blanc.Lift.Usdc.ImplV2_2Creation.ObservationData
import Blanc.Lift.Usdc.ImplV2_2Creation.SignedInput

/-! Unadopted finite observation binding for the original implementation deployment.
The original configured block, selected slot and receipt remain explicit.
Header roots identify observed fields, not consensus or trie authentication. -/
namespace Blanc.Lift.Usdc.ImplV2_2Creation

open Jaune ExecutionTrace

/-- The observed creation coordinates select the recorded historical fork. -/
theorem observed_fork :
    mainnetChainConfig.forkAt ObservationData.blockNumber ObservationData.blockTimestamp =
      .ok .shanghai := by
  decide +kernel

/-- The successful concrete receipt uses the cumulative gas counter. -/
theorem observed_receipt_success : ObservationData.receipt.2.succeeded = true := rfl

/-- The already-certified exact signed input occupies the original slot. These
correspondence fields are unresolved fetched-data inputs, not adopted assumptions. -/
structure OriginalObservation {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed) where
  number : block.block.header.number = ObservationData.blockNumber
  timestamp : block.block.header.timestamp = ObservationData.blockTimestamp
  hash : block.block.header.hash = ObservationData.blockHash
  stateRoot : block.block.header.stateRoot = ObservationData.stateRoot
  transactionRoot : block.block.header.txsRoot = ObservationData.transactionRoot
  receiptRoot : block.block.header.receiptRoot = ObservationData.receiptRoot
  slot : block.block.txs[26]? = some SignedInput.envelope.entry
  receipt : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (26 : Nat).toBytes)]? =
    some ObservationData.receipt

/-- Construct the selected cut inside the actual supplied original trace. -/
noncomputable def OriginalObservation.cut {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : OriginalObservation block) : block.bodyTrace.transactions.TxSplit 26 :=
  block.bodyTrace.txSplitOfSlot observed.slot (tx := SignedInput.tx) rfl

/-- Reuse the strict signed-constructor proof and concrete original receipt.
No runtime, initialized storage, signing hash or recovery result is supplied. -/
theorem OriginalObservation.installed {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : OriginalObservation block)
    (cut : block.bodyTrace.transactions.TxSplit 26) :
    cut.afterBenv.state.getCode F2prime.implementationV2_2 = Impl.code ∧
      cut.afterBenv.state.getStor F2prime.implementationV2_2 =
        solcOwnerConstructorStorage Stor.empty originalCreator := by
  exact SignedInput.effects_of_original_slot block cut observed.slot observed.receipt
    observed_receipt_success

/-- Every retained node of the original observed creation stays away from the
USDC proxy. The signed input determines the target; no success premise is needed. -/
theorem OriginalObservation.retainedNodes_target_ne_proxy {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : OriginalObservation block) :
    ∀ R ∈ observed.cut.head.settledRoots, ∀ n ∈ Exec.retainedNodes R.run,
      n.sevm.currentTarget ≠ usdcProxy := by
  let cut := observed.cut
  obtain ⟨_, same⟩ := block.bodyTrace.txSplit_tx_eq_of_slot cut observed.slot
    (tx := SignedInput.tx) rfl
  have recovered := SignedInput.recovered
  rw [← same] at recovered
  have sender := block.txSplit_sender_of_recovery cut recovered
  have receiver : cut.tx.type.receiver? = none := by rw [same]; rfl
  have input : cut.tx.data = code.toList := by rw [same]; rfl
  have target : cut.head.msg.currentTarget = F2prime.implementationV2_2 := by
    rw [cut.head.creation_target_eq receiver, sender, same]
    exact create_address
  have stateGas : cut.benv.beginTransaction.stat.rules.stateGas = none := by
    change cut.benv.stat.rules.stateGas = none
    have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
      block.txSplit_stat cut
    rw [stat]
    exact block.forkIn.stateGas_none
  apply cut.head.retainedNodes_currentTarget_ne_of_create_noExecs
    receiver input cert_check (by decide +kernel) stateGas
  rw [target]
  decide +kernel

end Blanc.Lift.Usdc.ImplV2_2Creation
