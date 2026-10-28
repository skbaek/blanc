import Blanc.Lift.Usdc.ImplV1Creation.ObservationData
import Blanc.Lift.Usdc.ImplV1Creation.SignedInput

/-! Unadopted finite observation binding for the original implementation deployment.
The original configured block, selected slot and receipt remain explicit.
Header roots identify observed fields, not consensus or trie authentication. -/
namespace Blanc.Lift.Usdc.ImplV1Creation

open Jaune ExecutionTrace

/-- The observed creation coordinates select the recorded historical fork. -/
theorem observed_fork :
    mainnetChainConfig.forkAt ObservationData.blockNumber ObservationData.blockTimestamp =
      .ok .byzantium := by
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
  slot : block.block.txs[30]? = some SignedInput.envelope.entry
  receipt : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (30 : Nat).toBytes)]? =
    some ObservationData.receipt

/-- Construct the selected cut inside the actual supplied original trace. -/
noncomputable def OriginalObservation.cut {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : OriginalObservation block) : block.bodyTrace.transactions.TxSplit 30 :=
  block.bodyTrace.txSplitOfSlot observed.slot (tx := SignedInput.tx) rfl

/-- Reuse the strict signed-constructor proof and concrete original receipt.
No runtime, initialized storage, signing hash or recovery result is supplied. -/
theorem OriginalObservation.installed {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : OriginalObservation block)
    (cut : block.bodyTrace.transactions.TxSplit 30) :
    cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      cut.afterBenv.state.getStor ProxyCreation.initialImplementation.toAdr =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  exact SignedInput.effects_of_original_slot block cut observed.slot observed.receipt
    observed_receipt_success

end Blanc.Lift.Usdc.ImplV1Creation
