import Blanc.Composition.LiveUsdcWeth9B26213219History
import Blanc.Lift.Weth9.Creation.SignedInput
import Blanc.Lift.Weth9.Creation.ObservationData

/-! Unadopted original WETH deployment observations. The exact supplied block,
selected slot and receipt remain an explicit correspondence boundary. No
consensus inclusion, trie authentication or new history assumption is adopted. -/
namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Weth9.Creation

/-- The recorded wire is the exact strict-decoder input. -/
theorem weth_observed_signed_bytes :
    SignedInput.signedBytes = ObservationData.signedBytes := by
  unfold SignedInput.signedBytes SignedInput.payload
  rw [ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

/-- Strict signed decoding of the observed original transaction bytes. -/
theorem weth_observed_signed_decode :
    ObservationData.signedBytes.toBLT?.bind (fun blt => blt.toExTx.toOption) =
      some SignedInput.tx := by
  rw [← weth_observed_signed_bytes]
  exact SignedInput.signed_decode

/-- The original deployment coordinates select Byzantium. -/
theorem weth_observed_fork :
    mainnetChainConfig.forkAt ObservationData.blockNumber ObservationData.blockTimestamp =
      .ok .byzantium := by
  decide +kernel

/-- Fetched correspondence for the actual original block and receipt. Header
roots identify observed fields, not a recomputation over the supplied world. -/
structure WethOriginalObservation {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed) where
  number : block.block.header.number = ObservationData.blockNumber
  timestamp : block.block.header.timestamp = ObservationData.blockTimestamp
  hash : block.block.header.hash = ObservationData.blockHash
  stateRoot : block.block.header.stateRoot = ObservationData.stateRoot
  transactionRoot : block.block.header.txsRoot = ObservationData.transactionRoot
  receiptRoot : block.block.header.receiptRoot = ObservationData.receiptRoot
  slot : block.block.txs[85]? = some SignedInput.envelope.entry
  receipt : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (85 : Nat).toBytes)]? =
    some ObservationData.receipt

noncomputable def WethOriginalObservation.cut {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : WethOriginalObservation block) : block.bodyTrace.transactions.TxSplit 85 :=
  block.bodyTrace.txSplitOfSlot observed.slot (tx := SignedInput.tx) rfl

/-- Concrete signed fields and successful receipt construct the deployment
input. The exact hash computation, subsequent actual history and HASH-T remain
explicit; no final footprint, funding, collision or allowance premise is supplied. -/
noncomputable def WethOriginalObservation.deployment
    {checkpoint pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : WethOriginalObservation block)
    (hashed : signingPayload.keccak =
      0x1e62afdbf54076edd8083f93eab1bf693f2a5a3675886b669d13d9b3e6221235)
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed checkpoint)
    (fresh : Weth9.KeysFresh (fun _ => False)
      (Weth9.midTouchedKeysIn Weth9.Creation.weth9Address
        ((MidHistoryTraceIn.tail block observed.cut).append history))) :
    WethDeploymentTo checkpoint := by
  exact .of_original_creation_receipt block observed.number observed.timestamp
    observed.slot (tx := SignedInput.tx) rfl rfl rfl rfl rfl
    (SignedInput.recovered hashed) rfl observed.receipt rfl history fresh

end Blanc.Composition.LiveUsdcWeth9B26213219
