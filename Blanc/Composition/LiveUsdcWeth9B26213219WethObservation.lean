import Blanc.Composition.LiveUsdcWeth9B26213219History
import Blanc.Lift.Weth9.Creation.SignedInput
import Blanc.Lift.Weth9.Creation.ObservationData
import Blanc.Lift.Weth9.Creation.SigningHash

/-! Original WETH deployment observations. The supplied block's number and
timestamp, the signed transaction at its slot 85 and the receipt at key 85 are
the observed correspondence consumed here. No consensus inclusion, trie
authentication or new history assumption is adopted. -/
namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Weth9.Creation

/-- Fetched correspondence for the actual original block and receipt: the
header's number and timestamp, the signed creation transaction at slot 85 and
the receipt at key 85. Each field is consumed by `WethOriginalObservation.deployment`. -/
structure WethOriginalObservation {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed) where
  number : block.block.header.number = ObservationData.blockNumber
  timestamp : block.block.header.timestamp = ObservationData.blockTimestamp
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

/-- The observed original WETH9 creation block joined to a configured history ending at
`checkpoint`, with trace-local freshness of the keys that history touches. No installed code,
`SumNof`, footprint, funding, collision or signing-hash premise is an input. -/
structure WethObservedHistory (checkpoint : BlockChain) where
  pre : BlockChain
  completed : BlockChain
  block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed
  observed : WethOriginalObservation block
  history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed checkpoint
  fresh : Weth9.KeysFresh (fun _ => False)
    (Weth9.midTouchedKeysIn Weth9.Creation.weth9Address
      ((MidHistoryTraceIn.tail block observed.cut).append history))

/-- The deployment record, from the observation and the checked signing hash. -/
noncomputable def WethObservedHistory.deployment {checkpoint : BlockChain}
    (h : WethObservedHistory checkpoint) : WethDeploymentTo checkpoint :=
  h.observed.deployment Weth9.Creation.signingPayload_hash h.history h.fresh

end Blanc.Composition.LiveUsdcWeth9B26213219
