import Blanc.Composition.LiveUsdcWeth9FactoryAnchorData
import Blanc.Composition.LiveUsdcWeth9B26213219Code
import Blanc.Lift.UniswapV2Factory.History
import Blanc.Lift.UniswapV2Pair.Creation.Facts
import Blanc.Lift.Usdc.HistoryAnchorObservationData

/-! Factory identity at the original Pair-creation transaction from a finite
observation at its parent block. Correspondence remains explicit and unadopted.
The original trace's prefix supplies preservation; no final-code read is used. -/
namespace Blanc.Composition.LiveUsdcWeth9FactoryAnchor

open Jaune Blanc.ExecutionTrace Blanc.Lift

open Blanc.Composition.LiveUsdcWeth9FactoryAnchorData

/-- The observed anchor is exactly one block before the recorded D block. -/
theorem number_before_d : blockNumber + 1 = Usdc.HistoryAnchorObservationData.D.blockNumber := by
  decide +kernel

/-- The observed parent precedes the recorded D timestamp. -/
theorem timestamp_before_d : timestamp < Usdc.HistoryAnchorObservationData.D.blockTimestamp := by
  decide +kernel

/-- This is the same D block already used by the receipt consumer. -/
theorem d_hash_eq : dBlockHash = Usdc.HistoryAnchorObservationData.D.blockHash := by
  decide +kernel

/-- Finite correspondence for the original D prestate. The parent tip and
header coordinates identify the observation; `runtime` is a read at that
same state, not an assertion about code at the selected transaction. -/
structure OriginalDParent {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (parent : Block) : Prop where
  chain : pre.chainId = 1
  tip : pre.blocks.getLast? = some parent
  parentNumber : parent.header.number = blockNumber
  parentTimestamp : parent.header.timestamp = timestamp
  parentHash : parent.header.hash = blockHash
  parentStateRoot : parent.header.stateRoot = stateRoot
  dNumber : block.block.header.number = Usdc.HistoryAnchorObservationData.D.blockNumber
  dHash : block.block.header.hash = dBlockHash
  parentLink : block.block.header.parentHash = blockHash
  runtime : (pre.state.getCode factory).data.toList = codeBytes

/-- The reused observed literal is already kernel-identified with the checked
factory runtime. This establishes installation only at the observed prestate. -/
theorem OriginalDParent.installed {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post} {parent : Block}
    (observed : OriginalDParent block parent) :
    pre.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact observed.runtime.trans LiveUsdcWeth9B26213219.factory_code

/-- Supply precisely the factory argument of `CDObservation.OriginalD.pairDeployment`.
The original block's opening and transaction prefix preserve the observed code;
CREATE2 is permitted and raw safety is produced by the factory certificate. -/
theorem OriginalDParent.factory_at_pair_cut {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post} {parent : Block}
    (observed : OriginalDParent block parent) (cut : block.bodyTrace.transactions.TxSplit 38) :
    cut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code := by
  exact block.code_before_txSplit_of_runtimeSafety UniswapV2Factory.runtimeSafety cut
    BodyStageCapabilities.historical observed.installed

end Blanc.Composition.LiveUsdcWeth9FactoryAnchor
