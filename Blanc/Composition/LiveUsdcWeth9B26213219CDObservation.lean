import Blanc.Composition.LiveUsdcWeth9B26213219History
import Blanc.Composition.UniswapV2PairUsdcOriginSeed
import Blanc.Lift.Usdc.HistoryAnchorObservationData

/-! Concrete C/D receipts at the original transaction cuts.
Header/body/receipt correspondence is explicit and unadopted. The observations
do not supply factory code, intervening history, HASH-T or a final invariant. -/
namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Usdc
  Blanc.Composition.UniswapV2PairUsdcWeth9

namespace CDObservation

open HistoryAnchorObservationData

theorem c_fork : mainnetChainConfig.forkAt C.blockNumber C.blockTimestamp =
    .ok .byzantium := by decide +kernel

theorem d_fork : mainnetChainConfig.forkAt D.blockNumber D.blockTimestamp =
    .ok .muirGlacier := by decide +kernel

theorem c_bloom : C.bloom = HistoricalBloomExclusion.observedCBloom := by decide +kernel
theorem d_bloom : D.bloom = HistoricalBloomExclusion.observedDBloom := by decide +kernel
theorem c_success : C.receipt.2.succeeded = true := rfl
theorem d_success : D.receipt.2.succeeded = true := rfl

/-- The concrete receipt contains exactly the event required by the existing
factory inverse, including the encoded Pair address and pair count. -/
theorem d_logs : D.receipt.2.logs = [⟨UniswapV2Pair.Creation.factory,
    [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
     0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
     0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2],
    UniswapV2Pair.Creation.pairAddress.toB256.toBytes ++ (1 : B256).toBytes⟩] := by
  rfl

/-- Nine correspondence fields for the original proxy-creation block. -/
structure OriginalC {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post) where
  number : block.block.header.number = C.blockNumber
  timestamp : block.block.header.timestamp = C.blockTimestamp
  hash : block.block.header.hash = C.blockHash
  stateRoot : block.block.header.stateRoot = C.stateRoot
  transactionRoot : block.block.header.txsRoot = C.transactionRoot
  receiptRoot : block.block.header.receiptRoot = C.receiptRoot
  bloom : block.block.header.bloom = C.bloom
  body : block.block.txs = HistoryAnchorBody.cBody
  receipt : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
    some C.receipt

/-- Nine correspondence fields for the original Pair-creation block. -/
structure OriginalD {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post) where
  number : block.block.header.number = D.blockNumber
  timestamp : block.block.header.timestamp = D.blockTimestamp
  hash : block.block.header.hash = D.blockHash
  stateRoot : block.block.header.stateRoot = D.stateRoot
  transactionRoot : block.block.header.txsRoot = D.transactionRoot
  receiptRoot : block.block.header.receiptRoot = D.receiptRoot
  bloom : block.block.header.bloom = D.bloom
  body : block.block.txs = HistoryAnchorBody.dBody
  receipt : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (38 : Nat).toBytes)]? =
    some D.receipt

/-- The same C cut receives the constructor seed from the observed successful
receipt and existing exact signer proof. Slot separation remains explicit. -/
theorem OriginalC.seed {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : OriginalC block) (cut : block.bodyTrace.transactions.TxSplit 22)
    {owner : Adr} {tracked : Adr → Prop}
    (apart : ∀ spender, tracked spender →
      allowSlot owner spender ≠ implSlot ∧ allowSlot owner spender ≠ adminSlot) :
    cut.head.messageOut.error = none ∧
      ProxyCreation.OriginalConstructorSeed cut.afterBenv.state owner tracked := by
  obtain ⟨_, nonce, receiver, value, input, _⟩ :=
    HistoryAnchorBody.c_original_cut_fields block cut observed.body
  exact ProxyCreation.original_constructor_seed_of_receipt_cut22 block cut
    block.forkIn.stateGas_none receiver input value
    (HistoryAnchorBody.c_original_cut_sender_mainnet block cut observed.body) nonce
    observed.receipt c_success apart

/-- The actual D receipt supplies collision and guard facts used by the live
deployment record. Factory identity, original continuation and HASH-T remain
separate inputs; no initial Pair storage observation is required. -/
def OriginalD.pairDeployment {checkpoint pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : OriginalD block) (cut : block.bodyTrace.transactions.TxSplit 38)
    (factory : cut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code)
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig post checkpoint)
    (fresh : UniswapV2Pair.WriterFreshKeys (fun _ => False)
      (UniswapV2Pair.pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
        ((MidHistoryTraceIn.tail block cut).append history))) : PairDeploymentTo checkpoint := by
  obtain ⟨factoryNonce, pairNonce, pairCode, guard⟩ :=
    original_factory_preconditions_of_receipt block cut observed.body observed.number
      observed.timestamp factory observed.receipt d_success d_logs
  obtain ⟨txType, data, value, nonce, funds, gas, gasBound, _⟩ :=
    original_factory_admission_of_body block cut observed.body observed.number observed.timestamp
  exact ⟨pre, post, block, observed.number, observed.timestamp, cut, 4000000000,
    txType, data, value, nonce, funds, gas, gasBound, factory, factoryNonce,
    pairNonce, pairCode, guard, history, fresh⟩

/-- The constructor-produced deployment record retains the supplied original
suffix and later history definitionally. -/
theorem OriginalD.pairDeployment_trace {checkpoint pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : OriginalD block) (cut : block.bodyTrace.transactions.TxSplit 38)
    (factory : cut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code)
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig post checkpoint)
    (fresh : UniswapV2Pair.WriterFreshKeys (fun _ => False)
      (UniswapV2Pair.pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
        ((MidHistoryTraceIn.tail block cut).append history))) :
    (observed.pairDeployment cut factory history fresh).trace =
      (MidHistoryTraceIn.tail block cut).append history := rfl

end CDObservation
end Blanc.Composition.LiveUsdcWeth9B26213219
