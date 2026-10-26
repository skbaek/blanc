import Blanc.Lift.UniswapV2Factory.CreatePairTransaction
import Blanc.ExecutionMidHistoryIn

/-!
# Foreign installed accounts across the original Pair-creation transaction

The selected transaction is the retained `TxSplit 38` of block 10,008,355.
The factory frame changes only the factory and the new Pair. Admission
excludes an installed foreign account from being the sender, and the shared
settlement theorem preserves its code and storage through credits and cleanup.
This transports a foreign storage invariant across D; it does not establish
that invariant before D or supply a lifetime premise for the Pair address.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift

/-- Every installed account other than the factory and Pair retains its code
and complete storage across the original retained Pair-creation transaction. -/
theorem createPair_block_preserves_foreign_installed {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (hnumber : block.block.header.number = 10008355)
    (htime : block.block.header.timestamp = 1588710145)
    (cut : block.bodyTrace.transactions.TxSplit 38) {gasPrice : Nat}
    (htype : cut.tx.type = .zero gasPrice (some UniswapV2Pair.Creation.factory))
    (hdata : cut.tx.data = createPairData) (hvalue : cut.tx.value = 0)
    (hnonce : cut.tx.nonce = 205)
    (hfunds : (cut.tx.gas * cut.head.effectiveGasPrice).toB256 ≤
      cut.benv.state.bal cut.head.sender)
    (hgas : cut.head.intrinsicGas + 2600000 ≤ cut.tx.gas) (hgasb : cut.tx.gas < 2 ^ 64)
    (hfactory : cut.benv.state.getCode UniswapV2Pair.Creation.factory = code)
    (hfnonce : (cut.benv.state.get UniswapV2Pair.Creation.factory).nonce ≠ UInt64.max)
    (hpairNonce : (cut.benv.state.get UniswapV2Pair.Creation.pairAddress).nonce = 0)
    (hpairCode : (cut.benv.state.get UniswapV2Pair.Creation.pairAddress).code.size = 0)
    (hpairStor : (cut.benv.state.get UniswapV2Pair.Creation.pairAddress).stor.size = 0)
    (hslot2 : (cut.benv.state.get UniswapV2Pair.Creation.factory).stor.get fk2 = 0)
    (hslot5 : (cut.benv.state.get UniswapV2Pair.Creation.factory).stor.get fk5 = 0) :
    ∀ a, a ≠ UniswapV2Pair.Creation.factory →
      a ≠ UniswapV2Pair.Creation.pairAddress →
      (cut.benv.state.getCode a).toList ≠ [] →
      cut.afterBenv.state.getCode a = cut.benv.state.getCode a ∧
      cut.afterBenv.state.getStor a = cut.benv.state.getStor a := by
  have hstat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
    cut.before.stat_eq
  have hfork : mainnetChainConfig.forkAt 10008355 1588710145 = .ok cut.benv.stat.fork := by
    have h := block.forkAt
    rw [hnumber, htime] at h
    rw [hstat]
    exact h
  have hsg : cut.benv.stat.rules.stateGas = none := by
    rw [hstat]
    exact BodyStageCapabilities.historical.stateGas_none block.forkIn
  have hvalid : validateTransaction cut.benv.stat.rules cut.tx 0 =
      .ok (cut.head.intrinsicGas, cut.head.calldataFloorGasCost) :=
    (validateTransaction_sender_congr_none hsg).trans cut.head.validation
  obtain ⟨post, bout', htx, _, _, foreign⟩ := pair_createPair_transaction_muirGlacier_effects
    hfork htype hdata hvalue hnonce hvalid cut.head.checked hfunds hgas hgasb hfactory hfnonce
    hpairNonce hpairCode hpairStor hslot2 hslot5
  have hpost : post = cut.txState :=
    (Prod.mk.inj (Except.ok.inj (htx.symm.trans cut.head.result))).1
  subst hpost
  exact foreign

end Blanc.Lift.UniswapV2Factory
