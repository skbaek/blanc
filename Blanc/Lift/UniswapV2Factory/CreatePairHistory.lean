import Blanc.Lift.UniswapV2Factory.CreatePairTransaction
import Blanc.Lift.UniswapV2Pair.PairMidHistoryIn

/-!
# The Pair's committed history from the factory's createPair inside its block

`pair_history_initialized_from_createPair_block` composes the factory's `createPair(WETH, USDC)`
transaction at Muir Glacier (`pair_createPair_transaction_muirGlacier`) at position 38 of block
10,008,355, cut by `TxSplit`, with the Pair's committed history over the rest of that block
followed by any later `HistFork` history (`pair_mid_history_initialized_withIn`, historical
supply `pairAdmittedSupplyH`). The `initialize` call runs inside transaction 38, so it is part of
the transaction-level theorem, not of the replayed history.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift

/-- **The Pair from the factory's createPair inside block 10,008,355.** Let `block` be a retained
`HistFork` block of the mainnet configuration at the Pair's deployment coordinates (block
10,008,355, timestamp 1,588,710,145), and `cut` its transaction fold cut at position 38, where
the transaction is the factory's `createPair(WETH, USDC)`: legacy type to the factory, the
`createPair` calldata, no value, nonce 205, enough funds and gas, the factory holding its
certified code with a nonce below the maximum, the Pair address with nonce zero, no code and no
storage, and the two `getPair` slots of the factory zero. Then the state right after the
transaction holds the certified Pair runtime at the Pair address with storage at the initialized
checkpoint; and over the rest of the block followed by any later `HistFork` history, with
trace-local freshness of the touched rows, the runtime stays installed and authenticated steps
whose committed subtrees are exactly the committed non-static Pair frames from the transaction
after `createPair` onwards replay from the initialized model state to a model state the future
Pair storage represents. -/
theorem pair_history_initialized_from_createPair_block {pre completed : BlockChain}
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
    (cut.afterBenv.state.getCode UniswapV2Pair.Creation.pairAddress).toList =
        UniswapV2Pair.code.toList ∧
      UniswapV2Pair.InitializedCheckpoint
        (cut.afterBenv.state.getStor UniswapV2Pair.Creation.pairAddress)
        UniswapV2Pair.Creation.factory
        (UniswapV2Pair.Creation.domainSeparator cut.benv.stat.chainId.toB256
          UniswapV2Pair.Creation.pairAddress)
        UniswapV2Pair.Creation.token0 UniswapV2Pair.Creation.token1 ∧
      ∀ {future : BlockChain}
        (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed future),
        UniswapV2Pair.WriterFreshKeys (fun _ => False)
          (UniswapV2Pair.pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
            ((MidHistoryTraceIn.tail block cut).append history)) →
        some (future.state.getCode UniswapV2Pair.Creation.pairAddress).toList =
            UniswapV2Pair.pairSem.image ∧
        ∃ steps : List UniswapV2Pair.PairStep,
          steps.flatMap (fun s => UniswapV2Pair.pairSubtreeFrames
              UniswapV2Pair.Creation.pairAddress s.frame) =
            UniswapV2Pair.committedPairFramesMidIn UniswapV2Pair.Creation.pairAddress
              ((MidHistoryTraceIn.tail block cut).append history) ∧
          (∀ s ∈ steps, s.AuthenticWith UniswapV2Pair.PairEntryAuth
            UniswapV2Pair.Creation.pairAddress) ∧
          ∃ (finish : UniswapV2Pair.State) (K' : UniswapV2Pair.WriterKey → Prop),
            UniswapV2Pair.PairObservedReplayWith UniswapV2Pair.PairAdmittedConsumesH
              (UniswapV2Pair.initializedState UniswapV2Pair.Creation.factory
                (UniswapV2Pair.Creation.domainSeparator cut.benv.stat.chainId.toB256
                  UniswapV2Pair.Creation.pairAddress)
                UniswapV2Pair.Creation.token0 UniswapV2Pair.Creation.token1) steps finish ∧
            UniswapV2Pair.SourceReplay
              (UniswapV2Pair.initializedState UniswapV2Pair.Creation.factory
                (UniswapV2Pair.Creation.domainSeparator cut.benv.stat.chainId.toB256
                  UniswapV2Pair.Creation.pairAddress)
                UniswapV2Pair.Creation.token0 UniswapV2Pair.Creation.token1)
              (steps.map UniswapV2Pair.PairStep.source) finish ∧
            UniswapV2Pair.runSourceInvocations
              (UniswapV2Pair.initializedState UniswapV2Pair.Creation.factory
                (UniswapV2Pair.Creation.domainSeparator cut.benv.stat.chainId.toB256
                  UniswapV2Pair.Creation.pairAddress)
                UniswapV2Pair.Creation.token0 UniswapV2Pair.Creation.token1)
              (steps.map UniswapV2Pair.PairStep.source) = some finish ∧
            (∀ k, K' k → k ∈ UniswapV2Pair.pairMidTouchedKeysIn
              UniswapV2Pair.Creation.pairAddress
              ((MidHistoryTraceIn.tail block cut).append history)) ∧
            UniswapV2Pair.WriterRep K'
              (future.state.getStor UniswapV2Pair.Creation.pairAddress) finish := by
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
  obtain ⟨post, bout', htx, hcode, hinit⟩ := pair_createPair_transaction_muirGlacier hfork
    htype hdata hvalue hnonce hvalid cut.head.checked hfunds hgas hgasb hfactory hfnonce
    hpairNonce hpairCode hpairStor hslot2 hslot5
  have hpost : post = cut.txState :=
    (Prod.mk.inj (Except.ok.inj (htx.symm.trans cut.head.result))).1
  subst hpost
  refine ⟨hcode, hinit, ?_⟩
  intro future history fresh
  exact UniswapV2Pair.pair_mid_history_initialized_withIn
    (fun _ inj apart => UniswapV2Pair.pairAdmittedSupplyH inj apart UniswapV2Pair.pairSem
      UniswapV2Pair.pairSem_image)
    (fun _ _ _ _ consumed => consumed.exact) HistFork.neutral BodyStageCapabilities.historical
    (fun _ hf => hf.dataNonZero_ge) ((MidHistoryTraceIn.tail block cut).append history)
    (by show some _ = some UniswapV2Pair.code.toList; rw [← hcode]; rfl) hinit fresh

end Blanc.Lift.UniswapV2Factory
