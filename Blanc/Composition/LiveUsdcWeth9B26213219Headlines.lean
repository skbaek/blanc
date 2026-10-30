import Blanc.Composition.LiveUsdcWeth9B26213219Joint
import Blanc.Lift.UniswapV2Pair.StorageObservers
import Blanc.Lift.Weth9.Holders

/-!
# Live WETH9 and USDC/WETH9 Pair headlines over storage words

Each headline is rooted in the actual deployment record (`WethDeploymentTo`, `PairDeploymentTo`):
the retained creation block, its creation transaction, and the later configured history ending at
the block named by the record.  Each concludes one named Prop over storage words and balances read
from that block's state; the model replay that proves it stays below.

* `weth9_deployment`: the actual creation transaction installs WETH9's runtime and leaves exactly the
  constructor's storage;
* `weth9_backed`: the balance words of every holder the history touched sum to at most WETH9's ether;
* `pair_ledger`: the Pair's supply word is the sum of the balance words of every LP holder the
  history touched;
* `live_pair_reserves_backed`: after any mainnet history from the observed block, the reserves stored
  in the Pair's slot `8` are at most the Pair's USDC and WETH9 balance words.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.UniswapV2Pair
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- WETH9 is deployed in `w`: its runtime is installed and its storage is the constructor's. -/
def WethDeployed (w : Jaune.State) : Prop :=
  (w.getCode weth).toList = Weth9.code.toList ∧ w.getStor weth = Weth9.Creation.deployedStor

/-- **WETH9 deployment (actual transaction).**  The deployment record's creation transaction, in its
retained block 4719568, installs WETH9's runtime at `weth` and leaves exactly the constructor's
storage. -/
theorem weth9_deployment {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint) :
    WethDeployed d.cut.afterBenv.state := by
  have created := Weth9.weth9_history_committed_from_creation_block d.block d.number d.time
    d.cut d.txType d.data d.value d.nonce d.sender d.funds d.gas d.gasBound d.empty
  rw [WethDeployed, weth_creation_address]
  exact ⟨created.1, created.2.1⟩

/-- **WETH9 backing.**  At any block after WETH9's deployment, the stored balance words of every
holder the history from the creation transaction touched sum to at most WETH9's ether. -/
theorem weth9_backed {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint) :
    Weth9.EtherBacked (Weth9.midTouchedKeysIn weth d.trace) (checkpoint.state.getStor weth)
      (checkpoint.state.bal weth) := by
  have foot := d.foot.2
  rw [weth_creation_address] at foot ⊢
  exact Weth9.FootInv.etherBacked foot

/-- The Pair's actual creation history replays to a model state with the LP ledger, represented
by the final storage over keys the history touched. -/
private theorem PairDeploymentTo.replayed {checkpoint : BlockChain} (d : PairDeploymentTo checkpoint) :
    ∃ (finish : UniswapV2Pair.State) (K : WriterKey → Prop),
      (∀ k, K k → k ∈ pairMidTouchedKeysIn pair d.trace) ∧
      WriterRep K (checkpoint.state.getStor pair) finish ∧ finish.Ledger := by
  have created := UniswapV2Factory.pair_history_initialized_from_createPair_block_noCollision
    d.block d.number d.time d.cut d.txType d.data d.value d.nonce d.funds d.gas d.gasBound
    d.factoryCode d.factoryNonce d.pairNonce d.pairCode d.slot2
  obtain ⟨_, _, _, _, finish, K, _, source, _, sub, rep⟩ := (created.2.2 d.history d.fresh)
  rw [pair_creation_address]
  exact ⟨finish, K, sub, rep,
    source.ledger (State.initialized_ledgerOn _ _ _ _).ledger⟩

/-- **Uniswap V2 LP ledger.**  At any block after the USDC/WETH9 Pair's deployment, its stored
supply (slot `0`) is the sum of the stored LP balance words of every holder the history from the
`createPair` transaction touched. -/
theorem pair_ledger {checkpoint : BlockChain} (d : PairDeploymentTo checkpoint) :
    LpLedgerBalanced (pairMidTouchedKeysIn pair d.trace) (checkpoint.state.getStor pair) := by
  obtain ⟨_, _, sub, rep, ledger⟩ := d.replayed
  have fresh := d.fresh
  rw [← pair_creation_address] at fresh
  exact rep.lpLedgerBalanced sub fresh ledger

/-- The Pair's reserves, as stored, are at most its USDC and WETH9 balance words. -/
def ReservesBacked (w : Jaune.State) : Prop :=
  pairReserve0 (w.getStor pair) ≤ Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot pair)) ∧
  pairReserve1 (w.getStor pair) ≤ ((w.getStor weth).get (Weth9.balSlot pair)).toNat

/-- **Live USDC/WETH9 Pair: reserves backed.**  After any mainnet history from the observed block,
the reserves stored in the Pair's slot `8` are at most the Pair's USDC and WETH9 balance words.
The premises are exactly those of `joint_from_original_history`. -/
theorem live_pair_reserves_backed
    {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (wd : WethDeploymentTo checkpoint) (pd : PairDeploymentTo checkpoint)
    (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (wethSenderExcluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initialPair : wd.cut.afterBenv.state.getCode pair = ByteArray.empty)
    (continuation : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    (usdcHistory : OriginalUsdcHistory (anchor.futureTrace continuation))
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation)) :
    ReservesBacked future.state := by
  obtain ⟨_, _, _, ⟨_, _, _, _, _, _, _, rep⟩, r0, _, r1, _⟩ :=
    joint_from_original_history anchor wd pd link holderFresh wethSenderExcluded avoid
      initialPair continuation usdcHistory pairFresh usdcFresh wethFresh governance
  exact ⟨rep.reserve0 ▸ r0, rep.reserve1 ▸ r1⟩

end Blanc.Composition.LiveUsdcWeth9B26213219
