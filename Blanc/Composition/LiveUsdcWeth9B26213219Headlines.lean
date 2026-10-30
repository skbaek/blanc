import Blanc.Composition.LiveUsdcWeth9B26213219Joint
import Blanc.Lift.UniswapV2Pair.StorageObservers
import Blanc.Lift.UniswapV2Pair.RawCallers
import Blanc.ExecutionStagedSstoreAttribution
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
* `weth9_net_flow`: each such word is the committed writer calls' credits minus debits to that
  holder, modulo `2 ^ 256`;
* `pair_ledger`: the Pair's supply word is the sum of the balance words of every LP holder the
  history touched;
* `pair_minimum_liquidity`: if no frame of that history entered at the Pair has caller zero, the
  supply word is zero or address zero's LP balance word is at least `1000`;
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

/-- **WETH9 net flow.**  At any block after WETH9's deployment, every holder the history from the
creation transaction touched has, as its stored balance word, what the decoded committed writer
calls of that history credited to it minus what they debited, modulo `2 ^ 256`. -/
theorem weth9_net_flow {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint) :
    Weth9.NetFlow (Weth9.midTouchedKeysIn weth d.trace)
      (Weth9.replayCalls (Weth9.midCommittedInvocationsIn weth d.trace))
      (checkpoint.state.getStor weth) := by
  have replay := d.replay
  rw [← weth_creation_address] at replay
  exact Weth9.netFlow_of_replay replay

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

/-- The raw frames of a mid history are closed under descent. -/
private theorem midRawFramesClosed {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future) :
    RawFramesClosed trace.rawFrames := by
  induction trace with
  | tail block cut =>
    exact RawFramesClosed.append cut.after.rawFrames_closed
      block.bodyTrace.requests.rawFrames_closed
  | step prior block ih => exact RawFramesClosed.append ih block.bodyTrace.rawFrames_closed

/-- **Uniswap V2 minimum liquidity.**  At any block after the USDC/WETH9 Pair's deployment, if no
frame of the history from the `createPair` transaction entered at the Pair has caller zero, the
stored supply is zero or address zero's stored LP balance is at least `MINIMUM_LIQUIDITY`. -/
theorem pair_minimum_liquidity {checkpoint : BlockChain} (d : PairDeploymentTo checkpoint)
    (callers : ∀ D ∈ d.trace.rawFrames, D.sevm.currentTarget = pair → D.sevm.caller ≠ 0) :
    MinLiquidity (checkpoint.state.getStor pair) := by
  have created := UniswapV2Factory.pair_history_initialized_from_createPair_block_noCollision
    d.block d.number d.time d.cut d.txType d.data d.value d.nonce d.funds d.gas d.gasBound
    d.factoryCode d.factoryNonce d.pairNonce d.pairCode d.slot2
  obtain ⟨_, steps, observed, auth, finish, K, replay, source, _, _, rep⟩ :=
    created.2.2 d.history d.fresh
  rw [pair_creation_address] at callers ⊢
  have raw : ∀ s ∈ steps, Exec.Frame.rootDeriv s.frame ∈ d.trace.rawFrames := by
    intro s member
    obtain ⟨_, _, target, mutable, _⟩ := auth s member
    have own : s.frame ∈ steps.flatMap
        (fun s => pairSubtreeFrames UniswapV2Pair.Creation.pairAddress s.frame) :=
      List.mem_flatMap.mpr ⟨s, member, by
        rw [PairTokenJoint.pairSubtreeFrames_self target mutable]
        exact List.mem_cons_self⟩
    rw [observed] at own
    obtain ⟨G, settled, obs⟩ := List.mem_flatMap.mp own
    unfold pairFrameObs at obs
    split at obs
    · rw [List.mem_singleton.mp obs]
      exact d.trace.mem_rawFrames_of_mem_settledFrames G settled
    · cases obs
  have floor := (source.supplyFloor ⟨Or.inl B256.toNat_zero, fun _ => rfl⟩
    (State.initialized_ledgerOn _ _ _ _).ledger
    (fun inv member => by
      obtain ⟨s, sMem, rfl⟩ := List.mem_map.mp member
      change s.frame.sevm.currentTarget ≠ 0
      rw [(auth s sMem).2.2.1]
      decide)
    (fun inv member => by
      obtain ⟨s, sMem, rfl⟩ := List.mem_map.mp member
      refine replay.callersNonzero (fun s m => ?_) (fun s m => ?_) s sMem
      · intro E below same
        exact callers E (midRawFramesClosed d.trace _ (raw s m) E below)
          (same.trans (auth s m).2.2.1)
      · exact callers _ (raw s m) (auth s m).2.2.1)).1
  exact rep.minLiquidity floor

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
