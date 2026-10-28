import Blanc.Composition.LiveUsdcWeth9B26213219Checkpoint
import Blanc.Lift.Weth9.DeployBlockHistory
import Blanc.Lift.Weth9.AllowanceReplay
import Blanc.Lift.UniswapV2Factory.CreatePairHistory
import Blanc.Lift.UniswapV2Pair.PairPositionalCalls
import Blanc.ExecutionMidHistoryOwnCode
import Blanc.ExecutionMidHistoryCallers

/-!
# The concrete checkpoint from deployment histories ending at one block

The input records contain retained configured blocks, their actual transaction
cuts, creation transaction/prestate facts, later histories and HASH-T. They do
not contain the final footprint or Pair representation. Those are produced by
the landed L4 theorems, on the same `checkpoint.state` as the finite observations.
The WETH allowance-zero provenance and USDC L3 future allowance result remain
separate obligations; this module does not claim they have been discharged.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.UniswapV2Pair
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- Actual creation cut and later WETH9 history, with the original L4 premises. -/
structure WethDeploymentTo (checkpoint : BlockChain) where
  pre : BlockChain
  completed : BlockChain
  block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed
  number : block.block.header.number = 4719568
  time : block.block.header.timestamp = 1513077455
  index : Nat
  cut : block.bodyTrace.transactions.TxSplit index
  gasPrice : Nat
  txType : cut.tx.type = .zero gasPrice none
  data : cut.tx.data = Weth9.Creation.code.toList
  value : cut.tx.value = 0
  nonce : cut.tx.nonce = 446
  sender : cut.head.sender = Weth9.Creation.deployer
  funds : (cut.tx.gas * cut.head.effectiveGasPrice).toB256 ≤
    cut.benv.state.bal Weth9.Creation.deployer
  gas : cut.head.intrinsicGas + 720000 ≤ cut.tx.gas
  gasBound : cut.tx.gas < 2 ^ 64
  empty : accountHasCodeOrNonce cut.benv.state Weth9.Creation.weth9Address = false
  history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed checkpoint
  fresh : Weth9.KeysFresh (fun _ => False)
    (Weth9.midTouchedKeysIn Weth9.Creation.weth9Address
      ((MidHistoryTraceIn.tail block cut).append history))

def WethDeploymentTo.trace {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint) :=
  (MidHistoryTraceIn.tail d.block d.cut).append d.history

def WethDeploymentTo.keys {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint) :
    Weth9.Key → Prop :=
  Weth9.midKeyUniverseIn Weth9.Creation.weth9Address d.trace (fun _ => False)

theorem weth_creation_address : weth = Weth9.Creation.weth9Address := by decide +kernel
theorem pair_creation_address : pair = UniswapV2Pair.Creation.pairAddress := by decide +kernel

/-- Backing and the world-sum bound are conclusions of the actual creation history. -/
theorem WethDeploymentTo.foot {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint) :
    SumNof checkpoint.state.bal ∧
    Weth9.FootInv d.keys (checkpoint.state.getStor weth) (checkpoint.state.bal weth) := by
  have created := Weth9.weth9_history_committed_from_creation_block d.block d.number d.time
    d.cut d.txType d.data d.value d.nonce d.sender d.funds d.gas d.gasBound d.empty
  have finished := created.2.2.2.2 d.history d.fresh
  rw [weth_creation_address]
  exact ⟨finished.2.1, finished.2.2.1⟩

/-- The model replay is retained for the remaining allowance provenance proof. -/
theorem WethDeploymentTo.replay {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint) :
    (Weth9.ledger (fun _ => False) Weth9.Creation.deployedStor).run
      (Weth9.replayCalls (Weth9.midCommittedInvocationsIn Weth9.Creation.weth9Address d.trace)) =
    some (Weth9.ledger d.keys (checkpoint.state.getStor weth)) := by
  have created := Weth9.weth9_history_committed_from_creation_block d.block d.number d.time
    d.cut d.txType d.data d.value d.nonce d.sender d.funds d.gas d.gasBound d.empty
  rw [weth_creation_address]
  exact (created.2.2.2.2 d.history d.fresh).2.2.2.1

/-- Every retained frame sees WETH's installed runtime; frames at WETH execute it. -/
theorem WethDeploymentTo.ownCode {checkpoint : BlockChain} (d : WethDeploymentTo checkpoint) :
    ∀ G ∈ d.trace.settledFrames, OwnCodeAtIn HistFork weth Weth9.code G := by
  have created := Weth9.weth9_history_committed_from_creation_block d.block d.number d.time
    d.cut d.txType d.data d.value d.nonce d.sender d.funds d.gas d.gasBound d.empty
  have spawns : OwnSpawnsIn Weth9.Creation.weth9Address Weth9.code := by
    intro R N x pc code _ ordinary chain hat
    obtain ⟨_, reach, ok⟩ := cursor_of_parentPrefix_noStateGas Weth9.cert_check
      pc code ordinary chain
    rcases ok.exec_call_or_staticcall (Cursor.callOnly_of_reach Weth9.cert_callOnly reach) hat
      with call | staticcall
    · exact Or.inl call
    · exact Or.inr (Or.inl staticcall)
  rw [weth_creation_address]
  exact MidHistoryTraceIn.settled_ownCode_of_imageIn Weth9.weth9Sem
    Weth9.Creation.weth9Address d.trace BodyStageCapabilities.historical
    (congrArg some created.1) Weth9.installedCert rfl
    (Weth9.weth9Sem.ne_nil rfl) (Weth9.weth9Sem.not_delegation rfl) spawns

/-- WETH's actual retained children receive WETH as caller, even on the old forks. -/
theorem WethDeploymentTo.children_caller {checkpoint : BlockChain}
    (d : WethDeploymentTo checkpoint) (G : Exec.Frame) (member : G ∈ d.trace.settledFrames)
    (target : G.sevm.currentTarget = weth) :
    ∀ c ∈ Exec.childFrames G.run, c.sevm.caller = G.sevm.currentTarget := by
  have entry := d.ownCode G member
  apply Exec.childFrames_caller_of_callKinds (root := Exec.Frame.rootDeriv G) ?_
    G.run (.refl _)
  intro node x chain hat
  obtain ⟨_, reach, ok⟩ := cursor_of_parentPrefix_noStateGas Weth9.cert_check
    entry.2.1 (entry.2.2.2.2 target) entry.2.2.2.1 chain
  exact ok.exec_call_or_staticcall (Cursor.callOnly_of_reach Weth9.cert_callOnly reach) hat

/-- Actual createPair cut and later Pair history, with no final representation premise.
Only nonce/code collision exclusion and the executed masked factory guard are
needed; CREATE clears the Pair's previous storage. -/
structure PairDeploymentTo (checkpoint : BlockChain) where
  pre : BlockChain
  completed : BlockChain
  block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed
  number : block.block.header.number = 10008355
  time : block.block.header.timestamp = 1588710145
  cut : block.bodyTrace.transactions.TxSplit 38
  gasPrice : Nat
  txType : cut.tx.type = .zero gasPrice (some UniswapV2Pair.Creation.factory)
  data : cut.tx.data = UniswapV2Factory.createPairData
  value : cut.tx.value = 0
  nonce : cut.tx.nonce = 205
  funds : (cut.tx.gas * cut.head.effectiveGasPrice).toB256 ≤ cut.benv.state.bal cut.head.sender
  gas : cut.head.intrinsicGas + 2600000 ≤ cut.tx.gas
  gasBound : cut.tx.gas < 2 ^ 64
  factoryCode : cut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code
  factoryNonce : (cut.benv.state.get UniswapV2Pair.Creation.factory).nonce ≠ UInt64.max
  pairNonce : (cut.benv.state.get UniswapV2Pair.Creation.pairAddress).nonce = 0
  pairCode : (cut.benv.state.get UniswapV2Pair.Creation.pairAddress).code.size = 0
  slot2 : (cut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk2 &&&
    (0xffffffffffffffffffffffffffffffffffffffff : B256) = 0
  history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed checkpoint
  fresh : WriterFreshKeys (fun _ => False)
    (pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
      ((MidHistoryTraceIn.tail block cut).append history))

def PairDeploymentTo.trace {checkpoint : BlockChain} (d : PairDeploymentTo checkpoint) :=
  (MidHistoryTraceIn.tail d.block d.cut).append d.history

/-- After the genuine deployment cut, the Pair's retained mutable children never approve.
The historical replay supplies positional consumption; no endpoint allowance or factory-quiet
premise is used to classify the outgoing selectors. -/
theorem PairDeploymentTo.children_noApprove {checkpoint : BlockChain}
    (d : PairDeploymentTo checkpoint) :
    ∀ G ∈ d.trace.settledFrames, G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ c ∈ Exec.childFrames G.run, c.sevm.isStatic = false →
        Sevm.selector c.sevm ≠ 0x095ea7b3 := by
  have created := UniswapV2Factory.pair_history_initialized_from_createPair_block_noCollision
    d.block d.number d.time d.cut d.txType d.data d.value d.nonce d.funds d.gas d.gasBound
    d.factoryCode d.factoryNonce d.pairNonce d.pairCode d.slot2
  obtain ⟨_, steps, observed, auth, finish, K', replay, _⟩ := created.2.2 d.history d.fresh
  have shaped := replay.children_shape (fun _ _ _ _ consumed => consumed.choose) observed auth
  intro G member target mutableG c child mutable
  rw [pair_creation_address] at target
  have selector := (shaped G member target mutableG c child mutable).2.2
  rcases selector with selector | selector <;> rw [selector] <;> decide

/-- The actual createPair history produces the model and its represented key universe. -/
theorem PairDeploymentTo.represented {checkpoint : BlockChain} (d : PairDeploymentTo checkpoint) :
    ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
      WriterRep K (checkpoint.state.getStor pair) st := by
  have created := UniswapV2Factory.pair_history_initialized_from_createPair_block_noCollision
    d.block d.number d.time d.cut d.txType d.data d.value d.nonce d.funds d.gas d.gasBound
    d.factoryCode d.factoryNonce d.pairNonce d.pairCode d.slot2
  obtain ⟨_, steps, _, _, st, K, _, _, _, _, rep⟩ := created.2.2 d.history d.fresh
  rw [pair_creation_address]
  exact ⟨st, K, rep⟩

/-- Select the model already produced by the actual creation-history theorem.
This fixes one witness for later freshness and liveness statements; no endpoint
representation is supplied by a caller. -/
noncomputable def PairDeploymentTo.model {checkpoint : BlockChain}
    (d : PairDeploymentTo checkpoint) : UniswapV2Pair.State :=
  Classical.choose d.represented

/-- The represented key universe belonging to the same selected model. -/
noncomputable def PairDeploymentTo.keys {checkpoint : BlockChain}
    (d : PairDeploymentTo checkpoint) : WriterKey → Prop :=
  Classical.choose (Classical.choose_spec d.represented)

theorem PairDeploymentTo.rep {checkpoint : BlockChain} (d : PairDeploymentTo checkpoint) :
    WriterRep d.keys (checkpoint.state.getStor pair) d.model :=
  Classical.choose_spec (Classical.choose_spec d.represented)

/-- A fresh observed nonzero balance row must already occur in the historical footprint. -/
theorem ObservedAt.weth_tracked {w : Jaune.State} {K : Weth9.Key → Prop}
    (reads : ObservedAt w) (foot : Weth9.FootInv K (w.getStor weth) (w.bal weth))
    (fresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots K (.bal pair)) :
    K (.bal pair) := by
  by_contra absent
  have zero := foot.support.get_eq_zero fresh absent
  change (w.getStor weth).get (Weth9.balSlot pair) = 0 at zero
  rw [weth_balance_slot, reads.wethBalance] at zero
  exact (by decide +kernel : LiveUsdcWeth9B26213219Data.wethPairBalanceWord ≠ 0) zero

/-- The remaining provenance obligation is about actual retained calls, not an endpoint value. -/
def WethDeploymentTo.NoPairApproval {checkpoint : BlockChain}
    (d : WethDeploymentTo checkpoint) : Prop :=
  ∀ inv ∈ Weth9.midCommittedInvocationsIn Weth9.Creation.weth9Address d.trace,
    inv.sevm.caller = pair → Sevm.selector inv.sevm ≠ 0x095ea7b3

/-- The actual WETH image supplies its child-caller law on any retained suffix.
The segment must consist of original frames from this deployment history. -/
theorem WethDeploymentTo.callerTarget_of_senders_children {checkpoint : BlockChain}
    (d : WethDeploymentTo checkpoint) {start : Benv}
    (segment : MidHistoryTraceIn HistFork mainnetChainConfig start checkpoint)
    (included : segment.settledFrames ⊆ d.trace.settledFrames)
    (senders : segment.NoSenderAt pair)
    (pairChildren : ∀ G ∈ segment.settledFrames,
      G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ c ∈ Exec.childFrames G.run, c.sevm.isStatic = false →
        Sevm.selector c.sevm ≠ 0x095ea7b3) :
    ∀ G ∈ segment.settledFrames,
      CallerTarget pair weth (fun s => s.isStatic = false → Sevm.selector s ≠ 0x095ea7b3)
        G.sevm := by
  have roots := segment.settledRoots_caller_ne_of_noSender senders address_separation.2.2.2.1
  refine segment.settledFrames_callerTarget_of_children ?_ ?_
  · intro R member _ caller
    exact (roots R member caller).elim
  · intro G member target c child _ caller mutable
    rcases target with atPair | atWeth
    · cases static : G.sevm.isStatic with
      | false => exact pairChildren G member atPair static c child mutable
      | true =>
        have inherited := Exec.childFrames_isStatic G.run static c child
        rw [mutable] at inherited
        cases inherited
    · have fromWeth := (d.children_caller G (included member) atWeth c child).trans atWeth
      exact (address_separation.1 (caller.symm.trans fromWeth)).elim

/-- Project retained frame provenance to the actual mutable WETH invocation list. -/
theorem WethDeploymentTo.noPairApproval_of_callerTarget {checkpoint : BlockChain}
    (d : WethDeploymentTo checkpoint)
    (frames : ∀ G ∈ d.trace.settledFrames,
      CallerTarget pair weth (fun s => s.isStatic = false → Sevm.selector s ≠ 0x095ea7b3)
        G.sevm) : d.NoPairApproval := by
  intro inv member caller
  obtain ⟨G, retained, selected⟩ := List.mem_flatMap.mp member
  unfold Weth9.committedFrameInvocations at selected
  split at selected
  · rename_i accepted
    have same := List.mem_singleton.mp selected
    subst inv
    apply frames G retained
    · exact accepted.1.trans weth_creation_address.symm
    · exact caller
    · exact accepted.2.1
  · cases selected

/-- The retained caller forest reduces the allowance obligation to message-root
keylessness and the Pair's direct children. WETH's own children are discharged
from its actual installed runtime, without any endpoint allowance premise. -/
theorem WethDeploymentTo.noPairApproval_of_senders_children {checkpoint : BlockChain}
    (d : WethDeploymentTo checkpoint)
    (senders : d.trace.NoSenderAt pair)
    (pairChildren : ∀ G ∈ d.trace.settledFrames,
      G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ c ∈ Exec.childFrames G.run, c.sevm.isStatic = false →
        Sevm.selector c.sevm ≠ 0x095ea7b3) : d.NoPairApproval := by
  have frames := d.callerTarget_of_senders_children d.trace (fun _ member => member)
    senders pairChildren
  exact d.noPairApproval_of_callerTarget frames

/-- Starting from the constructor's empty mapping, retained call provenance proves zero. -/
theorem WethDeploymentTo.allowance_zero {checkpoint : BlockChain}
    (d : WethDeploymentTo checkpoint) (calls : d.NoPairApproval) :
    ∀ g, d.keys (.allow pair g) →
      (checkpoint.state.getStor weth).get (Weth9.allowSlot pair g) = 0 := by
  have zero := Weth9.replay_allow_zero d.replay
    (h := pair) (fun g => by
      change Weth9.trackedAllow (fun _ => False) Weth9.Creation.deployedStor pair g = 0
      exact Weth9.trackedAllow_of_not (fun impossible => impossible)) calls
  intro g tracked
  have value := zero g
  change Weth9.trackedAllow d.keys (checkpoint.state.getStor weth) pair g = 0 at value
  rwa [Weth9.trackedAllow_self tracked] at value

/-- Creation histories supply representation, backing and world-sum facts.
Zero WETH allowances follow from replay and the retained caller/selector obligation. -/
theorem checkpoint_from_deployment_histories {checkpoint : BlockChain}
    (reads : ObservedAt checkpoint.state) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (calls : wd.NoPairApproval) :
    ∃ (st : UniswapV2Pair.State) (KP : WriterKey → Prop),
      JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys KP st
        checkpoint.state := by
  obtain ⟨st, KP, rep⟩ := pd.represented
  obtain ⟨sumNof, foot⟩ := wd.foot
  exact ⟨st, KP, checkpoint_of_history reads rep foot sumNof
    (reads.weth_tracked foot holderFresh) (wd.allowance_zero calls)⟩

end Blanc.Composition.LiveUsdcWeth9B26213219
