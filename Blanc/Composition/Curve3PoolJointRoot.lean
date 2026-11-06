import Blanc.Composition.Curve3Pool3CrvCheckpoint
import Blanc.Lift.Curve3Pool.Creation.HistoricalTxTrace
import Blanc.Lift.Curve3Pool.HistoryWindow
import Blanc.Lift.Curve3Crv.HistFrameReady
import Blanc.Lift.Curve3Crv.HistWindow
import Blanc.Lift.Curve3Crv.SetMinterTx
import Blanc.ExecutionHistoryInAppend

/-!
# The joint deployment root of the Curve 3pool and 3Crv

`JointDeployment` is one retained `HistFork` mainnet history from 3Crv's actual creation
transaction (block 10,809,467, slot 76) through the pool's (block 10,809,473, slot 53) and the
minter assignment (block 10,809,482, slot 135), each with its successful receipt, running to the end
of the minter block. It takes no contract fact: code, nonce, sender, funds, deployed storage and
the joint checkpoint are theorems.

Besides the blocks, these facts about the history are fields:

* `fresh`: 3Crv's HASH-T (R4's own premise, over the same frames);
* `callbacks`: every child of a pool frame keeps the pool's storage and every coin child keeps 3Crv's
  (`PoolMidEnv.callbacks`, the coin frames' obligation);
* `idEmpty`: the identity precompile's account holds no code just after 3Crv's creation block;
* `idNoFrame`: no CREATE frame of the history lands at the identity precompile's address.

`joint_root` is the headline, stated **right after the minter assignment**: both runtimes are installed
and `JointCheckpoint` holds. `joint_root_replay` says what the checkpoint's states are: the pool's is
the state its model reaches from the constructor's `poolInitState deployTime` over exactly the
committed pool calls between the pool's creation and that cut, and 3Crv's the state its model reaches
over exactly its committed invocations. The minter is not assumed: the model accepts `set_minter` only
from the current minter, so the slot's successful receipt is enough, and nothing runs at 3Crv after it
up to the cut. No frame-level exclusion over the window is assumed: a pool frame in the window is
replayed like any other.
-/

namespace Blanc.Composition.Curve3PoolJointRoot

open Jaune Blanc Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)

local notation "pool" => Lift.Curve3Pool.Creation.poolAddress
local notation "c3Adr" => Lift.Curve3Crv.Creation.tokenAddress

/-- **The joint deployment record.** The three recorded transactions in their retained Muir blocks
with their successful receipts, the configured history joining them, and the facts listed above. -/
structure JointDeployment where
  c3Pre : BlockChain
  c3Completed : BlockChain
  c3Block : ConfiguredBlockTraceIn HistFork mainnetChainConfig c3Pre c3Completed
  c3Number : c3Block.block.header.number = 10809467
  c3Time : c3Block.block.header.timestamp = 1599414946
  c3Entry : Bytes ⊕ Tx
  c3Slot : c3Block.block.txs[76]? = some c3Entry
  c3Decoded : decodeTx c3Block.fork.ruleSet c3Entry = .ok Lift.Curve3Crv.Creation.HistoricalTx.tx
  c3Receipt : Fin 5 × Receipt
  c3Lookup : c3Block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (76 : Nat).toBytes)]? =
    some c3Receipt
  c3Succeeded : c3Receipt.2.succeeded = true
  poolPre : BlockChain
  toPool : ConfiguredHistoryTraceIn HistFork mainnetChainConfig c3Completed poolPre
  poolCompleted : BlockChain
  poolBlock : ConfiguredBlockTraceIn HistFork mainnetChainConfig poolPre poolCompleted
  poolNumber : poolBlock.block.header.number = 10809473
  poolTime : poolBlock.block.header.timestamp = 1599414978
  poolEntry : Bytes ⊕ Tx
  poolSlot : poolBlock.block.txs[53]? = some poolEntry
  poolDecoded : decodeTx poolBlock.fork.ruleSet poolEntry =
    .ok Lift.Curve3Pool.Creation.HistoricalTx.tx
  poolReceipt : Fin 5 × Receipt
  poolLookup : poolBlock.blockOutput.receiptsTrie[BLT.toBytes (.bytes (53 : Nat).toBytes)]? =
    some poolReceipt
  poolSucceeded : poolReceipt.2.succeeded = true
  minterPre : BlockChain
  toMinter : ConfiguredHistoryTraceIn HistFork mainnetChainConfig poolCompleted minterPre
  minterCompleted : BlockChain
  minterBlock : ConfiguredBlockTraceIn HistFork mainnetChainConfig minterPre minterCompleted
  minterNumber : minterBlock.block.header.number = 10809482
  minterTime : minterBlock.block.header.timestamp = 1599415164
  minterEntry : Bytes ⊕ Tx
  minterSlot : minterBlock.block.txs[135]? = some minterEntry
  minterDecoded : decodeTx minterBlock.fork.ruleSet minterEntry =
    .ok Lift.Curve3Crv.SetMinter.tx
  minterReceipt : Fin 5 × Receipt
  minterLookup : minterBlock.blockOutput.receiptsTrie[BLT.toBytes (.bytes (135 : Nat).toBytes)]? =
    some minterReceipt
  minterSucceeded : minterReceipt.2.succeeded = true
  fresh : Lift.Curve3Crv.FreshKeys (fun _ => False)
    (Lift.Curve3Crv.midTouchedKeysIn c3Adr
      ((MidHistoryTraceIn.tail c3Block (c3Block.bodyTrace.txSplitOfSlot c3Slot c3Decoded)).append
        (((toPool.step poolBlock).append toMinter).step minterBlock)))
  callbacks : (((MidHistoryTraceIn.tail poolBlock
      (poolBlock.bodyTrace.txSplitOfSlot poolSlot poolDecoded)).append toMinter).step
      minterBlock).FrameAdmitted pool (Exec.derivEntry fun D =>
        Lift.Curve3Pool.PoolCallsKeep D ∧ Lift.Curve3Pool.PoolCoinCallsKeepToken D)
  idEmpty : c3Completed.state.getCode 4 = ByteArray.empty
  idNoFrame : ∀ root ∈ (((toPool.step poolBlock).append toMinter).step minterBlock).rawFrames,
    root.sevm.codeAddress = none → root.sevm.currentTarget ≠ 4

namespace JointDeployment

variable (j : JointDeployment)

/-- The whole history after 3Crv's creation block, as R4's premise. -/
noncomputable def history :
    ConfiguredHistoryTraceIn HistFork mainnetChainConfig j.c3Completed j.minterCompleted :=
  ((j.toPool.step j.poolBlock).append j.toMinter).step j.minterBlock

/-- 3Crv's deployment record over the whole history (R4). -/
noncomputable def c3 : Lift.Curve3Crv.C3crvDeploymentTo j.minterCompleted where
  pre := j.c3Pre
  completed := j.c3Completed
  block := j.c3Block
  number := j.c3Number
  time := j.c3Time
  entry := j.c3Entry
  slot := j.c3Slot
  decoded := j.c3Decoded
  receipt := j.c3Receipt
  lookup := j.c3Lookup
  succeeded := j.c3Succeeded
  history := j.history
  fresh := j.fresh

/-- The pool's creation cut. -/
noncomputable def poolCut : j.poolBlock.bodyTrace.transactions.TxSplit 53 :=
  j.poolBlock.bodyTrace.txSplitOfSlot j.poolSlot j.poolDecoded

/-- The minter assignment's cut. -/
noncomputable def minterCut : j.minterBlock.bodyTrace.transactions.TxSplit 135 :=
  j.minterBlock.bodyTrace.txSplitOfSlot j.minterSlot j.minterDecoded

/-- From just after the pool's creation to the block before the minter block. -/
noncomputable def poolMid :
    MidHistoryTraceIn HistFork mainnetChainConfig j.poolCut.afterBenv j.minterPre :=
  (MidHistoryTraceIn.tail j.poolBlock j.poolCut).append j.toMinter

/-- From just after the pool's creation to the end of the minter block. -/
noncomputable def span :
    MidHistoryTraceIn HistFork mainnetChainConfig j.poolCut.afterBenv j.minterCompleted :=
  j.poolMid.step j.minterBlock

/-- From just after 3Crv's creation to the block before the minter block. -/
noncomputable def c3Mid :
    MidHistoryTraceIn HistFork mainnetChainConfig j.c3.cut.afterBenv j.minterPre :=
  (MidHistoryTraceIn.tail j.c3Block j.c3.cut).append ((j.toPool.step j.poolBlock).append j.toMinter)

/-- The world right after the minter assignment. -/
noncomputable def cutState : Jaune.State := j.minterCut.afterBenv.state

/-- The committed pool calls of the window from the pool's creation to the minter assignment. -/
noncomputable def poolFrames : List Exec.Frame :=
  Lift.Curve3Pool.committedPoolFramesWindow pool j.poolMid j.minterBlock j.minterCut

/-- 3Crv's committed writer invocations from its creation through the minter assignment. -/
noncomputable def c3Invocations : List Lift.Curve3Crv.WriterInvocation :=
  Lift.Curve3Crv.windowCommittedInvocationsIn c3Adr j.c3Mid j.minterBlock j.minterCut

/-- The 3Crv keys tracked at the cut: those its committed invocations touch. -/
noncomputable def c3Keys : Lift.Curve3Crv.Key → Prop :=
  Lift.Curve3Crv.Key.extend (fun _ => False) (Lift.Curve3Crv.invocationKeys j.c3Invocations)

end JointDeployment

/-! ## The pool's environment, from the history -/

/-- The recorded coins and token are no precompile of any historical fork. -/
theorem parties_not_precompile {f : Fork} (hf : HistFork f) :
    (∀ k : Fin 3, ¬ (Fork.ruleSet f).isPrecomp
      (Lift.Curve3Pool.adrOf (Lift.Curve3Pool.Creation.coinsN.get k))) ∧
      ¬ (Fork.ruleSet f).isPrecomp (Lift.Curve3Pool.adrOf Lift.Curve3Pool.Creation.tokenN) := by
  revert hf
  cases f <;> decide +kernel

/-- The history ends before Cancun, so every block's fork is pre-Cancun. -/
theorem JointDeployment.forks (j : JointDeployment) : j.history.ForksSatisfy PreCancun := by
  have last : j.minterCompleted.blocks.getLast? = some j.minterBlock.block :=
    (congrArg (fun chain : BlockChain => chain.blocks.getLast?) j.minterBlock.postEq).trans
      (appendBlock_getLast? _ _)
  exact j.history.forksPreCancun_of_mainnet_tip last (by rw [j.minterTime]; decide)

/-- **The pool's history environment over the span**: `parties`, `sysNe` and `idNoAuthority` are
theorems here, the last two because the history ends before Cancun. -/
theorem JointDeployment.poolEnv (j : JointDeployment) :
    Lift.Curve3Pool.PoolMidEnv j.history j.span pool Lift.Curve3Pool.Creation.coinsN
      Lift.Curve3Pool.Creation.tokenN where
  subset := by
    intro root member
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _
        (MidHistoryTraceIn.rawFrames_subset_full j.toPool j.poolBlock j.poolCut j.toMinter member)
    · exact List.mem_append_right _ member
  callbacks := j.callbacks
  parties := fun root member _ =>
    parties_not_precompile (j.span.rootEntryIn root member).2
  idEmpty := j.idEmpty
  idNoAuthority := j.history.pragueNoAuthorityAt_of_prePrague
    (j.forks.mono fun _ hf => hf.toPrePrague) 4
  idNoFrame := j.idNoFrame
  sysNe := fun root member => by
    rw [j.history.systemRawFrames_nil_of_preCancun j.forks] at member
    cases member

/-! ## 3Crv's minter -/

section Minter

open Lift.Curve3Crv

variable {A : Sevm → Devm → Adr → B256 → Prop}

/-- A run over a concatenation passes through a state after the first part. -/
theorem InvRunBy.of_append :
    ∀ {s s' : Blanc.Curve3Crv.State} {xs ys : List WriterInvocation},
      InvRunBy A s (xs ++ ys) s' → ∃ m, InvRunBy A s xs m ∧ InvRunBy A m ys s'
  | s, s', [], ys, h => ⟨s, rfl, h⟩
  | s, s', inv :: rest, ys, h => by
      obtain ⟨o, step, tail⟩ := h
      obtain ⟨m, first, second⟩ := InvRunBy.of_append tail
      exact ⟨m, ⟨o, step, first⟩, second⟩

/-- A run over frames ending with the frame writing `set_minter` to `a`, followed only by frames
that invoke nothing, ends at minter `a`. -/
theorem minter_of_split {s s' : Blanc.Curve3Crv.State} {before after : List Exec.Frame}
    {frame : Exec.Frame}
    (run : InvRunBy A s ((before ++ frame :: after).flatMap (committedFrameInvocations c3Adr)) s')
    (target : frame.sevm.currentTarget = c3Adr)
    (data : frame.sevm.data = SetMinter.callData)
    (silent : ∀ f ∈ after, committedFrameInvocations c3Adr f = []) :
    s'.minter = SetMinter.poolWord.toAdr := by
  have call := SetMinter.decodeCall_of_data data
  have selected : committedFrameInvocations c3Adr frame = [frameInvocation frame] := by
    unfold committedFrameInvocations
    rw [ite_eq_left ⟨target, by rw [call]; trivial⟩]
  rw [List.flatMap_append, List.flatMap_cons, selected, List.flatMap_eq_nil_iff.mpr silent,
    List.append_nil] at run
  obtain ⟨_, -, o, ⟨accepted, -⟩, tail⟩ := InvRunBy.of_append run
  change Blanc.Curve3Crv.step _ (decodeCall frame.sevm) _ = _ at accepted
  rw [call] at accepted
  rw [InvRunBy] at tail
  rw [tail]
  exact SetMinter.minter_of_setMinter accepted

end Minter

/-- **The minter assignment landed**: the model state 3Crv's replay reaches right after the minter
assignment has the pool as minter. -/
theorem c3_minter (j : JointDeployment) {s : Blanc.Curve3Crv.State}
    (run : Lift.Curve3Crv.InvRunBy Lift.Curve3Crv.OwnerAnswerH
      (Lift.Curve3Crv.Creation.curveDeployedState Lift.Curve3Crv.Creation.deployer)
      j.c3Invocations s) :
    s.minter = pool := by
  obtain ⟨index, sameTx⟩ :=
    j.minterBlock.bodyTrace.txSplitOfSlot_spec j.minterSlot j.minterDecoded
  have lookup : j.minterBlock.blockOutput.receiptsTrie[BLT.toBytes
      (.bytes j.minterCut.index.toBytes)]? = some j.minterReceipt := by
    change j.minterBlock.blockOutput.receiptsTrie[BLT.toBytes
      (.bytes (j.minterBlock.bodyTrace.txSplitOfSlot j.minterSlot
        j.minterDecoded).index.toBytes)]? = _
    rw [index]
    exact j.minterLookup
  obtain ⟨forkEq, hfork, -, -⟩ := j.minterBlock.txSplit_muir (by
    rw [j.minterNumber, j.minterTime]; decide +kernel) j.minterCut
  have success := j.minterBlock.txSplit_error_eq_none_of_receipt j.minterCut
    (by rw [forkEq]; rfl) lookup j.minterSucceeded
  have sameTx' : j.minterCut.tx = Lift.Curve3Crv.SetMinter.tx := sameTx
  have root : ∃ frame, j.minterCut.head.settledFrames = frame :: Exec.descendantFrames frame.run ∧
      frame.sevm.currentTarget = c3Adr ∧ frame.sevm.data = Lift.Curve3Crv.SetMinter.callData := by
    generalize j.minterCut = cut at sameTx' hfork success ⊢
    obtain ⟨_, tx', _, _, _, _, _, _, head, _, _, _⟩ := cut
    subst sameTx'
    exact Lift.Curve3Crv.SetMinter.root_of_success head hfork success
  obtain ⟨frame, heads, target, data⟩ := root
  obtain ⟨hcode, -, hinv⟩ := j.c3.created
  have installed : some (j.c3.cut.afterBenv.state.getCode c3Adr).toList =
      Lift.Curve3Crv.c3crvSem.image := by
    rw [hcode]
    rfl
  have ready := Lift.Curve3Crv.c3crv_mid_readyH j.c3.trace installed hinv j.fresh
  have inTrace : ∀ f ∈ j.minterCut.head.settledFrames, f ∈ j.c3.trace.settledFrames := by
    intro f member
    change f ∈ j.c3Mid.settledFrames ++ j.minterBlock.settledFrames
    rw [j.minterBlock.settledFrames_throughCut j.minterCut]
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ member))
  have readyFrame := ready frame (inTrace frame (by rw [heads]; exact List.mem_cons_self))
  have silent : ∀ f ∈ Exec.descendantFrames frame.run,
      Lift.Curve3Crv.committedFrameInvocations c3Adr f = [] := fun f member =>
    Lift.Curve3Crv.committedFrameInvocations_nil_of_static
      (ready f (inTrace f (by rw [heads]; exact List.mem_cons_of_mem _ member)))
      (Lift.Curve3Crv.c3crv_descendants_staticH readyFrame target f member)
  have run' : Lift.Curve3Crv.InvRunBy Lift.Curve3Crv.OwnerAnswerH
      (Lift.Curve3Crv.Creation.curveDeployedState Lift.Curve3Crv.Creation.deployer)
      ((j.c3Mid.settledFrames ++ (j.minterBlock.bodyTrace.beacon.settledFrames ++
        j.minterBlock.bodyTrace.history.settledFrames ++ j.minterCut.before.settledFrames) ++
          frame :: Exec.descendantFrames frame.run).flatMap
        (Lift.Curve3Crv.committedFrameInvocations c3Adr)) s := by
    have shape : j.c3Invocations = (j.c3Mid.settledFrames ++
        (j.minterBlock.bodyTrace.beacon.settledFrames ++
          j.minterBlock.bodyTrace.history.settledFrames ++ j.minterCut.before.settledFrames ++
            j.minterCut.head.settledFrames)).flatMap
        (Lift.Curve3Crv.committedFrameInvocations c3Adr) := rfl
    rw [shape, heads, ← List.append_assoc] at run
    exact run
  have word : Lift.Curve3Crv.SetMinter.poolWord.toAdr = pool := by decide +kernel
  rw [← word]
  exact minter_of_split run' target data silent

/-! ## The headline -/

/-- **The checkpoint is the replay.** Right after the minter assignment both runtimes are installed
and `JointCheckpoint` holds of two states: the pool's is the state its model reaches from the
constructor's `poolInitState deployTime` over exactly the committed pool calls between the pool's
creation and the cut, each authentic and entered at a checkpoint of the state its prefix reaches; and
3Crv's is the state its model reaches over exactly its committed invocations from its deployed state. -/
theorem joint_root_replay (j : JointDeployment) :
    some (j.cutState.getCode pool).toList = Lift.Curve3Pool.poolSem.image ∧
    some (j.cutState.getCode c3Adr).toList = Lift.Curve3Crv.c3crvSem.image ∧
    ∃ (invs : List Lift.Curve3Pool.PoolInvocation) (ps : Lift.Curve3Pool.State)
      (cs : Blanc.Curve3Crv.State),
      invs.flatMap (fun i => Lift.Curve3Pool.poolSubtreeFrames pool i.frame) = j.poolFrames ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      Lift.Curve3Pool.PoolEntries
        (Lift.Curve3Pool.Creation.poolInitState Lift.Curve3Pool.Creation.deployTime.toNat) invs ∧
      Lift.Curve3Pool.PoolRun
        (Lift.Curve3Pool.Creation.poolInitState Lift.Curve3Pool.Creation.deployTime.toNat) invs ps ∧
      Lift.Curve3Pool.runPool
        (Lift.Curve3Pool.Creation.poolInitState Lift.Curve3Pool.Creation.deployTime.toNat) invs =
          some ps ∧
      Lift.Curve3Crv.InvRunBy Lift.Curve3Crv.OwnerAnswerH
        (Lift.Curve3Crv.Creation.curveDeployedState Lift.Curve3Crv.Creation.deployer)
        j.c3Invocations cs ∧
      JointCheckpoint pool c3Adr ps cs j.c3Keys j.cutState := by
  -- the pool
  obtain ⟨index, sameTx⟩ := j.poolBlock.bodyTrace.txSplitOfSlot_spec j.poolSlot j.poolDecoded
  have lookup : j.poolBlock.blockOutput.receiptsTrie[BLT.toBytes
      (.bytes j.poolCut.index.toBytes)]? = some j.poolReceipt := by
    change j.poolBlock.blockOutput.receiptsTrie[BLT.toBytes
      (.bytes (j.poolBlock.bodyTrace.txSplitOfSlot j.poolSlot j.poolDecoded).index.toBytes)]? = _
    rw [index]
    exact j.poolLookup
  obtain ⟨hcode, hstor⟩ := Lift.Curve3Pool.Creation.HistoricalTx.actual_block_cut j.poolBlock
    j.poolNumber j.poolTime j.poolCut sameTx lookup j.poolSucceeded
  have poolInstalled : some (j.poolCut.afterBenv.state.getCode pool).toList =
      Lift.Curve3Pool.poolSem.image := by
    change some (j.poolCut.txState.getCode pool).toList = _
    rw [hcode]
    rfl
  have poolInitial : Lift.Curve3Pool.Checkpoint (j.poolCut.afterBenv.state.getStor pool)
      (Lift.Curve3Pool.Creation.poolInitState Lift.Curve3Pool.Creation.deployTime.toNat) := by
    change Lift.Curve3Pool.Checkpoint (j.poolCut.txState.getStor pool) _
    rw [hstor]
    exact Lift.Curve3Pool.Creation.deployedStor_checkpoint (by decide)
  obtain ⟨poolCode, invs, obs, auth, entries, ps, run, fold, poolCk, -, htoken⟩ :=
    Lift.Curve3Pool.pool_window_history j.poolMid j.minterBlock j.minterCut poolInstalled poolInitial
      j.poolEnv
  -- 3Crv
  obtain ⟨c3Hcode, -, hinv⟩ := j.c3.created
  have c3Installed : some (j.c3.cut.afterBenv.state.getCode c3Adr).toList =
      Lift.Curve3Crv.c3crvSem.image := by
    rw [c3Hcode]
    rfl
  obtain ⟨c3Code, cs, c3Run, c3Final⟩ := Lift.Curve3Crv.c3crv_window_framesHist j.c3Mid j.minterBlock
    j.minterCut c3Installed hinv j.fresh
  exact ⟨poolCode, c3Code, invs, ps, cs, obs, auth, entries, run, fold, c3Run,
    { poolCk := poolCk
      c3 := c3Final
      tokenIs := by rw [htoken]; decide
      minterIs := c3_minter j c3Run
      apart := by decide }⟩

/-- **The joint deployment root.** Over one configured history from 3Crv's actual creation through
the pool's and the minter assignment, right after the assignment both runtimes are installed and
`JointCheckpoint` holds: the pool's storage abstracts a replayed state whose coins and token are the
constructor's (`joint_root_replay` says which), and 3Crv's the state its model reaches over exactly
its committed invocations from its deployed state, with the pool as minter. -/
theorem joint_root (j : JointDeployment) :
    some (j.cutState.getCode pool).toList = Lift.Curve3Pool.poolSem.image ∧
    some (j.cutState.getCode c3Adr).toList = Lift.Curve3Crv.c3crvSem.image ∧
    ∃ ps cs, Lift.Curve3Crv.InvRunBy Lift.Curve3Crv.OwnerAnswerH
        (Lift.Curve3Crv.Creation.curveDeployedState Lift.Curve3Crv.Creation.deployer)
        j.c3Invocations cs ∧
      JointCheckpoint pool c3Adr ps cs j.c3Keys j.cutState := by
  obtain ⟨poolCode, c3Code, _, ps, cs, -, -, -, -, -, run, joint⟩ := joint_root_replay j
  exact ⟨poolCode, c3Code, ps, cs, run, joint⟩

end Blanc.Composition.Curve3PoolJointRoot
