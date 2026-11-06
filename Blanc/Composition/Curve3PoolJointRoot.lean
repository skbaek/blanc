import Blanc.Composition.Curve3Pool3CrvCheckpoint
import Blanc.Lift.Curve3Pool.Creation.HistoricalTxTrace
import Blanc.Lift.Curve3Pool.Ladder
import Blanc.Lift.Curve3Crv.SetMinterTx
import Blanc.ExecutionHistoryInAppend
import Blanc.ExecutionHistoryCellProvenanceFrom
import Blanc.ExecutionNoninterference

/-!
# The joint deployment root of the Curve 3pool and 3Crv

`JointDeployment` is one retained `HistFork` mainnet history from 3Crv's actual creation
transaction (block 10,809,467, slot 76) through the pool's (block 10,809,473, slot 53) and the
minter assignment (block 10,809,482, slot 135), each with its successful receipt, ending at the end
of the minter block. It takes no contract fact: code, nonce, sender, funds, deployed storage and
the joint checkpoint are theorems.

Besides the blocks, two trace-local facts about the history are fields:

* `fresh`: 3Crv's HASH-T (R4's own premise, over the same frames);
* `quiet`: no raw frame from just after the pool's creation to the end of the minter block runs at
  the pool or is called by it. The pool's refinement is stated over covered forks only, so a frame
  at the pool under Muir Glacier could not be replayed here; `quiet` is what makes the checkpoint's
  pool state the constructor's `poolInitState` rather than a replayed one.

`joint_root` is the headline: at the end of the minter block both runtimes are installed and
`JointCheckpoint` holds, with the pool at `poolInitState deployTime` and 3Crv at the state its model
reaches over exactly its committed invocations. The minter is not assumed: the model accepts
`set_minter` only from the current minter, so the slot's successful receipt is enough, and only the
pool could replace the minter again.
-/

namespace Blanc.Composition.Curve3PoolJointRoot

open Jaune Blanc Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)

local notation "pool" => Lift.Curve3Pool.Creation.poolAddress
local notation "c3Adr" => Lift.Curve3Crv.Creation.tokenAddress

/-- **The joint deployment record.** The three recorded transactions in their retained Muir blocks
with their successful receipts, the configured history joining them, and the two trace-local
facts. -/
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
  quiet : ∀ root ∈ (((MidHistoryTraceIn.tail poolBlock
      (poolBlock.bodyTrace.txSplitOfSlot poolSlot poolDecoded)).append toMinter).step
      minterBlock).rawFrames,
    root.sevm.currentTarget ≠ pool ∧ root.sevm.caller ≠ pool

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

/-- From just after the pool's creation to the end of the minter block. -/
noncomputable def span :
    MidHistoryTraceIn HistFork mainnetChainConfig j.poolCut.afterBenv j.minterCompleted :=
  ((MidHistoryTraceIn.tail j.poolBlock j.poolCut).append j.toMinter).step j.minterBlock

end JointDeployment

/-! ## An account no frame enters -/

section Quiet

variable {F : Fork → Prop} {cfg : ChainConfig} {wa : Adr} {C : ByteArray}

/-- A cell whose provenance runs over nodes none of which owns the account keeps its value. -/
theorem cell_eq_of_noTarget {k init v : B256} {nodes : List Exec.Deriv}
    (h : CellProv wa k init nodes v) (quiet : ∀ m ∈ nodes, m.sevm.currentTarget ≠ wa) :
    v = init := by
  rcases h with same | ⟨b₁, b₂, m, w, split, found, owner, -, -⟩
  · exact same
  · have member : m ∈ nodes := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨-, hm⟩ := successfulSstore?_node_owner found
    exact absurd (hm.symm.trans owner) (quiet m member)

/-- **A mid history no frame enters at an account keeps its code and every storage word.** The code
must be nonempty and undesignated, so settlement's sweep and delegation leave it alone. -/
theorem MidHistoryTraceIn.keeps_of_quiet {start : Benv} {future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start future) (capabilities : BodyStageCapabilities F)
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    (installed : start.state.getCode wa = C)
    (quiet : ∀ root ∈ mid.rawFrames, root.sevm.currentTarget ≠ wa) :
    future.state.getCode wa = C ∧
      ∀ k, (future.state.getStor wa).get k = (start.state.getStor wa).get k := by
  induction mid with
  | @tail boundary completed i block cut =>
    have hsgBody : (initBenv block.fork boundary block.block.header).stat.rules.stateGas = none :=
      capabilities.stateGas_none block.forkIn
    have hsg : cut.afterBenv.stat.rules.stateGas = none := by
      rw [block.txSplit_stat cut]
      exact hsgBody
    have nodesA : ∀ m ∈ cut.after.rawNodes, m.sevm.currentTarget ≠ wa := by
      intro m hm
      obtain ⟨R, hR, chain⟩ := (cut.after.mem_rawNodes_iff_rawFrame_parentPrefix m).mp hm
      rw [Exec.Deriv.ParentPrefix.sevm_eq chain]
      exact quiet R (List.mem_append_left _ hR)
    have nodesR : ∀ m ∈ block.bodyTrace.requests.rawNodes, m.sevm.currentTarget ≠ wa := by
      intro m hm
      obtain ⟨R, hR, chain⟩ :=
        (block.bodyTrace.requests.mem_rawNodes_iff_rawFrame_parentPrefix m).mp hm
      rw [Exec.Deriv.ParentPrefix.sevm_eq chain]
      exact quiet R (List.mem_append_right _ hR)
    have step : ∀ k, (block.bodyState.getStor wa).get k = (cut.afterBenv.state.getStor wa).get k ∧
        block.bodyState.getCode wa = C := by
      intro k
      obtain ⟨cellA, codeA⟩ := cut.after.cellProv_post hCdel k hsg installed hCne
        (block.txSplit_notCreated cut wa)
        (cut.after.safeRawFrames_of_rawNodes fun m hm target => absurd target (nodesA m hm))
      obtain ⟨cellR, codeR⟩ := block.bodyTrace.requests_cellProv_post hCdel k hsgBody hCne
        AdrSet.not_mem_empty codeA fun m hm target => absurd target (nodesR m hm)
      exact ⟨(cell_eq_of_noTarget cellR nodesR).trans (cell_eq_of_noTarget cellA nodesA), codeR⟩
    rw [congrArg BlockChain.state block.postEq]
    exact ⟨(step 0).2, fun k => (step k).1⟩
  | step prior block ih =>
    obtain ⟨code, stor⟩ := ih installed fun root member => quiet root (List.mem_append_left _ member)
    have nodes : ∀ m ∈ block.rawNodes, m.sevm.currentTarget ≠ wa := by
      intro m hm
      obtain ⟨R, hR, chain⟩ := (block.mem_rawNodes_iff_rawFrame_parentPrefix m).mp hm
      rw [Exec.Deriv.ParentPrefix.sevm_eq chain]
      exact quiet R (List.mem_append_right _ hR)
    have step : ∀ k, _ := fun k => block.cellProv_post hCdel hCne capabilities k code
      (block.safeRawFrames_of_rawNodes fun m hm target => absurd target (nodes m hm))
    exact ⟨(step 0).2, fun k => (cell_eq_of_noTarget (step k).1 nodes).trans (stor k)⟩

end Quiet

/-- The pool's checkpoint predicate reads storage words only. -/
theorem checkpoint_of_get {stor stor' : Stor} {s : Lift.Curve3Pool.State}
    (h : Lift.Curve3Pool.Checkpoint stor s) (same : ∀ k, stor'.get k = stor.get k) :
    Lift.Curve3Pool.Checkpoint stor' s := by
  obtain ⟨abs, unlocked, addr⟩ := h
  obtain ⟨c, b, fee, aFee, o, t, iA, fA, iT, fT, d, tr, fFee, fAFee, fO, kl, kd⟩ := abs
  exact
    { abs :=
      { coins := fun i => by rw [same]; exact c i
        balances := fun i => by rw [same]; exact b i
        fee := by rw [same]; exact fee
        adminFee := by rw [same]; exact aFee
        owner := by rw [same]; exact o
        token := by rw [same]; exact t
        initialA := by rw [same]; exact iA
        futureA := by rw [same]; exact fA
        initialATime := by rw [same]; exact iT
        futureATime := by rw [same]; exact fT
        adminActionsDeadline := by rw [same]; exact d
        transferOwnershipDeadline := by rw [same]; exact tr
        futureFee := by rw [same]; exact fFee
        futureAdminFee := by rw [same]; exact fAFee
        futureOwner := by rw [same]; exact fO
        isKilled := by rw [same]; exact kl
        killDeadline := by rw [same]; exact kd }
      unlocked := by rw [same]; exact unlocked
      addr := addr }

/-- **The pool at the end of the minter block is exactly as its constructor left it.** -/
theorem pool_installed (j : JointDeployment) :
    some (j.minterCompleted.state.getCode pool).toList = Lift.Curve3Pool.poolSem.image ∧
      ∀ k, (j.minterCompleted.state.getStor pool).get k =
        (Lift.Curve3Pool.Creation.deployedStor Lift.Curve3Pool.Creation.deployTime).get k := by
  obtain ⟨index, sameTx⟩ := j.poolBlock.bodyTrace.txSplitOfSlot_spec j.poolSlot j.poolDecoded
  have lookup : j.poolBlock.blockOutput.receiptsTrie[BLT.toBytes
      (.bytes j.poolCut.index.toBytes)]? = some j.poolReceipt := by
    change j.poolBlock.blockOutput.receiptsTrie[BLT.toBytes
      (.bytes (j.poolBlock.bodyTrace.txSplitOfSlot j.poolSlot j.poolDecoded).index.toBytes)]? = _
    rw [index]
    exact j.poolLookup
  obtain ⟨hcode, hstor⟩ := Lift.Curve3Pool.Creation.HistoricalTx.actual_block_cut j.poolBlock
    j.poolNumber j.poolTime j.poolCut sameTx lookup j.poolSucceeded
  have installed : j.poolCut.afterBenv.state.getCode pool = Lift.Curve3Pool.code :=
    Lift.Curve3Pool.code_eq_of_toList (congrArg some hcode)
  obtain ⟨code, stor⟩ := MidHistoryTraceIn.keeps_of_quiet j.span BodyStageCapabilities.historical
    (Lift.Curve3Pool.poolSem.not_delegation rfl) Lift.Curve3Pool.Creation.HistoricalTx.runtime_ne_nil
    installed fun root member => (j.quiet root member).1
  refine ⟨by rw [code]; rfl, fun k => ?_⟩
  rw [stor k]
  exact congrArg (fun st : Stor => st.get k) hstor

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

/-- Only the minter replaces the minter: invocations none of which the minter calls keep it. -/
theorem InvRunBy.minter_keep {a : Adr} :
    ∀ {s s' : Blanc.Curve3Crv.State} {ys : List WriterInvocation},
      InvRunBy A s ys s' → s.minter = a → (∀ inv ∈ ys, inv.sevm.caller ≠ a) → s'.minter = a
  | s, s', [], h, hm, _ => by
      rw [InvRunBy] at h
      rw [h]
      exact hm
  | s, s', inv :: rest, h, hm, callers => by
      obtain ⟨o, ⟨accepted, -⟩, tail⟩ := h
      refine InvRunBy.minter_keep tail ?_ fun i member =>
        callers i (List.mem_cons_of_mem _ member)
      by_contra moved
      have hne : o.1.minter ≠ s.minter := by rw [hm]; exact moved
      have sender := Blanc.Curve3Crv.minter_change_by_minter accepted hne
      exact callers inv List.mem_cons_self (by rw [← hm]; exact sender)

/-- A run over the settled frames of a list split at `frame`, with the frame writing `set_minter`
to `a`, ends at minter `a` when no later invocation is called by `a`. -/
theorem minter_of_split {s s' : Blanc.Curve3Crv.State} {before after : List Exec.Frame}
    {frame : Exec.Frame}
    (run : InvRunBy A s ((before ++ frame :: after).flatMap (committedFrameInvocations c3Adr)) s')
    (target : frame.sevm.currentTarget = c3Adr)
    (data : frame.sevm.data = SetMinter.callData)
    (callers : ∀ f ∈ after, f.sevm.caller ≠ SetMinter.poolWord.toAdr) :
    s'.minter = SetMinter.poolWord.toAdr := by
  have call := SetMinter.decodeCall_of_data data
  have selected : committedFrameInvocations c3Adr frame = [frameInvocation frame] := by
    unfold committedFrameInvocations
    rw [ite_eq_left ⟨target, by rw [call]; trivial⟩]
  rw [List.flatMap_append, List.flatMap_cons, selected, List.singleton_append] at run
  obtain ⟨_, -, o, ⟨accepted, -⟩, tail⟩ := InvRunBy.of_append run
  change Blanc.Curve3Crv.step _ (decodeCall frame.sevm) _ = _ at accepted
  rw [call] at accepted
  refine InvRunBy.minter_keep tail (SetMinter.minter_of_setMinter accepted) fun inv member => ?_
  obtain ⟨f, hf, selected⟩ := List.mem_flatMap.mp member
  unfold committedFrameInvocations at selected
  split at selected
  · rw [List.mem_singleton.mp selected]
    exact callers f hf
  · cases selected

end Minter

/-- **The minter assignment landed**: the model state 3Crv's replay reaches at the end of the minter
block has the pool as minter. -/
theorem c3_minter (j : JointDeployment) {s : Blanc.Curve3Crv.State}
    (run : Lift.Curve3Crv.InvRunBy Lift.Curve3Crv.OwnerAnswerH
      (Lift.Curve3Crv.Creation.curveDeployedState Lift.Curve3Crv.Creation.deployer)
      j.c3.invocations s) :
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
  have root : ∃ frame ∈ j.minterCut.head.settledFrames,
      frame.sevm.currentTarget = c3Adr ∧ frame.sevm.data = Lift.Curve3Crv.SetMinter.callData := by
    generalize j.minterCut = cut at sameTx' hfork success ⊢
    obtain ⟨_, tx', _, _, _, _, _, _, head, _, _, _⟩ := cut
    subst sameTx'
    exact Lift.Curve3Crv.SetMinter.root_of_success head hfork success
  obtain ⟨frame, member, target, data⟩ := root
  have inBlock : frame ∈ j.minterBlock.settledFrames := by
    rw [j.minterBlock.settledFrames_txSplit j.minterCut]
    simp only [List.mem_append]
    exact .inl (.inr member)
  obtain ⟨before, after, split⟩ := List.append_of_mem inBlock
  have frames : j.c3.trace.settledFrames =
      ((MidHistoryTraceIn.tail j.c3Block
        (j.c3Block.bodyTrace.txSplitOfSlot j.c3Slot j.c3Decoded)).append
        ((j.toPool.step j.poolBlock).append j.toMinter)).settledFrames ++
        j.minterBlock.settledFrames := rfl
  have run' : Lift.Curve3Crv.InvRunBy Lift.Curve3Crv.OwnerAnswerH
      (Lift.Curve3Crv.Creation.curveDeployedState Lift.Curve3Crv.Creation.deployer)
      ((((MidHistoryTraceIn.tail j.c3Block
        (j.c3Block.bodyTrace.txSplitOfSlot j.c3Slot j.c3Decoded)).append
        ((j.toPool.step j.poolBlock).append j.toMinter)).settledFrames ++ before ++
          frame :: after).flatMap
        (Lift.Curve3Crv.committedFrameInvocations c3Adr)) s := by
    have shape : j.c3.invocations = (j.c3.trace.settledFrames).flatMap
        (Lift.Curve3Crv.committedFrameInvocations c3Adr) := rfl
    rw [shape, frames, split, ← List.append_assoc] at run
    exact run
  have callers : ∀ f ∈ after, f.sevm.caller ≠ Lift.Curve3Crv.SetMinter.poolWord.toAdr := by
    intro f hf
    have settled : f ∈ j.span.settledFrames := by
      change f ∈ _ ++ j.minterBlock.settledFrames
      rw [split]
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ hf))
    exact (j.quiet _ (j.span.mem_rawFrames_of_mem_settledFrames f settled)).2
  have word : Lift.Curve3Crv.SetMinter.poolWord.toAdr = pool := by decide +kernel
  rw [← word]
  exact minter_of_split run' target data callers

/-! ## The headline -/

/-- **The joint deployment root.** Over one configured history from 3Crv's actual creation through
the pool's and the minter assignment, at the end of the minter block both runtimes are installed
and `JointCheckpoint` holds: the pool's storage abstracts the constructor's state
`poolInitState deployTime`, and 3Crv's abstracts the state its model reaches over exactly its
committed invocations from its deployed state, with the pool as minter. -/
theorem joint_root (j : JointDeployment) :
    some (j.minterCompleted.state.getCode pool).toList = Lift.Curve3Pool.poolSem.image ∧
    some (j.minterCompleted.state.getCode c3Adr).toList = Lift.Curve3Crv.c3crvSem.image ∧
    ∃ cs, Lift.Curve3Crv.InvRunBy Lift.Curve3Crv.OwnerAnswerH
        (Lift.Curve3Crv.Creation.curveDeployedState Lift.Curve3Crv.Creation.deployer)
        j.c3.invocations cs ∧
      JointCheckpoint pool c3Adr
        (Lift.Curve3Pool.Creation.poolInitState Lift.Curve3Pool.Creation.deployTime.toNat)
        cs j.c3.keys j.minterCompleted.state := by
  obtain ⟨poolCode, poolStor⟩ := pool_installed j
  obtain ⟨hcode, -, hinv⟩ := j.c3.created
  have installed : some (j.c3.cut.afterBenv.state.getCode c3Adr).toList =
      Lift.Curve3Crv.c3crvSem.image := by
    rw [hcode]
    rfl
  have c3Code := (Lift.Curve3Crv.c3crv_mid_history_framesHist j.c3.trace installed hinv j.c3.fresh).1
  obtain ⟨cs, run, -, final, -⟩ := j.c3.frames
  refine ⟨poolCode, c3Code, cs, run, ?_⟩
  exact
    { poolCk := checkpoint_of_get
        (Lift.Curve3Pool.Creation.deployedStor_checkpoint (by decide)) poolStor
      c3 := final
      tokenIs := by decide
      minterIs := c3_minter j run
      apart := by decide }

end Blanc.Composition.Curve3PoolJointRoot
