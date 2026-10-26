import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionTraceFrameEnv
import Blanc.ExecutionOccurrence

/-!
# Retained SSTOREs at the raw frames of a selected-domain history

The raw frames of a `ConfiguredHistoryTraceIn` are closed under descent
(`rawFrames_closed`): every raw frame root inside a raw frame's derivation is
itself a raw frame of the history. A committing raw frame whose own
derivation changes a storage cell of an initially code-bearing owner has a
last retained successful `SSTORE` of that cell (G2,
`Exec.exists_lastRetainedSstore_of_getStor_ne_noStateGas`, with
`stateGas = none` from `rawFrame_entryFacts`). The write sits on the
same-frame prefix of a committed frame of that derivation; that frame is a
raw frame of the history and executes at the owner.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

theorem BeaconStageTrace.rawFrames_closed {rules : ForkRules} {benv : Benv} {state : State}
    {bal : BalBuilder} (trace : BeaconStageTrace rules benv state bal) :
    RawFramesClosed trace.rawFrames :=
  match trace with
  | .skipped .. => RawFramesClosed.nil
  | .called _ _ message _ _ => message.message.rawFrames_closed

theorem HistoryStageTrace.rawFrames_closed {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    RawFramesClosed trace.rawFrames :=
  match trace with
  | .skipped .. => RawFramesClosed.nil
  | .called _ _ _ _ message _ _ => message.message.rawFrames_closed

theorem RequestStageTrace.rawFrames_closed {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    RawFramesClosed trace.rawFrames :=
  match trace with
  | .skipped .. => RawFramesClosed.nil
  | .called _ requests _ => RawFramesClosed.append
      requests.withdrawal.message.rawFrames_closed
      requests.consolidation.message.rawFrames_closed

theorem StagedBodyTrace.rawFrames_closed {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    RawFramesClosed trace.rawFrames :=
  RawFramesClosed.append (RawFramesClosed.append (RawFramesClosed.append
    trace.beacon.rawFrames_closed trace.history.rawFrames_closed)
    trace.transactions.rawFrames_closed) trace.requests.rawFrames_closed

/-- **The raw frames of a selected-domain history are closed under descent.** -/
theorem ConfiguredHistoryTraceIn.rawFrames_closed {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    RawFramesClosed history.rawFrames := by
  induction history with
  | refl => exact RawFramesClosed.nil
  | step prior block ih =>
      exact RawFramesClosed.append ih block.bodyTrace.rawFrames_closed

/-- A committed frame of a raw frame's derivation is a raw frame of the
history. -/
theorem ConfiguredHistoryTraceIn.committedFrame_mem_rawFrames {F : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    {frame : Exec.Frame} (committed : frame ∈ Exec.committedFrames R.exc) :
    Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames :=
  history.rawFrames_closed R member _
    (Exec.mem_rawFrameRoots_of_mem_committedFrames R.exc frame committed)

/-- **Attribution of a changed cell to a retained SSTORE at the owner.** A
committing raw frame `R` of a selected-domain history whose own derivation
changes cell `key` of an owner with nonempty code at `R`'s entry has a last
retained successful `SSTORE` of that cell recording the final word. The
write lies on the same-frame prefix of a committed frame of `R`'s
derivation; that frame is a raw frame of the history executing at the
owner. -/
theorem ConfiguredHistoryTraceIn.exists_retainedSstore_frame {F : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {owner : Adr} {key : B256}
    (hcode : (R.devm.getCode owner).toList ≠ [])
    (changed : (Devm.getStor R.devm owner).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) owner).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = owner ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) owner).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = owner := by
  obtain ⟨-, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities R member
  rcases R with ⟨pc, sevm, pre, out, run⟩
  dsimp only at hsg committed hcode changed member ⊢
  obtain ⟨write, retained, ownerEq, keyEq, valueEq, last⟩ :=
    Exec.exists_lastRetainedSstore_of_getStor_ne_noStateGas run committed hsg hcode changed
  obtain ⟨frame, frameMem, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix run write.occurrence.node).mp
      retained
  refine ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem,
    history.committedFrame_mem_rawFrames member frameMem, chain, ?_⟩
  have target := congrArg Sevm.currentTarget (Exec.Deriv.ParentPrefix.sevm_eq chain)
  exact target.symm.trans ownerEq

end ExecutionTrace

end Blanc
