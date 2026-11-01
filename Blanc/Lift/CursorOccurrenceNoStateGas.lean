import Blanc.Lift.CursorOccurrence
import Blanc.ExecutionStagedSstoreAttribution
import Blanc.Lift.CursorTreeNinst

/-!
# Checked cursors at actual occurrences without a covered fork

The cursor cuts themselves take `stateGas = none` (`cursor_next_forwardH` in
`CursorCuts`, `cursor_next_call_occurrence_forwardH` in `CursorOccurrence`).

At a raw frame of a `ConfiguredHistoryTraceIn` the entry facts of the lift
(pc zero, `stateGas = none`) come from `rawFrame_entryFacts`:
`ConfiguredHistoryTraceIn.rawFrame_reach_of_parentPrefix` places every node
of the frame's same-frame chain at a checked cursor reached by `StepIn`
steps of that frame, and
`ConfiguredHistoryTraceIn.exists_retainedSstore_frame_reach` places the
retained `SSTORE` attributed by `exists_retainedSstore_frame` at such a
cursor of the committed frame executing at the owner, for whichever
certified code that frame runs, and
`ConfiguredHistoryTraceIn.exists_retainedSstore_frame_sstoreCursor` adds that
the cursor's tree there is the checked `SSTORE` next node, with the write's
key and value on top of the node's stack.
-/

namespace Blanc.Lift

open Jaune

end Blanc.Lift

namespace Blanc.ExecutionTrace

open Jaune Blanc.Lift

/-- **Same-frame nodes of a raw history frame sit at checked cursors.** For a
raw frame of a selected-domain history running certified code, every node of
its same-frame chain is reached from entry by `StepIn` steps of that frame
and sits at a checked cursor. -/
theorem ConfiguredHistoryTraceIn.rawFrame_reach_of_parentPrefix {F : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    {R N : Exec.Deriv} (member : R ∈ history.rawFrames) (hcode : R.sevm.code = code)
    (chain : Exec.Deriv.ParentPrefix R N) :
    ∃ κ, Reach (StepIn R) c.prog R.sevm ((Cursor.start c).conf R.devm) (κ.conf N.devm) ∧
      CursorOK code c N κ := by
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities R member
  exact reach_of_parentPrefix_noStateGas checked pc hcode hsg chain

/-- **A changed cell's last retained SSTORE at a checked cursor.** The write
attributed by `exists_retainedSstore_frame` lies in a committed raw frame at
the owner; whichever certified code that frame runs, the write's node is
reached from the frame's entry by `StepIn` steps of the frame and sits at a
checked cursor. -/
theorem ConfiguredHistoryTraceIn.exists_retainedSstore_frame_reach {F : Fork → Prop}
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
      frame.sevm.currentTarget = owner ∧
      ∀ {code : ByteArray} {c : Cert}, Cert.check code c = true → frame.sevm.code = code →
        ∃ κ, Reach (StepIn (Blanc.Exec.Frame.rootDeriv frame)) c.prog frame.sevm
            ((Cursor.start c).conf frame.pre) (κ.conf write.occurrence.node.devm) ∧
          CursorOK code c write.occurrence.node κ := by
  obtain ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target⟩ := history.exists_retainedSstore_frame capabilities member committed hcode changed
  exact ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, fun checked code =>
      history.rawFrame_reach_of_parentPrefix capabilities checked frameRaw code chain⟩

/-- **A changed cell's last retained SSTORE at a checked `SSTORE` node.**
`exists_retainedSstore_frame_reach` with the cursor's tree at the write's node
being the checked `SSTORE` next node (`CursorOK.tree_of_sstore`) and the
write's key and value on top of that node's stack. -/
theorem ConfiguredHistoryTraceIn.exists_retainedSstore_frame_sstoreCursor {F : Fork → Prop}
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
      frame.sevm.currentTarget = owner ∧
      (∃ rest, write.occurrence.node.devm.stack = write.key :: write.value :: rest) ∧
      ∀ {code : ByteArray} {c : Cert}, Cert.check code c = true → frame.sevm.code = code →
        ∃ (κ : Cursor) (g : SFunc),
          Reach (StepIn (Blanc.Exec.Frame.rootDeriv frame)) c.prog frame.sevm
            ((Cursor.start c).conf frame.pre) (κ.conf write.occurrence.node.devm) ∧
          CursorOK code c write.occurrence.node κ ∧ κ.f = .next (.reg .sstore) g := by
  obtain ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, reach⟩ := history.exists_retainedSstore_frame_reach capabilities member committed
      hcode changed
  have decoded : Ninst.At write.occurrence.node.sevm.code write.occurrence.node.pc
      (.reg .sstore) := by
    rw [← write.instruction_eq]
    exact write.occurrence.decoded
  refine ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, ⟨_, write.popped⟩, fun checked code => ?_⟩
  obtain ⟨κ, reached, placed⟩ := reach checked code
  obtain ⟨g, tree, -⟩ := placed.tree_of_sstore decoded
  exact ⟨κ, g, reached, placed, tree⟩

end Blanc.ExecutionTrace
