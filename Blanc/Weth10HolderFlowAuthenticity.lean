import Blanc.Weth10HolderFlow

/-!
Root-altitude facts for the retained execution ledger.

Every `Exec` admitted by a settled message trace starts at the initial machine
of an entered frame.  Recursive child derivations likewise start at their
frame entry.  This is the bridge from the structural committed-frame traversal
to the whole-program functional theorems, which require `pc = 0` and fresh
memory.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- A retained frame is a whole entered code frame, rather than an arbitrary
mid-program continuation. -/
def Exec.Frame.IsRoot (frame : Exec.Frame) : Prop :=
  frame.pc = 0 ∧ frame.pre.memory = Mem.empty

private theorem frame_enter_run_memory
    {frame : Frame} {child : Evm}
    (h : frame.enter = .run child) : child.dyna.memory = Mem.empty := by
  obtain ⟨benv, _, rfl⟩ := Frame.enter_run_inv h
  rfl

private theorem byteArray_eq_of_toList_eq {left right : ByteArray}
    (h : left.toList = right.toList) : left = right := by
  cases left with
  | mk leftData =>
      cases right with
      | mk rightData =>
          simp only [ByteArray.toList_eq_toList_data] at h
          cases Array.ext' h
          rfl

/-- The proof-only context required to turn an executable candidate into an
authentic whole-program action.  It adds the installed-code witness that is
deliberately absent from the decidable filter. -/
structure Exec.Frame.AuthenticContext
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop where
  root : frame.IsRoot
  invocation : frame.exactInvocation dp ca
  installed : Prog.At (weth10 dp) ca frame.pc frame.sevm frame.pre

theorem Exec.Frame.AuthenticContext.memory_wf
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (h : frame.AuthenticContext dp ca) : Mem.Wf frame.pre.memory := by
  rw [h.root.2]
  exact Mem.wf_empty

theorem Exec.Frame.AuthenticContext.memory_reads_empty
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (h : frame.AuthenticContext dp ca) : Mem.Reads frame.pre.memory [] := by
  rw [h.root.2]
  exact Mem.reads_empty

theorem Exec.Frame.AuthenticContext.stateCode_eq
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (h : frame.AuthenticContext dp ca) :
    frame.pre.getCode ca = frame.sevm.code := by
  apply byteArray_eq_of_toList_eq
  exact Option.some.inj (h.installed.1.trans h.invocation.2.2.2.symm)

/-- Every descendant retained by `Exec.descendantFrames` is the initial
machine of an actually entered child frame. -/
theorem Exec.mem_descendantFrames_isRoot
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) {frame : Exec.Frame}
    (hmem : frame ∈ Blanc.Weth10.Exec.descendantFrames run) :
    frame.IsRoot := by
  induction run with
  | halt hstep =>
      simp [Blanc.Weth10.Exec.descendantFrames] at hmem
  | cont hstep next ih =>
      apply ih
      simpa only [Blanc.Weth10.Exec.descendantFrames] using hmem
  | doneErr hstep henter hresume =>
      simp [Blanc.Weth10.Exec.descendantFrames] at hmem
  | doneOk hstep henter hresume next ih =>
      apply ih
      simpa only [Blanc.Weth10.Exec.descendantFrames] using hmem
  | runErr hstep henter child hresume ihChild =>
      simp [Blanc.Weth10.Exec.descendantFrames] at hmem
  | runOk hstep henter child hresume next ihChild ihNext =>
      simp only [Blanc.Weth10.Exec.descendantFrames] at hmem
      split at hmem
      · simp only [List.mem_append, List.mem_cons] at hmem
        rcases hmem with (rfl | hchild) | hnext
        · exact ⟨Frame.enter_run_pc henter,
            frame_enter_run_memory henter⟩
        · exact ihChild hchild
        · exact ihNext hnext
      · exact ihNext hmem

/-- Root freshness plus the structural child theorem covers the complete
committed-frame list. -/
theorem Exec.committedFrames_isRoot
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hpc : pc = 0) (hmemory : pre.memory = Mem.empty) :
    ∀ frame ∈ Blanc.Weth10.Exec.committedFrames run, frame.IsRoot := by
  intro frame hframe
  unfold Blanc.Weth10.Exec.committedFrames at hframe
  split at hframe
  · simp only [List.mem_cons] at hframe
    rcases hframe with rfl | hdesc
    · exact ⟨hpc, hmemory⟩
    · exact Exec.mem_descendantFrames_isRoot run hdesc
  · cases hframe

/-- All committed frames retained by one raw execution slot start at whole
frame altitude. -/
def RetainedXlot.AllFramesRoot :
    {xl : Xlot} → RetainedXlot xl → Prop
  | _, .none => True
  | _, .some run =>
      ∀ frame ∈ Blanc.Weth10.Exec.committedFrames run, frame.IsRoot

theorem ProcessMessageTrace.allFramesRoot
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) :
    trace.retained.AllFramesRoot := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none => simp [RetainedXlot.AllFramesRoot]
  | @some pc sevm pre execution run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hrun).1
      exact Exec.committedFrames_isRoot run
        (Frame.enter_run_pc henter)
        (frame_enter_run_memory henter)

theorem ProcessCreateMessageTrace.allFramesRoot
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) :
    trace.retained.AllFramesRoot := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none => simp [RetainedXlot.AllFramesRoot]
  | @some pc sevm pre execution run =>
      have henter : (Frame.ofCreate msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hrun).1
      exact Exec.committedFrames_isRoot run
        (Frame.enter_run_pc henter)
        (frame_enter_run_memory henter)

/-- Accounted replay does not weaken the existing configured-chain stability
theorem; its ordinary reach projection transports the checkpoint invariant to
the endpoint. -/
theorem AccountedHistory.future_stable
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    Stable dp ca future.state :=
  chainUsing_preserves_stable dp ca
    (ChainConfig.pragueOnly chainId) checkpoint future
    history.toReachUsing hstable

end Weth10

end Blanc
