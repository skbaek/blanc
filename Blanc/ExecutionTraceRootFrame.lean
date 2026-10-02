import Blanc.ExecutionTraceSettledFrames
import Blanc.TransactionForward

/-!
# A committed transaction's root frame is a settled frame

`settledFrames` collects the committed frames of every retained execution of a
trace.  This module shows the converse completeness fact a witness needs: the
top-level frame a successful message call runs — the frame Jaune's
`processMessage` enters, `initEvm (msg.withBenv after)` — is itself among them
when its settlement commits.  `ProcessMessageTrace.root_mem_settledFrames` is the
message-level statement; `TransactionTrace.root_frame_of_call_value` lifts it to
a type-2 call transaction in the vocabulary of `processTransaction_call_value_of_exec`.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- **The entered frame of a retained message execution is a settled frame.**  If the
call frame enters `cevm`, its execution returns `post`, and settlement commits, the
retained trace's settled frames contain a frame with exactly `cevm`'s pc, static
environment and entry state, and outcome `.ok post`. -/
theorem ProcessMessageTrace.root_mem_settledFrames {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) {cevm : Evm}
    (henter : (Frame.ofCall msg).enter = .run cevm) {post : Devm}
    (hexec : exec cevm = .ok post)
    (hcommit : Frame.settlementCommits (Frame.ofCall msg) (.ok post) = true) :
    ∃ frame ∈ trace.settledFrames, frame.pc = cevm.pc ∧ frame.sevm = cevm.sta ∧
      frame.pre = cevm.dyna ∧ frame.out = .ok post := by
  rcases trace with ⟨slot, retained, run⟩
  have hrun := run
  unfold ProcessMessage RunFrame at hrun
  rw [henter] at hrun
  obtain ⟨raw, hslot, -⟩ := hrun
  subst hslot
  rcases cevm with ⟨pc, sevm, pre⟩
  cases retained with
  | some exn =>
    have hraw : raw = .ok post := by
      have h := (exec_iff_exec_eq pc sevm pre raw).mp ⟨exn⟩
      rw [← h]
      exact hexec
    subst hraw
    have hcommits : Execution.commits (.ok post : Execution) = true := by
      have h := hcommit
      unfold Frame.settlementCommits at h
      sorry
    refine ⟨Exec.Frame.ofRun exn hcommits, ?_, rfl, rfl, rfl, rfl⟩
    simp only [ProcessMessageTrace.settledFrames, hcommit, ite_true]
    unfold Exec.committedFrames
    rw [dif_pos hcommits]
    exact List.mem_cons_self

end Blanc.ExecutionTrace
