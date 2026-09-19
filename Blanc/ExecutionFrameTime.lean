import Blanc.ExecutionFrames
import Blanc.ExecutionTraceFrames

/-!
# Block-environment inheritance for execution frames

Every frame entered by an execution inherits the block environment statics of
the execution's outer frame.  The result is stated over the raw frame-root
traversal so it can be combined with trace-local admission conditions.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

private lemma Frame.enter_run_benvStat_of_step
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume} {pc' : Nat} {child : Evm}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run child) :
    child.sta.benvStat = sevm.benvStat := by
  obtain ⟨x, _at, hspawn, _pc⟩ := Evm.step_spawn_inv hstep
  rw [Frame.enter_run_benvStat henter]
  exact Xinst.step_spawn_benvStat hspawn

theorem Exec.frameAdmitted_benvStat {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) (ca : Adr) :
    Exec.FrameAdmitted ca (fun frameSevm _ => frameSevm.benvStat = sevm.benvStat) run := by
  induction run with
  | halt hstep =>
      intro root member target
      simp [Exec.rawFrameRoots, Exec.rawFrameDescendants] at member
      rcases member with rfl
      rfl
  | cont hstep next ih =>
      intro root member target
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact ih root (by simp [Exec.rawFrameRoots, member]) target
  | doneErr hstep henter hresume =>
      intro root member target
      simp [Exec.rawFrameRoots, Exec.rawFrameDescendants] at member
      rcases member with rfl
      rfl
  | doneOk hstep henter hresume next ih =>
      intro root member target
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact ih root (by simp [Exec.rawFrameRoots, member]) target
  | runErr hstep henter child hresume ih =>
      intro root member target
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · rcases member with rfl | member
        · exact Frame.enter_run_benvStat_of_step hstep henter
        · exact (ih root (by simp [Exec.rawFrameRoots, member]) target).trans
            (Frame.enter_run_benvStat_of_step hstep henter)
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro root member target
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | member
      · rfl
      · rcases member with rfl | member
        · exact Frame.enter_run_benvStat_of_step hstep henter
        · rcases member with member | member
          · exact (ihChild root (by simp [Exec.rawFrameRoots, member]) target).trans
              (Frame.enter_run_benvStat_of_step hstep henter)
          · exact ihNext root (by simp [Exec.rawFrameRoots, member]) target

end Blanc
