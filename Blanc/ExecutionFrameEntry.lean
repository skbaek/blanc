import Blanc.ExecutionFrames

/-!
# Fresh entry facts for retained execution-frame roots

Every interpreter execution retained by a message begins at the initial
machine of an entered frame.  This module records the corresponding empty
stack and memory condition for the outer root and every recursively entered
child root, independently of settlement or commitment filtering.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

/-- The machine-local part of a freshly entered code frame. -/
def Exec.FreshEntry (_sevm : Sevm) (pre : Devm) : Prop :=
  pre.stack = [] ∧ pre.memory = Mem.empty

/-- A successfully entered child starts with an empty stack and memory. -/
theorem Frame.enter_run_fresh
    {frame : Frame} {child : Evm}
    (henter : frame.enter = .run child) :
    Exec.FreshEntry child.sta child.dyna := by
  obtain ⟨benv, _htransfer, rfl⟩ := Frame.enter_run_inv henter
  exact ⟨rfl, rfl⟩

/-- Every raw descendant is the root of a freshly entered child frame. -/
theorem Exec.rawFrameDescendants_fresh
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    ∀ root ∈ Exec.rawFrameDescendants run,
      Exec.FreshEntry root.sevm root.devm := by
  induction run with
  | halt hstep =>
      intro root member
      simp [Exec.rawFrameDescendants] at member
  | cont hstep next ih =>
      intro root member
      exact ih root (by simpa only [Exec.rawFrameDescendants] using member)
  | doneErr hstep henter hresume =>
      intro root member
      simp [Exec.rawFrameDescendants] at member
  | doneOk hstep henter hresume next ih =>
      intro root member
      exact ih root (by simpa only [Exec.rawFrameDescendants] using member)
  | runErr hstep henter child hresume ih =>
      intro root member
      simp only [Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact Frame.enter_run_fresh henter
      · exact ih root member
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro root member
      simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
      rcases member with rfl | member
      · exact Frame.enter_run_fresh henter
      · rcases member with member | member
        · exact ihChild root member
        · exact ihNext root member

/-- An outer execution selected by a frame entry carries fresh-entry
admission at every raw frame root. -/
theorem Exec.FrameAdmitted.fresh_of_enter
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {frame : Jaune.Frame}
    (henter : frame.enter = FrameEntry.run ⟨pc, sevm, pre⟩)
    (run : Exec pc sevm pre out)
    (ca : Adr) :
    Exec.FrameAdmitted ca Exec.FreshEntry run := by
  intro root member _target
  simp only [Exec.rawFrameRoots, List.mem_cons] at member
  rcases member with rfl | member
  · exact Frame.enter_run_fresh henter
  · exact Exec.rawFrameDescendants_fresh run root member

/-- Two independently checked entry conditions can be carried together over
the same exact frame-root traversal. -/
theorem Exec.FrameAdmitted.and
    {ca : Adr} {left right : Sevm → Devm → Prop}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (hleft : Exec.FrameAdmitted ca left run)
    (hright : Exec.FrameAdmitted ca right run) :
    Exec.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) run := by
  intro root member target
  exact ⟨hleft root member target, hright root member target⟩

end Blanc
