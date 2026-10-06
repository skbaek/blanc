import Blanc.Lift.CallerProvenance
import Blanc.ExecutionNoninterference

/-!
# The callers of the direct children of a frame that spawns only by CALL/STATICCALL

`CALL` and `STATICCALL` hand the parent's current target to the child as its caller
(`Xinst.step_call_spawn_caller`, `Xinst.step_staticcall_spawn_caller`).  So when every external
instruction a frame executes along its own chain is one of the two, every direct child of the frame
is called by the frame's current target (`Exec.childFrames_caller_of_callKinds`).  A static frame has
only static children (`Exec.childFrames_isStatic`).

`ConfiguredHistoryTrace.settledFrames_callerTarget_of_children` is the caller fold of
`Blanc/Lift/CallerProvenance.lean` with a weaker obligation at `ca`: the direct children of a frame
at `ca` need only satisfy the target property themselves (instead of never being called by `p`),
so a target property that holds trivially on some children (e.g. static ones) needs nothing about
their parent's code.  Everything here is contract-neutral.
-/

namespace Blanc

open Jaune

/-- A `CALL` spawn hands the parent's current target to the child as caller. -/
theorem Xinst.step_call_spawn_caller {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (hspawn : Xinst.step sevm devm .call = .spawn frame resume) :
    frame.inner.caller = sevm.currentTarget := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hspawn
  repeat' split at hspawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  all_goals first
    | cases hspawn
    | rw [(genericCall_step_spawn_exact hspawn).1]; rfl
    | rw [(genericCallAmsterdam_step_spawn_exact hspawn).1]; rfl

/-- A `STATICCALL` spawn hands the parent's current target to the child as caller. -/
theorem Xinst.step_staticcall_spawn_caller {sevm : Sevm} {devm : Devm} {frame : Frame}
    {resume : Resume} (hspawn : Xinst.step sevm devm .staticcall = .spawn frame resume) :
    frame.inner.caller = sevm.currentTarget := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hspawn
  repeat' split at hspawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  all_goals first
    | cases hspawn
    | rw [(genericCall_step_spawn_exact hspawn).1]; rfl
    | rw [(genericCallAmsterdam_step_spawn_exact hspawn).1]; rfl

/-- **The direct children of a CALL/STATICCALL-only frame are called by its current target.**  If every
external instruction decoded along the chain of `root` is `CALL` or `STATICCALL`, every direct child of
a suffix of that chain has the frame's current target as caller. -/
theorem Exec.childFrames_caller_of_callKinds {root : Exec.Deriv}
    (kinds : ∀ {node : Exec.Deriv} {x : Xinst}, Exec.Deriv.ParentPrefix root node →
      Ninst.At node.sevm.code node.pc (.exec x) → x = .call ∨ x = .staticcall) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ c ∈ Exec.childFrames run, c.sevm.caller = sevm.currentTarget := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ c member
      simp only [Exec.childFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro chain
      simpa only [Exec.childFrames] using ih (chain.snoc (.cont step next))
  | doneErr _ _ _ =>
      intro _ c member
      simp only [Exec.childFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro chain
      simpa only [Exec.childFrames] using ih (chain.snoc (.doneOk step enter resume next))
  | runErr _ _ _ _ =>
      intro _ c member
      simp only [Exec.childFrames, List.not_mem_nil] at member
  | runOk step enter child resume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro chain c member
      simp only [Exec.childFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_singleton] at here
          subst here
          obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
          have callerEq : cevm.sta.caller = frame.inner.caller := by
            obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv enter
            rfl
          change cevm.sta.caller = nodeSevm.currentTarget
          rw [callerEq]
          rcases kinds chain instruction with rfl | rfl
          · exact Xinst.step_call_spawn_caller spawn
          · exact Xinst.step_staticcall_spawn_caller spawn
        · simp only [List.not_mem_nil] at here
      · exact nextIh (chain.snoc (.runOk step enter child resume next)) c later

/-- A static frame has only static direct children. -/
theorem Exec.childFrames_isStatic :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      sevm.isStatic = true → ∀ c ∈ Exec.childFrames run, c.sevm.isStatic = true := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ c member
      simp only [Exec.childFrames, List.not_mem_nil] at member
  | cont _ _ ih =>
      simpa only [Exec.childFrames] using ih
  | doneErr _ _ _ =>
      intro _ c member
      simp only [Exec.childFrames, List.not_mem_nil] at member
  | doneOk _ _ _ _ ih =>
      simpa only [Exec.childFrames] using ih
  | runErr _ _ _ _ =>
      intro _ c member
      simp only [Exec.childFrames, List.not_mem_nil] at member
  | runOk step enter _ _ _ _ nextIh =>
      intro static c member
      simp only [Exec.childFrames, List.mem_append] at member
      rcases member with here | later
      · split at here
        · rw [List.mem_singleton] at here
          subst here
          obtain ⟨x, -, spawn, _⟩ := Evm.step_spawn_inv step
          exact (Frame.enter_run_isStatic enter).trans (Xinst.step_spawn_isStatic spawn static)
        · simp only [List.not_mem_nil] at here
      · exact nextIh static c later

/-- The parent-level obligation of the weakened fold: every direct child of a frame at `p` or at `ca`
satisfies the target property. -/
def CallerChildren (p ca : Adr) (Q : Sevm → Prop) (sevm : Sevm) (cs : List Exec.Frame) : Prop :=
  sevm.currentTarget = p ∨ sevm.currentTarget = ca → ∀ c ∈ cs, CallerTarget p ca Q c.sevm

theorem Exec.descendantFrames_callerTarget_of_children {p ca : Adr} {Q : Sevm → Prop} :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      CallerChildren p ca Q sevm (Exec.childFrames run) →
      (∀ G ∈ Exec.descendantFrames run, CallerChildren p ca Q G.sevm (Exec.childFrames G.run)) →
      ∀ F ∈ Exec.descendantFrames run, CallerTarget p ca Q F.sevm := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ _ F member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont _ next ih =>
      intro here below
      simp only [Exec.descendantFrames, Exec.childFrames] at here below ⊢
      exact ih here below
  | doneErr _ _ _ =>
      intro _ _ F member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk _ _ _ next ih =>
      intro here below
      simp only [Exec.descendantFrames, Exec.childFrames] at here below ⊢
      exact ih here below
  | runErr _ _ _ _ =>
      intro _ _ F member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro here below
      by_cases hs : Frame.settlementCommits frame raw = true
      · have hchildren : Exec.childFrames (Exec.runOk hstep henter child hresume next) =
            Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits hs) ::
              Exec.childFrames next := by
          simp only [Exec.childFrames, dite_eq_left hs, List.singleton_append]
        rw [hchildren] at here
        rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume next hs]
          at below ⊢
        have childOk : CallerTarget p ca Q cevm.sta := by
          intro target caller
          rcases Evm.step_spawn_child_caller hstep henter with h | h
          · exact here (Or.inl (h ▸ caller)) _ List.mem_cons_self target caller
          · exact here (Or.inr (h ▸ target)) _ List.mem_cons_self target caller
        intro F member
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with (hF | inChild) | inNext
        · rw [hF]
          exact childOk
        · exact childIh (below _ List.mem_cons_self)
            (fun G hG => below G (List.mem_cons_of_mem _ (List.mem_append_left _ hG))) F inChild
        · exact nextIh (fun t c hc => here t c (List.mem_cons_of_mem _ hc))
            (fun G hG => below G (List.mem_cons_of_mem _ (List.mem_append_right _ hG))) F inNext
      · have hchildren : Exec.childFrames (Exec.runOk hstep henter child hresume next) =
            Exec.childFrames next := by
          simp only [Exec.childFrames, dite_eq_right hs, List.nil_append]
        rw [hchildren] at here
        rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child hresume next hs]
          at below ⊢
        exact nextIh here below

namespace ExecutionTrace

/-- **The weakened caller fold over a configured history.**  If no settled message root runs at `ca`
with caller `p` without `Q`, and every direct child of every settled frame at `p` or at `ca` satisfies
the target property, every settled frame satisfies it. -/
theorem ConfiguredHistoryTrace.settledFrames_callerTarget_of_children {p ca : Adr}
    {Q : Sevm → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (roots : ∀ R ∈ trace.settledRoots, CallerTarget p ca Q R.sevm)
    (children : ∀ G ∈ trace.settledFrames, CallerChildren p ca Q G.sevm (Exec.childFrames G.run)) :
    ∀ F ∈ trace.settledFrames, CallerTarget p ca Q F.sevm := by
  rw [trace.settledFrames_eq] at children ⊢
  intro F member
  obtain ⟨R, hR, inR⟩ := List.mem_flatMap.mp member
  have below : ∀ G ∈ Exec.committedFrames R.run,
      CallerChildren p ca Q G.sevm (Exec.childFrames G.run) :=
    fun G hG => children G (List.mem_flatMap.mpr ⟨R, hR, hG⟩)
  unfold Exec.committedFrames at below inR
  split at inR
  · rename_i committed
    rw [dite_eq_left committed] at below
    rcases List.mem_cons.mp inR with rfl | inner
    · exact roots _ hR
    · exact Exec.descendantFrames_callerTarget_of_children R.run (below _ List.mem_cons_self)
        (fun G hG => below G (List.mem_cons_of_mem _ hG)) F inner
  · simp only [List.not_mem_nil] at inR

end ExecutionTrace

end Blanc
