import Blanc.Lift.SoundSpan
import Blanc.Lift.Quiet

/-!
# An exec-free synthetic run keeps its logs

`SFunc.Run.logs_keep`: a run through an exec-free closure that returns holds every log it started with. A walk that has
seen a `LOG` can cross an internal callee with no law about its logs.
-/

namespace Blanc.Lift

open Jaune
open scoped LogOutputHinv

/-- A successful instruction that is no external call keeps the logs. -/
theorem Ninst.logs_keep {sevm : Sevm} {pre post : Devm} {n : Ninst} (hx : ∀ x, n ≠ .exec x)
    (run : Ninst.Run sevm pre n post) : ∀ l ∈ pre.logs, l ∈ post.logs := by
  intro l hl
  cases n with
  | exec x => exact absurd rfl (hx x)
  | reg r =>
    by_cases isLog : ∃ k, r = .log k
    · obtain ⟨k, rfl⟩ := isLog
      obtain ⟨_, _, _, _, _, logs⟩ := of_run_log_val run
      rw [logs]
      exact List.mem_append_left _ hl
    · rcases run with ⟨xl, -, pc, hrun⟩
      simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hrun
      rw [Rinst.logs_of_ok (fun k e => isLog ⟨k, e⟩) hrun.2.symm]
      exact hl
  | push bytes bound => rw [← Ninst.Hinv.inv (f := Devm.logs) run]; exact hl
  | dupn imm => rw [Ninst.dupn_logs run]; exact hl
  | swapn imm => rw [Ninst.swapn_logs run]; exact hl
  | exchange imm => rw [Ninst.exchange_logs run]; exact hl

/-- **A run of an exec-free tree that returns holds the logs it started with.** -/
theorem SFunc.Run.logs_keep {fs : List SFunc} {sevm : Sevm} {E : List Nat} (hE : ExecFreeSet fs E = true) {d : Devm}
    {f : SFunc} {o : Outcome} (run : SFunc.Run fs sevm d f o) :
    ∀ {d' : Devm}, o = .returned d' → f.execFreeIn E = true → ∀ l ∈ d.logs, l ∈ d'.logs := by
  induction run with
  | zero _ hpop _ ih =>
    intro d' hd hfree l hl
    exact ih hd (execFreeIn_branch hfree).1 l (by rw [← hpop.logs]; exact hl)
  | succ _ _ _ hpop _ ih =>
    intro d' hd hfree l hl
    exact ih hd (execFreeIn_branch hfree).2 l (by rw [← hpop.logs]; exact hl)
  | toZero _ hpop _ ih =>
    intro d' hd hfree l hl
    exact ih hd (execFreeIn_branchTo hfree).1 l (by rw [← hpop.logs]; exact hl)
  | toSucc _ _ _ hget hpop _ ih =>
    intro d' hd hfree l hl
    exact ih hd (ExecFreeSet.lookup hE (execFreeIn_branchTo hfree).2 hget) l (by rw [← hpop.logs]; exact hl)
  | last _ => intro d' hd; cases hd
  | next hn _ ih =>
    intro d' hd hfree l hl
    obtain ⟨hx, hf⟩ := execFreeIn_next hfree
    exact ih hd hf l (Ninst.logs_keep hx hn l hl)
  | dest hb _ ih =>
    intro d' hd hfree l hl
    exact ih hd (execFreeIn_dest hfree) l (by rw [← hb.logs]; exact hl)
  | jump _ hget hpop _ ih =>
    intro d' hd hfree l hl
    exact ih hd (ExecFreeSet.lookup hE (execFreeIn_jump hfree) hget) l (by rw [← hpop.logs]; exact hl)
  | ret _ hpop =>
    intro d' hd hfree l hl
    cases hd
    rw [← hpop.logs]
    exact hl
  | callHalt _ _ _ _ _ => intro d' hd; cases hd
  | callRet _ hget hpop _ _ ih1 ih2 =>
    intro d' hd hfree l hl
    obtain ⟨hf, hk⟩ := execFreeIn_callNext hfree
    exact ih2 hd hf l (ih1 rfl (ExecFreeSet.lookup hE hk hget) l (by rw [← hpop.logs]; exact hl))
  | pcAt hn _ _ ih =>
    intro d' hd hfree l hl
    exact ih hd (execFreeIn_pcAt hfree) l (Ninst.logs_keep (fun _ e => by cases e) hn l hl)

end Blanc.Lift
