import Blanc.Lift.Quiet
import Blanc.Lift.WalkKitSupport

/-! # Log preservation for lifted trees with storage writes and static calls -/

namespace Jaune

/-- A regular non-LOG instruction or STATICCALL cannot append logs. -/
def Ninst.logSilent : Ninst → Bool
  | .reg (.log _) => false
  | .exec x => x == .staticcall
  | _ => true

end Jaune

namespace Blanc.Lift

open Jaune

/-- Log-silent steps may write storage; STATICCALL children use actual static semantics. -/
theorem Ninst.logs_of_logSilent {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (fork : CoveredFork sevm.benvStat.fork) (silent : n.logSilent = true)
    (run : Ninst.Run sevm pre n post) : post.logs = pre.logs := by
  cases n with
  | reg r =>
      obtain ⟨pc, executed⟩ := of_run_reg run
      apply Rinst.logs_of_ok ?_ executed
      rintro k rfl
      simp only [Ninst.logSilent, Bool.false_eq_true] at silent
  | exec x =>
      have hx : x = .staticcall := by simpa only [Ninst.logSilent, beq_iff_eq] using silent
      subst x
      exact (Ninst.world_of_quiet fork rfl run).2
  | push bytes bound => exact (Ninst.world_of_quiet fork rfl run).2
  | dupn imm => exact (Ninst.world_of_quiet fork rfl run).2
  | swapn imm => exact (Ninst.world_of_quiet fork rfl run).2
  | exchange imm => exact (Ninst.world_of_quiet fork rfl run).2

/-- A tree whose steps preserve logs and whose terminals exclude SELFDESTRUCT. -/
def SFunc.logSilent : SFunc → Bool
  | .branch f g => f.logSilent && g.logSilent
  | .branchTo f _ => f.logSilent
  | .last l => l != .selfdestruct
  | .next n f => n.logSilent && f.logSilent
  | .dest f => f.logSilent
  | .jump _ => true
  | .callNext _ f => f.logSilent
  | .ret => true
  | .pcAt _ f => f.logSilent
  | .undefined => true

/-- Entry membership is closed under every referenced internal jump and call. -/
def LogSilentSet (fs : List SFunc) (entries : List Nat) : Bool :=
  entries.all fun k => match fs[k]? with
    | some f => f.logSilent && f.refs.all (· ∈ entries)
    | none => false

/-- The same original lifted run preserves its entry log list. -/
theorem SFunc.Run.logs_of_logSilent {fs : List SFunc} {entries : List Nat}
    (closed : LogSilentSet fs entries = true) {sevm : Sevm}
    (fork : CoveredFork sevm.benvStat.fork)
    {pre : Devm} {f : SFunc} {out : Outcome}
    (silent : f.logSilent = true) (refs : f.refs.all (· ∈ entries) = true)
    (run : SFunc.Run fs sevm pre f out) : (Outcome.devm out).logs = pre.logs := by
  have lookup : ∀ {k g}, k ∈ entries → fs[k]? = some g →
      g.logSilent = true ∧ g.refs.all (· ∈ entries) = true := by
    intro k g member found
    have h := (List.all_eq_true.mp closed) k member
    rw [found] at h
    simpa only [Bool.and_eq_true] using h
  induction run with
  | zero _ popped _ ih =>
      simp only [SFunc.logSilent, Bool.and_eq_true] at silent
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at refs
      exact (ih silent.1 refs.1).trans popped.logs.symm
  | succ _ _ _ popped _ ih =>
      simp only [SFunc.logSilent, Bool.and_eq_true] at silent
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at refs
      exact (ih silent.2 refs.2).trans popped.logs.symm
  | toZero _ popped _ ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      exact (ih silent refs.2).trans popped.logs.symm
  | toSucc _ _ _ found popped _ ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      have target := lookup (of_decide_eq_true refs.1) found
      exact (ih target.1 target.2).trans popped.logs.symm
  | last executed =>
      exact (Linst.world_of_ok (by simpa only [SFunc.logSilent, bne_iff_ne] using silent)
        executed).2
  | next step _ ih =>
      simp only [SFunc.logSilent, Bool.and_eq_true] at silent
      exact (ih silent.2 refs).trans (Ninst.logs_of_logSilent fork silent.1 step)
  | dest burned _ ih => exact (ih silent refs).trans burned.logs.symm
  | jump _ found popped _ ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      have target := lookup (of_decide_eq_true refs.1) found
      exact (ih target.1 target.2).trans popped.logs.symm
  | ret _ popped => exact popped.logs.symm
  | callHalt _ found popped _ ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      have target := lookup (of_decide_eq_true refs.1) found
      exact (ih target.1 target.2).trans popped.logs.symm
  | callRet _ found popped _ _ ihCall ihTail =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at refs
      have target := lookup (of_decide_eq_true refs.1) found
      exact (ihTail silent refs.2).trans ((ihCall target.1 target.2).trans popped.logs.symm)
  | pcAt step _ _ ih =>
      exact (ih silent refs).trans (Ninst.logs_of_logSilent fork rfl step)

end Blanc.Lift
