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
open scoped LogOutputHinv

/-- Log-silent steps may write storage; STATICCALL children use actual static semantics. -/
theorem Ninst.logs_of_logSilent_any {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (silent : n.logSilent = true)
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
      exact congrArg Prod.fst (Ninst.staticcall_logs_balances_any run)
  | push bytes bound => exact (Ninst.Hinv.inv (f := Devm.logs) run).symm
  | dupn imm => exact Ninst.dupn_logs run
  | swapn imm => exact Ninst.swapn_logs run
  | exchange imm => exact Ninst.exchange_logs run

/-- Compatibility wrapper retaining the covered-fork interface. -/
theorem Ninst.logs_of_logSilent {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (fork : CoveredFork sevm.benvStat.fork) (silent : n.logSilent = true)
    (run : Ninst.Run sevm pre n post) : post.logs = pre.logs := by
  have _ := fork
  exact Ninst.logs_of_logSilent_any silent run

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

theorem SFunc.logSilent_eq_stepsLastsSatisfy (f : SFunc) :
    f.logSilent = f.stepsLastsSatisfy Ninst.logSilent (· != .selfdestruct) := by
  induction f <;> simp_all only [SFunc.logSilent, SFunc.stepsLastsSatisfy]

/-- Entry membership is closed under every referenced internal jump and call. -/
def LogSilentSet (fs : List SFunc) (entries : List Nat) : Bool :=
  entries.all fun k => match fs[k]? with
    | some f => f.logSilent && f.refs.all (· ∈ entries)
    | none => false

/-- The same original lifted run preserves its entry log list. -/
theorem SFunc.Run.logs_of_logSilent_any {fs : List SFunc} {entries : List Nat}
    (closed : LogSilentSet fs entries = true) {sevm : Sevm}
    {pre : Devm} {f : SFunc} {out : Outcome}
    (silent : f.logSilent = true) (refs : f.refs.all (· ∈ entries) = true)
    (run : SFunc.Run fs sevm pre f out) : (Outcome.devm out).logs = pre.logs := by
  exact SFunc.Run.observation_eq (observe := Devm.logs)
    (next := Ninst.logSilent) (last := (· != .selfdestruct))
    (pop := fun h => h.logs.symm) (burn := fun h => h.logs.symm)
    (step := Ninst.logs_of_logSilent_any)
    (terminal := fun hl hrun =>
      (Linst.world_of_ok (by simpa only [bne_iff_ne] using hl) hrun).2)
    (pc := rfl)
    (closed := by
      unfold ClosedEntrySet
      apply List.all_eq_true.mpr
      intro k member
      have admitted := (List.all_eq_true.mp closed) k member
      cases found : fs[k]? with
      | none => simp only [found, Bool.false_eq_true] at admitted
      | some g =>
        simp only [found, Bool.and_eq_true] at admitted ⊢
        exact ⟨(SFunc.logSilent_eq_stepsLastsSatisfy g).symm.trans admitted.1, admitted.2⟩)
    (checked := by simpa only [← SFunc.logSilent_eq_stepsLastsSatisfy] using silent)
    (refs := refs) run

/-- Compatibility wrapper retaining the original closed-set and covered-fork inputs. -/
theorem SFunc.Run.logs_of_logSilent {fs : List SFunc} {entries : List Nat}
    (closed : LogSilentSet fs entries = true) {sevm : Sevm}
    (fork : CoveredFork sevm.benvStat.fork)
    {pre : Devm} {f : SFunc} {out : Outcome}
    (silent : f.logSilent = true) (refs : f.refs.all (· ∈ entries) = true)
    (run : SFunc.Run fs sevm pre f out) : (Outcome.devm out).logs = pre.logs := by
  have _ := fork
  exact SFunc.Run.logs_of_logSilent_any closed silent refs run

private theorem Ninst.logSilent_of_quiet {n : Ninst} (quiet : n.quiet = true) :
    n.logSilent = true := by
  cases n with
  | reg r => cases r <;> simp_all only [Ninst.quiet, Ninst.logSilent, Bool.false_eq_true]
  | exec x => exact quiet
  | push _ _ => rfl
  | dupn _ => rfl
  | swapn _ => rfl
  | exchange _ => rfl

private theorem SFunc.logSilent_of_quiet {f : SFunc} (quiet : f.quiet = true) :
    f.logSilent = true := by
  induction f with
  | branch f g left right =>
    simp only [SFunc.quiet, SFunc.logSilent, Bool.and_eq_true] at quiet ⊢
    exact ⟨left quiet.1, right quiet.2⟩
  | branchTo f _ ih => exact ih quiet
  | last l => exact quiet
  | next n f ih =>
    simp only [SFunc.quiet, SFunc.logSilent, Bool.and_eq_true] at quiet ⊢
    exact ⟨Ninst.logSilent_of_quiet quiet.1, ih quiet.2⟩
  | dest f ih => exact ih quiet
  | jump _ => rfl
  | callNext _ f ih => exact ih quiet
  | ret => rfl
  | pcAt _ f ih => exact ih quiet
  | undefined => rfl

/-- Quiet closed entry sets satisfy the same log-silent closure without changing membership. -/
theorem LogSilentSet.of_quiet {fs : List SFunc} {entries : List Nat}
    (quiet : QuietSet fs entries = true) : LogSilentSet fs entries = true := by
  unfold QuietSet at quiet
  unfold LogSilentSet
  apply List.all_eq_true.mpr
  intro k member
  have admitted := (List.all_eq_true.mp quiet) k member
  cases found : fs[k]? with
  | none => simp only [found, Bool.false_eq_true] at admitted
  | some f =>
    simp only [found, Bool.and_eq_true] at admitted ⊢
    exact ⟨SFunc.logSilent_of_quiet admitted.1, admitted.2⟩

end Blanc.Lift
