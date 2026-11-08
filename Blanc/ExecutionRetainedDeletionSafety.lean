import Blanc.ExecutionDeletionSafety
import Blanc.ExecutionExistingAccount
import Jaune.ExecChronology

/-!
No-deletion along the actual complete-settlement-retained chronology.
Discarded child settlements preserve the resumed parent's deletion set;
account preservation supplies code and created-account exclusion separately.
-/

namespace Blanc

open Jaune

/-- An ordinary CREATE resuming from a flagged settled child keeps the
saved parent's deletion set. -/
theorem Resume.create_atd_of_error {parent child post : Devm} {address : Adr}
    (failed : child.error.isSome = true)
    (run : (Resume.create parent address).run (.ok child) = .ok post) :
    post.accountsToDelete = parent.accountsToDelete := by
  simp only [Resume.run, liftToExecution, Bind.bind, Except.bind, failed,
    ↓reduceIte] at run
  exact congrArg Prod.fst (Devm.push_delSets_eq run)

/-- An ordinary CALL resuming from a flagged settled child keeps the
saved parent's deletion set, including the status push and output copy. -/
theorem Resume.call_atd_of_error {parent child post : Devm} {oi os : Nat}
    (failed : child.error.isSome = true)
    (run : (Resume.call parent oi os).run (.ok child) = .ok post) :
    post.accountsToDelete = parent.accountsToDelete := by
  simp only [Resume.run, liftToExecution, Bind.bind, Except.bind, failed,
    ↓reduceIte] at run
  cases hp : (incorporateChildOnError parent child child.output).push 0 with
  | error e => simp only [hp, reduceCtorEq] at run
  | ok pushed =>
    simp only [hp, Except.ok.injEq] at run
    subst post
    exact congrArg Prod.fst (Devm.push_delSets_eq hp)

/-- A discarded COMPLETE settlement and successful ordinary-lane resumption
preserve the actual spawning parent's deletion set. Raw child success is not
a settlement-commitment assumption. -/
theorem Evm.step_spawn_resume_atd_of_discarded_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {raw : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (discarded : Frame.settlementCommits frame raw ≠ true)
    (hresume : resume.run (frame.settle raw) = .ok post) :
    post.accountsToDelete = pre.accountsToDelete := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hstep
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with ⟨ex, hs, -⟩ |
    ⟨d, endowment, address, mi, ms, hf, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isSt, ii, isz,
      oi, osz, code, dp, hf, -, -, -, hs⟩
  · rw [hx] at hs
    cases hs
  · have spawn := hs.symm.trans hx
    obtain ⟨-, rfl⟩ := genericCreate_step_spawn_exact spawn
    cases settled : frame.settle raw with
    | error e =>
      rw [settled] at hresume
      exact False.elim (Resume.create_run_error hresume)
    | ok child =>
      have failed : child.error.isSome = true := by
        simpa only [Frame.settlementCommits, settled, Bool.not_eq_true,
          Option.isNone_eq_false_iff] using discarded
      have atd := Resume.create_atd_of_error failed (settled ▸ hresume)
      exact atd.trans hf.accountsToDelete.symm
  · have spawn := hs.symm.trans hx
    obtain ⟨-, rfl⟩ := genericCall_step_spawn_exact spawn
    cases settled : frame.settle raw with
    | error e =>
      rw [settled] at hresume
      exact False.elim (Resume.call_run_error hresume)
    | ok child =>
      have failed : child.error.isSome = true := by
        simpa only [Frame.settlementCommits, settled, Bool.not_eq_true,
          Option.isNone_eq_false_iff] using discarded
      have atd := Resume.call_atd_of_error failed (settled ▸ hresume)
      exact atd.trans hf.accountsToDelete.symm

end Blanc
