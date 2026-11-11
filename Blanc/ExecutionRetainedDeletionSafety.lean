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

/-- A successful Amsterdam CREATE resumption from a flagged child keeps the saved deletion set. -/
theorem Resume.createAmsterdam_atd_of_error {state : StateGasRules} {parent child post : Devm} {address : Adr} {nac : Bool}
    (failed : child.error.isSome = true)
    (run : (Resume.createAmsterdam state parent address nac).run (.ok child) = .ok post) :
    post.accountsToDelete = parent.accountsToDelete := by
  simp only [Resume.run, liftToExecution, Bind.bind, Except.bind, failed, ↓reduceIte] at run
  by_cases guard : child.AmsterdamFailedChildSettled
  · simp only [Except.assert, guard, ↓reduceIte] at run
    split at run <;> exact congrArg Prod.fst (Devm.push_delSets_eq run)
  · simp only [Except.assert, guard, ↓reduceIte] at run
    cases run

/-- A successful Amsterdam CALL error resumption preserves the saved deletion set through output copy. -/
theorem Resume.callAmsterdam_atd_of_error
    {state : StateGasRules} {parent child post : Devm} {oi os : Nat} {nac : Bool}
    (failed : child.error.isSome = true)
    (run : (Resume.callAmsterdam state parent oi os nac).run (.ok child) = .ok post) :
    post.accountsToDelete = parent.accountsToDelete := by
  have finish : ∀ d : Devm, d.accountsToDelete = parent.accountsToDelete →
      (do let pushed ← d.push 0
          .ok (pushed.memWrite oi (child.output.take os)) : Execution) = .ok post →
      post.accountsToDelete = parent.accountsToDelete := by
    intro d same run
    cases hp : d.push 0 with
    | error e => simp only [hp, Except.bind_error, reduceCtorEq] at run
    | ok pushed =>
      simp only [hp, Except.bind_ok, Except.ok.injEq] at run
      subst post
      exact (congrArg Prod.fst (Devm.push_delSets_eq hp)).trans same
  simp only [Resume.run, liftToExecution, Bind.bind, Except.bind, failed, ↓reduceIte] at run
  by_cases guard : child.AmsterdamFailedChildSettled
  · simp only [Except.assert, guard, ↓reduceIte] at run
    exact finish
      (if nac then (incorporateChildAmsterdamOnError parent child child.output).creditStateGasRefund state.newAccount
        else incorporateChildAmsterdamOnError parent child child.output)
      (by split <;> rfl) run
  · simp only [Except.assert, guard, ↓reduceIte] at run
    cases run

/-- The actual Amsterdam CREATE spawn preserves its saved parent and inherited deletion fields. -/
theorem GenericCreateAmsterdam.step_spawn_atd
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} {frame : Frame} {resume : Resume}
    (spawn : genericCreateAmsterdam.step sevm state devm endowment newAddress mi ms = .spawn frame resume) :
    ∃ (m : Msg) (parent : Devm) (nac : Bool), frame = Frame.ofCreate m ∧
      resume = .createAmsterdam state parent newAddress nac ∧
      parent.accountsToDelete = devm.accountsToDelete ∧
      m.inheritedDeletions = (if sevm.benvStat.rules.settle.selfdestructRefund = 0
        then .emptyWithCapacity else parent.accountsToDelete) := by
  have grants (d : Devm) :
      (d.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce sevm.currentTarget).accountsToDelete =
        d.accountsToDelete := by
    exact (Devm.drainStateGasReservoir_instructionFrame d.withholdCreateGas.2).accountsToDelete.symm.trans
      (Devm.withholdCreateGas_instructionFrame d).accountsToDelete.symm
  have reads :
      ((addAccessedAddress ((devm.withReturnData []).balReadAccount sevm.benvStat.rules sevm.currentTarget) newAddress).balReadAccount sevm.benvStat.rules newAddress).accountsToDelete = devm.accountsToDelete := by
    exact (Devm.balReadAccount_instructionFrame _ _ _).accountsToDelete.symm.trans
      ((addAccessedAddress_instructionFrame _ _).accountsToDelete.symm.trans
        (Devm.balReadAccount_instructionFrame _ _ _).accountsToDelete.symm)
  simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at spawn
  all_goals obtain ⟨rfl, rfl⟩ := spawn
  · rename_i _ _ _ charged charge collision
    refine ⟨_, _, _, rfl, rfl, ?_, rfl⟩
    exact (grants charged).trans ((congrArg Prod.fst (chargeStateGas_delSets_eq charge)).trans reads)
  · refine ⟨_, _, _, rfl, rfl, ?_, rfl⟩
    exact (grants _).trans reads

/-- Every discarded complete child settlement preserves its actual spawning parent's deletion set, for all rules. -/
theorem Evm.step_spawn_resume_atd_of_discarded_any
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {raw : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (discarded : Frame.settlementCommits frame raw ≠ true)
    (hresume : resume.run (frame.settle raw) = .ok post) :
    post.accountsToDelete = pre.accountsToDelete := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hstep
  rcases Xinst.step_shape sevm pre x with ⟨ex, hs, -⟩ |
    ⟨d, endowment, address, mi, ms, hf, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isSt, ii, isz,
      oi, osz, code, dp, hf, -, -, -, hs⟩ |
    ⟨d, state, endowment, address, mi, ms, hf, hs⟩ |
    ⟨d, d₀, state, gas, reservoir, value, caller, target, codeAddress, stv, isSt,
      ii, isz, oi, osz, code, dp, nac, ib, hf, -, -, -, hs⟩
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
  · have spawn := hs.symm.trans hx
    obtain ⟨m, parent, charged, -, resumeEq, parentAtd, -⟩ :=
      GenericCreateAmsterdam.step_spawn_atd spawn
    rw [resumeEq] at hresume
    cases settled : frame.settle raw with
    | error e =>
      simp only [settled, Resume.run, liftToExecution, Except.bind_error, reduceCtorEq] at hresume
    | ok child =>
      have failed : child.error.isSome = true := by
        simpa only [Frame.settlementCommits, settled, Bool.not_eq_true,
          Option.isNone_eq_false_iff] using discarded
      have atd := Resume.createAmsterdam_atd_of_error failed (settled ▸ hresume)
      exact atd.trans (parentAtd.trans hf.accountsToDelete.symm)
  · have spawn := hs.symm.trans hx
    rw [(genericCallAmsterdam_step_spawn_exact spawn).2] at hresume
    cases settled : frame.settle raw with
    | error e =>
      simp only [settled, Resume.run, liftToExecution, Except.bind_error, reduceCtorEq] at hresume
    | ok child =>
      have failed : child.error.isSome = true := by
        simpa only [Frame.settlementCommits, settled, Bool.not_eq_true,
          Option.isNone_eq_false_iff] using discarded
      have atd := Resume.callAmsterdam_atd_of_error failed (settled ▸ hresume)
      exact atd.trans hf.accountsToDelete.symm

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
  exact (fun _ : sevm.benvStat.rules.stateGas = none =>
    Evm.step_spawn_resume_atd_of_discarded_any hstep discarded hresume) hsg

end Blanc
