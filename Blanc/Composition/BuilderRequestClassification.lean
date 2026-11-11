import Blanc.Corpus.Freeze.BuilderRequest
import Blanc.Lift.BuilderRequest.PrivilegedFrame

/-!
# Every kept builder frame has one of the four frozen forms

The original retained executions supply the local inversions. No exclusion of
SYSTEM_ADDRESS from transactions, code, authorities or creations is needed:
its empty and nonempty calldata select dequeue and reversible latch.
-/

namespace Blanc.Composition.BuilderRequestClassification

open Jaune Blanc Blanc.Lift.BuilderRequest
open Blanc.Composition.BuilderRequestPublic (depositAddr exitAddr)

private theorem wordFee_of_run {excess finalOutput : B256} {iterations : Nat}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations finalOutput) :
    finalOutput / (17 : B256) = Corpus.Freeze.Builder.wordFee excess := by
  have chosen := Classical.choose_spec (WordFakeExponential.run_exists_unique excess 17 1 17 0).exists
  have output := (run.deterministic chosen).2
  unfold Corpus.Freeze.Builder.wordFee
  rw [output]

private theorem deposit_user_settled {b : KeptBlock} {f : Exec.Frame}
    {l : StorageSteps f.sevm} (target : f.sevm.currentTarget = depositAddr)
    (caller : f.sevm.caller ≠ systemAddress)
    (law : Deposit.UserFrameOn l f.pre f.post) : Corpus.Freeze.Builder.DepositSettled b f := by
  cases law with
  | submission iterations finalOutput effect =>
      have fee : finalOutput / (17 : B256) =
          Corpus.Freeze.Builder.wordFee (Corpus.Freeze.Builder.quotedExcess 8 f.pre depositAddr) := by
        simpa only [storedExcess, Corpus.Freeze.Builder.quotedExcess, target] using wordFee_of_run effect.quote
      refine .submission caller effect.length effect.dynamic ?_ ?_ ?_ ?_ effect.balance ?_ effect.output
      · simpa only [target] using effect.active
      · simpa only [fee] using effect.admitted
      · simpa only [target] using effect.storage
      · simpa only [target] using effect.otherStorage
      · simpa only [target] using effect.logs
  | feeRead iterations finalOutput empty effect =>
      have fee : finalOutput / (17 : B256) =
          Corpus.Freeze.Builder.wordFee (Corpus.Freeze.Builder.quotedExcess 8 f.pre depositAddr) := by
        simpa only [storedExcess, Corpus.Freeze.Builder.quotedExcess, target] using wordFee_of_run effect.quote
      refine .feeRead caller empty effect.value ?_ ?_ effect.storage effect.balance effect.logs
      · simpa only [target] using effect.active
      · simpa only [fee] using effect.output

private theorem exit_user_settled {b : KeptBlock} {f : Exec.Frame}
    {l : StorageSteps f.sevm} (target : f.sevm.currentTarget = exitAddr)
    (caller : f.sevm.caller ≠ systemAddress)
    (law : Exit.UserFrameOn l f.pre f.post) : Corpus.Freeze.Builder.ExitSettled b f := by
  cases law with
  | submission iterations finalOutput effect =>
      have fee : finalOutput / (17 : B256) =
          Corpus.Freeze.Builder.wordFee (Corpus.Freeze.Builder.quotedExcess 2 f.pre exitAddr) := by
        simpa only [storedExcess, Corpus.Freeze.Builder.quotedExcess, target] using wordFee_of_run effect.quote
      refine .submission caller effect.length effect.dynamic ?_ ?_ ?_ ?_ effect.balance ?_ effect.output
      · simpa only [target] using effect.active
      · simpa only [fee] using effect.covered
      · simpa only [target] using effect.storage
      · simpa only [target] using effect.otherStorage
      · simpa only [target] using effect.logs
  | feeRead iterations finalOutput empty effect =>
      have fee : finalOutput / (17 : B256) =
          Corpus.Freeze.Builder.wordFee (Corpus.Freeze.Builder.quotedExcess 2 f.pre exitAddr) := by
        simpa only [storedExcess, Corpus.Freeze.Builder.quotedExcess, target] using wordFee_of_run effect.quote
      refine .feeRead caller empty effect.value ?_ ?_ effect.storage effect.balance effect.logs
      · simpa only [target] using effect.active
      · simpa only [fee] using effect.output

private theorem deposit_settled {b : KeptBlock} {f : Exec.Frame}
    (entry : Exec.Frame.EntryIn depositAddr Deposit.code b.benv.stat f)
    (fork : KeptFork b.fork) : Corpus.Freeze.Builder.DepositSettled b f := by
  obtain ⟨orig, e⟩ := entry
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  obtain ⟨hpc, target, code, stack, size, wf, hstat, dlen⟩ := e
  dsimp only at hpc target code stack size wf hstat dlen
  subst hpc
  cases out with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      have hfork : KeptFork sevm.benvStat.fork := by
        rw [hstat]
        exact fork
      by_cases caller : sevm.caller = systemAddress
      · obtain ⟨dynamic, state, output, balance, logs⟩ :=
          Deposit.privilegedPath.exec_frame code hfork stack wf dlen caller run
        by_cases empty : sevm.data = []
        · refine .dequeue caller empty dynamic ?_ ?_ balance logs
          · rw [ite_eq_left empty, target] at state
            exact state
          · rw [target] at output
            exact output
        · refine .latch caller empty dynamic ?_ ?_ balance logs
          · rw [ite_eq_right empty, target] at state
            exact state
          · rw [target] at output
            exact output
      · rcases hfork with covered | amsterdam
        · exact deposit_user_settled target caller
            (Deposit.exec_user_frame_on (coveredSteps_valid covered) code stack size wf dlen caller run)
        · exact deposit_user_settled target caller
            (Deposit.exec_user_frame_on (amsterdamSteps_valid amsterdam) code stack size wf dlen caller run)

private theorem exit_settled {b : KeptBlock} {f : Exec.Frame}
    (entry : Exec.Frame.EntryIn exitAddr Exit.code b.benv.stat f)
    (fork : KeptFork b.fork) : Corpus.Freeze.Builder.ExitSettled b f := by
  obtain ⟨orig, e⟩ := entry
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  obtain ⟨hpc, target, code, stack, size, wf, hstat, dlen⟩ := e
  dsimp only at hpc target code stack size wf hstat dlen
  subst hpc
  cases out with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      have hfork : KeptFork sevm.benvStat.fork := by
        rw [hstat]
        exact fork
      by_cases caller : sevm.caller = systemAddress
      · obtain ⟨dynamic, state, output, balance, logs⟩ :=
          Exit.privilegedPath.exec_frame code hfork stack wf dlen caller run
        by_cases empty : sevm.data = []
        · refine .dequeue caller empty dynamic ?_ ?_ balance logs
          · rw [ite_eq_left empty, target] at state
            exact state
          · rw [target] at output
            exact output
        · refine .latch caller empty dynamic ?_ ?_ balance logs
          · rw [ite_eq_right empty, target] at state
            exact state
          · rw [target] at output
            exact output
      · rcases hfork with covered | amsterdam
        · exact exit_user_settled target caller
            (Exit.exec_user_frame_on (coveredSteps_valid covered) code stack size wf dlen caller run)
        · exact exit_user_settled target caller
            (Exit.exec_user_frame_on (amsterdamSteps_valid amsterdam) code stack size wf dlen caller run)

/-- Every original retained deposit frame has one of the four frozen forms,
under CodesKept alone, including SYSTEM calls before Amsterdam. -/
theorem b_s2_deposit : Corpus.Freeze.Builder.B_S2_deposit := by
  intro cfg start stop blocks kept b hb f hf
  obtain ⟨next, step⟩ := kept.linked.mem_step b hb
  exact deposit_settled
    (kept.linked.entry_in kept.deposit Deposit.linked.runnable.1 Deposit.linked.runnable.2 b hb f hf) step.kept

/-- Every original retained exit frame has the same four forms and exact effects,
under CodesKept alone and at every kept fork. -/
theorem b_s2_exit : Corpus.Freeze.Builder.B_S2_exit := by
  intro cfg start stop blocks kept b hb f hf
  obtain ⟨next, step⟩ := kept.linked.mem_step b hb
  exact exit_settled
    (kept.linked.entry_in kept.exit Exit.linked.runnable.1 Exit.linked.runnable.2 b hb f hf) step.kept

/-- The exact frozen positive B-S2 conjunction. The ordinary-caller mutant
controls and nonempty applicability witness are separate obligations. -/
theorem b_s2 : Corpus.Freeze.Builder.B_S2 := ⟨b_s2_deposit, b_s2_exit⟩

end Blanc.Composition.BuilderRequestClassification
