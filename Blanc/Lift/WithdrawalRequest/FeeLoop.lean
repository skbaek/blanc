import Blanc.Lift.WithdrawalRequest.UserSetup
import Blanc.Lift.RequestFee.Window

/-!
The certified unsigned-word fee loop, an instance of `RequestFee.loopTree`. The
walk stops before the postloop tree, retaining arbitrary base state and memory.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

private def loopDest : RequestFee.PushWord := ⟨0x4d, [], by decide⟩
private def postloopDest : RequestFee.PushWord := ⟨0x68, [], by decide⟩

/-- Entry five's cloned tree is definitionally the same header as the initial entry. -/
private theorem loop_entry :
    prog[5]? = some (RequestFee.loopTree postloopDest loopDest 5 t_0068_c0) := rfl

/-- Inversion follows the same finite word witness and exposes the discarded final counter. -/
theorem fee_loop_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator finalOutput : B256}
    {iterations : Nat} {o : Outcome}
    (wordRun : WordFakeExponential.Run numerator denominator counter accumulator output iterations finalOutput)
    (run : SFunc.Run prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M G) t_004d_c0 o) :
    ∃ finalCounter G', SFunc.Run prog sevm
      (St b [finalOutput, 0, finalCounter, numerator, denominator] M G') t_0068_c0 o :=
  RequestFee.loop_inv loop_entry wordRun run

/-- Exact continuation transport for the word witness's body count. -/
theorem fee_loop_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator finalOutput : B256}
    {iterations : Nat} {o : Outcome}
    (hfork : CoveredFork sevm.benvStat.fork)
    (wordRun : WordFakeExponential.Run numerator denominator counter accumulator output iterations finalOutput)
    (tail : ∀ finalCounter, SFunc.RunExact prog sevm
      (St b [finalOutput, 0, finalCounter, numerator, denominator] M G) t_0068_c0 o) :
    SFunc.RunExact prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + RequestFee.feeLoopGas iterations))
      t_004d_c0 o :=
  RequestFee.loop_exact loop_entry hfork.rules_push0 wordRun tail

/-- A successful canonical user execution reaches the word sum at the postloop boundary. -/
theorem exec_fee_loop {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = Blanc.withdrawalRequestCode)
    (hfork : CoveredFork sevm.benvStat.fork) (hstack : pre.stack = [])
    (user : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ iterations finalOutput,
      WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput ∧
      ∃ finalCounter G, SFunc.Run prog sevm
        (St (afterSload sevm pre 0) [finalOutput, 0, finalCounter, pre.getStorVal sevm.currentTarget 0, 17]
          pre.memory G) t_0068_c0 (.halted post) := by
  obtain ⟨active, _, run⟩ := exec_user_setup hcode hfork hstack user exec
  obtain ⟨iterations, finalOutput, wordRun, _⟩ :=
    WordFakeExponential.run_exists (pre.getStorVal sevm.currentTarget 0) 17 1 17 0
  exact ⟨active, iterations, finalOutput, wordRun, fee_loop_inv wordRun run⟩

/-- Exact postloop continuations transport through the initialized user setup and word loop. -/
theorem user_fee_loop_exact {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat}
    {finalOutput : B256} {o : Outcome} (hfork : CoveredFork sevm.benvStat.fork)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput)
    (tail : ∀ finalCounter, SFunc.RunExact prog sevm
      (St (afterSload sevm b 0) [finalOutput, 0, finalCounter, b.getStorVal sevm.currentTarget 0, 17] M G)
      t_0068_c0 o) :
    SFunc.RunExact prog sevm
      (St b [] M (G + RequestFee.feeLoopGas iterations + userSetupGas sevm b)) t_001a_c0 o := by
  exact user_setup_exact hfork active (fee_loop_exact hfork wordRun tail)

end Blanc.Lift.WithdrawalRequest
