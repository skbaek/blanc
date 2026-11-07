import Blanc.Lift.BuilderRequest.Deposit.Cert
import Blanc.Lift.RequestFee.Getter
import Blanc.RequestFeeWord

/-!
The deposit runtime's fee window and fee read, as instances of the shared request-fee machinery.
The walks start at the tree that takes the target-adjusted excess on the stack; the read of that
excess, and the inhibitor guard before it, are not stated here. Submission-side continuations are
left arbitrary by the window and are not walked.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune

/-- The checked certificate's program. -/
def prog : List SFunc := cert.prog

private def loopDest : RequestFee.PushWord := ⟨0x64, [], by decide⟩
private def postloopDest : RequestFee.PushWord := ⟨0x7f, [], by decide⟩
private def lenWord : RequestFee.PushWord := ⟨0xb8, [], by decide⟩
private def submissionDest : RequestFee.PushWord := ⟨0x9f, [], by decide⟩
private def revertDest : RequestFee.PushWord := ⟨0x02, [0x70], by decide⟩

/-- Entry six's cloned tree is definitionally the header the window falls into. -/
private theorem loop_entry :
    prog[6]? = some (RequestFee.loopTree postloopDest loopDest 6 t_007f_c1) := rfl

variable {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat} {excess finalOutput : B256}
  {o : Outcome}

/-- Inversion of the window from the excess word to the postloop, at the word witness's count. -/
theorem fee_window_inv
    (wordRun : WordFakeExponential.Run excess 17 1 17 0 iterations finalOutput)
    (run : SFunc.Run prog sevm (St b [excess] M G) t_0058_c1 o) :
    ∃ finalCounter G', SFunc.Run prog sevm
      (St b [finalOutput, 0, finalCounter, excess, 17] M G') t_007f_c1 o := by
  obtain ⟨_, run⟩ := ric_dest run.cut
  winv 2
  change SFunc.RunCut _ _ _ (St b [excess, 17] M _) _ _ at run
  obtain ⟨_, run⟩ := RequestFee.init_inv (header := t_0064_c1) run.uncut
  exact RequestFee.loop_inv loop_entry wordRun run

/-- The window forward, at its exact charge. -/
theorem fee_window_exact (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (wordRun : WordFakeExponential.Run excess 17 1 17 0 iterations finalOutput)
    (tail : ∀ finalCounter, SFunc.RunExact prog sevm
      (St b [finalOutput, 0, finalCounter, excess, 17] M G) t_007f_c1 o) :
    SFunc.RunExact prog sevm
      (St b [excess] M (G + RequestFee.feeLoopGas iterations + 19 + 3 + 3 + 1)) t_0058_c1 o := by
  refine rx_dest ?_
  refine rx_push (w := (17 : B256)) rfl (by change 1 < 1024; decide) ?_
  refine rx_swap1 ?_
  exact RequestFee.init_exact (header := t_0064_c1) h_push0
    (RequestFee.loop_exact loop_entry h_push0 wordRun tail)

/-- A successful fee read has zero value and returns a quotient at most the natural fee. -/
theorem fee_read_inv {post : Devm} (aligned : M.size % 32 = 0) (wf : Mem.Wf M)
    (empty : sevm.data = [])
    (wordRun : WordFakeExponential.Run excess 17 1 17 0 iterations finalOutput)
    (run : SFunc.Run prog sevm (St b [excess] M G) t_0058_c1 (.halted post)) :
    sevm.value = 0 ∧ post.output = (finalOutput / (17 : B256)).toBytes ∧
      (finalOutput / (17 : B256)).toNat ≤ fakeExp 1 excess.toNat 17 := by
  obtain ⟨_, _, run⟩ := fee_window_inv wordRun run
  obtain ⟨_, run⟩ := RequestFee.postloop_inv (len := lenWord) (dest := submissionDest)
    (w := 184) rfl run
  have hlen : sevm.data.length.toB256 ≠ 184 := by rw [empty]; decide
  simp only [RequestFee.selected, ite_eq_right hlen] at run
  obtain ⟨_, zero, _, run⟩ := RequestFee.guard_inv (dest := revertDest)
    (accept := t_0099_c1) (revert := t_0270_c1) rfl run
  obtain ⟨_, rfl⟩ := RequestFee.return_inv aligned run
  exact ⟨zero, (RequestFee.feeGetterPost_facts _ _ _ _ wf aligned).1,
    RequestFeeWord.word_fee_le wordRun⟩

/-- The fee read forward, at its exact charge, with the actual RETURN outcome. -/
theorem fee_read_exact (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (aligned : M.size % 32 = 0) (empty : sevm.data = []) (zero : sevm.value = 0)
    (wordRun : WordFakeExponential.Run excess 17 1 17 0 iterations finalOutput) :
    SFunc.RunExact prog sevm
      (St b [excess] M
        (G + RequestFee.feeGetterGas M + 30 + 45 + RequestFee.feeLoopGas iterations + 19 + 3 + 3 + 1))
      t_0058_c1 (.halted (RequestFee.feeGetterPost b M (finalOutput / (17 : B256)) G)) := by
  have hlen : sevm.data.length.toB256 ≠ 184 := by rw [empty]; decide
  have hempty : sevm.data.length.toB256 = 0 := by rw [empty]; rfl
  refine fee_window_exact h_push0 wordRun fun _ => ?_
  refine RequestFee.postloop_exact (len := lenWord) (dest := submissionDest) (w := 184) rfl ?_
  simp only [RequestFee.selected, ite_eq_right hlen]
  exact RequestFee.guard_exact (dest := revertDest) (revert := t_0270_c1) hempty zero
    (RequestFee.return_exact h_push0 aligned)

end Blanc.Lift.BuilderRequest.Deposit
