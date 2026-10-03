import Blanc.Lift.WithdrawalRequest.UserSetup
import Blanc.WordFakeExponential
import Blanc.MachineDataFacts

/-!
The certified unsigned-word fee loop. Its finite recurrence witness supplies
the body count; no independent fuel or termination proof is used. The walk
stops before the postloop tree, retaining arbitrary base state and memory.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune
open WordFakeExponential (nextAccumulator)

/-- JUMPDEST, PUSH0, DUP3, GT, ISZERO, PUSH1, JUMPI. -/
def feeLoopHeaderGas : Nat := gJumpdest + gBase + 4 * gVerylow + gHigh

/-- Thirteen very-low operations, two MULs, DIV, and the backedge JUMP. -/
def feeLoopBodyGas : Nat := 13 * gVerylow + 3 * gLow + gMid

/-- Every active body has a header test; one additional test exits the loop. -/
def feeLoopGas (iterations : Nat) : Nat :=
  feeLoopHeaderGas * (iterations + 1) + feeLoopBodyGas * iterations

theorem feeLoopHeaderGas_eq : feeLoopHeaderGas = 25 := rfl
theorem feeLoopBodyGas_eq : feeLoopBodyGas = 62 := rfl

theorem feeLoopGas_eq (iterations : Nat) : feeLoopGas iterations = 25 + 87 * iterations := by
  unfold feeLoopGas
  rw [feeLoopHeaderGas_eq, feeLoopBodyGas_eq, Nat.mul_add, Nat.mul_one]
  rw [Nat.add_right_comm, ← Nat.add_mul]
  exact Nat.add_comm _ _

private theorem feeLoopGas_succ (iterations : Nat) :
    feeLoopGas (iterations + 1) = feeLoopGas iterations + 62 + 25 := by
  rw [feeLoopGas_eq, feeLoopGas_eq, Nat.mul_add, Nat.mul_one]
  simp only [Nat.add_assoc]

/-- Entry five's cloned tree is definitionally the same header as the initial entry. -/
private theorem loop_entry : prog[5]? = some t_004d_c0 := rfl

private theorem header_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator : B256} {o : Outcome}
    (run : SFunc.Run prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M G) t_004d_c0 o) :
    ∃ G', SFunc.Run prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M G')
      (if accumulator = 0 then t_0068_c0 else t_0055_c0) o := by
  obtain ⟨_, run⟩ := ric_dest run.cut
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  change SFunc.RunCut _ _ _ (St b [0, output, accumulator, counter, numerator, denominator] M _) _ _ at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := accumulator) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_gt h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_iszero h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  rcases ric_branch run with ⟨flag, G', run⟩ | ⟨flag, G', run⟩
  · have active : accumulator ≠ 0 := by
      intro hz
      subst accumulator
      change (1 : B256) = 0 at flag
      exact (by decide : (1 : B256) ≠ 0) flag
    exact ⟨G', (ite_eq_right active) ▸ run.uncut⟩
  · have hle := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero flag)
    have hz : accumulator = 0 := B256.toNat_inj _ _ (Nat.eq_zero_of_le_zero hle)
    exact ⟨G', (ite_eq_left hz) ▸ run.uncut⟩

private theorem header_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator : B256} {o : Outcome}
    (tail : SFunc.RunExact prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M G)
      (if accumulator = 0 then t_0068_c0 else t_0055_c0) o) :
    SFunc.RunExact prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + 25)) t_004d_c0 o := by
  have hgas : G + 25 = G + 10 + 3 + 3 + 3 + 3 + 2 + 1 := by
    simp only [Nat.add_assoc]
  rw [hgas]
  unfold t_004d_c0
  refine rx_dest ?_
  refine rx_push0 (by change 5 < 1024; decide) ?_
  refine rx_dup3 (by change 6 < 1024; decide) ?_
  refine rx_gt rfl (by change 5 < 1024; decide) ?_
  refine rx_iszero rfl (by change 5 < 1024; decide) ?_
  refine rx_push rfl (by change 6 < 1024; decide) ?_
  by_cases hz : accumulator = 0
  · subst accumulator
    change SFunc.RunExact _ _ (St b ((104 : B256) :: 1 :: _) _ _) _ _
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) tail
  · have positive : (0 : B256) < accumulator := by
      rw [B256.lt_iff_toNat_lt_toNat]
      exact Nat.pos_of_ne_zero (fun h => hz (B256.toNat_inj _ _ h))
    have flag : B256.eqCheck (B256.gtCheck accumulator 0) 0 = 0 := by
      simp only [B256.gtCheck, ite_eq_left positive, B256.eqCheck,
        ite_eq_right (by decide : (1 : B256) ≠ 0)]
    rw [flag]
    apply rx_branch_zero
    simpa only [ite_eq_right hz] using tail

private theorem body_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator : B256} {o : Outcome}
    (run : SFunc.Run prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M G) t_0055_c0 o) :
    ∃ G', SFunc.Run prog sevm
      (St b [output + accumulator, nextAccumulator numerator denominator counter accumulator,
        counter + 1, numerator, denominator] M G') t_004d_c0 o := by
  have run := run.cut
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := accumulator) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_add h
  rw [show accumulator + output = output + accumulator from B256.add_comm] at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := [accumulator, output + accumulator, counter, numerator, denominator]) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := numerator) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mul h
  rw [Blanc.B256.mul_comm numerator accumulator] at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := denominator) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := counter) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mul h
  rw [Blanc.B256.mul_comm counter denominator] at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap
    (S' := [accumulator * numerator, denominator * counter, output + accumulator, counter, numerator, denominator]) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_div h
  change SFunc.RunCut _ _ _
    (St b [nextAccumulator numerator denominator counter accumulator, output + accumulator,
      counter, numerator, denominator] M _) _ _ at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap
    (S' := [counter, output + accumulator, nextAccumulator numerator denominator counter accumulator,
      numerator, denominator]) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  change SFunc.RunCut _ _ _ (St b
    [1, counter, output + accumulator, nextAccumulator numerator denominator counter accumulator,
      numerator, denominator] M _) _ _ at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_add h
  rw [show (1 : B256) + counter = counter + 1 from B256.add_comm] at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap
    (S' := [nextAccumulator numerator denominator counter accumulator, output + accumulator,
      counter + 1, numerator, denominator]) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap
    (S' := [output + accumulator, nextAccumulator numerator denominator counter accumulator,
      counter + 1, numerator, denominator]) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨G', run⟩ := ric_jump (by intro h; cases h) loop_entry run
  exact ⟨G', run.uncut⟩

private theorem body_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator : B256} {o : Outcome}
    (tail : SFunc.RunExact prog sevm
      (St b [output + accumulator, nextAccumulator numerator denominator counter accumulator,
        counter + 1, numerator, denominator] M G) t_004d_c0 o) :
    SFunc.RunExact prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + 62)) t_0055_c0 o := by
  have hgas : G + 62 = G + 8 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 5 + 3 + 3 + 5 + 3 + 3 + 3 + 3 := by
    simp only [Nat.add_assoc]
  rw [hgas]
  unfold t_0055_c0
  refine rx_dup2 (by change 5 < 1024; decide) ?_
  refine rx_add' B256.add_comm (by change 4 < 1024; decide) ?_
  refine rx_swap1 ?_
  refine rx_dup4 (by change 5 < 1024; decide) ?_
  refine rx_mul (Blanc.B256.mul_comm numerator accumulator) (by change 4 < 1024; decide) ?_
  refine rx_dup (n := 4) rfl (by change 5 < 1024; decide) ?_
  refine rx_dup4 (by change 6 < 1024; decide) ?_
  refine rx_mul (Blanc.B256.mul_comm counter denominator) (by change 5 < 1024; decide) ?_
  refine rx_swap1 ?_
  refine rx_div (v := nextAccumulator numerator denominator counter accumulator) rfl
    (by change 4 < 1024; decide) ?_
  refine rx_swap2 ?_
  refine rx_push (w := (1 : B256)) rfl (by change 5 < 1024; decide) ?_
  refine rx_add' B256.add_comm (by change 4 < 1024; decide) ?_
  refine rx_swap2 ?_
  refine rx_swap1 ?_
  refine rx_push rfl (by change 5 < 1024; decide) ?_
  exact rx_jump loop_entry tail

/-- Inversion follows the same finite word witness and exposes the discarded final counter. -/
theorem fee_loop_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator finalOutput : B256}
    {iterations : Nat} {o : Outcome}
    (wordRun : WordFakeExponential.Run numerator denominator counter accumulator output iterations finalOutput)
    (run : SFunc.Run prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M G) t_004d_c0 o) :
    ∃ finalCounter G', SFunc.Run prog sevm
      (St b [finalOutput, 0, finalCounter, numerator, denominator] M G') t_0068_c0 o := by
  induction wordRun generalizing G with
  | stop counter output =>
    obtain ⟨G', run⟩ := header_inv run
    exact ⟨counter, G', run⟩
  | step active next ih =>
    obtain ⟨_, run⟩ := header_inv run
    simp only [ite_eq_right active] at run
    obtain ⟨_, run⟩ := body_inv run
    exact ih run

/-- Exact continuation transport for the word witness's body count. -/
theorem fee_loop_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator finalOutput : B256}
    {iterations : Nat} {o : Outcome}
    (wordRun : WordFakeExponential.Run numerator denominator counter accumulator output iterations finalOutput)
    (tail : ∀ finalCounter, SFunc.RunExact prog sevm
      (St b [finalOutput, 0, finalCounter, numerator, denominator] M G) t_0068_c0 o) :
    SFunc.RunExact prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + feeLoopGas iterations))
      t_004d_c0 o := by
  induction wordRun generalizing G with
  | stop counter output =>
    exact header_exact (tail counter)
  | @step counter accumulator output iterations finalOutput active next ih =>
    rw [feeLoopGas_succ, ← Nat.add_assoc, ← Nat.add_assoc]
    apply header_exact
    simp only [ite_eq_right active]
    exact body_exact (ih tail)

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
      (St b [] M (G + feeLoopGas iterations + userSetupGas sevm b)) t_001a_c0 o := by
  exact user_setup_exact hfork active (fee_loop_exact wordRun tail)

end Blanc.Lift.WithdrawalRequest
