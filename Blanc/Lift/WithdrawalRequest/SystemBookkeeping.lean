import Blanc.Lift.WithdrawalRequest.SystemBookkeepingState
import Blanc.Lift.PackedSha

/-! Certified metadata bookkeeping and the actual RETURN. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

private theorem pointer_join : prog[2]? = some t_01a0_c2 := rfl
private theorem excess_join : prog[3]? = some t_01cd_c3 := rfl
private theorem stores_join : prog[4]? = some t_01e8_c4 := rfl

private theorem pointer_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {count head tail : B256} {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St base [count, count, head, tail] memory gas) t_0183_c1 out) :
    sevm.isStatic = false ∧ ∃ gas', SFunc.Run prog sevm
      (St (systemPointerBase sevm base head tail count) [count] memory gas') t_01a0_c2 out := by
  obtain ⟨_, run⟩ := ric_dest run.cut
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := [head, count, count, tail]) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := systemAdvancedHead head count) rfl (ri_add step)
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := [tail, systemAdvancedHead head count, count,
    systemAdvancedHead head count]) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  by_cases drained : systemAdvancedHead head count = tail
  · simp only [B256.eqCheck, ite_eq_left drained.symm] at run
    rcases ric_branch run with ⟨flag, _, _⟩ | ⟨_, _, run⟩
    · exact False.elim ((by decide : (1 : B256) ≠ 0) flag)
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    have dynamic := ri_sstore_nonstatic fork step
    obtain ⟨_, rfl⟩ := ri_sstore fork step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_sstore fork step
    simp only [systemPointerBase, ite_eq_left drained]
    exact ⟨dynamic, _, run.uncut⟩
  · have different : tail ≠ systemAdvancedHead head count := Ne.symm drained
    simp only [B256.eqCheck, ite_eq_right different] at run
    rcases ric_branch run with ⟨_, _, run⟩ | ⟨flag, _, _⟩
    · obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_swap rfl step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, run⟩ := ric_next run
      have dynamic := ri_sstore_nonstatic fork step
      obtain ⟨_, rfl⟩ := ri_sstore fork step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, run⟩ := ric_jump (by intro h; cases h) pointer_join run
      simp only [systemPointerBase, ite_eq_right drained]
      exact ⟨dynamic, _, run.uncut⟩
    · exact False.elim (flag rfl)

private theorem pointer_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {count head tail : B256} {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < gas)
    (next : SFunc.RunExact prog sevm
      (St (systemPointerBase sevm base head tail count) [count] memory gas) t_01a0_c2 out) :
    SFunc.RunExact prog sevm (St base [count, count, head, tail] memory
      (gas + systemPointerGas sevm base head tail count)) t_0183_c1 out := by
  have branch : SFunc.RunExact prog sevm
      (St base [405, B256.eqCheck tail (systemAdvancedHead head count), count,
        systemAdvancedHead head count] memory
        (gas + (if systemAdvancedHead head count = tail then
          16 + sstoreCost sevm base 2 0 + sstoreCost sevm (afterSstore sevm base 2 0) 3 0
        else 17 + sstoreCost sevm base 2 (systemAdvancedHead head count)) + 10))
      (.branch t_018d_c1 t_0195_c1) out := by
    by_cases drained : systemAdvancedHead head count = tail
    · simp only [systemPointerBase, ite_eq_left drained] at next
      simp only [B256.eqCheck, ite_eq_left drained.symm, ite_eq_left drained]
      have gasEq : gas + (16 + sstoreCost sevm base 2 0 +
          sstoreCost sevm (afterSstore sevm base 2 0) 3 0) + 10 =
          gas + sstoreCost sevm (afterSstore sevm base 2 0) 3 0 + 3 + 2 +
            sstoreCost sevm base 2 0 + 3 + 2 + 2 + 3 + 1 + 10 := by omega
      rw [gasEq]
      apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
      unfold t_0195_c1
      apply rx_dest
      apply rx_swap1
      apply rx_pop
      apply rx_push0 (by change 1 < 1024; decide)
      apply rx_push rfl (by change 2 < 1024; decide)
      apply rx_sstore fork (by omega) dynamic
      apply rx_push0 (by change 1 < 1024; decide)
      apply rx_push rfl (by change 2 < 1024; decide)
      exact rx_sstore fork (by omega) dynamic next
    · have different : tail ≠ systemAdvancedHead head count := Ne.symm drained
      simp only [systemPointerBase, ite_eq_right drained] at next
      simp only [B256.eqCheck, ite_eq_right different, ite_eq_right drained]
      have gasEq : gas + (17 + sstoreCost sevm base 2 (systemAdvancedHead head count)) + 10 =
          gas + 8 + 3 + sstoreCost sevm base 2 (systemAdvancedHead head count) + 3 + 3 + 10 := by omega
      rw [gasEq]
      apply rx_branch_zero
      unfold t_018d_c1
      apply rx_swap1
      apply rx_push rfl (by change 2 < 1024; decide)
      apply rx_sstore fork (by omega) dynamic
      apply rx_push rfl (by change 1 < 1024; decide)
      exact rx_jump pointer_join next
  have gasEq : gas + systemPointerGas sevm base head tail count =
      gas + (if systemAdvancedHead head count = tail then
        16 + sstoreCost sevm base 2 0 + sstoreCost sevm (afterSstore sevm base 2 0) 3 0
      else 17 + sstoreCost sevm base 2 (systemAdvancedHead head count)) +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + 1 := by
    unfold systemPointerGas
    omega
  rw [gasEq]
  unfold t_0183_c1
  apply rx_dest
  apply rx_swap (S' := [head, count, count, tail]) rfl
  apply rx_add (by change 2 < 1024; decide)
  apply rx_dup1 (by change 3 < 1024; decide)
  apply rx_swap (S' := [tail, systemAdvancedHead head count, count, systemAdvancedHead head count]) rfl
  apply rx_eq rfl (by change 2 < 1024; decide)
  apply rx_push rfl (by change 3 < 1024; decide)
  exact branch

private theorem excess_flag (sevm : Sevm) (base : Devm) :
    B256.eqCheck (B256.eqCheck B256.max (systemOldExcess sevm base)) 0 =
      if systemOldExcess sevm base = B256.max then 0 else 1 := by
  by_cases inhibited : systemOldExcess sevm base = B256.max
  · simp only [B256.eqCheck, ite_eq_left inhibited.symm, ite_eq_left inhibited,
      ite_eq_right (by decide : (1 : B256) ≠ 0)]
  · simp only [B256.eqCheck, ite_eq_right (Ne.symm inhibited), ite_eq_right inhibited, ite_true]

private theorem excess_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {count : B256} {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St base [count] memory gas) t_01a0_c2 out) :
    ∃ gas', SFunc.Run prog sevm
      (St (systemExcessRead sevm base) [systemEffectiveExcess sevm base, count] memory gas')
      t_01cd_c3 out := by
  obtain ⟨_, run⟩ := ric_dest run.cut
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := B256.max)
    (by simpa only [B256.add_zero, List.replicate_succ, List.replicate_zero] using ones_add_zero)
    (ri_push step)
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  change SFunc.RunCut prog sevm []
    (St (systemExcessRead sevm base)
      [461, B256.eqCheck (B256.eqCheck B256.max (systemOldExcess sevm base)) 0,
        systemOldExcess sevm base, count] memory _) (.branchTo t_01cb_c2 3) (.done out) at run
  rw [excess_flag] at run
  by_cases inhibited : systemOldExcess sevm base = B256.max
  · simp only [ite_eq_left inhibited] at run
    rcases ric_branchTo (by intro h; cases h) excess_join run with ⟨_, _, run⟩ | ⟨flag, _, _⟩
    · obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      simp only [systemEffectiveExcess, ite_eq_left inhibited]
      exact ⟨_, run.uncut⟩
    · exact False.elim (flag rfl)
  · simp only [ite_eq_right inhibited] at run
    rcases ric_branchTo (by intro h; cases h) excess_join run with ⟨flag, _, _⟩ | ⟨_, _, run⟩
    · exact False.elim ((by decide : (1 : B256) ≠ 0) flag)
    · simp only [systemEffectiveExcess, ite_eq_right inhibited]
      exact ⟨_, run.uncut⟩

private theorem excess_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {count : B256} {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (next : SFunc.RunExact prog sevm
      (St (systemExcessRead sevm base) [systemEffectiveExcess sevm base, count] memory gas)
      t_01cd_c3 out) :
    SFunc.RunExact prog sevm (St base [count] memory (gas + systemExcessReadGas sevm base))
      t_01a0_c2 out := by
  have branch : SFunc.RunExact prog sevm
      (St (systemExcessRead sevm base)
        [461, B256.eqCheck (B256.eqCheck B256.max (systemOldExcess sevm base)) 0,
          systemOldExcess sevm base, count] memory
        (gas + (if systemOldExcess sevm base = B256.max then 4 else 0) + 10))
      (.branchTo t_01cb_c2 3) out := by
    rw [excess_flag]
    by_cases inhibited : systemOldExcess sevm base = B256.max
    · simp only [systemEffectiveExcess, ite_eq_left inhibited] at next
      simp only [ite_eq_left inhibited]
      have gasEq : gas + 4 + 10 = gas + 2 + 2 + 10 := by omega
      rw [gasEq]
      apply rx_branchTo_zero
      unfold t_01cb_c2
      exact rx_pop (rx_push0 (by change 1 < 1024; decide) next)
    · simp only [systemEffectiveExcess, ite_eq_right inhibited] at next
      simp only [ite_eq_right inhibited, Nat.add_zero]
      exact rx_branchTo_succ (by decide : (1 : B256) ≠ 0) excess_join next
  have gasEq : gas + systemExcessReadGas sevm base =
      gas + (if systemOldExcess sevm base = B256.max then 4 else 0) +
        10 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm base 0 + 2 + 1 := by
    unfold systemExcessReadGas
    omega
  rw [gasEq]
  unfold t_01a0_c2
  apply rx_dest
  apply rx_push0 (by change 1 < 1024; decide)
  apply rx_sload_sel fork (by change 1 < 1024; decide)
  apply rx_dup1 (by change 2 < 1024; decide)
  apply rx_push (w := B256.max)
    (by simpa only [B256.add_zero, List.replicate_succ, List.replicate_zero] using ones_add_zero)
    (by change 3 < 1024; decide)
  apply rx_eq rfl (by change 2 < 1024; decide)
  apply rx_iszero rfl (by change 2 < 1024; decide)
  apply rx_push rfl (by change 3 < 1024; decide)
  exact branch

private theorem count_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {count : B256} {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm
      (St (systemExcessRead sevm base) [systemEffectiveExcess sevm base, count] memory gas)
      t_01cd_c3 out) :
    ∃ gas', SFunc.Run prog sevm
      (St (systemCountRead sevm base) [systemNewExcess sevm base, count] memory gas') t_01e8_c4 out := by
  obtain ⟨_, run⟩ := ric_dest run.cut
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := systemEffectiveExcess sevm base) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := systemPendingCount sevm base) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := systemExcessSum sevm base) rfl (ri_add step)
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_gt step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  change SFunc.RunCut prog sevm []
    (St (systemCountRead sevm base)
      [482, B256.gtCheck (systemExcessSum sevm base) 2, systemPendingCount sevm base,
        systemEffectiveExcess sevm base, count] memory _)
      (.branch t_01db_c3 t_01e2_c3) (.done out) at run
  simp only [B256.gtCheck, GT.gt] at run
  by_cases positive : (2 : B256) < systemExcessSum sevm base
  · simp only [ite_eq_left positive] at run
    rcases ric_branch run with ⟨flag, _, _⟩ | ⟨_, _, run⟩
    · exact False.elim ((by decide : (1 : B256) ≠ 0) flag)
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_val (w := systemExcessSum sevm base) rfl (ri_add step)
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_sub step
    simp only [systemNewExcess, ite_eq_left positive]
    exact ⟨_, run.uncut⟩
  · simp only [ite_eq_right positive] at run
    rcases ric_branch run with ⟨_, _, run⟩ | ⟨flag, _, _⟩
    · obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, run⟩ := ric_jump (by intro h; cases h) stores_join run
      simp only [systemNewExcess, ite_eq_right positive]
      exact ⟨_, run.uncut⟩
    · exact False.elim (flag rfl)

private theorem count_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {count : B256} {out : Outcome} (fork : CoveredFork sevm.benvStat.fork)
    (next : SFunc.RunExact prog sevm
      (St (systemCountRead sevm base) [systemNewExcess sevm base, count] memory gas) t_01e8_c4 out) :
    SFunc.RunExact prog sevm
      (St (systemExcessRead sevm base) [systemEffectiveExcess sevm base, count] memory
        (gas + systemCountReadGas sevm base)) t_01cd_c3 out := by
  have branch : SFunc.RunExact prog sevm
      (St (systemCountRead sevm base)
        [482, B256.gtCheck (systemExcessSum sevm base) 2, systemPendingCount sevm base,
          systemEffectiveExcess sevm base, count] memory
        (gas + (if (2 : B256) < systemExcessSum sevm base then 13 else 17) + 10))
      (.branch t_01db_c3 t_01e2_c3) out := by
    simp only [B256.gtCheck, GT.gt]
    by_cases positive : (2 : B256) < systemExcessSum sevm base
    · simp only [systemNewExcess, ite_eq_left positive] at next
      simp only [ite_eq_left positive]
      have gasEq : gas + 13 + 10 = gas + 3 + 3 + 3 + 3 + 1 + 10 := by omega
      rw [gasEq]
      apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
      unfold t_01e2_c3
      apply rx_dest
      apply rx_add (by change 1 < 1024; decide)
      apply rx_push rfl (by change 2 < 1024; decide)
      apply rx_swap1
      exact rx_sub (by change 1 < 1024; decide) next
    · simp only [systemNewExcess, ite_eq_right positive] at next
      simp only [ite_eq_right positive]
      have gasEq : gas + 17 + 10 = gas + 8 + 3 + 2 + 2 + 2 + 10 := by omega
      rw [gasEq]
      apply rx_branch_zero
      unfold t_01db_c3
      apply rx_pop
      apply rx_pop
      apply rx_push0 (by change 1 < 1024; decide)
      apply rx_push rfl (by change 2 < 1024; decide)
      exact rx_jump stores_join next
  have gasEq : gas + systemCountReadGas sevm base =
      gas + (if (2 : B256) < systemExcessSum sevm base then 13 else 17) +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm (systemExcessRead sevm base) 1 + 3 + 1 := by
    unfold systemCountReadGas
    omega
  rw [gasEq]
  unfold t_01cd_c3
  apply rx_dest
  apply rx_push rfl (by change 2 < 1024; decide)
  apply rx_sload_sel fork (by change 2 < 1024; decide)
  apply rx_push rfl (by change 3 < 1024; decide)
  apply rx_dup3 (by change 4 < 1024; decide)
  apply rx_dup3 (by change 5 < 1024; decide)
  apply rx_add (by change 4 < 1024; decide)
  apply rx_gt rfl (by change 3 < 1024; decide)
  apply rx_push rfl (by change 4 < 1024; decide)
  exact branch

private theorem final_inv {sevm : Sevm} {base post : Devm} {memory : Mem} {gas : Nat}
    {count : B256} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm
      (St (systemCountRead sevm base) [systemNewExcess sevm base, count] memory gas)
      t_01e8_c4 (.halted post)) :
    ∃ gas', post = systemBookkeepingPost sevm base memory count gas' := by
  obtain ⟨_, run⟩ := ric_dest run.cut
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := systemReturnSize count) rfl (ri_mul step)
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  have actual := run.uncut
  clear run
  change SFunc.Run prog sevm
    (St (systemBookkeepingBase sevm base) [0, systemReturnSize count] memory _)
    (.last .return_) (.halted post) at actual
  unfold systemBookkeepingPost
  generalize baseEq : systemBookkeepingBase sevm base = finalBase at actual ⊢
  cases actual with
  | last actual =>
    simp only [Linst.Run, Linst.run] at actual
    rw [show (St finalBase [0, systemReturnSize count] memory _).popToNat =
      .ok (0, St finalBase [systemReturnSize count] memory _) from rfl] at actual
    simp only [Except.bind_ok] at actual
    rw [show (St finalBase [systemReturnSize count] memory _).popToNat =
      .ok ((systemReturnSize count).toNat, St finalBase [] memory _) from rfl] at actual
    simp only [Except.bind_ok] at actual
    rcases Except.bind_eq_ok actual with ⟨charged, burn, actual⟩
    have chargedState := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas burn)
    rw [chargedState] at actual
    cases actual
    refine ⟨charged.gasLeft, ?_⟩
    simp only [returnPost, St, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach]
    rfl

private theorem final_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {count : B256} (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < gas) :
    SFunc.RunExact prog sevm
      (St (systemCountRead sevm base) [systemNewExcess sevm base, count] memory
        (gas + systemFinalStoresGas sevm base memory count)) t_01e8_c4
      (.halted (systemBookkeepingPost sevm base memory count gas)) := by
  have terminal : SFunc.RunExact prog sevm
      (St (systemBookkeepingBase sevm base) [0, systemReturnSize count] memory
        (gas + systemReturnGas memory count)) (.last .return_)
      (.halted (systemBookkeepingPost sevm base memory count gas)) := by
    refine .last ?_
    show Linst.run sevm _ .return_ = .ok _
    have expansion : (St (systemBookkeepingBase sevm base) [0, systemReturnSize count] memory
        (gas + systemReturnGas memory count)).extCost
        [⟨(0 : B256).toNat, (systemReturnSize count).toNat⟩] = systemReturnGas memory count :=
      St.extCost_eq rfl _ _
    apply Linst.run_return_eq_ok rfl
    · rw [expansion]
      change systemReturnGas memory count ≤ gas + systemReturnGas memory count
      omega
    · rw [expansion]
      simp only [St.gasLeft, Nat.add_sub_cancel]
      simp only [St, Devm.setMach_setMach, Devm.memory_setMach, Devm.stateGas_setMach]
      rfl
  have gasEq : gas + systemFinalStoresGas sevm base memory count =
      gas + systemReturnGas memory count + 2 + 5 + 3 +
        sstoreCost sevm (systemExcessStore sevm base) 1 0 + 3 + 2 +
        sstoreCost sevm (systemCountRead sevm base) 0 (systemNewExcess sevm base) + 2 + 1 := by
    unfold systemFinalStoresGas
    omega
  rw [gasEq]
  unfold t_01e8_c4
  apply rx_dest
  apply rx_push0 (by change 2 < 1024; decide)
  apply rx_sstore fork (by omega) dynamic
  apply rx_push0 (by change 1 < 1024; decide)
  apply rx_push rfl (by change 2 < 1024; decide)
  apply rx_sstore fork (by omega) dynamic
  apply rx_push rfl (by change 1 < 1024; decide)
  apply rx_mul rfl (by decide)
  apply rx_push0 (by change 1 < 1024; decide)
  exact terminal

/-- Successful bookkeeping has exactly the sequential stores and actual RETURN
state, and its first store establishes the frame is non-static. -/
theorem systemBookkeeping_inv {sevm : Sevm} {base post : Devm} {memory : Mem} {gas : Nat}
    {count head tail : B256} (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St base [count, count, head, tail] memory gas)
      t_0183_c1 (.halted post)) :
    sevm.isStatic = false ∧ ∃ gas', post =
      systemBookkeepingPost sevm (systemPointerBase sevm base head tail count) memory count gas' := by
  obtain ⟨dynamic, _, run⟩ := pointer_inv fork run
  obtain ⟨_, run⟩ := excess_inv fork run
  obtain ⟨_, run⟩ := count_inv fork run
  exact ⟨dynamic, final_inv fork run⟩

/-- Construct all bookkeeping branches and the actual RETURN. Residual gas
above the stipend transparently suffices for every selected SSTORE sentry. -/
theorem systemBookkeeping_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {count head tail : B256} (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < gas) :
    SFunc.RunExact prog sevm (St base [count, count, head, tail] memory
      (gas + systemBookkeepingGas sevm base memory head tail count)) t_0183_c1
      (.halted (systemBookkeepingPost sevm (systemPointerBase sevm base head tail count)
        memory count gas)) := by
  have stores := final_exact (base := systemPointerBase sevm base head tail count)
    (memory := memory) (count := count) fork dynamic slack
  have counted := count_exact fork stores
  have excess := excess_exact fork counted
  have pointers := pointer_exact (base := base) (head := head) (tail := tail)
    fork dynamic (by omega) excess
  have gasEq : gas + systemBookkeepingGas sevm base memory head tail count =
      gas + systemFinalStoresGas sevm (systemPointerBase sevm base head tail count) memory count +
        systemCountReadGas sevm (systemPointerBase sevm base head tail count) +
        systemExcessReadGas sevm (systemPointerBase sevm base head tail count) +
        systemPointerGas sevm base head tail count := by
    simp only [systemBookkeepingGas]
    omega
  rw [gasEq]
  exact pointers

/-- The bounded word return size is the actual unwrapped 76-byte count. No
memory well-formedness or alignment shortcut is needed to name the real read. -/
theorem systemBookkeepingPost_output {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {count : B256} (cap : count.toNat ≤ 16) :
    (systemBookkeepingPost sevm base memory count gas).output =
      (memory.read 0 (76 * count.toNat)).1 := by
  change (memory.read (0 : B256).toNat (systemReturnSize count).toNat).1 = _
  rw [systemReturnSize_toNat cap]
  rfl

/-- The exact pointer-stage input for metadata bookkeeping after the queue loop. -/
def systemFramePointers (sevm : Sevm) (base : Devm) (memory : Mem) : Devm :=
  systemPointerBase sevm (systemQueuePost sevm base memory).base
    (systemHead sevm base) (systemTail sevm base) (systemCount sevm base)

/-- The actual halting state for the whole canonical word system frame. -/
def systemFramePost (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat) : Devm :=
  systemBookkeepingPost sevm (systemFramePointers sevm base memory)
    (systemQueuePost sevm base memory).memory (systemCount sevm base) gas

/-- Exact caller/setup/loop/bookkeeping selected cost, including RETURN
expansion. Allocation and cold/warm sums have not yet been reduced for E6. -/
def systemFrameGas (sevm : Sevm) (base : Devm) (memory : Mem) : Nat :=
  systemBookkeepingGas sevm (systemQueuePost sevm base memory).base
    (systemQueuePost sevm base memory).memory
    (systemHead sevm base) (systemTail sevm base) (systemCount sevm base) +
  systemQueueGas sevm base memory + dispatchGas

/-- Every successful canonical-code system frame refines the complete raw
word state, all sequential base effects and the actual RETURN. -/
theorem exec_system_frame {sevm : Sevm} {pre post : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (caller : sevm.caller = systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    sevm.isStatic = false ∧ ∃ gas, post = systemFramePost sevm pre pre.memory gas := by
  obtain ⟨_, run⟩ := exec_system_loop code fork stack caller exec
  rw [← systemLoop_post_tree_eq] at run
  exact systemBookkeeping_inv fork run

/-- Canonical lifted system construction has an actual halting outcome, not
an exit-continuation premise. The explicit slack is sufficient, not minimal. -/
theorem system_frame_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (caller : sevm.caller = systemAddress)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < gas) :
    SFunc.RunExact prog sevm (St base [] memory (gas + systemFrameGas sevm base memory))
      t_0000_c0 (.halted (systemFramePost sevm base memory gas)) := by
  have bookkeeping := systemBookkeeping_exact
    (base := (systemQueuePost sevm base memory).base)
    (memory := (systemQueuePost sevm base memory).memory)
    (head := systemHead sevm base) (tail := systemTail sevm base) (count := systemCount sevm base)
    fork dynamic slack
  rw [systemLoop_post_tree_eq] at bookkeeping
  have frame := system_loop_exact fork caller bookkeeping
  simpa only [systemFrameGas, systemFramePost, systemFramePointers, Nat.add_assoc] using frame

/-- Construction over the canonical installed bytes, with the same exact
selected gas and terminal state. No model or queue representation is assumed. -/
theorem exec_system_frame_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (caller : sevm.caller = systemAddress)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < gas) :
    Nonempty (Exec 0 sevm (St base [] memory (gas + systemFrameGas sevm base memory))
      (.ok (systemFramePost sevm base memory gas))) := by
  apply lift_exact cert_check jumps_ok (code.trans code_eq.symm) fork
  exact ⟨t_0000_c0, prog_root, system_frame_exact fork caller dynamic slack⟩

/-- The complete frame returns exactly the actual loop memory window. -/
theorem systemFramePost_output (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat) :
    (systemFramePost sevm base memory gas).output =
      ((systemQueuePost sevm base memory).memory.read 0
        (76 * (systemCount sevm base).toNat)).1 :=
  systemBookkeepingPost_output (systemCount_le sevm base)

end Blanc.Lift.WithdrawalRequest
