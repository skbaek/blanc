import Blanc.Lift.WithdrawalRequest.Dispatch
import Blanc.Lift.CreationOps
import Blanc.Lift.PackedSha

/-!
The user path's slot-zero inhibitor guard and initialization of the fee loop.
The selected SLOAD base retains storage-key warming. These walks stop before
the fee-loop header's JUMPDEST and make no claim about the loop or its output.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- The fixed instruction charge before the fee-loop header, excluding SLOAD. -/
def userSetupFixedGas : Nat :=
  gVerylow + gBase + gVerylow + gVerylow + gVerylow + gVerylow + gHigh +
    gVerylow + gVerylow + gLow + gVerylow + gVerylow + gBase

theorem userSetupFixedGas_eq : userSetupFixedGas = 46 := rfl

/-- The fixed prefix plus the selected cold/warm charge for slot zero. -/
def userSetupGas (sevm : Sevm) (b : Devm) : Nat :=
  userSetupFixedGas + sloadCost sevm b 0

/-- The pinned warm/cold slot-zero schedule, with the fixed prefix charge included. -/
theorem userSetupGas_eq (sevm : Sevm) (b : Devm) :
    userSetupGas sevm b =
      if (sevm.currentTarget, (0 : B256)) ∈ b.accessedStorageKeys then 146 else 2146 := by
  by_cases hw : (sevm.currentTarget, (0 : B256)) ∈ b.accessedStorageKeys
  · simp only [userSetupGas, userSetupFixedGas_eq, sloadCost, ite_eq_left hw, gasWarmAccess]
  · simp only [userSetupGas, userSetupFixedGas_eq, sloadCost, ite_eq_right hw, gasColdSload]

private theorem denominator_push : Bytes.toB256 [0x11] = (17 : B256) := rfl
private theorem zero_push : Bytes.toB256 [] = (0 : B256) := rfl
private theorem one_push : Bytes.toB256 [0x01] = (1 : B256) := rfl
private theorem inhibitor_push :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = B256.max := by
  simpa only [B256.add_zero, List.replicate_succ, List.replicate_zero] using ones_add_zero

/-- The explicit inhibitor arm is a REVERT tree, hence has no successful Outcome. -/
private theorem revert_tail_no_run {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run prog sevm d t_01f4_c0 o) : False := by
  exact run.cut.false_of_noOk rfl

private theorem init_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {excess : B256} {o : Outcome}
    (run : SFunc.Run prog sevm (St b [excess, 17] M G) t_0045_c0 o) :
    ∃ G', SFunc.Run prog sevm (St b [0, 17, 1, excess, 17] M G') t_004d_c0 o := by
  cases run with
  | next hp k =>
    obtain ⟨_, rfl⟩ := ri_push hp
    rw [one_push] at k
    cases k with
    | next hd k =>
      obtain ⟨_, rfl⟩ := ri_dup (w := 17) rfl hd
      cases k with
      | next hm k =>
        obtain ⟨_, rfl⟩ := ri_mul hm
        rw [show (17 : B256) * 1 = 17 from rfl] at k
        cases k with
        | next hp k =>
          obtain ⟨_, rfl⟩ := ri_push hp
          rw [one_push] at k
          cases k with
          | next hs k =>
            obtain ⟨_, rfl⟩ := ri_swap (S' := [17, 1, excess, 17]) rfl hs
            cases k with
            | next hp k =>
              obtain ⟨_, rfl⟩ := ri_push hp
              rw [zero_push] at k
              exact ⟨_, k⟩

private theorem init_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {excess : B256} {o : Outcome}
    (tail : SFunc.RunExact prog sevm (St b [0, 17, 1, excess, 17] M G) t_004d_c0 o) :
    SFunc.RunExact prog sevm (St b [excess, 17] M (G + 19)) t_0045_c0 o := by
  have hgas : G + 19 = G + 2 + 3 + 3 + 5 + 3 + 3 := by
    simp only [Nat.add_assoc]
  rw [hgas]
  unfold t_0045_c0
  refine rx_push one_push (by change 2 < 1024; decide) ?_
  refine rx_dup3 (by change 3 < 1024; decide) ?_
  refine rx_mul (v := 17) rfl (by change 2 < 1024; decide) ?_
  refine rx_push one_push (by change 3 < 1024; decide) ?_
  refine rx_swap1 ?_
  exact rx_push0 (by change 4 < 1024; decide) tail

/-- Success excludes the inhibitor and reaches the initialized loop with slot zero warmed. -/
theorem user_setup_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St b [] M G) t_001a_c0 o) :
    b.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ G', SFunc.Run prog sevm
      (St (afterSload sevm b 0) [0, 17, 1, b.getStorVal sevm.currentTarget 0, 17] M G')
      t_004d_c0 o := by
  cases run with
  | next hp k =>
    obtain ⟨_, rfl⟩ := ri_push hp
    rw [denominator_push] at k
    cases k with
    | next hp k =>
      obtain ⟨_, rfl⟩ := ri_push hp
      rw [zero_push] at k
      cases k with
      | next hl k =>
        obtain ⟨_, rfl⟩ := ri_sload hfork hl
        cases k with
        | next hd k =>
          obtain ⟨_, rfl⟩ := ri_dup (w := b.getStorVal sevm.currentTarget 0) rfl hd
          cases k with
          | next hp k =>
            obtain ⟨_, rfl⟩ := ri_push hp
            rw [inhibitor_push] at k
            cases k with
            | next he k =>
              obtain ⟨_, rfl⟩ := ri_eq he
              cases k with
              | next hp k =>
                obtain ⟨_, rfl⟩ := ri_push hp
                cases k with
                | zero _ pop tail =>
                  have flag := (St.of_pop2 pop).2.1
                  have active : b.getStorVal sevm.currentTarget 0 ≠ B256.max := by
                    intro inhibited
                    simp only [inhibited, B256.eqCheck, ite_true] at flag
                    exact (by decide : (1 : B256) ≠ 0) flag
                  exact ⟨active, init_inv ((St.of_pop2 pop).2.2 ▸ tail)⟩
                | succ _ _ _ _ tail => exact False.elim (revert_tail_no_run tail)

/-- A non-inhibited exact loop continuation transports through the complete user setup. -/
theorem user_setup_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (hfork : CoveredFork sevm.benvStat.fork)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (tail : SFunc.RunExact prog sevm
      (St (afterSload sevm b 0) [0, 17, 1, b.getStorVal sevm.currentTarget 0, 17] M G)
      t_004d_c0 o) :
    SFunc.RunExact prog sevm (St b [] M (G + userSetupGas sevm b)) t_001a_c0 o := by
  have hgas : G + userSetupGas sevm b =
      G + 19 + 10 + 3 + 3 + 3 + 3 + sloadCost sevm b 0 + 2 + 3 := by
    simp only [userSetupGas, userSetupFixedGas_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    congr 1
    simp only [← Nat.add_assoc]
  rw [hgas]
  unfold t_001a_c0
  refine rx_push denominator_push (by decide) ?_
  refine rx_push0 (by change 1 < 1024; decide) ?_
  refine rx_sload_sel hfork (by change 1 < 1024; decide) ?_
  refine rx_dup1 (by change 2 < 1024; decide) ?_
  refine rx_push inhibitor_push (by change 3 < 1024; decide) ?_
  refine rx_eq (v := 0) ?_ (by change 2 < 1024; decide) ?_
  · simp only [B256.eqCheck, ite_eq_right (Ne.symm active)]
  · refine rx_push rfl (by change 3 < 1024; decide) ?_
    exact rx_branch_zero (init_exact tail)

/-- A successful canonical user execution reaches the non-inhibited initialized fee loop. -/
theorem exec_user_setup {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = Blanc.withdrawalRequestCode)
    (hfork : CoveredFork sevm.benvStat.fork) (hstack : pre.stack = [])
    (user : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ G, SFunc.Run prog sevm
      (St (afterSload sevm pre 0) [0, 17, 1, pre.getStorVal sevm.currentTarget 0, 17]
        pre.memory G) t_004d_c0 (.halted post) := by
  obtain ⟨_, run⟩ := exec_dispatch hcode hfork hstack exec
  simp only [dispatchTail, ite_eq_right user] at run
  exact user_setup_inv hfork run

end Blanc.Lift.WithdrawalRequest
