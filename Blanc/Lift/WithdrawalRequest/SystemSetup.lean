import Blanc.Lift.WithdrawalRequest.Dispatch
import Blanc.ForwardStorageAccess
import Blanc.Lift.CreationOps

/-!
# Certified system queue-loop setup

Only the prefix from 0xcb through the cap branch and zero loop index is
covered. The actual modulo-word difference is capped at 16 without logical
pointer or reachability assumptions. No loop body or bookkeeping is covered.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

def systemHead (sevm : Sevm) (base : Devm) : B256 :=
  base.getStorVal sevm.currentTarget 2

def systemTail (sevm : Sevm) (base : Devm) : B256 :=
  base.getStorVal sevm.currentTarget 3

def systemDifference (sevm : Sevm) (base : Devm) : B256 :=
  systemTail sevm base - systemHead sevm base

def systemCount (sevm : Sevm) (base : Devm) : B256 :=
  if (systemDifference sevm base).toNat < 16 then systemDifference sevm base else 16

/-- Exact meta-state after reading tail first, then head. -/
def systemSetupBase (sevm : Sevm) (base : Devm) : Devm :=
  afterSload sevm (afterSload sevm base 3) 2

theorem systemSetupBase_keys (sevm : Sevm) (base : Devm) :
    (systemSetupBase sevm base).accessedStorageKeys =
      sloadAccessedStorageKeys sevm.currentTarget
        (sloadAccessedStorageKeys sevm.currentTarget base.accessedStorageKeys 3) 2 := by
  simp only [systemSetupBase, afterSload_accessedStorageKeys]

theorem systemCount_toNat (sevm : Sevm) (base : Devm) :
    (systemCount sevm base).toNat = min 16 (systemDifference sevm base).toNat := by
  by_cases h : (systemDifference sevm base).toNat < 16
  · rw [systemCount, ite_eq_left h, Nat.min_eq_right (Nat.le_of_lt h)]
  · rw [systemCount, ite_eq_right h, Nat.min_eq_left (Nat.le_of_not_gt h)]
    rfl

theorem systemCount_le (sevm : Sevm) (base : Devm) :
    (systemCount sevm base).toNat ≤ 16 := by
  rw [systemCount_toNat]
  exact Nat.min_le_left _ _

/-- Two JUMPDESTs, nine very-low instructions, JUMPI, and PUSH0. -/
def systemSetupFixedGas : Nat := gJumpdest + 9 * gVerylow + gHigh + gJumpdest + gBase

theorem systemSetupFixedGas_eq : systemSetupFixedGas = 41 := rfl

/-- The capped fall-through adds POP and a nonempty PUSH of 16. -/
def systemSetupGas (sevm : Sevm) (base : Devm) : Nat :=
  sloadCost sevm base 3 + sloadCost sevm (afterSload sevm base 3) 2 +
    systemSetupFixedGas +
    if (systemDifference sevm base).toNat < 16 then 0 else gBase + gVerylow

private theorem setup_gt (sevm : Sevm) (base : Devm) :
    B256.gtCheck 16 (systemDifference sevm base) =
      if (systemDifference sevm base).toNat < 16 then 1 else 0 := by
  simp only [B256.gtCheck, GT.gt, B256.lt_iff_toNat_lt_toNat]
  rfl

private theorem prog_setup_join : prog[1]? = some t_00df_c1 := rfl

/-- A successful system prefix reaches the loop with the exact warmed base,
unchanged memory, zero index, capped count, head, and tail. -/
theorem systemSetup_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St base [] memory gas) t_00cb_c0 out) :
    ∃ gas', SFunc.Run prog sevm
      (St (systemSetupBase sevm base)
        [0, systemCount sevm base, systemHead sevm base, systemTail sevm base] memory gas')
      t_00e1_c1 out := by
  cases run with
  | dest burn run =>
    rw [St.of_burn burn] at run
    cases run with
    | next hp run =>
      obtain ⟨_, rfl⟩ := ri_push hp
      cases run with
      | next hs run =>
        obtain ⟨_, rfl⟩ := ri_sload fork hs
        cases run with
        | next hp run =>
          obtain ⟨_, rfl⟩ := ri_push hp
          cases run with
          | next hs run =>
            obtain ⟨_, rfl⟩ := ri_sload fork hs
            have headRead : (afterSload sevm base (Bytes.toB256 [3])).getStorVal
                sevm.currentTarget (Bytes.toB256 [2]) = systemHead sevm base :=
              congrArg (fun storage : Stor => storage.get 2)
                (afterSload_getStor sevm base 3 sevm.currentTarget)
            rw [headRead] at run
            cases run with
            | next hd run =>
              obtain ⟨_, rfl⟩ := ri_dup rfl hd
              cases run with
              | next hd run =>
                obtain ⟨_, rfl⟩ := ri_dup rfl hd
                cases run with
                | next hs run =>
                  obtain ⟨_, rfl⟩ := ri_sub hs
                  cases run with
                  | next hd run =>
                    obtain ⟨_, rfl⟩ := ri_dup rfl hd
                    cases run with
                    | next hp run =>
                      obtain ⟨_, rfl⟩ := ri_push hp
                      cases run with
                      | next hg run =>
                        obtain ⟨_, rfl⟩ := ri_gt hg
                        cases run with
                        | next hp run =>
                          obtain ⟨_, rfl⟩ := ri_push hp
                          change SFunc.Run prog sevm (St (systemSetupBase sevm base)
                            [223, B256.gtCheck 16 (systemDifference sevm base), systemDifference sevm base,
                              systemHead sevm base, systemTail sevm base] memory _)
                            (.branchTo t_00dc_c0 1) out at run
                          rw [setup_gt] at run
                          by_cases h : (systemDifference sevm base).toNat < 16
                          · simp only [systemCount, ite_eq_left h] at run ⊢
                            cases run with
                            | toZero _ pop _ =>
                              exact False.elim ((by decide : (1 : B256) ≠ 0) (St.of_pop2 pop).2.1)
                            | toSucc _ _ _ lookup pop run =>
                              rw [prog_setup_join] at lookup
                              cases lookup
                              rw [(St.of_pop2 pop).2.2] at run
                              cases run with
                              | dest burn run =>
                                rw [St.of_burn burn] at run
                                cases run with
                                | next hp run =>
                                  obtain ⟨_, rfl⟩ := ri_push hp
                                  exact ⟨_, run⟩
                          · simp only [systemCount, ite_eq_right h] at run ⊢
                            cases run with
                            | toSucc _ _ nz _ pop _ =>
                              exact False.elim (nz (St.of_pop2 pop).2.1.symm)
                            | toZero _ pop run =>
                              rw [(St.of_pop2 pop).2.2] at run
                              cases run with
                              | next hp run =>
                                obtain ⟨_, rfl⟩ := ri_pop hp
                                cases run with
                                | next hp run =>
                                  obtain ⟨_, rfl⟩ := ri_push hp
                                  cases run with
                                  | dest burn run =>
                                    rw [St.of_burn burn] at run
                                    cases run with
                                    | next hp run =>
                                      obtain ⟨_, rfl⟩ := ri_push hp
                                      exact ⟨_, run⟩

/-- An exact loop continuation constructs precisely the setup charge. -/
theorem systemSetup_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (loop : SFunc.RunExact prog sevm
      (St (systemSetupBase sevm base)
        [0, systemCount sevm base, systemHead sevm base, systemTail sevm base] memory gas)
      t_00e1_c1 out) :
    SFunc.RunExact prog sevm (St base [] memory (gas + systemSetupGas sevm base)) t_00cb_c0 out := by
  have branch : SFunc.RunExact prog sevm
      (St (systemSetupBase sevm base)
        [223, B256.gtCheck 16 (systemDifference sevm base), systemDifference sevm base,
          systemHead sevm base, systemTail sevm base] memory
        (gas + (if (systemDifference sevm base).toNat < 16 then 3 else 8) + 10))
      (.branchTo t_00dc_c0 1) out := by
    rw [setup_gt]
    by_cases h : (systemDifference sevm base).toNat < 16
    · simp only [systemCount, ite_eq_left h] at loop
      simp only [ite_eq_left h]
      refine rx_branchTo_succ (by decide) prog_setup_join ?_
      unfold t_00df_c1
      exact rx_dest (rx_push0 (by change 3 < 1024; decide) loop)
    · simp only [systemCount, ite_eq_right h] at loop
      simp only [ite_eq_right h]
      refine rx_branchTo_zero ?_
      unfold t_00dc_c0 t_00df_c1
      exact rx_pop (rx_push rfl (by change 2 < 1024; decide)
        (rx_dest (rx_push0 (by change 3 < 1024; decide) loop)))
  have gasEq : gas + systemSetupGas sevm base =
      gas + (if (systemDifference sevm base).toNat < 16 then 3 else 8) +
        10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 +
        sloadCost sevm (afterSload sevm base 3) 2 + 3 + sloadCost sevm base 3 + 3 + 1 := by
    unfold systemSetupGas
    rw [systemSetupFixedGas_eq]
    by_cases h : (systemDifference sevm base).toNat < 16
    · simp only [ite_eq_left h]
      omega
    · simp only [ite_eq_right h, gBase, gVerylow]
      omega
  rw [gasEq]
  unfold t_00cb_c0
  refine rx_dest ?_
  refine rx_push rfl (by decide) ?_
  refine rx_sload_sel fork (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_sload_sel fork (by change 1 < 1024; decide) ?_
  have headRead : (afterSload sevm base (Bytes.toB256 [3])).getStorVal
      sevm.currentTarget (Bytes.toB256 [2]) = systemHead sevm base :=
    congrArg (fun storage : Stor => storage.get 2)
      (afterSload_getStor sevm base 3 sevm.currentTarget)
  rw [headRead]
  refine rx_dup1 (by change 2 < 1024; decide) ?_
  refine rx_dup3 (by change 3 < 1024; decide) ?_
  refine rx_sub (by change 2 < 1024; decide) ?_
  refine rx_dup1 (by change 3 < 1024; decide) ?_
  refine rx_push rfl (by change 4 < 1024; decide) ?_
  refine rx_gt rfl (by change 3 < 1024; decide) ?_
  refine rx_push rfl (by change 4 < 1024; decide) ?_
  exact branch

end Blanc.Lift.WithdrawalRequest
