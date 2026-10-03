import Blanc.Lift.WithdrawalRequest.Creation.Cert
import Blanc.Lift.WithdrawalRequest.Creation.State
import Blanc.Lift.CreationOps

/-! Gas-exact certified constructor walk, stopping at its actual RETURN. -/

namespace Blanc.Lift.WithdrawalRequest.Creation

open Jaune Blanc.Lift

abbrev prog : List SFunc := cert.prog

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  rfl

theorem constructor_run (sevm : Sevm) (b : Devm) (G : Nat)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcode : sevm.code = creationCode) (hsentry : gCallStipend < G) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + constructorGas sevm b))
      (constructorPost sevm b G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have hgas : G + constructorGas sevm b =
      ((((((G + 2) + 99) + 2) + 3) + 3) + 3 + sstoreCost sevm b 0 B256.max) + 2 + 3 := by
    rw [Nat.add_right_comm _ (sstoreCost sevm b 0 B256.max) 2,
      Nat.add_right_comm _ (sstoreCost sevm b 0 B256.max) 3]
    simp only [constructorGas, ← Nat.add_assoc]

  rw [hgas]
  unfold t_0000_c0
  refine rx_push (w := B256.max) rfl (by decide) ?_
  refine rx_push0 (by change 1 < 1024; decide) ?_
  refine rx_sstore hfork ?_ hstatic ?_
  · apply Nat.lt_of_lt_of_le hsentry
    simp only [Nat.add_assoc]
    exact Nat.le_add_right G _
  · refine rx_push (w := (504 : B256)) rfl (by decide) ?_
    refine rx_dup1 (by change 1 < 1024; decide) ?_
    refine rx_push (w := (45 : B256)) rfl (by decide) ?_
    refine rx_push0 (by change 3 < 1024; decide) ?_
    refine rx_codecopy (c := 99) (M' := constructorMemory) ?_ ?_ ?_
    · exact constructor_codecopy_charge _ _
    · rw [hcode]
      change Mem.empty.write 0 (creationCode.sliceD 45 504 0) = constructorMemory
      rw [runtime_window]
      rfl
    · refine rx_push0 (by change 1 < 1024; decide) ?_
      exact rx_return_any rfl (constructor_return_charge _ _)

end Blanc.Lift.WithdrawalRequest.Creation
