import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Cert
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation.State
import Blanc.Lift.CreationOps
import Blanc.Lift.ExactWalkOps

/-! Gas-exact certified walk of the 0x6326 constructor, stopping at its actual `RETURN`. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation

open Jaune Blanc.Lift

abbrev prog : List SFunc := cert.prog

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  decide +kernel

/-- The unconditional constructor: `SSTORE(10, 31337)`, `JUMP` to the copier at `0x4489`,
`CODECOPY(0, 10, 0x4489 - 10)`, `RETURN(0, 0x4489 - 10)`. -/
theorem constructor_run (sevm : Sevm) (b : Devm) (G : Nat)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcode : sevm.code = creationCode) (hsentry : gCallStipend < G) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + constructorGas sevm b))
      (constructorPost sevm b G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have hgas : G + constructorGas sevm b =
      (((((((((((((((G + 3) + 3) + 3) + 3) + 3877) + 3) + 3) + 3) + 3) + 3) + 1) + 8) + 3)
        + sstoreCost sevm b 10 31337) + 3) + 3 := by
    unfold constructorGas
    omega
  rw [hgas]
  unfold t_0000_c0
  refine rx_push (w := (31337 : B256)) rfl (by decide) ?_
  refine rx_push (w := (10 : B256)) rfl (by decide) ?_
  refine rx_sstore hfork ?_ hstatic ?_
  · apply Nat.lt_of_lt_of_le hsentry
    omega
  · refine rx_push (w := (0x4489 : B256)) rfl (by decide) ?_
    refine rx_jump (g := t_4489_c1) (j := 1) rfl ?_
    unfold t_4489_c1
    refine rx_dest ?_
    refine rx_push (w := (10 : B256)) rfl (by decide) ?_
    refine rx_push (w := (0x4489 : B256)) rfl (by decide) ?_
    refine rx_sub' (v := (17535 : B256)) (by decide) (by decide) ?_
    refine rx_push (w := (10 : B256)) rfl (by decide) ?_
    refine rx_push (w := (0 : B256)) rfl (by decide) ?_
    refine rx_codecopy (c := 3877) (M' := constructorMemory) ?_ ?_ ?_
    · exact constructor_codecopy_charge _ _
    · rw [hcode]
      change Mem.empty.write 0 (creationCode.sliceD 10 17535 0) = constructorMemory
      rw [runtime_window]
      rfl
    · refine rx_push (w := (10 : B256)) rfl (by decide) ?_
      refine rx_push (w := (0x4489 : B256)) rfl (by decide) ?_
      refine rx_sub' (v := (17535 : B256)) (by decide) (by decide) ?_
      refine rx_push (w := (0 : B256)) rfl (by decide) ?_
      exact rx_return_any rfl (constructor_return_charge _ _)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation
