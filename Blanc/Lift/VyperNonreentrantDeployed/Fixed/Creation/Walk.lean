import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation.Cert
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation.State
import Blanc.Lift.CreationOps
import Blanc.Lift.CheckAssembly

/-! Gas-exact certified walk of the 0x847e constructor on its zero-value route, stopping at
its actual `RETURN`. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation

open Jaune Blanc.Lift

abbrev prog : List SFunc := cert.prog

theorem jumps_0 : jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true :=
  Cert.jumpsOk_singleton jumps_0

/-- The zero-value constructor: `CALLVALUE` is zero so the `JUMPI` to the rejection at
`0x47ac` falls through, `SSTORE(1, 1)`, `CODECOPY(0, 27, 18320)`, `RETURN(0, 18320)`. -/
theorem constructor_run (sevm : Sevm) (b : Devm) (G : Nat)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hcode : sevm.code = creationCode) (hvalue : sevm.value = 0) (hsentry : gCallStipend < G) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + constructorGas sevm b))
      (constructorPost sevm b G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have hgas : G + constructorGas sevm b =
      ((((((((((((G + 3) + 3) + 4082) + 3) + 3) + 3) + sstoreCost sevm b 1 1) + 3) + 3) + 10)
        + 3) + 2) := by
    unfold constructorGas
    omega
  rw [hgas]
  unfold t_0000_c0 t_0005_c0
  refine rx_callvalue (by decide) ?_
  rw [hvalue]
  refine rx_push (w := (0x47ac : B256)) rfl (by decide) ?_
  refine rx_branch_zero ?_
  refine rx_push (w := (1 : B256)) rfl (by decide) ?_
  refine rx_push (w := (1 : B256)) rfl (by decide) ?_
  refine rx_sstore hfork ?_ hstatic ?_
  · apply Nat.lt_of_lt_of_le hsentry
    omega
  · refine rx_push (w := (18320 : B256)) rfl (by decide) ?_
    refine rx_push (w := (27 : B256)) rfl (by decide) ?_
    refine rx_push (w := (0 : B256)) rfl (by decide) ?_
    refine rx_codecopy (c := 4082) (M' := constructorMemory) ?_ ?_ ?_
    · exact constructor_codecopy_charge _ _
    · rw [hcode]
      change Mem.empty.write 0 (creationCode.sliceD 27 18320 0) = constructorMemory
      rw [runtime_window]
      rfl
    · refine rx_push (w := (18320 : B256)) rfl (by decide) ?_
      refine rx_push (w := (0 : B256)) rfl (by decide) ?_
      exact rx_return_any rfl (constructor_return_charge _ _)

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation
