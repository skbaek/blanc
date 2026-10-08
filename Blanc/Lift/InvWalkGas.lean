import Blanc.Lift.InvWalkWorld

/-! Exact residual gas words in successful primitive GAS instructions. -/

namespace Blanc.Lift
open Jaune

/-- GAS pushes the successor's remaining gas, retaining every other machine field. -/
theorem ri_gas_remaining {sevm : Sevm} {b d : Devm} {S : List B256}
    {M : Mem} {G : Nat}
    (run : Ninst.Run sevm (St b S M G) (.reg .gas) d) :
    ∃ G', d = St b (G'.toB256 :: S) M G' := by
  obtain ⟨pc, step⟩ := of_run_reg run
  simp only [Rinst.run, Rinst.runCore] at step
  obtain ⟨charged, charge, push⟩ := Except.bind_eq_ok step
  have chargedEq := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas charge)
  have pushEq := Devm.eq_of_push_ok push
  refine ⟨charged.gasLeft, ?_⟩
  rw [pushEq, chargedEq]
  rfl

end Blanc.Lift
