import Blanc.Forward

/-!
# Forward steps under flat account-access pricing

The step keeps the actual code-size word and the complete pre-state base.
Flat pricing and disabled BAL recording are explicit capabilities, independent
of the fork-domain adapters used by the warm/cold forward steps.
-/

namespace Blanc

open Jaune

/-- Flat-priced `EXTCODESIZE` reads the actual pre-state code without warming
an address or changing account-read metadata when BAL recording is disabled. -/
theorem Ninst.runCompiled_extcodesize_flat
    {sevm : Sevm} {d : Devm} {x : B256} {S : List B256}
    {prices : FlatAccessGas} {G : Nat}
    (haccess : sevm.benvStat.rules.access = .flat prices)
    (hbal : sevm.benvStat.rules.bal = none)
    (hstack : d.stack = x :: S)
    (hgas : d.gasLeft =
      G + prices.extCode + sevm.benvStat.rules.gas.codeReadSurcharge)
    (hroom : S.length < 1024) :
    Ninst.RunCompiled sevm d (.reg .extcodesize)
      (d.setMach
        ⟨(d.getCode x.toAdr).size.toB256 :: S, d.memory, G, d.stateGas⟩) := by
  have hcost : prices.extCode + sevm.benvStat.rules.gas.codeReadSurcharge ≤ d.gasLeft := by
    omega
  have hleft : d.gasLeft -
      (prices.extCode + sevm.benvStat.rules.gas.codeReadSurcharge) = G := by
    omega
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  simp only [ExceptT.stM_eq, Rinst.runCore, haccess]
  rw [Devm.popToAdr_def, Devm.pop_eq_ok hstack]
  simp only [Functor.mapRev, Functor.map, Except.map, Prod.mapFst, Prod.map,
    id, bind, Except.bind]
  rw [chargeGas_eq_ok
    (devm := d.setMach ⟨S, d.memory, d.gasLeft, d.stateGas⟩) hcost]
  simp only [Devm.balReadAccount_of_bal_none hbal,
    Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stack_setMach, Devm.stateGas_setMach, hleft]
  rw [Devm.push_eq_ok
    (devm := d.setMach ⟨S, d.memory, G, d.stateGas⟩) hroom]
  rw [Devm.getCode_setMach]
  rfl

end Blanc
