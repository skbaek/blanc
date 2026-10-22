import Blanc.Lift.Usdc.ProxyCreation.Cert
import Blanc.Lift.ExactWalkOps
import Blanc.ForwardFlatAccess

/-!
# The original proxy constructor's code-size predicate

The registered entry at `0x27d` reads the actual code-size word and returns
its positive predicate, with the selected flat charge and exact stack image.
This fragment does not construct the whole constructor or a historical run.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune

/-- The registered `isContract` entry returns the predicate of the actual
code-size word, preserving its base and memory under flat access pricing. -/
theorem isContract_runExact
    {sevm : Sevm} {b : Devm} {x rho : B256} {S : List B256}
    {M : Mem} {G : Nat} {prices : FlatAccessGas}
    (haccess : sevm.benvStat.rules.access = .flat prices)
    (hbal : sevm.benvStat.rules.bal = none)
    (hroom : S.length + 6 ≤ 1024) :
    SFunc.RunExact cert.prog sevm
      (St b (x :: rho :: S) M
        (G + prices.extCode + sevm.benvStat.rules.gas.codeReadSurcharge + 47))
      t_027d_c4
      (.returned (St b
        ((if 0 < (b.getCode x.toAdr).size.toB256 then 1 else 0) :: S) M G)) := by
  unfold t_027d_c4
  apply rx_dest
  apply rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup (n := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (n := 2) rfl (by simp only [List.length_cons]; omega)
  refine SFunc.RunExact.next
    (devm' := St b ((b.getCode x.toAdr).size.toB256 :: 0 :: 0 :: x :: rho :: S)
      M (G + 37)) ?_ ?_
  · simpa only [St, Devm.getCode_setMach, Devm.setMach_setMach,
      Devm.memory_setMach, Devm.stateGas_setMach] using
      (Ninst.runCompiled_extcodesize_flat
        (d := St b (x :: 0 :: 0 :: x :: rho :: S) M
          (G + prices.extCode + sevm.benvStat.rules.gas.codeReadSurcharge + 37))
        (G := G + 37) haccess hbal rfl (by simp only [St.gasLeft]; omega)
        (by simp only [List.length_cons]; omega))
  · apply rx_swap1
    apply rx_pop
    apply rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_dup (n := 1) rfl (by simp only [List.length_cons]; omega)
    apply rx_gt (v := if 0 < (b.getCode x.toAdr).size.toB256 then 1 else 0)
      rfl (by simp only [List.length_cons]; omega)
    apply rx_swap2
    apply rx_pop
    apply rx_pop
    apply rx_swap2
    apply rx_swap1
    apply rx_pop
    exact rx_ret

end Blanc.Lift.Usdc.ProxyCreation
