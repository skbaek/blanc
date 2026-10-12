import Blanc.ForwardCall

/-! Re-pin bridge: the generic empty-return certificate awaits common-library hoisting. -/

namespace Blanc

open Jaune

theorem Func.runCompiledTo_push1Zero_return_empty
    (fs : List Func) (sevm : Sevm) (base : Devm) (G : Nat) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 6, base.stateGas⟩)
      (Ninst.push [0] (by decide) ::: Ninst.push [0] (by decide) ::: Func.last .return_)
      (.ok ((base.setMach ⟨[], Mem.empty, G, base.stateGas⟩).withOutput [])) := by
  func_run
  apply Func.runCompiledTo_return_word (i := 0) (sz := 0) (s := [])
    (e := 0) (G := G) (out := [])
  · rfl
  · exact Devm.extCost_empty_window
  · rw [Devm.gasLeft_setMach]
    dsimp only
    omega
  · rw [show B256.toNat (0 : B256) = 0 by decide]
    exact congrArg Prod.fst Devm.memRead_zero


end Blanc
