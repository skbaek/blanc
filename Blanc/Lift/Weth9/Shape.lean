import Blanc.Lift.Hoare
import Blanc.Lift.Weth9.Lift

/-! # WETH9's call-shape facts

The kernel-checked shape of the deployed WETH9's synthetic program that the
function specifications rely on: the state-silent entry set, the wrapper
entries and the entry each wrapper calls, and the dispatcher's single call.
The generic checkers are `SilentSet` (`Blanc/Lift/Silent.lean`) and
`SFunc.silentCallsWith`/`SFunc.callRefs` (`Blanc/Lift/Hoare.lean`). -/

namespace Blanc.Lift

open Jaune Weth9

private instance : Inhabited SFunc := ⟨.undefined⟩

def Weth9.silentSet : List Nat := [2, 4, 5, 6, 7, 10, 12, 13, 14, 15, 16, 17]

def Weth9.wrapperSet : List Nat := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem Weth9.silentSet_closed :
    SilentSet Weth9.prog Weth9.silentSet = true := by
  decide +kernel

theorem Weth9.silentSet_no_calls :
    Weth9.silentSet.all (fun k => match Weth9.prog[k]? with
      | some g => g.silentCalls Weth9.silentSet 0
      | none => false) = true := by
  decide +kernel

theorem Weth9.entry0_silentCalls :
    (Weth9.prog[0]!).silentCallsWith Weth9.silentSet Weth9.wrapperSet 1 = true := by
  change t_0000_c0.silentCallsWith Weth9.silentSet Weth9.wrapperSet 1 = true
  decide +kernel

theorem Weth9.entry0_callRefs :
    t_0000_c0.callRefs.all (· ∈ [1]) = true := by
  decide +kernel

end Blanc.Lift
