import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveFrame
import Blanc.Lift.Curve3Pool.ExactLivePremises
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityExactSchedule
import Blanc.Lift.GasErasureRun

/-!
# `exchange`, exactly: the call data and the gas-independent schedule

The exact walk fixes, before any residual gas, the four coin calls' independently supplied
debits and canonical successors (`ExchangeExactCalls`) and prices every later stage at the
canonical base, memory and stack the stage cores expose. The profiles enter the cores through
`StaticWordCallProfile.okE`/`MutableCallProfile.okE` with relation `ExactE`
(`RemoveLiquidityExactSchedule`). This module holds the data and the congruences the walk needs
to move a stage's charge from an actual base to its canonical one.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## `_A`'s and `get_y`'s charges at a base modulo gas -/

theorem aGas_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') :
    aGas sevm b = aGas sevm b' := by
  have h1 := Devm.EqModGas.afterSload sevm futureATimeSlot h
  have h2 := Devm.EqModGas.afterSload sevm futureASlot h1
  have h3 := Devm.EqModGas.afterSload sevm initialASlot h2
  unfold aGas
  rw [Devm.EqModGas.getStorVal_congr (t := sevm.currentTarget) (k := futureATimeSlot) h,
    Devm.EqModGas.getStorVal_congr (t := sevm.currentTarget) (k := futureASlot) h,
    Devm.EqModGas.getStorVal_congr (t := sevm.currentTarget) (k := initialASlot) h,
    Devm.EqModGas.sloadCost_congr sevm futureATimeSlot h,
    Devm.EqModGas.sloadCost_congr sevm futureASlot h1,
    Devm.EqModGas.sloadCost_congr sevm initialASlot h2,
    Devm.EqModGas.sloadCost_congr sevm initialATimeSlot h3]

theorem aBase_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b') :
    Devm.EqModGas (aBase sevm b) (aBase sevm b') := by
  have h1 := Devm.EqModGas.afterSload sevm futureATimeSlot h
  have h2 := Devm.EqModGas.afterSload sevm futureASlot h1
  have h3 := Devm.EqModGas.afterSload sevm initialASlot h2
  unfold aBase
  rw [Devm.EqModGas.getStorVal_congr (t := sevm.currentTarget) (k := futureATimeSlot) h]
  split
  · exact Devm.EqModGas.afterSload sevm initialATimeSlot h3
  · exact h2

theorem costGetY_congr (sevm : Sevm) {b b' : Devm} (h : Devm.EqModGas b b')
    (amp i j x x0 x1 x2 : Nat) :
    costGetY sevm b amp i j x x0 x1 x2 = costGetY sevm b' amp i j x x0 x1 x2 := by
  unfold costGetY
  rw [aGas_congr sevm h]

end Blanc.Lift.Curve3Pool
