import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveFrame
import Blanc.Lift.Curve3Pool.ExactLivePremises
import Blanc.Lift.GasErasureRun

/-!
# `exchange`, exactly: the call data and the gas-independent schedule

The exact walk fixes, before any residual gas, the four coin calls' independently supplied
debits and canonical successors (`ExchangeExactCalls`) and prices every later stage at the
canonical base, memory and stack the stage cores expose. This module holds the data, the
premises connecting it to the shared exact profiles, and the congruences the walk needs to move
a stage's charge from an actual base to its canonical one. It proves nothing about a run.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## Exact profiles as relation-carrying call premises -/

/-- The relation an exact profile carries for one call: its debit and canonical successor. -/
def ExactCallRel (debit : Devm → List B256 → Mem → Nat) (next : Devm → List B256 → Mem → Devm) :
    Devm → List B256 → Mem → Nat → Devm → Prop :=
  fun b S M G d => G = d.gasLeft + debit b S M ∧ Devm.EqModGas d (next b S M)

/-- An exact static profile is a relation-carrying static premise. -/
theorem StaticWordCallProfile.okE {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {A : B256} {U : Nat} {ii is oi : B256} {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (h : StaticWordCallProfile sevm W W' t data A U ii is oi debit next) :
    StaticWordOkAtE sevm W W' t data A U ii is oi (ExactCallRel debit next) := by
  intro b S M G hW hU hG hin hroom
  obtain ⟨hc, d, hrun, hgas, hnext, out, hpost, hlen, hlt, hA, hW', hid⟩ :=
    h.sound b S M G ⟨hW, hU, hG, hin, hroom⟩
  exact ⟨d, out, hrun, hpost, hlen, hlt, hA, by omega, by omega, hW', hid, hgas, hnext⟩

/-- An exact mutable profile is a relation-carrying mutable premise. -/
theorem MutableCallProfile.okE {sevm : Sevm} {W W' : Devm → Prop} {t : B256} {data : Bytes}
    {ok : Bytes → Prop} {U : Nat} {ii is oi : B256} {debit : Devm → List B256 → Mem → Nat}
    {next : Devm → List B256 → Mem → Devm}
    (h : MutableCallProfile sevm W W' t data ok U ii is oi debit next) :
    MutCallOkAtE sevm W W' t data ok U ii is oi (ExactCallRel debit next) := by
  intro b S M G hW hU hG hin hroom
  obtain ⟨hc, d, hrun, hgas, hnext, hpost, hok, hlt, hstor, hW', hid⟩ :=
    h.sound b S M G ⟨hW, hU, hG, hin, hroom⟩
  exact ⟨d, hrun, hpost, hok, hlt, by omega, by omega, hstor, hW', hid, hgas, hnext⟩

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
