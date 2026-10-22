import Blanc.Composition.Curve3Pool3CrvCheckpoint
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveModel

/-!
# U9(b): the model's `exchange(0, 1, 100, 0)` at the synthetic pool state

The pool's post state of a successful model `exchange` depends on its environment only through
`_A()` and the credited amount (`exchange_state`, read off `exchange_inv`).  At the synthetic
`poolState` (A = 100 with no ramp, so `_A()` is 100 at every timestamp; coin 0 is not the fee index,
so the credited amount is `dx`), every successful `exchange(0, 1, 100, 0)` — whatever the time, the
caller and the other answers — leaves balances `[1100, 1868, 3000]` and pushes 132 of coin 1
(`ex_model_step`), and the virtual-price `D` rises strictly from 22177905188247 to 22178770202300
(`ex_model_D`), by kernel evaluation of the checked Newton iterations.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Blanc.Lift Blanc.Lift.Curve3Pool Blanc.StableSwapNewton
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The state part of the model's `exchange` at `_A() = amp` and credited amount `D`, with the
amount pushed. -/
def exState (s : State) (amp D : Nat) (i j : Fin 3) : Option (V3 × Nat) := do
  let xp ← xpChk s.balances
  let x ← chkAdd (xp.get i) (← chkDiv (← chkMul D (rates.get i)) precision)
  let y ← getYChk amp i j x xp.get
  let dy ← chkSub (← chkSub (xp.get j) y) 1
  let dyFee ← chkDiv (← chkMul dy s.fee) feeDen
  let dyOut ← chkDiv (← chkMul (← chkSub dy dyFee) precision) (rates.get j)
  let adm ← chkDiv (← chkMul dyFee s.adminFee) feeDen
  let adm ← chkDiv (← chkMul adm precision) (rates.get j)
  let bi ← chkAdd (s.balances.get i) D
  let bj ← chkSub (← chkSub (s.balances.get j) dyOut) adm
  some ((s.balances.set i bi).set j bj, dyOut)

/-- **A successful `exchange` reads its environment, for its state and pushed amount, only through
`_A()` and the credited amount.** -/
theorem exchange_state {s : State} {e : Env} {i j : Fin 3} {dx minDy : Nat} {o : Out}
    (h : exchange s e i j dx minDy = some o) :
    ∃ amp D b out, aChk s e.time = some amp ∧ pullIn e i dx = some D ∧
      exState s amp D i j = some (b, out) ∧ o.state = { s with balances := b } ∧
      o.calls = [.pull i e.caller dx, .push j e.caller out] := by
  obtain ⟨-, xp, D, X, Y, x, amp, y, dy1, dy, dfp, fee, dop, outp, out, afp, adm0, aop, adm, bi,
    bj1, bj, hxp, hD, hX, hY, hx, hamp, hy, hdy1, hdy, hdfp, hfee, hdop, houtp, hout, -, hafp,
    hadm0, haop, hadm, hbi, hbj1, hbj, -, rfl⟩ := exchange_inv h
  refine ⟨amp, D, _, out, hamp, hD, ?_, rfl, rfl⟩
  unfold exState
  change (xpChk s.balances).bind _ = _
  rw [hxp, Option.bind_some]
  change (chkMul D (rates.get i)).bind _ = _
  rw [hX, Option.bind_some]
  change (chkDiv X precision).bind _ = _
  rw [hY, Option.bind_some]
  change (chkAdd (xp.get i) Y).bind _ = _
  rw [hx, Option.bind_some]
  change (getYChk amp i j x xp.get).bind _ = _
  rw [hy, Option.bind_some]
  change (chkSub (xp.get j) y).bind _ = _
  rw [hdy1, Option.bind_some]
  change (chkSub dy1 1).bind _ = _
  rw [hdy, Option.bind_some]
  change (chkMul dy s.fee).bind _ = _
  rw [hdfp, Option.bind_some]
  change (chkDiv dfp feeDen).bind _ = _
  rw [hfee, Option.bind_some]
  change (chkSub dy fee).bind _ = _
  rw [hdop, Option.bind_some]
  change (chkMul dop precision).bind _ = _
  rw [houtp, Option.bind_some]
  change (chkDiv outp (rates.get j)).bind _ = _
  rw [hout, Option.bind_some]
  change (chkMul fee s.adminFee).bind _ = _
  rw [hafp, Option.bind_some]
  change (chkDiv afp feeDen).bind _ = _
  rw [hadm0, Option.bind_some]
  change (chkMul adm0 precision).bind _ = _
  rw [haop, Option.bind_some]
  change (chkDiv aop (rates.get j)).bind _ = _
  rw [hadm, Option.bind_some]
  change (chkAdd (s.balances.get i) D).bind _ = _
  rw [hbi, Option.bind_some]
  change (chkSub (s.balances.get j) out).bind _ = _
  rw [hbj1, Option.bind_some]
  change (chkSub bj1 adm).bind _ = _
  rw [hbj, Option.bind_some]

/-- `_A()` at the synthetic pool is 100 at every timestamp (no ramp). -/
theorem poolState_aChk (t : Nat) : aChk poolState t = some 100 := by
  have h : ¬ t < poolState.futureATime := Nat.not_lt_zero t
  simp only [aChk, h, ↓reduceIte]
  rfl

/-- Coin 0 is not the fee index: a successful pull credits the amount itself. -/
theorem pullIn_zero {e : Env} {dx D : Nat} (h : pullIn e 0 dx = some D) : D = dx := by
  have h0 : (0 : Fin 3) ≠ feeIndex := by decide
  simp only [pullIn, h0, ↓reduceIte, req, Option.bind_eq_bind] at h
  split_ifs at h
  · simp only [Option.bind_some, Option.some.injEq] at h
    exact h.symm
  · simp only [Option.bind_none, reduceCtorEq] at h

/-- The synthetic pool's state after the swap. -/
def poolState1 : State := { poolState with balances := ⟨1100, 1868, 3000⟩ }

theorem exState_poolState : exState poolState 100 100 0 1 = some (⟨1100, 1868, 3000⟩, 132) := by
  decide +kernel

/-- **The model's swap at the synthetic pool**: every successful `exchange(0, 1, 100, 0)` leaves
`poolState1` and emits a pull of 100 of coin 0 and a push of 132 of coin 1, to and from the
caller. -/
theorem ex_model_step {e : Env} {o : Out} (h : exchange poolState e 0 1 100 0 = some o) :
    o.state = poolState1 ∧ o.calls = [.pull 0 e.caller 100, .push 1 e.caller 132] := by
  obtain ⟨amp, D, b, out, hamp, hD, hs, ho, hc⟩ := exchange_state h
  rw [poolState_aChk] at hamp
  obtain rfl := (Option.some.inj hamp).symm
  obtain rfl := pullIn_zero hD
  rw [exState_poolState] at hs
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hs)
  rw [← h2] at hc
  rw [← h1] at ho
  exact ⟨ho, hc⟩

theorem vD_poolState (t : Nat) : vDChk poolState t = some 22177905188247 := by
  unfold vDChk
  rw [poolState_aChk]
  decide +kernel

theorem vD_poolState1 (t : Nat) : vDChk poolState1 t = some 22178770202300 := by
  have h : aChk poolState1 t = some 100 := by
    have h : ¬ t < poolState1.futureATime := Nat.not_lt_zero t
    simp only [aChk, h, ↓reduceIte]
    rfl
  unfold vDChk
  rw [h]
  decide +kernel

/-- **`D` rises strictly across the swap**, at every timestamp. -/
theorem ex_model_D (t : Nat) :
    ∃ D D', vDChk poolState t = some D ∧ vDChk poolState1 t = some D' ∧ D < D' :=
  ⟨_, _, vD_poolState t, vD_poolState1 t, by decide⟩

end Blanc.Composition.Curve3Pool3CrvInstance
