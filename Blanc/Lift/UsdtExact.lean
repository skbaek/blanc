import Blanc.Lift.UsdtForwardLaws
import Blanc.Lift.WalkCostExact
import Blanc.Lift.CallProfileTransport
import Blanc.Lift.StaticGasTransport

/-!
# USDT: the exact costs of `transfer`, `transferFrom` and `balanceOf`

`UsdtForward`'s walks synthesize their charges; here each is a closed sum. USDT's charge depends on storage:
`feeG` on whether the fee's cap binds, `mvG` on whether a fee is due, `e10G` on whether the allowance is
unlimited. `e61G` is SafeMath's early exit on a zero amount.
-/

namespace Blanc.Lift.Usdt

open Jaune Blanc Blanc.Lift
open Blanc.Lift.AccumulatedWalk

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-! ## The closed sums -/

/-- A move's two reads and two writes, crediting `a`, at their states. -/
def mvCoreG (s : Sevm) (b : Devm) (v a t r : B256) : Nat :=
  sloadCost s b (ky r) + sstoreCost s (afterSload s b (ky r)) (ky r) (b.getStorVal s.currentTarget (ky r) - v) +
    sloadCost s (mvDebited s b v r) (ky t) +
    sstoreCost s (afterSload s (mvDebited s b v r) (ky t)) (ky t)
      ((mvDebited s b v r).getStorVal s.currentTarget (ky t) + a)

/-- The owner's cut's three reads of slot 0, its read and write of the owner's entry, at their states. -/
def ownG (s : Sevm) (C : Devm) (f : B256) : Nat :=
  sloadCost s C (Bytes.toB256 [0]) + sloadCost s (afterSload s C (Bytes.toB256 [0])) (oky s C) +
    sloadCost s (ownRead s C) (Bytes.toB256 [0]) +
    sstoreCost s (afterSload s (ownRead s C) (Bytes.toB256 [0])) (oky s (ownRead s C))
      ((afterSload s C (Bytes.toB256 [0])).getStorVal s.currentTarget (oky s C) + f) +
    sloadCost s (ownCredited s C f) (Bytes.toB256 [0])

/-- A move by arm: with no fee `lz` over its storage charges, with one `ln` and the owner's cut. -/
def mvG (lz ln : Nat) (s : Sevm) (b : Devm) (v f t r : B256) : Nat :=
  if f = 0 then lz + mvCoreG s b v (v - f) t r
  else ln + mvCoreG s b v (v - f) t r + ownG s (mvCredited s b v (v - f) t r) f

/-- SafeMath `mul`'s cost: an early exit on a zero left operand. -/
def e61G (y : B256) : Nat := if y = 0 then 72 else 138

/-- The fee rule's cost: `basisPointsRate` and `maximumFee`, the arithmetic, and the second read when the cap binds. -/
noncomputable def feeG (s : Sevm) (b : Devm) (v : B256) : Nat :=
  sloadCost s b (Bytes.toB256 [3]) + e61G v + sloadCost s (afterSload s b (Bytes.toB256 [3])) (Bytes.toB256 [4]) +
    if Capped (Devm.getStor b s.currentTarget) v
    then 236 + sloadCost s (afterSload s (afterSload s b (Bytes.toB256 [3])) (Bytes.toB256 [4])) (Bytes.toB256 [4])
    else 228

/-- `BasicToken.transfer`, from entry 60. -/
noncomputable def e60G (s : Sevm) (b : Devm) (v t : B256) : Nat :=
  feeG s b v + mvG 2586 4830 s (feeBase s b v) v (feeOf (Devm.getStor b s.currentTarget) v) t s.caller.toB256

/-- The gate's three reads. -/
def gateG (s : Sevm) (b : Devm) (a : B256) : Nat :=
  sloadCost s b (Bytes.toB256 [0]) +
    sloadCost s (afterSload s b (Bytes.toB256 [0])) (mapSlot (m20 &&& (m20 &&& a)) (Bytes.toB256 [6])) +
    sloadCost s (afterSload s (afterSload s b (Bytes.toB256 [0])) (mapSlot (m20 &&& (m20 &&& a)) (Bytes.toB256 [6])))
      (Bytes.toB256 [10])

/-- **`transfer`'s exact cost.** -/
noncomputable def xferG (s : Sevm) (b : Devm) : Nat :=
  1049 + gateG s b s.caller.toB256 + e60G s (gateBase s b s.caller.toB256) (xVal s) (xTo s)

/-- `transferFrom`'s allowance step and move, by whether the allowance is unlimited. -/
def e10G (s : Sevm) (b : Devm) (a v f t r : B256) : Nat :=
  if a = maxUint then 26 + mvG 2593 4838 s b v f t r
  else 320 + sstoreCost s b (ak r s.caller.toB256) (a - v) +
    mvG 2593 4838 s (afterSstore s b (ak r s.caller.toB256) (a - v)) v f t r

/-- `StandardToken.transferFrom`, from entry 56. -/
noncomputable def e56G (s : Sevm) (b : Devm) (v t r : B256) : Nat :=
  190 + sloadCost s b (ak r s.caller.toB256) + feeG s (alBase s b r) v +
    e10G s (feeBase s (alBase s b r) v) (b.getStorVal s.currentTarget (ak r s.caller.toB256)) v
      (feeOf (Devm.getStor b s.currentTarget) v) t r

/-- **`transferFrom`'s exact cost.** -/
noncomputable def pullG (s : Sevm) (b : Devm) : Nat :=
  755 + gateG s b (pSrc s) + e56G s (gateBase s b (pSrc s)) (pVal s) (pTo s) (pSrc s)

/-- **`balanceOf`'s exact cost.** -/
def balG (s : Sevm) (b : Devm) : Nat :=
  831 + sloadCost s b (Bytes.toB256 [10]) + sloadCost s (afterSload s b (Bytes.toB256 [10])) (ky (bHolder s))

section Charges

variable (sevm : Sevm) (b : Devm) (v t r ret a a' p q f f0 x y : B256) (S : List B256) (M : Mem)

theorem e50W_eq : (e50W sevm b x y ret S M).1 = 68 := by unfold e50W; dsimp only
theorem e51W_eq : (e51W sevm b x y ret S M).1 = 81 := by unfold e51W; dsimp only
theorem e63W_eq : (e63W sevm b x y ret S M).1 = 74 := by unfold e63W; dsimp only

theorem e61W_eq : (e61W sevm b x y ret S M).1 = e61G y := by
  unfold e61W e61G
  by_cases hy : y = 0
  · rw [dite_eq_left hy, ite_eq_left hy]; unfold e61ZW; dsimp only
  · rw [dite_eq_right hy, ite_eq_right hy]; unfold e61NW; dsimp only

theorem e13OW_eq : (e13OW sevm b p a f v t ret S M).1 = 4094 + ownG sevm b f := by
  unfold e13OW ownG ownCredited ownRead; dsimp only; xsum [e51W_eq]

theorem e11OW_eq : (e11OW sevm b p a' f a v t r ret S M).1 = 4100 + ownG sevm b f := by
  unfold e11OW ownG ownCredited ownRead; dsimp only; xsum [e51W_eq]

theorem e13ZW_eq : (e13ZW sevm b p q f v t ret S M).1 = 2586 + mvCoreG sevm b v (v - f) t sevm.caller.toB256 := by
  unfold e13ZW mvCoreG mvDebited; dsimp only; xsum [e50W_eq, e51W_eq]

theorem e13NW_eq : (e13NW sevm b p q f v t ret S M).1 =
    4830 + mvCoreG sevm b v (v - f) t sevm.caller.toB256 +
      ownG sevm (mvCredited sevm b v (v - f) t sevm.caller.toB256) f := by
  unfold e13NW mvCoreG mvDebited; dsimp only; xsum [e50W_eq, e51W_eq, e13OW_eq]

theorem e13W_eq : (e13W sevm b p q f0 f v t ret S M).1 = mvG 2586 4830 sevm b v f t sevm.caller.toB256 := by
  unfold e13W mvG
  by_cases hf : f = 0
  · rw [dite_eq_left hf, ite_eq_left hf]; exact e13ZW_eq ..
  · rw [dite_eq_right hf, ite_eq_right hf]; exact e13NW_eq ..

theorem e11ZW_eq : (e11ZW sevm b p q f a v t r ret S M).1 = 2593 + mvCoreG sevm b v (v - f) t r := by
  unfold e11ZW mvCoreG mvDebited; dsimp only; xsum [e50W_eq, e51W_eq]

theorem e11NW_eq : (e11NW sevm b p q f a v t r ret S M).1 =
    4838 + mvCoreG sevm b v (v - f) t r + ownG sevm (mvCredited sevm b v (v - f) t r) f := by
  unfold e11NW mvCoreG mvDebited; dsimp only; xsum [e50W_eq, e51W_eq, e11OW_eq]

theorem e11W_eq : (e11W sevm b p q f0 f a v t r ret S M).1 = mvG 2593 4838 sevm b v f t r := by
  unfold e11W mvG
  by_cases hf : f = 0
  · rw [dite_eq_left hf, ite_eq_left hf]; exact e11ZW_eq ..
  · rw [dite_eq_right hf, ite_eq_right hf]; exact e11NW_eq ..

theorem e10W_eq : (e10W sevm b p q f0 f a v t r ret S M).1 = e10G sevm b a v f t r := by
  unfold e10W e10G
  by_cases ha : a = maxUint
  · rw [dite_eq_left ha, ite_eq_left ha]; unfold e10MW; dsimp only; xsum [e11W_eq]
  · rw [dite_eq_right ha, ite_eq_right ha]; unfold e10LW; dsimp only; xsum [e50W_eq, e11W_eq]

theorem e60CW_eq : (e60CW sevm b v t ret S M).1 =
    236 + sloadCost sevm b (Bytes.toB256 [3]) + e61G v +
      sloadCost sevm (afterSload sevm b (Bytes.toB256 [3])) (Bytes.toB256 [4]) +
      sloadCost sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [3])) (Bytes.toB256 [4])) (Bytes.toB256 [4]) +
      mvG 2586 4830 sevm (afterSload sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [3])) (Bytes.toB256 [4]))
        (Bytes.toB256 [4])) v (feeOf (Devm.getStor b sevm.currentTarget) v) t sevm.caller.toB256 := by
  unfold e60CW; dsimp only; xsum [e61W_eq, e63W_eq, e13W_eq]

theorem e60KW_eq : (e60KW sevm b v t ret S M).1 =
    228 + sloadCost sevm b (Bytes.toB256 [3]) + e61G v +
      sloadCost sevm (afterSload sevm b (Bytes.toB256 [3])) (Bytes.toB256 [4]) +
      mvG 2586 4830 sevm (afterSload sevm (afterSload sevm b (Bytes.toB256 [3])) (Bytes.toB256 [4])) v
        (feeOf (Devm.getStor b sevm.currentTarget) v) t sevm.caller.toB256 := by
  unfold e60KW; dsimp only; xsum [e61W_eq, e63W_eq, e13W_eq]

theorem e60W_eq : (e60W sevm b v t ret S M).1 = e60G sevm b v t := by
  unfold e60W e60G feeG feeBase
  by_cases hc : Capped (Devm.getStor b sevm.currentTarget) v
  · rw [dite_eq_left hc, ite_eq_left hc, ite_eq_left hc, e60CW_eq]; xsum []
  · rw [dite_eq_right hc, ite_eq_right hc, ite_eq_right hc, e60KW_eq]; xsum []

theorem e39W_eq : (e39W sevm b v t ret S M).1 = 404 + gateG sevm b sevm.caller.toB256 + e60G sevm (gateBase sevm b sevm.caller.toB256) v t := by
  unfold e39W gateG; dsimp only; xsum [e60W_eq]

theorem e56CW_eq : (e56CW sevm b v t r ret S M).1 =
    426 + sloadCost sevm b (ak r sevm.caller.toB256) +
      sloadCost sevm (alBase sevm b r) (Bytes.toB256 [3]) + e61G v +
      sloadCost sevm (afterSload sevm (alBase sevm b r) (Bytes.toB256 [3])) (Bytes.toB256 [4]) +
      sloadCost sevm (afterSload sevm (afterSload sevm (alBase sevm b r) (Bytes.toB256 [3])) (Bytes.toB256 [4]))
        (Bytes.toB256 [4]) +
      e10G sevm (afterSload sevm (afterSload sevm (afterSload sevm (alBase sevm b r) (Bytes.toB256 [3]))
        (Bytes.toB256 [4])) (Bytes.toB256 [4])) (b.getStorVal sevm.currentTarget (ak r sevm.caller.toB256)) v
        (feeOf (Devm.getStor b sevm.currentTarget) v) t r := by
  unfold e56CW; dsimp only; xsum [e61W_eq, e63W_eq, e10W_eq]

theorem e56KW_eq : (e56KW sevm b v t r ret S M).1 =
    418 + sloadCost sevm b (ak r sevm.caller.toB256) +
      sloadCost sevm (alBase sevm b r) (Bytes.toB256 [3]) + e61G v +
      sloadCost sevm (afterSload sevm (alBase sevm b r) (Bytes.toB256 [3])) (Bytes.toB256 [4]) +
      e10G sevm (afterSload sevm (afterSload sevm (alBase sevm b r) (Bytes.toB256 [3])) (Bytes.toB256 [4]))
        (b.getStorVal sevm.currentTarget (ak r sevm.caller.toB256)) v
        (feeOf (Devm.getStor b sevm.currentTarget) v) t r := by
  unfold e56KW; dsimp only; xsum [e61W_eq, e63W_eq, e10W_eq]

theorem e56W_eq : (e56W sevm b v t r ret S M).1 = e56G sevm b v t r := by
  unfold e56W e56G feeG feeBase
  simp only [afterSload_getStor]
  by_cases hc : Capped (Devm.getStor b sevm.currentTarget) v
  · rw [dite_eq_left hc, ite_eq_left hc, ite_eq_left hc, e56CW_eq]; xsum []
  · rw [dite_eq_right hc, ite_eq_right hc, ite_eq_right hc, e56KW_eq]; xsum []

theorem e23W_eq : (e23W sevm b v t r ret S M).1 = 410 + gateG sevm b r + e56G sevm (gateBase sevm b r) v t r := by
  unfold e23W gateG; dsimp only; xsum [e56W_eq]

theorem xDisp_eq : (xDisp sevm b).1 = 546 := by unfold xDisp; dsimp only
theorem pDisp_eq : (pDisp sevm b).1 = 216 := by unfold pDisp; dsimp only
theorem bDisp_eq : (bDisp sevm b).1 = 436 := by unfold bDisp; dsimp only

theorem xferW_eq : (xferW sevm b).1 = xferG sevm b := by
  unfold xferW xferG; dsimp only; xsum [xDisp_eq, e39W_eq]

theorem pullW_eq : (pullW sevm b).1 = pullG sevm b := by
  unfold pullW pullG; dsimp only; xsum [pDisp_eq, e23W_eq]

theorem e57W_eq : (e57W sevm b a ret S M).1 = 118 + sloadCost sevm b (ky a) := by
  unfold e57W; dsimp only; xsum []

theorem e33W_eq : (e33W sevm b a ret S M).1 = 268 + sloadCost sevm b (Bytes.toB256 [10]) +
    sloadCost sevm (afterSload sevm b (Bytes.toB256 [10])) (ky a) := by
  unfold e33W; dsimp only; xsum [e57W_eq]

theorem balW_eq : (balW sevm b).1 = balG sevm b := by
  unfold balW balG; dsimp only; xsum [bDisp_eq, e33W_eq]

end Charges

/-! ## The posts, and what entry gas leaves alone -/

/-- `transfer`'s post at residual `R`. -/
noncomputable def xferPost (s : Sevm) (b : Devm) (R : Nat) : Devm :=
  St (xferBase s b) [selL s] (xferMem s b) R

/-- `transferFrom`'s base. -/
noncomputable def pullB (s : Sevm) (b : Devm) : Devm :=
  pullPost s (gateBase s b (pSrc s)) (pVal s) (pTo s) (pSrc s)

/-- `transferFrom`'s image. -/
noncomputable def pullI (s : Sevm) (b : Devm) : Mem :=
  pullMem s (gateBase s b (pSrc s)) (scr mem0 (m20 &&& (m20 &&& pSrc s))
    (Bytes.toB256 [6])) (pVal s) (pTo s) (pSrc s)

/-- `transferFrom`'s post at residual `R`. -/
noncomputable def pullP (s : Sevm) (b : Devm) (R : Nat) : Devm :=
  St (pullB s b) [selL s] (pullI s b) R

/-- `balanceOf`'s post at residual `R`. -/
noncomputable def balP (s : Sevm) (b : Devm) (R : Nat) : Devm :=
  ret60 (balBase s b) [selL s] (balMem s b) (bAns s b) R

theorem xferPost_gasLeft (s : Sevm) (b : Devm) (R : Nat) : (xferPost s b R).gasLeft = R := rfl
theorem pullP_gasLeft (s : Sevm) (b : Devm) (R : Nat) : (pullP s b R).gasLeft = R := rfl
theorem balP_gasLeft (s : Sevm) (b : Devm) (R : Nat) : (balP s b R).gasLeft = R := rfl

section Reframe

variable (s : Sevm) (p : Devm) (F R : Nat)

/-- What gas never reaches: the storage read, its charges, the fee's dispatch. -/
theorem feeBase_gas (b : Devm) (v : B256) :
    feeBase s (b.withGasLeft F) v = (feeBase s b v).withGasLeft F := by
  simp only [feeBase, getStor_withGasLeft, afterSload_withGasLeft]
  split <;> rfl

theorem feeBase_static (b : Devm) (v : B256) : feeBase {s with gas := F} b v = feeBase s b v := by
  simp only [feeBase, afterSload_withStaticGas]

theorem spentBase_gas (b : Devm) (a v r : B256) :
    spentBase s (b.withGasLeft F) a v r = (spentBase s b a v r).withGasLeft F := by
  simp only [spentBase, afterSstore_withGasLeft]
  split <;> rfl

theorem spentBase_static (b : Devm) (a v r : B256) : spentBase {s with gas := F} b a v r = spentBase s b a v r := by
  simp only [spentBase, afterSstore_withStaticGas]

theorem mvPost_gas (b : Devm) (v f t r : B256) :
    mvPost s (b.withGasLeft F) v f t r = (mvPost s b v f t r).withGasLeft F := by
  simp only [mvPost, ownLogged, ownCredited, ownRead, oky, mvCredited, mvDebited, afterSload_withGasLeft,
    afterSstore_withGasLeft, getStorVal_withGasLeft, addLog_withGasLeft]
  split <;> rfl

theorem mvPost_static (b : Devm) (v f t r : B256) : mvPost {s with gas := F} b v f t r = mvPost s b v f t r := by
  simp only [mvPost, ownLogged, ownCredited, ownRead, oky, mvCredited, mvDebited, afterSload_withStaticGas,
    afterSstore_withStaticGas]

theorem mvMem_gas (b : Devm) (M : Mem) (v f t r : B256) :
    mvMem s (b.withGasLeft F) M v f t r = mvMem s b M v f t r := by
  simp only [mvMem, ownMem, ownRead, oky, mvCredited, mvDebited, afterSload_withGasLeft, afterSstore_withGasLeft,
    getStorVal_withGasLeft]

theorem mvMem_static (b : Devm) (M : Mem) (v f t r : B256) : mvMem {s with gas := F} b M v f t r = mvMem s b M v f t r := by
  simp only [mvMem, ownMem, ownRead, oky, mvCredited, mvDebited, afterSload_withStaticGas, afterSstore_withStaticGas]

theorem mvG_gas (l l' : Nat) (b : Devm) (v f t r : B256) :
    mvG l l' s (b.withGasLeft F) v f t r = mvG l l' s b v f t r := by
  simp only [mvG, mvCoreG, ownG, ownCredited, ownRead, oky, mvCredited, mvDebited, afterSload_withGasLeft,
    afterSstore_withGasLeft, getStorVal_withGasLeft, sloadCost_withGasLeft, sstoreCost_withGasLeft]

theorem mvG_static (l l' : Nat) (b : Devm) (v f t r : B256) :
    mvG l l' {s with gas := F} b v f t r = mvG l l' s b v f t r := by
  simp only [mvG, mvCoreG, ownG, ownCredited, ownRead, oky, mvCredited, mvDebited, sloadCost_withStaticGas,
    sstoreCost_withStaticGas, afterSload_withStaticGas, afterSstore_withStaticGas]

theorem feeG_gas (b : Devm) (v : B256) : feeG s (b.withGasLeft F) v = feeG s b v := by
  simp only [feeG, afterSload_withGasLeft, sloadCost_withGasLeft, getStor_withGasLeft]

theorem feeG_static (b : Devm) (v : B256) : feeG {s with gas := F} b v = feeG s b v := by
  simp only [feeG, afterSload_withStaticGas, sloadCost_withStaticGas]

theorem e10G_gas (b : Devm) (a v f t r : B256) : e10G s (b.withGasLeft F) a v f t r = e10G s b a v f t r := by
  simp only [e10G, mvG_gas, sstoreCost_withGasLeft, afterSstore_withGasLeft]

theorem e10G_static (b : Devm) (a v f t r : B256) : e10G {s with gas := F} b a v f t r = e10G s b a v f t r := by
  simp only [e10G, mvG_static, sstoreCost_withStaticGas, afterSstore_withStaticGas]

theorem xferG_reframe : xferG {s with gas := F} (p.withGasLeft F) = xferG s p := by
  simp only [xferG, e60G, gateG, gateBase, xVal, xTo, dataWord_withStaticGas, mvG_gas, mvG_static, feeG_gas, feeG_static,
    feeBase_gas, feeBase_static, afterSload_withGasLeft, afterSload_withStaticGas, sloadCost_withGasLeft,
    sloadCost_withStaticGas, getStor_withGasLeft]

theorem pullG_reframe : pullG {s with gas := F} (p.withGasLeft F) = pullG s p := by
  simp only [pullG, e56G, gateG, gateBase, alBase, pSrc, pTo, pVal, dataWord_withStaticGas, e10G_gas, e10G_static,
    feeG_gas, feeG_static, feeBase_gas, feeBase_static, afterSload_withGasLeft, afterSload_withStaticGas,
    sloadCost_withGasLeft, sloadCost_withStaticGas, getStor_withGasLeft, getStorVal_withGasLeft]

theorem balG_reframe : balG {s with gas := F} (p.withGasLeft F) = balG s p := by
  simp only [balG, bHolder, dataWord_withStaticGas, afterSload_withGasLeft, afterSload_withStaticGas,
    sloadCost_withGasLeft, sloadCost_withStaticGas]

theorem selL_reframe : selL {s with gas := F} = selL s := by
  simp only [selL, dataWord_withStaticGas]

theorem xferBase_reframe : xferBase {s with gas := F} (p.withGasLeft F) = (xferBase s p).withGasLeft F := by
  simp only [xferBase, gateBase, xVal, xTo, dataWord_withStaticGas, mvPost_gas, mvPost_static, feeBase_gas,
    feeBase_static, afterSload_withGasLeft, afterSload_withStaticGas, getStor_withGasLeft]

theorem xferMem_reframe : xferMem {s with gas := F} (p.withGasLeft F) = xferMem s p := by
  simp only [xferMem, gateBase, xVal, xTo, dataWord_withStaticGas, mvMem_gas, mvMem_static, feeBase_gas,
    feeBase_static, afterSload_withGasLeft, afterSload_withStaticGas, getStor_withGasLeft]

theorem pullB_reframe : pullB {s with gas := F} (p.withGasLeft F) = (pullB s p).withGasLeft F := by
  simp only [pullB, pullPost, gateBase, alBase, pSrc, pTo, pVal, dataWord_withStaticGas, mvPost_gas, mvPost_static,
    spentBase_gas, spentBase_static, feeBase_gas, feeBase_static, afterSload_withGasLeft, afterSload_withStaticGas,
    getStor_withGasLeft, getStorVal_withGasLeft]

theorem pullI_reframe : pullI {s with gas := F} (p.withGasLeft F) = pullI s p := by
  simp only [pullI, pullMem, gateBase, alBase, pSrc, pTo, pVal, spentMem, dataWord_withStaticGas, mvMem_gas, mvMem_static,
    spentBase_gas, spentBase_static, feeBase_gas, feeBase_static, afterSload_withGasLeft, afterSload_withStaticGas,
    getStor_withGasLeft, getStorVal_withGasLeft]

theorem xferPost_canon : Devm.EqModGas (xferPost {s with gas := F} (p.withGasLeft F) R) (xferPost s p 0) := by
  unfold xferPost
  rw [selL_reframe, xferBase_reframe, xferMem_reframe]
  apply Devm.EqModGas.of_normalized_eq
  rfl

theorem pullP_canon : Devm.EqModGas (pullP {s with gas := F} (p.withGasLeft F) R) (pullP s p 0) := by
  unfold pullP
  rw [selL_reframe, pullB_reframe, pullI_reframe]
  apply Devm.EqModGas.of_normalized_eq
  rfl

theorem balP_canon : Devm.EqModGas (balP {s with gas := F} (p.withGasLeft F) R) (balP s p 0) := by
  unfold balP
  have h1 : balBase {s with gas := F} (p.withGasLeft F) = (balBase s p).withGasLeft F := by
    simp only [balBase, bHolder, dataWord_withStaticGas, afterSload_withGasLeft, afterSload_withStaticGas]
  have h2 : bAns {s with gas := F} (p.withGasLeft F) = bAns s p := by
    simp only [bAns, bHolder, dataWord_withStaticGas, afterSload_withGasLeft, afterSload_withStaticGas,
      getStorVal_withGasLeft]
  have h3 : balMem {s with gas := F} (p.withGasLeft F) = balMem s p := by
    simp only [balMem, bHolder, h2, dataWord_withStaticGas]
  rw [selL_reframe, h1, h2, h3]
  apply Devm.EqModGas.of_normalized_eq
  rfl

end Reframe

/-! ## The runs, with the charge and post named -/

/-- **`transfer`'s run at its exact cost**, under `xfer_lands`' premises. -/
theorem xfer_runE {sevm : Sevm} {pre : Devm} {dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : LGuards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 100056 ≤ pre.gasLeft)
    (hdep : NotDeprecated (Devm.getStor pre sevm.currentTarget))
    (hfits : XferFits (Devm.getStor pre sevm.currentTarget) sevm.caller dst v) :
    xferG sevm pre ≤ 97756 ∧
      SProg.RunExact cert.prog sevm pre (xferPost sevm pre (pre.gasLeft - xferG sevm pre)) := by
  obtain ⟨hp, hl, hfee, ok⟩ := hfits
  have hdst' : (xTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  have hle := xferW_le sevm pre
  have hrun := (xferW sevm pre).2 fork static g (gateW_of hp (by rw [toAdr_toB256]; exact hl) hdep)
    (by rw [hv]; exact hfee) (by rw [hv, hdst']; exact ok)
  rw [xferW_eq] at hle hrun
  have h := hrun (pre.gasLeft - xferG sevm pre) (by omega)
  rw [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h
  exact ⟨hle, _, rfl, h⟩

/-- **`transfer`'s run at the store sentry above its cost.** -/
theorem xfer_runF {sevm : Sevm} {pre : Devm} {dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : LGuards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : xferG sevm pre + 2300 ≤ pre.gasLeft)
    (hdep : NotDeprecated (Devm.getStor pre sevm.currentTarget))
    (hfits : XferFits (Devm.getStor pre sevm.currentTarget) sevm.caller dst v) :
    SProg.RunExact cert.prog sevm pre (xferPost sevm pre (pre.gasLeft - xferG sevm pre)) := by
  obtain ⟨hp, hl, hfee, ok⟩ := hfits
  have hdst' : (xTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  have hrun := (xferW sevm pre).2 fork static g (gateW_of hp (by rw [toAdr_toB256]; exact hl) hdep)
    (by rw [hv]; exact hfee) (by rw [hv, hdst']; exact ok)
  rw [xferW_eq] at hrun
  have h := hrun (pre.gasLeft - xferG sevm pre) (by omega)
  rw [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h
  exact ⟨_, rfl, h⟩

/-- **`transferFrom`'s run at its exact cost**, under `pull_lands`' premises. -/
theorem pull_runE {sevm : Sevm} {pre : Devm} {src dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : LGuards sevm 0x23b872dd (Bytes.toB256 [96])) (hsrc : pSrc sevm = src.toB256)
    (hdst : pTo sevm = dst.toB256) (hv : pVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 124480 ≤ pre.gasLeft)
    (hdep : NotDeprecated (Devm.getStor pre sevm.currentTarget))
    (hfits : PullFits (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v) :
    pullG sevm pre ≤ 122180 ∧
      SProg.RunExact cert.prog sevm pre (pullP sevm pre (pre.gasLeft - pullG sevm pre)) := by
  obtain ⟨hp, hl, pm⟩ := hfits
  have hsrc' : (pSrc sevm).toAdr = src := by rw [hsrc, toAdr_toB256]
  have hdst' : (pTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  have hle := pullW_le sevm pre
  have hrun := (pullW sevm pre).2 fork static g (gateW_of hp (by rw [hsrc']; exact hl) hdep)
    (by rw [hv, hsrc', hdst']; exact pm)
  rw [pullW_eq] at hle hrun
  have h := hrun (pre.gasLeft - pullG sevm pre) (by omega)
  rw [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h
  exact ⟨hle, _, rfl, h⟩

/-- **`balanceOf`'s run at its exact cost**, under `bal_lands`' premises. -/
theorem bal_runE {sevm : Sevm} {pre : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (g : LGuards sevm 0x70a08231 (Bytes.toB256 [32]))
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 7331 ≤ pre.gasLeft)
    (hdep : NotDeprecated (Devm.getStor pre sevm.currentTarget)) :
    balG sevm pre ≤ 5031 ∧
      SProg.RunExact cert.prog sevm pre (balP sevm pre (pre.gasLeft - balG sevm pre)) := by
  have hdW : (Bytes.toB256 [255] &&& pre.getStorVal sevm.currentTarget (Bytes.toB256 [10]) /
      B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 := by rw [gsv, lit10]; exact hdep
  have hle := balW_le sevm pre
  have hrun := (balW sevm pre).2 fork g hdW
  rw [balW_eq] at hle hrun
  have h := hrun (pre.gasLeft - balG sevm pre)
  rw [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h
  exact ⟨hle, _, rfl, h⟩

/-! ## The costs where the transaction form needs them -/

section Cold

variable {s : Sevm} {b : Devm} {v f t r a : B256}

/-- The fee rule with its two slots cold: the cap arm is `108` dearer. -/
theorem feeG_cold (h3 : (⟨s.currentTarget, Bytes.toB256 [3]⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (h4 : (⟨s.currentTarget, Bytes.toB256 [4]⟩ : Adr × B256) ∉ b.accessedStorageKeys) :
    feeG s b v = 4200 + e61G v + if Capped (Devm.getStor b s.currentTarget) v then 336 else 228 := by
  have h34 : Bytes.toB256 [3] ≠ Bytes.toB256 [4] := by decide
  unfold feeG
  rw [sloadCost_cold h3, sloadCost_cold (notMem_afterSload h34 h4)]
  by_cases hc : Capped (Devm.getStor b s.currentTarget) v
  · rw [ite_eq_left hc, ite_eq_left hc, sloadCost_of_warm (mem_afterSload _ _ _)]
    simp only [gasColdSload, gasWarmAccess]
    omega
  · rw [ite_eq_right hc, ite_eq_right hc]
    simp only [gasColdSload]
    omega

/-- The gate's three slots cold: `6300`. -/
theorem gateG_cold (h0 : (⟨s.currentTarget, Bytes.toB256 [0]⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (hl : (⟨s.currentTarget, mapSlot (m20 &&& (m20 &&& a)) (Bytes.toB256 [6])⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (h10 : (⟨s.currentTarget, Bytes.toB256 [10]⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (h0l : Bytes.toB256 [0] ≠ mapSlot (m20 &&& (m20 &&& a)) (Bytes.toB256 [6]))
    (hl10 : mapSlot (m20 &&& (m20 &&& a)) (Bytes.toB256 [6]) ≠ Bytes.toB256 [10]) :
    gateG s b a = 6300 := by
  have h010 : Bytes.toB256 [0] ≠ Bytes.toB256 [10] := by decide
  unfold gateG
  rw [sloadCost_cold h0, sloadCost_cold (notMem_afterSload h0l hl),
    sloadCost_cold (notMem_afterSload hl10 (notMem_afterSload h010 h10))]
  rfl

/-- A move with both its slots cold and apart, no fee or a fee: `4200`, its two stores' value classes,
and with a fee the owner's cut. -/
theorem mvG_cold (lz ln : Nat) (hr : (⟨s.currentTarget, ky r⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (ht : (⟨s.currentTarget, ky t⟩ : Adr × B256) ∉ b.accessedStorageKeys) (hne : ky r ≠ ky t) :
    mvG lz ln s b v f t r =
      (if f = 0 then lz else ln + ownG s (mvCredited s b v (v - f) t r) f) + 4200 +
        sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky r)) (b.getStorVal s.currentTarget (ky r))
          (b.getStorVal s.currentTarget (ky r) - v) +
        sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky t)) (b.getStorVal s.currentTarget (ky t))
          (b.getStorVal s.currentTarget (ky t) + (v - f)) := by
  have hcu : (mvDebited s b v r).getStorVal s.currentTarget (ky t) = b.getStorVal s.currentTarget (ky t) := by
    unfold mvDebited
    rw [curVal_afterSstore_ne hne, curVal_afterSload]
  have hm : mvCoreG s b v (v - f) t r = 4200 +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky r)) (b.getStorVal s.currentTarget (ky r))
        (b.getStorVal s.currentTarget (ky r) - v) +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky t)) (b.getStorVal s.currentTarget (ky t))
        (b.getStorVal s.currentTarget (ky t) + (v - f)) := by
    unfold mvCoreG
    rw [hcu]
    unfold mvDebited
    exact move_charges_cold hr ht hne
  unfold mvG
  rw [hm]
  split <;> omega

/-- The owner's cut with slot 0 warm and the owner's entry cold: `2400` and the store's value class. -/
theorem ownG_cold {C : Devm} {x : B256} (h0 : (⟨s.currentTarget, Bytes.toB256 [0]⟩ : Adr × B256) ∈ C.accessedStorageKeys)
    (hk : (⟨s.currentTarget, oky s C⟩ : Adr × B256) ∉ C.accessedStorageKeys) :
    ownG s C x = 2400 +
      sstoreValueCost (C.getOrigStorVal s s.currentTarget (oky s C)) (C.getStorVal s.currentTarget (oky s C))
        (C.getStorVal s.currentTarget (oky s C) + x) := by
  have hD0 : (⟨s.currentTarget, Bytes.toB256 [0]⟩ : Adr × B256) ∈
      (afterSload s C (oky s C)).accessedStorageKeys := mem_afterSload_of_mem h0
  have hR : ownRead s C = afterSload s C (oky s C) := by
    unfold ownRead
    rw [afterSload_of_warm h0]
  have hOk : oky s (afterSload s C (oky s C)) = oky s C := by
    unfold oky
    rw [curVal_afterSload]
  have hkw : (⟨s.currentTarget, oky s C⟩ : Adr × B256) ∈
      (afterSload s C (oky s C)).accessedStorageKeys := mem_afterSload s C _
  unfold ownG ownCredited
  rw [hR, hOk, afterSload_of_warm h0, sloadCost_of_warm h0, sloadCost_cold hk, sloadCost_of_warm hD0,
    afterSload_of_warm hD0, sstoreCost_warm_eq hkw, origVal_afterSload, curVal_afterSload,
    sloadCost_of_warm (mem_afterSstore_of_mem hD0)]
  simp only [gasColdSload, gasWarmAccess]
  omega

/-- `transferFrom`'s allowance step with the allowance's slot warm: unlimited or the store's value class. -/
theorem e10G_warm {al : B256}
    (hw : (⟨s.currentTarget, ak r s.caller.toB256⟩ : Adr × B256) ∈ b.accessedStorageKeys) :
    e10G s b al v f t r = if al = maxUint then 26 + mvG 2593 4838 s b v f t r
      else 320 + sstoreValueCost (b.getOrigStorVal s s.currentTarget (ak r s.caller.toB256))
          (b.getStorVal s.currentTarget (ak r s.caller.toB256)) (al - v) +
        mvG 2593 4838 s (afterSstore s b (ak r s.caller.toB256) (al - v)) v f t r := by
  unfold e10G
  rw [sstoreCost_warm_eq hw]

/-- `balanceOf` with both slots cold: `5031`, the bounded theorem's figure. -/
theorem balG_cold (h10 : (⟨s.currentTarget, Bytes.toB256 [10]⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (hk : (⟨s.currentTarget, ky (bHolder s)⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (hne : Bytes.toB256 [10] ≠ ky (bHolder s)) : balG s b = 5031 := by
  unfold balG
  rw [sloadCost_cold h10, sloadCost_cold (notMem_afterSload hne hk)]
  rfl

/-- `balanceOf` with both slots warm: `1031`. -/
theorem balG_warm (h10 : (⟨s.currentTarget, Bytes.toB256 [10]⟩ : Adr × B256) ∈ b.accessedStorageKeys)
    (hk : (⟨s.currentTarget, ky (bHolder s)⟩ : Adr × B256) ∈ b.accessedStorageKeys) : balG s b = 1031 := by
  unfold balG
  rw [sloadCost_of_warm h10, sloadCost_of_warm (mem_afterSload_of_mem hk)]
  rfl

end Cold

end Blanc.Lift.Usdt
