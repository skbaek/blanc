import Blanc.Lift.Usdc.ProxyLands
import Blanc.Lift.Usdc.V22Forward
import Blanc.Lift.WalkCostExact
import Blanc.Lift.CallProfileTransport
import Blanc.Lift.StaticGasTransport

/-!
# USDC: the exact costs of the proxy over `FiatTokenV2_2`

`implXferG`, `implPullG`, `implBalG`: V2_2's frames, closed sums over the slots' warmth and value classes.
`proxyPreG`, `tailG`: the proxy's charges around its `DELEGATECALL`.
-/

namespace Blanc.Composition.UsdcLive

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc
open Blanc.Lift.AccumulatedWalk

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
/-- `l255`. -/
local notation "l255" => Bytes.toB256 [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-! ## The closed sums -/

/-- `_setBalance`: the blacklist check's read, and the word's store. -/
def e99G (s : Sevm) (b : Devm) (x y : B256) : Nat :=
  250 + sloadCost s b (ky y) + sstoreCost s (afterSload s b (ky y)) (ky' y) x

/-- `_transfer(z, y, x)`, at its states. -/
def e93G (s : Sevm) (b : Devm) (x y z : B256) : Nat :=
  2438 + sloadCost s b (ky z) + sloadCost s (afterSload s b (ky z)) (ky z) +
    e99G s (afterSload s (afterSload s b (ky z)) (ky z))
      ((l255 &&& (afterSload s b (ky z)).getStorVal s.currentTarget (ky z)) - x) z +
    sloadCost s (e93Debited s b x z) (ky y) +
    e99G s (afterSload s (e93Debited s b x z) (ky y))
      (x + (l255 &&& (e93Debited s b x z).getStorVal s.currentTarget (ky y))) y

/-- `FiatTokenV2.transfer`'s modifiers and move. -/
def e37G (s : Sevm) (b : Devm) (x y : B256) : Nat :=
  367 + sloadCost s b (Bytes.toB256 [1]) + sloadCost s (afterSload s b (Bytes.toB256 [1])) (ky s.caller.toB256) +
    sloadCost s (afterSload s (afterSload s b (Bytes.toB256 [1])) (ky s.caller.toB256)) (ky y) +
    e93G s (e37Pre s b y) x y s.caller.toB256

/-- **V2_2's `transfer` frame, exactly.** -/
def implXferG (s : Sevm) (b : Devm) : Nat := 358 + e37G s b (xVal s) (xTo s)

/-- `transferFrom`'s modifiers, move and allowance debit. -/
def e68G (s : Sevm) (b : Devm) (x y z : B256) : Nat :=
  1052 + sloadCost s b (Bytes.toB256 [1]) + sloadCost s (afterSload s b (Bytes.toB256 [1])) (ky s.caller.toB256) +
    sloadCost s (afterSload s (afterSload s b (Bytes.toB256 [1])) (ky s.caller.toB256)) (ky z) +
    sloadCost s (afterSload s (afterSload s (afterSload s b (Bytes.toB256 [1])) (ky s.caller.toB256)) (ky z)) (ky y) +
    sloadCost s (afterSload s (afterSload s (afterSload s (afterSload s b (Bytes.toB256 [1])) (ky s.caller.toB256)) (ky z)) (ky y))
      (kA' s z) +
    e93G s (e68Pre s b y z) x y z +
    sloadCost s (e93Post s (e68Pre s b y z) x y z) (kA' s z) +
    sstoreCost s (afterSload s (e93Post s (e68Pre s b y z) x y z) (kA' s z)) (kA' s z)
      ((e93Post s (e68Pre s b y z) x y z).getStorVal s.currentTarget (kA' s z) - x)

/-- **V2_2's `transferFrom` frame, exactly.** -/
def implPullG (s : Sevm) (b : Devm) : Nat := 364 + e68G s b (pVal s) (pTo s) (pFrom s)

/-- **V2_2's `balanceOf` frame, exactly.** -/
def implBalG (s : Sevm) (b : Devm) : Nat := 453 + sloadCost s b (ky (bHolder s))

section Charges

variable (sevm : Sevm) (b : Devm) (a x y z ret : B256) (S : List B256) (M : Mem) (n : Nat)

theorem e83W_eq : (e83W sevm b a ret S M n).1 = 99 + sloadCost sevm b (ky a) := by
  unfold e83W; dsimp only; xsum []
theorem e96W_eq : (e96W sevm b a ret S M n).1 = 93 + sloadCost sevm b (ky a) := by
  unfold e96W; dsimp only; xsum []
theorem e100W_eq : (e100W sevm b x y ret S M).1 = 49 := by unfold e100W; dsimp only
theorem e98W_eq : (e98W sevm b x y ret S M).1 = 59 := by unfold e98W; dsimp only

theorem e99W_eq : (e99W sevm b x y ret S M n).1 = e99G sevm b x y := by
  unfold e99W e99G; dsimp only; xsum [e83W_eq]

theorem e93W_eq : (e93W sevm b x y z ret S M).1 = e93G sevm b x y z := by
  unfold e93W e93G e93Debited; dsimp only; xsum [e96W_eq, e100W_eq, e98W_eq, e99W_eq]

theorem e37W_eq : (e37W sevm b x y ret S M).1 = e37G sevm b x y := by
  unfold e37W e37G; dsimp only; xsum [e83W_eq, e93W_eq]

theorem implXferW_eq : (implXferW sevm b).1 = implXferG sevm b := by
  unfold implXferW implXferG; dsimp only; xsum [e37W_eq]

theorem e68W_eq : (e68W sevm b x y z ret S M).1 = e68G sevm b x y z := by
  unfold e68W e68G; dsimp only; xsum [e83W_eq, e93W_eq, e100W_eq]

theorem pullW_eq : (pullW sevm b).1 = implPullG sevm b := by
  unfold pullW implPullG; dsimp only; xsum [e68W_eq]

theorem e46W_eq : (e46W sevm b a ret S M n).1 = 133 + sloadCost sevm b (ky a) := by
  unfold e46W; dsimp only; xsum [e96W_eq]

theorem balW_eq : (balW sevm b).1 = implBalG sevm b := by
  unfold balW implBalG; dsimp only; xsum [e46W_eq]

end Charges

/-! ## The proxy's charges -/

/-- The calldata copy's memory charge. -/
noncomputable abbrev preExt (s : Sevm) (b : Devm) : Nat :=
  (St (pBase s b) [Bytes.toB256 [0], Bytes.toB256 [0], Nat.toB256 s.data.length,
      (afterSload s b pKA).getStorVal s.currentTarget pKI, Bytes.toB256 [2, 17], Bytes.toB256 [0, 117],
      Bytes.toB256 [255, 255, 255, 255] &&& Sevm.dataWord s (Bytes.toB256 [0]) /
        Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
    (Mem.empty.write 64 (Bytes.toB256 [128]).toBytes) 0).extCost
    [((Bytes.toB256 [0]).toNat, (Nat.toB256 s.data.length).toNat)]

/-- The proxy's charge up to its `DELEGATECALL`. -/
noncomputable def proxyPreG (s : Sevm) (b : Devm) : Nat :=
  436 + sloadCost s b pKA + sloadCost s (afterSload s b pKA) pKI +
    gasCopy * ceilDiv (Nat.toB256 s.data.length).toNat 32 + preExt s b

/-- The tail's charge for a word reply. -/
noncomputable def tailG (s : Sevm) (D : Devm) (R : List B256) (M : Mem) (w : B256) : Nat :=
  41 + gReturnDataCopy * ceilDiv (Nat.toB256 w.toBytes.length).toNat 32 +
    (St D (Bytes.toB256 [0] :: Bytes.toB256 [0] :: Nat.toB256 w.toBytes.length :: 1 :: R) M 0).extCost
      [((Bytes.toB256 [0]).toNat, (Nat.toB256 w.toBytes.length).toNat)]

section Proxy

variable (sevm : Sevm) (b D : Devm) (ret w : B256) (t : B256) (R S : List B256) (M : Mem)

theorem p8W_eq : (p8W sevm b ret S M).1 = 44 + sloadCost sevm b pKA := by
  unfold p8W; dsimp only; xsum []
theorem p14W_eq : (p14W sevm b ret S M).1 = 44 + sloadCost sevm b pKI := by
  unfold p14W; dsimp only; xsum []
theorem p31W_eq : (p31W sevm b ret S M).1 = 9 := by unfold p31W; dsimp only
theorem p22W_eq : (p22W sevm b ret S M).1 = 132 + sloadCost sevm b pKA := by
  unfold p22W; dsimp only; xsum [p8W_eq, p31W_eq]

theorem proxyPreW_eq : (proxyPreW sevm b t).1 = proxyPreG sevm b := by
  unfold proxyPreW proxyPreG preExt; dsimp only; xsum [p22W_eq, p14W_eq]

theorem dTailW_eq : (dTailW sevm D R M w).1 = tailG sevm D R M w := by
  unfold dTailW tailG; dsimp only; xsum []

end Proxy

/-! ## What entry gas leaves alone -/

section Reframe

variable (s : Sevm) (p : Devm) (F R : Nat)

theorem e99G_gas (b : Devm) (x y : B256) : e99G s (b.withGasLeft F) x y = e99G s b x y := by
  simp only [e99G, afterSload_withGasLeft, sloadCost_withGasLeft, sstoreCost_withGasLeft]

theorem e99G_static (b : Devm) (x y : B256) : e99G {s with gas := F} b x y = e99G s b x y := by
  simp only [e99G, afterSload_withStaticGas, sloadCost_withStaticGas, sstoreCost_withStaticGas]

theorem e93G_gas (b : Devm) (x y z : B256) : e93G s (b.withGasLeft F) x y z = e93G s b x y z := by
  simp only [e93G, e93Debited, e99G_gas, afterSload_withGasLeft, afterSstore_withGasLeft, sloadCost_withGasLeft,
    getStorVal_withGasLeft]

theorem e93G_static (b : Devm) (x y z : B256) : e93G {s with gas := F} b x y z = e93G s b x y z := by
  simp only [e93G, e93Debited, e99G_static, afterSload_withStaticGas, afterSstore_withStaticGas,
    sloadCost_withStaticGas]

theorem e93Post_gas (b : Devm) (x y z : B256) :
    e93Post s (b.withGasLeft F) x y z = (e93Post s b x y z).withGasLeft F := by
  simp only [e93Post, e93Debited, afterSload_withGasLeft, afterSstore_withGasLeft, getStorVal_withGasLeft,
    addLog_withGasLeft]

theorem e93Post_static (b : Devm) (x y z : B256) : e93Post {s with gas := F} b x y z = e93Post s b x y z := by
  simp only [e93Post, e93Debited, afterSload_withStaticGas, afterSstore_withStaticGas]

theorem implXferG_reframe : implXferG {s with gas := F} (p.withGasLeft F) = implXferG s p := by
  simp only [implXferG, e37G, e37Pre, xVal, xTo, dataWord_withStaticGas, e93G_gas, e93G_static, afterSload_withGasLeft,
    afterSload_withStaticGas, sloadCost_withGasLeft, sloadCost_withStaticGas]

theorem implPullG_reframe : implPullG {s with gas := F} (p.withGasLeft F) = implPullG s p := by
  simp only [implPullG, e68G, e68Pre, kA', pVal, pTo, pFrom, dataWord_withStaticGas, e93G_gas, e93G_static, e93Post_gas,
    e93Post_static, afterSload_withGasLeft, afterSload_withStaticGas, sloadCost_withGasLeft, sloadCost_withStaticGas,
    sstoreCost_withGasLeft, sstoreCost_withStaticGas, getStorVal_withGasLeft]

theorem implBalG_reframe : implBalG {s with gas := F} (p.withGasLeft F) = implBalG s p := by
  simp only [implBalG, bHolder, dataWord_withStaticGas, sloadCost_withGasLeft, sloadCost_withStaticGas]

theorem implXferPost_canon :
    Devm.EqModGas (implXferPost {s with gas := F} (p.withGasLeft F) R) (implXferPost s p 0) := by
  have hB : e93Post {s with gas := F} (e37Pre {s with gas := F} (p.withGasLeft F) (xTo {s with gas := F}))
        (xVal {s with gas := F}) (xTo {s with gas := F}) ({s with gas := F} : Sevm).caller.toB256 =
      (e93Post s (e37Pre s p (xTo s)) (xVal s) (xTo s) s.caller.toB256).withGasLeft F := by
    simp only [e37Pre, xVal, xTo, dataWord_withStaticGas, e93Post_gas, e93Post_static, afterSload_withGasLeft,
      afterSload_withStaticGas]
  have hM : implXferMem {s with gas := F} = implXferMem s := by
    simp only [implXferMem, xVal, xTo, dataWord_withStaticGas]
  unfold implXferPost
  rw [hB, hM]
  simp only [dataWord_withStaticGas]
  exact memRet_canon rfl

/-- `transferFrom`'s post at residual `R`. -/
noncomputable def implPullPost (s : Sevm) (b : Devm) (R : Nat) : Devm :=
  retV (Bytes.toB256 [128]) (pullBase s b) [selW s] (pullMem s) okW R

/-- `balanceOf`'s post at residual `R`. -/
noncomputable def implBalPost (s : Sevm) (b : Devm) (R : Nat) : Devm :=
  retV (Bytes.toB256 [128]) (afterSload s b (ky (bHolder s))) [selW s]
    ((sc9 mem0 (m20 &&& bHolder s)).write 128 (bAns s b).toBytes) (bAns s b) R

theorem implPullPost_canon :
    Devm.EqModGas (implPullPost {s with gas := F} (p.withGasLeft F) R) (implPullPost s p 0) := by
  have hB : pullBase {s with gas := F} (p.withGasLeft F) = (pullBase s p).withGasLeft F := by
    simp only [pullBase, e68Post, e68Pre, kA', pVal, pTo, pFrom, dataWord_withStaticGas, e93Post_gas, e93Post_static,
      afterSload_withGasLeft, afterSload_withStaticGas, afterSstore_withGasLeft, afterSstore_withStaticGas,
      getStorVal_withGasLeft]
  have hM : pullMem {s with gas := F} = pullMem s := by
    simp only [pullMem, e68Mem, sA, pVal, pTo, pFrom, dataWord_withStaticGas]
  have hS : selW {s with gas := F} = selW s := by simp only [selW, dataWord_withStaticGas]
  unfold implPullPost retV
  rw [hB, hM, hS]
  exact memRet_canon rfl

theorem implBalPost_canon :
    Devm.EqModGas (implBalPost {s with gas := F} (p.withGasLeft F) R) (implBalPost s p 0) := by
  have hB : afterSload {s with gas := F} (p.withGasLeft F) (ky (bHolder {s with gas := F})) =
      (afterSload s p (ky (bHolder s))).withGasLeft F := by
    simp only [bHolder, dataWord_withStaticGas, afterSload_withGasLeft, afterSload_withStaticGas]
  have hA : bAns {s with gas := F} (p.withGasLeft F) = bAns s p := by
    simp only [bAns, bHolder, dataWord_withStaticGas, getStorVal_withGasLeft]
  have hH : bHolder {s with gas := F} = bHolder s := by simp only [bHolder, dataWord_withStaticGas]
  have hS : selW {s with gas := F} = selW s := by simp only [selW, dataWord_withStaticGas]
  unfold implBalPost retV
  rw [hB, hA, hH, hS]
  exact memRet_canon rfl

end Reframe

/-! ## The implementation's runs, with the charge and post named -/

/-- **`transfer`'s run at its exact cost**, under `xfer_lands`' premises. -/
theorem xfer_runE {sevm : Sevm} {pre : Devm} {dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 74300 ≤ pre.gasLeft)
    (hf : MoveFits (Devm.getStor pre sevm.currentTarget) sevm.caller dst v) :
    implXferG sevm pre ≤ 72000 ∧
      SProg.RunExact Impl.cert.prog sevm pre (implXferPost sevm pre (pre.gasLeft - implXferG sevm pre)) := by
  have hle := implXferW_le sevm pre
  have hrun := (implXferW sevm pre).2 fork static (xferFacts_of g hdst hv hf)
  rw [implXferW_eq] at hle hrun
  have h := hrun (pre.gasLeft - implXferG sevm pre) (by omega)
  rw [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h
  exact ⟨hle, _, rfl, h⟩

/-- **`transferFrom`'s run at its exact cost**, under `pull_lands`' premises. -/
theorem pull_runE {sevm : Sevm} {pre : Devm} {src dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0x23b872dd (Bytes.toB256 [96])) (hsrc : pFrom sevm = src.toB256)
    (hdst : pTo sevm = dst.toB256) (hv : pVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 104300 ≤ pre.gasLeft)
    (hf : PullFits (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v) :
    implPullG sevm pre ≤ 102000 ∧
      SProg.RunExact Impl.cert.prog sevm pre (implPullPost sevm pre (pre.gasLeft - implPullG sevm pre)) := by
  have ok : E68Ok sevm pre (pVal sevm) (pTo sevm) (pFrom sevm) := by
    rw [hv]; exact e68Ok_of hsrc hdst hf
  have hle := pullW_le sevm pre
  have hrun := (pullW sevm pre).2 fork static g ok
  rw [pullW_eq] at hle hrun
  have h := hrun (pre.gasLeft - implPullG sevm pre) (by omega)
  rw [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h
  exact ⟨hle, _, rfl, h⟩

/-- **`balanceOf`'s run at its exact cost.** -/
theorem bal_runE {sevm : Sevm} {pre : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (g : Guards sevm 0x70a08231 (Bytes.toB256 [32]))
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 5800 ≤ pre.gasLeft) :
    implBalG sevm pre ≤ 3500 ∧
      SProg.RunExact Impl.cert.prog sevm pre (implBalPost sevm pre (pre.gasLeft - implBalG sevm pre)) := by
  have hle := balW_le sevm pre
  have hrun := (balW sevm pre).2 fork g
  rw [balW_eq] at hle hrun
  have h := hrun (pre.gasLeft - implBalG sevm pre)
  rw [pre_eq_St hs hm (Nat.sub_add_cancel (by omega))] at h
  exact ⟨hle, _, rfl, h⟩

end Blanc.Composition.UsdcLive
