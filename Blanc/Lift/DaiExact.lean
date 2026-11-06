import Blanc.Lift.DaiForward
import Blanc.Lift.WalkCostExact
import Blanc.Lift.CallProfileTransport
import Blanc.Lift.StaticGasTransport

/-!
# DAI: the exact costs of `transfer`, `transferFrom` and `balanceOf`

`DaiForward`'s walks synthesize their charges; here each is a closed sum over the slots' warmth and value
classes (`xferG`, `pullG`, `balG`), the same at every entry gas, and each law names its post (`xferCanon`,
`pullCanon`, `balCanon`), the same modulo gas. `xferG_cold` and its siblings evaluate the sums where
the transaction form needs them: every slot cold and at its value at the transaction's start.
-/

namespace Blanc.Lift.Dai

open Jaune Blanc Blanc.Lift
open Blanc.Lift.AccumulatedWalk

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-! ## The closed sums -/

/-- The storage charges of a move's two reads and two writes, at their states. -/
def mvGas (s : Sevm) (b : Devm) (v t r : B256) : Nat :=
  sloadCost s b (ky r) + sstoreCost s (afterSload s b (ky r)) (ky r) (b.getStorVal s.currentTarget (ky r) - v) +
    sloadCost s (mvDebited s b v r) (ky t) +
    sstoreCost s (afterSload s (mvDebited s b v r) (ky t)) (ky t)
      ((mvDebited s b v r).getStorVal s.currentTarget (ky t) + v)

/-- `transferFrom`'s spender-is-source arm, from entry 34. -/
def e34SelfG (s : Sevm) (b : Devm) (v t r : B256) : Nat :=
  179 + sloadCost s b (ky r) + (2412 + mvGas s (afterSload s b (ky r)) v t r)

/-- `transferFrom`'s unlimited-allowance arm, from entry 34. -/
def e34MaxG (s : Sevm) (b : Devm) (v t r : B256) : Nat :=
  372 + sloadCost s b (ky r) + sloadCost s (afterSload s b (ky r)) (ak r s.caller.toB256) +
    (2412 + mvGas s (afterSload s (afterSload s b (ky r)) (ak r s.caller.toB256)) v t r)

/-- `transferFrom`'s limited-allowance arm's charges for the allowance. -/
def limGas (s : Sevm) (b : Devm) (v r c : B256) : Nat :=
  sloadCost s b (ky r) + sloadCost s (afterSload s b (ky r)) (ak r c) +
    sloadCost s (afterSload s (afterSload s b (ky r)) (ak r c)) (ak r c) +
    sloadCost s (afterSload s (afterSload s (afterSload s b (ky r)) (ak r c)) (ak r c)) (ak r c) +
    sstoreCost s (afterSload s (afterSload s (afterSload s (afterSload s b (ky r)) (ak r c)) (ak r c)) (ak r c))
      (ak r c)
      ((afterSload s (afterSload s (afterSload s b (ky r)) (ak r c)) (ak r c)).getStorVal s.currentTarget
        (ak r c) - v)

/-- `transferFrom`'s limited-allowance arm, from entry 34. -/
def e34LimG (s : Sevm) (b : Devm) (v t r : B256) : Nat :=
  1029 + limGas s b v r s.caller.toB256 + (2412 + mvGas s (limBase s b v r s.caller.toB256) v t r)

/-- **`transfer`'s exact cost.** -/
def xferG (s : Sevm) (b : Devm) : Nat :=
  383 + e34SelfG s b (xVal s) (xTo s) s.caller.toB256

/-- **`balanceOf`'s exact cost.** -/
def balG (s : Sevm) (b : Devm) : Nat :=
  502 + sloadCost s b (mapSlot (bHolder s) (Bytes.toB256 [2]))

section Charges

variable (sevm : Sevm) (b : Devm) (v t r ret a p : B256) (S : List B256) (M : Mem)

theorem e36W_eq : (e36W sevm b v t ret S M).1 = 62 := by
  unfold e36W; dsimp only

theorem e37W_eq : (e37W sevm b v t ret S M).1 = 62 := by
  unfold e37W; dsimp only

theorem e29W_eq : (e29W sevm b a ret S M).1 = 91 + sloadCost sevm b (mapSlot a (Bytes.toB256 [2])) := by
  unfold e29W; dsimp only; xsum []

theorem e5W_eq : (e5W sevm b p v t r ret S M).1 = 2412 + mvGas sevm b v t r := by
  unfold e5W mvGas mvDebited; dsimp only; xsum [e36W_eq, e37W_eq]

theorem e34SelfW_eq : (e34SelfW sevm b v t r ret S M).1 = e34SelfG sevm b v t r := by
  unfold e34SelfW e34SelfG; dsimp only; xsum [e5W_eq]

theorem e34MaxW_eq : (e34MaxW sevm b v t r ret S M).1 = e34MaxG sevm b v t r := by
  unfold e34MaxW e34MaxG; dsimp only; xsum [e5W_eq]

theorem e34LimW_eq : (e34LimW sevm b v t r ret S M).1 = e34LimG sevm b v t r := by
  unfold e34LimW e34LimG limGas limBase; dsimp only; xsum [e5W_eq, e36W_eq]

theorem e10W_eq : (e10W sevm b v t ret S M).1 = 50 + e34SelfG sevm b v t sevm.caller.toB256 := by
  unfold e10W; dsimp only; xsum [e34SelfW_eq]

theorem xferW_eq : (xferW sevm b).1 = xferG sevm b := by
  unfold xferW xferG; dsimp only; xsum [e10W_eq]

theorem balW_eq : (balW sevm b).1 = balG sevm b := by
  unfold balW balG; dsimp only; xsum [e29W_eq]

theorem pullFrameW_eq (B : Devm) (Mr : Mem) (cc : Nat) : (pullFrameW sevm b B Mr cc).1 = 434 + cc := by
  unfold pullFrameW; dsimp only; xsum []

end Charges

/-! ## `transferFrom`, by arm -/

/-- Whether `transferFrom`'s source is its own spender. -/
abbrev pSelf (s : Sevm) : Prop := (pSrc s).toAdr = s.caller

/-- Whether `transferFrom`'s allowance is unlimited. -/
abbrev pMax (s : Sevm) (b : Devm) : Prop :=
  (Devm.getStor b s.currentTarget).get (allowSlot (pSrc s).toAdr s.caller) = maxUint

open Classical in
/-- **`transferFrom`'s exact cost**, by its arm. -/
noncomputable def pullG (s : Sevm) (b : Devm) : Nat :=
  434 + if pSelf s then e34SelfG s b (pVal s) (pTo s) (pSrc s)
    else if pMax s b then e34MaxG s b (pVal s) (pTo s) (pSrc s)
    else e34LimG s b (pVal s) (pTo s) (pSrc s)

open Classical in
/-- The base `transferFrom` halts from, by its arm. -/
noncomputable def pullB (s : Sevm) (b : Devm) : Devm :=
  if pSelf s then mvBase s (afterSload s b (ky (pSrc s))) (pVal s) (pTo s) (pSrc s)
  else if pMax s b then
    mvBase s (afterSload s (afterSload s b (ky (pSrc s))) (ak (pSrc s) s.caller.toB256)) (pVal s) (pTo s) (pSrc s)
  else mvBase s (limBase s b (pVal s) (pSrc s) s.caller.toB256) (pVal s) (pTo s) (pSrc s)

open Classical in
/-- The image `transferFrom` halts with, by its arm. -/
noncomputable def pullM (s : Sevm) (b : Devm) : Mem :=
  if pSelf s then mvMem (scr mem0 (m20 &&& (m20 &&& pSrc s)) (Bytes.toB256 [2])) (pVal s) (pTo s) (pSrc s)
  else if pMax s b then
    mvMem (am (scr mem0 (m20 &&& (m20 &&& pSrc s)) (Bytes.toB256 [2])) (pSrc s) s.caller.toB256)
      (pVal s) (pTo s) (pSrc s)
  else
    mvMem (am (am (am (am (scr mem0 (m20 &&& (m20 &&& pSrc s)) (Bytes.toB256 [2])) (pSrc s) s.caller.toB256)
      (pSrc s) s.caller.toB256) (pSrc s) s.caller.toB256) (pSrc s) s.caller.toB256) (pVal s) (pTo s) (pSrc s)

/-! ## The canonical posts, and what entry gas leaves alone -/

/-- `transfer`'s post at residual `R`. -/
def xferPost (s : Sevm) (b : Devm) (R : Nat) : Devm :=
  retAt (xferBase s b) [selW s] (xferMem s) okWord R

/-- `transferFrom`'s post at residual `R`. -/
noncomputable def pullPost (s : Sevm) (b : Devm) (R : Nat) : Devm :=
  retAt (pullB s b) [selW s] ((pullM s b).write 128 okWord.toBytes) okWord R

/-- `balanceOf`'s post at residual `R`. -/
def balPost (s : Sevm) (b : Devm) (R : Nat) : Devm :=
  retAt (afterSload s b (mapSlot (bHolder s) (Bytes.toB256 [2]))) [Bytes.toB256 [4, 139], selW s] (balMem s b)
    (bAns s b) R

section Reframe

variable (s : Sevm) (p : Devm) (F R : Nat)

theorem xferG_reframe : xferG {s with gas := F} (p.withGasLeft F) = xferG s p := by
  simp only [xferG, e34SelfG, mvGas, mvDebited, xVal, xTo, sloadCost_withStaticGas, sstoreCost_withStaticGas,
    afterSload_withStaticGas, afterSstore_withStaticGas, dataWord_withStaticGas, afterSload_withGasLeft,
    afterSstore_withGasLeft, getStorVal_withGasLeft, sloadCost_withGasLeft, sstoreCost_withGasLeft]

theorem pullG_reframe : pullG {s with gas := F} (p.withGasLeft F) = pullG s p := by
  simp only [pullG, pSelf, pMax, e34SelfG, e34MaxG, e34LimG, limGas, limBase, mvGas, mvDebited, pSrc, pTo, pVal,
    sloadCost_withStaticGas, sstoreCost_withStaticGas, afterSload_withStaticGas, afterSstore_withStaticGas,
    dataWord_withStaticGas, afterSload_withGasLeft, afterSstore_withGasLeft, getStorVal_withGasLeft,
    sloadCost_withGasLeft, sstoreCost_withGasLeft, getStor_withGasLeft]

theorem balG_reframe : balG {s with gas := F} (p.withGasLeft F) = balG s p := by
  simp only [balG, bHolder, sloadCost_withStaticGas, dataWord_withStaticGas, sloadCost_withGasLeft]

theorem xferBase_reframe : xferBase {s with gas := F} (p.withGasLeft F) = (xferBase s p).withGasLeft F := by
  simp only [xferBase, mvBase, mvDebited, xVal, xTo, afterSload_withStaticGas, afterSstore_withStaticGas,
    dataWord_withStaticGas, afterSload_withGasLeft, afterSstore_withGasLeft, getStorVal_withGasLeft,
    addLog_withGasLeft]

theorem pullB_reframe : pullB {s with gas := F} (p.withGasLeft F) = (pullB s p).withGasLeft F := by
  simp only [pullB, pSelf, pMax, limBase, mvBase, mvDebited, pSrc, pTo, pVal, afterSload_withStaticGas,
    afterSstore_withStaticGas, dataWord_withStaticGas, afterSload_withGasLeft, afterSstore_withGasLeft,
    getStorVal_withGasLeft, addLog_withGasLeft, getStor_withGasLeft]
  split_ifs <;> rfl

theorem pullM_reframe : pullM {s with gas := F} (p.withGasLeft F) = pullM s p := by
  simp only [pullM, pSelf, pMax, pSrc, pTo, pVal, dataWord_withStaticGas, getStor_withGasLeft]
  rfl

theorem selW_reframe : selW {s with gas := F} = selW s := by
  simp only [selW, dataWord_withStaticGas]

theorem xferMem_reframe : xferMem {s with gas := F} = xferMem s := by
  simp only [xferMem, xVal, xTo, dataWord_withStaticGas]

theorem balMem_reframe : balMem {s with gas := F} (p.withGasLeft F) = balMem s p := by
  simp only [balMem, bAns, bHolder, dataWord_withStaticGas, getStorVal_withGasLeft]

theorem bAns_reframe : bAns {s with gas := F} (p.withGasLeft F) = bAns s p := by
  simp only [bAns, bHolder, dataWord_withStaticGas, getStorVal_withGasLeft]

/-- A halting state's columns, apart from gas, are its base's. -/
theorem retAt_canon {B B' : Devm} {S : List B256} {M : Mem} {w : B256} (h : B = B'.withGasLeft F) :
    Devm.EqModGas (retAt B S M w R) (retAt B' S M w 0) := by
  subst h
  apply Devm.EqModGas.of_normalized_eq
  rfl

theorem xferPost_canon :
    Devm.EqModGas (xferPost {s with gas := F} (p.withGasLeft F) R) (xferPost s p 0) := by
  unfold xferPost
  rw [selW_reframe, xferMem_reframe]
  exact retAt_canon F R (xferBase_reframe s p F)

theorem pullPost_canon :
    Devm.EqModGas (pullPost {s with gas := F} (p.withGasLeft F) R) (pullPost s p 0) := by
  unfold pullPost
  rw [selW_reframe, pullM_reframe]
  exact retAt_canon F R (pullB_reframe s p F)

theorem balPost_canon :
    Devm.EqModGas (balPost {s with gas := F} (p.withGasLeft F) R) (balPost s p 0) := by
  unfold balPost
  rw [selW_reframe, balMem_reframe, bAns_reframe]
  refine retAt_canon F R ?_
  simp only [bHolder, afterSload_withStaticGas, dataWord_withStaticGas, afterSload_withGasLeft]

end Reframe

/-! ## The laws, with the charge and post named -/

/-- **`transfer(dst, v)`, exactly**: `xfer_lands` with its charge and post named. -/
theorem xfer_landsE {sevm : Sevm} {pre : Devm} {dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 58800 ≤ pre.gasLeft)
    (hfits : MoveFits (Devm.getStor pre sevm.currentTarget) sevm.caller dst v) :
    xferG sevm pre ≤ 56500 ∧ FrameLands cert.prog sevm pre (xferPost sevm pre (pre.gasLeft - xferG sevm pre))
      (xferG sevm pre) 1 (moveStor (Devm.getStor pre sevm.currentTarget) sevm.caller dst v)
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧ balSlot sevm.caller ≠ balSlot dst) := by
  have hle := xferW_le sevm pre
  have hrun := (xferW sevm pre).2 fork static g (by rw [hv, kn_bal]; exact hfits.1)
    (by rw [hv, hdst, kn_bal, kn_bal]; exact hfits.2)
  rw [xferW_eq] at hle hrun
  refine ⟨hle, frameLands_retAt (K := 56500) hrun hs hm hle (by omega) ?_ ?_ okWord_eq ?_⟩
  · exact (Keeps.sload (Keeps.refl sevm pre) _).mv _ _ _
  · unfold xferBase
    rw [mvBase_getStor, afterSload_getStor, hv, hdst, toAdr_toB256, toAdr_toB256]
  · rintro ⟨hor, hcr, hne⟩
    unfold xferBase
    refine le_trans (le_of_eq afterSload_refundCounter.symm)
      (mvBase_refund (σ := Devm.getStor pre sevm.currentTarget)
        (by rw [afterSload_createdAccounts]; exact hcr) hor ?_ ?_ ?_)
    · rw [afterSload_getStor]
    · rw [afterSload_getStor]
    · rw [hdst, ky_bal, ky_bal, toAdr_toB256, toAdr_toB256]; exact hne

/-- **`balanceOf(a)`, exactly**: `bal_lands` with its charge and post named. -/
theorem bal_landsE {sevm : Sevm} {pre : Devm} {a : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (g : Guards sevm 0x70a08231 (Bytes.toB256 [32]))
    (hholder : bHolder sevm = a.toB256)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 5300 ≤ pre.gasLeft) :
    balG sevm pre ≤ 3000 ∧ FrameLands cert.prog sevm pre (balPost sevm pre (pre.gasLeft - balG sevm pre))
      (balG sevm pre) ((Devm.getStor pre sevm.currentTarget).get (balSlot a))
      (Devm.getStor pre sevm.currentTarget) True := by
  have hle := balW_le sevm pre
  have hrun := (balW sevm pre).2 fork g
  rw [balW_eq] at hle hrun
  refine ⟨hle, frameLands_retAt (K := 3000) (fun G _ => hrun G) hs hm hle (by omega)
    ((Keeps.refl sevm pre).sload _) ?_ ?_ ?_⟩
  · rw [afterSload_getStor]
  · show pre.getStorVal sevm.currentTarget (mapSlot (bHolder sevm) (Bytes.toB256 [2])) = _
    rw [hholder, lit2]
    rfl
  · exact fun _ => le_of_eq afterSload_refundCounter.symm

/-- A `transferFrom` frame around an entry-34 arm, its charge named. -/
theorem pull_landsE_of {sevm : Sevm} {pre B : Devm} {Mr : Mem} {cc : Nat} {σ' : Stor} {R : Prop}
    (fork : CoveredFork sevm.benvStat.fork) (g : Guards sevm 0x23b872dd (Bytes.toB256 [96]))
    (hMr : FpM (Bytes.toB256 [128]) 160 Mr)
    (hc : ∀ X, 2300 ≤ X → SFunc.RunExact cert.prog sevm
      (St pre (pVal sevm :: pTo sevm :: pSrc sevm :: Bytes.toB256 [2, 186] :: [selW sevm]) mem0 (X + cc))
      t_0a25_c34 (.returned (St B (Bytes.toB256 [1] :: [selW sevm]) Mr X)))
    (hcc : cc ≤ 87000) (hs : pre.stack = []) (hm : pre.memory = Mem.empty)
    (hgas : 90300 ≤ pre.gasLeft) (hk : Keeps sevm pre B)
    (hst : Devm.getStor B sevm.currentTarget = σ') (hr : R → pre.refundCounter ≤ B.refundCounter) :
    FrameLands cert.prog sevm pre
      (retAt B [selW sevm] (Mr.write 128 okWord.toBytes) okWord (pre.gasLeft - (434 + cc))) (434 + cc) 1 σ' R := by
  have hrun := (pullFrameW sevm pre B Mr cc).2 fork g hMr hc
  rw [pullFrameW_eq] at hrun
  exact frameLands_retAt (K := 88000) hrun hs hm (by omega) (by omega) hk hst okWord_eq hr

/-- The apartness under which `transferFrom` does not lower the refund counter. -/
abbrev PullR (sevm : Sevm) (pre : Devm) (src dst : Adr) : Prop :=
  (getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
    sevm.currentTarget ∉ pre.createdAccounts ∧
    allowSlot src sevm.caller ≠ balSlot src ∧ allowSlot src sevm.caller ≠ balSlot dst ∧
    balSlot src ≠ balSlot dst

/-- **`transferFrom(src, dst, v)`, exactly**: `pull_lands` with its charge and post named, whichever arm. -/
theorem pull_landsE {sevm : Sevm} {pre : Devm} {src dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : Guards sevm 0x23b872dd (Bytes.toB256 [96])) (hsrc : pSrc sevm = src.toB256)
    (hdst : pTo sevm = dst.toB256) (hv : pVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 90300 ≤ pre.gasLeft)
    (hfits : PullFits (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v) :
    pullG sevm pre ≤ 88000 ∧ FrameLands cert.prog sevm pre (pullPost sevm pre (pre.gasLeft - pullG sevm pre))
      (pullG sevm pre) 1
      (moveStor (spendStor (Devm.getStor pre sevm.currentTarget) src sevm.caller v) src dst v)
      (PullR sevm pre src dst) := by
  obtain ⟨h0, hl, h1, h2⟩ := hfits
  have ksrc : kn (pSrc sevm) = balSlot src := by rw [hsrc, kn_bal]
  have kdst : kn (pTo sevm) = balSlot dst := by rw [hdst, kn_bal]
  have ysrc : ky (pSrc sevm) = balSlot src := by rw [hsrc, ky_bal, toAdr_toB256]
  have ydst : ky (pTo sevm) = balSlot dst := by rw [hdst, ky_bal, toAdr_toB256]
  have asrc : an (pSrc sevm) sevm.caller = allowSlot src sevm.caller := by rw [hsrc, an_allow]
  have tsrc : (pSrc sevm).toAdr = src := by rw [hsrc, toAdr_toB256]
  have tdst : (pTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  by_cases hself : src = sevm.caller
  · have hsp : spendStor (Devm.getStor pre sevm.currentTarget) src sevm.caller v =
        Devm.getStor pre sevm.currentTarget := by
      unfold spendStor; rw [ite_eq_right (fun hh => hh.1 hself)]
    rw [hsp] at h1 h2 ⊢
    have pS : pSelf sevm := by unfold pSelf; rw [tsrc]; exact hself
    have hle := e34SelfW_le sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) (Bytes.toB256 [2, 186]) [selW sevm] mem0
    rw [e34SelfW_eq] at hle
    have e1 : pullG sevm pre = 434 + e34SelfG sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) := by
      unfold pullG; rw [ite_eq_left pS]
    have e2 : pullB sevm pre = mvBase sevm (afterSload sevm pre (ky (pSrc sevm))) (pVal sevm) (pTo sevm) (pSrc sevm) := by
      unfold pullB; rw [ite_eq_left pS]
    have e3 : pullM sevm pre = mvMem (scr mem0 (m20 &&& (m20 &&& pSrc sevm)) (Bytes.toB256 [2])) (pVal sevm) (pTo sevm) (pSrc sevm) := by
      unfold pullM; rw [ite_eq_left pS]
    refine ⟨by rw [e1]; omega, ?_⟩
    unfold pullPost
    rw [e1, e2, e3]
    refine pull_landsE_of fork g (by xfp) (fun X hX => ?_) (by omega) hs hm hgas
      ((Keeps.sload (Keeps.refl sevm pre) _).mv _ _ _) ?_ ?_
    · have h := (e34SelfW sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) (Bytes.toB256 [2, 186]) [selW sevm] mem0).2
        fork static (FpM.init _) (by xroom) (by rw [hsrc, hself]; exact eqCheck_one rfl)
        (by rw [hv, ksrc]; exact h1) (by rw [hv, ksrc, kdst]; exact h2) X hX
      rwa [e34SelfW_eq] at h
    · rw [mvBase_getStor, afterSload_getStor, hv, tsrc, tdst]
    · rintro ⟨hor, hcr, -, -, hne⟩
      refine le_trans (le_of_eq afterSload_refundCounter.symm)
        (mvBase_refund (σ := Devm.getStor pre sevm.currentTarget)
          (by rw [afterSload_createdAccounts]; exact hcr) hor ?_ ?_ ?_)
      · rw [afterSload_getStor]
      · rw [afterSload_getStor]
      · rw [ysrc, ydst]; exact hne
  · have hF : B256.eqCheck (m20 &&& pSrc sevm) (m20 &&& sevm.caller.toB256) = 0 := by
      rw [hsrc]; exact eqCheck_ne (masked_ne hself)
    have pS : ¬ pSelf sevm := by unfold pSelf; rw [tsrc]; exact hself
    by_cases hmax : (Devm.getStor pre sevm.currentTarget).get (allowSlot src sevm.caller) = maxUint
    · have hsp : spendStor (Devm.getStor pre sevm.currentTarget) src sevm.caller v =
          Devm.getStor pre sevm.currentTarget := by
        unfold spendStor; rw [ite_eq_right (fun hh => hh.2 hmax)]
      rw [hsp] at h1 h2 ⊢
      have pM : pMax sevm pre := by unfold pMax; rw [tsrc]; exact hmax
      have hle := e34MaxW_le sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) (Bytes.toB256 [2, 186]) [selW sevm] mem0
      rw [e34MaxW_eq] at hle
      have e1 : pullG sevm pre = 434 + e34MaxG sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) := by
        unfold pullG; rw [ite_eq_right pS, ite_eq_left pM]
      have e2 : pullB sevm pre = mvBase sevm (afterSload sevm (afterSload sevm pre (ky (pSrc sevm)))
          (ak (pSrc sevm) sevm.caller.toB256)) (pVal sevm) (pTo sevm) (pSrc sevm) := by
        unfold pullB; rw [ite_eq_right pS, ite_eq_left pM]
      have e3 : pullM sevm pre = mvMem (am (scr mem0 (m20 &&& (m20 &&& pSrc sevm)) (Bytes.toB256 [2])) (pSrc sevm)
          sevm.caller.toB256) (pVal sevm) (pTo sevm) (pSrc sevm) := by
        unfold pullM; rw [ite_eq_right pS, ite_eq_left pM]
      refine ⟨by rw [e1]; omega, ?_⟩
      unfold pullPost
      rw [e1, e2, e3]
      refine pull_landsE_of fork g (by xfp) (fun X hX => ?_) (by omega) hs hm hgas
        ((((Keeps.refl sevm pre).sload _).sload _).mv _ _ _) ?_ ?_
      · have h := (e34MaxW sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) (Bytes.toB256 [2, 186]) [selW sevm] mem0).2
          fork static (FpM.init _) (by xroom) hF (by rw [asrc]; exact eqCheck_one hmax)
          (by rw [hv, ksrc]; exact h1) (by rw [hv, ksrc, kdst]; exact h2) X hX
        rwa [e34MaxW_eq] at h
      · rw [mvBase_getStor, afterSload_getStor, afterSload_getStor, hv, tsrc, tdst]
      · rintro ⟨hor, hcr, -, -, hne⟩
        refine le_trans (le_of_eq (afterSload_refundCounter.symm.trans afterSload_refundCounter.symm))
          (mvBase_refund (σ := Devm.getStor pre sevm.currentTarget)
            (by rw [afterSload_createdAccounts, afterSload_createdAccounts]; exact hcr) hor ?_ ?_ ?_)
        · rw [afterSload_getStor, afterSload_getStor]
        · rw [afterSload_getStor, afterSload_getStor]
        · rw [ysrc, ydst]; exact hne
    · have hsp : spendStor (Devm.getStor pre sevm.currentTarget) src sevm.caller v =
          (Devm.getStor pre sevm.currentTarget).set (allowSlot src sevm.caller)
            ((Devm.getStor pre sevm.currentTarget).get (allowSlot src sevm.caller) - v) := by
        unfold spendStor; rw [ite_eq_left ⟨hself, hmax⟩]
      rw [hsp] at h1 h2 ⊢
      have pM : ¬ pMax sevm pre := by unfold pMax; rw [tsrc]; exact hmax
      have hle := e34LimW_le sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) (Bytes.toB256 [2, 186]) [selW sevm] mem0
      rw [e34LimW_eq] at hle
      have e1 : pullG sevm pre = 434 + e34LimG sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) := by
        unfold pullG; rw [ite_eq_right pS, ite_eq_right pM]
      have e2 : pullB sevm pre = mvBase sevm (limBase sevm pre (pVal sevm) (pSrc sevm) sevm.caller.toB256)
          (pVal sevm) (pTo sevm) (pSrc sevm) := by
        unfold pullB; rw [ite_eq_right pS, ite_eq_right pM]
      have e3 : pullM sevm pre = mvMem (am (am (am (am (scr mem0 (m20 &&& (m20 &&& pSrc sevm)) (Bytes.toB256 [2]))
          (pSrc sevm) sevm.caller.toB256) (pSrc sevm) sevm.caller.toB256) (pSrc sevm) sevm.caller.toB256)
          (pSrc sevm) sevm.caller.toB256) (pVal sevm) (pTo sevm) (pSrc sevm) := by
        unfold pullM; rw [ite_eq_right pS, ite_eq_right pM]
      refine ⟨by rw [e1]; omega, ?_⟩
      unfold pullPost
      rw [e1, e2, e3]
      refine pull_landsE_of fork g (by xfp) (fun X hX => ?_) hle hs hm hgas
        ((Keeps.refl sevm pre).lim _ _ _ |>.mv _ _ _) ?_ ?_
      · have h := (e34LimW sevm pre (pVal sevm) (pTo sevm) (pSrc sevm) (Bytes.toB256 [2, 186]) [selW sevm] mem0).2
          fork static (FpM.init _) (by xroom) hF (by rw [asrc]; exact eqCheck_ne hmax)
          (by rw [hv, asrc]; exact hl hself hmax) (by rw [hv, ksrc]; exact h0)
          (by unfold spent; rw [hv, asrc, ksrc]; exact h1)
          (by unfold spent; rw [hv, asrc, ksrc, kdst]; exact h2) X hX
        rwa [e34LimW_eq] at h
      · rw [mvBase_getStor, limBase_getStor, hv, hsrc, toAdr_toB256, tdst]
      · rintro ⟨hor, hcr, ha1, ha2, hne⟩
        refine le_trans (limBase_refund (v := pVal sevm) (r := pSrc sevm) (c := sevm.caller.toB256) hcr hor ?_)
          (mvBase_refund (σ := Devm.getStor pre sevm.currentTarget)
            (by unfold limBase; simpa only [afterSstore_createdAccounts, afterSload_createdAccounts] using hcr) hor ?_ ?_ ?_)
        · rfl
        · rw [limBase_getStor, ysrc, hsrc, toAdr_toB256]
          exact Stor.get_set_ne _ ha1 _
        · rw [limBase_getStor, ydst, hsrc, toAdr_toB256]
          exact Stor.get_set_ne _ ha2 _
        · rw [ysrc, ydst]; exact hne

/-! ## The costs where the transaction form needs them -/

section Cold

variable {s : Sevm} {b : Devm} {v t r c : B256}

/-- The move's storage charges from a state with the debit's slot warm and the credit's cold and apart. -/
theorem mvGas_warm (hw : (⟨s.currentTarget, ky r⟩ : Adr × B256) ∈ b.accessedStorageKeys)
    (hc : (⟨s.currentTarget, ky t⟩ : Adr × B256) ∉ b.accessedStorageKeys) (hne : ky r ≠ ky t) :
    mvGas s b v t r = 2200 +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky r)) (b.getStorVal s.currentTarget (ky r))
        (b.getStorVal s.currentTarget (ky r) - v) +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky t)) (b.getStorVal s.currentTarget (ky t))
        (b.getStorVal s.currentTarget (ky t) + v) := by
  have hcu : (mvDebited s b v r).getStorVal s.currentTarget (ky t) = b.getStorVal s.currentTarget (ky t) := by
    unfold mvDebited
    rw [getStorVal_eq_getStor, getStorVal_eq_getStor, afterSstore_getStor_self, afterSload_getStor]
    exact Stor.get_set_ne _ hne _
  unfold mvGas
  rw [hcu]
  unfold mvDebited
  exact move_charges hw hc hne

/-- `afterSload` keeps the value classes' inputs. -/
theorem orig_afterSload (k k' : B256) :
    (afterSload s b k').getOrigStorVal s s.currentTarget k = b.getOrigStorVal s s.currentTarget k := by
  unfold Devm.getOrigStorVal
  rw [afterSload_createdAccounts]

theorem cur_afterSload (k k' : B256) :
    (afterSload s b k').getStorVal s.currentTarget k = b.getStorVal s.currentTarget k := by
  rw [getStorVal_eq_getStor, getStorVal_eq_getStor, afterSload_getStor]

/-- **`transfer` with both slots cold**: the fixed `7274` and the two stores' value classes. -/
theorem xferG_cold (hr : (⟨s.currentTarget, ky s.caller.toB256⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (ht : (⟨s.currentTarget, ky (xTo s)⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (hne : ky s.caller.toB256 ≠ ky (xTo s)) :
    xferG s b = 7274 +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky s.caller.toB256))
        (b.getStorVal s.currentTarget (ky s.caller.toB256)) (b.getStorVal s.currentTarget (ky s.caller.toB256) - xVal s) +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky (xTo s)))
        (b.getStorVal s.currentTarget (ky (xTo s))) (b.getStorVal s.currentTarget (ky (xTo s)) + xVal s) := by
  unfold xferG e34SelfG
  rw [mvGas_warm (mem_afterSload _ _ _) (notMem_afterSload hne ht) hne, orig_afterSload, orig_afterSload,
    cur_afterSload, cur_afterSload, sloadCost_cold hr]
  simp only [gasColdSload]
  omega

/-- **`transferFrom`'s unlimited arm with all slots cold.** -/
theorem e34MaxG_cold (hr : (⟨s.currentTarget, ky r⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (ht : (⟨s.currentTarget, ky t⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (ha : (⟨s.currentTarget, ak r s.caller.toB256⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (hne : ky r ≠ ky t) (hra : ak r s.caller.toB256 ≠ ky r) (hta : ak r s.caller.toB256 ≠ ky t) :
    e34MaxG s b v t r = 9184 +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky r)) (b.getStorVal s.currentTarget (ky r))
        (b.getStorVal s.currentTarget (ky r) - v) +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky t)) (b.getStorVal s.currentTarget (ky t))
        (b.getStorVal s.currentTarget (ky t) + v) := by
  unfold e34MaxG
  rw [mvGas_warm (mem_afterSload_of_mem (mem_afterSload s b (ky r)))
    (notMem_afterSload hta (notMem_afterSload hne ht)) hne]
  simp only [orig_afterSload, cur_afterSload]
  rw [sloadCost_cold hr, sloadCost_cold (notMem_afterSload (Ne.symm hra) ha)]
  simp only [gasColdSload]
  omega

/-- **`transferFrom`'s limited arm with all slots cold.** -/
theorem e34LimG_cold (hr : (⟨s.currentTarget, ky r⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (ht : (⟨s.currentTarget, ky t⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (ha : (⟨s.currentTarget, ak r s.caller.toB256⟩ : Adr × B256) ∉ b.accessedStorageKeys)
    (hne : ky r ≠ ky t) (hra : ak r s.caller.toB256 ≠ ky r) (hta : ak r s.caller.toB256 ≠ ky t) :
    e34LimG s b v t r = 10041 +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ak r s.caller.toB256))
        (b.getStorVal s.currentTarget (ak r s.caller.toB256)) (b.getStorVal s.currentTarget (ak r s.caller.toB256) - v) +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky r)) (b.getStorVal s.currentTarget (ky r))
        (b.getStorVal s.currentTarget (ky r) - v) +
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ky t)) (b.getStorVal s.currentTarget (ky t))
        (b.getStorVal s.currentTarget (ky t) + v) := by
  have ha2 := mem_afterSload s (afterSload s b (ky r)) (ak r s.caller.toB256)
  have hr2 : (⟨s.currentTarget, ky r⟩ : Adr × B256) ∈
      (afterSload s (afterSload s b (ky r)) (ak r s.caller.toB256)).accessedStorageKeys :=
    mem_afterSload_of_mem (mem_afterSload s b (ky r))
  have ht2 := notMem_afterSload hta (notMem_afterSload hne ht)
  generalize hb2 : afterSload s (afterSload s b (ky r)) (ak r s.caller.toB256) = b2 at ha2 hr2 ht2
  have ho : ∀ k, b2.getOrigStorVal s s.currentTarget k = b.getOrigStorVal s s.currentTarget k := by
    intro k; rw [← hb2, orig_afterSload, orig_afterSload]
  have hcu : ∀ k, b2.getStorVal s.currentTarget k = b.getStorVal s.currentTarget k := by
    intro k; rw [← hb2, cur_afterSload, cur_afterSload]
  have hL : limBase s b v r s.caller.toB256 =
      afterSstore s b2 (ak r s.caller.toB256) (b2.getStorVal s.currentTarget (ak r s.caller.toB256) - v) := by
    unfold limBase
    rw [hb2, afterSload_of_warm ha2, afterSload_of_warm ha2]
  have hkL : (limBase s b v r s.caller.toB256).accessedStorageKeys = b2.accessedStorageKeys := by
    rw [hL]; exact accessed_afterSstore_of_warm ha2
  have hoL : ∀ k, (limBase s b v r s.caller.toB256).getOrigStorVal s s.currentTarget k =
      b.getOrigStorVal s s.currentTarget k := by
    intro k
    rw [← ho k, hL]
    unfold Devm.getOrigStorVal
    rw [afterSstore_createdAccounts]
  have hcL : ∀ k, ak r s.caller.toB256 ≠ k → (limBase s b v r s.caller.toB256).getStorVal s.currentTarget k =
      b.getStorVal s.currentTarget k := by
    intro k hk
    rw [← hcu k, hL, getStorVal_eq_getStor, getStorVal_eq_getStor, afterSstore_getStor_self]
    exact Stor.get_set_ne _ hk _
  have hS : sstoreCost s b2 (ak r s.caller.toB256) (b2.getStorVal s.currentTarget (ak r s.caller.toB256) - v) =
      sstoreValueCost (b.getOrigStorVal s s.currentTarget (ak r s.caller.toB256))
        (b.getStorVal s.currentTarget (ak r s.caller.toB256))
        (b.getStorVal s.currentTarget (ak r s.caller.toB256) - v) := by
    unfold sstoreCost
    rw [ite_eq_left ha2, Nat.zero_add, ho, hcu]
  unfold e34LimG limGas
  rw [mvGas_warm (by rw [hkL]; exact hr2) (by rw [hkL]; exact ht2) hne, hoL, hoL, hcL _ hra, hcL _ hta, hb2,
    afterSload_of_warm ha2, sloadCost_of_warm ha2, afterSload_of_warm ha2, hS,
    sloadCost_cold hr, sloadCost_cold (notMem_afterSload (Ne.symm hra) ha)]
  simp only [gasColdSload, gasWarmAccess]
  omega

end Cold

end Blanc.Lift.Dai
