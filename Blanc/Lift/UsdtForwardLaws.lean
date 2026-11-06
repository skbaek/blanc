import Blanc.Lift.UsdtForward
import Blanc.CodeDelegation

/-!
# USDT: the forward laws of `transfer`, `transferFrom` and `balanceOf`

What a frame leaves, stated with the fee read from storage: `feeOf` is `basisPointsRate` and
`maximumFee` at the frame's entry, and `moveStor` credits the recipient `v - fee` and the owner `fee`
when it is nonzero, so a zero-rate state and a nonzero-rate state are the one law. `transfer` and
`transferFrom` stop, with an empty reply; `balanceOf` returns a word.

The named premises are the operator's powers: `NotDeprecated`, `NotPaused`, `NotListed`. While the
token is deprecated nothing is claimed.
-/

namespace Blanc.Lift.Usdt

open Jaune Blanc Blanc.Lift
open Blanc.Lift.AccumulatedWalk

/-- `m20`. -/
local notation "m20" => Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-! ## What a move leaves -/

section Move

variable {sevm : Sevm} {pre b : Devm}

theorem Keeps_mvCredited (h : Keeps sevm pre b) (v a t r : B256) : Keeps sevm pre (mvCredited sevm b v a t r) :=
  ((((h.sload _).sstore _ _).sload _).sstore _ _)

theorem Keeps_ownLogged (h : Keeps sevm pre b) (f r : B256) : Keeps sevm pre (ownLogged sevm b f r) :=
  (((((((h.sload _).sload _).sload _).sstore _ _).sload _)).log _)

theorem mvPost_keeps (h : Keeps sevm pre b) (v f t r : B256) : Keeps sevm pre (mvPost sevm b v f t r) := by
  unfold mvPost
  split
  · exact (Keeps_mvCredited h _ _ _ _).log _
  · exact (Keeps_ownLogged (Keeps_mvCredited h _ _ _ _) _ _).log _

theorem mvCredited_output (sevm : Sevm) (b : Devm) (v a t r : B256) : (mvCredited sevm b v a t r).output = b.output := by
  unfold mvCredited mvDebited
  simp only [afterSstore_output, afterSload_output]

theorem ownLogged_output (sevm : Sevm) (b : Devm) (f r : B256) : (ownLogged sevm b f r).output = b.output := by
  unfold ownLogged ownCredited ownRead
  simp only [Devm.addLog_output, afterSstore_output, afterSload_output]

theorem mvPost_output (sevm : Sevm) (b : Devm) (v f t r : B256) : (mvPost sevm b v f t r).output = b.output := by
  unfold mvPost
  split
  · rw [Devm.addLog_output, mvCredited_output]
  · rw [Devm.addLog_output, ownLogged_output, mvCredited_output]

theorem feeBase_output (sevm : Sevm) (b : Devm) (v : B256) : (feeBase sevm b v).output = b.output := by
  unfold feeBase
  split <;> simp only [afterSload_output]

/-- The owner's credit is `credit` on the ledger, at the owner the contract reads. -/
theorem ownLogged_getStor (sevm : Sevm) (C : Devm) (f r : B256) :
    Devm.getStor (ownLogged sevm C f r) sevm.currentTarget =
      credit (Devm.getStor C sevm.currentTarget) (ownerOf (Devm.getStor C sevm.currentTarget)) f := by
  have e1 : Devm.getStor (ownRead sevm C) sevm.currentTarget = Devm.getStor C sevm.currentTarget := by
    unfold ownRead; simp only [afterSload_getStor]
  unfold ownLogged ownCredited credit
  simp only [Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor, e1, oky_eq, getStorVal_afterSload]
  rw [gsv]

/-- **`mvPost` is the move on the ledger**: both arms of the fee. -/
theorem mvPost_getStor (sevm : Sevm) (b : Devm) (v f t r : B256) :
    Devm.getStor (mvPost sevm b v f t r) sevm.currentTarget =
      moveStor (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v f := by
  unfold mvPost moveStor
  by_cases hf : f = 0
  · rw [ite_eq_left hf, ite_eq_left hf, Devm.addLog_getStor, mvCredited_getStor]
  · rw [ite_eq_right hf, ite_eq_right hf, Devm.addLog_getStor, ownLogged_getStor, mvCredited_getStor]

/-- A move's two stores, first to their slots, do not lower the refund counter. -/
theorem mvCredited_refund {v a t r : B256} {σ : Stor}
    (hcr : sevm.currentTarget ∉ b.createdAccounts) (hor : (getOrigAcct sevm sevm.currentTarget).stor = σ)
    (h1 : (Devm.getStor b sevm.currentTarget).get (ky r) = σ.get (ky r))
    (h2 : (Devm.getStor b sevm.currentTarget).get (ky t) = σ.get (ky t)) (hne : ky r ≠ ky t) :
    b.refundCounter ≤ (mvCredited sevm b v a t r).refundCounter := by
  have a1 := sstore_ge (s := sevm) (d := afterSload sevm b (ky r)) (k := ky r)
    (v := b.getStorVal sevm.currentTarget (ky r) - v)
    (by rw [afterSload_createdAccounts]; exact hcr) hor (by rw [afterSload_getStor]; exact h1)
  have c1 : (afterSload sevm (mvDebited sevm b v r) (ky t)).createdAccounts = b.createdAccounts := by
    unfold mvDebited
    rw [afterSload_createdAccounts, afterSstore_createdAccounts, afterSload_createdAccounts]
  have a2 := sstore_ge (s := sevm) (d := afterSload sevm (mvDebited sevm b v r) (ky t)) (k := ky t)
    (v := (mvDebited sevm b v r).getStorVal sevm.currentTarget (ky t) + a)
    (by rw [c1]; exact hcr) hor (by
      unfold mvDebited
      rw [afterSload_getStor, afterSstore_getStor_self, Stor.get_set_ne _ hne, afterSload_getStor]
      exact h2)
  refine le_trans ?_ a2
  rw [afterSload_refundCounter]
  unfold mvDebited
  refine le_trans ?_ a1
  rw [afterSload_refundCounter]

/-- The owner's store, first to its slot, does not lower the refund counter. -/
theorem ownLogged_refund {f r : B256} {C : Devm} {σ : Stor}
    (hcr : sevm.currentTarget ∉ C.createdAccounts) (hor : (getOrigAcct sevm sevm.currentTarget).stor = σ)
    (h : (Devm.getStor C sevm.currentTarget).get (balSlot (ownerOf (Devm.getStor C sevm.currentTarget))) =
      σ.get (balSlot (ownerOf (Devm.getStor C sevm.currentTarget)))) :
    C.refundCounter ≤ (ownLogged sevm C f r).refundCounter := by
  have e1 : Devm.getStor (ownRead sevm C) sevm.currentTarget = Devm.getStor C sevm.currentTarget := by
    unfold ownRead; simp only [afterSload_getStor]
  have c1 : (afterSload sevm (ownRead sevm C) (Bytes.toB256 [0])).createdAccounts = C.createdAccounts := by
    unfold ownRead
    simp only [afterSload_createdAccounts]
  have a := sstore_ge (s := sevm) (d := afterSload sevm (ownRead sevm C) (Bytes.toB256 [0]))
    (k := oky sevm (ownRead sevm C))
    (v := (afterSload sevm C (Bytes.toB256 [0])).getStorVal sevm.currentTarget (oky sevm C) + f)
    (by rw [c1]; exact hcr) hor (by rw [afterSload_getStor, e1, oky_eq, e1]; exact h)
  have m : (ownLogged sevm C f r).refundCounter = (ownCredited sevm C f).refundCounter := by
    unfold ownLogged
    rw [Devm.addLog_refundCounter, afterSload_refundCounter]
  rw [m]
  refine le_trans ?_ a
  unfold ownRead
  simp only [afterSload_refundCounter]
  exact le_refl _

/-- The move's slots are first written here, and apart: the debit, the credit and, for a nonzero fee,
the owner's entry. `R` of the laws. -/
def MoveApart (σ : Stor) (src dst : Adr) (v f : B256) : Prop :=
  balSlot src ≠ balSlot dst ∧
    (f ≠ 0 → balSlot (ownerOf (credit (debit σ src v) dst (v - f))) ≠ balSlot src ∧
      balSlot (ownerOf (credit (debit σ src v) dst (v - f))) ≠ balSlot dst)

/-- The move's stores, first to their slots, do not lower the refund counter. -/
theorem mvPost_refund {v f t r : B256} {σ : Stor}
    (hcr : sevm.currentTarget ∉ b.createdAccounts) (hor : (getOrigAcct sevm sevm.currentTarget).stor = σ)
    (h1 : (Devm.getStor b sevm.currentTarget).get (balSlot r.toAdr) = σ.get (balSlot r.toAdr))
    (h2 : (Devm.getStor b sevm.currentTarget).get (balSlot t.toAdr) = σ.get (balSlot t.toAdr))
    (h3 : f ≠ 0 → (Devm.getStor b sevm.currentTarget).get
        (balSlot (ownerOf (credit (debit (Devm.getStor b sevm.currentTarget) r.toAdr v) t.toAdr (v - f)))) =
      σ.get (balSlot (ownerOf (credit (debit (Devm.getStor b sevm.currentTarget) r.toAdr v) t.toAdr (v - f)))))
    (hap : MoveApart (Devm.getStor b sevm.currentTarget) r.toAdr t.toAdr v f) :
    b.refundCounter ≤ (mvPost sevm b v f t r).refundCounter := by
  obtain ⟨hne, hO⟩ := hap
  have hC := mvCredited_refund (sevm := sevm) (b := b) (v := v) (a := v - f) (t := t) (r := r) hcr hor
    (by rw [ky_bal]; exact h1) (by rw [ky_bal]; exact h2)
    (by rw [ky_bal, ky_bal]; exact hne)
  unfold mvPost
  by_cases hf : f = 0
  · rw [ite_eq_left hf, Devm.addLog_refundCounter]; exact hC
  · rw [ite_eq_right hf, Devm.addLog_refundCounter]
    refine le_trans hC (ownLogged_refund (σ := σ) ?_ hor ?_)
    · unfold mvCredited mvDebited
      simp only [afterSstore_createdAccounts, afterSload_createdAccounts]
      exact hcr
    · rw [mvCredited_getStor]
      have e := h3 hf
      obtain ⟨n1, n2⟩ := hO hf
      revert e n1 n2
      generalize ownerOf (credit (debit (Devm.getStor b sevm.currentTarget) r.toAdr v) t.toAdr (v - f)) = w
      intro e n1 n2
      unfold credit debit
      rw [Stor.get_set_ne _ (Ne.symm n2), Stor.get_set_ne _ (Ne.symm n1)]
      exact e

end Move

/-! ## The frames -/

/-- **`transfer` fits**: the operator's gates are open, the fee rule's product fits and the move fits
the ledger, the fee read from storage. -/
structure XferFits (σ : Stor) (src dst : Adr) (v : B256) : Prop where
  notPaused : NotPaused σ
  notListed : NotListed σ src
  fee : FeeFits σ v
  move : MoveOk σ src dst v (feeOf σ v)

/-- **`transferFrom` fits**: the source is the blacklist's subject, the caller's allowance covers `v`
unless unlimited. -/
structure PullFits (σ : Stor) (src sp dst : Adr) (v : B256) : Prop where
  notPaused : NotPaused σ
  notListed : NotListed σ src
  move : PullMove σ src sp dst v

/-- The gate's three reads keep the world. -/
theorem keeps_gate (sevm : Sevm) (pre : Devm) (a : B256) : Keeps sevm pre (gateBase sevm pre a) :=
  ((((Keeps.refl sevm pre).sload _).sload _).sload _)

/-- **`transfer(dst, v)` from a frame entry, forward**: the frame stops with an empty reply, its charge
at most `97756`, the source debited `v`, `dst` credited `v - fee` and the owner `fee`. -/
theorem xfer_lands {sevm : Sevm} {pre : Devm} {dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : LGuards sevm 0xa9059cbb (Bytes.toB256 [64])) (hdst : xTo sevm = dst.toB256) (hv : xVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hout : pre.output = []) (hgas : 100056 ≤ pre.gasLeft)
    (hdep : NotDeprecated (Devm.getStor pre sevm.currentTarget))
    (hfits : XferFits (Devm.getStor pre sevm.currentTarget) sevm.caller dst v) :
    ∃ post used, used ≤ 97756 ∧ StopLands cert.prog sevm pre post used
      (moveStor (Devm.getStor pre sevm.currentTarget) sevm.caller dst v
        (feeOf (Devm.getStor pre sevm.currentTarget) v))
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧
        MoveApart (Devm.getStor pre sevm.currentTarget) sevm.caller dst v
          (feeOf (Devm.getStor pre sevm.currentTarget) v)) := by
  obtain ⟨hp, hl, hfee, ok⟩ := hfits
  have hdst' : (xTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  have gS : ∀ a, Devm.getStor (feeBase sevm (gateBase sevm pre sevm.caller.toB256) (xVal sevm)) a = Devm.getStor pre a :=
    fun a => (feeBase_getStor ..).trans (gateBase_getStor ..)
  refine ⟨_, _, xferW_le sevm pre, stopLands_of (K := 97756) rfl
    ((xferW sevm pre).2 fork static g (gateW_of hp (by rw [toAdr_toB256]; exact hl) hdep) (by rw [hv]; exact hfee)
      (by rw [hv, hdst']; exact ok)) hs hm (xferW_le sevm pre) (by omega)
    (mvPost_keeps (feeBase_keeps (keeps_gate sevm pre _) _) _ _ _ _) ?_ ?_ ?_⟩
  · unfold xferBase
    rw [mvPost_getStor, gS, hv, hdst', toAdr_toB256]
  · unfold xferBase
    rw [mvPost_output, feeBase_output]
    simp only [afterSload_output]
    exact hout
  · rintro ⟨hor, hcr, hap⟩
    have hr : pre.refundCounter ≤ (feeBase sevm (gateBase sevm pre sevm.caller.toB256) (xVal sevm)).refundCounter := by
      unfold feeBase
      split <;> simp only [afterSload_refundCounter] <;> exact le_refl _
    refine le_trans hr (mvPost_refund (σ := Devm.getStor pre sevm.currentTarget) ?_ hor
      (by rw [gS]) (by rw [gS]) (fun _ => by rw [gS]) ?_)
    · unfold feeBase
      split <;> simpa only [afterSload_createdAccounts] using hcr
    · rw [gS, hv, hdst', toAdr_toB256]; exact hap

/-- `feeOf` and the ledger's allowance step, read from the entry. -/
theorem pull_getStor (sevm : Sevm) (pre : Devm) (v t r : B256) :
    Devm.getStor (pullPost sevm pre v t r) sevm.currentTarget =
      moveStor (spendStor (Devm.getStor pre sevm.currentTarget) r.toAdr sevm.caller v) r.toAdr t.toAdr v
        (feeOf (Devm.getStor pre sevm.currentTarget) v) := by
  unfold pullPost
  rw [mvPost_getStor, spentBase_getStor _ _ _ _ _ (by
    simp only [feeBase_getStor, afterSload_getStor, gsv, ak_allow])]
  simp only [feeBase_getStor, afterSload_getStor]

/-- The allowance's debit, first to its slot, does not lower the refund counter; an unlimited allowance
writes nothing. -/
theorem spentBase_refund {sevm : Sevm} {b : Devm} {a v r : B256} {σ : Stor}
    (hcr : sevm.currentTarget ∉ b.createdAccounts) (hor : (getOrigAcct sevm sevm.currentTarget).stor = σ)
    (h : (Devm.getStor b sevm.currentTarget).get (allowSlot r.toAdr sevm.caller) =
      σ.get (allowSlot r.toAdr sevm.caller)) :
    b.refundCounter ≤ (spentBase sevm b a v r).refundCounter := by
  unfold spentBase
  split
  · exact le_refl _
  · exact sstore_ge hcr hor (by rw [ak_allow]; exact h)

theorem spentBase_keeps {sevm : Sevm} {pre b : Devm} (h : Keeps sevm pre b) (a v r : B256) :
    Keeps sevm pre (spentBase sevm b a v r) := by
  unfold spentBase
  split
  · exact h
  · exact h.sstore _ _

theorem spentBase_output (sevm : Sevm) (b : Devm) (a v r : B256) : (spentBase sevm b a v r).output = b.output := by
  unfold spentBase
  split
  · rfl
  · exact afterSstore_output ..

theorem spentBase_created (sevm : Sevm) (b : Devm) (a v r : B256) :
    (spentBase sevm b a v r).createdAccounts = b.createdAccounts := by
  unfold spentBase
  split
  · rfl
  · exact afterSstore_createdAccounts ..

theorem spend_get_ne {σ : Stor} {o s : Adr} {v k : B256} (h : k ≠ allowSlot o s) :
    (spendStor σ o s v).get k = σ.get k := by
  unfold spendStor
  split
  · rfl
  · exact Stor.get_set_ne _ (Ne.symm h) _

/-- `transferFrom`'s slots are first written here, and apart. -/
def PullApart (σ : Stor) (src sp dst : Adr) (v f : B256) : Prop :=
  MoveApart (spendStor σ src sp v) src dst v f ∧
    allowSlot src sp ≠ balSlot src ∧ allowSlot src sp ≠ balSlot dst ∧
    (f ≠ 0 → allowSlot src sp ≠
      balSlot (ownerOf (credit (debit (spendStor σ src sp v) src v) dst (v - f))))

/-- **`transferFrom(src, dst, v)` from a frame entry, forward**: the frame stops with an empty reply, its
charge at most `122180`, a limited allowance debited, the source debited `v`, `dst` credited `v - fee` and
the owner `fee`. -/
theorem pull_lands {sevm : Sevm} {pre : Devm} {src dst : Adr} {v : B256}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (g : LGuards sevm 0x23b872dd (Bytes.toB256 [96])) (hsrc : pSrc sevm = src.toB256)
    (hdst : pTo sevm = dst.toB256) (hv : pVal sevm = v)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hout : pre.output = []) (hgas : 124480 ≤ pre.gasLeft)
    (hdep : NotDeprecated (Devm.getStor pre sevm.currentTarget))
    (hfits : PullFits (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v) :
    ∃ post used, used ≤ 122180 ∧ StopLands cert.prog sevm pre post used
      (moveStor (spendStor (Devm.getStor pre sevm.currentTarget) src sevm.caller v) src dst v
        (feeOf (Devm.getStor pre sevm.currentTarget) v))
      ((getOrigAcct sevm sevm.currentTarget).stor = Devm.getStor pre sevm.currentTarget ∧
        sevm.currentTarget ∉ pre.createdAccounts ∧
        PullApart (Devm.getStor pre sevm.currentTarget) src sevm.caller dst v
          (feeOf (Devm.getStor pre sevm.currentTarget) v)) := by
  obtain ⟨hp, hl, pm⟩ := hfits
  have hsrc' : (pSrc sevm).toAdr = src := by rw [hsrc, toAdr_toB256]
  have hdst' : (pTo sevm).toAdr = dst := by rw [hdst, toAdr_toB256]
  have gS : ∀ a, Devm.getStor (gateBase sevm pre (pSrc sevm)) a = Devm.getStor pre a := gateBase_getStor sevm pre _
  have kB := spentBase_keeps (feeBase_keeps (((keeps_gate sevm pre (pSrc sevm)).sload (ak (pSrc sevm) sevm.caller.toB256))) (pVal sevm))
    ((gateBase sevm pre (pSrc sevm)).getStorVal sevm.currentTarget (ak (pSrc sevm) sevm.caller.toB256)) (pVal sevm) (pSrc sevm)
  refine ⟨_, _, pullW_le sevm pre, stopLands_of (K := 122180) rfl
    ((pullW sevm pre).2 fork static g (gateW_of hp (by rw [hsrc']; exact hl) hdep) (by rw [hv, hsrc', hdst']; exact pm))
    hs hm (pullW_le sevm pre) (by omega) (mvPost_keeps kB _ _ _ _) ?_ ?_ ?_⟩
  · rw [pull_getStor, gS, hv, hsrc', hdst']
  · unfold pullPost
    rw [mvPost_output, spentBase_output, feeBase_output]
    simp only [afterSload_output]
    exact hout
  · rintro ⟨hor, hcr, hap, ha1, ha2, ha3⟩
    subst hv hsrc' hdst'
    have hq : ∀ a, Devm.getStor (alBase sevm (gateBase sevm pre (pSrc sevm)) (pSrc sevm)) a = Devm.getStor pre a :=
      fun a => (afterSload_getStor ..).trans (gS a)
    have hF : ∀ a, Devm.getStor (feeBase sevm (alBase sevm (gateBase sevm pre (pSrc sevm)) (pSrc sevm)) (pVal sevm)) a =
        Devm.getStor pre a := fun a => (feeBase_getStor ..).trans (hq a)
    have hr : pre.refundCounter ≤ (feeBase sevm (alBase sevm (gateBase sevm pre (pSrc sevm)) (pSrc sevm)) (pVal sevm)).refundCounter := by
      unfold feeBase
      split <;> simp only [afterSload_refundCounter] <;> exact le_refl _
    have hc : (feeBase sevm (alBase sevm (gateBase sevm pre (pSrc sevm)) (pSrc sevm)) (pVal sevm)).createdAccounts =
        pre.createdAccounts := by
      unfold feeBase
      split <;> simp only [afterSload_createdAccounts]
    have ea : (gateBase sevm pre (pSrc sevm)).getStorVal sevm.currentTarget (ak (pSrc sevm) sevm.caller.toB256) =
        (Devm.getStor (feeBase sevm (alBase sevm (gateBase sevm pre (pSrc sevm)) (pSrc sevm)) (pVal sevm)) sevm.currentTarget).get
          (allowSlot (pSrc sevm).toAdr sevm.caller) := by
      rw [hF, gsv, gS, ak_allow]
    have hsp := spentBase_getStor sevm _ _ (pVal sevm) (pSrc sevm) ea
    rw [hF] at hsp
    unfold pullPost
    rw [gS]
    refine le_trans hr (le_trans (spentBase_refund (σ := Devm.getStor pre sevm.currentTarget)
      (by rw [hc]; exact hcr) hor (by rw [hF])) (mvPost_refund (σ := Devm.getStor pre sevm.currentTarget) ?_ hor ?_ ?_ ?_ ?_))
    · rw [spentBase_created, hc]; exact hcr
    · rw [hsp]; exact spend_get_ne ha1.symm
    · rw [hsp]; exact spend_get_ne ha2.symm
    · rw [hsp]; exact fun hf => spend_get_ne (ha3 hf).symm
    · rw [hsp]; exact hap

/-- **`balanceOf(a)` from a frame entry, not deprecated, forward**, static or not: it answers `a`'s entry
and writes nothing. -/
theorem bal_lands {sevm : Sevm} {pre : Devm} {a : Adr}
    (fork : CoveredFork sevm.benvStat.fork) (g : LGuards sevm 0x70a08231 (Bytes.toB256 [32]))
    (hholder : bHolder sevm = a.toB256)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hgas : 7331 ≤ pre.gasLeft)
    (hdep : NotDeprecated (Devm.getStor pre sevm.currentTarget)) :
    ∃ post used, used ≤ 5031 ∧ FrameLands cert.prog sevm pre post used
      ((Devm.getStor pre sevm.currentTarget).get (balSlot a)) (Devm.getStor pre sevm.currentTarget) True := by
  have hdW : (Bytes.toB256 [255] &&& pre.getStorVal sevm.currentTarget (Bytes.toB256 [10]) /
      B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 := by rw [gsv, lit10]; exact hdep
  refine ⟨_, _, balW_le sevm pre, frameLands_of (K := 5031) rfl
    (fun G _ => (balW sevm pre).2 fork g hdW G) hs hm (balW_le sevm pre) (by omega) (fun _ => rfl) (fun _ => ?_)
    (fun G => ?_) (fun _ => ?_) (fun _ _ => ?_)⟩
  · unfold ret60 bAns
    rw [ky_bal, getStorVal_afterSload, gsv, hholder, toAdr_toB256]
    rfl
  · exact ⟨fun x => (afterSload_getCode ..).trans (afterSload_getCode ..),
      fun x hx => (afterSload_getStor ..).trans (afterSload_getStor ..),
      (afterSload_error ..).trans (afterSload_error ..),
      (afterSload_createdAccounts ..).trans (afterSload_createdAccounts ..)⟩
  · show Devm.getStor (balBase sevm pre) sevm.currentTarget = _
    simp only [afterSload_getStor]
  · show pre.refundCounter ≤ (balBase sevm pre).refundCounter
    simp only [afterSload_refundCounter]
    exact le_refl _

theorem usdt_undelegated : getDelegatedCodeAddress code = none :=
  getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel)

/-- `LGuards`, from the message. -/
theorem lguards_of {e : Sevm} {sel w : B256} (hv : e.value = 0) (hsel : Blanc.Sevm.selector e = sel)
    (hlen : (w + Bytes.toB256 [4]).toNat ≤ e.data.length) (h4 : 4 ≤ e.data.length) (hn : e.data.length < 2 ^ 256) :
    LGuards e sel w :=
  ⟨hv, short_of_len h4 hn, B256.ltCheck_eq_zero_of_toNat_le (by rw [B256.toNat_toB256_of_lt hn]; exact hlen),
    (legacy_selector_word e).trans hsel⟩

end Blanc.Lift.Usdt
