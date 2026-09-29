import Blanc.Lift.BookedSupportSpec
import Blanc.Lift.Weth9.Footprint
import Blanc.Lift.Weth9.Frame

/-!
# WETH9 frames preserve a footprint over a fixed universe of keys

The footprint frame contract `footSpec U` is `ContractSpecSem.ofBookedSumWith weth9Sem (trackedSum U)
(Support U)`: its invariant is `Support U s ∧ trackedSum U s + v ≤ b` and its side condition is
`SumNof`.  `U` is a *universe* of tracked keys fixed in advance — the trace-fixed set
`K₀ ∪ (keys the trace's raw frames touch)` of `FootHistory.lean` — whose slots are injective
(`KeyInj U`) and off the fixed slots.  Every frame consumes only

* `frameKeys sevm ⊆ U`: the keys the call may read or write are tracked, where `frameKeys` is the
  decode-free over-approximation `[bal caller, bal a₀, bal a₁, allow a₀ caller, allow caller a₀]`
  (`aᵢ` the address-masked calldata words at 4 and 36): deposit and withdraw write `bal caller`;
  `transfer(dst, _)` writes `bal caller` and `bal a₀`; `transferFrom(src, dst, _)` writes `bal a₀`,
  `bal a₁` and (when `src ≠ caller`) `allow a₀ caller`; `approve(spender, _)` writes
  `allow caller a₀`;

no `AllowAdmitted`, no hash fact: the injectivity of the tracked slots replaces the universal
"allowance slots avoid every balance slot".  `foot_frame_post_in` is the frame theorem, assembled
from the effect lemmas of the writer entries by `frame_post_of` (`Frame.lean`).
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc
open Blanc.Lift

/-- The footprint frame contract over the tracked universe `U`. -/
noncomputable def footSpec (U : Key → Prop) : ContractSpecSem :=
  ContractSpecSem.ofBookedSumWith weth9Sem (trackedSum U) (Support U)

theorem footSpec_inv {U : Key → Prop} {s : Stor} {v b : B256} :
    (footSpec U).Inv s v b ↔ Support U s ∧ trackedSum U s + v.toNat ≤ b.toNat := Iff.rfl

theorem footSpec_side {U : Key → Prop} : (footSpec U).Side = SumNof := rfl

theorem footSpec_stateInv_iff {U : Key → Prop} {ca : Adr} {w : State} :
    (footSpec U).StateInv ca w ↔
      (some (w.getCode ca).toList = some code.toList ∧ SumNof w.bal ∧
        (Support U (w.getStor ca) ∧ trackedSum U (w.getStor ca) ≤ (w.bal ca).toNat)) := by
  constructor
  · intro h
    refine ⟨h.code, h.side, h.inv.1, ?_⟩
    have := (footSpec_inv.mp h.inv).2
    rw [B256.toNat_zero] at this
    omega
  · rintro ⟨hc, hs, hsup, hle⟩
    refine ⟨hc, hs, hsup, ?_⟩
    show trackedSum U (w.getStor ca) + (0 : B256).toNat ≤ (w.bal ca).toNat
    rw [B256.toNat_zero]
    omega

/-- The keys a frame's call may read or write: a decode-free over-approximation covering every
selector (see the module note). -/
def frameKeys (sevm : Sevm) : List Key :=
  [.bal sevm.caller, .bal (Sevm.dataWord sevm 4).toAdr, .bal (Sevm.dataWord sevm 36).toAdr,
    .allow (Sevm.dataWord sevm 4).toAdr sevm.caller,
    .allow sevm.caller (Sevm.dataWord sevm 4).toAdr]

/-! ## The frame postcondition from a storage effect -/

/-- A run that leaves the balances alone and does not raise the tracked ledger above the incoming
one (plus the callvalue in flight) ends in the footprint postcondition. -/
theorem footPost_of {U : Key → Prop} {sevm : Sevm} {d o : Devm}
    (hpre : (footSpec U).Pre sevm.currentTarget sevm d) (hbal : o.getBal = d.getBal)
    (hsup : Support U (Devm.getStor o sevm.currentTarget))
    (hsum : trackedSum U (Devm.getStor o sevm.currentTarget) ≤
      trackedSum U (Devm.getStor d sevm.currentTarget) + sevm.value.toNat) :
    (footSpec U).Post sevm.currentTarget sevm o := by
  refine ⟨hbal ▸ hpre.side, footSpec_inv.mpr ⟨hsup, ?_⟩⟩
  have h := (footSpec_inv.mp (hpre.inv.left rfl)).2
  rw [hbal, B256.toNat_zero]
  omega

/-- The tracked ledger fits a word whenever the incoming invariant holds. -/
theorem trackedSum_lt {U : Key → Prop} {sevm : Sevm} {d : Devm}
    (hpre : (footSpec U).Pre sevm.currentTarget sevm d) :
    trackedSum U (Devm.getStor d sevm.currentTarget) < 2 ^ 256 := by
  have h := (footSpec_inv.mp (hpre.inv.left rfl)).2
  have hlt := B256.toNat_lt (d.getBal sevm.currentTarget)
  omega

/-- A write at an allowance key tracked in `U` keeps the tracked ledger. -/
theorem trackedSum_set_allow {U : Key → Prop} (hinj : KeyInj U) {s : Stor} {o p : Adr}
    (h : U (.allow o p)) (w : B256) :
    trackedSum U (s.set (allowSlot o p) w) = trackedSum U s := by
  unfold trackedSum
  rw [tracked_set_off]
  intro a ha heq
  exact Key.noConfusion (hinj _ _ ha h heq)

/-! ## The writer entries -/

/-- **Deposit** (entry 1) preserves the footprint when the caller's balance row is tracked. -/
theorem foot_deposit {U : Key → Prop} (hinj : KeyInj U) {sevm : Sevm} {d : Devm}
    {o : Outcome} {g : SFunc} (hfork : CoveredFork sevm.benvStat.fork)
    (hg : prog[1]? = some g) (hcaller : U (.bal sevm.caller))
    (hpre : (footSpec U).Pre sevm.currentTarget sevm d) (run : SFunc.Run prog sevm d g o) :
    (footSpec U).Post sevm.currentTarget sevm (Outcome.devm o) := by
  obtain ⟨hstor, hbal⟩ := Weth9.deposit_effect hg hfork run
  have hsup := (footSpec_inv.mp (hpre.inv.left rfl)).1
  have hbound : trackedSum U (Devm.getStor d sevm.currentTarget) + sevm.value.toNat < 2 ^ 256 := by
    have h := (footSpec_inv.mp (hpre.inv.left rfl)).2
    have hlt := B256.toNat_lt (d.getBal sevm.currentTarget)
    omega
  refine footPost_of hpre hbal ?_ ?_
  · rw [hstor]
    exact hsup.set hcaller _
  · rw [hstor, trackedSum_deposit hinj hcaller hbound]

/-- **The `withdraw` debit step** for the footprint invariant: the `hstep` premise of
`Weth9.withdraw_post` when the caller's balance row is tracked. -/
theorem foot_withdraw_step {U : Key → Prop} (hinj : KeyInj U) {sevm : Sevm}
    (hcaller : U (.bal sevm.caller)) {s : Stor} {v b wad : B256}
    (h : (footSpec U).Inv s v b) (hle : wad ≤ s.get (balSlot sevm.caller)) :
    wad ≤ b ∧ (footSpec U).Inv (s.set (balSlot sevm.caller) (s.get (balSlot sevm.caller) - wad))
      0 (b - wad) := by
  obtain ⟨hsup, hsum⟩ := footSpec_inv.mp h
  have hw := trackedSum_withdraw hinj hcaller hle
  have hwle : wad.toNat ≤ trackedSum U s := by
    have h1 : wad ≤ tracked U s sevm.caller := by
      rw [tracked_self hcaller]
      exact hle
    exact (B256.toNat_le_toNat h1).trans le_sum
  have hwb : wad.toNat ≤ b.toNat := by omega
  have hle' : wad ≤ b := B256.le_of_toNat_le_toNat hwb
  refine ⟨hle', footSpec_inv.mpr ⟨hsup.set hcaller _, ?_⟩⟩
  rw [B256.toNat_sub_eq_of_le _ _ hle', B256.toNat_zero]
  omega

/-- **A balance transfer** (entry 9, possibly after an allowance write) preserves the footprint
when the source and destination rows, and the allowance row a distinct-owner transfer writes, are
tracked. -/
theorem foot_xfer {U : Key → Prop} (hinj : KeyInj U) {sevm : Sevm} {d : Devm} {o : Outcome}
    {wad dst src : B256} (hsrc : U (.bal src.toAdr)) (hdst : U (.bal dst.toAdr))
    (hallow : src.toAdr.toB256 ≠ sevm.caller.toB256 → U (.allow src.toAdr sevm.caller))
    (hpre : (footSpec U).Pre sevm.currentTarget sevm d)
    (hok : Weth9.XferOk sevm d o wad dst src) :
    (footSpec U).Post sevm.currentTarget sevm (Outcome.devm o) := by
  obtain ⟨⟨hbal, heffect⟩, hle⟩ := hok
  have hsup := (footSpec_inv.mp (hpre.inv.left rfl)).1
  have hlt := trackedSum_lt hpre
  -- the transfer over any storage `s₀` that agrees with the entry storage on the tracked ledger
  have main : ∀ s₀ : Stor, Support U s₀ → trackedSum U s₀ = trackedSum U (Devm.getStor d sevm.currentTarget) →
      wad ≤ s₀.get (balSlot src.toAdr) →
      Support U (Weth9.xferStor s₀ src.toAdr dst.toAdr wad) ∧
        trackedSum U (Weth9.xferStor s₀ src.toAdr dst.toAdr wad) =
          trackedSum U (Devm.getStor d sevm.currentTarget) := by
    intro s₀ hs₀ hsum₀ hle₀
    refine ⟨(hs₀.set hsrc _).set hdst _, ?_⟩
    rw [← hsum₀]
    exact trackedSum_transfer hinj hsrc hdst hle₀ (by omega)
  rcases heffect with hs | ⟨hne, w, hs⟩
  · obtain ⟨hs1, hs2⟩ := main _ hsup rfl hle
    refine footPost_of hpre hbal ?_ ?_
    · rw [hs]; exact hs1
    · rw [hs, hs2]; omega
  · have hallowU := hallow hne
    have hoff : balSlot src.toAdr ≠ allowKey src.toAdr.toB256 sevm.caller.toB256 := by
      intro heq
      exact Key.noConfusion (hinj _ _ hsrc hallowU heq)
    have hle₀ : wad ≤ ((Devm.getStor d sevm.currentTarget).set
        (allowKey src.toAdr.toB256 sevm.caller.toB256) w).get (balSlot src.toAdr) := by
      rw [Stor.get_set_ne _ (Ne.symm hoff)]
      exact hle
    obtain ⟨hs1, hs2⟩ := main ((Devm.getStor d sevm.currentTarget).set
      (allowKey src.toAdr.toB256 sevm.caller.toB256) w) (hsup.set hallowU w)
      (trackedSum_set_allow hinj hallowU w) hle₀
    refine footPost_of hpre hbal ?_ ?_
    · rw [hs]; exact hs1
    · rw [hs, hs2]; omega

/-- The `approve` wrapper preserves the footprint when the allowance row it writes is tracked. -/
theorem foot_approve {U : Key → Prop} (hinj : KeyInj U) {sevm : Sevm} {d : Devm}
    {o : Outcome} {w : SFunc} (hw : prog[27]? = some w)
    (hallow : U (.allow sevm.caller (Sevm.dataWord sevm 4).toAdr))
    (hpre : (footSpec U).Pre sevm.currentTarget sevm d) (run : SFunc.Run prog sevm d w o) :
    (footSpec U).Post sevm.currentTarget sevm (Outcome.devm o) := by
  obtain ⟨hbal, hs | ⟨v, hs⟩⟩ := approve_wrapper_effect hw run
  · refine footPost_of hpre hbal ?_ ?_
    · rw [hs]; exact (footSpec_inv.mp (hpre.inv.left rfl)).1
    · rw [hs]; omega
  · have hkey : allowKey sevm.caller.toB256 (allowArg sevm) =
        allowSlot sevm.caller (Sevm.dataWord sevm 4).toAdr := by
      rw [allowArg, and_mask_word]
      rfl
    rw [hkey] at hs
    refine footPost_of hpre hbal ?_ ?_
    · rw [hs]; exact (footSpec_inv.mp (hpre.inv.left rfl)).1.set hallow _
    · rw [hs, trackedSum_set_allow hinj hallow]; omega

/-! ## The frame -/

section Frame

variable {U : Key → Prop} {sevm : Sevm}

/-- **The footprint frame postcondition inside a root derivation.**  Every run of the lifted
program from a frame precondition ends in the frame postcondition, given that the frame's keys are
tracked; the `CALL` of `withdraw` is discharged by the admitted deeper-frame hypothesis as in
`frame_post_in`. -/
theorem foot_frame_post_in (hinj : KeyInj U) {R : Exec.Deriv} {entry : Sevm → Devm → Prop}
    {pre post : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hrun : SProg.RunP (StepIn R) prog sevm pre post)
    (hkeys : ∀ k ∈ frameKeys sevm, U k)
    (hadmR : Exec.FrameAdmitted sevm.currentTarget entry R.exc)
    (ih : ∀ pc' sevm' pre' post' (child : Exec pc' sevm' pre' (.ok post')),
        sevm'.depth < sevm.depth →
        (footSpec U).sem.At sevm.currentTarget pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        Exec.FrameAdmitted sevm.currentTarget entry child →
        (footSpec U).PreWf sevm.currentTarget sevm' pre' →
        (footSpec U).Post sevm.currentTarget sevm' post')
    (hpre : (footSpec U).Pre sevm.currentTarget sevm pre) :
    (footSpec U).Post sevm.currentTarget sevm post := by
  have hcaller : U (.bal sevm.caller) := hkeys _ (by simp [frameKeys])
  have ha0 : U (.bal (Sevm.dataWord sevm 4).toAdr) := hkeys _ (by simp [frameKeys])
  have ha1 : U (.bal (Sevm.dataWord sevm 36).toAdr) := hkeys _ (by simp [frameKeys])
  have hoc : U (.allow (Sevm.dataWord sevm 4).toAdr sevm.caller) := hkeys _ (by simp [frameKeys])
  have hco : U (.allow sevm.caller (Sevm.dataWord sevm 4).toAdr) := hkeys _ (by simp [frameKeys])
  refine frame_post_of (footSpec U) StepIn.toRun hrun ?_ ?_ ?_ ?_ ?_ hpre
  · intro d o g hg hd r
    exact foot_deposit hinj hfork hg hcaller hd r
  · intro d o g hg hd r
    obtain ⟨wad, hok⟩ := Weth9.transfer_wrapper_ok hg r
    refine foot_xfer hinj ?_ ?_ ?_ hd hok
    · rw [toAdr_toB256]; exact hcaller
    · rw [toAdr_toB256]; exact ha0
    · intro hne
      exact (hne (by rw [toAdr_toB256])).elim
  · intro d o g hg hd r
    obtain ⟨wad, hok⟩ := Weth9.transferFrom_wrapper_ok hg r
    refine foot_xfer hinj ?_ ?_ ?_ hd hok
    · rw [toAdr_toB256]; exact ha0
    · rw [toAdr_toB256]; exact ha1
    · intro _
      rw [toAdr_toB256]; exact hoc
  · intro d o g hg hd r
    exact foot_approve hinj hg hco hd r
  · intro d o g hg hd r
    exact Weth9.withdraw_post_in (c := footSpec U)
      (fun h hle => foot_withdraw_step hinj hcaller h hle) hfork rfl hadmR ih hg r hd

end Frame

end Blanc.Lift.Weth9
