import Blanc.Composition.BuilderRequestJointGBalance

/-!
# Tracking one builder payment entry through Gloas state transitions

Goal `eip8282-gloas-cross-layer-v1`, B5(iii) support (Plans `recon/statements.md` B5 (iii), rev 3.1). The
state-level machinery the run-level fates (`BuilderRequestJointGPayments`) are stated with:

* the slot loop one iteration at a time (`slotTick`, `slotLoop`, `processSlots_slotLoop`), with
  `process_epoch` split around `process_builder_pending_payments` (`epochPrefix`, `epochSuffix`), so the
  state each rotation reads is a function value;
* `payIdx s st` (the window index `settle_builder_payment` uses for slot `s`), `cell`, and
  `LiveAt s w st`: the payment of a bid at slot `s` with withdrawal `w` is live at `st`;
* `RotEval`/`QEv`: some rotation inside the loop evaluates the live entry, with its quorum verdict;
  `slotLoop_track` (a live entry stays put, or is evaluated), `rotEval_unique`, `rotEval_end_none`;
* the block phases and the Gloas step: `BuilderRequestJointGPaymentsBlock`.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset}

/-! ## The slot loop, one iteration at a time -/

/-- The phases of `process_epoch` before `process_builder_pending_payments`. -/
def epochPrefix (ctx : Ctx) (state : Gloas.BeaconState P) : M (Gloas.BeaconState P) := do
  let cfg := ctx.cfg
  let state ← Gloas.processJustificationAndFinalization cfg state
  let state ← Gloas.processInactivityUpdates cfg state
  let state ← Gloas.processRewardsAndPenalties cfg state
  let state ← Gloas.processRegistryUpdates cfg state
  let state ← Gloas.processSlashings cfg state
  let state ← Gloas.processEth1DataReset cfg state
  let state ← Gloas.processPendingDeposits ctx state
  Gloas.processPendingConsolidations cfg state

/-- The phases of `process_epoch` after `process_builder_pending_payments`. -/
def epochSuffix (ctx : Ctx) (state : Gloas.BeaconState P) : M (Gloas.BeaconState P) := do
  let cfg := ctx.cfg
  let state ← Gloas.processEffectiveBalanceUpdates cfg state
  let state ← Gloas.processSlashingsReset cfg state
  let state ← Gloas.processRandaoMixesReset cfg state
  let state ← Gloas.processHistoricalSummariesUpdate cfg state
  let state ← Gloas.processParticipationFlagUpdates cfg state
  let state ← Gloas.processSyncCommitteeUpdates ctx state
  let state ← Gloas.processProposerLookahead cfg state
  Gloas.processPtcWindow cfg state

theorem processEpoch_eq_split (ctx : Ctx) (st : Gloas.BeaconState P) :
    Gloas.processEpoch ctx st =
      (epochPrefix ctx st >>= fun a => Gloas.processBuilderPendingPayments ctx.cfg a >>= epochSuffix ctx) := by
  simp only [Gloas.processEpoch, epochPrefix, bind_assoc]
  rfl

theorem epochPrefix_invFrame {ctx : Ctx} {s a : Gloas.BeaconState P} (h : epochPrefix ctx s = .ok a) :
    InvFrame s a := by
  unfold epochPrefix at h
  obtain ⟨x1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x6, h6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x7, h7, h⟩ := bind_eq_ok_iff.mp h
  exact invFrame.trans (processJustificationAndFinalization_invFrame _ _ _ h1)
    (invFrame.trans (processInactivityUpdates_invFrame _ _ _ h2)
    (invFrame.trans (processRewardsAndPenalties_invFrame _ _ _ h3)
    (invFrame.trans (processRegistryUpdates_invFrame _ _ _ h4)
    (invFrame.trans (processSlashings_invFrame _ _ _ h5)
    (invFrame.trans (processEth1DataReset_invFrame _ _ _ h6)
    (invFrame.trans (processPendingDeposits_invFrame _ _ _ h7)
      (processPendingConsolidations_invFrame _ _ _ h)))))))

theorem epochSuffix_invFrame {ctx : Ctx} {s a : Gloas.BeaconState P} (h : epochSuffix ctx s = .ok a) :
    InvFrame s a := by
  unfold epochSuffix at h
  obtain ⟨x1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x6, h6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x7, h7, h⟩ := bind_eq_ok_iff.mp h
  exact invFrame.trans (processEffectiveBalanceUpdates_invFrame _ _ _ h1)
    (invFrame.trans (processSlashingsReset_invFrame _ _ _ h2)
    (invFrame.trans (processRandaoMixesReset_invFrame _ _ _ h3)
    (invFrame.trans (processHistoricalSummariesUpdate_invFrame _ _ _ h4)
    (invFrame.trans (processParticipationFlagUpdates_invFrame _ _ _ h5)
    (invFrame.trans (processSyncCommitteeUpdates_invFrame _ _ _ h6)
    (invFrame.trans (processProposerLookahead_invFrame _ _ _ h7)
      (processPtcWindow_invFrame _ _ _ h)))))))

/-- One iteration of the `process_slots` loop: `process_slot`, `process_epoch` at an epoch
boundary, then `slot := slot + 1`. -/
def slotTick (ctx : Ctx) (st : Gloas.BeaconState P) : M (Gloas.BeaconState P) := do
  let st1 ← Gloas.processSlot st
  let next ← st1.slot.add? U64.one "process_slots: state.slot + 1"
  if next.toNat % P.SLOTS_PER_EPOCH = 0 then
    let st2 ← Gloas.processEpoch ctx st1
    pure { st2 with slot := next }
  else
    pure { st1 with slot := next }

/-- `n` iterations of the `process_slots` loop. -/
def slotLoop (ctx : Ctx) : Nat → Gloas.BeaconState P → M (Gloas.BeaconState P)
  | 0, st => pure st
  | n + 1, st => slotTick ctx st >>= slotLoop ctx n

theorem forIn_range'_slotLoop {ctx : Ctx}
    {body : Nat → Gloas.BeaconState P → M (ForInStep (Gloas.BeaconState P))}
    (hb : ∀ i x r, body i x = .ok r → ∃ y, r = .yield y ∧ slotTick ctx x = .ok y) :
    ∀ (n s : Nat) (x out : Gloas.BeaconState P), forIn (List.range' s n) x body = .ok out →
      slotLoop ctx n x = .ok out
  | 0, s, x, out, h => by
    simp only [List.range'_zero, List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | n + 1, s, x, out, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨y, rfl, hy⟩ := hb s x r hr
    have := forIn_range'_slotLoop hb n (s + 1) y out h
    simp only [slotLoop, hy, bind, Except.bind]
    exact this

theorem processSlots_slotLoop {ctx : Ctx} {st st' : Gloas.BeaconState P} {T : U64}
    (h : Gloas.processSlots ctx st T = .ok st') :
    st.slot.toNat < T.toNat ∧ slotLoop ctx (T.toNat - st.slot.toNat) st = .ok st' := by
  unfold Gloas.processSlots Gloas.processSlotsWith at h
  obtain ⟨_, hr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine ⟨of_decide_eq_true (require_ok hr), ?_⟩
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hout
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at hout
  refine forIn_range'_slotLoop (fun i x r hx => ?_) _ _ _ _ hout
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨m, hm, hx⟩ := bind_eq_ok_iff.mp hx
  have hmn : m.toNat = next.toNat % P.SLOTS_PER_EPOCH := by
    rw [U64.toNat_mod? hm, U64.toNat_ofNat? hspe]
  split at hx
  · rename_i hz
    obtain ⟨st2, he, hx⟩ := bind_eq_ok_iff.mp hx
    cases hx
    refine ⟨_, rfl, ?_⟩
    have hz' : next.toNat % P.SLOTS_PER_EPOCH = 0 := by rw [← hmn]; simpa using hz
    simp only [slotTick, h1, hn, hz', he, bind, Except.bind, ite_true, pure, Except.pure]
  · rename_i hz
    cases hx
    refine ⟨_, rfl, ?_⟩
    have hz' : ¬ next.toNat % P.SLOTS_PER_EPOCH = 0 := by rw [← hmn]; simpa using hz
    simp only [slotTick, h1, hn, hz', bind, Except.bind, ite_false, pure, Except.pure]

theorem slotTick_cases {ctx : Ctx} {st st' : Gloas.BeaconState P} (h : slotTick ctx st = .ok st') :
    ∃ st1 next, Gloas.processSlot st = .ok st1 ∧
      st1.slot.add? U64.one "process_slots: state.slot + 1" = .ok next ∧ InvFrame st st1 ∧
      next.toNat = st.slot.toNat + 1 ∧
      ((next.toNat % P.SLOTS_PER_EPOCH ≠ 0 ∧ st' = { st1 with slot := next }) ∨
        (next.toNat % P.SLOTS_PER_EPOCH = 0 ∧ ∃ a b st2, epochPrefix ctx st1 = .ok a ∧
          Gloas.processBuilderPendingPayments ctx.cfg a = .ok b ∧ epochSuffix ctx b = .ok st2 ∧
          st' = { st2 with slot := next })) := by
  unfold slotTick at h
  obtain ⟨st1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨next, hn, h⟩ := bind_eq_ok_iff.mp h
  have f1 : InvFrame st st1 := processSlot_invFrame _ _ h1
  have hnext : next.toNat = st.slot.toNat + 1 := by
    rw [U64.toNat_add? hn, f1.2.2.2.2.2.2.1]; rfl
  refine ⟨st1, next, h1, hn, f1, hnext, ?_⟩
  split at h
  · rename_i hz
    obtain ⟨st2, he, h⟩ := bind_eq_ok_iff.mp h
    cases h
    rw [processEpoch_eq_split] at he
    obtain ⟨a, ha, he⟩ := bind_eq_ok_iff.mp he
    obtain ⟨b, hb, he⟩ := bind_eq_ok_iff.mp he
    exact Or.inr ⟨hz, a, b, st2, ha, hb, he, rfl⟩
  · cases h
    exact Or.inl ⟨by assumption, rfl⟩

theorem slotTick_slot {ctx : Ctx} {st st' : Gloas.BeaconState P} (h : slotTick ctx st = .ok st') :
    st'.slot.toNat = st.slot.toNat + 1 := by
  obtain ⟨st1, next, -, -, -, hn, hc⟩ := slotTick_cases h
  rcases hc with ⟨-, rfl⟩ | ⟨-, a, b, st2, -, -, -, rfl⟩ <;> exact hn

theorem slotLoop_slot {ctx : Ctx} :
    ∀ (n : Nat) (st st' : Gloas.BeaconState P), slotLoop ctx n st = .ok st' →
      st'.slot.toNat = st.slot.toNat + n
  | 0, st, st', h => by cases h; rfl
  | n + 1, st, st', h => by
    obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
    have := slotLoop_slot n x st' h
    rw [slotTick_slot hx] at this
    omega

/-- `process_slots` ends at the requested slot. -/
theorem processSlots_slot_eq {ctx : Ctx} {st st' : Gloas.BeaconState P} {T : U64}
    (h : Gloas.processSlots ctx st T = .ok st') : st'.slot = T := by
  obtain ⟨hlt, hl⟩ := processSlots_slotLoop h
  have := slotLoop_slot _ _ _ hl
  exact U64.ext_toNat (by omega)

/-! ## A payment entry, tracked by its slot -/

/-- The window index of the payment entry of virtual slot `s`. A bid at slot `t` is tracked at the
virtual slot `t + SLOTS_PER_EPOCH` (`payIdx_shift`: then this is `settle_builder_payment`'s
`payment_index`, CL:1795-1801): `SLOTS_PER_EPOCH + t % SLOTS_PER_EPOCH` while `t` is in the current
epoch, `t % SLOTS_PER_EPOCH` while it is in the previous epoch, none once it is older. The shift by one
epoch also names every entry of an anchor state, including a first-half entry at epoch `0`. -/
def payIdx (s : Nat) (st : Gloas.BeaconState P) : Option Nat :=
  if s / P.SLOTS_PER_EPOCH = curEpoch st + 1 then some (P.SLOTS_PER_EPOCH + s % P.SLOTS_PER_EPOCH)
  else if s / P.SLOTS_PER_EPOCH = curEpoch st then some (s % P.SLOTS_PER_EPOCH)
  else none

/-- `payIdx` at the virtual slot `t + SLOTS_PER_EPOCH` of a real slot `t`: the spec's window index of
`t` (`settle_builder_payment`'s `payment_index`). -/
theorem payIdx_shift (hspe : 0 < P.SLOTS_PER_EPOCH) (t : Nat) (st : Gloas.BeaconState P) :
    payIdx (t + P.SLOTS_PER_EPOCH) st =
      if t / P.SLOTS_PER_EPOCH = curEpoch st then some (P.SLOTS_PER_EPOCH + t % P.SLOTS_PER_EPOCH)
      else if t / P.SLOTS_PER_EPOCH + 1 = curEpoch st then some (t % P.SLOTS_PER_EPOCH)
      else none := by
  unfold payIdx
  rw [Nat.add_div_right _ hspe, Nat.add_mod_right]
  simp only [Nat.add_right_cancel_iff]

/-- The payment entry at the window index of virtual slot `s`. -/
def cell (s : Nat) (st : Gloas.BeaconState P) : Option Gloas.BuilderPendingPayment :=
  (payIdx s st).bind fun k => st.builder_pending_payments.toArray[k]?

/-- An entry is the tracked payment's: non-empty, carrying the withdrawal `w`. -/
def Ours (w : Gloas.BuilderPendingWithdrawal) (p : Gloas.BuilderPendingPayment) : Prop :=
  p ≠ Gloas.BuilderPendingPayment.empty ∧ p.withdrawal = w

/-- **The payment of virtual slot `s` recording withdrawal `w` is live at `st`**: the entry at its
window index is non-empty and carries `w`. -/
def LiveAt (s : Nat) (w : Gloas.BuilderPendingWithdrawal) (st : Gloas.BeaconState P) : Prop :=
  ∃ p, cell s st = some p ∧ Ours w p

theorem not_liveAt_of_none {s : Nat} {w : Gloas.BuilderPendingWithdrawal} {st : Gloas.BeaconState P}
    (h : payIdx s st = none) : ¬ LiveAt s w st := by
  rintro ⟨p, hp, -⟩
  simp [cell, h] at hp

theorem not_liveAt_of_empty {s : Nat} {w : Gloas.BuilderPendingWithdrawal} {st : Gloas.BeaconState P}
    (h : cell s st = some Gloas.BuilderPendingPayment.empty) :
    ¬ LiveAt s w st := by
  rintro ⟨p, hp, hne, -⟩
  rw [h] at hp; cases hp
  exact hne rfl

theorem payIdx_none_of_le {s : Nat} {st : Gloas.BeaconState P}
    (h : s / P.SLOTS_PER_EPOCH + 1 ≤ curEpoch st) : payIdx s st = none := by
  unfold payIdx
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- An evaluating epoch tick at `st`: `process_slot`, then the epoch boundary with the
pre-rotation state `a` satisfying `E st a`. -/
def EvalAt (ctx : Ctx) (E : Gloas.BeaconState P → Gloas.BeaconState P → Prop)
    (st : Gloas.BeaconState P) : Prop :=
  ∃ st1 next a, Gloas.processSlot st = .ok st1 ∧
    st1.slot.add? U64.one "process_slots: state.slot + 1" = .ok next ∧
    next.toNat % P.SLOTS_PER_EPOCH = 0 ∧ epochPrefix ctx st1 = .ok a ∧ E st a

/-- Some iteration of the `n`-iteration slot loop from `st` is an evaluating epoch tick. -/
def RotEval (ctx : Ctx) (E : Gloas.BeaconState P → Gloas.BeaconState P → Prop) :
    Nat → Gloas.BeaconState P → Prop
  | 0, _ => False
  | n + 1, st => EvalAt ctx E st ∨ ∃ st', slotTick ctx st = .ok st' ∧ RotEval ctx E n st'

/-- **The rotation evaluates the payment** (CL:1724-1726): at the epoch boundary that moves slot
`s`'s epoch out of the window, the entry at its index is live, and its weight reaches the quorum
of the pre-rotation state (`b = true`) or does not (`b = false`). -/
def QEv (s : Nat) (w : Gloas.BuilderPendingWithdrawal) (b : Bool) (x a : Gloas.BeaconState P) : Prop :=
  s / P.SLOTS_PER_EPOCH = curEpoch x ∧ ∃ p q, cell s x = some p ∧ Ours w p ∧
    Gloas.getBuilderPaymentQuorumThreshold a = .ok q ∧ decide (q ≤ p.weight) = b

/-- One slot iteration keeps the tracked entry, empties it (a bid in the next epoch, whose
index the shift empties), or moves the slot out of the window (`payIdx = none`): it was already
out, or this is the evaluating rotation. -/
theorem slotTick_track (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat}
    {st st' : Gloas.BeaconState P} (h : slotTick ctx st = .ok st') :
    cell s st' = cell s st ∨
      (payIdx s st = none ∧ cell s st' = some Gloas.BuilderPendingPayment.empty) ∨
      (payIdx s st' = none ∧ (payIdx s st = none ∨
        (s / P.SLOTS_PER_EPOCH = curEpoch st ∧ EvalAt ctx (fun _ a => ∃ b,
          Gloas.processBuilderPendingPayments ctx.cfg a = .ok b) st))) := by
  obtain ⟨st1, next, h1, hn, f1, hnext, hc⟩ := slotTick_cases h
  rcases hc with ⟨hne, rfl⟩ | ⟨h0, a, b, st2, ha, hb, hsuf, rfl⟩
  · left
    rw [hnext] at hne
    obtain ⟨hdiv, -⟩ := div_succ_of_mod_ne hne
    have hcur : curEpoch { st1 with slot := next } = curEpoch st := by
      unfold curEpoch; simp only []; rw [hnext, hdiv]
    unfold cell payIdx; rw [hcur]; simp only []; rw [f1.2.1]
  · have fa := epochPrefix_invFrame ha
    have fb := epochSuffix_invFrame hsuf
    obtain ⟨-, -, -, -, hP⟩ := processBuilderPendingPayments_frame hb
    have hsz : a.builder_pending_payments.toArray.size = 2 * P.SLOTS_PER_EPOCH :=
      a.builder_pending_payments.size_eq
    have hpa : a.builder_pending_payments = st.builder_pending_payments := by rw [fa.2.1, f1.2.1]
    have hp2 : ({ st2 with slot := next } : Gloas.BeaconState P).builder_pending_payments.toArray =
        a.builder_pending_payments.toArray.extract P.SLOTS_PER_EPOCH
          a.builder_pending_payments.toArray.size ++
        Array.replicate P.SLOTS_PER_EPOCH Gloas.BuilderPendingPayment.empty := by
      show st2.builder_pending_payments.toArray = _
      rw [fb.2.1, hP]
    have hcur : curEpoch { st2 with slot := next } = curEpoch st + 1 := by
      unfold curEpoch; simp only []; rw [hnext]; rw [hnext] at h0
      exact Nat.succ_div_of_mod_eq_zero h0
    have hm := Nat.mod_lt s hspe
    by_cases e0 : s / P.SLOTS_PER_EPOCH = curEpoch st + 1
    · left
      unfold cell payIdx
      rw [hcur, ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left e0]
      simp only [Option.bind_some]
      rw [hp2, shifted_lo hsz hm, hpa]
    · by_cases e1 : s / P.SLOTS_PER_EPOCH = curEpoch st
      · right; right
        refine ⟨by unfold payIdx; rw [hcur, ite_eq_right (by omega), ite_eq_right (by omega)], Or.inr ⟨e1,
          st1, next, a, h1, hn, h0, ha, b, hb⟩⟩
      · by_cases e2 : s / P.SLOTS_PER_EPOCH = curEpoch st + 2
        · right; left
          refine ⟨by unfold payIdx; rw [ite_eq_right e0, ite_eq_right e1], ?_⟩
          unfold cell payIdx
          rw [hcur, ite_eq_left e2]
          simp only [Option.bind_some]
          rw [hp2]; exact shifted_hi hsz (by omega) (by omega)
        · right; right
          refine ⟨by unfold payIdx; rw [hcur, ite_eq_right e2, ite_eq_right (by omega)],
            Or.inl (by unfold payIdx; rw [ite_eq_right e0, ite_eq_right e1])⟩

/-- Liveness only ends along the slot loop. -/
theorem slotTick_live_back (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat}
    {w : Gloas.BuilderPendingWithdrawal} {st st' : Gloas.BeaconState P}
    (h : slotTick ctx st = .ok st') (hl : LiveAt s w st') : LiveAt s w st := by
  rcases slotTick_track (s := s) hspe h with e | e | ⟨e, -⟩
  · obtain ⟨p, hp, hpw⟩ := hl; exact ⟨p, e ▸ hp, hpw⟩
  · exact absurd hl (not_liveAt_of_empty e.2)
  · exact absurd hl (not_liveAt_of_none e)

theorem slotLoop_live_back (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat}
    {w : Gloas.BuilderPendingWithdrawal} :
    ∀ (n : Nat) (st st' : Gloas.BeaconState P), slotLoop ctx n st = .ok st' →
      LiveAt s w st' → LiveAt s w st
  | 0, st, st', h, hl => by cases h; exact hl
  | n + 1, st, st', h, hl => by
    obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
    exact slotTick_live_back hspe hx (slotLoop_live_back hspe n x st' h hl)

theorem curEpoch_mono {a b : Gloas.BeaconState P} (h : a.slot.toNat ≤ b.slot.toNat) :
    curEpoch a ≤ curEpoch b := Nat.div_le_div_right h

theorem evalAt_cur {ctx : Ctx} {E : Gloas.BeaconState P → Gloas.BeaconState P → Prop}
    {st x : Gloas.BeaconState P} (he : EvalAt ctx E st) (hx : slotTick ctx st = .ok x) :
    curEpoch x = curEpoch st + 1 := by
  obtain ⟨st1, next, a, h1, hn, h0, -, -⟩ := he
  have f1 : InvFrame st st1 := processSlot_invFrame _ _ h1
  have hnext : next.toNat = st.slot.toNat + 1 := by
    rw [U64.toNat_add? hn, f1.2.2.2.2.2.2.1]; rfl
  unfold curEpoch
  rw [slotTick_slot hx]
  rw [hnext] at h0
  exact Nat.succ_div_of_mod_eq_zero h0

/-- **Along the slot loop, a live payment stays where it is, or a rotation evaluates it.** -/
theorem slotLoop_track (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat}
    {w : Gloas.BuilderPendingWithdrawal} :
    ∀ (n : Nat) (st st' : Gloas.BeaconState P), slotLoop ctx n st = .ok st' → LiveAt s w st →
      cell s st' = cell s st ∨ RotEval ctx (QEv s w true) n st ∨ RotEval ctx (QEv s w false) n st
  | 0, st, st', h, _ => by cases h; exact Or.inl rfl
  | n + 1, st, st', h, hl => by
    obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
    rcases slotTick_track (s := s) hspe hx with e | ⟨e, -⟩ | ⟨-, e | ⟨e1, st1, next, a, h1, hn, h0, ha, b, hb⟩⟩
    · have hlx : LiveAt s w x := by obtain ⟨p, hp, hpw⟩ := hl; exact ⟨p, e ▸ hp, hpw⟩
      rcases slotLoop_track hspe n x st' h hlx with e' | e' | e'
      · exact Or.inl (e'.trans e)
      · exact Or.inr (Or.inl (Or.inr ⟨x, hx, e'⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨x, hx, e'⟩))
    · exact absurd hl (not_liveAt_of_none e)
    · exact absurd hl (not_liveAt_of_none e)
    · obtain ⟨p, hp, hpw⟩ := hl
      obtain ⟨-, q, hq, -⟩ := processBuilderPendingPayments_frame hb
      by_cases hqw : q ≤ p.weight
      · exact Or.inr (Or.inl (Or.inl ⟨st1, next, a, h1, hn, h0, ha, e1, p, q, hp, hpw, hq,
          by simpa using hqw⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨st1, next, a, h1, hn, h0, ha, e1, p, q, hp, hpw, hq,
          by simpa using hqw⟩))

theorem rotEval_live (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat}
    {w : Gloas.BuilderPendingWithdrawal} {b : Bool} :
    ∀ (n : Nat) (st : Gloas.BeaconState P), RotEval ctx (QEv s w b) n st → LiveAt s w st
  | 0, _, h => h.elim
  | n + 1, st, h => by
    rcases h with ⟨_, _, _, _, _, _, _, -, p, q, hp, hpw, -⟩ | ⟨x, hx, h⟩
    · exact ⟨p, hp, hpw⟩
    · exact slotTick_live_back hspe hx (rotEval_live hspe n x h)

theorem rotEval_cur_le {ctx : Ctx} {s : Nat} {w : Gloas.BuilderPendingWithdrawal} {b : Bool} :
    ∀ (n : Nat) (st : Gloas.BeaconState P), RotEval ctx (QEv s w b) n st →
      curEpoch st ≤ s / P.SLOTS_PER_EPOCH
  | 0, _, h => h.elim
  | n + 1, st, h => by
    rcases h with ⟨_, _, _, _, _, _, _, e, -⟩ | ⟨x, hx, h⟩
    · exact e.symm.le
    · have := rotEval_cur_le n x h
      have := curEpoch_mono (a := st) (b := x) (by rw [slotTick_slot hx]; omega)
      omega

/-- After the evaluating rotation, the slot is out of the window for the rest of the loop. -/
theorem rotEval_end_none {ctx : Ctx} {s : Nat} {w : Gloas.BuilderPendingWithdrawal} {b : Bool} :
    ∀ (n : Nat) (st st' : Gloas.BeaconState P), RotEval ctx (QEv s w b) n st →
      slotLoop ctx n st = .ok st' → payIdx s st' = none
  | 0, _, _, h, _ => h.elim
  | n + 1, st, st', h, hl => by
    obtain ⟨x, hx, hl⟩ := bind_eq_ok_iff.mp hl
    rcases h with he | ⟨x', hx', h⟩
    · have hc := evalAt_cur he hx
      obtain ⟨_, _, _, _, _, _, _, e, -⟩ := he
      have hs := slotLoop_slot _ _ _ hl
      have := curEpoch_mono (a := x) (b := st') (by omega)
      exact payIdx_none_of_le (by omega)
    · rw [hx] at hx'; cases hx'
      exact rotEval_end_none n x st' h hl

/-- **At most one verdict**: a rotation cannot both reach and miss the quorum. -/
theorem rotEval_unique {ctx : Ctx} {s : Nat} {w : Gloas.BuilderPendingWithdrawal} :
    ∀ (n : Nat) (st : Gloas.BeaconState P), RotEval ctx (QEv s w true) n st →
      RotEval ctx (QEv s w false) n st → False
  | 0, _, h, _ => h.elim
  | n + 1, st, h, h' => by
    rcases h with he | ⟨x, hx, h⟩ <;> rcases h' with he' | ⟨x', hx', h'⟩
    · obtain ⟨st1, next, a, h1, hn, -, ha, -, p, q, hp, -, hq, hd⟩ := he
      obtain ⟨st1', next', a', h1', hn', -, ha', -, p', q', hp', -, hq', hd'⟩ := he'
      rw [h1] at h1'; cases h1'
      rw [hn] at hn'; cases hn'
      rw [ha] at ha'; cases ha'
      rw [hq] at hq'; cases hq'
      rw [hp] at hp'; cases hp'
      rw [hd] at hd'; cases hd'
    · have := evalAt_cur he hx'
      have := rotEval_cur_le n x' h'
      obtain ⟨_, _, _, _, _, _, _, e, -⟩ := he
      omega
    · have := evalAt_cur he' hx
      have := rotEval_cur_le n x h
      obtain ⟨_, _, _, _, _, _, _, e, -⟩ := he'
      omega
    · rw [hx] at hx'; cases hx'
      exact rotEval_unique n x h h'

end Blanc.Lift.BuilderRequest
