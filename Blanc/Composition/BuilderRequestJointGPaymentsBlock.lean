import Blanc.Composition.BuilderRequestJointGPaymentsTrack

/-!
# Tracking one builder payment entry through a Gloas block and a Gloas run step

Goal `eip8282-gloas-cross-layer-v1`, B5(iii) support (Plans `recon/statements.md` B5 (iii), rev 3.1),
continuing `BuilderRequestJointGPaymentsTrack`:

* the parent settlement settles exactly the parent slot's window index (`applyParentPrefix_idx`,
  `parent_cell`, `parent_settles`), the bid writes only its own slot's entry (`mid_cell`, `bid_live`),
  and the operations only keep, empty or re-weigh entries (`ops_live_back`, `OpsClear`);
* consecutive run steps (`GJointRun.link`, `GJointRun.last_post`);
* per Gloas step: `live_back` (liveness only ends), `flip_cases` (where it ends), and
  `no_quorum_latest` (G3-07: no quorum while the bid is still the latest bid).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset}

/-! ## The parent settlement settles the entry at the parent slot's window index -/

/-- `apply_parent_execution_payload`'s payment step, with the index it settles: the window index of
the parent's slot (`payIdx`), or, when that slot is out of the window, the direct append of a
paying `L` or nothing. -/
theorem applyParentPrefix_idx (hspe0 : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s a : Gloas.BeaconState P} {r : Gloas.ExecutionRequests}
    (h : Gloas.applyParentPrefix ctx s r = .ok a) :
    ∃ x, InvFrame x a ∧
      ((∃ idx : U64, payIdx (s.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) s = some idx.toNat ∧
          Gloas.settleBuilderPayment s idx = .ok x) ∨
        (payIdx (s.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) s = none ∧
          ((U64.zero < s.latest_execution_payload_bid.value ∧ x = directAppend s) ∨ x = s))) := by
  unfold Gloas.applyParentPrefix at h
  obtain ⟨pe, hpe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨cur, hcur, h⟩ := bind_eq_ok_iff.mp h
  have hpeN := computeEpochAtSlot_toNat hpe
  have hcN := getCurrentEpoch_toNat hcur
  have hsN := c64_toNat hspe
  dsimp only at h
  split at h
  · rename_i hc
    have hc' : pe = cur := U64.beq_eq_true_iff.mp hc
    obtain ⟨m, hm, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨idx, hidx, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
    refine ⟨x, ?_, Or.inl ⟨idx, ?_, hx⟩⟩
    · obtain ⟨l1, hl1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨l2, hl2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨l3, hl3, h⟩ := bind_eq_ok_iff.mp h
      cases h
      exact invFrame.trans (StepRel.forIn_array_rel invFrame id (fun _ _ => ok_pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) _ _ hl1)
        (invFrame.trans (StepRel.forIn_array_rel invFrame id (fun _ _ => by gvcg; exact ok_pure (processWithdrawalRequest_invFrame _ _ _ _ ‹_›)) _ _ hl2)
          (StepRel.forIn_array_rel invFrame id (fun _ _ => by gvcg; exact ok_pure (processConsolidationRequest_invFrame _ _ _ _ ‹_›)) _ _ hl3))
    · rw [U64.toNat_add? hidx, U64.toNat_mod? hm, hsN]
      rw [payIdx_shift hspe0]
      rw [ite_eq_left (by rw [← hpeN, hc', hcN])]
  · rename_i hc
    obtain ⟨prev, hprev, h⟩ := bind_eq_ok_iff.mp h
    have hpv := getPreviousEpoch_toNat hcur hprev
    have hne : pe.toNat ≠ cur.toNat := fun e => hc (U64.beq_eq_true_iff.mpr (U64.ext_toNat e))
    split at h
    · rename_i hp
      have hp' : pe = prev := U64.beq_eq_true_iff.mp hp
      obtain ⟨idx, hidx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
      refine ⟨x, ?_, Or.inl ⟨idx, ?_, hx⟩⟩
      · obtain ⟨l1, hl1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨l2, hl2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨l3, hl3, h⟩ := bind_eq_ok_iff.mp h
        cases h
        exact invFrame.trans (StepRel.forIn_array_rel invFrame id (fun _ _ => ok_pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) _ _ hl1)
          (invFrame.trans (StepRel.forIn_array_rel invFrame id (fun _ _ => by gvcg; exact ok_pure (processWithdrawalRequest_invFrame _ _ _ _ ‹_›)) _ _ hl2)
            (StepRel.forIn_array_rel invFrame id (fun _ _ => by gvcg; exact ok_pure (processConsolidationRequest_invFrame _ _ _ _ ‹_›)) _ _ hl3))
      · rw [U64.toNat_mod? hidx, hsN]
        have hc0 : cur.toNat ≠ 0 := fun h0 => hne (by rw [hp', hpv.1 h0, h0])
        have h1 := hpv.2 hc0
        rw [← hp'] at h1
        rw [payIdx_shift hspe0]
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    · rename_i hp
      have hd := direct_epochs hpeN hcN hpv hc hp
      have hnone : payIdx (s.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) s = none := by
        rw [payIdx_shift hspe0, ite_eq_right (by omega), ite_eq_right (by omega)]
      split at h
      · rename_i hv
        refine ⟨_, ?_, Or.inr ⟨hnone, Or.inl ⟨hv, rfl⟩⟩⟩
        obtain ⟨l1, hl1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨l2, hl2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨l3, hl3, h⟩ := bind_eq_ok_iff.mp h
        cases h
        exact invFrame.trans (StepRel.forIn_array_rel invFrame id (fun _ _ => ok_pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) _ _ hl1)
          (invFrame.trans (StepRel.forIn_array_rel invFrame id (fun _ _ => by gvcg; exact ok_pure (processWithdrawalRequest_invFrame _ _ _ _ ‹_›)) _ _ hl2)
            (StepRel.forIn_array_rel invFrame id (fun _ _ => by gvcg; exact ok_pure (processConsolidationRequest_invFrame _ _ _ _ ‹_›)) _ _ hl3))
      · refine ⟨s, ?_, Or.inr ⟨hnone, Or.inr rfl⟩⟩
        obtain ⟨l1, hl1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨l2, hl2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨l3, hl3, h⟩ := bind_eq_ok_iff.mp h
        cases h
        exact invFrame.trans (StepRel.forIn_array_rel invFrame id (fun _ _ => ok_pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) _ _ hl1)
          (invFrame.trans (StepRel.forIn_array_rel invFrame id (fun _ _ => by gvcg; exact ok_pure (processWithdrawalRequest_invFrame _ _ _ _ ‹_›)) _ _ hl2)
            (StepRel.forIn_array_rel invFrame id (fun _ _ => by gvcg; exact ok_pure (processConsolidationRequest_invFrame _ _ _ _ ‹_›)) _ _ hl3))

/-! ## The block, phase by phase -/

theorem payIdx_congr {s : Nat} {st st' : Gloas.BeaconState P} (h : st'.slot = st.slot) :
    payIdx s st' = payIdx s st := by
  unfold payIdx curEpoch; rw [h]

theorem cell_congr {s : Nat} {st st' : Gloas.BeaconState P} (h : st'.slot = st.slot)
    (hp : st'.builder_pending_payments = st.builder_pending_payments) : cell s st' = cell s st := by
  unfold cell; rw [payIdx_congr h, hp]

theorem cell_of_payIdx {s k : Nat} {st : Gloas.BeaconState P} (h : payIdx s st = some k) :
    cell s st = st.builder_pending_payments.toArray[k]? := by
  unfold cell; rw [h]; rfl

theorem liveAt_of_cell {s : Nat} {w : Gloas.BuilderPendingWithdrawal} {st st' : Gloas.BeaconState P}
    (h : cell s st' = cell s st) (hl : LiveAt s w st') : LiveAt s w st := by
  obtain ⟨p, hp, hpw⟩ := hl; exact ⟨p, h ▸ hp, hpw⟩

theorem eq_of_div_mod {a b n : Nat} (h1 : a / n = b / n) (h2 : a % n = b % n) : a = b := by
  rw [← Nat.div_add_mod a n, ← Nat.div_add_mod b n, h1, h2]

/-- Two slots with the same window index at the same state are equal. -/
theorem payIdx_inj {a b k : Nat} {st : Gloas.BeaconState P} (ha : payIdx a st = some k)
    (hb : payIdx b st = some k) : a = b := by
  unfold payIdx at ha hb
  rcases Nat.eq_zero_or_pos P.SLOTS_PER_EPOCH with h0 | hpos
  · simp only [h0, Nat.div_zero, Nat.mod_zero, Nat.zero_add] at ha hb
    split_ifs at ha hb <;> simp only [Option.some.injEq] at ha hb <;> omega
  · have ma := Nat.mod_lt a hpos
    have mb := Nat.mod_lt b hpos
    split_ifs at ha hb <;> simp only [Option.some.injEq] at ha hb <;>
      first | omega | exact eq_of_div_mod (n := P.SLOTS_PER_EPOCH) (by omega) (by omega)

/-- **The parent settlement** keeps the tracked entry, or empties it at the parent slot's window
index (`payIdx` of `latest_block_header.slot`) of a FULL parent. -/
theorem parent_cell (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat} {m s1 : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (h : Gloas.processParentExecutionPayload ctx m blk = .ok s1) :
    s1.slot = m.slot ∧
      (cell s s1 = cell s m ∨
        (parentFull m blk = true ∧ payIdx s m ≠ none ∧
          payIdx s m = payIdx (m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) m ∧
          cell s s1 = some Gloas.BuilderPendingPayment.empty)) := by
  rcases processParentExecutionPayload_cases h with ⟨rfl, _⟩ | ⟨hf, a, d, e, ha, hd, he, hs⟩
  · exact ⟨rfl, Or.inl rfl⟩
  have hfull : parentFull m blk = true := by simp [parentFull, hf]
  have fr := parentFull_frame ha hd he hs
  refine ⟨fr.2.2.2.2.2, ?_⟩
  have hda : d.builder_pending_payments = a.builder_pending_payments :=
    forIn_yield_inv (fun m => m.builder_pending_payments = a.builder_pending_payments) _
      (fun m _ m' hI hm => by
        show _ = _
        rw [(depReq_cases hm).1]; exact hI) _ _ _ hd rfl
  have hed : e.builder_pending_payments = d.builder_pending_payments :=
    forIn_yield_inv (fun m => m.builder_pending_payments = d.builder_pending_payments) _
      (fun m _ m' hI hm => by
        show _ = _
        rw [(exitReq_cases hm).1]; exact hI) _ _ _ he rfl
  have hs' := (applyParentSuffix_post hs).2.1
  obtain ⟨x, fx, hx⟩ := applyParentPrefix_idx hspe ha
  have e1 : s1.builder_pending_payments = x.builder_pending_payments := by
    rw [hs', hed, hda, fx.2.1]
  have hsl : payIdx s s1 = payIdx s m := payIdx_congr fr.2.2.2.2.2
  rcases hx with ⟨idx, hidx, hset⟩ | ⟨-, (⟨-, rfl⟩ | rfl)⟩
  · obtain ⟨-, p, -, -, -, hemp, hoth⟩ := settleBuilderPayment_frame hset
    cases hk : payIdx s m with
    | none => left; unfold cell; rw [hsl, hk]; rfl
    | some k =>
      by_cases hki : k = idx.toNat
      · subst hki
        right
        refine ⟨hfull, by simp, by rw [hidx], ?_⟩
        unfold cell; rw [hsl, hk]; simp only [Option.bind_some]; rw [e1, hemp]
      · left
        unfold cell; rw [hsl, hk]; simp only [Option.bind_some]; rw [e1, hoth k hki]
  · left; unfold cell; rw [hsl, e1]; rfl
  · left; unfold cell; rw [hsl, e1]

/-- A FULL parent whose slot is in the window has its entry emptied. -/
theorem parent_settles (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {m s1 : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (h : Gloas.processParentExecutionPayload ctx m blk = .ok s1) (hfull : parentFull m blk = true)
    {k : Nat} (hk : payIdx (m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) m = some k) :
    s1.builder_pending_payments.toArray[k]? = some Gloas.BuilderPendingPayment.empty := by
  rcases processParentExecutionPayload_cases h with ⟨_, hne⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact absurd (by simpa [parentFull] using hfull) hne
  have hda : d.builder_pending_payments = a.builder_pending_payments :=
    forIn_yield_inv (fun m => m.builder_pending_payments = a.builder_pending_payments) _
      (fun m _ m' hI hm => by
        show _ = _
        rw [(depReq_cases hm).1]; exact hI) _ _ _ hd rfl
  have hed : e.builder_pending_payments = d.builder_pending_payments :=
    forIn_yield_inv (fun m => m.builder_pending_payments = d.builder_pending_payments) _
      (fun m _ m' hI hm => by
        show _ = _
        rw [(exitReq_cases hm).1]; exact hI) _ _ _ he rfl
  have hs' := (applyParentSuffix_post hs).2.1
  obtain ⟨x, fx, hx⟩ := applyParentPrefix_idx hspe ha
  have e1 : s1.builder_pending_payments = x.builder_pending_payments := by
    rw [hs', hed, hda, fx.2.1]
  rcases hx with ⟨idx, hidx, hset⟩ | ⟨hn, -⟩
  · rw [hk] at hidx; cases hidx
    obtain ⟨-, p, -, -, -, hemp, -⟩ := settleBuilderPayment_frame hset
    rw [e1, hemp]
  · rw [hk] at hn; cases hn

/-- Between the parent settlement and the operations (header, withdrawals, the block's bid,
RANDAO, eth1 data), the entry of an earlier slot is untouched: the bid writes only its own slot's
entry. -/
theorem mid_cell (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat} {s1 s2 s3 s4 s5 s6 : Gloas.BeaconState P}
    {blk : Gloas.BeaconBlock P}
    (h2 : Gloas.processBlockHeader s1 blk = .ok s2) (h3 : Gloas.processWithdrawals s2 = .ok s3)
    (h4 : Gloas.processExecutionPayloadBid ctx s3 blk.body.signed_execution_payload_bid = .ok s4)
    (h5 : Gloas.processRandao ctx s4 blk.body = .ok s5) (h6 : Gloas.processEth1Data s5 blk.body = .ok s6)
    (hs : s ≠ blk.slot.toNat + P.SLOTS_PER_EPOCH) : cell s s6 = cell s s1 ∧ s6.slot = s1.slot := by
  obtain ⟨hbs, -, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  obtain ⟨-, -, -, -, -, -, -, hs4, -, -, hnp, hpp⟩ := b4
  have f5 := processRandao_invFrame _ _ _ _ h5
  have f6 := processEth1Data_invFrame _ _ _ h6
  have sl2 : s2.slot = s1.slot := by rw [hm2]
  have sl3 : s3.slot = s1.slot := by rw [w3.2.2.2.1, sl2]
  have c2 : cell s s2 = cell s s1 := cell_congr sl2 (by rw [hm2])
  have c3 : cell s s3 = cell s s2 := cell_congr w3.2.2.2.1 w3.2.2.2.2.1
  have c4 : cell s s4 = cell s s3 := by
    by_cases hv : U64.zero < blk.body.signed_execution_payload_bid.message.value
    · obtain ⟨pi, -, hoth⟩ := hpp hv
      have hp4 := payIdx_congr (s := s) hs4
      cases hk : payIdx s s3 with
      | none => unfold cell; rw [hp4, hk]; rfl
      | some k =>
        have hkK : k ≠ P.SLOTS_PER_EPOCH + s3.slot.toNat % P.SLOTS_PER_EPOCH := by
          rintro rfl
          have hK : payIdx (s3.slot.toNat + P.SLOTS_PER_EPOCH) s3 =
              some (P.SLOTS_PER_EPOCH + s3.slot.toNat % P.SLOTS_PER_EPOCH) := by
            rw [payIdx_shift hspe]; unfold curEpoch; rw [ite_eq_left rfl]
          exact hs ((payIdx_inj hk hK).trans (by rw [sl3, hbs]))
        unfold cell; rw [hp4, hk]; simp only [Option.bind_some]; exact hoth k hkK
    · exact cell_congr hs4 (hnp hv)
  have c6 : cell s s6 = cell s s4 :=
    (cell_congr f6.2.2.2.2.2.2.1 f6.2.1).trans (cell_congr f5.2.2.2.2.2.2.1 f5.2.1)
  refine ⟨c6.trans (c4.trans (c3.trans c2)), ?_⟩
  rw [f6.2.2.2.2.2.2.1, f5.2.2.2.2.2.2.1, hs4, sl3]

/-- **The block's own paying bid makes its payment live.** -/
theorem bid_live (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s3 s4 : Gloas.BeaconState P} {sb : Gloas.SignedExecutionPayloadBid}
    (h4 : Gloas.processExecutionPayloadBid ctx s3 sb = .ok s4) (hv : U64.zero < sb.message.value) :
    LiveAt (sb.message.slot.toNat + P.SLOTS_PER_EPOCH) (bidWithdrawal sb.message) s4 := by
  obtain ⟨-, hsl, -, -, -, -, -, hs4, -, -, -, hpp⟩ := processExecutionPayloadBid_post h4
  obtain ⟨pi, hk, -⟩ := hpp hv
  have hidx : payIdx (sb.message.slot.toNat + P.SLOTS_PER_EPOCH) s4 =
      some (P.SLOTS_PER_EPOCH + s3.slot.toNat % P.SLOTS_PER_EPOCH) := by
    rw [payIdx_shift hspe]; unfold curEpoch; rw [hs4, hsl, ite_eq_left rfl]
  refine ⟨_, by rw [cell_of_payIdx hidx, hk], fun h => ?_, rfl⟩
  have h2 := congrArg (fun q : Gloas.BuilderPendingPayment => q.withdrawal.amount) h
  simp only [bidWithdrawal] at h2
  rw [h2] at hv
  exact absurd hv (by decide)

/-- The operations only keep, empty, or re-weigh an entry. -/
theorem ops_live_back {ctx : Ctx} {s : Nat} {w : Gloas.BuilderPendingWithdrawal}
    {s6 s7 : Gloas.BeaconState P} {body : Gloas.BeaconBlockBody P} {ps : U64}
    (h7 : Gloas.processOperations ctx s6 body ps = .ok s7) (hl : LiveAt s w s7) : LiveAt s w s6 := by
  obtain ⟨c7, -, hp7⟩ := processOperations_ops _ _ _ _ _ h7
  have hpi : payIdx s s7 = payIdx s s6 := payIdx_congr c7.2.2.2.2.1
  obtain ⟨p, hp, hpw⟩ := hl
  cases hk : payIdx s s6 with
  | none => rw [cell, hpi, hk] at hp; cases hp
  | some k =>
    rw [cell, hpi, hk] at hp
    simp only [Option.bind_some] at hp
    rcases hp7 k with e | e | ⟨p0, p', h0, h1, hst, -⟩
    · exact ⟨p, by rw [cell_of_payIdx hk, ← e, hp], hpw⟩
    · rw [e] at hp; cases hp
      exact absurd rfl hpw.1
    · rw [h1] at hp; cases hp
      refine ⟨p0, by rw [cell_of_payIdx hk, h0], fun h0e => ?_, hst.1.symm.trans hpw.2⟩
      subst h0e
      rcases hst.2.2 with e | e
      · exact hpw.1 e
      · exact absurd e (by decide)

/-- **The operations clear the payment** (CL:1579-1581, the only site that empties an entry
inside `process_operations`): live just before `process_operations`, not live just after. -/
def OpsClear (ctx : Ctx) (s : Nat) (w : Gloas.BuilderPendingWithdrawal) (m : Gloas.BeaconState P)
    (blk : Gloas.BeaconBlock P) : Prop :=
  ∃ s1 s2 s3 s4 s5 s6 s7 : Gloas.BeaconState P,
    Gloas.processParentExecutionPayload ctx m blk = .ok s1 ∧ Gloas.processBlockHeader s1 blk = .ok s2 ∧
    Gloas.processWithdrawals s2 = .ok s3 ∧
    Gloas.processExecutionPayloadBid ctx s3 blk.body.signed_execution_payload_bid = .ok s4 ∧
    Gloas.processRandao ctx s4 blk.body = .ok s5 ∧ Gloas.processEth1Data s5 blk.body = .ok s6 ∧
    Gloas.processOperations ctx s6 blk.body m.latest_block_header.slot = .ok s7 ∧
    LiveAt s w s6 ∧ ¬ LiveAt s w s7

theorem sync_cell {ctx : Ctx} {s : Nat} {s7 m' : Gloas.BeaconState P} {sa : SyncAggregate P}
    (h8 : Gloas.processSyncAggregate ctx s7 sa = .ok m') : cell s m' = cell s s7 := by
  have f8 := processSyncAggregate_invFrame _ _ _ _ h8
  exact cell_congr f8.2.2.2.2.2.2.1 f8.2.1

/-- **The block, for a payment of an earlier slot.** Liveness only ends; and when it ends, either
the parent settlement emptied the entry (the parent's slot is the payment's), or the operations
cleared it. -/
theorem block_track (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat} {w : Gloas.BuilderPendingWithdrawal} {m m' : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P} (h : Gloas.processBlock ctx m blk = .ok m')
    (hs : s ≠ blk.slot.toNat + P.SLOTS_PER_EPOCH) :
    (LiveAt s w m' → LiveAt s w m) ∧
      (LiveAt s w m → ¬ LiveAt s w m' →
        (parentFull m blk = true ∧ s = m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) ∨ OpsClear ctx s w m blk) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  obtain ⟨-, hc1⟩ := parent_cell hspe (s := s) h1
  obtain ⟨c6, -⟩ := mid_cell hspe h2 h3 h4 h5 h6 hs
  have c8 := sync_cell (s := s) h8
  have back1 : LiveAt s w s1 → LiveAt s w m := by
    rcases hc1 with e | ⟨-, -, -, e⟩
    · exact liveAt_of_cell e
    · exact fun hl => absurd hl (not_liveAt_of_empty e)
  refine ⟨fun hl => back1 (liveAt_of_cell c6 (ops_live_back h7 (liveAt_of_cell c8 hl))),
    fun hl hn => ?_⟩
  rcases hc1 with e | ⟨hfull, hne, heq, -⟩
  · right
    refine ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, ?_, fun h7l => hn ?_⟩
    · obtain ⟨p, hp, hpw⟩ := hl; exact ⟨p, by rw [c6, e, hp], hpw⟩
    · obtain ⟨p, hp, hpw⟩ := h7l; exact ⟨p, by rw [c8, hp], hpw⟩
  · left
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hne
    exact ⟨hfull, payIdx_inj hk (heq ▸ hk)⟩

/-! ## Runs: consecutive steps -/

section Run

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

theorem _root_.Blanc.GJointRun.last_post {s₀ : GJointState P} :
    {sf : GJointState P} → (run : GJointRun cfg ccfg bls s₀ sf) → {i : Nat} →
    {A : GJointRunStep (P := P) cfg ccfg bls} → run.steps[i]? = some A → i + 1 = run.steps.length →
      A.postState = sf
  | _, .nil, _, _, h, _ => by simp only [GJointRun.steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run C hC, i, A, h, hl => by
    rw [GJointRun.steps_snoc] at h hl
    simp only [List.length_append, List.length_singleton] at hl
    rw [List.getElem?_append_right (by omega), List.getElem?_singleton] at h
    rw [ite_eq_left (by omega)] at h
    cases h; rfl

theorem _root_.Blanc.GJointRun.link {s₀ : GJointState P} :
    {sf : GJointState P} → (run : GJointRun cfg ccfg bls s₀ sf) → {i : Nat} →
    {A C : GJointRunStep (P := P) cfg ccfg bls} → run.steps[i]? = some A → run.steps[i + 1]? = some C →
      C.preState = A.postState
  | _, .nil, _, _, _, h, _ => by simp only [GJointRun.steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run B hB, i, A, C, hA, hC => by
    rw [GJointRun.steps_snoc] at hA hC
    have hi : i + 1 < run.steps.length + 1 := by
      have := (List.getElem?_eq_some_iff.mp hC).1; simpa using this
    by_cases hlt : i + 1 < run.steps.length
    · rw [List.getElem?_append_left hlt] at hC
      rw [List.getElem?_append_left (by omega)] at hA
      exact GJointRun.link run hA hC
    · rw [List.getElem?_append_right (by omega), List.getElem?_singleton, ite_eq_left (by omega)] at hC
      cases hC
      rw [List.getElem?_append_left (by omega)] at hA
      rw [hB]
      exact (GJointRun.last_post run hA (by omega)).symm

end Run

/-! ## A Gloas step, for a tracked payment -/

section Step

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-- The bid of a Gloas step's block. -/
abbrev _root_.Blanc.GloasStepData.bid (D : GloasStepData (P := P) cfg ccfg bls) :
    Gloas.ExecutionPayloadBid :=
  D.block.message.body.signed_execution_payload_bid.message

/-- The rotation inside the step's `process_slots` evaluates the payment of slot `s` (withdrawal
`w`) with verdict `b` (`true`: the quorum was reached). -/
def _root_.Blanc.GloasStepData.RotQ (D : GloasStepData (P := P) cfg ccfg bls) (s : Nat)
    (w : Gloas.BuilderPendingWithdrawal) (b : Bool) : Prop :=
  RotEval (gloasCtx ccfg bls) (QEv s w b) (D.block.message.slot.toNat - D.preB.slot.toNat) D.preB

theorem _root_.Blanc.GloasStepData.processBlock (D : GloasStepData (P := P) cfg ccfg bls) :
    Gloas.processBlock (gloasCtx ccfg bls) D.postSlots D.block.message = .ok D.postB :=
  applySignedBlockWith_ok D.transition

theorem _root_.Blanc.GloasStepData.postSlots_slot (D : GloasStepData (P := P) cfg ccfg bls) :
    D.postSlots.slot = D.block.message.slot := processSlots_slot_eq D.slots

theorem _root_.Blanc.GloasStepData.pre_lt (D : GloasStepData (P := P) cfg ccfg bls) :
    D.preB.slot.toNat < D.block.message.slot.toNat := (processSlots_slotLoop D.slots).1

theorem _root_.Blanc.GloasStepData.postB_slot (D : GloasStepData (P := P) cfg ccfg bls) :
    D.postB.slot = D.block.message.slot ∧ D.postB.latest_block_header.slot = D.block.message.slot := by
  have h := processBlock_slots D.processBlock
  rw [D.postSlots_slot] at h
  exact h

theorem _root_.Blanc.GloasStepData.postSlots_lbh (D : GloasStepData (P := P) cfg ccfg bls) :
    D.postSlots.latest_block_header.slot = D.preB.latest_block_header.slot :=
  processSlots_ind (ctx := gloasCtx ccfg bls)
    (fun m => m.latest_block_header.slot = D.preB.latest_block_header.slot)
    (fun _ _ _ _ hI f1 _ hc => (slotIter_core f1 hc).2.2.2.1.trans hI) D.slots rfl

theorem _root_.Blanc.GloasStepData.bid_slot (D : GloasStepData (P := P) cfg ccfg bls) :
    D.bid.slot = D.block.message.slot := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, -⟩ := processBlock_phases D.processBlock
  obtain ⟨hbs, -, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_wFrame _ _ h3
  obtain ⟨-, hsl, -⟩ := processExecutionPayloadBid_post h4
  rw [hsl, w3.2.2.2.1, show s2.slot = s1.slot by rw [hm2], hbs]

theorem _root_.Blanc.GloasStepData.postB_bid (D : GloasStepData (P := P) cfg ccfg bls) :
    D.postB.latest_execution_payload_bid = D.bid := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    processBlock_phases D.processBlock
  have hL4 := (processExecutionPayloadBid_post h4).1
  have f5 := processRandao_invFrame _ _ _ _ h5
  have f6 := processEth1Data_invFrame _ _ _ h6
  obtain ⟨c7, -, -⟩ := processOperations_ops _ _ _ _ _ h7
  have f8 := processSyncAggregate_invFrame _ _ _ _ h8
  rw [f8.2.2.2.1, c7.2.1, f6.2.2.2.1, f5.2.2.2.1, hL4]

/-- **A later step, for a payment of an earlier slot: liveness only ends.** -/
theorem _root_.Blanc.GloasStepData.live_back (D : GloasStepData (P := P) cfg ccfg bls)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s : Nat} {w : Gloas.BuilderPendingWithdrawal}
    (hs : s < D.block.message.slot.toNat + P.SLOTS_PER_EPOCH)
    (hl : LiveAt s w D.postB) :
    LiveAt s w D.preB := by
  obtain ⟨-, hloop⟩ := processSlots_slotLoop D.slots
  exact slotLoop_live_back hspe _ _ _ hloop
    ((block_track hspe D.processBlock (by omega)).1 hl)

/-- **Where a later step ends a live payment**: a rotation inside its `process_slots` (with
either verdict), the FULL settlement of the payment's own slot, or the operations. -/
theorem _root_.Blanc.GloasStepData.flip_cases (D : GloasStepData (P := P) cfg ccfg bls)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s : Nat} {w : Gloas.BuilderPendingWithdrawal}
    (hs : s < D.block.message.slot.toNat + P.SLOTS_PER_EPOCH)
    (hl : LiveAt s w D.preB) (hn : ¬ LiveAt s w D.postB) :
    D.RotQ s w true ∨ D.RotQ s w false ∨
      (parentFull D.postSlots D.block.message = true ∧ s = D.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH ∧
        LiveAt s w D.postSlots) ∨
      OpsClear (gloasCtx ccfg bls) s w D.postSlots D.block.message := by
  obtain ⟨-, hloop⟩ := processSlots_slotLoop D.slots
  rcases slotLoop_track hspe _ _ _ hloop hl with e | e | e
  · have hl' : LiveAt s w D.postSlots := liveAt_of_cell e.symm hl
    rcases (block_track hspe D.processBlock (by omega)).2 hl' hn with ⟨hf, he⟩ | hc
    · exact Or.inr (Or.inr (Or.inl ⟨hf, he, hl'⟩))
    · exact Or.inr (Or.inr (Or.inr hc))
  · exact Or.inl e
  · exact Or.inr (Or.inl e)

/-- A rotation verdict ends the payment before the block. -/
theorem _root_.Blanc.GloasStepData.rotQ_end (D : GloasStepData (P := P) cfg ccfg bls)
    {s : Nat} {w : Gloas.BuilderPendingWithdrawal} {b : Bool} (h : D.RotQ s w b) :
    payIdx s D.postSlots = none := by
  obtain ⟨-, hloop⟩ := processSlots_slotLoop D.slots
  exact rotEval_end_none _ _ _ h hloop

/-- The cleared entry was live after `process_slots`. -/
theorem opsClear_live (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat} {w : Gloas.BuilderPendingWithdrawal}
    {m : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (hs : s ≠ blk.slot.toNat + P.SLOTS_PER_EPOCH) (h : OpsClear ctx s w m blk) : LiveAt s w m := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, hl, -⟩ := h
  obtain ⟨-, hc1⟩ := parent_cell hspe (s := s) h1
  obtain ⟨c6, -⟩ := mid_cell hspe h2 h3 h4 h5 h6 hs
  have hl1 := liveAt_of_cell c6 hl
  rcases hc1 with e | ⟨-, -, -, e⟩
  · exact liveAt_of_cell e hl1
  · exact absurd hl1 (not_liveAt_of_empty e)

/-- The operations' clearing ends the payment for the rest of the block. -/
theorem opsClear_end {ctx : Ctx} {s : Nat} {w : Gloas.BuilderPendingWithdrawal}
    {m m' : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (hb : Gloas.processBlock ctx m blk = .ok m') (h : OpsClear ctx s w m blk) : ¬ LiveAt s w m' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, -, hn⟩ := h
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, g1, g2, g3, g4, g5, g6, g7, g8⟩ := processBlock_phases hb
  rw [h1] at g1; cases g1
  rw [h2] at g2; cases g2
  rw [h3] at g3; cases g3
  rw [h4] at g4; cases g4
  rw [h5] at g5; cases g5
  rw [h6] at g6; cases g6
  rw [h7] at g7; cases g7
  exact fun hl => hn (liveAt_of_cell (sync_cell g8) hl)

/-- The FULL settlement of the payment's own slot excludes a later clearing in the block, and ends
the payment. -/
theorem settle_excl (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat} {w : Gloas.BuilderPendingWithdrawal}
    {m m' : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (hb : Gloas.processBlock ctx m blk = .ok m') (hs : s ≠ blk.slot.toNat + P.SLOTS_PER_EPOCH)
    (hf : parentFull m blk = true) (hps : s = m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) (hl : LiveAt s w m) :
    ¬ OpsClear ctx s w m blk ∧ ¬ LiveAt s w m' := by
  obtain ⟨p, hp, -⟩ := hl
  obtain ⟨k, hk⟩ : ∃ k, payIdx s m = some k := by
    cases h : payIdx s m with
    | none => simp [cell, h] at hp
    | some k => exact ⟨k, rfl⟩
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, g1, g2, g3, g4, g5, g6, g7, g8⟩ := processBlock_phases hb
  have he := parent_settles hspe g1 hf (hps ▸ hk)
  obtain ⟨sl1, -⟩ := parent_cell hspe (s := s) g1
  have hc1 : cell s t1 = some Gloas.BuilderPendingPayment.empty := by
    rw [cell_of_payIdx (by rw [payIdx_congr sl1]; exact hk), he]
  have hn1 : ¬ LiveAt s w t1 := not_liveAt_of_empty hc1
  obtain ⟨c6, -⟩ := mid_cell hspe g2 g3 g4 g5 g6 hs
  have hn6 : ¬ LiveAt s w t6 := fun hl => hn1 (liveAt_of_cell c6 hl)
  refine ⟨fun hc => ?_, fun hl => hn6 (ops_live_back g7 (liveAt_of_cell (sync_cell g8) hl))⟩
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, -, hl6, -⟩ := hc
  rw [h1] at g1; cases g1
  rw [h2] at g2; cases g2
  rw [h3] at g3; cases g3
  rw [h4] at g4; cases g4
  rw [h5] at g5; cases g5
  rw [h6] at g6; cases g6
  exact hn6 hl6

end Step

/-! ## No quorum while the bid is still the latest bid (G3-07) -/

/-- The slot-loop invariant: G3-07 and FutureEmpty, with the latest bid at slot `s`. -/
def LatestAt (s : Nat) (st : Gloas.BeaconState P) : Prop :=
  NoLiveWeightOnLatestBid st ∧ FutureEmpty st ∧
    st.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH = s

theorem slotTick_latestAt (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat}
    {st st' : Gloas.BeaconState P} (h : slotTick ctx st = .ok st') (hI : LatestAt s st) :
    LatestAt s st' := by
  obtain ⟨st1, next, -, -, f1, hnext, hc⟩ := slotTick_cases h
  obtain ⟨st2, rfl, hc'⟩ : ∃ st2, st' = { st2 with slot := next } ∧
      ((st2 = st1 ∧ next.toNat % P.SLOTS_PER_EPOCH ≠ 0) ∨
        (next.toNat % P.SLOTS_PER_EPOCH = 0 ∧ Gloas.processEpoch ctx st1 = .ok st2)) := by
    rcases hc with ⟨hne, rfl⟩ | ⟨h0, a, b, st2, ha, hb, hsuf, rfl⟩
    · exact ⟨st1, rfl, Or.inl ⟨rfl, hne⟩⟩
    · refine ⟨st2, rfl, Or.inr ⟨h0, ?_⟩⟩
      rw [processEpoch_eq_split]
      simp only [ha, hb, hsuf, bind, Except.bind]
  obtain ⟨g7, fe⟩ := slotIter_noLiveWeight hspe ⟨hI.1, hI.2.1⟩ f1 hnext hc'
  exact ⟨g7, fe, by
    show st2.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH = s
    rw [(slotIter_core f1 hc').2.1]; exact hI.2.2⟩

/-- **While the bid is the latest bid, no rotation finds its entry at the quorum**: the entry of the
latest bid carries no weight (G3-07), and the quorum is positive. -/
theorem no_quorum_latest (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat} {w : Gloas.BuilderPendingWithdrawal} :
    ∀ (n : Nat) (st : Gloas.BeaconState P), LatestAt s st → ¬ RotEval ctx (QEv s w true) n st
  | 0, _, _, h => h
  | n + 1, st, hI, h => by
    rcases h with ⟨st1, next, a, -, -, -, -, -, p, q, hp, -, hq', hd⟩ | ⟨x, hx, h⟩
    · have hbi : bidIndex st = payIdx s st := by
        rw [← hI.2.2, payIdx_shift hspe]; rfl
      cases hk : payIdx s st with
      | none => simp [cell, hk] at hp
      | some k =>
        obtain ⟨E, hE, hw0, -⟩ := hI.1 k (by rw [hbi, hk])
        rw [cell_of_payIdx hk, hE] at hp
        have hpE : E = p := Option.some.inj hp
        rw [← hpE] at hd
        have hle : q.toNat ≤ E.weight.toNat := of_decide_eq_true hd
        rw [hw0] at hle
        have := quorum_pos hq hq'
        have hz : U64.zero.toNat = 0 := rfl
        omega
    · exact no_quorum_latest hq hspe n x (slotTick_latestAt hspe hx hI) h

end Blanc.Lift.BuilderRequest
