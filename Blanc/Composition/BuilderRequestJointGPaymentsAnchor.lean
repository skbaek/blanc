import Blanc.Composition.BuilderRequestJointGPaymentsAnchorCore

/-!
# B5(iii), the anchor half: headlines

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B5 (iii), SF-4).

* pending withdrawals: `TrackPos` (the queue position of `builder_pending_withdrawals[k]` before each
  step) and `withdrawal_fate` (removed by exactly one step's `process_withdrawals`, or still queued);
* **`ValidJointG.anchor_payment_fate`**: every entry pending at a Gloas anchor has exactly one
  destination of its kind;
* **`ValidJointG.anchor_witness_charged_once`**: the appends attributable to an anchor witness bid
  number at most one.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## Pending withdrawals: position in the queue -/

section Queue

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {sf : GJointState P}

/-- **The step's `process_withdrawals` removes the first `d` builder pending withdrawals** of the
queue it reads (the entries `get_builder_withdrawals` took, CL:2084-2086). -/
def _root_.Blanc.GloasStepData.Drops (B : GloasStepData (P := P) cfg ccfg bls) (d : Nat) : Prop :=
  ∃ s1 s2 s3 : Gloas.BeaconState P,
    Gloas.processParentExecutionPayload (gloasCtx ccfg bls) B.postSlots B.block.message = .ok s1 ∧
    Gloas.processBlockHeader s1 B.block.message = .ok s2 ∧ Gloas.processWithdrawals s2 = .ok s3 ∧
    s3.builder_pending_withdrawals.toArray.toList = s2.builder_pending_withdrawals.toArray.toList.drop d ∧
    d ≤ s2.builder_pending_withdrawals.toArray.toList.length

theorem _root_.Blanc.GloasStepData.drops_exists (B : GloasStepData (P := P) cfg ccfg bls) :
    ∃ d, B.Drops d := by
  obtain ⟨s1, s2, s3, -, -, -, -, h1, h2, h3, -⟩ := processBlock_phases B.processBlock
  obtain ⟨⟨k, hk⟩, -⟩ := processWithdrawals_wq h3
  refine ⟨min k s2.builder_pending_withdrawals.toArray.toList.length, s1, s2, s3, h1, h2, h3, ?_,
    Nat.min_le_right _ _⟩
  rw [hk]
  rcases Nat.le_total k s2.builder_pending_withdrawals.toArray.toList.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le h, List.drop_length]

theorem _root_.Blanc.GloasStepData.drops_unique (B : GloasStepData (P := P) cfg ccfg bls) {d d' : Nat}
    (h : B.Drops d) (h' : B.Drops d') : d = d' := by
  obtain ⟨s1, s2, s3, h1, h2, h3, e, hle⟩ := h
  obtain ⟨t1, t2, t3, g1, g2, g3, e', hle'⟩ := h'
  rw [h1] at g1; cases g1
  rw [h2] at g2; cases g2
  rw [h3] at g3; cases g3
  have := congrArg List.length e
  have := congrArg List.length e'
  simp only [List.length_drop] at *
  omega

/-- **The position of the anchor's `builder_pending_withdrawals[k]` before step `i`**: `k` at the
anchor, then less what each step's `process_withdrawals` removed ahead of it. -/
def TrackPos (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf) (k : Nat) : Nat → Nat → Prop
  | 0, p => p = k
  | i + 1, p' => ∃ p, ∃ B : GloasStepData (P := P) cfg ccfg bls, ∃ d, TrackPos run k i p ∧
      run.steps[i]? = some (.gloas B) ∧ B.Drops d ∧ d ≤ p ∧ p' = p - d

variable {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf} {k : Nat}

theorem trackPos_fun : ∀ {i p p' : Nat}, TrackPos run k i p → TrackPos run k i p' → p = p'
  | 0, p, p', h, h' => (h : p = k).trans (h' : p' = k).symm
  | i + 1, _, _, h, h' => by
    obtain ⟨q, B, d, hq, hB, hd, -, rfl⟩ := h
    obtain ⟨q', B', d', hq', hB', hd', -, rfl⟩ := h'
    rw [hB] at hB'; cases hB'
    rw [trackPos_fun hq hq', B.drops_unique hd hd']

theorem trackPos_prev : ∀ {i p : Nat}, TrackPos run k i p → ∀ j, j ≤ i → ∃ q, TrackPos run k j q
  | 0, p, h, j, hj => ⟨p, by rw [show j = 0 by omega]; exact h⟩
  | i + 1, p, h, j, hj => by
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact ⟨p, h⟩
    · obtain ⟨q, -, -, hq, -⟩ := h
      exact trackPos_prev hq j (by omega)

end Queue

/-! ## The anchor entries of a valid joint chain -/

section Headline

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {checkpoint : BlockChain}
  {final : GJointState P}

/-- The latest bid pays: a positive value from an external builder. -/
def LatestPays (a : Gloas.BeaconState P) : Prop :=
  U64.zero < a.latest_execution_payload_bid.value ∧
    a.latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD

/-- The virtual slot of the anchor's payments entry at index `idx`. -/
def anchorVs (a : Gloas.BeaconState P) (idx : Nat) : Nat := P.SLOTS_PER_EPOCH * curEpoch a + idx

theorem payIdx_anchorVs (hspe : 0 < P.SLOTS_PER_EPOCH) {idx : Nat} (hidx : idx < 2 * P.SLOTS_PER_EPOCH) :
    payIdx (anchorVs a idx) a = some idx := by
  unfold payIdx anchorVs
  by_cases h : P.SLOTS_PER_EPOCH ≤ idx
  · have e1 : (P.SLOTS_PER_EPOCH * curEpoch a + idx) / P.SLOTS_PER_EPOCH = curEpoch a + 1 := by
      rw [show P.SLOTS_PER_EPOCH * curEpoch a + idx =
        (idx - P.SLOTS_PER_EPOCH) + P.SLOTS_PER_EPOCH * (curEpoch a + 1) by rw [Nat.mul_add]; omega]
      rw [Nat.add_mul_div_left _ _ hspe, Nat.div_eq_of_lt (by omega)]; omega
    have e2 : (P.SLOTS_PER_EPOCH * curEpoch a + idx) % P.SLOTS_PER_EPOCH = idx - P.SLOTS_PER_EPOCH := by
      rw [show P.SLOTS_PER_EPOCH * curEpoch a + idx =
        (idx - P.SLOTS_PER_EPOCH) + P.SLOTS_PER_EPOCH * (curEpoch a + 1) by rw [Nat.mul_add]; omega]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_left e1, e2]; congr 1; omega
  · have e1 : (P.SLOTS_PER_EPOCH * curEpoch a + idx) / P.SLOTS_PER_EPOCH = curEpoch a := by
      rw [show P.SLOTS_PER_EPOCH * curEpoch a + idx = idx + P.SLOTS_PER_EPOCH * curEpoch a by omega]
      rw [Nat.add_mul_div_left _ _ hspe, Nat.div_eq_of_lt (by omega)]; omega
    have e2 : (P.SLOTS_PER_EPOCH * curEpoch a + idx) % P.SLOTS_PER_EPOCH = idx := by
      rw [show P.SLOTS_PER_EPOCH * curEpoch a + idx = idx + P.SLOTS_PER_EPOCH * curEpoch a by omega]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_right (by omega), ite_eq_left e1, e2]

/-- A step's settled parent is older than its block. -/
theorem _root_.Blanc.GloasStepData.lbh_lt (D : GloasStepData (P := P) cfg ccfg bls) :
    D.postSlots.latest_block_header.slot.toNat < D.block.message.slot.toNat := by
  obtain ⟨s1, s2, -, -, -, -, -, h1, h2, -⟩ := processBlock_phases D.processBlock
  have hlt := processBlockHeader_lt h2
  rcases processParentExecutionPayload_cases h1 with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact hlt
  · rw [(parentFull_frame ha hd he hs).2.2.2.2.1] at hlt; exact hlt

/-- What a withdrawal destination means for the anchor's `builder_pending_withdrawals[k]`. -/
def AnchorFate.holdsW {sf : GJointState P} {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf}
    {e : AnchorEntry a} (k : Nat) : AnchorFate run e → Prop
  | .paid j' => ∃ p, ∃ B : GloasStepData (P := P) cfg ccfg bls, ∃ d, TrackPos run k j' p ∧
      run.steps[j']? = some (.gloas B) ∧ B.Drops d ∧ p < d
  | .stillQueued => ∃ p, TrackPos run k run.steps.length p
  | _ => False

/-- What an anchor entry's destination means. -/
def AnchorFate.holds {sf : GJointState P} {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf}
    {e : AnchorEntry a} (f : AnchorFate run e) : Prop :=
  match e with
  | .payment idx => ∃ p, a.builder_pending_payments.toArray[idx]? = some p ∧
      f.holdsT (anchorVs a idx) p.withdrawal False
  | .latestBid => (LatestPays a ∧ f.holdsT (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)
        (bidWithdrawal a.latest_execution_payload_bid) True) ∨
      (¬ LatestPays a ∧ f = .noPayment)
  | .withdrawal k => f.holdsW k

section WithdrawalFate

variable {sf : GJointState P} {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf} {k : Nat}

theorem not_paid_of_later {j i q : Nat}
    (hp : (AnchorFate.paid j : AnchorFate run (.withdrawal k)).holdsW k) (hq : TrackPos run k i q)
    (hji : j < i) : False := by
  obtain ⟨p, B, d, hpj, hB, hd, hlt⟩ := hp
  obtain ⟨q', hq'⟩ := trackPos_prev hq (j + 1) (by omega)
  obtain ⟨p', B', d', hp', hB', hd', hle, -⟩ := hq'
  rw [hB] at hB'; cases hB'
  rw [trackPos_fun hp' hpj, B.drops_unique hd' hd] at hle
  omega

/-- **The fate of an anchor pending withdrawal**: removed by exactly one step's
`process_withdrawals`, or still queued at the end. -/
theorem withdrawal_fate : ∃! f : AnchorFate run (.withdrawal k), f.Allowed ∧ f.holdsW k := by
  have key : ∀ i, i ≤ run.steps.length →
      (∃ j < i, (AnchorFate.paid j : AnchorFate run (.withdrawal k)).holdsW k) ∨
        ∃ p, TrackPos run k i p := by
    intro i
    induction i with
    | zero => exact fun _ => Or.inr ⟨k, rfl⟩
    | succ i ih =>
      intro hi
      rcases ih (by omega) with ⟨j, hj, hp⟩ | ⟨p, hp⟩
      · exact Or.inl ⟨j, by omega, hp⟩
      · obtain ⟨B, hB⟩ := anchor_step (run := run) (i := i) (by omega)
        obtain ⟨d, hd⟩ := B.drops_exists
        by_cases hdp : d ≤ p
        · exact Or.inr ⟨p - d, p, B, d, hp, hB, hd, hdp, rfl⟩
        · exact Or.inl ⟨i, by omega, p, B, d, hp, hB, hd, by omega⟩
  rcases key run.steps.length le_rfl with ⟨j, hj, hp⟩ | ⟨p, hp⟩
  · refine ⟨.paid j, ⟨trivial, hp⟩, fun g hg' => ?_⟩
    obtain ⟨-, hg⟩ := hg'
    cases g
    all_goals try exact (hg : False).elim
    · rename_i j'
      rcases lt_trichotomy j j' with h | rfl | h
      · obtain ⟨q, -, -, hq, -⟩ := hg
        exact (not_paid_of_later hp hq h).elim
      · rfl
      · obtain ⟨q, -, -, hq, -⟩ := hp
        exact (not_paid_of_later hg hq h).elim
    · obtain ⟨q, hq⟩ := hg
      exact (not_paid_of_later hp hq hj).elim
  · refine ⟨.stillQueued, ⟨trivial, p, hp⟩, fun g hg' => ?_⟩
    obtain ⟨-, hg⟩ := hg'
    cases g
    all_goals try exact (hg : False).elim
    · rename_i j'
      have hj' : j' < run.steps.length := by
        obtain ⟨_, _, _, _, hB, _⟩ := hg
        exact (List.getElem?_eq_some_iff.mp hB).1
      exact (not_paid_of_later hg hp hj').elim
    · rfl

end WithdrawalFate

/-- **B5(iii), the anchor half: every entry pending at a Gloas anchor has exactly one destination
of its kind.** -/
theorem ValidJointG.anchor_payment_fate (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final)
    (e : AnchorEntry a) (he : e.Present) : ∃! f : AnchorFate v.run e, f.Allowed ∧ f.holds := by
  have hspe : 0 < P.SLOTS_PER_EPOCH := by have := v.slotsPerEpoch; omega
  have hinv : GAnchorInv (GJointState.gloas a ex pa) := v.anchorInv
  obtain ⟨-, -, -, -, -, g7, g8, -, fe⟩ := hinv
  have hLs : a.latest_execution_payload_bid.slot.toNat = a.latest_block_header.slot.toNat := by
    rw [g8.1]
  cases e with
  | payment idx =>
    obtain ⟨p, hp, hne, hnotL⟩ := he
    have hidx : idx < 2 * P.SLOTS_PER_EPOCH := by
      have := (Array.getElem?_eq_some_iff.mp hp).1
      rwa [a.builder_pending_payments.size_eq] at this
    have hpi := payIdx_anchorVs (a := a) hspe hidx
    have hvsle : anchorVs a idx ≤ a.slot.toNat + P.SLOTS_PER_EPOCH := by
      have hdm := Nat.div_add_mod a.slot.toNat P.SLOTS_PER_EPOCH
      unfold anchorVs curEpoch
      by_cases h : P.SLOTS_PER_EPOCH ≤ idx
      · have : idx - P.SLOTS_PER_EPOCH ≤ a.slot.toNat % P.SLOTS_PER_EPOCH := by
          by_contra hc
          have he := fe.1 (idx - P.SLOTS_PER_EPOCH) (by omega) (by omega)
          rw [show P.SLOTS_PER_EPOCH + (idx - P.SLOTS_PER_EPOCH) = idx by omega, hp] at he
          exact hne (Option.some.inj he)
        omega
      · omega
    have T : AnchorTrack v.run (anchorVs a idx) p.withdrawal False :=
      { hspe := hspe, hq := v.quorumPositive
        hvs := fun i B hB => by have := anchor_slot_lt hB; omega
        hL := False.elim
        hnotL := fun _ heq => by
          have h1 := hpi
          rw [heq, payIdx_shift hspe, ← hLs] at h1
          have hb : bidIndex a = some idx := h1
          obtain ⟨E, hE, -, hE'⟩ := g7 idx hb
          rw [hp] at hE; cases hE
          rcases hE' with ⟨-, hw⟩ | rfl
          · exact hnotL ⟨hb, hw⟩
          · exact hne rfl
        hlat := False.elim }
    have hl : LiveAt (anchorVs a idx) p.withdrawal a := ⟨p, by rw [cell_of_payIdx hpi, hp], hne, rfl⟩
    obtain ⟨f, hf⟩ := T.exists_live (e := .payment idx) hl
    refine ⟨f, ⟨?_, p, hp, hf⟩, fun g hg' => ?_⟩
    · cases f <;> simp only [AnchorFate.Allowed] <;> simp only [AnchorFate.holdsT] at hf <;>
        exact hf.1.elim
    · obtain ⟨-, p', hp', hg⟩ := hg'
      rw [hp] at hp'; cases hp'
      exact T.unique hg hf
  | latestBid =>
    by_cases hpay : LatestPays a
    · have T : AnchorTrack v.run (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)
          (bidWithdrawal a.latest_execution_payload_bid) True :=
        { hspe := hspe, hq := v.quorumPositive
          hvs := fun i B hB => by
            obtain ⟨B0, hB0⟩ := anchor_step (run := v.run) (i := 0)
              (by have := (List.getElem?_eq_some_iff.mp hB).1; omega)
            have h0 := B0.lbh_lt
            rw [B0.postSlots_lbh] at h0
            have hpre : B0.preB = a := by
              rcases anchor_pred hB0 with ⟨-, hp⟩ | ⟨h, -⟩
              · exact hp
              · omega
            rw [hpre, ← hLs] at h0
            rcases Nat.eq_zero_or_pos i with rfl | hpos
            · rw [hB0] at hB; cases hB; omega
            · have := slot_lt' v.run hB0 hB hpos; omega
          hL := fun _ => by rw [hLs]
          hnotL := fun h => (h trivial).elim
          hlat := fun _ => ⟨g7, fe, rfl⟩ }
      have ex : ∃ f : AnchorFate v.run .latestBid, f.holdsT
          (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)
          (bidWithdrawal a.latest_execution_payload_bid) True := by
        by_cases hl : LiveAt (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)
            (bidWithdrawal a.latest_execution_payload_bid) a
        · exact T.exists_live hl
        · exact AnchorTrack.exists_dead trivial hl
      obtain ⟨f, hf⟩ := ex
      refine ⟨f, ⟨?_, Or.inl ⟨hpay, hf⟩⟩, fun g hg' => ?_⟩
      · cases f <;> simp only [AnchorFate.Allowed] <;> simp only [AnchorFate.holdsT] at hf
      · obtain ⟨-, hg⟩ := hg'
        rcases hg with ⟨-, hg⟩ | ⟨hn, -⟩
        · exact T.unique hg hf
        · exact (hn hpay).elim
    · refine ⟨.noPayment, ⟨trivial, Or.inr ⟨hpay, rfl⟩⟩, fun g hg' => ?_⟩
      obtain ⟨-, hg⟩ := hg'
      rcases hg with ⟨h, -⟩ | ⟨-, rfl⟩
      · exact (hpay h).elim
      · rfl
  | withdrawal k =>
    obtain ⟨f, hf, hu⟩ := withdrawal_fate (run := v.run) (k := k)
    exact ⟨f, hf, fun g hg => hu g hg⟩

end Headline

/-! ## Each anchor witness bid is charged at most once -/

/-- At most one nonzero term, each at most `1`: the sum is at most `1`. -/
theorem sum_range_le_one {f : Nat → Nat} (h1 : ∀ i, f i ≤ 1)
    (hu : ∀ i j, f i ≠ 0 → f j ≠ 0 → i = j) : ∀ n, ((List.range n).map f).sum ≤ 1 ∧
      (((List.range n).map f).sum ≠ 0 → ∃ i < n, f i ≠ 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hz : f n = 0
    · rw [hz, Nat.add_zero]
      exact ⟨ih.1, fun h => let ⟨i, hi, hp⟩ := ih.2 h; ⟨i, by omega, hp⟩⟩
    · have h0 : ((List.range n).map f).sum = 0 := by
        by_contra hne
        obtain ⟨i, hi, hp⟩ := ih.2 hne
        have := hu i n hp hz
        omega
      rw [h0]
      exact ⟨by have := h1 n; omega, fun _ => ⟨n, by omega, hz⟩⟩

section Charged

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {checkpoint : BlockChain}
  {final : GJointState P}

/-- The witness reference of an anchor entry. -/
def AnchorEntry.ref : AnchorEntry a → WitnessRef
  | .payment idx => .payment idx
  | .withdrawal k => .withdrawal k
  | .latestBid => .latest

/-- The appends of an anchor entry's withdrawal to `builder_pending_withdrawals` at step `i`: a
quorum rotation, the settlement, or the direct append (a pending withdrawal is never appended
again). -/
noncomputable def anchorAppendsAt {sf : GJointState P} (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf)
    (e : AnchorEntry a) (i : Nat) : Nat := by
  classical
  exact (if (AnchorFate.quorum i : AnchorFate run e).holds then 1 else 0) +
    (if (AnchorFate.settled i : AnchorFate run e).holds then 1 else 0) +
    (if (AnchorFate.directAppend i : AnchorFate run e).holds then 1 else 0)

/-- The appends of an anchor entry along the run. -/
noncomputable def anchorAppends {sf : GJointState P} (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf)
    (e : AnchorEntry a) : Nat :=
  ((List.range run.steps.length).map (anchorAppendsAt run e)).sum

/-- **The appends attributable to the witness bid `β`**: those of every anchor entry whose witness is
`β` (payments entries, pending withdrawals, the latest bid). -/
noncomputable def witnessAppends {sf : GJointState P} (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf)
    (W : GloasBidWitness a) (β : Gloas.SignedExecutionPayloadBid) : Nat := by
  classical
  exact ((List.range (2 * P.SLOTS_PER_EPOCH)).map fun idx =>
      if (AnchorEntry.payment idx : AnchorEntry a).Present ∧ W.bid (.payment idx) = some β then
        anchorAppends run (.payment idx) else 0).sum +
    ((List.range a.builder_pending_withdrawals.toArray.size).map fun k =>
      if W.bid (.withdrawal k) = some β then anchorAppends run (.withdrawal k) else 0).sum +
    (if W.bid .latest = some β then anchorAppends run .latestBid else 0)

theorem anchorAppends_le_one (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final)
    {e : AnchorEntry a} (he : e.Present) : anchorAppends v.run e ≤ 1 := by
  classical
  obtain ⟨f₀, -, hu⟩ := v.anchor_payment_fate e he
  -- a holding appending destination is allowed
  have al : ∀ f : AnchorFate v.run e, f.holds →
      (∃ i, f = .quorum i ∨ f = .settled i ∨ f = .directAppend i) → f.Allowed := by
    rintro f hf ⟨i, rfl | rfl | rfl⟩ <;> cases e <;> simp only [AnchorFate.Allowed] <;>
      simp only [AnchorFate.holds, AnchorFate.holdsT, AnchorFate.holdsW] at hf <;>
      try (obtain ⟨_, _, hf⟩ := hf; exact hf.1.elim)
  have uq : ∀ {f g : AnchorFate v.run e}, f.holds → g.holds →
      (∃ i, f = .quorum i ∨ f = .settled i ∨ f = .directAppend i) →
      (∃ i, g = .quorum i ∨ g = .settled i ∨ g = .directAppend i) → f = g := by
    intro f g hf hg ef eg
    exact (hu f ⟨al f hf ef, hf⟩).trans (hu g ⟨al g hg eg, hg⟩).symm
  have h1 : ∀ i, anchorAppendsAt v.run e i ≤ 1 := by
    intro i
    unfold anchorAppendsAt
    split_ifs <;> first
      | omega
      | (have := uq (f := .quorum i) (g := .settled i) (by assumption) (by assumption)
          ⟨i, Or.inl rfl⟩ ⟨i, Or.inr (Or.inl rfl)⟩; cases this)
      | (have := uq (f := .quorum i) (g := .directAppend i) (by assumption) (by assumption)
          ⟨i, Or.inl rfl⟩ ⟨i, Or.inr (Or.inr rfl)⟩; cases this)
      | (have := uq (f := .settled i) (g := .directAppend i) (by assumption) (by assumption)
          ⟨i, Or.inr (Or.inl rfl)⟩ ⟨i, Or.inr (Or.inr rfl)⟩; cases this)
  have pos : ∀ i, anchorAppendsAt v.run e i ≠ 0 → ∃ f : AnchorFate v.run e, f.holds ∧
      (f = .quorum i ∨ f = .settled i ∨ f = .directAppend i) := by
    intro i h
    unfold anchorAppendsAt at h
    split_ifs at h
    all_goals first
      | omega
      | exact ⟨.quorum i, by assumption, Or.inl rfl⟩
      | exact ⟨.settled i, by assumption, Or.inr (Or.inl rfl)⟩
      | exact ⟨.directAppend i, by assumption, Or.inr (Or.inr rfl)⟩
  refine (sum_range_le_one h1 (fun i j hi hj => ?_) _).1
  obtain ⟨f, hf, ef⟩ := pos i hi
  obtain ⟨g, hg, eg⟩ := pos j hj
  have := uq hf hg ⟨i, ef⟩ ⟨j, eg⟩
  subst this
  rcases ef with rfl | rfl | rfl <;> rcases eg with h | h | h <;> cases h <;> rfl

theorem anchorAppends_withdrawal {sf : GJointState P} (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf)
    (k : Nat) : anchorAppends run (.withdrawal k) = 0 := by
  unfold anchorAppends
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  unfold anchorAppendsAt
  have hq : ¬ (AnchorFate.quorum i : AnchorFate run (.withdrawal k)).holds := id
  have hs : ¬ (AnchorFate.settled i : AnchorFate run (.withdrawal k)).holds := id
  have hd : ¬ (AnchorFate.directAppend i : AnchorFate run (.withdrawal k)).holds := id
  simp only [hq, hs, hd, ite_false, Nat.add_zero]

theorem anchorAppends_noPay {sf : GJointState P} (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf)
    (hn : ¬ LatestPays a) : anchorAppends run .latestBid = 0 := by
  classical
  unfold anchorAppends
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  unfold anchorAppendsAt
  have hq : ¬ (AnchorFate.quorum i : AnchorFate run .latestBid).holds := by
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hn h
    · cases h
  have hs : ¬ (AnchorFate.settled i : AnchorFate run .latestBid).holds := by
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hn h
    · cases h
  have hd : ¬ (AnchorFate.directAppend i : AnchorFate run .latestBid).holds := by
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hn h
    · cases h
  simp only [hq, hs, hd, ite_false, Nat.add_zero]

/-- **B5(iii): each anchor witness bid is charged at most once.** The appends to
`builder_pending_withdrawals` attributable to a witness bid `β` of `anchorWitness` (over every anchor
entry it witnesses: payments entries, pending withdrawals, the latest bid) number at most one: the
injective witnesses give `β` one entry (the latest bid's own live entry is the `.latestBid` entry),
and that entry has one destination. -/
theorem ValidJointG.anchor_witness_charged_once
    (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final) (β : Gloas.SignedExecutionPayloadBid) :
    witnessAppends v.run (v.anchorWitness : GloasBidWitness a) β ≤ 1 := by
  classical
  have W : GloasBidWitness a := v.anchorWitness
  set Wv : GloasBidWitness a := v.anchorWitness with hWv
  unfold witnessAppends
  set fP : Nat → Nat := fun idx =>
    if (AnchorEntry.payment idx : AnchorEntry a).Present ∧ Wv.bid (.payment idx) = some β then
      anchorAppends v.run (.payment idx) else 0 with hfP
  have hWd : ((List.range a.builder_pending_withdrawals.toArray.size).map fun k =>
      if Wv.bid (.withdrawal k) = some β then anchorAppends v.run (.withdrawal k) else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    simp only [anchorAppends_withdrawal, ite_self]
  rw [hWd, Nat.add_zero]
  have h1 : ∀ i, fP i ≤ 1 := by
    intro i
    simp only [hfP]
    split_ifs with h
    · exact anchorAppends_le_one v h.1
    · omega
  have hu : ∀ i j, fP i ≠ 0 → fP j ≠ 0 → i = j := by
    intro i j hi hj
    simp only [hfP] at hi hj
    split_ifs at hi hj with h h'
    · rcases Wv.injective _ _ β h.2 h'.2 with e | ⟨e, -⟩ | ⟨e, -⟩
      · cases e; rfl
      · cases e
      · cases e
    all_goals omega
  obtain ⟨hP1, hP2⟩ := sum_range_le_one h1 hu (2 * P.SLOTS_PER_EPOCH)
  have hL1 : (if Wv.bid .latest = some β then anchorAppends v.run .latestBid else 0) ≤ 1 := by
    split_ifs
    · exact anchorAppends_le_one v trivial
    · omega
  by_cases hP0 : ((List.range (2 * P.SLOTS_PER_EPOCH)).map fP).sum = 0
  · rw [hP0]; omega
  by_cases hL0 : (if Wv.bid .latest = some β then anchorAppends v.run .latestBid else 0) = 0
  · rw [hL0]; omega
  have hlat : Wv.bid .latest = some β := by
    by_contra h
    exact hL0 (by simp only [h, ite_false])
  exfalso
  obtain ⟨idx, -, hidx⟩ := hP2 hP0
  simp only [hfP] at hidx
  split_ifs at hidx with hpres
  · obtain ⟨⟨p, hp, hne, hnotL⟩, hβ⟩ := hpres
    rw [ite_eq_left hlat] at hL0
    rcases Wv.injective _ _ β hβ hlat with e | ⟨e, -⟩ | ⟨-, k, e, hk⟩
    · cases e
    · cases e
    · cases e
      by_cases hpay : LatestPays a
      · obtain ⟨β0, h0, -, hm⟩ := Wv.latest hpay.2
        rw [hlat] at h0; cases h0
        obtain ⟨β1, h1', -, hw⟩ := Wv.payment idx p hp hne
        rw [hβ] at h1'; cases h1'
        exact hnotL ⟨hk, by rw [hw, hm]⟩
      · exact hL0 (anchorAppends_noPay v.run hpay)
  · exact hidx rfl

end Charged

end Blanc.Lift.BuilderRequest
