import Blanc.Composition.BuilderRequestJointGAppends

/-!
# B5(iii), the anchor half: charged at most once, counting what the anchor already queued

Goal `eip8282-charge-once-v1`, outcome C3. `ValidJointG.anchor_witness_charged_once` counts the appends along the run
attributable to a witness bid; an entry already in `builder_pending_withdrawals` at the anchor counts `0` there. The
question was whether a Gloas anchor may hold the latest bid's payment already appended (a quorum append before the
anchor), after which the run's first block appends it again by the old-parent branch.

**No new anchor premise is needed.** `GloasBidWitness.injective` ranges over every pair of references, and its only
exception pairs `.latest` with a `.payment` entry. So the witness of a pending withdrawal witnesses nothing else
(`QueuedSeparate`, `GloasBidWitness.queuedSeparate`): not another pending withdrawal, not a payments entry, not the
latest bid.

* `witnessQueued W β`: the positions of the anchor's `builder_pending_withdrawals` whose witness is `β`.
* **`ValidJointG.anchor_witness_charged_once_queued`**: `witnessQueued + witnessAppends ≤ 1`. For a witness bid, the
  entries already queued at the anchor plus the appends along the run number at most one.
* `GloasBidWitness.latest_queued_two_bids`: what an anchor with `L`'s withdrawal already queued must supply, read on
  the state: two distinct signed bids, both verified, one being `L` and the other recording the same withdrawal.
* `ValidJointG.anchor_direct_append_fresh`: when the run's first block appends `L`'s withdrawal by the old-parent
  branch, the bid it charges witnesses no entry queued at the anchor.
* `GloasStepData.direct_append_duplicates`: the transition itself does not look at the queue. A FULL old parent
  appends the latest bid's withdrawal whatever is queued, so a withdrawal equal to it and queued before the step is
  then in the list at two positions. Only the witnesses tell one bid appended twice from two bids of one value.

What the witness says, and does not. A witness is data the anchor supplies, not history. Separation says that the
charges at and after the anchor are matched one to one with distinct signed bids verified under the builders' keys.
It does not say where a queued entry came from: an anchor whose queued entry was in fact produced by `L` is admitted
exactly when the builder signed a second bid recording the same withdrawal. `WitnessMessagesInjective` is the
optional refinement from distinct signed bids to distinct bid messages
(`ValidJointG.anchor_message_charged_once`).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## The witness of a queued entry witnesses nothing else -/

/-- **A queued entry's witness is separate**: a witness bid of a pending builder withdrawal is the witness of no
other reference (no other pending withdrawal, no payments entry, not the latest bid). -/
def QueuedSeparate (bid : WitnessRef → Option Gloas.SignedExecutionPayloadBid) : Prop :=
  ∀ (k : Nat) (r : WitnessRef) (β : Gloas.SignedExecutionPayloadBid),
    bid (.withdrawal k) = some β → bid r = some β → r = .withdrawal k

section Witness

variable {a : Gloas.BeaconState P}

/-- **The anchor witnesses already separate the queued entries** (`GloasBidWitness.injective`: its exception pairs
`.latest` with a `.payment` entry only). -/
theorem GloasBidWitness.queuedSeparate (W : GloasBidWitness a) : QueuedSeparate W.bid := by
  intro k r β hk hr
  rcases W.injective _ _ β hk hr with e | ⟨e, -⟩ | ⟨-, k', e, -⟩
  · exact e.symm
  · cases e
  · cases e

/-- **The entries already queued at the anchor that `β` witnesses**: the positions `k` of the anchor's
`builder_pending_withdrawals` with witness `β`. -/
noncomputable def witnessQueued (W : GloasBidWitness a) (β : Gloas.SignedExecutionPayloadBid) : Nat := by
  classical
  exact ((List.range a.builder_pending_withdrawals.toArray.size).map fun k =>
    if W.bid (.withdrawal k) = some β then 1 else 0).sum

theorem witnessQueued_spec (W : GloasBidWitness a) (β : Gloas.SignedExecutionPayloadBid) :
    witnessQueued W β ≤ 1 ∧ (witnessQueued W β ≠ 0 →
      ∃ k < a.builder_pending_withdrawals.toArray.size, W.bid (.withdrawal k) = some β) := by
  classical
  unfold witnessQueued
  obtain ⟨h1, h2⟩ := sum_range_le_one
    (f := fun k => if W.bid (.withdrawal k) = some β then 1 else 0)
    (fun k => by split_ifs <;> omega)
    (fun i j hi hj => by
      have hi' : W.bid (.withdrawal i) = some β := by
        by_contra h
        exact hi (ite_eq_right h)
      have hj' : W.bid (.withdrawal j) = some β := by
        by_contra h
        exact hj (ite_eq_right h)
      cases W.queuedSeparate i _ β hi' hj'
      rfl)
    a.builder_pending_withdrawals.toArray.size
  refine ⟨h1, fun h => ?_⟩
  obtain ⟨k, hk, hne⟩ := h2 h
  refine ⟨k, hk, ?_⟩
  by_contra hc
  exact hne (ite_eq_right hc)

/-- A bid that witnesses no reference has no append along the run. -/
theorem witnessAppends_eq_zero {ex : BlockChain} {pa : ParentPayload P} {sf : GJointState P}
    (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf) (W : GloasBidWitness a)
    {β : Gloas.SignedExecutionPayloadBid}
    (hP : ∀ idx, W.bid (.payment idx) ≠ some β) (hL : W.bid .latest ≠ some β) :
    witnessAppends run W β = 0 := by
  classical
  unfold witnessAppends
  refine Nat.add_eq_zero_iff.mpr ⟨Nat.add_eq_zero_iff.mpr ⟨?_, ?_⟩, ite_eq_right hL⟩
  · apply List.sum_eq_zero
    intro x hx
    obtain ⟨idx, -, rfl⟩ := List.mem_map.mp hx
    exact ite_eq_right fun h => hP idx h.2
  · apply List.sum_eq_zero
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    simp only [anchorAppends_withdrawal, ite_self]

end Witness

/-! ## Charged at most once, counting the anchor's queue -/

section Charged

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {checkpoint : BlockChain}
  {final : GJointState P}

/-- **B5(iii): each anchor witness bid is charged at most once, counting what the anchor already queued.** For a
witness bid `β` of `anchorWitness`, the entries of the anchor's `builder_pending_withdrawals` that `β` witnesses
(`witnessQueued`) plus the appends to `builder_pending_withdrawals` along the run attributable to `β`
(`witnessAppends`: over the payments entries and the latest bid it witnesses) number at most one. In particular a
bid already queued at the anchor is not appended along the run, and the latest bid, if the run appends it, was not
queued. No premise beyond `ValidJointG`: the witnesses of a queued entry and of any other entry differ
(`GloasBidWitness.queuedSeparate`). -/
theorem ValidJointG.anchor_witness_charged_once_queued
    (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final) (β : Gloas.SignedExecutionPayloadBid) :
    witnessQueued (v.anchorWitness : GloasBidWitness a) β +
      witnessAppends v.run (v.anchorWitness : GloasBidWitness a) β ≤ 1 := by
  obtain ⟨h1, h2⟩ := witnessQueued_spec (v.anchorWitness : GloasBidWitness a) β
  by_cases h : witnessQueued (v.anchorWitness : GloasBidWitness a) β = 0
  · rw [h, Nat.zero_add]
    exact v.anchor_witness_charged_once β
  · obtain ⟨k, -, hk⟩ := h2 h
    have hs := GloasBidWitness.queuedSeparate (v.anchorWitness : GloasBidWitness a)
    have h0 := witnessAppends_eq_zero v.run (v.anchorWitness : GloasBidWitness a) (β := β)
      (fun idx hc => by cases hs k _ β hk hc) (fun hc => by cases hs k _ β hk hc)
    omega

/-- **An anchor with `L`'s withdrawal already queued supplies two signed bids.** At a Gloas state with witnesses
whose latest bid `L` is a builder's, if position `k` of `builder_pending_withdrawals` holds `L`'s withdrawal, then the
witnesses name two distinct signed bids, both verified at the state: `L` itself, and a second one recording the same
withdrawal. A reader checks the premise on the state by exhibiting the second bid. -/
theorem GloasBidWitness.latest_queued_two_bids (W : GloasBidWitness a)
    (hL : a.latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD) {k : Nat}
    (hk : a.builder_pending_withdrawals.toArray[k]? = some (bidWithdrawal a.latest_execution_payload_bid)) :
    ∃ β β' : Gloas.SignedExecutionPayloadBid, β ≠ β' ∧
      W.bid .latest = some β ∧ BidSigned a β ∧ β.message = a.latest_execution_payload_bid ∧
      W.bid (.withdrawal k) = some β' ∧ BidSigned a β' ∧
      bidWithdrawal β'.message = bidWithdrawal a.latest_execution_payload_bid := by
  obtain ⟨β, hβ, hs, hm⟩ := W.latest hL
  obtain ⟨β', hβ', hs', hw⟩ := W.withdrawal k _ hk
  refine ⟨β, β', fun e => ?_, hβ, hs, hm, hβ', hs', hw.symm⟩
  subst e
  cases W.queuedSeparate k _ β hβ' hβ

/-- **The bid the first block appends directly was not queued at the anchor.** When the latest bid `L` of the anchor
pays and the run's first block settles it FULL by the old-parent branch (`DirectAnchor`), the first block's
`process_parent_execution_payload` pushes exactly `L`'s withdrawal onto `builder_pending_withdrawals`, and the signed
bid charged by that push (the witness of `L`) witnesses no entry of the anchor's `builder_pending_withdrawals`, even
one of the same value. -/
theorem ValidJointG.anchor_direct_append_fresh
    (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final) (hpay : LatestPays a)
    (hd : DirectAnchor v.run (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)) :
    ∃ (B : GloasStepData (P := P) cfg ccfg bls) (s1 : Gloas.BeaconState P)
      (β : Gloas.SignedExecutionPayloadBid),
      v.run.steps[0]? = some (.gloas B) ∧ B.preB = a ∧
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) B.postSlots B.block.message = .ok s1 ∧
      s1.builder_pending_withdrawals =
        B.postSlots.builder_pending_withdrawals.push (bidWithdrawal a.latest_execution_payload_bid) ∧
      (v.anchorWitness : GloasBidWitness a).bid .latest = some β ∧ BidSigned a β ∧
      β.message = a.latest_execution_payload_bid ∧
      ∀ k, (v.anchorWitness : GloasBidWitness a).bid (.withdrawal k) ≠ some β := by
  obtain ⟨-, B, s1, hB, hpre, -, h1, hs1⟩ := v.anchor_directAppend_appends (j' := 0)
    (Or.inl ⟨hpay, trivial, rfl, hd⟩)
  obtain ⟨β, hβ, hs, hm⟩ := (v.anchorWitness : GloasBidWitness a).latest hpay.2
  refine ⟨B, s1, β, hB, hpre, h1, hs1, hβ, hs, hm, fun k hk => ?_⟩
  cases GloasBidWitness.queuedSeparate (v.anchorWitness : GloasBidWitness a) k _ β hk hβ

end Charged

/-! ## The transition does not look at the queue -/

/-- **`process_slots` only appends to `builder_pending_withdrawals`**: the queue before the step's slots is a prefix
of the queue after them. -/
theorem _root_.Blanc.GloasStepData.postSlots_queue_extends (D : GloasStepData (P := P) cfg ccfg bls) :
    ∃ l, D.postSlots.builder_pending_withdrawals.toArray.toList =
      D.preB.builder_pending_withdrawals.toArray.toList ++ l :=
  processSlots_ind (ctx := gloasCtx ccfg bls)
    (fun m => ∃ l, m.builder_pending_withdrawals.toArray.toList =
      D.preB.builder_pending_withdrawals.toArray.toList ++ l)
    (fun st st1 st2 _ hI f1 _ hc => by
      obtain ⟨l, hl⟩ := hI
      rcases hc with ⟨rfl, -⟩ | ⟨-, he⟩
      · refine ⟨l, ?_⟩
        show st2.builder_pending_withdrawals.toArray.toList = _
        rw [f1.2.2.1, hl]
      · obtain ⟨x, y, fx, hy, fy⟩ := processEpoch_phases he
        obtain ⟨-, q, -, hw, -⟩ := processBuilderPendingPayments_frame hy
        refine ⟨l ++ List.map (fun p => p.withdrawal) (List.filter (fun p => decide (q ≤ p.weight))
          (x.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList), ?_⟩
        show st2.builder_pending_withdrawals.toArray.toList = _
        rw [fy.2.2.1, hw, fx.2.2.1, f1.2.2.1, hl, List.append_assoc])
    D.slots ⟨[], (List.append_nil _).symm⟩

/-- **The direct append does not look at the queue.** At any Gloas step whose parent settles FULL with its slot out
of the window and whose pre-state's latest bid pays, if position `k` of the pre-state's `builder_pending_withdrawals`
already holds the latest bid's withdrawal, then after the step's `process_parent_execution_payload` the list holds
that withdrawal at two positions: `k`, and the end of the post-slots queue. Nothing in the transition tells whether
the two are one bid appended twice or two bids of one value; on a `ValidJointG` chain the anchor witnesses do
(`ValidJointG.anchor_direct_append_fresh`). -/
theorem _root_.Blanc.GloasStepData.direct_append_duplicates (D : GloasStepData (P := P) cfg ccfg bls)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s1 : Gloas.BeaconState P}
    (h1 : Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1)
    (hfull : parentFull D.postSlots D.block.message = true)
    (hnone : payIdx (D.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) D.postSlots = none)
    (hv : U64.zero < D.preB.latest_execution_payload_bid.value) {k : Nat}
    (hk : D.preB.builder_pending_withdrawals.toArray.toList[k]? =
      some (bidWithdrawal D.preB.latest_execution_payload_bid)) :
    k < D.postSlots.builder_pending_withdrawals.toArray.toList.length ∧
      s1.builder_pending_withdrawals.toArray.toList[k]? =
        some (bidWithdrawal D.preB.latest_execution_payload_bid) ∧
      s1.builder_pending_withdrawals.toArray.toList[
          D.postSlots.builder_pending_withdrawals.toArray.toList.length]? =
        some (bidWithdrawal D.preB.latest_execution_payload_bid) := by
  have hL := D.postSlots_bid
  have hs1 := parent_direct_appends hspe h1 hfull hnone (by rw [hL]; exact hv)
  rw [hL] at hs1
  obtain ⟨l, hl⟩ := D.postSlots_queue_extends
  have hlt := (List.getElem?_eq_some_iff.mp hk).1
  have hlist : s1.builder_pending_withdrawals.toArray.toList =
      D.postSlots.builder_pending_withdrawals.toArray.toList ++
        [bidWithdrawal D.preB.latest_execution_payload_bid] := by
    rw [hs1]
    simp only [ProgressiveListS.push, Array.toList_push]
  have hk' : k < D.postSlots.builder_pending_withdrawals.toArray.toList.length := by
    rw [hl, List.length_append]
    omega
  refine ⟨hk', ?_, ?_⟩
  · rw [hlist, List.getElem?_append_left hk', hl, List.getElem?_append_left hlt, hk]
  · rw [hlist, List.getElem?_concat_length]

/-! ## Optional refinement: one message, one signed bid -/

section Message

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {checkpoint : BlockChain}
  {final : GJointState P}

/-- **Witness bids with one message are one signed bid.** `GloasBidWitness.injective` separates signed bids (a
message with its signature). This premise reads "distinct witnesses" as "distinct bid messages": two witnesses with
the same message are the same signed bid. For real BLS a key signs a message with one signature only; that fact is
not a Lean theorem here, so the premise is stated. Not a field of `ValidJointG`: the theorem that uses it takes it as
a hypothesis. -/
def WitnessMessagesInjective (W : GloasBidWitness a) : Prop :=
  ∀ (r r' : WitnessRef) (β β' : Gloas.SignedExecutionPayloadBid),
    W.bid r = some β → W.bid r' = some β' → β.message = β'.message → β = β'

/-- **One bid message is charged at most once, whatever its signature.** Under `WitnessMessagesInjective`, of two
distinct signed bids with one message at most one witnesses anything: the other has no entry queued at the anchor and
no append along the run. With `ValidJointG.anchor_witness_charged_once_queued`, the entries queued at the anchor plus
the appends along the run, over every signed bid of one message, number at most one. -/
theorem ValidJointG.anchor_message_charged_once
    (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final)
    (hM : WitnessMessagesInjective (v.anchorWitness : GloasBidWitness a))
    {β β' : Gloas.SignedExecutionPayloadBid} (hm : β.message = β'.message) (hne : β ≠ β') :
    witnessQueued (v.anchorWitness : GloasBidWitness a) β +
        witnessAppends v.run (v.anchorWitness : GloasBidWitness a) β = 0 ∨
      witnessQueued (v.anchorWitness : GloasBidWitness a) β' +
        witnessAppends v.run (v.anchorWitness : GloasBidWitness a) β' = 0 := by
  have key : ∀ γ : Gloas.SignedExecutionPayloadBid,
      (∀ r, (v.anchorWitness : GloasBidWitness a).bid r ≠ some γ) →
      witnessQueued (v.anchorWitness : GloasBidWitness a) γ +
        witnessAppends v.run (v.anchorWitness : GloasBidWitness a) γ = 0 := by
    intro γ hγ
    have h0 := witnessAppends_eq_zero v.run (v.anchorWitness : GloasBidWitness a) (β := γ)
      (fun idx => hγ _) (hγ _)
    have hq : witnessQueued (v.anchorWitness : GloasBidWitness a) γ = 0 := by
      by_contra hc
      obtain ⟨k, -, hk⟩ := (witnessQueued_spec (v.anchorWitness : GloasBidWitness a) γ).2 hc
      exact hγ _ hk
    omega
  by_cases h : ∃ r, (v.anchorWitness : GloasBidWitness a).bid r = some β
  · obtain ⟨r, hr⟩ := h
    exact Or.inr (key β' fun r' hr' => hne (hM r r' β β' hr hr' hm))
  · exact Or.inl (key β fun r hr => h ⟨r, hr⟩)

end Message

end Blanc.Lift.BuilderRequest
