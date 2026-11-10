import Blanc.Composition.BuilderRequestJointGChargeOnce
import Blanc.Composition.BuilderRequestJointGProvenance

/-!
# A bid witness built from history, carried across one step

Goal `eip8282-charge-once-v1`, outcome C4 (the anchor witness exists on every Gloas state reached from a Fulu
anchor), the one-step half. `BuilderRequestJointGAnchorReach` runs it along a run.

* `Hist steps n b bid`: `bid` assigns signed bids to the references of the Gloas state `b` (`WitnessRef`), each
  the signed bid of the block of a step before `n` of `steps` (`StepBid`), verified under real BLS at `b`
  (`BidSigned`), and placed by its slot: a payment reference's bid is the one whose payment is live at that
  window index; a queue reference's bid is the one whose payment an earlier step appended (`StepPush`) as that
  queue entry, of a slot before the latest bid's, no longer live, and no two queue references share a slot; the
  latest reference's bid is the latest bid. `Hist.toWitness` is the `GloasBidWitness`: injectivity is read off
  the slots.
* `Hist.crossing`: after the Fulu → Gloas step the queue is empty, every payment entry but the block's own bid's
  is empty, and the witness is the first Gloas block's signed bid.
* `Hist.push_bid`: every append of a Gloas step is the payment of a witness bid of its pre-state, with the
  bid's slot and withdrawal.
* `Hist.step`: a Gloas step carries `Hist` from its pre-state to its post-state.

`BidSigned` at a later state reads the signing domain there. `DomainKept` names what that needs of Jaune's
Gloas transition: `process_slots` and `process_block` (and the block's phases before the bid) keep `fork` and
`genesis_validators_root` (`DomFrame`). It is a property of the transition functions, not of a chain.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## The signing domain -/

/-- The inputs of `get_domain` other than the epoch are unchanged: `fork` and `genesis_validators_root`. -/
def DomFrame (s s' : Gloas.BeaconState P) : Prop :=
  s'.fork = s.fork ∧ s'.genesis_validators_root = s.genesis_validators_root

theorem DomFrame.trans {a b c : Gloas.BeaconState P} (h₁ : DomFrame a b) (h₂ : DomFrame b c) : DomFrame a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem DomFrame.symm {a b : Gloas.BeaconState P} (h : DomFrame a b) : DomFrame b a := ⟨h.1.symm, h.2.symm⟩

/-- **The Gloas transition keeps the signing domain's inputs**: `process_slots`, `process_block`, and the
phases of `process_block` before the bid (the parent settlement, the header, the withdrawals). -/
structure DomainKept (ctx : Ctx) (P : Preset) : Prop where
  slots : ∀ {s s' : Gloas.BeaconState P} {slot : Slot}, Gloas.processSlots ctx s slot = .ok s' → DomFrame s s'
  block : ∀ {s s' : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P},
    Gloas.processBlock ctx s blk = .ok s' → DomFrame s s'
  toBid : ∀ {s s1 s2 s3 : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P},
    Gloas.processParentExecutionPayload ctx s blk = .ok s1 → Gloas.processBlockHeader s1 blk = .ok s2 →
    Gloas.processWithdrawals s2 = .ok s3 → DomFrame s s3

theorem builderPubkey_of_get {s : Gloas.BeaconState P} {i : Gloas.BuilderIndex} {bb : Gloas.Builder}
    (h : s.builders.toArray[i.toNat]? = some bb) : Gloas.builderPubkey s i = .ok bb.pubkey := by
  unfold Gloas.builderPubkey getAt
  rw [h]
  rfl

/-- A signed bid stays verified at a state with the same domain inputs and the same builder key. -/
theorem BidSigned.of_frame {s s' : Gloas.BeaconState P} {β : Gloas.SignedExecutionPayloadBid}
    (h : BidSigned s β) (hd : DomFrame s s')
    (hk : ∀ pk, Gloas.builderPubkey s β.message.builder_index = .ok pk →
      Gloas.builderPubkey s' β.message.builder_index = .ok pk) : BidSigned s' β := by
  obtain ⟨pk, e, dom, hpk, he, hdom, hsig⟩ := h
  refine ⟨pk, e, dom, hk pk hpk, he, ?_, hsig⟩
  unfold Gloas.getDomain at hdom ⊢
  rw [hd.1, hd.2]
  exact hdom

/-! ## The block's own bid -/

/-- The builder signature `process_execution_payload_bid` checked, for a bid that pays or names an external
builder (Jaune's `processExecutionPayloadBid_sig` is the paying half). -/
theorem bid_sig {ctx : Ctx} {s s' : Gloas.BeaconState P} {sb : Gloas.SignedExecutionPayloadBid}
    (h : Gloas.processExecutionPayloadBid ctx s sb = .ok s')
    (hv : U64.zero < sb.message.value ∨ sb.message.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD) :
    ∃ (builder : Gloas.Builder) (dom : Domain),
      s.builders.toArray[sb.message.builder_index.toNat]? = some builder ∧
      Gloas.getDomain s Gloas.DOMAIN_BEACON_BUILDER = .ok dom ∧
      blsVerify ctx.blsActive builder.pubkey (computeSigningRoot sb.message dom) sb.signature = true := by
  rcases hv with hv | hne
  · exact processExecutionPayloadBid_sig h hv
  unfold Gloas.processExecutionPayloadBid at h
  dsimp only at h
  split at h
  · rename_i hc
    exact absurd (U64.beq_eq_true_iff.mp hc) hne
  · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hver, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, hreq, -⟩ := bind_eq_ok_iff.mp h
    have hvt := Inv.require_eq_ok_iff.mp hreq
    subst hvt
    unfold Gloas.verifyExecutionPayloadBidSignature at hver
    obtain ⟨builder, hg, hver⟩ := bind_eq_ok_iff.mp hver
    obtain ⟨dom, hd, hver⟩ := bind_eq_ok_iff.mp hver
    exact ⟨builder, dom, ProgressiveListS_get_ok hg, hd, (Except.ok.inj hver)⟩

/-- **What a Gloas block's bid leaves**: the latest bid is the block's bid, of the block's slot, and a bid that
pays or names an external builder is verified, under real BLS, at the block's post-state. -/
theorem block_newBid {ctx : Ctx} (hk : DomainKept ctx P) (hbls : ctx.blsActive = true)
    {m post : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P} (h : Gloas.processBlock ctx m blk = .ok post) :
    post.latest_execution_payload_bid = blk.body.signed_execution_payload_bid.message ∧
      blk.body.signed_execution_payload_bid.message.slot = blk.slot ∧
      (U64.zero < blk.body.signed_execution_payload_bid.message.value ∨
          blk.body.signed_execution_payload_bid.message.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD →
        BidSigned post blk.body.signed_execution_payload_bid) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have hL4 := (processExecutionPayloadBid_post h4).1
  have hsl := (processExecutionPayloadBid_post h4).2.1
  have f5 := processRandao_invFrame _ _ _ _ h5
  have f6 := processEth1Data_invFrame _ _ _ h6
  obtain ⟨c7, -, -⟩ := processOperations_ops _ _ _ _ _ h7
  have f8 := processSyncAggregate_invFrame _ _ _ _ h8
  obtain ⟨hbs, -, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_wFrame _ _ h3
  refine ⟨by rw [f8.2.2.2.1, c7.2.1, f6.2.2.2.1, f5.2.2.2.1, hL4],
    by rw [hsl, w3.2.2.2.1, show s2.slot = s1.slot by rw [hm2], hbs], fun hv => ?_⟩
  obtain ⟨builder, dom, hb, hd, hsig⟩ := bid_sig h4 hv
  rw [hbls] at hsig
  unfold Gloas.getDomain at hd
  obtain ⟨e, he, hd⟩ := bind_eq_ok_iff.mp hd
  have hdf : DomFrame s3 post := (hk.toBid h1 h2 h3).symm.trans (hk.block h)
  refine ⟨builder.pubkey, e, dom, ?_, by rw [hsl]; exact he, ?_, hsig⟩
  · rw [← processBlock_builders_of_bid h4 h5 h6 h7 h8] at hb
    exact builderPubkey_of_get hb
  · unfold Gloas.getDomain
    rw [hdf.1, hdf.2]
    exact hd

/-! ## Payment entries by slot -/

/-- The latest bid's virtual slot has the latest bid's window index. -/
theorem payIdx_latest (hspe : 0 < P.SLOTS_PER_EPOCH) (b : Gloas.BeaconState P) :
    payIdx (b.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH) b = bidIndex b := by
  rw [payIdx_shift hspe]
  rfl

/-- A non-empty payment entry is live at the virtual slot of its index. -/
theorem liveAt_of_entry (hspe : 0 < P.SLOTS_PER_EPOCH) {b : Gloas.BeaconState P} {k : Nat}
    {p : Gloas.BuilderPendingPayment} (hk : b.builder_pending_payments.toArray[k]? = some p)
    (hne : p ≠ Gloas.BuilderPendingPayment.empty) :
    payIdx (anchorVs b k) b = some k ∧ LiveAt (anchorVs b k) p.withdrawal b := by
  have hlt : k < 2 * P.SLOTS_PER_EPOCH := by
    have := (Array.getElem?_eq_some_iff.mp hk).1
    rwa [b.builder_pending_payments.size_eq] at this
  have hi := payIdx_anchorVs (a := b) hspe hlt
  exact ⟨hi, p, by rw [cell_of_payIdx hi, hk], hne, rfl⟩

/-- A live payment is a non-empty entry at its slot's window index. -/
theorem entry_of_liveAt {b : Gloas.BeaconState P} {s : Nat} {w : Gloas.BuilderPendingWithdrawal}
    (hl : LiveAt s w b) : ∃ k p, payIdx s b = some k ∧ b.builder_pending_payments.toArray[k]? = some p ∧
      p ≠ Gloas.BuilderPendingPayment.empty ∧ p.withdrawal = w := by
  obtain ⟨p, hp, hne, hw⟩ := hl
  cases hk : payIdx s b with
  | none => simp only [cell, hk, Option.bind_none, reduceCtorEq] at hp
  | some k => exact ⟨k, p, rfl, by rw [← cell_of_payIdx hk, hp], hne, hw⟩

theorem liveAt_fun {b : Gloas.BeaconState P} {s : Nat} {w w' : Gloas.BuilderPendingWithdrawal}
    (h : LiveAt s w b) (h' : LiveAt s w' b) : w = w' := by
  obtain ⟨p, hp, -, hw⟩ := h
  obtain ⟨p', hp', -, hw'⟩ := h'
  rw [hp] at hp'; cases hp'
  exact hw.symm.trans hw'

/-- **The entry at the latest bid's slot is the latest bid's** (G3-07): if a payment is live at the latest
bid's virtual slot, the latest bid pays and the payment records its withdrawal. -/
theorem latest_live (hspe : 0 < P.SLOTS_PER_EPOCH) {b : Gloas.BeaconState P} (g7 : NoLiveWeightOnLatestBid b)
    {w : Gloas.BuilderPendingWithdrawal}
    (hl : LiveAt (b.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH) w b) :
    U64.zero < b.latest_execution_payload_bid.value ∧ w = bidWithdrawal b.latest_execution_payload_bid := by
  obtain ⟨k, p, hk, hp, hne, hw⟩ := entry_of_liveAt hl
  rw [payIdx_latest hspe] at hk
  obtain ⟨E, hE, -, ⟨hv, hEw⟩ | he⟩ := g7 k hk
  · rw [hp] at hE; cases hE
    exact ⟨hv, hw.symm.trans hEw⟩
  · rw [hp] at hE; cases hE
    exact absurd he hne

/-! ## The history witness -/

/-- **A signed bid of the run**: the signed bid of the block of a step before `n` (the crossing's first Gloas
block or a Gloas step's). -/
def StepBid (steps : List (GJointRunStep (P := P) cfg ccfg bls)) (n : Nat)
    (β : Gloas.SignedExecutionPayloadBid) : Prop :=
  ∃ j < n, ∃ (C : GJointRunStep (P := P) cfg ccfg bls) (blk : Gloas.SignedBeaconBlock P),
    steps[j]? = some C ∧ C.block = .gloas blk ∧ β = blk.message.body.signed_execution_payload_bid

/-- **An append of the run**: an element a step before `n` appended to `builder_pending_withdrawals`. -/
def StepPush (steps : List (GJointRunStep (P := P) cfg ccfg bls)) (n : Nat) (e : Push) : Prop :=
  ∃ j < n, ∃ C : GJointRunStep (P := P) cfg ccfg bls, steps[j]? = some C ∧ e ∈ C.pushes

theorem StepBid.mono {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {n n' : Nat}
    {β : Gloas.SignedExecutionPayloadBid} (h : StepBid steps n β) (hn : n ≤ n') : StepBid steps n' β := by
  obtain ⟨j, hj, r⟩ := h
  exact ⟨j, by omega, r⟩

theorem StepBid.append {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {n : Nat}
    {β : Gloas.SignedExecutionPayloadBid} (h : StepBid steps n β)
    (l : List (GJointRunStep (P := P) cfg ccfg bls)) : StepBid (steps ++ l) n β := by
  obtain ⟨j, hj, C, blk, hC, hb, rfl⟩ := h
  exact ⟨j, hj, C, blk,
    by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hC).1]; exact hC, hb, rfl⟩

theorem StepPush.mono {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {n n' : Nat} {e : Push}
    (h : StepPush steps n e) (hn : n ≤ n') : StepPush steps n' e := by
  obtain ⟨j, hj, r⟩ := h
  exact ⟨j, by omega, r⟩

theorem StepPush.append {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {n : Nat} {e : Push}
    (h : StepPush steps n e) (l : List (GJointRunStep (P := P) cfg ccfg bls)) : StepPush (steps ++ l) n e := by
  obtain ⟨j, hj, C, hC, he⟩ := h
  exact ⟨j, hj, C, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hC).1]; exact hC, he⟩

/-- **A bid witness of the Gloas state `b`, built from the first `n` steps.** Every witness bid is a signed
bid of an earlier step's block, verified under real BLS at `b`, and

* `payOnly`: a payment reference's bid is the one whose payment is live at that window index (the index of the
  bid's slot plus one epoch), and it pays;
* `wdOnly`: a queue reference's bid pays, its slot is before the latest bid's, its payment is not live, and an
  earlier step appended exactly that payment (its slot, its withdrawal) as this queue entry;
* `wdInj`: two queue references with bids of one slot are the same reference;
* `latOnly`: the latest reference's bid is the latest bid.

`pay`, `wd`, `lat` say every reference `GloasBidWitness` asks for has a bid. -/
structure Hist (steps : List (GJointRunStep (P := P) cfg ccfg bls)) (n : Nat) (b : Gloas.BeaconState P)
    (bid : WitnessRef → Option Gloas.SignedExecutionPayloadBid) : Prop where
  signed : ∀ r β, bid r = some β → BidSigned b β ∧ StepBid steps n β
  pay : ∀ k p, b.builder_pending_payments.toArray[k]? = some p → p ≠ Gloas.BuilderPendingPayment.empty →
    ∃ β, bid (.payment k) = some β
  payOnly : ∀ k β, bid (.payment k) = some β →
    payIdx (β.message.slot.toNat + P.SLOTS_PER_EPOCH) b = some k ∧
      LiveAt (β.message.slot.toNat + P.SLOTS_PER_EPOCH) (bidWithdrawal β.message) b ∧
      U64.zero < β.message.value
  wd : ∀ k w, b.builder_pending_withdrawals.toArray.toList[k]? = some w → ∃ β, bid (.withdrawal k) = some β
  wdOnly : ∀ k β, bid (.withdrawal k) = some β → U64.zero < β.message.value ∧
    β.message.slot.toNat < b.latest_execution_payload_bid.slot.toNat ∧
    (∀ w, ¬ LiveAt (β.message.slot.toNat + P.SLOTS_PER_EPOCH) w b) ∧
    ∃ e, StepPush steps n e ∧ e.slot = β.message.slot.toNat + P.SLOTS_PER_EPOCH ∧
      e.w = bidWithdrawal β.message ∧ b.builder_pending_withdrawals.toArray.toList[k]? = some e.w
  wdInj : ∀ k k' β β', bid (.withdrawal k) = some β → bid (.withdrawal k') = some β' →
    β.message.slot = β'.message.slot → k = k'
  lat : b.latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD →
    ∃ β, bid .latest = some β
  latOnly : ∀ β, bid .latest = some β → β.message = b.latest_execution_payload_bid

theorem Hist.append {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {n : Nat} {b : Gloas.BeaconState P}
    {bid : WitnessRef → Option Gloas.SignedExecutionPayloadBid} (h : Hist steps n b bid)
    (l : List (GJointRunStep (P := P) cfg ccfg bls)) : Hist (steps ++ l) n b bid :=
  { h with
    signed := fun r β hβ => ⟨(h.signed r β hβ).1, (h.signed r β hβ).2.append l⟩
    wdOnly := fun k β hβ => by
      obtain ⟨hv, hlt, hd, e, he, r⟩ := h.wdOnly k β hβ
      exact ⟨hv, hlt, hd, e, he.append l, r⟩ }

/-- **The history witness is a `GloasBidWitness`.** Injectivity is read off the slots: a payment reference is
fixed by its bid's slot (the window index), a queue reference's bid is not live and is of a slot before the
latest bid's, and two queue references differ in slot. -/
def Hist.toWitness (hspe : 0 < P.SLOTS_PER_EPOCH)
    {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {n : Nat} {b : Gloas.BeaconState P}
    {bid : WitnessRef → Option Gloas.SignedExecutionPayloadBid} (h : Hist steps n b bid) : GloasBidWitness b where
  bid := bid
  payment k p hk hne := by
    obtain ⟨β, hβ⟩ := h.pay k p hk hne
    obtain ⟨hi, hl, -⟩ := h.payOnly k β hβ
    refine ⟨β, hβ, (h.signed _ β hβ).1, ?_⟩
    obtain ⟨k', p', hk', hp', -, hw⟩ := entry_of_liveAt hl
    rw [hi] at hk'; cases hk'
    rw [hk] at hp'; cases hp'
    exact hw
  withdrawal k w hk := by
    rw [← Array.getElem?_toList] at hk
    obtain ⟨β, hβ⟩ := h.wd k w hk
    obtain ⟨-, -, -, e, -, -, hew, hq⟩ := h.wdOnly k β hβ
    rw [hk] at hq
    exact ⟨β, hβ, (h.signed _ β hβ).1, (Option.some.inj hq).trans hew⟩
  latest hne := by
    obtain ⟨β, hβ⟩ := h.lat hne
    exact ⟨β, hβ, (h.signed _ β hβ).1, h.latOnly β hβ⟩
  injective r r' β hr hr' := by
    have pl : ∀ k, bid (.payment k) = some β → bid .latest = some β → bidIndex b = some k := fun k hp hL => by
      have hi := (h.payOnly k β hp).1
      rw [h.latOnly β hL, payIdx_latest hspe] at hi
      exact hi
    have pw : ∀ k k', bid (.payment k) = some β → bid (.withdrawal k') = some β → False := fun k k' hp hw =>
      (h.wdOnly k' β hw).2.2.1 _ (h.payOnly k β hp).2.1
    have wl : ∀ k, bid (.withdrawal k) = some β → bid .latest = some β → False := fun k hw hL => by
      have := (h.wdOnly k β hw).2.1
      rw [h.latOnly β hL] at this
      exact Nat.lt_irrefl _ this
    cases r with
    | payment k =>
      cases r' with
      | payment k' =>
        have h1 := (h.payOnly k β hr).1
        rw [(h.payOnly k' β hr').1] at h1
        exact Or.inl (by rw [Option.some.inj h1])
      | withdrawal k' => exact (pw k k' hr hr').elim
      | latest => exact Or.inr (Or.inr ⟨rfl, k, rfl, pl k hr hr'⟩)
    | withdrawal k =>
      cases r' with
      | payment k' => exact (pw k' k hr' hr).elim
      | withdrawal k' => exact Or.inl (by rw [h.wdInj k k' β β hr hr' rfl])
      | latest => exact (wl k hr hr').elim
    | latest =>
      cases r' with
      | payment k' => exact Or.inr (Or.inl ⟨rfl, k', rfl, pl k' hr' hr⟩)
      | withdrawal k' => exact (wl k' hr' hr).elim
      | latest => exact Or.inl rfl

/-! ## The Fulu → Gloas step -/

/-- **After the crossing, the witness is the first Gloas block's signed bid.** The queue is empty
(`CrossingData.queue_empty`), every payment entry was empty before the block (`CrossClean`), so the only live
payment is the block's own bid's (G3-07 at the post-state). -/
theorem Hist.crossing (hk : DomainKept (gloasCtx ccfg bls) P) (hbls : bls = true)
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {n : Nat} (C : CrossingData (P := P) cfg ccfg bls)
    (hC : steps[n]? = some (.crossing C)) (g7 : NoLiveWeightOnLatestBid C.postB)
    (vb : C.postB.validators.toArray.size ≤ 2 ^ 40) (bb : C.postB.builders.toArray.size ≤ 2 ^ 40) :
    ∃ bid, Hist steps (n + 1) C.postB bid := by
  classical
  have hspe0 : 0 < P.SLOTS_PER_EPOCH := by omega
  have hp : Gloas.processBlock (gloasCtx ccfg bls) C.postSlots C.block.message = .ok C.postB :=
    applySignedBlockWith_ok C.transition
  obtain ⟨hL, hsl, hsig⟩ := block_newBid hk hbls hp
  have hclean := (crossingSlots_crossClean hq C.slots (upgradeToGloas_crossClean C.upgrade)).1
  have hQ := (C.queue_empty hq hspe vb bb).2.2
  have hLslot : C.postB.latest_execution_payload_bid.slot = C.block.message.slot := by rw [hL]; exact hsl
  have live : ∀ s w, LiveAt s w C.postB →
      s = C.postB.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH ∧
        U64.zero < C.postB.latest_execution_payload_bid.value ∧
        w = bidWithdrawal C.postB.latest_execution_payload_bid := by
    intro s w hl
    have hs : s = C.block.message.slot.toNat + P.SLOTS_PER_EPOCH := by
      by_contra hne
      obtain ⟨k, p, -, hp', hne', -⟩ := entry_of_liveAt ((block_track hspe0 hp hne).1 hl)
      exact hne' (hclean.2.1 p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp')))
    rw [← hLslot] at hs
    subst hs
    exact ⟨rfl, latest_live hspe0 g7 hl⟩
  have stepBidN : StepBid steps (n + 1) C.block.message.body.signed_execution_payload_bid :=
    ⟨n, Nat.lt_succ_self n, _, C.block, hC, rfl, rfl⟩
  refine ⟨fun r => match r with
    | .latest => if C.postB.latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD then
        some C.block.message.body.signed_execution_payload_bid else none
    | .payment k =>
      if ∃ p, C.postB.builder_pending_payments.toArray[k]? = some p ∧ p ≠ Gloas.BuilderPendingPayment.empty then
        some C.block.message.body.signed_execution_payload_bid else none
    | .withdrawal _ => none,
    { signed := ?_, pay := ?_, payOnly := ?_, wd := ?_, wdOnly := ?_, wdInj := ?_, lat := ?_, latOnly := ?_ }⟩
  · intro r β hr
    cases r with
    | payment k =>
      dsimp only at hr
      split at hr
      · rename_i hex
        cases hr
        obtain ⟨p, hp', hne⟩ := hex
        obtain ⟨-, hv, -⟩ := live _ _ (liveAt_of_entry hspe0 hp' hne).2
        rw [hL] at hv
        exact ⟨hsig (Or.inl hv), stepBidN⟩
      · cases hr
    | withdrawal k => cases hr
    | latest =>
      dsimp only at hr
      split at hr
      · rename_i hne
        cases hr
        rw [hL] at hne
        exact ⟨hsig (Or.inr hne), stepBidN⟩
      · cases hr
  · intro k p hk hne
    exact ⟨_, ite_eq_left ⟨p, hk, hne⟩⟩
  · intro k β hr
    dsimp only at hr
    split at hr
    · rename_i hex
      cases hr
      obtain ⟨p, hp', hne⟩ := hex
      obtain ⟨hi, hl⟩ := liveAt_of_entry hspe0 hp' hne
      obtain ⟨hs, hv, hw⟩ := live _ _ hl
      rw [hs] at hi hl
      rw [hw] at hl
      rw [hL] at hi hl hv
      exact ⟨hi, hl, hv⟩
    · cases hr
  · intro k w hk
    rw [hQ] at hk
    simp only [List.getElem?_nil, reduceCtorEq] at hk
  · intro k β hr
    cases hr
  · intro k k' β β' hr
    cases hr
  · intro hne
    exact ⟨_, ite_eq_left hne⟩
  · intro β hr
    dsimp only at hr
    split at hr
    · cases hr; exact hL.symm
    · cases hr

/-! ## A Gloas step -/

theorem idx_eq_of_filter_le_one {α : Type} {p : α → Bool} :
    ∀ {l : List α} {i j : Nat} {x y : α}, (l.filter p).length ≤ 1 → l[i]? = some x → l[j]? = some y →
      p x = true → p y = true → i = j
  | [], _, _, _, _, _, hi, _, _, _ => by simp only [List.getElem?_nil, reduceCtorEq] at hi
  | _ :: _, 0, 0, _, _, _, _, _, _, _ => rfl
  | a :: l, 0, j + 1, x, y, h, hi, hj, hx, hy => by
    rw [List.getElem?_cons_zero] at hi; cases hi
    rw [List.getElem?_cons_succ] at hj
    rw [List.filter_cons_of_pos hx] at h
    have := List.length_pos_of_mem (List.mem_filter.mpr ⟨List.mem_of_getElem? hj, hy⟩)
    simp only [List.length_cons] at h; omega
  | a :: l, i + 1, 0, x, y, h, hi, hj, hx, hy => by
    rw [List.getElem?_cons_zero] at hj; cases hj
    rw [List.getElem?_cons_succ] at hi
    rw [List.filter_cons_of_pos hy] at h
    have := List.length_pos_of_mem (List.mem_filter.mpr ⟨List.mem_of_getElem? hi, hx⟩)
    simp only [List.length_cons] at h; omega
  | a :: l, i + 1, j + 1, x, y, h, hi, hj, hx, hy => by
    rw [List.getElem?_cons_succ] at hi hj
    have hle : (l.filter p).length ≤ 1 :=
      Nat.le_trans ((List.Sublist.filter p (List.sublist_cons_self a l)).length_le) h
    rw [idx_eq_of_filter_le_one hle hi hj hx hy]

/-- **Two appends of one step are of different slots** (`slot_pushes_le_one` on the one-step run). -/
theorem _root_.Blanc.GloasStepData.pushes_slot_inj (D : GloasStepData (P := P) cfg ccfg bls)
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hspe : 0 < P.SLOTS_PER_EPOCH)
    (hinv : NoLiveWeightOnLatestBid D.preB ∧ LatestBidCoherence D.preB ∧ FutureEmpty D.preB) {i i' : Nat}
    {e e' : Push} (hi : D.pushes[i]? = some e) (hi' : D.pushes[i']? = some e') (hs : e.slot = e'.slot) :
    i = i' := by
  let run : GJointRun cfg ccfg bls (GJointRunStep.gloas D).preState (GJointRunStep.gloas D).postState :=
    GJointRun.nil.snoc (.gloas D) rfl
  have hst : run.steps = [.gloas D] := rfl
  have h1 := slot_pushes_le_one hq hspe run (fun {j B} hB => by
    rw [hst] at hB
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, GJointRunStep.gloas.injEq] at hB
      subst hB; exact hinv
    | succ j => simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hB) e.slot
  have hp : run.pushes = D.pushes := by
    show [GJointRunStep.gloas D].flatMap GJointRunStep.pushes = _
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, GJointRunStep.pushes]
  rw [hp] at h1
  exact idx_eq_of_filter_le_one h1 hi hi' (decide_eq_true rfl) (decide_eq_true hs.symm)

/-- **Every append of a Gloas step is the payment of a witness bid of its pre-state.** A rotation or
settlement append is of a payment live at the pre-state, whose reference's bid has the append's slot and
withdrawal; the direct append is of the pre-state's latest bid, which pays and so names an external builder.
The reference is the one `stepBid` reads. -/
theorem Hist.push_bid (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {n : Nat}
    {bid : WitnessRef → Option Gloas.SignedExecutionPayloadBid} (D : GloasStepData (P := P) cfg ccfg bls)
    (h : Hist steps n D.preB bid) (g8 : LatestBidCoherence D.preB) (hA : LatestBidBuilderActive D.preB)
    (hbb : D.preB.builders.toArray.size ≤ 2 ^ 40) {e : Push} (he : e ∈ D.pushes) :
    ∃ r β, bid r = some β ∧
      (if e.path = .direct then bid .latest
        else (payIdx e.slot D.preB).bind fun k0 => bid (.payment k0)) = bid r ∧
      e.slot = β.message.slot.toNat + P.SLOTS_PER_EPOCH ∧ e.w = bidWithdrawal β.message ∧
      U64.zero < β.message.value ∧ Src D.preB (bidWithdrawal β.message) := by
  have liveCase : e.path ≠ .direct → LiveAt e.slot e.w D.preB → ∃ r β, bid r = some β ∧
      (if e.path = .direct then bid .latest
        else (payIdx e.slot D.preB).bind fun k0 => bid (.payment k0)) = bid r ∧
      e.slot = β.message.slot.toNat + P.SLOTS_PER_EPOCH ∧ e.w = bidWithdrawal β.message ∧
      U64.zero < β.message.value ∧ Src D.preB (bidWithdrawal β.message) := by
    intro hpd hl
    obtain ⟨k0, p, hk0, hp0, hne, hw⟩ := entry_of_liveAt hl
    obtain ⟨β, hβ⟩ := h.pay k0 p hp0 hne
    obtain ⟨hi, hlβ, hv⟩ := h.payOnly k0 β hβ
    have hs : e.slot = β.message.slot.toNat + P.SLOTS_PER_EPOCH := payIdx_inj hk0 hi
    have hew : e.w = bidWithdrawal β.message := liveAt_fun (hs ▸ hl) hlβ
    exact ⟨.payment k0, β, hβ, by rw [ite_eq_right hpd, hk0]; rfl, hs, hew, hv,
      Or.inr (Or.inl ⟨k0, p, hp0, hne, hw.trans hew⟩)⟩
  rcases D.push_source hq hspe he with ⟨hp, hr⟩ | ⟨hp, -, -, hl, -, -⟩ | ⟨hp, -, hslot, -, hv, hw, -⟩
  · exact liveCase (by rw [hp]; decide)
      (rotEval_live hspe _ _ (rotEval_imp (fun _ _ h => h.1) _ _ hr))
  · exact liveCase (by rw [hp]; decide)
      (slotLoop_live_back hspe _ _ _ (processSlots_slotLoop D.slots).2 hl)
  · rw [D.postSlots_bid] at hv hw
    have hne : D.preB.latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD := by
      intro heq
      obtain ⟨b0, hb0, -⟩ := hA hv
      have hlt := (Array.getElem?_eq_some_iff.mp hb0).1
      rw [heq, selfBuild_toNat] at hlt
      omega
    obtain ⟨β, hβ⟩ := h.lat hne
    have hm := h.latOnly β hβ
    refine ⟨.latest, β, hβ, by rw [ite_eq_left hp], ?_, by rw [hw, hm], by rw [hm]; exact hv,
      Or.inr (Or.inr ⟨hv, by rw [hm]⟩)⟩
    rw [hslot, D.postSlots_lbh, ← g8.1, hm]

open Classical in
/-- **The witness assignment after a Gloas step**, from the pre-state's (`d` is the number of queue entries
the step's `process_withdrawals` removed from the front):

* the latest reference: the block's signed bid, when it names an external builder;
* a payment reference with a non-empty entry: the block's signed bid at the latest bid's window index, else
  the pre-state bid of the same virtual slot;
* queue reference `k`: pre-state queue reference `d + k`, or, past the pre-state's queue, the bid of the
  step's append there: the pre-state's latest bid for the direct append, else the pre-state bid of the
  append's slot. -/
noncomputable def stepBid (D : GloasStepData (P := P) cfg ccfg bls) (d : Nat)
    (bid : WitnessRef → Option Gloas.SignedExecutionPayloadBid) :
    WitnessRef → Option Gloas.SignedExecutionPayloadBid
  | .latest =>
    if D.postB.latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD then
      some D.block.message.body.signed_execution_payload_bid else none
  | .payment k =>
    if ∃ p, D.postB.builder_pending_payments.toArray[k]? = some p ∧ p ≠ Gloas.BuilderPendingPayment.empty then
      if bidIndex D.postB = some k then some D.block.message.body.signed_execution_payload_bid
      else (payIdx (anchorVs D.postB k) D.preB).bind fun k0 => bid (.payment k0)
    else none
  | .withdrawal k =>
    if d + k < D.preB.builder_pending_withdrawals.toArray.toList.length then bid (.withdrawal (d + k))
    else match D.pushes[d + k - D.preB.builder_pending_withdrawals.toArray.toList.length]? with
      | none => none
      | some e => if e.path = .direct then bid .latest
          else (payIdx e.slot D.preB).bind fun k0 => bid (.payment k0)

/-- **A Gloas step carries the history witness.** From `Hist` at the step's pre-state, `stepBid` is `Hist` at
its post-state: a surviving payment or queue entry keeps its bid, still verified (the builder keeps its key,
`src_pubkey_kept`; the domain is kept, `DomainKept`); an appended entry takes the bid of the payment it was
(`Hist.push_bid`), which is no longer live (`GloasStepData.push_dead`) and of a slot before the block's; the
block's own bid is new, of a later slot than every other. -/
theorem Hist.step (hk : DomainKept (gloasCtx ccfg bls) P) (hbls : bls = true)
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    (hdelay : 0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY)
    {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {n : Nat}
    {bid : WitnessRef → Option Gloas.SignedExecutionPayloadBid} (D : GloasStepData (P := P) cfg ccfg bls)
    (hD : steps[n]? = some (.gloas D)) (h : Hist steps n D.preB bid) (hpre : GInv D.preB)
    (g7' : NoLiveWeightOnLatestBid D.postB) (bb : D.postB.builders.toArray.size ≤ 2 ^ 40) :
    ∃ bid', Hist steps (n + 1) D.postB bid' := by
  have hspe0 : 0 < P.SLOTS_PER_EPOCH := by omega
  obtain ⟨-, -, g4, -, -, g7, g8, hA, fe⟩ := hpre
  obtain ⟨d, -, -, hQ⟩ := D.pushes_exhaustive hspe0
  obtain ⟨hL, hsl, hsig⟩ := block_newBid hk hbls D.processBlock
  have hB := stateTransition_identityStable hspe hdelay D.stateTransition
  have hbb : D.preB.builders.toArray.size ≤ 2 ^ 40 := Nat.le_trans hB.1 bb
  have hdf : DomFrame D.preB D.postB := (hk.slots D.slots).trans (hk.block D.processBlock)
  have hloop := (processSlots_slotLoop D.slots).2
  have hLslot : D.postB.latest_execution_payload_bid.slot = D.block.message.slot := by rw [hL]; exact hsl
  have hpreL : D.preB.latest_execution_payload_bid.slot.toNat < D.block.message.slot.toNat := by
    have := D.lbh_lt
    rw [D.postSlots_lbh, ← g8.1] at this
    exact this
  have T : ∀ β, BidSigned D.preB β → Src D.preB (bidWithdrawal β.message) → U64.zero < β.message.value →
      BidSigned D.postB β := by
    intro β hs hsrc hv
    refine hs.of_frame hdf fun pk hpk => ?_
    obtain ⟨bb0, hbb0, rfl⟩ := builderPubkey_ok hpk
    obtain ⟨b', hb', hpk'⟩ := src_pubkey_kept hspe g4 hA hB hsrc hv hbb0
    rw [← hpk']
    exact builderPubkey_of_get hb'
  have back : ∀ s w, s ≠ D.block.message.slot.toNat + P.SLOTS_PER_EPOCH → LiveAt s w D.postB →
      LiveAt s w D.preB := fun s w hne hl =>
    slotLoop_live_back hspe0 _ _ _ hloop ((block_track hspe0 D.processBlock hne).1 hl)
  have stepBidN : StepBid steps (n + 1) D.block.message.body.signed_execution_payload_bid :=
    ⟨n, Nat.lt_succ_self n, _, D.block, hD, rfl, rfl⟩
  have pushN : ∀ e ∈ D.pushes, StepPush steps (n + 1) e := fun e he => ⟨n, Nat.lt_succ_self n, _, hD, he⟩
  have hq_old : ∀ k, d + k < D.preB.builder_pending_withdrawals.toArray.toList.length →
      D.postB.builder_pending_withdrawals.toArray.toList[k]? =
        D.preB.builder_pending_withdrawals.toArray.toList[d + k]? := by
    intro k hlt
    rw [hQ, List.getElem?_drop, List.getElem?_append_left hlt]
  have hq_new : ∀ k, ¬ d + k < D.preB.builder_pending_withdrawals.toArray.toList.length →
      D.postB.builder_pending_withdrawals.toArray.toList[k]? =
        (D.pushes[d + k - D.preB.builder_pending_withdrawals.toArray.toList.length]?).map (·.w) := by
    intro k hge
    rw [hQ, List.getElem?_drop, List.getElem?_append_right (by omega), List.getElem?_map]
  -- a surviving payment entry, not the block's own bid's
  have payOld : ∀ k p, D.postB.builder_pending_payments.toArray[k]? = some p →
      p ≠ Gloas.BuilderPendingPayment.empty → bidIndex D.postB ≠ some k →
      payIdx (anchorVs D.postB k) D.postB = some k ∧ LiveAt (anchorVs D.postB k) p.withdrawal D.postB ∧
        LiveAt (anchorVs D.postB k) p.withdrawal D.preB := by
    intro k p hk hne hbi
    obtain ⟨hi, hl⟩ := liveAt_of_entry hspe0 hk hne
    refine ⟨hi, hl, back _ _ (fun he => ?_) hl⟩
    rw [he, ← hLslot, payIdx_latest hspe0] at hi
    exact hbi hi
  -- what a payment reference of `stepBid` is
  have payCase : ∀ k β, stepBid D d bid (.payment k) = some β →
      ∃ p, D.postB.builder_pending_payments.toArray[k]? = some p ∧ p ≠ Gloas.BuilderPendingPayment.empty ∧
        ((β = D.block.message.body.signed_execution_payload_bid ∧ bidIndex D.postB = some k) ∨
          (bidIndex D.postB ≠ some k ∧
            ∃ k0, payIdx (anchorVs D.postB k) D.preB = some k0 ∧ bid (.payment k0) = some β)) := by
    intro k β hβ
    simp only [stepBid] at hβ
    split at hβ
    · rename_i hex
      obtain ⟨p, hp, hne⟩ := hex
      refine ⟨p, hp, hne, ?_⟩
      split at hβ
      · rename_i hbi
        cases hβ
        exact Or.inl ⟨rfl, hbi⟩
      · rename_i hbi
        cases hk0 : payIdx (anchorVs D.postB k) D.preB with
        | none => rw [hk0] at hβ; cases hβ
        | some k0 => rw [hk0] at hβ; exact Or.inr ⟨hbi, k0, rfl, hβ⟩
    · cases hβ
  have payOnly' : ∀ k β, stepBid D d bid (.payment k) = some β →
      payIdx (β.message.slot.toNat + P.SLOTS_PER_EPOCH) D.postB = some k ∧
        LiveAt (β.message.slot.toNat + P.SLOTS_PER_EPOCH) (bidWithdrawal β.message) D.postB ∧
        U64.zero < β.message.value := by
    intro k β hβ
    obtain ⟨p, hp, hne, ⟨rfl, hbi⟩ | ⟨hbi, k0, hk0, hβ0⟩⟩ := payCase k β hβ
    · obtain ⟨hi, hl⟩ := liveAt_of_entry hspe0 hp hne
      rw [← payIdx_latest hspe0] at hbi
      rw [payIdx_inj hi hbi] at hl
      obtain ⟨hv, hw⟩ := latest_live hspe0 g7' hl
      rw [hw] at hl
      rw [hL] at hbi hl hv
      exact ⟨hbi, hl, hv⟩
    · obtain ⟨hi, hl, hl'⟩ := payOld k p hp hne hbi
      obtain ⟨hi0, hl0, hv⟩ := h.payOnly k0 β hβ0
      have hs : β.message.slot.toNat + P.SLOTS_PER_EPOCH = anchorVs D.postB k := payIdx_inj hi0 hk0
      rw [hs]
      rw [hs] at hl0
      rw [liveAt_fun hl' hl0] at hl
      exact ⟨hi, hl, hv⟩
  -- what a queue reference of `stepBid` is
  have wdCase : ∀ k β, stepBid D d bid (.withdrawal k) = some β →
      (d + k < D.preB.builder_pending_withdrawals.toArray.toList.length ∧
        bid (.withdrawal (d + k)) = some β) ∨
      (¬ d + k < D.preB.builder_pending_withdrawals.toArray.toList.length ∧ ∃ e r,
        D.pushes[d + k - D.preB.builder_pending_withdrawals.toArray.toList.length]? = some e ∧
        bid r = some β ∧ e.slot = β.message.slot.toNat + P.SLOTS_PER_EPOCH ∧
        e.w = bidWithdrawal β.message ∧ U64.zero < β.message.value ∧
        Src D.preB (bidWithdrawal β.message)) := by
    intro k β hβ
    by_cases hlt : d + k < D.preB.builder_pending_withdrawals.toArray.toList.length
    · exact Or.inl ⟨hlt, by simpa only [stepBid, ite_eq_left hlt] using hβ⟩
    · refine Or.inr ⟨hlt, ?_⟩
      simp only [stepBid, ite_eq_right hlt] at hβ
      cases he : D.pushes[d + k - D.preB.builder_pending_withdrawals.toArray.toList.length]? with
      | none => rw [he] at hβ; cases hβ
      | some e =>
        rw [he] at hβ
        obtain ⟨r, β', hr, heq, hs, hw, hv, hsrc⟩ :=
          h.push_bid hq hspe0 D g8 hA hbb (List.mem_of_getElem? he)
        dsimp only at hβ
        rw [heq, hr] at hβ
        cases hβ
        exact ⟨e, r, rfl, hr, hs, hw, hv, hsrc⟩
  -- an append of the step is not the payment of a pre-state queue reference
  have clash : ∀ kk β0 e, bid (.withdrawal kk) = some β0 → e ∈ D.pushes →
      e.slot = β0.message.slot.toNat + P.SLOTS_PER_EPOCH → False := by
    intro kk β0 e h0 he hs
    obtain ⟨-, hslt, hdead, -⟩ := h.wdOnly kk β0 h0
    rcases D.push_source hq hspe0 he with ⟨-, hr⟩ | ⟨-, -, -, hl, -⟩ | ⟨-, -, hslot, -⟩
    · have hl : LiveAt e.slot e.w D.preB :=
        rotEval_live hspe0 _ _ (rotEval_imp (fun _ _ h => h.1) _ _ hr)
      rw [hs] at hl
      exact hdead _ hl
    · have hl' : LiveAt e.slot e.w D.preB := slotLoop_live_back hspe0 _ _ _ hloop hl
      rw [hs] at hl'
      exact hdead _ hl'
    · rw [D.postSlots_lbh, ← g8.1] at hslot
      omega
  refine ⟨stepBid D d bid,
    { signed := ?_, pay := ?_, payOnly := payOnly', wd := ?_, wdOnly := ?_, wdInj := ?_, lat := ?_,
      latOnly := ?_ }⟩
  · intro r β hβ
    cases r with
    | payment k =>
      obtain ⟨-, -, hv⟩ := payOnly' k β hβ
      obtain ⟨p, hp, hne, ⟨rfl, hbi⟩ | ⟨hbi, k0, hk0, hβ0⟩⟩ := payCase k β hβ
      · exact ⟨hsig (Or.inl hv), stepBidN⟩
      · obtain ⟨-, hl0, -⟩ := h.payOnly k0 β hβ0
        obtain ⟨k1, p1, -, hp1, hne1, hw1⟩ := entry_of_liveAt hl0
        exact ⟨T β (h.signed _ β hβ0).1 (Or.inr (Or.inl ⟨k1, p1, hp1, hne1, hw1⟩)) hv,
          (h.signed _ β hβ0).2.mono (Nat.le_succ n)⟩
    | withdrawal k =>
      rcases wdCase k β hβ with ⟨hlt, hβ0⟩ | ⟨-, e, r, -, hr, -, -, hv, hsrc⟩
      · obtain ⟨hv, -, -, e, -, -, hew, heq⟩ := h.wdOnly _ β hβ0
        exact ⟨T β (h.signed _ β hβ0).1 (Or.inl (hew ▸ List.mem_of_getElem? heq)) hv,
          (h.signed _ β hβ0).2.mono (Nat.le_succ n)⟩
      · exact ⟨T β (h.signed r β hr).1 hsrc hv, (h.signed r β hr).2.mono (Nat.le_succ n)⟩
    | latest =>
      simp only [stepBid] at hβ
      split at hβ
      · rename_i hne
        cases hβ
        rw [hL] at hne
        exact ⟨hsig (Or.inr hne), stepBidN⟩
      · cases hβ
  · intro k p hk hne
    by_cases hbi : bidIndex D.postB = some k
    · exact ⟨_, by simp only [stepBid]; rw [ite_eq_left ⟨p, hk, hne⟩, ite_eq_left hbi]⟩
    · obtain ⟨-, -, hl'⟩ := payOld k p hk hne hbi
      obtain ⟨k0, p0, hk0, hp0, hne0, -⟩ := entry_of_liveAt hl'
      obtain ⟨β, hβ⟩ := h.pay k0 p0 hp0 hne0
      exact ⟨β, by simp only [stepBid]; rw [ite_eq_left ⟨p, hk, hne⟩, ite_eq_right hbi, hk0]; exact hβ⟩
  · intro k w hk
    by_cases hlt : d + k < D.preB.builder_pending_withdrawals.toArray.toList.length
    · rw [hq_old k hlt] at hk
      obtain ⟨β, hβ⟩ := h.wd _ w hk
      exact ⟨β, by simp only [stepBid, ite_eq_left hlt]; exact hβ⟩
    · rw [hq_new k hlt] at hk
      cases he : D.pushes[d + k - D.preB.builder_pending_withdrawals.toArray.toList.length]? with
      | none => rw [he] at hk; cases hk
      | some e =>
        obtain ⟨r, β, hr, heq, -⟩ := h.push_bid hq hspe0 D g8 hA hbb (List.mem_of_getElem? he)
        exact ⟨β, by simp only [stepBid, ite_eq_right hlt, he]; rw [heq, hr]⟩
  · intro k β hβ
    rcases wdCase k β hβ with ⟨hlt, hβ0⟩ | ⟨hge, e, r, he, hr, hs, hw, hv, hsrc⟩
    · obtain ⟨hv, hslt, hdead, e, he, hes, hew, heq⟩ := h.wdOnly _ β hβ0
      refine ⟨hv, by rw [hLslot]; omega, fun w hl => hdead w (back _ _ (by omega) hl), e,
        he.mono (Nat.le_succ n), hes, hew, by rw [hq_old k hlt]; exact heq⟩
    · have hmem := List.mem_of_getElem? he
      have hlt := D.push_slot_lt hmem
      rw [paySlot_eq] at hlt
      refine ⟨hv, by rw [hLslot]; omega, fun w hl => D.push_dead hq hspe0 hmem (hs ▸ hl), e, pushN e hmem, hs,
        hw, by rw [hq_new k hge, he]; rfl⟩
  · intro k k' β β' hβ hβ' hslot
    rcases wdCase k β hβ with ⟨hlt, hβ0⟩ | ⟨hge, e, r, he, hr, hs, -⟩
    · rcases wdCase k' β' hβ' with ⟨hlt', hβ0'⟩ | ⟨hge', e', r', he', hr', hs', -⟩
      · have := h.wdInj _ _ β β' hβ0 hβ0' hslot
        omega
      · exact (clash _ β e' hβ0 (List.mem_of_getElem? he') (by rw [hs', hslot])).elim
    · rcases wdCase k' β' hβ' with ⟨hlt', hβ0'⟩ | ⟨hge', e', r', he', hr', hs', -⟩
      · exact (clash _ β' e hβ0' (List.mem_of_getElem? he) (by rw [hs, hslot])).elim
      · have := D.pushes_slot_inj hq hspe0 ⟨g7, g8, fe⟩ he he' (by rw [hs, hs', hslot])
        omega
  · intro hne
    exact ⟨_, by simp only [stepBid]; rw [ite_eq_left hne]⟩
  · intro β hβ
    simp only [stepBid] at hβ
    split at hβ
    · cases hβ; exact hL.symm
    · cases hβ

end Blanc.Lift.BuilderRequest
