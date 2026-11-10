import Blanc.Composition.BuilderRequestJointGBalance
import JauneConsensus.Facts.Gloas.StepB5

/-!
# B5(ii) over a valid Gloas joint chain: where every builder debit comes from

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B5 (ii), with the
`AnchorEntryWitnessed` disjunct of finding 3).

Jaune's `Src s` are the withdrawal sources of a Gloas state: a pending builder withdrawal, a non-empty pending
payment's withdrawal, or a paying latest bid's. Along a run:

* `src_processBlock`: Gloas `process_block` creates no source but its own paying bid's withdrawal, whose builder
  signature passed `blsVerify ctx.blsActive` at the state the bid was processed in (the block-only half of Jaune's
  `GStepView.src_step`, so the crossing's first block is covered too);
* `upgradeToGloas_noSrc`: the upgraded state has no source (empty queues, `L` self-built with value `0`); the
  crossing's slots create none, so the first Gloas block's sources are its own bid's;
* `anchor_src_witnessed`: at a Gloas anchor every source is matched by a witness bid of `anchorWitness` (G3-14),
  signed under real BLS. A paying `L` (`0 < L.value`) is a non-self-build bid: G3's `LatestBidBuilderActive` puts
  its builder in the registry, whose size the N7 bound keeps below `2^40 < BUILDER_INDEX_SELF_BUILD` (the spec's
  reason is CL:2170, a self-build bid has value `0`);
* `src_run`: every source at every Gloas state of the run is a run bid's (`BidPayment`, made by an earlier step, its
  signature verified under real BLS at `bls = true`) or an anchor witness's (`AnchorEntryWitnessed`).

`stepDebit_provenance` sharpens Jaune's `GStepView.debit_provenance`: a builder-routed withdrawal of a Gloas step
is the `k`-th entry of the pending builder withdrawals at the state `process_withdrawals` reads (after the parent
settlement and the header), or a withdrawable builder's own sweep, for exactly its balance after the withdrawals
before it. The headline is `ValidJointG.builder_withdrawal_provenance`.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts.Gloas JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## Sources across one block -/

/-- A block's bid is charged: its withdrawal is `x`, it pays, and its builder signature passed `blsVerify v` at the
state the bid was processed in. -/
def BidCharged (ctx : Ctx) (v : Bool) (blk : Gloas.SignedBeaconBlock P) (x : Gloas.BuilderPendingWithdrawal) :
    Prop :=
  x = bidWithdrawal blk.message.body.signed_execution_payload_bid.message ∧
    U64.zero < blk.message.body.signed_execution_payload_bid.message.value ∧
    ∃ (s3 s4 : Gloas.BeaconState P) (builder : Gloas.Builder) (dom : Domain),
      Gloas.processExecutionPayloadBid ctx s3 blk.message.body.signed_execution_payload_bid = .ok s4 ∧
      s3.builders.toArray[blk.message.body.signed_execution_payload_bid.message.builder_index.toNat]? =
        some builder ∧
      Gloas.getDomain s3 Gloas.DOMAIN_BEACON_BUILDER = .ok dom ∧
      blsVerify v builder.pubkey (computeSigningRoot blk.message.body.signed_execution_payload_bid.message dom)
        blk.message.body.signed_execution_payload_bid.signature = true

/-- **Gloas `process_block` creates no source but its own paying bid's.** -/
theorem src_processBlock {ctx : Ctx} {s post : Gloas.BeaconState P} {blk : Gloas.SignedBeaconBlock P}
    (h : Gloas.processBlock ctx s blk.message = .ok post) {x : Gloas.BuilderPendingWithdrawal}
    (hx : Src post x) : Src s x ∨ BidCharged ctx ctx.blsActive blk x := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have hpre : SrcLe s s3 := by
    obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
    have w3 := processWithdrawals_wFrame _ _ h3
    have hw3 : SrcLe s2 s3 := by
      rcases processWithdrawals_cases h3 with rfl | ⟨ex, t, -, -, -, hp', hw'⟩
      · exact SrcLe.refl _
      · intro y hy
        rcases hy with hy | hy | ⟨hv, hy⟩
        · rw [hw'] at hy; exact Or.inl (List.mem_of_mem_drop hy)
        · rw [hp'] at hy; exact Or.inr (Or.inl hy)
        · rw [w3.1] at hv hy; exact Or.inr (Or.inr ⟨hv, hy⟩)
    exact (srcLe_parent h1).trans ((srcLe_of_eqs (by rw [hm2]) (by rw [hm2]) (by rw [hm2])).trans hw3)
  have hpost : SrcLe s4 post :=
    (srcLe_of_inv (processRandao_invFrame _ _ _ _ h5)).trans
      ((srcLe_of_inv (processEth1Data_invFrame _ _ _ h6)).trans
        ((srcLe_ops (processOperations_ops _ _ _ _ _ h7)).trans
          (srcLe_of_inv (processSyncAggregate_invFrame _ _ _ _ h8))))
  rcases src_bid h4 x (hpost x hx) with h | ⟨rfl, hv⟩
  · exact Or.inl (hpre x h)
  · obtain ⟨builder, dom, hb, hd, hsig⟩ := processExecutionPayloadBid_sig h4 hv
    exact Or.inr ⟨rfl, hv, s3, s4, builder, dom, h4, hb, hd, hsig⟩

/-- **The upgraded state has no source**: `upgrade_to_gloas` leaves both queues empty and the latest bid a
self-build bid of value `0` (FK:202-215). -/
theorem upgradeToGloas_noSrc {ctx : Ctx} {pre : BeaconState P .fulu} {post : Gloas.BeaconState P}
    (h : Gloas.upgradeToGloas ctx pre = .ok post) (x : Gloas.BuilderPendingWithdrawal) : ¬ Src post x := by
  unfold Gloas.upgradeToGloas at h
  obtain ⟨p0, hp0, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨fr, -⟩ := onboard_post h
  unfold Gloas.upgradedState at hp0
  obtain ⟨_, _, hp0⟩ := Except.bind_eq_ok hp0
  obtain ⟨_, _, hp0⟩ := Except.bind_eq_ok hp0
  cases hp0
  obtain ⟨_, hP, hW, hL, -⟩ := fr
  simp only [] at hP hW hL
  have hWe : post.builder_pending_withdrawals.toArray.toList = [] := by rw [hW]; rfl
  have hPa : post.builder_pending_payments.toArray =
      Array.replicate (2 * P.SLOTS_PER_EPOCH) Gloas.BuilderPendingPayment.empty := by
    rw [hP]; rfl
  have hval : post.latest_execution_payload_bid.value = U64.zero := by rw [hL]
  rintro (hx | ⟨j, p, hj, hne, -⟩ | ⟨hv, -⟩)
  · rw [hWe] at hx; cases hx
  · rw [hPa, Array.getElem?_replicate] at hj
    split at hj
    · cases hj; exact hne rfl
    · cases hj
  · rw [hval] at hv; exact absurd hv (by decide)

/-- The crossing's slots create no source. -/
theorem srcLe_crossingSlots (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) {ctx : Ctx}
    {s s' : Gloas.BeaconState P} {slot : Slot} (h : crossingSlots ctx s slot = .ok s') : SrcLe s s' := by
  unfold crossingSlots at h
  split at h
  · cases h; exact SrcLe.refl _
  · exact srcLe_processSlots hq h

/-- **A run step's post-state sources**: its pre-state's (a Gloas pre-state), or its own block's charged bid. -/
theorem _root_.Blanc.GJointRunStep.src_post (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (C : GJointRunStep (P := P) cfg ccfg bls) {b : Gloas.BeaconState P} {exec : BlockChain} {par : ParentPayload P}
    (hC : C.postState = .gloas b exec par) {x : Gloas.BuilderPendingWithdrawal} (hx : Src b x) :
    (∃ b0 e0 p0, C.preState = .gloas b0 e0 p0 ∧ Src b0 x) ∨
      ∃ blk, C.block = .gloas blk ∧ BidCharged (gloasCtx ccfg bls) bls blk x := by
  cases C with
  | pre D => cases hC
  | crossing D =>
    simp only [GJointRunStep.postState, GJointState.gloas.injEq] at hC
    obtain ⟨rfl, -, -⟩ := hC
    rcases src_processBlock (gloasBlockTransition_processBlock_eq D.transition) hx with h | h
    · exact absurd (srcLe_crossingSlots hq D.slots x h) (upgradeToGloas_noSrc D.upgrade x)
    · exact Or.inr ⟨D.block, rfl, h⟩
  | gloas D =>
    simp only [GJointRunStep.postState, GJointState.gloas.injEq] at hC
    obtain ⟨rfl, -, -⟩ := hC
    rcases src_processBlock (gloasBlockTransition_processBlock_eq D.transition) hx with h | h
    · exact Or.inl ⟨D.preB, D.preExec, D.preParent, rfl, srcLe_processSlots hq D.slots x h⟩
    · exact Or.inr ⟨D.block, rfl, h⟩

/-! ## The anchor's sources are witnessed -/

/-- **G3-14's witness of an anchor entry** (statements.md B5(ii), rev 3.1 finding 3): a witness bid of the anchor,
for any of its references (a pending payment, a pending withdrawal, or the latest bid `L`), signed under real BLS at
the anchor, whose recorded withdrawal is `e`. False at a pre-Gloas anchor. -/
def AnchorEntryWitnessed : (a : GJointState P) → AnchorBidWitness a → Gloas.BuilderPendingWithdrawal → Prop
  | .pre _, _, _ => False
  | .gloas b _ _, W, e => ∃ r β, W.bid r = some β ∧ BidSigned b β ∧ e = bidWithdrawal β.message

/-- The self-build index is not a registry index below `2^40`. -/
theorem selfBuild_toNat : Gloas.BUILDER_INDEX_SELF_BUILD.toNat = 2 ^ 64 - 1 := rfl

/-- **Every source of a Gloas anchor is witnessed.** A paying `L` is not a self-build bid: its builder is in the
registry (`LatestBidBuilderActive`), whose size the N7 bound keeps at most `2^40`. -/
theorem anchor_src_witnessed {b : Gloas.BeaconState P} (W : GloasBidWitness b) (hA : LatestBidBuilderActive b)
    (hb : b.builders.toArray.size ≤ 2 ^ 40) {x : Gloas.BuilderPendingWithdrawal} (hx : Src b x) :
    ∃ r β, W.bid r = some β ∧ BidSigned b β ∧ x = bidWithdrawal β.message := by
  rcases hx with hx | ⟨j, p, hj, hne, rfl⟩ | ⟨hv, rfl⟩
  · obtain ⟨k, hk⟩ := getElem?_of_mem' hx
    obtain ⟨β, hβ, hs, he⟩ := W.withdrawal k x hk
    exact ⟨_, β, hβ, hs, he⟩
  · obtain ⟨β, hβ, hs, he⟩ := W.payment j p hj hne
    exact ⟨_, β, hβ, hs, he⟩
  · have hne : b.latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD := by
      intro he
      obtain ⟨bb, hbb, -⟩ := hA hv
      have hlt := (Array.getElem?_eq_some_iff.mp hbb).1
      rw [he, selfBuild_toNat] at hlt
      omega
    obtain ⟨β, hβ, hs, he⟩ := W.latest hne
    exact ⟨_, β, hβ, hs, by rw [he]⟩

/-! ## Sources along a run -/

/-- **A run-created bid payment** (statements.md `BidPayment`): `e` is the withdrawal of the paying bid of the block
of a step `j' < j` of `steps`, whose builder signature passed Jaune's real `blsVerify` (`true`) at the state the bid
was processed in. -/
def BidPayment (steps : List (GJointRunStep (P := P) cfg ccfg bls)) (j : Nat) (e : Gloas.BuilderPendingWithdrawal) :
    Prop :=
  ∃ j' < j, ∃ (C : GJointRunStep (P := P) cfg ccfg bls) (blk : Gloas.SignedBeaconBlock P),
    steps[j']? = some C ∧ C.block = .gloas blk ∧ BidCharged (gloasCtx ccfg bls) true blk e

theorem BidPayment.append {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {j : Nat}
    {e : Gloas.BuilderPendingWithdrawal} (h : BidPayment steps j e) (hj : j ≤ steps.length)
    (l : List (GJointRunStep (P := P) cfg ccfg bls)) : BidPayment (steps ++ l) j e := by
  obtain ⟨j', hj', C, blk, hC, hb, hc⟩ := h
  exact ⟨j', hj', C, blk, by rw [List.getElem?_append_left (by omega)]; exact hC, hb, hc⟩

/-- **Every source at every Gloas state of a run** is a run bid's (made by an earlier step, under real BLS) or
satisfies `AW`, given that every source at a Gloas start does. -/
theorem src_run (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hbls : bls = true)
    {s₀ : GJointState P} (AW : Gloas.BuilderPendingWithdrawal → Prop)
    (h₀ : ∀ b exec par, s₀ = .gloas b exec par → ∀ x, Src b x → AW x) :
    ∀ {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s),
      (∀ b exec par, s = .gloas b exec par → ∀ x, Src b x → BidPayment run.steps run.steps.length x ∨ AW x) ∧
      ∀ j C, run.steps[j]? = some C → ∀ b exec par, C.preState = .gloas b exec par → ∀ x, Src b x →
        BidPayment run.steps j x ∨ AW x
  | _, .nil => ⟨fun b exec par hs x hx => Or.inr (h₀ b exec par hs x hx),
      fun j C h => by simp only [GJointRun.steps, List.getElem?_nil, reduceCtorEq] at h⟩
  | _, .snoc run C hC => by
    obtain ⟨ih1, ih2⟩ := src_run hq hbls AW h₀ run
    rw [GJointRun.steps_snoc]
    refine ⟨fun b exec par hs x hx => ?_, fun j C' h b exec par hp x hx => ?_⟩
    · rcases C.src_post hq hs hx with ⟨b0, e0, p0, hp, hx0⟩ | ⟨blk, hblk, hc⟩
      · rcases ih1 b0 e0 p0 (hC ▸ hp) x hx0 with h | h
        · exact Or.inl ((h.append (Nat.le_refl _) [C]).elim fun j' ⟨hj', rest⟩ =>
            ⟨j', by rw [List.length_append]; omega, rest⟩)
        · exact Or.inr h
      · refine Or.inl ⟨run.steps.length, by rw [List.length_append, List.length_singleton]; omega, C, blk, ?_,
          hblk, hbls ▸ hc⟩
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
    · by_cases hj : j < run.steps.length
      · rw [List.getElem?_append_left hj] at h
        rcases ih2 j C' h b exec par hp x hx with h | h
        · exact Or.inl (h.append (Nat.le_of_lt hj) [C])
        · exact Or.inr h
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hj), List.getElem?_singleton] at h
        split at h
        · cases h
          have hjl : j = run.steps.length := by omega
          subst hjl
          rcases ih1 b exec par (hC ▸ hp) x hx with h | h
          · exact Or.inl (h.append (Nat.le_refl _) _)
          · exact Or.inr h
        · cases h

/-! ## Debits per step, sharpened -/

/-- **A Gloas step's builder debits, at the state `process_withdrawals` reads.** Each builder-routed withdrawal
the step applies is (a) the `k`-th pending builder withdrawal at that state (after the parent settlement and the
header), with its address, amount and index, the entry a source of the step's pre-state; or (b) the builders sweep
paying a builder `bj` of that state whose `withdrawable_epoch` has passed, to its own `execution_address`, for
exactly its balance after the withdrawals before it in the list (`get_builder_balance_after_withdrawals`), a
positive amount. -/
theorem stepDebit_provenance (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (D : GloasStepData (P := P) cfg ccfg bls) (vbound : D.postB.validators.toArray.size ≤ 2 ^ 40)
    {ws : List JauneConsensus.Withdrawal} (hws : stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws)
    {w : JauneConsensus.Withdrawal} (hw : w ∈ ws) {bi : U64} (hr : Routes bi w) :
    ∃ s1 s2 : Gloas.BeaconState P,
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1 ∧
      Gloas.processBlockHeader s1 D.block.message = .ok s2 ∧
      ((∃ (k : Nat) (e : Gloas.BuilderPendingWithdrawal), s2.builder_pending_withdrawals.toArray[k]? = some e ∧ w.address = e.fee_recipient ∧
          w.amount = e.amount ∧ Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok w.validator_index ∧
          Src D.preB e) ∨
        (∃ (bj : Gloas.BuilderIndex) (bb : Gloas.Builder) (ep : Epoch) (pre post : List JauneConsensus.Withdrawal),
          Gloas.convertBuilderIndexToValidatorIndex bj = .ok w.validator_index ∧
          s2.builders.toArray[bj.toNat]? = some bb ∧ Gloas.getCurrentEpoch s2 = .ok ep ∧
          bb.withdrawable_epoch ≤ ep ∧ w.address = bb.execution_address ∧ ws = pre ++ w :: post ∧
          Gloas.getBuilderBalanceAfterWithdrawals s2 bj pre.toArray = .ok w.amount ∧ U64.zero < w.amount)) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    processBlock_phases (gloasBlockTransition_processBlock_eq D.transition)
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have vb : s2.validators.toArray.size ≤ 2 ^ 40 := by
    have va : D.postB.validators.toArray.size = s3.validators.toArray.size :=
      afterWithdrawals_vlen h4 h5 h6 h7 h8
    have vb' : s3.validators.toArray.size = s2.validators.toArray.size :=
      processWithdrawals_vlen _ _ h3
    omega
  have hsrc : SrcLe D.preB s2 := (srcLe_processSlots hq D.slots).trans
    ((srcLe_parent h1).trans (srcLe_of_eqs (by rw [hm2]) (by rw [hm2]) (by rw [hm2])))
  refine ⟨s1, s2, h1, h2, ?_⟩
  simp only [stepWithdrawals, h1, h2, bind, Except.bind] at hws
  split at hws
  · cases hws; simp at hw
  obtain ⟨ex, hex, hws⟩ := Except.bind_eq_ok hws
  cases hws
  unfold Gloas.getExpectedWithdrawals at hex
  obtain ⟨⟨bw, i1, n1⟩, e1, hex⟩ := Except.bind_eq_ok hex
  obtain ⟨⟨pw, i2, n2⟩, e2, hex⟩ := Except.bind_eq_ok hex
  obtain ⟨⟨sw, i3, n3⟩, e3, hex⟩ := Except.bind_eq_ok hex
  obtain ⟨⟨vw, i4, n4⟩, e4, hex⟩ := Except.bind_eq_ok hex
  cases hex
  simp only [Array.toList_append, List.mem_append, List.nil_append] at hw
  have hval : ∀ (l : Array JauneConsensus.Withdrawal),
      (keepAll (fun w => w.validator_index.toNat < s2.validators.toArray.size)).R #[] l →
      w ∈ l.toList → False := fun l hk hm =>
    not_routes_of_lt (Nat.lt_of_lt_of_le (hk (fun _ hv => by simp at hv) w hm) vb) hr
  rcases hw with ((hw | hw) | hw) | hw
  · obtain ⟨-, prov⟩ := getBuilderWithdrawals_provenance e1
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk' : k < bw.size := by simpa using hk
    obtain ⟨e, he, ha, hm, hcv⟩ := prov k hk'
    exact Or.inl ⟨k, e, he, by simpa using ha, by simpa using hm, by simpa using hcv,
      hsrc e (Or.inl (mem_of_getElem?' he))⟩
  · exact (hval pw (getPendingPartialWithdrawals_inRange _ _ _ _ e2) hw).elim
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk' : k < sw.size := by simpa using hk
    obtain ⟨bj, bb, ep, hep, hcv, hbb, hwe, hadr, hbal, hpos⟩ := getBuildersSweepWithdrawals_provenance e3 k hk'
    have hpre : (bw.toList ++ pw.toList ++ sw.toList.take k).toArray = #[] ++ bw ++ pw ++ sw.extract 0 k := by
      apply Array.toList_inj.mp
      simp [Array.toList_extract, List.extract]
    have hsw := List.take_append_drop k sw.toList
    rw [List.drop_eq_getElem_cons hk] at hsw
    refine Or.inr ⟨bj, bb, ep, bw.toList ++ pw.toList ++ sw.toList.take k, sw.toList.drop (k + 1) ++ vw.toList,
      by simpa using hcv, hbb, hep, hwe, by simpa using hadr, ?_, by rw [hpre]; simpa using hbal,
      by simpa using hpos⟩
    simp only [Array.toList_append, List.nil_append, List.append_assoc]
    conv_lhs => rw [← hsw]
    simp only [List.append_assoc, List.cons_append]
  · exact (hval vw (getValidatorsSweepWithdrawals_inRange _ _ _ _ e4) hw).elim

/-! ## B5(ii) over a valid joint chain -/

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- Every source at a Gloas anchor of a valid joint chain is witnessed. -/
theorem anchor_witnessed (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    ∀ b exec par, anchor = .gloas b exec par → ∀ x, Src b x →
      AnchorEntryWitnessed anchor v.anchorWitness x := by
  intro b exec par ha x hx
  have hb := v.buildersBound anchor List.mem_cons_self
  have hi := v.anchorInv
  revert hb hi
  subst ha
  intro hb hi
  exact anchor_src_witnessed v.anchorWitness hi.2.2.2.2.2.2.2.1 hb hx

/-- **B5(ii): provenance of each builder debit** (`bls = true`: the bid signature check is real). At a Gloas step
`j` of a valid joint chain, every withdrawal the step's `process_withdrawals` applies that is routed to a builder is
either

* the `k`-th pending builder withdrawal `e` at the state `process_withdrawals` reads (after the parent settlement
  and the header: the prefix `get_builder_withdrawals` takes), with `w`'s address, amount and index from `e`, and
  `e` either a run bid's withdrawal (`BidPayment`: the paying bid of an earlier step's block, its builder signature
  verified under real BLS) or an anchor entry matched by a G3-14 witness bid, `L`'s included
  (`AnchorEntryWitnessed`); or
* the builders sweep paying a builder of that state whose `withdrawable_epoch` has passed, to its own
  `execution_address`, exactly its balance after the withdrawals before it, a positive amount.

Adaptations: `D.expectedBuilderWithdrawals` is written as the step's withdrawals (`stepWithdrawals`, RBA's form)
routed to a builder (`Routes bi w`); the sweep's builder is read at the state `get_expected_withdrawals` reads. -/
theorem builder_withdrawal_provenance (v : ValidJointG cfg ccfg bls checkpoint anchor final) (hbls : bls = true)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {ws : List JauneConsensus.Withdrawal} (hws : stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws)
    {w : JauneConsensus.Withdrawal} (hw : w ∈ ws) {bi : U64} (hr : Routes bi w) :
    ∃ s1 s2 : Gloas.BeaconState P,
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1 ∧
      Gloas.processBlockHeader s1 D.block.message = .ok s2 ∧
      ((∃ (k : Nat) (e : Gloas.BuilderPendingWithdrawal), s2.builder_pending_withdrawals.toArray[k]? = some e ∧ w.address = e.fee_recipient ∧
          w.amount = e.amount ∧ Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok w.validator_index ∧
          (BidPayment v.run.steps j e ∨ AnchorEntryWitnessed anchor v.anchorWitness e)) ∨
        (∃ (bj : Gloas.BuilderIndex) (bb : Gloas.Builder) (ep : Epoch) (pre post : List JauneConsensus.Withdrawal),
          Gloas.convertBuilderIndexToValidatorIndex bj = .ok w.validator_index ∧
          s2.builders.toArray[bj.toNat]? = some bb ∧ Gloas.getCurrentEpoch s2 = .ok ep ∧
          bb.withdrawable_epoch ≤ ep ∧ w.address = bb.execution_address ∧ ws = pre ++ w :: post ∧
          Gloas.getBuilderBalanceAfterWithdrawals s2 bj pre.toArray = .ok w.amount ∧ U64.zero < w.amount)) := by
  have vb := (v.post_bounds stepD).1
  obtain ⟨s1, s2, h1, h2, h⟩ := stepDebit_provenance v.quorumPositive D vb hws hw hr
  refine ⟨s1, s2, h1, h2, ?_⟩
  rcases h with ⟨k, e, he, ha, hm, hcv, hsrc⟩ | h
  · refine Or.inl ⟨k, e, he, ha, hm, hcv, ?_⟩
    exact (src_run v.quorumPositive hbls _ v.anchor_witnessed v.run).2 j _ stepD D.preB D.preExec D.preParent rfl
      e hsrc
  · exact Or.inr h

end ValidJointG

end Blanc.Lift.BuilderRequest
