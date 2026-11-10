import Blanc.Composition.BuilderRequestJointGBalance
import JauneConsensus.Facts.Gloas.StepB5
import JauneConsensus.Facts.Gloas.InvariantsControls

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

The signer clause (conformance fix SF3, statements.md B5(ii): "a bid *this* builder signed"): a positive debit of a
pending entry `e` is signed under the pubkey that the builder at `e.builder_index` has when `process_withdrawals`
reads the registry. `src_run_by` carries the key along the run, through G3-02 (`stateTransition_identityStable`) and
G3-04 (`src_pubkey_kept`: a positive pending amount keeps an exited slot from being reused); `g304_signer_control`
shows the clause fails at Jaune's G3-04 control state `s04`.
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
      ((∃ (k : Nat) (e : Gloas.BuilderPendingWithdrawal), s2.builder_pending_withdrawals.toArray[k]? = some e ∧
          w.address = e.fee_recipient ∧
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
  · cases hws; simp only [List.not_mem_nil] at hw
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
    not_routes_of_lt (Nat.lt_of_lt_of_le (hk (fun _ hv => by simp only [List.not_mem_nil] at hv) w hm) vb) hr
  rcases hw with ((hw | hw) | hw) | hw
  · obtain ⟨-, prov⟩ := getBuilderWithdrawals_provenance e1
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk' : k < bw.size := by simpa only [Array.length_toList] using hk
    obtain ⟨e, he, ha, hm, hcv⟩ := prov k hk'
    exact Or.inl ⟨k, e, he, by simpa only [Array.getElem_toList] using ha,
      by simpa only [Array.getElem_toList] using hm, by simpa only [ExceptT.stM_eq, Array.getElem_toList] using hcv,
      hsrc e (Or.inl (mem_of_getElem?' he))⟩
  · exact (hval pw (getPendingPartialWithdrawals_inRange _ _ _ _ e2) hw).elim
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk' : k < sw.size := by simpa only [Array.length_toList] using hk
    obtain ⟨bj, bb, ep, hep, hcv, hbb, hwe, hadr, hbal, hpos⟩ := getBuildersSweepWithdrawals_provenance e3 k hk'
    have hpre : (bw.toList ++ pw.toList ++ sw.toList.take k).toArray = #[] ++ bw ++ pw ++ sw.extract 0 k := by
      apply Array.toList_inj.mp
      simp only [List.append_assoc, Array.empty_append, Array.append_assoc, Array.toList_append,
        Array.toList_extract, List.extract, tsub_zero, List.drop_zero]
    have hsw := List.take_append_drop k sw.toList
    rw [List.drop_eq_getElem_cons hk] at hsw
    refine Or.inr ⟨bj, bb, ep, bw.toList ++ pw.toList ++ sw.toList.take k, sw.toList.drop (k + 1) ++ vw.toList,
      by simpa only [ExceptT.stM_eq, Array.getElem_toList] using hcv, hbb, hep, hwe,
      by simpa only [Array.getElem_toList] using hadr, ?_,
      by rw [hpre]
         simpa only [ExceptT.stM_eq, Array.empty_append, Array.append_assoc, Array.getElem_toList] using hbal,
      by simpa only [Array.getElem_toList] using hpos⟩
    simp only [Array.toList_append, List.nil_append, List.append_assoc]
    conv_lhs => rw [← hsw]
    simp only [List.append_assoc, List.cons_append]
  · exact (hval vw (getValidatorsSweepWithdrawals_inRange _ _ _ _ e4) hw).elim

/-! ## The signer is the debited builder (G3-02, G3-04)

A positive source's builder index keeps its pubkey from one Gloas state to the next: G3-02 lets a slot change its
pubkey only when its old record was reusable (`withdrawable_epoch` passed, balance `0`); a pending withdrawal or a
non-empty pending payment with a positive amount makes `pend` positive, which G3-04 forbids for an exited builder,
and a paying `L`'s builder is active (`LatestBidBuilderActive`). So the key a bid was signed with is still the key
of the builder its withdrawal debits. -/

/-- `BidCharged`, the signing key named: the bid's builder signature passed `blsVerify v` under `pk`, the pubkey of
its builder at the state the bid was processed in. -/
def BidChargedBy (ctx : Ctx) (v : Bool) (blk : Gloas.SignedBeaconBlock P) (x : Gloas.BuilderPendingWithdrawal)
    (pk : BLSPubkey) : Prop :=
  x = bidWithdrawal blk.message.body.signed_execution_payload_bid.message ∧
    U64.zero < blk.message.body.signed_execution_payload_bid.message.value ∧
    ∃ (s3 s4 : Gloas.BeaconState P) (builder : Gloas.Builder) (dom : Domain),
      Gloas.processExecutionPayloadBid ctx s3 blk.message.body.signed_execution_payload_bid = .ok s4 ∧
      s3.builders.toArray[blk.message.body.signed_execution_payload_bid.message.builder_index.toNat]? =
        some builder ∧ builder.pubkey = pk ∧
      Gloas.getDomain s3 Gloas.DOMAIN_BEACON_BUILDER = .ok dom ∧
      blsVerify v pk (computeSigningRoot blk.message.body.signed_execution_payload_bid.message dom)
        blk.message.body.signed_execution_payload_bid.signature = true

theorem BidChargedBy.charged {ctx : Ctx} {v : Bool} {blk : Gloas.SignedBeaconBlock P}
    {x : Gloas.BuilderPendingWithdrawal} {pk : BLSPubkey} (h : BidChargedBy ctx v blk x pk) :
    BidCharged ctx v blk x := by
  obtain ⟨h1, h2, s3, s4, b, d, h, hb, rfl, hd, hs⟩ := h
  exact ⟨h1, h2, s3, s4, b, d, h, hb, hd, hs⟩

/-- `BidPayment`, the signing key named. -/
def BidPaymentBy (steps : List (GJointRunStep (P := P) cfg ccfg bls)) (j : Nat) (e : Gloas.BuilderPendingWithdrawal)
    (pk : BLSPubkey) : Prop :=
  ∃ j' < j, ∃ (C : GJointRunStep (P := P) cfg ccfg bls) (blk : Gloas.SignedBeaconBlock P),
    steps[j']? = some C ∧ C.block = .gloas blk ∧ BidChargedBy (gloasCtx ccfg bls) true blk e pk

theorem BidPaymentBy.payment {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {j : Nat}
    {e : Gloas.BuilderPendingWithdrawal} {pk : BLSPubkey} (h : BidPaymentBy steps j e pk) :
    BidPayment steps j e := by
  obtain ⟨j', hj', C, blk, hC, hb, hc⟩ := h
  exact ⟨j', hj', C, blk, hC, hb, hc.charged⟩

theorem BidPaymentBy.append {steps : List (GJointRunStep (P := P) cfg ccfg bls)} {j : Nat}
    {e : Gloas.BuilderPendingWithdrawal} {pk : BLSPubkey} (h : BidPaymentBy steps j e pk) (hj : j ≤ steps.length)
    (l : List (GJointRunStep (P := P) cfg ccfg bls)) {j₂ : Nat} (hj₂ : j ≤ j₂) : BidPaymentBy (steps ++ l) j₂ e pk := by
  obtain ⟨j', hj', C, blk, hC, hb, hc⟩ := h
  exact ⟨j', by omega, C, blk, by rw [List.getElem?_append_left (by omega)]; exact hC, hb, hc⟩

/-- `AnchorEntryWitnessed`, the signing key named: `pk` is the pubkey of the witness bid's builder at the anchor. -/
def AnchorEntryWitnessedBy :
    (a : GJointState P) → AnchorBidWitness a → Gloas.BuilderPendingWithdrawal → BLSPubkey → Prop
  | .pre _, _, _, _ => False
  | .gloas b _ _, W, e, pk => ∃ r β, W.bid r = some β ∧ BidSigned b β ∧
      Gloas.builderPubkey b β.message.builder_index = .ok pk ∧ e = bidWithdrawal β.message

theorem AnchorEntryWitnessedBy.witnessed {a : GJointState P} {W : AnchorBidWitness a}
    {e : Gloas.BuilderPendingWithdrawal} {pk : BLSPubkey} (h : AnchorEntryWitnessedBy a W e pk) :
    AnchorEntryWitnessed a W e := by
  rcases a with _ | ⟨b, exec, par⟩
  · exact h.elim
  · obtain ⟨r, β, hβ, hs, -, he⟩ := h
    exact ⟨r, β, hβ, hs, he⟩

theorem builderPubkey_ok {s : Gloas.BeaconState P} {i : Gloas.BuilderIndex} {pk : BLSPubkey}
    (h : Gloas.builderPubkey s i = .ok pk) :
    ∃ bb, s.builders.toArray[i.toNat]? = some bb ∧ bb.pubkey = pk := by
  unfold Gloas.builderPubkey at h
  obtain ⟨bb, hb, h⟩ := Except.bind_eq_ok h
  exact ⟨bb, by unfold getAt at hb; split at hb <;> cases hb; assumption, Except.ok.inj h⟩

private theorem natLeSumOfMem {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih h) (Nat.le_add_left _ _)

/-- **A positive source's builder keeps its pubkey** across a G3-02 step, given G3-03, G3-04 and
`LatestBidBuilderActive` at the earlier state. -/
theorem src_pubkey_kept (hspe : 2 ≤ P.SLOTS_PER_EPOCH) {s s' : Gloas.BeaconState P}
    (g4 : ExitedHaveNoPending s) (hA : LatestBidBuilderActive s) (hB : BuilderIdentityStable s s')
    {x : Gloas.BuilderPendingWithdrawal} (hx : Src s x) (hpos : 0 < x.amount.toNat) {b : Gloas.Builder}
    (hb : s.builders.toArray[x.builder_index.toNat]? = some b) :
    ∃ b', s'.builders.toArray[x.builder_index.toNat]? = some b' ∧ b'.pubkey = b.pubkey := by
  obtain ⟨b', hb', hc⟩ := hB.2 _ b hb
  refine ⟨b', hb', ?_⟩
  rcases hc with hc | ⟨hr, -, -⟩
  · exact hc.1
  · exfalso
    have hfar : b.withdrawable_epoch = FAR_FUTURE_EPOCH := by
      rcases hx with hx | ⟨j, p, hj, hne, rfl⟩ | ⟨hv, rfl⟩
      · by_contra hne
        have h0 := g4 _ b hb hne
        have hle : wAmt x.builder_index.toNat x ≤ pend s x.builder_index.toNat := by
          unfold pend pendW
          exact Nat.le_add_right_of_le
            (natLeSumOfMem (List.mem_map.mpr ⟨x, hx, rfl⟩))
        simp only [wAmt, ↓reduceIte] at hle
        omega
      · by_contra hne'
        have h0 := g4 _ b hb hne'
        have hle : wAmt p.withdrawal.builder_index.toNat p.withdrawal ≤ pend s p.withdrawal.builder_index.toNat := by
          unfold pend pendP
          exact Nat.le_add_left_of_le
            (natLeSumOfMem (List.mem_map.mpr ⟨p, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj), rfl⟩))
        simp only [wAmt, ↓reduceIte] at hle
        omega
      · obtain ⟨b0, hb0, hf⟩ := hA hv
        simp only [bidWithdrawal] at hb
        rw [hb] at hb0
        cases hb0
        exact hf
    have h1 := hr.1
    have h2 := epoch_lt_far hspe s'
    rw [hfar] at h1
    omega

/-- The builders after Gloas `process_block` are those after its bid phase. -/
theorem processBlock_builders_of_bid {ctx : Ctx} {s post : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    {s3 s4 s5 s6 s7 : Gloas.BeaconState P}
    (h4 : Gloas.processExecutionPayloadBid ctx s3 blk.body.signed_execution_payload_bid = .ok s4)
    (h5 : Gloas.processRandao ctx s4 blk.body = .ok s5) (h6 : Gloas.processEth1Data s5 blk.body = .ok s6)
    (h7 : Gloas.processOperations ctx s6 blk.body s.latest_block_header.slot = .ok s7)
    (h8 : Gloas.processSyncAggregate ctx s7 blk.body.sync_aggregate = .ok post) :
    post.builders = s3.builders := by
  have b4 := processExecutionPayloadBid_post h4
  have c5 := coreFrame_of_inv (processRandao_invFrame _ _ _ _ h5)
  have c6 := coreFrame_of_inv (processEth1Data_invFrame _ _ _ h6)
  have c7 := processOperations_core _ _ _ _ _ h7
  have c8 := coreFrame_of_inv (processSyncAggregate_invFrame _ _ _ _ h8)
  rw [c8.1, c7.1, c6.1, c5.1, b4.2.2.2.2.1]

/-- **`src_processBlock`, the signing key at the post-state**: a new source is the block's own charged bid, signed
under the pubkey its builder has at the post-state. -/
theorem src_processBlock_by {ctx : Ctx} {s post : Gloas.BeaconState P} {blk : Gloas.SignedBeaconBlock P}
    (h : Gloas.processBlock ctx s blk.message = .ok post) {x : Gloas.BuilderPendingWithdrawal}
    (hx : Src post x) :
    Src s x ∨ ∃ bb, post.builders.toArray[x.builder_index.toNat]? = some bb ∧
      BidChargedBy ctx ctx.blsActive blk x bb.pubkey := by
  rcases src_processBlock h hx with h' | h'
  · exact Or.inl h'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  obtain ⟨rfl, hv, -⟩ := h'
  obtain ⟨builder, dom, hb, hd, hsig⟩ := processExecutionPayloadBid_sig h4 hv
  refine Or.inr ⟨builder, ?_, rfl, hv, s3, s4, builder, dom, h4, hb, rfl, hd, hsig⟩
  rw [processBlock_builders_of_bid h4 h5 h6 h7 h8]
  exact hb

/-- **A run step's positive post-state sources, with their keys**: a source of a Gloas pre-state whose builder keeps
its pubkey through the step, or the step's own charged bid, signed under the pubkey its builder has at the
post-state. -/
theorem _root_.Blanc.GJointRunStep.src_post_by (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 2 ≤ P.SLOTS_PER_EPOCH) (hdelay : 0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY)
    (C : GJointRunStep (P := P) cfg ccfg bls) (hpre : GInvJ C.preState) {b : Gloas.BeaconState P}
    {exec : BlockChain} {par : ParentPayload P}
    (hC : C.postState = .gloas b exec par) {x : Gloas.BuilderPendingWithdrawal} (hx : Src b x)
    (hpos : 0 < x.amount.toNat) :
    (∃ b0 e0 p0, C.preState = .gloas b0 e0 p0 ∧ Src b0 x ∧
        ∀ bb0, b0.builders.toArray[x.builder_index.toNat]? = some bb0 →
          ∃ bb, b.builders.toArray[x.builder_index.toNat]? = some bb ∧ bb.pubkey = bb0.pubkey) ∨
      ∃ blk, C.block = .gloas blk ∧ ∃ bb, b.builders.toArray[x.builder_index.toNat]? = some bb ∧
        BidChargedBy (gloasCtx ccfg bls) bls blk x bb.pubkey := by
  cases C with
  | pre D => cases hC
  | crossing D =>
    simp only [GJointRunStep.postState, GJointState.gloas.injEq] at hC
    obtain ⟨rfl, -, -⟩ := hC
    rcases src_processBlock_by (gloasBlockTransition_processBlock_eq D.transition) hx with h | h
    · exact absurd (srcLe_crossingSlots hq D.slots x h) (upgradeToGloas_noSrc D.upgrade x)
    · exact Or.inr ⟨D.block, rfl, h⟩
  | gloas D =>
    simp only [GJointRunStep.postState, GJointState.gloas.injEq] at hC
    obtain ⟨rfl, -, -⟩ := hC
    rcases src_processBlock_by (gloasBlockTransition_processBlock_eq D.transition) hx with h | h
    · have hs : Src D.preB x := srcLe_processSlots hq D.slots x h
      obtain ⟨-, -, g4, -, -, -, -, hA, -⟩ := (hpre : GInv D.preB)
      have hB := stateTransition_identityStable hspe hdelay D.stateTransition
      exact Or.inl ⟨D.preB, D.preExec, D.preParent, rfl, hs, fun bb0 hb0 =>
        src_pubkey_kept hspe g4 hA hB hs hpos hb0⟩
    · exact Or.inr ⟨D.block, rfl, h⟩

/-- Every positive source of a Gloas state `b` is signed, under the pubkey its builder has in `b`, by a run bid of
`steps` before `n` or as `AW` says. -/
def SignedSrcs (steps : List (GJointRunStep (P := P) cfg ccfg bls)) (n : Nat)
    (AW : Gloas.BuilderPendingWithdrawal → BLSPubkey → Prop) (b : Gloas.BeaconState P) : Prop :=
  ∀ x, Src b x → 0 < x.amount.toNat → ∃ bb, b.builders.toArray[x.builder_index.toNat]? = some bb ∧
    (BidPaymentBy steps n x bb.pubkey ∨ AW x bb.pubkey)

/-- **Every positive source at every Gloas state of a run is signed by the builder now at its index**: by a run bid
made by an earlier step (real BLS at `bls = true`), or as `AW` says, given that every positive source at a Gloas
start is; G3a's invariants ride along. -/
theorem src_run_by (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hdel : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY) (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    (hdelay : 0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) (hbls : bls = true)
    {s₀ : GJointState P} (AW : Gloas.BuilderPendingWithdrawal → BLSPubkey → Prop) (hinv₀ : GInvJ s₀)
    (h₀ : ∀ b exec par, s₀ = .gloas b exec par → ∀ x, Src b x → 0 < x.amount.toNat →
      ∃ bb, b.builders.toArray[x.builder_index.toNat]? = some bb ∧ AW x bb.pubkey) :
    ∀ {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s),
      (∀ st ∈ run.states, st.validatorCount ≤ 2 ^ 40) → (∀ st ∈ run.states, st.builderCount ≤ 2 ^ 40) →
      GInvJ s ∧ (∀ b exec par, s = .gloas b exec par → SignedSrcs run.steps run.steps.length AW b) ∧
      ∀ j C, run.steps[j]? = some C → ∀ b exec par, C.preState = .gloas b exec par →
        SignedSrcs run.steps j AW b
  | _, .nil, _, _ => ⟨hinv₀, fun b exec par hs x hx hp => by
      obtain ⟨bb, hb, h⟩ := h₀ b exec par hs x hx hp
      exact ⟨bb, hb, Or.inr h⟩,
      fun j C h => by simp only [GJointRun.steps, List.getElem?_nil, reduceCtorEq] at h⟩
  | _, .snoc run C hC, hv, hb => by
    have mem : ∀ st ∈ run.states, st ∈ (run.snoc C hC).states := fun st hst => by
      simp only [GJointRun.states, GJointRun.steps_snoc, List.map_append, List.mem_cons, List.mem_append] at hst ⊢
      rcases hst with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hpost : C.postState ∈ (run.snoc C hC).states := GJointRun.end_mem_states _
    obtain ⟨ihv, ih1, ih2⟩ := src_run_by hq hdel hspe hdelay hbls AW hinv₀ h₀ run
      (fun st h => hv st (mem st h)) (fun st h => hb st (mem st h))
    have hpre : GInvJ C.preState := hC ▸ ihv
    rw [GJointRun.steps_snoc]
    refine ⟨C.gInvJ hq hdel hspe hpre (hv _ hpost) (hb _ hpost), fun b exec par hs x hx hp => ?_,
      fun j C' h b exec par hp' x hx hpos => ?_⟩
    · rcases C.src_post_by hq hspe hdelay hpre hs hx hp with ⟨b0, e0, p0, hp0, hx0, hk⟩ | ⟨blk, hblk, bb, hbb, hc⟩
      · obtain ⟨bb0, hbb0, hprov⟩ := ih1 b0 e0 p0 (hC ▸ hp0) x hx0 hp
        obtain ⟨bb, hbb, hpk⟩ := hk bb0 hbb0
        refine ⟨bb, hbb, ?_⟩
        rw [hpk]
        rcases hprov with h | h
        · exact Or.inl (h.append (Nat.le_refl _) [C] (by rw [List.length_append]; omega))
        · exact Or.inr h
      · refine ⟨bb, hbb, Or.inl ⟨run.steps.length, by rw [List.length_append, List.length_singleton]; omega, C,
          blk, ?_, hblk, hbls ▸ hc⟩⟩
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
    · by_cases hj : j < run.steps.length
      · rw [List.getElem?_append_left hj] at h
        obtain ⟨bb, hbb, hprov⟩ := ih2 j C' h b exec par hp' x hx hpos
        refine ⟨bb, hbb, ?_⟩
        rcases hprov with h | h
        · exact Or.inl (h.append (Nat.le_of_lt hj) [C] (Nat.le_refl _))
        · exact Or.inr h
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hj), List.getElem?_singleton] at h
        split at h
        · cases h
          have hjl : j = run.steps.length := by omega
          subst hjl
          obtain ⟨bb, hbb, hprov⟩ := ih1 b exec par (hC ▸ hp') x hx hpos
          refine ⟨bb, hbb, ?_⟩
          rcases hprov with h | h
          · exact Or.inl (h.append (Nat.le_refl _) _ (Nat.le_refl _))
          · exact Or.inr h
        · cases h

/-- Every positive source of a Gloas anchor is signed by the builder at its index: its G3-14 witness bid's builder. -/
theorem anchor_src_signed {b : Gloas.BeaconState P} {exec : BlockChain} {par : ParentPayload P}
    (W : GloasBidWitness b) (hA : LatestBidBuilderActive b) (hb : b.builders.toArray.size ≤ 2 ^ 40)
    {x : Gloas.BuilderPendingWithdrawal} (hx : Src b x) :
    ∃ bb, b.builders.toArray[x.builder_index.toNat]? = some bb ∧
      AnchorEntryWitnessedBy (.gloas b exec par) W x bb.pubkey := by
  obtain ⟨r, β, hβ, hs, rfl⟩ := anchor_src_witnessed W hA hb hx
  obtain ⟨pk, -, -, hpk, -⟩ := id hs
  obtain ⟨bb, hbb, rfl⟩ := builderPubkey_ok hpk
  exact ⟨bb, hbb, r, β, hβ, hs, hpk, rfl⟩

/-- The registry `process_withdrawals` reads has the pubkeys of the block's post-state. -/
theorem processBlock_s2_pubkey {ctx : Ctx} {s post s1 s2 : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (h : Gloas.processBlock ctx s blk = .ok post)
    (h1 : Gloas.processParentExecutionPayload ctx s blk = .ok s1) (h2 : Gloas.processBlockHeader s1 blk = .ok s2)
    {i : Nat} {bb : Gloas.Builder} (hb : post.builders.toArray[i]? = some bb) :
    ∃ c, s2.builders.toArray[i]? = some c ∧ c.pubkey = bb.pubkey := by
  obtain ⟨t1, t2, s3, s4, s5, s6, s7, e1, e2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  rw [h1] at e1; cases e1
  rw [h2] at e2; cases e2
  have w3 := processWithdrawals_wFrame _ _ h3
  have hb3 : post.builders = s3.builders := processBlock_builders_of_bid h4 h5 h6 h7 h8
  have hlt : i < s2.builders.toArray.size := by
    rw [← w3.2.2.2.2.2.1, ← hb3]; exact (Array.getElem?_eq_some_iff.mp hb).1
  obtain ⟨c, hc⟩ : ∃ c, s2.builders.toArray[i]? = some c := ⟨_, Array.getElem?_eq_getElem hlt⟩
  obtain ⟨c', hc', hid⟩ := w3.2.2.2.2.2.2.1 i c hc
  rw [← hb3, hb] at hc'
  cases hc'
  exact ⟨c, hc, hid.1.1.symm⟩

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

/-- Every positive source at a Gloas anchor of a valid joint chain is signed by the builder at its index. -/
theorem anchor_signed (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    ∀ b exec par, anchor = .gloas b exec par → ∀ x, Src b x → 0 < x.amount.toNat →
      ∃ bb, b.builders.toArray[x.builder_index.toNat]? = some bb ∧
        AnchorEntryWitnessedBy anchor v.anchorWitness x bb.pubkey := by
  intro b exec par ha x hx _
  have hb := v.buildersBound anchor List.mem_cons_self
  have hi := v.anchorInv
  revert hb hi
  subst ha
  intro hb hi
  exact anchor_src_signed v.anchorWitness hi.2.2.2.2.2.2.2.1 hb hx

/-- **B5(ii): provenance of each builder debit** (`bls = true`: the bid signature check is real). At a Gloas step
`j` of a valid joint chain, every withdrawal the step's `process_withdrawals` applies that is routed to a builder is
either

* the `k`-th pending builder withdrawal `e` at the state `process_withdrawals` reads (after the parent settlement
  and the header: the prefix `get_builder_withdrawals` takes), with `w`'s address, amount and index from `e`, and
  `e` either a run bid's withdrawal (`BidPayment`: the paying bid of an earlier step's block, its builder signature
  verified under real BLS) or an anchor entry matched by a G3-14 witness bid, `L`'s included
  (`AnchorEntryWitnessed`).
  When `w` moves value (`0 < w.amount`), the signer is the debited builder: the builder at `e.builder_index` in that
  state (the index `apply_withdrawals` debits, equal to `bi` below `2^40`) has the pubkey the bid was signed under
  (`BidPaymentBy`, `AnchorEntryWitnessedBy`); or
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
      ((∃ (k : Nat) (e : Gloas.BuilderPendingWithdrawal), s2.builder_pending_withdrawals.toArray[k]? = some e ∧
          w.address = e.fee_recipient ∧
          w.amount = e.amount ∧ Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok w.validator_index ∧
          (BidPayment v.run.steps j e ∨ AnchorEntryWitnessed anchor v.anchorWitness e) ∧
          (0 < w.amount.toNat → ∃ bb : Gloas.Builder, s2.builders.toArray[e.builder_index.toNat]? = some bb ∧
            (bi.toNat < 2 ^ 40 → bi = e.builder_index) ∧
            (BidPaymentBy v.run.steps j e bb.pubkey ∨ AnchorEntryWitnessedBy anchor v.anchorWitness e bb.pubkey))) ∨
        (∃ (bj : Gloas.BuilderIndex) (bb : Gloas.Builder) (ep : Epoch) (pre post : List JauneConsensus.Withdrawal),
          Gloas.convertBuilderIndexToValidatorIndex bj = .ok w.validator_index ∧
          s2.builders.toArray[bj.toNat]? = some bb ∧ Gloas.getCurrentEpoch s2 = .ok ep ∧
          bb.withdrawable_epoch ≤ ep ∧ w.address = bb.execution_address ∧ ws = pre ++ w :: post ∧
          Gloas.getBuilderBalanceAfterWithdrawals s2 bj pre.toArray = .ok w.amount ∧ U64.zero < w.amount)) := by
  have vb := (v.post_bounds stepD).1
  obtain ⟨s1, s2, h1, h2, h⟩ := stepDebit_provenance v.quorumPositive D vb hws hw hr
  refine ⟨s1, s2, h1, h2, ?_⟩
  rcases h with ⟨k, e, he, ha, hm, hcv, hsrc⟩ | h
  · refine Or.inl ⟨k, e, he, ha, hm, hcv,
      (src_run v.quorumPositive hbls _ v.anchor_witnessed v.run).2 j _ stepD D.preB D.preExec D.preParent rfl
        e hsrc, fun hpos => ?_⟩
    have hpos' : 0 < e.amount.toNat := by rw [← hm]; exact hpos
    obtain ⟨-, -, h2s⟩ := src_run_by v.quorumPositive v.inclusionDelay v.slotsPerEpoch v.exitDelayPos hbls _
      v.anchor_gInvJ v.anchor_signed v.run v.validatorsBound v.buildersBound
    obtain ⟨bb0, hbb0, hprov⟩ := h2s j _ stepD D.preB D.preExec D.preParent rfl e hsrc hpos'
    obtain ⟨-, -, g4, -, -, -, -, hA, -⟩ := v.gInv_pre stepD
    obtain ⟨bb, hbb, hpk⟩ := src_pubkey_kept v.slotsPerEpoch g4 hA
      (stateTransition_identityStable v.slotsPerEpoch v.exitDelayPos D.stateTransition) hsrc hpos' hbb0
    obtain ⟨c, hc, hcpk⟩ :=
      processBlock_s2_pubkey (gloasBlockTransition_processBlock_eq D.transition) h1 h2 hbb
    refine ⟨c, hc, fun hbi => ?_, by rw [hcpk, hpk]; exact hprov⟩
    have hlt : e.builder_index.toNat < 2 ^ 40 :=
      Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hbb).1 (v.post_bounds stepD).2
    exact U64.ext_toNat (routes_inj hr hcv hbi hlt)
  · exact Or.inr h

end ValidJointG


/-! ## The G3-04 control bites the signer clause -/

/-- **G3-04 control on B5(ii)'s signer clause** (Jaune's `g304_control`, state `s04`). Without G3-04, exited and
swept builder 0 still has the pending withdrawal `w5` of 5 gwei, a positive source; a deposit for a new pubkey
reuses slot 0 (and `g304_control` shows the builder withdrawals then debit the new builder by 5). The builder now at
`w5`'s index has a pubkey that no anchor witness of `w5` can be signed under: every such witness names builder 0's
pubkey at the anchor. So `builder_withdrawal_provenance`'s signer clause fails at an `s04` anchor (with a run of no
earlier step, `BidPaymentBy` is empty), and G3-04 is the premise its proof (`src_pubkey_kept`) consumes. -/
theorem g304_signer_control :
    ¬ ExitedHaveNoPending Controls.s04 ∧ Src Controls.s04 Controls.w5 ∧ 0 < Controls.w5.amount.toNat ∧
    ∃ (s1 : Gloas.BeaconState Preset.minimal) (bb : Gloas.Builder),
      Gloas.processBuilderDepositRequest Controls.ctxOff Controls.s04 Controls.depK = .ok s1 ∧
      s1.builders.toArray[Controls.w5.builder_index.toNat]? = some bb ∧
      ∀ (exec : BlockChain) (par : ParentPayload Preset.minimal)
        (W : AnchorBidWitness (GJointState.gloas Controls.s04 exec par)),
        ¬ AnchorEntryWitnessedBy (GJointState.gloas Controls.s04 exec par) W Controls.w5 bb.pubkey := by
  refine ⟨Controls.g304_control.1, Or.inl (by
    simp only [Controls.s04, ProgressiveListS.ofArray, List.mem_cons, List.not_mem_nil, or_false]), by decide, ?_⟩
  have hk : (Gloas.processBuilderDepositRequest Controls.ctxOff Controls.s04 Controls.depK).toOption.map
      (fun s1 => s1.builders.toArray[0]?.map (·.pubkey)) = some (some (Witnesses.pk 9)) := by
    decide +kernel
  cases h : Gloas.processBuilderDepositRequest Controls.ctxOff Controls.s04 Controls.depK with
  | error e => rw [h] at hk; cases hk
  | ok s1 =>
    rw [h] at hk
    obtain ⟨bb, hbb, hpk⟩ := Option.map_eq_some_iff.mp (Option.some.inj hk)
    refine ⟨s1, bb, rfl, hbb, ?_⟩
    rintro exec par W ⟨r, β, -, -, hpk', he⟩
    have hi : β.message.builder_index = U64.zero := (congrArg (·.builder_index) he).symm
    rw [hi] at hpk'
    obtain ⟨b0, hb0, hpk0⟩ := builderPubkey_ok hpk'
    have h0 : Controls.s04.builders.toArray[U64.zero.toNat]? =
        some (Witnesses.bld 1 ⟨1⟩ U64.zero U64.zero U64.zero) := rfl
    rw [h0] at hb0
    cases hb0
    rw [hpk] at hpk0
    exact absurd hpk0 (by decide)

end Blanc.Lift.BuilderRequest
