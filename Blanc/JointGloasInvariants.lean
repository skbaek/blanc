import Blanc.JointGloasHistory
import JauneConsensus.Facts.Gloas.Invariants
import JauneConsensus.Facts.Gloas.InvariantsBid
import JauneConsensus.Facts.Gloas.InvariantsCrossing
import JauneConsensus.Facts.Gloas.InvariantsRequests
import JauneConsensus.Facts.Gloas.HeaderFrames
import JauneConsensus.Facts.Gloas.FirstBlockFrames

/-!
# The joint-level Gloas invariants G3-09, G3-10, G3-11, and the crossing's FULL settlement (O-b)

The three joint-level rows of Plans `recon/design.md` §5 (rev 3.1), over `GJointState`:

* **G3-09 `ExecHeadIsLatestBlockHash`**: the built-upon chain's head hash is the beacon state's
  `latest_block_hash` (on a pre-Gloas state, the Electra/Fulu `latest_execution_payload_header.block_hash`, the
  hash `upgrade_to_gloas` copies into `latest_block_hash`, FK:176);
* **G3-10 `ParentPayloadCoherence`**: a delivered payload is for the latest bid (`block_hash`), on the latest
  block hash (`parent_hash`), its request is the envelope's, and its chain is the engine's verdict on the built-upon
  chain; a landed payload is the head, and its bid commits to the empty requests;
* **G3-11 `ExpectedWithdrawalsLedger`** (list form): a delivered payload carries exactly
  `payload_expected_withdrawals`; a landed one leaves none outstanding.

Preservation (`GloasStepData.gJointInv`, `CrossingData.gJointInv`, `GJointRunStep.postState_ledger`): G3-10 and
G3-11 hold at every run step's post-state outright (the envelope check establishes them); G3-09 is carried by a
Gloas step from G3-09 and G3-10 at its pre-state, established by every pre-Gloas step outright (`PreStepData.execHead`,
from Jaune's `jointStep_head`), and established by the crossing from the Fulu head relation at its pre-state
(`CrossingData.fuluHead`, through Jaune's `crossFromFulu_header`); so every run step carries all three
(`GJointRunStep.gJointInv_post`).

**G3-11, full ledger form** (`GJointRun.expectedWithdrawals_ledger`): at a Gloas state the run ends in,
`payload_expected_withdrawals` is the withdrawals debited by the last step that wrote it (the crossing or a FULL
Gloas step, `GloasStepData.pew_full`, `CrossingData.pew_full`), every later step settling EMPTY, which keeps it
exactly (`GloasStepData.pew_empty`) and builds upon nothing; or the anchor's, every step settling EMPTY. The debited
withdrawals are thus credited in no built-upon payload yet.

**O-b** (`crossing_parentFull`, `jointStepG_cross_ok_of_spec`): at the crossing, Gloas `process_block` succeeding
forces the FULL settlement, because `upgrade_to_gloas` sets `latest_block_hash` to the synthetic bid's
`block_hash` (FK:176, 209) and the bid check requires `bid.parent_block_hash == latest_block_hash` (CL:2193). So the
joint step's named refusal of an EMPTY first settlement excludes no chain the beacon transition accepts.

**O-a** (the builder half of `crossing_builders`, `CrossingData.buildersPkWe`, `CrossingData.buildersFar`): after
the first Gloas block every builder has `upgrade_to_gloas`'s pubkey and `withdrawable_epoch`, all
`FAR_FUTURE_EPOCH`, and there are as many: the first block's requests are empty, so neither a builder request nor a
fresh record runs (the writers of `withdrawable_epoch` are only those, `withdrawableEpoch_writers`). Complete
(`CrossingData.builders_eq`, Jaune's `crossing_builders_eq`): the builders are exactly `upgrade_to_gloas`'s,
balances included, and `builder_pending_withdrawals` is `upgrade_to_gloas`'s (empty).
-/

namespace Blanc

open Jaune JauneConsensus ExecutionTrace JauneConsensus.Facts.Gloas

variable {P : Preset}

/-! ## Vocabulary -/

/-- The hash of a chain's head block, if any. -/
def execHeadHash (ch : BlockChain) : Option B256 := ch.blocks.getLast?.map (·.header.hash)

/-- **G3-09 ExecHeadIsLatestBlockHash.** -/
def ExecHeadIsLatestBlockHash : GJointState P → Prop
  | .pre s => execHeadHash s.exec = some s.beacon.latest_execution_payload_header.block_hash
  | .gloas b exec _ => execHeadHash exec = some b.latest_block_hash

/-- **G3-10 ParentPayloadCoherence.** -/
def ParentPayloadCoherence (cfg : ChainConfig) : GJointState P → Prop
  | .gloas b exec (.delivered e req post) =>
    e.message.payload.block_hash = b.latest_execution_payload_bid.block_hash ∧
      e.message.payload.parent_hash = b.latest_block_hash ∧
      Gloas.envelopeNewPayloadRequest b e = .ok req ∧ engineVerdictG cfg exec req = .ok post
  | .gloas b exec .landed =>
    b.latest_execution_payload_bid.block_hash = b.latest_block_hash ∧
      execHeadHash exec = some b.latest_block_hash ∧
      b.latest_execution_payload_bid.execution_requests_root =
        Ssz.hashTreeRoot Gloas.ExecutionRequests.empty
  | _ => True

/-- **G3-11 ExpectedWithdrawalsLedger** (the list form). -/
def ExpectedWithdrawalsLedger : GJointState P → Prop
  | .gloas b _ (.delivered e _ _) => Gloas.WithdrawalsMatchExpected b e
  | .gloas b _ .landed => b.payload_expected_withdrawals.toArray.toList = []
  | _ => True

/-- The three joint-level invariants together. -/
def GJointInv (cfg : ChainConfig) (s : GJointState P) : Prop :=
  ExecHeadIsLatestBlockHash s ∧ ParentPayloadCoherence cfg s ∧ ExpectedWithdrawalsLedger s

/-- G3-10 includes the coherence the run's kept history needs. -/
theorem ParentPayloadCoherence.coherent {cfg : ChainConfig} {s : GJointState P}
    (h : ParentPayloadCoherence cfg s) : ParentCoherent cfg s := by
  rcases s with _ | ⟨b, exec, _ | _ | ⟨e, req, post⟩⟩
  all_goals first | trivial | exact h.2.2.2

/-! ## Frames of `latest_block_hash` and the latest bid -/

/-- Gloas `process_slots` keeps the builders, the latest bid and `latest_block_hash`. -/
theorem processSlots_bidFrame {ctx : Ctx} {s s' : Gloas.BeaconState P} {slot : Slot}
    (h : Gloas.processSlots ctx s slot = .ok s') :
    s'.builders = s.builders ∧ s'.latest_execution_payload_bid = s.latest_execution_payload_bid ∧
      s'.latest_block_hash = s.latest_block_hash :=
  Inv.processSlots_ind (ctx := ctx)
    (fun m => m.builders = s.builders ∧
      m.latest_execution_payload_bid = s.latest_execution_payload_bid ∧
      m.latest_block_hash = s.latest_block_hash)
    (fun _ _ _ _ hI f1 _ hc => by
      obtain ⟨hb, hl, hk, _, _⟩ := Inv.slotIter_core f1 hc
      exact ⟨hb.trans hI.1, hl.trans hI.2.1, hk.trans hI.2.2⟩) h ⟨rfl, rfl, rfl⟩

/-- The crossing's slots function keeps the builders, the latest bid and `latest_block_hash`. -/
theorem crossingSlots_bidFrame {ctx : Ctx} {s s' : Gloas.BeaconState P} {slot : Slot}
    (h : crossingSlots ctx s slot = .ok s') :
    s'.builders = s.builders ∧ s'.latest_execution_payload_bid = s.latest_execution_payload_bid ∧
      s'.latest_block_hash = s.latest_block_hash := by
  unfold crossingSlots at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · exact processSlots_bidFrame h

/-- The rest of a Gloas `state_transition` after the slots is Gloas `process_block`. -/
theorem gloasBlockTransition_processBlock_eq {ctx : Ctx} {st post : Gloas.BeaconState P}
    {b : Gloas.SignedBeaconBlock P} (h : gloasBlockTransition ctx st b = .ok post) :
    Gloas.processBlock ctx st b.message = .ok post :=
  Inv.applySignedBlockWith_ok h

/-- **Gloas `process_block` moves `latest_block_hash` only by a FULL settlement**, to the parent bid's
`block_hash`; and the block's bid builds on the `latest_block_hash` the settlement leaves (CL:2193). -/
theorem processBlock_latestBlockHash {ctx : Ctx} {s s' : Gloas.BeaconState P}
    {blk : Gloas.BeaconBlock P} (h : Gloas.processBlock ctx s blk = .ok s') :
    s'.latest_block_hash =
        (if parentFull s blk then s.latest_execution_payload_bid.block_hash else s.latest_block_hash) ∧
      blk.body.signed_execution_payload_bid.message.parent_block_hash =
        (if parentFull s blk then s.latest_execution_payload_bid.block_hash else s.latest_block_hash) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Inv.processBlock_phases h
  have hs1 : s1.latest_block_hash =
      (if parentFull s blk then s.latest_execution_payload_bid.block_hash else s.latest_block_hash) := by
    rcases Inv.processParentExecutionPayload_cases h1 with ⟨he, hne⟩ | ⟨heq, a, d, e, ha, hd, he, hs⟩
    · have hf : parentFull s blk = false := by
        unfold parentFull
        exact beq_false_of_ne hne
      rw [hf, he]
      rfl
    · have hf : parentFull s blk = true := by
        unfold parentFull
        exact beq_iff_eq.mpr heq
      rw [hf]
      exact (Inv.parentFull_frame ha hd he hs).2.2.2.1
  obtain ⟨-, -, hm2⟩ := Inv.processBlockHeader_post h2
  have e2 : s2.latest_block_hash = s1.latest_block_hash := by rw [hm2]
  have w3 := Inv.processWithdrawals_wFrame _ _ h3
  have b4 := Inv.processExecutionPayloadBid_post h4
  have c := Inv.afterBid_core h5 h6 h7 h8
  refine ⟨?_, ?_⟩
  · rw [c.2.2.1, b4.2.2.2.2.2.1, w3.2.1, e2, hs1]
  · rw [b4.2.2.1, w3.2.1, e2, hs1]

/-- A Gloas `process_block` from a state whose `latest_block_hash` is the latest bid's `block_hash` settles the
parent FULL. -/
theorem processBlock_full_of_latestBlockHash {ctx : Ctx} {s s' : Gloas.BeaconState P}
    {blk : Gloas.BeaconBlock P} (h : Gloas.processBlock ctx s blk = .ok s')
    (hl : s.latest_block_hash = s.latest_execution_payload_bid.block_hash) : parentFull s blk = true := by
  have hb := (processBlock_latestBlockHash h).2
  cases hf : parentFull s blk with
  | true => rfl
  | false =>
    rw [hf, ite_eq_right (by simp only [Bool.false_eq_true, not_false_eq_true]), hl] at hb
    unfold parentFull at hf
    rw [hb, beq_self_eq_true] at hf
    cases hf

/-- `upgrade_to_gloas` sets `latest_block_hash` and the synthetic bid's `block_hash` both to the Fulu
`latest_execution_payload_header.block_hash` (FK:176, 209). -/
theorem upgradeToGloas_latestBlockHash {ctx : Ctx} {pre : BeaconState P .fulu}
    {post : Gloas.BeaconState P} (h : Gloas.upgradeToGloas ctx pre = .ok post) :
    post.latest_block_hash = pre.latest_execution_payload_header.block_hash ∧
      post.latest_execution_payload_bid.block_hash = pre.latest_execution_payload_header.block_hash := by
  unfold Gloas.upgradeToGloas at h
  obtain ⟨p0, hp0, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨fr, -⟩ := Inv.onboard_post h
  unfold Gloas.upgradedState at hp0
  obtain ⟨_, _, hp0⟩ := Except.bind_eq_ok hp0
  obtain ⟨_, _, hp0⟩ := Except.bind_eq_ok hp0
  cases hp0
  obtain ⟨_, _, _, hL, hK, _⟩ := fr
  exact ⟨hK, by rw [hL]⟩

/-! ## O-b: the crossing settles FULL -/

/-- **O-b.** At the crossing, if Gloas `process_block` accepts the first Gloas block, its settlement is FULL:
`upgrade_to_gloas` leaves `latest_block_hash` equal to the synthetic bid's `block_hash`, the crossing's slots keep
both, and the bid check (CL:2193) then makes the block's bid build on that hash. -/
theorem crossing_parentFull {ccfg : Config} {bls : Bool} {beacon : BeaconState P .fulu}
    {upgraded postSlots post : Gloas.BeaconState P} {b : Gloas.SignedBeaconBlock P}
    (hup : Gloas.crossFromFulu (gloasCtx ccfg bls) beacon = .ok upgraded)
    (h0 : crossingSlots (gloasCtx ccfg bls) upgraded b.message.slot = .ok postSlots)
    (hp : gloasBlockTransition (gloasCtx ccfg bls) postSlots b = .ok post) :
    parentFull postSlots b.message = true := by
  obtain ⟨atFork, hat⟩ := crossFromFulu_upgrade hup
  obtain ⟨hk, hl⟩ := upgradeToGloas_latestBlockHash hat
  obtain ⟨-, hL, hK⟩ := crossingSlots_bidFrame h0
  refine processBlock_full_of_latestBlockHash (gloasBlockTransition_processBlock_eq hp) ?_
  rw [hK, hL, hk, hl]

/-- **O-b, the refusal excludes no spec-valid chain.** A Fulu state before the fork slot, a Gloas block at or
after it, the crossing (`crossFromFulu`) and slots, and the block accepted by the Gloas block transition: then the
joint step's crossing succeeds as soon as the block's `parent_execution_requests` are empty by value (the SF-7
strengthening of the spec's root check, FK:218) and its envelope, if any, passes. The named refusal of an EMPTY
first settlement (`jointStepG_cross_refuses_empty`) never fires on such a chain. -/
theorem jointStepG_cross_ok_of_spec {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon : BeaconState P .fulu} {exec : BlockChain} {b : Gloas.SignedBeaconBlock P}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {upgraded postSlots post : Gloas.BeaconState P}
    {s' : GJointState P}
    (h1 : beacon.slot.toNat < gloasForkSlot (P := P) ccfg) (h2 : gloasForkSlot (P := P) ccfg ≤ b.message.slot.toNat)
    (hup : Gloas.crossFromFulu (gloasCtx ccfg bls) beacon = .ok upgraded)
    (h0 : crossingSlots (gloasCtx ccfg bls) upgraded b.message.slot = .ok postSlots)
    (hp : gloasBlockTransition (gloasCtx ccfg bls) postSlots b = .ok post)
    (hr : b.message.body.parent_execution_requests = Gloas.ExecutionRequests.empty)
    (hd : gloasDeliverOpt cfg ccfg bls post exec env? = .ok s') :
    jointStepG cfg ccfg bls (.pre ⟨.fulu, beacon, exec⟩) (.gloas b) env? = .ok s' :=
  jointStepG_cross_ok_iff.mpr ⟨h1, h2, upgraded, postSlots, post, hup, h0, crossing_parentFull hup h0 hp, hr, hp, hd⟩

/-! ## G3-10 and G3-11 at every post-state -/

/-- The request `envelopeNewPayloadRequest` builds carries the envelope's payload. -/
theorem envelopeNewPayloadRequest_payload {state : Gloas.BeaconState P}
    {e : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P}
    (h : Gloas.envelopeNewPayloadRequest state e = .ok req) :
    req.execution_payload = e.message.payload := by
  unfold Gloas.envelopeNewPayloadRequest at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl

/-- The end of a Gloas step establishes G3-10 and G3-11: the envelope check ties a delivered payload to the
post-block state's bid and `latest_block_hash`, its withdrawals to `payload_expected_withdrawals`, and its chain
to the engine. -/
theorem gloasDeliverOpt_ledger {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {post : Gloas.BeaconState P} {exec : BlockChain} {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)}
    {s' : GJointState P} (h : gloasDeliverOpt cfg ccfg bls post exec env? = .ok s') :
    ParentPayloadCoherence cfg s' ∧ ExpectedWithdrawalsLedger s' := by
  rcases gloasDeliverOpt_ok_iff.mp h with ⟨-, rfl⟩ | ⟨e, req, postE, -, hv, rfl⟩
  · exact ⟨trivial, trivial⟩
  · obtain ⟨hc, hw, hr, he⟩ := verifyEnvelopeG_ok_iff.mp hv
    exact ⟨⟨hc.blockHash, hc.parentHash, hr, he⟩, hw⟩

/-- **G3-10 and G3-11 hold at every run step's post-state**, whatever its pre-state. -/
theorem GJointRunStep.postState_ledger {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GJointRunStep (P := P) cfg ccfg bls) :
    ParentPayloadCoherence cfg D.postState ∧ ExpectedWithdrawalsLedger D.postState := by
  cases D with
  | pre D => exact ⟨trivial, trivial⟩
  | crossing D => exact gloasDeliverOpt_ledger D.deliver
  | gloas D => exact gloasDeliverOpt_ledger D.deliver

/-! ## G3-09 -/

/-- **G3-09 across a Gloas step**, from G3-09 and G3-10 at the pre-state. FULL over a delivered payload: the
chain becomes the engine's, whose head is the payload's block, whose hash is the payload's `block_hash`, the
latest bid's (G3-10), which the settlement writes to `latest_block_hash`. FULL over a landed payload: the bid's
`block_hash` already is `latest_block_hash` (G3-10). EMPTY: neither moves. -/
theorem GloasStepData.execHead {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GloasStepData (P := P) cfg ccfg bls)
    (h9 : ExecHeadIsLatestBlockHash (GJointState.gloas D.preB D.preExec D.preParent))
    (h10 : ParentPayloadCoherence cfg (GJointState.gloas D.preB D.preExec D.preParent)) :
    ExecHeadIsLatestBlockHash (GJointState.gloas D.postB D.postExec D.postParent) := by
  have hpb := (processBlock_latestBlockHash (gloasBlockTransition_processBlock_eq D.transition)).1
  obtain ⟨-, hL, hK⟩ := processSlots_bidFrame D.slots
  change execHeadHash D.preExec = some D.preB.latest_block_hash at h9
  show execHeadHash D.postExec = some D.postB.latest_block_hash
  rcases settleParent_ok_iff.mp D.settleOk with
    ⟨hf, env, req, post, hpar, -, hex, -⟩ | ⟨hf, hpar, -, hex, -⟩ | ⟨hf, -, hex, -⟩
  · rw [hpar] at h10
    obtain ⟨hbh, -, hreq, heng⟩ := h10
    rw [hpb, hf, ite_eq_left rfl, hL, hex, execHeadHash, engineVerdictG_getLast heng, Option.map_some,
      (engineVerdictG_ok_iff.mp heng).2.1, envelopeNewPayloadRequest_payload hreq, hbh]
  · rw [hpar] at h10
    obtain ⟨hbh, -, -⟩ := h10
    rw [hpb, hf, ite_eq_left rfl, hL, hex, hbh, h9]
  · rw [hpb, hf, ite_eq_right (by simp only [Bool.false_eq_true, not_false_eq_true]), hK, hex, h9]

/-- **G3-09 across the crossing**, from the Fulu head relation at the fork state `atFork`: the built-upon chain
does not move, and the first block's FULL settlement writes the synthetic bid's `block_hash`, which
`upgrade_to_gloas` copied from `atFork`'s `latest_execution_payload_header`. -/
theorem CrossingData.execHead {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : CrossingData (P := P) cfg ccfg bls)
    (h : execHeadHash D.exec = some D.atFork.latest_execution_payload_header.block_hash) :
    ExecHeadIsLatestBlockHash (GJointState.gloas D.postB D.exec D.postParent) := by
  have hpb := (processBlock_latestBlockHash (gloasBlockTransition_processBlock_eq D.transition)).1
  obtain ⟨-, hL, -⟩ := crossingSlots_bidFrame D.slots
  obtain ⟨-, hl⟩ := upgradeToGloas_latestBlockHash D.upgrade
  show execHeadHash D.exec = some D.postB.latest_block_hash
  rw [hpb, D.full, ite_eq_left rfl, hL, hl, h]

/-- **The joint invariants across a Gloas step.** -/
theorem GloasStepData.gJointInv {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GloasStepData (P := P) cfg ccfg bls)
    (h : GJointInv cfg (GJointState.gloas D.preB D.preExec D.preParent)) :
    GJointInv cfg (GJointState.gloas D.postB D.postExec D.postParent) :=
  ⟨D.execHead h.1 h.2.1, gloasDeliverOpt_ledger D.deliver⟩

/-- **The joint invariants across the crossing**, from the Fulu head relation at the fork state. -/
theorem CrossingData.gJointInv {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : CrossingData (P := P) cfg ccfg bls)
    (h : execHeadHash D.exec = some D.atFork.latest_execution_payload_header.block_hash) :
    GJointInv cfg (GJointState.gloas D.postB D.exec D.postParent) :=
  ⟨D.execHead h, gloasDeliverOpt_ledger D.deliver⟩

/-! ## O-a: the builders after the first Gloas block -/

/-- The first Gloas block's parent settlement, with empty requests, leaves the builders as they were. -/
theorem processParentExecutionPayload_builders_of_empty {ctx : Ctx} {s s1 : Gloas.BeaconState P}
    {blk : Gloas.BeaconBlock P} (h : Gloas.processParentExecutionPayload ctx s blk = .ok s1)
    (hr : blk.body.parent_execution_requests = Gloas.ExecutionRequests.empty) : s1.builders = s.builders := by
  rcases Inv.processParentExecutionPayload_cases h with ⟨he, -⟩ | ⟨-, a, d, e, ha, hd, he, hs⟩
  · rw [he]
  · rw [hr] at hd he
    have ca := Inv.applyParentPrefix_core _ _ _ _ ha
    cases hd
    cases he
    rw [(Inv.applyParentSuffix_post hs).1]
    exact ca.1

/-- **O-a, the builders.** After the first Gloas block, the builders are `upgrade_to_gloas`'s, as pubkeys and
withdrawable epochs, and as many: the crossing's slots keep them, the parent settlement over empty requests keeps
them, and the rest of the block writes neither (`processBlock_after_parent`). -/
theorem CrossingData.buildersPkWe {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : CrossingData (P := P) cfg ccfg bls) : BuildersPkWe D.upgraded D.postB := by
  obtain ⟨hb0, -, -⟩ := crossingSlots_bidFrame D.slots
  obtain ⟨mid, hmid, hpk⟩ :=
    processBlock_after_parent _ _ _ _ (gloasBlockTransition_processBlock_eq D.transition)
  have hm : mid.builders = D.upgraded.builders :=
    (processParentExecutionPayload_builders_of_empty hmid D.emptyRequests).trans hb0
  unfold BuildersPkWe at hpk ⊢
  rw [hm] at hpk
  exact hpk

/-- **O-a, `withdrawable_epoch`.** After the first Gloas block every builder is at `FAR_FUTURE_EPOCH`. -/
theorem CrossingData.buildersFar {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : CrossingData (P := P) cfg ccfg bls) : BuildersFar D.postB := by
  obtain ⟨-, hmap⟩ := D.buildersPkWe
  have hf := (upgradeToGloas_builders D.upgrade).1
  intro i x hx
  have hi := hmap i
  rw [hx] at hi
  cases hu : D.upgraded.builders.toArray[i]? with
  | none => rw [hu] at hi; cases hi
  | some y =>
    rw [hu] at hi
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hi
    rw [hi.2]
    exact hf i y hu

/-! ## G3-09 over pre-Gloas steps and the crossing's Fulu head relation (G3c) -/

/-- The engine's chain after an accepted Electra/Fulu payload ends with the payload's block. -/
theorem engineVerdict_getLast {cfg : ChainConfig} {cf : CFork} {exec post : BlockChain}
    {req : NewPayloadRequest P} (h : engineVerdict cfg cf exec req = .ok post) :
    post.blocks.getLast? = some (payloadToBlock req) := by
  obtain ⟨_, _, _, hc, f, hf, _, _, hs, _⟩ := engineVerdict_ok_iff.mp h
  obtain ⟨_, _, _, _, _, _, rfl⟩ :=
    exists_configuredBody_of_transition (stateTransitionUsing_of_scheduled hc hf hs)
  exact appendBlock_getLast? _ _

/-- **G3-09 after every pre-Gloas joint step**, whatever held before: the step's chain ends with its
payload's block, whose hash is the post-state's `latest_execution_payload_header.block_hash`
(Jaune's `jointStep_head`). -/
theorem jointStep_execHead {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s s' : JointState P}
    {b : AnySignedBlock P} (h : jointStep cfg ccfg bls s b = .ok s') :
    ExecHeadIsLatestBlockHash (GJointState.pre s') := by
  obtain ⟨req, hv, hh⟩ := jointStep_head h
  show execHeadHash s'.exec = some _
  rw [execHeadHash, engineVerdict_getLast hv, Option.map_some, hh]

/-- **G3-09 across a pre-Gloas run step.** -/
theorem PreStepData.execHead {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : PreStepData (P := P) cfg ccfg bls) : ExecHeadIsLatestBlockHash (GJointState.pre D.post) :=
  jointStep_execHead D.step

/-- **The crossing's Fulu head relation from its pre-state**: `crossFromFulu` upgrades a state carrying the
pre-state's `latest_execution_payload_header` (Jaune's `crossFromFulu_header`), and `upgrade_to_gloas` copies its
`block_hash` into `latest_block_hash`, so every fork state that upgrades to the crossing's upgraded state has the
pre-state's `block_hash`. -/
theorem CrossingData.fuluHead {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : CrossingData (P := P) cfg ccfg bls)
    (h : ExecHeadIsLatestBlockHash (GJointState.pre ⟨.fulu, D.preFulu, D.exec⟩)) :
    execHeadHash D.exec = some D.atFork.latest_execution_payload_header.block_hash := by
  obtain ⟨atFork', hup', hhd⟩ := crossFromFulu_header D.cross
  have e1 := (upgradeToGloas_latestBlockHash hup').1
  have e2 := (upgradeToGloas_latestBlockHash D.upgrade).1
  change execHeadHash D.exec = some D.preFulu.latest_execution_payload_header.block_hash at h
  rw [← e2, e1, hhd]
  exact h

/-- **The joint invariants after every run step**, from G3-09 at its pre-state (only the crossing reads it). -/
theorem GJointRunStep.gJointInv_post {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GJointRunStep (P := P) cfg ccfg bls) (h : GJointInv cfg D.preState) :
    GJointInv cfg D.postState := by
  cases D with
  | pre D => exact ⟨D.execHead, trivial, trivial⟩
  | crossing C => exact C.gJointInv (C.fuluHead h.1)
  | gloas G => exact G.gJointInv h

/-! ## O-a: the builders after the first Gloas block, as an equality (G3c) -/

/-- **O-a, complete.** After the first Gloas block the builders are exactly `upgrade_to_gloas`'s, balances
included, and `builder_pending_withdrawals` is `upgrade_to_gloas`'s (empty) (Jaune's `crossing_builders_eq`):
the crossing's slots append nothing (every payment empty, the quorum positive), the settlement appends nothing,
and `process_withdrawals` debits no builder (none pending, the validator phases route to validators only, the
sweep finds every builder at `FAR_FUTURE_EPOCH`). The N7 bounds at the post-state and the configuration bounds
`quorumPositive`, `slotsPerEpoch` are `ValidJointG` fields. -/
theorem CrossingData.builders_eq {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : CrossingData (P := P) cfg ccfg bls)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    (validatorsBound : D.postB.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : D.postB.builders.toArray.size ≤ 2 ^ 40) :
    D.postB.builders = D.upgraded.builders ∧
      D.postB.builder_pending_withdrawals = D.upgraded.builder_pending_withdrawals :=
  crossing_builders_eq quorumPositive slotsPerEpoch D.upgrade D.slots
    (gloasBlockTransition_processBlock_eq D.transition) D.emptyRequests validatorsBound buildersBound

/-! ## G3-11's frame: `payload_expected_withdrawals` across a step (G3c) -/

/-- **G3-11, EMPTY preservation, per Gloas step.** A step that settles its parent EMPTY keeps
`payload_expected_withdrawals` exactly (the early return of `process_withdrawals`, and no other phase or slot
writes it) and withdraws nothing. -/
theorem GloasStepData.pew_empty {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GloasStepData (P := P) cfg ccfg bls) (hE : parentFull D.postSlots D.block.message = false) :
    D.postB.payload_expected_withdrawals = D.preB.payload_expected_withdrawals ∧
      stepWithdrawals ccfg bls D.postSlots D.block.message = .ok [] := by
  obtain ⟨e, hw⟩ :=
    (processBlock_payloadExpectedWithdrawals (gloasBlockTransition_processBlock_eq D.transition)).1 hE
  exact ⟨e.trans (processSlots_pew D.slots), hw⟩

/-- **G3-11, the write, per Gloas step.** A step that settles its parent FULL (over a delivered or the landed
payload) ends with `payload_expected_withdrawals` exactly the withdrawals its `process_withdrawals` debited. -/
theorem GloasStepData.pew_full {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GloasStepData (P := P) cfg ccfg bls) (hF : parentFull D.postSlots D.block.message = true) :
    ∃ ws, stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws ∧
      D.postB.payload_expected_withdrawals.toArray.toList = ws :=
  (processBlock_payloadExpectedWithdrawals (gloasBlockTransition_processBlock_eq D.transition)).2 hF

/-- **G3-11, the write, at the crossing.** The first Gloas block settles FULL, so it ends with
`payload_expected_withdrawals` exactly the withdrawals its `process_withdrawals` debited. -/
theorem CrossingData.pew_full {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : CrossingData (P := P) cfg ccfg bls) :
    ∃ ws, stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws ∧
      D.postB.payload_expected_withdrawals.toArray.toList = ws :=
  (processBlock_payloadExpectedWithdrawals (gloasBlockTransition_processBlock_eq D.transition)).2 D.full

/-- An EMPTY Gloas step builds upon nothing. -/
theorem GloasStepData.kept_of_empty {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : GloasStepData (P := P) cfg ccfg bls) (hE : parentFull D.postSlots D.block.message = false) :
    D.kept = [] := by
  rcases settleParent_ok_iff.mp D.settleOk with ⟨hf, -⟩ | ⟨hf, -⟩ | ⟨-, -, -, hs⟩
  · rw [hE] at hf; cases hf
  · rw [hE] at hf; cases hf
  · rcases D.keptSpec with ⟨_, _, _, h, -⟩ | ⟨-, hk⟩
    · rw [hs] at h; cases h
    · exact hk

/-- A run step that writes `payload_expected_withdrawals` to `ws`: the crossing, or a Gloas step settling its
parent FULL, whose `process_withdrawals` debited `ws`. -/
def _root_.Blanc.GJointRunStep.WritesExpected {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (ws : List JauneConsensus.Withdrawal) : GJointRunStep (P := P) cfg ccfg bls → Prop
  | .pre _ => False
  | .crossing D => stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws
  | .gloas D => parentFull D.postSlots D.block.message = true ∧
      stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws

/-- A run step that settles its parent EMPTY: a Gloas step that withdraws nothing and builds upon nothing. -/
def _root_.Blanc.GJointRunStep.SettlesEmpty {cfg : ChainConfig} {ccfg : Config} {bls : Bool} :
    GJointRunStep (P := P) cfg ccfg bls → Prop
  | .gloas D => parentFull D.postSlots D.block.message = false ∧ D.kept = []
  | _ => False

/-- **G3-11, the full ledger form, over a joint run.** At a Gloas state the run ends in,
`payload_expected_withdrawals` is either

* exactly the withdrawals `ws` debited by the last step `i` that wrote it (the crossing, or a Gloas step settling
  FULL), and every later step settles EMPTY, preserving it exactly and building upon nothing: `ws` has been
  debited on the consensus side and credited in no built-upon payload yet; or
* the anchor's `payload_expected_withdrawals`, every step of the run settling EMPTY and building upon nothing. -/
theorem _root_.Blanc.GJointRun.expectedWithdrawals_ledger {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ : GJointState P} :
    {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) →
    ∀ {b : Gloas.BeaconState P} {exec : BlockChain} {par : ParentPayload P}, s = .gloas b exec par →
    (∃ (i : Nat) (C : GJointRunStep (P := P) cfg ccfg bls) (ws : List JauneConsensus.Withdrawal),
        run.steps[i]? = some C ∧ C.WritesExpected ws ∧ b.payload_expected_withdrawals.toArray.toList = ws ∧
        ∀ k, i < k → k < run.steps.length →
          ∃ C' : GJointRunStep (P := P) cfg ccfg bls, run.steps[k]? = some C' ∧ C'.SettlesEmpty) ∨
      ((∀ (k : Nat) (C' : GJointRunStep (P := P) cfg ccfg bls), run.steps[k]? = some C' → C'.SettlesEmpty) ∧
        ∃ (b₀ : Gloas.BeaconState P) (e₀ : BlockChain) (p₀ : ParentPayload P), s₀ = .gloas b₀ e₀ p₀ ∧
          b.payload_expected_withdrawals = b₀.payload_expected_withdrawals)
  | _, .nil, b, exec, par, h => Or.inr ⟨fun k C' h' => by simp only [GJointRun.steps, List.length_nil,
      not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h', b, exec, par, h, rfl⟩
  | _, .snoc run D hD, b, exec, par, h => by
    have hlen : (run.snoc D hD).steps.length = run.steps.length + 1 := by
      simp only [GJointRun.steps_snoc, List.length_append, List.length_cons, List.length_nil, zero_add]
    have hlast : (run.snoc D hD).steps[run.steps.length]? = some D := by
      simp only [GJointRun.steps_snoc, List.length_append, List.length_cons, List.length_nil, zero_add,
          lt_add_iff_pos_right, zero_lt_one, getElem?_pos, Std.le_refl, List.getElem_append_right,
          tsub_self, List.getElem_cons_zero]
    have hprev : ∀ k, k < run.steps.length → (run.snoc D hD).steps[k]? = run.steps[k]? := by
      intro k hk; rw [GJointRun.steps_snoc, List.getElem?_append_left hk]
    cases D with
    | pre D => simp only [GJointRunStep.postState, reduceCtorEq] at h
    | crossing C =>
      simp only [GJointRunStep.postState, GJointState.gloas.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      obtain ⟨ws, hw, he⟩ := C.pew_full
      exact Or.inl ⟨run.steps.length, .crossing C, ws, hlast, hw, he, fun k h1 h2 => by omega⟩
    | gloas G =>
      simp only [GJointRunStep.postState, GJointState.gloas.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      cases hF : parentFull G.postSlots G.block.message with
      | true =>
        obtain ⟨ws, hw, he⟩ := G.pew_full hF
        exact Or.inl ⟨run.steps.length, .gloas G, ws, hlast, ⟨hF, hw⟩, he, fun k h1 h2 => by omega⟩
      | false =>
        obtain ⟨e, -⟩ := G.pew_empty hF
        have hE : (GJointRunStep.gloas G).SettlesEmpty := ⟨hF, G.kept_of_empty hF⟩
        rcases GJointRun.expectedWithdrawals_ledger run hD.symm with
          ⟨i, C, ws, hi, hw, he', hk⟩ | ⟨hall, b₀, e₀, p₀, h₀, he'⟩
        · have hil : i < run.steps.length := (List.getElem?_eq_some_iff.mp hi).1
          refine Or.inl ⟨i, C, ws, by rw [hprev i hil]; exact hi, hw, by rw [e]; exact he', ?_⟩
          intro k h1 h2
          by_cases hkl : k < run.steps.length
          · obtain ⟨C', hC', hs⟩ := hk k h1 hkl
            exact ⟨C', by rw [hprev k hkl]; exact hC', hs⟩
          · have : k = run.steps.length := by omega
            subst this
            exact ⟨_, hlast, hE⟩
        · refine Or.inr ⟨fun k C' hk => ?_, b₀, e₀, p₀, h₀, by rw [e]; exact he'⟩
          by_cases hkl : k < run.steps.length
          · rw [hprev k hkl] at hk; exact hall k C' hk
          · have hk' := (List.getElem?_eq_some_iff.mp hk).1
            rw [hlen] at hk'
            have : k = run.steps.length := by omega
            subst this
            rw [hlast] at hk; cases hk; exact hE

end Blanc
