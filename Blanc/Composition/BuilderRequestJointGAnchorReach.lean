import Blanc.Composition.BuilderRequestJointGAnchorReachDomain
import Blanc.Composition.BuilderRequestJointGAnchorQueued

/-!
# The anchor witness exists on every Gloas state reached from a Fulu anchor

Goal `eip8282-charge-once-v1`, outcome C4. `ValidJointG` asks a Gloas anchor for bid witnesses
(`GloasBidWitness`, G3-14), and `anchor_witness_charged_once_queued` reads their injectivity. On a real chain
Gloas begins at the fork, and the witness is not an assumption: it is built from the history.

* `reach_hist`: along any run from a pre-Gloas state, every Gloas state has a history witness (`Hist`): after
  the crossing by `Hist.crossing`, after each Gloas step by `Hist.step`.
* **`ValidJointG.reach_witness`** (C4): at every Gloas state `b` of a valid joint chain from a Fulu anchor there
  is a `GloasBidWitness b` whose every bid is the signed bid of an earlier step's block (the crossing's first
  Gloas block or a Gloas step's), with: a payment reference's bid the one whose payment is live at that index; a
  queue reference's bid the one whose payment an earlier step appended as that queue entry (its slot, its
  withdrawal); the latest reference's bid the latest bid. So at every Gloas state a real chain reaches, the
  witness the Gloas-anchor theorems ask for exists and is the chain's own bids (the chain is not re-anchored there).
* **`ValidJointG.push_is_step_bid`**: every element the run appends to `builder_pending_withdrawals` is the
  payment of the signed bid of an earlier step's block: the append's slot is that bid's and its element that
  bid's withdrawal. This attributes each append to a bid, the first Gloas block's included.
* `ValidJointG.crossing_bid_append_is_bid`: an append at the first Gloas block's bid's slot is that bid's
  withdrawal (the element identity `crossing_bid_appended_at_most_once` lacked): block slots strictly increase
  from the crossing on (`gblock_slot_lt`), so the bid of that slot is the crossing's.
* **`ValidJointG.reach_witness_message`**: the same witness, with `WitnessMessagesInjective`: two of its bids
  with one message are one signed bid. A step's bid is of its block's slot and block slots strictly increase
  (`stepBid_slot_inj`), so one message means one step's block; no fact about BLS signatures is used.

`BidSigned` at a later state reads the signing domain there; that the Gloas transition keeps `fork` and
`genesis_validators_root` is `domainKept` (`BuilderRequestJointGAnchorReachDomain`).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## Along a run -/

theorem _root_.Blanc.GJointRun.states_snoc {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s)
    (C : GJointRunStep (P := P) cfg ccfg bls) (hC : C.preState = s) :
    (run.snoc C hC).states = run.states ++ [C.postState] := by
  simp only [GJointRun.states, GJointRun.steps_snoc, List.map_append, List.map_cons, List.map_nil,
    List.cons_append]

theorem _root_.Blanc.GJointRun.states_length {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) :
    run.states.length = run.steps.length + 1 := by
  simp only [GJointRun.states, List.length_cons, List.length_map]

/-- The end of a run is its last state. -/
theorem _root_.Blanc.GJointRun.states_end {s₀ : GJointState P} :
    ∀ {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s), run.states[run.steps.length]? = some s
  | _, .nil => rfl
  | _, .snoc run C hC => by
    rw [GJointRun.states_snoc, GJointRun.steps_snoc, List.length_append, List.length_singleton,
      List.getElem?_append_right (by rw [run.states_length]), run.states_length, Nat.sub_self]
    rfl

/-- State `j` of a run is step `j`'s pre-state. -/
theorem _root_.Blanc.GJointRun.states_pre {s₀ : GJointState P} :
    ∀ {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) {j : Nat}
      {C : GJointRunStep (P := P) cfg ccfg bls}, run.steps[j]? = some C → run.states[j]? = some C.preState
  | _, .nil, _, _, h => by simp only [GJointRun.steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run B hB, j, C, h => by
    rw [GJointRun.steps_snoc] at h
    rw [GJointRun.states_snoc]
    by_cases hj : j < run.steps.length
    · rw [List.getElem?_append_left hj] at h
      rw [List.getElem?_append_left (by rw [run.states_length]; omega)]
      exact GJointRun.states_pre run h
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hj), List.getElem?_singleton] at h
      split at h
      · cases h
        have hjl : j = run.steps.length := by omega
        subst hjl
        rw [List.getElem?_append_left (by rw [run.states_length]; omega), run.states_end, hB]
      · cases h

/-- **Every Gloas state of a run from a pre-Gloas state has a history witness**, built from the steps before
it; G3a's invariants ride along. -/
theorem reach_hist (hbls : bls = true)
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hdel : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY) (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    (hdelay : 0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) {s₀ : JointState P} :
    ∀ {s : GJointState P} (run : GJointRun cfg ccfg bls (.pre s₀) s),
      (∀ st ∈ run.states, st.validatorCount ≤ 2 ^ 40) → (∀ st ∈ run.states, st.builderCount ≤ 2 ^ 40) →
      GInvJ s ∧ (∀ b ex pa, s = .gloas b ex pa → ∃ bid, Hist run.steps run.steps.length b bid) ∧
        ∀ i b ex pa, run.states[i]? = some (.gloas b ex pa) → ∃ bid, Hist run.steps i b bid
  | _, .nil, _, _ => by
    refine ⟨trivial, fun b ex pa h => (by cases h), fun i b ex pa h => ?_⟩
    cases i with
    | zero =>
      simp only [GJointRun.states, GJointRun.steps, List.map_nil, List.getElem?_cons_zero, Option.some.injEq,
        reduceCtorEq] at h
    | succ i =>
      simp only [GJointRun.states, GJointRun.steps, List.map_nil, List.getElem?_cons_succ, List.getElem?_nil,
        reduceCtorEq] at h
  | _, .snoc run C hC, hv, hb => by
    have mem : ∀ st ∈ run.states, st ∈ (run.snoc C hC).states := fun st hst => by
      rw [GJointRun.states_snoc]; exact List.mem_append_left _ hst
    have hpost : C.postState ∈ (run.snoc C hC).states := GJointRun.end_mem_states _
    obtain ⟨ihv, ih1, ih2⟩ := reach_hist hbls hq hdel hspe hdelay run
      (fun st h => hv st (mem st h)) (fun st h => hb st (mem st h))
    have hpre : GInvJ C.preState := hC ▸ ihv
    have hinv : GInvJ C.postState := C.gInvJ hq hdel hspe hpre (hv _ hpost) (hb _ hpost)
    have hCn : (run.steps ++ [C])[run.steps.length]? = some C := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
    have hend : ∀ b ex pa, C.postState = .gloas b ex pa →
        ∃ bid, Hist (run.steps ++ [C]) (run.steps.length + 1) b bid := by
      intro b ex pa hs
      have hvb := hv _ hpost
      have hbb := hb _ hpost
      cases C with
      | pre D => cases hs
      | crossing D =>
        simp only [GJointRunStep.postState, GJointState.gloas.injEq] at hs
        obtain ⟨rfl, -, -⟩ := hs
        exact Hist.crossing (domainKept _) hbls hq hspe D hCn (hinv : GInv D.postB).2.2.2.2.2.1 hvb hbb
      | gloas D =>
        simp only [GJointRunStep.postState, GJointState.gloas.injEq] at hs
        obtain ⟨rfl, -, -⟩ := hs
        obtain ⟨bid, hbid⟩ := ih1 D.preB D.preExec D.preParent hC.symm
        exact Hist.step (domainKept _) hbls hq hspe hdelay D hCn (hbid.append _) hpre
          (hinv : GInv D.postB).2.2.2.2.2.1 hbb
    rw [GJointRun.steps_snoc]
    refine ⟨hinv, fun b ex pa hs => by
      rw [List.length_append, List.length_singleton]; exact hend b ex pa hs, fun i b ex pa hi => ?_⟩
    rw [GJointRun.states_snoc] at hi
    by_cases hlt : i < run.states.length
    · rw [List.getElem?_append_left hlt] at hi
      obtain ⟨bid, hbid⟩ := ih2 i b ex pa hi
      exact ⟨bid, hbid.append _⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt), List.getElem?_singleton] at hi
      split at hi
      · have hil : i = run.steps.length + 1 := by have := run.states_length; omega
        subst hil
        exact hend b ex pa (Option.some.inj hi)
      · cases hi

/-! ## Block slots from the crossing on -/

section Slots

variable {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf)

/-- The block of a step with a Gloas block is processed at its own slot, which is the post-state's. -/
theorem gblock_post {C : GJointRunStep (P := P) cfg ccfg bls} {blk : Gloas.SignedBeaconBlock P}
    (hb : C.block = .gloas blk) :
    ∃ m pb ex pa, C.postState = .gloas pb ex pa ∧ pb.slot = blk.message.slot ∧
      Gloas.processBlock (gloasCtx ccfg bls) m blk.message = .ok pb := by
  cases C with
  | pre D => cases hb
  | crossing D =>
    simp only [GJointRunStep.block, GBlock.gloas.injEq] at hb
    subst hb
    have hp : Gloas.processBlock (gloasCtx ccfg bls) D.postSlots D.block.message = .ok D.postB :=
      applySignedBlockWith_ok D.transition
    refine ⟨D.postSlots, D.postB, D.exec, D.postParent, rfl, ?_, hp⟩
    rw [(processBlock_slots hp).1]
    have hs := D.slots
    unfold crossingSlots at hs
    split at hs
    · rename_i heq
      rw [← Except.ok.inj hs]
      exact (U64.beq_eq_true_iff.mp heq).symm
    · exact processSlots_slot_eq hs
  | gloas D =>
    simp only [GJointRunStep.block, GBlock.gloas.injEq] at hb
    subst hb
    exact ⟨D.postSlots, D.postB, D.postExec, D.postParent, rfl, D.postB_slot.1, D.processBlock⟩

/-- The step after a step with a Gloas block is a Gloas step, at a later slot. -/
theorem gblock_succ {a : Nat} {A C : GJointRunStep (P := P) cfg ccfg bls} {blk : Gloas.SignedBeaconBlock P}
    (hA : run.steps[a]? = some A) (hb : A.block = .gloas blk) (hC : run.steps[a + 1]? = some C) :
    ∃ D, C = .gloas D ∧ blk.message.slot.toNat < D.block.message.slot.toNat := by
  obtain ⟨m, pb, ex, pa, hpost, hslot, -⟩ := gblock_post hb
  have h := GJointRun.pre_succ run hA hC
  rw [hpost] at h
  cases C with
  | pre C => simp only [GJointRunStep.preState, reduceCtorEq] at h
  | crossing C => simp only [GJointRunStep.preState, reduceCtorEq] at h
  | gloas D =>
    simp only [GJointRunStep.preState, GJointState.gloas.injEq] at h
    refine ⟨D, rfl, ?_⟩
    have := D.pre_lt
    rw [h.1, hslot] at this
    exact this

/-- **Block slots strictly increase from the first Gloas block on.** -/
theorem gblock_slot_lt {a b : Nat} {A B : GJointRunStep (P := P) cfg ccfg bls}
    {blkA blkB : Gloas.SignedBeaconBlock P} (hA : run.steps[a]? = some A) (hbA : A.block = .gloas blkA)
    (hB : run.steps[b]? = some B) (hbB : B.block = .gloas blkB) (hab : a < b) :
    blkA.message.slot.toNat < blkB.message.slot.toNat := by
  obtain ⟨C, hC⟩ : ∃ C, run.steps[a + 1]? = some C :=
    ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp hB).1; omega)⟩
  obtain ⟨D, rfl, hlt⟩ := gblock_succ run hA hbA hC
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hab) with rfl | hlt'
  · rw [hC] at hB
    cases hB
    simp only [GJointRunStep.block, GBlock.gloas.injEq] at hbB
    subst hbB
    exact hlt
  · obtain ⟨D', hD'⟩ := gloas_from run hC (b - (a + 1)) (by
      have := (List.getElem?_eq_some_iff.mp hB).1; omega)
    rw [show a + 1 + (b - (a + 1)) = b by omega, hB] at hD'
    cases hD'
    simp only [GJointRunStep.block, GBlock.gloas.injEq] at hbB
    subst hbB
    have := slot_lt' run hC hB hlt'
    omega

/-- **Two signed bids of the run with one slot are one signed bid.** A Gloas block's bid is of the block's slot
(`block_newBid`) and block slots strictly increase from the first Gloas block on (`gblock_slot_lt`), so both
are the bid of one step's block. -/
theorem stepBid_slot_inj (hbls : bls = true) {n n' : Nat} {β β' : Gloas.SignedExecutionPayloadBid}
    (h : StepBid run.steps n β) (h' : StepBid run.steps n' β') (hs : β.message.slot = β'.message.slot) :
    β = β' := by
  subst hbls
  obtain ⟨j, -, C, blk, hC, hblk, rfl⟩ := h
  obtain ⟨j', -, C', blk', hC', hblk', rfl⟩ := h'
  obtain ⟨m, pb, -, -, -, -, hp⟩ := gblock_post hblk
  obtain ⟨m', pb', -, -, -, -, hp'⟩ := gblock_post hblk'
  have heq : blk.message.slot.toNat = blk'.message.slot.toNat := by
    rw [← (block_newBid (domainKept _) rfl hp).2.1, ← (block_newBid (domainKept _) rfl hp').2.1, hs]
  have hjj : j = j' := by
    rcases Nat.lt_trichotomy j j' with h | h | h
    · have := gblock_slot_lt run hC hblk hC' hblk' h
      omega
    · exact h
    · have := gblock_slot_lt run hC' hblk' hC hblk h
      omega
  subst hjj
  rw [hC] at hC'
  cases hC'
  rw [hblk] at hblk'
  cases hblk'
  rfl

end Slots

/-! ## Over a valid joint chain from a Fulu anchor -/

namespace ValidJointG

variable {checkpoint : BlockChain} {final : GJointState P} {s₀ : JointState P}

/-- **C4: every Gloas state reached from a Fulu anchor has the anchor witness, built from its history.** On a
valid joint chain from a pre-Gloas anchor (`bls = true`: the bid signature check is real), at every Gloas
state `b` of the run (`run.states[i]`) there is a `GloasBidWitness b` (the G3-14 data `ValidJointG` asks of a
Gloas anchor, injectivity included) such that

* every witness bid is the signed bid of the block of a step before `i` (`StepBid`: the crossing's first
  Gloas block or a Gloas step's);
* a payment reference's bid is the one whose payment is live at that window index;
* a queue reference's bid is the one whose payment a step before `i` appended (`StepPush`, an element of that
  step's `pushes`), with the bid's slot and withdrawal, as the queue entry at that position;
* the latest reference's bid is the latest bid.

This gives the witness the Gloas-anchor theorems ask for; it does not re-anchor the chain at `b` (no theorem
builds the `ValidJointG` from state `i`), so it is not composed with `anchor_witness_charged_once_queued`. -/
theorem reach_witness
    (v : ValidJointG cfg ccfg true checkpoint (.pre s₀) final) {i : Nat} {b : Gloas.BeaconState P}
    {ex : BlockChain} {pa : ParentPayload P} (hi : v.run.states[i]? = some (.gloas b ex pa)) :
    ∃ W : GloasBidWitness b,
      (∀ r β, W.bid r = some β → StepBid v.run.steps i β) ∧
      (∀ k β, W.bid (.payment k) = some β →
        payIdx (β.message.slot.toNat + P.SLOTS_PER_EPOCH) b = some k ∧
          LiveAt (β.message.slot.toNat + P.SLOTS_PER_EPOCH) (bidWithdrawal β.message) b) ∧
      (∀ k β, W.bid (.withdrawal k) = some β → ∃ e, StepPush v.run.steps i e ∧
        e.slot = β.message.slot.toNat + P.SLOTS_PER_EPOCH ∧ e.w = bidWithdrawal β.message ∧
        b.builder_pending_withdrawals.toArray[k]? = some e.w) ∧
      (∀ β, W.bid .latest = some β → β.message = b.latest_execution_payload_bid) := by
  obtain ⟨bid, hb⟩ := (reach_hist rfl v.quorumPositive v.inclusionDelay v.slotsPerEpoch v.exitDelayPos v.run
    v.validatorsBound v.buildersBound).2.2 i b ex pa hi
  refine ⟨hb.toWitness (by have := v.slotsPerEpoch; omega), fun r β h => (hb.signed r β h).2,
    fun k β h => ⟨(hb.payOnly k β h).1, (hb.payOnly k β h).2.1⟩, fun k β h => ?_, hb.latOnly⟩
  obtain ⟨-, -, -, e, he, hs, hw, hq⟩ := hb.wdOnly k β h
  exact ⟨e, he, hs, hw, by rw [← Array.getElem?_toList]; exact hq⟩

/-- **Every append of a real chain is the payment of a bid of the chain.** On a valid joint chain from a Fulu
anchor, each element a step appends to `builder_pending_withdrawals` (`e ∈ C.pushes`, by any of the three
paths) is the payment of the signed bid of an earlier step's block: the bid pays, the append is attributed to
that bid's slot, and the appended element is that bid's withdrawal. The bid is verified under real BLS at the
appending step's pre-state. -/
theorem push_is_step_bid
    (v : ValidJointG cfg ccfg true checkpoint (.pre s₀) final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg true} (hD : v.run.steps[j]? = some (.gloas D)) {e : Push}
    (he : e ∈ D.pushes) :
    ∃ β, StepBid v.run.steps j β ∧ BidSigned D.preB β ∧ U64.zero < β.message.value ∧
      e.slot = β.message.slot.toNat + P.SLOTS_PER_EPOCH ∧ e.w = bidWithdrawal β.message := by
  obtain ⟨bid, hb⟩ := (reach_hist rfl v.quorumPositive v.inclusionDelay v.slotsPerEpoch v.exitDelayPos v.run
    v.validatorsBound v.buildersBound).2.2 j D.preB D.preExec D.preParent (v.run.states_pre hD)
  obtain ⟨-, -, -, -, -, -, g8, hA, -⟩ := v.gInv_pre hD
  have hbb : D.preB.builders.toArray.size ≤ 2 ^ 40 :=
    v.buildersBound _ (List.mem_of_getElem? (v.run.states_pre hD))
  obtain ⟨r, β, hr, -, hs, hw, hv, -⟩ :=
    hb.push_bid v.quorumPositive (by have := v.slotsPerEpoch; omega) D g8 hA hbb he
  exact ⟨β, (hb.signed r β hr).2, (hb.signed r β hr).1, hv, hs, hw⟩

/-- **An append at the first Gloas block's bid's slot is that bid's withdrawal.** With
`crossing_bid_appended_at_most_once`: the crossing's bid is appended at most once, and what is appended is its
own withdrawal. -/
theorem crossing_bid_append_is_bid
    (v : ValidJointG cfg ccfg true checkpoint (.pre s₀) final) {j : Nat}
    {C : CrossingData (P := P) cfg ccfg true} (stepC : v.run.steps[j]? = some (.crossing C)) :
    ∀ e ∈ v.run.pushes, e.slot = C.block.message.slot.toNat + P.SLOTS_PER_EPOCH →
      e.w = bidWithdrawal C.block.message.body.signed_execution_payload_bid.message := by
  intro e he hslot
  obtain ⟨C', hC', heC⟩ := List.mem_flatMap.mp he
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hC'
  cases C' with
  | pre _ => cases heC
  | crossing _ => cases heC
  | gloas D =>
    obtain ⟨β, ⟨j', -, C'', blk, hC'', hblk, rfl⟩, -, -, hs, hw⟩ := v.push_is_step_bid hi heC
    obtain ⟨m, pb, -, -, -, -, hp⟩ := gblock_post hblk
    have hbs := (block_newBid (domainKept _) rfl hp).2.1
    have heq : blk.message.slot.toNat = C.block.message.slot.toNat := by
      rw [hs, hbs] at hslot
      omega
    have hjj : j' = j := by
      rcases Nat.lt_trichotomy j' j with h | h | h
      · have := gblock_slot_lt v.run hC'' hblk stepC rfl h
        omega
      · exact h
      · have := gblock_slot_lt v.run stepC rfl hC'' hblk h
        omega
    subst hjj
    rw [stepC] at hC''
    cases hC''
    simp only [GJointRunStep.block, GBlock.gloas.injEq] at hblk
    subst hblk
    exact hw

/-- **A witness of the chain's own bids separates messages.** At a Gloas state of a valid joint chain from a
Fulu anchor, a bid witness whose every bid is the signed bid of an earlier step's block (`StepBid`, the first
clause of `reach_witness`) has `WitnessMessagesInjective`: two witness bids with one message are one signed bid,
because one message is one slot and one slot is one step's block (`stepBid_slot_inj`). -/
theorem witnessMessagesInjective_of_stepBid
    (v : ValidJointG cfg ccfg true checkpoint (.pre s₀) final) {i : Nat} {b : Gloas.BeaconState P}
    (W : GloasBidWitness b) (hW : ∀ r β, W.bid r = some β → StepBid v.run.steps i β) :
    WitnessMessagesInjective W :=
  fun r r' β β' hr hr' hm => stepBid_slot_inj v.run rfl (hW r β hr) (hW r' β' hr') (by rw [hm])

/-- **C4 with one message, one signed bid.** `reach_witness`, with the witness also `WitnessMessagesInjective`:
at every Gloas state reached from a Fulu anchor the witness is the chain's own bids, and two of them with one
message are one signed bid. So on a real chain `anchor_message_charged_once`'s premise holds of this witness,
with no assumption on BLS signatures. -/
theorem reach_witness_message
    (v : ValidJointG cfg ccfg true checkpoint (.pre s₀) final) {i : Nat} {b : Gloas.BeaconState P}
    {ex : BlockChain} {pa : ParentPayload P} (hi : v.run.states[i]? = some (.gloas b ex pa)) :
    ∃ W : GloasBidWitness b,
      (∀ r β, W.bid r = some β → StepBid v.run.steps i β) ∧
      (∀ k β, W.bid (.payment k) = some β →
        payIdx (β.message.slot.toNat + P.SLOTS_PER_EPOCH) b = some k ∧
          LiveAt (β.message.slot.toNat + P.SLOTS_PER_EPOCH) (bidWithdrawal β.message) b) ∧
      (∀ k β, W.bid (.withdrawal k) = some β → ∃ e, StepPush v.run.steps i e ∧
        e.slot = β.message.slot.toNat + P.SLOTS_PER_EPOCH ∧ e.w = bidWithdrawal β.message ∧
        b.builder_pending_withdrawals.toArray[k]? = some e.w) ∧
      (∀ β, W.bid .latest = some β → β.message = b.latest_execution_payload_bid) ∧
      WitnessMessagesInjective W := by
  obtain ⟨W, h1, h2, h3, h4⟩ := v.reach_witness hi
  exact ⟨W, h1, h2, h3, h4, v.witnessMessagesInjective_of_stepBid W h1⟩

end ValidJointG

end Blanc.Lift.BuilderRequest
