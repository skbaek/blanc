import Blanc.Composition.BuilderRequestJointGPaymentsAnchor

/-!
# B5(iii): the appending destinations append the withdrawal

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B5 (iii)): `quorum`,
`settled` and `directAppend` each say "and `payment.withdrawal` is appended to `builder_pending_withdrawals`".
`PaymentFate.holds` and `AnchorFate.holds` state those destinations by the step's guard; the theorems here are their
append conclusions, at the step `j'` the destination names, for the run half and the anchor half.

* **quorum** (`ValidJointG.payment_quorum_appends`, `ValidJointG.anchor_payment_quorum_appends`,
  `ValidJointG.anchor_latest_quorum_appends`): at the evaluating rotation inside step `j'`'s `process_slots`
  (`RotEval`, with the same `QEv` verdict), `process_builder_pending_payments` at the pre-rotation state `a` returns
  `b` whose `builder_pending_withdrawals` is `a`'s followed by the withdrawals of the first-half entries with weight at
  least the quorum (CL:1724-1726), and the tracked withdrawal is among them (`PendingAppend`).
* **settled** (`ValidJointG.payment_settled_appends`, `ValidJointG.anchor_settled_appends`): at step `j'`'s
  post-slots state, `settle_builder_payment` at the parent's window index pushes exactly the withdrawal, and the whole
  parent settlement (`process_parent_execution_payload`) ends with `builder_pending_withdrawals` equal to the
  post-slots state's with exactly that withdrawal pushed.
* **directAppend** (`ValidJointG.payment_directAppend_appends`, `ValidJointG.anchor_directAppend_appends`): the
  old-parent branch of step `j'`'s parent settlement pushes exactly the withdrawal; the parent settlement ends with the
  post-slots state's `builder_pending_withdrawals` with that one entry pushed.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## `process_builder_pending_payments` -/

/-- The withdrawals `process_builder_pending_payments` appends at state `a` with quorum `q`: those of the first-half
payment entries with weight at least `q`, in order (CL:1724-1726). -/
def quorumWithdrawals (q : U64) (a : Gloas.BeaconState P) : List Gloas.BuilderPendingWithdrawal :=
  ((a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList.filter
    (fun p => decide (q ≤ p.weight))).map (·.withdrawal)

/-- **`process_builder_pending_payments` at `a` appends `w`**: it returns `b` whose builder withdrawals are `a`'s
followed by `quorumWithdrawals q a` (`q`: `a`'s quorum), and `w` is one of them. -/
def PendingAppend (c : Config) (w : Gloas.BuilderPendingWithdrawal) (a : Gloas.BeaconState P) : Prop :=
  ∃ b q, Gloas.processBuilderPendingPayments c a = .ok b ∧ Gloas.getBuilderPaymentQuorumThreshold a = .ok q ∧
    b.builder_pending_withdrawals.toArray.toList =
      a.builder_pending_withdrawals.toArray.toList ++ quorumWithdrawals q a ∧
    w ∈ quorumWithdrawals q a

/-- **The evaluating rotation appends the payment.** Along a successful slot loop, the rotation that evaluates the
payment of slot `s` with the quorum reached runs `process_builder_pending_payments`, which appends `w`. -/
theorem rotEval_pendingAppend (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {s : Nat}
    {w : Gloas.BuilderPendingWithdrawal} :
    ∀ (n : Nat) (st st' : Gloas.BeaconState P), RotEval ctx (QEv s w true) n st → slotLoop ctx n st = .ok st' →
      RotEval ctx (fun x a => QEv s w true x a ∧ PendingAppend ctx.cfg w a) n st
  | 0, _, _, h, _ => h.elim
  | n + 1, st, st', h, hl => by
    obtain ⟨x, hx, hl⟩ := bind_eq_ok_iff.mp hl
    rcases h with he | ⟨x', hx', h⟩
    · refine Or.inl ?_
      obtain ⟨st1, next, a, h1, hn, h0, ha, hq⟩ := he
      obtain ⟨st1', next', h1', hn', f1, -, hc⟩ := slotTick_cases hx
      rw [h1] at h1'; cases h1'
      rw [hn] at hn'; cases hn'
      rcases hc with ⟨hne, -⟩ | ⟨-, a', b, st2, ha', hb, -, -⟩
      · exact absurd h0 hne
      rw [ha] at ha'; cases ha'
      obtain ⟨-, q', hq', hbw, -⟩ := processBuilderPendingPayments_frame hb
      refine ⟨st1, next, a, h1, hn, h0, ha, hq, b, q', hb, hq', hbw, ?_⟩
      obtain ⟨e, p, q, hp, ⟨-, hpw⟩, hqa, hd⟩ := hq
      rw [hqa] at hq'; cases hq'
      have fa := epochPrefix_invFrame ha
      have hpay : a.builder_pending_payments = st.builder_pending_payments := by rw [fa.2.1, f1.2.1]
      have hk : payIdx s st = some (s % P.SLOTS_PER_EPOCH) := by
        unfold payIdx; rw [ite_eq_right (by omega), ite_eq_left e]
      have hk' : st.builder_pending_payments.toArray[s % P.SLOTS_PER_EPOCH]? = some p := by
        simpa only [cell, hk, Option.bind_some] using hp
      have hlt : s % P.SLOTS_PER_EPOCH < P.SLOTS_PER_EPOCH := Nat.mod_lt _ hspe
      have hex : (a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH)[s % P.SLOTS_PER_EPOCH]? =
          some p := by
        rw [Array.getElem?_extract, ite_eq_left ?_, Nat.zero_add, hpay, hk']
        have := (Array.getElem?_eq_some_iff.mp hk').1
        rw [hpay]; omega
      unfold quorumWithdrawals
      rw [← hpw]
      refine List.mem_map_of_mem (List.mem_filter.mpr ⟨?_, hd⟩)
      exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hex)
    · rw [hx] at hx'; cases hx'
      exact Or.inr ⟨x, hx, rotEval_pendingAppend hspe n x st' h hl⟩

/-- **A step's quorum rotation appends the payment** (`process_builder_pending_payments` inside its
`process_slots`). -/
theorem _root_.Blanc.GloasStepData.rotQ_appends (D : GloasStepData (P := P) cfg ccfg bls)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s : Nat}
    {w : Gloas.BuilderPendingWithdrawal} (h : D.RotQ s w true) :
    RotEval (gloasCtx ccfg bls) (fun x a => QEv s w true x a ∧ PendingAppend ccfg w a)
      (D.block.message.slot.toNat - D.preB.slot.toNat) D.preB :=
  rotEval_pendingAppend hspe _ _ _ h (processSlots_slotLoop D.slots).2

/-! ## The parent settlement -/

theorem builderLoops_bpw {ctx : Ctx} {a d e : Gloas.BeaconState P} {r : Gloas.ExecutionRequests}
    (hd : forIn r.builder_deposits.toArray.toList a
      (fun op s => do let s' ← Gloas.processBuilderDepositRequest ctx s op; pure (ForInStep.yield s')) = .ok d)
    (he : forIn r.builder_exits.toArray.toList d
      (fun op s => do let s' ← Gloas.processBuilderExitRequest ctx.cfg s op; pure (ForInStep.yield s')) = .ok e) :
    e.builder_pending_withdrawals = a.builder_pending_withdrawals := by
  have h1 := forIn_yield_inv (fun m => m.builder_pending_withdrawals = a.builder_pending_withdrawals) _
    (fun m _ m' hI hm => by
      show _ = _
      rw [(processBuilderDepositRequest_frame hm).2.2.2.2.1]; exact hI) _ _ _ hd rfl
  exact forIn_yield_inv (fun m => m.builder_pending_withdrawals = a.builder_pending_withdrawals) _
    (fun m _ m' hI hm => by
      show _ = _
      rw [(processBuilderExitRequest_frame hm).2.2.2.2.1]; exact hI) _ _ _ he h1

/-- **The FULL settlement of a live parent entry appends its withdrawal.** When the parent settles FULL and the
entry at the parent slot's window index is live with withdrawal `w` of positive amount, `settle_builder_payment` at
that index pushes exactly `w`, and the parent settlement ends with exactly `w` pushed. -/
theorem parent_settled_appends (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {m s1 : Gloas.BeaconState P}
    {blk : Gloas.BeaconBlock P} {w : Gloas.BuilderPendingWithdrawal}
    (h : Gloas.processParentExecutionPayload ctx m blk = .ok s1) (hfull : parentFull m blk = true)
    (hl : LiveAt (m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) w m) (hpos : U64.zero < w.amount) :
    (∃ (idx : U64) (x : Gloas.BeaconState P),
      payIdx (m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) m = some idx.toNat ∧
      Gloas.settleBuilderPayment m idx = .ok x ∧
      x.builder_pending_withdrawals = m.builder_pending_withdrawals.push w) ∧
    s1.builder_pending_withdrawals = m.builder_pending_withdrawals.push w := by
  rcases processParentExecutionPayload_cases h with ⟨_, hne⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact absurd (by simpa only [parentFull, beq_iff_eq] using hfull) hne
  obtain ⟨x, fx, hc⟩ := applyParentPrefix_idx hspe ha
  obtain ⟨p, hp, hne, hpw⟩ := hl
  rcases hc with ⟨idx, hidx, hx⟩ | ⟨hnone, -⟩
  · obtain ⟨-, p', hp', hpush, -⟩ := settleBuilderPayment_frame hx
    have hp'' : m.builder_pending_payments.toArray[idx.toNat]? = some p := by
      simpa only [cell, hidx, Option.bind_some] using hp
    rw [hp''] at hp'; cases hp'
    have hxw : x.builder_pending_withdrawals = m.builder_pending_withdrawals.push w := by
      rw [hpush (hpw ▸ hpos), hpw]
    refine ⟨⟨idx, x, hidx, hx, hxw⟩, ?_⟩
    rw [(applyParentSuffix_post hs).2.2.1, builderLoops_bpw hd he, fx.2.2.1, hxw]
  · simp only [cell, hnone, Option.bind_none, reduceCtorEq] at hp

/-- **The old-parent branch appends the parent bid's withdrawal.** When the parent settles FULL with its slot out of
the window and its bid pays, the parent settlement ends with exactly `bidWithdrawal L` pushed. -/
theorem parent_direct_appends (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {m s1 : Gloas.BeaconState P}
    {blk : Gloas.BeaconBlock P}
    (h : Gloas.processParentExecutionPayload ctx m blk = .ok s1) (hfull : parentFull m blk = true)
    (hnone : payIdx (m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) m = none)
    (hv : U64.zero < m.latest_execution_payload_bid.value) :
    s1.builder_pending_withdrawals =
      m.builder_pending_withdrawals.push (bidWithdrawal m.latest_execution_payload_bid) := by
  rcases processParentExecutionPayload_cases h with ⟨_, hne⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact absurd (by simpa only [parentFull, beq_iff_eq] using hfull) hne
  obtain ⟨x, fx, hc⟩ := applyParentPrefix_idx hspe ha
  rcases hc with ⟨idx, hidx, -⟩ | ⟨-, ⟨-, rfl⟩ | ⟨hv0, -⟩⟩
  · rw [hnone] at hidx; cases hidx
  · rw [(applyParentSuffix_post hs).2.2.1, builderLoops_bpw hd he, fx.2.2.1]; rfl
  · exact absurd hv hv0

/-- `process_slots` keeps the latest bid. -/
theorem _root_.Blanc.GloasStepData.postSlots_bid (D : GloasStepData (P := P) cfg ccfg bls) :
    D.postSlots.latest_execution_payload_bid = D.preB.latest_execution_payload_bid :=
  processSlots_ind (ctx := gloasCtx ccfg bls)
    (fun m => m.latest_execution_payload_bid = D.preB.latest_execution_payload_bid)
    (fun _ _ _ _ hI f1 _ hc => (slotIter_core f1 hc).2.1.trans hI) D.slots rfl

/-! ## The run half -/

theorem PaymentFate.holds_at {s₀ sf : GJointState P} {run : GJointRun cfg ccfg bls s₀ sf} {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : run.steps[j]? = some (.gloas D)) {f : PaymentFate run j}
    (h : f.holds) : f.holdsFor D := by
  obtain ⟨D', hD', hf⟩ := h
  rw [stepD] at hD'; cases hD'; exact hf

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- **B5(iii), `quorum` appends** (run half). When step `j`'s payment has destination `quorum j'`, the evaluating
rotation inside step `j'`'s `process_slots` (the one with the `QEv` verdict) runs `process_builder_pending_payments`,
which appends the bid's withdrawal `D.payW` to `builder_pending_withdrawals` (`PendingAppend`). -/
theorem payment_quorum_appends (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j j' : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    (h : (PaymentFate.quorum j' : PaymentFate v.run j).holds) :
    j < j' ∧ ∃ D', v.run.steps[j']? = some (.gloas D') ∧
      RotEval (gloasCtx ccfg bls) (fun x a => QEv D.paySlot D.payW true x a ∧ PendingAppend ccfg D.payW a)
        (D'.block.message.slot.toNat - D'.preB.slot.toNat) D'.preB := by
  obtain ⟨hjj, D', hD', hr⟩ := PaymentFate.holds_at stepD h
  exact ⟨hjj, D', hD', D'.rotQ_appends (by have := v.slotsPerEpoch; omega) hr⟩

/-- **B5(iii), `settled` appends** (run half). When step `j`'s payment (positive value) has destination
`settled j'`, at step `j'`'s post-slots state `settle_builder_payment` at the payment's window index pushes exactly
`D.payW`, and `process_parent_execution_payload` ends with exactly `D.payW` pushed onto
`builder_pending_withdrawals`. -/
theorem payment_settled_appends (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j j' : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    (bid : U64.zero < D.bid.value) (h : (PaymentFate.settled j' : PaymentFate v.run j).holds) :
    j' = j + 1 ∧ ∃ (D' : GloasStepData (P := P) cfg ccfg bls) (s1 : Gloas.BeaconState P),
      v.run.steps[j']? = some (.gloas D') ∧
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D'.postSlots D'.block.message = .ok s1 ∧
      (∃ (idx : U64) (x : Gloas.BeaconState P), payIdx D.paySlot D'.postSlots = some idx.toNat ∧
        Gloas.settleBuilderPayment D'.postSlots idx = .ok x ∧
        x.builder_pending_withdrawals = D'.postSlots.builder_pending_withdrawals.push D.payW) ∧
      s1.builder_pending_withdrawals = D'.postSlots.builder_pending_withdrawals.push D.payW := by
  have hspe : 0 < P.SLOTS_PER_EPOCH := by have := v.slotsPerEpoch; omega
  obtain ⟨rfl, D', hD', hfull, hl⟩ := PaymentFate.holds_at stepD h
  obtain ⟨C, hC, hpre⟩ := pred_step stepD hD' (by omega)
  rw [show j + 1 - 1 = j by omega, stepD] at hC; cases hC
  have hps : D.paySlot = D'.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH := by
    rw [D'.postSlots_lbh, hpre, D.postB_slot.2, paySlot_eq]
  obtain ⟨s1, -, -, -, -, -, -, h1, -⟩ := processBlock_phases D'.processBlock
  rw [hps] at hl ⊢
  obtain ⟨hx, hs1⟩ := parent_settled_appends hspe h1 hfull hl bid
  exact ⟨rfl, D', s1, hD', h1, hx, hs1⟩

/-- **B5(iii), `directAppend` appends** (run half). When step `j`'s payment (positive value) has destination
`directAppend j'`, step `j'`'s post-slots state still carries `D.bid` as its latest bid, and its
`process_parent_execution_payload` (the old-parent branch) ends with exactly `D.payW` pushed onto
`builder_pending_withdrawals`. -/
theorem payment_directAppend_appends (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j j' : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    (bid : U64.zero < D.bid.value) (h : (PaymentFate.directAppend j' : PaymentFate v.run j).holds) :
    j' = j + 1 ∧ ∃ (D' : GloasStepData (P := P) cfg ccfg bls) (s1 : Gloas.BeaconState P),
      v.run.steps[j']? = some (.gloas D') ∧ D'.postSlots.latest_execution_payload_bid = D.bid ∧
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D'.postSlots D'.block.message = .ok s1 ∧
      s1.builder_pending_withdrawals = D'.postSlots.builder_pending_withdrawals.push D.payW := by
  have hspe : 0 < P.SLOTS_PER_EPOCH := by have := v.slotsPerEpoch; omega
  obtain ⟨rfl, D', hD', hfull, hnone⟩ := PaymentFate.holds_at stepD h
  obtain ⟨C, hC, hpre⟩ := pred_step stepD hD' (by omega)
  rw [show j + 1 - 1 = j by omega, stepD] at hC; cases hC
  have hps : D.paySlot = D'.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH := by
    rw [D'.postSlots_lbh, hpre, D.postB_slot.2, paySlot_eq]
  have hL : D'.postSlots.latest_execution_payload_bid = D.bid := by
    rw [D'.postSlots_bid, hpre, D.postB_bid]
  obtain ⟨s1, -, -, -, -, -, -, h1, -⟩ := processBlock_phases D'.processBlock
  rw [hps] at hnone
  have hs1 := parent_direct_appends hspe h1 hfull hnone (by rw [hL]; exact bid)
  rw [hL] at hs1
  exact ⟨rfl, D', s1, hD', hL, h1, hs1⟩

end ValidJointG

/-! ## The anchor half -/

section Anchor

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {checkpoint : BlockChain}
  {final : GJointState P}

/-- **B5(iii), `quorum` appends** (anchor half, a payments entry). When the anchor's payments entry at `idx` has
destination `quorum j'`, the evaluating rotation inside step `j'`'s `process_slots` runs
`process_builder_pending_payments`, which appends the entry's withdrawal. -/
theorem ValidJointG.anchor_payment_quorum_appends
    (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final) {idx j' : Nat}
    (h : (AnchorFate.quorum j' : AnchorFate v.run (.payment idx)).holds) :
    ∃ (p : Gloas.BuilderPendingPayment) (B : GloasStepData (P := P) cfg ccfg bls),
      a.builder_pending_payments.toArray[idx]? = some p ∧ v.run.steps[j']? = some (.gloas B) ∧
      RotEval (gloasCtx ccfg bls)
        (fun x a' => QEv (anchorVs a idx) p.withdrawal true x a' ∧ PendingAppend ccfg p.withdrawal a')
        (B.block.message.slot.toNat - B.preB.slot.toNat) B.preB := by
  obtain ⟨p, hp, B, hB, hr⟩ := h
  exact ⟨p, B, hp, hB, B.rotQ_appends (by have := v.slotsPerEpoch; omega) hr⟩

/-- **B5(iii), `quorum` appends** (anchor half, the latest bid). When the anchor's latest bid has destination
`quorum j'`, it pays, and the evaluating rotation inside step `j'`'s `process_slots` runs
`process_builder_pending_payments`, which appends its withdrawal. -/
theorem ValidJointG.anchor_latest_quorum_appends
    (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final) {j' : Nat}
    (h : (AnchorFate.quorum j' : AnchorFate v.run .latestBid).holds) :
    LatestPays a ∧ ∃ B : GloasStepData (P := P) cfg ccfg bls, v.run.steps[j']? = some (.gloas B) ∧
      RotEval (gloasCtx ccfg bls)
        (fun x a' => QEv (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)
            (bidWithdrawal a.latest_execution_payload_bid) true x a' ∧
          PendingAppend ccfg (bidWithdrawal a.latest_execution_payload_bid) a')
        (B.block.message.slot.toNat - B.preB.slot.toNat) B.preB := by
  rcases h with ⟨hpay, B, hB, hr⟩ | ⟨-, hn⟩
  · exact ⟨hpay, B, hB, B.rotQ_appends (by have := v.slotsPerEpoch; omega) hr⟩
  · cases hn

theorem ValidJointG.anchor_first_pre (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final)
    {B : GloasStepData (P := P) cfg ccfg bls} (hB : v.run.steps[0]? = some (.gloas B)) :
    B.preB = a ∧ a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH =
      B.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH := by
  have hinv : GAnchorInv (GJointState.gloas a ex pa) := v.anchorInv
  obtain ⟨-, -, -, -, -, -, g8, -, -, -⟩ := hinv
  have hpre : B.preB = a := by
    obtain ⟨B', hBB, hp⟩ := first_gloas hB
    cases hBB; exact hp
  refine ⟨hpre, ?_⟩
  rw [B.postSlots_lbh, hpre, g8.1]

/-- **B5(iii), `settled` appends** (anchor half). When the anchor's latest bid has destination `settled j'`, then
`j' = 0`, and at the first step's post-slots state `settle_builder_payment` at the bid's window index pushes exactly
the bid's withdrawal, and `process_parent_execution_payload` ends with exactly that withdrawal pushed onto
`builder_pending_withdrawals`. -/
theorem ValidJointG.anchor_settled_appends
    (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final) {j' : Nat}
    (h : (AnchorFate.settled j' : AnchorFate v.run .latestBid).holds) :
    j' = 0 ∧ ∃ (B : GloasStepData (P := P) cfg ccfg bls) (s1 : Gloas.BeaconState P),
      v.run.steps[0]? = some (.gloas B) ∧ B.preB = a ∧
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) B.postSlots B.block.message = .ok s1 ∧
      (∃ (idx : U64) (x : Gloas.BeaconState P),
        payIdx (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH) B.postSlots = some idx.toNat ∧
        Gloas.settleBuilderPayment B.postSlots idx = .ok x ∧
        x.builder_pending_withdrawals =
          B.postSlots.builder_pending_withdrawals.push (bidWithdrawal a.latest_execution_payload_bid)) ∧
      s1.builder_pending_withdrawals =
        B.postSlots.builder_pending_withdrawals.push (bidWithdrawal a.latest_execution_payload_bid) := by
  have hspe : 0 < P.SLOTS_PER_EPOCH := by have := v.slotsPerEpoch; omega
  rcases h with ⟨hpay, -, rfl, B, hB, hfull, hl⟩ | ⟨-, hn⟩
  · obtain ⟨hpre, hps⟩ := v.anchor_first_pre hB
    obtain ⟨s1, -, -, -, -, -, -, h1, -⟩ := processBlock_phases B.processBlock
    rw [hps] at hl ⊢
    obtain ⟨hx, hs1⟩ := parent_settled_appends hspe h1 hfull hl hpay.1
    exact ⟨rfl, B, s1, hB, hpre, h1, hx, hs1⟩
  · cases hn

/-- **B5(iii), `directAppend` appends** (anchor half). When the anchor's latest bid has destination
`directAppend j'`, then `j' = 0`, the first step's post-slots state still carries the anchor's latest bid, and its
`process_parent_execution_payload` (the old-parent branch) ends with exactly the bid's withdrawal pushed onto
`builder_pending_withdrawals`. -/
theorem ValidJointG.anchor_directAppend_appends
    (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final) {j' : Nat}
    (h : (AnchorFate.directAppend j' : AnchorFate v.run .latestBid).holds) :
    j' = 0 ∧ ∃ (B : GloasStepData (P := P) cfg ccfg bls) (s1 : Gloas.BeaconState P),
      v.run.steps[0]? = some (.gloas B) ∧ B.preB = a ∧
      B.postSlots.latest_execution_payload_bid = a.latest_execution_payload_bid ∧
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) B.postSlots B.block.message = .ok s1 ∧
      s1.builder_pending_withdrawals =
        B.postSlots.builder_pending_withdrawals.push (bidWithdrawal a.latest_execution_payload_bid) := by
  have hspe : 0 < P.SLOTS_PER_EPOCH := by have := v.slotsPerEpoch; omega
  rcases h with ⟨hpay, -, rfl, B, hB, hfull, hnone⟩ | ⟨-, hn⟩
  · obtain ⟨hpre, hps⟩ := v.anchor_first_pre hB
    have hL : B.postSlots.latest_execution_payload_bid = a.latest_execution_payload_bid := by
      rw [B.postSlots_bid, hpre]
    obtain ⟨s1, -, -, -, -, -, -, h1, -⟩ := processBlock_phases B.processBlock
    rw [hps] at hnone
    have hs1 := parent_direct_appends hspe h1 hfull hnone (by rw [hL]; exact hpay.1)
    rw [hL] at hs1
    exact ⟨rfl, B, s1, hB, hpre, hL, h1, hs1⟩
  · cases hn

end Anchor

end Blanc.Lift.BuilderRequest
