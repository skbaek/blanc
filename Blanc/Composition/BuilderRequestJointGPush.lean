import Blanc.Composition.BuilderRequestJointGAppends

/-!
# Every append to `builder_pending_withdrawals` at a Gloas step, with its path and its payment

Goal `eip8282-charge-once-v1`, outcome C1 (push exhaustiveness). `BuilderRequestJointGAppends` shows that each
appending destination of a payment appends its withdrawal. This module is the converse, about the list itself:
what a Gloas step appends to `builder_pending_withdrawals`, element by element.

* `Push`: one appended element, with the path that appended it (`PushPath`: the quorum rotation of
  `process_builder_pending_payments`, `settle_builder_payment`, or the old-parent direct append of
  `apply_parent_execution_payload`) and the virtual slot of the payment it is attributed to (the bid's slot plus
  one epoch, the slot `payIdx` tracks a payment by).
* `GloasStepData.pushes`: the appends of a step, in order, as a function of the step's states: those of each
  epoch rotation inside its `process_slots` (`loopPushes`: at each epoch boundary the first-half entries whose
  weight reaches the quorum, `rotPushes`), then that of its parent settlement (`parentPushes`: at most one).
* **`GloasStepData.pushes_exhaustive`**: the step's post-state queue is its pre-state queue followed by exactly
  the withdrawals of `D.pushes`, less the `d` entries its `process_withdrawals` removed from the front
  (`GloasStepData.Drops`). Nothing else is appended.
* **`GloasStepData.push_source`**: each element of `D.pushes` is appended by exactly the path it names, for the
  payment at its slot (`GloasStepData.PushSource`): the evaluating rotation found that payment's live entry at the
  quorum and `process_builder_pending_payments` appended it (`PendingAppend`); or the step settled its parent FULL
  with that payment's entry live (positive amount) and pushed exactly its withdrawal; or it settled its parent FULL
  with the parent's slot out of the window and pushed exactly the paying parent bid's withdrawal. The quorum case
  reads the positive quorum (`quorumPositive`): an empty entry has weight `0` and is not appended.
* `loopPushes_sorted`, `GloasStepData.push_slot_lt`: the rotation appends of a step are in strictly increasing
  slot order, and every append of a step is attributed to a slot before the step's own bid's.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## Pushes -/

/-- The three paths that append to `builder_pending_withdrawals`: the quorum rotation
(`process_builder_pending_payments`, CL:1724-1726), `settle_builder_payment` (CL:1538-1543), and the old-parent
direct append of `apply_parent_execution_payload` (CL:1805-1814). -/
inductive PushPath where
  | quorum
  | settled
  | direct
  deriving DecidableEq

/-- **One append to `builder_pending_withdrawals`**: the path that appended it, the virtual slot of the payment
it is attributed to (the bid's slot plus one epoch, as `payIdx` tracks it), and the appended element. -/
structure Push where
  path : PushPath
  slot : Nat
  w : Gloas.BuilderPendingWithdrawal

/-! ## The quorum rotation -/

/-- **The appends of `process_builder_pending_payments` at `a` with quorum `q`**: the first-half payment entries
with weight at least `q`, in order, each attributed to the virtual slot of its window index (the slot `s` of the
epoch about to end with `payIdx s a` that index). -/
def rotPushes (q : U64) (a : Gloas.BeaconState P) : List Push :=
  ((a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList.zipIdx.filter
    (fun x => decide (q ≤ x.1.weight))).map
    (fun x => ⟨.quorum, P.SLOTS_PER_EPOCH * curEpoch a + x.2, x.1.withdrawal⟩)

theorem zipIdx_filter_map_fst {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ (l : List α) (n : Nat),
      ((l.zipIdx n).filter (fun x => p x.1)).map (fun x => f x.1) = (l.filter p).map f
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.filter_cons, List.filter_cons]
    cases h : p a
    · simpa only [h, Bool.false_eq_true, ite_false] using zipIdx_filter_map_fst p f l (n + 1)
    · simp only [ite_true, List.map_cons, zipIdx_filter_map_fst p f l (n + 1)]

/-- The elements `rotPushes` appends are `quorumWithdrawals`. -/
theorem rotPushes_w (q : U64) (a : Gloas.BeaconState P) :
    (rotPushes q a).map (·.w) = quorumWithdrawals q a := by
  unfold rotPushes quorumWithdrawals
  rw [List.map_map]
  exact zipIdx_filter_map_fst (fun p : Gloas.BuilderPendingPayment => decide (q ≤ p.weight))
    (fun p : Gloas.BuilderPendingPayment => p.withdrawal) _ 0

theorem mem_rotPushes {q : U64} {a : Gloas.BeaconState P} {e : Push} (he : e ∈ rotPushes q a) :
    ∃ k p, k < P.SLOTS_PER_EPOCH ∧ a.builder_pending_payments.toArray[k]? = some p ∧ q ≤ p.weight ∧
      e = ⟨.quorum, P.SLOTS_PER_EPOCH * curEpoch a + k, p.withdrawal⟩ := by
  obtain ⟨⟨p, k⟩, hx, rfl⟩ := List.mem_map.mp he
  obtain ⟨hx, hd⟩ := List.mem_filter.mp hx
  have hk : (a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH)[k]? = some p := by
    rw [← Array.getElem?_toList]; exact List.mem_zipIdx_iff_getElem?.mp hx
  rw [Array.getElem?_extract] at hk
  split at hk
  · rename_i hlt
    rw [Nat.zero_add] at hk
    exact ⟨k, p, by omega, hk, of_decide_eq_true hd, rfl⟩
  · cases hk

/-- The rotation's appends are in strictly increasing slot order. -/
theorem rotPushes_sorted (q : U64) (a : Gloas.BeaconState P) :
    (rotPushes q a).Pairwise (fun x y => x.slot < y.slot) := by
  unfold rotPushes
  rw [List.pairwise_map]
  refine List.Pairwise.filter _ ?_
  have h : ((a.builder_pending_payments.toArray.extract 0 P.SLOTS_PER_EPOCH).toList.zipIdx.map
      Prod.snd).Pairwise (· < ·) := by
    rw [List.zipIdx_map_snd]; exact List.pairwise_lt_range'
  exact (List.pairwise_map.mp h).imp (fun h => Nat.add_lt_add_left h _)

/-! ## The slot loop -/

/-- **The appends of one iteration of the `process_slots` loop at `st`**: none unless the iteration crosses an
epoch boundary, where `process_epoch` runs `process_builder_pending_payments` at the pre-rotation state
(`epochPrefix` of the `process_slot` state), with that state's quorum. -/
def tickPushes (ctx : Ctx) (st : Gloas.BeaconState P) : List Push :=
  if (st.slot.toNat + 1) % P.SLOTS_PER_EPOCH = 0 then
    match Gloas.processSlot st with
    | .ok st1 =>
      match epochPrefix ctx st1 with
      | .ok a =>
        match Gloas.getBuilderPaymentQuorumThreshold a with
        | .ok q => rotPushes q a
        | .error _ => []
      | .error _ => []
    | .error _ => []
  else []

/-- **The appends of `n` iterations of the `process_slots` loop from `st`**, in order. -/
def loopPushes (ctx : Ctx) : Nat → Gloas.BeaconState P → List Push
  | 0, _ => []
  | n + 1, st => tickPushes ctx st ++
      match slotTick ctx st with
      | .ok st' => loopPushes ctx n st'
      | .error _ => []

theorem loopPushes_succ {ctx : Ctx} {n : Nat} {st st' : Gloas.BeaconState P}
    (h : slotTick ctx st = .ok st') :
    loopPushes ctx (n + 1) st = tickPushes ctx st ++ loopPushes ctx n st' := by
  simp only [loopPushes, h]

/-- One successful iteration: it appends nothing and keeps the queue, or it is an epoch rotation at the
pre-rotation state `a`, whose `process_builder_pending_payments` appends `rotPushes q a`. -/
theorem tick_cases {ctx : Ctx} {st st' : Gloas.BeaconState P} (h : slotTick ctx st = .ok st') :
    (tickPushes ctx st = [] ∧ st'.builder_pending_withdrawals = st.builder_pending_withdrawals) ∨
    ∃ st1 next a b q, Gloas.processSlot st = .ok st1 ∧
      st1.slot.add? U64.one "process_slots: state.slot + 1" = .ok next ∧
      next.toNat % P.SLOTS_PER_EPOCH = 0 ∧ epochPrefix ctx st1 = .ok a ∧
      Gloas.processBuilderPendingPayments ctx.cfg a = .ok b ∧
      Gloas.getBuilderPaymentQuorumThreshold a = .ok q ∧ tickPushes ctx st = rotPushes q a ∧
      InvFrame st a ∧ st'.builder_pending_withdrawals = b.builder_pending_withdrawals ∧
      curEpoch st' = curEpoch st + 1 := by
  obtain ⟨st1, next, h1, hn, f1, hnext, hc⟩ := slotTick_cases h
  rcases hc with ⟨hne, rfl⟩ | ⟨h0, a, b, st2, ha, hb, hsuf, rfl⟩
  · left
    refine ⟨?_, f1.2.2.1⟩
    rw [hnext] at hne
    simp only [tickPushes, hne, ite_false]
  · right
    obtain ⟨-, q, hq, -⟩ := processBuilderPendingPayments_frame hb
    have hcur := evalAt_cur (E := fun _ _ => True) ⟨st1, next, a, h1, hn, h0, ha, trivial⟩ h
    refine ⟨st1, next, a, b, q, h1, hn, h0, ha, hb, hq, ?_, invFrame.trans f1 (epochPrefix_invFrame ha),
      (epochSuffix_invFrame hsuf).2.2.1, hcur⟩
    rw [hnext] at h0
    simp only [tickPushes, h0, ite_true, h1, ha, hq]

/-- **The slot loop appends exactly `loopPushes`.** -/
theorem slotLoop_pushes {ctx : Ctx} :
    ∀ (n : Nat) (st st' : Gloas.BeaconState P), slotLoop ctx n st = .ok st' →
      st'.builder_pending_withdrawals.toArray.toList =
        st.builder_pending_withdrawals.toArray.toList ++ (loopPushes ctx n st).map (·.w)
  | 0, st, st', h => by cases h; simp only [loopPushes, List.map_nil, List.append_nil]
  | n + 1, st, st', h => by
    obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
    rw [slotLoop_pushes n x st' h, loopPushes_succ hx, List.map_append, ← List.append_assoc]
    congr 1
    rcases tick_cases hx with ⟨e, hw⟩ | ⟨st1, next, a, b, q, -, -, -, -, hb, hq, e, fa, hw, -⟩
    · rw [e, hw, List.map_nil, List.append_nil]
    · obtain ⟨-, q', hq', hbw, -⟩ := processBuilderPendingPayments_frame hb
      rw [hq] at hq'; cases hq'
      rw [e, rotPushes_w, hw, hbw, fa.2.2.1]
      rfl

/-- The virtual slot `SLOTS_PER_EPOCH * e + k` of a first-half index `k`. -/
theorem vslot_div_mod {k e : Nat} (hk : k < P.SLOTS_PER_EPOCH) :
    (P.SLOTS_PER_EPOCH * e + k) / P.SLOTS_PER_EPOCH = e ∧ (P.SLOTS_PER_EPOCH * e + k) % P.SLOTS_PER_EPOCH = k := by
  have hspe : 0 < P.SLOTS_PER_EPOCH := by omega
  rw [Nat.mul_add_div hspe, Nat.mul_add_mod, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
  exact ⟨rfl, rfl⟩

/-- **Every append of the slot loop is a quorum append of an evaluated live payment.** Along a successful slot
loop, each element of `loopPushes` was appended by the rotation that evaluates the payment of its slot, live, with
the quorum reached (`QEv … true`). The quorum is positive, so the evaluated entry is not the empty one. -/
theorem loopPushes_rotEval (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) {ctx : Ctx} {e : Push} :
    ∀ (n : Nat) (st st' : Gloas.BeaconState P), slotLoop ctx n st = .ok st' → e ∈ loopPushes ctx n st →
      e.path = .quorum ∧ RotEval ctx (QEv e.slot e.w true) n st
  | 0, _, _, _, he => by simp only [loopPushes, List.not_mem_nil] at he
  | n + 1, st, st', h, he => by
    obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
    rw [loopPushes_succ hx] at he
    rcases List.mem_append.mp he with he | he
    · rcases tick_cases hx with ⟨e0, -⟩ | ⟨st1, next, a, b, q, h1, hn, h0, ha, -, hqa, e0, fa, -, -⟩
      · rw [e0] at he; cases he
      · rw [e0] at he
        obtain ⟨k, p, hk, hp, hw, rfl⟩ := mem_rotPushes he
        have hcur : curEpoch a = curEpoch st := by unfold curEpoch; rw [fa.2.2.2.2.2.2.1]
        obtain ⟨hdiv, hmod⟩ := vslot_div_mod (P := P) (e := curEpoch st) hk
        refine ⟨rfl, Or.inl ⟨st1, next, a, h1, hn, h0, ha, ?_, p, q, ?_, ⟨?_, rfl⟩, hqa, decide_eq_true hw⟩⟩
        · show (P.SLOTS_PER_EPOCH * curEpoch a + k) / P.SLOTS_PER_EPOCH = curEpoch st
          rw [hcur]; exact hdiv
        · show cell (P.SLOTS_PER_EPOCH * curEpoch a + k) st = some p
          have hidx : payIdx (P.SLOTS_PER_EPOCH * curEpoch a + k) st = some k := by
            unfold payIdx; rw [hcur, ite_eq_right (by omega), ite_eq_left hdiv, hmod]
          rw [cell_of_payIdx hidx, ← fa.2.1]; exact hp
        · rintro rfl
          have hpos := quorum_pos hq hqa
          have hle : q.toNat ≤ Gloas.BuilderPendingPayment.empty.weight.toNat := hw
          have hz : Gloas.BuilderPendingPayment.empty.weight.toNat = 0 := rfl
          omega
    · obtain ⟨hp, hr⟩ := loopPushes_rotEval hq n x st' h he
      exact ⟨hp, Or.inr ⟨x, hx, hr⟩⟩

/-- Every append of the slot loop is attributed to a slot of an epoch the loop ends: from the loop's first epoch
on, before its last. -/
theorem loopPushes_epoch {ctx : Ctx} {e : Push} :
    ∀ (n : Nat) (st st' : Gloas.BeaconState P), slotLoop ctx n st = .ok st' → e ∈ loopPushes ctx n st →
      curEpoch st ≤ e.slot / P.SLOTS_PER_EPOCH ∧ e.slot / P.SLOTS_PER_EPOCH < curEpoch st'
  | 0, _, _, _, he => by simp only [loopPushes, List.not_mem_nil] at he
  | n + 1, st, st', h, he => by
    obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
    rw [loopPushes_succ hx] at he
    have hsx : curEpoch st ≤ curEpoch x := curEpoch_mono (by rw [slotTick_slot hx]; omega)
    rcases List.mem_append.mp he with he | he
    · rcases tick_cases hx with ⟨e0, -⟩ | ⟨st1, next, a, b, q, -, -, -, -, -, -, e0, fa, -, hcx⟩
      · rw [e0] at he; cases he
      · rw [e0] at he
        obtain ⟨k, p, hk, -, -, rfl⟩ := mem_rotPushes he
        have hcur : curEpoch a = curEpoch st := by unfold curEpoch; rw [fa.2.2.2.2.2.2.1]
        have hdiv : (P.SLOTS_PER_EPOCH * curEpoch a + k) / P.SLOTS_PER_EPOCH = curEpoch st := by
          rw [hcur]; exact (vslot_div_mod hk).1
        have hxs : curEpoch x ≤ curEpoch st' := curEpoch_mono (by rw [slotLoop_slot _ _ _ h]; omega)
        show curEpoch st ≤ (P.SLOTS_PER_EPOCH * curEpoch a + k) / P.SLOTS_PER_EPOCH ∧
          (P.SLOTS_PER_EPOCH * curEpoch a + k) / P.SLOTS_PER_EPOCH < curEpoch st'
        rw [hdiv]; omega
    · have := loopPushes_epoch n x st' h he
      omega

/-- **The slot loop's appends are in strictly increasing slot order**: at most one per payment. -/
theorem loopPushes_sorted {ctx : Ctx} :
    ∀ (n : Nat) (st st' : Gloas.BeaconState P), slotLoop ctx n st = .ok st' →
      (loopPushes ctx n st).Pairwise (fun x y => x.slot < y.slot)
  | 0, _, _, _ => by simp only [loopPushes, List.Pairwise.nil]
  | n + 1, st, st', h => by
    obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
    rw [loopPushes_succ hx, List.pairwise_append]
    refine ⟨?_, loopPushes_sorted n x st' h, fun e1 he1 e2 he2 => ?_⟩
    · rcases tick_cases hx with ⟨e0, -⟩ | ⟨st1, next, a, b, q, -, -, -, -, -, -, e0, -⟩
      · rw [e0]; exact List.Pairwise.nil
      · rw [e0]; exact rotPushes_sorted q a
    · rcases tick_cases hx with ⟨e0, -⟩ | ⟨st1, next, a, b, q, -, -, -, -, -, -, e0, fa, -, hcx⟩
      · rw [e0] at he1; cases he1
      · rw [e0] at he1
        obtain ⟨k, p, hk, -, -, rfl⟩ := mem_rotPushes he1
        have hcur : curEpoch a = curEpoch st := by unfold curEpoch; rw [fa.2.2.2.2.2.2.1]
        have hdiv : (P.SLOTS_PER_EPOCH * curEpoch a + k) / P.SLOTS_PER_EPOCH = curEpoch st := by
          rw [hcur]; exact (vslot_div_mod hk).1
        have h2 := (loopPushes_epoch n x st' h he2).1
        show P.SLOTS_PER_EPOCH * curEpoch a + k < e2.slot
        have hlt : (P.SLOTS_PER_EPOCH * curEpoch a + k) / P.SLOTS_PER_EPOCH < e2.slot / P.SLOTS_PER_EPOCH := by
          rw [hdiv]; omega
        exact Nat.lt_of_div_lt_div hlt

/-! ## The parent settlement -/

/-- **The append of `process_parent_execution_payload` at `m`** (at most one): nothing on an EMPTY parent; on a
FULL parent whose slot is in the window, the withdrawal of the entry at its window index when the amount is
positive (`settle_builder_payment`); on a FULL parent whose slot is out of the window, the parent bid's
withdrawal when the bid pays (the old-parent direct append). Either is attributed to the parent's slot. -/
def parentPushes (m : Gloas.BeaconState P) (blk : Gloas.BeaconBlock P) : List Push :=
  if parentFull m blk = true then
    match payIdx (m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH) m with
    | some k =>
      match m.builder_pending_payments.toArray[k]? with
      | some p =>
        if U64.zero < p.withdrawal.amount then
          [⟨.settled, m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH, p.withdrawal⟩]
        else []
      | none => []
    | none =>
      if U64.zero < m.latest_execution_payload_bid.value then
        [⟨.direct, m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH,
          bidWithdrawal m.latest_execution_payload_bid⟩]
      else []
  else []

theorem parentPushes_length (m : Gloas.BeaconState P) (blk : Gloas.BeaconBlock P) :
    (parentPushes m blk).length ≤ 1 := by
  unfold parentPushes
  repeat' split
  all_goals simp only [List.length_nil, List.length_cons, Nat.zero_le, Nat.le_refl]

/-- What an element of `parentPushes` is. -/
theorem mem_parentPushes {m : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P} {e : Push}
    (he : e ∈ parentPushes m blk) :
    parentFull m blk = true ∧ e.slot = m.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH ∧
      ((e.path = .settled ∧ LiveAt e.slot e.w m ∧ U64.zero < e.w.amount) ∨
        (e.path = .direct ∧ payIdx e.slot m = none ∧ U64.zero < m.latest_execution_payload_bid.value ∧
          e.w = bidWithdrawal m.latest_execution_payload_bid)) := by
  unfold parentPushes at he
  split at he
  · rename_i hfull
    split at he
    · rename_i k hk
      split at he
      · rename_i p hp
        split at he
        · rename_i hpos
          rw [List.mem_singleton] at he
          subst he
          exact ⟨hfull, rfl, Or.inl ⟨rfl, ⟨p, by rw [cell_of_payIdx hk, hp], ne_empty_of_amount hpos, rfl⟩, hpos⟩⟩
        · cases he
      · cases he
    · rename_i hk
      split at he
      · rename_i hv
        rw [List.mem_singleton] at he
        subst he
        exact ⟨hfull, rfl, Or.inr ⟨rfl, hk, hv, rfl⟩⟩
      · cases he
  · cases he

theorem toList_push {s : Spine} {α : Type} (l : ProgressiveListS s α) (x : α) :
    (l.push x).toArray.toList = l.toArray.toList ++ [x] := by
  show (l.toArray.push x).toList = _
  rw [Array.toList_push]

/-- **The parent settlement appends exactly `parentPushes`.** -/
theorem parent_pushes (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx} {m s1 : Gloas.BeaconState P}
    {blk : Gloas.BeaconBlock P} (h : Gloas.processParentExecutionPayload ctx m blk = .ok s1) :
    s1.builder_pending_withdrawals.toArray.toList =
      m.builder_pending_withdrawals.toArray.toList ++ (parentPushes m blk).map (·.w) := by
  rcases processParentExecutionPayload_cases h with ⟨rfl, hne⟩ | ⟨hf, a, d, e, ha, hd, he, hs⟩
  · have hfull : parentFull s1 blk = false := by
      simpa only [parentFull, beq_eq_false_iff_ne, ne_eq] using hne
    simp only [parentPushes, hfull, Bool.false_eq_true, ite_false, List.map_nil, List.append_nil]
  have hfull : parentFull m blk = true := by simp only [parentFull, hf, beq_self_eq_true]
  obtain ⟨x, fx, hc⟩ := applyParentPrefix_idx hspe ha
  have e1 : s1.builder_pending_withdrawals = x.builder_pending_withdrawals := by
    rw [(applyParentSuffix_post hs).2.2.1, builderLoops_bpw hd he, fx.2.2.1]
  rw [e1]
  rcases hc with ⟨idx, hidx, hx⟩ | ⟨hnone, ⟨hv, rfl⟩ | ⟨hv0, rfl⟩⟩
  · obtain ⟨-, p, hp, hpush, hkeep, -⟩ := settleBuilderPayment_frame hx
    by_cases hpos : U64.zero < p.withdrawal.amount
    · rw [hpush hpos, toList_push]
      simp only [parentPushes, hfull, ite_true, hidx, hp, hpos, List.map_cons, List.map_nil]
    · rw [hkeep hpos]
      simp only [parentPushes, hfull, ite_true, hidx, hp, hpos, ite_false, List.map_nil, List.append_nil]
  · have hd' : (directAppend m).builder_pending_withdrawals =
        m.builder_pending_withdrawals.push (bidWithdrawal m.latest_execution_payload_bid) := rfl
    rw [hd', toList_push]
    simp only [parentPushes, hfull, ite_true, hnone, hv, List.map_cons, List.map_nil]
  · simp only [parentPushes, hfull, ite_true, hnone, hv0, ite_false, List.map_nil, List.append_nil]

/-! ## A Gloas step -/

/-- **The appends of a Gloas step to `builder_pending_withdrawals`**, in order: those of the epoch rotations
inside its `process_slots`, then that of its parent settlement. -/
def _root_.Blanc.GloasStepData.pushes (D : GloasStepData (P := P) cfg ccfg bls) : List Push :=
  loopPushes (gloasCtx ccfg bls) (D.block.message.slot.toNat - D.preB.slot.toNat) D.preB ++
    parentPushes D.postSlots D.block.message

/-- **C1, the list: a Gloas step appends exactly `D.pushes`.** The step's post-state
`builder_pending_withdrawals` is its pre-state's followed by the withdrawals of `D.pushes`, in order, less the
`d` entries its `process_withdrawals` removed from the front (`D.Drops d`: the `d` the step drops from the queue
`process_withdrawals` reads, which is the pre-state queue followed by the appends). No other phase of the step
writes the queue. -/
theorem _root_.Blanc.GloasStepData.pushes_exhaustive (D : GloasStepData (P := P) cfg ccfg bls)
    (hspe : 0 < P.SLOTS_PER_EPOCH) :
    ∃ d, D.Drops d ∧
      d ≤ (D.preB.builder_pending_withdrawals.toArray.toList ++ D.pushes.map (·.w)).length ∧
      D.postB.builder_pending_withdrawals.toArray.toList =
        (D.preB.builder_pending_withdrawals.toArray.toList ++ D.pushes.map (·.w)).drop d := by
  obtain ⟨d, s1, s2, s3, h1, h2, h3, hdrop, hle⟩ := D.drops_exists
  obtain ⟨t1, t2, t3, s4, s5, s6, s7, g1, g2, g3, h4, h5, h6, h7, h8⟩ := processBlock_phases D.processBlock
  rw [h1] at g1; cases g1
  rw [h2] at g2; cases g2
  rw [h3] at g3; cases g3
  obtain ⟨-, -, hm2⟩ := processBlockHeader_post h2
  have e2 : s2.builder_pending_withdrawals = s1.builder_pending_withdrawals := by rw [hm2]
  have b4 := processExecutionPayloadBid_post h4
  have o7 := processOperations_ops _ _ _ _ _ h7
  have e8 : D.postB.builder_pending_withdrawals = s7.builder_pending_withdrawals :=
    (processSyncAggregate_invFrame _ _ _ _ h8).2.2.1
  have e6 : s6.builder_pending_withdrawals = s4.builder_pending_withdrawals :=
    ((processEth1Data_invFrame _ _ _ h6).2.2.1).trans (processRandao_invFrame _ _ _ _ h5).2.2.1
  have hq : s2.builder_pending_withdrawals.toArray.toList =
      D.preB.builder_pending_withdrawals.toArray.toList ++ D.pushes.map (·.w) := by
    rw [e2, parent_pushes hspe h1, slotLoop_pushes _ _ _ (processSlots_slotLoop D.slots).2,
      GloasStepData.pushes, List.map_append, List.append_assoc]
  refine ⟨d, ⟨s1, s2, s3, h1, h2, h3, hdrop, hle⟩, hq ▸ hle, ?_⟩
  rw [e8, o7.2.1, e6, b4.2.2.2.2.2.2.2.2.2.1, hdrop, hq]

/-- **The source of one append of a Gloas step**: the path it names appended it, for the payment at its slot.

* `quorum`: the rotation inside the step's `process_slots` that evaluates the payment of slot `e.slot` found its
  entry live, carrying `e.w`, with weight at least the quorum (`QEv … true`), and ran
  `process_builder_pending_payments`, which appended `e.w` (`PendingAppend`);
* `settled`: the step settled its parent FULL, `e.slot` is the parent's slot, the parent's payment entry was
  live carrying `e.w` of positive amount, and `process_parent_execution_payload` pushed exactly `e.w`;
* `direct`: the step settled its parent FULL, `e.slot` is the parent's slot, out of the window, the parent bid
  pays, `e.w` is its withdrawal, and `process_parent_execution_payload` pushed exactly `e.w`. -/
def _root_.Blanc.GloasStepData.PushSource (D : GloasStepData (P := P) cfg ccfg bls) (e : Push) : Prop :=
  (e.path = .quorum ∧
    RotEval (gloasCtx ccfg bls) (fun x a => QEv e.slot e.w true x a ∧ PendingAppend ccfg e.w a)
      (D.block.message.slot.toNat - D.preB.slot.toNat) D.preB) ∨
  (e.path = .settled ∧ parentFull D.postSlots D.block.message = true ∧
    e.slot = D.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH ∧
    LiveAt e.slot e.w D.postSlots ∧ U64.zero < e.w.amount ∧
    ∃ s1, Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1 ∧
      s1.builder_pending_withdrawals = D.postSlots.builder_pending_withdrawals.push e.w) ∨
  (e.path = .direct ∧ parentFull D.postSlots D.block.message = true ∧
    e.slot = D.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH ∧
    payIdx e.slot D.postSlots = none ∧ U64.zero < D.postSlots.latest_execution_payload_bid.value ∧
    e.w = bidWithdrawal D.postSlots.latest_execution_payload_bid ∧
    ∃ s1, Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1 ∧
      s1.builder_pending_withdrawals = D.postSlots.builder_pending_withdrawals.push e.w)

/-- **C1, the sources: every append of a Gloas step comes through exactly the path it names, for the payment at
its slot.** With the quorum positive (`quorumPositive`). -/
theorem _root_.Blanc.GloasStepData.push_source (D : GloasStepData (P := P) cfg ccfg bls)
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hspe : 0 < P.SLOTS_PER_EPOCH) {e : Push}
    (he : e ∈ D.pushes) : D.PushSource e := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨hp, hr⟩ := loopPushes_rotEval hq _ _ _ (processSlots_slotLoop D.slots).2 he
    exact Or.inl ⟨hp, D.rotQ_appends hspe hr⟩
  · obtain ⟨s1, -, -, -, -, -, -, h1, -⟩ := processBlock_phases D.processBlock
    obtain ⟨hfull, hslot, ⟨hp, hl, hpos⟩ | ⟨hp, hnone, hv, hw⟩⟩ := mem_parentPushes he
    · rw [hslot] at hl
      have hs1 := (parent_settled_appends hspe h1 hfull hl hpos).2
      exact Or.inr (Or.inl ⟨hp, hfull, hslot, hslot ▸ hl, hpos, s1, h1, hs1⟩)
    · rw [hslot] at hnone
      have hs1 := parent_direct_appends hspe h1 hfull hnone hv
      exact Or.inr (Or.inr ⟨hp, hfull, hslot, hslot ▸ hnone, hv, hw, s1, h1, hw ▸ hs1⟩)

/-- The rotation appends of a step come first, in strictly increasing slot order. -/
theorem _root_.Blanc.GloasStepData.loopPushes_sorted (D : GloasStepData (P := P) cfg ccfg bls) :
    (loopPushes (gloasCtx ccfg bls) (D.block.message.slot.toNat - D.preB.slot.toNat) D.preB).Pairwise
      (fun x y => x.slot < y.slot) :=
  Blanc.Lift.BuilderRequest.loopPushes_sorted _ _ _ (processSlots_slotLoop D.slots).2

/-- **Every append of a step is attributed to a slot before the step's own bid's**: a rotation append to a slot
of an epoch that ended before the block, the settlement's to the parent's slot. -/
theorem _root_.Blanc.GloasStepData.push_slot_lt (D : GloasStepData (P := P) cfg ccfg bls) {e : Push}
    (he : e ∈ D.pushes) : e.slot < D.paySlot := by
  rw [paySlot_eq]
  rcases List.mem_append.mp he with he | he
  · have h := (loopPushes_epoch _ _ _ (processSlots_slotLoop D.slots).2 he).2
    have hlt : e.slot < D.postSlots.slot.toNat := Nat.lt_of_div_lt_div h
    rw [D.postSlots_slot] at hlt
    omega
  · obtain ⟨-, hslot, -⟩ := mem_parentPushes he
    have := D.lbh_lt
    omega

end Blanc.Lift.BuilderRequest
