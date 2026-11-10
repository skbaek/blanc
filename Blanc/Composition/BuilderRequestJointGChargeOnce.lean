import Blanc.Composition.BuilderRequestJointGPush

/-!
# Every bid placed during a run is appended to `builder_pending_withdrawals` at most once

Goal `eip8282-charge-once-v1`, outcome C2 (real-chain safety), counting the appended elements themselves
(`BuilderRequestJointGPush`), not destination labels.

* `GJointRun.pushes`: every append of the run to `builder_pending_withdrawals`, in order: each Gloas step's
  `GloasStepData.pushes`; none before Gloas, and none at the crossing, whose queue is empty at the upgraded state,
  after its slots and after its block (`CrossingData.queue_empty`).
* **`ValidJointG.queue_suffix_pushes`**: the final queue is a suffix of the anchor's queue followed by the run's
  appends. From a pre-Gloas (Fulu) anchor the anchor's queue is empty, so every queued element is one of the run's
  appends (`ValidJointG.fulu_queue_suffix_pushes`): Gloas begins at the fork, and nothing is charged that the run
  did not append.
* **`ValidJointG.bid_appended_at_most_once`** (C2): for a Gloas step `j` whose bid pays an external builder, at
  most one element of `run.pushes` is attributed to that bid's payment (the pushes at its slot `D.paySlot`), over
  the whole run and over all three paths; `ValidJointG.bid_append_is_bid`: such an element is the bid's own
  withdrawal `D.payW`. The statement holds from any anchor; from a Fulu anchor, with the suffix theorem, it is the
  whole of the queue's history.

The count is derived from the exclusivity of the payment's destinations (`fate_unique`, the uniqueness half of
`ValidJointG.payment_fate`): `push_fate` turns each append at the bid's slot (C1's `GloasStepData.push_source`)
into the appending destination of its path at its step, so two appends would be two destinations. Within one step
the rotation appends have strictly increasing slots and the settlement appends at most one element. The positive
quorum (`ValidJointG.quorumPositive`) is read twice: an appended entry is not the empty one
(`loopPushes_rotEval`), and no rotation finds the latest bid's entry at the quorum (`no_quorum_latest`, inside
`fate_unique`), which is what excludes a quorum append followed by the old-parent direct append. A bid whose
proposer is slashed in its own block (entry emptied) and whose FULL child comes two or more epochs later is still
appended once, by the direct append, which reads the bid and not the entry: that is the one element counted.

* **`ValidJointG.slot_appended_at_most_once`**: the same count for every slot, proved from the appends alone
  (liveness of the entry, no destination labels): at most one element of `run.pushes` is attributed to the payment
  of any one slot. It covers what `payment_fate` does not state: the first Gloas block's bid, placed by the
  crossing step (`ValidJointG.crossing_bid_appended_at_most_once`).

* Run-level forms, for any run prefix (no `ValidJointG`): `GJointRun.queue_suffix_pushes` and
  `slot_pushes_le_one` (the appends of a run have pairwise distinct slots, given G3-07, G3-08 and `FutureEmpty`
  at each Gloas step's pre-state).
* `pushes_before_latest`: every append up to and including a Gloas step is attributed to a slot before that
  step's bid's. So at every Gloas state after a Gloas step, the latest bid's payment has not been appended by the
  run (the invariant a Gloas-anchor premise of the form "the latest bid is not already queued" needs).
  `push_dead_after`: a payment the run appended is not live at any later Gloas state, so no queued entry and
  live payments entry are of the same slot.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## The appends of a run -/

/-- **The appends of one run step to `builder_pending_withdrawals`**: a Gloas step's `pushes`; none before
Gloas (there is no such queue) and none at the crossing (`CrossingData.queue_empty`). -/
def _root_.Blanc.GJointRunStep.pushes : GJointRunStep (P := P) cfg ccfg bls → List Push
  | .pre _ => []
  | .crossing _ => []
  | .gloas D => D.pushes

/-- **The appends of a run to `builder_pending_withdrawals`**, in order. -/
def _root_.Blanc.GJointRun.pushes {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) : List Push :=
  run.steps.flatMap GJointRunStep.pushes

/-- The pending builder withdrawals of a joint state (none before Gloas). -/
def _root_.JauneConsensus.GJointState.builderQueue : GJointState P → List Gloas.BuilderPendingWithdrawal
  | .pre _ => []
  | .gloas b _ _ => b.builder_pending_withdrawals.toArray.toList

/-- **The crossing appends nothing**: `builder_pending_withdrawals` is empty at `upgrade_to_gloas`'s state,
after the crossing's slots, and after the first Gloas block. -/
theorem _root_.Blanc.CrossingData.queue_empty (C : CrossingData (P := P) cfg ccfg bls)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH)
    (validatorsBound : C.postB.validators.toArray.size ≤ 2 ^ 40)
    (buildersBound : C.postB.builders.toArray.size ≤ 2 ^ 40) :
    C.upgraded.builder_pending_withdrawals.toArray.toList = [] ∧
      C.postSlots.builder_pending_withdrawals.toArray.toList = [] ∧
      C.postB.builder_pending_withdrawals.toArray.toList = [] := by
  have hc0 := upgradeToGloas_crossClean C.upgrade
  refine ⟨hc0.1, (crossingSlots_crossClean quorumPositive C.slots hc0).1.1, ?_⟩
  rw [(C.builders_eq quorumPositive slotsPerEpoch validatorsBound buildersBound).2]
  exact hc0.1

/-! ## An append at a bid's slot is an appending destination of the bid's payment -/

theorem rotEval_imp {ctx : Ctx} {E E' : Gloas.BeaconState P → Gloas.BeaconState P → Prop}
    (h : ∀ x a, E x a → E' x a) : ∀ (n : Nat) (st : Gloas.BeaconState P), RotEval ctx E n st → RotEval ctx E' n st
  | 0, _, hr => hr
  | n + 1, _, hr => by
    rcases hr with ⟨st1, next, a, h1, hn, h0, ha, hE⟩ | ⟨x, hx, hr⟩
    · exact Or.inl ⟨st1, next, a, h1, hn, h0, ha, h _ _ hE⟩
    · exact Or.inr ⟨x, hx, rotEval_imp h n x hr⟩

/-- After a step whose bid pays, a live entry at the bid's slot carries the bid's withdrawal. -/
theorem _root_.Blanc.GloasStepData.live_postB_payW (D : GloasStepData (P := P) cfg ccfg bls)
    (hspe : 0 < P.SLOTS_PER_EPOCH) (hv : U64.zero < D.bid.value) {w : Gloas.BuilderPendingWithdrawal}
    (hl : LiveAt D.paySlot w D.postB) : w = D.payW := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases D.processBlock
  have l4 : LiveAt D.paySlot D.payW s4 := bid_live hspe h4 hv
  have f5 := processRandao_invFrame _ _ _ _ h5
  have f6 := processEth1Data_invFrame _ _ _ h6
  have c64 : cell D.paySlot s6 = cell D.paySlot s4 :=
    (cell_congr f6.2.2.2.2.2.2.1 f6.2.1).trans (cell_congr f5.2.2.2.2.2.2.1 f5.2.1)
  obtain ⟨p, hp, -, hpw⟩ := liveAt_of_cell c64 (ops_live_back h7 (liveAt_of_cell (sync_cell h8) hl))
  obtain ⟨p', hp', -, hpw'⟩ := l4
  rw [hp] at hp'; cases hp'
  exact hpw.symm.trans hpw'

/-- The appending destination a path names at a step, as a key: the path and the step. -/
def PaymentFate.pushKey? {s₀ sf : GJointState P} {run : GJointRun cfg ccfg bls s₀ sf} {j : Nat} :
    PaymentFate run j → Option (PushPath × Nat)
  | .quorum i => some (.quorum, i)
  | .settled i => some (.settled, i)
  | .directAppend i => some (.direct, i)
  | .droppedSubQuorum _ => none
  | .clearedBySlash _ => none
  | .pendingAtEnd => none

/-- **An append at a paying bid's slot is the bid's payment reaching the appending destination of its path, at
its step.** Step `j`'s bid pays; `e` is an append of step `i` (`e ∈ D'.pushes`) attributed to the bid's slot. Then
`e` is the bid's withdrawal, and the destination of `e`'s path at step `i` (`quorum i`, `settled i` or
`directAppend i`) holds for the bid's payment. -/
theorem push_fate (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hspe : 0 < P.SLOTS_PER_EPOCH)
    {s₀ sf : GJointState P} {run : GJointRun cfg ccfg bls s₀ sf} {j i : Nat}
    {D D' : GloasStepData (P := P) cfg ccfg bls} (stepD : run.steps[j]? = some (.gloas D))
    (hv : U64.zero < D.bid.value) (hD' : run.steps[i]? = some (.gloas D')) {e : Push} (he : e ∈ D'.pushes)
    (hs : e.slot = D.paySlot) :
    e.w = D.payW ∧ ∃ f : PaymentFate run j, f.holdsFor D ∧ f.pushKey? = some (e.path, i) := by
  have hji : j < i := by
    by_contra hc
    have h1 := D'.push_slot_lt he
    have h2 := paySlot_le hD' stepD (Nat.le_of_not_lt hc)
    rw [← paySlot_eq] at h2
    omega
  obtain ⟨C, hC, hpre⟩ := pred_step stepD hD' hji
  have back : ∀ w, LiveAt D.paySlot w D'.preB → w = D.payW := fun w hl =>
    D.live_postB_payW hspe hv
      (live_chain' run hspe stepD hC (by omega) (paySlot_eq D).le (hpre ▸ hl))
  -- a parent append at the bid's slot is the next step's
  have next : e.slot = D'.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH →
      i = j + 1 ∧ D'.preB = D.postB := by
    intro hslot
    have hCs : D.block.message.slot.toNat = C.block.message.slot.toNat := by
      have h1 := paySlot_eq D
      rw [← hs, hslot, D'.postSlots_lbh, hpre, C.postB_slot.2] at h1
      omega
    have hij : i - 1 = j := by
      by_contra hne
      have := slot_lt' run stepD hC (by omega)
      omega
    rw [hij, stepD] at hC; cases hC
    exact ⟨by omega, hpre⟩
  rcases D'.push_source hq hspe he with ⟨hp, hr⟩ | ⟨hp, hfull, hslot, hl, -, -⟩ |
      ⟨hp, hfull, hslot, hnone, -, hw, -⟩
  · have hr' : RotEval (gloasCtx ccfg bls) (QEv e.slot e.w true)
        (D'.block.message.slot.toNat - D'.preB.slot.toNat) D'.preB := rotEval_imp (fun _ _ h => h.1) _ _ hr
    have hl := rotEval_live hspe _ _ hr'
    rw [hs] at hr' hl
    have hw := back _ hl
    rw [hw] at hr'
    exact ⟨hw, .quorum i, ⟨hji, D', hD', hr'⟩, by rw [hp]; rfl⟩
  · obtain ⟨rfl, -⟩ := next hslot
    rw [hs] at hl
    have hw := back _ (slotLoop_live_back hspe _ _ _ (processSlots_slotLoop D'.slots).2 hl)
    rw [hw] at hl
    exact ⟨hw, .settled (j + 1), ⟨rfl, D', hD', hfull, hl⟩, by rw [hp]; rfl⟩
  · obtain ⟨rfl, hpre'⟩ := next hslot
    rw [hs] at hnone
    refine ⟨?_, .directAppend (j + 1), ⟨rfl, D', hD', hfull, hnone⟩, by rw [hp]; rfl⟩
    rw [hw, D'.postSlots_bid, hpre', D.postB_bid]

/-! ## Counting -/

theorem filter_length_le_one {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.Pairwise (fun x y => ¬ (p x = true ∧ p y = true)) → (l.filter p).length ≤ 1
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    rw [List.filter_cons]
    by_cases ha : p a = true
    · rw [ite_eq_left ha, List.filter_eq_nil_iff.mpr (fun x hx hpx => h.1 x hx ⟨ha, hpx⟩)]
      exact Nat.le_refl 1
    · rw [ite_eq_right ha]; exact filter_length_le_one h.2

theorem pairwise_of_length_le_one {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.length ≤ 1 → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | _ :: _ :: _, h => absurd h (by simp only [List.length_cons]; omega)

/-- At most one append of a run at slot `s`, when any two appends of the run at `s` have the same path and the
same step: within one step the rotation appends have strictly increasing slots and the settlement appends at most
one element. -/
theorem pushes_filter_le_one (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    {s₀ sf : GJointState P} {run : GJointRun cfg ccfg bls s₀ sf} {s : Nat}
    (key : ∀ {i i' : Nat} {B B' : GloasStepData (P := P) cfg ccfg bls} {x y : Push},
      run.steps[i]? = some (.gloas B) → run.steps[i']? = some (.gloas B') → x ∈ B.pushes → y ∈ B'.pushes →
      x.slot = s → y.slot = s → x.path = y.path ∧ i = i') :
    (run.pushes.filter (fun e => decide (e.slot = s))).length ≤ 1 := by
  refine filter_length_le_one ?_
  simp only [decide_eq_true_eq]
  unfold GJointRun.pushes
  rw [List.pairwise_flatMap]
  refine ⟨fun C hC => ?_, List.pairwise_iff_getElem.mpr fun i i' hi hi' hlt x hx y hy hxy => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hC
    cases C with
    | pre _ => exact List.Pairwise.nil
    | crossing _ => exact List.Pairwise.nil
    | gloas B =>
      refine List.pairwise_append.mpr ⟨B.loopPushes_sorted.imp (fun hlt hxy => by omega),
        pairwise_of_length_le_one (parentPushes_length _ _), fun x hx y hy hxy => ?_⟩
      have hpx := (loopPushes_rotEval hq _ _ _ (processSlots_slotLoop B.slots).2 hx).1
      obtain ⟨hp, -⟩ := key hi hi (List.mem_append_left _ hx) (List.mem_append_right _ hy) hxy.1 hxy.2
      rw [hpx] at hp
      obtain ⟨-, -, ⟨hpy, -⟩ | ⟨hpy, -⟩⟩ := mem_parentPushes hy <;> rw [hpy] at hp <;> cases hp
  · have hC := List.getElem?_eq_getElem hi
    have hC' := List.getElem?_eq_getElem hi'
    generalize run.steps[i] = C at hC hx
    generalize run.steps[i'] = C' at hC' hy
    cases C with
    | pre _ => cases hx
    | crossing _ => cases hx
    | gloas B =>
      cases C' with
      | pre _ => cases hy
      | crossing _ => cases hy
      | gloas B' =>
        have := (key hC hC' hx hy hxy.1 hxy.2).2
        omega

/-- **After a step, no payment the step appended is live**: the rotation moved its slot out of the window, the
settlement emptied its entry, or its slot was already out of the window (the direct append). -/
theorem _root_.Blanc.GloasStepData.push_dead (B : GloasStepData (P := P) cfg ccfg bls)
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hspe : 0 < P.SLOTS_PER_EPOCH) {x : Push}
    (hx : x ∈ B.pushes) {w : Gloas.BuilderPendingWithdrawal} : ¬ LiveAt x.slot w B.postB := by
  intro hl
  have hne : x.slot ≠ B.block.message.slot.toNat + P.SLOTS_PER_EPOCH := by
    have := B.push_slot_lt hx
    rw [paySlot_eq] at this
    omega
  have hl' := (block_track hspe B.processBlock hne).1 hl
  rcases B.push_source hq hspe hx with ⟨-, hr⟩ | ⟨-, hfull, hslot, -⟩ | ⟨-, -, -, hnone, -⟩
  · exact not_liveAt_of_none
      (B.rotQ_end (show B.RotQ x.slot x.w true from rotEval_imp (fun _ _ h => h.1) _ _ hr)) hl'
  · exact (settle_excl hspe B.processBlock hne hfull hslot hl').2 hl
  · exact not_liveAt_of_none hnone hl'

/-! ## The queue along a run -/

/-- **Along any run, the queue holds nothing but the start's entries and the run's appends**: the end state's
`builder_pending_withdrawals` is a suffix of the start's followed by the withdrawals of `run.pushes` (the N7
bounds are read at the crossing, `CrossingData.queue_empty`). -/
theorem _root_.Blanc.GJointRun.queue_suffix_pushes {s₀ : GJointState P}
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (slotsPerEpoch : 2 ≤ P.SLOTS_PER_EPOCH) :
    ∀ {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s),
      (∀ st ∈ run.states, st.validatorCount ≤ 2 ^ 40) → (∀ st ∈ run.states, st.builderCount ≤ 2 ^ 40) →
      s.builderQueue <:+ s₀.builderQueue ++ run.pushes.map (·.w) := by
  have hspe : 0 < P.SLOTS_PER_EPOCH := by omega
  intro s run
  induction run with
  | nil =>
    intro _ _
    simp only [GJointRun.pushes, GJointRun.steps, List.flatMap_nil, List.map_nil, List.append_nil]
    exact List.suffix_refl _
  | @snoc s run C hC ih =>
    intro hv hb
    have mem : ∀ st ∈ run.states, st ∈ (run.snoc C hC).states := fun st hst => by
      simp only [GJointRun.states, GJointRun.steps_snoc, List.map_append, List.mem_cons, List.mem_append] at hst ⊢
      rcases hst with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hpost : C.postState ∈ (run.snoc C hC).states := GJointRun.end_mem_states _
    have ih' := ih (fun st h => hv st (mem st h)) (fun st h => hb st (mem st h))
    have hp : (run.snoc C hC).pushes = run.pushes ++ C.pushes := by
      simp only [GJointRun.pushes, GJointRun.steps_snoc, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    rw [hp, List.map_append, ← List.append_assoc]
    cases C with
    | pre D => exact List.nil_suffix
    | crossing C =>
      show C.postB.builder_pending_withdrawals.toArray.toList <:+ _
      rw [(C.queue_empty quorumPositive slotsPerEpoch (hv _ hpost) (hb _ hpost)).2.2]
      exact List.nil_suffix
    | gloas D =>
      subst hC
      obtain ⟨d, -, -, hd⟩ := D.pushes_exhaustive hspe
      obtain ⟨t, ht⟩ := ih'
      show D.postB.builder_pending_withdrawals.toArray.toList <:+ _
      rw [hd]
      refine (List.drop_suffix _ _).trans ⟨t, ?_⟩
      rw [← List.append_assoc]
      exact congrArg (· ++ D.pushes.map (·.w)) ht

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- **Every append of the run at a paying bid's slot is the bid's own withdrawal.** -/
theorem bid_append_is_bid (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    (bid : U64.zero < D.bid.value ∧ D.bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD) :
    ∀ e ∈ v.run.pushes, e.slot = D.paySlot → e.w = D.payW := by
  intro e he hs
  obtain ⟨C, hC, heC⟩ := List.mem_flatMap.mp he
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hC
  cases C with
  | pre _ => cases heC
  | crossing _ => cases heC
  | gloas D' =>
    exact (push_fate v.quorumPositive (by have := v.slotsPerEpoch; omega) stepD bid.1 hi heC hs).1

/-- **C2: every bid placed during the run is appended at most once.** A Gloas step `j` whose bid pays
(`value > 0`) an external builder: among all the elements the run appends to `builder_pending_withdrawals`
(`run.pushes`: every quorum-rotation, settlement and old-parent direct append of every step, in order), at most
one is attributed to that bid's payment (its slot `D.paySlot`). In particular a quorum append and the old-parent
direct append of one bid never both happen. -/
theorem bid_appended_at_most_once (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    (bid : U64.zero < D.bid.value ∧ D.bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD) :
    (v.run.pushes.filter (fun e => decide (e.slot = D.paySlot))).length ≤ 1 := by
  have hspe : 0 < P.SLOTS_PER_EPOCH := by have := v.slotsPerEpoch; omega
  have hq := v.quorumPositive
  -- two appends at the bid's slot have the same path and the same step
  have key : ∀ {i i' : Nat} {B B' : GloasStepData (P := P) cfg ccfg bls} {x y : Push},
      v.run.steps[i]? = some (.gloas B) → v.run.steps[i']? = some (.gloas B') → x ∈ B.pushes → y ∈ B'.pushes →
      x.slot = D.paySlot → y.slot = D.paySlot → x.path = y.path ∧ i = i' := by
    intro i i' B B' x y hB hB' hx hy hxs hys
    obtain ⟨-, f, hf, kf⟩ := push_fate hq hspe stepD bid.1 hB hx hxs
    obtain ⟨-, g, hg, kg⟩ := push_fate hq hspe stepD bid.1 hB' hy hys
    have hfg := fate_unique hspe hq stepD (fun _ hD' => v.latest_inv hD') hf hg
    rw [hfg, kg] at kf
    simpa only [Option.some.injEq, Prod.mk.injEq, eq_comm] using kf
  exact pushes_filter_le_one hq key

end ValidJointG

/-- **At most one append per slot, along any run** whose Gloas steps start from states with G3-07, G3-08 and
`FutureEmpty` (`hinv`; on a valid joint chain, `ValidJointG.gInv_pre`). Proved from the appends alone, without the
destination labels: a later rotation append needs the entry live, and no payment a step appended is live after it
(`GloasStepData.push_dead`); a later settlement or direct append is of its own parent's slot, after every earlier
append's; and within one step a rotation append excludes the settlement (the slot left the window) and the direct
append (`no_quorum_latest`: no quorum on the latest bid's entry, the quorum being positive). -/
theorem slot_pushes_le_one (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf)
    (hinv : ∀ {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      NoLiveWeightOnLatestBid B.preB ∧ LatestBidCoherence B.preB ∧ FutureEmpty B.preB) (s : Nat) :
    (run.pushes.filter (fun e => decide (e.slot = s))).length ≤ 1 := by
  -- an append of a later step
  have cross : ∀ {i i' : Nat} {B B' : GloasStepData (P := P) cfg ccfg bls} {x y : Push},
      run.steps[i]? = some (.gloas B) → run.steps[i']? = some (.gloas B') → x ∈ B.pushes → y ∈ B'.pushes →
      i < i' → x.slot = y.slot → False := by
    intro i i' B B' x y hB hB' hx hy hlt hxy
    obtain ⟨C, hC, hpre⟩ := pred_step hB hB' hlt
    have hxs := B.push_slot_lt hx
    have hBC := paySlot_le hB hC (by omega)
    have parent : y.slot ≠ B'.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH := by
      rw [B'.postSlots_lbh, hpre, C.postB_slot.2]; omega
    rcases B'.push_source hq hspe hy with ⟨-, hr⟩ | ⟨-, -, hslot, -⟩ | ⟨-, -, hslot, -⟩
    · have hl := rotEval_live hspe _ _ (rotEval_imp (fun _ _ h => h.1) _ _ hr)
      rw [hpre, ← hxy] at hl
      exact B.push_dead hq hspe hx
        (live_chain' run hspe hB hC (by omega) (by rw [paySlot_eq] at hxs; omega) hl)
    · exact parent hslot
    · exact parent hslot
  -- a rotation append and the parent append of one step
  have within : ∀ {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls} {x y : Push},
      run.steps[i]? = some (.gloas B) → x ∈ B.pushes → y ∈ B.pushes → x.path = .quorum → y.path ≠ .quorum →
      x.slot = y.slot → False := by
    intro i B x y hB hx hy hpx hpy hxy
    have hr : B.RotQ x.slot x.w true := by
      rcases B.push_source hq hspe hx with ⟨-, hr⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
      · exact rotEval_imp (fun _ _ h => h.1) _ _ hr
      · rw [hpx] at hp; cases hp
      · rw [hpx] at hp; cases hp
    rcases B.push_source hq hspe hy with ⟨hp, -⟩ | ⟨-, -, -, hl, -⟩ | ⟨-, -, hslot, -⟩
    · exact hpy hp
    · rw [← hxy] at hl
      exact not_liveAt_of_none (B.rotQ_end hr) hl
    · obtain ⟨g7, g8, fe⟩ := hinv hB
      refine no_quorum_latest hq hspe _ _ ⟨g7, fe, ?_⟩ hr
      rw [hxy, hslot, B.postSlots_lbh, g8.1]
  -- two parent appends of one step
  have par : ∀ {B : GloasStepData (P := P) cfg ccfg bls} {x : Push}, x ∈ B.pushes → x.path ≠ .quorum →
      x ∈ parentPushes B.postSlots B.block.message := by
    intro B x hx hpx
    rcases List.mem_append.mp hx with h | h
    · exact absurd (loopPushes_rotEval hq _ _ _ (processSlots_slotLoop B.slots).2 h).1 hpx
    · exact h
  have one : ∀ {l : List Push} {x y : Push}, l.length ≤ 1 → x ∈ l → y ∈ l → x = y := by
    intro l x y hl hx hy
    match l, hl, hx, hy with
    | [a], _, hx, hy => rw [List.mem_singleton.mp hx, List.mem_singleton.mp hy]
    | _ :: _ :: _, hl, _, _ => simp only [List.length_cons] at hl; omega
  refine pushes_filter_le_one hq fun {i i' B B' x y} hB hB' hx hy hxs hys => ?_
  have hxy : x.slot = y.slot := hxs.trans hys.symm
  rcases lt_trichotomy i i' with h | rfl | h
  · exact (cross hB hB' hx hy h hxy).elim
  · rw [hB] at hB'; cases hB'
    refine ⟨?_, rfl⟩
    by_cases hpx : x.path = .quorum
    · by_cases hpy : y.path = .quorum
      · rw [hpx, hpy]
      · exact (within hB hx hy hpx hpy hxy).elim
    · by_cases hpy : y.path = .quorum
      · exact (within hB hy hx hpy hpx hxy.symm).elim
      · rw [one (parentPushes_length _ _) (par hx hpx) (par hy hpy)]
  · exact (cross hB' hB hy hx h hxy.symm).elim

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- **At most one append per slot.** For every slot `s`, at most one element the run appends to
`builder_pending_withdrawals` is attributed to the payment of slot `s`, whatever placed that payment: a Gloas
step's bid (`bid_appended_at_most_once`), the first Gloas block's bid at the crossing, or an entry already
pending at a Gloas anchor (`slot_pushes_le_one`, with the G3a invariants of `gInv_pre`). -/
theorem slot_appended_at_most_once (v : ValidJointG cfg ccfg bls checkpoint anchor final) (s : Nat) :
    (v.run.pushes.filter (fun e => decide (e.slot = s))).length ≤ 1 :=
  slot_pushes_le_one v.quorumPositive (by have := v.slotsPerEpoch; omega) v.run
    (fun hB => by
      obtain ⟨-, -, -, -, -, g7, g8, -, fe⟩ := v.gInv_pre hB
      exact ⟨g7, g8, fe⟩) s

/-- **The first Gloas block's bid is appended at most once.** The crossing step's block carries a bid too; at
most one element the run appends is attributed to its payment. -/
theorem crossing_bid_appended_at_most_once (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {C : CrossingData (P := P) cfg ccfg bls} (_stepC : v.run.steps[j]? = some (.crossing C)) :
    (v.run.pushes.filter
      (fun e => decide (e.slot = C.block.message.slot.toNat + P.SLOTS_PER_EPOCH))).length ≤ 1 :=
  v.slot_appended_at_most_once _

/-- **The queue holds nothing but the anchor's entries and the run's appends.** The final
`builder_pending_withdrawals` is a suffix of the anchor's followed by the withdrawals of `run.pushes`: each step
appends exactly its `pushes` (`GloasStepData.pushes_exhaustive`) and removes entries from the front only. -/
theorem queue_suffix_pushes (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    final.builderQueue <:+ anchor.builderQueue ++ v.run.pushes.map (·.w) :=
  v.run.queue_suffix_pushes v.quorumPositive v.slotsPerEpoch v.validatorsBound v.buildersBound

/-- **From a pre-Gloas (Fulu) anchor, every queued builder withdrawal is one of the run's appends.** Gloas
begins at the fork with an empty queue, so the final `builder_pending_withdrawals` is a suffix of the withdrawals
of `run.pushes`; with `bid_appended_at_most_once`, each bid placed during the run accounts for at most one of
them. -/
theorem fulu_queue_suffix_pushes {s₀ : JointState P}
    (v : ValidJointG cfg ccfg bls checkpoint (.pre s₀) final) :
    final.builderQueue <:+ v.run.pushes.map (·.w) :=
  v.queue_suffix_pushes

end ValidJointG

end Blanc.Lift.BuilderRequest
