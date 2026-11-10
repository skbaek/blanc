import Blanc.Composition.BuilderRequestJointGPaymentsBlock

/-!
# B5(iii) over a valid Gloas joint chain: the fate of a run-created builder payment

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B5 (iii)).

A Gloas step `j` whose block carries a paying bid (`value > 0`, an external builder) writes the bid's
payment entry at its slot's window index. The payment is tracked by its slot `s` and withdrawal `w`
(`LiveAt s w`: the entry at `payIdx s` carries `w`). `PaymentFate run j` has the six frozen
destinations; `PaymentFate.holds`:

* `quorum j'` (`j < j'`): a rotation inside step `j'`'s `process_slots` reads the live entry with
  weight at least the quorum (CL:1724-1726, the append);
* `settled j'` (`j' = j + 1`): the next block settles its parent FULL while the entry is live
  (`settle_builder_payment`, CL:1799-1804; live implies the parent is in the window and the amount
  is the bid's positive value);
* `directAppend j'` (`j' = j + 1`): the next block settles its parent FULL with the parent's slot out
  of the window (the old-parent branch, CL:1805-1814; it reads the bid, whether or not the entry was
  cleared or dropped before);
* `droppedSubQuorum j'` (`j < j'`): a rotation inside step `j'` reads the live entry below the
  quorum, and no direct append follows;
* `clearedBySlash j'` (`j ≤ j'`): step `j'`'s `process_operations` takes the entry from live to not
  live (only `slash_validator` empties an entry there, CL:1579-1581), and no direct append follows;
* `pendingAtEnd`: the entry is live at the run's final state.

`ValidJointG.payment_fate`: exactly one holds. `ValidJointG.payment_at_most_one_append`: at most one
of the three appending destinations holds, over every step index.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-- The virtual slot a step's bid payment is tracked by (`payIdx`): the bid's slot plus one epoch. -/
abbrev _root_.Blanc.GloasStepData.paySlot (D : GloasStepData (P := P) cfg ccfg bls) : Nat :=
  D.bid.slot.toNat + P.SLOTS_PER_EPOCH

/-- The withdrawal a step's bid records. -/
abbrev _root_.Blanc.GloasStepData.payW (D : GloasStepData (P := P) cfg ccfg bls) :
    Gloas.BuilderPendingWithdrawal :=
  bidWithdrawal D.bid

/-! ## The fates -/

/-- **The destinations of the payment created at step `j`** (statements.md B5 (iii)). -/
inductive PaymentFate {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf) (j : Nat) : Type
  | quorum (j' : Nat)
  | settled (j' : Nat)
  | directAppend (j' : Nat)
  | droppedSubQuorum (j' : Nat)
  | clearedBySlash (j' : Nat)
  | pendingAtEnd

/-- The old-parent branch of the next block appends the bid's withdrawal directly: step `j + 1`
settles its parent FULL while the parent's slot is out of the window. -/
def DirectAppendAt {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf) (j : Nat)
    (D : GloasStepData (P := P) cfg ccfg bls) : Prop :=
  ∃ D', run.steps[j + 1]? = some (.gloas D') ∧ parentFull D'.postSlots D'.block.message = true ∧
    payIdx D.paySlot D'.postSlots = none

/-- What each destination means, for the creating step `D`. -/
def PaymentFate.holdsFor {s₀ sf : GJointState P} {run : GJointRun cfg ccfg bls s₀ sf} {j : Nat}
    (D : GloasStepData (P := P) cfg ccfg bls) : PaymentFate run j → Prop
  | .quorum j' => j < j' ∧ ∃ D', run.steps[j']? = some (.gloas D') ∧ D'.RotQ D.paySlot D.payW true
  | .settled j' => j' = j + 1 ∧ ∃ D', run.steps[j']? = some (.gloas D') ∧
      parentFull D'.postSlots D'.block.message = true ∧ LiveAt D.paySlot D.payW D'.postSlots
  | .directAppend j' => j' = j + 1 ∧ DirectAppendAt run j D
  | .droppedSubQuorum j' => j < j' ∧
      (∃ D', run.steps[j']? = some (.gloas D') ∧ D'.RotQ D.paySlot D.payW false) ∧
      ¬ DirectAppendAt run j D
  | .clearedBySlash j' => j ≤ j' ∧
      (∃ D', run.steps[j']? = some (.gloas D') ∧
        OpsClear (gloasCtx ccfg bls) D.paySlot D.payW D'.postSlots D'.block.message) ∧
      ¬ DirectAppendAt run j D
  | .pendingAtEnd => ∃ b e p, sf = .gloas b e p ∧ LiveAt D.paySlot D.payW b

/-- **The destination holds** for the payment created at step `j` (a Gloas step). -/
def PaymentFate.holds {s₀ sf : GJointState P} {run : GJointRun cfg ccfg bls s₀ sf} {j : Nat}
    (f : PaymentFate run j) : Prop :=
  ∃ D, run.steps[j]? = some (.gloas D) ∧ f.holdsFor D

/-! ## The run after the creating step -/

section Chain

variable {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf)

theorem gloas_succ {i : Nat} {A : GloasStepData (P := P) cfg ccfg bls}
    {C : GJointRunStep (P := P) cfg ccfg bls} (hA : run.steps[i]? = some (.gloas A))
    (hC : run.steps[i + 1]? = some C) : ∃ C', C = .gloas C' ∧ C'.preB = A.postB := by
  have h := run.link hA hC
  cases C with
  | pre C => simp [GJointRunStep.preState, GJointRunStep.postState] at h
  | crossing C => simp [GJointRunStep.preState, GJointRunStep.postState] at h
  | gloas C' =>
    simp only [GJointRunStep.preState, GJointRunStep.postState, GJointState.gloas.injEq] at h
    exact ⟨C', rfl, h.1⟩

theorem gloas_from {a : Nat} {A : GloasStepData (P := P) cfg ccfg bls}
    (hA : run.steps[a]? = some (.gloas A)) :
    ∀ d, a + d < run.steps.length → ∃ B, run.steps[a + d]? = some (.gloas B)
  | 0, _ => ⟨A, hA⟩
  | d + 1, hd => by
    obtain ⟨B, hB⟩ := gloas_from hA d (by omega)
    obtain ⟨C, hC⟩ : ∃ C, run.steps[a + d + 1]? = some C :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨C', rfl, -⟩ := gloas_succ run hB hC
    exact ⟨C', hC⟩

theorem slot_lt {a : Nat} {A : GloasStepData (P := P) cfg ccfg bls}
    (hA : run.steps[a]? = some (.gloas A)) :
    ∀ d (B : GloasStepData (P := P) cfg ccfg bls), run.steps[a + d + 1]? = some (.gloas B) →
      A.block.message.slot.toNat < B.block.message.slot.toNat
  | 0, B, hB => by
    obtain ⟨B', hB', hpre⟩ := gloas_succ run hA hB
    cases hB'
    have := B.pre_lt
    rw [hpre, A.postB_slot.1] at this
    exact this
  | d + 1, B, hB => by
    obtain ⟨C, hC⟩ := gloas_from run hA (d + 1)
      (by have := (List.getElem?_eq_some_iff.mp hB).1; omega)
    have ih := slot_lt hA d C hC
    obtain ⟨B', hB', hpre⟩ := gloas_succ run hC hB
    cases hB'
    have := B.pre_lt
    rw [hpre, C.postB_slot.1] at this
    omega

theorem slot_lt' {a b : Nat} {A B : GloasStepData (P := P) cfg ccfg bls}
    (hA : run.steps[a]? = some (.gloas A)) (hB : run.steps[b]? = some (.gloas B)) (hab : a < b) :
    A.block.message.slot.toNat < B.block.message.slot.toNat := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
  exact slot_lt run hA d B hB

/-- **Liveness only ends along the run** (for a payment of a slot not after step `a`'s). -/
theorem live_chain (hspe : 0 < P.SLOTS_PER_EPOCH) {s : Nat} {w : Gloas.BuilderPendingWithdrawal}
    {a : Nat} {A : GloasStepData (P := P) cfg ccfg bls}
    (hA : run.steps[a]? = some (.gloas A)) (hs : s ≤ A.block.message.slot.toNat + P.SLOTS_PER_EPOCH) :
    ∀ d (B : GloasStepData (P := P) cfg ccfg bls), run.steps[a + d]? = some (.gloas B) →
      LiveAt s w B.postB → LiveAt s w A.postB
  | 0, B, hB, hl => by rw [Nat.add_zero, hA] at hB; cases hB; exact hl
  | d + 1, B, hB, hl => by
    obtain ⟨C, hC⟩ := gloas_from run hA d
      (by have := (List.getElem?_eq_some_iff.mp hB).1; omega)
    obtain ⟨B', hB', hpre⟩ := gloas_succ run hC hB
    cases hB'
    have hlt := slot_lt run hA d B hB
    have := B.live_back hspe (by omega) hl
    rw [hpre] at this
    exact live_chain hspe hA hs d C hC this

theorem live_chain' (hspe : 0 < P.SLOTS_PER_EPOCH) {s : Nat} {w : Gloas.BuilderPendingWithdrawal}
    {a b : Nat} {A B : GloasStepData (P := P) cfg ccfg bls}
    (hA : run.steps[a]? = some (.gloas A)) (hB : run.steps[b]? = some (.gloas B)) (hab : a ≤ b)
    (hs : s ≤ A.block.message.slot.toNat + P.SLOTS_PER_EPOCH) (hl : LiveAt s w B.postB) :
    LiveAt s w A.postB := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  exact live_chain run hspe hA hs d B hB hl

/-- The run ends at the last step's post-state, a Gloas state after a Gloas step. -/
theorem final_of {a : Nat} {A : GloasStepData (P := P) cfg ccfg bls}
    (hA : run.steps[a]? = some (.gloas A)) :
    ∃ n B, a ≤ n ∧ n + 1 = run.steps.length ∧ run.steps[n]? = some (.gloas B) ∧
      sf = .gloas B.postB B.postExec B.postParent := by
  have hlen := (List.getElem?_eq_some_iff.mp hA).1
  obtain ⟨B, hB⟩ := gloas_from run hA (run.steps.length - 1 - a) (by omega)
  refine ⟨_, B, by omega, by omega, hB, ?_⟩
  exact (run.last_post hB (by omega)).symm

end Chain

/-! ## The fate of one payment -/

section Fate

variable {s₀ sf : GJointState P} {run : GJointRun cfg ccfg bls s₀ sf} {j : Nat}
  {D : GloasStepData (P := P) cfg ccfg bls}

theorem paySlot_eq (D : GloasStepData (P := P) cfg ccfg bls) :
    D.paySlot = D.block.message.slot.toNat + P.SLOTS_PER_EPOCH := by
  unfold GloasStepData.paySlot; rw [D.bid_slot]

theorem paySlot_le (stepD : run.steps[j]? = some (.gloas D)) {i : Nat}
    {B : GloasStepData (P := P) cfg ccfg bls} (hB : run.steps[i]? = some (.gloas B)) (hji : j ≤ i) :
    D.paySlot ≤ B.block.message.slot.toNat + P.SLOTS_PER_EPOCH := by
  rw [paySlot_eq]
  rcases Nat.eq_or_lt_of_le hji with rfl | h
  · rw [stepD] at hB; cases hB; exact le_rfl
  · have := slot_lt' run stepD hB h; omega

theorem paySlot_lt (stepD : run.steps[j]? = some (.gloas D)) {i : Nat}
    {B : GloasStepData (P := P) cfg ccfg bls} (hB : run.steps[i]? = some (.gloas B)) (hji : j < i) :
    D.paySlot < B.block.message.slot.toNat + P.SLOTS_PER_EPOCH := by
  rw [paySlot_eq]; have := slot_lt' run stepD hB hji; omega

/-- Every step after the creating step is a Gloas step, whose pre-state is its predecessor's
post-state. -/
theorem pred_step (stepD : run.steps[j]? = some (.gloas D)) {i : Nat}
    {B : GloasStepData (P := P) cfg ccfg bls} (hB : run.steps[i]? = some (.gloas B)) (hji : j < i) :
    ∃ C, run.steps[i - 1]? = some (.gloas C) ∧ B.preB = C.postB := by
  obtain ⟨C, hC⟩ := gloas_from run stepD (i - 1 - j)
    (by have := (List.getElem?_eq_some_iff.mp hB).1; omega)
  rw [show j + (i - 1 - j) = i - 1 by omega] at hC
  obtain ⟨B', hB', hpre⟩ := gloas_succ run hC (by rw [show i - 1 + 1 = i by omega]; exact hB)
  cases hB'
  exact ⟨C, hC, hpre⟩

/-- Live at a later step's pre-state: live after every step from the creating one on. -/
theorem before_live (hspe : 0 < P.SLOTS_PER_EPOCH) (stepD : run.steps[j]? = some (.gloas D)) {i : Nat}
    {B : GloasStepData (P := P) cfg ccfg bls} (hB : run.steps[i]? = some (.gloas B)) (hji : j < i)
    (hl : LiveAt D.paySlot D.payW B.preB) :
    ∀ i' (B' : GloasStepData (P := P) cfg ccfg bls), run.steps[i']? = some (.gloas B') → j ≤ i' →
      i' < i → LiveAt D.paySlot D.payW B'.postB := by
  intro i' B' hB' hj' hi'
  obtain ⟨C, hC, hpre⟩ := pred_step stepD hB hji
  rw [hpre] at hl
  exact live_chain' run hspe hB' hC (by omega) (paySlot_le stepD hB' hj') hl

theorem postB_to_postSlots (hspe : 0 < P.SLOTS_PER_EPOCH) (stepD : run.steps[j]? = some (.gloas D))
    {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls} (hB : run.steps[i]? = some (.gloas B))
    (hji : j < i) (hl : LiveAt D.paySlot D.payW B.postB) : LiveAt D.paySlot D.payW B.postSlots :=
  (block_track hspe B.processBlock (by have := paySlot_lt stepD hB hji; omega)).1 hl

theorem postSlots_to_preB (hspe : 0 < P.SLOTS_PER_EPOCH) {B : GloasStepData (P := P) cfg ccfg bls} (hl : LiveAt D.paySlot D.payW B.postSlots) :
    LiveAt D.paySlot D.payW B.preB :=
  slotLoop_live_back hspe _ _ _ (processSlots_slotLoop B.slots).2 hl

/-- The index of the step at which a non-appending-by-the-old-parent destination ends the
payment. -/
def PaymentFate.flipIdx? {s₀ sf : GJointState P} {run : GJointRun cfg ccfg bls s₀ sf} {j : Nat} :
    PaymentFate run j → Option Nat
  | .quorum i => some i
  | .settled i => some i
  | .droppedSubQuorum i => some i
  | .clearedBySlash i => some i
  | .directAppend _ => none
  | .pendingAtEnd => none

/-- **Each such destination ends the payment at its step, and only there**: not live after that
step, live after every earlier step from the creating one. -/
theorem flip_index (hspe : 0 < P.SLOTS_PER_EPOCH) (stepD : run.steps[j]? = some (.gloas D)) {f : PaymentFate run j} (hf : f.holdsFor D) {i : Nat}
    (hi : f.flipIdx? = some i) :
    j ≤ i ∧ (∃ B, run.steps[i]? = some (.gloas B) ∧ ¬ LiveAt D.paySlot D.payW B.postB) ∧
      ∀ i' (B' : GloasStepData (P := P) cfg ccfg bls), run.steps[i']? = some (.gloas B') → j ≤ i' →
        i' < i → LiveAt D.paySlot D.payW B'.postB := by
  have rot : ∀ {b : Bool} {B : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      j < i → B.RotQ D.paySlot D.payW b →
      j ≤ i ∧ (∃ B, run.steps[i]? = some (.gloas B) ∧ ¬ LiveAt D.paySlot D.payW B.postB) ∧
      ∀ i' (B' : GloasStepData (P := P) cfg ccfg bls), run.steps[i']? = some (.gloas B') → j ≤ i' →
        i' < i → LiveAt D.paySlot D.payW B'.postB := by
    intro b B hB hji hr
    refine ⟨hji.le, ⟨B, hB, fun hl => not_liveAt_of_none (B.rotQ_end hr)
      (postB_to_postSlots hspe stepD hB hji hl)⟩, before_live hspe stepD hB hji ?_⟩
    exact rotEval_live hspe _ _ hr
  cases f with
  | quorum i₀ =>
    cases hi
    obtain ⟨hji, B, hB, hr⟩ := hf
    exact rot hB hji hr
  | droppedSubQuorum i₀ =>
    cases hi
    obtain ⟨hji, ⟨B, hB, hr⟩, -⟩ := hf
    exact rot hB hji hr
  | settled i₀ =>
    cases hi
    obtain ⟨rfl, B, hB, hfull, hl⟩ := hf
    obtain ⟨C, hC, hpre⟩ := pred_step stepD hB (by omega)
    rw [show j + 1 - 1 = j by omega, stepD] at hC; cases hC
    have hps : D.paySlot = B.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH := by
      rw [B.postSlots_lbh, hpre, D.postB_slot.2, paySlot_eq]
    refine ⟨by omega, ⟨B, hB, (settle_excl hspe B.processBlock
      (by have := paySlot_lt stepD hB (by omega); omega) hfull hps hl).2⟩,
      before_live hspe stepD hB (by omega) (postSlots_to_preB hspe hl)⟩
  | clearedBySlash i₀ =>
    cases hi
    obtain ⟨hji, ⟨B, hB, hc⟩, -⟩ := hf
    refine ⟨hji, ⟨B, hB, opsClear_end B.processBlock hc⟩, ?_⟩
    rcases Nat.eq_or_lt_of_le hji with rfl | hlt
    · intro i' _ _ h1 h2; omega
    · exact before_live hspe stepD hB hlt (postSlots_to_preB hspe
        (opsClear_live hspe (by have := paySlot_lt stepD hB hlt; omega) hc))
  | directAppend _ => cases hi
  | pendingAtEnd => cases hi

end Fate

/-! ## Existence and exclusivity -/

section Main

variable {s₀ sf : GJointState P} {run : GJointRun cfg ccfg bls s₀ sf} {j : Nat}
  {D : GloasStepData (P := P) cfg ccfg bls}

/-- **Some destination holds.** -/
theorem fate_exists (hspe : 0 < P.SLOTS_PER_EPOCH) (hv : U64.zero < D.bid.value)
    (stepD : run.steps[j]? = some (.gloas D)) : ∃ f : PaymentFate run j, f.holdsFor D := by
  classical
  by_cases hd : DirectAppendAt run j D
  · exact ⟨.directAppend (j + 1), rfl, hd⟩
  by_cases hall : ∀ i (B : GloasStepData (P := P) cfg ccfg bls), run.steps[i]? = some (.gloas B) →
      j ≤ i → LiveAt D.paySlot D.payW B.postB
  · obtain ⟨n, B, hn, -, hB, hsf⟩ := final_of run stepD
    exact ⟨.pendingAtEnd, B.postB, B.postExec, B.postParent, hsf, hall n B hB hn⟩
  have hex : ∃ i, ∃ B : GloasStepData (P := P) cfg ccfg bls, run.steps[i]? = some (.gloas B) ∧
      j ≤ i ∧ ¬ LiveAt D.paySlot D.payW B.postB := by
    push Not at hall
    obtain ⟨i, B, hB, hji, hn⟩ := hall
    exact ⟨i, B, hB, hji, hn⟩
  obtain ⟨i, ⟨B, hB, hji, hn⟩, hmin⟩ : ∃ i, (∃ B : GloasStepData (P := P) cfg ccfg bls,
      run.steps[i]? = some (.gloas B) ∧ j ≤ i ∧ ¬ LiveAt D.paySlot D.payW B.postB) ∧
      ∀ i' < i, ¬ ∃ B : GloasStepData (P := P) cfg ccfg bls,
        run.steps[i']? = some (.gloas B) ∧ j ≤ i' ∧ ¬ LiveAt D.paySlot D.payW B.postB :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i' h => Nat.find_min hex h⟩
  rcases Nat.eq_or_lt_of_le hji with rfl | hlt
  · -- the creating step: only its own operations can end the payment
    rw [stepD] at hB; cases hB
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      processBlock_phases D.processBlock
    have l4 : LiveAt D.paySlot D.payW s4 := bid_live hspe h4 hv
    have f5 := processRandao_invFrame _ _ _ _ h5
    have f6 := processEth1Data_invFrame _ _ _ h6
    have l6 : LiveAt D.paySlot D.payW s6 :=
      liveAt_of_cell ((cell_congr f6.2.2.2.2.2.2.1 f6.2.1).trans
        (cell_congr f5.2.2.2.2.2.2.1 f5.2.1)).symm l4
    have n7 : ¬ LiveAt D.paySlot D.payW s7 := fun hl => hn (liveAt_of_cell (sync_cell h8).symm hl)
    exact ⟨.clearedBySlash j, le_rfl,
      ⟨D, stepD, s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, l6, n7⟩, hd⟩
  · obtain ⟨C, hC, hpre⟩ := pred_step stepD hB hlt
    have hlC : LiveAt D.paySlot D.payW C.postB := by
      by_contra hc
      exact hmin (i - 1) (by omega) ⟨C, hC, by omega, hc⟩
    rw [← hpre] at hlC
    rcases B.flip_cases hspe (paySlot_lt stepD hB hlt) hlC hn with h | h | ⟨hf, hps, hl⟩ | h
    · exact ⟨.quorum i, hlt, B, hB, h⟩
    · exact ⟨.droppedSubQuorum i, hlt, ⟨B, hB, h⟩, hd⟩
    · have hps' : D.paySlot = C.block.message.slot.toNat + P.SLOTS_PER_EPOCH := by
        rw [hps, B.postSlots_lbh, hpre, C.postB_slot.2]
      have hi : i = j + 1 := by
        by_contra hne
        have := paySlot_lt stepD hC (by omega)
        omega
      exact ⟨.settled i, hi, B, hB, hf, hl⟩
    · exact ⟨.clearedBySlash i, hlt.le, ⟨B, hB, h⟩, hd⟩

theorem rot_vs_live {B : GloasStepData (P := P) cfg ccfg bls} {b : Bool}
    (hr : B.RotQ D.paySlot D.payW b) (hl : LiveAt D.paySlot D.payW B.postSlots) : False :=
  not_liveAt_of_none (B.rotQ_end hr) hl

/-- Two destinations ending the payment at the same step are the same. -/
theorem same_index (hspe : 0 < P.SLOTS_PER_EPOCH) (stepD : run.steps[j]? = some (.gloas D)) {f g : PaymentFate run j} {i : Nat}
    (hfi : f.flipIdx? = some i) (hgi : g.flipIdx? = some i) (hf : f.holdsFor D) (hg : g.holdsFor D) :
    f = g := by
  have hne : ∀ {B : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) → j < i →
      D.paySlot ≠ B.block.message.slot.toNat + P.SLOTS_PER_EPOCH := fun hB hlt => by
    have := paySlot_lt stepD hB hlt; omega
  -- a rotation verdict and a later event of the same step
  have rc : ∀ {b : Bool} {B B' : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      run.steps[i]? = some (.gloas B') → j < i → B.RotQ D.paySlot D.payW b →
      OpsClear (gloasCtx ccfg bls) D.paySlot D.payW B'.postSlots B'.block.message → False := by
    intro b B B' hB hB' hlt hr hc
    rw [hB] at hB'; cases hB'
    exact rot_vs_live hr (opsClear_live hspe (hne hB hlt) hc)
  have rs : ∀ {b : Bool} {B B' : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      run.steps[i]? = some (.gloas B') → B.RotQ D.paySlot D.payW b →
      LiveAt D.paySlot D.payW B'.postSlots → False := by
    intro b B B' hB hB' hr hl
    rw [hB] at hB'; cases hB'
    exact rot_vs_live hr hl
  have sc : ∀ {B B' : GloasStepData (P := P) cfg ccfg bls}, i = j + 1 →
      run.steps[i]? = some (.gloas B) → run.steps[i]? = some (.gloas B') →
      parentFull B.postSlots B.block.message = true → LiveAt D.paySlot D.payW B.postSlots →
      OpsClear (gloasCtx ccfg bls) D.paySlot D.payW B'.postSlots B'.block.message → False := by
    intro B B' hi hB hB' hfull hl hc
    rw [hB] at hB'; cases hB'
    obtain ⟨C, hC, hpre⟩ := pred_step stepD hB (by omega)
    rw [hi, show j + 1 - 1 = j by omega, stepD] at hC; cases hC
    have hps : D.paySlot = B.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH := by
      rw [B.postSlots_lbh, hpre, D.postB_slot.2, paySlot_eq]
    exact (settle_excl hspe B.processBlock (hne hB (by omega)) hfull hps hl).1 hc
  cases f <;> cases g <;> simp only [PaymentFate.flipIdx?, Option.some.injEq, reduceCtorEq] at hfi hgi
  all_goals subst hfi; subst hgi
  all_goals first
    | rfl
    | exfalso
      first
        | (obtain ⟨_, B, hB, hr⟩ := hf; obtain ⟨_, ⟨B', hB', hr'⟩, -⟩ := hg
           rw [hB] at hB'; cases hB'; exact rotEval_unique _ _ hr hr')
        | (obtain ⟨_, ⟨B, hB, hr⟩, -⟩ := hf; obtain ⟨_, B', hB', hr'⟩ := hg
           rw [hB] at hB'; cases hB'; exact rotEval_unique _ _ hr' hr)
        | (obtain ⟨_, B, hB, hr⟩ := hf; obtain ⟨_, B', hB', -, hl⟩ := hg; exact rs hB hB' hr hl)
        | (obtain ⟨_, ⟨B, hB, hr⟩, -⟩ := hf; obtain ⟨_, B', hB', -, hl⟩ := hg; exact rs hB hB' hr hl)
        | (obtain ⟨_, B, hB, -, hl⟩ := hf; obtain ⟨_, B', hB', hr⟩ := hg; exact rs hB' hB hr hl)
        | (obtain ⟨_, B, hB, -, hl⟩ := hf; obtain ⟨_, ⟨B', hB', hr⟩, -⟩ := hg; exact rs hB' hB hr hl)
        | (obtain ⟨hlt, B, hB, hr⟩ := hf; obtain ⟨_, ⟨B', hB', hc⟩, -⟩ := hg; exact rc hB hB' hlt hr hc)
        | (obtain ⟨hlt, ⟨B, hB, hr⟩, -⟩ := hf; obtain ⟨_, ⟨B', hB', hc⟩, -⟩ := hg
           exact rc hB hB' hlt hr hc)
        | (obtain ⟨_, ⟨B', hB', hc⟩, -⟩ := hf; obtain ⟨hlt, B, hB, hr⟩ := hg; exact rc hB hB' hlt hr hc)
        | (obtain ⟨_, ⟨B', hB', hc⟩, -⟩ := hf; obtain ⟨hlt, ⟨B, hB, hr⟩, -⟩ := hg
           exact rc hB hB' hlt hr hc)
        | (obtain ⟨hi, B, hB, hfull, hl⟩ := hf; obtain ⟨_, ⟨B', hB', hc⟩, -⟩ := hg
           exact sc hi hB hB' hfull hl hc)
        | (obtain ⟨_, ⟨B', hB', hc⟩, -⟩ := hf; obtain ⟨hi, B, hB, hfull, hl⟩ := hg
           exact sc hi hB hB' hfull hl hc)

/-- The direct append ends the payment by the next step. -/
theorem direct_dead (hspe : 0 < P.SLOTS_PER_EPOCH) (stepD : run.steps[j]? = some (.gloas D))
    {D' : GloasStepData (P := P) cfg ccfg bls} (hD' : run.steps[j + 1]? = some (.gloas D'))
    (hnone : payIdx D.paySlot D'.postSlots = none) : ¬ LiveAt D.paySlot D.payW D'.postB :=
  fun hl => not_liveAt_of_none hnone (postB_to_postSlots hspe stepD hD' (by omega) hl)

/-- Liveness at the run's end reaches back to every step from the creating one. -/
theorem final_live (hspe : 0 < P.SLOTS_PER_EPOCH) (stepD : run.steps[j]? = some (.gloas D)) {b : Gloas.BeaconState P} {e : BlockChain}
    {p : ParentPayload P} (hsf : sf = .gloas b e p) (hl : LiveAt D.paySlot D.payW b) {i : Nat}
    {B : GloasStepData (P := P) cfg ccfg bls} (hB : run.steps[i]? = some (.gloas B)) (hji : j ≤ i) :
    LiveAt D.paySlot D.payW B.postB := by
  obtain ⟨n, Bn, -, hn, hBn, hsf'⟩ := final_of run stepD
  rw [hsf] at hsf'
  simp only [GJointState.gloas.injEq] at hsf'
  rw [hsf'.1] at hl
  have := (List.getElem?_eq_some_iff.mp hB).1
  exact live_chain' run hspe hB hBn (by omega) (paySlot_le stepD hB hji) hl

/-- The direct append or the end state against a destination that ends the payment at a step. -/
theorem none_vs_some (hspe : 0 < P.SLOTS_PER_EPOCH)
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (stepD : run.steps[j]? = some (.gloas D))
    (hinv : ∀ D' : GloasStepData (P := P) cfg ccfg bls, run.steps[j + 1]? = some (.gloas D') →
      NoLiveWeightOnLatestBid D'.preB ∧ FutureEmpty D'.preB)
    {f g : PaymentFate run j} (hgi : g.flipIdx? = none) (hg : g.holdsFor D) {i : Nat}
    (hfi : f.flipIdx? = some i) (hf : f.holdsFor D) : False := by
  obtain ⟨hji, ⟨B, hB, hn⟩, hm⟩ := flip_index hspe stepD hf hfi
  cases g <;> simp only [PaymentFate.flipIdx?, reduceCtorEq] at hgi
  · -- direct append
    obtain ⟨-, D', hD', hfull, hnone⟩ := hg
    have hdead := direct_dead hspe stepD hD' hnone
    cases f <;> simp only [PaymentFate.flipIdx?, Option.some.injEq, reduceCtorEq] at hfi
    · subst hfi
      obtain ⟨hlt, B₁, hB₁, hr⟩ := hf
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with heq | hlt'
      · rw [← heq, hD'] at hB₁; cases hB₁
        obtain ⟨C, hC, hpre⟩ := pred_step stepD hD' (by omega)
        rw [show j + 1 - 1 = j by omega, stepD] at hC; cases hC
        have hlat : LatestAt D.paySlot D'.preB := by
          obtain ⟨g7, fe⟩ := hinv D' hD'
          exact ⟨g7, fe, by rw [hpre, D.postB_bid]⟩
        exact no_quorum_latest hq hspe _ _ hlat hr
      · exact hdead (hm (j + 1) D' hD' (by omega) hlt')
    · subst hfi
      obtain ⟨rfl, B₁, hB₁, -, hl⟩ := hf
      rw [hD'] at hB₁; cases hB₁
      exact not_liveAt_of_none hnone hl
    · exact hf.2.2 ⟨D', hD', hfull, hnone⟩
    · exact hf.2.2 ⟨D', hD', hfull, hnone⟩
  · -- the end state
    obtain ⟨b, e, p, hsf, hl⟩ := hg
    exact hn (final_live hspe stepD hsf hl hB hji)

theorem none_none (hspe : 0 < P.SLOTS_PER_EPOCH) (stepD : run.steps[j]? = some (.gloas D)) {f g : PaymentFate run j}
    (hfi : f.flipIdx? = none) (hgi : g.flipIdx? = none) (hf : f.holdsFor D) (hg : g.holdsFor D) :
    f = g := by
  have dp : ∀ {j' : Nat}, (PaymentFate.directAppend j' : PaymentFate run j).holdsFor D →
      ¬ (PaymentFate.pendingAtEnd : PaymentFate run j).holdsFor D := by
    intro j' hd hp
    obtain ⟨-, D', hD', -, hnone⟩ := hd
    obtain ⟨b, e, p, hsf, hl⟩ := hp
    exact direct_dead hspe stepD hD' hnone (final_live hspe stepD hsf hl hD' (by omega))
  cases f <;> cases g <;> simp only [PaymentFate.flipIdx?, reduceCtorEq] at hfi hgi
  · obtain ⟨rfl, -⟩ := hf; obtain ⟨rfl, -⟩ := hg; rfl
  · exact (dp hf hg).elim
  · exact (dp hg hf).elim
  · rfl

/-- **Exclusivity.** -/
theorem fate_unique (hspe : 0 < P.SLOTS_PER_EPOCH)
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (stepD : run.steps[j]? = some (.gloas D))
    (hinv : ∀ D' : GloasStepData (P := P) cfg ccfg bls, run.steps[j + 1]? = some (.gloas D') →
      NoLiveWeightOnLatestBid D'.preB ∧ FutureEmpty D'.preB)
    {f g : PaymentFate run j} (hf : f.holdsFor D) (hg : g.holdsFor D) : f = g := by
  cases hfi : f.flipIdx? with
  | some i =>
    cases hgi : g.flipIdx? with
    | some i' =>
      obtain ⟨hj1, ⟨B, hB, hn⟩, hm⟩ := flip_index hspe stepD hf hfi
      obtain ⟨hj2, ⟨B', hB', hn'⟩, hm'⟩ := flip_index hspe stepD hg hgi
      have hii : i = i' := by
        rcases lt_trichotomy i i' with h | h | h
        · exact absurd (hm' i B hB hj1 h) hn
        · exact h
        · exact absurd (hm i' B' hB' hj2 h) hn'
      subst hii
      exact same_index hspe stepD hfi hgi hf hg
    | none => exact (none_vs_some hspe hq stepD hinv hgi hg hfi hf).elim
  | none =>
    cases hgi : g.flipIdx? with
    | some i' => exact (none_vs_some hspe hq stepD hinv hfi hf hgi hg).elim
    | none => exact none_none hspe stepD hfi hgi hf hg

/-- **B5(iii), run form: exactly one destination.** -/
theorem payment_fate_run (hspe : 0 < P.SLOTS_PER_EPOCH)
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) (hv : U64.zero < D.bid.value)
    (stepD : run.steps[j]? = some (.gloas D))
    (hinv : ∀ D' : GloasStepData (P := P) cfg ccfg bls, run.steps[j + 1]? = some (.gloas D') →
      NoLiveWeightOnLatestBid D'.preB ∧ FutureEmpty D'.preB) :
    ∃! f : PaymentFate run j, f.holds := by
  obtain ⟨f, hf⟩ := fate_exists hspe hv stepD
  refine ⟨f, ⟨D, stepD, hf⟩, fun g hg => ?_⟩
  obtain ⟨D', hD', hg⟩ := hg
  rw [stepD] at hD'; cases hD'
  exact fate_unique hspe hq stepD hinv hg hf

end Main

/-! ## Over a valid Gloas joint chain -/

/-- Some destination appends the payment's withdrawal at step `i`: a quorum rotation, the
settlement, or the old-parent direct append (the only appends of a payment, CL:1724-1726,
1799-1804, 1805-1814). -/
noncomputable def paymentAppendsAt {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf) (j : Nat)
    (D : GloasStepData (P := P) cfg ccfg bls) (i : Nat) : Nat := by
  classical
  exact (if (PaymentFate.quorum i : PaymentFate run j).holdsFor D then 1 else 0) +
    (if (PaymentFate.settled i : PaymentFate run j).holdsFor D then 1 else 0) +
    (if (PaymentFate.directAppend i : PaymentFate run j).holdsFor D then 1 else 0)

/-- **The number of appends of step `j`'s payment to `builder_pending_withdrawals` along the
run**: each appending destination, at each step. -/
noncomputable def paymentAppends {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf) (j : Nat)
    (D : GloasStepData (P := P) cfg ccfg bls) : Nat :=
  ((List.range run.steps.length).map (paymentAppendsAt run j D)).sum

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

theorem latest_inv (v : ValidJointG cfg ccfg bls checkpoint anchor final) {i : Nat}
    {D' : GloasStepData (P := P) cfg ccfg bls} (hD' : v.run.steps[i]? = some (.gloas D')) :
    NoLiveWeightOnLatestBid D'.preB ∧ FutureEmpty D'.preB := by
  obtain ⟨-, -, -, -, -, g7, -, -, fe⟩ := v.gInv_pre hD'
  exact ⟨g7, fe⟩

/-- **B5(iii): the fate of a run-created bid payment.** A Gloas step `j` whose bid pays
(`value > 0`) an external builder creates a payment with exactly one destination. -/
theorem payment_fate (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    (bid : U64.zero < D.bid.value ∧ D.bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD) :
    ∃! f : PaymentFate v.run j, f.holds :=
  payment_fate_run (by have := v.slotsPerEpoch; omega) v.quorumPositive bid.1 stepD
    (fun _ hD' => v.latest_inv hD')

/-- **B5(iii): at most one append.** Step `j`'s payment is appended to
`builder_pending_withdrawals` at most once along the run. -/
theorem payment_at_most_one_append (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    (_bid : U64.zero < D.bid.value ∧ D.bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD) :
    paymentAppends v.run j D ≤ 1 := by
  classical
  have hspe : 0 < P.SLOTS_PER_EPOCH := by have := v.slotsPerEpoch; omega
  have uq : ∀ {f g : PaymentFate v.run j}, f.holdsFor D → g.holdsFor D → f = g :=
    fun hf hg => fate_unique hspe v.quorumPositive stepD (fun _ hD' => v.latest_inv hD') hf hg
  -- at one step, at most one appending destination
  have le1 : ∀ i, paymentAppendsAt v.run j D i ≤ 1 := by
    intro i
    have n12 : ¬ ((PaymentFate.quorum i : PaymentFate v.run j).holdsFor D ∧
        (PaymentFate.settled i : PaymentFate v.run j).holdsFor D) := fun ⟨a, b⟩ => by
      have := uq a b; cases this
    have n13 : ¬ ((PaymentFate.quorum i : PaymentFate v.run j).holdsFor D ∧
        (PaymentFate.directAppend i : PaymentFate v.run j).holdsFor D) := fun ⟨a, b⟩ => by
      have := uq a b; cases this
    have n23 : ¬ ((PaymentFate.settled i : PaymentFate v.run j).holdsFor D ∧
        (PaymentFate.directAppend i : PaymentFate v.run j).holdsFor D) := fun ⟨a, b⟩ => by
      have := uq a b; cases this
    unfold paymentAppendsAt
    split_ifs <;> first
      | omega
      | exact absurd ⟨by assumption, by assumption⟩ n12
      | exact absurd ⟨by assumption, by assumption⟩ n13
      | exact absurd ⟨by assumption, by assumption⟩ n23
  -- an appending destination at a step
  have pos : ∀ i, 0 < paymentAppendsAt v.run j D i → ∃ f : PaymentFate v.run j, f.holdsFor D ∧
      (f = .quorum i ∨ f = .settled i ∨ f = .directAppend i) := by
    intro i h
    unfold paymentAppendsAt at h
    by_cases h1 : (PaymentFate.quorum i : PaymentFate v.run j).holdsFor D
    · exact ⟨_, h1, Or.inl rfl⟩
    by_cases h2 : (PaymentFate.settled i : PaymentFate v.run j).holdsFor D
    · exact ⟨_, h2, Or.inr (Or.inl rfl)⟩
    by_cases h3 : (PaymentFate.directAppend i : PaymentFate v.run j).holdsFor D
    · exact ⟨_, h3, Or.inr (Or.inr rfl)⟩
    simp only [h1, h2, h3, ite_false] at h
    omega
  have key : ∀ n, ((List.range n).map (paymentAppendsAt v.run j D)).sum ≤ 1 ∧
      (0 < ((List.range n).map (paymentAppendsAt v.run j D)).sum →
        ∃ i < n, 0 < paymentAppendsAt v.run j D i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      by_cases hz : paymentAppendsAt v.run j D n = 0
      · rw [hz, Nat.add_zero]
        exact ⟨ih.1, fun h => let ⟨i, hi, hp⟩ := ih.2 h; ⟨i, by omega, hp⟩⟩
      · have hn1 := le1 n
        have h0 : ((List.range n).map (paymentAppendsAt v.run j D)).sum = 0 := by
          by_contra hne
          obtain ⟨i, hi, hp⟩ := ih.2 (by omega)
          obtain ⟨f, hf, ef⟩ := pos i hp
          obtain ⟨g, hg, eg⟩ := pos n (by omega)
          have := uq hf hg
          subst this
          rcases ef with rfl | rfl | rfl <;> rcases eg with h | h | h <;> cases h <;> omega
        rw [h0]
        exact ⟨by omega, fun _ => ⟨n, by omega, by omega⟩⟩
  exact (key _).1

end ValidJointG

end Blanc.Lift.BuilderRequest
