import Blanc.Composition.BuilderRequestJointGPayments

/-!
# B5(iii), the anchor half: anchor entries, their fates, and the tracked-payment core

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B5 (iii), SF-4).

An entry pending at the anchor has no creating step in the run. `AnchorEntry a` names a non-empty
`builder_pending_payments[idx]` that is not the latest bid's live entry (`.payment idx`), a
`builder_pending_withdrawals[k]` (`.withdrawal k`), or the latest bid's payment (`.latestBid`).
`AnchorFate run e` has the frozen constructors; `AnchorFate.Allowed` restricts them by kind, and
`AnchorFate.holds` says what each means. A payment entry is tracked by its virtual slot (`payIdx`):
an entry at index `idx` of the anchor by `SLOTS_PER_EPOCH * epoch + idx`, the latest bid by its slot
plus one epoch. This module holds the definitions and the core (`AnchorTrack`: existence and
exclusivity for a tracked anchor payment); `BuilderRequestJointGPaymentsAnchor` holds the pending
withdrawals, the headline `ValidJointG.anchor_payment_fate` and `anchor_witness_charged_once`.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## The first step of a run -/

theorem _root_.Blanc.GJointRun.nil_end {s₀ : GJointState P} :
    {sf : GJointState P} → (run : GJointRun cfg ccfg bls s₀ sf) → run.steps = [] → sf = s₀
  | _, .nil, _ => rfl
  | _, .snoc run D _, h => by simp [GJointRun.steps] at h

theorem _root_.Blanc.GJointRun.first_pre {s₀ : GJointState P} :
    {sf : GJointState P} → (run : GJointRun cfg ccfg bls s₀ sf) →
    {C : GJointRunStep (P := P) cfg ccfg bls} → run.steps[0]? = some C → C.preState = s₀
  | _, .nil, _, h => by simp [GJointRun.steps] at h
  | _, .snoc run D hD, C, h => by
    rw [GJointRun.steps_snoc] at h
    by_cases hl : 0 < run.steps.length
    · rw [List.getElem?_append_left hl] at h
      exact GJointRun.first_pre run h
    · have h0 : run.steps = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [h0, List.nil_append] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [hD]
      exact GJointRun.nil_end run h0

section Core

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {sf : GJointState P}
  {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf}

theorem first_gloas {C : GJointRunStep (P := P) cfg ccfg bls} (h : run.steps[0]? = some C) :
    ∃ C', C = .gloas C' ∧ C'.preB = a := by
  have hp := run.first_pre h
  cases C with
  | pre C => simp [GJointRunStep.preState] at hp
  | crossing C => simp [GJointRunStep.preState] at hp
  | gloas C' =>
    simp only [GJointRunStep.preState, GJointState.gloas.injEq] at hp
    exact ⟨C', rfl, hp.1⟩

theorem anchor_step {i : Nat} (hi : i < run.steps.length) :
    ∃ B, run.steps[i]? = some (.gloas B) := by
  obtain ⟨C, hC⟩ : ∃ C, run.steps[0]? = some C := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨C', rfl, -⟩ := first_gloas hC
  have := gloas_from run hC i (by omega)
  simpa using this

theorem anchor_pred {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls}
    (hB : run.steps[i]? = some (.gloas B)) :
    (i = 0 ∧ B.preB = a) ∨ (0 < i ∧ ∃ C, run.steps[i - 1]? = some (.gloas C) ∧ B.preB = C.postB) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · obtain ⟨B', hB', hp⟩ := first_gloas hB
    cases hB'; exact Or.inl ⟨rfl, hp⟩
  · have hlen := (List.getElem?_eq_some_iff.mp hB).1
    obtain ⟨C, hC⟩ := anchor_step (run := run) (i := i - 1) (by omega)
    obtain ⟨B', hB', hpre⟩ := gloas_succ run hC (by rw [show i - 1 + 1 = i by omega]; exact hB)
    cases hB'
    exact Or.inr ⟨hpos, C, hC, hpre⟩

theorem anchor_slot_lt {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls}
    (hB : run.steps[i]? = some (.gloas B)) : a.slot.toNat < B.block.message.slot.toNat := by
  obtain ⟨B0, hB0⟩ := anchor_step (run := run) (i := 0)
    (by have := (List.getElem?_eq_some_iff.mp hB).1; omega)
  have h0 : a.slot.toNat < B0.block.message.slot.toNat := by
    rcases anchor_pred hB0 with ⟨-, hp⟩ | ⟨h, -⟩
    · rw [← hp]; exact B0.pre_lt
    · omega
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [hB0] at hB; cases hB; exact h0
  · have := slot_lt' run hB0 hB hpos; omega

/-- The old-parent branch of the run's first block appends the latest bid's withdrawal directly. -/
def DirectAnchor (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf) (vs : Nat) : Prop :=
  ∃ B, run.steps[0]? = some (.gloas B) ∧ parentFull B.postSlots B.block.message = true ∧
    payIdx vs B.postSlots = none

end Core

/-! ## Anchor entries and their fates -/

/-- **An entry pending at the anchor** (statements.md B5 (iii), anchor half). -/
inductive AnchorEntry (a : Gloas.BeaconState P) : Type
  /-- A non-empty `builder_pending_payments[idx]` that is not the latest bid's live entry. -/
  | payment (idx : Nat)
  /-- `builder_pending_withdrawals[k]`. -/
  | withdrawal (k : Nat)
  /-- The latest bid's payment, whether its entry is live or already empty. -/
  | latestBid

/-- The entry is one the anchor has (the payments entry is non-empty and not `L`'s live entry; the
withdrawals entry exists). -/
def AnchorEntry.Present {a : Gloas.BeaconState P} : AnchorEntry a → Prop
  | .payment idx => ∃ p, a.builder_pending_payments.toArray[idx]? = some p ∧
      p ≠ Gloas.BuilderPendingPayment.empty ∧
      ¬ (bidIndex a = some idx ∧ p.withdrawal = bidWithdrawal a.latest_execution_payload_bid)
  | .withdrawal k => k < a.builder_pending_withdrawals.toArray.size
  | .latestBid => True

/-- **The destinations of an anchor entry** (the frozen constructors; `Allowed` restricts them by
kind). -/
inductive AnchorFate {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P}
    {sf : GJointState P} (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf) (e : AnchorEntry a) : Type
  | quorum (j' : Nat)
  | droppedSubQuorum (j' : Nat)
  | clearedBySlash (j' : Nat)
  | pendingAtEnd
  | settled (j' : Nat)
  | directAppend (j' : Nat)
  | clearedAtAnchor
  | noPayment
  | paid (j' : Nat)
  | stillQueued

section Fates

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {sf : GJointState P}
  {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf}

/-- The constructors allowed for each kind: a non-`L` payment is appended at a quorum, dropped,
cleared or still pending; `L` additionally settled, directly appended, cleared at the anchor, or
no payment; a withdrawal is paid or still queued. -/
def AnchorFate.Allowed {e : AnchorEntry a} : AnchorFate run e → Prop
  | .quorum _ | .droppedSubQuorum _ | .clearedBySlash _ | .pendingAtEnd =>
    match e with
    | .withdrawal _ => False
    | _ => True
  | .settled _ | .directAppend _ | .clearedAtAnchor | .noPayment =>
    match e with
    | .latestBid => True
    | _ => False
  | .paid _ | .stillQueued =>
    match e with
    | .withdrawal _ => True
    | _ => False

/-- What a payment destination means for an entry tracked at virtual slot `vs` with withdrawal `w`;
`isL` marks the latest bid (only it is settled, directly appended, or cleared at the anchor). -/
def AnchorFate.holdsT {e : AnchorEntry a} (vs : Nat) (w : Gloas.BuilderPendingWithdrawal) (isL : Prop) :
    AnchorFate run e → Prop
  | .quorum j' => ∃ B, run.steps[j']? = some (.gloas B) ∧ B.RotQ vs w true
  | .droppedSubQuorum j' => (∃ B, run.steps[j']? = some (.gloas B) ∧ B.RotQ vs w false) ∧
      (isL → ¬ DirectAnchor run vs)
  | .clearedBySlash j' => (∃ B, run.steps[j']? = some (.gloas B) ∧
      OpsClear (gloasCtx ccfg bls) vs w B.postSlots B.block.message) ∧ (isL → ¬ DirectAnchor run vs)
  | .pendingAtEnd => ∃ b e p, sf = .gloas b e p ∧ LiveAt vs w b
  | .settled j' => isL ∧ j' = 0 ∧ ∃ B, run.steps[0]? = some (.gloas B) ∧
      parentFull B.postSlots B.block.message = true ∧ LiveAt vs w B.postSlots
  | .directAppend j' => isL ∧ j' = 0 ∧ DirectAnchor run vs
  | .clearedAtAnchor => isL ∧ ¬ LiveAt vs w a ∧ ¬ DirectAnchor run vs
  | .noPayment | .paid _ | .stillQueued => False

end Fates

/-! ## The fate of an anchor payment entry -/

theorem postSlots_to_preB' (hspe : 0 < P.SLOTS_PER_EPOCH) {vs : Nat} {w : Gloas.BuilderPendingWithdrawal}
    {B : GloasStepData (P := P) cfg ccfg bls}
    (hl : LiveAt vs w B.postSlots) : LiveAt vs w B.preB :=
  slotLoop_live_back hspe _ _ _ (processSlots_slotLoop B.slots).2 hl

section CoreFate

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {sf : GJointState P}
  {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf} {e : AnchorEntry a}
  {vs : Nat} {w : Gloas.BuilderPendingWithdrawal} {isL : Prop}

/-- The step at which a destination ends the entry, for those that do. -/
def AnchorFate.flipIdx? : AnchorFate run e → Option Nat
  | .quorum i | .droppedSubQuorum i | .clearedBySlash i | .settled i => some i
  | _ => none

/-- The hypotheses of the anchor core: positive amount, every run block after the entry's slot, the
settlement of the first block reads `L`'s slot only for `L`, and `L` is still the latest bid. -/
structure AnchorTrack (run : GJointRun cfg ccfg bls (GJointState.gloas a ex pa) sf) (vs : Nat)
    (w : Gloas.BuilderPendingWithdrawal) (isL : Prop) : Prop where
  hspe : 0 < P.SLOTS_PER_EPOCH
  hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT
  hvs : ∀ (i : Nat) (B : GloasStepData (P := P) cfg ccfg bls), run.steps[i]? = some (GJointRunStep.gloas B) →
    vs < B.block.message.slot.toNat + P.SLOTS_PER_EPOCH
  hL : isL → vs = a.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH
  hnotL : ¬ isL → vs ≠ a.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH
  hlat : isL → LatestAt vs a

variable (T : AnchorTrack run vs w isL)
include T

theorem AnchorTrack.back {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls}
    (hB : run.steps[i]? = some (.gloas B)) (hl : LiveAt vs w B.preB) :
    (∀ i' (B' : GloasStepData (P := P) cfg ccfg bls), run.steps[i']? = some (.gloas B') → i' < i →
      LiveAt vs w B'.postB) ∧ LiveAt vs w a := by
  rcases anchor_pred hB with ⟨rfl, hp⟩ | ⟨hpos, C, hC, hpre⟩
  · exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _), hp ▸ hl⟩
  · rw [hpre] at hl
    have hpost : ∀ i' (B' : GloasStepData (P := P) cfg ccfg bls), run.steps[i']? = some (.gloas B') →
        i' < i → LiveAt vs w B'.postB := fun i' B' hB' hi' =>
      live_chain' run T.hspe hB' hC (by omega) (T.hvs i' B' hB').le hl
    refine ⟨hpost, ?_⟩
    obtain ⟨B0, hB0⟩ := anchor_step (run := run) (i := 0)
      (by have := (List.getElem?_eq_some_iff.mp hB).1; omega)
    have h0 := B0.live_back T.hspe (T.hvs 0 B0 hB0) (hpost 0 B0 hB0 hpos)
    rcases anchor_pred hB0 with ⟨-, hp⟩ | ⟨h, -⟩
    · exact hp ▸ h0
    · omega

theorem AnchorTrack.postB_to_postSlots {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls}
    (hB : run.steps[i]? = some (.gloas B)) (hl : LiveAt vs w B.postB) : LiveAt vs w B.postSlots :=
  (block_track T.hspe B.processBlock (by have := T.hvs i B hB; omega)).1 hl

theorem AnchorTrack.flip_index {f : AnchorFate run e} (hf : f.holdsT vs w isL) {i : Nat}
    (hi : f.flipIdx? = some i) :
    (∃ B, run.steps[i]? = some (.gloas B) ∧ ¬ LiveAt vs w B.postB) ∧
      (∀ i' (B' : GloasStepData (P := P) cfg ccfg bls), run.steps[i']? = some (.gloas B') → i' < i →
        LiveAt vs w B'.postB) ∧ LiveAt vs w a := by
  have rot : ∀ {b : Bool} {B : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      B.RotQ vs w b → (∃ B, run.steps[i]? = some (.gloas B) ∧ ¬ LiveAt vs w B.postB) ∧
      (∀ i' (B' : GloasStepData (P := P) cfg ccfg bls), run.steps[i']? = some (.gloas B') → i' < i →
        LiveAt vs w B'.postB) ∧ LiveAt vs w a := fun hB hr =>
    ⟨⟨_, hB, fun hl => not_liveAt_of_none (GloasStepData.rotQ_end _ hr) (T.postB_to_postSlots hB hl)⟩,
      T.back hB (rotEval_live T.hspe _ _ hr)⟩
  cases f <;> simp only [AnchorFate.flipIdx?, Option.some.injEq, reduceCtorEq] at hi <;> subst hi
  · obtain ⟨B, hB, hr⟩ := hf; exact rot hB hr
  · obtain ⟨⟨B, hB, hr⟩, -⟩ := hf; exact rot hB hr
  · obtain ⟨⟨B, hB, hc⟩, -⟩ := hf
    exact ⟨⟨B, hB, opsClear_end B.processBlock hc⟩, T.back hB (postSlots_to_preB' T.hspe
      (opsClear_live T.hspe (by have := T.hvs _ B hB; omega) hc))⟩
  · obtain ⟨hL, rfl, B, hB, hfull, hl⟩ := hf
    have hpre : B.preB = a := by
      rcases anchor_pred hB with ⟨-, hp⟩ | ⟨h, -⟩
      · exact hp
      · omega
    have hps : vs = B.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH := by
      rw [B.postSlots_lbh, hpre]; exact T.hL hL
    exact ⟨⟨B, hB, (settle_excl T.hspe B.processBlock (by have := T.hvs 0 B hB; omega) hfull hps
      hl).2⟩, T.back hB (postSlots_to_preB' T.hspe hl)⟩

theorem AnchorTrack.final_live {b : Gloas.BeaconState P} {e' : BlockChain} {p : ParentPayload P}
    (hsf : sf = .gloas b e' p) (hl : LiveAt vs w b) :
    (∀ (i : Nat) (B : GloasStepData (P := P) cfg ccfg bls), run.steps[i]? = some (.gloas B) →
      LiveAt vs w B.postB) ∧ LiveAt vs w a := by
  by_cases hn : run.steps = []
  · have h := run.nil_end hn
    rw [hsf] at h
    simp only [GJointState.gloas.injEq] at h
    refine ⟨fun i B hB => by simp [hn] at hB, h.1 ▸ hl⟩
  · obtain ⟨B0, hB0⟩ := anchor_step (run := run) (i := 0) (List.length_pos_iff.mpr hn)
    obtain ⟨n, Bn, -, hlen, hBn, hsf'⟩ := final_of run hB0
    rw [hsf] at hsf'
    simp only [GJointState.gloas.injEq] at hsf'
    rw [hsf'.1] at hl
    have hall : ∀ (i : Nat) (B : GloasStepData (P := P) cfg ccfg bls), run.steps[i]? = some (.gloas B) →
        LiveAt vs w B.postB := fun i B hB => by
      have := (List.getElem?_eq_some_iff.mp hB).1
      exact live_chain' run T.hspe hB hBn (by omega) (T.hvs i B hB).le hl
    refine ⟨hall, ?_⟩
    have h0 := B0.live_back T.hspe (T.hvs 0 B0 hB0) (hall 0 B0 hB0)
    rcases anchor_pred hB0 with ⟨-, hp⟩ | ⟨h, -⟩
    · exact hp ▸ h0
    · omega

theorem AnchorTrack.direct_dead (hd : DirectAnchor run vs) {B : GloasStepData (P := P) cfg ccfg bls}
    (hB : run.steps[0]? = some (.gloas B)) : ¬ LiveAt vs w B.postB := by
  obtain ⟨B', hB', -, hnone⟩ := hd
  rw [hB] at hB'; cases hB'
  exact fun hl => not_liveAt_of_none hnone (T.postB_to_postSlots hB hl)

/-- **Some destination holds** for a live anchor payment. -/
theorem AnchorTrack.exists_live (hl : LiveAt vs w a) : ∃ f : AnchorFate run e, f.holdsT vs w isL := by
  classical
  by_cases hd : isL ∧ DirectAnchor run vs
  · exact ⟨.directAppend 0, hd.1, rfl, hd.2⟩
  have hnd : isL → ¬ DirectAnchor run vs := fun h h' => hd ⟨h, h'⟩
  by_cases hall : ∀ (i : Nat) (B : GloasStepData (P := P) cfg ccfg bls), run.steps[i]? = some (.gloas B) →
      LiveAt vs w B.postB
  · by_cases hn : run.steps = []
    · exact ⟨.pendingAtEnd, a, ex, pa, run.nil_end hn, hl⟩
    · obtain ⟨B0, hB0⟩ := anchor_step (run := run) (i := 0) (List.length_pos_iff.mpr hn)
      obtain ⟨n, B, -, -, hB, hsf⟩ := final_of run hB0
      exact ⟨.pendingAtEnd, B.postB, B.postExec, B.postParent, hsf, hall n B hB⟩
  have hex : ∃ i : Nat, ∃ B : GloasStepData (P := P) cfg ccfg bls, run.steps[i]? = some (.gloas B) ∧
      ¬ LiveAt vs w B.postB := by
    push Not at hall
    exact hall
  obtain ⟨i, ⟨B, hB, hn⟩, hmin⟩ : ∃ i : Nat, (∃ B : GloasStepData (P := P) cfg ccfg bls,
      run.steps[i]? = some (.gloas B) ∧ ¬ LiveAt vs w B.postB) ∧
      ∀ i' < i, ¬ ∃ B : GloasStepData (P := P) cfg ccfg bls,
        run.steps[i']? = some (.gloas B) ∧ ¬ LiveAt vs w B.postB :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i' h => Nat.find_min hex h⟩
  have hpre : LiveAt vs w B.preB := by
    rcases anchor_pred hB with ⟨-, hp⟩ | ⟨hpos, C, hC, hp⟩
    · rw [hp]; exact hl
    · rw [hp]
      by_contra hc
      exact hmin (i - 1) (by omega) ⟨C, hC, hc⟩
  rcases B.flip_cases T.hspe (T.hvs i B hB) hpre hn with h | h | ⟨hf, hps, hl'⟩ | h
  · exact ⟨.quorum i, B, hB, h⟩
  · exact ⟨.droppedSubQuorum i, ⟨B, hB, h⟩, hnd⟩
  · rcases anchor_pred hB with ⟨rfl, hp⟩ | ⟨hpos, C, hC, hp⟩
    · rw [B.postSlots_lbh, hp] at hps
      by_cases hL : isL
      · exact ⟨.settled 0, hL, rfl, B, hB, hf, hl'⟩
      · exact absurd hps (T.hnotL hL)
    · rw [B.postSlots_lbh, hp, C.postB_slot.2] at hps
      have := T.hvs (i - 1) C hC
      omega
  · exact ⟨.clearedBySlash i, ⟨B, hB, h⟩, hnd⟩

omit T in
/-- **Some destination holds** for `L` when its entry is not live at the anchor. -/
theorem AnchorTrack.exists_dead (hL : isL) (hn : ¬ LiveAt vs w a) :
    ∃ f : AnchorFate run e, f.holdsT vs w isL := by
  by_cases hd : DirectAnchor run vs
  · exact ⟨.directAppend 0, hL, rfl, hd⟩
  · exact ⟨.clearedAtAnchor, hL, hn, hd⟩

/-- Two destinations ending the entry at the same step are the same. -/
theorem AnchorTrack.same_index {f g : AnchorFate run e} {i : Nat} (hfi : f.flipIdx? = some i)
    (hgi : g.flipIdx? = some i) (hf : f.holdsT vs w isL) (hg : g.holdsT vs w isL) : f = g := by
  have hne : ∀ {B : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      vs ≠ B.block.message.slot.toNat + P.SLOTS_PER_EPOCH := fun {B} hB => by
    have := T.hvs i B hB; omega
  have rv : ∀ {b : Bool} {B : GloasStepData (P := P) cfg ccfg bls}, B.RotQ vs w b →
      LiveAt vs w B.postSlots → False := fun hr hl => not_liveAt_of_none (GloasStepData.rotQ_end _ hr) hl
  have rc : ∀ {b : Bool} {B B' : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      run.steps[i]? = some (.gloas B') → B.RotQ vs w b →
      OpsClear (gloasCtx ccfg bls) vs w B'.postSlots B'.block.message → False := by
    intro b B B' hB hB' hr hc
    rw [hB] at hB'; cases hB'
    exact rv hr (opsClear_live T.hspe (hne hB) hc)
  have rs : ∀ {b : Bool} {B B' : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      run.steps[i]? = some (.gloas B') → B.RotQ vs w b → LiveAt vs w B'.postSlots → False := by
    intro b B B' hB hB' hr hl
    rw [hB] at hB'; cases hB'
    exact rv hr hl
  have sc : ∀ {B B' : GloasStepData (P := P) cfg ccfg bls}, isL → i = 0 →
      run.steps[i]? = some (.gloas B) → run.steps[i]? = some (.gloas B') →
      parentFull B.postSlots B.block.message = true → LiveAt vs w B.postSlots →
      OpsClear (gloasCtx ccfg bls) vs w B'.postSlots B'.block.message → False := by
    intro B B' hL hi hB hB' hfull hl hc
    rw [hB] at hB'; cases hB'
    subst hi
    have hpre : B.preB = a := by
      rcases anchor_pred hB with ⟨-, hp⟩ | ⟨h, -⟩
      · exact hp
      · omega
    have hps : vs = B.postSlots.latest_block_header.slot.toNat + P.SLOTS_PER_EPOCH := by
      rw [B.postSlots_lbh, hpre]; exact T.hL hL
    exact (settle_excl T.hspe B.processBlock (hne hB) hfull hps hl).1 hc
  cases f <;> cases g <;> simp only [AnchorFate.flipIdx?, Option.some.injEq, reduceCtorEq] at hfi hgi
  all_goals subst hfi; subst hgi
  all_goals first
    | rfl
    | exfalso
      first
        | (obtain ⟨B, hB, hr⟩ := hf; obtain ⟨⟨B', hB', hr'⟩, -⟩ := hg
           rw [hB] at hB'; cases hB'; exact rotEval_unique _ _ hr hr')
        | (obtain ⟨⟨B, hB, hr⟩, -⟩ := hf; obtain ⟨B', hB', hr'⟩ := hg
           rw [hB] at hB'; cases hB'; exact rotEval_unique _ _ hr' hr)
        | (obtain ⟨B, hB, hr⟩ := hf; obtain ⟨-, rfl, B', hB', -, hl⟩ := hg; exact rs hB hB' hr hl)
        | (obtain ⟨⟨B, hB, hr⟩, -⟩ := hf; obtain ⟨-, rfl, B', hB', -, hl⟩ := hg; exact rs hB hB' hr hl)
        | (obtain ⟨-, rfl, B, hB, -, hl⟩ := hf; obtain ⟨B', hB', hr⟩ := hg; exact rs hB' hB hr hl)
        | (obtain ⟨-, rfl, B, hB, -, hl⟩ := hf; obtain ⟨⟨B', hB', hr⟩, -⟩ := hg; exact rs hB' hB hr hl)
        | (obtain ⟨B, hB, hr⟩ := hf; obtain ⟨⟨B', hB', hc⟩, -⟩ := hg; exact rc hB hB' hr hc)
        | (obtain ⟨⟨B, hB, hr⟩, -⟩ := hf; obtain ⟨⟨B', hB', hc⟩, -⟩ := hg; exact rc hB hB' hr hc)
        | (obtain ⟨⟨B', hB', hc⟩, -⟩ := hf; obtain ⟨B, hB, hr⟩ := hg; exact rc hB hB' hr hc)
        | (obtain ⟨⟨B', hB', hc⟩, -⟩ := hf; obtain ⟨⟨B, hB, hr⟩, -⟩ := hg; exact rc hB hB' hr hc)
        | (obtain ⟨hL, hi, B, hB, hfull, hl⟩ := hf; obtain ⟨⟨B', hB', hc⟩, -⟩ := hg
           subst hi; exact sc hL rfl hB hB' hfull hl hc)
        | (obtain ⟨⟨B', hB', hc⟩, -⟩ := hf; obtain ⟨hL, hi, B, hB, hfull, hl⟩ := hg
           subst hi; exact sc hL rfl hB hB' hfull hl hc)

theorem AnchorTrack.none_vs_some {f g : AnchorFate run e} (hgi : g.flipIdx? = none) (hg : g.holdsT vs w isL)
    {i : Nat} (hfi : f.flipIdx? = some i) (hf : f.holdsT vs w isL) : False := by
  obtain ⟨⟨B, hB, hn⟩, hm, ha⟩ := T.flip_index hf hfi
  cases g <;> simp only [AnchorFate.flipIdx?, reduceCtorEq] at hgi <;> simp only [AnchorFate.holdsT] at hg
  · obtain ⟨b, e', p, hsf, hl⟩ := hg
    exact hn ((T.final_live hsf hl).1 i B hB)
  · obtain ⟨hL, -, hd⟩ := hg
    obtain ⟨B0, hB0, -, hnone⟩ := id hd
    have hdead := T.direct_dead hd hB0
    cases f <;> simp only [AnchorFate.flipIdx?, Option.some.injEq, reduceCtorEq] at hfi
    · obtain ⟨B₁, hB₁, hr⟩ := hf
      rw [hfi] at hB₁
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hB0] at hB₁; cases hB₁
        have hpre : B0.preB = a := by
          rcases anchor_pred hB0 with ⟨-, hp⟩ | ⟨h, -⟩
          · exact hp
          · omega
        exact no_quorum_latest T.hq T.hspe _ _ (hpre ▸ T.hlat hL) hr
      · exact hdead (hm 0 B0 hB0 hpos)
    · exact hf.2 hL hd
    · exact hf.2 hL hd
    · obtain ⟨-, rfl, B₁, hB₁, -, hl⟩ := hf
      rw [hB0] at hB₁; cases hB₁
      exact not_liveAt_of_none hnone hl
  · exact hg.2.1 ha

theorem AnchorTrack.none_none {f g : AnchorFate run e} (hfi : f.flipIdx? = none) (hgi : g.flipIdx? = none)
    (hf : f.holdsT vs w isL) (hg : g.holdsT vs w isL) : f = g := by
  have pd : (AnchorFate.pendingAtEnd : AnchorFate run e).holdsT vs w isL →
      ¬ (AnchorFate.directAppend 0 : AnchorFate run e).holdsT vs w isL := by
    rintro ⟨b, e', p, hsf, hl⟩ ⟨-, -, hd⟩
    obtain ⟨B0, hB0, -⟩ := id hd
    exact T.direct_dead hd hB0 ((T.final_live hsf hl).1 0 B0 hB0)
  have pc : (AnchorFate.pendingAtEnd : AnchorFate run e).holdsT vs w isL →
      ¬ (AnchorFate.clearedAtAnchor : AnchorFate run e).holdsT vs w isL := by
    rintro ⟨b, e', p, hsf, hl⟩ ⟨-, hn, -⟩
    exact hn (T.final_live hsf hl).2
  cases f <;> cases g <;> simp only [AnchorFate.flipIdx?, reduceCtorEq] at hfi hgi <;>
    simp only [AnchorFate.holdsT] at hf hg
  all_goals first
    | rfl
    | (obtain ⟨-, rfl, -⟩ := hf; obtain ⟨-, rfl, -⟩ := hg; rfl)
    | (obtain ⟨hL, rfl, hd⟩ := hg; exact (pd hf ⟨hL, rfl, hd⟩).elim)
    | (obtain ⟨hL, rfl, hd⟩ := hf; exact (pd hg ⟨hL, rfl, hd⟩).elim)
    | exact (pc hf hg).elim
    | exact (pc hg hf).elim
    | exact (hg.2.2 hf.2.2).elim
    | exact (hf.2.2 hg.2.2).elim

/-- **Exclusivity** for an anchor payment entry. -/
theorem AnchorTrack.unique {f g : AnchorFate run e} (hf : f.holdsT vs w isL) (hg : g.holdsT vs w isL) :
    f = g := by
  cases hfi : f.flipIdx? with
  | some i =>
    cases hgi : g.flipIdx? with
    | some i' =>
      obtain ⟨⟨B, hB, hn⟩, hm, -⟩ := T.flip_index hf hfi
      obtain ⟨⟨B', hB', hn'⟩, hm', -⟩ := T.flip_index hg hgi
      have hii : i = i' := by
        rcases lt_trichotomy i i' with h | h | h
        · exact absurd (hm' i B hB h) hn
        · exact h
        · exact absurd (hm i' B' hB' h) hn'
      subst hii
      exact T.same_index hfi hgi hf hg
    | none => exact (T.none_vs_some hgi hg hfi hf).elim
  | none =>
    cases hgi : g.flipIdx? with
    | some i' => exact (T.none_vs_some hfi hf hgi hg).elim
    | none => exact T.none_none hfi hgi hf hg

end CoreFate

end Blanc.Lift.BuilderRequest
