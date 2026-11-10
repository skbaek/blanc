import Blanc.Composition.BuilderRequestJointGPayments

/-!
# B5(iii), the anchor half: the fate of every entry pending at a Gloas anchor

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B5 (iii), SF-4).

An entry pending at the anchor has no creating step in the run. `AnchorEntry a` names a non-empty
`builder_pending_payments[idx]` that is not the latest bid's live entry (`.payment idx`), a
`builder_pending_withdrawals[k]` (`.withdrawal k`), or the latest bid's payment (`.latestBid`).
`AnchorFate run e` has the frozen constructors; `AnchorFate.Allowed` restricts them by kind, and
`AnchorFate.holds` says what each means. A payment entry is tracked by its virtual slot (`payIdx`):
an entry at index `idx` of the anchor by `SLOTS_PER_EPOCH * epoch + idx`, the latest bid by its slot
plus one epoch.
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

/-! ## Pending withdrawals: position in the queue -/

section Queue

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {sf : GJointState P}

/-- **The step's `process_withdrawals` removes the first `d` builder pending withdrawals** of the
queue it reads (the entries `get_builder_withdrawals` took, CL:2084-2086). -/
def _root_.Blanc.GloasStepData.Drops (B : GloasStepData (P := P) cfg ccfg bls) (d : Nat) : Prop :=
  ∃ s1 s2 s3 : Gloas.BeaconState P,
    Gloas.processParentExecutionPayload (gloasCtx ccfg bls) B.postSlots B.block.message = .ok s1 ∧
    Gloas.processBlockHeader s1 B.block.message = .ok s2 ∧ Gloas.processWithdrawals s2 = .ok s3 ∧
    s3.builder_pending_withdrawals.toArray.toList = s2.builder_pending_withdrawals.toArray.toList.drop d ∧
    d ≤ s2.builder_pending_withdrawals.toArray.toList.length

theorem _root_.Blanc.GloasStepData.drops_exists (B : GloasStepData (P := P) cfg ccfg bls) :
    ∃ d, B.Drops d := by
  obtain ⟨s1, s2, s3, -, -, -, -, h1, h2, h3, -⟩ := processBlock_phases B.processBlock
  obtain ⟨⟨k, hk⟩, -⟩ := processWithdrawals_wq h3
  refine ⟨min k s2.builder_pending_withdrawals.toArray.toList.length, s1, s2, s3, h1, h2, h3, ?_,
    Nat.min_le_right _ _⟩
  rw [hk]
  rcases Nat.le_total k s2.builder_pending_withdrawals.toArray.toList.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le h, List.drop_length]

theorem _root_.Blanc.GloasStepData.drops_unique (B : GloasStepData (P := P) cfg ccfg bls) {d d' : Nat}
    (h : B.Drops d) (h' : B.Drops d') : d = d' := by
  obtain ⟨s1, s2, s3, h1, h2, h3, e, hle⟩ := h
  obtain ⟨t1, t2, t3, g1, g2, g3, e', hle'⟩ := h'
  rw [h1] at g1; cases g1
  rw [h2] at g2; cases g2
  rw [h3] at g3; cases g3
  have := congrArg List.length e
  have := congrArg List.length e'
  simp only [List.length_drop] at *
  omega

/-- **The position of the anchor's `builder_pending_withdrawals[k]` before step `i`**: `k` at the
anchor, then less what each step's `process_withdrawals` removed ahead of it. -/
def TrackPos (run : GJointRun cfg ccfg bls (.gloas a ex pa) sf) (k : Nat) : Nat → Nat → Prop
  | 0, p => p = k
  | i + 1, p' => ∃ p, ∃ B : GloasStepData (P := P) cfg ccfg bls, ∃ d, TrackPos run k i p ∧
      run.steps[i]? = some (.gloas B) ∧ B.Drops d ∧ d ≤ p ∧ p' = p - d

variable {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf} {k : Nat}

theorem trackPos_fun : ∀ {i p p' : Nat}, TrackPos run k i p → TrackPos run k i p' → p = p'
  | 0, p, p', h, h' => (h : p = k).trans (h' : p' = k).symm
  | i + 1, _, _, h, h' => by
    obtain ⟨q, B, d, hq, hB, hd, -, rfl⟩ := h
    obtain ⟨q', B', d', hq', hB', hd', -, rfl⟩ := h'
    rw [hB] at hB'; cases hB'
    rw [trackPos_fun hq hq', B.drops_unique hd hd']

theorem trackPos_prev : ∀ {i p : Nat}, TrackPos run k i p → ∀ j, j ≤ i → ∃ q, TrackPos run k j q
  | 0, p, h, j, hj => ⟨p, by rw [show j = 0 by omega]; exact h⟩
  | i + 1, p, h, j, hj => by
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact ⟨p, h⟩
    · obtain ⟨q, -, -, hq, -⟩ := h
      exact trackPos_prev hq j (by omega)

end Queue

/-! ## The anchor entries of a valid joint chain -/

section Headline

variable {a : Gloas.BeaconState P} {ex : BlockChain} {pa : ParentPayload P} {checkpoint : BlockChain}
  {final : GJointState P}

/-- The latest bid pays: a positive value from an external builder. -/
def LatestPays (a : Gloas.BeaconState P) : Prop :=
  U64.zero < a.latest_execution_payload_bid.value ∧
    a.latest_execution_payload_bid.builder_index ≠ Gloas.BUILDER_INDEX_SELF_BUILD

/-- The virtual slot of the anchor's payments entry at index `idx`. -/
def anchorVs (a : Gloas.BeaconState P) (idx : Nat) : Nat := P.SLOTS_PER_EPOCH * curEpoch a + idx

theorem payIdx_anchorVs (hspe : 0 < P.SLOTS_PER_EPOCH) {idx : Nat} (hidx : idx < 2 * P.SLOTS_PER_EPOCH) :
    payIdx (anchorVs a idx) a = some idx := by
  unfold payIdx anchorVs
  by_cases h : P.SLOTS_PER_EPOCH ≤ idx
  · have e1 : (P.SLOTS_PER_EPOCH * curEpoch a + idx) / P.SLOTS_PER_EPOCH = curEpoch a + 1 := by
      rw [show P.SLOTS_PER_EPOCH * curEpoch a + idx =
        (idx - P.SLOTS_PER_EPOCH) + P.SLOTS_PER_EPOCH * (curEpoch a + 1) by rw [Nat.mul_add]; omega]
      rw [Nat.add_mul_div_left _ _ hspe, Nat.div_eq_of_lt (by omega)]; omega
    have e2 : (P.SLOTS_PER_EPOCH * curEpoch a + idx) % P.SLOTS_PER_EPOCH = idx - P.SLOTS_PER_EPOCH := by
      rw [show P.SLOTS_PER_EPOCH * curEpoch a + idx =
        (idx - P.SLOTS_PER_EPOCH) + P.SLOTS_PER_EPOCH * (curEpoch a + 1) by rw [Nat.mul_add]; omega]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_left e1, e2]; congr 1; omega
  · have e1 : (P.SLOTS_PER_EPOCH * curEpoch a + idx) / P.SLOTS_PER_EPOCH = curEpoch a := by
      rw [show P.SLOTS_PER_EPOCH * curEpoch a + idx = idx + P.SLOTS_PER_EPOCH * curEpoch a by omega]
      rw [Nat.add_mul_div_left _ _ hspe, Nat.div_eq_of_lt (by omega)]; omega
    have e2 : (P.SLOTS_PER_EPOCH * curEpoch a + idx) % P.SLOTS_PER_EPOCH = idx := by
      rw [show P.SLOTS_PER_EPOCH * curEpoch a + idx = idx + P.SLOTS_PER_EPOCH * curEpoch a by omega]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_right (by omega), ite_eq_left e1, e2]

/-- A step's settled parent is older than its block. -/
theorem _root_.Blanc.GloasStepData.lbh_lt (D : GloasStepData (P := P) cfg ccfg bls) :
    D.postSlots.latest_block_header.slot.toNat < D.block.message.slot.toNat := by
  obtain ⟨s1, s2, -, -, -, -, -, h1, h2, -⟩ := processBlock_phases D.processBlock
  have hlt := processBlockHeader_lt h2
  rcases processParentExecutionPayload_cases h1 with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact hlt
  · rw [(parentFull_frame ha hd he hs).2.2.2.2.1] at hlt; exact hlt

/-- What a withdrawal destination means for the anchor's `builder_pending_withdrawals[k]`. -/
def AnchorFate.holdsW {sf : GJointState P} {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf}
    {e : AnchorEntry a} (k : Nat) : AnchorFate run e → Prop
  | .paid j' => ∃ p, ∃ B : GloasStepData (P := P) cfg ccfg bls, ∃ d, TrackPos run k j' p ∧
      run.steps[j']? = some (.gloas B) ∧ B.Drops d ∧ p < d
  | .stillQueued => ∃ p, TrackPos run k run.steps.length p
  | _ => False

/-- What an anchor entry's destination means. -/
def AnchorFate.holds {sf : GJointState P} {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf}
    {e : AnchorEntry a} (f : AnchorFate run e) : Prop :=
  match e with
  | .payment idx => ∃ p, a.builder_pending_payments.toArray[idx]? = some p ∧
      f.holdsT (anchorVs a idx) p.withdrawal False
  | .latestBid => (LatestPays a ∧ f.holdsT (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)
        (bidWithdrawal a.latest_execution_payload_bid) True) ∨
      (¬ LatestPays a ∧ f = .noPayment)
  | .withdrawal k => f.holdsW k

section WithdrawalFate

variable {sf : GJointState P} {run : GJointRun cfg ccfg bls (.gloas a ex pa) sf} {k : Nat}

theorem not_paid_of_later {j i q : Nat}
    (hp : (AnchorFate.paid j : AnchorFate run (.withdrawal k)).holdsW k) (hq : TrackPos run k i q)
    (hji : j < i) : False := by
  obtain ⟨p, B, d, hpj, hB, hd, hlt⟩ := hp
  obtain ⟨q', hq'⟩ := trackPos_prev hq (j + 1) (by omega)
  obtain ⟨p', B', d', hp', hB', hd', hle, -⟩ := hq'
  rw [hB] at hB'; cases hB'
  rw [trackPos_fun hp' hpj, B.drops_unique hd' hd] at hle
  omega

/-- **The fate of an anchor pending withdrawal**: removed by exactly one step's
`process_withdrawals`, or still queued at the end. -/
theorem withdrawal_fate : ∃! f : AnchorFate run (.withdrawal k), f.Allowed ∧ f.holdsW k := by
  have key : ∀ i, i ≤ run.steps.length →
      (∃ j < i, (AnchorFate.paid j : AnchorFate run (.withdrawal k)).holdsW k) ∨
        ∃ p, TrackPos run k i p := by
    intro i
    induction i with
    | zero => exact fun _ => Or.inr ⟨k, rfl⟩
    | succ i ih =>
      intro hi
      rcases ih (by omega) with ⟨j, hj, hp⟩ | ⟨p, hp⟩
      · exact Or.inl ⟨j, by omega, hp⟩
      · obtain ⟨B, hB⟩ := anchor_step (run := run) (i := i) (by omega)
        obtain ⟨d, hd⟩ := B.drops_exists
        by_cases hdp : d ≤ p
        · exact Or.inr ⟨p - d, p, B, d, hp, hB, hd, hdp, rfl⟩
        · exact Or.inl ⟨i, by omega, p, B, d, hp, hB, hd, by omega⟩
  rcases key run.steps.length le_rfl with ⟨j, hj, hp⟩ | ⟨p, hp⟩
  · refine ⟨.paid j, ⟨trivial, hp⟩, fun g hg' => ?_⟩
    obtain ⟨-, hg⟩ := hg'
    cases g
    all_goals try exact (hg : False).elim
    · rename_i j'
      rcases lt_trichotomy j j' with h | rfl | h
      · obtain ⟨q, -, -, hq, -⟩ := hg
        exact (not_paid_of_later hp hq h).elim
      · rfl
      · obtain ⟨q, -, -, hq, -⟩ := hp
        exact (not_paid_of_later hg hq h).elim
    · obtain ⟨q, hq⟩ := hg
      exact (not_paid_of_later hp hq hj).elim
  · refine ⟨.stillQueued, ⟨trivial, p, hp⟩, fun g hg' => ?_⟩
    obtain ⟨-, hg⟩ := hg'
    cases g
    all_goals try exact (hg : False).elim
    · rename_i j'
      have hj' : j' < run.steps.length := by
        obtain ⟨_, _, _, _, hB, _⟩ := hg
        exact (List.getElem?_eq_some_iff.mp hB).1
      exact (not_paid_of_later hg hp hj').elim
    · rfl

end WithdrawalFate

/-- **B5(iii), the anchor half: every entry pending at a Gloas anchor has exactly one destination
of its kind.** -/
theorem ValidJointG.anchor_payment_fate (v : ValidJointG cfg ccfg bls checkpoint (.gloas a ex pa) final)
    (e : AnchorEntry a) (he : e.Present) : ∃! f : AnchorFate v.run e, f.Allowed ∧ f.holds := by
  have hspe : 0 < P.SLOTS_PER_EPOCH := by have := v.slotsPerEpoch; omega
  have hinv : GAnchorInv (GJointState.gloas a ex pa) := v.anchorInv
  obtain ⟨-, -, -, -, -, g7, g8, -, fe⟩ := hinv
  have hLs : a.latest_execution_payload_bid.slot.toNat = a.latest_block_header.slot.toNat := by
    rw [g8.1]
  cases e with
  | payment idx =>
    obtain ⟨p, hp, hne, hnotL⟩ := he
    have hidx : idx < 2 * P.SLOTS_PER_EPOCH := by
      have := (Array.getElem?_eq_some_iff.mp hp).1
      rwa [a.builder_pending_payments.size_eq] at this
    have hpi := payIdx_anchorVs (a := a) hspe hidx
    have hvsle : anchorVs a idx ≤ a.slot.toNat + P.SLOTS_PER_EPOCH := by
      have hdm := Nat.div_add_mod a.slot.toNat P.SLOTS_PER_EPOCH
      unfold anchorVs curEpoch
      by_cases h : P.SLOTS_PER_EPOCH ≤ idx
      · have : idx - P.SLOTS_PER_EPOCH ≤ a.slot.toNat % P.SLOTS_PER_EPOCH := by
          by_contra hc
          have he := fe.1 (idx - P.SLOTS_PER_EPOCH) (by omega) (by omega)
          rw [show P.SLOTS_PER_EPOCH + (idx - P.SLOTS_PER_EPOCH) = idx by omega, hp] at he
          exact hne (Option.some.inj he)
        omega
      · omega
    have T : AnchorTrack v.run (anchorVs a idx) p.withdrawal False :=
      { hspe := hspe, hq := v.quorumPositive
        hvs := fun i B hB => by have := anchor_slot_lt hB; omega
        hL := False.elim
        hnotL := fun _ heq => by
          have h1 := hpi
          rw [heq, payIdx_shift hspe, ← hLs] at h1
          have hb : bidIndex a = some idx := h1
          obtain ⟨E, hE, -, hE'⟩ := g7 idx hb
          rw [hp] at hE; cases hE
          rcases hE' with ⟨-, hw⟩ | rfl
          · exact hnotL ⟨hb, hw⟩
          · exact hne rfl
        hlat := False.elim }
    have hl : LiveAt (anchorVs a idx) p.withdrawal a := ⟨p, by rw [cell_of_payIdx hpi, hp], hne, rfl⟩
    obtain ⟨f, hf⟩ := T.exists_live (e := .payment idx) hl
    refine ⟨f, ⟨?_, p, hp, hf⟩, fun g hg' => ?_⟩
    · cases f <;> simp only [AnchorFate.Allowed] <;> simp only [AnchorFate.holdsT] at hf <;>
        exact hf.1.elim
    · obtain ⟨-, p', hp', hg⟩ := hg'
      rw [hp] at hp'; cases hp'
      exact T.unique hg hf
  | latestBid =>
    by_cases hpay : LatestPays a
    · have T : AnchorTrack v.run (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)
          (bidWithdrawal a.latest_execution_payload_bid) True :=
        { hspe := hspe, hq := v.quorumPositive
          hvs := fun i B hB => by
            obtain ⟨B0, hB0⟩ := anchor_step (run := v.run) (i := 0)
              (by have := (List.getElem?_eq_some_iff.mp hB).1; omega)
            have h0 := B0.lbh_lt
            rw [B0.postSlots_lbh] at h0
            have hpre : B0.preB = a := by
              rcases anchor_pred hB0 with ⟨-, hp⟩ | ⟨h, -⟩
              · exact hp
              · omega
            rw [hpre, ← hLs] at h0
            rcases Nat.eq_zero_or_pos i with rfl | hpos
            · rw [hB0] at hB; cases hB; omega
            · have := slot_lt' v.run hB0 hB hpos; omega
          hL := fun _ => by rw [hLs]
          hnotL := fun h => (h trivial).elim
          hlat := fun _ => ⟨g7, fe, rfl⟩ }
      have ex : ∃ f : AnchorFate v.run .latestBid, f.holdsT
          (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)
          (bidWithdrawal a.latest_execution_payload_bid) True := by
        by_cases hl : LiveAt (a.latest_execution_payload_bid.slot.toNat + P.SLOTS_PER_EPOCH)
            (bidWithdrawal a.latest_execution_payload_bid) a
        · exact T.exists_live hl
        · exact AnchorTrack.exists_dead trivial hl
      obtain ⟨f, hf⟩ := ex
      refine ⟨f, ⟨?_, Or.inl ⟨hpay, hf⟩⟩, fun g hg' => ?_⟩
      · cases f <;> simp only [AnchorFate.Allowed] <;> simp only [AnchorFate.holdsT] at hf
      · obtain ⟨-, hg⟩ := hg'
        rcases hg with ⟨-, hg⟩ | ⟨hn, -⟩
        · exact T.unique hg hf
        · exact (hn hpay).elim
    · refine ⟨.noPayment, ⟨trivial, Or.inr ⟨hpay, rfl⟩⟩, fun g hg' => ?_⟩
      obtain ⟨-, hg⟩ := hg'
      rcases hg with ⟨h, -⟩ | ⟨-, rfl⟩
      · exact (hpay h).elim
      · rfl
  | withdrawal k =>
    obtain ⟨f, hf, hu⟩ := withdrawal_fate (run := v.run) (k := k)
    exact ⟨f, hf, fun g hg => hu g hg⟩

end Headline

end Blanc.Lift.BuilderRequest
