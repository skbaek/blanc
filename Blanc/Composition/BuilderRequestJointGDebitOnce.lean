import Blanc.Composition.BuilderRequestJointGChargeOnce
import Blanc.GloasWithdrawalPrefix
import Blanc.Lift.RequestQueue.Batch

/-!
# Actual withdrawal prefixes meet the tagged cap-one queue model (`P3`: `payment-debit-at-most-once`)

Each step witness comes from its original successful parent/header/withdrawal calls.
The local erasure law uses the same processed count as that actual apply phase.
Run occurrence attribution is developed here using `DebitOrigin := Sum Nat (Nat × Nat)`:
- `Sum.inl k` tags the initial anchor queue occurrence at index `k < anchor.builderQueue.length`;
- `Sum.inr (j, k)` tags the `k`-th append `Push` emitted by run step `j`.

Every consumed pending-withdrawal occurrence in `run.debitSpent` corresponds to a unique
`(stepIndex, prefixOffset)` pair `(i, k)` and routes through the literal singleton
`a.builders.modify e.builder_index.toNat (... saturatingSubGwei ...)` step inside
`Gloas.applyWithdrawals`. At most one append-origin debit is attributed to any virtual payment
slot `s` over the entire run (including the crossing block's bid slot
`C.block.message.slot.toNat + P.SLOTS_PER_EPOCH`); for every ordinary Gloas block bid (`GloasStepData`)
with positive value, any such debit carries `D.payW` and resolves to the unique appending
`PaymentFate` (`quorum`, `settled`, or `directAppend`) via `push_fate`.
(Goal §14 crossing-bid note: `PaymentFate` is indexed over `GloasStepData` steps, so the first
Gloas block placed at `CrossingData` receives the exact per-slot append-debit bound `≤ 1` and
empty crossing-step withdrawal prefix `CrossingData.withdrawal_prefix_zero`, without claiming
3-path `PaymentFate` over pre-block crossing state.)
Builder sweeps and natural balance changes are separate from pending-prefix events, as witnessed
by `payment_debit_control`.
-/

namespace Blanc.Lift.BuilderRequest
open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv
variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

theorem _root_.Blanc.GloasStepData.withdrawal_prefix
    (D : GloasStepData (P := P) cfg ccfg bls) (hspe : 0 < P.SLOTS_PER_EPOCH) :
    ∃ (s1 s2 s3 : Gloas.BeaconState P) (ws : Array JauneConsensus.Withdrawal) (d : Nat),
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1 ∧
      Gloas.processBlockHeader s1 D.block.message = .ok s2 ∧
      Gloas.processWithdrawals s2 = .ok s3 ∧
      GloasWithdrawalPrefix.PrefixSpec s2 s3 ws d ∧
      s2.builder_pending_withdrawals.toArray.toList =
        D.preB.builder_pending_withdrawals.toArray.toList ++ D.pushes.map (·.w) ∧
      D.Drops d ∧ D.postB.builder_pending_withdrawals.toArray.toList =
        s2.builder_pending_withdrawals.toArray.toList.drop d := by
  obtain ⟨s1, s2, s3, -, -, -, -, h1, h2, h3, -⟩ := processBlock_phases D.processBlock
  obtain ⟨ws, d, hp⟩ := GloasWithdrawalPrefix.processWithdrawals_prefix h3
  have hd : D.Drops d := ⟨s1, s2, s3, h1, h2, h3, hp.2.1, hp.1⟩
  obtain ⟨-, -, hm2⟩ := processBlockHeader_post h2
  have e2 : s2.builder_pending_withdrawals = s1.builder_pending_withdrawals := by rw [hm2]
  have hq : s2.builder_pending_withdrawals.toArray.toList =
      D.preB.builder_pending_withdrawals.toArray.toList ++ D.pushes.map (·.w) := by
    rw [e2, parent_pushes hspe h1, slotLoop_pushes _ _ _ (processSlots_slotLoop D.slots).2,
      GloasStepData.pushes, List.map_append, List.append_assoc]
  obtain ⟨d', hd', -, he⟩ := D.pushes_exhaustive hspe
  have hdd : d' = d := D.drops_unique hd' hd
  rw [hdd] at he
  refine ⟨s1, s2, s3, ws, d, h1, h2, h3, hp, hq, hd, ?_⟩
  rw [hq]
  exact he

theorem _root_.Blanc.GloasStepData.tagged_batch_erasure
    {Tag : Type} (D : GloasStepData (P := P) cfg ccfg bls) (hspe : 0 < P.SLOTS_PER_EPOCH)
    (st : QueueState (Tag × Gloas.BuilderPendingWithdrawal))
    (rs : List (Tag × Gloas.BuilderPendingWithdrawal))
    (pre : st.queue.map Prod.snd = D.preB.builder_pending_withdrawals.toArray.toList)
    (app : rs.map Prod.snd = D.pushes.map (·.w)) :
    ∃ d, D.Drops d ∧
      ((RequestQueue.run 1 st (rs.map RequestQueue.Effect.push ++
        List.replicate d (.drain (fun _ _ => 0)))).queue.map Prod.snd) =
        D.postB.builder_pending_withdrawals.toArray.toList := by
  obtain ⟨s1, s2, s3, ws, d, -, -, -, -, hq, hd, he⟩ := D.withdrawal_prefix hspe
  refine ⟨d, hd, ?_⟩
  rw [RequestQueue.run_append, RequestQueue.run_unit_drains_queue, RequestQueue.run_pushes_queue,
    List.map_drop, List.map_append, pre, app, ← hq, ← he]

/-! ## Crossing zero-prefix law -/

/-- At the Fulu → Gloas crossing step, the read-phase `builder_pending_withdrawals` is empty,
`processWithdrawals` processes `0` builder pending-withdrawal prefix entries, and the post-block
queue remains empty. -/
theorem _root_.Blanc.CrossingData.withdrawal_prefix_zero
    (C : CrossingData (P := P) cfg ccfg bls)
    (quorumPositive : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT) :
    ∃ (s1 s2 s3 : Gloas.BeaconState P) (ws : Array JauneConsensus.Withdrawal),
      Gloas.processParentExecutionPayload (gloasCtx ccfg bls) C.postSlots C.block.message = .ok s1 ∧
      Gloas.processBlockHeader s1 C.block.message = .ok s2 ∧
      Gloas.processWithdrawals s2 = .ok s3 ∧
      s2.builder_pending_withdrawals.toArray.toList = [] ∧
      GloasWithdrawalPrefix.PrefixSpec s2 s3 ws 0 ∧
      C.postB.builder_pending_withdrawals.toArray.toList = [] := by
  have hc0 := upgradeToGloas_crossClean C.upgrade
  obtain ⟨hcS, -⟩ := crossingSlots_crossClean quorumPositive C.slots hc0
  have hpB : Gloas.processBlock (gloasCtx ccfg bls) C.postSlots C.block.message = .ok C.postB :=
    applySignedBlockWith_ok C.transition
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases hpB
  obtain ⟨-, hw1⟩ := parent_crossClean h1 C.emptyRequests hcS
  obtain ⟨-, -, hm2⟩ := processBlockHeader_post h2
  have hw2 : s2.builder_pending_withdrawals.toArray.toList = [] := by
    rw [hm2]
    exact hw1
  obtain ⟨ws, d, hp⟩ := GloasWithdrawalPrefix.processWithdrawals_prefix h3
  have hsz : s2.builder_pending_withdrawals.toArray.size = 0 := by
    rw [← Array.length_toList, hw2]
    rfl
  have hd0 : d = 0 := Nat.eq_zero_of_le_zero (hsz ▸ hp.1)
  subst hd0
  have b4 := processExecutionPayloadBid_post h4
  have o7 := processOperations_ops _ _ _ _ _ h7
  have e8 : C.postB.builder_pending_withdrawals = s7.builder_pending_withdrawals :=
    (processSyncAggregate_invFrame _ _ _ _ h8).2.2.1
  have e6 : s6.builder_pending_withdrawals = s4.builder_pending_withdrawals :=
    ((processEth1Data_invFrame _ _ _ h6).2.2.1).trans (processRandao_invFrame _ _ _ _ h5).2.2.1
  have hwpost : C.postB.builder_pending_withdrawals.toArray.toList = [] := by
    rw [e8, o7.2.1, e6, b4.2.2.2.2.2.2.2.2.2.1, hp.2.1, hw2, List.drop_nil]
  exact ⟨s1, s2, s3, ws, h1, h2, h3, hw2, hp, hwpost⟩

/-! ## Cap-one batch projections -/

section BatchHelpers

private theorem pushed_map_push {Record : Type} (rs : List Record) :
    RequestQueue.pushed (rs.map RequestQueue.Effect.push) = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, RequestQueue.pushed, ih]

private theorem pushed_replicate_drain {Record : Type} (d : Nat) :
    RequestQueue.pushed (List.replicate d (RequestQueue.Effect.drain (Record := Record) (fun _ _ => 0))) = [] := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [List.replicate_succ, RequestQueue.pushed, ih]

private theorem deliveries_map_push {Record : Type} (st : QueueState Record) (rs : List Record) :
    (RequestQueue.deliveries 1 st (rs.map RequestQueue.Effect.push)).flatten = [] := by
  induction rs generalizing st with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, RequestQueue.deliveries, RequestQueue.taken, RequestQueue.apply,
      List.flatten_cons, List.nil_append, ih]

private theorem deliveries_batch {Record : Type} (st : QueueState Record) (rs : List Record) (d : Nat) :
    (RequestQueue.deliveries 1 st
      (rs.map RequestQueue.Effect.push ++ List.replicate d (.drain (fun _ _ => 0)))).flatten =
      (st.queue ++ rs).take d := by
  rw [RequestQueue.deliveries_append, List.flatten_append, deliveries_map_push, List.nil_append,
    RequestQueue.deliveries_unit_drains, RequestQueue.run_pushes_queue]

private theorem deliveredCount_append {Record : Type} (st : QueueState Record)
    (xs ys : List (RequestQueue.Effect Record)) :
    RequestQueue.deliveredCount 1 st (xs ++ ys) =
      RequestQueue.deliveredCount 1 st xs +
        RequestQueue.deliveredCount 1 (RequestQueue.run 1 st xs) ys := by
  simp only [RequestQueue.deliveredCount, RequestQueue.deliveries_append, List.flatten_append,
    List.length_append]

end BatchHelpers

/-! ## Occurrence-tagged run observers -/

/-- Occurrence origin of a pending builder withdrawal: `Sum.inl k` for initial anchor queue slot `k`,
or `Sum.inr (j, k)` for run step `j`'s `k`-th appended `Push`. -/
abbrev DebitOrigin : Type := Sum Nat (Nat × Nat)

/-- Tagged pending builder withdrawal row in the cap-one queue model. -/
abbrev DebitRow : Type := DebitOrigin × Gloas.BuilderPendingWithdrawal

/-- Number of pending builder withdrawals dropped at one run step (`0` before or at crossing,
and the unique `Drops` count at an ordinary Gloas step). -/
noncomputable def _root_.Blanc.GJointRunStep.drops : GJointRunStep (P := P) cfg ccfg bls → Nat
  | .pre _ => 0
  | .crossing _ => 0
  | .gloas D => Classical.choose D.drops_exists

theorem _root_.Blanc.GloasStepData.drops_spec (D : GloasStepData (P := P) cfg ccfg bls) :
    D.Drops (GJointRunStep.gloas D).drops :=
  Classical.choose_spec D.drops_exists

theorem _root_.Blanc.GloasStepData.drops_eq (D : GloasStepData (P := P) cfg ccfg bls) {d : Nat}
    (hd : D.Drops d) : (GJointRunStep.gloas D).drops = d :=
  D.drops_unique D.drops_spec hd

/-- Tagged rows appended by step `j`. -/
def stepDebitTags (j : Nat) (S : GJointRunStep (P := P) cfg ccfg bls) : List DebitRow :=
  S.pushes.zipIdx.map (fun ek => (Sum.inr (j, ek.2), ek.1.w))

/-- Tagged initial rows at `s₀`. -/
def anchorDebitRows (s₀ : GJointState P) : List DebitRow :=
  s₀.builderQueue.zipIdx.map (fun wk => (Sum.inl wk.2, wk.1))

/-- Initial cap-one queue state carrying `anchorDebitRows s₀`. -/
def initialDebitQueue (s₀ : GJointState P) : QueueState DebitRow :=
  ⟨0, 0, 0, s₀.builderQueue.length, anchorDebitRows s₀⟩

/-- Per-step effect batch: push `stepDebitTags j S`, then drain `S.drops` cap-one entries. -/
noncomputable def stepDebitBatch (j : Nat) (S : GJointRunStep (P := P) cfg ccfg bls) :
    List (RequestQueue.Effect DebitRow) :=
  (stepDebitTags j S).map RequestQueue.Effect.push ++
    List.replicate S.drops (.drain (fun _ _ => 0))

/-- Computed list of per-step effect batches along `run`. -/
noncomputable def _root_.Blanc.GJointRun.debitBatches {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) : List (List (RequestQueue.Effect DebitRow)) :=
  run.steps.zipIdx.map (fun Sj => stepDebitBatch Sj.2 Sj.1)

/-- Flattened effect trace along `run`. -/
noncomputable def _root_.Blanc.GJointRun.debitEffects {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) : List (RequestQueue.Effect DebitRow) :=
  run.debitBatches.flatten

/-- Consumed (physically processed) tagged pending-withdrawal rows along `run`, in apply order. -/
noncomputable def _root_.Blanc.GJointRun.debitSpent {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) : List DebitRow :=
  (RequestQueue.deliveries 1 (initialDebitQueue s₀) run.debitEffects).flatten

/-- Unconsumed tagged pending-withdrawal rows remaining in the queue at the end of `run`. -/
noncomputable def _root_.Blanc.GJointRun.debitLeft {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) : List DebitRow :=
  (RequestQueue.run 1 (initialDebitQueue s₀) run.debitEffects).queue

/-- Full tagged source sequence: anchor queue occurrences followed by all run append occurrences. -/
def _root_.Blanc.GJointRun.debitSource {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) : List DebitRow :=
  anchorDebitRows s₀ ++ run.steps.zipIdx.flatMap (fun Sj => stepDebitTags Sj.2 Sj.1)

/-- Queue state immediately before step `i` of `run`. -/
noncomputable def _root_.Blanc.GJointRun.debitBefore {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) (i : Nat) : QueueState DebitRow :=
  RequestQueue.run 1 (initialDebitQueue s₀) (run.debitBatches.take i).flatten

/-- Global index into `run.debitSpent` at the start of step `i`. -/
noncomputable def _root_.Blanc.GJointRun.debitCursor {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) (i : Nat) : Nat :=
  RequestQueue.deliveredCount 1 (initialDebitQueue s₀) (run.debitBatches.take i).flatten

/-- Lookup mapping an append `DebitOrigin` back to its exact `Push` in `run.steps`. -/
def _root_.Blanc.GJointRun.lookupPush {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) : DebitOrigin → Option Push
  | .inl _ => none
  | .inr (j, k) => match run.steps[j]? with
    | some S => S.pushes[k]?
    | none => none

/-! ## Tag projections, `Nodup`, and run FIFO -/

theorem stepDebitTags_map_snd (j : Nat) (S : GJointRunStep (P := P) cfg ccfg bls) :
    (stepDebitTags j S).map Prod.snd = S.pushes.map (·.w) := by
  unfold stepDebitTags
  rw [List.map_map]
  have h : List.map (Prod.snd ∘ fun ek => ((Sum.inr (j, ek.2) : DebitOrigin), ek.1.w)) S.pushes.zipIdx =
      (S.pushes.zipIdx.map Prod.fst).map (·.w) := by
    rw [List.map_map]
    rfl
  rw [h, List.zipIdx_map_fst]

theorem anchorDebitRows_map_snd (s₀ : GJointState P) :
    (anchorDebitRows s₀).map Prod.snd = s₀.builderQueue := by
  unfold anchorDebitRows
  rw [List.map_map]
  exact List.zipIdx_map_fst 0 s₀.builderQueue

private theorem pushed_stepDebitBatch (j : Nat) (S : GJointRunStep (P := P) cfg ccfg bls) :
    RequestQueue.pushed (stepDebitBatch j S) = stepDebitTags j S := by
  unfold stepDebitBatch
  rw [RequestQueue.pushed_append, pushed_map_push, pushed_replicate_drain, List.append_nil]

private theorem pushed_batches_flatten :
    ∀ (l : List (GJointRunStep (P := P) cfg ccfg bls × Nat)),
      RequestQueue.pushed ((l.map (fun Sj => stepDebitBatch Sj.2 Sj.1)).flatten) =
        l.flatMap (fun Sj => stepDebitTags Sj.2 Sj.1)
  | [] => rfl
  | (S, j) :: l => by
    simp only [List.map_cons, List.flatten_cons, RequestQueue.pushed_append, pushed_stepDebitBatch,
      List.flatMap_cons, pushed_batches_flatten l]

private theorem ge_of_mem_zipIdx {α : Type} :
    ∀ (l : List α) (n : Nat) {x : α} {j : Nat}, (x, j) ∈ l.zipIdx n → n ≤ j
  | [], _, _, _, h => by cases h
  | _ :: l, n, _, _, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.mp h with heq | hm
    · cases heq; exact Nat.le_refl n
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (ge_of_mem_zipIdx l (n + 1) hm))

private theorem stepDebitTags_fst_nodup (j : Nat) (S : GJointRunStep (P := P) cfg ccfg bls) :
    ((stepDebitTags j S).map Prod.fst).Nodup := by
  unfold stepDebitTags
  rw [List.map_map]
  have h : List.map (Prod.fst ∘ fun ek => ((Sum.inr (j, ek.2) : DebitOrigin), ek.1.w)) S.pushes.zipIdx =
      (S.pushes.zipIdx.map Prod.snd).map (fun k => (Sum.inr (j, k) : DebitOrigin)) := by
    rw [List.map_map]
    rfl
  rw [h, List.zipIdx_map_snd]
  exact List.Nodup.map (fun a b hab => by cases hab; rfl) List.nodup_range'

private theorem flatMap_stepDebitTags_fst_nodup :
    ∀ (l : List (GJointRunStep (P := P) cfg ccfg bls)) (n : Nat),
      (((l.zipIdx n).flatMap (fun Sj => stepDebitTags Sj.2 Sj.1)).map Prod.fst).Nodup
  | [], _ => List.nodup_nil
  | S :: l, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.map_append]
    refine List.nodup_append.mpr ⟨stepDebitTags_fst_nodup n S, flatMap_stepDebitTags_fst_nodup l (n + 1), ?_⟩
    intro x hx y hy hxy
    obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hx
    dsimp only [stepDebitTags] at hr1
    obtain ⟨⟨_, k⟩, _, rfl⟩ := List.mem_map.mp hr1
    obtain ⟨r2, hr2, rfl⟩ := List.mem_map.mp hy
    obtain ⟨⟨S', j⟩, hj, hr2'⟩ := List.mem_flatMap.mp hr2
    dsimp only [stepDebitTags] at hr2'
    obtain ⟨⟨_, k'⟩, _, rfl⟩ := List.mem_map.mp hr2'
    have hge : n + 1 ≤ j := ge_of_mem_zipIdx l (n + 1) hj
    cases hxy
    omega

private theorem anchorDebitRows_fst_nodup (s₀ : GJointState P) :
    ((anchorDebitRows s₀).map Prod.fst).Nodup := by
  unfold anchorDebitRows
  rw [List.map_map]
  have h : List.map (Prod.fst ∘ fun wk => ((Sum.inl wk.2 : DebitOrigin), wk.1)) s₀.builderQueue.zipIdx =
      (s₀.builderQueue.zipIdx.map Prod.snd).map (fun k => (Sum.inl k : DebitOrigin)) := by
    rw [List.map_map]
    rfl
  rw [h, List.zipIdx_map_snd]
  exact List.Nodup.map (fun a b hab => by cases hab; rfl) List.nodup_range'

theorem _root_.Blanc.GJointRun.debitSource_fst_nodup {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) :
    (run.debitSource.map Prod.fst).Nodup := by
  unfold GJointRun.debitSource
  rw [List.map_append]
  refine List.nodup_append.mpr ⟨anchorDebitRows_fst_nodup s₀,
    flatMap_stepDebitTags_fst_nodup run.steps 0, ?_⟩
  intro x hx y hy hxy
  obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hx
  unfold anchorDebitRows at hr1
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hr1
  obtain ⟨r2, hr2, rfl⟩ := List.mem_map.mp hy
  obtain ⟨⟨S, j⟩, _, hr2'⟩ := List.mem_flatMap.mp hr2
  dsimp only [stepDebitTags] at hr2'
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hr2'
  cases hxy

theorem _root_.Blanc.GJointRun.debit_fifo_raw {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) :
    run.debitSpent ++ run.debitLeft = run.debitSource := by
  unfold GJointRun.debitSpent GJointRun.debitLeft GJointRun.debitEffects GJointRun.debitBatches
    GJointRun.debitSource
  have h := RequestQueue.fifo 1 (initialDebitQueue s₀)
    ((run.steps.zipIdx.map (fun Sj => stepDebitBatch Sj.2 Sj.1)).flatten)
  rw [pushed_batches_flatten] at h
  exact h

theorem _root_.Blanc.GJointRun.debitSpent_fst_nodup {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) :
    (run.debitSpent.map Prod.fst).Nodup := by
  have h := run.debitSource_fst_nodup
  rw [← run.debit_fifo_raw, List.map_append] at h
  exact (List.nodup_append.mp h).1

private theorem debitBatches_snoc {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s)
    (C : GJointRunStep (P := P) cfg ccfg bls) (hC : C.preState = s) :
    (run.snoc C hC).debitBatches = run.debitBatches ++ [stepDebitBatch run.steps.length C] := by
  unfold GJointRun.debitBatches
  rw [GJointRun.steps_snoc, List.zipIdx_append, List.map_append]
  simp only [Nat.zero_add, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil]

private theorem debitEffects_snoc {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s)
    (C : GJointRunStep (P := P) cfg ccfg bls) (hC : C.preState = s) :
    (run.snoc C hC).debitEffects = run.debitEffects ++ stepDebitBatch run.steps.length C := by
  unfold GJointRun.debitEffects
  rw [debitBatches_snoc, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem _root_.Blanc.GJointRun.debitLeft_map_snd
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) :
    run.debitLeft.map Prod.snd = s.builderQueue := by
  induction run with
  | nil =>
    unfold GJointRun.debitLeft GJointRun.debitEffects GJointRun.debitBatches GJointRun.steps
      initialDebitQueue
    simp only [List.zipIdx_nil, List.map_nil, List.flatten_nil, RequestQueue.run, List.foldl_nil,
      anchorDebitRows_map_snd]
  | @snoc s run C hC ih =>
    unfold GJointRun.debitLeft
    rw [debitEffects_snoc, RequestQueue.run_append]
    cases C with
    | pre D =>
      have h0 : stepDebitBatch run.steps.length (.pre D) = [] := rfl
      rw [h0]
      change (GJointRun.debitLeft run).map Prod.snd = []
      rw [ih, ← hC]
      rfl
    | crossing X =>
      have h0 : stepDebitBatch run.steps.length (.crossing X) = [] := rfl
      rw [h0]
      change (GJointRun.debitLeft run).map Prod.snd = X.postB.builder_pending_withdrawals.toArray.toList
      obtain ⟨-, -, -, -, -, -, -, -, -, hwpost⟩ := X.withdrawal_prefix_zero hq
      rw [ih, ← hC, hwpost]
      rfl
    | gloas D =>
      subst hC
      obtain ⟨d, hd, her⟩ := D.tagged_batch_erasure hspe
        (RequestQueue.run 1 (initialDebitQueue s₀) run.debitEffects)
        (stepDebitTags run.steps.length (.gloas D)) ih
        (stepDebitTags_map_snd run.steps.length (.gloas D))
      have hdeq : (GJointRunStep.gloas D).drops = d := D.drops_eq hd
      unfold stepDebitBatch
      rw [hdeq]
      exact her

/-- **Mandatory run FIFO & constructed occurrence uniqueness**: `debitSpent ++ debitLeft = debitSource`,
`debitLeft` erases to `s.builderQueue`, and both `debitSource` and `debitSpent` have pairwise-distinct
`DebitOrigin` keys without assuming any input payload `Nodup`. -/
theorem _root_.Blanc.GJointRun.debit_fifo
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) :
    run.debitSpent ++ run.debitLeft = run.debitSource ∧
      run.debitLeft.map Prod.snd = s.builderQueue ∧
      (run.debitSource.map Prod.fst).Nodup ∧
      (run.debitSpent.map Prod.fst).Nodup :=
  ⟨run.debit_fifo_raw, run.debitLeft_map_snd hq hspe, run.debitSource_fst_nodup, run.debitSpent_fst_nodup⟩

theorem _root_.Blanc.GJointRun.debitBefore_queue_eq
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {i : Nat} {S : GJointRunStep (P := P) cfg ccfg bls}
    (hS : run.steps[i]? = some S) :
    (run.debitBefore i).queue.map Prod.snd = S.preState.builderQueue := by
  induction run generalizing i S with
  | nil =>
    simp only [GJointRun.steps, List.getElem?_nil, reduceCtorEq] at hS
  | @snoc s run C hC ih =>
    have hlen : run.debitBatches.length = run.steps.length := by
      simp only [GJointRun.debitBatches, List.length_map, List.length_zipIdx]
    rw [GJointRun.steps_snoc] at hS
    by_cases hi : i < run.steps.length
    · rw [List.getElem?_append_left hi] at hS
      unfold GJointRun.debitBefore
      rw [debitBatches_snoc, List.take_append_of_le_length (by omega)]
      exact ih hS
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi), List.getElem?_singleton] at hS
      split at hS
      · rename_i heq
        have hi' : i = run.steps.length := by omega
        subst hi'
        cases hS
        unfold GJointRun.debitBefore
        rw [debitBatches_snoc, List.take_left' hlen]
        change run.debitLeft.map Prod.snd = C.preState.builderQueue
        exact (run.debitLeft_map_snd hq hspe).trans
          (congrArg GJointState.builderQueue hC).symm
      · cases hS

/-! ## Cursor monotonicity, step increments, and global positions -/

private theorem debitBatches_length {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) :
    run.debitBatches.length = run.steps.length := by
  simp only [GJointRun.debitBatches, List.length_map, List.length_zipIdx]

private theorem debitBatches_getElem? {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s)
    {i : Nat} {S : GJointRunStep (P := P) cfg ccfg bls} (hS : run.steps[i]? = some S) :
    run.debitBatches[i]? = some (stepDebitBatch i S) := by
  unfold GJointRun.debitBatches
  rw [List.getElem?_map, List.getElem?_zipIdx, hS]
  simp only [Option.map_some, Nat.zero_add]

private theorem take_succ_flatten {α : Type} (bs : List (List α)) {i : Nat} {b : List α}
    (hb : bs[i]? = some b) :
    (bs.take (i + 1)).flatten = (bs.take i).flatten ++ b := by
  have hi : i < bs.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbe : bs[i] = b := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hb)
  rw [List.take_add_one, List.getElem?_eq_getElem hi, hbe, Option.toList_some,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]

private theorem step_deliveries_eq
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {i : Nat} {S : GJointRunStep (P := P) cfg ccfg bls}
    (hS : run.steps[i]? = some S) :
    (RequestQueue.deliveries 1 (run.debitBefore i) (stepDebitBatch i S)).flatten =
      ((run.debitBefore i).queue ++ stepDebitTags i S).take S.drops ∧
    S.drops ≤ ((run.debitBefore i).queue ++ stepDebitTags i S).length := by
  refine ⟨deliveries_batch (run.debitBefore i) (stepDebitTags i S) S.drops, ?_⟩
  cases S with
  | pre _ => exact Nat.zero_le _
  | crossing _ => exact Nat.zero_le _
  | gloas D =>
    obtain ⟨s1, s2, s3, ws, d, -, -, -, hp, hq2, hd, -⟩ := D.withdrawal_prefix hspe
    have hdeq : (GJointRunStep.gloas D).drops = d := D.drops_eq hd
    have hpre := run.debitBefore_queue_eq hq hspe hS
    have hlen : ((run.debitBefore i).queue ++ stepDebitTags i (.gloas D)).length =
        s2.builder_pending_withdrawals.toArray.size := by
      have hm := congrArg List.length (show
        ((run.debitBefore i).queue ++ stepDebitTags i (.gloas D)).map Prod.snd =
          s2.builder_pending_withdrawals.toArray.toList by
        rw [List.map_append, hpre, stepDebitTags_map_snd]
        exact hq2.symm)
      simpa only [List.length_map, Array.length_toList] using hm
    rw [hdeq, hlen]
    exact hp.1

theorem _root_.Blanc.GJointRun.debitCursor_zero {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) : run.debitCursor 0 = 0 := rfl

theorem _root_.Blanc.GJointRun.debitCursor_end {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) :
    run.debitCursor run.steps.length = run.debitSpent.length := by
  unfold GJointRun.debitCursor GJointRun.debitSpent GJointRun.debitEffects RequestQueue.deliveredCount
  rw [← debitBatches_length run, List.take_length]

theorem _root_.Blanc.GJointRun.debitCursor_succ
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {i : Nat} {S : GJointRunStep (P := P) cfg ccfg bls}
    (hS : run.steps[i]? = some S) :
    run.debitCursor (i + 1) = run.debitCursor i + S.drops := by
  unfold GJointRun.debitCursor
  rw [take_succ_flatten run.debitBatches (debitBatches_getElem? run hS), deliveredCount_append]
  change run.debitCursor i +
    (RequestQueue.deliveries 1 (run.debitBefore i) (stepDebitBatch i S)).flatten.length = _
  obtain ⟨hdel, hle⟩ := step_deliveries_eq hq hspe run hS
  rw [hdel, List.length_take_of_le hle]
  rfl

theorem _root_.Blanc.GJointRun.debitCursor_mono {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {i j : Nat} (hij : i ≤ j) :
    run.debitCursor i ≤ run.debitCursor j := by
  have htake : run.debitBatches.take j =
      run.debitBatches.take i ++ (run.debitBatches.drop i).take (j - i) := by
    have h : run.debitBatches.take (i + (j - i)) =
        run.debitBatches.take i ++ (run.debitBatches.drop i).take (j - i) := List.take_add
    rwa [Nat.add_sub_of_le hij] at h
  unfold GJointRun.debitCursor
  rw [htake, List.flatten_append, deliveredCount_append]
  omega

private theorem debitSpent_split {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s)
    {i : Nat} {S : GJointRunStep (P := P) cfg ccfg bls} (hS : run.steps[i]? = some S) :
    run.debitSpent =
      (RequestQueue.deliveries 1 (initialDebitQueue s₀) (run.debitBatches.take i).flatten).flatten ++
      (RequestQueue.deliveries 1 (run.debitBefore i) (stepDebitBatch i S)).flatten ++
      (RequestQueue.deliveries 1 (run.debitBefore (i + 1)) (run.debitBatches.drop (i + 1)).flatten).flatten := by
  have hb := debitBatches_getElem? run hS
  have hsplit : run.debitBatches =
      run.debitBatches.take (i + 1) ++ run.debitBatches.drop (i + 1) :=
    (List.take_append_drop (i + 1) run.debitBatches).symm
  unfold GJointRun.debitSpent GJointRun.debitEffects GJointRun.debitBefore
  conv_lhs => rw [hsplit, List.flatten_append, take_succ_flatten run.debitBatches hb]
  rw [RequestQueue.deliveries_append, List.flatten_append, RequestQueue.deliveries_append,
    List.flatten_append, ← take_succ_flatten run.debitBatches hb]

theorem _root_.Blanc.GJointRun.debitSpent_at_step
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {i : Nat} {D : GloasStepData (P := P) cfg ccfg bls}
    (hD : run.steps[i]? = some (.gloas D)) {k : Nat} (hk : k < (GJointRunStep.gloas D).drops) :
    ∃ origin e,
      run.debitSpent[run.debitCursor i + k]? = some (origin, e) ∧
      (D.preB.builder_pending_withdrawals.toArray.toList ++ D.pushes.map (·.w))[k]? = some e := by
  have hsp := debitSpent_split run hD
  obtain ⟨hdel, hle⟩ := step_deliveries_eq hq hspe run hD
  have hmid_len : (RequestQueue.deliveries 1 (run.debitBefore i)
      (stepDebitBatch i (.gloas D))).flatten.length = (GJointRunStep.gloas D).drops := by
    rw [hdel, List.length_take_of_le hle]
  have hleft_len : (RequestQueue.deliveries 1 (initialDebitQueue s₀)
      (run.debitBatches.take i).flatten).flatten.length = run.debitCursor i := rfl
  have hidx : run.debitSpent[run.debitCursor i + k]? =
      ((run.debitBefore i).queue ++ stepDebitTags i (.gloas D))[k]? := by
    rw [hsp, List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [hleft_len, Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (by omega), hdel, List.getElem?_take_of_lt hk]
  have hlt : k < ((run.debitBefore i).queue ++ stepDebitTags i (.gloas D)).length :=
    Nat.lt_of_lt_of_le hk hle
  rcases hpair : ((run.debitBefore i).queue ++ stepDebitTags i (.gloas D))[k] with ⟨origin, e⟩
  have hget : ((run.debitBefore i).queue ++ stepDebitTags i (.gloas D))[k]? = some (origin, e) := by
    rw [List.getElem?_eq_getElem hlt, hpair]
  refine ⟨origin, e, hidx.trans hget, ?_⟩
  have hpre := run.debitBefore_queue_eq hq hspe hD
  have hmap : ((run.debitBefore i).queue ++ stepDebitTags i (.gloas D)).map Prod.snd =
      D.preB.builder_pending_withdrawals.toArray.toList ++ D.pushes.map (·.w) := by
    rw [List.map_append, hpre, stepDebitTags_map_snd]
    rfl
  rw [← hmap, List.getElem?_map, hget]
  rfl

/-! ## Physical singleton debit witness (`DebitStepEvent`) -/

/-- Exact physical pending-withdrawal debit witness at step `i` (`run.steps[i]? = some (.gloas D)`)
and pending-prefix offset `k < (GJointRunStep.gloas D).drops`: locates `(origin, e)` at global
spent index `run.debitCursor i + k`, connects `s2` and `ws` through `PrefixSpec`, splits
`Gloas.applyWithdrawals s2 ws` around `#[w]`, and exhibits the literal singleton
`a_pre.builders.modify e.builder_index.toNat (... saturatingSubGwei ...)` step. -/
def DebitStepEvent {s₀ s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s)
    (i : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (k : Nat)
    (origin : DebitOrigin) (e : Gloas.BuilderPendingWithdrawal) : Prop :=
  run.steps[i]? = some (.gloas D) ∧
  k < (GJointRunStep.gloas D).drops ∧
  run.debitSpent[run.debitCursor i + k]? = some (origin, e) ∧
  ∃ (s1 s2 s3 a a_pre a_post : Gloas.BeaconState P) (ws : Array JauneConsensus.Withdrawal)
      (w : JauneConsensus.Withdrawal) (bs : ProgressiveListS Spine.successorRight Gloas.Builder),
    Gloas.processParentExecutionPayload (gloasCtx ccfg bls) D.postSlots D.block.message = .ok s1 ∧
    Gloas.processBlockHeader s1 D.block.message = .ok s2 ∧
    Gloas.processWithdrawals s2 = .ok s3 ∧
    GloasWithdrawalPrefix.PrefixSpec s2 s3 ws (GJointRunStep.gloas D).drops ∧
    s2.builder_pending_withdrawals.toArray[k]? = some e ∧
    ws[k]? = some w ∧
    w.address = e.fee_recipient ∧
    w.amount = e.amount ∧
    Gloas.convertBuilderIndexToValidatorIndex e.builder_index = .ok w.validator_index ∧
    Gloas.isBuilderIndex w.validator_index = true ∧
    Gloas.convertValidatorIndexToBuilderIndex w.validator_index = .ok e.builder_index ∧
    Gloas.applyWithdrawals s2 ws = .ok a ∧
    D.postB.builders = a.builders ∧
    Gloas.applyWithdrawals s2 (ws.toList.take k).toArray = .ok a_pre ∧
    Gloas.applyWithdrawals a_pre #[w] = .ok a_post ∧
    Gloas.applyWithdrawals a_post (ws.toList.drop (k + 1)).toArray = .ok a ∧
    a_pre.builders.modify e.builder_index.toNat
      (fun x => do pure {x with balance := ← Gloas.saturatingSubGwei x.balance e.amount})
      "apply_withdrawals" = .ok bs ∧
    a_post = {a_pre with builders := bs}

theorem _root_.Blanc.GJointRun.debit_event_at
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {i : Nat} {D : GloasStepData (P := P) cfg ccfg bls}
    (hD : run.steps[i]? = some (.gloas D))
    (g3 : PendingRefsInRange D.preB) (hA : LatestBidBuilderActive D.preB)
    (bb : D.postB.builders.toArray.size ≤ 2 ^ 40)
    {k : Nat} (hk : k < (GJointRunStep.gloas D).drops) :
    ∃ origin e, DebitStepEvent run i D k origin e := by
  obtain ⟨origin, e, hspent, hqe⟩ := run.debitSpent_at_step hq hspe hD hk
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    processBlock_phases D.processBlock
  obtain ⟨s1', s2', s3', ws, d, h1', h2', h3', hp, hq2, hd, -⟩ := D.withdrawal_prefix hspe
  rw [h1] at h1'; cases h1'
  rw [h2] at h2'; cases h2'
  rw [h3] at h3'; cases h3'
  have hdeq : (GJointRunStep.gloas D).drops = d := D.drops_eq hd
  rw [← hdeq] at hp
  have hs2e : s2.builder_pending_withdrawals.toArray[k]? = some e := by
    rw [← Array.getElem?_toList, hq2]
    exact hqe
  obtain ⟨e', w, hs2e', hw, haddr, hamt, hconv⟩ := hp.2.2.2 k hk
  rw [hs2e] at hs2e'; cases hs2e'
  rcases hp.2.2.1 with ⟨-, -, -, hd0⟩ | ⟨-, ex, a, -, _, _, ha, hs3a⟩
  · omega
  have hws_k : ws[k]? = some w := by
    rwa [Array.getElem?_toList] at hw
  have hk_ws : k < ws.size := (Array.getElem?_eq_some_iff.mp hws_k).1
  obtain ⟨a_pre, a_post, w', hws_k', hapre, hasing, hapost⟩ :=
    GloasWithdrawalPrefix.applyWithdrawals_at ha k hk_ws
  rw [hws_k] at hws_k'; cases hws_k'
  have g3' := processSlots_pendingRefsInRange hq D.slots g3
  have hA' := processSlots_latestBidBuilderActive D.slots hA
  have r1 := (parent_refs_x04 hA' h1).1 g3'
  obtain ⟨-, -, hm2⟩ := processBlockHeader_post h2
  have r2 : PendingRefsInRange s2 := refs_of_eqs (by rw [hm2]) (by rw [hm2]) (by rw [hm2]) r1
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  have c := afterBid_core h5 h6 h7 h8
  have hpostb : D.postB.builders = s3.builders := by rw [c.1, b4.2.2.2.2.1]
  have hsz2 : s2.builders.toArray.size = D.postB.builders.toArray.size := by
    rw [hpostb, ← w3.2.2.2.2.2.1]
  have he_mem : e ∈ s2.builder_pending_withdrawals.toArray.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_getElem? hs2e)
  have hrange : e.builder_index.toNat < 2 ^ 40 :=
    Nat.lt_of_lt_of_le (r2.1 e he_mem) (hsz2 ▸ bb)
  obtain ⟨hib, hc, bs, hbs, hapost_eq⟩ :=
    GloasWithdrawalPrefix.applyWithdrawals_pending_singleton hasing hamt hconv hrange
  exact ⟨origin, e, hD, hk, hspent, s1, s2, s3, a, a_pre, a_post, ws, w, bs,
    h1, h2, h3, hp, hs2e, hws_k, haddr, hamt, hconv, hib, hc,
    ha, hpostb.trans hs3a, hapre, hasing, hapost, hbs, hapost_eq⟩

/-- Every global index `p < run.debitSpent.length` comes from an ordinary Gloas step `i` and
prefix offset `k < (GJointRunStep.gloas D).drops` with `p = run.debitCursor i + k`. -/
theorem _root_.Blanc.GJointRun.debitSpent_index_source
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {p : Nat} (hp : p < run.debitSpent.length) :
    ∃ i D k,
      run.steps[i]? = some (.gloas D) ∧
      k < (GJointRunStep.gloas D).drops ∧
      p = run.debitCursor i + k := by
  suffices H : ∀ n, n ≤ run.steps.length → p < run.debitCursor n →
      ∃ i D k, run.steps[i]? = some (.gloas D) ∧ k < (GJointRunStep.gloas D).drops ∧
        p = run.debitCursor i + k by
    exact H run.steps.length (Nat.le_refl _) (by rwa [run.debitCursor_end])
  intro n
  induction n with
  | zero =>
    intro _ hp0
    rw [run.debitCursor_zero] at hp0
    omega
  | succ n ih =>
    intro hn hp_succ
    have hn_lt : n < run.steps.length := by omega
    have hS : run.steps[n]? = some run.steps[n] := List.getElem?_eq_getElem hn_lt
    rw [run.debitCursor_succ hq hspe hS] at hp_succ
    by_cases hlt : p < run.debitCursor n
    · exact ih (by omega) hlt
    · generalize hStep : run.steps[n] = S at hS hp_succ
      cases S with
      | pre _ =>
        change p < run.debitCursor n + 0 at hp_succ
        omega
      | crossing _ =>
        change p < run.debitCursor n + 0 at hp_succ
        omega
      | gloas D =>
        exact ⟨n, D, p - run.debitCursor n, hS, by omega, by omega⟩

/-- **Event uniqueness per `DebitOrigin`**: if two pending-prefix debit events have the same
`DebitOrigin`, they are the exact same `(stepIndex, prefixOffset)` occurrence (`i = i' ∧ k = k'`). -/
theorem _root_.Blanc.GJointRun.debit_origin_unique
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s)
    {i i' k k' : Nat} {D D' : GloasStepData (P := P) cfg ccfg bls}
    {origin : DebitOrigin} {e e' : Gloas.BuilderPendingWithdrawal}
    (h1 : run.steps[i]? = some (.gloas D)) (hk1 : k < (GJointRunStep.gloas D).drops)
    (hs1 : run.debitSpent[run.debitCursor i + k]? = some (origin, e))
    (h2 : run.steps[i']? = some (.gloas D')) (hk2 : k' < (GJointRunStep.gloas D').drops)
    (hs2 : run.debitSpent[run.debitCursor i' + k']? = some (origin, e')) :
    i = i' ∧ k = k' ∧ e = e' := by
  have hp1 : run.debitCursor i + k < (run.debitSpent.map Prod.fst).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hs1).1
  have hp2 : run.debitCursor i' + k' < (run.debitSpent.map Prod.fst).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hs2).1
  have hf1 : (run.debitSpent.map Prod.fst)[run.debitCursor i + k] = origin := by
    exact Option.some.inj ((List.getElem?_eq_getElem hp1).symm.trans (by
      rw [List.getElem?_map, hs1]; rfl))
  have hf2 : (run.debitSpent.map Prod.fst)[run.debitCursor i' + k'] = origin := by
    exact Option.some.inj ((List.getElem?_eq_getElem hp2).symm.trans (by
      rw [List.getElem?_map, hs2]; rfl))
  have hpos : run.debitCursor i + k = run.debitCursor i' + k' :=
    (run.debitSpent_fst_nodup.getElem_inj_iff (i := run.debitCursor i + k)
      (j := run.debitCursor i' + k') (hi := hp1) (hj := hp2)).mp (hf1.trans hf2.symm)
  have hii : i = i' := by
    rcases lt_trichotomy i i' with hlt | rfl | hlt
    · have hc1 := run.debitCursor_succ hq hspe h1
      have hm := run.debitCursor_mono (show i + 1 ≤ i' by omega)
      omega
    · rfl
    · have hc2 := run.debitCursor_succ hq hspe h2
      have hm := run.debitCursor_mono (show i' + 1 ≤ i by omega)
      omega
  subst hii
  have hkk : k = k' := by omega
  subst hkk
  rw [hs1] at hs2
  cases hs2
  exact ⟨rfl, rfl, rfl⟩

/-! ## Source lookup, anchor dichotomy, per-slot debit bound, and 3-path bid attribution -/

private theorem filterMap_anchorDebitRows_lookup {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) :
    (anchorDebitRows s₀).filterMap (fun r => run.lookupPush r.1) = [] := by
  unfold anchorDebitRows
  rw [List.filterMap_map]
  exact List.filterMap_eq_nil_iff.mpr (fun _ _ => rfl)

private theorem filterMap_zipIdx_getElem? {α : Type} (full : List α) :
    ∀ (ps : List α) (n : Nat),
      (∀ k x, ps[k]? = some x → full[n + k]? = some x) →
      (ps.zipIdx n).filterMap (fun xk => full[xk.2]?) = ps
  | [], _, _ => rfl
  | x :: ps, n, h => by
    have h0 : full[n]? = some x := by simpa only [Nat.add_zero] using h 0 x rfl
    rw [List.zipIdx_cons, List.filterMap_cons, h0]
    dsimp only
    congr 1
    exact filterMap_zipIdx_getElem? full ps (n + 1) (fun k y hy => by
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h (k + 1) y hy)

private theorem filterMap_stepDebitTags_lookup {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {j : Nat} {S : GJointRunStep (P := P) cfg ccfg bls}
    (hS : run.steps[j]? = some S) :
    (stepDebitTags j S).filterMap (fun r => run.lookupPush r.1) = S.pushes := by
  unfold stepDebitTags
  rw [List.filterMap_map]
  have hfun : ((fun r : DebitRow => run.lookupPush r.1) ∘
      (fun (ek : Push × Nat) => ((Sum.inr (j, ek.2) : DebitOrigin), ek.1.w))) =
      (fun ek => S.pushes[ek.2]?) := by
    funext ek
    simp only [Function.comp_apply, GJointRun.lookupPush, hS]
  rw [hfun]
  exact filterMap_zipIdx_getElem? S.pushes S.pushes 0 (fun k x hx => by
    simpa only [Nat.zero_add] using hx)

private theorem filterMap_flatMap_zipIdx_lookup {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) :
    ∀ (ss : List (GJointRunStep (P := P) cfg ccfg bls)) (n : Nat),
      (∀ k S, ss[k]? = some S → run.steps[n + k]? = some S) →
      ((ss.zipIdx n).flatMap (fun Sj => stepDebitTags Sj.2 Sj.1)).filterMap
        (fun r => run.lookupPush r.1) = ss.flatMap GJointRunStep.pushes
  | [], _, _ => rfl
  | S :: ss, n, h => by
    have h0 : run.steps[n]? = some S := by simpa only [Nat.add_zero] using h 0 S rfl
    rw [List.zipIdx_cons, List.flatMap_cons, List.filterMap_append,
      filterMap_stepDebitTags_lookup run h0, List.flatMap_cons,
      filterMap_flatMap_zipIdx_lookup run ss (n + 1) (fun k S' hS' => by
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h (k + 1) S' hS')]

theorem _root_.Blanc.GJointRun.lookupPush_source {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) :
    run.debitSource.filterMap (fun r => run.lookupPush r.1) = run.pushes := by
  unfold GJointRun.debitSource GJointRun.pushes
  rw [List.filterMap_append, filterMap_anchorDebitRows_lookup, List.nil_append]
  exact filterMap_flatMap_zipIdx_lookup run run.steps 0 (fun k S hS => by
    simpa only [Nat.zero_add] using hS)

theorem _root_.Blanc.GJointRun.debitSource_mem_iff {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {origin : DebitOrigin}
    {e : Gloas.BuilderPendingWithdrawal} :
    (origin, e) ∈ run.debitSource ↔
      (∃ k, origin = Sum.inl k ∧ s₀.builderQueue[k]? = some e) ∨
      (∃ j k D p, origin = Sum.inr (j, k) ∧ run.steps[j]? = some (.gloas D) ∧
        D.pushes[k]? = some p ∧ p.w = e ∧ run.lookupPush origin = some p) := by
  unfold GJointRun.debitSource anchorDebitRows stepDebitTags
  rw [List.mem_append]
  constructor
  · rintro (h | h)
    · obtain ⟨⟨w, k⟩, hwk, heq⟩ := List.mem_map.mp h
      cases heq
      exact Or.inl ⟨k, rfl, List.mem_zipIdx_iff_getElem?.mp hwk⟩
    · obtain ⟨⟨S, j⟩, hSj, hr⟩ := List.mem_flatMap.mp h
      obtain ⟨⟨p, k⟩, hpk, heq⟩ := List.mem_map.mp hr
      cases heq
      have hj : run.steps[j]? = some S := List.mem_zipIdx_iff_getElem?.mp hSj
      have hk : S.pushes[k]? = some p := List.mem_zipIdx_iff_getElem?.mp hpk
      cases S with
      | pre _ => simp only [GJointRunStep.pushes, List.getElem?_nil, reduceCtorEq] at hk
      | crossing _ => simp only [GJointRunStep.pushes, List.getElem?_nil, reduceCtorEq] at hk
      | gloas D =>
        have hk' : D.pushes[k]? = some p := hk
        refine Or.inr ⟨j, k, D, p, rfl, hj, hk', rfl, ?_⟩
        simp only [GJointRun.lookupPush, hj, GJointRunStep.pushes, hk']
  · rintro (⟨k, rfl, hk⟩ | ⟨j, k, D, p, rfl, hj, hk, rfl, -⟩)
    · exact Or.inl (List.mem_map.mpr ⟨(e, k), List.mem_zipIdx_iff_getElem?.mpr hk, rfl⟩)
    · refine Or.inr (List.mem_flatMap.mpr ⟨(.gloas D, j), List.mem_zipIdx_iff_getElem?.mpr hj, ?_⟩)
      exact List.mem_map.mpr ⟨(p, k), List.mem_zipIdx_iff_getElem?.mpr hk, rfl⟩

/-- Every initial anchor queue occurrence `s₀.builderQueue[k]? = some e` is either physically
processed once (`∈ run.debitSpent` and `∉ run.debitLeft`) or still queued (`∈ run.debitLeft` and
`∉ run.debitSpent`), even when multiple anchor rows carry equal payload bytes. -/
theorem _root_.Blanc.GJointRun.anchor_origin_dichotomy {s₀ s : GJointState P}
    (run : GJointRun cfg ccfg bls s₀ s) {k : Nat} {e : Gloas.BuilderPendingWithdrawal}
    (hk : s₀.builderQueue[k]? = some e) :
    ((Sum.inl k, e) ∈ run.debitSpent ∧ (Sum.inl k, e) ∉ run.debitLeft) ∨
      ((Sum.inl k, e) ∈ run.debitLeft ∧ (Sum.inl k, e) ∉ run.debitSpent) := by
  have hmem : (Sum.inl k, e) ∈ run.debitSource :=
    run.debitSource_mem_iff.mpr (Or.inl ⟨k, rfl, hk⟩)
  rw [← run.debit_fifo_raw, List.mem_append] at hmem
  have hnodup := run.debitSource_fst_nodup
  rw [← run.debit_fifo_raw, List.map_append] at hnodup
  have hdisj := (List.nodup_append.mp hnodup).2.2
  rcases hmem with hs | hl
  · refine Or.inl ⟨hs, fun hl => ?_⟩
    exact hdisj (Sum.inl k) (List.mem_map_of_mem hs) (Sum.inl k) (List.mem_map_of_mem hl) rfl
  · refine Or.inr ⟨hl, fun hs => ?_⟩
    exact hdisj (Sum.inl k) (List.mem_map_of_mem hs) (Sum.inl k) (List.mem_map_of_mem hl) rfl

/-- **At most one append-origin pending-withdrawal debit per virtual payment slot `slot`** along `run`,
covering both ordinary Gloas bids (`D.paySlot`) and the first Gloas block's bid at the crossing
(`C.block.message.slot.toNat + P.SLOTS_PER_EPOCH`). -/
theorem _root_.Blanc.GJointRun.slot_debits_le_one
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf)
    (hinv : ∀ {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls}, run.steps[i]? = some (.gloas B) →
      NoLiveWeightOnLatestBid B.preB ∧ LatestBidCoherence B.preB ∧ FutureEmpty B.preB)
    (slot : Nat) :
    ((run.debitSpent.filterMap (fun r => run.lookupPush r.1)).filter
      (fun p => decide (p.slot = slot))).length ≤ 1 := by
  have hpush_eq :
      run.debitSpent.filterMap (fun r => run.lookupPush r.1) ++
        run.debitLeft.filterMap (fun r => run.lookupPush r.1) = run.pushes := by
    rw [← List.filterMap_append, run.debit_fifo_raw, run.lookupPush_source]
  have hlen :
      ((run.debitSpent.filterMap (fun r => run.lookupPush r.1)).filter
        (fun p => decide (p.slot = slot))).length ≤
      (run.pushes.filter (fun p => decide (p.slot = slot))).length := by
    rw [← hpush_eq, List.filter_append, List.length_append]
    omega
  exact Nat.le_trans hlen (slot_pushes_le_one hq hspe run hinv slot)

/-- **3-path ordinary Gloas bid attribution for consumed append occurrences**: any consumed append
in `run.debitSpent` attributed to a paying Gloas step `j`'s `D.paySlot` carries `D.payW` and
witnesses the unique appending `PaymentFate` (`quorum`, `settled`, or `directAppend`) at the
appending step `j_app`. -/
theorem _root_.Blanc.GJointRun.bid_debit_attribution
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls}
    (stepD : run.steps[j]? = some (.gloas D)) (hv : U64.zero < D.bid.value)
    {origin : DebitOrigin} {e : Gloas.BuilderPendingWithdrawal} {p : Push}
    (hspent : (origin, e) ∈ run.debitSpent)
    (hlook : run.lookupPush origin = some p)
    (hslot : p.slot = D.paySlot) :
    e = D.payW ∧ p.w = D.payW ∧
      ∃ j_app k_app D_app, ∃ f : PaymentFate run j,
        origin = Sum.inr (j_app, k_app) ∧
        run.steps[j_app]? = some (.gloas D_app) ∧
        D_app.pushes[k_app]? = some p ∧
        f.holdsFor D ∧
        f.pushKey? = some (p.path, j_app) := by
  have hsrc : (origin, e) ∈ run.debitSource := by
    rw [← run.debit_fifo_raw]
    exact List.mem_append_left _ hspent
  rcases run.debitSource_mem_iff.mp hsrc with ⟨k, rfl, -⟩ | ⟨j_app, k_app, D_app, p', rfl, hj, hk, hpw, hlook'⟩
  · simp only [GJointRun.lookupPush, reduceCtorEq] at hlook
  · rw [hlook] at hlook'
    cases hlook'
    have hp_mem : p ∈ D_app.pushes := List.mem_of_getElem? hk
    obtain ⟨hpw_pay, f, hf, hkey⟩ := push_fate hq hspe stepD hv hj hp_mem hslot
    exact ⟨hpw.symm.trans hpw_pay, hpw_pay, j_app, k_app, D_app, f, rfl, hj, hk, hf, hkey⟩

/-! ## Focused and `ValidJointG` `P3` headlines (`payment_debit_at_most_once`) -/

/-- **Focused `P3` (`payment_debit_at_most_once_focused`)**: along any `GJointRun` satisfying only
`quorumPositive`, `0 < SLOTS_PER_EPOCH`, post-state `buildersBound` (`≤ 2^40`), and the local
Gloas pre-state invariants (`PendingRefsInRange`, `LatestBidBuilderActive`, `NoLiveWeightOnLatestBid`,
`LatestBidCoherence`, `FutureEmpty`), with zero execution/fee/BLS/replay/`NoRegisterAt` premises:
1. `debitSpent ++ debitLeft = debitSource`, `debitLeft` erases to `sf.builderQueue`, and both
   `debitSource` and `debitSpent` have constructed `Nodup` over `DebitOrigin`;
2. every Gloas step `i` and prefix offset `k < drops` induces a physical singleton `builders.modify`
   / `saturatingSubGwei` `DebitStepEvent` at `debitSpent[debitCursor i + k]`, and conversely every
   entry of `debitSpent` comes from a unique `(i, k)` occurrence;
3. every anchor queue entry at `k` is either processed once in `debitSpent` or remains in `debitLeft`;
4. for every virtual payment slot `slot` (including any crossing block bid slot), at most one
   append-origin debit occurs across the run; and for every ordinary Gloas paying bid (`GloasStepData`),
   any such debit carries `D.payW` and resolves to its 3-path `PaymentFate`. -/
theorem payment_debit_at_most_once_focused
    (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hspe : 0 < P.SLOTS_PER_EPOCH) {s₀ sf : GJointState P} (run : GJointRun cfg ccfg bls s₀ sf)
    (hrefs : ∀ {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls},
      run.steps[i]? = some (.gloas B) → PendingRefsInRange B.preB ∧ LatestBidBuilderActive B.preB)
    (hslotInv : ∀ {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls},
      run.steps[i]? = some (.gloas B) →
      NoLiveWeightOnLatestBid B.preB ∧ LatestBidCoherence B.preB ∧ FutureEmpty B.preB)
    (hbb : ∀ {i : Nat} {B : GloasStepData (P := P) cfg ccfg bls},
      run.steps[i]? = some (.gloas B) → B.postB.builders.toArray.size ≤ 2 ^ 40) :
    (run.debitSpent ++ run.debitLeft = run.debitSource ∧
      run.debitLeft.map Prod.snd = sf.builderQueue ∧
      (run.debitSource.map Prod.fst).Nodup ∧
      (run.debitSpent.map Prod.fst).Nodup) ∧
    (∀ {i k : Nat} {D : GloasStepData (P := P) cfg ccfg bls},
      run.steps[i]? = some (.gloas D) → k < (GJointRunStep.gloas D).drops →
      ∃ origin e, DebitStepEvent run i D k origin e) ∧
    (∀ {p : Nat} {origin : DebitOrigin} {e : Gloas.BuilderPendingWithdrawal},
      run.debitSpent[p]? = some (origin, e) →
      ∃ i D k, p = run.debitCursor i + k ∧ DebitStepEvent run i D k origin e) ∧
    (∀ {i i' k k' : Nat} {D D' : GloasStepData (P := P) cfg ccfg bls}
        {origin : DebitOrigin} {e e' : Gloas.BuilderPendingWithdrawal},
      run.steps[i]? = some (.gloas D) → k < (GJointRunStep.gloas D).drops →
      run.debitSpent[run.debitCursor i + k]? = some (origin, e) →
      run.steps[i']? = some (.gloas D') → k' < (GJointRunStep.gloas D').drops →
      run.debitSpent[run.debitCursor i' + k']? = some (origin, e') →
      i = i' ∧ k = k' ∧ e = e') ∧
    (∀ {k : Nat} {e : Gloas.BuilderPendingWithdrawal},
      s₀.builderQueue[k]? = some e →
      ((Sum.inl k, e) ∈ run.debitSpent ∧ (Sum.inl k, e) ∉ run.debitLeft) ∨
        ((Sum.inl k, e) ∈ run.debitLeft ∧ (Sum.inl k, e) ∉ run.debitSpent)) ∧
    (∀ slot : Nat,
      ((run.debitSpent.filterMap (fun r => run.lookupPush r.1)).filter
        (fun p => decide (p.slot = slot))).length ≤ 1) ∧
    (∀ {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls}
        {origin : DebitOrigin} {e : Gloas.BuilderPendingWithdrawal} {p : Push},
      run.steps[j]? = some (.gloas D) → U64.zero < D.bid.value →
      (origin, e) ∈ run.debitSpent → run.lookupPush origin = some p → p.slot = D.paySlot →
      e = D.payW ∧ p.w = D.payW ∧
        ∃ j_app k_app D_app, ∃ f : PaymentFate run j,
          origin = Sum.inr (j_app, k_app) ∧
          run.steps[j_app]? = some (.gloas D_app) ∧
          D_app.pushes[k_app]? = some p ∧
          f.holdsFor D ∧
          f.pushKey? = some (p.path, j_app)) := by
  refine ⟨run.debit_fifo hq hspe, ?_, ?_, ?_, ?_, run.slot_debits_le_one hq hspe hslotInv, ?_⟩
  · intro i k D hD hk
    obtain ⟨g3, hA⟩ := hrefs hD
    exact run.debit_event_at hq hspe hD g3 hA (hbb hD) hk
  · intro p origin e hp_get
    have hp_lt : p < run.debitSpent.length := (List.getElem?_eq_some_iff.mp hp_get).1
    obtain ⟨i, D, k, hD, hk, rfl⟩ := run.debitSpent_index_source hq hspe hp_lt
    obtain ⟨g3, hA⟩ := hrefs hD
    obtain ⟨origin', e', hev⟩ := run.debit_event_at hq hspe hD g3 hA (hbb hD) hk
    have heq := hev.2.2.1.symm.trans hp_get
    cases heq
    exact ⟨i, D, k, rfl, hev⟩
  · intro i i' k k' D D' origin e e' h1 hk1 hs1 h2 hk2 hs2
    exact run.debit_origin_unique hq hspe h1 hk1 hs1 h2 hk2 hs2
  · intro k e hk
    exact run.anchor_origin_dichotomy hk
  · intro j D origin e p stepD hv hspent hlook hslot
    exact run.bid_debit_attribution hq hspe stepD hv hspent hlook hslot

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- **`B-S9` / `P3` (`payment-debit-at-most-once`)**: over any `ValidJointG` chain, every pending-builder
withdrawal occurrence (`DebitOrigin := Sum Nat (Nat × Nat)`) is physically processed through the
singleton `builders.modify` / `saturatingSubGwei` pending-prefix path at most once at a unique
`(stepIndex, prefixOffset)`, at most one append-origin debit is attributed to any virtual payment
slot `slot`, and every ordinary Gloas paying bid's append-origin debit carries `D.payW` and
matches its 3-path `PaymentFate`. -/
theorem payment_debit_at_most_once (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    (v.run.debitSpent ++ v.run.debitLeft = v.run.debitSource ∧
      v.run.debitLeft.map Prod.snd = final.builderQueue ∧
      (v.run.debitSource.map Prod.fst).Nodup ∧
      (v.run.debitSpent.map Prod.fst).Nodup) ∧
    (∀ {i k : Nat} {D : GloasStepData (P := P) cfg ccfg bls},
      v.run.steps[i]? = some (.gloas D) → k < (GJointRunStep.gloas D).drops →
      ∃ origin e, DebitStepEvent v.run i D k origin e) ∧
    (∀ {p : Nat} {origin : DebitOrigin} {e : Gloas.BuilderPendingWithdrawal},
      v.run.debitSpent[p]? = some (origin, e) →
      ∃ i D k, p = v.run.debitCursor i + k ∧ DebitStepEvent v.run i D k origin e) ∧
    (∀ {i i' k k' : Nat} {D D' : GloasStepData (P := P) cfg ccfg bls}
        {origin : DebitOrigin} {e e' : Gloas.BuilderPendingWithdrawal},
      v.run.steps[i]? = some (.gloas D) → k < (GJointRunStep.gloas D).drops →
      v.run.debitSpent[v.run.debitCursor i + k]? = some (origin, e) →
      v.run.steps[i']? = some (.gloas D') → k' < (GJointRunStep.gloas D').drops →
      v.run.debitSpent[v.run.debitCursor i' + k']? = some (origin, e') →
      i = i' ∧ k = k' ∧ e = e') ∧
    (∀ {k : Nat} {e : Gloas.BuilderPendingWithdrawal},
      anchor.builderQueue[k]? = some e →
      ((Sum.inl k, e) ∈ v.run.debitSpent ∧ (Sum.inl k, e) ∉ v.run.debitLeft) ∨
        ((Sum.inl k, e) ∈ v.run.debitLeft ∧ (Sum.inl k, e) ∉ v.run.debitSpent)) ∧
    (∀ slot : Nat,
      ((v.run.debitSpent.filterMap (fun r => v.run.lookupPush r.1)).filter
        (fun p => decide (p.slot = slot))).length ≤ 1) ∧
    (∀ {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls}
        {origin : DebitOrigin} {e : Gloas.BuilderPendingWithdrawal} {p : Push},
      v.run.steps[j]? = some (.gloas D) → U64.zero < D.bid.value →
      (origin, e) ∈ v.run.debitSpent → v.run.lookupPush origin = some p → p.slot = D.paySlot →
      e = D.payW ∧ p.w = D.payW ∧
        ∃ j_app k_app D_app, ∃ f : PaymentFate v.run j,
          origin = Sum.inr (j_app, k_app) ∧
          v.run.steps[j_app]? = some (.gloas D_app) ∧
          D_app.pushes[k_app]? = some p ∧
          f.holdsFor D ∧
          f.pushKey? = some (p.path, j_app)) :=
  payment_debit_at_most_once_focused v.quorumPositive (by have := v.slotsPerEpoch; omega) v.run
    (fun hB => by
      obtain ⟨-, g3, -, -, -, -, -, hA, -⟩ := v.gInv_pre hB
      exact ⟨g3, hA⟩)
    (fun hB => by
      obtain ⟨-, -, -, -, -, g7, g8, -, fe⟩ := v.gInv_pre hB
      exact ⟨g7, g8, fe⟩)
    (fun hB => (v.post_bounds hB).2)

end ValidJointG

/-! ## Physical-debit negative controls (`payment_debit_control`) -/

private theorem applyWithdrawals_singleton_zero (s : Gloas.BeaconState P) (b0 : Gloas.Builder)
    (addr : ExecutionAddress) (amt : U64) (hb0 : s.builders.toArray[0]? = some b0)
    (hle : amt.toNat ≤ b0.balance.toNat) :
    let w : JauneConsensus.Withdrawal :=
      { index := U64.zero, validator_index := Gloas.BUILDER_INDEX_FLAG, address := addr, amount := amt }
    ∃ s1 b1, Gloas.applyWithdrawals s #[w] = .ok s1 ∧
      s1.builders.toArray[0]? = some b1 ∧
      b1.balance.toNat + amt.toNat = b0.balance.toNat := by
  intro w
  have hvi : Gloas.isBuilderIndex w.validator_index = true := by
    change Gloas.isBuilderIndex Gloas.BUILDER_INDEX_FLAG = true
    decide
  have hroutes : Routes U64.zero w := by
    change Gloas.convertBuilderIndexToValidatorIndex U64.zero = .ok Gloas.BUILDER_INDEX_FLAG
    rw [convertBuilderIndexToValidatorIndex_eq_ok_iff]
    rfl
  have hcbi : Gloas.convertValidatorIndexToBuilderIndex w.validator_index = .ok U64.zero :=
    convertValidatorIndexToBuilderIndex_of_routes hroutes (by change 0 < 2 ^ 40; decide)
  have hsub_ok : ∃ bal1, Gloas.saturatingSubGwei b0.balance amt = .ok bal1 := by
    unfold Gloas.saturatingSubGwei
    split
    · rename_i hlt
      have hlt' : amt.toNat < b0.balance.toNat := hlt
      obtain ⟨x, hx⟩ := (U64.sub?_ok_iff (a := b0.balance) (b := amt) (site := "saturating_sub")).mpr
        (Nat.le_of_lt hlt')
      exact ⟨x, hx⟩
    · exact ⟨U64.zero, rfl⟩
  obtain ⟨bal1, hbal1⟩ := hsub_ok
  have hex := saturatingSubGwei_exact hle hbal1
  have hj : 0 < s.builders.toArray.size := (Array.getElem?_eq_some_iff.mp hb0).1
  have hmod : ∃ bs, s.builders.modify 0
      (fun x => do pure {x with balance := ← Gloas.saturatingSubGwei x.balance w.amount})
      "apply_withdrawals" = .ok bs := by
    unfold ProgressiveListS.modify ProgressiveListS.get getAt ProgressiveListS.set
    simp only [hb0, w, bind, Except.bind, pure, Except.pure, hbal1, hj, ↓reduceDIte]
    exact ⟨_, rfl⟩
  obtain ⟨bs, hbs⟩ := hmod
  obtain ⟨v, b1, hv, hg, -, hget⟩ := ProgressiveListS_modify_ok hbs
  rw [hb0] at hv; cases hv
  simp only [w, bind, Except.bind, pure, Except.pure, hbal1, Except.ok.injEq] at hg
  refine ⟨{ s with builders := bs }, b1, ?_, ?_, ?_⟩
  · unfold Gloas.applyWithdrawals
    dsimp only
    have hwl : (#[w] : Array JauneConsensus.Withdrawal).toList = [w] := rfl
    rw [← Array.forIn_toList, hwl]
    simp only [List.forIn_cons, List.forIn_nil, hvi, ite_true, hcbi, bind_assoc, pure_bind, bind_pure]
    change (do
      let bs' ← s.builders.modify U64.zero.toNat
        (fun x => do pure {x with balance := ← Gloas.saturatingSubGwei x.balance w.amount})
        "apply_withdrawals"
      pure { s with builders := bs' }) = .ok { s with builders := bs }
    have hz : U64.zero.toNat = 0 := rfl
    rw [hz, hbs]
    rfl
  · simpa only [↓reduceIte] using hget 0
  · subst hg; exact hex

/-- **Physical-debit negative control (`P3`)** demonstrating why each structural boundary of
`payment_debit_at_most_once` bites:
1. **Occurrence tags vs payload-value `Nodup`:** two identical `BuilderPendingWithdrawal` values
   `[e, e]` fail payload `Nodup` (`¬ [e, e].Nodup`), while distinct `DebitOrigin` tags
   `[(Sum.inl 0, e), (Sum.inl 1, e)]` satisfy key `Nodup`, and two corresponding withdrawal records
   `#[w, w]` physically execute two sequential `Gloas.applyWithdrawals` steps when builder `0` exists;
2. **Builder index `< 2^40` bound (`PendingRefsInRange` + `buildersBound`):** at `bi = BUILDER_INDEX_FLAG`
   (`bi.toNat = 2^40`), `convertBuilderIndexToValidatorIndex` collides with `U64.zero` and
   `convertValidatorIndexToBuilderIndex` strips bit `40` back to `U64.zero ≠ bi`;
3. **Pending-prefix vs non-prefix withdrawal separation:** when `builder_pending_withdrawals` is
   empty (`d = 0`), a non-prefix builder sweep withdrawal `#[w_sweep]` with `isBuilderIndex = true`
   still modifies `builders` outside the pending-withdrawal prefix `[0, d)`. -/
theorem payment_debit_control :
    (∀ e : Gloas.BuilderPendingWithdrawal,
      ¬ ([e, e] : List Gloas.BuilderPendingWithdrawal).Nodup ∧
        (([((Sum.inl 0 : DebitOrigin), e), ((Sum.inl 1 : DebitOrigin), e)]).map Prod.fst).Nodup) ∧
    (Gloas.BUILDER_INDEX_FLAG.toNat = 2 ^ 40 ∧
      ¬ (Gloas.BUILDER_INDEX_FLAG.toNat < 2 ^ 40) ∧
      Gloas.convertBuilderIndexToValidatorIndex Gloas.BUILDER_INDEX_FLAG =
        Gloas.convertBuilderIndexToValidatorIndex U64.zero ∧
      Gloas.convertValidatorIndexToBuilderIndex Gloas.BUILDER_INDEX_FLAG = .ok U64.zero ∧
      Gloas.BUILDER_INDEX_FLAG ≠ U64.zero) ∧
    (∀ (s : Gloas.BeaconState P) (b0 : Gloas.Builder) (amt : U64),
      s.builder_pending_withdrawals.toArray.toList = [] →
      s.builders.toArray[0]? = some b0 →
      0 < amt.toNat →
      2 * amt.toNat ≤ b0.balance.toNat →
      let w : JauneConsensus.Withdrawal :=
        { index := U64.zero, validator_index := Gloas.BUILDER_INDEX_FLAG,
          address := b0.execution_address, amount := amt }
      ∃ s1 s2 b1 b2,
        Gloas.applyWithdrawals s #[w] = .ok s1 ∧
        Gloas.applyWithdrawals s #[w, w] = .ok s2 ∧
        s1.builders.toArray[0]? = some b1 ∧
        s2.builders.toArray[0]? = some b2 ∧
        b1.balance.toNat < b0.balance.toNat ∧
        b2.balance.toNat < b1.balance.toNat) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    refine ⟨?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_singleton, not_true_eq_false, false_and, not_false_eq_true]
    · simp only [List.map_cons, List.map_nil]
      decide
  · refine ⟨rfl, by decide, rfl, rfl, by decide⟩
  · intro s b0 amt _ hb0 hpos hle w
    obtain ⟨s1, b1, hs1, hb1, hbal1⟩ :=
      applyWithdrawals_singleton_zero s b0 b0.execution_address amt hb0 (by omega)
    obtain ⟨s2, b2, hs2, hb2, hbal2⟩ :=
      applyWithdrawals_singleton_zero s1 b1 b0.execution_address amt hb1 (by omega)
    have h12 : Gloas.applyWithdrawals s #[w, w] = .ok s2 := by
      have happ := GloasWithdrawalPrefix.applyWithdrawals_append s #[w] #[w]
      have harr : (#[w] ++ #[w] : Array JauneConsensus.Withdrawal) = #[w, w] := rfl
      rw [harr] at happ
      rw [happ, hs1]
      exact hs2
    exact ⟨s1, s2, b1, b2, hs1, h12, hb1, hb2, by omega, by omega⟩

end Blanc.Lift.BuilderRequest
