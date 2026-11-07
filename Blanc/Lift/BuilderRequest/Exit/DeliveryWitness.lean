import Blanc.Lift.BuilderRequest.Exit.Delivery

/-!
# The exit sequence's premises can be met

`witness_sequence` builds a compiled chain of real frames from the deployed storage: an unlocking system call, 17
submissions, then two system calls, the first of which drains only part of the queue. Each submission is the
`Exec` of the code under Amsterdam, classified by `exec_user_frame_amsterdam`; each system call is
`processCheckedSystemTransaction`. Each frame runs on a state holding the storage the last one left, which is all
`Chain` asks: it speaks of this contract's storage and nothing else, so this says nothing about a chain's history.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestSystem
open Delivery
open Creation (address)

/-- The frame's static machine: this record's source calling with its key, the highest value, under Amsterdam. -/
def recordSevm (r : Record) : Sevm where
  caller := r.source
  target := some address
  currentTarget := address
  gas := 0
  value := B256.max
  data := r.pubkey
  codeAddress := some address
  code := code
  depth := 0
  shouldTransferValue := true
  isStatic := false
  disablePrecompiles := false
  benvStat := { (default : BenvStat) with fork := .amsterdam }
  tenvStat := default

/-- From any storage off the inhibitor there is a real submission frame enqueuing any record whose source is not
the system address. -/
theorem exists_submission (r : Record) (hr : r.source ≠ systemAddress) {s : Stor} (off : s.get 0 ≠ B256.max) :
    ∃ f : Frame, f.before = s ∧ f.event = .submission r := by
  have hb := holdingDevm_getStorVal address code s
  obtain ⟨i, o, run, -⟩ := WordFakeExponential.run_exists
    (storedExcess 2 (recordSevm r) (holdingDevm address code s)) 17 1 17 0
  have hfork : (recordSevm r).benvStat.fork = .amsterdam := rfl
  have cov : (o / (17 : B256)).toNat ≤ (recordSevm r).value.toNat := by
    have := B256.toNat_lt (o / (17 : B256))
    show _ ≤ B256.max.toNat
    rw [max_toNat]
    omega
  obtain ⟨exec⟩ := exec_submission_amsterdam (b := holdingDevm address code s) (M := .empty) (G := gCallStipend + 1)
    (sevm := recordSevm r) rfl hfork hr r.pubkey_length rfl (by omega) (by
      show (holdingDevm address code s).getStorVal address 0 ≠ _
      rw [hb]
      exact off) run cov
  have frame := exec_user_frame_amsterdam (sevm := recordSevm r) (pre := St (holdingDevm address code s) [] .empty _) rfl hfork rfl rfl Mem.wf_empty
    (by show r.pubkey.length < _; rw [r.pubkey_length]; decide) hr exec
  have hbefore : ∀ G, (St (holdingDevm address code s) [] .empty G).getStor address = s := fun _ => holding_getStor address code s
  cases frame with
  | submission i' o' law =>
    exact ⟨.submission (recordSevm r) _ _ _ i' o' (.amsterdam hfork) rfl hr law, hbefore _, rfl⟩
  | feeRead i' o' empty law =>
    have := r.pubkey_length
    rw [show r.pubkey = [] from empty] at this
    cases this

/-- From any storage there is a real empty-calldata system call frame. -/
theorem exists_system (s : Stor) : ∃ f : Frame, f.before = s ∧ f.event = .system false := by
  refine Delivery.Frame.exists_system (c := contract) (fun s => ?_) s
  obtain ⟨o, run, -⟩ := system_call_state (benv := holdingBenv address code s) rfl (holding_getCode _ _ s)
  exact ⟨_, o, run⟩

/-- Real submission frames for a list of records, chained from any represented queue off the inhibitor. -/
theorem exists_submissions (rs : List Record) (hrs : ∀ r ∈ rs, r.source ≠ systemAddress) {s : Stor}
    {st : QueueState Record} (rep : Holds contract s st) (hne : st.excess ≠ 2 ^ 256 - 1)
    (slots : queueBase 3 (st.tail + rs.length) ≤ 2 ^ 256) (count : st.count + rs.length < 2 ^ 256) :
    ∃ (frames : List Frame) (t : Stor), Chain s frames t ∧ events frames = rs.map .submission := by
  induction rs generalizing s st with
  | nil => exact ⟨[], s, .nil s, rfl⟩
  | cons r rs ih =>
    have off : s.get 0 ≠ B256.max := fun h => by
      have h0 : s.get 0 = st.excess.toB256 := rep.excess
      have := congrArg B256.toNat (h0.symm.trans h)
      rw [B256.toNat_toB256_of_lt rep.excess_lt, max_toNat] at this
      exact hne this
    obtain ⟨f, hb, he⟩ := exists_submission r (hrs r List.mem_cons_self) off
    subst hb
    have hlen : (r :: rs).length = rs.length + 1 := rfl
    rw [hlen] at slots count
    obtain ⟨hrep, -⟩ := f.step_holds rep
      (by rw [he]; exact (queueBase_mono 3 (by show st.tail + 1 ≤ _; omega)).trans slots)
      (by rw [he]; show st.count + 1 < _; omega)
    rw [he] at hrep
    obtain ⟨frames, t, chain, hev⟩ := ih (fun x hx => hrs x (List.mem_cons_of_mem _ hx)) hrep hne
      ((queueBase_mono 3 (by show st.tail + 1 + _ ≤ _; omega)).trans slots)
      (by show st.count + 1 + _ < _; omega)
    exact ⟨f :: frames, t, .cons rfl chain, by simp only [events, List.map_cons, he]; exact congrArg _ hev⟩

theorem submitted_map (rs : List Record) : submitted (rs.map Event.submission) = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    show r :: submitted (rs.map Event.submission) = _
    rw [ih]

theorem noSystem_map (rs : List Record) : NoSystem (rs.map Event.submission) := by
  intro e he latch heq
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp he
  cases heq

/-- **The sequence's premises can be met, with a partial drain.** For any 17 records with sources other than the
system address there is a chain of real frames from the deployed storage: the unlocking call, those 17 submissions,
one call `f` returning exactly the first 16 records and leaving the last queued, then a call returning it. So the
cap is reached and the queue is not emptied by `f`. All 17 come out, in order, and the queue ends empty. -/
theorem witness_sequence (rs : List Record) (hrs : ∀ r ∈ rs, r.source ≠ systemAddress) (hlen : rs.length = 17) :
    ∃ (xs : List Frame) (f : Frame) (ys : List Frame) (t : Stor),
      Chain deployedStorage (xs ++ f :: ys) t ∧ submissions xs = rs ∧ f.event = .system false ∧
      f.output = (rs.take 16).flatMap Record.out ∧
      (queueAfter deployedQueue (xs ++ [f])).queue = rs.drop 16 ∧ rs.drop 16 ≠ [] ∧
      systemOutput (xs ++ f :: ys) = rs.flatMap Record.out ∧
      (queueAfter deployedQueue (xs ++ f :: ys)).queue = [] := by
  obtain ⟨f0, hb0, he0⟩ := exists_system deployedStorage
  have rep0 : Holds contract f0.before deployedQueue := by
    rw [hb0]
    exact deployed_represents
  have hstep0 := (f0.step_holds rep0 (by rw [he0]; decide) (by rw [he0]; decide)).1
  rw [he0] at hstep0
  let st1 : QueueState Record := step 16 2 deployedQueue (.system false)
  have rep1 : Holds contract f0.after st1 := hstep0
  have hq1 : st1.queue = [] := rfl
  have ht1 : st1.tail = 0 := rfl
  have hc1 : st1.count = 0 := rfl
  have hx1 : st1.excess = 0 := by
    show (drainedState 16 2 deployedQueue).excess = 0
    rw [drainedState_excess, show deployedQueue.excess = 2 ^ 256 - 1 from rfl, inhibitor_toB256,
      excessNext_inhibitor]
    rfl
  have hslots : queueBase 3 (st1.tail + rs.length) ≤ 2 ^ 256 := by
    rw [ht1, hlen]
    decide
  have hcount : st1.count + rs.length < 2 ^ 256 := by
    rw [hc1, hlen]
    decide
  obtain ⟨frames, t1, c1, ev1⟩ := exists_submissions rs hrs rep1 (by rw [hx1]; decide) hslots hcount
  obtain ⟨f, hb, he⟩ := exists_system t1
  obtain ⟨g, hg, heg⟩ := exists_system f.after
  have cxs : Chain deployedStorage (f0 :: frames) t1 := .cons hb0 c1
  have hsubsx : submissions (f0 :: frames) = rs := by
    show submitted (f0.event :: events frames) = rs
    rw [he0, ev1]
    exact submitted_map rs
  have hevx : events (f0 :: frames) = .system false :: rs.map .submission := by
    show f0.event :: events frames = _
    rw [he0, ev1]
  have hqx : (queueAfter deployedQueue (f0 :: frames)).queue = rs := by
    show (replay 16 2 deployedQueue (events (f0 :: frames))).queue = rs
    rw [hevx]
    show (replay 16 2 st1 (rs.map .submission)).queue = rs
    rw [replay_noSystem_queue _ _ _ (noSystem_map rs), hq1, submitted_map]
    rfl
  have hk : deliveredRecords deployedQueue (f0 :: frames) = 0 := by
    have hd := (delivery cxs (by rw [hsubsx, hlen]; decide)).2.1
    rw [hqx, hsubsx] at hd
    have hl := congrArg List.length hd
    rw [List.length_drop] at hl
    have hpos : deliveredRecords deployedQueue (f0 :: frames) ≤ rs.length := by
      by_contra hgt
      omega
    omega
  have tail2 : Chain t1 (f :: [g]) g.after := .cons hb (.cons hg (.nil _))
  have whole : Chain deployedStorage ((f0 :: frames) ++ f :: [g]) g.after := cxs.append tail2
  have hsplit1 : queueAfter deployedQueue ((f0 :: frames) ++ [f]) =
      drainedState 16 2 (queueAfter deployedQueue (f0 :: frames)) := by
    simp only [queueAfter, events, List.map_append, replay_append, List.map_cons, List.map_nil, he]
    rfl
  have hq2 : (queueAfter deployedQueue ((f0 :: frames) ++ [f])).queue = rs.drop 16 := by
    rw [hsplit1, drainedState_queue, hqx]
  have hsplit2 : queueAfter deployedQueue ((f0 :: frames) ++ f :: [g]) =
      drainedState 16 2 (drainedState 16 2 (queueAfter deployedQueue (f0 :: frames))) := by
    simp only [queueAfter, events, List.map_append, replay_append, List.map_cons, List.map_nil, he, heg]
    rfl
  have hq3 : (queueAfter deployedQueue ((f0 :: frames) ++ f :: [g])).queue = [] := by
    rw [hsplit2, drainedState_queue, drainedState_queue, hqx]
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_drop, hlen]
  have hsubsAll : submissions ((f0 :: frames) ++ f :: [g]) = rs := by
    rw [submissions_append, hsubsx]
    show rs ++ submitted [f.event, g.event] = rs
    rw [he, heg]
    exact List.append_nil rs
  refine ⟨f0 :: frames, f, [g], g.after, whole, hsubsx, he, ?_, hq2, ?_, ?_, hq3⟩
  · have := call_delivers whole he (by rw [hsubsx, hlen]; decide)
    rw [hsubsx, hk, List.drop_zero] at this
    exact this
  · intro h
    have := congrArg List.length h
    simp only [List.length_drop, hlen, List.length_nil] at this
    omega
  · obtain ⟨-, hdrop, hout⟩ := delivery whole (by rw [hsubsAll, hlen]; decide)
    rw [hq3, hsubsAll] at hdrop
    rw [hout, hsubsAll]
    have htake := List.take_append_drop (deliveredRecords deployedQueue ((f0 :: frames) ++ f :: [g])) rs
    rw [← hdrop, List.append_nil] at htake
    rw [htake]

/-- Records meeting `witness_sequence`'s premises exist, all distinct. -/
def witnessRecords : List Record :=
  (List.range 17).map fun i => ⟨1, List.replicate 48 i.toUInt8, by rw [List.length_replicate]⟩

theorem witnessRecords_ok :
    (∀ r ∈ witnessRecords, r.source ≠ systemAddress) ∧ witnessRecords.length = 17 ∧
      (witnessRecords.map Record.pubkey).Nodup := by
  refine ⟨?_, rfl, by decide⟩
  intro r hr
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
  show (1 : Adr) ≠ systemAddress
  decide

end Blanc.Lift.BuilderRequest.Exit
