import Batteries.Tactic.OpenPrivate
import Blanc.ExecutionKeptClean
import Blanc.ListChunks
import Blanc.ListFlatMapPosition
import Blanc.Lift.RequestQueue.Link

/-!
# Occurrence-indexed submissions, emissions and queues over a covered-fork kept history

`RequestQueue.Link` turns a covered-fork kept history at a request contract into a byte-level `Chain` of queue steps.
This module indexes that delivery by occurrence and by block, for any covered-fork request contract with a `Reading`
of its stored queue and a `DrainLinked` refinement recording that user frames do not drain while the request-phase
system call drains:

* `submissions L blocks`: every committed submission at the contract, in order, in output form;
* `blockEmissions R L b`: the records block `b` outputs as requests of type `L.ty`, its request bytes cut into
  `R.size`-byte records via `Link.chunks`; `emissions R L blocks` is their concatenation, block by block;
* `remainingQueue R L stop`: the live queue in the history's final storage, read head to tail;
* `queueAtRequests R L b`: the live queue in the storage the block's request step read;
* `boundarySubmissions L b`: the submissions of block `b` kept before its request step.

On covered forks every block runs the request fold over `pragueRequests`, which lists `L.address` once, so every block
has a unique kept system frame at `L.address` (`history_block`) and drains `min(length, q.cap)` records from the queue
read there. `history_fifo`, `history_fate`, and `history_latency` follow without re-walking contract bytecode.
-/

namespace Blanc.Lift.RequestQueue.Occurrence

open Jaune ExecutionTrace
open BuilderRequest (QueueState queueBase Represents)
open Link (Linked kept blockDelivered delivered chunks chunks_flatMap covered_requests covered_request_root stepOutput)

open private withdrawalsPass_getCode from Blanc.ExecutionKeptChain

/-! ## Reading a stored queue -/

/-- How a request contract's stored queue reads back in output form. -/
structure Reading (q : Queue) where
  /-- Record at absolute queue index `idx`, in output form, read off the storage. -/
  read : (B256 → B256) → Nat → Bytes
  /-- Bytes per record in a system call's output. -/
  size : Nat
  size_pos : 0 < size
  out_length : ∀ r, (q.out r).length = size
  /-- On storage representing a queue, the reader returns each live record `st.head + i` in output form. -/
  read_eq : ∀ {rd : B256 → B256} {st : QueueState q.Record}, Represents q.width q.words rd st →
    ∀ i (hi : i < st.queue.length), read rd (st.head + i) = q.out st.queue[i]

variable {q : Queue}

/-- The live queue a storage holds, from the head (slot 2) to the tail (slot 3), in output form. -/
def storedQueue (R : Reading q) (rd : B256 → B256) : List Bytes :=
  (List.range ((rd 3).toNat - (rd 2).toNat)).map fun i => R.read rd ((rd 2).toNat + i)

theorem storedQueue_eq (R : Reading q) {rd : B256 → B256} {st : QueueState q.Record}
    (rep : Represents q.width q.words rd st) : storedQueue R rd = st.queue.map q.out := by
  have hh : (rd 2).toNat = st.head := by
    rw [rep.head]
    exact B256.toNat_toB256_of_lt rep.head_lt
  have ht : (rd 3).toNat = st.tail := by
    rw [rep.tail]
    exact B256.toNat_toB256_of_lt rep.tail_lt
  unfold storedQueue
  rw [hh, ht, show st.tail - st.head = st.queue.length by have := rep.coherent; omega]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i h1 _
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    exact R.read_eq rep i h1

/-! ## Drain-aware contract link -/

/-- Refinement of `Link.Linked` recording that user frames do not drain (`∀ next, s.effect ≠ .drain next`) and the
request-phase system call drains (`∃ next, s.effect = .drain next`). -/
structure DrainLinked (L : Linked q) : Prop where
  /-- A kept user frame is a non-draining step with empty output. -/
  user : ∀ {f : Exec.Frame} {stat : BenvStat}, Exec.Frame.EntryIn L.address L.code stat f → CoveredFork stat.fork →
    f.sevm.caller ≠ systemAddress → ∃ s : Step q, s.before = Devm.getStor f.pre L.address ∧
      s.after = Devm.getStor f.post L.address ∧ pushed [s.effect] = (L.record? f).toList ∧ s.output = [] ∧
      ∀ next, s.effect ≠ .drain next
  /-- The request phase's call is a draining step returning whole records. -/
  system : ∀ {benv : Benv} {post : State} {out : MsgCallOutput}, CoveredFork benv.stat.fork →
    benv.state.getCode L.address = L.code → processCheckedSystemTransaction benv L.address [] = .ok (post, out) →
    ∃ s : Step q, s.before = benv.state.getStor L.address ∧ s.after = post.getStor L.address ∧
      pushed [s.effect] = [] ∧ s.output = out.returnData ∧ (∃ next, s.effect = .drain next) ∧
      ∃ rs : List q.Record, out.returnData = rs.flatMap q.out

/-! ## The observers -/

/-- A kept frame with the system caller. -/
def isSystemFrame (f : Exec.Frame) : Bool := decide (f.sevm.caller = systemAddress)

/-- Every committed submission the blocks keep at the contract, in order, in output form. -/
def submissions (L : Linked q) (blocks : List KeptBlock) : List Bytes :=
  ((kept L.address blocks).filterMap L.record?).map q.out

/-- The records one block outputs as requests of type `L.ty`: its type-`L.ty` request bytes cut at `R.size` bytes. -/
def blockEmissions (R : Reading q) (L : Linked q) (b : KeptBlock) : List Bytes :=
  chunks R.size (blockDelivered L.ty b)

/-- The records the blocks output as requests of type `L.ty`, block by block, in order. -/
def emissions (R : Reading q) (L : Linked q) (blocks : List KeptBlock) : List Bytes :=
  blocks.flatMap (blockEmissions R L)

/-- The live queue the contract's storage holds at the history's end. -/
def remainingQueue (R : Reading q) (L : Linked q) (stop : BlockChain) : List Bytes :=
  storedQueue R (stop.state.getStor L.address).get

/-- The frame a block's request step ran at `a`: its first kept frame there with the system caller. -/
def requestFrame (a : Adr) (b : KeptBlock) : Option Exec.Frame :=
  (b.keptAt a).find? isSystemFrame

/-- The live queue in the storage the block's request step at the contract read; empty if it has none. -/
def queueAtRequests (R : Reading q) (L : Linked q) (b : KeptBlock) : List Bytes :=
  match requestFrame L.address b with
  | some f => storedQueue R (Devm.getStor f.pre L.address).get
  | none => []

/-- The submissions a block keeps at the contract before its request step, in output form. -/
def boundarySubmissions (L : Linked q) (b : KeptBlock) : List Bytes :=
  (((b.keptAt L.address).takeWhile fun f => !isSystemFrame f).filterMap L.record?).map q.out

theorem kept_append (a : Adr) (xs ys : List KeptBlock) :
    kept a (xs ++ ys) = kept a xs ++ kept a ys := List.flatMap_append

theorem submissions_append (L : Linked q) (xs ys : List KeptBlock) :
    submissions L (xs ++ ys) = submissions L xs ++ submissions L ys := by
  simp only [submissions, kept, List.flatMap_append, List.filterMap_append, List.map_append]

theorem emissions_append (R : Reading q) (L : Linked q) (xs ys : List KeptBlock) :
    emissions R L (xs ++ ys) = emissions R L xs ++ emissions R L ys := List.flatMap_append

/-! ## Prefix delivery over `RequestQueue.Step` -/

/-- A list of effects containing no `.drain`. -/
def NoDrain {Record : Type} (es : List (Effect Record)) : Prop :=
  ∀ e ∈ es, ∀ next, e ≠ .drain next

theorem deliveredCount_noDrain {Record : Type} (cap : Nat) :
    ∀ (st : QueueState Record) {es : List (Effect Record)}, NoDrain es → deliveredCount cap st es = 0
  | _, [], _ => rfl
  | st, e :: es, h => by
    have tail := deliveredCount_noDrain cap (apply cap st e) (es := es)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have he : taken cap st e = [] := by
      cases e with
      | push _ => rfl
      | keep => rfl
      | drain next => exact absurd rfl (h _ List.mem_cons_self next)
    unfold deliveredCount at tail ⊢
    show (taken cap st e :: deliveries cap (apply cap st e) es).flatten.length = 0
    rw [List.flatten_cons, he, List.nil_append]
    exact tail

theorem submissions_steps_append (xs ys : List (Step q)) :
    RequestQueue.submissions (xs ++ ys) = RequestQueue.submissions xs ++ RequestQueue.submissions ys := by
  simp only [RequestQueue.submissions, effects, List.map_append, pushed_append]

theorem deliveredRecords_append (st : QueueState q.Record) (xs ys : List (Step q)) :
    deliveredRecords st (xs ++ ys) = deliveredRecords st xs + deliveredRecords (queueAfter st xs) ys := by
  simp only [deliveredRecords, deliveredCount, effects, List.map_append, deliveries_append, List.flatten_append,
    List.length_append, queueAfter]

theorem deliveredRecords_prefix (st : QueueState q.Record) (xs fs : List (Step q)) :
    deliveredRecords st xs ≤ deliveredRecords st (xs ++ fs) := by
  rw [deliveredRecords_append]
  exact Nat.le_add_right _ _

theorem deliveredRecords_noDrain (st : QueueState q.Record) (xs : List (Step q))
    {ys : List (Step q)} (h : NoDrain (effects ys)) :
    deliveredRecords st (xs ++ ys) = deliveredRecords st xs := by
  rw [deliveredRecords_append]
  unfold deliveredRecords
  rw [deliveredCount_noDrain q.cap (queueAfter st xs) h, Nat.add_zero]

theorem deliveredRecords_le (st : QueueState q.Record) (xs : List (Step q)) :
    deliveredRecords st xs ≤ (st.queue ++ RequestQueue.submissions xs).length := by
  have := congrArg List.length (fifo q.cap st (effects xs))
  rw [List.length_append] at this
  unfold deliveredRecords deliveredCount RequestQueue.submissions
  omega

/-- On a chain with the word range over all its steps, a prefix delivers the oldest records of the whole. -/
theorem prefix_facts {s t : Stor} {st : QueueState q.Record} {xs ys : List (Step q)}
    (chain : Chain s (xs ++ ys) t) (rep : Holds q s st)
    (slots : queueBase q.width (st.tail + (RequestQueue.submissions (xs ++ ys)).length) ≤ 2 ^ 256)
    (count : st.count + (RequestQueue.submissions (xs ++ ys)).length < 2 ^ 256) :
    ∃ m, Chain s xs m ∧ Chain m ys t ∧ Delivered st xs m ∧
      output xs = ((st.queue ++ RequestQueue.submissions (xs ++ ys)).take (deliveredRecords st xs)).flatMap q.out := by
  obtain ⟨m, h1, h2⟩ := chain.append_split
  have hl : (RequestQueue.submissions xs).length ≤ (RequestQueue.submissions (xs ++ ys)).length := by
    rw [submissions_steps_append, List.length_append]
    omega
  have d := h1.delivered rep ((queueBase_mono _ (by omega)).trans slots) (by omega)
  refine ⟨m, h1, h2, d, ?_⟩
  rw [d.output, submissions_steps_append, ← List.append_assoc,
    List.take_append_of_le_length (deliveredRecords_le st xs)]

/-- **One segment's output.** The steps `fs` between `xs` and `ys` output the records delivered from the end of
`xs`'s delivery up to the end of `fs`'s, in order. -/
theorem segment_output {s t : Stor} {st : QueueState q.Record} {xs fs ys : List (Step q)}
    (chain : Chain s (xs ++ (fs ++ ys)) t) (rep : Holds q s st)
    (slots : queueBase q.width (st.tail + (RequestQueue.submissions (xs ++ (fs ++ ys))).length) ≤ 2 ^ 256)
    (count : st.count + (RequestQueue.submissions (xs ++ (fs ++ ys))).length < 2 ^ 256) :
    output fs = (((st.queue ++ RequestQueue.submissions (xs ++ (fs ++ ys))).drop (deliveredRecords st xs)).take
      (deliveredRecords st (xs ++ fs) - deliveredRecords st xs)).flatMap q.out := by
  obtain ⟨-, -, -, -, o1⟩ := prefix_facts chain rep slots count
  have chain' : Chain s ((xs ++ fs) ++ ys) t := by rwa [List.append_assoc]
  have e : xs ++ (fs ++ ys) = (xs ++ fs) ++ ys := (List.append_assoc _ _ _).symm
  obtain ⟨-, -, -, -, o2⟩ := prefix_facts chain' rep (by rwa [← e]) (by rwa [← e])
  rw [← e] at o2
  have le : deliveredRecords st xs ≤ deliveredRecords st (xs ++ fs) := deliveredRecords_prefix st xs fs
  obtain ⟨d, hd⟩ : ∃ d, deliveredRecords st (xs ++ fs) = deliveredRecords st xs + d := ⟨_, (Nat.add_sub_cancel' le).symm⟩
  have split : output (xs ++ fs) = output xs ++ output fs := List.flatMap_append
  rw [o2, o1, hd, List.take_add, List.flatMap_append] at split
  rw [hd, Nat.add_sub_cancel_left]
  exact (List.append_cancel_left split).symm

/-! ## Drain-aware correspondence and per-block steps -/

/-- A step matching a kept frame, with non-drain / empty-output on user frames and drain on system frames. -/
structure DrainMatches (L : Linked q) (s : Step q) (f : Exec.Frame) : Prop extends Link.Matches L s f where
  user_step : f.sevm.caller ≠ systemAddress → (∀ next, s.effect ≠ .drain next) ∧ s.output = []
  system_step : f.sevm.caller = systemAddress → ∃ next, s.effect = .drain next

def DrainCorresponds (L : Linked q) (steps : List (Step q)) (kept : List Exec.Frame) : Prop :=
  List.Forall₂ (DrainMatches L) steps kept

section DrainLink

variable {L : Linked q}

theorem DrainCorresponds.toCorresponds {steps : List (Step q)} {kept : List Exec.Frame}
    (h : DrainCorresponds L steps kept) : Link.Corresponds L steps kept :=
  h.imp fun _ _ m => m.toMatches

theorem DrainCorresponds.noDrain {steps : List (Step q)} {kept : List Exec.Frame}
    (h : DrainCorresponds L steps kept) (users : ∀ f ∈ kept, f.sevm.caller ≠ systemAddress) :
    NoDrain (effects steps) ∧ output steps = [] := by
  induction h with
  | nil => exact ⟨fun _ he => absurd he List.not_mem_nil, rfl⟩
  | @cons s f ss fs m _ ih =>
    obtain ⟨nd, out⟩ := m.user_step (users f List.mem_cons_self)
    obtain ⟨ndTail, outTail⟩ := ih fun x hx => users x (List.mem_cons_of_mem _ hx)
    refine ⟨?_, ?_⟩
    · intro e he next
      rcases List.mem_cons.mp he with rfl | he
      · exact nd next
      · exact ndTail e he next
    · show s.output ++ output ss = []
      rw [out, outTail, List.nil_append]

def DrainMapped (L : Linked q) (kept : List Exec.Frame) (out : Bytes) : Prop :=
  ∃ steps, DrainCorresponds L steps kept ∧ output steps = out

theorem DrainMapped.nil : DrainMapped L [] [] := ⟨[], .nil, rfl⟩

theorem DrainMapped.append {xs ys : List Exec.Frame} {o p : Bytes}
    (first : DrainMapped L xs o) (second : DrainMapped L ys p) : DrainMapped L (xs ++ ys) (o ++ p) := by
  obtain ⟨gs, h, rfl⟩ := first
  obtain ⟨hs, k, rfl⟩ := second
  exact ⟨gs ++ hs, List.rel_append h k, List.flatMap_append⟩

theorem DrainMapped.ofUsers (DL : DrainLinked L) {kept : List Exec.Frame} {stat : BenvStat}
    (entries : ∀ f ∈ kept, Exec.Frame.EntryIn L.address L.code stat f) (fork : CoveredFork stat.fork)
    (callers : ∀ f ∈ kept, f.sevm.caller ≠ systemAddress) : DrainMapped L kept [] := by
  induction kept with
  | nil => exact .nil
  | cons f rest ih =>
    have cf := callers f List.mem_cons_self
    obtain ⟨s, before, after, pushes, out, nd⟩ := DL.user (entries f List.mem_cons_self) fork cf
    obtain ⟨ss, h, hout⟩ := ih (fun x hx => entries x (List.mem_cons_of_mem _ hx))
      (fun x hx => callers x (List.mem_cons_of_mem _ hx))
    refine ⟨s :: ss, .cons ⟨⟨before, after, pushes, ⟨[], by rw [out]; rfl⟩⟩,
      fun _ => ⟨nd, out⟩, fun sys => absurd sys cf⟩ h, ?_⟩
    show s.output ++ output ss = []
    rw [out, hout]
    rfl

theorem DrainMapped.ofRequestStep (DL : DrainLinked L) {benv : Benv} {post : State} {out : MsgCallOutput}
    {rs : List Root} (fork : CoveredFork benv.stat.fork) (code : benv.state.getCode L.address = L.code)
    (run : processCheckedSystemTransaction benv L.address [] = .ok (post, out))
    (roots : MessageRoots (systemTransactionMessage benv L.address []) post out rs) :
    DrainMapped L (rs.flatMap (Root.keptAt L.address)) out.returnData := by
  obtain ⟨f, flat, caller, -, before, after⟩ := covered_request_root fork L.member code L.runnable run roots
  obtain ⟨s, sb, sa, pushes, sout, drain, records⟩ := DL.system fork code run
  rw [flat]
  refine ⟨[s], .cons ⟨⟨sb.trans before.symm, sa.trans after.symm, ?_, ?_⟩,
    fun ne => absurd caller ne, fun _ => drain⟩ .nil, ?_⟩
  · rw [pushes, L.system_none f caller]
    rfl
  · rw [sout]
    exact records
  · show s.output ++ [] = _
    rw [sout, List.append_nil]

theorem DrainMapped.ofRequestRoots (DL : DrainLinked L) {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv}
    {acc acc' : List Bytes} {bal bal' : BalBuilder} {final : State} {steps : List RequestStep}
    (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) (fork : CoveredFork benv.stat.fork)
    (code : benv.state.getCode L.address = L.code)
    (others : ∀ s ∈ steps, s.target ≠ L.address → ∀ f ∈ s.roots.flatMap (Root.keptAt L.address),
      f.sevm.caller ≠ systemAddress)
    (entries : ∀ f ∈ (requestRootsOf steps).flatMap (Root.keptAt L.address),
      Exec.Frame.EntryIn L.address L.code benv.stat f) :
    DrainMapped L ((requestRootsOf steps).flatMap (Root.keptAt L.address)) (steps.flatMap (stepOutput L.address)) := by
  obtain ⟨hc, hd⟩ := L.runnable
  induction h with
  | nil => exact .nil
  | @cons type target rest benv acc acc' bal bal' post final out rs steps hcall roots tail ih =>
    have split : (requestRootsOf (⟨type, target, post, out, rs⟩ :: steps)).flatMap (Root.keptAt L.address) =
        rs.flatMap (Root.keptAt L.address) ++ (requestRootsOf steps).flatMap (Root.keptAt L.address) := by
      unfold requestRootsOf
      rw [List.flatMap_cons, List.flatMap_append]
    have hc' : (benv.state.getCode L.address).toList ≠ [] := by rw [code]; exact hc
    have hd' : ¬ isValidDelegation (benv.state.getCode L.address) := by rw [code]; exact hd
    have code' : post.getCode L.address = benv.state.getCode L.address := (MessageRoots.chain roots hc' hd').2
    rw [split] at entries ⊢
    rw [List.flatMap_cons]
    have below := ih fork (code'.trans code)
      (fun s hs => others s (List.mem_cons_of_mem _ hs))
      (fun f hf => entries f (List.mem_append_right _ hf))
    refine DrainMapped.append ?_ below
    by_cases here : target = L.address
    · subst here
      rw [show stepOutput L.address ⟨type, L.address, post, out, rs⟩ = out.returnData from ite_eq_left rfl]
      exact DrainMapped.ofRequestStep DL fork code hcall roots
    · rw [show stepOutput L.address ⟨type, target, post, out, rs⟩ = [] from ite_eq_right here]
      exact DrainMapped.ofUsers DL (fun f hf => entries f (List.mem_append_left _ hf)) fork
        (others _ List.mem_cons_self here)

theorem prague_count (L : Linked q) :
    (pragueRequests.filter fun p => decide (p.2 = L.address)).length = 1 := by
  have e : pragueRequests.filter (fun p => decide (p.2 = L.address)) =
      (pragueRequests.filter fun p => p.1 == L.ty || p.2 == L.address).filter
        (fun p => decide (p.2 = L.address)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro p _
    by_cases hp : p.2 = L.address
    · simp only [hp, decide_true, beq_self_eq_true, Bool.or_true, Bool.and_self]
    · simp only [hp, decide_false, Bool.false_and]
  rw [e, L.listed,
    List.filter_cons_of_pos (p := fun p : UInt8 × Adr => decide (p.2 = L.address)) (decide_eq_true rfl)]
  rfl

theorem fold_systemCount (L : Linked q) {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv}
    {acc acc' : List Bytes} {bal bal' : BalBuilder} {final : State} {steps : List RequestStep}
    (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) (fork : CoveredFork benv.stat.fork)
    (code : benv.state.getCode L.address = L.code)
    (others : ∀ s ∈ steps, s.target ≠ L.address → ∀ f ∈ s.roots.flatMap (Root.keptAt L.address),
      f.sevm.caller ≠ systemAddress) :
    (((requestRootsOf steps).flatMap (Root.keptAt L.address)).filter isSystemFrame).length =
      (contracts.filter fun p => decide (p.2 = L.address)).length := by
  induction h with
  | nil => rfl
  | @cons type target rest benv acc acc' bal bal' post final out rs steps hcall roots tail ih =>
    have split : (requestRootsOf (⟨type, target, post, out, rs⟩ :: steps)).flatMap (Root.keptAt L.address) =
        rs.flatMap (Root.keptAt L.address) ++ (requestRootsOf steps).flatMap (Root.keptAt L.address) := by
      unfold requestRootsOf
      rw [List.flatMap_cons, List.flatMap_append]
    have hc : (benv.state.getCode L.address).toList ≠ [] := by rw [code]; exact L.runnable.1
    have hd : ¬ isValidDelegation (benv.state.getCode L.address) := by rw [code]; exact L.runnable.2
    have code' : post.getCode L.address = benv.state.getCode L.address := (MessageRoots.chain roots hc hd).2
    have below := ih fork (code'.trans code) (fun s hs => others s (List.mem_cons_of_mem _ hs))
    rw [split, List.filter_append, List.length_append, below, List.filter_cons]
    by_cases here : target = L.address
    · subst here
      obtain ⟨f, flat, caller, -⟩ := covered_request_root fork L.member code L.runnable hcall roots
      rw [flat]
      simp only [isSystemFrame, caller, decide_true, List.filter_cons_of_pos, List.filter_nil,
        List.length_cons, List.length_nil, ↓reduceIte]
      omega
    · have none : (rs.flatMap (Root.keptAt L.address)).filter isSystemFrame = [] := by
        rw [List.filter_eq_nil_iff]
        intro f hf
        simp only [isSystemFrame, decide_eq_true_eq]
        exact others _ List.mem_cons_self here f hf
      rw [none]
      simp only [here, decide_false, Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.zero_add]

theorem DrainMapped.ofBody (DL : DrainLinked L) {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput} {run : BodyRun}
    (h : BodyRoots benv txs ommers wds state bout run) (rules : KeptRules benv.stat.rules)
    (fork : CoveredFork benv.stat.fork) (code : benv.state.getCode L.address = L.code)
    (created : L.address ∉ benv.createdAccounts)
    (outside : ∀ f ∈ run.outsideRequests L.address, f.sevm.caller ≠ systemAddress)
    (others : ∀ s ∈ run.requests, s.target ≠ L.address → ∀ f ∈ s.roots.flatMap (Root.keptAt L.address),
      f.sevm.caller ≠ systemAddress)
    (entries : ∀ f ∈ run.roots.flatMap (Root.keptAt L.address), Exec.Frame.EntryIn L.address L.code benv.stat f) :
    DrainMapped L (run.roots.flatMap (Root.keptAt L.address)) (run.requests.flatMap (stepOutput L.address)) ∧
      ((run.roots.flatMap (Root.keptAt L.address)).filter isSystemFrame).length = 1 := by
  have split : run.roots.flatMap (Root.keptAt L.address) = run.outsideRequests L.address ++
      (requestRootsOf run.requests).flatMap (Root.keptAt L.address) := by
    unfold BodyRun.roots BodyRun.outsideRequests
    rw [List.flatMap_append]
  have firstNil : (run.outsideRequests L.address).filter isSystemFrame = [] := by
    rw [List.filter_eq_nil_iff]
    intro f hf
    simp only [isSystemFrame, decide_eq_true_eq]
    exact outside f hf
  rw [split] at entries ⊢
  have first : DrainMapped L (run.outsideRequests L.address) [] :=
    DrainMapped.ofUsers DL (fun f hf => entries f (List.mem_append_left _ hf)) fork outside
  obtain ⟨st, out, pass, -, -⟩ := h.stages
  obtain ⟨decoded, -, roots⟩ := h.transactions
  have hs : run.txEnv.stat = benv.stat := h.txEnv_stat
  have on : benv.stat.rules.header.requestsHash = true :=
    fork.cases (motive := fun f => f.ruleSet.header.requestsHash = true) rfl rfl rfl rfl
  have on' : (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut
      wds).1).stat.rules.header.requestsHash = true := by
    change run.txEnv.stat.rules.header.requestsHash = true
    rw [hs]
    exact on
  unfold RequestPass at pass
  rw [ite_eq_left on'] at pass
  obtain ⟨deposits, acc, bal, -, fold, -⟩ := pass
  obtain ⟨hne, hnd⟩ := L.runnable
  have hc : (benv.state.getCode L.address).toList ≠ [] := by rw [code]; exact hne
  have hd : ¬ isValidDelegation (benv.state.getCode L.address) := by rw [code]; exact hnd
  have code₁ := (h.pre.chain hc hd).2
  have code₂ := (roots.chain rules (a := L.address) (by simpa only [Benv.withState, code₁] using hc)
    (by simpa only [Benv.withState, code₁] using hd) created).2
  have codeReq :=
    (withdrawalsPass_getCode benv.stat.rules run.txEnv run.txOut wds L.address).trans (code₂.trans (code₁.trans code))
  have forkReq : CoveredFork (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut wds).1).stat.fork := by
    change CoveredFork run.txEnv.stat.fork
    rw [hs]
    exact fork
  have second : DrainMapped L ((requestRootsOf run.requests).flatMap (Root.keptAt L.address))
      (run.requests.flatMap (stepOutput L.address)) :=
    DrainMapped.ofRequestRoots DL fold forkReq codeReq others fun f hf => by
      change Exec.Frame.EntryIn L.address L.code run.txEnv.stat f
      rw [hs]
      exact entries f (List.mem_append_right _ hf)
  refine ⟨first.append second, ?_⟩
  rw [List.filter_append, firstNil, List.nil_append, fold_systemCount L fold forkReq codeReq others]
  change (run.txEnv.stat.fork.ruleSet.requests.filter fun p => decide (p.2 = L.address)).length = 1
  rw [hs, covered_requests fork]
  exact prague_count L

end DrainLink

/-! ## A history's steps, block by block -/

/-- The queue steps of one covered-fork block: they match its kept frames at the contract, output its requests of type
`L.ty`, and the block has exactly one kept frame there with the system caller. -/
def BlockSteps (L : Linked q) (fs : List (Step q)) (b : KeptBlock) : Prop :=
  DrainCorresponds L fs (b.keptAt L.address) ∧ output fs = blockDelivered L.ty b ∧
    ((b.keptAt L.address).filter isSystemFrame).length = 1

section History

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock} {st : QueueState q.Record}

theorem blockSteps (L : Linked q) (DL : DrainLinked L) (h : KeptHistory cfg start blocks stop)
    (covered : ∀ b ∈ blocks, CoveredFork b.fork) (code : start.state.getCode L.address = L.code)
    (outside : ∀ b ∈ blocks, ∀ f ∈ b.run.outsideRequests L.address, f.sevm.caller ≠ systemAddress)
    (others : ∀ b ∈ blocks, ∀ s ∈ b.run.requests, s.target ≠ L.address →
      ∀ f ∈ s.roots.flatMap (Root.keptAt L.address), f.sevm.caller ≠ systemAddress)
    (entries : ∀ b ∈ blocks, ∀ f ∈ b.keptAt L.address, Exec.Frame.EntryIn L.address L.code b.benv.stat f) :
    ∃ fss : List (List (Step q)), List.Forall₂ (BlockSteps L) fss blocks := by
  have hc : (start.state.getCode L.address).toList ≠ [] := by rw [code]; exact L.runnable.1
  have hd : ¬ isValidDelegation (start.state.getCode L.address) := by rw [code]; exact L.runnable.2
  induction h with
  | refl => exact ⟨[], .nil⟩
  | @step blocks b post prior step ih =>
    have mem : b ∈ blocks ++ [b] := List.mem_append_right _ List.mem_cons_self
    obtain ⟨fss, below⟩ := ih (fun x hx => covered x (List.mem_append_left _ hx))
      (fun x hx => outside x (List.mem_append_left _ hx))
      (fun x hx => others x (List.mem_append_left _ hx))
      (fun x hx => entries x (List.mem_append_left _ hx))
    have codeB := (prior.chain hc hd).2.trans code
    obtain ⟨⟨fs, corr, out⟩, count⟩ := DrainMapped.ofBody DL step.body step.kept.rules (covered b mem) codeB
      AdrSet.not_mem_empty (outside b mem) (others b mem) (entries b mem)
    rw [← Link.block_entries L step.body (covered b mem)] at out
    exact ⟨fss ++ [fs], List.rel_append below (.cons ⟨corr, out, count⟩ .nil)⟩

theorem corresponds_flatten {L : Linked q} :
    ∀ {fss : List (List (Step q))} {bs : List KeptBlock}, List.Forall₂ (BlockSteps L) fss bs →
      DrainCorresponds L fss.flatten (kept L.address bs)
  | _, _, .nil => .nil
  | _, _, .cons hb rest => by
    show DrainCorresponds L (_ ++ _) (List.flatMap _ (_ :: _))
    rw [List.flatMap_cons]
    exact List.rel_append hb.1 (corresponds_flatten rest)

/-- The premises the covered-fork history results share, for a contract whose start storage represents `st`. -/
structure Premises (L : Linked q) (cfg : ChainConfig) (start : BlockChain) (blocks : List KeptBlock)
    (stop : BlockChain) (st : QueueState q.Record) : Prop where
  history : KeptHistory cfg start blocks stop
  covered : ∀ b ∈ blocks, CoveredFork b.fork
  code : start.state.getCode L.address = L.code
  rep : Holds q (start.state.getStor L.address) st
  empty : start.state.getCode systemAddress = ByteArray.empty
  clean : HistoryClean blocks
  slots : queueBase q.width (st.tail + ((kept L.address blocks).filterMap L.record?).length) ≤ 2 ^ 256
  count : st.count + ((kept L.address blocks).filterMap L.record?).length < 2 ^ 256

theorem Premises.steps {L : Linked q} (DL : DrainLinked L) (P : Premises L cfg start blocks stop st) :
    ∃ fss : List (List (Step q)), List.Forall₂ (BlockSteps L) fss blocks ∧
      Chain (start.state.getStor L.address) fss.flatten (stop.state.getStor L.address) ∧
      RequestQueue.submissions fss.flatten = (kept L.address blocks).filterMap L.record? := by
  have hc : (start.state.getCode L.address).toList ≠ [] := by rw [P.code]; exact L.runnable.1
  have hd : ¬ isValidDelegation (start.state.getCode L.address) := by rw [P.code]; exact L.runnable.2
  obtain ⟨outside, others, -⟩ := P.history.caller_ne (a := L.address) P.empty L.beacon L.history
    P.clean.senders P.clean.authorities P.clean.creates
  obtain ⟨fss, hf⟩ := blockSteps L DL P.history P.covered P.code outside others
    (P.history.entry_in P.code L.runnable.1 L.runnable.2)
  have corr := (corresponds_flatten hf).toCorresponds
  exact ⟨fss, hf, corr.chain (P.history.chain hc hd).1, corr.submissions⟩

theorem blockEmissions_of_output (R : Reading q) (L : Linked q) {b : KeptBlock} {rs : List q.Record}
    (h : blockDelivered L.ty b = rs.flatMap q.out) : blockEmissions R L b = rs.map q.out := by
  unfold blockEmissions
  rw [h]
  exact chunks_flatMap R.size q.out R.out_length R.size_pos rs

/-- **Emissions along consecutive blocks.** Over the blocks of a segment of the chain, the emitted records are the
records delivered from the end of the steps before them up to the end of their own. -/
theorem emissions_segments (R : Reading q) (L : Linked q) {s t : Stor} :
    ∀ {fss : List (List (Step q))} {bs : List KeptBlock}, List.Forall₂ (BlockSteps L) fss bs →
      ∀ {xs ys : List (Step q)}, Chain s (xs ++ (fss.flatten ++ ys)) t → Holds q s st →
      queueBase q.width (st.tail + (RequestQueue.submissions (xs ++ (fss.flatten ++ ys))).length) ≤ 2 ^ 256 →
      st.count + (RequestQueue.submissions (xs ++ (fss.flatten ++ ys))).length < 2 ^ 256 →
      emissions R L bs = (((st.queue ++ RequestQueue.submissions (xs ++ (fss.flatten ++ ys))).drop
        (deliveredRecords st xs)).take (deliveredRecords st (xs ++ fss.flatten) - deliveredRecords st xs)).map q.out
  | _, _, .nil, _, _, _, _, _, _ => by
    simp only [emissions, List.flatMap_nil, List.flatten_nil, List.append_nil, Nat.sub_self, List.take_zero,
      List.map_nil]
  | _, _, @List.Forall₂.cons _ _ _ fs b fss bs hb rest, xs, ys, chain, rep, slots, count => by
    have assoc : xs ++ ((fs :: fss).flatten ++ ys) = xs ++ (fs ++ (fss.flatten ++ ys)) := by
      rw [List.flatten_cons, List.append_assoc]
    rw [assoc] at chain slots count ⊢
    have one := segment_output chain rep slots count
    rw [hb.2.1] at one
    have block := blockEmissions_of_output R L one
    have chain' : Chain s ((xs ++ fs) ++ (fss.flatten ++ ys)) t := by rwa [List.append_assoc]
    have e : (xs ++ fs) ++ (fss.flatten ++ ys) = xs ++ (fs ++ (fss.flatten ++ ys)) := List.append_assoc _ _ _
    have tail := emissions_segments R L rest chain' rep (by rwa [e]) (by rwa [e])
    rw [e] at tail
    have k12 := deliveredRecords_prefix st xs fs
    have k23 := deliveredRecords_prefix st (xs ++ fs) fss.flatten
    have e3 : xs ++ (fs :: fss).flatten = (xs ++ fs) ++ fss.flatten := by
      rw [List.flatten_cons, List.append_assoc]
    rw [e3]
    show blockEmissions R L b ++ emissions R L bs = _
    rw [block, tail, ← List.map_append]
    congr 1
    generalize st.queue ++ RequestQueue.submissions (xs ++ (fs ++ (fss.flatten ++ ys))) = S at *
    generalize deliveredRecords st xs = k1 at *
    generalize deliveredRecords st (xs ++ fs) = k2 at *
    generalize deliveredRecords st (xs ++ fs ++ fss.flatten) = k3 at *
    obtain ⟨d, rfl⟩ : ∃ d, k2 = k1 + d := ⟨k2 - k1, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ d', k3 = k1 + d + d' := ⟨k3 - (k1 + d), by omega⟩
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.add_assoc, Nat.add_sub_cancel_left, List.take_add,
      List.drop_drop]

/-! ## FIFO, per-block boundary, fate, and latency -/

/-- **The history FIFO.** Every committed submission, after the start queue, is in order either a record the blocks
emitted or a record still in the final queue. -/
theorem history_fifo (R : Reading q) {L : Linked q} (DL : DrainLinked L) (P : Premises L cfg start blocks stop st) :
    st.queue.map q.out ++ submissions L blocks = emissions R L blocks ++ remainingQueue R L stop := by
  obtain ⟨fss, hf, chain, subs⟩ := P.steps DL
  have slots : queueBase q.width (st.tail + (RequestQueue.submissions fss.flatten).length) ≤ 2 ^ 256 := by
    rw [subs]; exact P.slots
  have count : st.count + (RequestQueue.submissions fss.flatten).length < 2 ^ 256 := by
    rw [subs]; exact P.count
  have em := emissions_segments R L hf (xs := []) (ys := [])
    (by simpa only [List.nil_append, List.append_nil] using chain) P.rep
    (by simpa only [List.nil_append, List.append_nil] using slots)
    (by simpa only [List.nil_append, List.append_nil] using count)
  have z : deliveredRecords st ([] : List (Step q)) = 0 := rfl
  simp only [List.nil_append, List.append_nil] at em
  rw [z, Nat.sub_zero, List.drop_zero] at em
  have d := chain.delivered P.rep slots count
  unfold remainingQueue
  rw [storedQueue_eq R d.represents, d.queue, em, ← List.map_append, List.take_append_drop, submissions, ← subs,
    List.map_append]

/-- **One block's emission and request boundary.** Every covered-fork block has a unique request-step frame `f` at the
contract (`requestFrame L.address b = some f`), emits the first `q.cap` records of the queue `f` read, and the
submissions through its request boundary, after the start queue, equal the earlier blocks' emissions followed by that
queue. -/
theorem history_block (R : Reading q) {L : Linked q} (DL : DrainLinked L) (P : Premises L cfg start blocks stop st)
    {pre post : List KeptBlock} {b : KeptBlock} (split : blocks = pre ++ b :: post) :
    ((blockEmissions R L b).flatten = blockDelivered L.ty b ∧ ∀ e ∈ blockEmissions R L b, e.length = R.size) ∧
    (∃ f, requestFrame L.address b = some f) ∧
    blockEmissions R L b = (queueAtRequests R L b).take q.cap ∧
    st.queue.map q.out ++ submissions L pre ++ boundarySubmissions L b =
      emissions R L pre ++ queueAtRequests R L b := by
  obtain ⟨fss, hf, chain, subs⟩ := P.steps DL
  rw [split] at hf
  obtain ⟨fpre, fs, fpost, rfl, hpre, hb, -⟩ := Blanc.List.forall₂_split hf
  have eF : (fpre ++ fs :: fpost).flatten = fpre.flatten ++ (fs ++ fpost.flatten) := by
    rw [List.flatten_append, List.flatten_cons]
  rw [eF] at chain subs
  have slots : queueBase q.width (st.tail + (RequestQueue.submissions (fpre.flatten ++ (fs ++ fpost.flatten))).length)
      ≤ 2 ^ 256 := by rw [subs]; exact P.slots
  have count : st.count + (RequestQueue.submissions (fpre.flatten ++ (fs ++ fpost.flatten))).length < 2 ^ 256 := by
    rw [subs]; exact P.count
  obtain ⟨kpre, f, kpost, hk, fsys, others, found, taken⟩ :=
    Blanc.List.split_of_filter_length_one isSystemFrame hb.2.2
  have corr := hb.1
  rw [hk] at corr
  obtain ⟨gs, g, hs, rfl, cg, mg, ch⟩ := Blanc.List.forall₂_split corr
  have fcaller : f.sevm.caller = systemAddress := by simpa only [isSystemFrame, decide_eq_true_eq] using fsys
  obtain ⟨next, gdrain⟩ := mg.system_step fcaller
  obtain ⟨ndg, outg⟩ := DrainCorresponds.noDrain cg fun x hx => by
    simpa only [isSystemFrame, decide_eq_false_iff_not] using others x (List.mem_append_left _ hx)
  obtain ⟨-, outh⟩ := DrainCorresponds.noDrain ch fun x hx => by
    simpa only [isSystemFrame, decide_eq_false_iff_not] using others x (List.mem_append_right _ hx)
  set X := fpre.flatten
  set Y := fpost.flatten
  have e : X ++ ((gs ++ g :: hs) ++ Y) = (X ++ gs) ++ g :: (hs ++ Y) := by
    simp only [List.append_assoc, List.cons_append]
  rw [e] at chain slots count
  have hl : (RequestQueue.submissions (X ++ gs)).length ≤
      (RequestQueue.submissions ((X ++ gs) ++ g :: (hs ++ Y))).length := by
    rw [submissions_steps_append (X ++ gs), List.length_append]
    omega
  have slotsP : queueBase q.width (st.tail + (RequestQueue.submissions (X ++ gs)).length) ≤ 2 ^ 256 :=
    (queueBase_mono _ (by omega)).trans slots
  have countP : st.count + (RequestQueue.submissions (X ++ gs)).length < 2 ^ 256 := by omega
  have out := chain.drain_delivers P.rep slotsP countP gdrain
  have kX : deliveredRecords st (X ++ gs) = deliveredRecords st X := deliveredRecords_noDrain st X ndg
  rw [kX] at out
  have sysOut : output (gs ++ g :: hs) = g.output := by
    unfold output at outg outh ⊢
    rw [List.flatMap_append, List.flatMap_cons, outg, outh, List.nil_append, List.append_nil]
  have deliv : blockDelivered L.ty b = (((st.queue ++ RequestQueue.submissions (X ++ gs)).drop
      (deliveredRecords st X)).take q.cap).flatMap q.out := by
    rw [← hb.2.1, sysOut, out]
  obtain ⟨m, h1, h2⟩ := chain.append_split
  have starts : g.before = m := by
    cases h2 with
    | cons starts _ => exact starts
  have d := h1.delivered P.rep slotsP countP
  have queue : queueAtRequests R L b = ((st.queue ++ RequestQueue.submissions (X ++ gs)).drop
      (deliveredRecords st X)).map q.out := by
    unfold queueAtRequests requestFrame
    rw [found]
    dsimp only
    rw [← mg.before, starts, storedQueue_eq R d.represents, d.queue, kX]
  refine ⟨?_, ⟨f, found⟩, ?_, ?_⟩
  · rw [blockEmissions_of_output R L deliv, deliv, List.flatMap_def]
    refine ⟨rfl, fun e he => ?_⟩
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp he
    exact R.out_length r
  · rw [blockEmissions_of_output R L deliv, queue, List.map_take]
  · have hsubPre : submissions L pre = (RequestQueue.submissions X).map q.out := by
      unfold submissions
      rw [(corresponds_flatten hpre).toCorresponds.submissions]
    have hbound : boundarySubmissions L b = (RequestQueue.submissions gs).map q.out := by
      unfold boundarySubmissions
      rw [taken, ← (DrainCorresponds.toCorresponds cg).submissions]
    have em := emissions_segments R L hpre (xs := []) (ys := (gs ++ g :: hs) ++ Y)
      (by simpa only [List.nil_append, List.append_assoc, List.cons_append] using chain)
      P.rep (by simpa only [List.nil_append, List.append_assoc, List.cons_append] using slots)
      (by simpa only [List.nil_append, List.append_assoc, List.cons_append] using count)
    have z : deliveredRecords st ([] : List (Step q)) = 0 := rfl
    rw [List.nil_append, List.nil_append, z, Nat.sub_zero, List.drop_zero] at em
    have hk : deliveredRecords st X ≤ (st.queue ++ RequestQueue.submissions X).length := deliveredRecords_le st X
    have tS : (st.queue ++ RequestQueue.submissions (X ++ ((gs ++ g :: hs) ++ Y))).take (deliveredRecords st X) =
        (st.queue ++ RequestQueue.submissions X).take (deliveredRecords st X) := by
      rw [submissions_steps_append, ← List.append_assoc, List.take_append_of_le_length hk]
    have tT : (st.queue ++ RequestQueue.submissions (X ++ gs)).take (deliveredRecords st X) =
        (st.queue ++ RequestQueue.submissions X).take (deliveredRecords st X) := by
      rw [submissions_steps_append, ← List.append_assoc, List.take_append_of_le_length hk]
    rw [hsubPre, hbound, em, tS, queue, ← tT]
    conv => rhs; rw [← List.map_append, List.take_append_drop]
    rw [submissions_steps_append, List.map_append, List.map_append, List.append_assoc]

theorem emissions_take_succ (R : Reading q) (L : Linked q) {j : Nat} {x : KeptBlock} (h : blocks[j]? = some x) :
    emissions R L (blocks.take (j + 1)) = emissions R L (blocks.take j) ++ blockEmissions R L x := by
  rw [List.take_add_one, h, Option.toList_some, emissions_append]
  simp only [emissions, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem emissions_take_mono (R : Reading q) (L : Linked q) {i i' : Nat} (h : i ≤ i') :
    (emissions R L (blocks.take i)).length ≤ (emissions R L (blocks.take i')).length := by
  have e : blocks.take i' = blocks.take i ++ (blocks.take i').drop i := by
    conv_lhs => rw [← List.take_append_drop i (blocks.take i')]
    rw [List.take_take, Nat.min_eq_left h]
  rw [e, emissions_append, List.length_append]
  omega

/-- **The fate of every submission (occurrence-indexed).** Every committed submission `n`, after the start queue, is
either emitted as record `k` of block `j` for a unique pair `(j, k)` or still queued at the end at `n − E`. -/
theorem history_fate (R : Reading q) {L : Linked q} (DL : DrainLinked L) (P : Premises L cfg start blocks stop st)
    (n : Nat) :
    (n < (emissions R L blocks).length ∧
      ∃ j k, ∃ hj : j < blocks.length, k < (blockEmissions R L blocks[j]).length ∧
        (emissions R L (blocks.take j)).length + k = n ∧
        (blockEmissions R L blocks[j])[k]? = (st.queue.map q.out ++ submissions L blocks)[n]? ∧
        (∀ a, j < a ↔ n < (emissions R L (blocks.take a)).length) ∧
        ∀ j' k' (hj' : j' < blocks.length), k' < (blockEmissions R L blocks[j']).length →
          (emissions R L (blocks.take j')).length + k' = n → j' = j ∧ k' = k) ∨
    ((emissions R L blocks).length ≤ n ∧
      (remainingQueue R L stop)[n - (emissions R L blocks).length]? =
        (st.queue.map q.out ++ submissions L blocks)[n]?) := by
  have fifo := history_fifo R DL P
  by_cases hE : n < (emissions R L blocks).length
  · left
    refine ⟨hE, ?_⟩
    obtain ⟨j, k, hj, hk, pos⟩ := Blanc.List.exists_flatMap_position (blockEmissions R L) blocks hE
    have get := Blanc.List.getElem?_flatMap_position (blockEmissions R L) blocks hj hk
    refine ⟨j, k, hj, hk, pos, ?_, ?_, ?_⟩
    · rw [fifo, List.getElem?_append_left hE, ← get]
      unfold emissions
      rw [pos]
    · intro a
      have hx : blocks[j]? = some blocks[j] := List.getElem?_eq_getElem hj
      have succ := congrArg List.length (emissions_take_succ R L hx)
      rw [List.length_append] at succ
      have e : (emissions R L (blocks.take j)).length = ((blocks.take j).flatMap (blockEmissions R L)).length := rfl
      constructor
      · intro ha
        have := emissions_take_mono (blocks := blocks) R L (show j + 1 ≤ a by omega)
        omega
      · intro hlt
        by_contra hge
        have := emissions_take_mono (blocks := blocks) R L (Nat.le_of_not_lt hge)
        omega
    · intro j' k' hj' hk' pos'
      exact Blanc.List.flatMap_position_inj (blockEmissions R L) blocks hj' hj hk' hk (pos'.trans pos.symm)
  · right
    refine ⟨Nat.le_of_not_lt hE, ?_⟩
    rw [fifo, List.getElem?_append_right (Nat.le_of_not_lt hE)]

/-- **Latency, occurrence-indexed.** If record `r` sits at position `q0` of the queue block `j`'s request step read,
and the history reaches block `j + q0 / q.cap`, then block `j + q0 / q.cap` emits `r` as its record `q0 % q.cap`,
preceded by the queue's records from `q.cap * (q0 / q.cap)`, and `r` is submission occurrence `E_j + q0` after the
start queue. -/
theorem history_latency (R : Reading q) {L : Linked q} (DL : DrainLinked L) (P : Premises L cfg start blocks stop st)
    (hcap : 0 < q.cap) {j q0 : Nat} {B D : KeptBlock} {r : Bytes}
    (hB : blocks[j]? = some B) (hD : blocks[j + q0 / q.cap]? = some D)
    (queued : (queueAtRequests R L B)[q0]? = some r) :
    (blockEmissions R L D)[q0 % q.cap]? = some r ∧
    (∀ i ≤ q0 % q.cap, (blockEmissions R L D)[i]? = (queueAtRequests R L B)[q.cap * (q0 / q.cap) + i]?) ∧
    (st.queue.map q.out ++ submissions L blocks)[(emissions R L (blocks.take j)).length + q0]? = some r ∧
    (emissions R L (blocks.take j)).length + q0 =
      (emissions R L (blocks.take (j + q0 / q.cap))).length + q0 % q.cap := by
  let T : Nat → KeptBlock → List Bytes := fun i x =>
    st.queue.map q.out ++ submissions L (blocks.take i) ++ boundarySubmissions L x
  let E : Nat → Nat := fun i => (emissions R L (blocks.take i)).length
  have A : ∀ i x, blocks[i]? = some x → True →
      blockEmissions R L x = (queueAtRequests R L x).take q.cap ∧
      T i x = emissions R L (blocks.take i) ++ queueAtRequests R L x := by
    intro i x hx _
    have hb := history_block R DL P (Blanc.List.eq_take_cons_drop hx)
    exact ⟨hb.2.2.1, hb.2.2.2⟩
  have A1 : ∀ i x, blocks[i]? = some x → True → ∀ k, (T i x)[E i + k]? = (queueAtRequests R L x)[k]? := by
    intro i x hx tr k
    rw [(A i x hx tr).2, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have A2 : ∀ i x, blocks[i]? = some x → True → blockEmissions R L x = (queueAtRequests R L x).take q.cap :=
    fun i x hx tr => (A i x hx tr).1
  have bpre : ∀ x, boundarySubmissions L x <+: submissions L [x] := by
    intro x
    unfold boundarySubmissions submissions kept
    rw [List.flatMap_singleton]
    exact ((List.takeWhile_prefix _).filterMap _).map _
  have subsSucc : ∀ i x, blocks[i]? = some x →
      submissions L (blocks.take (i + 1)) = submissions L (blocks.take i) ++ submissions L [x] := by
    intro i x hx
    rw [List.take_add_one, hx, Option.toList_some, submissions_append]
  have B2 : ∀ i x y, blocks[i]? = some x → blocks[i + 1]? = some y → T i x <+: T (i + 1) y := by
    intro i x y hx _
    obtain ⟨u, hu⟩ := bpre x
    refine ⟨u ++ boundarySubmissions L y, ?_⟩
    show (st.queue.map q.out ++ submissions L (blocks.take i) ++ boundarySubmissions L x) ++
      (u ++ boundarySubmissions L y) = st.queue.map q.out ++ submissions L (blocks.take (i + 1)) ++
        boundarySubmissions L y
    rw [subsSucc i x hx, ← hu]
    simp only [List.append_assoc]
  have B3 : ∀ i x, blocks[i]? = some x → E (i + 1) = E i + (blockEmissions R L x).length := by
    intro i x hx
    show (emissions R L (blocks.take (i + 1))).length = _
    rw [emissions_take_succ R L hx, List.length_append]
  have B1 : T j B <+: st.queue.map q.out ++ submissions L blocks := by
    obtain ⟨u, hu⟩ := bpre B
    refine ⟨u ++ submissions L (blocks.drop (j + 1)), ?_⟩
    show (st.queue.map q.out ++ submissions L (blocks.take j) ++ boundarySubmissions L B) ++
      (u ++ submissions L (blocks.drop (j + 1))) = st.queue.map q.out ++ submissions L blocks
    conv_rhs => rw [← List.take_append_drop (j + 1) blocks, submissions_append, subsSucc j B hB, ← hu]
    simp only [List.append_assoc]
  have hlen : j + q0 / q.cap < blocks.length := (List.getElem?_eq_some_iff.mp hD).1
  have core := Blanc.List.drain_position q.cap hcap blocks (fun _ => True) (blockEmissions R L)
    (queueAtRequests R L) T E A1 A2 B2 B3
  have hT : (T j B)[E j + q0]? = some r := by rw [A1 j B hB trivial]; exact queued
  obtain ⟨y, hy, hbe, hidx⟩ := core (q0 / q.cap) j q0 B r rfl hB hlen (fun _ _ _ _ => trivial) hT
  rw [hD] at hy
  cases hy
  refine ⟨hbe, ?_, ?_, hidx⟩
  · intro i hi
    have hmod : i < q.cap := Nat.lt_of_le_of_lt hi (Nat.mod_lt _ hcap)
    have hdiv : (q.cap * (q0 / q.cap) + i) / q.cap = q0 / q.cap := by
      rw [Nat.mul_add_div hcap, Nat.div_eq_of_lt hmod, Nat.add_zero]
    have hm : (q.cap * (q0 / q.cap) + i) % q.cap = i := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hmod]
    have qlt : q0 < (queueAtRequests R L B).length := (List.getElem?_eq_some_iff.mp queued).1
    have split := Nat.div_add_mod q0 q.cap
    have hlt : q.cap * (q0 / q.cap) + i < (queueAtRequests R L B).length := by omega
    have hq' := List.getElem?_eq_getElem hlt
    have hT' : (T j B)[E j + (q.cap * (q0 / q.cap) + i)]? =
        some (queueAtRequests R L B)[q.cap * (q0 / q.cap) + i] := by
      rw [A1 j B hB trivial]; exact hq'
    obtain ⟨y', hy', hbe', -⟩ := core (q0 / q.cap) j _ B _ hdiv hB hlen (fun _ _ _ _ => trivial) hT'
    rw [hD] at hy'
    cases hy'
    rw [hm] at hbe'
    rw [hbe', hq']
  · obtain ⟨u, hu⟩ := B1
    rw [← hu, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hT).1]
    exact hT

end History

end Blanc.Lift.RequestQueue.Occurrence
