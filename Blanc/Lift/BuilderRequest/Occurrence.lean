import Batteries.Tactic.OpenPrivate
import Blanc.ListChunks
import Blanc.ListFlatMapPosition
import Blanc.Lift.BuilderRequest.ChainLink

/-!
# Occurrence-indexed submissions, emissions and queues over a kept history

The EIP-8282 history results in `ChainLink` give a byte prefix: what the blocks output as requests of type `ty` is a
prefix of the submitted records' bytes. This module indexes it by occurrence and by block, for any builder contract
with a `Reading` of its stored queue. All observers read only the history:

* `submissions c blocks`: every committed paid submission at the contract, in order, in output form;
* `blockEmissions R ty b`: the records block `b` outputs as requests of type `ty`, its request bytes cut into
  `R.size`-byte records; `emissions R ty blocks` is their concatenation, block by block;
* `remainingQueue R stop`: the live queue in the history's final storage, read head to tail;
* `queueAtRequests R b`: the live queue in the storage the block's request step read;
* `boundarySubmissions c b`: the submissions of block `b` kept before its request step.

`history_fifo` is the FIFO: the submissions are the emissions followed by the remaining queue.
`history_requests` is the per-block cap: an Amsterdam block emits the first `cap` records of the queue its request
step read, and that queue is the submissions through the block's request boundary minus the earlier emissions; a
block at a covered fork emits nothing. `history_fate` and `history_latency` are the occurrence forms B2 and B6 read.

Everything is derived from the byte-level delivery (`Chain.delivered`, `Chain.call_delivers`) and the per-block chain
link; no bytecode is re-walked.
-/

namespace Blanc.Lift.BuilderRequest.Occurrence

open Jaune Delivery ChainLink

open private withdrawalsPass_getCode from Blanc.ExecutionKeptChain

/-! ## Reading a stored queue -/

/-- How a builder contract's stored queue reads back in output form. -/
structure Reading (c : Contract) where
  /-- Record `i` past the head `h`, in output form, read off the storage. -/
  read : (B256 → B256) → B256 → B256 → Bytes
  /-- Bytes per record in a system call's output. -/
  size : Nat
  size_pos : 0 < size
  out_length : ∀ r, (c.out r).length = size
  /-- On storage representing a queue, the reader returns the live records in output form. -/
  read_eq : ∀ {rd : B256 → B256} {st : QueueState c.Record}, Represents c.width c.words rd st →
    ∀ i (hi : i < st.queue.length), read rd st.head.toB256 i.toB256 = c.out st.queue[i]

variable {c : Contract} {ty : UInt8}

/-- The live queue a storage holds, from the head (slot 2) to the tail (slot 3), in output form. -/
def storedQueue (R : Reading c) (rd : B256 → B256) : List Bytes :=
  (List.range ((rd 3).toNat - (rd 2).toNat)).map fun i => R.read rd (rd 2) i.toB256

theorem storedQueue_eq (R : Reading c) {rd : B256 → B256} {st : QueueState c.Record}
    (rep : Represents c.width c.words rd st) : storedQueue R rd = st.queue.map c.out := by
  have length : (rd 3).toNat - (rd 2).toNat = st.queue.length := by
    rw [rep.head, rep.tail, B256.toNat_toB256_of_lt rep.head_lt, B256.toNat_toB256_of_lt rep.tail_lt]
    have := rep.coherent
    omega
  unfold storedQueue
  rw [length, rep.head]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i h1 _
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    exact R.read_eq rep i h1

/-! ## The observers -/

/-- A kept frame with the system caller. -/
def isSystemFrame (f : Exec.Frame) : Bool := decide (f.sevm.caller = systemAddress)

/-- Every committed paid submission the blocks keep at the contract, in order, in output form. -/
def submissions (c : Contract) (blocks : List KeptBlock) : List Bytes :=
  (History.submitted c blocks).map c.out

/-- The records one block outputs as requests of type `ty`: its type-`ty` request bytes cut at `R.size` bytes. A short
trailing piece is kept, never padded or dropped. -/
def blockEmissions (R : Reading c) (ty : UInt8) (b : KeptBlock) : List Bytes :=
  Blanc.List.chunksOf R.size (blockDelivered ty b)

/-- The records the blocks output as requests of type `ty`, block by block, in order. -/
def emissions (R : Reading c) (ty : UInt8) (blocks : List KeptBlock) : List Bytes :=
  blocks.flatMap (blockEmissions R ty)

/-- The live queue the contract's storage holds at the history's end. -/
def remainingQueue (R : Reading c) (stop : BlockChain) : List Bytes :=
  storedQueue R (stop.state.getStor c.address).get

/-- The frame a block's request step ran at `a`: its first kept frame there with the system caller. -/
def requestFrame (a : Adr) (b : KeptBlock) : Option Exec.Frame :=
  (b.keptAt a).find? isSystemFrame

/-- The live queue in the storage the block's request step at the contract read; empty if it has none. -/
def queueAtRequests (R : Reading c) (b : KeptBlock) : List Bytes :=
  match requestFrame c.address b with
  | some f => storedQueue R (Devm.getStor f.pre c.address).get
  | none => []

/-- The submissions a block keeps at the contract before its request step, in output form. -/
def boundarySubmissions (c : Contract) (b : KeptBlock) : List Bytes :=
  (((b.keptAt c.address).takeWhile fun f => !isSystemFrame f).filterMap (submittedBy c)).map c.out

theorem submitted_append (xs ys : List KeptBlock) :
    History.submitted c (xs ++ ys) = History.submitted c xs ++ History.submitted c ys := by
  simp only [History.submitted, History.kept, List.flatMap_append, List.filterMap_append]

theorem submissions_append (xs ys : List KeptBlock) :
    submissions c (xs ++ ys) = submissions c xs ++ submissions c ys := by
  simp only [submissions, submitted_append, List.map_append]

theorem emissions_append (R : Reading c) (xs ys : List KeptBlock) :
    emissions R ty (xs ++ ys) = emissions R ty xs ++ emissions R ty ys := List.flatMap_append

/-! ## The delivery model over prefixes -/

section Model

variable {Record : Type}

theorem deliveredCount_noSystem (cap : Nat) (target : B256) :
    ∀ (st : QueueState Record) {es : List (Event Record)}, NoSystem es → deliveredCount cap target st es = 0
  | _, [], _ => rfl
  | st, e :: es, h => by
    have tail := deliveredCount_noSystem cap target (step cap target st e) (es := es)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have he : chunk cap st e = [] := by
      cases e with
      | submission r => rfl
      | feeRead => rfl
      | system latch => exact absurd rfl (h _ List.mem_cons_self latch)
    unfold deliveredCount at tail ⊢
    show (chunk cap st e :: chunks cap target (step cap target st e) es).flatten.length = 0
    rw [List.flatten_cons, he, List.nil_append]
    exact tail

end Model

variable {s t : Stor} {st : QueueState c.Record}

theorem deliveredRecords_noSystem (st : QueueState c.Record) (xs : List (Delivery.Frame c))
    {ys : List (Delivery.Frame c)} (h : NoSystem (events ys)) :
    deliveredRecords st (xs ++ ys) = deliveredRecords st xs := by
  have zero := deliveredCount_noSystem c.cap c.target (replay c.cap c.target st (events xs)) h
  unfold deliveredCount at zero
  simp only [deliveredRecords, deliveredCount, events, List.map_append, chunks_append, List.flatten_append,
    List.length_append]
  simp only [events] at zero
  omega

theorem systemOutput_noSystem : ∀ {fs : List (Delivery.Frame c)}, NoSystem (events fs) → systemOutput fs = []
  | [], _ => rfl
  | f :: fs, h => by
    show f.output ++ systemOutput fs = []
    rw [f.output_user (fun latch he => h f.event List.mem_cons_self latch he),
      systemOutput_noSystem (fun e he => h e (List.mem_cons_of_mem _ he)), List.nil_append]

theorem deliveredRecords_le (st : QueueState c.Record) (xs : List (Delivery.Frame c)) :
    deliveredRecords st xs ≤ (st.queue ++ Delivery.submissions xs).length := by
  have := congrArg List.length (delivered_append_queue c.cap c.target st (events xs))
  rw [List.length_append] at this
  unfold deliveredRecords deliveredCount Delivery.submissions
  omega

/-- On a chain with the word range over all its frames, a prefix delivers the oldest records of the whole. -/
theorem prefix_facts {xs ys : List (Delivery.Frame c)} (chain : Chain s (xs ++ ys) t) (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (Delivery.submissions (xs ++ ys)).length) ≤ 2 ^ 256)
    (count : st.count + (Delivery.submissions (xs ++ ys)).length < 2 ^ 256) :
    ∃ m, Chain s xs m ∧ Chain m ys t ∧ Delivered st xs m ∧
      systemOutput xs = ((st.queue ++ Delivery.submissions (xs ++ ys)).take (deliveredRecords st xs)).flatMap c.out := by
  obtain ⟨m, h1, h2⟩ := chain.append_split
  have hl : (Delivery.submissions xs).length ≤ (Delivery.submissions (xs ++ ys)).length := by
    rw [Delivery.submissions_append, List.length_append]
    omega
  have d := h1.delivered rep ((queueBase_mono _ (by omega)).trans slots) (by omega)
  refine ⟨m, h1, h2, d, ?_⟩
  rw [d.output, Delivery.submissions_append, ← List.append_assoc,
    List.take_append_of_le_length (deliveredRecords_le st xs)]

/-- **One segment's output.** The frames `fs` between `xs` and `ys` output the records delivered from the end of
`xs`'s delivery up to the end of `fs`'s, in order. -/
theorem segment_output {xs fs ys : List (Delivery.Frame c)} (chain : Chain s (xs ++ (fs ++ ys)) t)
    (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (Delivery.submissions (xs ++ (fs ++ ys))).length) ≤ 2 ^ 256)
    (count : st.count + (Delivery.submissions (xs ++ (fs ++ ys))).length < 2 ^ 256) :
    systemOutput fs = (((st.queue ++ Delivery.submissions (xs ++ (fs ++ ys))).drop (deliveredRecords st xs)).take
      (deliveredRecords st (xs ++ fs) - deliveredRecords st xs)).flatMap c.out := by
  obtain ⟨-, -, -, -, o1⟩ := prefix_facts chain rep slots count
  have chain' : Chain s ((xs ++ fs) ++ ys) t := by rwa [List.append_assoc]
  have e : xs ++ (fs ++ ys) = (xs ++ fs) ++ ys := (List.append_assoc _ _ _).symm
  obtain ⟨-, -, -, -, o2⟩ := prefix_facts chain' rep (by rwa [← e]) (by rwa [← e])
  rw [← e] at o2
  have le : deliveredRecords st xs ≤ deliveredRecords st (xs ++ fs) := deliveredRecords_prefix st xs fs
  obtain ⟨d, hd⟩ : ∃ d, deliveredRecords st (xs ++ fs) = deliveredRecords st xs + d := ⟨_, (Nat.add_sub_cancel' le).symm⟩
  have split : systemOutput (xs ++ fs) = systemOutput xs ++ systemOutput fs := List.flatMap_append
  rw [o2, o1, hd, List.take_add, List.flatMap_append] at split
  rw [hd, Nat.add_sub_cancel_left]
  exact (List.append_cancel_left split).symm

/-! ## A block's frames -/

/-- The delivery frames of one block: they are its kept frames at the contract, they output its requests of type
`ty`, and the block has one kept frame there with the system caller at Amsterdam and none at a covered fork. -/
def BlockFrames (c : Contract) (ty : UInt8) (fs : List (Delivery.Frame c)) (b : KeptBlock) : Prop :=
  Corresponds c fs (b.keptAt c.address) ∧ systemOutput fs = blockDelivered ty b ∧
    ((b.keptAt c.address).filter isSystemFrame).length = if b.fork = .amsterdam then 1 else 0

/-- **The request fold's system frames at the contract**: one per listed step at it. -/
theorem fold_systemCount (L : Linked c ty) {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv}
    {acc acc' : List Bytes} {bal bal' : BalBuilder} {final : State} {steps : List RequestStep}
    (h : RequestRoots idx contracts benv acc bal final acc' bal' steps)
    (code : benv.state.getCode c.address = c.code)
    (onlyAmsterdam : ∀ p ∈ contracts, p.2 = c.address → benv.stat.fork = .amsterdam)
    (others : ∀ s ∈ steps, s.target ≠ c.address → ∀ f ∈ s.roots.flatMap (Root.keptAt c.address),
      f.sevm.caller ≠ systemAddress) :
    (((requestRootsOf steps).flatMap (Root.keptAt c.address)).filter isSystemFrame).length =
      (contracts.filter fun p => decide (p.2 = c.address)).length := by
  induction h with
  | nil benv acc bal => rfl
  | @cons type target rest benv acc acc' bal bal' post final out rs steps hcall roots tail ih =>
      have split : (requestRootsOf (⟨type, target, post, out, rs⟩ :: steps)).flatMap (Root.keptAt c.address) =
          rs.flatMap (Root.keptAt c.address) ++ (requestRootsOf steps).flatMap (Root.keptAt c.address) := by
        unfold requestRootsOf
        rw [List.flatMap_cons, List.flatMap_append]
      have hc : (benv.state.getCode c.address).toList ≠ [] := by rw [code]; exact L.runnable.1
      have hd : ¬ isValidDelegation (benv.state.getCode c.address) := by rw [code]; exact L.runnable.2
      have code' : post.getCode c.address = benv.state.getCode c.address := (MessageRoots.chain roots hc hd).2
      have below := ih (code'.trans code) (fun p hp => onlyAmsterdam p (List.mem_cons_of_mem _ hp))
        (fun s hs => others s (List.mem_cons_of_mem _ hs))
      rw [split, List.filter_append, List.length_append, below, List.filter_cons]
      by_cases here : target = c.address
      · subst here
        obtain ⟨f, flat, caller, -⟩ := request_step_root (onlyAmsterdam _ List.mem_cons_self rfl)
          hc hd (L.placed.precompile _ (.inr rfl)) hcall roots
        rw [flat]
        simp only [isSystemFrame, caller, decide_true, List.filter_cons_of_pos, List.filter_nil,
          List.length_cons, List.length_nil, ↓reduceIte]
        omega
      · have none : (rs.flatMap (Root.keptAt c.address)).filter isSystemFrame = [] := by
          rw [List.filter_eq_nil_iff]
          intro f hf
          simp only [isSystemFrame, decide_eq_true_eq]
          exact others _ List.mem_cons_self here f hf
        rw [none]
        simp only [here, decide_false, Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.zero_add]

/-- Amsterdam lists the contract exactly once. -/
theorem _root_.Blanc.Lift.BuilderRequest.ChainLink.Linked.amsterdam_count (L : Linked c ty) :
    (amsterdamRequests.filter fun p => decide (p.2 = c.address)).length = 1 := by
  have e : amsterdamRequests.filter (fun p => decide (p.2 = c.address)) =
      (amsterdamRequests.filter fun p => p.1 == ty || p.2 == c.address).filter
        (fun p => decide (p.2 = c.address)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro p _
    by_cases hp : p.2 = c.address
    · simp only [hp, decide_true, beq_self_eq_true, Bool.or_true, Bool.and_self]
    · simp only [hp, decide_false, Bool.false_and]
  rw [e, L.listed, List.filter_cons_of_pos (p := fun p : UInt8 × Adr => decide (p.2 = c.address)) (decide_eq_true rfl)]
  rfl

/-- **A body's system frames at the contract**: one at Amsterdam, none at a covered fork. -/
theorem body_systemCount (L : Linked c ty) {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput} {run : BodyRun}
    (h : BodyRoots benv txs ommers wds state bout run)
    (rules : KeptRules benv.stat.rules) (fork : KeptFork benv.stat.fork)
    (code : benv.state.getCode c.address = c.code) (created : c.address ∉ benv.createdAccounts)
    (outside : ∀ f ∈ run.outsideRequests c.address, f.sevm.caller ≠ systemAddress)
    (others : ∀ s ∈ run.requests, s.target ≠ c.address → ∀ f ∈ s.roots.flatMap (Root.keptAt c.address),
      f.sevm.caller ≠ systemAddress) :
    ((run.roots.flatMap (Root.keptAt c.address)).filter isSystemFrame).length =
      if benv.stat.fork = .amsterdam then 1 else 0 := by
  have split : run.roots.flatMap (Root.keptAt c.address) = run.outsideRequests c.address ++
      (requestRootsOf run.requests).flatMap (Root.keptAt c.address) := by
    unfold BodyRun.roots BodyRun.outsideRequests
    rw [List.flatMap_append]
  have first : (run.outsideRequests c.address).filter isSystemFrame = [] := by
    rw [List.filter_eq_nil_iff]
    intro f hf
    simp only [isSystemFrame, decide_eq_true_eq]
    exact outside f hf
  rw [split, List.filter_append, first, List.nil_append]
  have hs : run.txEnv.stat = benv.stat := h.txEnv_stat
  by_cases on : benv.stat.rules.header.requestsHash = true
  · obtain ⟨st, out, pass, -, -⟩ := h.stages
    obtain ⟨decoded, -, roots⟩ := h.transactions
    have on' : (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut
        wds).1).stat.rules.header.requestsHash = true := by
      change run.txEnv.stat.rules.header.requestsHash = true
      rw [hs]
      exact on
    unfold RequestPass at pass
    rw [ite_eq_left on'] at pass
    obtain ⟨deposits, acc, bal, -, fold, -⟩ := pass
    have hc : (benv.state.getCode c.address).toList ≠ [] := by rw [code]; exact L.runnable.1
    have hd : ¬ isValidDelegation (benv.state.getCode c.address) := by rw [code]; exact L.runnable.2
    have code₁ := (h.pre.chain hc hd).2
    have code₂ := (roots.chain rules (a := c.address) (by simpa only [Benv.withState, code₁] using hc)
      (by simpa only [Benv.withState, code₁] using hd) created).2
    have count := fold_systemCount L fold
      ((withdrawalsPass_getCode _ _ _ _ c.address).trans (code₂.trans (code₁.trans code)))
      (by
        intro p hp here
        change run.txEnv.stat.fork = .amsterdam
        rw [hs]
        refine L.onlyAmsterdam fork p ?_ here
        change p ∈ run.txEnv.stat.fork.ruleSet.requests at hp
        rw [hs] at hp
        exact hp)
      others
    rw [count]
    change (run.txEnv.stat.fork.ruleSet.requests.filter fun p => decide (p.2 = c.address)).length = _
    rw [hs]
    rcases fork with covered | amsterdam
    · have none : benv.stat.fork.ruleSet.requests.filter (fun p => decide (p.2 = c.address)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        simp only [decide_eq_true_eq]
        exact (L.unlisted _ covered p hp).2
      have ne : benv.stat.fork ≠ .amsterdam := fun e => CoveredFork.not_amsterdam (e ▸ covered)
      rw [none, ite_eq_right ne]
      rfl
    · rw [amsterdam, ite_eq_left rfl]
      exact L.amsterdam_count
  · rw [h.requests_off on]
    have ne : benv.stat.fork ≠ .amsterdam := by
      intro e
      apply on
      change benv.stat.fork.ruleSet.header.requestsHash = true
      rw [e]
      rfl
    rw [ite_eq_right ne]
    rfl

/-! ## A history's frames, block by block -/

section History

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

/-- **The per-block chain link.** Each block's kept frames at the contract have delivery frames outputting its requests
of type `ty`, with one system frame at Amsterdam and none at a covered fork. -/
theorem blockFrames (L : Linked c ty) (h : KeptHistory cfg start blocks stop)
    (code : start.state.getCode c.address = c.code)
    (outside : ∀ b ∈ blocks, ∀ f ∈ b.run.outsideRequests c.address, f.sevm.caller ≠ systemAddress)
    (others : ∀ b ∈ blocks, ∀ s ∈ b.run.requests, s.target ≠ c.address →
      ∀ f ∈ s.roots.flatMap (Root.keptAt c.address), f.sevm.caller ≠ systemAddress)
    (entries : ∀ b ∈ blocks, ∀ f ∈ b.keptAt c.address, Exec.Frame.EntryIn c.address c.code b.benv.stat f) :
    ∃ fss : List (List (Delivery.Frame c)), List.Forall₂ (BlockFrames c ty) fss blocks := by
  have hc : (start.state.getCode c.address).toList ≠ [] := by rw [code]; exact L.runnable.1
  have hd : ¬ isValidDelegation (start.state.getCode c.address) := by rw [code]; exact L.runnable.2
  induction h with
  | refl => exact ⟨[], .nil⟩
  | @step blocks b post prior step ih =>
      have mem : b ∈ blocks ++ [b] := List.mem_append_right _ List.mem_cons_self
      obtain ⟨fss, below⟩ := ih (fun x hx => outside x (List.mem_append_left _ hx))
        (fun x hx => others x (List.mem_append_left _ hx)) (fun x hx => entries x (List.mem_append_left _ hx))
      have codeB := (prior.chain hc hd).2.trans code
      have one := Mapped.ofBody L step.body step.kept.rules step.kept codeB
        AdrSet.not_mem_empty (outside b mem) (others b mem) (entries b mem)
      rw [← block_entries L step.body step.kept] at one
      obtain ⟨fs, corr, out⟩ := one
      have count := body_systemCount L step.body step.kept.rules step.kept codeB AdrSet.not_mem_empty
        (outside b mem) (others b mem)
      exact ⟨fss ++ [fs], List.rel_append below (.cons ⟨corr, out, count⟩ .nil)⟩

theorem corresponds_flatten :
    ∀ {fss : List (List (Delivery.Frame c))} {bs : List KeptBlock}, List.Forall₂ (BlockFrames c ty) fss bs →
      Corresponds c fss.flatten (History.kept c.address bs)
  | _, _, .nil => .nil
  | _, _, .cons hb rest => by
    show Corresponds c (_ ++ _) (List.flatMap _ (_ :: _))
    rw [List.flatMap_cons]
    exact List.rel_append hb.1 (corresponds_flatten rest)

/-- The premises the history results share, for a contract whose start storage represents `st`: the history, the
code, the system address free of code, senders, authorities and creations, and the word range over the submissions. -/
structure Premises (c : Contract) (cfg : ChainConfig) (start : BlockChain) (blocks : List KeptBlock)
    (stop : BlockChain) (st : QueueState c.Record) : Prop where
  history : KeptHistory cfg start blocks stop
  code : start.state.getCode c.address = c.code
  rep : Holds c (start.state.getStor c.address) st
  empty : start.state.getCode systemAddress = ByteArray.empty
  senders : History.NoSender systemAddress blocks
  authorities : History.NoAuthority systemAddress blocks
  creates : History.NoCreate systemAddress blocks
  slots : queueBase c.width (st.tail + (History.submitted c blocks).length) ≤ 2 ^ 256
  count : st.count + (History.submitted c blocks).length < 2 ^ 256

/-- The premises give per-block frames forming one chain over the history. -/
theorem Premises.frames (L : Linked c ty) (P : Premises c cfg start blocks stop st) :
    ∃ fss : List (List (Delivery.Frame c)), List.Forall₂ (BlockFrames c ty) fss blocks ∧
      Chain (start.state.getStor c.address) fss.flatten (stop.state.getStor c.address) ∧
      Delivery.submissions fss.flatten = History.submitted c blocks := by
  have hc : (start.state.getCode c.address).toList ≠ [] := by rw [P.code]; exact L.runnable.1
  have hd : ¬ isValidDelegation (start.state.getCode c.address) := by rw [P.code]; exact L.runnable.2
  obtain ⟨outside, others, -⟩ := P.history.caller_ne (a := c.address) P.empty L.placed.beacon L.placed.history
    P.senders P.authorities P.creates
  obtain ⟨fss, hf⟩ := blockFrames L P.history P.code outside others
    (P.history.entry_in P.code L.runnable.1 L.runnable.2)
  have corr := corresponds_flatten hf
  exact ⟨fss, hf, corr.chain (P.history.chain hc hd).1, corr.submissions⟩

/-- A block's request bytes are its emitted records' bytes; with `blockEmissions`'s cut, they are the records. -/
theorem blockEmissions_of_output (R : Reading c) {b : KeptBlock} {rs : List c.Record}
    (h : blockDelivered ty b = rs.flatMap c.out) : blockEmissions R ty b = rs.map c.out := by
  unfold blockEmissions
  rw [h]
  exact Blanc.List.chunksOf_flatMap R.size_pos c.out rs fun r _ => R.out_length r

/-- **Emissions along consecutive blocks.** Over the blocks of a segment of the chain, the emitted records are the
records delivered from the end of the frames before them up to the end of their own. -/
theorem emissions_segments (R : Reading c) :
    ∀ {fss : List (List (Delivery.Frame c))} {bs : List KeptBlock}, List.Forall₂ (BlockFrames c ty) fss bs →
      ∀ {xs ys : List (Delivery.Frame c)}, Chain s (xs ++ (fss.flatten ++ ys)) t → Holds c s st →
      queueBase c.width (st.tail + (Delivery.submissions (xs ++ (fss.flatten ++ ys))).length) ≤ 2 ^ 256 →
      st.count + (Delivery.submissions (xs ++ (fss.flatten ++ ys))).length < 2 ^ 256 →
      emissions R ty bs = (((st.queue ++ Delivery.submissions (xs ++ (fss.flatten ++ ys))).drop
        (deliveredRecords st xs)).take (deliveredRecords st (xs ++ fss.flatten) - deliveredRecords st xs)).map c.out
  | _, _, .nil, xs, ys, _, _, _, _ => by
    simp only [emissions, List.flatMap_nil, List.flatten_nil, List.append_nil, Nat.sub_self, List.take_zero,
      List.map_nil]
  | _, _, @List.Forall₂.cons _ _ _ fs b fss bs hb rest, xs, ys, chain, rep, slots, count => by
    have assoc : xs ++ ((fs :: fss).flatten ++ ys) = xs ++ (fs ++ (fss.flatten ++ ys)) := by
      rw [List.flatten_cons, List.append_assoc]
    have assoc' : xs ++ ((fs :: fss).flatten ++ ys) = (xs ++ fs) ++ (fss.flatten ++ ys) := by
      rw [List.flatten_cons, List.append_assoc, List.append_assoc]
    rw [assoc] at chain slots count ⊢
    have one := segment_output chain rep slots count
    rw [hb.2.1] at one
    have block := blockEmissions_of_output R one
    have chain' : Chain s ((xs ++ fs) ++ (fss.flatten ++ ys)) t := by
      rwa [List.append_assoc]
    have e : (xs ++ fs) ++ (fss.flatten ++ ys) = xs ++ (fs ++ (fss.flatten ++ ys)) := List.append_assoc _ _ _
    have tail := emissions_segments R rest chain' rep (by rwa [e]) (by rwa [e])
    rw [e] at tail
    have k12 := deliveredRecords_prefix st xs fs
    have k23 := deliveredRecords_prefix st (xs ++ fs) fss.flatten
    have e3 : xs ++ (fs :: fss).flatten = (xs ++ fs) ++ fss.flatten := by
      rw [List.flatten_cons, List.append_assoc]
    rw [e3]
    show blockEmissions R ty b ++ emissions R ty bs = _
    rw [block, tail, ← List.map_append]
    congr 1
    generalize st.queue ++ Delivery.submissions (xs ++ (fs ++ (fss.flatten ++ ys))) = S at *
    generalize deliveredRecords st xs = k1 at *
    generalize deliveredRecords st (xs ++ fs) = k2 at *
    generalize deliveredRecords st (xs ++ fs ++ fss.flatten) = k3 at *
    obtain ⟨d, rfl⟩ : ∃ d, k2 = k1 + d := ⟨k2 - k1, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ d', k3 = k1 + d + d' := ⟨k3 - (k1 + d), by omega⟩
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, Nat.add_assoc, Nat.add_sub_cancel_left, List.take_add,
      List.drop_drop]

/-! ## The FIFO -/

/-- **The history FIFO.** Every committed paid submission, after the start queue, is in order either a record the
blocks emitted or a record still in the final queue. -/
theorem history_fifo (R : Reading c) (L : Linked c ty) (P : Premises c cfg start blocks stop st) :
    st.queue.map c.out ++ submissions c blocks = emissions R ty blocks ++ remainingQueue R stop := by
  obtain ⟨fss, hf, chain, subs⟩ := P.frames L
  have slots : queueBase c.width (st.tail + (Delivery.submissions fss.flatten).length) ≤ 2 ^ 256 := by
    rw [subs]; exact P.slots
  have count : st.count + (Delivery.submissions fss.flatten).length < 2 ^ 256 := by
    rw [subs]; exact P.count
  have em := emissions_segments R hf (xs := []) (ys := []) (by simpa only [List.nil_append, List.append_nil] using chain)
    P.rep (by simpa only [List.nil_append, List.append_nil] using slots)
    (by simpa only [List.nil_append, List.append_nil] using count)
  have z : deliveredRecords st ([] : List (Delivery.Frame c)) = 0 := rfl
  simp only [List.nil_append, List.append_nil] at em
  rw [z, Nat.sub_zero, List.drop_zero] at em
  have d := chain.delivered P.rep slots count
  unfold remainingQueue
  rw [storedQueue_eq R d.represents, d.queue, em, ← List.map_append, List.take_append_drop, submissions, ← subs,
    List.map_append]

/-! ## One block -/

/-- **One block's emission and request boundary.** At a covered fork a block emits nothing and has no request
boundary. At Amsterdam it emits the first `cap` records of the queue its request step read, and the submissions
through its request boundary, after the start queue, are the earlier blocks' emissions followed by that queue.
Either way its request bytes are its emitted records, each `R.size` bytes. -/
theorem history_block_with_prefix (R : Reading c) (L : Linked c ty) (P : Premises c cfg start blocks stop st)
    {pre post : List KeptBlock} {b : KeptBlock} (split : blocks = pre ++ b :: post) :
    (((blockEmissions R ty b).flatten = blockDelivered ty b ∧ ∀ e ∈ blockEmissions R ty b, e.length = R.size) ∧
    (b.fork ≠ .amsterdam → blockEmissions R ty b = [] ∧ queueAtRequests R b = []) ∧
    (b.fork = .amsterdam →
      blockEmissions R ty b = (queueAtRequests R b).take c.cap ∧
      st.queue.map c.out ++ submissions c pre ++ boundarySubmissions c b =
        emissions R ty pre ++ queueAtRequests R b)) ∧
    (b.fork = .amsterdam →
      ∃ (xs ys : List (Delivery.Frame c)) (g : Delivery.Frame c) (f : Exec.Frame),
        Corresponds c (xs ++ g :: ys) (History.kept c.address blocks) ∧
        Chain (start.state.getStor c.address) (xs ++ g :: ys) (stop.state.getStor c.address) ∧
        Chain (start.state.getStor c.address) xs g.before ∧
        requestFrame c.address b = some f ∧ Matches c g f ∧
        g.event = .system false ∧ queueAtRequests R b = (queueAfter st xs).queue.map c.out) := by
  obtain ⟨fss, hf, chain, subs⟩ := P.frames L
  have allcorr := corresponds_flatten hf
  rw [split] at hf
  obtain ⟨fpre, fs, fpost, rfl, hpre, hb, -⟩ := Blanc.List.forall₂_split hf
  have eF : (fpre ++ fs :: fpost).flatten = fpre.flatten ++ (fs ++ fpost.flatten) := by
    rw [List.flatten_append, List.flatten_cons]
  rw [eF] at chain subs allcorr
  have slots : queueBase c.width (st.tail + (Delivery.submissions (fpre.flatten ++ (fs ++ fpost.flatten))).length)
      ≤ 2 ^ 256 := by rw [subs]; exact P.slots
  have count : st.count + (Delivery.submissions (fpre.flatten ++ (fs ++ fpost.flatten))).length < 2 ^ 256 := by
    rw [subs]; exact P.count
  have feed : ∀ {rs : List c.Record}, blockDelivered ty b = rs.flatMap c.out →
      (blockEmissions R ty b).flatten = blockDelivered ty b ∧ ∀ e ∈ blockEmissions R ty b, e.length = R.size := by
    intro rs h
    rw [blockEmissions_of_output R h, h, List.flatMap_def]
    refine ⟨rfl, ?_⟩
    intro e he
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp he
    exact R.out_length r
  have hcount := hb.2.2
  by_cases am : b.fork = .amsterdam
  · rw [ite_eq_left am] at hcount
    obtain ⟨kpre, f, kpost, hk, fsys, others, found, taken⟩ :=
      Blanc.List.split_of_filter_length_one isSystemFrame hcount
    have corr := hb.1
    rw [hk] at corr
    obtain ⟨gs, g, hs, rfl, cg, mg, ch⟩ := corr.split
    have fcaller : f.sevm.caller = systemAddress := by simpa only [isSystemFrame, decide_eq_true_eq] using fsys
    have gev : g.event = .system false := mg.system fcaller
    have nsg : NoSystem (events gs) := cg.noSystem fun x hx => by
      simpa only [isSystemFrame, decide_eq_false_iff_not] using others x (List.mem_append_left _ hx)
    have nsh : NoSystem (events hs) := ch.noSystem fun x hx => by
      simpa only [isSystemFrame, decide_eq_false_iff_not] using others x (List.mem_append_right _ hx)
    set X := fpre.flatten
    set Y := fpost.flatten
    have e : X ++ ((gs ++ g :: hs) ++ Y) = (X ++ gs) ++ g :: (hs ++ Y) := by
      simp only [List.append_assoc, List.cons_append]
    rw [e] at chain slots count allcorr
    have hl : (Delivery.submissions (X ++ gs)).length ≤
        (Delivery.submissions ((X ++ gs) ++ g :: (hs ++ Y))).length := by
      rw [Delivery.submissions_append (X ++ gs), List.length_append]
      omega
    have slotsP : queueBase c.width (st.tail + (Delivery.submissions (X ++ gs)).length) ≤ 2 ^ 256 :=
      (queueBase_mono _ (by omega)).trans slots
    have countP : st.count + (Delivery.submissions (X ++ gs)).length < 2 ^ 256 := by omega
    have out := chain.call_delivers P.rep slotsP countP gev
    have kX : deliveredRecords st (X ++ gs) = deliveredRecords st X := deliveredRecords_noSystem st X nsg
    rw [kX] at out
    have sysOut : systemOutput (gs ++ g :: hs) = g.output := by
      have h1 := systemOutput_noSystem nsg
      have h2 := systemOutput_noSystem nsh
      unfold systemOutput at h1 h2 ⊢
      rw [List.flatMap_append, List.flatMap_cons, h1, h2, List.nil_append, List.append_nil]
    have delivered : blockDelivered ty b = (((st.queue ++ Delivery.submissions (X ++ gs)).drop
        (deliveredRecords st X)).take c.cap).flatMap c.out := by
      rw [← hb.2.1, sysOut, out]
    obtain ⟨m, h1, h2⟩ := chain.append_split
    have starts : g.before = m := by
      cases h2 with
      | cons starts _ => exact starts
    have d := h1.delivered P.rep slotsP countP
    have actual_queue : queueAtRequests R b = (queueAfter st (X ++ gs)).queue.map c.out := by
      unfold queueAtRequests requestFrame
      rw [found]
      dsimp only
      rw [← mg.before, starts, storedQueue_eq R d.represents]
    have queue : queueAtRequests R b = ((st.queue ++ Delivery.submissions (X ++ gs)).drop
        (deliveredRecords st X)).map c.out := by
      rw [actual_queue, d.queue, kX]
    have original : ((blockEmissions R ty b).flatten = blockDelivered ty b ∧ ∀ e ∈ blockEmissions R ty b, e.length = R.size) ∧
    (b.fork ≠ .amsterdam → blockEmissions R ty b = [] ∧ queueAtRequests R b = []) ∧
    (b.fork = .amsterdam →
      blockEmissions R ty b = (queueAtRequests R b).take c.cap ∧
      st.queue.map c.out ++ submissions c pre ++ boundarySubmissions c b =
        emissions R ty pre ++ queueAtRequests R b) := by
      refine ⟨feed delivered, fun ne => absurd am ne, fun _ => ⟨?_, ?_⟩⟩
      · rw [blockEmissions_of_output R delivered, queue, List.map_take]
      · have hsubPre : submissions c pre = (Delivery.submissions X).map c.out := by
          unfold submissions
          rw [(corresponds_flatten hpre).submissions]
          rfl
        have hbound : boundarySubmissions c b = (Delivery.submissions gs).map c.out := by
          unfold boundarySubmissions
          rw [taken, ← cg.submissions]
        have em := emissions_segments R hpre (xs := []) (ys := (gs ++ g :: hs) ++ Y)
          (by simpa only [List.nil_append, List.append_assoc, List.cons_append] using chain)
          P.rep (by simpa only [List.nil_append, List.append_assoc, List.cons_append] using slots)
          (by simpa only [List.nil_append, List.append_assoc, List.cons_append] using count)
        have z : deliveredRecords st ([] : List (Delivery.Frame c)) = 0 := rfl
        rw [List.nil_append, List.nil_append, z, Nat.sub_zero, List.drop_zero] at em
        have hk : deliveredRecords st X ≤ (st.queue ++ Delivery.submissions X).length := deliveredRecords_le st X
        have tS : (st.queue ++ Delivery.submissions (X ++ ((gs ++ g :: hs) ++ Y))).take (deliveredRecords st X) =
            (st.queue ++ Delivery.submissions X).take (deliveredRecords st X) := by
          rw [Delivery.submissions_append, ← List.append_assoc, List.take_append_of_le_length hk]
        have tT : (st.queue ++ Delivery.submissions (X ++ gs)).take (deliveredRecords st X) =
            (st.queue ++ Delivery.submissions X).take (deliveredRecords st X) := by
          rw [Delivery.submissions_append, ← List.append_assoc, List.take_append_of_le_length hk]
        rw [hsubPre, hbound, em, tS, queue, ← tT]
        conv => rhs; rw [← List.map_append, List.take_append_drop]
        rw [Delivery.submissions_append, List.map_append, List.map_append, List.append_assoc]
    refine ⟨original, fun _ => ⟨X ++ gs, hs ++ Y, g, f, allcorr, chain, ?_, found, mg, gev, actual_queue⟩⟩
    rw [starts]
    exact h1
  · rw [ite_eq_right am] at hcount
    have users : ∀ x ∈ b.keptAt c.address, x.sevm.caller ≠ systemAddress := fun x hx => by
      simpa only [isSystemFrame, decide_eq_false_iff_not] using Blanc.List.filter_length_zero isSystemFrame hcount x hx
    have none : blockDelivered ty b = ([] : List c.Record).flatMap c.out := by
      rw [← hb.2.1, systemOutput_noSystem (hb.1.noSystem users)]
      rfl
    have original : ((blockEmissions R ty b).flatten = blockDelivered ty b ∧ ∀ e ∈ blockEmissions R ty b, e.length = R.size) ∧
    (b.fork ≠ .amsterdam → blockEmissions R ty b = [] ∧ queueAtRequests R b = []) ∧
    (b.fork = .amsterdam →
      blockEmissions R ty b = (queueAtRequests R b).take c.cap ∧
      st.queue.map c.out ++ submissions c pre ++ boundarySubmissions c b =
        emissions R ty pre ++ queueAtRequests R b) := by
      refine ⟨feed none, fun _ => ⟨?_, ?_⟩, fun h => absurd h am⟩
      · rw [blockEmissions_of_output R none]
        rfl
      · unfold queueAtRequests requestFrame
        rw [List.find?_eq_none.mpr fun x hx => by
          simpa only [isSystemFrame, decide_eq_true_eq] using users x hx]
    exact ⟨original, fun same => False.elim (am same)⟩


/-- The original block statement, projected from the same boundary derivation. -/
theorem history_block (R : Reading c) (L : Linked c ty) (P : Premises c cfg start blocks stop st)
    {pre post : List KeptBlock} {b : KeptBlock} (split : blocks = pre ++ b :: post) :
    ((blockEmissions R ty b).flatten = blockDelivered ty b ∧ ∀ e ∈ blockEmissions R ty b, e.length = R.size) ∧
    (b.fork ≠ .amsterdam → blockEmissions R ty b = [] ∧ queueAtRequests R b = []) ∧
    (b.fork = .amsterdam →
      blockEmissions R ty b = (queueAtRequests R b).take c.cap ∧
      st.queue.map c.out ++ submissions c pre ++ boundarySubmissions c b =
        emissions R ty pre ++ queueAtRequests R b) :=
  (history_block_with_prefix R L P split).1

/-! ## Occurrences -/

theorem emissions_take_succ (R : Reading c) {j : Nat} {x : KeptBlock} (h : blocks[j]? = some x) :
    emissions R ty (blocks.take (j + 1)) = emissions R ty (blocks.take j) ++ blockEmissions R ty x := by
  rw [List.take_add_one, h, Option.toList_some, emissions_append]
  simp only [emissions, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem emissions_take_mono (R : Reading c) {i i' : Nat} (h : i ≤ i') :
    (emissions R ty (blocks.take i)).length ≤ (emissions R ty (blocks.take i')).length := by
  have e : blocks.take i' = blocks.take i ++ (blocks.take i').drop i := by
    conv_lhs => rw [← List.take_append_drop i (blocks.take i')]
    rw [List.take_take, Nat.min_eq_left h]
  rw [e, emissions_append, List.length_append]
  omega

/-- **The fate of every submission (occurrence-indexed).** Every committed paid submission `n`, after the start
queue, is either emitted, as record `k` of block `j` for exactly one pair `(j, k)`, with `j` before an anchor `a`
exactly when `n` is below the emissions of the first `a` blocks; or still queued at the end, at position `n − E`. -/
theorem history_fate (R : Reading c) (L : Linked c ty) (P : Premises c cfg start blocks stop st) (n : Nat) :
    (n < (emissions R ty blocks).length ∧
      ∃ j k, ∃ hj : j < blocks.length, k < (blockEmissions R ty blocks[j]).length ∧
        (emissions R ty (blocks.take j)).length + k = n ∧
        (blockEmissions R ty blocks[j])[k]? = (st.queue.map c.out ++ submissions c blocks)[n]? ∧
        (∀ a, j < a ↔ n < (emissions R ty (blocks.take a)).length) ∧
        ∀ j' k' (hj' : j' < blocks.length), k' < (blockEmissions R ty blocks[j']).length →
          (emissions R ty (blocks.take j')).length + k' = n → j' = j ∧ k' = k) ∨
    ((emissions R ty blocks).length ≤ n ∧
      (remainingQueue R stop)[n - (emissions R ty blocks).length]? =
        (st.queue.map c.out ++ submissions c blocks)[n]?) := by
  have fifo := history_fifo R L P
  by_cases hE : n < (emissions R ty blocks).length
  · left
    refine ⟨hE, ?_⟩
    obtain ⟨j, k, hj, hk, pos⟩ := Blanc.List.exists_flatMap_position (blockEmissions R ty) blocks hE
    have get := Blanc.List.getElem?_flatMap_position (blockEmissions R ty) blocks hj hk
    refine ⟨j, k, hj, hk, pos, ?_, ?_, ?_⟩
    · rw [fifo, List.getElem?_append_left hE, ← get]
      unfold emissions
      rw [pos]
    · intro a
      have hx : blocks[j]? = some blocks[j] := List.getElem?_eq_getElem hj
      have succ := congrArg List.length (emissions_take_succ (ty := ty) R hx)
      rw [List.length_append] at succ
      have e : (emissions R ty (blocks.take j)).length = ((blocks.take j).flatMap (blockEmissions R ty)).length :=
        rfl
      constructor
      · intro ha
        have := emissions_take_mono (blocks := blocks) (ty := ty) R (show j + 1 ≤ a by omega)
        omega
      · intro hlt
        by_contra hge
        have := emissions_take_mono (blocks := blocks) (ty := ty) R (Nat.le_of_not_lt hge)
        omega
    · intro j' k' hj' hk' pos'
      exact (Blanc.List.flatMap_position_inj (blockEmissions R ty) blocks hj' hj hk' hk (pos'.trans pos.symm))
  · right
    refine ⟨Nat.le_of_not_lt hE, ?_⟩
    rw [fifo, List.getElem?_append_right (Nat.le_of_not_lt hE)]

/-- **Latency, occurrence-indexed.** Let record `r` sit at index `q` of the queue block `j`'s request step read,
and let blocks `j` to `j + q / cap` all be Amsterdam blocks of the history. Then block `j + q / cap` emits `r` as its
record `q % cap`, preceded by exactly the queue's records from position `cap * (q / cap)`; `r` is the history's
submission occurrence `E_j + q`, after the start queue, where `E_j` counts the records emitted before block `j`; and that
occurrence is record `q % cap` of block `j + q / cap` in `history_fate`'s indexing. -/
theorem history_latency (R : Reading c) (L : Linked c ty) (P : Premises c cfg start blocks stop st)
    (hcap : 0 < c.cap) {j q : Nat} {B D : KeptBlock} {r : Bytes}
    (hB : blocks[j]? = some B) (hD : blocks[j + q / c.cap]? = some D)
    (amsterdam : ∀ i ≤ q / c.cap, ∀ x, blocks[j + i]? = some x → x.fork = .amsterdam)
    (queued : (queueAtRequests R B)[q]? = some r) :
    (blockEmissions R ty D)[q % c.cap]? = some r ∧
    (∀ i ≤ q % c.cap, (blockEmissions R ty D)[i]? = (queueAtRequests R B)[c.cap * (q / c.cap) + i]?) ∧
    (st.queue.map c.out ++ submissions c blocks)[(emissions R ty (blocks.take j)).length + q]? = some r ∧
    (emissions R ty (blocks.take j)).length + q =
      (emissions R ty (blocks.take (j + q / c.cap))).length + q % c.cap := by
  let T : Nat → KeptBlock → List Bytes := fun i x =>
    st.queue.map c.out ++ submissions c (blocks.take i) ++ boundarySubmissions c x
  let E : Nat → Nat := fun i => (emissions R ty (blocks.take i)).length
  have A : ∀ i x, blocks[i]? = some x → x.fork = .amsterdam →
      blockEmissions R ty x = (queueAtRequests R x).take c.cap ∧
      T i x = emissions R ty (blocks.take i) ++ queueAtRequests R x := by
    intro i x hx am
    exact (history_block R L P (Blanc.List.eq_take_cons_drop hx)).2.2 am
  have A1 : ∀ i x, blocks[i]? = some x → x.fork = .amsterdam → ∀ k, (T i x)[E i + k]? = (queueAtRequests R x)[k]? := by
    intro i x hx am k
    rw [(A i x hx am).2, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have A2 : ∀ i x, blocks[i]? = some x → x.fork = .amsterdam → blockEmissions R ty x = (queueAtRequests R x).take c.cap :=
    fun i x hx am => (A i x hx am).1
  have bpre : ∀ x, boundarySubmissions c x <+: submissions c [x] := by
    intro x
    unfold boundarySubmissions submissions History.submitted History.kept
    rw [List.flatMap_singleton]
    exact ((List.takeWhile_prefix _).filterMap _).map _
  have subsSucc : ∀ i x, blocks[i]? = some x →
      submissions c (blocks.take (i + 1)) = submissions c (blocks.take i) ++ submissions c [x] := by
    intro i x hx
    rw [List.take_add_one, hx, Option.toList_some, submissions_append]
  have B2 : ∀ i x y, blocks[i]? = some x → blocks[i + 1]? = some y → T i x <+: T (i + 1) y := by
    intro i x y hx _
    obtain ⟨u, hu⟩ := bpre x
    refine ⟨u ++ boundarySubmissions c y, ?_⟩
    show (st.queue.map c.out ++ submissions c (blocks.take i) ++ boundarySubmissions c x) ++
      (u ++ boundarySubmissions c y) = st.queue.map c.out ++ submissions c (blocks.take (i + 1)) ++
        boundarySubmissions c y
    rw [subsSucc i x hx, ← hu]
    simp only [List.append_assoc]
  have B3 : ∀ i x, blocks[i]? = some x → E (i + 1) = E i + (blockEmissions R ty x).length := by
    intro i x hx
    show (emissions R ty (blocks.take (i + 1))).length = _
    rw [emissions_take_succ R hx, List.length_append]
  have B1 : T j B <+: st.queue.map c.out ++ submissions c blocks := by
    obtain ⟨u, hu⟩ := bpre B
    refine ⟨u ++ submissions c (blocks.drop (j + 1)), ?_⟩
    show (st.queue.map c.out ++ submissions c (blocks.take j) ++ boundarySubmissions c B) ++
      (u ++ submissions c (blocks.drop (j + 1))) = st.queue.map c.out ++ submissions c blocks
    conv_rhs => rw [← List.take_append_drop (j + 1) blocks, submissions_append, subsSucc j B hB, ← hu]
    simp only [List.append_assoc]
  have hlen : j + q / c.cap < blocks.length := (List.getElem?_eq_some_iff.mp hD).1
  have amB : B.fork = .amsterdam := amsterdam 0 (Nat.zero_le _) B (by rw [Nat.add_zero]; exact hB)
  have core := Blanc.List.drain_position c.cap hcap blocks (fun x => x.fork = .amsterdam) (blockEmissions R ty)
    (queueAtRequests R) T E A1 A2 B2 B3
  have hT : (T j B)[E j + q]? = some r := by rw [A1 j B hB amB]; exact queued
  obtain ⟨y, hy, hbe, hidx⟩ := core (q / c.cap) j q B r rfl hB hlen amsterdam hT
  rw [hD] at hy
  cases hy
  refine ⟨hbe, ?_, ?_, hidx⟩
  · intro i hi
    have hmod : i < c.cap := Nat.lt_of_le_of_lt hi (Nat.mod_lt _ hcap)
    have hdiv : (c.cap * (q / c.cap) + i) / c.cap = q / c.cap := by
      rw [Nat.mul_add_div hcap, Nat.div_eq_of_lt hmod, Nat.add_zero]
    have hm : (c.cap * (q / c.cap) + i) % c.cap = i := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hmod]
    have qlt : q < (queueAtRequests R B).length := (List.getElem?_eq_some_iff.mp queued).1
    have split := Nat.div_add_mod q c.cap
    have hlt : c.cap * (q / c.cap) + i < (queueAtRequests R B).length := by omega
    have hq' := List.getElem?_eq_getElem hlt
    have hT' : (T j B)[E j + (c.cap * (q / c.cap) + i)]? = some (queueAtRequests R B)[c.cap * (q / c.cap) + i] := by
      rw [A1 j B hB amB]; exact hq'
    obtain ⟨y', hy', hbe', -⟩ := core (q / c.cap) j _ B _ hdiv hB hlen amsterdam hT'
    rw [hD] at hy'
    cases hy'
    rw [hm] at hbe'
    rw [hbe', hq']
  · obtain ⟨u, hu⟩ := B1
    rw [← hu, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hT).1]
    exact hT

end History

end Blanc.Lift.BuilderRequest.Occurrence
