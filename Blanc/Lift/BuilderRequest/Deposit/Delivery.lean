import Blanc.Lift.BuilderRequest.Delivery
import Blanc.Lift.BuilderRequest.Deposit.Backlog

/-!
# Exact delivery at the deposit contract, over a given sequence of frames

The frames are an input: a list of submissions and fee reads under covered forks or Amsterdam, and system calls
under Amsterdam, each with what its frame law gives, each running on the storage the last one left, from the
storage the factory deploys. "Committed" here means "in the given sequence". That a chain's retained frames form
such a list is not claimed: that needs message and transaction level.

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`; the bytes and `sys-asm`
`83f9801`, not the EIP text.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open RequestSystem
open Delivery
open Creation (address)

/-- The record a submission's calldata holds. -/
def recordOf (sevm : Sevm) (_h : sevm.data.length = 184) : Record where
  pubkey := sevm.data.sliceD 0 48 0
  credentials := sevm.data.sliceD 48 32 0
  amount := sevm.data.sliceD 80 8 0
  signature := sevm.data.sliceD 88 96 0
  pubkey_length := List.length_sliceD ..
  credentials_length := List.length_sliceD ..
  amount_length := List.length_sliceD ..
  signature_length := List.length_sliceD ..

/-- **The record is exactly the calldata.** -/
theorem recordOf_data (sevm : Sevm) (h : sevm.data.length = 184) : (recordOf sevm h).data = sevm.data := by
  have whole := sliceD_self sevm.data h
  rw [show (184 : Nat) = 48 + (32 + (8 + 96)) by rfl, List.sliceD_split, List.sliceD_split, List.sliceD_split] at whole
  conv_rhs => rw [← whole]
  simp only [Record.data, recordOf, List.append_assoc]

/-- The record's stored word `j` is the calldata's word at byte `32 * j`. -/
theorem recordOf_word (sevm : Sevm) (h : sevm.data.length = 184) (j : Nat) :
    (recordOf sevm h).word j = Bytes.toB256 (sevm.data.sliceD (32 * j) 32 0) := by
  rw [Record.word, recordOf_data]

/-- **The amount field is what the guards credit.** The word `amountGwei` reads, masked to its low 64 bits, holds
exactly the record's amount field: calldata bytes 80 to 87, big-endian. -/
theorem amountGwei_toBytes (sevm : Sevm) (h : sevm.data.length = 184) :
    (amountGwei sevm).toBytes = List.replicate 24 0 ++ (recordOf sevm h).amount := by
  have hw : ∀ w : B256, (amountMask &&& w).toBytes = List.replicate 24 0 ++ w.toBytes.sliceD 24 8 0 := by
    intro w
    rcases w with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    have hm : amountMask = ((0, 0), (0, 18446744073709551615)) := rfl
    rw [hm]
    change B256.toBytes ⟨⟨(0 : UInt64) &&& a, (0 : UInt64) &&& b⟩, ⟨(0 : UInt64) &&& c, _ &&& d⟩⟩ = _
    rw [UInt64.zero_and, UInt64.zero_and, UInt64.zero_and, max_and]
    have hs : (B256.toBytes ((a, b), c, d)).sliceD 24 8 0 = UInt64.toBytes d := by
      have := Bytes.sliceD_append_middle (B128.toBytes (a, b) ++ UInt64.toBytes c) (UInt64.toBytes d) []
      rwa [List.append_nil] at this
    rw [hs]
    show B128.toBytes (0, 0) ++ (UInt64.toBytes 0 ++ UInt64.toBytes d) = _
    rw [← List.append_assoc]
    rfl
  rw [amountGwei, hw, Sevm.dataWord, Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)]
  rw [sliceD_sliceD _ (by omega)]
  rfl

/-- A submission's storage effect on a represented queue, with its slots and count in word range. -/
theorem represents_submit (sevm : Sevm) (h : sevm.data.length = 184) {s : Stor} {st : QueueState Record}
    (rep : Represents 6 Record.word (fun key => s.get key) st)
    (slots : queueBase 6 st.tail + 6 ≤ 2 ^ 256) (count : st.count + 1 < 2 ^ 256) :
    Represents 6 Record.word (fun key => (submittedStorage sevm s).get key) (submit st (recordOf sevm h)) := by
  have ht : s.get 3 = st.tail.toB256 := rep.tail
  have key : submissionKey (s.get 3) = queueSlot 6 st.tail 0 := by
    rw [ht]
    exact submissionKey_queueSlot _
  have step : ∀ j, (1 : B256) + queueSlot 6 st.tail j = queueSlot 6 st.tail (j + 1) := fun j => by
    rw [show (1 : B256) = Nat.toB256 1 by decide]
    exact record_key_add 6 st.tail j 1
  have val : ∀ j, j < 6 → (queueSlot 6 st.tail j).toNat = 4 + 6 * st.tail + j := fun j hj => by
    unfold queueSlot queueBase at *
    rw [B256.toNat_toB256_of_lt (by omega)]
  have ne : ∀ i j, i < 6 → j < 6 → i ≠ j → queueSlot 6 st.tail i ≠ queueSlot 6 st.tail j := fun i j hi hj hij e => by
    have := congrArg B256.toNat e
    rw [val i hi, val j hj] at this
    omega
  have hmeta : ∀ n, n < 4 → ∀ j, j < 6 → queueSlot 6 st.tail j ≠ n.toB256 := fun n hn j hj e => by
    have := congrArg B256.toNat e
    rw [val j hj, B256.toNat_toB256_of_lt (by omega)] at this
    omega
  have m0 : ∀ j, j < 6 → queueSlot 6 st.tail j ≠ 0 := hmeta 0 (by omega)
  have m1 : ∀ j, j < 6 → queueSlot 6 st.tail j ≠ 1 := hmeta 1 (by omega)
  have m2 : ∀ j, j < 6 → queueSlot 6 st.tail j ≠ 2 := hmeta 2 (by omega)
  have m3 : ∀ j, j < 6 → queueSlot 6 st.tail j ≠ 3 := hmeta 3 (by omega)
  have n01 : ∀ {j}, j < 6 → (0 : B256) ≠ queueSlot 6 st.tail j := fun hj => (m0 _ hj).symm
  have d10 : (1 : B256) ≠ 0 := by decide
  have d30 : (3 : B256) ≠ 0 := by decide
  have d31 : (3 : B256) ≠ 1 := by decide
  have d12 : (1 : B256) ≠ 2 := by decide
  have d32 : (3 : B256) ≠ 2 := by decide
  have d13 : (1 : B256) ≠ 3 := by decide
  have hstor : ∀ k, (submittedStorage sevm s).get k =
      if (3 : B256) = k then 1 + s.get 3 else
      if queueSlot 6 st.tail 5 = k then Sevm.dataWord sevm 160 else
      if queueSlot 6 st.tail 4 = k then Sevm.dataWord sevm 128 else
      if queueSlot 6 st.tail 3 = k then Sevm.dataWord sevm 96 else
      if queueSlot 6 st.tail 2 = k then Sevm.dataWord sevm 64 else
      if queueSlot 6 st.tail 1 = k then Sevm.dataWord sevm 32 else
      if queueSlot 6 st.tail 0 = k then Sevm.dataWord sevm 0 else
      if (1 : B256) = k then 1 + s.get 1 else s.get k := fun k => by
    simp only [submittedStorage, key, step, Nat.zero_add, Nat.reduceAdd, Stor.get_set_ite]
  refine represents_after_submit rep (by omega) slots count ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hstor]
    simp only [d30, m0 _ (by omega : 5 < 6), m0 _ (by omega : 4 < 6), m0 _ (by omega : 3 < 6), m0 _ (by omega : 2 < 6),
      m0 _ (by omega : 1 < 6), m0 _ (by omega : 0 < 6), d10, ↓reduceIte]
  · rw [hstor]
    simp only [d31, m1 _ (by omega : 5 < 6), m1 _ (by omega : 4 < 6), m1 _ (by omega : 3 < 6), m1 _ (by omega : 2 < 6),
      m1 _ (by omega : 1 < 6), m1 _ (by omega : 0 < 6), ↓reduceIte]
    show (1 : B256) + s.get 1 = _
    rw [show s.get 1 = st.count.toB256 from rep.count]
    exact one_add_word _
  · rw [hstor]
    simp only [d32, m2 _ (by omega : 5 < 6), m2 _ (by omega : 4 < 6), m2 _ (by omega : 3 < 6), m2 _ (by omega : 2 < 6),
      m2 _ (by omega : 1 < 6), m2 _ (by omega : 0 < 6), d12, ↓reduceIte]
  · rw [hstor]
    simp only [↓reduceIte]
    rw [ht]
    exact one_add_word _
  · intro j hj
    have hk3 : ∀ j, j < 6 → (3 : B256) ≠ queueSlot 6 st.tail j := fun j hj => (m3 j hj).symm
    rw [hstor, ite_eq_right (hk3 j hj), recordOf_word]
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [ne 5 0 (by omega) (by omega) (by omega), ne 4 0 (by omega) (by omega) (by omega),
        ne 3 0 (by omega) (by omega) (by omega), ne 2 0 (by omega) (by omega) (by omega),
        ne 1 0 (by omega) (by omega) (by omega), ↓reduceIte]
      rfl
    · simp only [ne 5 1 (by omega) (by omega) (by omega), ne 4 1 (by omega) (by omega) (by omega),
        ne 3 1 (by omega) (by omega) (by omega), ne 2 1 (by omega) (by omega) (by omega), ↓reduceIte]
      rfl
    · simp only [ne 5 2 (by omega) (by omega) (by omega), ne 4 2 (by omega) (by omega) (by omega),
        ne 3 2 (by omega) (by omega) (by omega), ↓reduceIte]
      rfl
    · simp only [ne 5 3 (by omega) (by omega) (by omega), ne 4 3 (by omega) (by omega) (by omega), ↓reduceIte]
      rfl
    · simp only [ne 5 4 (by omega) (by omega) (by omega), ↓reduceIte]
      rfl
    · simp only [↓reduceIte]
      rfl
  · intro k h1 h3 hs
    rw [hstor, ite_eq_right h3, ite_eq_right (hs 5 (by omega)), ite_eq_right (hs 4 (by omega)),
      ite_eq_right (hs 3 (by omega)), ite_eq_right (hs 2 (by omega)), ite_eq_right (hs 1 (by omega)),
      ite_eq_right (hs 0 (by omega)), ite_eq_right h1]

/-- The empty-calldata system call's law. -/
theorem system_law {benv : Benv} {post : State} {result : MsgCallOutput} (hf : benv.stat.fork = .amsterdam)
    (hi : benv.state.getCode address = code)
    (run : processCheckedSystemTransaction benv address [] = .ok (post, result)) :
    post = sysState sysShape benv.state address ∧
      ∀ {st : QueueState Record}, Represents 6 Record.word (storOf benv.state address) st →
        result.returnData = (st.queue.take 64).flatMap Record.out := by
  obtain ⟨o, h, _⟩ := system_call_state hf hi
  have e : (post, result) = (sysState sysShape benv.state address, o) := Except.ok.inj (run.symm.trans h)
  obtain ⟨e1, -⟩ := Prod.mk.inj e
  refine ⟨e1, ?_⟩
  intro st rep
  obtain ⟨_, o', h', _, hout, _⟩ := system_call_fifo hf hi rep
  have e' : (post, result) = (_, o') := Except.ok.inj (run.symm.trans h')
  exact (congrArg (fun x => x.2.returnData) e').trans hout

/-- The nonempty-calldata system call's law. -/
theorem latch_law {benv : Benv} {data : Bytes} {post : State} {result : MsgCallOutput}
    (hf : benv.stat.fork = .amsterdam) (hi : benv.state.getCode address = code) (hne : data ≠ [])
    (hlen : data.length < 2 ^ 256)
    (run : processCheckedSystemTransaction benv address data = .ok (post, result)) :
    post = latchState sysShape benv.state address ∧
      ∀ {st : QueueState Record}, Represents 6 Record.word (storOf benv.state address) st →
        result.returnData = (st.queue.take 64).flatMap Record.out := by
  obtain ⟨o, _, h, _⟩ := latch_call hf hi hne hlen
  have e : (post, result) = (latchState sysShape benv.state address, o) := Except.ok.inj (run.symm.trans h)
  obtain ⟨e1, -⟩ := Prod.mk.inj e
  refine ⟨e1, ?_⟩
  intro st rep
  obtain ⟨_, o', h', _, hout, _⟩ := latch_fifo hf hi hne hlen rep
  have e' : (post, result) = (_, o') := Except.ok.inj (run.symm.trans h')
  exact (congrArg (fun x => x.2.returnData) e').trans hout

/-- The deposit contract, as the sequence statements take it. -/
abbrev contract : Contract where
  code := code
  address := address
  target := 8
  cap := 64
  width := 6
  Record := Record
  words := Record.word
  out := Record.out
  Submitted := fun l pre post i o => SubmittedOn l pre post i o
  payload := 184
  recordOf := recordOf
  submitStor := submittedStorage
  shape := sysShape
  length := fun h => h.length
  storage := fun h => h.storage
  active := fun h => h.active
  quote := fun h => h.quote
  paid := fun h => by
    have := h.admitted.covered
    omega
  represents_submit := represents_submit
  cap_word := by decide
  target_eq := rfl
  next_eq := rfl
  target_ne := by decide
  system_law := system_law
  latch_law := latch_law

/-- A frame at the deposit contract. -/
abbrev Frame := Delivery.Frame contract

/-- The queue the deployed storage holds: empty, every counter 0. -/
def deployedQueue : QueueState Record := ⟨0, 0, 0, 0, []⟩

/-- `Creation.factory_deploy`'s storage represents it. -/
theorem deployed_represents : Holds contract Stor.empty deployedQueue where
  coherent := rfl
  excess_lt := by decide
  count_lt := by decide
  head_lt := by decide
  tail_lt := by decide
  live_lt := fun i hi => absurd hi (Nat.not_lt_zero _)
  excess := rfl
  count := rfl
  head := rfl
  tail := rfl
  live := fun i hi => absurd hi (Nat.not_lt_zero _)

/-! ## O17 -/

/-- **Exact delivery at the deposit contract.** Over any given chain of frames from the deployed storage, with the
word range `4 + 6 * n ≤ 2 ^ 256` on the `n` submissions: storage at the end represents `queueAfter`, whose records
are exactly the submissions not yet delivered, in order; and the system calls' concatenated output is exactly the
delivered submissions' records, in order, amounts little-endian (`Record.out`). `deliveredRecords` counts what the
calls took, each `min(length, 64)` of what it found. So nothing is dropped, duplicated or reordered;
`call_delivers` says nothing is early. `recordOf_data`: each record is its submission's calldata;
`amountGwei_toBytes`: its amount field is what the guards credited. The list has no reverted frame and no frame with
caller `systemAddress` other than the request phase's calls (`Frame`): such a frame would drain the queue to its
caller, and the delivery stated here would not be to the block's requests. -/
theorem delivery {frames : List Frame} {t : Stor} (chain : Chain Stor.empty frames t)
    (range : 4 + 6 * (submissions frames).length ≤ 2 ^ 256) :
    Represents 6 Record.word (fun key => t.get key) (queueAfter deployedQueue frames) ∧
      (queueAfter deployedQueue frames).queue =
        (submissions frames).drop (deliveredRecords deployedQueue frames) ∧
      systemOutput frames =
        ((submissions frames).take (deliveredRecords deployedQueue frames)).flatMap Record.out := by
  have h := chain.delivered deployed_represents (by show 4 + _ * (0 + _) ≤ _; rw [Nat.zero_add]; exact range)
    (by show 0 + _ < _; omega)
  exact ⟨h.represents, h.queue, h.output⟩

/-- **Each system call delivers the next records and no others.** On a chain from the deployed storage, a system
call's output is the oldest `min(length, 64)` of the records submitted before it and not yet delivered. -/
theorem call_delivers {xs ys : List Frame} {f : Frame} {latch : Bool} {t : Stor}
    (chain : Chain Stor.empty (xs ++ f :: ys) t) (call : f.event = .system latch)
    (range : 4 + 6 * (submissions xs).length ≤ 2 ^ 256) :
    f.output = (((submissions xs).drop (deliveredRecords deployedQueue xs)).take 64).flatMap Record.out :=
  chain.call_delivers deployed_represents (by show 4 + _ * (0 + _) ≤ _; rw [Nat.zero_add]; exact range)
    (by show 0 + _ < _; omega) call

/-! ## The word range from a budget -/

/-- All the value the frames carry. -/
def paid (frames : List Frame) : Nat := (frames.map Delivery.Frame.value).sum

/-- Each submission carries at least 1 ETH: the frame law's `Admitted`. -/
theorem ether_le_paid (frames : List Frame) : (submissions frames).length * oneEther ≤ paid frames := by
  induction frames with
  | nil => exact Nat.le_refl _
  | cons f rest ih =>
    have hs : (submissions (f :: rest)).length =
        (submitted [f.event]).length + (submissions rest).length := submitted_cons_length _ _
    have hp : paid (f :: rest) = f.value + paid rest := by
      simp only [paid, List.map_cons, List.sum_cons]
    have key : (submitted [f.event]).length * oneEther ≤ f.value := by
      cases f with
      | submission sevm pre post l i o rules target caller law =>
        have h1 := law.admitted.credited
        have h2 := law.admitted.covered
        change (submitted [Event.submission (recordOf sevm law.length)]).length * oneEther ≤ sevm.value.toNat
        rw [show (submitted [Event.submission (recordOf sevm law.length)]).length = 1 from rfl, Nat.one_mul]
        simp only [oneEther]
        omega
      | feeRead sevm pre post l i o rules target caller law =>
        change (submitted [(Event.feeRead : Event Record)]).length * oneEther ≤ _
        rw [show (submitted [(Event.feeRead : Event Record)]).length = 0 from rfl, Nat.zero_mul]
        exact Nat.zero_le _
      | system benv data post out fork installed length run =>
        change (submitted [(Event.system (!data.isEmpty) : Event Record)]).length * oneEther ≤ _
        rw [show (submitted [(Event.system (!data.isEmpty) : Event Record)]).length = 0 from rfl, Nat.zero_mul]
        exact Nat.zero_le _
    rw [hs, hp, Nat.add_mul]
    omega

/-- **The word range follows from any budget of at most `2 ^ 256` wei.** Every submission carries at least 1 ETH,
so no sequence within that budget has enough submissions to reach the word range. No fee is involved. -/
theorem range_of_budget {frames : List Frame} (hb : paid frames ≤ 2 ^ 256) :
    4 + 6 * (submissions frames).length ≤ 2 ^ 256 := by
  have := ether_le_paid frames
  simp only [oneEther] at this
  omega

/-- **Exact delivery within a budget.** `delivery`, with the word range replaced by the sequence paying at most
`2 ^ 256` wei in all, far above all the ether that exists. -/
theorem delivery_of_budget {frames : List Frame} {t : Stor} (chain : Chain Stor.empty frames t)
    (hb : paid frames ≤ 2 ^ 256) :
    Represents 6 Record.word (fun key => t.get key) (queueAfter deployedQueue frames) ∧
      (queueAfter deployedQueue frames).queue =
        (submissions frames).drop (deliveredRecords deployedQueue frames) ∧
      systemOutput frames =
        ((submissions frames).take (deliveredRecords deployedQueue frames)).flatMap Record.out :=
  delivery chain (range_of_budget hb)

/-- The cost a chain of frames with no system call pays, from a represented queue at excess 0. -/
theorem backlog_paid {s t : Stor} {frames : List Frame} (chain : Chain s frames t)
    {st : QueueState Record} (rep : Holds contract s st) (he : st.excess = 0)
    (none : NoSystem (events frames))
    (slots : queueBase 6 (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : st.count + (submissions frames).length < 2 ^ 256) :
    backlogCost (min (st.count + (submissions frames).length) 982) ≤
      backlogCost (min st.count 982) + paid frames := by
  induction chain generalizing st with
  | nil s =>
    show backlogCost (min (st.count + 0) 982) ≤ _ + 0
    exact Nat.le_refl _
  | @cons s f rest t hb tail ih =>
    subst hb
    have tailNone : NoSystem (events rest) := fun x hx => none x (List.mem_cons_of_mem _ hx)
    have hs : (submissions (f :: rest)).length =
        (submitted [f.event]).length + (submissions rest).length := submitted_cons_length _ _
    have hp : paid (f :: rest) = f.value + paid rest := by
      simp only [paid, List.map_cons, List.sum_cons]
    rw [hs] at slots count ⊢
    rw [hp]
    obtain ⟨hrep, -⟩ := f.step_holds rep ((queueBase_mono 6 (by omega)).trans slots) (by omega)
    have htail := step_tail_le contract.cap contract.target st f.event
    have hcount := step_count_le contract.cap contract.target st f.event
    have hsl : queueBase 6 ((step contract.cap contract.target st f.event).tail + (submissions rest).length) ≤ 2 ^ 256 :=
      (queueBase_mono 6 (by omega)).trans slots
    cases f with
    | submission sevm pre post l i o rules target caller law =>
      have hl : (submitted [Delivery.Frame.event
          (.submission sevm pre post l i o rules target caller law : Frame)]).length = 1 := rfl
      rw [hl] at count ⊢
      have ih' := ih hrep he tailNone hsl (by
        show st.count + 1 + _ < _
        omega)
      change backlogCost (min (st.count + 1 + _) 982) ≤
        backlogCost (min (st.count + 1) 982) + _ at ih'
      by_cases hi : st.count ≤ 981
      · have s0 : pre.getStorVal sevm.currentTarget 0 = 0 := by
          rw [target]
          have : (pre.getStor address).get 0 = st.excess.toB256 := rep.excess
          rw [he] at this
          exact this
        have s1 : pre.getStorVal sevm.currentTarget 1 = st.count.toB256 := by
          rw [target]
          exact rep.count
        have pays := submission_pays hi s0 s1 law
        have hv : Delivery.Frame.value (.submission sevm pre post l i o rules target caller law : Frame) =
            sevm.value.toNat := rfl
        rw [hv, Nat.min_eq_left (by omega : st.count ≤ 982)]
        rw [Nat.min_eq_left (by omega : st.count + 1 ≤ 982)] at ih'
        rw [show st.count + (1 + (submissions rest).length) = st.count + 1 + (submissions rest).length by omega]
        have hstep : backlogCost (st.count + 1) = backlogCost st.count + (quotedFee st.count + oneEther) := rfl
        omega
      · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
        omega
    | feeRead sevm pre post l i o rules target caller law =>
      have hl : (submitted [Delivery.Frame.event
          (.feeRead sevm pre post l i o rules target caller law : Frame)]).length = 0 := rfl
      rw [hl, Nat.zero_add] at count ⊢
      have ih' := ih hrep he tailNone hsl count
      change backlogCost (min (st.count + _) 982) ≤ backlogCost (min st.count 982) + _ at ih'
      omega
    | system benv data post out fork installed length run =>
      exact absurd rfl (none _ List.mem_cons_self _)

/-- **A budget bounds the count before the first system call.** On a chain from the deployed storage with no system
call, paying at most a budget of at most `2 ^ 256` wei, below `backlogCost n` for an `n ≤ 982`: there are fewer than
`n` submissions, and that is the count in storage. The budget is a premise. -/
theorem count_lt_of_budget {frames : List Frame} {t : Stor} {budget n : Nat}
    (chain : Chain Stor.empty frames t) (none : NoSystem (events frames)) (hb : paid frames ≤ budget)
    (big : budget ≤ 2 ^ 256) (low : budget < backlogCost n) (hn : n ≤ 982) :
    (queueAfter deployedQueue frames).count = (submissions frames).length ∧ (submissions frames).length < n := by
  have hrange := range_of_budget (hb.trans big)
  refine ⟨(count_noSystem _ _ _ none).trans (Nat.zero_add _), ?_⟩
  by_contra hge
  have h := backlog_paid chain deployed_represents rfl none
    (by show 4 + _ * (0 + _) ≤ _; rw [Nat.zero_add]; exact hrange) (by show 0 + _ < _; omega)
  rw [show deployedQueue.count = 0 from rfl, Nat.zero_add, Nat.zero_min, show backlogCost 0 = 0 from rfl, Nat.zero_add] at h
  have mono : backlogCost n ≤ backlogCost (min (submissions frames).length 982) := by
    rcases Nat.lt_or_eq_of_le (show n ≤ min (submissions frames).length 982 by omega) with hlt | heq
    · exact (backlogCost_strictMono hlt).le
    · rw [heq]
  omega

/-- **The instance.** With 120,000,000 ETH, a chain from the deployed storage with no system call has count at most
981. -/
theorem count_le_981 {frames : List Frame} {t : Stor} (chain : Chain Stor.empty frames t)
    (none : NoSystem (events frames)) (hb : paid frames ≤ instanceBudget) :
    (queueAfter deployedQueue frames).count ≤ 981 := by
  have h982 := backlogEval_981.2
  rw [backlogEval_eq (by omega)] at h982
  obtain ⟨h1, h2⟩ := count_lt_of_budget chain none hb (by decide) h982 (Nat.le_refl _)
  omega

/-! ## A pre-fork backlog followed by Amsterdam calls -/

/-- A submission under a covered fork. -/
def PreFork : Frame → Prop
  | .submission sevm .. => CoveredFork sevm.benvStat.fork
  | _ => False

/-- A checked system call with empty calldata. -/
def EmptyCall (f : Frame) : Prop := f.event = .system false

/-- Two cuts of a list leaving the same suffix leave the same backlog. -/
theorem take_eq_of_drop_eq {α : Type} {xs : List α} {a b : Nat} (h : xs.drop a = xs.drop b) :
    xs.take a = xs.take b := by
  have hl := congrArg List.length h
  rw [List.length_drop, List.length_drop] at hl
  by_cases hab : a = b
  · rw [hab]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- A pre-fork backlog has no system call. -/
theorem noSystem_preFork {backlog : List Frame} (hp : ∀ f ∈ backlog, PreFork f) : NoSystem (events backlog) := by
  intro e he latch heq
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  cases f with
  | submission sevm pre post l i o rules target caller law => cases heq
  | feeRead sevm pre post l i o rules target caller law => exact hp _ hf
  | system benv data post out fork installed length run => exact hp _ hf

/-- **A pre-fork backlog, then Amsterdam calls (the list's item 8).** A backlog of submissions under covered forks,
followed by `k` empty-calldata system calls under Amsterdam, as a given chain from the deployed storage. Its `n`
records are the backlog's calldata, in order. The calls return their first `64 * k` records, little-endian amounts,
and the queue holds the rest. After at least one call, the count is 0 and the excess is `n - 8 * k` in naturals. -/
theorem prefork_then_calls {backlog calls : List Frame} {t : Stor} (chain : Chain Stor.empty (backlog ++ calls) t)
    (hp : ∀ f ∈ backlog, PreFork f) (hc : ∀ f ∈ calls, EmptyCall f)
    (range : 4 + 6 * (submissions backlog).length ≤ 2 ^ 256) :
    Represents 6 Record.word (fun key => t.get key) (queueAfter deployedQueue (backlog ++ calls)) ∧
      (queueAfter deployedQueue (backlog ++ calls)).queue = (submissions backlog).drop (64 * calls.length) ∧
      systemOutput (backlog ++ calls) = ((submissions backlog).take (64 * calls.length)).flatMap Record.out ∧
      (0 < calls.length →
        (queueAfter deployedQueue (backlog ++ calls)).excess = (submissions backlog).length - 8 * calls.length ∧
        (queueAfter deployedQueue (backlog ++ calls)).count = 0) := by
  have hnone := noSystem_preFork hp
  have hev := events_calls hc
  have hsub : submissions (backlog ++ calls) = submissions backlog := by
    rw [submissions_append, show submissions calls = [] by
      simp only [submissions, hev]
      clear hev hc chain
      induction calls.length with
      | zero => rfl
      | succ k ih => exact ih, List.append_nil]
  have hrange : 4 + 6 * (submissions (backlog ++ calls)).length ≤ 2 ^ 256 := by rwa [hsub]
  obtain ⟨hrep, hq, hout⟩ := delivery chain hrange
  have hsplit : queueAfter deployedQueue (backlog ++ calls) =
      replay 64 8 (queueAfter deployedQueue backlog) (List.replicate calls.length (.system false)) := by
    show replay 64 8 deployedQueue (events (backlog ++ calls)) = _
    rw [show events (backlog ++ calls) = events backlog ++ events calls from List.map_append .., replay_append, hev]
    rfl
  have hprefix : (queueAfter deployedQueue backlog).queue = submissions backlog :=
    replay_noSystem_queue _ _ _ hnone
  have hnewq : (queueAfter deployedQueue (backlog ++ calls)).queue = (submissions backlog).drop (64 * calls.length) := by
    rw [hsplit, replay_calls_queue, hprefix]
  refine ⟨hrep, hnewq, ?_, ?_⟩
  · rw [hsub] at hq hout
    rw [hout, take_eq_of_drop_eq (hq.symm.trans hnewq)]
  · intro hk
    obtain ⟨k, hk'⟩ : ∃ k, calls.length = k + 1 := ⟨calls.length - 1, by omega⟩
    have he : (queueAfter deployedQueue backlog).excess = 0 := excess_noSystem _ _ _ hnone
    have hcnt : (queueAfter deployedQueue backlog).count = (submissions backlog).length :=
      (count_noSystem _ _ _ hnone).trans (Nat.zero_add _)
    have hsum : (queueAfter deployedQueue backlog).excess + (queueAfter deployedQueue backlog).count < 2 ^ 256 - 1 := by
      rw [he, hcnt]
      omega
    have hne : (queueAfter deployedQueue backlog).excess ≠ 2 ^ 256 - 1 := by
      rw [he]
      decide
    rw [hsplit, hk']
    obtain ⟨h1, h2⟩ := replay_calls_excess 64 8 _ k hne hsum
    refine ⟨?_, h2⟩
    rw [h1, he, hcnt, Nat.zero_add]
    rfl

/-! ## O18 -/

/-- **The excess over the sequence, at the deposit contract.** Over any given chain from the deployed storage, with
the word range: slot 0 is the inhibitor exactly when the last system call had nonempty calldata (never, if every
call's calldata is empty, as in the request phase: `inhibitedAfter_requestPhase`); away from it `excess + count` is at most the
number of submissions so far; and until the first system call slot 0 is 0. -/
theorem excess_dynamics {frames : List Frame} {t : Stor} (chain : Chain Stor.empty frames t)
    (range : 4 + 6 * (submissions frames).length ≤ 2 ^ 256) :
    (t.get 0 = B256.max ↔ inhibitedAfter false (events frames) = true) ∧
      ((queueAfter deployedQueue frames).excess = 2 ^ 256 - 1 ∨
        (queueAfter deployedQueue frames).excess + (queueAfter deployedQueue frames).count ≤
          (submissions frames).length) ∧
      (NoSystem (events frames) → t.get 0 = 0) := by
  have hslots : queueBase 6 (deployedQueue.tail + (submissions frames).length) ≤ 2 ^ 256 := by
    show 4 + _ * (0 + _) ≤ _
    rw [Nat.zero_add]
    exact range
  have hcount : deployedQueue.count + (submissions frames).length < 2 ^ 256 := by
    show 0 + _ < _
    omega
  have hload : load deployedQueue = 0 := by decide
  have hiff := chain.excess_iff deployed_represents hslots hcount
  rw [show decide (deployedQueue.excess = 2 ^ 256 - 1) = false by decide] at hiff
  have hbound := excess_bound (c := contract) (frames := frames) (st := deployedQueue) (by decide)
    (by rw [hload]; omega)
  rw [hload, Nat.zero_add] at hbound
  refine ⟨hiff, hbound, fun none => ?_⟩
  have hx := (chain.holds deployed_represents hslots hcount).1.excess
  have he : (queueAfter deployedQueue frames).excess = 0 := excess_noSystem _ _ _ none
  rw [he] at hx
  exact hx

/-- **A quote over the sequence, at the deposit contract, in naturals.** A frame's word quote, with at most 2892
submissions before it on a chain from the deployed storage, is `fake_exponential(1, excess + max(0, count - 8), 17)`
of the queue it finds. `RequestFeeWord.word_fee_ne_natural_2893` is where this agreement stops. -/
theorem quote_natural {xs ys : List Frame} {f : Frame} {q : B256} {t : Stor}
    (chain : Chain Stor.empty (xs ++ f :: ys) t) (few : (submissions xs).length ≤ 2892)
    (hq : f.quotedFee = some q) :
    q.toNat = fakeExp 1 ((queueAfter deployedQueue xs).excess + ((queueAfter deployedQueue xs).count - 8)) 17 :=
  chain.quote_natural deployed_represents
    (by show 4 + 6 * (0 + _) ≤ _; omega) (by show 0 + _ < _; omega)
    (by decide) few hq

/-- **A backlog's decay.** After `k + 1` empty-calldata calls on the deployed storage's chain of `n` pre-fork
submissions, the excess is `n - 8 * (k + 1)` in naturals, so `max(0, n - 8)` after the first call, falling by 8 per
call to 0. -/
theorem backlog_decay {backlog calls : List Frame} {t : Stor} (chain : Chain Stor.empty (backlog ++ calls) t)
    (hp : ∀ f ∈ backlog, PreFork f) (hc : ∀ f ∈ calls, EmptyCall f)
    (range : 4 + 6 * (submissions backlog).length ≤ 2 ^ 256) (hk : 0 < calls.length) :
    (queueAfter deployedQueue (backlog ++ calls)).excess = (submissions backlog).length - 8 * calls.length :=
  ((prefork_then_calls chain hp hc range).2.2.2 hk).1

/-- **The fee at count `i`.** With `i` submissions before a frame and no system call, at most 2892 of them: its word quote is `fake_exponential(1, max(0, i - 8), 17)`. `i` counts the submissions
before this frame, so the first submission pays at `i = 0`, as `quotedFee` numbers them. -/
theorem fee_at_count {xs ys : List Frame} {f : Frame} {q : B256} {t : Stor}
    (chain : Chain Stor.empty (xs ++ f :: ys) t) (none : NoSystem (events xs))
    (few : (submissions xs).length ≤ 2892) (hq : f.quotedFee = some q) :
    q.toNat = quotedFee (submissions xs).length := by
  have h := quote_natural chain few hq
  rw [show (queueAfter deployedQueue xs).excess = 0 from excess_noSystem _ _ _ none,
    show (queueAfter deployedQueue xs).count = (submissions xs).length from
      (count_noSystem _ _ _ none).trans (Nat.zero_add _), Nat.zero_add] at h
  exact h

/-- **A submission paying the quote read at the same storage is admitted.** A frame quoted `q` on some storage. A
later machine `b` holding that same storage at the contract, under either fork's steps, with at least 1 ETH credited and value covering the credit plus `q` (`Admitted`): the submission
runs, at its stated charge and with its exact post state. -/
theorem paying_quote_admitted {f : Frame} {q : B256} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {l : StorageSteps sevm} (v : l.Valid) (hq : f.quotedFee = some q)
    (same : f.before = b.getStor address) (target : sevm.currentTarget = address)
    (hcode : sevm.code = code) (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 184)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) (pay : Admitted sevm q) :
    ∃ iterations, Nonempty (Exec 0 sevm (St b [] M (G + submissionGasOn l b M iterations))
      (.ok (Steps.submissionPost l (l.feeBase b) M (G + Steps.bodyRepay l (l.feeBase b) M)))) := by
  obtain ⟨i, o, rfl, run⟩ := f.quote_run hq
  have hactive := f.quoted_active hq
  rw [same] at run hactive
  have hread : ∀ k, b.getStorVal sevm.currentTarget k = (b.getStor address).get k := fun k => by
    rw [target]
    rfl
  refine ⟨i, exec_submission_on v hcode caller hlen dynamic slack (by rw [hread]; exact hactive) ?_ pay⟩
  rw [storedExcess, hread, hread]
  exact run

/-- **A later quote at the deposit contract, with the count.** With no system call in `ys`, a quoting frame after
them quotes `fake_exponential(1, excess + max(0, count + m - 8), 17)`: `excess` and `count` are the queue's after
`xs` and `m` the number of submissions in `ys`. Nothing else in between moves it. Under 2892 submissions before it. -/
theorem later_quote {xs ys zs : List Frame} {g : Frame} {q : B256} {t : Stor}
    (chain : Chain Stor.empty ((xs ++ ys) ++ g :: zs) t) (none : NoSystem (events ys))
    (few : (submissions (xs ++ ys)).length ≤ 2892) (hq : g.quotedFee = some q) :
    q.toNat = fakeExp 1 ((queueAfter deployedQueue xs).excess +
      ((queueAfter deployedQueue xs).count + (submissions ys).length - 8)) 17 :=
  chain.later_quote deployed_represents
    (by show 4 + 6 * (0 + _) ≤ _; omega) (by show 0 + _ < _; omega) (by decide) none few hq

end Blanc.Lift.BuilderRequest.Deposit
