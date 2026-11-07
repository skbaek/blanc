import Blanc.Lift.BuilderRequest.SystemCall
import Blanc.Lift.BuilderRequest.QueueLayout
import Blanc.MemoryWindows

/-!
# What a builder system call returns and leaves

`SysOutput` says a runtime's record writes extend the visible output by one record. `framePost_output`
then reads the whole return window, from any storage, as `drained`. `represents_sysState` is the
storage half of the FIFO: on storage representing a queue, the post storage represents the drained
queue, with the oldest `min(length, cap)` records gone. These are representation statements. Nothing
here says which storage is reachable, or that a stored record came from a real submission.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-- Storage reads leave storage alone. -/
theorem readsBase_getStorVal (sevm : Sevm) (d : Devm) (keys : List B256) (a : Adr) :
    (readsBase sevm d keys).getStorVal a = d.getStorVal a := by
  funext key
  unfold Devm.getStorVal Devm.getAcct
  rw [readsBase_state]

/-- A runtime's records extend the return window one at a time. -/
structure SysOutput (k : SysPath) (m : SysMemory k) where
  /-- One record's returned bytes, from the storage read. -/
  record : (B256 → B256) → B256 → B256 → Bytes
  extend : ∀ rd h (i : Nat) image, i < k.capN →
    ((k.stage rd h i.toB256).applyImage image).sliceD 0 (m.lenN * (i + 1)) 0 =
      image.sliceD 0 (m.lenN * i) 0 ++ record rd h i.toB256

namespace SysOutput

variable {k : SysPath} {m : SysMemory k} (o : SysOutput k m)

/-- The first `n` records' returned bytes. -/
def drained (rd : B256 → B256) (h : B256) (n : Nat) : Bytes :=
  (List.range n).flatMap fun i => o.record rd h i.toB256

theorem drained_succ (rd : B256 → B256) (h : B256) (n : Nat) :
    o.drained rd h (n + 1) = o.drained rd h n ++ o.record rd h n.toB256 := by
  simp only [drained, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The loop's memory reads as the records drained so far. -/
theorem fold_image {sevm : Sevm} {h : B256} {rd : B256 → B256} (n : Nat) {index : Nat} {b : Devm}
    {M : Mem} {image : Bytes} (hrd : b.getStorVal sevm.currentTarget = rd) (wf : Mem.Wf M)
    (reads : Mem.Reads M image) (bound : index + n ≤ k.capN)
    (hp : image.sliceD 0 (m.lenN * index) 0 = o.drained rd h index) :
    ∃ final, Mem.Reads (k.fold sevm h index n b M).memory final ∧
      final.sliceD 0 (m.lenN * (index + n)) 0 = o.drained rd h (index + n) := by
  induction n generalizing index b M image with
  | zero => exact ⟨image, reads, hp⟩
  | succ n ih =>
    have step := MemoryStage.wf_reads (k.stage rd h index.toB256) wf reads
    have hp' : ((k.stage rd h index.toB256).applyImage image).sliceD 0 (m.lenN * (index + 1)) 0 =
        o.drained rd h (index + 1) := by
      rw [o.extend rd h index image (by omega), hp, drained_succ]
    have hnext : k.fold sevm h index (n + 1) b M =
        let post := k.fold sevm h (index + 1) n (readsBase sevm b (k.keys h index.toB256))
          ((k.stage rd h index.toB256).applyMemory M)
        ⟨post.base, post.memory, 23 + k.bodyFixed + readsGas sevm b (k.keys h index.toB256) +
          MemoryStage.selectedGas (k.stage rd h index.toB256) M + post.charges⟩ := by
      subst hrd
      rfl
    obtain ⟨final, hr, hs⟩ := ih (index := index + 1) (b := readsBase sevm b (k.keys h index.toB256))
      (M := (k.stage rd h index.toB256).applyMemory M)
      (image := (k.stage rd h index.toB256).applyImage image)
      ((readsBase_getStorVal _ _ _ _).trans hrd) step.1 step.2 (by omega) hp'
    rw [hnext]
    refine ⟨final, hr, ?_⟩
    rw [show index + (n + 1) = index + 1 + n by omega]
    exact hs

/-- The return window's length, as a number. -/
theorem outLen_toNat (sevm : Sevm) (b : Devm) :
    (k.outLen sevm b).toNat = m.lenN * (k.count sevm b).toNat := by
  have hc := k.count_le sevm b
  have h1 := Nat.mul_le_mul_left m.lenN hc
  unfold SysPath.outLen
  rw [B256.toNat_mul, m.len_word]
  exact Nat.mod_eq_of_lt (by have := m.len_le; have := m.alloc_lt; omega)

/-- **What the frame returns, from any storage.** -/
theorem framePost_output (sevm : Sevm) (b : Devm) (G : Nat) :
    (k.framePost sevm b G).output =
      o.drained (SysPath.rd sevm b) (SysPath.rd sevm b 2) (k.count sevm b).toNat := by
  have hrd : (setupBase sevm b).getStorVal sevm.currentTarget = SysPath.rd sevm b := by
    funext key
    exact SysPath.getStorVal_of_state (SysPath.setupBase_state sevm b) key
  obtain ⟨final, hr, hs⟩ := o.fold_image (sevm := sevm) (h := SysPath.rd sevm b 2)
    (k.count sevm b).toNat (index := 0) (b := setupBase sevm b) (M := .empty) (image := [])
    hrd Mem.wf_empty Mem.reads_empty (by have := k.count_le sevm b; omega) (by
      simp only [Nat.mul_zero]
      rfl)
  show ((k.drain sevm b).memory.read (0 : B256).toNat (k.outLen sevm b).toNat).1 = _
  rw [show (k.drain sevm b).memory =
    (k.fold sevm (SysPath.rd sevm b 2) 0 (k.count sevm b).toNat (setupBase sevm b) .empty).memory
    from rfl, hr.read, outLen_toNat (m := m), show (0 : B256).toNat = 0 from rfl]
  simpa only [Nat.zero_add] using hs

end SysOutput

/-! ## The call on a queue -/

/-- What the call returns, from any storage. -/
theorem SysOutput.callPost_output {k : SysPath} {m : SysMemory k} (o : SysOutput k m) (benv : Benv)
    (target : Adr) :
    (SysPath.callPost k benv target).output =
      o.drained (fun key => (benv.state.getStor target).get key) ((benv.state.getStor target).get 2)
        (drainCount k.shape.cap.word ((benv.state.getStor target).get 2)
          ((benv.state.getStor target).get 3)).toNat :=
  o.framePost_output _ _ _

/-! ## The representation -/

variable {Record : Type}

/-- The queue a call leaves: the oldest `min(length, cap)` records gone, the pointers moved as the bytes
move them, the excess as stored, and the count cleared. -/
def drainedState (cap : Nat) (target : B256) (st : QueueState Record) : QueueState Record :=
  let excess := (excessNext target st.excess.toB256 st.count.toB256).toNat
  if st.queue.length ≤ cap then ⟨excess, 0, 0, 0, []⟩
  else ⟨excess, 0, st.head + cap, st.tail, st.queue.drop cap⟩

/-- The storage a call reads, as a function. -/
abbrev storOf (σ : State) (a : Adr) : B256 → B256 := fun key => (σ.getStor a).get key

/-- The count of records a call drains, on a represented queue. -/
theorem drainCount_represented {head len tail capN : Nat} {cap : B256} (hcap : cap.toNat = capN)
    (coherent : head + len = tail) (tail_lt : tail < 2 ^ 256) :
    drainCount cap head.toB256 tail.toB256 = (min len capN).toB256 := by
  have hdiff : tail.toB256 - head.toB256 = len.toB256 := by
    apply B256.toNat_inj
    rw [B256.toNat_sub, B256.toNat_toB256_of_lt tail_lt, B256.toNat_toB256_of_lt (by omega),
      B256.toNat_toB256_of_lt (by omega)]
    change (2 ^ 256 + tail - head) % 2 ^ 256 = len
    omega
  unfold drainCount
  rw [hdiff]
  by_cases hlt : len < capN
  · have hgt : cap > len.toB256 := by
      apply B256.lt_iff_toNat_lt_toNat.mpr
      rw [B256.toNat_toB256_of_lt (by omega), hcap]
      exact hlt
    rw [ite_eq_left_iff.mpr (fun no => absurd hgt no), Nat.min_eq_left (by omega)]
  · have hgt : ¬ cap > len.toB256 := by
      intro h
      have := B256.lt_iff_toNat_lt_toNat.mp h
      rw [B256.toNat_toB256_of_lt (by omega), hcap] at this
      omega
    rw [ite_eq_right_iff.mpr (fun yes => absurd yes hgt), Nat.min_eq_right (by omega), ← hcap,
      toB256_toNat]

/-- The post storage, slot by slot. -/
theorem sysState_get (p : SysShape) (σ : State) (a : Adr) (key : B256) :
    ((sysState p σ a).getStor a).get key =
      let rd := storOf σ a
      let c := drainCount p.cap.word (rd 2) (rd 3)
      if (1 : B256) = key then 0
      else if (0 : B256) = key then excessNext p.target.word (rd 0) (rd 1)
      else if rd 2 + c = rd 3 then
        (if (3 : B256) = key then 0 else if (2 : B256) = key then 0 else rd key)
      else (if (2 : B256) = key then rd 2 + c else rd key) := by
  simp only [sysState]
  split <;> simp only [State.getStor_setStorVal_self, Stor.get_set_ite]

/-- A live record's slot is none of the four metadata slots. -/
theorem queueSlot_ne {width index offset n : Nat} (hn : n < 4) {x : B256} (hx : x.toNat = n)
    (hlt : queueBase width index + width ≤ 2 ^ 256) (hj : offset < width) :
    x ≠ queueSlot width index offset := by
  intro eq
  have := congrArg B256.toNat eq
  rw [hx, queueSlot, B256.toNat_toB256_of_lt (by omega)] at this
  unfold queueBase at this
  omega

/-- **The storage half of the FIFO.** On storage representing a queue, a call's post storage represents
the queue with its oldest `min(length, cap)` records gone. -/
theorem represents_sysState {width : Nat} {words : Record → Nat → B256} (p : SysShape) {capN : Nat}
    (hcap : p.cap.word.toNat = capN) {σ : State} {a : Adr} {st : QueueState Record}
    (rep : Represents width words (storOf σ a) st) :
    Represents width words (storOf (sysState p σ a) a) (drainedState capN p.target.word st) := by
  have hcount := drainCount_represented hcap rep.coherent rep.tail_lt
  have hc : drainCount p.cap.word (storOf σ a 2) (storOf σ a 3) = (min st.queue.length capN).toB256 := by
    rw [rep.head, rep.tail]
    exact hcount
  have hadd : storOf σ a 2 + (min st.queue.length capN).toB256 =
      (st.head + min st.queue.length capN).toB256 := by
    rw [rep.head, toB256_add_toB256]
  have tail_lt := rep.tail_lt
  have coh := rep.coherent
  have hget : ∀ key, storOf (sysState p σ a) a key =
      if (1 : B256) = key then 0
      else if (0 : B256) = key then excessNext p.target.word st.excess.toB256 st.count.toB256
      else if st.queue.length ≤ capN then
        (if (3 : B256) = key then 0 else if (2 : B256) = key then 0 else storOf σ a key)
      else (if (2 : B256) = key then (st.head + capN).toB256 else storOf σ a key) := by
    intro key
    show ((sysState p σ a).getStor a).get key = _
    rw [sysState_get]
    dsimp only
    rw [hc, hadd, rep.excess, rep.count]
    by_cases hle : st.queue.length ≤ capN
    · have hem : (st.head + min st.queue.length capN).toB256 = storOf σ a 3 := by
        rw [rep.tail, Nat.min_eq_left hle, coh]
      rw [ite_eq_left_iff.mpr (fun no => absurd hem no), if_pos hle]
    · have hmin : min st.queue.length capN = capN := Nat.min_eq_right (by omega)
      have hne : ¬ (st.head + capN).toB256 = storOf σ a 3 := by
        rw [rep.tail]
        intro eq
        have := congrArg B256.toNat eq
        rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt tail_lt] at this
        omega
      rw [hmin, if_neg hne, if_neg hle]
  have h0 : (0 : Nat) < 2 ^ 256 := by decide
  unfold drainedState
  dsimp only
  by_cases hle : st.queue.length ≤ capN
  · rw [if_pos hle]
    refine ⟨by simp only [List.length_nil], B256.toNat_lt _, h0, h0, h0,
      fun i hi => absurd hi (by simp only [List.length_nil]; omega), ?_, ?_, ?_, ?_,
      fun i hi => absurd hi (by simp only [List.length_nil]; omega)⟩
    · rw [hget, if_neg (by decide), if_pos rfl, toB256_toNat]
    · rw [hget, if_pos rfl]
      rfl
    · rw [hget, if_neg (by decide), if_neg (by decide), if_pos hle, if_neg (by decide), if_pos rfl]
      rfl
    · rw [hget, if_neg (by decide), if_neg (by decide), if_pos hle, if_pos rfl]
      rfl
  · rw [if_neg hle]
    refine ⟨?_, B256.toNat_lt _, h0, (by show st.head + capN < 2 ^ 256; omega), tail_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_drop]
      omega
    · intro i hi
      simp only [List.length_drop] at hi
      have := rep.live_lt (capN + i) (by omega)
      rw [show st.head + capN + i = st.head + (capN + i) by omega]
      exact this
    · rw [hget, if_neg (by decide), if_pos rfl, toB256_toNat]
    · rw [hget, if_pos rfl]
      rfl
    · rw [hget, if_neg (by decide), if_neg (by decide), if_neg hle, if_pos rfl]
    · rw [hget, if_neg (by decide), if_neg (by decide), if_neg hle, if_neg (by decide)]
      exact rep.tail
    · intro i hi j hj
      simp only [List.length_drop] at hi
      have hl := rep.live_lt (capN + i) (by omega)
      have hslot : st.head + capN + i = st.head + (capN + i) := by omega
      rw [hslot]
      rw [hget, if_neg (queueSlot_ne (n := 1) (by omega) (by decide) hl hj),
        if_neg (queueSlot_ne (n := 0) (by omega) (by decide) hl hj), if_neg hle,
        if_neg (queueSlot_ne (n := 2) (by omega) (by decide) hl hj)]
      rw [rep.live (capN + i) (by omega) j hj, List.getElem_drop]

/-- On a represented queue, the first records are its oldest. -/
theorem flatMap_range_eq {out : Record → Bytes} (q : List Record) (f : Nat → Bytes) (n : Nat)
    (hn : n ≤ q.length) (hf : ∀ i (hi : i < q.length), i < n → f i = out q[i]) :
    (List.range n).flatMap f = (q.take n).flatMap out := by
  induction n with
  | zero => simp only [List.range_zero, List.flatMap_nil, List.take_zero]
  | succ n ih =>
    have hlt : n < q.length := by omega
    rw [List.range_succ, List.flatMap_append, ih (by omega) (fun i hi hin => hf i hi (by omega)),
      List.take_succ_eq_append_getElem hlt, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hf n hlt (by omega)]

/-- **The output half of the FIFO.** On storage representing a queue, the call returns the oldest
`min(length, cap)` records. -/
theorem SysOutput.output_represented {k : SysPath} {m : SysMemory k} (o : SysOutput k m)
    {width : Nat} {words : Record → Nat → B256} {out : Record → Bytes} {benv : Benv} {target : Adr}
    {st : QueueState Record} (rep : Represents width words (storOf benv.state target) st)
    (hrec : ∀ i (hi : i < st.queue.length), i < k.capN →
      o.record (storOf benv.state target) st.head.toB256 i.toB256 = out st.queue[i]) :
    (SysPath.callPost k benv target).output = (st.queue.take k.capN).flatMap out := by
  rw [o.callPost_output]
  have h2 : (benv.state.getStor target).get 2 = st.head.toB256 := rep.head
  have h3 : (benv.state.getStor target).get 3 = st.tail.toB256 := rep.tail
  rw [h2, h3, drainCount_represented k.cap_word rep.coherent rep.tail_lt]
  have hcap : k.capN < 2 ^ 256 := by
    have := k.cap_word
    have := B256.toNat_lt k.shape.cap.word
    omega
  rw [B256.toNat_toB256_of_lt (by omega)]
  have htake : st.queue.take k.capN = st.queue.take (min st.queue.length k.capN) := by
    rw [← List.take_take]
    exact (List.take_of_length_le (List.length_take_le' _ _)).symm
  rw [htake]
  exact flatMap_range_eq st.queue _ _ (by omega) (fun i hi hin => hrec i hi (by omega))

/-- **The request phase's call is the empty-data call.** One step of `runRequestContracts` is exactly
`processCheckedSystemTransaction benv addr []`, whatever the contract: the code's calldata latch needs
nonempty calldata, so it is unreachable from the request phase. -/
theorem runRequestContracts_step {idx : Nat} {ty : UInt8} {addr : Adr} {rest : List (UInt8 × Adr)}
    {benv : Benv} {acc : List Bytes} {bal : BalBuilder} {state : State} {out : MsgCallOutput}
    (h : processCheckedSystemTransaction benv addr [] = .ok (state, out)) :
    runRequestContracts idx ((ty, addr) :: rest) benv acc bal =
      runRequestContracts idx rest (benv.withState state)
        (if out.returnData.length > 0 then acc ++ [[ty] ++ out.returnData] else acc)
        (match benv.stat.rules.bal with
          | none => bal
          | some _ => bal.incorporate idx benv.state state (addr :: out.accountReads.toList)
              out.storageReads.toList out.storageWrites.toList) := by
  simp only [runRequestContracts, h, bind, Except.bind]
  rfl

/-- Slot 0 after a call on empty calldata is `excessNext`, never the calldata latch's inhibitor write. -/
theorem sysState_get_zero (p : SysShape) (σ : State) (a : Adr) :
    ((sysState p σ a).getStor a).get 0 =
      excessNext p.target.word ((σ.getStor a).get 0) ((σ.getStor a).get 1) := by
  rw [sysState_get]
  dsimp only
  rw [if_neg (by decide), if_pos rfl]

/-- The inhibitor resets the excess. -/
theorem excessNext_inhibitor (target count : B256) : excessNext target B256.max count = 0 := by
  simp only [excessNext, ite_true]

/-- With no excess, the next excess is the count over the target, in naturals. -/
theorem excessNext_zero (target : B256) {count : Nat} (hc : count < 2 ^ 256) :
    (excessNext target (0 : Nat).toB256 count.toB256).toNat = count - target.toNat := by
  have hmax : B256.max ≠ (0 : Nat).toB256 := by decide
  have hz : count.toB256 + (0 : Nat).toB256 = count.toB256 := by
    rw [toB256_add_toB256, Nat.add_zero]
  have hcn := B256.toNat_toB256_of_lt hc
  simp only [excessNext, if_neg hmax, hz]
  by_cases hgt : count.toB256 > target
  · have hlt := B256.lt_iff_toNat_lt_toNat.mp hgt
    rw [hcn] at hlt
    rw [if_pos hgt, B256.toNat_sub, hcn]
    change (2 ^ 256 + count - target.toNat) % 2 ^ 256 = _
    have := B256.toNat_lt target
    omega
  · have hle : ¬ target.toNat < count := fun hlt =>
      hgt (B256.lt_iff_toNat_lt_toNat.mpr (by rw [hcn]; exact hlt))
    rw [if_neg hgt, show (0 : B256).toNat = 0 from rfl]
    omega

/-- An account with this code and storage, in any state: the installation and storage premises can be
met together. -/
theorem install_witness (σ : State) (a : Adr) (code : ByteArray) (s : Stor) :
    (σ.set a { σ.get a with code := code, stor := s }).getCode a = code ∧
      storOf (σ.set a { σ.get a with code := code, stor := s }) a = fun key => s.get key := by
  constructor
  · unfold State.getCode
    rw [State.get_set_self]
  · funext key
    show ((σ.set a { σ.get a with code := code, stor := s }).get a).stor.get key = _
    rw [State.get_set_self]

end Blanc.Lift.BuilderRequest
