import Blanc.Lift.BuilderRequest.Deposit.SystemCall
import Blanc.Lift.BuilderRequest.SystemOutput
import Blanc.WordByteCodecs

/-!
# The deposit builder's system call on a queue

A record is the 184 submission bytes: public key, withdrawal credentials, amount, signature. Slots 0 to 5
hold its six calldata words, the last zero-padded, as a submission stores them. The call returns the oldest
`min(length, 64)` records, 184 bytes each, with each amount's eight bytes reversed: big-endian in the
record, little-endian in the output.

These statements take storage representing a queue. They do not claim that storage at activation has that
shape, that a stored record came from a real submission, or anything about a first Amsterdam block's
transactions. **Build target:** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open Creation (address)

/-- The amount's bytes as the code writes them, low byte first. -/
def amountLE (w : B256) : Bytes :=
  [(amountOf w).2.2.toUInt8, (amountOf w >>> 8).2.2.toUInt8, (amountOf w >>> 16).2.2.toUInt8,
    (amountOf w >>> 24).2.2.toUInt8, (amountOf w >>> 32).2.2.toUInt8, (amountOf w >>> 40).2.2.toUInt8,
    (amountOf w >>> 48).2.2.toUInt8, (amountOf w >>> 56).2.2.toUInt8]

/-- The bytes one record returns, from the storage read. -/
def recordBytes (rd : B256 → B256) (h i : B256) : Bytes :=
  (rd (recordKey h i)).toBytes ++ (rd (1 + recordKey h i)).toBytes ++
    (rd (2 + recordKey h i)).toBytes.sliceD 0 16 0 ++ amountLE (rd (2 + recordKey h i)) ++
    (rd (2 + recordKey h i)).toBytes.sliceD 24 8 0 ++ (rd (3 + recordKey h i)).toBytes ++
    (rd (4 + recordKey h i)).toBytes ++ (rd (5 + recordKey h i)).toBytes.sliceD 0 24 0

/-- The deposit runtime's output: each record extends the return window by 184 bytes. -/
def sysOutput : SysOutput sysPath sysMemory where
  record := recordBytes
  extend := fun rd h i image hi => by
    have hi' : i < 64 := hi
    show ((recordStage rd h i.toB256).applyImage image).sliceD 0 (184 * (i + 1)) 0 =
      image.sliceD 0 (184 * i) 0 ++ recordBytes rd h i.toB256
    have hS := recordStage_eq hi' rd h
    dsimp only at hS
    generalize recordStage rd h i.toB256 = S at hS
    have hl : ∀ v : B256, v.toBytes.length = 32 := B256.length_toBytes
    have w0 : (MemoryStage.applyImage S image).sliceD (184 * i) 32 0 =
        (rd (recordKey h i.toB256)).toBytes := by
      subst hS
      refine (window_at 0 image rfl ?_ (d := 0) (by omega) (by rw [hl]; try omega)).trans
        (sliceD_self _ (hl _))
      avoids_tac
    have w1 : (MemoryStage.applyImage S image).sliceD (184 * i + 32) 32 0 =
        (rd (1 + recordKey h i.toB256)).toBytes := by
      subst hS
      refine (window_at 1 image rfl ?_ (d := 0) (by omega) (by rw [hl]; try omega)).trans
        (sliceD_self _ (hl _))
      avoids_tac
    have w2 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32) 16 0 =
        (rd (2 + recordKey h i.toB256)).toBytes.sliceD 0 16 0 := by
      subst hS
      refine window_at 2 image rfl ?_ (by omega) (by rw [hl]; try omega)
      avoids_tac
    have y0 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16) 1 0 =
        [(amountOf (rd (2 + recordKey h i.toB256))).2.2.toUInt8] := by
      subst hS
      refine (window_at 10 image rfl ?_ (d := 0) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)).trans
        (sliceD_self _ rfl)
      avoids_tac
    have y1 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1) 1 0 =
        [(amountOf (rd (2 + recordKey h i.toB256)) >>> 8).2.2.toUInt8] := by
      subst hS
      refine (window_at 9 image rfl ?_ (d := 0) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)).trans
        (sliceD_self _ rfl)
      avoids_tac
    have y2 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1) 1 0 =
        [(amountOf (rd (2 + recordKey h i.toB256)) >>> 16).2.2.toUInt8] := by
      subst hS
      refine (window_at 8 image rfl ?_ (d := 0) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)).trans
        (sliceD_self _ rfl)
      avoids_tac
    have y3 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1 + 1) 1 0 =
        [(amountOf (rd (2 + recordKey h i.toB256)) >>> 24).2.2.toUInt8] := by
      subst hS
      refine (window_at 7 image rfl ?_ (d := 0) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)).trans
        (sliceD_self _ rfl)
      avoids_tac
    have y4 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1 + 1 + 1) 1 0 =
        [(amountOf (rd (2 + recordKey h i.toB256)) >>> 32).2.2.toUInt8] := by
      subst hS
      refine (window_at 6 image rfl ?_ (d := 0) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)).trans
        (sliceD_self _ rfl)
      avoids_tac
    have y5 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1 + 1 + 1 + 1) 1 0 =
        [(amountOf (rd (2 + recordKey h i.toB256)) >>> 40).2.2.toUInt8] := by
      subst hS
      refine (window_at 5 image rfl ?_ (d := 0) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)).trans
        (sliceD_self _ rfl)
      avoids_tac
    have y6 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1 + 1 + 1 + 1 + 1) 1 0 =
        [(amountOf (rd (2 + recordKey h i.toB256)) >>> 48).2.2.toUInt8] := by
      subst hS
      refine (window_at 4 image rfl ?_ (d := 0) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)).trans
        (sliceD_self _ rfl)
      avoids_tac
    have y7 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1 + 1 + 1 + 1 + 1 + 1) 1 0 =
        [(amountOf (rd (2 + recordKey h i.toB256)) >>> 56).2.2.toUInt8] := by
      subst hS
      refine (window_at 3 image rfl ?_ (d := 0) (by omega) (by simp only [List.length_cons, List.length_nil]; omega)).trans
        (sliceD_self _ rfl)
      avoids_tac
    have w2' : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) 8 0 =
        (rd (2 + recordKey h i.toB256)).toBytes.sliceD 24 8 0 := by
      subst hS
      refine window_at 2 image rfl ?_ (by omega) (by rw [hl]; try omega)
      avoids_tac
    have w3 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 8) 32 0 =
        (rd (3 + recordKey h i.toB256)).toBytes := by
      subst hS
      refine (window_at 11 image rfl ?_ (d := 0) (by omega) (by rw [hl]; try omega)).trans (sliceD_self _ (hl _))
      avoids_tac
    have w4 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 8 + 32) 32 0 =
        (rd (4 + recordKey h i.toB256)).toBytes := by
      subst hS
      refine (window_at 12 image rfl ?_ (d := 0) (by omega) (by rw [hl]; try omega)).trans (sliceD_self _ (hl _))
      avoids_tac
    have w5 : (MemoryStage.applyImage S image).sliceD (184 * i + 32 + 32 + 16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 8 + 32 + 32) 24 0 =
        (rd (5 + recordKey h i.toB256)).toBytes.sliceD 0 24 0 := by
      subst hS
      refine window_at 13 image rfl ?_ (by omega) (by rw [hl]; try omega)
      avoids_tac
    have pre : (MemoryStage.applyImage S image).sliceD 0 (184 * i) 0 = image.sliceD 0 (184 * i) 0 := by
      subst hS
      apply MemoryStage.applyImage_sliceD_of_avoids
      avoids_tac
    rw [show 184 * (i + 1) = 184 * i + (32 + (32 + (16 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (8 + (32 + (32 + 24)))))))))))))) by omega,
      List.sliceD_split, Nat.zero_add]
    repeat rw [List.sliceD_split]
    rw [pre, w0, w1, w2, y0, y1, y2, y3, y4, y5, y6, y7, w2', w3, w4, w5]
    simp only [recordBytes, amountLE, List.append_assoc, List.cons_append, List.nil_append]

/-! ## The record model -/

/-- A record of the deposit queue. -/
structure Record where
  pubkey : Bytes
  credentials : Bytes
  /-- The amount, big-endian as submitted. -/
  amount : Bytes
  signature : Bytes
  pubkey_length : pubkey.length = 48
  credentials_length : credentials.length = 32
  amount_length : amount.length = 8
  signature_length : signature.length = 96

/-- The record as submitted. -/
def Record.data (r : Record) : Bytes := r.pubkey ++ r.credentials ++ r.amount ++ r.signature

/-- A record's stored words: the data's six 32-byte chunks, the last zero-padded. -/
def Record.word (r : Record) (j : Nat) : B256 := Bytes.toB256 (r.data.sliceD (32 * j) 32 0)

/-- A record as the call returns it: the amount recoded to little-endian. -/
def Record.out (r : Record) : Bytes :=
  r.pubkey ++ r.credentials ++ r.amount.reverse ++ r.signature

theorem max_and (x : UInt64) : (18446744073709551615 : UInt64) &&& x = x := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (18446744073709551615 : UInt64).toNat = 2 ^ 64 - 1 from rfl, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.toNat_lt_size]

/-- A word holding only `w`'s amount lane, at its place. -/
def amountWord (w : B256) : B256 := ((0, 0), (w.2.1, 0))

/-- The masked amount's bytes are the word's bytes 16 to 23, reversed. -/
theorem amountLE_eq (w : B256) : amountLE w = (w.toBytes.sliceD 16 8 0).reverse := by
  rcases w with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  have hamt : amountOf ((a, b), c, d) = amountWord ((a, b), c, d) >>> 64 := by
    unfold amountOf amountWord
    apply Prod.ext
    · apply Prod.ext
      · exact UInt64.zero_and
      · exact UInt64.zero_and
    · apply Prod.ext
      · exact UInt64.zero_and
      · exact max_and _
  have hslice : (amountWord ((a, b), c, d)).toBytes.sliceD 16 8 0 =
      (B256.toBytes ((a, b), c, d)).sliceD 16 8 0 := rfl
  unfold amountLE
  rw [hamt, ← hslice]
  exact WordByteCodecs.shift64_low_bytes_reverse_slice16 _

/-- A record's returned bytes, from its stored words. -/
theorem recordBytes_eq {rd : B256 → B256} {h i : B256} (r : Record)
    (h0 : rd (recordKey h i) = r.word 0) (h1 : rd (1 + recordKey h i) = r.word 1)
    (h2 : rd (2 + recordKey h i) = r.word 2) (h3 : rd (3 + recordKey h i) = r.word 3)
    (h4 : rd (4 + recordKey h i) = r.word 4) (h5 : rd (5 + recordKey h i) = r.word 5) :
    recordBytes rd h i = r.out := by
  have hb : ∀ j, (r.word j).toBytes = r.data.sliceD (32 * j) 32 0 := fun j =>
    Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)
  have lp := r.pubkey_length
  have lc := r.credentials_length
  have la := r.amount_length
  have ls := r.signature_length
  have hpre : (r.pubkey ++ r.credentials).length = 80 := by
    rw [List.length_append]
    omega
  have hD : r.data = (r.pubkey ++ r.credentials) ++ r.amount ++ r.signature := rfl
  have hA : r.data.sliceD 0 80 0 = r.pubkey ++ r.credentials := by
    have := Bytes.sliceD_append_middle [] (r.pubkey ++ r.credentials) (r.amount ++ r.signature)
    rw [List.length_nil, hpre] at this
    rw [hD, List.append_assoc]
    exact this
  have hB : r.data.sliceD 80 8 0 = r.amount := by
    have := Bytes.sliceD_append_middle (r.pubkey ++ r.credentials) r.amount r.signature
    rw [hpre, la] at this
    rw [hD]
    exact this
  have hC : r.data.sliceD 88 96 0 = r.signature := by
    have := Bytes.sliceD_append_middle (r.pubkey ++ r.credentials ++ r.amount) r.signature []
    rw [List.length_append, hpre, la, ls, List.append_nil] at this
    rw [hD]
    exact this
  unfold recordBytes Record.out
  rw [h0, h1, h2, h3, h4, h5, amountLE_eq]
  simp only [hb]
  rw [sliceD_sliceD _ (by omega), sliceD_sliceD _ (by omega), sliceD_sliceD _ (by omega),
    sliceD_sliceD _ (by omega)]
  have e0 : r.data.sliceD (32 * 0) 32 0 ++ r.data.sliceD (32 * 1) 32 0 ++
      r.data.sliceD (32 * 2 + 0) 16 0 = r.pubkey ++ r.credentials := by
    rw [← hA, show (80 : Nat) = 32 + (32 + 16) by rfl, List.sliceD_split, List.sliceD_split,
      List.append_assoc]
  have e1 : r.data.sliceD (32 * 2 + 16) 8 0 = r.amount := hB
  have e2 : r.data.sliceD (32 * 2 + 24) 8 0 ++ r.data.sliceD (32 * 3) 32 0 ++
      r.data.sliceD (32 * 4) 32 0 ++ r.data.sliceD (32 * 5 + 0) 24 0 = r.signature := by
    rw [← hC, show (96 : Nat) = 8 + (32 + (32 + 24)) by rfl, List.sliceD_split, List.sliceD_split,
      List.sliceD_split, List.append_assoc, List.append_assoc]
  rw [e1, ← e0, ← e2]
  simp only [List.append_assoc]

/-- Queue keys at a represented head. -/
theorem recordKey_slot (head i : Nat) : recordKey head.toB256 i.toB256 = queueSlot 6 (head + i) 0 := by
  unfold recordKey
  rw [toB256_add_toB256, ← record_key, Nat.add_comm i head]
  rfl

/-- **The deposit builder's FIFO.** On storage representing a queue, the checked system call returns the
oldest `min(length, 64)` records with their amounts little-endian, and its post storage represents the
queue without them. The pointers, count and excess are those of `drainedState`: head and tail reset when
the queue empties, otherwise the head advances; the count clears; the excess is `excessNext`, which resets
the inhibitor to zero. -/
theorem system_call_fifo {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) {st : QueueState Record}
    (rep : Represents 6 Record.word (storOf benv.state address) st) :
    ∃ post out, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
      systemTransactionGas - out.gasLeft ≤ 888000 ∧
      out.returnData = (st.queue.take 64).flatMap Record.out ∧
      Represents 6 Record.word (storOf post address) (drainedState 64 8 st) := by
  obtain ⟨hcall, hgas⟩ := sysCall.spec hfork installed
  replace hcall : processCheckedSystemTransaction benv address [] =
      .ok (sysState sysShape benv.state address, _) := hcall
  refine ⟨_, _, hcall, hgas, ?_, represents_sysState sysShape (by decide) rep⟩
  refine sysOutput.output_represented (out := Record.out) rep ?_
  intro i hi hcap
  have hlive := rep.live i hi
  have key : ∀ (x : B256) (n : Nat), x = Nat.toB256 n → n < 6 →
      storOf benv.state address (x + recordKey st.head.toB256 i.toB256) = st.queue[i].word n := by
    intro x n hx hn
    subst hx
    have e := record_key_add 6 (st.head + i) 0 n
    rw [Nat.zero_add] at e
    rw [recordKey_slot st.head i, e]
    exact hlive n hn
  refine recordBytes_eq _ ?_ (key 1 1 (by decide) (by decide)) (key 2 2 (by decide) (by decide))
    (key 3 3 (by decide) (by decide)) (key 4 4 (by decide) (by decide)) (key 5 5 (by decide) (by decide))
  rw [recordKey_slot]
  exact hlive 0 (by decide)

/-- **The deposit contract's activation step.** On any storage representing a queue with excess 0 and any
count, the call drains the oldest `min(length, 64)` records, sets the excess to `max(0, count - 8)` and clears
the count. It claims nothing about whether storage at activation has this shape. -/
theorem activation_step {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) {st : QueueState Record}
    (rep : Represents 6 Record.word (storOf benv.state address) st) (hexcess : st.excess = 0) :
    ∃ post out, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
      systemTransactionGas - out.gasLeft ≤ 888000 ∧
      out.returnData = (st.queue.take 64).flatMap Record.out ∧
      Represents 6 Record.word (storOf post address) (drainedState 64 8 st) ∧
      (drainedState 64 8 st).excess = st.count - 8 ∧ (drainedState 64 8 st).count = 0 := by
  obtain ⟨post, out, h1, h2, h3, h4⟩ := system_call_fifo hfork installed rep
  have hE : (excessNext 8 st.excess.toB256 st.count.toB256).toNat = st.count - 8 := by
    rw [hexcess]
    exact excessNext_zero 8 rep.count_lt
  refine ⟨post, out, h1, h2, h3, h4, ?_, ?_⟩
  · unfold drainedState
    dsimp only
    split <;> exact hE
  · unfold drainedState
    dsimp only
    split <;> rfl

/-- **The calldata latch is unreachable from the request phase.** One request-phase step at this contract
is the call with `[]` calldata, whose post state is `sysState`, and slot 0 after it is `excessNext`. Change
the `[]` and this no longer follows: `runRequestContracts` passes exactly that argument. -/
theorem request_step_no_latch {idx : Nat} {ty : UInt8} {rest : List (UInt8 × Adr)} {benv : Benv}
    {acc : List Bytes} {bal : BalBuilder} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) :
    ∃ out, processCheckedSystemTransaction benv address [] =
        .ok (sysState sysShape benv.state address, out) ∧
      runRequestContracts idx ((ty, address) :: rest) benv acc bal =
        runRequestContracts idx rest (benv.withState (sysState sysShape benv.state address))
          (if out.returnData.length > 0 then acc ++ [[ty] ++ out.returnData] else acc)
          (match benv.stat.rules.bal with
            | none => bal
            | some _ => bal.incorporate idx benv.state (sysState sysShape benv.state address)
                (address :: out.accountReads.toList) out.storageReads.toList out.storageWrites.toList) ∧
      ((sysState sysShape benv.state address).getStor address).get 0 =
        excessNext 8 ((benv.state.getStor address).get 0) ((benv.state.getStor address).get 1) :=
  let h := (sysCall.spec hfork installed).1
  ⟨_, h, runRequestContracts_step h, sysState_get_zero _ _ _⟩

/-! ## The statements can be met -/

/-- Storage holding a one-record queue. -/
def witnessStor (r : Record) : Stor :=
  ((((((((Stor.empty.set 1 1).set 3 1).set 4 (r.word 0)).set 5 (r.word 1)).set 6 (r.word 2)).set 7
    (r.word 3)).set 8 (r.word 4)).set 9 (r.word 5))

/-- That queue. -/
def witnessQueue (r : Record) : QueueState Record := ⟨0, 1, 0, 1, [r]⟩

/-- **The FIFO's premise can be met**, on a non-empty queue, for every record. -/
theorem witness_represents (r : Record) :
    Represents 6 Record.word (fun key => (witnessStor r).get key) (witnessQueue r) where
  coherent := rfl
  excess_lt := show 0 < 2 ^ 256 by decide
  count_lt := show 1 < 2 ^ 256 by decide
  head_lt := show 0 < 2 ^ 256 by decide
  tail_lt := show 1 < 2 ^ 256 by decide
  live_lt := fun i hi => by
    have hi' : i < 1 := hi
    obtain rfl : i = 0 := by omega
    show queueBase 6 0 + 6 ≤ 2 ^ 256
    decide
  excess := by simp (decide := true) only [witnessStor, Stor.get_set_ite, ↓reduceIte]; rfl
  count := by simp (decide := true) only [witnessStor, Stor.get_set_ite, ↓reduceIte]; rfl
  head := by simp (decide := true) only [witnessStor, Stor.get_set_ite, ↓reduceIte]; rfl
  tail := by simp (decide := true) only [witnessStor, Stor.get_set_ite, ↓reduceIte]; rfl
  live := fun i hi j hj => by
    have hi' : i < 1 := hi
    obtain rfl : i = 0 := by omega
    have hkey : ∀ n, queueSlot 6 ((witnessQueue r).head + 0) n = (4 + n).toB256 := fun _ => rfl
    rw [hkey]
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (decide := true) only [witnessStor, Stor.get_set_ite, ↓reduceIte] <;> rfl

/-- A record exists, so the witness is not vacuous. -/
def witnessRecord : Record :=
  ⟨List.replicate 48 0xaa, List.replicate 32 0xbb, List.replicate 8 0xcc, List.replicate 96 0xdd,
    by decide, by decide, by decide, by decide⟩

/-- **Installation and the queue premise together.** From any state, an account with the canonical code
and this storage meets both premises of `system_call_fifo`, on a one-record queue. -/
theorem witness_state (σ : State) :
    ∃ σ' : State, σ'.getCode address = code ∧
      Represents 6 Record.word (storOf σ' address) (witnessQueue witnessRecord) := by
  obtain ⟨hc, hs⟩ := install_witness σ address code (witnessStor witnessRecord)
  exact ⟨_, hc, by rw [hs]; exact witness_represents witnessRecord⟩

end Blanc.Lift.BuilderRequest.Deposit
