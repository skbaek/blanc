import Blanc.Lift.BuilderRequest.Exit.SystemCall
import Blanc.Lift.BuilderRequest.SystemOutput
import Blanc.WordByteCodecs

/-!
# The exit builder's system call on a queue

A record is the source address and the 48-byte public key: slot 0 holds the address, slots 1 and 2 the
key's first 32 and last 16 bytes (zero-padded), as a submission stores them. The call returns the oldest
`min(length, 16)` records, 68 bytes each.

These statements take storage representing a queue. They do not claim that storage at activation has
that shape, or that a stored record came from a real submission. **Build target:** Jaune pin `e8db2742`,
built on `tests@v21.0.1`, EELS `1562e2f`.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestSystem
open Creation (address)

/-- The bytes one record returns, from the storage read. -/
def recordBytes (rd : B256 → B256) (h i : B256) : Bytes :=
  (rd (recordKey h i) <<< 96).toBytes.sliceD 0 20 0 ++ (rd (1 + recordKey h i)).toBytes ++
    (rd (2 + recordKey h i)).toBytes.sliceD 0 16 0

/-- The exit runtime's output: each record extends the return window by 68 bytes. -/
def sysOutput : SysOutput sysPath sysMemory where
  record := recordBytes
  extend := fun rd h i image hi => by
    have hi' : i < 16 := hi
    show ((recordStage rd h i.toB256).applyImage image).sliceD 0 (68 * (i + 1)) 0 =
      image.sliceD 0 (68 * i) 0 ++ recordBytes rd h i.toB256
    rw [recordStage_eq hi' rd h]
    generalize hS : [(68 * i, (rd (recordKey h i.toB256) <<< 96).toBytes),
       (20 + 68 * i, (rd (1 + recordKey h i.toB256)).toBytes),
       (52 + 68 * i, (rd (2 + recordKey h i.toB256)).toBytes)] = S
    have w0 : (MemoryStage.applyImage S image).sliceD (68 * i) 20 0 =
        (rd (recordKey h i.toB256) <<< 96).toBytes.sliceD 0 20 0 := by
      subst hS
      refine window_at 0 image rfl ?_ (by omega) (by simp only [B256.length_toBytes]; omega)
      avoids_tac
    have w1 : (MemoryStage.applyImage S image).sliceD (68 * i + 20) 32 0 =
        (rd (1 + recordKey h i.toB256)).toBytes := by
      subst hS
      refine (window_at 1 image rfl ?_ (d := 0) (by omega)
        (by simp only [B256.length_toBytes]; omega)).trans (sliceD_self _ (B256.length_toBytes _))
      avoids_tac
    have w2 : (MemoryStage.applyImage S image).sliceD (68 * i + 20 + 32) 16 0 =
        (rd (2 + recordKey h i.toB256)).toBytes.sliceD 0 16 0 := by
      subst hS
      refine window_at 2 image rfl ?_ (by omega) (by simp only [B256.length_toBytes]; omega)
      avoids_tac
    have pre : (MemoryStage.applyImage S image).sliceD 0 (68 * i) 0 = image.sliceD 0 (68 * i) 0 := by
      subst hS
      apply MemoryStage.applyImage_sliceD_of_avoids
      avoids_tac
    rw [show 68 * (i + 1) = 68 * i + (20 + (32 + 16)) by omega, List.sliceD_split, Nat.zero_add,
      List.sliceD_split, List.sliceD_split, pre, w0, w1, w2]
    simp only [recordBytes, List.append_assoc]

/-- A record of the exit queue. -/
structure Record where
  source : Adr
  pubkey : Bytes
  pubkey_length : pubkey.length = 48

/-- A record's stored words: the address, then the key's two zero-padded chunks. -/
def Record.word (r : Record) : Nat → B256
  | 0 => r.source.toB256
  | 1 => Bytes.toB256 (r.pubkey.sliceD 0 32 0)
  | _ => Bytes.toB256 (r.pubkey.sliceD 32 32 0)

/-- A record as the call returns it. -/
def Record.out (r : Record) : Bytes := r.source.toBytes ++ r.pubkey

/-- A nested slice inside a slice. -/
theorem word_slice16 (xs : Bytes) :
    (Bytes.toB256 (xs.sliceD 32 32 0)).toBytes.sliceD 0 16 0 = xs.sliceD 32 16 0 := by
  rw [Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)]
  rw [show (32 : Nat) = 16 + 16 by rfl, List.sliceD_split]
  have h := Bytes.sliceD_append_middle [] (xs.sliceD (16 + 16) 16 0) (xs.sliceD (16 + 16 + 16) 16 0)
  rw [List.length_nil, List.length_sliceD] at h
  exact h

/-- A record's returned bytes, from its stored words. -/
theorem recordBytes_eq {rd : B256 → B256} {h i : B256} (r : Record)
    (h0 : rd (recordKey h i) = r.word 0) (h1 : rd (1 + recordKey h i) = r.word 1)
    (h2 : rd (2 + recordKey h i) = r.word 2) :
    recordBytes rd h i = r.out := by
  have hsplit : r.pubkey = r.pubkey.sliceD 0 32 0 ++ r.pubkey.sliceD 32 16 0 := by
    have := List.sliceD_split r.pubkey (0 : UInt8) 32 0 16
    rw [Nat.zero_add] at this
    rw [← this]
    exact (sliceD_self _ r.pubkey_length).symm
  unfold recordBytes Record.out
  rw [h0, h1, h2]
  have ha : (r.word 0 <<< 96).toBytes.sliceD 0 20 0 = r.source.toBytes := by
    unfold List.sliceD
    rw [List.drop_zero, List.takeD_eq_take _ (by rw [B256.length_toBytes]; omega),
      WordByteCodecs.shift96_take20_toAdr_bytes]
    show (r.source.toB256).toAdr.toBytes = _
    rw [toAdr_toB256]
  rw [ha]
  show _ ++ (Bytes.toB256 (r.pubkey.sliceD 0 32 0)).toBytes ++
    (Bytes.toB256 (r.pubkey.sliceD 32 32 0)).toBytes.sliceD 0 16 0 = _
  rw [Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _), word_slice16]
  conv_rhs => rw [hsplit]
  rw [List.append_assoc]

/-- Queue keys at a represented head. -/
theorem recordKey_slot (head i : Nat) : recordKey head.toB256 i.toB256 = queueSlot 3 (head + i) 0 := by
  unfold recordKey
  rw [Nat.toB256_add_toB256, ← record_key, Nat.add_comm i head]
  rfl

/-- **The exit builder's FIFO.** On storage representing a queue, the checked system call returns the
oldest `min(length, 16)` records, and its post storage represents the queue without them. The pointers,
count and excess are those of `drainedState`: head and tail reset when the queue empties, otherwise the
head advances; the count clears; the excess is `excessNext`, which resets the inhibitor to zero. It uses at
most 161,000 regular gas, state gas excluded: state gas draws on the reservoir of 16 × `storageSet`. -/
theorem system_call_fifo {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) {st : QueueState Record}
    (rep : Represents 3 Record.word (storOf benv.state address) st) :
    ∃ post out, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
      RegularGasWithin out.gasLeft 161000 ∧
      out.returnData = (st.queue.take 16).flatMap Record.out ∧
      Represents 3 Record.word (storOf post address) (drainedState 16 2 st) := by
  obtain ⟨hcall, hgas⟩ := sysCall.spec hfork installed
  replace hcall : processCheckedSystemTransaction benv address [] =
      .ok (sysState sysShape benv.state address, _) := hcall
  refine ⟨_, _, hcall, hgas, ?_, represents_sysState sysShape (by decide) rfl rep⟩
  refine output_represented sysOutput (out := Record.out) rep ?_
  intro i hi hcap
  have hlive := rep.live i hi
  refine recordBytes_eq _ ?_ ?_ ?_
  · rw [recordKey_slot]
    exact hlive 0 (by decide)
  · have key : (1 : B256) + queueSlot 3 (st.head + i) 0 = queueSlot 3 (st.head + i) 1 := by
      rw [show (1 : B256) = Nat.toB256 1 by decide]
      exact record_key_add 3 (st.head + i) 0 1
    rw [recordKey_slot, key]
    exact hlive 1 (by decide)
  · have key : (2 : B256) + queueSlot 3 (st.head + i) 0 = queueSlot 3 (st.head + i) 2 := by
      rw [show (2 : B256) = Nat.toB256 2 by decide]
      exact record_key_add 3 (st.head + i) 0 2
    rw [recordKey_slot, key]
    exact hlive 2 (by decide)

/-- **The exit contract's activation step.** On the deployed storage (`Creation.factory_deploy`'s
`Stor.empty.set 0 B256.max`), the checked system call succeeds, returns nothing, and moves slot 0 from
the inhibitor to 0, leaving every slot 0, within 161,000 regular gas, state gas excluded: state gas draws
on the reservoir of 16 × `storageSet`. -/
theorem activation_unlocks {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code)
    (deployed : benv.state.getStor address = Stor.empty.set 0 B256.max) :
    ∃ post out, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
      RegularGasWithin out.gasLeft 161000 ∧
      out.returnData = [] ∧ ∀ key, (post.getStor address).get key = 0 := by
  obtain ⟨hcall, hgas⟩ := sysCall.spec hfork installed
  replace hcall : processCheckedSystemTransaction benv address [] =
      .ok (sysState sysShape benv.state address, _) := hcall
  have hget : ∀ key, (benv.state.getStor address).get key = if (0 : B256) = key then B256.max else 0 := by
    intro key
    rw [deployed, Stor.get_set_ite]
    rfl
  have h0 : (benv.state.getStor address).get 0 = B256.max := by rw [hget]; rfl
  have h1 : (benv.state.getStor address).get 1 = 0 := by rw [hget, if_neg (by decide)]
  have h2 : (benv.state.getStor address).get 2 = 0 := by rw [hget, if_neg (by decide)]
  have h3 : (benv.state.getStor address).get 3 = 0 := by rw [hget, if_neg (by decide)]
  have hc : drainCount sysShape.cap.word 0 0 = 0 := by decide
  refine ⟨_, _, hcall, hgas, ?_, ?_⟩
  · show (SysPath.callPost sysPath benv address).output = []
    rw [sysOutput.callPost_output]
    show sysOutput.drained _ _ (drainCount sysShape.cap.word _ _).toNat = []
    rw [h2, h3, hc]
    rfl
  · intro key
    rw [sysState_get]
    show (if (1 : B256) = key then _ else if (0 : B256) = key then
        excessNext sysShape.target.word ((benv.state.getStor address).get 0)
          ((benv.state.getStor address).get 1)
      else if (benv.state.getStor address).get 2 +
          drainCount sysShape.cap.word ((benv.state.getStor address).get 2)
            ((benv.state.getStor address).get 3) = (benv.state.getStor address).get 3 then
        (if (3 : B256) = key then 0 else if (2 : B256) = key then 0
          else (benv.state.getStor address).get key)
      else _) = _
    rw [h0, h1, h2, h3, hc, excessNext_inhibitor, if_pos (by decide : (0 : B256) + 0 = 0)]
    by_cases k1 : (1 : B256) = key
    · rw [if_pos k1]
    · rw [if_neg k1]
      by_cases k0 : (0 : B256) = key
      · rw [if_pos k0]
      · rw [if_neg k0]
        by_cases k3 : (3 : B256) = key
        · rw [if_pos k3]
        · rw [if_neg k3]
          by_cases k2 : (2 : B256) = key
          · rw [if_pos k2]
          · rw [if_neg k2, hget, if_neg k0]

/-- **The calldata latch is unreachable from the request phase.** One request-phase step at this contract
is the call with `[]` calldata, whose post state is `sysState`; slot 0 after it is `excessNext`, which is
never the inhibitor, so a request-phase step never leaves slot 0 at `B256.max`, whatever it was before. Change
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
        excessNext 2 ((benv.state.getStor address).get 0) ((benv.state.getStor address).get 1) ∧
      ((sysState sysShape benv.state address).getStor address).get 0 ≠ B256.max :=
  let h := (sysCall.spec hfork installed).1
  ⟨_, h, runRequestContracts_step h, sysState_get_zero _ _ _,
    (sysState_get_zero _ _ _).trans_ne (excessNext_ne_max (by decide) _ _)⟩

/-! ## The statements can be met -/

/-- A record for the witness. -/
def witnessRecord : Record := ⟨1, List.replicate 48 0xaa, by decide⟩

/-- Storage holding a one-record queue. -/
def witnessStor : Stor :=
  (((((Stor.empty.set 1 1).set 3 1).set 4 (witnessRecord.word 0)).set 5 (witnessRecord.word 1)).set 6
    (witnessRecord.word 2))

/-- That queue. -/
def witnessQueue : QueueState Record := ⟨0, 1, 0, 1, [witnessRecord]⟩

/-- **The FIFO's premise can be met**, on a non-empty queue. -/
theorem witness_represents : Represents 3 Record.word (fun key => witnessStor.get key) witnessQueue where
  coherent := rfl
  excess_lt := by decide
  count_lt := by decide
  head_lt := by decide
  tail_lt := by decide
  live_lt := fun i hi => by
    have hi' : i < 1 := hi
    obtain rfl : i = 0 := by omega
    decide
  excess := by simp (decide := true) only [witnessStor, Stor.get_set_ite]
  count := by simp (decide := true) only [witnessStor, Stor.get_set_ite]
  head := by simp (decide := true) only [witnessStor, Stor.get_set_ite]
  tail := by simp (decide := true) only [witnessStor, Stor.get_set_ite]
  live := fun i hi j hj => by
    have hi' : i < 1 := hi
    obtain rfl : i = 0 := by omega
    have hkey : ∀ n, queueSlot 3 (witnessQueue.head + 0) n = (4 + n).toB256 := fun _ => rfl
    rw [hkey]
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;>
      simp (decide := true) only [witnessStor, Stor.get_set_ite] <;> rfl

/-- **Installation and the queue premise together.** From any state, an account with the canonical code
and this storage meets both premises of `system_call_fifo`, on a one-record queue. -/
theorem witness_state (σ : State) :
    ∃ σ' : State, σ'.getCode address = code ∧
      Represents 3 Record.word (storOf σ' address) witnessQueue := by
  obtain ⟨hc, hs⟩ := install_witness σ address code witnessStor
  exact ⟨_, hc, by rw [hs]; exact witness_represents⟩

end Blanc.Lift.BuilderRequest.Exit
