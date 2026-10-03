import Blanc.Lift.WithdrawalRequest.Model
import Blanc.CommonProofs

/-!
# EIP-7002 fields and concrete byte/word representation

The logical fields and order are those of the EIP model. Input and LOG0 retain
the big-endian amount; system return records use little-endian amount bytes.
Concrete queue words describe CALDATALOAD packing, not the EIP pseudocode's
little-endian storage notation. This module proves no EVM execution or gas law.
-/

namespace Blanc.WithdrawalRequest

open Jaune

/-- Raw 56-byte submission: all 48 pubkey bytes, then amount in big-endian. -/
def submissionPayload (entry : Entry) : Bytes :=
  entry.pubkey.val ++ entry.amount.toBytes

/-- Data of the successful submission's empty-topic LOG0. -/
def submissionLog (entry : Entry) : Bytes :=
  entry.caller.toBytes ++ submissionPayload entry

/-- One 76-byte system return record; no EIP-7685 type byte is included. -/
def outputRecord (entry : Entry) : Bytes :=
  entry.caller.toBytes ++ entry.pubkey.val ++ entry.amount.toBytes.reverse

/-- Ordered concatenation, preserving record boundaries without padding. -/
def outputRecords : List Entry → Bytes
  | [] => []
  | entry :: entries => outputRecord entry ++ outputRecords entries

/-- Serialization of the model's at-most-16 FIFO prefix. -/
def systemOutput (state : State) : Bytes := outputRecords (emitted state)

theorem submissionPayload_length (entry : Entry) : (submissionPayload entry).length = 56 := by
  simp only [submissionPayload, List.length_append, entry.pubkey.property,
    UInt64.length_toBytes]

theorem submissionLog_length (entry : Entry) : (submissionLog entry).length = 76 := by
  simp only [submissionLog, Adr.toBytes, List.length_append, UInt32.length_toBytes,
    B128.length_toBytes, submissionPayload_length]

theorem outputRecord_length (entry : Entry) : (outputRecord entry).length = 76 := by
  simp only [outputRecord, Adr.toBytes, List.length_append, UInt32.length_toBytes,
    B128.length_toBytes, entry.pubkey.property,
    List.length_reverse, UInt64.length_toBytes]

theorem outputRecords_append (left right : List Entry) :
    outputRecords (left ++ right) = outputRecords left ++ outputRecords right := by
  induction left with
  | nil => simp only [List.nil_append, outputRecords]
  | cons entry entries ih =>
    simp only [List.cons_append, outputRecords, ih, List.append_assoc]

theorem outputRecords_length (entries : List Entry) :
    (outputRecords entries).length = 76 * entries.length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [outputRecords, List.length_append, outputRecord_length, ih, List.length_cons]
    omega

theorem systemOutput_length (state : State) :
    (systemOutput state).length = 76 * min maxPerBlock state.queue.length := by
  rw [systemOutput, outputRecords_length, emitted_length]

/-- The full unsigned 64-bit amount is recovered from the submission suffix. -/
theorem submissionPayload_amount (entry : Entry) :
    Bytes.toUInt64 ((submissionPayload entry).drop 48) = entry.amount := by
  rw [submissionPayload, Jaune.List.drop_length_append' entry.pubkey.property.symm,
    UInt64.toUInt64_toBytes]

/-- Reversing exactly the output's final eight bytes recovers the same amount. -/
theorem outputRecord_amount (entry : Entry) :
    Bytes.toUInt64 ((outputRecord entry).drop 68).reverse = entry.amount := by
  have prefixLength : (entry.caller.toBytes ++ entry.pubkey.val).length = 68 := by
    simp only [Adr.toBytes, List.length_append, UInt32.length_toBytes,
      B128.length_toBytes, entry.pubkey.property]
  rw [outputRecord,
    Jaune.List.drop_length_append' prefixLength.symm,
    List.reverse_reverse, UInt64.toUInt64_toBytes]

/-- Caller is the right-aligned integer address in its own storage word. -/
def callerWord (entry : Entry) : B256 := entry.caller.toB256

theorem callerWord_address (entry : Entry) : (callerWord entry).toAdr = entry.caller :=
  toAdr_toB256 entry.caller

/-- The first complete calldata word is the first 32 pubkey bytes. -/
def pubkeyWord (entry : Entry) : B256 := Bytes.toB256 (entry.pubkey.val.take 32)

/-- Exact second CALLDATALOAD image, including its eight zero-padding bytes. -/
def pubkeyAmountBytes (entry : Entry) : Bytes :=
  entry.pubkey.val.drop 32 ++ entry.amount.toBytes ++ List.replicate 8 0

def pubkeyAmountWord (entry : Entry) : B256 := Bytes.toB256 (pubkeyAmountBytes entry)

theorem pubkey_prefix_length (entry : Entry) : (entry.pubkey.val.take 32).length = 32 := by
  rw [List.length_take, entry.pubkey.property]
  rfl

theorem pubkeyAmountBytes_length (entry : Entry) : (pubkeyAmountBytes entry).length = 32 := by
  simp only [pubkeyAmountBytes, List.length_append, List.length_drop,
    entry.pubkey.property, UInt64.length_toBytes, List.length_replicate]

theorem pubkeyWord_bytes (entry : Entry) :
    (pubkeyWord entry).toBytes = entry.pubkey.val.take 32 :=
  Blanc.Bytes.toBytes_toB256_of_length (pubkey_prefix_length entry)

theorem pubkeyAmountWord_bytes (entry : Entry) :
    (pubkeyAmountWord entry).toBytes = pubkeyAmountBytes entry :=
  Blanc.Bytes.toBytes_toB256_of_length (pubkeyAmountBytes_length entry)

/-- The two concrete pubkey pieces preserve all 48 logical bytes. -/
theorem queueWords_pubkey (entry : Entry) :
    (pubkeyWord entry).toBytes ++ (pubkeyAmountWord entry).toBytes.take 16 =
      entry.pubkey.val := by
  have suffixLength : (entry.pubkey.val.drop 32).length = 16 := by
    rw [List.length_drop, entry.pubkey.property]
  rw [pubkeyWord_bytes, pubkeyAmountWord_bytes, pubkeyAmountBytes, List.append_assoc,
    Jaune.List.take_length_append' suffixLength.symm, List.take_append_drop]

/-- Logical Nat address, before any EVM word reduction. -/
def queueBase (index : Nat) : Nat := 4 + 3 * index

/-- Concrete modulo-2^256 storage key; bounds remain a separate obligation. -/
def queueSlot (index offset : Nat) : B256 := (queueBase index + offset).toB256

/-- Explicit finite-word assumptions to be discharged from reachable histories. -/
structure StorageBounds (state : State) : Prop where
  excess_lt : state.excess < 2 ^ 256
  count_lt : state.count < 2 ^ 256
  head_lt : state.head < 2 ^ 256
  tail_lt : state.tail < 2 ^ 256
  liveSlot_lt : ∀ i, i < state.queue.length → queueBase (state.head + i) + 2 < 2 ^ 256

/-- Only metadata and live queue words are constrained. Removed or otherwise
stale queue slots may contain arbitrary values; a drained queue need not have
zeroed words. This is a representation predicate, not a reachability theorem. -/
structure RepresentsStorage (storage : B256 → B256) (state : State) : Prop where
  coherent : Coherent state
  bounds : StorageBounds state
  excess : storage 0 = state.excess.toB256
  count : storage 1 = state.count.toB256
  head : storage 2 = state.head.toB256
  tail : storage 3 = state.tail.toB256
  live : ∀ i (hi : i < state.queue.length),
    storage (queueSlot (state.head + i) 0) = callerWord state.queue[i] ∧
    storage (queueSlot (state.head + i) 1) = pubkeyWord state.queue[i] ∧
    storage (queueSlot (state.head + i) 2) = pubkeyAmountWord state.queue[i]

end Blanc.WithdrawalRequest
