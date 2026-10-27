import Blanc.Basic
import Jaune.Execution
import Std.Tactic.BVDecide

/-! Address membership in Jaune's log bloom has no false negatives. The
three positions use the actual Keccak digest; no hash injectivity is needed. -/

namespace Blanc.LogBloom

open Jaune

/-- Jaune's reversed index in the 2048-bit bloom. -/
def bitIndex (hash : Bytes) (index : Nat) : UInt16 :=
  0x07FF - ((UInt16.ofBytes (hash.getD index 0) (hash.getD (index + 1) 0)) &&& 0x07FF)

/-- Byte containing one required bloom bit. -/
def byteIndex (hash : Bytes) (index : Nat) : Nat :=
  (bitIndex hash index / 8).toNat

/-- Required bit within that byte. -/
def bitMask (hash : Bytes) (index : Nat) : UInt8 :=
  0x01 <<< (0x07 - ((bitIndex hash index).lows &&& 0x07))

/-- One of the bits required by the entry digest is present. -/
def HasIndex (bloom hash : Bytes) (index : Nat) : Prop :=
  bloom.getD (byteIndex hash index) 0 &&& bitMask hash index = bitMask hash index

/-- All three address bits required by the real Keccak digest are present. -/
def ContainsAddress (bloom : Bytes) (address : Adr) : Prop :=
  let hash := (Bytes.keccak address.toBytes).toBytes
  HasIndex bloom hash 0 ∧ HasIndex bloom hash 2 ∧ HasIndex bloom hash 4

private def Preserves (before after : Bytes) : Prop :=
  ∀ i mask, before.getD i 0 &&& mask = mask → after.getD i 0 &&& mask = mask

private theorem byteIndex_lt (hash : Bytes) (index : Nat) :
    byteIndex hash index < 256 := by
  have bound : bitIndex hash index < 2048 := by
    unfold bitIndex
    generalize UInt16.ofBytes (hash.getD index 0) (hash.getD (index + 1) 0) = x
    bv_decide
  change (bitIndex hash index / 8).toNat < 256
  rw [UInt16.toNat_div]
  change (bitIndex hash index).toNat / 8 < 256
  change (bitIndex hash index).toNat < 2048 at bound
  omega

private theorem addIndex_length (bloom hash : Bytes) (index : Nat) :
    (addIndexToBloom hash index bloom).length = bloom.length := by
  simp only [addIndexToBloom, List.length_set]

private theorem addIndex_preserves (bloom hash : Bytes) (index : Nat) :
    Preserves bloom (addIndexToBloom hash index bloom) := by
  intro i mask present
  change (bloom.set (byteIndex hash index)
    (bloom.getD (byteIndex hash index) 0 ||| bitMask hash index)).getD i 0 &&& mask = mask
  by_cases same : byteIndex hash index = i
  · subst i
    by_cases bound : byteIndex hash index < bloom.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_self bound]
      change (bloom.getD (byteIndex hash index) 0 ||| bitMask hash index) &&& mask = mask
      generalize bloom.getD (byteIndex hash index) 0 = x at *
      generalize bitMask hash index = y
      bv_decide
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set,
        ↓reduceIte, bound, Option.getD_none]
      simpa only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (Nat.le_of_not_lt bound), Option.getD_none] using present
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_set_ne same] using present

private theorem addIndex_has (bloom hash : Bytes) (index : Nat)
    (size : bloom.length = 256) :
    HasIndex (addIndexToBloom hash index bloom) hash index := by
  have bound : byteIndex hash index < bloom.length := by rw [size]; exact byteIndex_lt hash index
  change (bloom.set (byteIndex hash index)
    (bloom.getD (byteIndex hash index) 0 ||| bitMask hash index)).getD
      (byteIndex hash index) 0 &&& bitMask hash index = bitMask hash index
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self bound]
  change (bloom.getD (byteIndex hash index) 0 ||| bitMask hash index) &&& bitMask hash index = bitMask hash index
  generalize bloom.getD (byteIndex hash index) 0 = x
  generalize bitMask hash index = y
  bv_decide

private theorem preserves_trans {a b c : Bytes}
    (ab : Preserves a b) (bc : Preserves b c) : Preserves a c :=
  fun i mask h => bc i mask (ab i mask h)

private theorem addEntry_length (bloom entry : Bytes) :
    (addEntryToBloom bloom entry).length = bloom.length := by
  simp only [addEntryToBloom, addIndex_length]

private theorem addEntry_preserves (bloom entry : Bytes) :
    Preserves bloom (addEntryToBloom bloom entry) :=
  preserves_trans (addIndex_preserves bloom _ 0)
    (preserves_trans (addIndex_preserves _ _ 2) (addIndex_preserves _ _ 4))

private theorem fold_length {α : Type} (f : Bytes → α → Bytes)
    (length : ∀ bloom item, (f bloom item).length = bloom.length)
    (items : List α) (bloom : Bytes) :
    (items.foldl f bloom).length = bloom.length := by
  induction items generalizing bloom with
  | nil => rfl
  | cons item rest ih => exact (ih _).trans (length bloom item)

private theorem fold_preserves {α : Type} (f : Bytes → α → Bytes)
    (preserves : ∀ bloom item, Preserves bloom (f bloom item))
    (items : List α) (bloom : Bytes) :
    Preserves bloom (items.foldl f bloom) := by
  induction items generalizing bloom with
  | nil => exact fun _ _ h => h
  | cons item rest ih => exact preserves_trans (preserves bloom item) (ih _)

private theorem addLog_length (bloom : Bytes) (log : Log) :
    (addLogToBloom bloom log).length = bloom.length :=
  (fold_length addEntryToBloom addEntry_length _ _).trans (addEntry_length ..)

private theorem addLog_preserves (bloom : Bytes) (log : Log) :
    Preserves bloom (addLogToBloom bloom log) :=
  preserves_trans (addEntry_preserves bloom log.address.toBytes)
    (fold_preserves addEntryToBloom addEntry_preserves _ _)

private theorem containsAddress_of_preserves {before after : Bytes} {address : Adr}
    (preserves : Preserves before after)
    (present : ContainsAddress before address) : ContainsAddress after address :=
  ⟨preserves _ _ present.1, preserves _ _ present.2.1, preserves _ _ present.2.2⟩

private theorem addLog_containsAddress (bloom : Bytes) (log : Log)
    (size : bloom.length = 256) :
    ContainsAddress (addLogToBloom bloom log) log.address := by
  apply containsAddress_of_preserves
    (fold_preserves addEntryToBloom addEntry_preserves _ _)
  let hash := (Bytes.keccak log.address.toBytes).toBytes
  have size0 : (addIndexToBloom hash 0 bloom).length = 256 :=
    (addIndex_length ..).trans size
  have size2 : (addIndexToBloom hash 2 (addIndexToBloom hash 0 bloom)).length = 256 :=
    (addIndex_length ..).trans size0
  exact ⟨addIndex_preserves _ hash 4 _ _
      (addIndex_preserves _ hash 2 _ _ (addIndex_has bloom hash 0 size)),
    addIndex_preserves _ hash 4 _ _ (addIndex_has _ hash 2 size0),
    addIndex_has _ hash 4 size2⟩

private theorem fold_containsAddress (logs : List Log) (bloom : Bytes)
    (size : bloom.length = 256) {log : Log} (member : log ∈ logs) :
    ContainsAddress (logs.foldl addLogToBloom bloom) log.address := by
  induction logs generalizing bloom with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst head
        exact containsAddress_of_preserves
          (fold_preserves addLogToBloom addLog_preserves tail (addLogToBloom bloom log))
          (addLog_containsAddress bloom log size)
      · exact ih _ ((addLog_length ..).trans size) later

/-- Every address that actually emits a log has all three required bloom bits. -/
theorem containsAddress_of_mem {logs : List Log} {log : Log}
    (member : log ∈ logs) : ContainsAddress (logsBloom logs) log.address :=
  fold_containsAddress logs _ (List.length_replicate ..) member

/-- A missing address bit excludes every log from that address. -/
theorem address_ne_of_missing {logs : List Log} {log : Log} {address : Adr}
    (missing : ¬ ContainsAddress (logsBloom logs) address)
    (member : log ∈ logs) : log.address ≠ address := by
  intro same
  exact missing (same ▸ containsAddress_of_mem member)

end Blanc.LogBloom
