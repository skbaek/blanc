import Jaune.Transaction
import Blanc.RlpConcrete

/-! Structural equations for concrete RLP proofs over Jaune's actual codec. -/

namespace Blanc.RlpConcrete

open Jaune

private theorem bytes_of_singleton_rlp (bs : Bytes) (b : UInt8)
    (small : b < 0x80) (encoded : (BLT.bytes bs).toBytes = [b]) : bs = [b] := by
  cases bs with
  | nil =>
      rw [BLT.toBytes] at encoded <;>
        try simp only [reduceCtorEq, imp_self, implies_true]
      change [0x80] = [b] at encoded
      have same := (List.cons.inj encoded).1
      rw [← same] at small
      exact False.elim ((by decide : ¬ (0x80 : UInt8) < 0x80) small)
  | cons a rest =>
      cases rest with
      | nil =>
          rw [BLT.toBytes] at encoded
          split at encoded
          · exact encoded
          · have lengths := congrArg List.length encoded
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at lengths
            omega
      | cons c rest =>
          rw [BLT.toBytes] at encoded <;>
            try simp only [List.cons.injEq, reduceCtorEq, and_false, imp_self, implies_true]
          have lengths := congrArg List.length encoded
          split at lengths <;>
            simp only [List.length_cons, List.length_nil, List.length_append] at lengths <;> omega

/-- A positive transaction index below 128 is its one-byte RLP atom. -/
theorem receipt_key_small (index : Nat) (positive : 0 < index) (small : index < 128) :
    (BLT.bytes index.toBytes).toBytes = [index.toUInt8] := by
  have byteSmall : index.toUInt8 < 0x80 := by
    change index.toUInt8.toNat < 128
    simpa only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow,
      Nat.mod_eq_of_lt (by omega : index < 256)] using small
  cases index with
  | zero => omega
  | succ n =>
      unfold Nat.toBytes
      rw [Nat.toBytes.aux]
      rw [Nat.div_eq_of_lt (by omega : n + 1 < 256),
        Nat.mod_eq_of_lt (by omega : n + 1 < 256), Nat.toBytes.aux]
      rw [BLT.toBytes, ite_eq_left byteSmall]

/-- No other natural index has the RLP receipt key of a positive index below
128. The other index is unbounded; no general codec injectivity is assumed. -/
theorem receipt_key_ne_of_small {index other : Nat}
    (positive : 0 < index) (small : index < 128) (different : other ≠ index) :
    (BLT.bytes other.toBytes).toBytes ≠ (BLT.bytes index.toBytes).toBytes := by
  intro same
  rw [receipt_key_small index positive small] at same
  have byteSmall : index.toUInt8 < 0x80 := by
    change index.toUInt8.toNat < 128
    simpa only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow,
      Nat.mod_eq_of_lt (by omega : index < 256)] using small
  have bytes := bytes_of_singleton_rlp other.toBytes index.toUInt8 byteSmall same
  have number := congrArg Bytes.toNat bytes
  rw [nat_bytes_roundtrip] at number
  simp only [Bytes.toNat, Bytes.toNat.aux, Nat.zero_mul, Nat.zero_add,
    Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow,
    Nat.mod_eq_of_lt (by omega : index < 256)] at number
  exact different number

end Blanc.RlpConcrete
