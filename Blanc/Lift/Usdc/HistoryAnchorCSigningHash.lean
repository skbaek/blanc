import Blanc.Lift.Usdc.HistoryAnchorBodyGeneratedC02

/-!
# Exact C transaction signing payload

These facts concern the existing strictly decoded `c22Tx`, with its unchanged
creation input. They assert neither historical body identity nor execution.
-/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

/-- The EIP-155 signing envelope of the frozen C transaction. -/
def c22SigningPayload : Bytes :=
  [0xf9, 0x0b, 0x5b, 0x14, 0x84, 0xee, 0x6b, 0x28, 0x00,
    0x83, 0x66, 0x91, 0xb7, 0x80, 0x80, 0xb9, 0x0b, 0x49] ++
    c22F5 ++ [0x01, 0x80, 0x80]

theorem c22_signingEncoded :
    c22Tx.signingHash = some c22SigningPayload.keccak := by
  have fields : c22Tx.signingHash = some (BLT.list
      [.bytes c22F0, .bytes c22F1, .bytes c22F2, .bytes c22F3,
        .bytes c22F4, .bytes c22F5, .bytes [1], .bytes [], .bytes []]).toBytes.keccak := by
    norm_num only [Tx.signingHash, c22Tx, c22F0, c22F1, c22F2, c22F3, c22F4,
      Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true,
      Bool.or_self, ↓reduceIte]
    rfl
  rw [fields]
  apply congrArg some
  apply congrArg Bytes.keccak
  have joined : BLTs.toBytesJoin
      [.bytes c22F0, .bytes c22F1, .bytes c22F2, .bytes c22F3,
        .bytes c22F4, .bytes c22F5, .bytes [1], .bytes [], .bytes []] =
      [0x14, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x66, 0x91, 0xb7,
        0x80, 0x80, 0xb9, 0x0b, 0x49] ++ c22F5 ++ [0x01, 0x80, 0x80] := by
    simp only [BLTs.toBytesJoin, c22_encode5, BLT.toBytes,
      c22F0, c22F1, c22F2, c22F3, c22F4, List.length_cons, List.length_nil,
      Nat.reduceLT, UInt8.reduceLT, ↓reduceIte, List.cons_append, List.nil_append,
      List.append_nil]
    rfl
  rw [BLT.toBytes, BLTs.toBytes, joined]
  have len : c22F5.length = 2889 := by decide +kernel
  norm_num only [List.length_append, List.length_cons, List.length_nil, len,
    Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
    Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq,
    UInt8.reduceOfNat, UInt8.reduceAdd, ↓reduceIte, List.cons_append,
    List.nil_append, c22SigningPayload]

/-- Kernel-checked Keccak of the exact C transaction's EIP-155 payload. -/
theorem c22_signingHash :
    c22Tx.signingHash =
      some (0x8f58d4b5f41a1e83a7606bbb4f35fba4442c9a26c0473c77ee897355fe5c571d : B256) := by
  rw [c22_signingEncoded]
  decide +kernel

end Blanc.Lift.Usdc.HistoryAnchorBody
