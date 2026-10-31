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
  rw [BLT.toBytes_eq_toBytesS]; decide +kernel

/-- Kernel-checked Keccak of the exact C transaction's EIP-155 payload. -/
theorem c22_signingHash :
    c22Tx.signingHash =
      some (0x8f58d4b5f41a1e83a7606bbb4f35fba4442c9a26c0473c77ee897355fe5c571d : B256) := by
  rw [c22_signingEncoded]
  decide +kernel

end Blanc.Lift.Usdc.HistoryAnchorBody
