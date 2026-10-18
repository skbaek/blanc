import Blanc.Composition.Curve3Pool3CrvTxData
import Blanc.RlpConcrete

/-!
The exchange transaction's signing payload.  Its 132-byte calldata is kept abstract while the RLP
encoder is rewritten; the calldata's length and its string header are computed separately.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The type-2 signing payload `0x02 ‖ rlp(unsigned fields)`, around the calldata. -/
def exchangeSigningPayload : Bytes :=
  [0x02, 0xf8, 0xa5, 0x01, 0x80, 0x01, 0x08, 0x83, 0x0d, 0xbb, 0xa0, 0x94, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,
    0x80, 0xb8, 0x84] ++ exchangeData ++ [0xc0]

theorem exchangeData_length : exchangeData.length = 132 := by decide +kernel

theorem exchangeData_encoded : (BLT.bytes exchangeData).toBytes = [0xb8, 0x84] ++ exchangeData := by
  rw [RlpConcrete.encode_bytes_many _ (by rw [exchangeData_length]; decide), exchangeData_length]
  have hp : Nat.toBytesPack 132 = [0x84] := by
    simp only [Nat.toBytesPack, Nat.toBytes, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toBytes.aux,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  simp only [show ¬ (132 < 56) from by decide, ite_false, hp]
  rfl

theorem exchange_signingEncoded :
    signedExchangeTx.signingHash = some exchangeSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have h0 : Nat.toBytes 0 = [] := by decide +kernel
  have hn : (UInt64.toBytes 0).sig = [] := by decide +kernel
  have h1 : Nat.toBytes 1 = [1] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, zero_add,
      Nat.one_mod, Nat.toUInt8_eq, UInt8.ofNat_one, Nat.reduceDiv]
  have h8 : Nat.toBytes 8 = [8] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  have hg : Nat.toBytes 900000 = [0x0d, 0xbb, 0xa0] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  have hto : ((some poolAddr <&> Adr.toBytes).getD []) =
      [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x01, 0x00] := by decide +kernel
  have hp : Nat.toBytesPack 165 = [0xa5] := by
    simp only [Nat.toBytesPack, Nat.toBytes, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toBytes.aux,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  simp only [Tx.signingHash, signedExchangeTx, exchangeTx, hc, hn, h0, h1, h8, hg, hto,
    AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  rw [BLT.toBytes, BLTs.toBytes]
  simp only [BLTs.toBytesJoin, exchangeData_encoded, BLT.toBytes, BLTs.toBytes, UInt8.reduceLT,
    ↓reduceIte, List.length_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, add_zero,
    List.length_cons, List.length_append, exchangeData_length, zero_add, Nat.reduceAdd,
    Nat.reduceLT, UInt8.reduceAdd, List.cons_append, List.nil_append, List.append_nil, hp,
    exchangeSigningPayload]

end Blanc.Composition.Curve3Pool3CrvInstance
