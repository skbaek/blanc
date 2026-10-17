import Blanc.Composition.UniswapV2PairWeth9SigningData
import Blanc.RlpConcrete

/-!
`tx2`'s signing payload.  Its 164-byte calldata is kept abstract while the RLP encoder is
rewritten (a literal of the whole 200-byte payload is too deep for `simp`); the calldata's length
and its string header are computed separately.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift

/-- `tx2`'s type-2 signing payload `0x02 ‖ rlp(unsigned fields)`, around its calldata. -/
def tx2SigningPayload : Bytes :=
  [0x02, 0xf8, 0xc5, 0x01, 0x01, 0x01, 0x08, 0x83, 0x04, 0x93, 0xe0, 0x94, 0x22, 0x22, 0x22, 0x22,
    0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
    0x80, 0xb8, 0xa4] ++ tx2Data ++ [0xc0]

theorem tx2Data_length : tx2Data.length = 164 := by decide +kernel

theorem tx2Data_encoded : (BLT.bytes tx2Data).toBytes = [0xb8, 0xa4] ++ tx2Data := by
  rw [RlpConcrete.encode_bytes_many _ (by rw [tx2Data_length]; decide), tx2Data_length]
  have hp : Nat.toBytesPack 164 = [0xa4] := by
    simp only [Nat.toBytesPack, Nat.toBytes, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toBytes.aux,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  simp only [show ¬ (164 < 56) from by decide, ite_false, hp]
  rfl

theorem tx2_signingEncoded :
    signedTx2.signingHash = some tx2SigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have h0 : Nat.toBytes 0 = [] := by decide +kernel
  have h1 : Nat.toBytes 1 = [1] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, zero_add,
      Nat.one_mod, Nat.toUInt8_eq, UInt8.ofNat_one, Nat.reduceDiv]
  have h8 : Nat.toBytes 8 = [8] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  have hg : Nat.toBytes 300000 = [0x04, 0x93, 0xe0] := by
    simp only [Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  have hto : ((some pair <&> Adr.toBytes).getD []) =
      [0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
        0x22, 0x22, 0x22, 0x22, 0x22] := by decide +kernel
  have hp : Nat.toBytesPack 197 = [0xc5] := by
    simp only [Nat.toBytesPack, Nat.toBytes, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toBytes.aux,
      Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv]
  simp only [Tx.signingHash, signedTx2, tx2, hc, h0, h1, h8, hg, hto,
    AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  rw [BLT.toBytes, BLTs.toBytes]
  simp only [BLTs.toBytesJoin, tx2Data_encoded, BLT.toBytes, BLTs.toBytes, UInt8.reduceLT,
    ↓reduceIte, List.length_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, add_zero,
    List.length_cons, List.length_append, tx2Data_length, zero_add, Nat.reduceAdd, Nat.reduceLT,
    UInt8.reduceAdd, List.cons_append, List.nil_append, List.append_nil, hp,
    tx2SigningPayload]

end Blanc.Composition.UniswapV2PairWeth9Instance
