import Blanc.Lift.Weth9.DeployBlockHistory
import Blanc.RlpConcrete

/-!
# WETH creation signing envelope from explicit transaction fields

These are codec facts conditional on the supplied transaction's fields. They
do not identify an original mainnet transaction or adopt RPC observations.
-/

namespace Blanc.Lift.Weth9.Creation

open Jaune

def signingPayload : Bytes :=
  [0xf9, 0x0d, 0xc5, 0x82, 0x01, 0xbe, 0x85, 0x04, 0xe3, 0xb2, 0x92, 0x00,
    0x83, 0x16, 0xe3, 0x60, 0x80, 0x80, 0xb9, 0x0d, 0xb0] ++
    code.toList ++ [0x01, 0x80, 0x80]

theorem signingEncoded {tx : Tx}
    (htype : tx.type = .zero 21000000000 none)
    (hnonce : tx.nonce = 446) (hgas : tx.gas = 1500000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37) :
    tx.signingHash = some signingPayload.keccak := by
  have fields : tx.signingHash = some (BLT.list
      [.bytes [0x01, 0xbe], .bytes [0x04, 0xe3, 0xb2, 0x92, 0x00],
        .bytes [0x16, 0xe3, 0x60], .bytes [], .bytes [], .bytes code.toList,
        .bytes [1], .bytes [], .bytes []]).toBytes.keccak := by
    norm_num only [Tx.signingHash, htype, hnonce, hgas, hvalue, hdata, hv,
      Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true,
      Bool.or_self, ↓reduceIte]
    rfl
  rw [fields]
  apply congrArg some
  apply congrArg Bytes.keccak
  have inputEncoded : (BLT.bytes code.toList).toBytes =
      [0xb9, 0x0d, 0xb0] ++ code.toList := by
    rw [RlpConcrete.encode_bytes_many _ (by rw [code_toList_length]; omega),
      code_toList_length]
    norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
      Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq,
      UInt8.reduceOfNat, UInt8.reduceAdd, ↓reduceIte, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append]
  have joined : BLTs.toBytesJoin
      [.bytes [0x01, 0xbe], .bytes [0x04, 0xe3, 0xb2, 0x92, 0x00],
        .bytes [0x16, 0xe3, 0x60], .bytes [], .bytes [], .bytes code.toList,
        .bytes [1], .bytes [], .bytes []] =
      [0x82, 0x01, 0xbe, 0x85, 0x04, 0xe3, 0xb2, 0x92, 0x00,
        0x83, 0x16, 0xe3, 0x60, 0x80, 0x80, 0xb9, 0x0d, 0xb0] ++
        code.toList ++ [0x01, 0x80, 0x80] := by
    simp only [BLTs.toBytesJoin, inputEncoded, BLT.toBytes,
      List.length_cons, List.length_nil, Nat.reduceLT, UInt8.reduceLT, ↓reduceIte,
      List.cons_append, List.nil_append, List.append_nil]
    rfl
  rw [BLT.toBytes, BLTs.toBytes, joined]
  norm_num only [List.length_append, List.length_cons, List.length_nil, code_toList_length,
    Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
    Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq,
    UInt8.reduceOfNat, UInt8.reduceAdd, ↓reduceIte, List.cons_append,
    List.nil_append, signingPayload]

end Blanc.Lift.Weth9.Creation
