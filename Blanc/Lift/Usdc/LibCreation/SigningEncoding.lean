import Blanc.Lift.Usdc.LibCreation.Cert
import Blanc.RlpConcrete

/-! Unadopted original library deployment signing envelope. Exact field
correspondence to the original historical transaction remains separate. -/
namespace Blanc.Lift.Usdc.LibCreation
open Jaune

def signingPayload : Bytes :=
  [0xf9, 0x7, 0x6, 0x80, 0x85, 0x5, 0x1f, 0x4d, 0x5c, 0x0, 0x83, 0xe4, 0xe1, 0xc0, 0x80, 0x80, 0xb9, 0x6, 0xf3] ++
    code.toList ++ [0x01, 0x80, 0x80]

theorem code_toList_length : code.toList.length = 1779 := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem signingEncoded {tx : Tx}
    (htype : tx.type = .zero 22000000000 none)
    (hnonce : tx.nonce = 0) (hgas : tx.gas = 15000000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37) :
    tx.signingHash = some signingPayload.keccak := by
  have fields : tx.signingHash = some (BLT.list
      [.bytes [], .bytes [0x05, 0x1f, 0x4d, 0x5c, 0x00],
        .bytes [0xe4, 0xe1, 0xc0], .bytes [], .bytes [], .bytes code.toList,
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
      [0xb9, 0x06, 0xf3] ++ code.toList := by
    rw [RlpConcrete.encode_bytes_many _ (by rw [code_toList_length]; omega),
      code_toList_length]
    norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
      Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq,
      UInt8.reduceOfNat, UInt8.reduceAdd, ↓reduceIte, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append]
  have joined : BLTs.toBytesJoin
      [.bytes [], .bytes [0x05, 0x1f, 0x4d, 0x5c, 0x00],
        .bytes [0xe4, 0xe1, 0xc0], .bytes [], .bytes [], .bytes code.toList,
        .bytes [1], .bytes [], .bytes []] =
      [0x80, 0x85, 0x05, 0x1f, 0x4d, 0x5c, 0x00,
        0x83, 0xe4, 0xe1, 0xc0, 0x80, 0x80, 0xb9, 0x06, 0xf3] ++
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

end Blanc.Lift.Usdc.LibCreation
