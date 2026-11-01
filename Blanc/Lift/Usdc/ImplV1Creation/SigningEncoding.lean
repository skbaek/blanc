import Blanc.Lift.Usdc.ImplV1Creation.Bindings
import Blanc.RlpListEncode

/-! Signing envelope of the unadopted V1 creation preview, conditional on explicit fields. -/
namespace Blanc.Lift.Usdc.ImplV1Creation

open Jaune

theorem code_toList_length : code.toList.length = 12270 := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

def signingPayload : Bytes :=
  [0xf9, 0x30, 0x00, 0x12, 0x84, 0xee, 0x6b, 0x28, 0x00,
    0x83, 0x66, 0x91, 0xb7, 0x80, 0x80, 0xb9, 0x2f, 0xee] ++
    code.toList ++ [0x01, 0x80, 0x80]

/-- Exact signing encoding from fields; no original body-slot identity is asserted. -/
theorem signingEncoded {tx : Tx}
    (htype : tx.type = .zero 4000000000 none)
    (hnonce : tx.nonce = 18) (hgas : tx.gas = 6721975)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 38) :
    tx.signingHash = some signingPayload.keccak := by
  have fields : tx.signingHash = some (BLT.list
      [.bytes [0x12], .bytes [0xee, 0x6b, 0x28, 0x00],
        .bytes [0x66, 0x91, 0xb7], .bytes [], .bytes [], .bytes code.toList,
        .bytes [1], .bytes [], .bytes []]).toBytes.keccak := by
    norm_num only [Tx.signingHash, htype, hnonce, hgas, hvalue, hdata, hv,
      Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true,
      Bool.or_self, ↓reduceIte]
    rfl
  rw [fields]
  exact congrArg (fun b => some (Bytes.keccak b))
    (RlpConcrete.encode_list_at 5 rfl code_toList_length (by decide) (by decide +kernel)
      (by decide +kernel))

end Blanc.Lift.Usdc.ImplV1Creation
