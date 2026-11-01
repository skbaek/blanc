import Blanc.Lift.Usdc.ImplV2_2Creation.Bindings
import Blanc.RlpListEncode

/-! Signing envelope of the unadopted V2.2 creation preview, conditional on explicit fields. -/
namespace Blanc.Lift.Usdc.ImplV2_2Creation

open Jaune

theorem code_toList_length : code.toList.length = 23567 := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

def signingPayload : Bytes :=
  [0xf9, 0x5c, 0x22, 0x01, 0x85, 0x05, 0x1f, 0x4d, 0x5c, 0x00,
    0x83, 0xe4, 0xe1, 0xc0, 0x80, 0x80, 0xb9, 0x5c, 0x0f] ++
    code.toList ++ [0x01, 0x80, 0x80]

/-- Exact signing encoding from fields; no original body-slot identity is asserted. -/
theorem signingEncoded {tx : Tx}
    (htype : tx.type = .zero 22000000000 none)
    (hnonce : tx.nonce = 1) (hgas : tx.gas = 15000000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37) :
    tx.signingHash = some signingPayload.keccak := by
  have fields : tx.signingHash = some (BLT.list
      [.bytes [0x01], .bytes [0x05, 0x1f, 0x4d, 0x5c, 0x00],
        .bytes [0xe4, 0xe1, 0xc0], .bytes [], .bytes [], .bytes code.toList,
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

end Blanc.Lift.Usdc.ImplV2_2Creation
