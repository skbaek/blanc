import Blanc.Lift.Usdc.ImplV2_1Creation.Bindings
import Blanc.RlpListEncode

/-! Signing envelope of the unadopted V2.1 creation preview, conditional on explicit fields. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation

open Jaune

theorem code_toList_length : code.toList.length = 21586 := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

def signingPayload : Bytes :=
  [0xf9, 0x54, 0x62, 0x26, 0x85, 0x1e, 0x44, 0x9a, 0x94, 0x00,
    0x83, 0x53, 0xec, 0x60, 0x80, 0x80, 0xb9, 0x54, 0x52] ++ code.toList

/-- Exact signing encoding from fields; no original body-slot identity is asserted. -/
theorem signingEncoded {tx : Tx}
    (htype : tx.type = .zero 130000000000 none)
    (hnonce : tx.nonce = 38) (hgas : tx.gas = 5500000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 28) :
    tx.signingHash = some signingPayload.keccak := by
  have fields : tx.signingHash = some (BLT.list
      [.bytes [0x26], .bytes [0x1e, 0x44, 0x9a, 0x94, 0x00],
        .bytes [0x53, 0xec, 0x60], .bytes [], .bytes [], .bytes code.toList]).toBytes.keccak := by
    norm_num only [Tx.signingHash, htype, hnonce, hgas, hvalue, hdata, hv,
      Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd,
      Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true,
      Bool.or_self, ↓reduceIte]
    rfl
  rw [fields]
  exact congrArg (fun b => some (Bytes.keccak b))
    (RlpConcrete.encode_list_at_last 5 rfl rfl code_toList_length (by decide)
      (by decide +kernel))

end Blanc.Lift.Usdc.ImplV2_1Creation
