import Blanc.Lift.Weth9.DeployBlockHistory
import Blanc.RlpListEncode

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
  exact congrArg (fun b => some (Bytes.keccak b))
    (RlpConcrete.encode_list_at 5 rfl code_toList_length (by decide) (by decide +kernel)
      (by decide +kernel))

end Blanc.Lift.Weth9.Creation
