import Blanc.RlpListEncode
import Blanc.RlpRoundTrip
import Blanc.Lift.Weth9.Creation.SigningRecover

/-! The WETH9 signed creation transaction (block 4,719,568, slot 85): its fields, its exact signed
bytes and their canonical re-encoding and strict decode. The slot binding against the block hash
is `WethHashAnchor.observation`. -/
namespace Blanc.Lift.Weth9.Creation.SignedInput
open Jaune

def rBytes : Bytes :=
  (0x7ce08af79f7a6c1b8b336f50890a80602c4dcd1e3cc5ca131373f0e8ff15e278 : B256).toBytes
def sBytes : Bytes :=
  (0x45e183d91f1e8f31e32d333cf6090990c9bf7d35dd00472cfd2d3a63ca8b1a5 : B256).toBytes

def tx : Tx := {
  nonce := 446, gas := 1500000, value := 0, data := code.toList,
  v := 37, r := rBytes, s := sBytes, type := .zero 21000000000 none }

def fields : List BLT :=
  [.bytes [0x01, 0xbe], .bytes [0x04, 0xe3, 0xb2, 0x92, 0x00], .bytes [0x16, 0xe3, 0x60],
   .bytes [], .bytes [], .bytes code.toList, .bytes [0x25], .bytes rBytes, .bytes sBytes]

/-- The exact signed envelope: a closed header, the creation input, and the closed signature
tail. -/
def signedBytes : Bytes :=
  [0xf9, 0x0e, 0x05, 0x82, 0x01, 0xbe, 0x85, 0x04, 0xe3, 0xb2, 0x92, 0x00,
    0x83, 0x16, 0xe3, 0x60, 0x80, 0x80, 0xb9, 0x0d, 0xb0] ++
    code.toList ++ ([0x25, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes)

theorem tx_blt : tx.toBLT = .list fields := by
  dsimp only [tx, fields, Tx.toBLT]
  congr <;> decide +kernel

/-- Canonical re-encoding preserves the complete signed envelope. -/
theorem canonical : tx.toBLT.toBytes = signedBytes := by
  rw [tx_blt]
  exact RlpConcrete.encode_list_at 5 rfl code_toList_length (by decide) (by decide +kernel)
    (by decide +kernel)

theorem envelope_parse : signedBytes.toBLT? = some (.list fields) :=
  RlpConcrete.toBLT?_of_encoded (tx_blt ▸ canonical)
    (by rw [signedBytes, List.length_append, List.length_append, code_toList_length]
        decide +kernel)

/-- Full signed bytes pass the actual strict legacy decoder. -/
theorem signed_decode :
    signedBytes.toBLT?.bind (fun blt => blt.toExTx.toOption) = some tx := by
  rw [envelope_parse]
  rfl

theorem transaction_hash_bytes : getTxHash tx = signedBytes.keccak := by
  unfold getTxHash
  rw [canonical]

end Blanc.Lift.Weth9.Creation.SignedInput
