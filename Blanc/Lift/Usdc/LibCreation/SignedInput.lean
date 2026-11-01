import Blanc.RlpListEncode
import Blanc.RlpRoundTrip
import Blanc.Lift.Usdc.LibCreation.SigningHash

/-! Strict decoding of the unadopted library signed creation envelope. -/
namespace Blanc.Lift.Usdc.LibCreation.SignedInput
open Jaune

def rBytes : Bytes :=
  (0x8d0be5d57375e2f8fac9bf0acabf15f777eca08c3f29869fafd1b8f960022ac6 : B256).toBytes
def sBytes : Bytes :=
  (0x40399d6b9e8c42bad4bf10d25d15cf3c702b6cf23237ef03a26157fbc1a76b09 : B256).toBytes

def tx : Tx := {
  nonce := 0, gas := 15000000, value := 0, data := code.toList,
  v := 37, r := rBytes, s := sBytes, type := .zero 22000000000 none }

def fields : List BLT :=
  [.bytes [], .bytes [0x05, 0x1f, 0x4d, 0x5c, 0x00], .bytes [0xe4, 0xe1, 0xc0],
   .bytes [], .bytes [], .bytes code.toList, .bytes [0x25], .bytes rBytes, .bytes sBytes]

/-- The exact signed envelope: a closed header, the creation input, and the closed signature
tail. -/
def signedBytes : Bytes :=
  [0xf9, 0x07, 0x46, 0x80, 0x85, 0x05, 0x1f, 0x4d, 0x5c, 0x00, 0x83, 0xe4,
    0xe1, 0xc0, 0x80, 0x80, 0xb9, 0x06, 0xf3] ++
    code.toList ++ ([0x25, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes)

theorem strict_legacy_decode : BLT.toExLegacyTx fields = .ok tx := by
  rfl

/-- The slot is certified by the strict legacy decoder, not a typed-slot bypass. -/
def envelope : TxEnvelope := TxEnvelope.ofLegacyDecode strict_legacy_decode

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

theorem signing_hash : tx.signingHash =
    some 0x0b923c20ae300a3a20431bf4781920c212aa03d3894190c1bde5a93411bc8abd := by
  exact signingHash rfl rfl rfl rfl rfl rfl

theorem recovered : recoverSender 1 tx = .ok originalCreator := by
  exact recoveredSender rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel)

end Blanc.Lift.Usdc.LibCreation.SignedInput
