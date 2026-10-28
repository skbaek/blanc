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

def payload : Bytes :=
  [0x80, 0x85, 0x05, 0x1f, 0x4d, 0x5c, 0x00, 0x83, 0xe4, 0xe1, 0xc0,
    0x80, 0x80, 0xb9, 0x06, 0xf3] ++ code.toList ++
    [0x25, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes

def signedBytes : Bytes := [0xf9, 0x07, 0x46] ++ payload

theorem strict_legacy_decode : BLT.toExLegacyTx fields = .ok tx := by
  rfl

/-- The slot is certified by the strict legacy decoder, not a typed-slot bypass. -/
def envelope : TxEnvelope := TxEnvelope.ofLegacyDecode strict_legacy_decode

theorem payload_length : payload.length = 1862 := by
  simp only [payload, List.length_append, List.length_cons, List.length_nil,
    code_toList_length, rBytes, sBytes, B256.length_toBytes, Nat.reduceAdd]

theorem payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) payload = some fields := by
  have hlen : Bytes.toNat [0x06, 0xf3] = code.toList.length := by
    rw [code_toList_length]
    decide +kernel
  have hr : rBytes.length = 32 := by decide +kernel
  have hs : sBytes.length = 32 := by decide +kernel
  unfold payload fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 [0x05, 0x1f, 0x4d, 0x5c, 0x00] _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [0xe4, 0xe1, 0xc0] _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_two _ _ _ _ _ hlen
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 _ _ _ hr
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil] using RlpConcrete.decode_bytes_32 k sBytes [] hs
  rw [Bytes.toBLTs?]

theorem envelope_parse : signedBytes.toBLT? = some (.list fields) := by
  have hlen : Bytes.toNat [0x07, 0x46] = payload.length := by
    rw [payload_length]
    decide +kernel
  have parsed := RlpConcrete.decode_list_long_two 1864 0x07 0x46
    payload [] fields hlen (payload_parse 1855)
  simp only [List.append_nil] at parsed
  unfold signedBytes Bytes.toBLT?
  simp only [List.cons_append, List.nil_append, List.length_cons, payload_length]
  rw [parsed]

/-- Full signed bytes pass the actual strict legacy decoder. -/
theorem signed_decode :
    signedBytes.toBLT?.bind (fun blt => blt.toExTx.toOption) = some tx := by
  rw [envelope_parse]
  rfl

theorem tx_blt : tx.toBLT = .list fields := by
  dsimp only [tx, fields, Tx.toBLT]
  congr <;> decide +kernel

/-- Canonical re-encoding preserves the complete signed envelope. -/
theorem canonical : tx.toBLT.toBytes = signedBytes := by
  have hcode : (BLT.bytes code.toList).toBytes =
      [0xb9, 0x06, 0xf3] ++ code.toList := by
    rw [RlpConcrete.encode_bytes_many _ (by rw [code_toList_length]; omega),
      code_toList_length]
    norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
      Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq,
      UInt8.reduceOfNat, UInt8.reduceAdd, ↓reduceIte, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append]
  have hr : (BLT.bytes rBytes).toBytes = 0xa0 :: rBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
      show rBytes.length = 32 from by decide +kernel]
    rfl
  have hs : (BLT.bytes sBytes).toBytes = 0xa0 :: sBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
      show sBytes.length = 32 from by decide +kernel]
    rfl
  have joined : BLTs.toBytesJoin fields = payload := by
    simp only [fields, payload, BLTs.toBytesJoin, hcode, hr, hs, BLT.toBytes,
      List.length_cons, List.length_nil, Nat.reduceLT, UInt8.reduceLT, ↓reduceIte,
      List.cons_append, List.nil_append, List.append_nil, List.append_assoc]
    rfl
  rw [tx_blt, BLT.toBytes, BLTs.toBytes, joined, payload_length]
  unfold signedBytes
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one,
      Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq,
      UInt8.reduceOfNat, UInt8.reduceAdd, ↓reduceIte, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append]

theorem transaction_hash_bytes : getTxHash tx = signedBytes.keccak := by
  unfold getTxHash
  rw [canonical]

theorem signing_hash : tx.signingHash =
    some 0x0b923c20ae300a3a20431bf4781920c212aa03d3894190c1bde5a93411bc8abd := by
  exact signingHash rfl rfl rfl rfl rfl rfl

theorem recovered : recoverSender 1 tx = .ok originalCreator := by
  exact recoveredSender rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel)

end Blanc.Lift.Usdc.LibCreation.SignedInput
