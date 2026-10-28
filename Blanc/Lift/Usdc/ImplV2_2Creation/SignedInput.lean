import Blanc.Lift.Usdc.ImplV2_2Creation.SigningHash

/-! Strict decoding of the unadopted V2.2 signed creation envelope. -/
namespace Blanc.Lift.Usdc.ImplV2_2Creation.SignedInput
open Jaune ExecutionTrace

def rBytes : Bytes :=
  (0x8c64b91a38d78c9289668f0ee1673fcbba4867e138dacca7b6c3a6b3c35d9df0 : B256).toBytes
def sBytes : Bytes :=
  (0x39aa4fe1f3512c8e0d30a6faf1e4dd1fe808d78753a57fe75aafc94b4b82d21c : B256).toBytes

def tx : Tx := {
  nonce := 1, gas := 15000000, value := 0, data := code.toList,
  v := 37, r := rBytes, s := sBytes, type := .zero 22000000000 none }

def fields : List BLT :=
  [.bytes [0x01], .bytes [0x05, 0x1f, 0x4d, 0x5c, 0x00], .bytes [0xe4, 0xe1, 0xc0],
   .bytes [], .bytes [], .bytes code.toList, .bytes [0x25], .bytes rBytes, .bytes sBytes]

def payload : Bytes :=
  [0x01, 0x85, 0x05, 0x1f, 0x4d, 0x5c, 0x00, 0x83, 0xe4, 0xe1, 0xc0,
    0x80, 0x80, 0xb9, 0x5c, 0x0f] ++ code.toList ++
    [0x25, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes

def signedBytes : Bytes := [0xf9, 0x5c, 0x62] ++ payload

theorem strict_legacy_decode : BLT.toExLegacyTx fields = .ok tx := by
  rfl

/-- The slot is certified by the strict legacy decoder, not a typed-slot bypass. -/
def envelope : TxEnvelope := TxEnvelope.ofLegacyDecode strict_legacy_decode

theorem payload_length : payload.length = 23650 := by
  simp only [payload, List.length_append, List.length_cons, List.length_nil,
    code_toList_length, rBytes, sBytes, B256.length_toBytes, Nat.reduceAdd]

theorem payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) payload = some fields := by
  have hlen : Bytes.toNat [0x5c, 0x0f] = code.toList.length := by
    rw [code_toList_length]
    decide +kernel
  have hr : rBytes.length = 32 := by decide +kernel
  have hs : sBytes.length = 32 := by decide +kernel
  unfold payload fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ rfl
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
  have hlen : Bytes.toNat [0x5c, 0x62] = payload.length := by
    rw [payload_length]
    decide +kernel
  have parsed := RlpConcrete.decode_list_long_two 23652 0x5c 0x62
    payload [] fields hlen (payload_parse 23643)
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
      [0xb9, 0x5c, 0x0f] ++ code.toList := by
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
    some 0x343519a45eb48ace5cbe7daeab09d33857ada1ea478e7f513955b7e5b1db3dc5 := by
  exact signingHash rfl rfl rfl rfl rfl rfl

theorem recovered : recoverSender 1 tx = .ok originalCreator := by
  exact recoveredSender rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel)

/-- One original, decoder-certified legacy slot supplies all constructor fields.
The actual block/cut and successful receipt are still the original witnesses. -/
theorem effects_of_original_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 26)
    (atIndex : block.block.txs[26]? = some envelope.entry)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (26 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode F2prime.implementationV2_2 = Impl.code ∧
      cut.afterBenv.state.getStor F2prime.implementationV2_2 =
        solcOwnerConstructorStorage Stor.empty originalCreator := by
  exact effects_of_encoded_slot block cut atIndex (tx := tx) rfl
    rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) lookup succeeded

end Blanc.Lift.Usdc.ImplV2_2Creation.SignedInput
