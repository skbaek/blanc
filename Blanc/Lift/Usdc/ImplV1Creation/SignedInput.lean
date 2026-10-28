import Blanc.Lift.Usdc.ImplV1Creation.SigningHash

/-! Strict decoding of the unadopted V1 signed creation envelope. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SignedInput
open Jaune ExecutionTrace

def rBytes : Bytes :=
  (0xb27c0adac33faeeb6a7fc58d536ba8bda38e3054d53461008d39a18031531609 : B256).toBytes
def sBytes : Bytes :=
  (0x7a25d7dc3f2f43eda8a8b560f6224aa83270bc4d8804d453b792df8200ba0d15 : B256).toBytes

def tx : Tx := {
  nonce := 18, gas := 6721975, value := 0, data := code.toList,
  v := 38, r := rBytes, s := sBytes, type := .zero 4000000000 none }

def fields : List BLT :=
  [.bytes [0x12], .bytes [0xee, 0x6b, 0x28, 0x00], .bytes [0x66, 0x91, 0xb7],
   .bytes [], .bytes [], .bytes code.toList, .bytes [0x26], .bytes rBytes, .bytes sBytes]

def payload : Bytes :=
  [0x12, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x66, 0x91, 0xb7,
    0x80, 0x80, 0xb9, 0x2f, 0xee] ++ code.toList ++
    [0x26, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes

def signedBytes : Bytes := [0xf9, 0x30, 0x40] ++ payload

theorem strict_legacy_decode : BLT.toExLegacyTx fields = .ok tx := by
  rfl

/-- The slot is certified by the strict legacy decoder, not a typed-slot bypass. -/
def envelope : TxEnvelope := TxEnvelope.ofLegacyDecode strict_legacy_decode

theorem payload_length : payload.length = 12352 := by
  simp only [payload, List.length_append, List.length_cons, List.length_nil,
    code_toList_length, rBytes, sBytes, B256.length_toBytes, Nat.reduceAdd]

theorem payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) payload = some fields := by
  have hlen : Bytes.toNat [0x2f, 0xee] = code.toList.length := by
    rw [code_toList_length]
    decide +kernel
  have hr : rBytes.length = 32 := by decide +kernel
  have hs : sBytes.length = 32 := by decide +kernel
  unfold payload fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 [0xee, 0x6b, 0x28, 0x00] _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [0x66, 0x91, 0xb7] _ rfl
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
  have hlen : Bytes.toNat [0x30, 0x40] = payload.length := by
    rw [payload_length]
    decide +kernel
  have parsed := RlpConcrete.decode_list_long_two 12354 0x30 0x40
    payload [] fields hlen (payload_parse 12345)
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
  have hr : trimZero rBytes = rBytes := by decide +kernel
  have hs : trimZero sBytes = sBytes := by decide +kernel
  norm_num only [tx, fields, Tx.toBLT, hr, hs, Nat.toBytes, Nat.toBytes.aux,
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv,
    Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat]

/-- Canonical re-encoding preserves the complete signed envelope. -/
theorem canonical : tx.toBLT.toBytes = signedBytes := by
  have hcode : (BLT.bytes code.toList).toBytes =
      [0xb9, 0x2f, 0xee] ++ code.toList := by
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
    some 0x3a424731e9075d7b45dcc6ab92455664e56100fbb6419923723a54aa9d5710ad := by
  exact signingHash rfl rfl rfl rfl rfl rfl

theorem recovered : recoverSender 1 tx = .ok ProxyCreation.originalCreator := by
  exact recoveredSender rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel)

/-- One original, decoder-certified legacy slot supplies all constructor fields.
The actual block/cut and successful receipt are still the original witnesses. -/
theorem effects_of_original_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 30)
    (atIndex : block.block.txs[30]? = some envelope.entry)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (30 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      cut.afterBenv.state.getStor ProxyCreation.initialImplementation.toAdr =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  exact effects_of_encoded_slot block cut atIndex (tx := tx) rfl
    rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) lookup succeeded

end Blanc.Lift.Usdc.ImplV1Creation.SignedInput
