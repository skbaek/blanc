import Blanc.Lift.Usdc.ImplV2_1Creation.SigningHash

/-! Strict decoding of the unadopted V2.1 signed creation envelope. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SignedInput
open Jaune ExecutionTrace

def rBytes : Bytes :=
  (0xb9bc3eb6db5a1802c08eef290588d55994b3b5c1a11c86bd346aa8b1a8c0b9d9 : B256).toBytes
def sBytes : Bytes :=
  (0x5017bbef826d8cfb3815bc8b77a3aeb8f306f19efeb38b166e779670ce4a0023 : B256).toBytes

def tx : Tx := {
  nonce := 38, gas := 5500000, value := 0, data := code.toList,
  v := 28, r := rBytes, s := sBytes, type := .zero 130000000000 none }

def fields : List BLT :=
  [.bytes [0x26], .bytes [0x1e, 0x44, 0x9a, 0x94, 0x00], .bytes [0x53, 0xec, 0x60],
   .bytes [], .bytes [], .bytes code.toList, .bytes [0x1c], .bytes rBytes, .bytes sBytes]

def payload : Bytes :=
  [0x26, 0x85, 0x1e, 0x44, 0x9a, 0x94, 0x00, 0x83, 0x53, 0xec, 0x60,
    0x80, 0x80, 0xb9, 0x54, 0x52] ++ code.toList ++
    [0x1c, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes

def signedBytes : Bytes := [0xf9, 0x54, 0xa5] ++ payload

theorem strict_legacy_decode : BLT.toExLegacyTx fields = .ok tx := by
  rfl

/-- The slot is certified by the strict legacy decoder, not a typed-slot bypass. -/
def envelope : TxEnvelope := TxEnvelope.ofLegacyDecode strict_legacy_decode

theorem payload_length : payload.length = 21669 := by
  simp only [payload, List.length_append, List.length_cons, List.length_nil,
    code_toList_length, rBytes, sBytes, B256.length_toBytes, Nat.reduceAdd]

theorem payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) payload = some fields := by
  have hlen : Bytes.toNat [0x54, 0x52] = code.toList.length := by
    rw [code_toList_length]
    decide +kernel
  have hr : rBytes.length = 32 := by decide +kernel
  have hs : sBytes.length = 32 := by decide +kernel
  unfold payload fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 [0x1e, 0x44, 0x9a, 0x94, 0x00] _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [0x53, 0xec, 0x60] _ rfl
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
  have hlen : Bytes.toNat [0x54, 0xa5] = payload.length := by
    rw [payload_length]
    decide +kernel
  have parsed := RlpConcrete.decode_list_long_two 21671 0x54 0xa5
    payload [] fields hlen (payload_parse 21662)
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
      [0xb9, 0x54, 0x52] ++ code.toList := by
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
    some 0x67266765a0508883ae11ac6dd0ad8d63c2d6cf26d7af55c349361662a14ede87 := by
  exact signingHash rfl rfl rfl rfl rfl rfl

theorem recovered : recoverSender 1 tx = .ok ProxyCreation.originalCreator := by
  exact recoveredSender rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel)

/-- One original, decoder-certified legacy slot supplies all constructor fields.
The actual block/cut and successful receipt are still the original witnesses. -/
theorem effects_of_original_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 8)
    (atIndex : block.block.txs[8]? = some envelope.entry)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (8 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode F2prime.implementationV2_1 = ImplV2_1.code ∧
      cut.afterBenv.state.getStor F2prime.implementationV2_1 =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  exact effects_of_encoded_slot block cut atIndex (tx := tx) rfl
    rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) lookup succeeded

end Blanc.Lift.Usdc.ImplV2_1Creation.SignedInput
