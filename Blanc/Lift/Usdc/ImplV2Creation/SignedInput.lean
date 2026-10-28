import Blanc.Lift.Usdc.ImplV2Creation.SigningHash

/-! Strict decoding of the unadopted V2 signed creation envelope. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SignedInput
open Jaune ExecutionTrace

def rBytes : Bytes :=
  (0x97d92aab5ca93d6c4b864f2c41822537d7eeb03ea2e319348727a0ce6db7cc1b : B256).toBytes
def sBytes : Bytes :=
  (0x134f14d536f99dce12e7b4ac2209061b26d6c4ee7725a5a0317ad88e7315458d : B256).toBytes

def tx : Tx := {
  nonce := 31, gas := 5200000, value := 0, data := code.toList,
  v := 28, r := rBytes, s := sBytes, type := .zero 150000000000 none }

def fields : List BLT :=
  [.bytes [0x1f], .bytes [0x22, 0xec, 0xb2, 0x5c, 0x00], .bytes [0x4f, 0x58, 0x80],
   .bytes [], .bytes [], .bytes code.toList, .bytes [0x1c], .bytes rBytes, .bytes sBytes]

def payload : Bytes :=
  [0x1f, 0x85, 0x22, 0xec, 0xb2, 0x5c, 0x00, 0x83, 0x4f, 0x58, 0x80,
    0x80, 0x80, 0xb9, 0x5a, 0xd0] ++ code.toList ++
    [0x1c, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes

def signedBytes : Bytes := [0xf9, 0x5b, 0x23] ++ payload

theorem strict_legacy_decode : BLT.toExLegacyTx fields = .ok tx := by
  rfl

/-- The slot is certified by the strict legacy decoder, not a typed-slot bypass. -/
def envelope : TxEnvelope := TxEnvelope.ofLegacyDecode strict_legacy_decode

theorem payload_length : payload.length = 23331 := by
  simp only [payload, List.length_append, List.length_cons, List.length_nil,
    code_toList_length, rBytes, sBytes, B256.length_toBytes, Nat.reduceAdd]

theorem payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) payload = some fields := by
  have hlen : Bytes.toNat [0x5a, 0xd0] = code.toList.length := by
    rw [code_toList_length]
    decide +kernel
  have hr : rBytes.length = 32 := by decide +kernel
  have hs : sBytes.length = 32 := by decide +kernel
  unfold payload fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 [0x22, 0xec, 0xb2, 0x5c, 0x00] _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [0x4f, 0x58, 0x80] _ rfl
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
  have hlen : Bytes.toNat [0x5b, 0x23] = payload.length := by
    rw [payload_length]
    decide +kernel
  have parsed := RlpConcrete.decode_list_long_two 23333 0x5b 0x23
    payload [] fields hlen (payload_parse 23324)
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
      [0xb9, 0x5a, 0xd0] ++ code.toList := by
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
    some 0xf2c79146b7c5d2251888a408d1391aee591ac0f105668159b5638f7ac3c73215 := by
  exact signingHash rfl rfl rfl rfl rfl rfl

theorem recovered : recoverSender 1 tx = .ok ProxyCreation.originalCreator := by
  exact recoveredSender rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel)

/-- One original, decoder-certified legacy slot supplies all constructor fields.
The actual block/cut and successful receipt are still the original witnesses. -/
theorem effects_of_original_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 38)
    (atIndex : block.block.txs[38]? = some envelope.entry)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (38 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode F2prime.implementationV2 = ImplV2.code ∧
      cut.afterBenv.state.getStor F2prime.implementationV2 =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  exact effects_of_encoded_slot block cut atIndex (tx := tx) rfl
    rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) lookup succeeded

end Blanc.Lift.Usdc.ImplV2Creation.SignedInput
