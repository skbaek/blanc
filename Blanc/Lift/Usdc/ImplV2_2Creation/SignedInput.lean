import Blanc.RlpListEncode
import Blanc.RlpRoundTrip
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

/-- The exact signed envelope: a closed header, the creation input, and the closed signature
tail. -/
def signedBytes : Bytes :=
  [0xf9, 0x5c, 0x62, 0x01, 0x85, 0x05, 0x1f, 0x4d, 0x5c, 0x00, 0x83, 0xe4,
    0xe1, 0xc0, 0x80, 0x80, 0xb9, 0x5c, 0x0f] ++
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
