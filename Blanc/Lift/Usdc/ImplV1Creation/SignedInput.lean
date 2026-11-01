import Blanc.RlpListEncode
import Blanc.RlpRoundTrip
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

/-- The exact signed envelope: a closed header, the creation input, and the closed signature
tail. -/
def signedBytes : Bytes :=
  [0xf9, 0x30, 0x40, 0x12, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x66, 0x91,
    0xb7, 0x80, 0x80, 0xb9, 0x2f, 0xee] ++
    code.toList ++ ([0x26, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes)

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
