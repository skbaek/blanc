import Blanc.Lift.Usdc.ImplV1Creation.SigningEncoding

/-! Exact hash and signature consumers for the unadopted V1 creation preview. -/
namespace Blanc.Lift.Usdc.ImplV1Creation
open Jaune ExecutionTrace

/-- Kernel hash of the exact conditional EIP-155 signing envelope. -/
theorem signingPayload_hash : signingPayload.keccak =
    (0x3a424731e9075d7b45dcc6ab92455664e56100fbb6419923723a54aa9d5710ad : B256) := by
  unfold signingPayload
  rw [ByteArray.toList_eq_toList_data]
  simp only [code, List.toList_toArray]
  decide +kernel

/-- Explicit transaction fields determine the signing hash. -/
theorem signingHash {tx : Tx}
    (htype : tx.type = .zero 4000000000 none)
    (hnonce : tx.nonce = 18) (hgas : tx.gas = 6721975)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 38) :
    tx.signingHash = some 0x3a424731e9075d7b45dcc6ab92455664e56100fbb6419923723a54aa9d5710ad := by
  rw [signingEncoded htype hnonce hgas hvalue hdata hv, signingPayload_hash]

/-- These fields and signature recover the registered creator, without a hash premise. -/
theorem recoveredSender {tx : Tx}
    (htype : tx.type = .zero 4000000000 none)
    (hnonce : tx.nonce = 18) (hgas : tx.gas = 6721975)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 38)
    (hr : tx.r.toB256 = 0xb27c0adac33faeeb6a7fc58d536ba8bda38e3054d53461008d39a18031531609)
    (hs : tx.s.toB256 = 0x7a25d7dc3f2f43eda8a8b560f6224aa83270bc4d8804d453b792df8200ba0d15) :
    recoverSender 1 tx = .ok ProxyCreation.originalCreator := by
  exact ImplV1Origin.recoveredSender_of_signingHash htype hv hr hs
    (signingHash htype hnonce hgas hvalue hdata hv)

/-- The original decoded signed transaction and successful receipt install V1.
Only original history, slot/field and receipt correspondence remain explicit. -/
theorem effects_of_encoded_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 30)
    {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : block.block.txs[30]? = some slot)
    (decoded : decodeTx block.fork.ruleSet slot = .ok tx)
    (htype : tx.type = .zero 4000000000 none)
    (hnonce : tx.nonce = 18) (hgas : tx.gas = 6721975)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 38)
    (hr : tx.r.toB256 = 0xb27c0adac33faeeb6a7fc58d536ba8bda38e3054d53461008d39a18031531609)
    (hs : tx.s.toB256 = 0x7a25d7dc3f2f43eda8a8b560f6224aa83270bc4d8804d453b792df8200ba0d15)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (30 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      cut.afterBenv.state.getStor ProxyCreation.initialImplementation.toAdr =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  exact effects_of_signed_slot block cut atIndex decoded htype hdata hnonce hv hr hs
    (signingHash htype hnonce hgas hvalue hdata hv) lookup succeeded

end Blanc.Lift.Usdc.ImplV1Creation
