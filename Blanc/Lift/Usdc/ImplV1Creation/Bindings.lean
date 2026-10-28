import Blanc.Lift.Usdc.ImplV1Creation.Check
import Blanc.Lift.Usdc.ImplV1Origin

/-! Unadopted V1 constructor binding preview. Actual historical witnesses remain explicit. -/

namespace Blanc.Lift.Usdc.ImplV1Creation

open Jaune ExecutionTrace

/-- The actual entry certified for the proposed V1 creation code. -/
theorem constructor_entry : cert.prog[0]? = some legacyOwnerConstructor := by
  rfl

/-- The certified internal owner initializer is the shared legacy helper. -/
theorem owner_entry : cert.prog[1]? = some SolcStorageReturn.legacyOwnerInit := by
  rfl

/-- The certified return entry selects the exact V1 runtime window. -/
theorem return_entry : cert.prog[2]? = some
    (solcRuntimeReturn [0x2f, 0x5b] [0x00, 0x93] (by decide) (by decide)) := by
  rfl

/-- Byte identity only: the proposed constructor returns the registered V1 runtime. -/
theorem runtime_window : code.sliceD 147 12123 0 = ImplV1.code.toList := by
  rw [ByteArray.sliceD_eq, ByteArray.toList_eq_toList_data,
    ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

/-- Concrete constructor certification and byte identity supply the code/storage
installation at the original index30 cut. Original transaction and receipt
correspondence remain explicit inputs. -/
theorem effects_of_original_receipt
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 30)
    (receiver : cut.tx.type.receiver? = none) (input : cut.tx.data = code.toList)
    (nonce : cut.tx.nonce = 18)
    (recovered : recoverSender 1 cut.tx = .ok ProxyCreation.originalCreator)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (30 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      cut.afterBenv.state.getStor ProxyCreation.initialImplementation.toAdr =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  exact ImplV1Origin.constructor_effects_of_original_receipt cert_check constructor_entry
    owner_entry return_entry runtime_window block cut receiver input nonce recovered lookup succeeded

/-- Exact original signed fields discharge sender recovery using the existing
conditional signature proof. The signing hash and actual body/receipt witnesses
remain explicit; no historical execution is introduced as an assumption. -/
theorem effects_of_signed_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 30)
    {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : block.block.txs[30]? = some slot)
    (decoded : decodeTx block.fork.ruleSet slot = .ok tx)
    (txType : tx.type = .zero 4000000000 none) (input : tx.data = code.toList)
    (nonce : tx.nonce = 18)
    (v : tx.v = 38)
    (r : tx.r.toB256 = 0xb27c0adac33faeeb6a7fc58d536ba8bda38e3054d53461008d39a18031531609)
    (s : tx.s.toB256 = 0x7a25d7dc3f2f43eda8a8b560f6224aa83270bc4d8804d453b792df8200ba0d15)
    (hashed : tx.signingHash = some 0x3a424731e9075d7b45dcc6ab92455664e56100fbb6419923723a54aa9d5710ad)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (30 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      cut.afterBenv.state.getStor ProxyCreation.initialImplementation.toAdr =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  exact ImplV1Origin.constructor_effects_of_signed_slot cert_check constructor_entry
    owner_entry return_entry runtime_window block cut atIndex decoded txType input nonce
    v r s hashed lookup succeeded

end Blanc.Lift.Usdc.ImplV1Creation
