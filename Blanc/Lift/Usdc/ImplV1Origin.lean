import Blanc.Lift.ConstructorTransaction
import Blanc.Lift.Usdc.ProxyCreation.Transaction
import Blanc.Lift.Usdc.ImplV1.Cert
import Blanc.ExecutionMidHistoryInFacts
import Blanc.ExecutionBodyTransactionCut

/-!
# V1 implementation origin from its original successful creation receipt

The creator and implementation address are already registered proxy constants.
Creation code and its certificate remain parameters: this module adopts no new
creation input or historical observation. Original transaction fields, recovery,
receipt lookup and the runtime-window certificate remain explicit.
-/

namespace Blanc.Lift.Usdc.ImplV1Origin

open Jaune ExecutionTrace

/-- At nonce18, the already registered creator computes the already registered
initial implementation address. This is arithmetic, not historical inclusion. -/
theorem create_address :
    computeContractAddress ProxyCreation.originalCreator 18 = ProxyCreation.initialImplementation.toAdr := by
  have senderBytes : ProxyCreation.originalCreator.toBytes =
      [0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11] := by decide +kernel
  have nonceBytes : (UInt64.toBytes 18).sig = [0x12] := by decide +kernel
  have encoding : BLT.toBytes (.list [.bytes
      [0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11], .bytes [0x12]]) =
      [0xd6, 0x94, 0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11, 0x12] := by
    simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.toUInt8_eq, UInt8.reduceOfNat,
      UInt8.reduceAdd, UInt8.reduceLT, List.append_nil, List.cons_append, List.nil_append]
  unfold computeContractAddress
  rw [senderBytes, nonceBytes, encoding]
  decide +kernel

/-- The original index30 receipt yields the registered V1 runtime and owner
storage at the exact cut. Creation-code certification, runtime-window identity,
original fields and recovery remain explicit; none is adopted here. -/
theorem constructor_effects_of_original_receipt
    {pre completed : BlockChain} {creationCode : ByteArray} {c : Cert}
    (checked : Cert.check creationCode c = true)
    (first : c.prog[0]? = some legacyOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.legacyOwnerInit)
    (returnEntry : c.prog[2]? = some
      (solcRuntimeReturn [0x2f, 0x5b] [0x00, 0x93] (by decide) (by decide)))
    (window : creationCode.sliceD 147 12123 0 = ImplV1.code.toList)
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 30)
    (receiver : cut.tx.type.receiver? = none) (input : cut.tx.data = creationCode.toList)
    (nonce : cut.tx.nonce = 18)
    (recovered : recoverSender 1 cut.tx = .ok ProxyCreation.originalCreator)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (30 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      cut.afterBenv.state.getStor ProxyCreation.initialImplementation.toAdr =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  have sender := block.txSplit_sender_of_recovery cut recovered
  have address : computeContractAddress cut.head.sender cut.tx.nonce =
      ProxyCreation.initialImplementation.toAdr := by
    rw [sender, nonce]
    exact create_address
  have actualLookup :
      block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? = some receipt := by
    rw [cut.putIndex_eq.1]
    exact lookup
  have effects := legacyOwnerConstructor_runtime_of_txSplit_receipt
    (size := 12123) (offset := 147) checked first ownerEntry returnEntry
    (by decide +kernel) (by decide +kernel) (by decide) window block cut
    (HistFork.stateGas_none block.forkIn) receiver input address actualLookup succeeded
  simpa only [sender] using effects

/-- One identified original body slot and its actual decoder result supply the
same V1 transaction fields to the original-cut producer. Other body slots keep
their original inputs; the selected transaction is never substituted. -/
theorem constructor_effects_of_original_slot
    {pre completed : BlockChain} {creationCode : ByteArray} {c : Cert}
    (checked : Cert.check creationCode c = true)
    (first : c.prog[0]? = some legacyOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.legacyOwnerInit)
    (returnEntry : c.prog[2]? = some
      (solcRuntimeReturn [0x2f, 0x5b] [0x00, 0x93] (by decide) (by decide)))
    (window : creationCode.sliceD 147 12123 0 = ImplV1.code.toList)
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 30)
    {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : block.block.txs[30]? = some slot)
    (decoded : decodeTx block.fork.ruleSet slot = .ok tx)
    (receiver : tx.type.receiver? = none) (input : tx.data = creationCode.toList)
    (nonce : tx.nonce = 18)
    (recovered : recoverSender 1 tx = .ok ProxyCreation.originalCreator)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (30 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      cut.afterBenv.state.getStor ProxyCreation.initialImplementation.toAdr =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  obtain ⟨_, same⟩ := block.bodyTrace.txSplit_tx_eq_of_slot cut atIndex decoded
  rw [← same] at receiver input nonce recovered
  exact constructor_effects_of_original_receipt checked first ownerEntry returnEntry window
    block cut receiver input nonce recovered lookup succeeded

/-- The explicit signature recovers the registered creator conditional on
this transaction's signing hash. The hash equality and original transaction
correspondence are obligations, not consequences of the offline candidate. -/
theorem recoveredSender_of_signingHash {tx : Tx}
    (txType : tx.type = .zero 4000000000 none)
    (v : tx.v = 38)
    (r : tx.r.toB256 = 0xb27c0adac33faeeb6a7fc58d536ba8bda38e3054d53461008d39a18031531609)
    (s : tx.s.toB256 = 0x7a25d7dc3f2f43eda8a8b560f6224aa83270bc4d8804d453b792df8200ba0d15)
    (hashed : tx.signingHash = some 0x3a424731e9075d7b45dcc6ab92455664e56100fbb6419923723a54aa9d5710ad) :
    recoverSender 1 tx = .ok ProxyCreation.originalCreator := by
  rw [recoverSender, r, s, v, hashed, txType]
  decide +kernel

/-- Signed fields identify the original creator without an independently
supplied recovery result. The signing-hash equality, creation certificate,
runtime window and original slot/receipt correspondence remain explicit. -/
theorem constructor_effects_of_signed_slot
    {pre completed : BlockChain} {creationCode : ByteArray} {c : Cert}
    (checked : Cert.check creationCode c = true)
    (first : c.prog[0]? = some legacyOwnerConstructor)
    (ownerEntry : c.prog[1]? = some SolcStorageReturn.legacyOwnerInit)
    (returnEntry : c.prog[2]? = some
      (solcRuntimeReturn [0x2f, 0x5b] [0x00, 0x93] (by decide) (by decide)))
    (window : creationCode.sliceD 147 12123 0 = ImplV1.code.toList)
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 30)
    {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : block.block.txs[30]? = some slot)
    (decoded : decodeTx block.fork.ruleSet slot = .ok tx)
    (txType : tx.type = .zero 4000000000 none) (input : tx.data = creationCode.toList)
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
  exact constructor_effects_of_original_slot checked first ownerEntry returnEntry window
    block cut atIndex decoded (by rw [txType]; rfl) input nonce
    (recoveredSender_of_signingHash txType v r s hashed) lookup succeeded

end Blanc.Lift.Usdc.ImplV1Origin
