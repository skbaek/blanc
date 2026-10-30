import Blanc.Lift.Usdc.ImplV2_1Creation.SigningEncoding
import Blanc.Lift.Usdc.ProxyCreation.Transaction
import Blanc.ExecutionBodyTransactionCut
import Blanc.ExecutionMidHistoryInFacts

/-! Exact hash and signature consumers for the unadopted V2.1 creation preview. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation
open Jaune ExecutionTrace

/-- Kernel hash of the exact unprotected legacy signing envelope. -/
theorem signingPayload_hash : signingPayload.keccak = (0x67266765a0508883ae11ac6dd0ad8d63c2d6cf26d7af55c349361662a14ede87 : B256) := by
  unfold signingPayload
  rw [ByteArray.toList_eq_toList_data]
  simp only [code, List.toList_toArray]
  decide +kernel

/-- Explicit original transaction fields determine the signing hash. -/
theorem signingHash {tx : Tx}
    (htype : tx.type = .zero 130000000000 none)
    (hnonce : tx.nonce = 38) (hgas : tx.gas = 5500000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 28) :
    tx.signingHash = some 0x67266765a0508883ae11ac6dd0ad8d63c2d6cf26d7af55c349361662a14ede87 := by
  rw [signingEncoded htype hnonce hgas hvalue hdata hv, signingPayload_hash]

/-- Exact fields and signature recover the registered creator without a hash premise. -/
theorem recoveredSender {tx : Tx}
    (htype : tx.type = .zero 130000000000 none)
    (hnonce : tx.nonce = 38) (hgas : tx.gas = 5500000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 28)
    (hr : tx.r.toB256 = 0xb9bc3eb6db5a1802c08eef290588d55994b3b5c1a11c86bd346aa8b1a8c0b9d9)
    (hs : tx.s.toB256 = 0x5017bbef826d8cfb3815bc8b77a3aeb8f306f19efeb38b166e779670ce4a0023) :
    recoverSender 1 tx = .ok ProxyCreation.originalCreator := by
  rw [recoverSender, hr, hs, hv,
    signingHash htype hnonce hgas hvalue hdata hv, htype]
  decide +kernel

/-- Nonce 38 of the registered creator computes the registered V2.1 address. -/
theorem create_address :
    computeContractAddress ProxyCreation.originalCreator 38 = F2prime.implementationV2_1 := by
  have senderBytes : ProxyCreation.originalCreator.toBytes =
      [0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11] := by decide +kernel
  have nonceBytes : (UInt64.toBytes 38).sig = [0x26] := by decide +kernel
  have encoding : BLT.toBytes (.list [.bytes
      [0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11], .bytes [0x26]]) =
      [0xd6, 0x94, 0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11, 0x26] := by
    simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.toUInt8_eq, UInt8.reduceOfNat,
      UInt8.reduceAdd, UInt8.reduceLT, List.append_nil, List.cons_append, List.nil_append]
  unfold computeContractAddress
  rw [senderBytes, nonceBytes, encoding]
  decide +kernel


/-- The original decoded signed transaction and successful receipt install V2.1.
Original history, slot/field and receipt correspondence remain explicit. -/
theorem effects_of_encoded_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 8)
    {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : block.block.txs[8]? = some slot)
    (decoded : decodeTx block.fork.ruleSet slot = .ok tx)
    (htype : tx.type = .zero 130000000000 none)
    (hnonce : tx.nonce = 38) (hgas : tx.gas = 5500000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 28)
    (hr : tx.r.toB256 = 0xb9bc3eb6db5a1802c08eef290588d55994b3b5c1a11c86bd346aa8b1a8c0b9d9)
    (hs : tx.s.toB256 = 0x5017bbef826d8cfb3815bc8b77a3aeb8f306f19efeb38b166e779670ce4a0023)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (8 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode F2prime.implementationV2_1 = ImplV2_1.code ∧
      cut.afterBenv.state.getStor F2prime.implementationV2_1 =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  obtain ⟨_, same⟩ := block.bodyTrace.txSplit_tx_eq_of_slot cut atIndex decoded
  have recovered := recoveredSender htype hnonce hgas hvalue hdata hv hr hs
  rw [← same] at recovered
  have sender := block.txSplit_sender_of_recovery cut recovered
  have receiver : cut.tx.type.receiver? = none := by rw [same, htype]; rfl
  have input : cut.tx.data = code.toList := by rw [same, hdata]
  have address : computeContractAddress cut.head.sender cut.tx.nonce =
      F2prime.implementationV2_1 := by
    rw [sender, same, hnonce]
    exact create_address
  have effects := effects_of_original_receipt block cut receiver input address lookup succeeded
  simpa only [sender] using effects

end Blanc.Lift.Usdc.ImplV2_1Creation
