import Blanc.Lift.Usdc.ImplV2Creation.SigningEncoding
import Blanc.Lift.Usdc.ProxyCreation.Transaction
import Blanc.ExecutionBodyTransactionCut
import Blanc.ExecutionMidHistoryInFacts

/-! Exact hash and signature consumers for the unadopted V2 creation preview. -/
namespace Blanc.Lift.Usdc.ImplV2Creation
open Jaune ExecutionTrace

/-- Kernel hash of the exact unprotected legacy signing envelope. -/
theorem signingPayload_hash : signingPayload.keccak = (0xf2c79146b7c5d2251888a408d1391aee591ac0f105668159b5638f7ac3c73215 : B256) := by
  unfold signingPayload
  rw [ByteArray.toList_eq_toList_data]
  simp only [code, List.toList_toArray]
  decide +kernel

/-- Explicit original transaction fields determine the signing hash. -/
theorem signingHash {tx : Tx}
    (htype : tx.type = .zero 150000000000 none)
    (hnonce : tx.nonce = 31) (hgas : tx.gas = 5200000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 28) :
    tx.signingHash = some 0xf2c79146b7c5d2251888a408d1391aee591ac0f105668159b5638f7ac3c73215 := by
  rw [signingEncoded htype hnonce hgas hvalue hdata hv, signingPayload_hash]

/-- Exact fields and signature recover the registered creator without a hash premise. -/
theorem recoveredSender {tx : Tx}
    (htype : tx.type = .zero 150000000000 none)
    (hnonce : tx.nonce = 31) (hgas : tx.gas = 5200000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 28)
    (hr : tx.r.toB256 = 0x97d92aab5ca93d6c4b864f2c41822537d7eeb03ea2e319348727a0ce6db7cc1b)
    (hs : tx.s.toB256 = 0x134f14d536f99dce12e7b4ac2209061b26d6c4ee7725a5a0317ad88e7315458d) :
    recoverSender 1 tx = .ok ProxyCreation.originalCreator := by
  rw [recoverSender, hr, hs, hv,
    signingHash htype hnonce hgas hvalue hdata hv, htype]
  decide +kernel

/-- Nonce31 of the registered creator computes the registered V2 address. -/
theorem create_address :
    computeContractAddress ProxyCreation.originalCreator 31 = F2prime.implementationV2 := by
  have senderBytes : ProxyCreation.originalCreator.toBytes =
      [0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11] := by decide +kernel
  have nonceBytes : (UInt64.toBytes 31).sig = [0x1f] := by decide +kernel
  have encoding : BLT.toBytes (.list [.bytes
      [0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11], .bytes [0x1f]]) =
      [0xd6, 0x94, 0x95, 0xba, 0x4c, 0xf8, 0x7d, 0x67, 0x23, 0xad, 0x9c, 0x0d,
       0xb2, 0x17, 0x37, 0xd8, 0x62, 0xbe, 0x80, 0xe9, 0x39, 0x11, 0x1f] := by
    simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.toUInt8_eq, UInt8.reduceOfNat,
      UInt8.reduceAdd, UInt8.reduceLT, List.append_nil, List.cons_append, List.nil_append]
  unfold computeContractAddress
  rw [senderBytes, nonceBytes, encoding]
  decide +kernel


/-- The original decoded signed transaction and successful receipt install V2.
Original history, slot/field and receipt correspondence remain explicit. -/
theorem effects_of_encoded_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 38)
    {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : block.block.txs[38]? = some slot)
    (decoded : decodeTx block.fork.ruleSet slot = .ok tx)
    (htype : tx.type = .zero 150000000000 none)
    (hnonce : tx.nonce = 31) (hgas : tx.gas = 5200000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 28)
    (hr : tx.r.toB256 = 0x97d92aab5ca93d6c4b864f2c41822537d7eeb03ea2e319348727a0ce6db7cc1b)
    (hs : tx.s.toB256 = 0x134f14d536f99dce12e7b4ac2209061b26d6c4ee7725a5a0317ad88e7315458d)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (38 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode F2prime.implementationV2 = ImplV2.code ∧
      cut.afterBenv.state.getStor F2prime.implementationV2 =
        solcOwnerConstructorStorage Stor.empty ProxyCreation.originalCreator := by
  obtain ⟨_, same⟩ := block.bodyTrace.txSplit_tx_eq_of_slot cut atIndex decoded
  have recovered := recoveredSender htype hnonce hgas hvalue hdata hv hr hs
  rw [← same] at recovered
  have sender := block.txSplit_sender_of_recovery cut recovered
  have receiver : cut.tx.type.receiver? = none := by rw [same, htype]; rfl
  have input : cut.tx.data = code.toList := by rw [same, hdata]
  have address : computeContractAddress cut.head.sender cut.tx.nonce =
      F2prime.implementationV2 := by
    rw [sender, same, hnonce]
    exact create_address
  have effects := effects_of_original_receipt block cut receiver input address lookup succeeded
  simpa only [sender] using effects

end Blanc.Lift.Usdc.ImplV2Creation
