import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds00
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds01
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds02
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds03
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds04
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds05
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds06
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds07
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds08
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds09
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds10
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds11
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds12
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds13
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds14
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds15
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds16
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds17
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds18
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds19
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds20
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds21
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds22
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds23
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds24
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds25
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds26
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds27
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningRounds28
import Blanc.Lift.Usdc.ProxyCreation.Transaction
import Blanc.ExecutionBodyTransactionCut
import Blanc.ExecutionMidHistoryInFacts

/-! Exact hash and signature consumers for the unadopted V2.2 creation preview. -/
namespace Blanc.Lift.Usdc.ImplV2_2Creation
open Jaune ExecutionTrace
open SigningBlocks

/-- Explicit creator witness for this unadopted deployment preview. -/
def originalCreator : Adr := 0x2ba937d2c71d0fbbeda8ce3bf02a8b88727961ec

/-- Kernel hash of the exact EIP155 legacy signing envelope. -/
theorem signingPayload_hash : signingPayload.keccak = (0x343519a45eb48ace5cbe7daeab09d33857ada1ea478e7f513955b7e5b1db3dc5 : B256) := by
  change KECCAK.Bytes.run 0 signingPayload state000 = _
  rw [payload_split]
  unfold segment0 segment1 segment2 segment3 segment4 segment5
  simp only [List.append_assoc]
  rewrite [blocks00, blocks01, blocks02, blocks03, blocks04, blocks05]
  rewrite [blocks06, blocks07, blocks08, blocks09, blocks10, blocks11]
  rewrite [blocks12, blocks13, blocks14, blocks15, blocks16, blocks17]
  rewrite [blocks18, blocks19, blocks20, blocks21, blocks22, blocks23]
  rewrite [blocks24, blocks25, blocks26, blocks27]
  exact blocks28

/-- Explicit original transaction fields determine the signing hash. -/
theorem signingHash {tx : Tx}
    (htype : tx.type = .zero 22000000000 none)
    (hnonce : tx.nonce = 1) (hgas : tx.gas = 15000000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37) :
    tx.signingHash = some 0x343519a45eb48ace5cbe7daeab09d33857ada1ea478e7f513955b7e5b1db3dc5 := by
  rw [signingEncoded htype hnonce hgas hvalue hdata hv, signingPayload_hash]

/-- Exact fields and signature recover the explicit creator without a hash premise. -/
theorem recoveredSender {tx : Tx}
    (htype : tx.type = .zero 22000000000 none)
    (hnonce : tx.nonce = 1) (hgas : tx.gas = 15000000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37)
    (hr : tx.r.toB256 = 0x8c64b91a38d78c9289668f0ee1673fcbba4867e138dacca7b6c3a6b3c35d9df0)
    (hs : tx.s.toB256 = 0x39aa4fe1f3512c8e0d30a6faf1e4dd1fe808d78753a57fe75aafc94b4b82d21c) :
    recoverSender 1 tx = .ok originalCreator := by
  rw [recoverSender, hr, hs, hv,
    signingHash htype hnonce hgas hvalue hdata hv, htype]
  decide +kernel

/-- Nonce 1 of the explicit creator computes the registered V2.2 address. -/
theorem create_address :
    computeContractAddress originalCreator 1 = F2prime.implementationV2_2 := by
  have senderBytes : originalCreator.toBytes =
      [0x2b, 0xa9, 0x37, 0xd2, 0xc7, 0x1d, 0x0f, 0xbb, 0xed, 0xa8,
       0xce, 0x3b, 0xf0, 0x2a, 0x8b, 0x88, 0x72, 0x79, 0x61, 0xec] := by decide +kernel
  have nonceBytes : (UInt64.toBytes 1).sig = [0x01] := by decide +kernel
  have encoding : BLT.toBytes (.list [.bytes
      [0x2b, 0xa9, 0x37, 0xd2, 0xc7, 0x1d, 0x0f, 0xbb, 0xed, 0xa8,
       0xce, 0x3b, 0xf0, 0x2a, 0x8b, 0x88, 0x72, 0x79, 0x61, 0xec], .bytes [0x01]]) =
      [0xd6, 0x94, 0x2b, 0xa9, 0x37, 0xd2, 0xc7, 0x1d, 0x0f, 0xbb, 0xed, 0xa8,
       0xce, 0x3b, 0xf0, 0x2a, 0x8b, 0x88, 0x72, 0x79, 0x61, 0xec, 0x01] := by
    simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.toUInt8_eq, UInt8.reduceOfNat,
      UInt8.reduceAdd, UInt8.reduceLT, List.append_nil, List.cons_append, List.nil_append]
  unfold computeContractAddress
  rw [senderBytes, nonceBytes, encoding]
  decide +kernel


/-- The original decoded signed transaction and successful receipt install V2.2.
Original history, slot/field and receipt correspondence remain explicit. -/
theorem effects_of_encoded_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 26)
    {slot : Bytes ⊕ Tx} {tx : Tx}
    (atIndex : block.block.txs[26]? = some slot)
    (decoded : decodeTx block.fork.ruleSet slot = .ok tx)
    (htype : tx.type = .zero 22000000000 none)
    (hnonce : tx.nonce = 1) (hgas : tx.gas = 15000000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37)
    (hr : tx.r.toB256 = 0x8c64b91a38d78c9289668f0ee1673fcbba4867e138dacca7b6c3a6b3c35d9df0)
    (hs : tx.s.toB256 = 0x39aa4fe1f3512c8e0d30a6faf1e4dd1fe808d78753a57fe75aafc94b4b82d21c)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (26 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode F2prime.implementationV2_2 = Impl.code ∧
      cut.afterBenv.state.getStor F2prime.implementationV2_2 =
        solcOwnerConstructorStorage Stor.empty originalCreator := by
  obtain ⟨_, same⟩ := block.bodyTrace.txSplit_tx_eq_of_slot cut atIndex decoded
  have recovered := recoveredSender htype hnonce hgas hvalue hdata hv hr hs
  rw [← same] at recovered
  have sender := block.txSplit_sender_of_recovery cut recovered
  have receiver : cut.tx.type.receiver? = none := by rw [same, htype]; rfl
  have input : cut.tx.data = code.toList := by rw [same, hdata]
  have address : computeContractAddress cut.head.sender cut.tx.nonce =
      F2prime.implementationV2_2 := by
    rw [sender, same, hnonce]
    exact create_address
  have effects := effects_of_original_receipt block cut receiver input address lookup succeeded
  simpa only [sender] using effects

end Blanc.Lift.Usdc.ImplV2_2Creation
