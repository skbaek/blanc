import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds00
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds01
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds02
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds03
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds04
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds05
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds06
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds07
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds08
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds09
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds10
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds11
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds12
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds13
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds14
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds15
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds16
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds17
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds18
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds19
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds20
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds21
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds22
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds23
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds24
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds25
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningRounds26
import Blanc.Lift.Usdc.ProxyCreation.Transaction
import Blanc.ExecutionBodyTransactionCut
import Blanc.ExecutionMidHistoryInFacts

/-! Exact hash and signature consumers for the unadopted V2.1 creation preview. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation
open Jaune ExecutionTrace
open SigningBlocks

/-- Kernel hash of the exact unprotected legacy signing envelope. -/
theorem signingPayload_hash : signingPayload.keccak = (0x67266765a0508883ae11ac6dd0ad8d63c2d6cf26d7af55c349361662a14ede87 : B256) := by
  change KECCAK.Bytes.run 0 signingPayload state000 = _
  rw [payload_split]
  unfold segment0 segment1 segment2 segment3 segment4 segment5
  simp only [List.append_assoc]
  rewrite [block000, block001, block002, block003, block004, block005]
  rewrite [block006, block007, block008, block009, block010, block011]
  rewrite [block012, block013, block014, block015, block016, block017]
  rewrite [block018, block019, block020, block021, block022, block023]
  rewrite [block024, block025, block026, block027, block028, block029]
  rewrite [block030, block031, block032, block033, block034, block035]
  rewrite [block036, block037, block038, block039, block040, block041]
  rewrite [block042, block043, block044, block045, block046, block047]
  rewrite [block048, block049, block050, block051, block052, block053]
  rewrite [block054, block055, block056, block057, block058, block059]
  rewrite [block060, block061, block062, block063, block064, block065]
  rewrite [block066, block067, block068, block069, block070, block071]
  rewrite [block072, block073, block074, block075, block076, block077]
  rewrite [block078, block079, block080, block081, block082, block083]
  rewrite [block084, block085, block086, block087, block088, block089]
  rewrite [block090, block091, block092, block093, block094, block095]
  rewrite [block096, block097, block098, block099, block100, block101]
  rewrite [block102, block103, block104, block105, block106, block107]
  rewrite [block108, block109, block110, block111, block112, block113]
  rewrite [block114, block115, block116, block117, block118, block119]
  rewrite [block120, block121, block122, block123, block124, block125]
  rewrite [block126, block127, block128, block129, block130, block131]
  rewrite [block132, block133, block134, block135, block136, block137]
  rewrite [block138, block139, block140, block141, block142, block143]
  rewrite [block144, block145, block146, block147, block148, block149]
  rewrite [block150, block151, block152, block153, block154, block155]
  rewrite [block156, block157]
  exact finalHash

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
