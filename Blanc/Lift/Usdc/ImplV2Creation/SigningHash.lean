import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds00
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds01
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds02
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds03
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds04
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds05
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds06
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds07
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds08
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds09
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds10
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds11
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds12
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds13
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds14
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds15
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds16
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds17
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds18
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds19
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds20
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds21
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds22
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds23
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds24
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds25
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds26
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds27
import Blanc.Lift.Usdc.ImplV2Creation.SigningRounds28
import Blanc.Lift.Usdc.ProxyCreation.Transaction
import Blanc.ExecutionBodyTransactionCut
import Blanc.ExecutionMidHistoryInFacts

/-! Exact hash and signature consumers for the unadopted V2 creation preview. -/
namespace Blanc.Lift.Usdc.ImplV2Creation
open Jaune ExecutionTrace
open SigningBlocks

/-- Kernel hash of the exact unprotected legacy signing envelope. -/
theorem signingPayload_hash : signingPayload.keccak = (0xf2c79146b7c5d2251888a408d1391aee591ac0f105668159b5638f7ac3c73215 : B256) := by
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
  rewrite [block156, block157, block158, block159, block160, block161]
  rewrite [block162, block163, block164, block165, block166, block167]
  rewrite [block168, block169, block170]
  exact finalHash

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
