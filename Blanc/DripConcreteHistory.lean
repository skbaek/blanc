-- DripConcreteHistory.lean : literal inputs for the configured deployment.
--
-- Off-chain tooling proposes fixed type-2 transaction bytes only.  Every
-- decoder, signature, address, header and transition equality used below is
-- proved by Lean; no fixture result is a theorem premise.

import Blanc.DripDeploy
import Blanc.RlpConcrete

namespace Blanc
namespace Drip

open Jaune

def concreteCreateR : Bytes :=
  (0x7464c2d4052056b12b9ae05f570242b29f203e35ccb6698083dd3ea4c18dac6c : B256).toBytes
def concreteCreateS : Bytes :=
  (0x489dd9e7f128c202cdd8830fb1189bb2551ab4a2daa0b16e4caa510717fb2a2f : B256).toBytes

/-- A deterministic type-2 CREATE transaction for the frozen DRIP creation
artifact. The byte scalars are its EIP-1559 signature, proposed from key 1. -/
def concreteCreateTx : Tx := {
  nonce := 0
  gas := 500000
  value := 0
  data := creationCode
  v := 0
  r := concreteCreateR
  s := concreteCreateS
  type := .two 1 1 8 none []
}

def concreteCreateTxRlp : Bytes := 0x02 :: concreteCreateTx.toBLT.toBytes
def concreteCreateSender : Adr := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf
def concreteCreateTarget : Adr := 0xf2e246bb76df876cef8b38ae84130f4f55de395b

/- The configured transition remains to be proved.
The decoder and CREATE-address facts below contain no success assumptions. -/

theorem concreteCreateAddress : computeContractAddress concreteCreateSender 0 = concreteCreateTarget := by
  have hs : concreteCreateSender.toBytes =
      [0x7e, 0x5f, 0x45, 0x52, 0x09, 0x1a, 0x69, 0x12, 0x5d, 0x5d,
       0xfc, 0xb7, 0xb8, 0xc2, 0x65, 0x90, 0x29, 0x39, 0x5b, 0xdf] := by decide +kernel
  have hz : (UInt64.toBytes 0).sig = [] := by decide +kernel
  simp only [computeContractAddress, hs, hz, BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin]
  decide +kernel

private theorem concreteCreationEncoded :
    (BLT.bytes creationCode).toBytes = [0xb9, 0x07, 0xd1] ++ creationCode := by
  have hlen : creationCode.length = 2001 := creationCodeSize_exact
  rw [RlpConcrete.encode_bytes_many creationCode (by omega), hlen]
  simp [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux]

def concreteCreatePayload : Bytes :=
  [0x01, 0x80, 0x01, 0x08, 0x83, 0x07, 0xa1, 0x20, 0x80, 0x80, 0xb9, 0x07, 0xd1] ++
  creationCode ++ [0xc0, 0x80, 0xa0] ++ concreteCreateTx.r ++ [0xa0] ++ concreteCreateTx.s

def concreteCreateFields : List BLT :=
  [.bytes [1], .bytes [], .bytes [1], .bytes [8], .bytes [7, 0xa1, 0x20],
   .bytes [], .bytes [], .bytes creationCode, .list [], .bytes [],
   .bytes concreteCreateR, .bytes concreteCreateS]

theorem concreteCreateBLT : concreteCreateTx.toBLT = .list concreteCreateFields := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hr : trimZero concreteCreateR = concreteCreateR := by decide +kernel
  have hs : trimZero concreteCreateS = concreteCreateS := by decide +kernel
  simp [Tx.toBLT, concreteCreateTx, concreteCreateFields, AccessList.toBLT,
    hc, hr, hs, Nat.toBytes, Nat.toBytes.aux]

theorem concreteCreateEncoded :
    concreteCreateTxRlp = [0x02, 0xf9, 0x08, 0x22] ++ concreteCreatePayload := by
  have hrlen : concreteCreateR.length = 32 := by decide +kernel
  have hslen : concreteCreateS.length = 32 := by decide +kernel
  have hr : (BLT.bytes concreteCreateR).toBytes = 0xa0 :: concreteCreateR := by
    rw [RlpConcrete.encode_bytes_many _ (by omega), hrlen]
    rfl
  have hs : (BLT.bytes concreteCreateS).toBytes = 0xa0 :: concreteCreateS := by
    rw [RlpConcrete.encode_bytes_many _ (by omega), hslen]
    rfl
  have hlen : creationCode.length = 2001 := creationCodeSize_exact
  rw [concreteCreateTxRlp, concreteCreateBLT]
  simp [concreteCreateFields, BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin,
    concreteCreationEncoded, hr, hs, hlen, hrlen, hslen,
    Nat.toBytes, Nat.toBytes.aux, Nat.toBytesPack,
    concreteCreatePayload, concreteCreateTx, List.append_assoc]

theorem concreteCreatePayloadParse (k : Nat) :
    Bytes.toBLTs? (k + 12) concreteCreatePayload = some concreteCreateFields := by
  have hrlen : concreteCreateR.length = 32 := by decide +kernel
  have hslen : concreteCreateS.length = 32 := by decide +kernel
  have hlen : Bytes.toNat [0x07, 0xd1] = creationCode.length := by
    rw [show creationCode.length = 2001 from creationCodeSize_exact]
    decide +kernel
  unfold concreteCreatePayload concreteCreateFields
  simp only [List.append_assoc, List.cons_append, List.nil_append, concreteCreateTx]
  change Bytes.toBLTs? (k + 12)
    (1 :: 0x80 :: 1 :: 8 :: 0x83 :: 7 :: 0xa1 :: 0x20 :: 0x80 :: 0x80 ::
      0xb9 :: 7 :: 0xd1 :: (creationCode ++ (0xc0 :: 0x80 :: 0xa0 ::
        (concreteCreateR ++ (0xa0 :: concreteCreateS))))) = _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by rfl)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by rfl)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by rfl)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [7, 0xa1, 0x20] _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_two _ _ _ _ _ hlen
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_list _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 _ _ _ hrlen
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil] using RlpConcrete.decode_bytes_32 k concreteCreateS [] hslen
  rw [Bytes.toBLTs?]

theorem concreteCreatePayload_length : concreteCreatePayload.length = 2082 := by
  have hlen : creationCode.length = 2001 := creationCodeSize_exact
  simp [concreteCreatePayload, concreteCreateTx, concreteCreateR, concreteCreateS,
    B256.length_toBytes, hlen]

theorem concreteCreateEnvelopeParse :
    Bytes.toBLT? (0xf9 :: 0x08 :: 0x22 :: concreteCreatePayload) =
      some (.list concreteCreateFields) := by
  have hlen : Bytes.toNat [0x08, 0x22] = concreteCreatePayload.length := by
    rw [concreteCreatePayload_length]
    decide +kernel
  have hparse := RlpConcrete.decode_list_long_two 2084 0x08 0x22
    concreteCreatePayload [] concreteCreateFields hlen (concreteCreatePayloadParse 2072)
  simp only [List.append_nil] at hparse
  unfold Bytes.toBLT?
  simp only [List.length_cons, concreteCreatePayload_length]
  rw [hparse]

theorem concreteCreateDecode :
    decodeTx (.inl concreteCreateTxRlp) = .ok concreteCreateTx := by
  simp only [decodeTx, concreteCreateEncoded, List.cons_append, List.nil_append,
    Bytes.toExTx, concreteCreateEnvelopeParse, concreteCreateFields]
  rfl

def concreteCreateSigningPayload : Bytes :=
  [0x02, 0xf9, 0x07, 0xdf, 0x01, 0x80, 0x01, 0x08, 0x83, 0x07, 0xa1,
    0x20, 0x80, 0x80, 0xb9, 0x07, 0xd1] ++ creationCode ++ [0xc0]

theorem concreteCreateSigningEncoded :
    concreteCreateTx.signingHash = some concreteCreateSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 0).sig = [] := by decide +kernel
  have h0 : Nat.toBytes 0 = [] := by simp [Nat.toBytes, Nat.toBytes.aux]
  have h1 : Nat.toBytes 1 = [1] := by simp [Nat.toBytes, Nat.toBytes.aux]
  have h8 : Nat.toBytes 8 = [8] := by simp [Nat.toBytes, Nat.toBytes.aux]
  have hg : Nat.toBytes 500000 = [7, 0xa1, 0x20] := by simp [Nat.toBytes, Nat.toBytes.aux]
  have hlen : creationCode.length = 2001 := creationCodeSize_exact
  simp only [Tx.signingHash, concreteCreateTx, hc, hn, h0, h1, h8, hg,
    AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  change 2 :: (BLT.list
    [.bytes [1], .bytes [], .bytes [1], .bytes [8], .bytes [7, 0xa1, 0x20],
     .bytes [], .bytes [], .bytes creationCode, .list []]).toBytes = _
  simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, concreteCreationEncoded,
    hlen, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux,
    concreteCreateSigningPayload]

theorem concreteCreateSigningHash :
    concreteCreateTx.signingHash =
      some (0x8b8f23d35f43a936d35980c133ac5c7303966324ed24f0cd4db79e2c78b8bfe0 : B256) := by
  rw [concreteCreateSigningEncoded]
  decide +kernel

theorem concreteCreateRecoveredSender :
    recoverSender 1 concreteCreateTx = .ok concreteCreateSender := by
  rw [recoverSender, concreteCreateSigningHash]
  decide +kernel

/-- A funded private Prague chain; the protocol addresses execute STOP. -/
def concreteConfig : ChainConfig := ChainConfig.pragueOnly 1

def concreteGenesisState : State := State.ofList
  [(concreteCreateSender, { Acct.nil with bal := 1000000000000000000 }),
   (beaconRootsAddress, { Acct.nil with code := ⟨#[0x5b, 0]⟩ }),
   (historyStorageAddress, { Acct.nil with code := ⟨#[0x5b, 0]⟩ }),
   (withdrawalRequestPredeployAddress, { Acct.nil with code := ⟨#[0x5b, 0]⟩ }),
   (consolidationRequestPredeployAddress, { Acct.nil with code := ⟨#[0x5b, 0]⟩ })]

def concreteGenesisHeader : Header := {
  parentHash := 0, ommersHash := emptyOmmerHash, coinbase := 0,
  stateRoot := concreteGenesisState.root, txsRoot := 0, receiptRoot := 0,
  bloom := List.replicate 256 0, difficulty := 0, number := 0,
  gasLimit := 10000000, gasUsed := 5000000, timestamp := 0,
  extraData := [], prevRandao := 0, nonce := 0, baseFeePerGas := 1,
  withdrawalsRoot := 0, blobGasUsed := 0, excessBlobGas := 0,
  parentBeaconBlockRoot := 0, requestsHash := some 0 }

def concreteGenesisBlock : Block :=
  { header := concreteGenesisHeader, txs := [], ommers := [], wds := [] }

def concreteBase : BlockChain :=
  ⟨[concreteGenesisBlock], concreteGenesisState, 1⟩

theorem concreteGenesisTarget : concreteGenesisState.get concreteCreateTarget = Acct.nil := by
  simp (disch := decide +kernel) only [concreteGenesisState, State.ofList,
    List.foldl_cons, List.foldl_nil, State.get_set_ne]
  rfl

theorem concreteGenesisSender :
    concreteGenesisState.get concreteCreateSender =
      { Acct.nil with bal := 1000000000000000000 } := by
  simp (disch := decide +kernel) only [concreteGenesisState, State.ofList,
    List.foldl_cons, List.foldl_nil, State.get_set_ne, State.get_set_self]

theorem concreteGenesisSystemCode (a : Adr)
    (ha : a ∈ [beaconRootsAddress, historyStorageAddress,
      withdrawalRequestPredeployAddress, consolidationRequestPredeployAddress]) :
    some (concreteGenesisState.getCode a).toList = Prog.compile deploymentSystemProgram := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  all_goals
    simp (disch := decide +kernel) only [State.getCode, concreteGenesisState,
      State.ofList, List.foldl_cons, List.foldl_nil, State.get_set_ne, State.get_set_self]
    decide +kernel

theorem concreteBase_validContext : concreteBase.ValidContext := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · change concreteGenesisState.Canonical
    apply State.canonical_ofList
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> exact Stor.canonical_empty
  · decide +kernel
  · intro tip htip
    have ht : tip = concreteGenesisBlock := by
      simpa only [concreteBase, List.getLast?_singleton, Option.mem_def,
        Option.some.injEq] using htip.symm
    subst tip
    rfl

theorem concreteDeploymentBase :
    CanonicalDeploymentBase concreteConfig pragueRules concreteBase
      concreteCreateSender concreteCreateTarget := by
  refine {
    configValid := ChainConfig.pragueOnly_valid 1
    chainId_eq := rfl
    validContext := concreteBase_validContext
    target_eq := ?_
    target_ne_zero := by decide +kernel
    target_not_precompile := ?_
    beacon_not_precompile := by decide +kernel
    history_not_precompile := by decide +kernel
    withdrawalRequest_not_precompile := by decide +kernel
    consolidationRequest_not_precompile := by decide +kernel
    sender_ne_target := by decide +kernel
    withdrawalRequest_ne_target := by decide +kernel
    consolidationRequest_ne_target := by decide +kernel
    target_noCodeOrNonce := by
      change accountHasCodeOrNonce concreteGenesisState _ = false
      simp only [accountHasCodeOrNonce, State.getNonce, State.getCode, concreteGenesisTarget]
      decide +kernel
    target_noStorage := by
      change accountHasStorage concreteGenesisState _ = false
      simp only [accountHasStorage, State.getStor, concreteGenesisTarget]
      decide +kernel
    target_zeroBalance := by
      change (concreteGenesisState.get concreteCreateTarget).bal = 0
      rw [concreteGenesisTarget]; rfl
    lastBlockHash := ?_
    beaconCode := concreteGenesisSystemCode _ (by decide +kernel)
    historyCode := concreteGenesisSystemCode _ (by decide +kernel)
    withdrawalRequestCode := concreteGenesisSystemCode _ (by decide +kernel)
    consolidationRequestCode := concreteGenesisSystemCode _ (by decide +kernel) }
  · have hn : concreteBase.state.getNonce concreteCreateSender = 0 := by
      change (concreteGenesisState.get concreteCreateSender).nonce = 0
      rw [concreteGenesisSender]; rfl
    rw [hn]
    exact concreteCreateAddress.symm
  · intro timestamp selected hrules
    have hr : selected = pragueRules := by
      exact (Except.ok.inj hrules).symm
    subst selected
    decide +kernel
  · exact ⟨concreteGenesisHeader.hash, rfl⟩

/-- Header fields read by execution; commitment fields are filled from the
actual block-body output in the final envelope. -/
def concreteExecutionHeader : Header :=
  { concreteGenesisHeader with
    parentHash := concreteGenesisHeader.hash
    number := 1
    gasUsed := 0
    timestamp := 1 }

theorem concreteCreateValidated :
    validateTransaction pragueRules concreteCreateTx =
      .ok (calculateIntrinsicCost concreteCreateTx) := by
  decide +kernel

theorem concreteCreateGasBound :
    deploymentTransactionGasBound concreteCreateTx ≤ concreteCreateTx.gas := by
  decide +kernel

theorem concreteCreateChecked :
    checkTransaction (initBenv pragueRules concreteBase concreteExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteCreateTx 0) concreteCreateTx =
      .ok (concreteCreateSender, 2, [], 0) := by
  have hgas : checkTransactionGasLimits
      (initBenv pragueRules concreteBase concreteExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteCreateTx 0) concreteCreateTx = .ok 0 := by decide +kernel
  have hchain : checkTransactionChainId
      (initBenv pragueRules concreteBase concreteExecutionHeader).beginTransaction
      concreteCreateTx = .ok () := by decide +kernel
  rw [checkTransaction, hgas]
  simp only [Except.mapError, bind, Except.bind]
  rw [hchain]
  change (do
    let sender ← Except.mapError TransitionError.senderRecovery (recoverSender 1 concreteCreateTx)
    let (effective, maxFee) ← Except.mapError TransitionError.transaction
      (checkTransactionGasFee (initBenv pragueRules concreteBase concreteExecutionHeader).beginTransaction concreteCreateTx)
    let (maxFee, hashes) ← Except.mapError TransitionError.transaction
      (checkTransactionBlobData (initBenv pragueRules concreteBase concreteExecutionHeader).beginTransaction concreteCreateTx maxFee)
    Except.mapError TransitionError.transaction (checkTransactionReceiver concreteCreateTx)
    Except.mapError TransitionError.transaction (checkTransactionAuthorizationList concreteCreateTx)
    Except.mapError TransitionError.transaction (checkTransactionSenderAccount (concreteGenesisState.get sender) concreteCreateTx maxFee)
    pure (sender, effective, hashes, 0)) = _
  rw [concreteCreateRecoveredSender]
  simp only [Except.mapError, bind, Except.bind, concreteGenesisSender]
  decide +kernel

end Drip
end Blanc
