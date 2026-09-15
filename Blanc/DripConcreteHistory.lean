-- DripConcreteHistory.lean : literal inputs for the configured deployment.
--
-- Off-chain tooling proposes fixed type-2 transaction bytes only.  Every
-- decoder, signature, address, header and transition equality used below is
-- proved by Lean; no fixture result is a theorem premise.

import Blanc.DripDeploy
import Blanc.RlpConcrete
import Blanc.DripRpow

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

/- The decoder and CREATE-address facts below feed the actual configured
deployment transition at the end of this module, without success assumptions. -/

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

theorem concreteCreateGasUsed : deploymentTransactionGasBound concreteCreateTx = 479909 := by
  decide +kernel

/-- The execution header with concrete gas accounting and independently
supplied commitment words. The final caller supplies actual body commitments. -/
def concreteDeploymentHeader (stateRoot txsRoot receiptRoot withdrawalsRoot requestsHash : B256) : Header :=
  { concreteExecutionHeader with
    gasUsed := 479909
    stateRoot := stateRoot
    txsRoot := txsRoot
    receiptRoot := receiptRoot
    withdrawalsRoot := withdrawalsRoot
    requestsHash := some requestsHash }

theorem concreteDeploymentHeader_benv (sr tr rr wr rh : B256) :
    initBenv pragueRules concreteBase (concreteDeploymentHeader sr tr rr wr rh) =
      initBenv pragueRules concreteBase concreteExecutionHeader := rfl

theorem concreteDeploymentHeader_decode (sr tr rr wr rh : B256) :
    (concreteDeploymentHeader sr tr rr wr rh).toBLT.toExHeader =
      .ok (concreteDeploymentHeader sr tr rr wr rh) := by
  have hc (name : String) : (0 : Adr).toBytes.toRlpAdr name = .ok 0 := by rfl
  have hb : Bytes.toRlpFixed "header bloom" 256 (List.replicate 256 0) =
      .ok (List.replicate 256 0) := by decide +kernel
  have h0b : Nat.toBytes 0 = [] := by simp [Nat.toBytes, Nat.toBytes.aux]
  have h1b : Nat.toBytes 1 = [1] := by simp [Nat.toBytes, Nat.toBytes.aux]
  have h0 (name : String) : (0 : Nat).toBytes.toRlpNat name 32 = .ok 0 := by rw [h0b]; rfl
  have h1 (name : String) : (1 : Nat).toBytes.toRlpNat name 32 = .ok 1 := by rw [h1b]; rfl
  have hl : (10000000 : Nat).toBytes.toRlpNat "header gasLimit" 32 = .ok 10000000 := by decide +kernel
  have hg : (479909 : Nat).toBytes.toRlpNat "header gasUsed" 32 = .ok 479909 := by decide +kernel
  have hn : (0 : UInt64).toBytes.toRlpFixedB64 "header nonce" = .ok 0 := by decide +kernel
  have h64 (name : String) : (0 : Nat).toBytes.toRlpB64 name = .ok 0 := by rw [h0b]; rfl
  simp only [concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader,
    Header.toBLT, List.cons_append, List.nil_append, BLT.toExHeader,
    RlpConcrete.decode_hash, bind, Except.bind, Except.map, hc, hb, h0, h1, hl, hg, hn, h64]
  rfl

theorem concreteDeploymentHeader_valid (sr tr rr wr rh : B256) :
    validateHeader pragueRules concreteBase (concreteDeploymentHeader sr tr rr wr rh) =
      .ok () := by
  simp only [validateHeader, concreteBase, concreteGenesisBlock,
    List.getLast?_singleton, Option.toExcept, bind, Except.bind,
    concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader,
    Header.hash, ne_eq, not_true_eq_false, ite_false]
  decide +kernel

def concreteHeaderFields (sr tr rr wr rh : B256) : List BLT :=
  [.bytes concreteGenesisHeader.hash.toBytes, .bytes emptyOmmerHash.toBytes,
   .bytes (0 : Adr).toBytes, .bytes sr.toBytes, .bytes tr.toBytes, .bytes rr.toBytes,
   .bytes (List.replicate 256 0), .bytes [], .bytes [1],
   .bytes [0x98, 0x96, 0x80], .bytes [7, 0x52, 0xa5], .bytes [1], .bytes [],
   .bytes (0 : B256).toBytes, .bytes (0 : UInt64).toBytes, .bytes [1],
   .bytes wr.toBytes, .bytes [], .bytes [], .bytes (0 : B256).toBytes, .bytes rh.toBytes]

theorem concreteHeaderBLT (sr tr rr wr rh : B256) :
    (concreteDeploymentHeader sr tr rr wr rh).toBLT = .list (concreteHeaderFields sr tr rr wr rh) := by
  simp [-List.reduceReplicate, concreteDeploymentHeader, concreteExecutionHeader, Header.toBLT,
    concreteGenesisHeader, concreteHeaderFields, Nat.toBytes, Nat.toBytes.aux]

def concreteHeaderPayload (sr tr rr wr rh : B256) : Bytes :=
  [0xa0] ++ concreteGenesisHeader.hash.toBytes ++ [0xa0] ++ emptyOmmerHash.toBytes ++
  [0x94] ++ (0 : Adr).toBytes ++ [0xa0] ++ sr.toBytes ++ [0xa0] ++ tr.toBytes ++
  [0xa0] ++ rr.toBytes ++ [0xb9, 1, 0] ++ List.replicate 256 0 ++
  [0x80, 1, 0x83, 0x98, 0x96, 0x80, 0x83, 7, 0x52, 0xa5, 1, 0x80, 0xa0] ++
  (0 : B256).toBytes ++ [0x88] ++ (0 : UInt64).toBytes ++ [1, 0xa0] ++ wr.toBytes ++
  [0x80, 0x80, 0xa0] ++ (0 : B256).toBytes ++ [0xa0] ++ rh.toBytes

theorem concreteHeaderPayload_length (sr tr rr wr rh : B256) :
    (concreteHeaderPayload sr tr rr wr rh).length = 601 := by
  simp only [concreteHeaderPayload, List.length_append, List.length_cons, List.length_nil,
    B256.length_toBytes, List.length_replicate, UInt64.length_toBytes]
  rfl

theorem concreteHeaderPayloadEncoded (sr tr rr wr rh : B256) :
    BLTs.toBytesJoin (concreteHeaderFields sr tr rr wr rh) =
      concreteHeaderPayload sr tr rr wr rh := by
  have hw (word : B256) : (BLT.bytes word.toBytes).toBytes = 0xa0 :: word.toBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by rw [B256.length_toBytes]; decide)]
    simp [B256.length_toBytes]
  have ha : (BLT.bytes (0 : Adr).toBytes).toBytes = 0x94 :: (0 : Adr).toBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by decide +kernel)]
    rfl
  have hn : (BLT.bytes (0 : UInt64).toBytes).toBytes = 0x88 :: (0 : UInt64).toBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by decide +kernel)]
    rfl
  have hb : (BLT.bytes (List.replicate 256 0)).toBytes =
      [0xb9, 1, 0] ++ List.replicate 256 0 := by
    rw [RlpConcrete.encode_bytes_many _ (by simp only [List.length_replicate]; decide)]
    simp [-List.reduceReplicate, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux]
  unfold concreteHeaderFields concreteHeaderPayload
  generalize concreteGenesisHeader.hash = parentHash
  simp only [BLTs.toBytesJoin, hw, ha, hn, hb]
  simp only [BLT.toBytes]
  simp [-List.reduceReplicate, List.append_assoc]

theorem concreteHeaderEncoded (sr tr rr wr rh : B256) :
    (concreteDeploymentHeader sr tr rr wr rh).toBLT.toBytes =
      [0xf9, 2, 0x59] ++ concreteHeaderPayload sr tr rr wr rh := by
  rw [concreteHeaderBLT, BLT.toBytes, BLTs.toBytes, concreteHeaderPayloadEncoded,
    concreteHeaderPayload_length]
  simp only [show ¬ (601 < 56) from by decide, if_false]
  have hpack : Nat.toBytesPack 601 = [2, 0x59] := by
    simp [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux]
  rw [hpack]
  rfl

theorem concreteHeaderPayloadParse (k : Nat) (sr tr rr wr rh : B256) :
    Bytes.toBLTs? (k + 21) (concreteHeaderPayload sr tr rr wr rh) =
      some (concreteHeaderFields sr tr rr wr rh) := by
  unfold concreteHeaderPayload concreteHeaderFields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 (k + 20) _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 (k + 19) _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short (k + 18) 20 _ _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 (k + 17) _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 (k + 16) _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 (k + 15) _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_two (k + 14) 1 0 _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes (k + 13) _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte (k + 12) 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three (k + 11) [0x98, 0x96, 0x80] _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three (k + 10) [7, 0x52, 0xa5] _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte (k + 9) 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes (k + 8) _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 (k + 7) _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short (k + 6) 8 _ _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte (k + 5) 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 (k + 4) _ _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes (k + 3) _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes (k + 2) _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 (k + 1) _ _ rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil] using RlpConcrete.decode_bytes_32 k rh.toBytes [] rfl
  rw [Bytes.toBLTs?]

theorem concreteCreateTxRlp_length : concreteCreateTxRlp.length = 2086 := by
  rw [concreteCreateEncoded]
  simp only [List.length_append, List.length_cons, List.length_nil,
    concreteCreatePayload_length]

theorem concreteTxStringEncoded : (BLT.bytes concreteCreateTxRlp).toBytes =
    [0xb9, 8, 0x26] ++ concreteCreateTxRlp := by
  rw [RlpConcrete.encode_bytes_many _ (by rw [concreteCreateTxRlp_length]; decide),
    concreteCreateTxRlp_length]
  have hp : Nat.toBytesPack 2086 = [8, 0x26] := by
    simp [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux]
  simp only [show ¬ (2086 < 56) from by decide, if_false, hp]
  rfl

theorem concreteTxListEncoded : (BLT.list [.bytes concreteCreateTxRlp]).toBytes =
    [0xf9, 8, 0x29, 0xb9, 8, 0x26] ++ concreteCreateTxRlp := by
  rw [BLT.toBytes, BLTs.toBytes]
  simp only [BLTs.toBytesJoin, concreteTxStringEncoded, List.append_nil,
    List.length_append, List.length_cons, List.length_nil, concreteCreateTxRlp_length]
  have hp : Nat.toBytesPack 2089 = [8, 0x29] := by
    simp [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux]
  simp only [show ¬ (3 + 2086 < 56) from by decide, if_false, hp]
  rfl

def concreteDeploymentBlock (sr tr rr wr rh : B256) : Block :=
  { header := concreteDeploymentHeader sr tr rr wr rh,
    txs := [.inl concreteCreateTxRlp], ommers := [], wds := [] }

def concreteBlockPayload (sr tr rr wr rh : B256) : Bytes :=
  [0xf9, 2, 0x59] ++ concreteHeaderPayload sr tr rr wr rh ++
  [0xf9, 8, 0x29, 0xb9, 8, 0x26] ++ concreteCreateTxRlp ++ [0xc0, 0xc0]

theorem concreteBlockPayload_length (sr tr rr wr rh : B256) :
    (concreteBlockPayload sr tr rr wr rh).length = 2698 := by
  simp only [concreteBlockPayload, List.length_append, List.length_cons,
    List.length_nil, concreteHeaderPayload_length, concreteCreateTxRlp_length]

theorem concreteBlockEncoded (sr tr rr wr rh : B256) :
    (concreteDeploymentBlock sr tr rr wr rh).toBLT.toBytes =
      [0xf9, 0x0a, 0x8a] ++ concreteBlockPayload sr tr rr wr rh := by
  have hpayload : BLTs.toBytesJoin
      [(concreteDeploymentHeader sr tr rr wr rh).toBLT,
       .list [.bytes concreteCreateTxRlp], .list [], .list []] =
      concreteBlockPayload sr tr rr wr rh := by
    simp only [BLTs.toBytesJoin, concreteHeaderEncoded, concreteTxListEncoded]
    have he : (BLT.list []).toBytes = [0xc0] := by rw [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin]; rfl
    rw [he]
    simp only [concreteBlockPayload, List.append_assoc, List.cons_append, List.nil_append]
  simp only [concreteDeploymentBlock, Block.toBLT, List.map_cons, List.map_nil, B8LOrTxToBLT]
  rw [BLT.toBytes, BLTs.toBytes, hpayload, concreteBlockPayload_length]
  have hp : Nat.toBytesPack 2698 = [0x0a, 0x8a] := by
    simp [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux]
  simp only [show ¬ (2698 < 56) from by decide, if_false, hp]
  rfl

theorem concreteHeaderDiff (k : Nat) (sr tr rr wr rh : B256) (tail : Bytes) :
    Bytes.toBLTDiff? (k + 22)
      (0xf9 :: 2 :: 0x59 :: (concreteHeaderPayload sr tr rr wr rh ++ tail)) =
      some ((concreteDeploymentHeader sr tr rr wr rh).toBLT, tail) := by
  rw [concreteHeaderBLT]
  exact RlpConcrete.decode_list_long_two (k + 21) 2 0x59 _ _ _
    (by rw [concreteHeaderPayload_length]; rfl) (concreteHeaderPayloadParse k sr tr rr wr rh)

theorem concreteTxListDiff (k : Nat) (tail : Bytes) :
    Bytes.toBLTDiff? (k + 2)
      (0xf9 :: 8 :: 0x29 :: 0xb9 :: 8 :: 0x26 :: (concreteCreateTxRlp ++ tail)) =
      some (.list [.bytes concreteCreateTxRlp], tail) := by
  have hparse : Bytes.toBLTs? (k + 1) (0xb9 :: 8 :: 0x26 :: concreteCreateTxRlp) =
      some [.bytes concreteCreateTxRlp] := by
    apply RlpConcrete.parse_cons
    · simpa only [List.append_nil] using
        RlpConcrete.decode_bytes_long_two k 8 0x26 concreteCreateTxRlp []
          (by rw [concreteCreateTxRlp_length]; rfl)
    rw [Bytes.toBLTs?]
  exact RlpConcrete.decode_list_long_two (k + 1) 8 0x29
    (0xb9 :: 8 :: 0x26 :: concreteCreateTxRlp) tail _
    (by simp only [List.length_cons, concreteCreateTxRlp_length]; rfl) hparse

theorem concreteBlockPayloadParse (k : Nat) (sr tr rr wr rh : B256) :
    Bytes.toBLTs? (k + 24) (concreteBlockPayload sr tr rr wr rh) =
      some [(concreteDeploymentHeader sr tr rr wr rh).toBLT,
        .list [.bytes concreteCreateTxRlp], .list [], .list []] := by
  unfold concreteBlockPayload
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact concreteHeaderDiff (k + 2) sr tr rr wr rh _
  apply RlpConcrete.parse_cons
  · exact concreteTxListDiff (k + 21) _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_list (k + 21) _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_list (k + 20) _
  rw [Bytes.toBLTs?]

theorem concreteBlockParse (sr tr rr wr rh : B256) :
    Bytes.toBLT? ([0xf9, 0x0a, 0x8a] ++ concreteBlockPayload sr tr rr wr rh) =
      some (concreteDeploymentBlock sr tr rr wr rh).toBLT := by
  have hp := RlpConcrete.decode_list_long_two 2700 0x0a 0x8a
    (concreteBlockPayload sr tr rr wr rh) []
    [(concreteDeploymentHeader sr tr rr wr rh).toBLT,
      .list [.bytes concreteCreateTxRlp], .list [], .list []]
    (by rw [concreteBlockPayload_length]; rfl)
    (concreteBlockPayloadParse 2676 sr tr rr wr rh)
  simp only [List.append_nil] at hp
  unfold Bytes.toBLT?
  simp only [List.length_cons, concreteBlockPayload_length,
    List.cons_append, List.nil_append]
  rw [hp]
  rfl

theorem concreteBlockDecode (sr tr rr wr rh : B256) :
    rlpToBlock ([0xf9, 0x0a, 0x8a] ++ concreteBlockPayload sr tr rr wr rh) =
      .ok (concreteDeploymentBlock sr tr rr wr rh,
        (concreteDeploymentHeader sr tr rr wr rh).hash) := by
  rw [rlpToBlock, rlpToBlockE, concreteBlockParse]
  simp only [Option.toExcept, bind, Except.bind, concreteDeploymentBlock, Block.toBLT,
    List.map_cons, List.map_nil, B8LOrTxToBLT, BLT.toExBlock,
    concreteDeploymentHeader_decode, List.mapM_cons, List.mapM_nil]
  change Except.mapError DecodeError.render
    (if [0xf9, 0x0a, 0x8a] ++ concreteBlockPayload sr tr rr wr rh ≠
      (concreteDeploymentBlock sr tr rr wr rh).toBLT.toBytes then _ else _) = _
  rw [concreteBlockEncoded]
  simp only [ne_eq, not_true_eq_false, if_false, Except.mapError]
  rfl

def concreteCanonicalBlock (sr tr rr wr rh : B256) : CanonicalBlock :=
  CanonicalBlock.ofDecode (concreteBlockDecode sr tr rr wr rh)

theorem concreteCanonicalEnvelope (sr tr rr wr rh : B256) :
    CanonicalDripDeploymentBlock concreteConfig pragueRules concreteBase
      (concreteCanonicalBlock sr tr rr wr rh) concreteCreateTxRlp concreteCreateTx
      concreteCreateSender concreteCreateTarget := by
  refine {
    txs_eq := rfl
    decode_eq := concreteCreateDecode
    ommers_eq := rfl
    withdrawals_eq := rfl
    rulesAt := ChainConfig.pragueOnly_rulesAt 1 _
    type_eq := ⟨1, 8, rfl⟩
    value_eq := rfl
    data_eq := rfl
    nonce_eq := ?_
    nonce_not_max := by decide +kernel
    recoveredSender := concreteCreateRecoveredSender
    validated := concreteCreateValidated
    checked := ?_
    base_fee_le_effective := ?_
    upfront_funded := ?_
    gas_bound := concreteCreateGasBound
    runtime_code_fits := by decide +kernel
    block_gas_room := by change 500000 ≤ 10000000; decide
    timestamp_ne_zero := by change (1 : Nat).toB256 ≠ 0; decide +kernel
    coinbase_ne_target := by change (0 : Adr) ≠ concreteCreateTarget; decide +kernel
    target_eq := concreteCreateAddress.symm }
  · change 0 = (concreteGenesisState.get concreteCreateSender).nonce
    rw [concreteGenesisSender]
    rfl
  · change checkTransaction
      (initBenv pragueRules concreteBase (concreteDeploymentHeader sr tr rr wr rh)).beginTransaction
      (deploymentTxPreludeBout .init concreteCreateTx 0) concreteCreateTx =
      .ok (concreteCreateSender,
        deploymentEffectiveGasPrice (initBenv pragueRules concreteBase
          (concreteDeploymentHeader sr tr rr wr rh)) concreteCreateTx, [], 0)
    rw [concreteDeploymentHeader_benv]
    exact concreteCreateChecked
  · change 1 ≤ 2
    decide
  · change 500000 * 2 ≤ (concreteGenesisState.get concreteCreateSender).bal.toNat
    rw [concreteGenesisSender]
    decide +kernel

private theorem concreteDeploymentBody_exists : ∃ output : State × BlockOutput,
    applyBody (initBenv pragueRules concreteBase concreteExecutionHeader)
      [.inl concreteCreateTxRlp] [] = .ok output ∧
    output.2.blockGasUsed = 479909 ∧ output.2.blockLogs = [] ∧ output.2.blobGasUsed = 0 := by
  let preview := concreteCanonicalBlock 0 0 0 0 0
  have henv := concreteCanonicalEnvelope 0 0 0 0 0
  obtain ⟨ctx⟩ := prepareCanonicalDeploymentContext concreteConfig pragueRules concreteBase
    preview concreteCreateTx concreteCreateSender concreteCreateTarget concreteDeploymentBase henv
  obtain ⟨post, bout, htx⟩ := canonicalDeploymentTransaction_succeeds concreteConfig pragueRules
    concreteBase preview concreteCreateTx concreteCreateSender concreteCreateTarget
    concreteDeploymentBase henv ctx
  obtain ⟨suffix⟩ := canonicalDeploymentSuffix_succeeds concreteConfig pragueRules concreteBase
    preview concreteCreateTx concreteCreateSender concreteCreateTarget concreteDeploymentBase
    ctx post bout htx
  have hrun := canonicalDeploymentApplyBody_succeeds concreteConfig pragueRules concreteBase
    preview concreteCreateTxRlp concreteCreateTx concreteCreateSender concreteCreateTarget
    henv ctx post bout htx suffix
  change applyBody (initBenv pragueRules concreteBase (concreteDeploymentHeader 0 0 0 0 0))
    [.inl concreteCreateTxRlp] [] = .ok (post, bout) at hrun
  rw [concreteDeploymentHeader_benv] at hrun
  exact ⟨(post, bout), hrun, htx.blockGasUsed.trans concreteCreateGasUsed,
    htx.blockLogs, htx.blobGasUsed⟩

/-- A name for the actual successful body output. Its existence comes from
the constructor execution proof above, and its run equation fixes it uniquely. -/
noncomputable def concreteDeploymentBody : State × BlockOutput :=
  Classical.choose concreteDeploymentBody_exists

theorem concreteDeploymentBody_run :
    applyBody (initBenv pragueRules concreteBase concreteExecutionHeader)
      [.inl concreteCreateTxRlp] [] = .ok concreteDeploymentBody :=
  (Classical.choose_spec concreteDeploymentBody_exists).1

theorem concreteDeploymentBody_gas : concreteDeploymentBody.2.blockGasUsed = 479909 :=
  (Classical.choose_spec concreteDeploymentBody_exists).2.1

theorem concreteDeploymentBody_logs : concreteDeploymentBody.2.blockLogs = [] :=
  (Classical.choose_spec concreteDeploymentBody_exists).2.2.1

theorem concreteDeploymentBody_blobGas : concreteDeploymentBody.2.blobGasUsed = 0 :=
  (Classical.choose_spec concreteDeploymentBody_exists).2.2.2

noncomputable def concreteDeploymentEnvelope : CanonicalBlock :=
  concreteCanonicalBlock concreteDeploymentBody.1.root
    (getTransactionsRoot concreteDeploymentBody.2) (getReceiptRoot concreteDeploymentBody.2)
    (getWithdrawalsRoot concreteDeploymentBody.2) (computeRequestsHash concreteDeploymentBody.2.requests)

noncomputable def concreteDeployed : BlockChain :=
  ⟨appendBlock concreteBase.blocks concreteDeploymentEnvelope.block,
    concreteDeploymentBody.1, concreteBase.chainId⟩

theorem concreteDeploymentBody_finalHeader :
    applyBody (initBenv pragueRules concreteBase concreteDeploymentEnvelope.block.header)
      concreteDeploymentEnvelope.block.txs concreteDeploymentEnvelope.block.wds =
      .ok concreteDeploymentBody := by
  change applyBody (initBenv pragueRules concreteBase (concreteDeploymentHeader _ _ _ _ _))
    [.inl concreteCreateTxRlp] [] = .ok concreteDeploymentBody
  rw [concreteDeploymentHeader_benv]
  exact concreteDeploymentBody_run

theorem concreteDeploymentChecks :
    stateTransitionChecks concreteDeploymentBody.2 concreteDeploymentEnvelope.block.header
      (getTransactionsRoot concreteDeploymentBody.2) concreteDeploymentBody.1.root
      (getReceiptRoot concreteDeploymentBody.2) (logsBloom concreteDeploymentBody.2.blockLogs)
      (getWithdrawalsRoot concreteDeploymentBody.2)
      (computeRequestsHash concreteDeploymentBody.2.requests) = .ok () := by
  simp only [stateTransitionChecks, concreteDeploymentBody_gas, concreteDeploymentBody_logs,
    concreteDeploymentBody_blobGas, concreteDeploymentEnvelope, concreteCanonicalBlock,
    CanonicalBlock.ofDecode, concreteDeploymentBlock, concreteDeploymentHeader,
    concreteExecutionHeader, concreteGenesisHeader, logsBloom, List.foldl_nil,
    ne_eq, not_true_eq_false, ite_false, pure, Bind.bind, Except.bind]
  rfl

theorem concreteDeploymentStep :
    stateTransitionUsing concreteConfig concreteBase concreteDeploymentEnvelope.block =
      .ok concreteDeployed := by
  rw [stateTransitionUsing_eq_of_chainId_eq concreteDeploymentBase.chainId_eq]
  rw [show concreteConfig.rulesAt concreteDeploymentEnvelope.block.header.timestamp =
    .ok pragueRules from ChainConfig.pragueOnly_rulesAt 1 _]
  change stateTransitionWith pragueRules concreteBase concreteDeploymentEnvelope.block = _
  rw [stateTransitionWith_eq_ok_iff, stateTransitionE]
  have hheader : validateHeader pragueRules concreteBase concreteDeploymentEnvelope.block.header =
      .ok () := concreteDeploymentHeader_valid _ _ _ _ _
  rw [hheader]
  change (do
    let output ← applyBody (initBenv pragueRules concreteBase concreteDeploymentEnvelope.block.header)
      concreteDeploymentEnvelope.block.txs concreteDeploymentEnvelope.block.wds
    Except.mapError TransitionError.block (stateTransitionChecks output.2
      concreteDeploymentEnvelope.block.header (getTransactionsRoot output.2) output.1.root
      (getReceiptRoot output.2) (logsBloom output.2.blockLogs) (getWithdrawalsRoot output.2)
      (computeRequestsHash output.2.requests))
    .ok (⟨appendBlock concreteBase.blocks concreteDeploymentEnvelope.block,
      output.1, concreteBase.chainId⟩ : BlockChain)) = .ok concreteDeployed
  rw [concreteDeploymentBody_finalHeader]
  simp only [Bind.bind, Except.bind, concreteDeploymentChecks, Except.mapError]
  rfl

/-- The configured private genesis actually deploys the strict signed envelope. -/
theorem concreteDeploymentRoot :
    DeploymentRoot concreteConfig concreteBase concreteDeployed concreteCreateTarget :=
  canonicalDeploymentStep_establishes_root concreteConfig pragueRules concreteBase concreteDeployed
    concreteDeploymentEnvelope concreteCreateTxRlp concreteCreateTx concreteCreateSender
    concreteCreateTarget concreteDeploymentBase (concreteCanonicalEnvelope _ _ _ _ _)
    concreteDeploymentStep

/-- The standard retained trace of the actual deployment body. -/
noncomputable def concreteDeploymentTrace :
    ExecutionTrace.AppliedBodyTrace
      (initBenv pragueRules concreteBase concreteDeploymentEnvelope.block.header)
      concreteDeploymentEnvelope.block.txs concreteDeploymentEnvelope.block.wds
      concreteDeploymentBody.1 concreteDeploymentBody.2 :=
  Classical.choice (ExecutionTrace.exists_appliedBodyTrace concreteDeploymentBody_finalHeader)

theorem concreteDeploymentStateForm :
    ∃ ctx : PreparedDeploymentContext concreteConfig pragueRules concreteBase
        (concreteCanonicalBlock 0 0 0 0 0) concreteCreateTx concreteCreateSender concreteCreateTarget,
      ∃ entry : Benv,
        (processCreateMessage.msg ctx.msg).benvAfterTransfer = .ok entry ∧
        concreteDeployed.state = deploymentFinalState ctx.txInput concreteCreateTx concreteCreateSender
          (constructorInstalledState entry.state concreteCreateTarget ctx.msg.benv.stat.time)
          (deploymentTransactionGasBound concreteCreateTx) := by
  let preview := concreteCanonicalBlock 0 0 0 0 0
  have henv := concreteCanonicalEnvelope 0 0 0 0 0
  obtain ⟨ctx⟩ := prepareCanonicalDeploymentContext concreteConfig pragueRules concreteBase
    preview concreteCreateTx concreteCreateSender concreteCreateTarget concreteDeploymentBase henv
  obtain ⟨post, bout, htx⟩ := canonicalDeploymentTransaction_succeeds concreteConfig pragueRules
    concreteBase preview concreteCreateTx concreteCreateSender concreteCreateTarget
    concreteDeploymentBase henv ctx
  obtain ⟨suffix⟩ := canonicalDeploymentSuffix_succeeds concreteConfig pragueRules concreteBase
    preview concreteCreateTx concreteCreateSender concreteCreateTarget concreteDeploymentBase
    ctx post bout htx
  have hrun := canonicalDeploymentApplyBody_succeeds concreteConfig pragueRules concreteBase
    preview concreteCreateTxRlp concreteCreateTx concreteCreateSender concreteCreateTarget
    henv ctx post bout htx suffix
  change applyBody (initBenv pragueRules concreteBase (concreteDeploymentHeader 0 0 0 0 0))
    [.inl concreteCreateTxRlp] [] = .ok (post, bout) at hrun
  rw [concreteDeploymentHeader_benv] at hrun
  have hpost : post = concreteDeployed.state :=
    congrArg Prod.fst (Except.ok.inj (hrun.symm.trans concreteDeploymentBody_run))
  obtain ⟨entry, hentry, hstate⟩ := htx.state
  exact ⟨ctx, entry, hentry, hpost.symm.trans hstate⟩

def concreteDeploymentDebit : State :=
  let nonceState := concreteGenesisState.incrNonce concreteCreateSender
  nonceState.setBal concreteCreateSender (nonceState.bal concreteCreateSender - 1000000)

def concreteConstructorPrepared : State :=
  (concreteDeploymentDebit.setStor concreteCreateTarget .empty).incrNonce concreteCreateTarget

def concreteConstructorEntry : State :=
  (concreteConstructorPrepared.setBal concreteCreateSender
    (concreteConstructorPrepared.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0

/-- A finite update expression for the actual deployed world, including fees. -/
def concreteDeploymentState : State :=
  deploymentFinalState (initBenv pragueRules concreteBase concreteExecutionHeader)
    concreteCreateTx concreteCreateSender
    (constructorInstalledState concreteConstructorEntry concreteCreateTarget 1) 479909

theorem concreteDeployed_state : concreteDeployed.state = concreteDeploymentState := by
  obtain ⟨ctx, entry, hentry, hstate⟩ := concreteDeploymentStateForm
  have hdebit := (State.of_subBal ctx.debit_eq).2
  have hbegun : ctx.begun.state = concreteGenesisState := by
    rw [ctx.begun_eq]
    change ctx.txInput.state = concreteGenesisState
    exact ctx.systemPrefix.state_eq
  have hprice : deploymentEffectiveGasPrice ctx.txInput concreteCreateTx = 2 := by
    rw [ctx.systemPrefix.environment_eq]
    rfl
  have hdebitEq : ctx.debit = concreteDeploymentDebit := by
    rw [hbegun, hprice] at hdebit
    exact hdebit
  obtain ⟨mid, hsub, hentryEq⟩ := of_benvAfterTransfer
    (msg := processCreateMessage.msg ctx.msg) ctx.msg_shouldTransferValue_eq hentry
  have hmid := (State.of_subBal hsub).2
  have hprepared : (processCreateMessage.msg ctx.msg).benv.state = concreteConstructorPrepared := by
    change (ctx.msg.benv.state.setStor ctx.msg.currentTarget .empty).incrNonce ctx.msg.currentTarget = _
    rw [ctx.msg_benv_eq]
    simp only [ctx.target_eq]
    rw [hdebitEq]
    rfl
  have hentryState : entry.state = concreteConstructorEntry := by
    rw [hentryEq]
    change mid.addBal ctx.msg.currentTarget ctx.msg.value = _
    rw [hmid]
    change (((processCreateMessage.msg ctx.msg).benv.state.setBal ctx.msg.caller
      ((processCreateMessage.msg ctx.msg).benv.state.bal ctx.msg.caller - ctx.msg.value)).addBal
      ctx.msg.currentTarget ctx.msg.value) = _
    rw [hprepared, ctx.msg_caller_eq, ctx.msg_value_eq]
    simp only [ctx.target_eq]
    rfl
  rw [hstate, hentryState, ctx.msg_time_eq, ctx.systemPrefix.environment_eq, concreteCreateGasUsed]
  rfl

theorem concreteDeployedSenderNonce : concreteDeployed.state.getNonce concreteCreateSender = 1 := by
  rw [concreteDeployed_state]
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  change ((((constructorInstalledState concreteConstructorEntry concreteCreateTarget 1).addBal
    concreteCreateSender 40182).addBal 0 479909).get concreteCreateSender).nonce = 1
  simp only [constructorInstalledState, constructorStoredState, concreteConstructorEntry,
    concreteConstructorPrepared, concreteDeploymentDebit, State.addBal, State.setBal,
    State.setCode, State.setStorVal, State.setStor, State.incrNonce,
    State.get_set_self, State.get_set_ne _ ht, State.get_set_ne _ hz, concreteGenesisSender]
  decide +kernel

theorem concreteDeployedSenderBalance :
    concreteDeployed.state.bal concreteCreateSender = 999999999999040182 := by
  rw [concreteDeployed_state]
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  change ((((constructorInstalledState concreteConstructorEntry concreteCreateTarget 1).addBal
    concreteCreateSender 40182).addBal 0 479909).get concreteCreateSender).bal = 999999999999040182
  simp only [constructorInstalledState, constructorStoredState, concreteConstructorEntry,
    concreteConstructorPrepared, concreteDeploymentDebit, State.addBal, State.setBal,
    State.setCode, State.setStorVal, State.setStor, State.incrNonce, State.bal,
    State.get_set_self, State.get_set_ne _ ht, State.get_set_ne _ hz, concreteGenesisSender]
  decide +kernel

theorem concreteDeployedCode (address : Adr) (hne : concreteCreateTarget ≠ address) :
    concreteDeployed.state.getCode address = concreteGenesisState.getCode address := by
  rw [concreteDeployed_state]
  unfold concreteDeploymentState deploymentFinalState
  rw [State.addBal_getCode, State.addBal_getCode]
  simp only [constructorInstalledState, constructorStoredState, concreteConstructorEntry,
    concreteConstructorPrepared, concreteDeploymentDebit, State.getCode,
    State.addBal, State.setBal_get_code, State.incrNonce_get_code,
    State.setStor_get_code, State.setCode_get_code_ne hne,
    State.setStorVal, State.get_set_ne _ hne]

theorem concreteDeployedSystemCode (address : Adr)
    (ha : address ∈ [beaconRootsAddress, historyStorageAddress,
      withdrawalRequestPredeployAddress, consolidationRequestPredeployAddress]) :
    some (concreteDeployed.state.getCode address).toList = Prog.compile deploymentSystemProgram := by
  have hne : concreteCreateTarget ≠ address := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel
  rw [concreteDeployedCode address hne]
  exact concreteGenesisSystemCode address ha

/-- The first post-deployment transaction spends the actual sender's nonce 1. -/
def concreteJoinTx : Tx := {
  nonce := 1
  gas := 500000
  value := 100
  data := [0xb6, 0x88, 0xa3, 0x63]
  v := 1
  r := (0x72cf3fe1ef8a8e6f2fde1aa9a41a2754761d914e2305a9ec3f20efeb74414849 : B256).toBytes
  s := (0x179411568d74fce909f6fbbcffc9ad904712032504d81974e5e8d2ca2566f6d9 : B256).toBytes
  type := .two 1 1 8 (some concreteCreateTarget) [] }

def concreteJoinSigningPayload : Bytes :=
  [0x02, 0xe4, 1, 1, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++
  concreteCreateTarget.toBytes ++ [100, 0x84, 0xb6, 0x88, 0xa3, 0x63, 0xc0]

theorem concreteJoinSigningEncoded :
    concreteJoinTx.signingHash = some concreteJoinSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have ht : (BLT.bytes concreteCreateTarget.toBytes).toBytes =
      0x94 :: concreteCreateTarget.toBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by decide +kernel)]
    rfl
  have hlen : concreteCreateTarget.toBytes.length = 20 := rfl
  simp only [Tx.signingHash, concreteJoinTx, hc, AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  change 2 :: (BLT.list [.bytes [1], .bytes [1], .bytes (Nat.toBytes 1),
    .bytes (Nat.toBytes 8), .bytes (Nat.toBytes 500000), .bytes concreteCreateTarget.toBytes,
    .bytes (Nat.toBytes 100), .bytes [0xb6, 0x88, 0xa3, 0x63], .list []]).toBytes = _
  simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, ht, hlen,
    Nat.toBytes, Nat.toBytes.aux, concreteJoinSigningPayload]

theorem concreteJoinSigningHash :
    concreteJoinTx.signingHash =
      some (0xf0f9b2fc39cd89c110c7e4b3aa0188dabe8d5d989db1caad9c03ed226fc5357e : B256) := by
  rw [concreteJoinSigningEncoded]
  decide +kernel

theorem concreteJoinRecoveredSender :
    recoverSender 1 concreteJoinTx = .ok concreteCreateSender := by
  rw [recoverSender, concreteJoinSigningHash]
  decide +kernel

def concreteJoinFields : List BLT :=
  [.bytes [1], .bytes [1], .bytes [1], .bytes [8], .bytes [7, 0xa1, 0x20],
   .bytes concreteCreateTarget.toBytes, .bytes [100], .bytes [0xb6, 0x88, 0xa3, 0x63],
   .list [], .bytes [1], .bytes concreteJoinTx.r, .bytes concreteJoinTx.s]

def concreteJoinPayload : Bytes :=
  [1, 1, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++ concreteCreateTarget.toBytes ++
  [100, 0x84, 0xb6, 0x88, 0xa3, 0x63, 0xc0, 1, 0xa0] ++ concreteJoinTx.r ++
  [0xa0] ++ concreteJoinTx.s

def concreteJoinTxRlp : Bytes := [2, 0xf8, 0x67] ++ concreteJoinPayload

theorem concreteJoinBLT : concreteJoinTx.toBLT = .list concreteJoinFields := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hr : trimZero concreteJoinTx.r = concreteJoinTx.r := by decide +kernel
  have hs : trimZero concreteJoinTx.s = concreteJoinTx.s := by decide +kernel
  simp only [Tx.toBLT, concreteJoinTx, hc, AccessList.toBLT, List.map_nil]
  simp [concreteJoinFields, concreteJoinTx, Nat.toBytes, Nat.toBytes.aux]
  exact ⟨hr, hs⟩

theorem concreteJoinPayloadParse (k : Nat) :
    Bytes.toBLTs? (k + 12) concreteJoinPayload = some concreteJoinFields := by
  unfold concreteJoinPayload concreteJoinFields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 8 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [7, 0xa1, 0x20] _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 _ _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 100 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 [0xb6, 0x88, 0xa3, 0x63] _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_list _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 _ _ _ rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil] using RlpConcrete.decode_bytes_32 k concreteJoinTx.s [] rfl
  rw [Bytes.toBLTs?]

theorem concreteJoinPayload_length : concreteJoinPayload.length = 103 := by
  simp only [concreteJoinPayload, List.length_append, List.length_cons, List.length_nil]
  rfl

theorem concreteJoinEnvelopeParse :
    Bytes.toBLT? (0xf8 :: 0x67 :: concreteJoinPayload) = some (.list concreteJoinFields) := by
  have hsplit : Jaune.List.splitAt? 103 concreteJoinPayload = some (concreteJoinPayload, []) := by
    simpa only [concreteJoinPayload_length, List.append_nil] using
      RlpConcrete.splitAt_append concreteJoinPayload ([] : Bytes)
  have hp : Bytes.toBLTDiff? 105 (0xf8 :: 0x67 :: concreteJoinPayload) =
      some (.list concreteJoinFields, []) := by
    rw [Bytes.toBLTDiff?]
    change (do
      let p ← Jaune.List.splitAt? 1 ([0x67] ++ concreteJoinPayload)
      let q ← Jaune.List.splitAt? (Bytes.toNat p.1) p.2
      let rs ← Bytes.toBLTs? 104 q.1
      pure (BLT.list rs, q.2)) = _
    rw [show Jaune.List.splitAt? 1 ([0x67] ++ concreteJoinPayload) =
      some ([0x67], concreteJoinPayload) from
        RlpConcrete.splitAt_append [0x67] concreteJoinPayload]
    change (do
      let q ← Jaune.List.splitAt? 103 concreteJoinPayload
      let rs ← Bytes.toBLTs? 104 q.1
      pure (BLT.list rs, q.2)) = _
    rw [hsplit]
    change (do let rs ← Bytes.toBLTs? 104 concreteJoinPayload; pure (BLT.list rs, [])) = _
    rw [concreteJoinPayloadParse 92]
    rfl
  unfold Bytes.toBLT?
  simp only [List.length_cons, concreteJoinPayload_length]
  rw [hp]

theorem concreteJoinDecode : decodeTx (.inl concreteJoinTxRlp) = .ok concreteJoinTx := by
  simp only [decodeTx, concreteJoinTxRlp, List.cons_append, List.nil_append,
    Bytes.toExTx, concreteJoinEnvelopeParse, concreteJoinFields]
  rfl

noncomputable def concreteJoinExecutionHeader : Header :=
  { concreteDeploymentEnvelope.block.header with
    parentHash := concreteDeploymentEnvelope.block.header.hash
    number := 2
    gasUsed := 0
    timestamp := 2 }

theorem concreteDeployedSenderCode :
    concreteDeployed.state.getCode concreteCreateSender = ByteArray.empty := by
  rw [concreteDeployedCode concreteCreateSender (by decide +kernel)]
  change (concreteGenesisState.get concreteCreateSender).code = _
  rw [concreteGenesisSender]
  rfl

theorem concreteJoinSenderChecked :
    checkTransactionSenderAccount (concreteDeployed.state.get concreteCreateSender)
      concreteJoinTx 4000000 = .ok () := by
  have hn : (concreteDeployed.state.get concreteCreateSender).nonce = 1 := concreteDeployedSenderNonce
  have hb : (concreteDeployed.state.get concreteCreateSender).bal = 999999999999040182 :=
    concreteDeployedSenderBalance
  have hc : (concreteDeployed.state.get concreteCreateSender).code = ByteArray.empty :=
    concreteDeployedSenderCode
  simp only [checkTransactionSenderAccount, hn, hb, checkTransactionSenderCode, hc]
  decide +kernel

theorem concreteJoinValidated :
    validateTransaction pragueRules concreteJoinTx = .ok (calculateIntrinsicCost concreteJoinTx) := by
  decide +kernel

theorem concreteJoinChecked :
    checkTransaction (initBenv pragueRules concreteDeployed concreteJoinExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteJoinTx 0) concreteJoinTx =
      .ok (concreteCreateSender, 2, [], 0) := by
  have hgas : checkTransactionGasLimits
      (initBenv pragueRules concreteDeployed concreteJoinExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteJoinTx 0) concreteJoinTx = .ok 0 := by decide +kernel
  have hchain : checkTransactionChainId
      (initBenv pragueRules concreteDeployed concreteJoinExecutionHeader).beginTransaction
      concreteJoinTx = .ok () := by decide +kernel
  have hfee : checkTransactionGasFee
      (initBenv pragueRules concreteDeployed concreteJoinExecutionHeader).beginTransaction
      concreteJoinTx = .ok (2, 4000000) := by decide +kernel
  rw [checkTransaction, hgas]
  simp only [Except.mapError, bind, Except.bind]
  rw [hchain]
  change (do
    let sender ← Except.mapError TransitionError.senderRecovery (recoverSender 1 concreteJoinTx)
    let (effective, maxFee) ← Except.mapError TransitionError.transaction
      (checkTransactionGasFee (initBenv pragueRules concreteDeployed concreteJoinExecutionHeader).beginTransaction concreteJoinTx)
    let (maxFee, hashes) ← Except.mapError TransitionError.transaction
      (checkTransactionBlobData (initBenv pragueRules concreteDeployed concreteJoinExecutionHeader).beginTransaction concreteJoinTx maxFee)
    Except.mapError TransitionError.transaction (checkTransactionReceiver concreteJoinTx)
    Except.mapError TransitionError.transaction (checkTransactionAuthorizationList concreteJoinTx)
    Except.mapError TransitionError.transaction (checkTransactionSenderAccount (concreteDeployed.state.get sender) concreteJoinTx maxFee)
    pure (sender, effective, hashes, 0)) = _
  rw [concreteJoinRecoveredSender, hfee]
  change (do
    Except.mapError TransitionError.transaction
      (checkTransactionSenderAccount (concreteDeployed.state.get concreteCreateSender) concreteJoinTx 4000000)
    pure (concreteCreateSender, 2, [], 0)) = _
  rw [concreteJoinSenderChecked]
  rfl

noncomputable def concreteJoinTxInput : Benv :=
  initBenv pragueRules concreteDeployed concreteJoinExecutionHeader

noncomputable def concreteJoinDebit : State :=
  let nonceState := concreteDeployed.state.incrNonce concreteCreateSender
  nonceState.setBal concreteCreateSender (nonceState.bal concreteCreateSender - 1000000)

theorem concreteJoinDebit_run :
    (concreteJoinTxInput.beginTransaction.state.incrNonce concreteCreateSender).subBal
      concreteCreateSender 1000000 = some concreteJoinDebit := by
  have hb : (concreteDeployed.state.incrNonce concreteCreateSender).bal concreteCreateSender =
      999999999999040182 := by
    unfold State.bal
    rw [State.incrNonce_get_bal]
    exact concreteDeployedSenderBalance
  change (concreteDeployed.state.incrNonce concreteCreateSender).subBal concreteCreateSender
    1000000 = _
  unfold State.subBal
  rw [hb, if_neg (by decide +kernel)]
  unfold concreteJoinDebit
  dsimp only
  rw [hb]

noncomputable def concreteJoinTenv : Tenv :=
  deploymentTenv concreteJoinTxInput concreteJoinTx concreteCreateSender 0

noncomputable def concreteJoinMessage : Msg := {
  benv := { concreteJoinTxInput.beginTransaction with state := concreteJoinDebit }
  tenv := concreteJoinTenv
  caller := concreteCreateSender
  target := some concreteCreateTarget
  currentTarget := concreteCreateTarget
  gas := concreteJoinTenv.stat.gas
  value := 100
  data := concreteJoinTx.data
  code := concreteJoinDebit.getCode concreteCreateTarget
  codeAddress := some concreteCreateTarget
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := concreteJoinTenv.stat.accessListAddresses.insertMany
    (pragueRules.precompiles ++ [concreteCreateSender, concreteCreateTarget])
  accessedStorageKeys := concreteJoinTenv.stat.accessListStorageKeys
  disablePrecompiles := false }

theorem concreteJoinMessage_prepared :
    prepareMessage { concreteJoinTxInput.beginTransaction with state := concreteJoinDebit }
      concreteJoinTenv concreteJoinTx = .ok concreteJoinMessage := rfl

theorem concreteJoinMessage_code : concreteJoinMessage.code.toList = code := by
  change (concreteJoinDebit.getCode concreteCreateTarget).toList = code
  unfold concreteJoinDebit
  rw [State.setBal_getCode]
  change ((concreteDeployed.state.incrNonce concreteCreateSender).get concreteCreateTarget).code.toList = code
  rw [State.incrNonce_get_code]
  change (concreteDeployed.state.getCode concreteCreateTarget).toList = code
  rw [concreteDeploymentRoot.installed]
  simp [ByteArray.toList_eq_toList_data]

theorem concreteJoinDebit_balance :
    concreteJoinDebit.bal concreteCreateSender = 999999999998040182 := by
  unfold concreteJoinDebit
  change ((concreteDeployed.state.incrNonce concreteCreateSender).setBal concreteCreateSender
    ((concreteDeployed.state.incrNonce concreteCreateSender).bal concreteCreateSender - 1000000)).bal _ = _
  unfold State.bal
  rw [State.setBal_get_self, State.incrNonce_get_bal]
  change concreteDeployed.state.bal concreteCreateSender - 1000000 = _
  rw [concreteDeployedSenderBalance]
  decide +kernel

noncomputable def concreteJoinEntry : Benv :=
  concreteJoinMessage.benv.withState
    ((concreteJoinDebit.setBal concreteCreateSender
      (concreteJoinDebit.bal concreteCreateSender - 100)).addBal concreteCreateTarget 100)

theorem concreteJoinEntry_run :
    concreteJoinMessage.benvAfterTransfer = .ok concreteJoinEntry := by
  have hs : concreteJoinDebit.subBal concreteCreateSender 100 =
      some (concreteJoinDebit.setBal concreteCreateSender
        (concreteJoinDebit.bal concreteCreateSender - 100)) := by
    unfold State.subBal
    rw [concreteJoinDebit_balance, if_neg (by decide +kernel)]
  change (do
    let b ← (concreteJoinMessage.benv.subBal concreteCreateSender 100).toExcept _
    pure (b.addBal concreteCreateTarget 100)) = _
  unfold Benv.subBal
  change (do
    let b ← (do
      let st ← concreteJoinDebit.subBal concreteCreateSender 100
      some (concreteJoinMessage.benv.withState st)).toExcept _
    pure (b.addBal concreteCreateTarget 100)) = _
  rw [hs]
  rfl

theorem concreteJoinEntry_storage (address : Adr) :
    (concreteJoinEntry.state.get address).stor = (concreteDeployed.state.get address).stor := by
  change (((concreteJoinDebit.setBal _ _).addBal _ _).get address).stor = _
  unfold State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteJoinDebit
  dsimp only
  rw [State.setBal_get_stor, State.incrNonce_get_stor]

private theorem concreteJoin_dispatch (sevm : Sevm) (base post : Devm) (G : Nat)
    (hdata : sevm.data = concreteJoinTx.data)
    (hjoin : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G⟩) join post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
    (base.setMach ⟨[], Mem.empty, G + 113⟩) main post := by
  have hd : dripSelector = (0x9f678cca : B256) := by decide +kernel
  have hj : joinSelector = (0xb688a363 : B256) := by decide +kernel
  have hshift : Sevm.dataWord sevm 0 >>> B256.toNat 224 = joinSelector := by
    simp only [Sevm.dataWord, hdata, concreteJoinTx]
    decide +kernel
  func_run (1)
  simp only [hdata, concreteJoinTx]
  func_run (5) [joinSelector]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[joinSelector], Mem.empty, G + 113 - 27⟩) (dispatch tree) post
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[joinSelector], Mem.empty, G + 113 - 27⟩)
    (Ninst.dup 0 ::: Ninst.pushB256 dripSelector ::: Ninst.gt :::
      (dispatch (.fork (.fork (.leaf convertToAssetsSelector (nonpayable (exactCalldata 36 convertToAssets)))
          (.leaf exitSelector (nonpayable (exactCalldata 36 exit))))
        (.leaf convertToUnitsSelector (nonpayable (exactCalldata 36 convertToUnits)))) <?>
       dispatch (.fork (.leaf dripSelector (nonpayable (exactCalldata 4 drip)))
         (.leaf joinSelector (exactCalldata 4 join))))) post
  simp only [hd, hj]
  func_run (4) [0]
  func_run (11) [0, 1, 1]
  all_goals first
    | exact hjoin
    | (simp only [hdata, concreteJoinTx]; decide +kernel)

noncomputable def concreteJoinSevm : Sevm :=
  initSevm (concreteJoinMessage.withBenv concreteJoinEntry)

def concreteJoinStagingMemory : Mem :=
  (((Mem.empty.write 64 (100 : B256).toBytes).write 96 (0 : B256).toBytes).write
    128 (0 : B256).toBytes).write 32 (5 : B256).toBytes

def concreteJoinStagingBase (base : Devm) : Devm :=
  addAccessedStorageKey (addAccessedStorageKey base concreteCreateTarget
    concreteCreateSender.toB256) concreteCreateTarget totalUnitsSlot

private theorem concreteJoin_stage (base post : Devm) (G : Nat)
    (hrow : base.getStorVal concreteCreateTarget concreteCreateSender.toB256 = 0)
    (htotal : base.getStorVal concreteCreateTarget totalUnitsSlot = 0)
    (hcoldRow : (concreteCreateTarget, concreteCreateSender.toB256) ∉ base.accessedStorageKeys)
    (hcoldTotal : (concreteCreateTarget, totalUnitsSlot) ∉ base.accessedStorageKeys)
    (hfresh : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      ((concreteJoinStagingBase base).setMach ⟨[], concreteJoinStagingMemory, G⟩)
      freshStart post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], Mem.empty, G + 4327⟩) join post := by
  func_run (8) [9, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  func_run (1)
  simp only [Devm.getStorVal_setMach]
  change Func.RunCompiled _ concreteJoinSevm
    ((addAccessedStorageKey _ concreteCreateTarget concreteCreateSender.toB256).setMach
      ⟨[base.getStorVal concreteCreateTarget concreteCreateSender.toB256],
        Mem.empty.write 64 (100 : B256).toBytes, G + 4327 - 2141⟩) _ post
  rw [hrow]
  func_run (7) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteJoinSevm
    ((addAccessedStorageKey base concreteCreateTarget concreteCreateSender.toB256).setMach
      ⟨[totalUnitsSlot], (Mem.empty.write 64 (100 : B256).toBytes).write 96 (0 : B256).toBytes,
        G + 4327 - 2175⟩) _ post
  func_run (1)
  · change (concreteCreateTarget, totalUnitsSlot) ∉
      base.accessedStorageKeys.insert (concreteCreateTarget, concreteCreateSender.toB256)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by decide +kernel, hcoldTotal⟩
  change Func.RunCompiled _ concreteJoinSevm
    ((concreteJoinStagingBase base).setMach
      ⟨[base.getStorVal concreteCreateTarget totalUnitsSlot],
        (Mem.empty.write 64 (100 : B256).toBytes).write 96 (0 : B256).toBytes,
        G + 4327 - 4275⟩) _ post
  rw [htotal]
  func_run (6) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  func_run (3) [0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteJoinSevm
    ((concreteJoinStagingBase base).setMach ⟨[], concreteJoinStagingMemory, G + 4327 - 4315⟩)
    (.call freshStartSlot) post
  apply Func.runCompiled_call' (f := freshStart) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hfresh

theorem concreteDeployedRho : (concreteDeployed.state.getStor concreteCreateTarget).get rhoSlot = 1 := by
  rw [concreteDeployed_state]
  unfold concreteDeploymentState deploymentFinalState
  change (((((constructorInstalledState concreteConstructorEntry concreteCreateTarget 1).addBal _ _).addBal _ _).get
    concreteCreateTarget).stor).get rhoSlot = 1
  simp only [State.addBal, State.setBal_get_stor, constructorInstalledState,
    State.setCode_get_stor, constructorStoredState, State.setStorVal,
    State.get_set_self]
  exact Stor.get_set_self _ _ _

noncomputable def concreteJoinDevm : Devm :=
  initDevm (concreteJoinMessage.withBenv concreteJoinEntry)

theorem concreteJoinDevm_chi : concreteJoinDevm.getStorVal concreteCreateTarget chiSlot = scale := by
  change (concreteJoinEntry.state.get concreteCreateTarget).stor.get chiSlot = scale
  rw [concreteJoinEntry_storage]
  exact concreteDeploymentRoot.chi

theorem concreteJoinDevm_rho : concreteJoinDevm.getStorVal concreteCreateTarget rhoSlot = 1 := by
  change (concreteJoinEntry.state.get concreteCreateTarget).stor.get rhoSlot = 1
  rw [concreteJoinEntry_storage]
  exact concreteDeployedRho

theorem concreteJoinDevm_pie (k : B256) (hc : k ≠ chiSlot) (hr : k ≠ rhoSlot) :
    concreteJoinDevm.getStorVal concreteCreateTarget k = 0 := by
  change (concreteJoinEntry.state.get concreteCreateTarget).stor.get k = 0
  rw [concreteJoinEntry_storage]
  exact concreteDeploymentRoot.pie k hc hr

theorem concreteJoinDevm_cold (k : B256) :
    (concreteCreateTarget, k) ∉ concreteJoinDevm.accessedStorageKeys := by
  change (concreteCreateTarget, k) ∉ (∅ : Std.HashSet (Adr × B256))
  simp

theorem concreteJoin_factor_one : B256.rpow scale half rate 1 = rate := by
  rw [drip_word_rpow_unfold_nonzero (by decide : (1 : Nat) ≠ 0)]
  decide +kernel

/-- The exponent-one initialization leaves exponent zero at the loop entry. -/
private theorem concreteJoin_rpowZero (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hread : Bytes.toB256 (M.read 0 32).1 = 0)
    (hmem : (M.read 0 32).2 = M)
    (hcompose : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G⟩) composeFresh post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G + 34⟩) rpowLoop post := by
  func_run (1)
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mload_of (v := 0) (M := M) (c := 3) (G := G + 29)
      (s := []) rfl ?_ hread hmem ?_ (by decide)) ?_
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  simp only [Devm.setMach_setMach]
  func_run (2) [1]
  apply Func.runCompiled_call' (f := composeFresh) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hcompose

private theorem concreteJoin_readChi (base post : Devm) (M : Mem) (G : Nat) (next : Func)
    (hchi : base.getStorVal concreteCreateTarget chiSlot = scale)
    (hcold : (concreteCreateTarget, chiSlot) ∉ base.accessedStorageKeys)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      ((addAccessedStorageKey base concreteCreateTarget chiSlot).setMach ⟨[scale], M, G⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G + 2103⟩)
      (Ninst.pushB256 chiSlot ::: Ninst.sload ::: next) post := by
  func_run (2)
  change Func.RunCompiled _ concreteJoinSevm
    ((addAccessedStorageKey base concreteCreateTarget chiSlot).setMach
      ⟨[base.getStorVal concreteCreateTarget chiSlot], M, G + 2103 - 2103⟩) next post
  simpa only [hchi, Nat.add_sub_cancel] using htail

def concreteJoinClockMemory : Mem :=
  (concreteJoinStagingMemory.write 160 scale.toBytes).write 192 (2 : B256).toBytes

private theorem concreteJoin_stageClock (base post : Devm) (M C : Mem)
    (G : Nat) (next : Func)
    (hsize : M.size = 160)
    (hstore : M.write (storedChiWord * 32).toNat scale.toBytes = C)
    (hcsize : C.size = 192)
    (hread : Bytes.toB256 (C.read (storedChiWord * 32).toNat 32).1 = scale)
    (hmem : (C.read (storedChiWord * 32).toNat 32).2 = C)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], C.write 192 (2 : B256).toBytes, G⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[scale], M, G + 70⟩)
      (mstoreAt storedChiWord +++
        (Ninst.pushB256 scale ::: loadWord storedChiWord +++ Ninst.lt :::
          (.revert <?>
            (loadWord storedChiWord +++ Ninst.pushB256 maxChi ::: Ninst.lt :::
              (.revert <?> (Ninst.timestamp ::: mstoreAt nowWord +++ next)))))) post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (3) [0]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  change Func.RunCompiled _ concreteJoinSevm
    (base.setMach ⟨[], C.write 192 (2 : B256).toBytes, G + 70 - 70⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteJoin_stageElapsed (base post : Devm) (M E : Mem)
    (G : Nat) (next : Func)
    (hrho : base.getStorVal concreteCreateTarget rhoSlot = 1)
    (hcold : (concreteCreateTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hsize : M.size = 224)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 2)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hstore : M.write (exponentWord * 32).toNat (1 : B256).toBytes = E)
    (hesize : E.size = 224)
    (hexp : Bytes.toB256 (E.read (exponentWord * 32).toNat 32).1 = 1)
    (hemem : (E.read (exponentWord * 32).toNat 32).2 = E)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      ((addAccessedStorageKey base concreteCreateTarget rhoSlot).setMach ⟨[], E, G⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G + 2166⟩)
      (Ninst.pushB256 rhoSlot ::: Ninst.sload ::: Ninst.dup 0 :::
        loadWord nowWord +++ Ninst.lt :::
          (.revert <?> (loadWord nowWord +++ Ninst.sub :::
            mstoreAt exponentWord +++ loadWord exponentWord +++
            Ninst.pushB256 maxElapsed ::: Ninst.lt ::: (.revert <?> next)))) post := by
  func_run (2)
  change Func.RunCompiled _ concreteJoinSevm
    ((addAccessedStorageKey base concreteCreateTarget rhoSlot).setMach
      ⟨[base.getStorVal concreteCreateTarget rhoSlot], M, G + 2166 - 2103⟩) _ post
  rw [hrho]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (3) [1, 0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hesize]
    decide +kernel
  rw [hexp, hemem]
  func_run (3) [0]
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteJoin_initializeRpow (base post : Devm) (M B A Z : Mem)
    (G : Nat) (zeroBase zeroExponent evenExponent : Func)
    (hsize : M.size = 224)
    (hbase : M.write (baseWord * 32).toNat rate.toBytes = B)
    (hbsize : B.size = 256)
    (hbexp : Bytes.toB256 (B.read (exponentWord * 32).toNat 32).1 = 1)
    (hbmem : (B.read (exponentWord * 32).toNat 32).2 = B)
    (hacc : B.write (accumulatorWord * 32).toNat rate.toBytes = A)
    (hasize : A.size = 288)
    (haexp : Bytes.toB256 (A.read (exponentWord * 32).toNat 32).1 = 1)
    (hamem : (A.read (exponentWord * 32).toNat 32).2 = A)
    (hzero : A.write (exponentWord * 32).toNat (0 : B256).toBytes = Z)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], Z, G⟩) rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G + 122⟩)
      (Ninst.pushB256 rate ::: Ninst.dup 0 ::: mstoreAt baseWord +++ Ninst.iszero :::
        (zeroBase <?> (loadWord exponentWord +++ Ninst.iszero :::
          (zeroExponent <?> (loadWord exponentWord +++ Ninst.pushB256 1 ::: Ninst.and :::
            ((Ninst.pushB256 rate ::: mstoreAt accumulatorWord +++ loadWord exponentWord +++
              Ninst.pushB256 2 ::: Ninst.swap 0 ::: Ninst.div ::: mstoreAt exponentWord +++
              .call rpowLoopSlot) <?> evenExponent)))))) post := by
  func_run (4) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hbase]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (3) [1]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hacc]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [haexp, hamem]
  func_run (5) [0, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [hzero]
  apply Func.runCompiled_call' (f := rpowLoop) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hloop

def concreteJoinExponentMemory : Mem := concreteJoinClockMemory.write 0 (1 : B256).toBytes
def concreteJoinBaseMemory : Mem := concreteJoinExponentMemory.write 224 rate.toBytes
def concreteJoinAccumulatorMemory : Mem := concreteJoinBaseMemory.write 256 rate.toBytes
def concreteJoinRpowMemory : Mem := concreteJoinAccumulatorMemory.write 0 (0 : B256).toBytes

def concreteJoinFreshBase (base : Devm) : Devm :=
  addAccessedStorageKey (addAccessedStorageKey base concreteCreateTarget chiSlot)
    concreteCreateTarget rhoSlot

private theorem concreteJoin_stagingSize : concreteJoinStagingMemory.size = 160 := by decide +kernel

private theorem concreteJoin_chiMemoryFacts :
    (concreteJoinStagingMemory.write 160 scale.toBytes).size = 192 ∧
    Bytes.toB256 ((concreteJoinStagingMemory.write 160 scale.toBytes).read 160 32).1 = scale ∧
    ((concreteJoinStagingMemory.write 160 scale.toBytes).read 160 32).2 =
      concreteJoinStagingMemory.write 160 scale.toBytes := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_clockMemoryFacts : concreteJoinClockMemory.size = 224 ∧
    Bytes.toB256 (concreteJoinClockMemory.read 192 32).1 = 2 ∧
    (concreteJoinClockMemory.read 192 32).2 = concreteJoinClockMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_exponentMemoryFacts : concreteJoinExponentMemory.size = 224 ∧
    Bytes.toB256 (concreteJoinExponentMemory.read 0 32).1 = 1 ∧
    (concreteJoinExponentMemory.read 0 32).2 = concreteJoinExponentMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_baseMemoryFacts : concreteJoinBaseMemory.size = 256 ∧
    Bytes.toB256 (concreteJoinBaseMemory.read 0 32).1 = 1 ∧
    (concreteJoinBaseMemory.read 0 32).2 = concreteJoinBaseMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_accumulatorMemoryFacts : concreteJoinAccumulatorMemory.size = 288 ∧
    Bytes.toB256 (concreteJoinAccumulatorMemory.read 0 32).1 = 1 ∧
    (concreteJoinAccumulatorMemory.read 0 32).2 = concreteJoinAccumulatorMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteJoin_rpowMemorySize : concreteJoinRpowMemory.size = 288 := by
  decide +kernel

private theorem concreteJoin_rpowMemoryRead : Bytes.toB256 (concreteJoinRpowMemory.read 0 32).1 = 0 := by
  decide +kernel

private theorem concreteJoin_rpowMemoryUnchanged :
    (concreteJoinRpowMemory.read 0 32).2 = concreteJoinRpowMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteJoin_rpowMemorySize]
  decide +kernel

theorem concreteJoin_freshStart (base post : Devm) (G : Nat)
    (hchi : base.getStorVal concreteCreateTarget chiSlot = scale)
    (hrho : base.getStorVal concreteCreateTarget rhoSlot = 1)
    (hcoldChi : (concreteCreateTarget, chiSlot) ∉ base.accessedStorageKeys)
    (hcoldRho : (concreteCreateTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hcompose : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      ((concreteJoinFreshBase base).setMach ⟨[], concreteJoinRpowMemory, G⟩)
      composeFresh post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], concreteJoinStagingMemory, G + 34 + 122 + 2166 + 70 + 2103⟩)
      freshStart post := by
  apply concreteJoin_readChi _ _ _ _ _ hchi hcoldChi
  apply concreteJoin_stageClock (C := concreteJoinStagingMemory.write 160 scale.toBytes)
  · exact concreteJoin_stagingSize
  · rfl
  · exact concreteJoin_chiMemoryFacts.1
  · exact concreteJoin_chiMemoryFacts.2.1
  · exact concreteJoin_chiMemoryFacts.2.2
  apply concreteJoin_stageElapsed (E := concreteJoinExponentMemory)
  · exact hrho
  · change (concreteCreateTarget, rhoSlot) ∉ base.accessedStorageKeys.insert
      (concreteCreateTarget, chiSlot)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by decide +kernel, hcoldRho⟩
  · exact concreteJoin_clockMemoryFacts.1
  · exact concreteJoin_clockMemoryFacts.2.1
  · exact concreteJoin_clockMemoryFacts.2.2
  · rfl
  · exact concreteJoin_exponentMemoryFacts.1
  · exact concreteJoin_exponentMemoryFacts.2.1
  · exact concreteJoin_exponentMemoryFacts.2.2
  apply concreteJoin_initializeRpow (B := concreteJoinBaseMemory)
    (A := concreteJoinAccumulatorMemory) (Z := concreteJoinRpowMemory)
  · exact concreteJoin_exponentMemoryFacts.1
  · rfl
  · exact concreteJoin_baseMemoryFacts.1
  · exact concreteJoin_baseMemoryFacts.2.1
  · exact concreteJoin_baseMemoryFacts.2.2
  · rfl
  · exact concreteJoin_accumulatorMemoryFacts.1
  · exact concreteJoin_accumulatorMemoryFacts.2.1
  · exact concreteJoin_accumulatorMemoryFacts.2.2
  · rfl
  exact concreteJoin_rpowZero _ _ _ _ concreteJoin_rpowMemorySize
    concreteJoin_rpowMemoryRead concreteJoin_rpowMemoryUnchanged hcompose

private theorem concreteJoin_composeFresh (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hchi : Bytes.toB256 (M.read (storedChiWord * 32).toNat 32).1 = scale)
    (hchiMem : (M.read (storedChiWord * 32).toNat 32).2 = M)
    (hfactor : Bytes.toB256 (M.read (accumulatorWord * 32).toNat 32).1 = rate)
    (hfactorMem : (M.read (accumulatorWord * 32).toNat 32).2 = M)
    (hroute : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate], M, G⟩) freshRoute post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[], M, G + 104⟩) composeFresh post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [scale * rate, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [scale, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (3) [1, 0]
  func_run (7) [rate, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  apply Func.runCompiled_call' (f := freshRoute) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hroute

private theorem concreteJoin_freshRoute (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hroute : Bytes.toB256 (M.read (routeWord * 32).toNat 32).1 = routeJoin)
    (hmem : (M.read (routeWord * 32).toNat 32).2 = M)
    (hjoin : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate], M, G⟩) afterJoin post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate], M, G + 114⟩) freshRoute post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hroute, hmem]
  func_run (19) [0, 0, 0, 0, 1]
  simpa only [Nat.add_sub_cancel] using hjoin

def concreteJoinCommit : Func :=
  commitFresh +++ Ninst.caller ::: Ninst.sstore ::: Ninst.swap 0 :::
    Ninst.pushB256 totalUnitsSlot ::: Ninst.sstore :::
    mstoreAt 0 +++ returnMemoryRange 0 32

private theorem concreteJoin_afterJoin (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (harg : Bytes.toB256 (M.read (argumentWord * 32).toNat 32).1 = 100)
    (hargMem : (M.read (argumentWord * 32).toNat 32).2 = M)
    (hrow : Bytes.toB256 (M.read (rowWord * 32).toNat 32).1 = 0)
    (hrowMem : (M.read (rowWord * 32).toNat 32).2 = M)
    (htotal : Bytes.toB256 (M.read (totalWord * 32).toNat 32).1 = 0)
    (htotalMem : (M.read (totalWord * 32).toNat 32).2 = M)
    (hcommit : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate, 99, 99, 99], M, G⟩) concreteJoinCommit post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate], M, G + 96⟩) afterJoin post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [harg, hargMem]
  func_run (8) [100 * scale, 99, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hrow, hrowMem]
  func_run (5) [99, 0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [htotal, htotalMem]
  func_run (7) [99, 0]
  simpa only [Nat.add_sub_cancel, concreteJoinCommit] using hcommit

private theorem concreteJoin_commitFresh (base C R post : Devm) (M : Mem) (G : Nat)
    (next : Func)
    (hsize : M.size = 288)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 2)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hchiCost : sstoreCost concreteJoinSevm base chiSlot rate = 2900)
    (hchi : afterSstore concreteJoinSevm base chiSlot rate = C)
    (hrhoCost : sstoreCost concreteJoinSevm C rhoSlot 2 = 2900)
    (hrho : afterSstore concreteJoinSevm C rhoSlot 2 = R)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (R.setMach ⟨[99, 99, 99], M, G⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[rate, 99, 99, 99], M, G + 5812⟩)
      (commitFresh +++ next) post := by
  func_run (1)
  rw [show G + 5812 - 3 = (G + 2909) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := C.setMach ⟨[99, 99, 99], M, G + 2909⟩) ?_ ?_
  · simpa only [hchiCost, hchi] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := concreteJoinSevm)
        (base := base) (key := chiSlot) (value := rate)
        (stack := [99, 99, 99]) (memory := M) (G := G + 2909)
        (by rw [hchiCost]; simp only [gCallStipend]; omega) rfl)
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (1)
  rw [show G + 2909 - 9 = G + 2900 by omega]
  refine Func.RunCompiled.next (devm' := R.setMach ⟨[99, 99, 99], M, G⟩) ?_ ?_
  · simpa only [hrhoCost, hrho] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := concreteJoinSevm)
        (base := C) (key := rhoSlot) (value := 2)
        (stack := [99, 99, 99]) (memory := M) (G := G)
        (by rw [hrhoCost]; simp only [gCallStipend]; omega) rfl)
  exact htail

private def concreteJoinRpowImage : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt [] 64 (100 : B256).toBytes)
        96 (0 : B256).toBytes) 128 (0 : B256).toBytes) 32 (5 : B256).toBytes)
      160 scale.toBytes) 192 (2 : B256).toBytes) 0 (1 : B256).toBytes)
    224 rate.toBytes) 256 rate.toBytes) 0 (0 : B256).toBytes

private theorem concreteJoin_rpowReads : Mem.Reads concreteJoinRpowMemory concreteJoinRpowImage := by
  unfold concreteJoinRpowMemory concreteJoinAccumulatorMemory concreteJoinBaseMemory
    concreteJoinExponentMemory concreteJoinClockMemory concreteJoinStagingMemory concreteJoinRpowImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteJoin_originalStorage (key : B256) :
    getOrigStorVal concreteJoinSevm concreteCreateTarget key =
      (concreteDeployed.state.getStor concreteCreateTarget).get key := by
  rfl


private theorem concreteJoin_rpowRead_chi :
    Bytes.toB256 (concreteJoinRpowMemory.read 160 32).1 = scale := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 192 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_factor :
    Bytes.toB256 (concreteJoinRpowMemory.read 256 32).1 = rate := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_route :
    Bytes.toB256 (concreteJoinRpowMemory.read 32 32).1 = routeJoin := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 160 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_argument :
    Bytes.toB256 (concreteJoinRpowMemory.read 64 32).1 = 100 := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 32 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 128 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 96 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_row :
    Bytes.toB256 (concreteJoinRpowMemory.read 96 32).1 = 0 := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 32 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 128 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_total :
    Bytes.toB256 (concreteJoinRpowMemory.read 128 32).1 = 0 := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 32 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteJoin_rpowRead_now :
    Bytes.toB256 (concreteJoinRpowMemory.read 192 32).1 = 2 := by
  rw [concreteJoin_rpowReads.read]
  unfold concreteJoinRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

noncomputable def concreteJoinStorageBase : Devm :=
  concreteJoinFreshBase (concreteJoinStagingBase concreteJoinDevm)

private theorem concreteJoinStorageBase_storage (a : Adr) (k : B256) :
    concreteJoinStorageBase.getStorVal a k = concreteJoinDevm.getStorVal a k := rfl

private theorem concreteJoinStorageBase_warm (k : B256)
    (hk : k = chiSlot ∨ k = rhoSlot ∨ k = concreteCreateSender.toB256 ∨ k = totalUnitsSlot) :
    (concreteCreateTarget, k) ∈ concreteJoinStorageBase.accessedStorageKeys := by
  change (concreteCreateTarget, k) ∈
    (((concreteJoinDevm.accessedStorageKeys.insert
      (concreteCreateTarget, concreteCreateSender.toB256)).insert
      (concreteCreateTarget, totalUnitsSlot)).insert
      (concreteCreateTarget, chiSlot)).insert (concreteCreateTarget, rhoSlot)
  rcases hk with h | h | h | h <;> subst k <;> simp

noncomputable def concreteJoinChiBase : Devm :=
  (concreteJoinStorageBase.withRefundCounter 0).setStorVal concreteCreateTarget chiSlot rate

private theorem concreteJoin_chiStore :
    sstoreCost concreteJoinSevm concreteJoinStorageBase chiSlot rate = 2900 ∧
    afterSstore concreteJoinSevm concreteJoinStorageBase chiSlot rate = concreteJoinChiBase := by
  have ht : concreteJoinSevm.currentTarget = concreteCreateTarget := rfl
  have hw := concreteJoinStorageBase_warm chiSlot (Or.inl rfl)
  have hr : concreteJoinStorageBase.refundCounter = 0 := rfl
  have hc : sstoreValueCost scale scale rate = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter rate scale scale 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteJoin_originalStorage,
      concreteDeploymentRoot.chi, concreteJoinStorageBase_storage, concreteJoinDevm_chi, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteJoin_originalStorage,
      concreteDeploymentRoot.chi, concreteJoinStorageBase_storage, concreteJoinDevm_chi, hr, hf]
    rfl

private theorem concreteJoinChiBase_storage (k : B256) (h : chiSlot ≠ k) :
    concreteJoinChiBase.getStorVal concreteCreateTarget k =
      concreteJoinStorageBase.getStorVal concreteCreateTarget k := by
  change (Devm.getStor ((concreteJoinStorageBase.withRefundCounter 0).setStorVal
    concreteCreateTarget chiSlot rate) concreteCreateTarget).get k = _
  rw [setStorVal_getStor_self, Stor.get_set_ne _ h, Devm.withRefundCounter_getStor]
  rfl

noncomputable def concreteJoinRhoBase : Devm :=
  (concreteJoinChiBase.withRefundCounter 0).setStorVal concreteCreateTarget rhoSlot 2

private theorem concreteJoin_rhoStore :
    sstoreCost concreteJoinSevm concreteJoinChiBase rhoSlot 2 = 2900 ∧
    afterSstore concreteJoinSevm concreteJoinChiBase rhoSlot 2 = concreteJoinRhoBase := by
  have ht : concreteJoinSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, rhoSlot) ∈ concreteJoinChiBase.accessedStorageKeys := by
    rw [concreteJoinChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteJoinStorageBase_warm rhoSlot (Or.inr (Or.inl rfl))
  have hr : concreteJoinChiBase.refundCounter = 0 := rfl
  have hv : concreteJoinChiBase.getStorVal concreteCreateTarget rhoSlot = 1 := by
    rw [concreteJoinChiBase_storage _ (by decide +kernel), concreteJoinStorageBase_storage]
    exact concreteJoinDevm_rho
  have hc : sstoreValueCost 1 1 2 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter 2 1 1 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteJoin_originalStorage,
      concreteDeployedRho, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteJoin_originalStorage,
      concreteDeployedRho, hv, hr, hf]
    rfl

private theorem concreteJoinRhoBase_storage (k : B256) (hc : chiSlot ≠ k) (hr : rhoSlot ≠ k) :
    concreteJoinRhoBase.getStorVal concreteCreateTarget k = 0 := by
  change (Devm.getStor ((concreteJoinChiBase.withRefundCounter 0).setStorVal
    concreteCreateTarget rhoSlot 2) concreteCreateTarget).get k = _
  rw [setStorVal_getStor_self, Stor.get_set_ne _ hr, Devm.withRefundCounter_getStor]
  change concreteJoinChiBase.getStorVal concreteCreateTarget k = 0
  rw [concreteJoinChiBase_storage _ hc, concreteJoinStorageBase_storage]
  exact concreteJoinDevm_pie _ (Ne.symm hc) (Ne.symm hr)

noncomputable def concreteJoinRowBase : Devm :=
  (concreteJoinRhoBase.withRefundCounter 0).setStorVal
    concreteCreateTarget concreteCreateSender.toB256 99

private theorem concreteJoin_rowStore :
    sstoreCost concreteJoinSevm concreteJoinRhoBase concreteCreateSender.toB256 99 = 20000 ∧
    afterSstore concreteJoinSevm concreteJoinRhoBase concreteCreateSender.toB256 99 =
      concreteJoinRowBase := by
  have ht : concreteJoinSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, concreteCreateSender.toB256) ∈
      concreteJoinRhoBase.accessedStorageKeys := by
    rw [concreteJoinRhoBase, Devm.sstoreWarmBase_accessedStorageKeys,
      concreteJoinChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteJoinStorageBase_warm _ (Or.inr (Or.inr (Or.inl rfl)))
  have hr : concreteJoinRhoBase.refundCounter = 0 := rfl
  have ho : (concreteDeployed.state.getStor concreteCreateTarget).get
      concreteCreateSender.toB256 = 0 :=
    concreteDeploymentRoot.pie _ (by decide +kernel) (by decide +kernel)
  have hv := concreteJoinRhoBase_storage concreteCreateSender.toB256
    (by decide +kernel) (by decide +kernel)
  have hc : sstoreValueCost 0 0 99 = 20000 := by decide +kernel
  have hf : sstoreNewRefundCounter 99 0 0 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteJoin_originalStorage, ho, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteJoin_originalStorage, ho, hv, hr, hf]
    rfl

noncomputable def concreteJoinTotalBase : Devm :=
  (concreteJoinRowBase.withRefundCounter 0).setStorVal concreteCreateTarget totalUnitsSlot 99

private theorem concreteJoin_totalStore :
    sstoreCost concreteJoinSevm concreteJoinRowBase totalUnitsSlot 99 = 20000 ∧
    afterSstore concreteJoinSevm concreteJoinRowBase totalUnitsSlot 99 = concreteJoinTotalBase := by
  have ht : concreteJoinSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, totalUnitsSlot) ∈ concreteJoinRowBase.accessedStorageKeys := by
    rw [concreteJoinRowBase, Devm.sstoreWarmBase_accessedStorageKeys,
      concreteJoinRhoBase, Devm.sstoreWarmBase_accessedStorageKeys,
      concreteJoinChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteJoinStorageBase_warm _ (Or.inr (Or.inr (Or.inr rfl)))
  have hr : concreteJoinRowBase.refundCounter = 0 := rfl
  have ho : (concreteDeployed.state.getStor concreteCreateTarget).get totalUnitsSlot = 0 :=
    concreteDeploymentRoot.pie _ (by decide +kernel) (by decide +kernel)
  have hv : concreteJoinRowBase.getStorVal concreteCreateTarget totalUnitsSlot = 0 := by
    change (Devm.getStor ((concreteJoinRhoBase.withRefundCounter 0).setStorVal
      concreteCreateTarget concreteCreateSender.toB256 99) concreteCreateTarget).get totalUnitsSlot = _
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel :
      concreteCreateSender.toB256 ≠ totalUnitsSlot), Devm.withRefundCounter_getStor]
    exact concreteJoinRhoBase_storage _ (by decide +kernel) (by decide +kernel)
  have hc : sstoreValueCost 0 0 99 = 20000 := by decide +kernel
  have hf : sstoreNewRefundCounter 99 0 0 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteJoin_originalStorage, ho, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteJoin_originalStorage, ho, hv, hr, hf]
    rfl

private theorem concreteJoin_commitUnits (base P T : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hrowCost : sstoreCost concreteJoinSevm base concreteCreateSender.toB256 99 = 20000)
    (hrow : afterSstore concreteJoinSevm base concreteCreateSender.toB256 99 = P)
    (htotalCost : sstoreCost concreteJoinSevm P totalUnitsSlot 99 = 20000)
    (htotal : afterSstore concreteJoinSevm P totalUnitsSlot 99 = T) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (base.setMach ⟨[99, 99, 99], M, G + 40018⟩)
      (Ninst.caller ::: Ninst.sstore ::: Ninst.swap 0 :::
        Ninst.pushB256 totalUnitsSlot ::: Ninst.sstore :::
        mstoreAt 0 +++ returnMemoryRange 0 32)
      ((T.setMach ⟨[], M.write 0 (99 : B256).toBytes, G⟩).withOutput (99 : B256).toBytes) := by
  have hcaller : concreteJoinSevm.caller = concreteCreateSender := rfl
  func_run (1)
  rw [hcaller]
  rw [show G + 40018 - 2 = (G + 20016) + 20000 by omega]
  refine Func.RunCompiled.next (devm' := P.setMach ⟨[99, 99], M, G + 20016⟩) ?_ ?_
  · simpa only [hrowCost, hrow] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := concreteJoinSevm)
        (base := base) (key := concreteCreateSender.toB256) (value := 99)
        (stack := [99, 99]) (memory := M) (G := G + 20016)
        (by rw [hrowCost]; simp only [gCallStipend]; omega) rfl)
  func_run (2)
  rw [show G + 20016 - 6 = (G + 10) + 20000 by omega]
  refine Func.RunCompiled.next (devm' := T.setMach ⟨[99], M, G + 10⟩) ?_ ?_
  · simpa only [htotalCost, htotal] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := concreteJoinSevm)
        (base := P) (key := totalUnitsSlot) (value := 99)
        (stack := [99]) (memory := M) (G := G + 10)
        (by rw [htotalCost]; simp only [gCallStipend]; omega) rfl)
  func_run (4) [0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  have hnsize : (M.write 0 (99 : B256).toBytes).size = 288 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsize]; decide)]
    exact hsize
  have hnread : ((M.write 0 (99 : B256).toBytes).read 0 32).1 = (99 : B256).toBytes := by
    simpa only [B256.length_toBytes] using
      (Mem.read_write_zero M (ys := (99 : B256).toBytes) (by decide +kernel))
  have hnmem : ((M.write 0 (99 : B256).toBytes).read 0 32).2 = M.write 0 (99 : B256).toBytes := by
    apply Mem.read_snd_eq_self
    rw [hnsize]
    decide +kernel
  apply Func.runCompiled_return_of (G := G) (e := 0)
  · rfl
  · change calculateMemoryGasCost (memExtsSize (M.write 0 (99 : B256).toBytes).size [(0, 32)]) -
      calculateMemoryGasCost (M.write 0 (99 : B256).toBytes).size = 0
    rw [hnsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  · change (((M.write 0 (99 : B256).toBytes).read 0 32).1,
      T.setMach ⟨[], ((M.write 0 (99 : B256).toBytes).read 0 32).2, G⟩) = _
    rw [hnread, hnmem]

private theorem concreteJoin_rpowMemoryUnchangedAt (i : Nat) (h : i + 32 ≤ 288) :
    (concreteJoinRpowMemory.read i 32).2 = concreteJoinRpowMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteJoin_rpowMemorySize]
  exact memExtSize_of_le (by decide) h

noncomputable def concreteJoinRuntimePost (G : Nat) : Devm :=
  (concreteJoinTotalBase.setMach
    ⟨[], concreteJoinRpowMemory.write 0 (99 : B256).toBytes, G⟩).withOutput (99 : B256).toBytes

theorem concreteJoin_composedRun (G : Nat) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (concreteJoinStorageBase.setMach ⟨[], concreteJoinRpowMemory, G + 45830 + 96 + 114 + 104⟩)
      composeFresh (concreteJoinRuntimePost G) := by
  apply concreteJoin_composeFresh
  · exact concreteJoin_rpowMemorySize
  · exact concreteJoin_rpowRead_chi
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  · exact concreteJoin_rpowRead_factor
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  apply concreteJoin_freshRoute
  · exact concreteJoin_rpowMemorySize
  · exact concreteJoin_rpowRead_route
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  apply concreteJoin_afterJoin
  · exact concreteJoin_rpowMemorySize
  · exact concreteJoin_rpowRead_argument
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  · exact concreteJoin_rpowRead_row
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  · exact concreteJoin_rpowRead_total
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  unfold concreteJoinCommit
  rw [show G + 45830 = (G + 40018) + 5812 by omega]
  apply concreteJoin_commitFresh (C := concreteJoinChiBase) (R := concreteJoinRhoBase)
  · exact concreteJoin_rpowMemorySize
  · exact concreteJoin_rpowRead_now
  · exact concreteJoin_rpowMemoryUnchangedAt _ (by decide)
  · exact concreteJoin_chiStore.1
  · exact concreteJoin_chiStore.2
  · exact concreteJoin_rhoStore.1
  · exact concreteJoin_rhoStore.2
  exact concreteJoin_commitUnits _ concreteJoinRowBase concreteJoinTotalBase _ G
    concreteJoin_rpowMemorySize concreteJoin_rowStore.1 concreteJoin_rowStore.2
    concreteJoin_totalStore.1 concreteJoin_totalStore.2

theorem concreteJoin_runtime (G : Nat) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteJoinSevm
      (concreteJoinDevm.setMach ⟨[], Mem.empty, G + 55079⟩)
      main (concreteJoinRuntimePost G) := by
  rw [show G + 55079 = G + 45830 + 96 + 114 + 104 + 34 + 122 + 2166 + 70 + 2103 + 4327 + 113 by omega]
  apply concreteJoin_dispatch
  · rfl
  apply concreteJoin_stage
  · exact concreteJoinDevm_pie _ (by decide +kernel) (by decide +kernel)
  · exact concreteJoinDevm_pie _ (by decide +kernel) (by decide +kernel)
  · exact concreteJoinDevm_cold _
  · exact concreteJoinDevm_cold _
  apply concreteJoin_freshStart
  · exact concreteJoinDevm_chi
  · exact concreteJoinDevm_rho
  · change (concreteCreateTarget, chiSlot) ∉
      (concreteJoinDevm.accessedStorageKeys.insert
        (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)
    simp only [Std.HashSet.mem_insert, concreteJoinDevm_cold, or_false, not_or]
    exact ⟨by decide +kernel, by decide +kernel⟩
  · change (concreteCreateTarget, rhoSlot) ∉
      (concreteJoinDevm.accessedStorageKeys.insert
        (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)
    simp only [Std.HashSet.mem_insert, concreteJoinDevm_cold, or_false, not_or]
    exact ⟨by decide +kernel, by decide +kernel⟩
  exact concreteJoin_composedRun G

theorem concreteJoinDevm_gas : concreteJoinDevm.gasLeft = 478936 := by
  change 500000 - deploymentIntrinsicGas concreteJoinTx = 478936
  decide +kernel

theorem concreteJoin_program :
    Prog.RunCompiled concreteJoinSevm concreteJoinDevm runtime (concreteJoinRuntimePost 423856) := by
  apply Prog.runCompiled_intro (G := 423856 + 55079)
    (mid := concreteJoinDevm.setMach ⟨[], Mem.empty, 423856 + 55079⟩)
  · rw [concreteJoinDevm_gas]
    decide
  · rfl
  exact concreteJoin_runtime 423856

theorem concreteJoin_compiled : some concreteJoinSevm.code.toList = Prog.compile runtime := by
  change some concreteJoinMessage.code.toList = _
  rw [concreteJoinMessage_code, code_compile]

theorem concreteJoin_exec :
    exec (initEvm (concreteJoinMessage.withBenv concreteJoinEntry)) =
      .ok (concreteJoinRuntimePost 423856) :=
  Prog.exec_of_runCompiled concreteJoin_program concreteJoin_compiled

theorem concreteJoin_frameEntry :
    (Frame.ofCall concreteJoinMessage).enter =
      .run (initEvm (concreteJoinMessage.withBenv concreteJoinEntry)) := by
  have hnp : ¬ pragueRules.isPrecomp concreteCreateTarget :=
    concreteDeploymentBase.target_not_precompile (ChainConfig.pragueOnly_rulesAt 1 2)
  have he : executeCode.enter (concreteJoinMessage.withBenv concreteJoinEntry) =
      .inl (initEvm (concreteJoinMessage.withBenv concreteJoinEntry)) := by
    unfold executeCode.enter
    change (if !false && pragueRules.isPrecomp concreteCreateTarget then _ else _) = _
    simp only [Bool.not_false, Bool.true_and, hnp]
    rfl
  unfold Frame.enter Frame.ofCall
  rw [concreteJoinEntry_run]
  dsimp only
  rw [he]

private theorem concreteJoin_postError : (concreteJoinRuntimePost 423856).error = none := rfl

theorem concreteJoin_processMessage :
    processMessage concreteJoinMessage = .ok (concreteJoinRuntimePost 423856) := by
  unfold processMessage runFrame
  rw [concreteJoin_frameEntry]
  unfold Frame.settle Frame.settleMsg processMessage.settle executeCode.handleError
  simp only [concreteJoin_exec, concreteJoin_postError, Frame.ofCall, Option.isSome,
    Bool.false_eq_true, if_false, bind, Except.bind]

noncomputable def concreteJoinMessageState : State := (concreteJoinRuntimePost 423856).state

def concreteJoinMessageOutput : MsgCallOutput := {
  gasLeft := 423856
  refundCounter := 0
  logs := []
  accountsToDelete := .emptyWithCapacity
  error := none
  returnData := (99 : B256).toBytes }

theorem concreteJoin_messageCall :
    processMessageCall concreteJoinMessage = .ok (concreteJoinMessageState, concreteJoinMessageOutput) := by
  have htarget : concreteJoinMessage.target.isNone = false := rfl
  have hauths : concreteJoinMessage.tenv.stat.auths = [] := rfl
  have hcode : some concreteJoinMessage.code.toList = Prog.compile runtime := concreteJoin_compiled
  have hdelegation : getDelegatedCodeAddress concreteJoinMessage.code = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg (not_delegation_of_compile hcode)]
  have hrefund : (concreteJoinRuntimePost 423856).refundCounter = 0 := rfl
  unfold processMessageCall
  rw [htarget]
  unfold processMessageCall.call
  simp only [hauths, List.isEmpty, if_true, bind, Except.bind, hdelegation,
    concreteJoin_processMessage, Except.bimap, id_eq, concreteJoin_postError,
    Option.isNone, hrefund]
  rfl

noncomputable def concreteJoinTransactionState : State :=
  deploymentFinalState concreteJoinTxInput concreteJoinTx concreteCreateSender
    concreteJoinMessageState 76144

def concreteJoinTransactionBout : BlockOutput :=
  deploymentFinalBout .init concreteJoinTx 0 concreteJoinMessageOutput 76144

theorem concreteJoin_transaction :
    processTransaction concreteJoinTxInput .init concreteJoinTx 0 =
      .ok (concreteJoinTransactionState, concreteJoinTransactionBout) := by
  have hchecked := concreteJoinChecked
  change checkTransaction concreteJoinTxInput.beginTransaction
    (deploymentTxPreludeBout .init concreteJoinTx 0) concreteJoinTx =
      .ok (concreteCreateSender, 2, [], 0) at hchecked
  have hdebit := concreteJoinDebit_run
  simp only [Benv.beginTransaction] at hdebit
  have hprepare := concreteJoinMessage_prepared
  have hrules : concreteJoinTxInput.beginTransaction.stat.rules = pragueRules := rfl
  unfold processTransaction
  simp only [bind, Except.bind]
  rw [hrules, concreteJoinValidated]
  simp only [Except.mapError]
  simp only [deploymentTxPreludeBout, ExecutionTrace.transactionPreludeBout] at hchecked
  rw [hchecked]
  simp only [Tx.isTypeThree, Tx.accessList, TxType.accessList, Tx.auths,
    concreteJoinTx, Bool.false_eq_true, if_false, Nat.add_zero, Benv.beginTransaction]
  rw [show Nat.toB256 (500000 * 2) = 1000000 by decide +kernel, hdebit]
  simp only [Option.toExcept]
  simp only [concreteJoinTenv, deploymentTenv, deploymentIntrinsicGas, Benv.beginTransaction,
    concreteJoinTx] at hprepare
  simp only [List.map_nil, List.flatten_nil]
  simp only [deploymentEffectiveGasPrice] at hprepare ⊢
  have hprice : min 1 (8 - concreteJoinTxInput.stat.baseFeePerGas) +
      concreteJoinTxInput.stat.baseFeePerGas = 2 := by rfl
  rw [hprice] at hprepare
  simp only [hprepare, concreteJoin_messageCall]
  have hgas : max (500000 - 423856 - min ((500000 - 423856) / 5) 0)
      (calculateIntrinsicCost concreteJoinTx).2 = 76144 := by decide +kernel
  simp only [concreteJoinTx] at hgas
  simp only [concreteJoinMessageOutput]
  rw [show Int.toNat? 0 = some 0 by rfl]
  simp only [hgas]
  unfold concreteJoinTransactionState concreteJoinTransactionBout deploymentFinalState deploymentFinalBout
  simp only [deploymentEffectiveGasPrice, concreteJoinTx, concreteJoinMessageOutput, hprice]
  have hdelete : (Std.HashSet.emptyWithCapacity : AdrSet).toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    rfl
  rw [hdelete]
  simp only [List.foldl_nil]
  rfl

theorem concreteJoinTransactionCode (a : Adr) :
    concreteJoinTransactionState.getCode a = concreteDeployed.state.getCode a := by
  unfold concreteJoinTransactionState deploymentFinalState
  rw [State.addBal_getCode, State.addBal_getCode]
  unfold concreteJoinMessageState concreteJoinRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  change concreteJoinTotalBase.getCode a = _
  unfold concreteJoinTotalBase
  rw [Devm.setStorVal_getCode]
  change concreteJoinRowBase.getCode a = _
  unfold concreteJoinRowBase
  rw [Devm.setStorVal_getCode]
  change concreteJoinRhoBase.getCode a = _
  unfold concreteJoinRhoBase
  rw [Devm.setStorVal_getCode]
  change concreteJoinChiBase.getCode a = _
  unfold concreteJoinChiBase
  rw [Devm.setStorVal_getCode]
  change concreteJoinEntry.state.getCode a = _
  change ((concreteJoinDebit.setBal _ _).addBal _ _).getCode a = _
  rw [State.addBal_getCode, State.setBal_getCode]
  unfold concreteJoinDebit
  rw [State.setBal_getCode]
  change ((concreteDeployed.state.incrNonce concreteCreateSender).get a).code = _
  rw [State.incrNonce_get_code]
  rfl

theorem concreteJoin_receiptEntry :
    concreteJoinTransactionBout.receiptsTrie[deploymentReceiptKey 0]? =
      some (makeReceipt concreteJoinTx none 76144 []) := by
  change (BlockOutput.init.receiptsTrie.insert (deploymentReceiptKey 0)
    (makeReceipt concreteJoinTx none 76144 []))[deploymentReceiptKey 0]? = _
  rw [Std.TreeMap.getElem?_insert_self]

theorem concreteJoin_requestSuffix :
    processGeneralPurposeRequests (concreteJoinTxInput.withState concreteJoinTransactionState)
      concreteJoinTransactionBout = .ok (concreteJoinTransactionState, concreteJoinTransactionBout) := by
  have hcode (a : Adr) (ha : a ∈ [beaconRootsAddress, historyStorageAddress,
      withdrawalRequestPredeployAddress, consolidationRequestPredeployAddress]) :
      some (concreteJoinTransactionState.getCode a).toList = Prog.compile deploymentSystemProgram := by
    rw [concreteJoinTransactionCode]
    exact concreteDeployedSystemCode a ha
  obtain ⟨withdrawalOut, hw, _, _, _, _, hwr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (concreteJoinTxInput.withState concreteJoinTransactionState) withdrawalRequestPredeployAddress []
      (hcode _ (by simp)) (by change ¬ pragueRules.isPrecomp withdrawalRequestPredeployAddress; decide)
  obtain ⟨consolidationOut, hc, _, _, _, _, hcr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((concreteJoinTxInput.withState concreteJoinTransactionState).withState concreteJoinTransactionState)
      consolidationRequestPredeployAddress [] (hcode _ (by simp))
      (by change ¬ pragueRules.isPrecomp consolidationRequestPredeployAddress; decide)
  have hd : parseDepositRequests concreteJoinTransactionBout = .ok [] := by
    unfold parseDepositRequests
    have hk : concreteJoinTransactionBout.receiptKeys = [deploymentReceiptKey 0] := rfl
    rw [hk]
    simp
    rw [concreteJoin_receiptEntry]
    unfold makeReceipt
    rfl
  unfold processGeneralPurposeRequests
  rw [hd]
  simp only [List.length_nil, Nat.lt_irrefl, if_false, bind, Except.bind]
  rw [hw]
  simp only [hwr, List.length_nil, Nat.lt_irrefl, if_false]
  change (do
    let ⟨st, out⟩ ← processCheckedSystemTransaction
      ((concreteJoinTxInput.withState concreteJoinTransactionState).withState concreteJoinTransactionState)
      consolidationRequestPredeployAddress []
    if out.returnData.length > 0 then
      .ok (st, {concreteJoinTransactionBout with requests := concreteJoinTransactionBout.requests ++
        [consolidationRequestType ++ out.returnData]})
    else .ok (st, {concreteJoinTransactionBout with requests := concreteJoinTransactionBout.requests})) = _
  simp only [hc, bind, Except.bind, hcr, List.length_nil, Nat.lt_irrefl, if_false]
  rfl

theorem concreteJoin_body :
    applyBody concreteJoinTxInput [.inl concreteJoinTxRlp] [] =
      .ok (concreteJoinTransactionState, concreteJoinTransactionBout) := by
  obtain ⟨beaconOut, hb, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    concreteJoinTxInput beaconRootsAddress concreteJoinTxInput.stat.parentBeaconBlockRoot.toBytes
    (concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp beaconRootsAddress; decide)
  obtain ⟨historyOut, hh, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (concreteJoinTxInput.withState concreteDeployed.state) historyStorageAddress
    concreteDeploymentEnvelope.block.header.hash.toBytes
    (concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp historyStorageAddress; decide)
  have hl : (concreteJoinTxInput.withState concreteDeployed.state).stat.blockHashes.getLast? =
      some concreteDeploymentEnvelope.block.header.hash := by rfl
  have hi : (concreteJoinTxInput.withState concreteDeployed.state).withState concreteDeployed.state =
      concreteJoinTxInput := rfl
  unfold applyBody
  rw [hb]
  simp only [Except.mapError, bind, Except.bind]
  change (do
    let lastHash ← (concreteJoinTxInput.withState concreteDeployed.state).stat.blockHashes.getLast?.toExcept
      (TransitionError.internal (.invariant (.text "block hashes is empty")))
    let ⟨stHistory, _⟩ ← Except.mapError TransitionError.vm
      (processUncheckedSystemTransaction (concreteJoinTxInput.withState concreteDeployed.state)
        historyStorageAddress lastHash.toBytes)
    let ⟨benvTxs, boutTxs⟩ ← applyTransactions
      (← ([.inl concreteJoinTxRlp] : List (Bytes ⊕ Tx)).mapM decodeTx).putIndex
      ((concreteJoinTxInput.withState concreteDeployed.state).withState stHistory) .init
    let ⟨stWds, boutWds⟩ := processWithdrawals benvTxs boutTxs []
    processGeneralPurposeRequests (benvTxs.withState stWds) boutWds) = _
  rw [hl]
  simp only [Option.toExcept, hh, Except.mapError, bind, Except.bind]
  rw [show (concreteJoinTxInput.withState concreteDeployed.state).state =
    concreteDeployed.state from rfl, hi]
  simp only [List.mapM_cons, List.mapM_nil, concreteJoinDecode, pure, Except.pure, bind, Except.bind, List.putIndex, List.putIndex.aux,
    applyTransactions, concreteJoin_transaction]
  change processGeneralPurposeRequests (concreteJoinTxInput.withState concreteJoinTransactionState)
    concreteJoinTransactionBout = _
  exact concreteJoin_requestSuffix

noncomputable def concreteJoinHeader (sr tr rr wr rh : B256) : Header :=
  { concreteJoinExecutionHeader with
    gasUsed := 76144
    stateRoot := sr
    txsRoot := tr
    receiptRoot := rr
    withdrawalsRoot := wr
    requestsHash := some rh }

theorem concreteJoinHeader_benv (sr tr rr wr rh : B256) :
    initBenv pragueRules concreteDeployed (concreteJoinHeader sr tr rr wr rh) = concreteJoinTxInput := rfl

theorem concreteJoinHeader_valid (sr tr rr wr rh : B256) :
    validateHeader pragueRules concreteDeployed (concreteJoinHeader sr tr rr wr rh) = .ok () := by
  have hlast : concreteDeployed.blocks.getLast? = some concreteDeploymentEnvelope.block :=
    appendBlock_getLast? concreteBase.blocks concreteDeploymentEnvelope.block
  simp only [validateHeader, hlast, Option.toExcept, bind, Except.bind,
    concreteJoinHeader, concreteJoinExecutionHeader, Header.hash, ne_eq, not_true_eq_false, ite_false]
  simp only [concreteDeploymentEnvelope, concreteCanonicalBlock, CanonicalBlock.ofDecode,
    concreteDeploymentBlock, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader]
  decide +kernel

noncomputable def concreteJoinBlock : Block := {
  header := concreteJoinHeader concreteJoinTransactionState.root
    (getTransactionsRoot concreteJoinTransactionBout) (getReceiptRoot concreteJoinTransactionBout)
    (getWithdrawalsRoot concreteJoinTransactionBout) (computeRequestsHash concreteJoinTransactionBout.requests)
  txs := [.inl concreteJoinTxRlp]
  ommers := []
  wds := [] }

noncomputable def concreteJoined : BlockChain :=
  ⟨appendBlock concreteDeployed.blocks concreteJoinBlock, concreteJoinTransactionState, concreteDeployed.chainId⟩

theorem concreteJoin_checks :
    stateTransitionChecks concreteJoinTransactionBout concreteJoinBlock.header
      (getTransactionsRoot concreteJoinTransactionBout) concreteJoinTransactionState.root
      (getReceiptRoot concreteJoinTransactionBout) (logsBloom concreteJoinTransactionBout.blockLogs)
      (getWithdrawalsRoot concreteJoinTransactionBout)
      (computeRequestsHash concreteJoinTransactionBout.requests) = .ok () := by
  have hg : concreteJoinTransactionBout.blockGasUsed = 76144 := rfl
  have hl : concreteJoinTransactionBout.blockLogs = [] := rfl
  have hb : concreteJoinTransactionBout.blobGasUsed = 0 := rfl
  simp only [stateTransitionChecks, hg, hl, hb, concreteJoinBlock, concreteJoinHeader,
    concreteJoinExecutionHeader, concreteDeploymentEnvelope, concreteCanonicalBlock,
    CanonicalBlock.ofDecode, concreteDeploymentBlock, concreteDeploymentHeader,
    concreteExecutionHeader, concreteGenesisHeader, logsBloom, List.foldl_nil,
    ne_eq, not_true_eq_false, ite_false, pure, Bind.bind, Except.bind]
  rfl

theorem concreteJoin_step :
    stateTransitionUsing concreteConfig concreteDeployed concreteJoinBlock = .ok concreteJoined := by
  rw [stateTransitionUsing_eq_of_chainId_eq concreteDeploymentRoot.deployed_chainId]
  rw [show concreteConfig.rulesAt concreteJoinBlock.header.timestamp = .ok pragueRules from
    ChainConfig.pragueOnly_rulesAt 1 _]
  change stateTransitionWith pragueRules concreteDeployed concreteJoinBlock = _
  rw [stateTransitionWith_eq_ok_iff, stateTransitionE]
  have hh : validateHeader pragueRules concreteDeployed concreteJoinBlock.header = .ok () :=
    concreteJoinHeader_valid _ _ _ _ _
  rw [hh]
  change (do
    let output ← applyBody (initBenv pragueRules concreteDeployed concreteJoinBlock.header)
      concreteJoinBlock.txs concreteJoinBlock.wds
    Except.mapError TransitionError.block (stateTransitionChecks output.2
      concreteJoinBlock.header (getTransactionsRoot output.2) output.1.root
      (getReceiptRoot output.2) (logsBloom output.2.blockLogs)
      (getWithdrawalsRoot output.2) (computeRequestsHash output.2.requests))
    .ok (⟨appendBlock concreteDeployed.blocks concreteJoinBlock, output.1,
      concreteDeployed.chainId⟩ : BlockChain)) = .ok concreteJoined
  have hbody : applyBody (initBenv pragueRules concreteDeployed concreteJoinBlock.header)
      concreteJoinBlock.txs concreteJoinBlock.wds =
      .ok (concreteJoinTransactionState, concreteJoinTransactionBout) := by
    change applyBody (initBenv pragueRules concreteDeployed (concreteJoinHeader _ _ _ _ _))
      [.inl concreteJoinTxRlp] [] = _
    rw [concreteJoinHeader_benv]
    exact concreteJoin_body
  rw [hbody]
  simp only [Bind.bind, Except.bind, concreteJoin_checks, Except.mapError]
  rfl

theorem concreteJoined_storage : concreteJoined.state.getStor concreteCreateTarget =
    ((((concreteDeployed.state.getStor concreteCreateTarget).set chiSlot rate).set rhoSlot 2).set
      concreteCreateSender.toB256 99).set totalUnitsSlot 99 := by
  change concreteJoinTransactionState.getStor concreteCreateTarget = _
  unfold concreteJoinTransactionState deploymentFinalState State.getStor State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteJoinMessageState concreteJoinRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  change Devm.getStor concreteJoinTotalBase concreteCreateTarget = _
  unfold concreteJoinTotalBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteJoinRowBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteJoinRhoBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteJoinChiBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  have hs : Devm.getStor concreteJoinStorageBase concreteCreateTarget =
      (concreteDeployed.state.get concreteCreateTarget).stor := by
    change (concreteJoinEntry.state.get concreteCreateTarget).stor = _
    exact concreteJoinEntry_storage _
  rw [hs]

theorem concreteJoined_values :
    (concreteJoined.state.getStor concreteCreateTarget).get chiSlot = rate ∧
    (concreteJoined.state.getStor concreteCreateTarget).get rhoSlot = 2 ∧
    (concreteJoined.state.getStor concreteCreateTarget).get concreteCreateSender.toB256 = 99 ∧
    (concreteJoined.state.getStor concreteCreateTarget).get totalUnitsSlot = 99 := by
  rw [concreteJoined_storage]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel),
      Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  · exact Stor.get_set_self _ _ _

theorem concreteJoin_receiptSucceeded :
    (concreteJoinTransactionBout.receiptsTrie[deploymentReceiptKey 0]?).map
      (fun entry => entry.2.succeeded) = some true := by
  rw [concreteJoin_receiptEntry]
  rfl

private theorem concreteJoinMessageState_sender :
    concreteJoinMessageState.get concreteCreateSender = concreteJoinEntry.state.get concreteCreateSender := by
  unfold concreteJoinMessageState concreteJoinRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  change (((((concreteJoinEntry.state.setStorVal concreteCreateTarget chiSlot rate).setStorVal
    concreteCreateTarget rhoSlot 2).setStorVal concreteCreateTarget concreteCreateSender.toB256 99).setStorVal
    concreteCreateTarget totalUnitsSlot 99).get concreteCreateSender) = _
  simp only [State.setStorVal, State.get_set_ne _ ht]

theorem concreteJoinedSenderNonce : concreteJoined.state.getNonce concreteCreateSender = 2 := by
  change (concreteJoinTransactionState.get concreteCreateSender).nonce = _
  unfold concreteJoinTransactionState deploymentFinalState
  change (((concreteJoinMessageState.addBal concreteCreateSender 847712).addBal 0 76144).get
    concreteCreateSender).nonce = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  rw [concreteJoinMessageState_sender]
  change ((((concreteJoinDebit.setBal concreteCreateSender
    (concreteJoinDebit.bal concreteCreateSender - 100)).addBal concreteCreateTarget 100).get
    concreteCreateSender).nonce) = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  unfold concreteJoinDebit
  simp only [State.setBal_get_self, State.incrNonce, State.get_set_self]
  change (concreteDeployed.state.getNonce concreteCreateSender) + 1 = 2
  rw [concreteDeployedSenderNonce]
  rfl

theorem concreteJoinedSenderBalance : concreteJoined.state.bal concreteCreateSender = 999999999998887794 := by
  change (concreteJoinTransactionState.get concreteCreateSender).bal = _
  unfold concreteJoinTransactionState deploymentFinalState
  change (((concreteJoinMessageState.addBal concreteCreateSender 847712).addBal 0 76144).get
    concreteCreateSender).bal = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  change (concreteJoinMessageState.get concreteCreateSender).bal + 847712 = _
  rw [concreteJoinMessageState_sender]
  change ((((concreteJoinDebit.setBal concreteCreateSender
    (concreteJoinDebit.bal concreteCreateSender - 100)).addBal concreteCreateTarget 100).get
    concreteCreateSender).bal) + 847712 = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  change (concreteJoinDebit.bal concreteCreateSender - 100) + 847712 = _
  rw [concreteJoinDebit_balance]
  decide +kernel

theorem concreteJoinedCode (a : Adr) :
    concreteJoined.state.getCode a = concreteDeployed.state.getCode a := concreteJoinTransactionCode a

def concreteDripTx : Tx := {
  nonce := 2
  gas := 500000
  value := 0
  data := [0x9f, 0x67, 0x8c, 0xca]
  v := 1
  r := (0x54bbe7f6c75d559928c649a8d39736a680bb4e569d274ed61fc2e20098435621 : B256).toBytes
  s := (0x4e3417937e13aa8105714ddc0ab4591dc8359cb0a950cceeaa56ada642129272 : B256).toBytes
  type := .two 1 1 8 (some concreteCreateTarget) [] }

def concreteDripSigningPayload : Bytes :=
  [0x02, 0xe4, 1, 2, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++
  concreteCreateTarget.toBytes ++ [0x80, 0x84, 0x9f, 0x67, 0x8c, 0xca, 0xc0]

theorem concreteDripSigningEncoded :
    concreteDripTx.signingHash = some concreteDripSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 2).sig = [2] := by decide +kernel
  have ht : (BLT.bytes concreteCreateTarget.toBytes).toBytes =
      0x94 :: concreteCreateTarget.toBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by decide +kernel)]
    rfl
  have hlen : concreteCreateTarget.toBytes.length = 20 := rfl
  simp only [Tx.signingHash, concreteDripTx, hc, hn, AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  change 2 :: (BLT.list [.bytes [1], .bytes [2], .bytes (Nat.toBytes 1),
    .bytes (Nat.toBytes 8), .bytes (Nat.toBytes 500000), .bytes concreteCreateTarget.toBytes,
    .bytes (Nat.toBytes 0), .bytes [0x9f, 0x67, 0x8c, 0xca], .list []]).toBytes = _
  simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, ht, hlen,
    Nat.toBytes, Nat.toBytes.aux, concreteDripSigningPayload]

theorem concreteDripSigningHash :
    concreteDripTx.signingHash =
      some (0x1570eb57cef628e0a7446f140edbacc6972f0f656ad8f176b2ebadfd37f517bc : B256) := by
  rw [concreteDripSigningEncoded]
  decide +kernel

theorem concreteDripRecoveredSender :
    recoverSender 1 concreteDripTx = .ok concreteCreateSender := by
  rw [recoverSender, concreteDripSigningHash]
  decide +kernel

def concreteDripFields : List BLT :=
  [.bytes [1], .bytes [2], .bytes [1], .bytes [8], .bytes [7, 0xa1, 0x20],
   .bytes concreteCreateTarget.toBytes, .bytes [], .bytes [0x9f, 0x67, 0x8c, 0xca],
   .list [], .bytes [1], .bytes concreteDripTx.r, .bytes concreteDripTx.s]

def concreteDripPayload : Bytes :=
  [1, 2, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++ concreteCreateTarget.toBytes ++
  [0x80, 0x84, 0x9f, 0x67, 0x8c, 0xca, 0xc0, 1, 0xa0] ++ concreteDripTx.r ++
  [0xa0] ++ concreteDripTx.s

def concreteDripTxRlp : Bytes := [2, 0xf8, 0x67] ++ concreteDripPayload

theorem concreteDripBLT : concreteDripTx.toBLT = .list concreteDripFields := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 2).sig = [2] := by decide +kernel
  have hr : trimZero concreteDripTx.r = concreteDripTx.r := by decide +kernel
  have hs : trimZero concreteDripTx.s = concreteDripTx.s := by decide +kernel
  simp only [Tx.toBLT, concreteDripTx, hc, AccessList.toBLT, List.map_nil]
  simp [concreteDripFields, concreteDripTx, Nat.toBytes, Nat.toBytes.aux]
  exact ⟨hr, hs⟩

theorem concreteDripPayloadParse (k : Nat) :
    Bytes.toBLTs? (k + 12) concreteDripPayload = some concreteDripFields := by
  unfold concreteDripPayload concreteDripFields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 2 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 8 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [7, 0xa1, 0x20] _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 _ _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 [0x9f, 0x67, 0x8c, 0xca] _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_list _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 _ _ _ rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil] using RlpConcrete.decode_bytes_32 k concreteDripTx.s [] rfl
  rw [Bytes.toBLTs?]

theorem concreteDripPayload_length : concreteDripPayload.length = 103 := by
  simp only [concreteDripPayload, List.length_append, List.length_cons, List.length_nil]
  rfl

theorem concreteDripEnvelopeParse :
    Bytes.toBLT? (0xf8 :: 0x67 :: concreteDripPayload) = some (.list concreteDripFields) := by
  have hsplit : Jaune.List.splitAt? 103 concreteDripPayload = some (concreteDripPayload, []) := by
    simpa only [concreteDripPayload_length, List.append_nil] using
      RlpConcrete.splitAt_append concreteDripPayload ([] : Bytes)
  have hp : Bytes.toBLTDiff? 105 (0xf8 :: 0x67 :: concreteDripPayload) =
      some (.list concreteDripFields, []) := by
    rw [Bytes.toBLTDiff?]
    change (do
      let p ← Jaune.List.splitAt? 1 ([0x67] ++ concreteDripPayload)
      let q ← Jaune.List.splitAt? (Bytes.toNat p.1) p.2
      let rs ← Bytes.toBLTs? 104 q.1
      pure (BLT.list rs, q.2)) = _
    rw [show Jaune.List.splitAt? 1 ([0x67] ++ concreteDripPayload) =
      some ([0x67], concreteDripPayload) from
        RlpConcrete.splitAt_append [0x67] concreteDripPayload]
    change (do
      let q ← Jaune.List.splitAt? 103 concreteDripPayload
      let rs ← Bytes.toBLTs? 104 q.1
      pure (BLT.list rs, q.2)) = _
    rw [hsplit]
    change (do let rs ← Bytes.toBLTs? 104 concreteDripPayload; pure (BLT.list rs, [])) = _
    rw [concreteDripPayloadParse 92]
    rfl
  unfold Bytes.toBLT?
  simp only [List.length_cons, concreteDripPayload_length]
  rw [hp]

theorem concreteDripDecode : decodeTx (.inl concreteDripTxRlp) = .ok concreteDripTx := by
  simp only [decodeTx, concreteDripTxRlp, List.cons_append, List.nil_append,
    Bytes.toExTx, concreteDripEnvelopeParse, concreteDripFields]
  rfl


noncomputable def concreteDripExecutionHeader : Header :=
  { concreteJoinBlock.header with
    parentHash := concreteJoinBlock.header.hash
    number := 3
    gasUsed := 0
    timestamp := 5 }

theorem concreteJoinedSenderCode : concreteJoined.state.getCode concreteCreateSender = ByteArray.empty := by
  rw [concreteJoinedCode]
  exact concreteDeployedSenderCode

theorem concreteDripSenderChecked :
    checkTransactionSenderAccount (concreteJoined.state.get concreteCreateSender)
      concreteDripTx 4000000 = .ok () := by
  have hn : (concreteJoined.state.get concreteCreateSender).nonce = 2 := concreteJoinedSenderNonce
  have hb : (concreteJoined.state.get concreteCreateSender).bal = 999999999998887794 :=
    concreteJoinedSenderBalance
  have hc : (concreteJoined.state.get concreteCreateSender).code = ByteArray.empty :=
    concreteJoinedSenderCode
  simp only [checkTransactionSenderAccount, hn, hb, checkTransactionSenderCode, hc]
  decide +kernel

theorem concreteDripValidated :
    validateTransaction pragueRules concreteDripTx = .ok (calculateIntrinsicCost concreteDripTx) := by
  decide +kernel

theorem concreteDripChecked :
    checkTransaction (initBenv pragueRules concreteJoined concreteDripExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteDripTx 0) concreteDripTx =
      .ok (concreteCreateSender, 2, [], 0) := by
  have hgas : checkTransactionGasLimits
      (initBenv pragueRules concreteJoined concreteDripExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteDripTx 0) concreteDripTx = .ok 0 := by decide +kernel
  have hchain : checkTransactionChainId
      (initBenv pragueRules concreteJoined concreteDripExecutionHeader).beginTransaction
      concreteDripTx = .ok () := by decide +kernel
  have hfee : checkTransactionGasFee
      (initBenv pragueRules concreteJoined concreteDripExecutionHeader).beginTransaction
      concreteDripTx = .ok (2, 4000000) := by decide +kernel
  rw [checkTransaction, hgas]
  simp only [Except.mapError, bind, Except.bind]
  rw [hchain]
  change (do
    let sender ← Except.mapError TransitionError.senderRecovery (recoverSender 1 concreteDripTx)
    let (effective, maxFee) ← Except.mapError TransitionError.transaction
      (checkTransactionGasFee (initBenv pragueRules concreteJoined concreteDripExecutionHeader).beginTransaction concreteDripTx)
    let (maxFee, hashes) ← Except.mapError TransitionError.transaction
      (checkTransactionBlobData (initBenv pragueRules concreteJoined concreteDripExecutionHeader).beginTransaction concreteDripTx maxFee)
    Except.mapError TransitionError.transaction (checkTransactionReceiver concreteDripTx)
    Except.mapError TransitionError.transaction (checkTransactionAuthorizationList concreteDripTx)
    Except.mapError TransitionError.transaction (checkTransactionSenderAccount (concreteJoined.state.get sender) concreteDripTx maxFee)
    pure (sender, effective, hashes, 0)) = _
  rw [concreteDripRecoveredSender, hfee]
  change (do
    Except.mapError TransitionError.transaction
      (checkTransactionSenderAccount (concreteJoined.state.get concreteCreateSender) concreteDripTx 4000000)
    pure (concreteCreateSender, 2, [], 0)) = _
  rw [concreteDripSenderChecked]
  rfl

noncomputable def concreteDripTxInput : Benv :=
  initBenv pragueRules concreteJoined concreteDripExecutionHeader

noncomputable def concreteDripDebit : State :=
  let nonceState := concreteJoined.state.incrNonce concreteCreateSender
  nonceState.setBal concreteCreateSender (nonceState.bal concreteCreateSender - 1000000)

theorem concreteDripDebit_run :
    (concreteDripTxInput.beginTransaction.state.incrNonce concreteCreateSender).subBal
      concreteCreateSender 1000000 = some concreteDripDebit := by
  have hb : (concreteJoined.state.incrNonce concreteCreateSender).bal concreteCreateSender =
      999999999998887794 := by
    unfold State.bal
    rw [State.incrNonce_get_bal]
    exact concreteJoinedSenderBalance
  change (concreteJoined.state.incrNonce concreteCreateSender).subBal concreteCreateSender
    1000000 = _
  unfold State.subBal
  rw [hb, if_neg (by decide +kernel)]
  unfold concreteDripDebit
  dsimp only
  rw [hb]

noncomputable def concreteDripTenv : Tenv :=
  deploymentTenv concreteDripTxInput concreteDripTx concreteCreateSender 0

noncomputable def concreteDripMessage : Msg := {
  benv := { concreteDripTxInput.beginTransaction with state := concreteDripDebit }
  tenv := concreteDripTenv
  caller := concreteCreateSender
  target := some concreteCreateTarget
  currentTarget := concreteCreateTarget
  gas := concreteDripTenv.stat.gas
  value := 0
  data := concreteDripTx.data
  code := concreteDripDebit.getCode concreteCreateTarget
  codeAddress := some concreteCreateTarget
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := concreteDripTenv.stat.accessListAddresses.insertMany
    (pragueRules.precompiles ++ [concreteCreateSender, concreteCreateTarget])
  accessedStorageKeys := concreteDripTenv.stat.accessListStorageKeys
  disablePrecompiles := false }

theorem concreteDripMessage_prepared :
    prepareMessage { concreteDripTxInput.beginTransaction with state := concreteDripDebit }
      concreteDripTenv concreteDripTx = .ok concreteDripMessage := rfl

theorem concreteDripMessage_code : concreteDripMessage.code.toList = code := by
  change (concreteDripDebit.getCode concreteCreateTarget).toList = code
  unfold concreteDripDebit
  rw [State.setBal_getCode]
  change ((concreteJoined.state.incrNonce concreteCreateSender).get concreteCreateTarget).code.toList = code
  rw [State.incrNonce_get_code]
  change (concreteJoined.state.getCode concreteCreateTarget).toList = code
  rw [concreteJoinedCode, concreteDeploymentRoot.installed]
  simp [ByteArray.toList_eq_toList_data]

theorem concreteDripDebit_balance :
    concreteDripDebit.bal concreteCreateSender = 999999999997887794 := by
  unfold concreteDripDebit
  change ((concreteJoined.state.incrNonce concreteCreateSender).setBal concreteCreateSender
    ((concreteJoined.state.incrNonce concreteCreateSender).bal concreteCreateSender - 1000000)).bal _ = _
  unfold State.bal
  rw [State.setBal_get_self, State.incrNonce_get_bal]
  change concreteJoined.state.bal concreteCreateSender - 1000000 = _
  rw [concreteJoinedSenderBalance]
  decide +kernel

noncomputable def concreteDripEntry : Benv :=
  concreteDripMessage.benv.withState
    ((concreteDripDebit.setBal concreteCreateSender
      (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0)

theorem concreteDripEntry_run :
    concreteDripMessage.benvAfterTransfer = .ok concreteDripEntry := by
  unfold concreteDripEntry concreteDripMessage
  generalize concreteDripDebit = debit
  generalize concreteDripTxInput.beginTransaction = begun
  generalize concreteDripTenv = tenv
  have hnot : ¬ debit.bal concreteCreateSender < (0 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero]
    omega
  simp only [Msg.benvAfterTransfer, if_true, Benv.subBal, State.subBal, hnot, if_false,
    bind, Option.bind, Option.toExcept, Except.bind, Benv.addBal, Benv.withState]

theorem concreteDripEntry_storage (address : Adr) :
    (concreteDripEntry.state.get address).stor = (concreteJoined.state.get address).stor := by
  change (((concreteDripDebit.setBal _ _).addBal _ _).get address).stor = _
  unfold State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteDripDebit
  dsimp only
  rw [State.setBal_get_stor, State.incrNonce_get_stor]


noncomputable def concreteDripSevm : Sevm := initSevm (concreteDripMessage.withBenv concreteDripEntry)
noncomputable def concreteDripDevm : Devm := initDevm (concreteDripMessage.withBenv concreteDripEntry)

theorem concreteDripDevm_chi : concreteDripDevm.getStorVal concreteCreateTarget chiSlot = rate := by
  change (concreteDripEntry.state.get concreteCreateTarget).stor.get chiSlot = rate
  rw [concreteDripEntry_storage]
  exact concreteJoined_values.1

theorem concreteDripDevm_rho : concreteDripDevm.getStorVal concreteCreateTarget rhoSlot = 2 := by
  change (concreteDripEntry.state.get concreteCreateTarget).stor.get rhoSlot = 2
  rw [concreteDripEntry_storage]
  exact concreteJoined_values.2.1

theorem concreteDripDevm_cold (k : B256) :
    (concreteCreateTarget, k) ∉ concreteDripDevm.accessedStorageKeys := by
  change (concreteCreateTarget, k) ∉ (∅ : Std.HashSet (Adr × B256))
  simp

def concreteDripStagingMemory : Mem := Mem.empty.write 32 (4 : B256).toBytes

private theorem concreteDrip_stage (sevm : Sevm) (base post : Devm) (G : Nat)
    (hfresh : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteDripStagingMemory, G⟩) freshStart post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G + 27⟩) drip post := by
  func_run (3) [6]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], concreteDripStagingMemory, G + 27 - 15⟩) (.call freshStartSlot) post
  apply Func.runCompiled_call' (f := freshStart) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hfresh

private theorem concreteDrip_readChi (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat) (next : Func)
    (hchi : base.getStorVal sevm.currentTarget chiSlot = rate)
    (hcold : (sevm.currentTarget, chiSlot) ∉ base.accessedStorageKeys)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((addAccessedStorageKey base sevm.currentTarget chiSlot).setMach ⟨[rate], M, G⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 2103⟩)
      (Ninst.pushB256 chiSlot ::: Ninst.sload ::: next) post := by
  func_run (2)
  change Func.RunCompiled _ sevm
    ((addAccessedStorageKey base sevm.currentTarget chiSlot).setMach
      ⟨[base.getStorVal sevm.currentTarget chiSlot], M, G + 2103 - 2103⟩) next post
  simpa only [hchi, Nat.add_sub_cancel] using htail


private theorem concreteDrip_stageClock (sevm : Sevm) (base post : Devm) (M C : Mem)
    (G : Nat) (next : Func) (htime : sevm.benvStat.time = 5)
    (hsize : M.size = 64)
    (hstore : M.write (storedChiWord * 32).toNat rate.toBytes = C)
    (hcsize : C.size = 192)
    (hread : Bytes.toB256 (C.read (storedChiWord * 32).toNat 32).1 = rate)
    (hmem : (C.read (storedChiWord * 32).toNat 32).2 = C)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], C.write 192 (5 : B256).toBytes, G⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[rate], M, G + 79⟩)
      (mstoreAt storedChiWord +++
        (Ninst.pushB256 scale ::: loadWord storedChiWord +++ Ninst.lt :::
          (.revert <?>
            (loadWord storedChiWord +++ Ninst.pushB256 maxChi ::: Ninst.lt :::
              (.revert <?> (Ninst.timestamp ::: mstoreAt nowWord +++ next)))))) post := by
  func_run (2) [12]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (3) [0]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [htime]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], C.write 192 (5 : B256).toBytes, G + 79 - 79⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteDrip_stageElapsed (sevm : Sevm) (base post : Devm) (M E : Mem)
    (G : Nat) (next : Func)
    (hrho : base.getStorVal sevm.currentTarget rhoSlot = 2)
    (hcold : (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hsize : M.size = 224)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 5)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hstore : M.write (exponentWord * 32).toNat (3 : B256).toBytes = E)
    (hesize : E.size = 224)
    (hexp : Bytes.toB256 (E.read (exponentWord * 32).toNat 32).1 = 3)
    (hemem : (E.read (exponentWord * 32).toNat 32).2 = E)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((addAccessedStorageKey base sevm.currentTarget rhoSlot).setMach ⟨[], E, G⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 2166⟩)
      (Ninst.pushB256 rhoSlot ::: Ninst.sload ::: Ninst.dup 0 :::
        loadWord nowWord +++ Ninst.lt :::
          (.revert <?> (loadWord nowWord +++ Ninst.sub :::
            mstoreAt exponentWord +++ loadWord exponentWord +++
            Ninst.pushB256 maxElapsed ::: Ninst.lt ::: (.revert <?> next)))) post := by
  func_run (2)
  change Func.RunCompiled _ sevm
    ((addAccessedStorageKey base sevm.currentTarget rhoSlot).setMach
      ⟨[base.getStorVal sevm.currentTarget rhoSlot], M, G + 2166 - 2103⟩) _ post
  rw [hrho]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (3) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hesize]
    decide +kernel
  rw [hexp, hemem]
  func_run (3) [0]
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteDrip_initializeRpow (sevm : Sevm) (base post : Devm) (M B A Z : Mem)
    (G : Nat) (zeroBase zeroExponent evenExponent : Func)
    (hsize : M.size = 224)
    (hbase : M.write (baseWord * 32).toNat rate.toBytes = B)
    (hbsize : B.size = 256)
    (hbexp : Bytes.toB256 (B.read (exponentWord * 32).toNat 32).1 = 3)
    (hbmem : (B.read (exponentWord * 32).toNat 32).2 = B)
    (hacc : B.write (accumulatorWord * 32).toNat rate.toBytes = A)
    (hasize : A.size = 288)
    (haexp : Bytes.toB256 (A.read (exponentWord * 32).toNat 32).1 = 3)
    (hamem : (A.read (exponentWord * 32).toNat 32).2 = A)
    (hzero : A.write (exponentWord * 32).toNat (1 : B256).toBytes = Z)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Z, G⟩) rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 122⟩)
      (Ninst.pushB256 rate ::: Ninst.dup 0 ::: mstoreAt baseWord +++ Ninst.iszero :::
        (zeroBase <?> (loadWord exponentWord +++ Ninst.iszero :::
          (zeroExponent <?> (loadWord exponentWord +++ Ninst.pushB256 1 ::: Ninst.and :::
            ((Ninst.pushB256 rate ::: mstoreAt accumulatorWord +++ loadWord exponentWord +++
              Ninst.pushB256 2 ::: Ninst.swap 0 ::: Ninst.div ::: mstoreAt exponentWord +++
              .call rpowLoopSlot) <?> evenExponent)))))) post := by
  func_run (4) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hbase]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (3) [1]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hacc]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [haexp, hamem]
  func_run (5) [1, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [hzero]
  apply Func.runCompiled_call' (f := rpowLoop) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hloop


def concreteDripClockMemory : Mem :=
  (concreteDripStagingMemory.write 160 rate.toBytes).write 192 (5 : B256).toBytes
def concreteDripExponentMemory : Mem := concreteDripClockMemory.write 0 (3 : B256).toBytes
def concreteDripBaseMemory : Mem := concreteDripExponentMemory.write 224 rate.toBytes
def concreteDripAccumulatorMemory : Mem := concreteDripBaseMemory.write 256 rate.toBytes
def concreteDripLoopMemory : Mem := concreteDripAccumulatorMemory.write 0 (1 : B256).toBytes

def concreteDripFreshBase (sevm : Sevm) (base : Devm) : Devm :=
  addAccessedStorageKey (addAccessedStorageKey base sevm.currentTarget chiSlot) sevm.currentTarget rhoSlot

private theorem concreteDrip_stagingSize : concreteDripStagingMemory.size = 64 := by decide +kernel

private theorem concreteDrip_chiMemoryFacts :
    (concreteDripStagingMemory.write 160 rate.toBytes).size = 192 ∧
    Bytes.toB256 ((concreteDripStagingMemory.write 160 rate.toBytes).read 160 32).1 = rate ∧
    ((concreteDripStagingMemory.write 160 rate.toBytes).read 160 32).2 =
      concreteDripStagingMemory.write 160 rate.toBytes := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteDrip_clockMemoryFacts : concreteDripClockMemory.size = 224 ∧
    Bytes.toB256 (concreteDripClockMemory.read 192 32).1 = 5 ∧
    (concreteDripClockMemory.read 192 32).2 = concreteDripClockMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteDrip_exponentMemoryFacts : concreteDripExponentMemory.size = 224 ∧
    Bytes.toB256 (concreteDripExponentMemory.read 0 32).1 = 3 ∧
    (concreteDripExponentMemory.read 0 32).2 = concreteDripExponentMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteDrip_baseMemoryFacts : concreteDripBaseMemory.size = 256 ∧
    Bytes.toB256 (concreteDripBaseMemory.read 0 32).1 = 3 ∧
    (concreteDripBaseMemory.read 0 32).2 = concreteDripBaseMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteDrip_accumulatorMemoryFacts : concreteDripAccumulatorMemory.size = 288 ∧
    Bytes.toB256 (concreteDripAccumulatorMemory.read 0 32).1 = 3 ∧
    (concreteDripAccumulatorMemory.read 0 32).2 = concreteDripAccumulatorMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

theorem concreteDrip_freshStart (sevm : Sevm) (base post : Devm) (G : Nat)
    (htime : sevm.benvStat.time = 5)
    (hchi : base.getStorVal sevm.currentTarget chiSlot = rate)
    (hrho : base.getStorVal sevm.currentTarget rhoSlot = 2)
    (hcoldChi : (sevm.currentTarget, chiSlot) ∉ base.accessedStorageKeys)
    (hcoldRho : (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((concreteDripFreshBase sevm base).setMach ⟨[], concreteDripLoopMemory, G⟩)
      rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteDripStagingMemory, G + 122 + 2166 + 79 + 2103⟩)
      freshStart post := by
  apply concreteDrip_readChi sevm _ _ _ _ _ hchi hcoldChi
  apply concreteDrip_stageClock (sevm := sevm) (C := concreteDripStagingMemory.write 160 rate.toBytes)
  · exact htime
  · exact concreteDrip_stagingSize
  · rfl
  · exact concreteDrip_chiMemoryFacts.1
  · exact concreteDrip_chiMemoryFacts.2.1
  · exact concreteDrip_chiMemoryFacts.2.2
  apply concreteDrip_stageElapsed (E := concreteDripExponentMemory)
  · exact hrho
  · change (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys.insert
      (sevm.currentTarget, chiSlot)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by simp only [beq_iff_eq, Prod.mk.injEq, true_and]; decide +kernel, hcoldRho⟩
  · exact concreteDrip_clockMemoryFacts.1
  · exact concreteDrip_clockMemoryFacts.2.1
  · exact concreteDrip_clockMemoryFacts.2.2
  · rfl
  · exact concreteDrip_exponentMemoryFacts.1
  · exact concreteDrip_exponentMemoryFacts.2.1
  · exact concreteDrip_exponentMemoryFacts.2.2
  apply concreteDrip_initializeRpow (B := concreteDripBaseMemory)
    (A := concreteDripAccumulatorMemory) (Z := concreteDripLoopMemory)
  · exact concreteDrip_exponentMemoryFacts.1
  · rfl
  · exact concreteDrip_baseMemoryFacts.1
  · exact concreteDrip_baseMemoryFacts.2.1
  · exact concreteDrip_baseMemoryFacts.2.2
  · rfl
  · exact concreteDrip_accumulatorMemoryFacts.1
  · exact concreteDrip_accumulatorMemoryFacts.2.1
  · exact concreteDrip_accumulatorMemoryFacts.2.2
  · rfl
  exact hloop


def concreteDripSquare : B256 := 1000000003094251918120023625
def concreteDripFactor : B256 := 1000000004641377880770433536
def concreteDripChi : B256 := 1000000006188503845814442183

private theorem concreteDrip_square (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (next : Func) (hsize : M.size = 288)
    (hread : Bytes.toB256 (M.read (baseWord * 32).toNat 32).1 = rate)
    (hmem : (M.read (baseWord * 32).toNat 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write (baseWord * 32).toNat concreteDripSquare.toBytes, G⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 107⟩)
      (guardedRoundedMul baseWord baseWord baseWord next) post := by
  unfold guardedRoundedMul roundedMulRecovery
  rw [if_pos rfl]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hread, hmem]
  func_run (11) [rate * rate, rate, 1, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  func_run (8) [half + rate * rate, 0]
  func_run (1)
  func_run (5) [concreteDripSquare, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write (baseWord * 32).toNat concreteDripSquare.toBytes, G + 107 - 107⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteDrip_accumulate (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (next : Func) (hsize : M.size = 288)
    (hacc : Bytes.toB256 (M.read (accumulatorWord * 32).toNat 32).1 = rate)
    (haccMem : (M.read (accumulatorWord * 32).toNat 32).2 = M)
    (hbase : Bytes.toB256 (M.read (baseWord * 32).toNat 32).1 = concreteDripSquare)
    (hbaseMem : (M.read (baseWord * 32).toNat 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write (accumulatorWord * 32).toNat concreteDripFactor.toBytes, G⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 110⟩)
      (guardedRoundedMul accumulatorWord baseWord accumulatorWord next) post := by
  unfold guardedRoundedMul roundedMulRecovery
  rw [if_neg (by decide +kernel)]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hacc, haccMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hbase, hbaseMem]
  func_run (4) [rate * concreteDripSquare, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hbase, hbaseMem]
  func_run (4) [rate, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hacc, haccMem]
  func_run (2) [1, 0]
  func_run (8) [half + rate * concreteDripSquare, 0]
  func_run (1)
  func_run (5) [concreteDripFactor, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write (accumulatorWord * 32).toNat concreteDripFactor.toBytes, G + 110 - 110⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteDrip_loopOne (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hexp : Bytes.toB256 (M.read 0 32).1 = 1) (hexpMem : (M.read 0 32).2 = M)
    (hbase : Bytes.toB256 (M.read 224 32).1 = rate) (hbaseMem : (M.read 224 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write 224 concreteDripSquare.toBytes, G⟩) rpowAfterSquare post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 140⟩) rpowLoop post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[Bytes.toB256 (M.read 0 32).1], (M.read 0 32).2, G + 140 - 5⟩) _ post
  rw [hexp, hexpMem]
  func_run (2) [0]
  rw [show G + 140 - 21 = (G + 12) + 107 by omega]
  apply concreteDrip_square _ _ _ _ _ _ hsize hbase hbaseMem
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write 224 concreteDripSquare.toBytes, G + 12⟩) (.call rpowAfterSquareSlot) post
  apply Func.runCompiled_call' (f := rpowAfterSquare) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using htail

private theorem concreteDrip_afterSquare (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hexp : Bytes.toB256 (M.read 0 32).1 = 1) (hexpMem : (M.read 0 32).2 = M)
    (hacc : Bytes.toB256 (M.read 256 32).1 = rate) (haccMem : (M.read 256 32).2 = M)
    (hbase : Bytes.toB256 (M.read 224 32).1 = concreteDripSquare)
    (hbaseMem : (M.read 224 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write 256 concreteDripFactor.toBytes, G⟩) rpowAdvance post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 147⟩) rpowAfterSquare post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[Bytes.toB256 (M.read 0 32).1], (M.read 0 32).2, G + 147 - 5⟩) _ post
  rw [hexp, hexpMem]
  func_run (3) [1]
  rw [show G + 147 - 25 = (G + 12) + 110 by omega]
  apply concreteDrip_accumulate _ _ _ _ _ _ hsize hacc haccMem hbase hbaseMem
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write 256 concreteDripFactor.toBytes, G + 12⟩) (.call rpowAdvanceSlot) post
  apply Func.runCompiled_call' (f := rpowAdvance) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using htail

private theorem concreteDrip_advance (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hexp : Bytes.toB256 (M.read 0 32).1 = 1) (hexpMem : (M.read 0 32).2 = M)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M.write 0 (0 : B256).toBytes, G⟩) rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 33⟩) rpowAdvance post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[Bytes.toB256 (M.read 0 32).1], (M.read 0 32).2, G + 33 - 5⟩) _ post
  rw [hexp, hexpMem]
  func_run (5) [0, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], M.write 0 (0 : B256).toBytes, G + 33 - 21⟩) (.call rpowLoopSlot) post
  apply Func.runCompiled_call' (f := rpowLoop) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using htail

private theorem concreteDrip_rpowZero (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hread : Bytes.toB256 (M.read 0 32).1 = 0)
    (hmem : (M.read 0 32).2 = M)
    (hcompose : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G⟩) composeFresh post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 34⟩) rpowLoop post := by
  func_run (1)
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mload_of (v := 0) (M := M) (c := 3) (G := G + 29)
      (s := []) rfl ?_ hread hmem ?_ (by decide)) ?_
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  simp only [Devm.setMach_setMach]
  func_run (2) [1]
  apply Func.runCompiled_call' (f := composeFresh) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hcompose


def concreteDripSquareMemory : Mem := concreteDripLoopMemory.write 224 concreteDripSquare.toBytes
def concreteDripFactorMemory : Mem := concreteDripSquareMemory.write 256 concreteDripFactor.toBytes
def concreteDripRpowMemory : Mem := concreteDripFactorMemory.write 0 (0 : B256).toBytes

private def concreteDripLoopImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes) 0 (3 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (1 : B256).toBytes)

private theorem concreteDrip_loopReads : Mem.Reads concreteDripLoopMemory concreteDripLoopImage := by
  unfold concreteDripLoopMemory concreteDripAccumulatorMemory concreteDripBaseMemory concreteDripExponentMemory concreteDripClockMemory concreteDripStagingMemory concreteDripLoopImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteDrip_loopSize : concreteDripLoopMemory.size = 288 := by decide +kernel

private theorem concreteDrip_loopUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteDripLoopMemory.read i 32).2 = concreteDripLoopMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteDrip_loopSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteDrip_loopRead0 :
    Bytes.toB256 (concreteDripLoopMemory.read 0 32).1 = (1 : B256) := by
  rw [concreteDrip_loopReads.read]
  unfold concreteDripLoopImage
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_loopRead224 :
    Bytes.toB256 (concreteDripLoopMemory.read 224 32).1 = rate := by
  rw [concreteDrip_loopReads.read]
  unfold concreteDripLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 224 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 224 256 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private def concreteDripSquareImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes) 0 (3 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (1 : B256).toBytes) 224 concreteDripSquare.toBytes)

private theorem concreteDrip_squareReads : Mem.Reads concreteDripSquareMemory concreteDripSquareImage := by
  unfold concreteDripSquareMemory concreteDripLoopMemory concreteDripAccumulatorMemory concreteDripBaseMemory concreteDripExponentMemory concreteDripClockMemory concreteDripStagingMemory concreteDripSquareImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteDrip_squareSize : concreteDripSquareMemory.size = 288 := by
  unfold concreteDripSquareMemory
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, concreteDrip_loopSize]; decide)]
  exact concreteDrip_loopSize

private theorem concreteDrip_squareUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteDripSquareMemory.read i 32).2 = concreteDripSquareMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteDrip_squareSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteDrip_squareRead0 :
    Bytes.toB256 (concreteDripSquareMemory.read 0 32).1 = (1 : B256) := by
  rw [concreteDrip_squareReads.read]
  unfold concreteDripSquareImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 0 224 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_squareRead224 :
    Bytes.toB256 (concreteDripSquareMemory.read 224 32).1 = concreteDripSquare := by
  rw [concreteDrip_squareReads.read]
  unfold concreteDripSquareImage
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_squareRead256 :
    Bytes.toB256 (concreteDripSquareMemory.read 256 32).1 = rate := by
  rw [concreteDrip_squareReads.read]
  unfold concreteDripSquareImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private def concreteDripFactorImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes) 0 (3 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (1 : B256).toBytes) 224 concreteDripSquare.toBytes) 256 concreteDripFactor.toBytes)

private theorem concreteDrip_factorReads : Mem.Reads concreteDripFactorMemory concreteDripFactorImage := by
  unfold concreteDripFactorMemory concreteDripSquareMemory concreteDripLoopMemory concreteDripAccumulatorMemory concreteDripBaseMemory concreteDripExponentMemory concreteDripClockMemory concreteDripStagingMemory concreteDripFactorImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteDrip_factorSize : concreteDripFactorMemory.size = 288 := by
  unfold concreteDripFactorMemory
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, concreteDrip_squareSize])]
  exact concreteDrip_squareSize

private theorem concreteDrip_factorUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteDripFactorMemory.read i 32).2 = concreteDripFactorMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteDrip_factorSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteDrip_factorRead0 :
    Bytes.toB256 (concreteDripFactorMemory.read 0 32).1 = (1 : B256) := by
  rw [concreteDrip_factorReads.read]
  unfold concreteDripFactorImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 0 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 0 224 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private def concreteDripRpowImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 32 (4 : B256).toBytes) 160 rate.toBytes) 192 (5 : B256).toBytes) 0 (3 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (1 : B256).toBytes) 224 concreteDripSquare.toBytes) 256 concreteDripFactor.toBytes) 0 (0 : B256).toBytes)

private theorem concreteDrip_rpowReads : Mem.Reads concreteDripRpowMemory concreteDripRpowImage := by
  unfold concreteDripRpowMemory concreteDripFactorMemory concreteDripSquareMemory concreteDripLoopMemory concreteDripAccumulatorMemory concreteDripBaseMemory concreteDripExponentMemory concreteDripClockMemory concreteDripStagingMemory concreteDripRpowImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteDrip_rpowSize : concreteDripRpowMemory.size = 288 := by
  unfold concreteDripRpowMemory
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, concreteDrip_factorSize]; decide)]
  exact concreteDrip_factorSize

private theorem concreteDrip_rpowUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteDripRpowMemory.read i 32).2 = concreteDripRpowMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteDrip_rpowSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteDrip_rpowRead0 :
    Bytes.toB256 (concreteDripRpowMemory.read 0 32).1 = (0 : B256) := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_rpowRead32 :
    Bytes.toB256 (concreteDripRpowMemory.read 32 32).1 = (4 : B256) := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 160 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_rpowRead160 :
    Bytes.toB256 (concreteDripRpowMemory.read 160 32).1 = rate := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 192 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_rpowRead192 :
    Bytes.toB256 (concreteDripRpowMemory.read 192 32).1 = (5 : B256) := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteDrip_rpowRead256 :
    Bytes.toB256 (concreteDripRpowMemory.read 256 32).1 = concreteDripFactor := by
  rw [concreteDrip_rpowReads.read]
  unfold concreteDripRpowImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _


theorem concreteDrip_rpow (sevm : Sevm) (base post : Devm) (G : Nat)
    (hcompose : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteDripRpowMemory, G⟩) composeFresh post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteDripLoopMemory, G + 354⟩) rpowLoop post := by
  rw [show G + 354 = (G + 214) + 140 by omega]
  apply concreteDrip_loopOne
  · exact concreteDrip_loopSize
  · exact concreteDrip_loopRead0
  · exact concreteDrip_loopUnchanged _ (by decide)
  · exact concreteDrip_loopRead224
  · exact concreteDrip_loopUnchanged _ (by decide)
  change Func.RunCompiled _ sevm (base.setMach ⟨[], concreteDripSquareMemory, G + 214⟩) rpowAfterSquare post
  rw [show G + 214 = (G + 67) + 147 by omega]
  apply concreteDrip_afterSquare
  · exact concreteDrip_squareSize
  · exact concreteDrip_squareRead0
  · exact concreteDrip_squareUnchanged _ (by decide)
  · exact concreteDrip_squareRead256
  · exact concreteDrip_squareUnchanged _ (by decide)
  · exact concreteDrip_squareRead224
  · exact concreteDrip_squareUnchanged _ (by decide)
  change Func.RunCompiled _ sevm (base.setMach ⟨[], concreteDripFactorMemory, G + 67⟩) rpowAdvance post
  rw [show G + 67 = (G + 34) + 33 by omega]
  apply concreteDrip_advance
  · exact concreteDrip_factorSize
  · exact concreteDrip_factorRead0
  · exact concreteDrip_factorUnchanged _ (by decide)
  exact concreteDrip_rpowZero _ _ _ _ _ concreteDrip_rpowSize concreteDrip_rpowRead0
    (concreteDrip_rpowUnchanged _ (by decide)) hcompose

private theorem concreteDrip_composeFresh (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hchi : Bytes.toB256 (M.read (storedChiWord * 32).toNat 32).1 = rate)
    (hchiMem : (M.read (storedChiWord * 32).toNat 32).2 = M)
    (hfactor : Bytes.toB256 (M.read (accumulatorWord * 32).toNat 32).1 = concreteDripFactor)
    (hfactorMem : (M.read (accumulatorWord * 32).toNat 32).2 = M)
    (hroute : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G⟩) freshRoute post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 104⟩) composeFresh post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [rate * concreteDripFactor, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [rate, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (3) [1, 0]
  func_run (7) [concreteDripChi, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  apply Func.runCompiled_call' (f := freshRoute) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hroute

private theorem concreteDrip_freshRoute (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hroute : Bytes.toB256 (M.read (routeWord * 32).toNat 32).1 = routeDrip)
    (hmem : (M.read (routeWord * 32).toNat 32).2 = M)
    (hdrip : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G⟩) afterDrip post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G + 97⟩) freshRoute post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hroute, hmem]
  func_run (17) [0, 0, 0, 1]
  simpa only [Nat.add_sub_cancel] using hdrip


private theorem concreteDrip_afterDrip (sevm : Sevm) (base C R : Devm) (M : Mem) (G : Nat)
    (hstatic : sevm.isStatic = false) (hsize : M.size = 288)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 5)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hchiCost : sstoreCost sevm base chiSlot concreteDripChi = 2900)
    (hchi : afterSstore sevm base chiSlot concreteDripChi = C)
    (hrhoCost : sstoreCost sevm C rhoSlot 5 = 2900)
    (hrho : afterSstore sevm C rhoSlot 5 = R) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G + 5825⟩) afterDrip
      ((R.setMach ⟨[], M.write 0 concreteDripChi.toBytes, G⟩).withOutput concreteDripChi.toBytes) := by
  func_run (2)
  rw [show G + 5825 - 6 = (G + 2919) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := C.setMach ⟨[concreteDripChi], M, G + 2919⟩) ?_ ?_
  · simpa only [hchiCost, hchi] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := base)
        (key := chiSlot) (value := concreteDripChi) (stack := [concreteDripChi])
        (memory := M) (G := G + 2919)
        (by rw [hchiCost]; simp only [gCallStipend]; omega) hstatic)
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (1)
  rw [show G + 2919 - 9 = (G + 10) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := R.setMach ⟨[concreteDripChi], M, G + 10⟩) ?_ ?_
  · simpa only [hrhoCost, hrho] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := C)
        (key := rhoSlot) (value := 5) (stack := [concreteDripChi])
        (memory := M) (G := G + 10)
        (by rw [hrhoCost]; simp only [gCallStipend]; omega) hstatic)
  func_run (4) [0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  have hnsize : (M.write 0 concreteDripChi.toBytes).size = 288 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsize]; decide)]
    exact hsize
  have hnread : ((M.write 0 concreteDripChi.toBytes).read 0 32).1 = concreteDripChi.toBytes := by
    simpa only [B256.length_toBytes] using
      (Mem.read_write_zero M (ys := concreteDripChi.toBytes) (by decide +kernel))
  have hnmem : ((M.write 0 concreteDripChi.toBytes).read 0 32).2 = M.write 0 concreteDripChi.toBytes := by
    apply Mem.read_snd_eq_self
    rw [hnsize]
    decide +kernel
  apply Func.runCompiled_return_of (G := G) (e := 0)
  · rfl
  · change calculateMemoryGasCost (memExtsSize (M.write 0 concreteDripChi.toBytes).size [(0, 32)]) -
      calculateMemoryGasCost (M.write 0 concreteDripChi.toBytes).size = 0
    rw [hnsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  · change (((M.write 0 concreteDripChi.toBytes).read 0 32).1,
      R.setMach ⟨[], ((M.write 0 concreteDripChi.toBytes).read 0 32).2, G⟩) = _
    rw [hnread, hnmem]


noncomputable def concreteDripStorageBase : Devm := concreteDripFreshBase concreteDripSevm concreteDripDevm
noncomputable def concreteDripChiBase : Devm :=
  (concreteDripStorageBase.withRefundCounter 0).setStorVal concreteCreateTarget chiSlot concreteDripChi
noncomputable def concreteDripRhoBase : Devm :=
  (concreteDripChiBase.withRefundCounter 0).setStorVal concreteCreateTarget rhoSlot 5

private theorem concreteDrip_originalStorage (key : B256) :
    getOrigStorVal concreteDripSevm concreteCreateTarget key =
      (concreteJoined.state.getStor concreteCreateTarget).get key := by rfl

private theorem concreteDripStorageBase_warm (key : B256) (hk : key = chiSlot ∨ key = rhoSlot) :
    (concreteCreateTarget, key) ∈ concreteDripStorageBase.accessedStorageKeys := by
  change (concreteCreateTarget, key) ∈ (concreteDripDevm.accessedStorageKeys.insert
    (concreteCreateTarget, chiSlot)).insert (concreteCreateTarget, rhoSlot)
  rcases hk with rfl | rfl <;> simp

private theorem concreteDrip_chiStore :
    sstoreCost concreteDripSevm concreteDripStorageBase chiSlot concreteDripChi = 2900 ∧
    afterSstore concreteDripSevm concreteDripStorageBase chiSlot concreteDripChi = concreteDripChiBase := by
  have ht : concreteDripSevm.currentTarget = concreteCreateTarget := rfl
  have hw := concreteDripStorageBase_warm chiSlot (Or.inl rfl)
  have hr : concreteDripStorageBase.refundCounter = 0 := rfl
  have hv : concreteDripStorageBase.getStorVal concreteCreateTarget chiSlot = rate := concreteDripDevm_chi
  have hc : sstoreValueCost rate rate concreteDripChi = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteDripChi rate rate 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteDrip_originalStorage,
      concreteJoined_values.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteDrip_originalStorage,
      concreteJoined_values.1, hv, hr, hf]
    rfl

private theorem concreteDrip_rhoStore :
    sstoreCost concreteDripSevm concreteDripChiBase rhoSlot 5 = 2900 ∧
    afterSstore concreteDripSevm concreteDripChiBase rhoSlot 5 = concreteDripRhoBase := by
  have ht : concreteDripSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, rhoSlot) ∈ concreteDripChiBase.accessedStorageKeys := by
    rw [concreteDripChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteDripStorageBase_warm rhoSlot (Or.inr rfl)
  have hr : concreteDripChiBase.refundCounter = 0 := rfl
  have hv : concreteDripChiBase.getStorVal concreteCreateTarget rhoSlot = 2 := by
    change (Devm.getStor ((concreteDripStorageBase.withRefundCounter 0).setStorVal
      concreteCreateTarget chiSlot concreteDripChi) concreteCreateTarget).get rhoSlot = _
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    exact concreteDripDevm_rho
  have hc : sstoreValueCost 2 2 5 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter 5 2 2 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteDrip_originalStorage,
      concreteJoined_values.2.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteDrip_originalStorage,
      concreteJoined_values.2.1, hv, hr, hf]
    rfl

noncomputable def concreteDripRuntimePost (G : Nat) : Devm :=
  (concreteDripRhoBase.setMach ⟨[], concreteDripRpowMemory.write 0 concreteDripChi.toBytes, G⟩).withOutput
    concreteDripChi.toBytes

theorem concreteDrip_endpoint (G : Nat) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteDripSevm
      (concreteDripDevm.setMach ⟨[], Mem.empty, G + 10877⟩) drip (concreteDripRuntimePost G) := by
  rw [show G + 10877 = G + 5825 + 97 + 104 + 354 + 122 + 2166 + 79 + 2103 + 27 by omega]
  apply concreteDrip_stage
  apply concreteDrip_freshStart
  · rfl
  · exact concreteDripDevm_chi
  · exact concreteDripDevm_rho
  · exact concreteDripDevm_cold _
  · exact concreteDripDevm_cold _
  apply concreteDrip_rpow
  apply concreteDrip_composeFresh
  · exact concreteDrip_rpowSize
  · exact concreteDrip_rpowRead160
  · exact concreteDrip_rpowUnchanged _ (by decide)
  · exact concreteDrip_rpowRead256
  · exact concreteDrip_rpowUnchanged _ (by decide)
  apply concreteDrip_freshRoute
  · exact concreteDrip_rpowSize
  · exact concreteDrip_rpowRead32
  · exact concreteDrip_rpowUnchanged _ (by decide)
  exact concreteDrip_afterDrip _ concreteDripStorageBase concreteDripChiBase concreteDripRhoBase _ G
    rfl concreteDrip_rpowSize concreteDrip_rpowRead192 (concreteDrip_rpowUnchanged _ (by decide))
    concreteDrip_chiStore.1 concreteDrip_chiStore.2 concreteDrip_rhoStore.1 concreteDrip_rhoStore.2

private theorem concreteDrip_dispatch (sevm : Sevm) (base post : Devm) (G : Nat)
    (hdata : sevm.data = concreteDripTx.data)
    (hvalue : sevm.value = 0)
    (hdrip : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G⟩) drip post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
    (base.setMach ⟨[], Mem.empty, G + 133⟩) main post := by
  have hd : dripSelector = (0x9f678cca : B256) := by decide +kernel
  have hj : joinSelector = (0xb688a363 : B256) := by decide +kernel
  have hshift : Sevm.dataWord sevm 0 >>> B256.toNat 224 = dripSelector := by
    simp only [Sevm.dataWord, hdata, concreteDripTx]
    decide +kernel
  func_run (1)
  simp only [hdata, concreteDripTx]
  func_run (5) [dripSelector]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[dripSelector], Mem.empty, G + 133 - 27⟩) (dispatch tree) post
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[dripSelector], Mem.empty, G + 133 - 27⟩)
    (Ninst.dup 0 ::: Ninst.pushB256 dripSelector ::: Ninst.gt :::
      (dispatch (.fork (.fork (.leaf convertToAssetsSelector (nonpayable (exactCalldata 36 convertToAssets)))
          (.leaf exitSelector (nonpayable (exactCalldata 36 exit))))
        (.leaf convertToUnitsSelector (nonpayable (exactCalldata 36 convertToUnits)))) <?>
       dispatch (.fork (.leaf dripSelector (nonpayable (exactCalldata 4 drip)))
         (.leaf joinSelector (exactCalldata 4 join))))) post
  simp only [hd, hj]
  func_run (4) [0]
  func_run (4) [1]
  func_run (3) [1]
  func_run (1)
  rw [hvalue]
  func_run (2) [1]
  func_run (4) [1]
  all_goals first
    | simpa only [Nat.add_sub_cancel] using hdrip
    | (simp only [hdata, concreteDripTx]; decide +kernel)

theorem concreteDrip_runtime (G : Nat) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteDripSevm
      (concreteDripDevm.setMach ⟨[], Mem.empty, G + 11010⟩) main (concreteDripRuntimePost G) := by
  rw [show G + 11010 = (G + 10877) + 133 by omega]
  exact concreteDrip_dispatch _ _ _ _ rfl rfl (concreteDrip_endpoint G)

theorem concreteDripDevm_gas : concreteDripDevm.gasLeft = 478936 := by
  change 500000 - deploymentIntrinsicGas concreteDripTx = 478936
  decide +kernel

theorem concreteDrip_program :
    Prog.RunCompiled concreteDripSevm concreteDripDevm runtime (concreteDripRuntimePost 467925) := by
  apply Prog.runCompiled_intro (G := 467925 + 11010)
    (mid := concreteDripDevm.setMach ⟨[], Mem.empty, 467925 + 11010⟩)
  · rw [concreteDripDevm_gas]
    decide
  · rfl
  exact concreteDrip_runtime 467925

theorem concreteDrip_compiled : some concreteDripSevm.code.toList = Prog.compile runtime := by
  change some concreteDripMessage.code.toList = _
  rw [concreteDripMessage_code, code_compile]

theorem concreteDrip_exec :
    exec (initEvm (concreteDripMessage.withBenv concreteDripEntry)) =
      .ok (concreteDripRuntimePost 467925) :=
  Prog.exec_of_runCompiled concreteDrip_program concreteDrip_compiled

theorem concreteDrip_frameEntry :
    (Frame.ofCall concreteDripMessage).enter =
      .run (initEvm (concreteDripMessage.withBenv concreteDripEntry)) := by
  have hnp : ¬ pragueRules.isPrecomp concreteCreateTarget :=
    concreteDeploymentBase.target_not_precompile (ChainConfig.pragueOnly_rulesAt 1 5)
  have he : executeCode.enter (concreteDripMessage.withBenv concreteDripEntry) =
      .inl (initEvm (concreteDripMessage.withBenv concreteDripEntry)) := by
    unfold executeCode.enter
    change (if !false && pragueRules.isPrecomp concreteCreateTarget then _ else _) = _
    simp only [Bool.not_false, Bool.true_and, hnp]
    rfl
  unfold Frame.enter Frame.ofCall
  rw [concreteDripEntry_run]
  dsimp only
  rw [he]

private theorem concreteDrip_postError : (concreteDripRuntimePost 467925).error = none := rfl

theorem concreteDrip_processMessage :
    processMessage concreteDripMessage = .ok (concreteDripRuntimePost 467925) := by
  unfold processMessage runFrame
  rw [concreteDrip_frameEntry]
  unfold Frame.settle Frame.settleMsg processMessage.settle executeCode.handleError
  simp only [concreteDrip_exec, concreteDrip_postError, Frame.ofCall, Option.isSome,
    Bool.false_eq_true, if_false, bind, Except.bind]

noncomputable def concreteDripMessageState : State := (concreteDripRuntimePost 467925).state

def concreteDripMessageOutput : MsgCallOutput := {
  gasLeft := 467925
  refundCounter := 0
  logs := []
  accountsToDelete := .emptyWithCapacity
  error := none
  returnData := concreteDripChi.toBytes }

theorem concreteDrip_messageCall :
    processMessageCall concreteDripMessage = .ok (concreteDripMessageState, concreteDripMessageOutput) := by
  have htarget : concreteDripMessage.target.isNone = false := rfl
  have hauths : concreteDripMessage.tenv.stat.auths = [] := rfl
  have hcode : some concreteDripMessage.code.toList = Prog.compile runtime := concreteDrip_compiled
  have hdelegation : getDelegatedCodeAddress concreteDripMessage.code = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg (not_delegation_of_compile hcode)]
  have hrefund : (concreteDripRuntimePost 467925).refundCounter = 0 := rfl
  unfold processMessageCall
  rw [htarget]
  unfold processMessageCall.call
  simp only [hauths, List.isEmpty, if_true, bind, Except.bind, hdelegation,
    concreteDrip_processMessage, Except.bimap, id_eq, concreteDrip_postError,
    Option.isNone, hrefund]
  rfl

noncomputable def concreteDripTransactionState : State :=
  deploymentFinalState concreteDripTxInput concreteDripTx concreteCreateSender
    concreteDripMessageState 32075

def concreteDripTransactionBout : BlockOutput :=
  deploymentFinalBout .init concreteDripTx 0 concreteDripMessageOutput 32075

theorem concreteDrip_transaction :
    processTransaction concreteDripTxInput .init concreteDripTx 0 =
      .ok (concreteDripTransactionState, concreteDripTransactionBout) := by
  have hchecked := concreteDripChecked
  change checkTransaction concreteDripTxInput.beginTransaction
    (deploymentTxPreludeBout .init concreteDripTx 0) concreteDripTx =
      .ok (concreteCreateSender, 2, [], 0) at hchecked
  have hdebit := concreteDripDebit_run
  simp only [Benv.beginTransaction] at hdebit
  have hprepare := concreteDripMessage_prepared
  have hrules : concreteDripTxInput.beginTransaction.stat.rules = pragueRules := rfl
  unfold processTransaction
  simp only [bind, Except.bind]
  rw [hrules, concreteDripValidated]
  simp only [Except.mapError]
  simp only [deploymentTxPreludeBout, ExecutionTrace.transactionPreludeBout] at hchecked
  rw [hchecked]
  simp only [Tx.isTypeThree, Tx.accessList, TxType.accessList, Tx.auths,
    concreteDripTx, Bool.false_eq_true, if_false, Nat.add_zero, Benv.beginTransaction]
  rw [show Nat.toB256 (500000 * 2) = 1000000 by decide +kernel, hdebit]
  simp only [Option.toExcept]
  simp only [concreteDripTenv, deploymentTenv, deploymentIntrinsicGas, Benv.beginTransaction,
    concreteDripTx] at hprepare
  simp only [List.map_nil, List.flatten_nil]
  simp only [deploymentEffectiveGasPrice] at hprepare ⊢
  have hprice : min 1 (8 - concreteDripTxInput.stat.baseFeePerGas) +
      concreteDripTxInput.stat.baseFeePerGas = 2 := by rfl
  rw [hprice] at hprepare
  simp only [hprepare, concreteDrip_messageCall]
  have hgas : max (500000 - 467925 - min ((500000 - 467925) / 5) 0)
      (calculateIntrinsicCost concreteDripTx).2 = 32075 := by decide +kernel
  simp only [concreteDripTx] at hgas
  simp only [concreteDripMessageOutput]
  rw [show Int.toNat? 0 = some 0 by rfl]
  simp only [hgas]
  unfold concreteDripTransactionState concreteDripTransactionBout deploymentFinalState deploymentFinalBout
  simp only [deploymentEffectiveGasPrice, concreteDripTx, concreteDripMessageOutput, hprice]
  have hdelete : (Std.HashSet.emptyWithCapacity : AdrSet).toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    rfl
  rw [hdelete]
  simp only [List.foldl_nil]
  rfl


theorem concreteDripTransactionCode (a : Adr) :
    concreteDripTransactionState.getCode a = concreteJoined.state.getCode a := by
  unfold concreteDripTransactionState deploymentFinalState
  rw [State.addBal_getCode, State.addBal_getCode]
  unfold concreteDripMessageState concreteDripRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  change concreteDripRhoBase.getCode a = _
  unfold concreteDripRhoBase
  rw [Devm.setStorVal_getCode]
  change concreteDripChiBase.getCode a = _
  unfold concreteDripChiBase
  rw [Devm.setStorVal_getCode]
  change concreteDripEntry.state.getCode a = _
  change ((concreteDripDebit.setBal _ _).addBal _ _).getCode a = _
  rw [State.addBal_getCode, State.setBal_getCode]
  unfold concreteDripDebit
  rw [State.setBal_getCode]
  change ((concreteJoined.state.incrNonce concreteCreateSender).get a).code = _
  rw [State.incrNonce_get_code]
  rfl

theorem concreteDrip_receiptEntry :
    concreteDripTransactionBout.receiptsTrie[deploymentReceiptKey 0]? =
      some (makeReceipt concreteDripTx none 32075 []) := by
  change (BlockOutput.init.receiptsTrie.insert (deploymentReceiptKey 0)
    (makeReceipt concreteDripTx none 32075 []))[deploymentReceiptKey 0]? = _
  rw [Std.TreeMap.getElem?_insert_self]

theorem concreteDrip_requestSuffix :
    processGeneralPurposeRequests (concreteDripTxInput.withState concreteDripTransactionState)
      concreteDripTransactionBout = .ok (concreteDripTransactionState, concreteDripTransactionBout) := by
  have hcode (a : Adr) (ha : a ∈ [beaconRootsAddress, historyStorageAddress,
      withdrawalRequestPredeployAddress, consolidationRequestPredeployAddress]) :
      some (concreteDripTransactionState.getCode a).toList = Prog.compile deploymentSystemProgram := by
    rw [concreteDripTransactionCode]
    rw [concreteJoinedCode]
    exact concreteDeployedSystemCode a ha
  obtain ⟨withdrawalOut, hw, _, _, _, _, hwr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (concreteDripTxInput.withState concreteDripTransactionState) withdrawalRequestPredeployAddress []
      (hcode _ (by simp)) (by change ¬ pragueRules.isPrecomp withdrawalRequestPredeployAddress; decide)
  obtain ⟨consolidationOut, hc, _, _, _, _, hcr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((concreteDripTxInput.withState concreteDripTransactionState).withState concreteDripTransactionState)
      consolidationRequestPredeployAddress [] (hcode _ (by simp))
      (by change ¬ pragueRules.isPrecomp consolidationRequestPredeployAddress; decide)
  have hd : parseDepositRequests concreteDripTransactionBout = .ok [] := by
    unfold parseDepositRequests
    have hk : concreteDripTransactionBout.receiptKeys = [deploymentReceiptKey 0] := rfl
    rw [hk]
    simp
    rw [concreteDrip_receiptEntry]
    unfold makeReceipt
    rfl
  unfold processGeneralPurposeRequests
  rw [hd]
  simp only [List.length_nil, Nat.lt_irrefl, if_false, bind, Except.bind]
  rw [hw]
  simp only [hwr, List.length_nil, Nat.lt_irrefl, if_false]
  change (do
    let ⟨st, out⟩ ← processCheckedSystemTransaction
      ((concreteDripTxInput.withState concreteDripTransactionState).withState concreteDripTransactionState)
      consolidationRequestPredeployAddress []
    if out.returnData.length > 0 then
      .ok (st, {concreteDripTransactionBout with requests := concreteDripTransactionBout.requests ++
        [consolidationRequestType ++ out.returnData]})
    else .ok (st, {concreteDripTransactionBout with requests := concreteDripTransactionBout.requests})) = _
  simp only [hc, bind, Except.bind, hcr, List.length_nil, Nat.lt_irrefl, if_false]
  rfl

theorem concreteDrip_body :
    applyBody concreteDripTxInput [.inl concreteDripTxRlp] [] =
      .ok (concreteDripTransactionState, concreteDripTransactionBout) := by
  obtain ⟨beaconOut, hb, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    concreteDripTxInput beaconRootsAddress concreteDripTxInput.stat.parentBeaconBlockRoot.toBytes
    (by change some (concreteJoined.state.getCode _).toList = _
        rw [concreteJoinedCode]; exact concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp beaconRootsAddress; decide)
  obtain ⟨historyOut, hh, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (concreteDripTxInput.withState concreteJoined.state) historyStorageAddress
    concreteJoinBlock.header.hash.toBytes
    (by change some (concreteJoined.state.getCode _).toList = _
        rw [concreteJoinedCode]; exact concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp historyStorageAddress; decide)
  have hl : (concreteDripTxInput.withState concreteJoined.state).stat.blockHashes.getLast? =
      some concreteJoinBlock.header.hash := by rfl
  have hi : (concreteDripTxInput.withState concreteJoined.state).withState concreteJoined.state =
      concreteDripTxInput := rfl
  unfold applyBody
  rw [hb]
  simp only [Except.mapError, bind, Except.bind]
  change (do
    let lastHash ← (concreteDripTxInput.withState concreteJoined.state).stat.blockHashes.getLast?.toExcept
      (TransitionError.internal (.invariant (.text "block hashes is empty")))
    let ⟨stHistory, _⟩ ← Except.mapError TransitionError.vm
      (processUncheckedSystemTransaction (concreteDripTxInput.withState concreteJoined.state)
        historyStorageAddress lastHash.toBytes)
    let ⟨benvTxs, boutTxs⟩ ← applyTransactions
      (← ([.inl concreteDripTxRlp] : List (Bytes ⊕ Tx)).mapM decodeTx).putIndex
      ((concreteDripTxInput.withState concreteJoined.state).withState stHistory) .init
    let ⟨stWds, boutWds⟩ := processWithdrawals benvTxs boutTxs []
    processGeneralPurposeRequests (benvTxs.withState stWds) boutWds) = _
  rw [hl]
  simp only [Option.toExcept, hh, Except.mapError, bind, Except.bind]
  rw [show (concreteDripTxInput.withState concreteJoined.state).state =
    concreteJoined.state from rfl, hi]
  simp only [List.mapM_cons, List.mapM_nil, concreteDripDecode, pure, Except.pure, bind, Except.bind, List.putIndex, List.putIndex.aux,
    applyTransactions, concreteDrip_transaction]
  have hwd (be : Benv) (bo : BlockOutput) : processWithdrawals be bo [] = (be.state, bo) := rfl
  rw [hwd]
  have hwith (be : Benv) : be.withState be.state = be := by cases be; rfl
  simp only [hwith]
  exact concreteDrip_requestSuffix

noncomputable def concreteDripHeader (sr tr rr wr rh : B256) : Header :=
  { concreteDripExecutionHeader with
    gasUsed := 32075
    stateRoot := sr
    txsRoot := tr
    receiptRoot := rr
    withdrawalsRoot := wr
    requestsHash := some rh }

theorem concreteDripHeader_benv (sr tr rr wr rh : B256) :
    initBenv pragueRules concreteJoined (concreteDripHeader sr tr rr wr rh) = concreteDripTxInput := rfl

theorem concreteDripHeader_valid (sr tr rr wr rh : B256) :
    validateHeader pragueRules concreteJoined (concreteDripHeader sr tr rr wr rh) = .ok () := by
  have hlast : concreteJoined.blocks.getLast? = some concreteJoinBlock :=
    appendBlock_getLast? concreteDeployed.blocks concreteJoinBlock
  simp only [validateHeader, hlast, Option.toExcept, bind, Except.bind,
    concreteDripHeader, concreteDripExecutionHeader, Header.hash, ne_eq, not_true_eq_false, ite_false]
  simp only [concreteJoinBlock, concreteJoinHeader, concreteJoinExecutionHeader, concreteDeploymentEnvelope, concreteCanonicalBlock, CanonicalBlock.ofDecode,
    concreteDeploymentBlock, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader]
  decide +kernel

noncomputable def concreteDripBlock : Block := {
  header := concreteDripHeader concreteDripTransactionState.root
    (getTransactionsRoot concreteDripTransactionBout) (getReceiptRoot concreteDripTransactionBout)
    (getWithdrawalsRoot concreteDripTransactionBout) (computeRequestsHash concreteDripTransactionBout.requests)
  txs := [.inl concreteDripTxRlp]
  ommers := []
  wds := [] }

noncomputable def concreteDripped : BlockChain :=
  ⟨appendBlock concreteJoined.blocks concreteDripBlock, concreteDripTransactionState, concreteJoined.chainId⟩

theorem concreteDrip_checks :
    stateTransitionChecks concreteDripTransactionBout concreteDripBlock.header
      (getTransactionsRoot concreteDripTransactionBout) concreteDripTransactionState.root
      (getReceiptRoot concreteDripTransactionBout) (logsBloom concreteDripTransactionBout.blockLogs)
      (getWithdrawalsRoot concreteDripTransactionBout)
      (computeRequestsHash concreteDripTransactionBout.requests) = .ok () := by
  have hg : concreteDripTransactionBout.blockGasUsed = 32075 := rfl
  have hl : concreteDripTransactionBout.blockLogs = [] := rfl
  have hb : concreteDripTransactionBout.blobGasUsed = 0 := rfl
  simp only [stateTransitionChecks, hg, hl, hb, concreteDripBlock, concreteDripHeader,
    concreteDripExecutionHeader, concreteJoinBlock, concreteJoinHeader, concreteJoinExecutionHeader, concreteDeploymentEnvelope, concreteCanonicalBlock,
    CanonicalBlock.ofDecode, concreteDeploymentBlock, concreteDeploymentHeader,
    concreteExecutionHeader, concreteGenesisHeader, logsBloom, List.foldl_nil,
    ne_eq, not_true_eq_false, ite_false, pure, Bind.bind, Except.bind]
  rfl

theorem concreteDrip_step :
    stateTransitionUsing concreteConfig concreteJoined concreteDripBlock = .ok concreteDripped := by
  have hchain : concreteConfig.chainId = concreteJoined.chainId := concreteDeploymentRoot.deployed_chainId
  rw [stateTransitionUsing_eq_of_chainId_eq hchain]
  rw [show concreteConfig.rulesAt concreteDripBlock.header.timestamp = .ok pragueRules from
    ChainConfig.pragueOnly_rulesAt 1 _]
  change stateTransitionWith pragueRules concreteJoined concreteDripBlock = _
  rw [stateTransitionWith_eq_ok_iff, stateTransitionE]
  have hh : validateHeader pragueRules concreteJoined concreteDripBlock.header = .ok () :=
    concreteDripHeader_valid _ _ _ _ _
  rw [hh]
  change (do
    let output ← applyBody (initBenv pragueRules concreteJoined concreteDripBlock.header)
      concreteDripBlock.txs concreteDripBlock.wds
    Except.mapError TransitionError.block (stateTransitionChecks output.2
      concreteDripBlock.header (getTransactionsRoot output.2) output.1.root
      (getReceiptRoot output.2) (logsBloom output.2.blockLogs)
      (getWithdrawalsRoot output.2) (computeRequestsHash output.2.requests))
    .ok (⟨appendBlock concreteJoined.blocks concreteDripBlock, output.1,
      concreteJoined.chainId⟩ : BlockChain)) = .ok concreteDripped
  have hbody : applyBody (initBenv pragueRules concreteJoined concreteDripBlock.header)
      concreteDripBlock.txs concreteDripBlock.wds =
      .ok (concreteDripTransactionState, concreteDripTransactionBout) := by
    change applyBody (initBenv pragueRules concreteJoined (concreteDripHeader _ _ _ _ _))
      [.inl concreteDripTxRlp] [] = _
    rw [concreteDripHeader_benv]
    exact concreteDrip_body
  rw [hbody]
  simp only [Bind.bind, Except.bind, concreteDrip_checks, Except.mapError]
  rfl

theorem concreteDripped_storage : concreteDripped.state.getStor concreteCreateTarget =
    ((concreteJoined.state.getStor concreteCreateTarget).set chiSlot concreteDripChi).set rhoSlot 5 := by
  change concreteDripTransactionState.getStor concreteCreateTarget = _
  unfold concreteDripTransactionState deploymentFinalState State.getStor State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteDripMessageState concreteDripRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  change Devm.getStor concreteDripRhoBase concreteCreateTarget = _
  unfold concreteDripRhoBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteDripChiBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  have hs : Devm.getStor concreteDripStorageBase concreteCreateTarget =
      (concreteJoined.state.get concreteCreateTarget).stor := by
    change (concreteDripEntry.state.get concreteCreateTarget).stor = _
    exact concreteDripEntry_storage _
  rw [hs]

theorem concreteDripped_values :
    (concreteDripped.state.getStor concreteCreateTarget).get chiSlot = concreteDripChi ∧
    (concreteDripped.state.getStor concreteCreateTarget).get rhoSlot = 5 ∧
    (concreteDripped.state.getStor concreteCreateTarget).get concreteCreateSender.toB256 = 99 ∧
    (concreteDripped.state.getStor concreteCreateTarget).get totalUnitsSlot = 99 := by
  rw [concreteDripped_storage]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · exact Stor.get_set_self _ _ _
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel)]
    exact concreteJoined_values.2.2.1
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel)]
    exact concreteJoined_values.2.2.2

theorem concreteDrip_receiptSucceeded :
    (concreteDripTransactionBout.receiptsTrie[deploymentReceiptKey 0]?).map
      (fun entry => entry.2.succeeded) = some true := by
  rw [concreteDrip_receiptEntry]
  rfl

theorem concreteDrip_observations :
    concreteDripMessageOutput.returnData = concreteDripChi.toBytes ∧
    concreteDripTransactionBout.blockGasUsed = 32075 ∧
    concreteDripTransactionBout.blockLogs = [] ∧
    concreteDripBlock.header.timestamp = 5 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem concreteDripMessageState_sender :
    concreteDripMessageState.get concreteCreateSender = concreteDripEntry.state.get concreteCreateSender := by
  unfold concreteDripMessageState concreteDripRuntimePost
  rw [Devm.withOutput_state, Devm.setMach_state]
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  change (((concreteDripEntry.state.setStorVal concreteCreateTarget chiSlot concreteDripChi).setStorVal
    concreteCreateTarget rhoSlot 5).get concreteCreateSender) = _
  simp only [State.setStorVal, State.get_set_ne _ ht]

theorem concreteDrippedSenderNonce : concreteDripped.state.getNonce concreteCreateSender = 3 := by
  change (concreteDripTransactionState.get concreteCreateSender).nonce = _
  unfold concreteDripTransactionState deploymentFinalState
  change (((concreteDripMessageState.addBal concreteCreateSender 935850).addBal 0 32075).get
    concreteCreateSender).nonce = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  rw [concreteDripMessageState_sender]
  change ((((concreteDripDebit.setBal concreteCreateSender
    (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateSender).nonce) = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  unfold concreteDripDebit
  simp only [State.setBal_get_self, State.incrNonce, State.get_set_self]
  change (concreteJoined.state.getNonce concreteCreateSender) + 1 = 3
  rw [concreteJoinedSenderNonce]
  rfl

theorem concreteDrippedSenderBalance : concreteDripped.state.bal concreteCreateSender = 999999999998823644 := by
  change (concreteDripTransactionState.get concreteCreateSender).bal = _
  unfold concreteDripTransactionState deploymentFinalState
  change (((concreteDripMessageState.addBal concreteCreateSender 935850).addBal 0 32075).get
    concreteCreateSender).bal = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  change (concreteDripMessageState.get concreteCreateSender).bal + 935850 = _
  rw [concreteDripMessageState_sender]
  change ((((concreteDripDebit.setBal concreteCreateSender
    (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateSender).bal) + 935850 = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  change (concreteDripDebit.bal concreteCreateSender - 0) + 935850 = _
  rw [concreteDripDebit_balance]
  decide +kernel

theorem concreteDrippedCode (a : Adr) :
    concreteDripped.state.getCode a = concreteJoined.state.getCode a := concreteDripTransactionCode a

def concreteExitTx : Tx := {
  nonce := 3
  gas := 500000
  value := 0
  data := [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28]
  v := 1
  r := (0x2c0058ac7e7b06e684ece60a8968d4fa9baee82b97db878467bc1637d680b80a : B256).toBytes
  s := (0x149ab14861a161a3b2c4448817f8031f3516a24cd5a55220aa471fc67063a424 : B256).toBytes
  type := .two 1 1 8 (some concreteCreateTarget) [] }

def concreteExitSigningPayload : Bytes :=
  [0x02, 0xf8, 0x44, 1, 3, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++
  concreteCreateTarget.toBytes ++ [0x80, 0xa4] ++ [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28] ++ [0xc0]

theorem concreteExitSigningEncoded :
    concreteExitTx.signingHash = some concreteExitSigningPayload.keccak := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 3).sig = [3] := by decide +kernel
  have ht : (BLT.bytes concreteCreateTarget.toBytes).toBytes =
      0x94 :: concreteCreateTarget.toBytes := by
    rw [RlpConcrete.encode_bytes_many _ (by decide +kernel)]
    rfl
  have hlen : concreteCreateTarget.toBytes.length = 20 := rfl
  simp only [Tx.signingHash, concreteExitTx, hc, hn, AccessList.toBLT, List.map_nil]
  apply congrArg some
  apply congrArg Bytes.keccak
  change 2 :: (BLT.list [.bytes [1], .bytes [3], .bytes (Nat.toBytes 1),
    .bytes (Nat.toBytes 8), .bytes (Nat.toBytes 500000), .bytes concreteCreateTarget.toBytes,
    .bytes (Nat.toBytes 0), .bytes [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28], .list []]).toBytes = _
  simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, ht, hlen,
    Nat.toBytes, Nat.toBytes.aux, concreteExitSigningPayload]
  rw [show Nat.toBytesPack 68 = [68] by decide +kernel]
  exact ⟨rfl, rfl⟩

theorem concreteExitSigningHash :
    concreteExitTx.signingHash =
      some (0x22c4bcb62ad0275fea1abcb8e2238dd2b59b0a62d83c953ed26e59ed645af53c : B256) := by
  rw [concreteExitSigningEncoded]
  decide +kernel

theorem concreteExitRecoveredSender :
    recoverSender 1 concreteExitTx = .ok concreteCreateSender := by
  rw [recoverSender, concreteExitSigningHash]
  decide +kernel

def concreteExitFields : List BLT :=
  [.bytes [1], .bytes [3], .bytes [1], .bytes [8], .bytes [7, 0xa1, 0x20],
   .bytes concreteCreateTarget.toBytes, .bytes [], .bytes [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28],
   .list [], .bytes [1], .bytes concreteExitTx.r, .bytes concreteExitTx.s]

def concreteExitPayload : Bytes :=
  [1, 3, 1, 8, 0x83, 7, 0xa1, 0x20, 0x94] ++ concreteCreateTarget.toBytes ++
  [0x80, 0xa4] ++ [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28] ++ [0xc0, 1, 0xa0] ++ concreteExitTx.r ++
  [0xa0] ++ concreteExitTx.s

def concreteExitTxRlp : Bytes := [2, 0xf8, 0x87] ++ concreteExitPayload

theorem concreteExitBLT : concreteExitTx.toBLT = .list concreteExitFields := by
  have hc : (UInt64.toBytes 1).sig = [1] := by decide +kernel
  have hn : (UInt64.toBytes 3).sig = [3] := by decide +kernel
  have hr : trimZero concreteExitTx.r = concreteExitTx.r := by decide +kernel
  have hs : trimZero concreteExitTx.s = concreteExitTx.s := by decide +kernel
  simp only [Tx.toBLT, concreteExitTx, hc, AccessList.toBLT, List.map_nil]
  simp [concreteExitFields, concreteExitTx, Nat.toBytes, Nat.toBytes.aux]
  exact ⟨hr, hs⟩

theorem concreteExitPayloadParse (k : Nat) :
    Bytes.toBLTs? (k + 12) concreteExitPayload = some concreteExitFields := by
  unfold concreteExitPayload concreteExitFields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 3 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 8 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_three _ [7, 0xa1, 0x20] _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 _ _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 36 [0x7f, 0x86, 0x61, 0xa1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x28] _ (by decide) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_list _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ 1 _ rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_32 _ _ _ rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil] using RlpConcrete.decode_bytes_32 k concreteExitTx.s [] rfl
  rw [Bytes.toBLTs?]

theorem concreteExitPayload_length : concreteExitPayload.length = 135 := by
  simp only [concreteExitPayload, List.length_append, List.length_cons, List.length_nil]
  rfl

theorem concreteExitEnvelopeParse :
    Bytes.toBLT? (0xf8 :: 0x87 :: concreteExitPayload) = some (.list concreteExitFields) := by
  have hsplit : Jaune.List.splitAt? 135 concreteExitPayload = some (concreteExitPayload, []) := by
    simpa only [concreteExitPayload_length, List.append_nil] using
      RlpConcrete.splitAt_append concreteExitPayload ([] : Bytes)
  have hp : Bytes.toBLTDiff? 137 (0xf8 :: 0x87 :: concreteExitPayload) =
      some (.list concreteExitFields, []) := by
    rw [Bytes.toBLTDiff?]
    change (do
      let p ← Jaune.List.splitAt? 1 ([0x87] ++ concreteExitPayload)
      let q ← Jaune.List.splitAt? (Bytes.toNat p.1) p.2
      let rs ← Bytes.toBLTs? 136 q.1
      pure (BLT.list rs, q.2)) = _
    rw [show Jaune.List.splitAt? 1 ([0x87] ++ concreteExitPayload) =
      some ([0x87], concreteExitPayload) from
        RlpConcrete.splitAt_append [0x87] concreteExitPayload]
    change (do
      let q ← Jaune.List.splitAt? 135 concreteExitPayload
      let rs ← Bytes.toBLTs? 136 q.1
      pure (BLT.list rs, q.2)) = _
    rw [hsplit]
    change (do let rs ← Bytes.toBLTs? 136 concreteExitPayload; pure (BLT.list rs, [])) = _
    rw [concreteExitPayloadParse 124]
    rfl
  unfold Bytes.toBLT?
  simp only [List.length_cons, concreteExitPayload_length]
  rw [hp]

theorem concreteExitDecode : decodeTx (.inl concreteExitTxRlp) = .ok concreteExitTx := by
  simp only [decodeTx, concreteExitTxRlp, List.cons_append, List.nil_append,
    Bytes.toExTx, concreteExitEnvelopeParse, concreteExitFields]
  rfl


noncomputable def concreteExitExecutionHeader : Header :=
  { concreteDripBlock.header with
    parentHash := concreteDripBlock.header.hash
    number := 4
    gasUsed := 0
    timestamp := 6 }

theorem concreteDrippedSenderCode : concreteDripped.state.getCode concreteCreateSender = ByteArray.empty := by
  rw [concreteDrippedCode]
  exact concreteJoinedSenderCode

theorem concreteExitSenderChecked :
    checkTransactionSenderAccount (concreteDripped.state.get concreteCreateSender)
      concreteExitTx 4000000 = .ok () := by
  have hn : (concreteDripped.state.get concreteCreateSender).nonce = 3 := concreteDrippedSenderNonce
  have hb : (concreteDripped.state.get concreteCreateSender).bal = 999999999998823644 :=
    concreteDrippedSenderBalance
  have hc : (concreteDripped.state.get concreteCreateSender).code = ByteArray.empty :=
    concreteDrippedSenderCode
  simp only [checkTransactionSenderAccount, hn, hb, checkTransactionSenderCode, hc]
  decide +kernel

theorem concreteExitValidated :
    validateTransaction pragueRules concreteExitTx = .ok (calculateIntrinsicCost concreteExitTx) := by
  decide +kernel

theorem concreteExitChecked :
    checkTransaction (initBenv pragueRules concreteDripped concreteExitExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteExitTx 0) concreteExitTx =
      .ok (concreteCreateSender, 2, [], 0) := by
  have hgas : checkTransactionGasLimits
      (initBenv pragueRules concreteDripped concreteExitExecutionHeader).beginTransaction
      (deploymentTxPreludeBout .init concreteExitTx 0) concreteExitTx = .ok 0 := by decide +kernel
  have hchain : checkTransactionChainId
      (initBenv pragueRules concreteDripped concreteExitExecutionHeader).beginTransaction
      concreteExitTx = .ok () := by decide +kernel
  have hfee : checkTransactionGasFee
      (initBenv pragueRules concreteDripped concreteExitExecutionHeader).beginTransaction
      concreteExitTx = .ok (2, 4000000) := by decide +kernel
  rw [checkTransaction, hgas]
  simp only [Except.mapError, bind, Except.bind]
  rw [hchain]
  change (do
    let sender ← Except.mapError TransitionError.senderRecovery (recoverSender 1 concreteExitTx)
    let (effective, maxFee) ← Except.mapError TransitionError.transaction
      (checkTransactionGasFee (initBenv pragueRules concreteDripped concreteExitExecutionHeader).beginTransaction concreteExitTx)
    let (maxFee, hashes) ← Except.mapError TransitionError.transaction
      (checkTransactionBlobData (initBenv pragueRules concreteDripped concreteExitExecutionHeader).beginTransaction concreteExitTx maxFee)
    Except.mapError TransitionError.transaction (checkTransactionReceiver concreteExitTx)
    Except.mapError TransitionError.transaction (checkTransactionAuthorizationList concreteExitTx)
    Except.mapError TransitionError.transaction (checkTransactionSenderAccount (concreteDripped.state.get sender) concreteExitTx maxFee)
    pure (sender, effective, hashes, 0)) = _
  rw [concreteExitRecoveredSender, hfee]
  change (do
    Except.mapError TransitionError.transaction
      (checkTransactionSenderAccount (concreteDripped.state.get concreteCreateSender) concreteExitTx 4000000)
    pure (concreteCreateSender, 2, [], 0)) = _
  rw [concreteExitSenderChecked]
  rfl

noncomputable def concreteExitTxInput : Benv :=
  initBenv pragueRules concreteDripped concreteExitExecutionHeader

noncomputable def concreteExitDebit : State :=
  let nonceState := concreteDripped.state.incrNonce concreteCreateSender
  nonceState.setBal concreteCreateSender (nonceState.bal concreteCreateSender - 1000000)

theorem concreteExitDebit_run :
    (concreteExitTxInput.beginTransaction.state.incrNonce concreteCreateSender).subBal
      concreteCreateSender 1000000 = some concreteExitDebit := by
  have hb : (concreteDripped.state.incrNonce concreteCreateSender).bal concreteCreateSender =
      999999999998823644 := by
    unfold State.bal
    rw [State.incrNonce_get_bal]
    exact concreteDrippedSenderBalance
  change (concreteDripped.state.incrNonce concreteCreateSender).subBal concreteCreateSender
    1000000 = _
  unfold State.subBal
  rw [hb, if_neg (by decide +kernel)]
  unfold concreteExitDebit
  dsimp only
  rw [hb]

noncomputable def concreteExitTenv : Tenv :=
  deploymentTenv concreteExitTxInput concreteExitTx concreteCreateSender 0

noncomputable def concreteExitMessage : Msg := {
  benv := { concreteExitTxInput.beginTransaction with state := concreteExitDebit }
  tenv := concreteExitTenv
  caller := concreteCreateSender
  target := some concreteCreateTarget
  currentTarget := concreteCreateTarget
  gas := concreteExitTenv.stat.gas
  value := 0
  data := concreteExitTx.data
  code := concreteExitDebit.getCode concreteCreateTarget
  codeAddress := some concreteCreateTarget
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := concreteExitTenv.stat.accessListAddresses.insertMany
    (pragueRules.precompiles ++ [concreteCreateSender, concreteCreateTarget])
  accessedStorageKeys := concreteExitTenv.stat.accessListStorageKeys
  disablePrecompiles := false }

theorem concreteExitMessage_prepared :
    prepareMessage { concreteExitTxInput.beginTransaction with state := concreteExitDebit }
      concreteExitTenv concreteExitTx = .ok concreteExitMessage := rfl

theorem concreteExitMessage_code : concreteExitMessage.code.toList = code := by
  change (concreteExitDebit.getCode concreteCreateTarget).toList = code
  unfold concreteExitDebit
  rw [State.setBal_getCode]
  change ((concreteDripped.state.incrNonce concreteCreateSender).get concreteCreateTarget).code.toList = code
  rw [State.incrNonce_get_code]
  change (concreteDripped.state.getCode concreteCreateTarget).toList = code
  rw [concreteDrippedCode, concreteJoinedCode, concreteDeploymentRoot.installed]
  simp [ByteArray.toList_eq_toList_data]

theorem concreteExitDebit_balance :
    concreteExitDebit.bal concreteCreateSender = 999999999997823644 := by
  unfold concreteExitDebit
  change ((concreteDripped.state.incrNonce concreteCreateSender).setBal concreteCreateSender
    ((concreteDripped.state.incrNonce concreteCreateSender).bal concreteCreateSender - 1000000)).bal _ = _
  unfold State.bal
  rw [State.setBal_get_self, State.incrNonce_get_bal]
  change concreteDripped.state.bal concreteCreateSender - 1000000 = _
  rw [concreteDrippedSenderBalance]
  decide +kernel

noncomputable def concreteExitEntry : Benv :=
  concreteExitMessage.benv.withState
    ((concreteExitDebit.setBal concreteCreateSender
      (concreteExitDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0)

theorem concreteExitEntry_run :
    concreteExitMessage.benvAfterTransfer = .ok concreteExitEntry := by
  unfold concreteExitEntry concreteExitMessage
  generalize concreteExitDebit = debit
  generalize concreteExitTxInput.beginTransaction = begun
  generalize concreteExitTenv = tenv
  have hnot : ¬ debit.bal concreteCreateSender < (0 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero]
    omega
  simp only [Msg.benvAfterTransfer, if_true, Benv.subBal, State.subBal, hnot, if_false,
    bind, Option.bind, Option.toExcept, Except.bind, Benv.addBal, Benv.withState]

theorem concreteExitEntry_storage (address : Adr) :
    (concreteExitEntry.state.get address).stor = (concreteDripped.state.get address).stor := by
  change (((concreteExitDebit.setBal _ _).addBal _ _).get address).stor = _
  unfold State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor]
  unfold concreteExitDebit
  dsimp only
  rw [State.setBal_get_stor, State.incrNonce_get_stor]


noncomputable def concreteExitSevm : Sevm := initSevm (concreteExitMessage.withBenv concreteExitEntry)
noncomputable def concreteExitDevm : Devm := initDevm (concreteExitMessage.withBenv concreteExitEntry)

theorem concreteExitDevm_chi : concreteExitDevm.getStorVal concreteCreateTarget chiSlot = concreteDripChi := by
  change (concreteExitEntry.state.get concreteCreateTarget).stor.get chiSlot = concreteDripChi
  rw [concreteExitEntry_storage]
  exact concreteDripped_values.1

theorem concreteExitDevm_rho : concreteExitDevm.getStorVal concreteCreateTarget rhoSlot = 5 := by
  change (concreteExitEntry.state.get concreteCreateTarget).stor.get rhoSlot = 5
  rw [concreteExitEntry_storage]
  exact concreteDripped_values.2.1

theorem concreteExitDevm_cold (k : B256) :
    (concreteCreateTarget, k) ∉ concreteExitDevm.accessedStorageKeys := by
  change (concreteCreateTarget, k) ∉ (∅ : Std.HashSet (Adr × B256))
  simp

theorem concreteJoinedTargetBalance : concreteJoined.state.bal concreteCreateTarget = 100 := by
  have hm : concreteJoinMessageState.bal concreteCreateTarget = concreteJoinEntry.state.bal concreteCreateTarget := by
    unfold concreteJoinMessageState concreteJoinRuntimePost
    rw [Devm.withOutput_state, Devm.setMach_state]
    have hs (d : Devm) (k v : B256) :
        (d.setStorVal concreteCreateTarget k v).getBal concreteCreateTarget =
          d.getBal concreteCreateTarget :=
      (Devm.StateWriteFrame.getBal_eq (Devm.setStorVal_stateWriteFrame d _ k v) _).symm
    change (concreteJoinTotalBase).getBal concreteCreateTarget = _
    unfold concreteJoinTotalBase
    rw [hs]
    change (concreteJoinRowBase).getBal concreteCreateTarget = _
    unfold concreteJoinRowBase
    rw [hs]
    change (concreteJoinRhoBase).getBal concreteCreateTarget = _
    unfold concreteJoinRhoBase
    rw [hs]
    change (concreteJoinChiBase).getBal concreteCreateTarget = _
    unfold concreteJoinChiBase
    rw [hs]
    rfl
  have hz : (0 : Adr) ≠ concreteCreateTarget := by decide +kernel
  have ht : concreteCreateSender ≠ concreteCreateTarget := by decide +kernel
  change (concreteJoinTransactionState.get concreteCreateTarget).bal = _
  unfold concreteJoinTransactionState deploymentFinalState
  change (((concreteJoinMessageState.addBal concreteCreateSender 847712).addBal 0 76144).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_ne ht]
  change concreteJoinMessageState.bal concreteCreateTarget = _
  rw [hm]
  change (((concreteJoinDebit.setBal concreteCreateSender
    (concreteJoinDebit.bal concreteCreateSender - 100)).addBal concreteCreateTarget 100).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_self, State.setBal_get_ne ht, Acct.withBal]
  simp only [State.bal, State.setBal_get_ne ht]
  change concreteJoinDebit.bal concreteCreateTarget + 100 = _
  unfold concreteJoinDebit State.bal
  rw [State.setBal_get_ne ht, State.incrNonce_get_bal]
  change concreteDeployed.state.bal concreteCreateTarget + 100 = _
  rw [concreteDeploymentRoot.bal]
  decide +kernel

theorem concreteDrippedTargetBalance : concreteDripped.state.bal concreteCreateTarget = 100 := by
  have hm : concreteDripMessageState.bal concreteCreateTarget = concreteDripEntry.state.bal concreteCreateTarget := by
    unfold concreteDripMessageState concreteDripRuntimePost
    rw [Devm.withOutput_state, Devm.setMach_state]
    have hs (d : Devm) (k v : B256) :
        (d.setStorVal concreteCreateTarget k v).getBal concreteCreateTarget =
          d.getBal concreteCreateTarget :=
      (Devm.StateWriteFrame.getBal_eq (Devm.setStorVal_stateWriteFrame d _ k v) _).symm
    change (concreteDripRhoBase).getBal concreteCreateTarget = _
    unfold concreteDripRhoBase
    rw [hs]
    change (concreteDripChiBase).getBal concreteCreateTarget = _
    unfold concreteDripChiBase
    rw [hs]
    rfl
  have hz : (0 : Adr) ≠ concreteCreateTarget := by decide +kernel
  have ht : concreteCreateSender ≠ concreteCreateTarget := by decide +kernel
  change (concreteDripTransactionState.get concreteCreateTarget).bal = _
  unfold concreteDripTransactionState deploymentFinalState
  change (((concreteDripMessageState.addBal concreteCreateSender 935850).addBal 0 32075).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_ne ht]
  change concreteDripMessageState.bal concreteCreateTarget = _
  rw [hm]
  change (((concreteDripDebit.setBal concreteCreateSender
    (concreteDripDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_self, State.setBal_get_ne ht, Acct.withBal]
  simp only [State.bal, State.setBal_get_ne ht]
  change concreteDripDebit.bal concreteCreateTarget + 0 = _
  unfold concreteDripDebit State.bal
  rw [State.setBal_get_ne ht, State.incrNonce_get_bal]
  change concreteJoined.state.bal concreteCreateTarget + 0 = _
  rw [concreteJoinedTargetBalance]
  decide +kernel

theorem concreteExitDevm_balance : concreteExitDevm.getBal concreteCreateTarget = 100 := by
  have ht : concreteCreateSender ≠ concreteCreateTarget := by decide +kernel
  change (((concreteExitDebit.setBal concreteCreateSender
    (concreteExitDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateTarget).bal = _
  simp only [State.addBal, State.setBal_get_self, State.setBal_get_ne ht, Acct.withBal]
  simp only [State.bal, State.setBal_get_ne ht]
  change concreteExitDebit.bal concreteCreateTarget + 0 = _
  unfold concreteExitDebit State.bal
  rw [State.setBal_get_ne ht, State.incrNonce_get_bal]
  change concreteDripped.state.bal concreteCreateTarget + 0 = _
  rw [concreteDrippedTargetBalance]
  decide +kernel

def concreteExitArgumentMemory : Mem :=
  ((Mem.empty.write 64 (40 : B256).toBytes).write 96 (99 : B256).toBytes).write 128 (99 : B256).toBytes

def concreteExitStagingMemory : Mem := concreteExitArgumentMemory.write 32 (2 : B256).toBytes

private theorem concreteExit_stage (base post : Devm) (G : Nat)
    (hrow : base.getStorVal concreteCreateTarget concreteCreateSender.toB256 = 99)
    (htotal : base.getStorVal concreteCreateTarget totalUnitsSlot = 99)
    (hcoldRow : (concreteCreateTarget, concreteCreateSender.toB256) ∉ base.accessedStorageKeys)
    (hcoldTotal : (concreteCreateTarget, totalUnitsSlot) ∉ base.accessedStorageKeys)
    (hfresh : Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      ((concreteJoinStagingBase base).setMach ⟨[], concreteExitStagingMemory, G⟩)
      freshStart post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (base.setMach ⟨[], Mem.empty, G + 4387⟩) exit post := by
  have harg : Sevm.dataWord concreteExitSevm (32 * 0 + 4) = 40 := by
    change Bytes.toB256 (concreteExitTx.data.sliceD 4 32 0) = 40
    decide +kernel
  func_run (2)
  rw [harg]
  func_run (7) [9, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  func_run (1)
  simp only [Devm.getStorVal_setMach]
  change Func.RunCompiled _ concreteExitSevm
    ((addAccessedStorageKey _ concreteCreateTarget concreteCreateSender.toB256).setMach
      ⟨[base.getStorVal concreteCreateTarget concreteCreateSender.toB256],
        Mem.empty.write 64 (40 : B256).toBytes, G + 4387 - 2145⟩) _ post
  rw [hrow]
  func_run (7) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteExitSevm
    ((addAccessedStorageKey base concreteCreateTarget concreteCreateSender.toB256).setMach
      ⟨[totalUnitsSlot], (Mem.empty.write 64 (40 : B256).toBytes).write 96 (99 : B256).toBytes,
        G + 4387 - 2179⟩) _ post
  func_run (1)
  · change (concreteCreateTarget, totalUnitsSlot) ∉
      base.accessedStorageKeys.insert (concreteCreateTarget, concreteCreateSender.toB256)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by decide +kernel, hcoldTotal⟩
  change Func.RunCompiled _ concreteExitSevm
    ((concreteJoinStagingBase base).setMach
      ⟨[base.getStorVal concreteCreateTarget totalUnitsSlot],
        (Mem.empty.write 64 (40 : B256).toBytes).write 96 (99 : B256).toBytes,
        G + 4387 - 4279⟩) _ post
  rw [htotal]
  func_run (6) [3, 0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteExitSevm
    ((concreteJoinStagingBase base).setMach ⟨[], concreteExitArgumentMemory, G + 4387 - 4310⟩) _ post
  have hs : concreteExitArgumentMemory.size = 160 := by decide +kernel
  have ha : Bytes.toB256 (concreteExitArgumentMemory.read 64 32).1 = 40 := by decide +kernel
  have hr : Bytes.toB256 (concreteExitArgumentMemory.read 96 32).1 = 99 := by decide +kernel
  have ht : Bytes.toB256 (concreteExitArgumentMemory.read 128 32).1 = 99 := by decide +kernel
  have hm (n : Nat) (hn : n + 32 ≤ 160) :
      (concreteExitArgumentMemory.read n 32).2 = concreteExitArgumentMemory :=
    Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le (by decide) hn)
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hs]
    decide +kernel
  rw [show (argumentWord * 32).toNat = 64 by decide +kernel, ha, hm 64 (by decide)]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hs]
    decide +kernel
  rw [show (rowWord * 32).toNat = 96 by decide +kernel, hr, hm 96 (by decide)]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hs]
    decide +kernel
  rw [show (argumentWord * 32).toNat = 64 by decide +kernel, ha, hm 64 (by decide)]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hs]
    decide +kernel
  rw [show (totalWord * 32).toNat = 128 by decide +kernel, ht, hm 128 (by decide)]
  func_run (2) [0]
  func_run (3) [0]
  · simp only [Devm.extCost, Devm.memory_setMach]
    decide +kernel
  change Func.RunCompiled _ concreteExitSevm
    ((concreteJoinStagingBase base).setMach ⟨[], concreteExitStagingMemory, G + 4387 - 4375⟩)
    (.call freshStartSlot) post
  apply Func.runCompiled_call' (f := freshStart) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hfresh

private theorem concreteExit_readChi (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat) (next : Func)
    (hchi : base.getStorVal sevm.currentTarget chiSlot = concreteDripChi)
    (hcold : (sevm.currentTarget, chiSlot) ∉ base.accessedStorageKeys)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((addAccessedStorageKey base sevm.currentTarget chiSlot).setMach ⟨[concreteDripChi], M, G⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 2103⟩)
      (Ninst.pushB256 chiSlot ::: Ninst.sload ::: next) post := by
  func_run (2)
  change Func.RunCompiled _ sevm
    ((addAccessedStorageKey base sevm.currentTarget chiSlot).setMach
      ⟨[base.getStorVal sevm.currentTarget chiSlot], M, G + 2103 - 2103⟩) next post
  simpa only [hchi, Nat.add_sub_cancel] using htail


private theorem concreteExit_stageClock (sevm : Sevm) (base post : Devm) (M C : Mem)
    (G : Nat) (next : Func) (htime : sevm.benvStat.time = 6)
    (hsize : M.size = 160)
    (hstore : M.write (storedChiWord * 32).toNat concreteDripChi.toBytes = C)
    (hcsize : C.size = 192)
    (hread : Bytes.toB256 (C.read (storedChiWord * 32).toNat 32).1 = concreteDripChi)
    (hmem : (C.read (storedChiWord * 32).toNat 32).2 = C)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], C.write 192 (6 : B256).toBytes, G⟩) next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteDripChi], M, G + 70⟩)
      (mstoreAt storedChiWord +++
        (Ninst.pushB256 scale ::: loadWord storedChiWord +++ Ninst.lt :::
          (.revert <?>
            (loadWord storedChiWord +++ Ninst.pushB256 maxChi ::: Ninst.lt :::
              (.revert <?> (Ninst.timestamp ::: mstoreAt nowWord +++ next)))))) post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [hread, hmem]
  func_run (3) [0]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hcsize]
    decide +kernel
  rw [htime]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[], C.write 192 (6 : B256).toBytes, G + 70 - 70⟩) next post
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteExit_stageElapsed (sevm : Sevm) (base post : Devm) (M E : Mem)
    (G : Nat) (next : Func)
    (hrho : base.getStorVal sevm.currentTarget rhoSlot = 5)
    (hcold : (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hsize : M.size = 224)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 6)
    (hmem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hstore : M.write (exponentWord * 32).toNat (1 : B256).toBytes = E)
    (hesize : E.size = 224)
    (hexp : Bytes.toB256 (E.read (exponentWord * 32).toNat 32).1 = 1)
    (hemem : (E.read (exponentWord * 32).toNat 32).2 = E)
    (htail : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((addAccessedStorageKey base sevm.currentTarget rhoSlot).setMach ⟨[], E, G⟩)
      next post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 2166⟩)
      (Ninst.pushB256 rhoSlot ::: Ninst.sload ::: Ninst.dup 0 :::
        loadWord nowWord +++ Ninst.lt :::
          (.revert <?> (loadWord nowWord +++ Ninst.sub :::
            mstoreAt exponentWord +++ loadWord exponentWord +++
            Ninst.pushB256 maxElapsed ::: Ninst.lt ::: (.revert <?> next)))) post := by
  func_run (2)
  change Func.RunCompiled _ sevm
    ((addAccessedStorageKey base sevm.currentTarget rhoSlot).setMach
      ⟨[base.getStorVal sevm.currentTarget rhoSlot], M, G + 2166 - 2103⟩) _ post
  rw [hrho]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hmem]
  func_run (3) [1, 0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hstore]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hesize]
    decide +kernel
  rw [hexp, hemem]
  func_run (3) [0]
  simpa only [Nat.add_sub_cancel] using htail

private theorem concreteExit_initializeRpow (sevm : Sevm) (base post : Devm) (M B A Z : Mem)
    (G : Nat) (zeroBase zeroExponent evenExponent : Func)
    (hsize : M.size = 224)
    (hbase : M.write (baseWord * 32).toNat rate.toBytes = B)
    (hbsize : B.size = 256)
    (hbexp : Bytes.toB256 (B.read (exponentWord * 32).toNat 32).1 = 1)
    (hbmem : (B.read (exponentWord * 32).toNat 32).2 = B)
    (hacc : B.write (accumulatorWord * 32).toNat rate.toBytes = A)
    (hasize : A.size = 288)
    (haexp : Bytes.toB256 (A.read (exponentWord * 32).toNat 32).1 = 1)
    (hamem : (A.read (exponentWord * 32).toNat 32).2 = A)
    (hzero : A.write (exponentWord * 32).toNat (0 : B256).toBytes = Z)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Z, G⟩) rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 122⟩)
      (Ninst.pushB256 rate ::: Ninst.dup 0 ::: mstoreAt baseWord +++ Ninst.iszero :::
        (zeroBase <?> (loadWord exponentWord +++ Ninst.iszero :::
          (zeroExponent <?> (loadWord exponentWord +++ Ninst.pushB256 1 ::: Ninst.and :::
            ((Ninst.pushB256 rate ::: mstoreAt accumulatorWord +++ loadWord exponentWord +++
              Ninst.pushB256 2 ::: Ninst.swap 0 ::: Ninst.div ::: mstoreAt exponentWord +++
              .call rpowLoopSlot) <?> evenExponent)))))) post := by
  func_run (4) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hbase]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (2) [0]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hbexp, hbmem]
  func_run (3) [1]
  func_run (3) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hbsize]
    decide +kernel
  rw [hacc]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [haexp, hamem]
  func_run (5) [0, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hasize]
    decide +kernel
  rw [hzero]
  apply Func.runCompiled_call' (f := rpowLoop) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hloop


def concreteExitClockMemory : Mem :=
  (concreteExitStagingMemory.write 160 concreteDripChi.toBytes).write 192 (6 : B256).toBytes
def concreteExitExponentMemory : Mem := concreteExitClockMemory.write 0 (1 : B256).toBytes
def concreteExitBaseMemory : Mem := concreteExitExponentMemory.write 224 rate.toBytes
def concreteExitAccumulatorMemory : Mem := concreteExitBaseMemory.write 256 rate.toBytes
def concreteExitLoopMemory : Mem := concreteExitAccumulatorMemory.write 0 (0 : B256).toBytes

private theorem concreteExit_stagingSize : concreteExitStagingMemory.size = 160 := by decide +kernel

private theorem concreteExit_chiMemoryFacts :
    (concreteExitStagingMemory.write 160 concreteDripChi.toBytes).size = 192 ∧
    Bytes.toB256 ((concreteExitStagingMemory.write 160 concreteDripChi.toBytes).read 160 32).1 = concreteDripChi ∧
    ((concreteExitStagingMemory.write 160 concreteDripChi.toBytes).read 160 32).2 =
      concreteExitStagingMemory.write 160 concreteDripChi.toBytes := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteExit_clockMemoryFacts : concreteExitClockMemory.size = 224 ∧
    Bytes.toB256 (concreteExitClockMemory.read 192 32).1 = 6 ∧
    (concreteExitClockMemory.read 192 32).2 = concreteExitClockMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteExit_exponentMemoryFacts : concreteExitExponentMemory.size = 224 ∧
    Bytes.toB256 (concreteExitExponentMemory.read 0 32).1 = 1 ∧
    (concreteExitExponentMemory.read 0 32).2 = concreteExitExponentMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteExit_baseMemoryFacts : concreteExitBaseMemory.size = 256 ∧
    Bytes.toB256 (concreteExitBaseMemory.read 0 32).1 = 1 ∧
    (concreteExitBaseMemory.read 0 32).2 = concreteExitBaseMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

private theorem concreteExit_accumulatorMemoryFacts : concreteExitAccumulatorMemory.size = 288 ∧
    Bytes.toB256 (concreteExitAccumulatorMemory.read 0 32).1 = 1 ∧
    (concreteExitAccumulatorMemory.read 0 32).2 = concreteExitAccumulatorMemory := by
  exact ⟨by decide +kernel, by decide +kernel, Mem.read_snd_eq_self (by decide +kernel)⟩

theorem concreteExit_freshStart (sevm : Sevm) (base post : Devm) (G : Nat)
    (htime : sevm.benvStat.time = 6)
    (hchi : base.getStorVal sevm.currentTarget chiSlot = concreteDripChi)
    (hrho : base.getStorVal sevm.currentTarget rhoSlot = 5)
    (hcoldChi : (sevm.currentTarget, chiSlot) ∉ base.accessedStorageKeys)
    (hcoldRho : (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys)
    (hloop : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      ((concreteDripFreshBase sevm base).setMach ⟨[], concreteExitLoopMemory, G⟩)
      rpowLoop post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], concreteExitStagingMemory, G + 122 + 2166 + 70 + 2103⟩)
      freshStart post := by
  apply concreteExit_readChi sevm _ _ _ _ _ hchi hcoldChi
  apply concreteExit_stageClock (sevm := sevm) (C := concreteExitStagingMemory.write 160 concreteDripChi.toBytes)
  · exact htime
  · exact concreteExit_stagingSize
  · rfl
  · exact concreteExit_chiMemoryFacts.1
  · exact concreteExit_chiMemoryFacts.2.1
  · exact concreteExit_chiMemoryFacts.2.2
  apply concreteExit_stageElapsed (E := concreteExitExponentMemory)
  · exact hrho
  · change (sevm.currentTarget, rhoSlot) ∉ base.accessedStorageKeys.insert
      (sevm.currentTarget, chiSlot)
    simp only [Std.HashSet.mem_insert]
    exact not_or.mpr ⟨by simp only [beq_iff_eq, Prod.mk.injEq, true_and]; decide +kernel, hcoldRho⟩
  · exact concreteExit_clockMemoryFacts.1
  · exact concreteExit_clockMemoryFacts.2.1
  · exact concreteExit_clockMemoryFacts.2.2
  · rfl
  · exact concreteExit_exponentMemoryFacts.1
  · exact concreteExit_exponentMemoryFacts.2.1
  · exact concreteExit_exponentMemoryFacts.2.2
  apply concreteExit_initializeRpow (B := concreteExitBaseMemory)
    (A := concreteExitAccumulatorMemory) (Z := concreteExitLoopMemory)
  · exact concreteExit_exponentMemoryFacts.1
  · rfl
  · exact concreteExit_baseMemoryFacts.1
  · exact concreteExit_baseMemoryFacts.2.1
  · exact concreteExit_baseMemoryFacts.2.2
  · rfl
  · exact concreteExit_accumulatorMemoryFacts.1
  · exact concreteExit_accumulatorMemoryFacts.2.1
  · exact concreteExit_accumulatorMemoryFacts.2.2
  · rfl
  exact hloop


def concreteExitChi : B256 := 1000000007735629813252049571

private def concreteExitLoopImage : Bytes :=
  (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 64 (40 : B256).toBytes) 96 (99 : B256).toBytes) 128 (99 : B256).toBytes) 32 (2 : B256).toBytes) 160 concreteDripChi.toBytes) 192 (6 : B256).toBytes) 0 (1 : B256).toBytes) 224 rate.toBytes) 256 rate.toBytes) 0 (0 : B256).toBytes)

private theorem concreteExit_loopReads : Mem.Reads concreteExitLoopMemory concreteExitLoopImage := by
  unfold concreteExitLoopMemory concreteExitAccumulatorMemory concreteExitBaseMemory concreteExitExponentMemory concreteExitClockMemory concreteExitStagingMemory concreteExitArgumentMemory concreteExitLoopImage
  repeat' first | apply Mem.Reads.write | apply Mem.Wf.write | exact Mem.wf_empty | exact Mem.reads_empty

private theorem concreteExit_loopSize : concreteExitLoopMemory.size = 288 := by
  unfold concreteExitLoopMemory
  rw [Mem.size_write_of_le (by rw [B256.length_toBytes, concreteExit_accumulatorMemoryFacts.1]; decide)]
  exact concreteExit_accumulatorMemoryFacts.1

private theorem concreteExit_loopUnchanged (i : Nat) (h : i + 32 ≤ 288) :
    (concreteExitLoopMemory.read i 32).2 = concreteExitLoopMemory := by
  apply Mem.read_snd_eq_self
  rw [concreteExit_loopSize]
  exact memExtSize_of_le (by decide) h

private theorem concreteExit_loopRead0 :
    Bytes.toB256 (concreteExitLoopMemory.read 0 32).1 = (0 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead32 :
    Bytes.toB256 (concreteExitLoopMemory.read 32 32).1 = (2 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 32 160 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead64 :
    Bytes.toB256 (concreteExitLoopMemory.read 64 32).1 = (40 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 32 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 128 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 96 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead96 :
    Bytes.toB256 (concreteExitLoopMemory.read 96 32).1 = (99 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 32 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 96 128 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead128 :
    Bytes.toB256 (concreteExitLoopMemory.read 128 32).1 = (99 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 192 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 160 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 128 32 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead160 :
    Bytes.toB256 (concreteExitLoopMemory.read 160 32).1 = concreteDripChi := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 160 192 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead192 :
    Bytes.toB256 (concreteExitLoopMemory.read 192 32).1 = (6 : B256) := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 256 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 224 _ (by decide)]
  rw [Bytes.readWord_writeAt_of_disjoint _ 192 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_loopRead256 :
    Bytes.toB256 (concreteExitLoopMemory.read 256 32).1 = rate := by
  rw [concreteExit_loopReads.read]
  unfold concreteExitLoopImage
  rw [Bytes.readWord_writeAt_of_disjoint _ 256 0 _ (by decide)]
  exact Bytes.readWord_writeAt_self _ _ _

private theorem concreteExit_composeFresh (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hchi : Bytes.toB256 (M.read (storedChiWord * 32).toNat 32).1 = concreteDripChi)
    (hchiMem : (M.read (storedChiWord * 32).toNat 32).2 = M)
    (hfactor : Bytes.toB256 (M.read (accumulatorWord * 32).toNat 32).1 = rate)
    (hfactorMem : (M.read (accumulatorWord * 32).toNat 32).2 = M)
    (hroute : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteExitChi], M, G⟩) freshRoute post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], M, G + 104⟩) composeFresh post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [concreteDripChi * rate, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hfactor, hfactorMem]
  func_run (4) [concreteDripChi, 3]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hchi, hchiMem]
  func_run (3) [1, 0]
  func_run (7) [concreteExitChi, 0]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  apply Func.runCompiled_call' (f := freshRoute) (G := G) rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]
    omega
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach, Devm.memory_setMach] using hroute

private theorem concreteExit_freshRoute (sevm : Sevm) (base post : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288)
    (hroute : Bytes.toB256 (M.read (routeWord * 32).toNat 32).1 = routeExit)
    (hmem : (M.read (routeWord * 32).toNat 32).2 = M)
    (hexit : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteExitChi], M, G⟩) afterExit post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteExitChi], M, G + 53⟩) freshRoute post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hroute, hmem]
  func_run (9) [0, 1]
  simpa only [Nat.add_sub_cancel] using hexit


private theorem concreteExit_beforeCall (sevm : Sevm) (base C R U T post : Devm) (M : Mem) (G : Nat)
    (hstatic : sevm.isStatic = false) (hsize : M.size = 288)
    (harg : Bytes.toB256 (M.read (argumentWord * 32).toNat 32).1 = 40)
    (hargMem : (M.read (argumentWord * 32).toNat 32).2 = M)
    (hrow : Bytes.toB256 (M.read (rowWord * 32).toNat 32).1 = 99)
    (hrowMem : (M.read (rowWord * 32).toNat 32).2 = M)
    (htotal : Bytes.toB256 (M.read (totalWord * 32).toNat 32).1 = 99)
    (htotalMem : (M.read (totalWord * 32).toNat 32).2 = M)
    (hnow : Bytes.toB256 (M.read (nowWord * 32).toNat 32).1 = 6)
    (hnowMem : (M.read (nowWord * 32).toNat 32).2 = M)
    (hchiCost : sstoreCost sevm base chiSlot concreteExitChi = 2900)
    (hchi : afterSstore sevm base chiSlot concreteExitChi = C)
    (hrhoCost : sstoreCost sevm C rhoSlot 6 = 2900)
    (hrho : afterSstore sevm C rhoSlot 6 = R)
    (hrowCost : sstoreCost sevm R sevm.caller.toB256 59 = 2900)
    (hrowStore : afterSstore sevm R sevm.caller.toB256 59 = U)
    (htotalCost : sstoreCost sevm U totalUnitsSlot 59 = 2900)
    (htotalStore : afterSstore sevm U totalUnitsSlot 59 = T)
    (hcall : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (T.setMach ⟨[40], M, G⟩)
      (Ninst.dup 0 ::: sendToCaller +++ ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)) post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[concreteExitChi], M, G + 11675⟩) afterExit post := by
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [harg, hargMem]
  func_run (5) [concreteExitChi * 40, 40]
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  · simp only [Devm.gasLeft_setMach, gLow]
    omega
  func_run (2)
  rw [show G + 11675 - 31 = (G + 8744) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := C.setMach ⟨[40], M, G + 8744⟩) ?_ ?_
  · simpa only [hchiCost, hchi] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := base)
        (key := chiSlot) (value := concreteExitChi) (stack := [40]) (memory := M) (G := G + 8744)
        (by rw [hchiCost]; simp only [gCallStipend]; omega) hstatic)
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hnow, hnowMem]
  func_run (1)
  rw [show G + 8744 - 9 = (G + 5835) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := R.setMach ⟨[40], M, G + 5835⟩) ?_ ?_
  · simpa only [hrhoCost, hrho] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := C)
        (key := rhoSlot) (value := 6) (stack := [40]) (memory := M) (G := G + 5835)
        (by rw [hrhoCost]; simp only [gCallStipend]; omega) hstatic)
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [harg, hargMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [hrow, hrowMem]
  func_run (2) [59]
  rw [show G + 5835 - 17 = (G + 2918) + 2900 by omega]
  refine Func.RunCompiled.next (devm' := U.setMach ⟨[40], M, G + 2918⟩) ?_ ?_
  · simpa only [hrowCost, hrowStore] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := R)
        (key := sevm.caller.toB256) (value := 59) (stack := [40]) (memory := M) (G := G + 2918)
        (by rw [hrowCost]; simp only [gCallStipend]; omega) hstatic)
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [harg, hargMem]
  func_run (2) [3]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  rw [htotal, htotalMem]
  func_run (2) [59]
  rw [show G + 2918 - 18 = G + 2900 by omega]
  refine Func.RunCompiled.next (devm' := T.setMach ⟨[40], M, G⟩) ?_ ?_
  · simpa only [htotalCost, htotalStore] using
      (Ninst.runCompiled_sstore_selected_setMach (sevm := sevm) (base := U)
        (key := totalUnitsSlot) (value := 59) (stack := [40]) (memory := M) (G := G)
        (by rw [htotalCost]; simp only [gCallStipend]; omega) hstatic)
  exact hcall

theorem concreteExitDevm_units :
    concreteExitDevm.getStorVal concreteCreateTarget concreteCreateSender.toB256 = 99 ∧
    concreteExitDevm.getStorVal concreteCreateTarget totalUnitsSlot = 99 := by
  change (concreteExitEntry.state.get concreteCreateTarget).stor.get concreteCreateSender.toB256 = 99 ∧
    (concreteExitEntry.state.get concreteCreateTarget).stor.get totalUnitsSlot = 99
  rw [concreteExitEntry_storage]
  exact concreteDripped_values.2.2

noncomputable def concreteExitStorageBase : Devm :=
  concreteDripFreshBase concreteExitSevm (concreteJoinStagingBase concreteExitDevm)
noncomputable def concreteExitChiBase : Devm :=
  (concreteExitStorageBase.withRefundCounter 0).setStorVal concreteCreateTarget chiSlot concreteExitChi
noncomputable def concreteExitRhoBase : Devm :=
  (concreteExitChiBase.withRefundCounter 0).setStorVal concreteCreateTarget rhoSlot 6
noncomputable def concreteExitRowBase : Devm :=
  (concreteExitRhoBase.withRefundCounter 0).setStorVal concreteCreateTarget concreteCreateSender.toB256 59
noncomputable def concreteExitTotalBase : Devm :=
  (concreteExitRowBase.withRefundCounter 0).setStorVal concreteCreateTarget totalUnitsSlot 59

private theorem concreteExit_originalStorage (key : B256) :
    getOrigStorVal concreteExitSevm concreteCreateTarget key =
      (concreteDripped.state.getStor concreteCreateTarget).get key := by rfl

private theorem concreteExitStorageBase_warm (key : B256)
    (hk : key = chiSlot ∨ key = rhoSlot ∨ key = concreteCreateSender.toB256 ∨ key = totalUnitsSlot) :
    (concreteCreateTarget, key) ∈ concreteExitStorageBase.accessedStorageKeys := by
  change (concreteCreateTarget, key) ∈ (((concreteExitDevm.accessedStorageKeys.insert
    (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)).insert
      (concreteCreateTarget, chiSlot)).insert (concreteCreateTarget, rhoSlot)
  rcases hk with rfl | rfl | rfl | rfl <;> simp

private theorem concreteExit_chiStore :
    sstoreCost concreteExitSevm concreteExitStorageBase chiSlot concreteExitChi = 2900 ∧
    afterSstore concreteExitSevm concreteExitStorageBase chiSlot concreteExitChi = concreteExitChiBase := by
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, chiSlot) ∈ concreteExitStorageBase.accessedStorageKeys := by
    exact concreteExitStorageBase_warm chiSlot (Or.inl rfl)
  have hr : concreteExitStorageBase.refundCounter = 0 := rfl
  have hv : concreteExitStorageBase.getStorVal concreteCreateTarget chiSlot = concreteDripChi := by
    change (Devm.getStor concreteExitStorageBase concreteCreateTarget).get chiSlot = _
    exact concreteExitDevm_chi
  have hc : sstoreValueCost concreteDripChi concreteDripChi concreteExitChi = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter concreteExitChi concreteDripChi concreteDripChi 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteExit_originalStorage,
      concreteDripped_values.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteExit_originalStorage,
      concreteDripped_values.1, hv, hr, hf]
    rfl

private theorem concreteExit_rhoStore :
    sstoreCost concreteExitSevm concreteExitChiBase rhoSlot 6 = 2900 ∧
    afterSstore concreteExitSevm concreteExitChiBase rhoSlot 6 = concreteExitRhoBase := by
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, rhoSlot) ∈ concreteExitChiBase.accessedStorageKeys := by
    rw [concreteExitChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteExitStorageBase_warm rhoSlot (Or.inr (Or.inl rfl))
  have hr : concreteExitChiBase.refundCounter = 0 := rfl
  have hv : concreteExitChiBase.getStorVal concreteCreateTarget rhoSlot = 5 := by
    change (Devm.getStor concreteExitChiBase concreteCreateTarget).get rhoSlot = _
    unfold concreteExitChiBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    exact concreteExitDevm_rho
  have hc : sstoreValueCost 5 5 6 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter 6 5 5 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteExit_originalStorage,
      concreteDripped_values.2.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteExit_originalStorage,
      concreteDripped_values.2.1, hv, hr, hf]
    rfl

private theorem concreteExit_rowStore :
    sstoreCost concreteExitSevm concreteExitRhoBase concreteCreateSender.toB256 59 = 2900 ∧
    afterSstore concreteExitSevm concreteExitRhoBase concreteCreateSender.toB256 59 = concreteExitRowBase := by
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, concreteCreateSender.toB256) ∈ concreteExitRhoBase.accessedStorageKeys := by
    rw [concreteExitRhoBase, Devm.sstoreWarmBase_accessedStorageKeys]
    rw [concreteExitChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteExitStorageBase_warm concreteCreateSender.toB256 (Or.inr (Or.inr (Or.inl rfl)))
  have hr : concreteExitRhoBase.refundCounter = 0 := rfl
  have hv : concreteExitRhoBase.getStorVal concreteCreateTarget concreteCreateSender.toB256 = 99 := by
    change (Devm.getStor concreteExitRhoBase concreteCreateTarget).get concreteCreateSender.toB256 = _
    unfold concreteExitRhoBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    unfold concreteExitChiBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    exact concreteExitDevm_units.1
  have hc : sstoreValueCost 99 99 59 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter 59 99 99 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteExit_originalStorage,
      concreteDripped_values.2.2.1, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteExit_originalStorage,
      concreteDripped_values.2.2.1, hv, hr, hf]
    rfl

private theorem concreteExit_totalStore :
    sstoreCost concreteExitSevm concreteExitRowBase totalUnitsSlot 59 = 2900 ∧
    afterSstore concreteExitSevm concreteExitRowBase totalUnitsSlot 59 = concreteExitTotalBase := by
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  have hw : (concreteCreateTarget, totalUnitsSlot) ∈ concreteExitRowBase.accessedStorageKeys := by
    rw [concreteExitRowBase, Devm.sstoreWarmBase_accessedStorageKeys]
    rw [concreteExitRhoBase, Devm.sstoreWarmBase_accessedStorageKeys]
    rw [concreteExitChiBase, Devm.sstoreWarmBase_accessedStorageKeys]
    exact concreteExitStorageBase_warm totalUnitsSlot (Or.inr (Or.inr (Or.inr rfl)))
  have hr : concreteExitRowBase.refundCounter = 0 := rfl
  have hv : concreteExitRowBase.getStorVal concreteCreateTarget totalUnitsSlot = 99 := by
    change (Devm.getStor concreteExitRowBase concreteCreateTarget).get totalUnitsSlot = _
    unfold concreteExitRowBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    unfold concreteExitRhoBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    unfold concreteExitChiBase
    rw [setStorVal_getStor_self, Stor.get_set_ne _ (by decide +kernel), Devm.withRefundCounter_getStor]
    exact concreteExitDevm_units.2
  have hc : sstoreValueCost 99 99 59 = 2900 := by decide +kernel
  have hf : sstoreNewRefundCounter 59 99 99 0 = 0 := by decide +kernel
  constructor
  · simp only [sstoreCost, ht, hw, if_pos, Nat.zero_add, concreteExit_originalStorage,
      concreteDripped_values.2.2.2, hv, hc]
  · simp only [afterSstore, ht, hw, if_pos, concreteExit_originalStorage,
      concreteDripped_values.2.2.2, hv, hr, hf]
    rfl

private theorem concreteExit_prefix (G : Nat) (post : Devm)
    (hcall : Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (concreteExitTotalBase.setMach ⟨[40], concreteExitLoopMemory, G⟩)
      (Ninst.dup 0 ::: sendToCaller +++ ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)) post) :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (concreteExitDevm.setMach ⟨[], Mem.empty, G + 20714⟩) exit post := by
  change Func.RunCompiled _ _
    (concreteExitDevm.setMach ⟨[], Mem.empty, G + 11675 + 53 + 104 + 34 + 122 + 2166 + 70 + 2103 + 4387⟩) _ _
  apply concreteExit_stage
  · exact concreteExitDevm_units.1
  · exact concreteExitDevm_units.2
  · exact concreteExitDevm_cold _
  · exact concreteExitDevm_cold _
  apply concreteExit_freshStart
  · rfl
  · exact concreteExitDevm_chi
  · exact concreteExitDevm_rho
  · change (concreteCreateTarget, chiSlot) ∉
      (concreteExitDevm.accessedStorageKeys.insert
        (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)
    simp only [Std.HashSet.mem_insert, concreteExitDevm_cold, or_false, not_or]
    exact ⟨by decide +kernel, by decide +kernel⟩
  · change (concreteCreateTarget, rhoSlot) ∉
      (concreteExitDevm.accessedStorageKeys.insert
        (concreteCreateTarget, concreteCreateSender.toB256)).insert (concreteCreateTarget, totalUnitsSlot)
    simp only [Std.HashSet.mem_insert, concreteExitDevm_cold, or_false, not_or]
    exact ⟨by decide +kernel, by decide +kernel⟩
  apply concreteDrip_rpowZero
  · exact concreteExit_loopSize
  · exact concreteExit_loopRead0
  · exact concreteExit_loopUnchanged 0 (by decide)
  apply concreteExit_composeFresh
  · exact concreteExit_loopSize
  · exact concreteExit_loopRead160
  · exact concreteExit_loopUnchanged 160 (by decide)
  · exact concreteExit_loopRead256
  · exact concreteExit_loopUnchanged 256 (by decide)
  apply concreteExit_freshRoute
  · exact concreteExit_loopSize
  · exact concreteExit_loopRead32
  · exact concreteExit_loopUnchanged 32 (by decide)
  apply concreteExit_beforeCall _ concreteExitStorageBase concreteExitChiBase concreteExitRhoBase
    concreteExitRowBase concreteExitTotalBase
  · rfl
  · exact concreteExit_loopSize
  · exact concreteExit_loopRead64
  · exact concreteExit_loopUnchanged 64 (by decide)
  · exact concreteExit_loopRead96
  · exact concreteExit_loopUnchanged 96 (by decide)
  · exact concreteExit_loopRead128
  · exact concreteExit_loopUnchanged 128 (by decide)
  · exact concreteExit_loopRead192
  · exact concreteExit_loopUnchanged 192 (by decide)
  · exact concreteExit_chiStore.1
  · exact concreteExit_chiStore.2
  · exact concreteExit_rhoStore.1
  · exact concreteExit_rhoStore.2
  · exact concreteExit_rowStore.1
  · exact concreteExit_rowStore.2
  · exact concreteExit_totalStore.1
  · exact concreteExit_totalStore.2
  exact hcall

theorem concreteExitTotalBase_balance : concreteExitTotalBase.getBal concreteCreateTarget = 100 := by
  have hs (d : Devm) (k v : B256) :
      (d.setStorVal concreteCreateTarget k v).getBal concreteCreateTarget = d.getBal concreteCreateTarget :=
    (Devm.StateWriteFrame.getBal_eq (Devm.setStorVal_stateWriteFrame d _ k v) _).symm
  unfold concreteExitTotalBase
  rw [hs]
  change concreteExitRowBase.getBal concreteCreateTarget = _
  unfold concreteExitRowBase
  rw [hs]
  change concreteExitRhoBase.getBal concreteCreateTarget = _
  unfold concreteExitRhoBase
  rw [hs]
  change concreteExitChiBase.getBal concreteCreateTarget = _
  unfold concreteExitChiBase
  rw [hs]
  exact concreteExitDevm_balance

theorem concreteExitTotalBase_storage : Devm.getStor concreteExitTotalBase concreteCreateTarget =
    ((((concreteDripped.state.getStor concreteCreateTarget).set chiSlot concreteExitChi).set rhoSlot 6).set
      concreteCreateSender.toB256 59).set totalUnitsSlot 59 := by
  unfold concreteExitTotalBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteExitRowBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteExitRhoBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  unfold concreteExitChiBase
  rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  have hs : Devm.getStor concreteExitStorageBase concreteCreateTarget =
      concreteDripped.state.getStor concreteCreateTarget := concreteExitEntry_storage _
  rw [hs]

theorem concreteExitTotalBase_code (a : Adr) :
    concreteExitTotalBase.getCode a = concreteDripped.state.getCode a := by
  unfold concreteExitTotalBase
  rw [Devm.setStorVal_getCode]
  change concreteExitRowBase.getCode a = _
  unfold concreteExitRowBase
  rw [Devm.setStorVal_getCode]
  change concreteExitRhoBase.getCode a = _
  unfold concreteExitRhoBase
  rw [Devm.setStorVal_getCode]
  change concreteExitChiBase.getCode a = _
  unfold concreteExitChiBase
  rw [Devm.setStorVal_getCode]
  change concreteExitEntry.state.getCode a = _
  change ((concreteExitDebit.setBal _ _).addBal _ _).getCode a = _
  rw [State.addBal_getCode, State.setBal_getCode]
  unfold concreteExitDebit
  rw [State.setBal_getCode]
  change ((concreteDripped.state.incrNonce concreteCreateSender).get a).code = _
  rw [State.incrNonce_get_code]
  rfl

private theorem concreteExit_dispatch (sevm : Sevm) (base post : Devm) (G : Nat)
    (hdata : sevm.data = concreteExitTx.data)
    (hvalue : sevm.value = 0)
    (hexit : Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[], Mem.empty, G⟩) exit post) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
    (base.setMach ⟨[], Mem.empty, G + 156⟩) main post := by
  have hd : dripSelector = (0x9f678cca : B256) := by decide +kernel
  have hj : joinSelector = (0xb688a363 : B256) := by decide +kernel
  have hx : exitSelector = (0x7f8661a1 : B256) := by decide +kernel
  have hu : convertToUnitsSelector = (0x9227149a : B256) := by decide +kernel
  have hshift : Sevm.dataWord sevm 0 >>> B256.toNat 224 = exitSelector := by
    simp only [Sevm.dataWord, hdata, concreteExitTx]
    decide +kernel
  func_run (1)
  simp only [hdata, concreteExitTx]
  func_run (5) [exitSelector]
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[exitSelector], Mem.empty, G + 156 - 27⟩) (dispatch tree) post
  change Func.RunCompiled _ sevm
    (base.setMach ⟨[exitSelector], Mem.empty, G + 156 - 27⟩)
    (Ninst.dup 0 ::: Ninst.pushB256 dripSelector ::: Ninst.gt :::
      (dispatch (.fork (.fork (.leaf convertToAssetsSelector (nonpayable (exactCalldata 36 convertToAssets)))
          (.leaf exitSelector (nonpayable (exactCalldata 36 exit))))
        (.leaf convertToUnitsSelector (nonpayable (exactCalldata 36 convertToUnits)))) <?>
       dispatch (.fork (.leaf dripSelector (nonpayable (exactCalldata 4 drip)))
         (.leaf joinSelector (exactCalldata 4 join))))) post
  simp only [hd, hj, hx, hu]
  func_run (4) [1]
  func_run (4) [1]
  func_run (4) [0]
  func_run (3) [1]
  func_run (1)
  rw [hvalue]
  func_run (2) [1]
  func_run (4) [1]
  all_goals first
    | simpa only [Nat.add_sub_cancel] using hexit
    | (simp only [hdata, concreteExitTx]; decide +kernel)

noncomputable def concreteExitCallInput : Devm :=
  concreteExitTotalBase.setMach
    ⟨[457907, concreteCreateSender.toB256, 40, 0, 0, 0, 0, 40],
      concreteExitLoopMemory, 457907⟩

noncomputable def concreteExitCallResolved : Devm :=
  addAccessedAddress
    (concreteExitTotalBase.setMach ⟨[40], concreteExitLoopMemory, 457907⟩)
    concreteCreateSender

private theorem concreteExitTotalBase_senderBalance :
    concreteExitTotalBase.getBal concreteCreateSender = 999999999997823644 := by
  have hs (d : Devm) (k v : B256) :
      (d.setStorVal concreteCreateTarget k v).getBal concreteCreateSender = d.getBal concreteCreateSender :=
    (Devm.StateWriteFrame.getBal_eq (Devm.setStorVal_stateWriteFrame d _ k v) _).symm
  unfold concreteExitTotalBase
  rw [hs]
  change concreteExitRowBase.getBal concreteCreateSender = _
  unfold concreteExitRowBase
  rw [hs]
  change concreteExitRhoBase.getBal concreteCreateSender = _
  unfold concreteExitRhoBase
  rw [hs]
  change concreteExitChiBase.getBal concreteCreateSender = _
  unfold concreteExitChiBase
  rw [hs]
  change (((concreteExitDebit.setBal concreteCreateSender
    (concreteExitDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
      concreteCreateSender).bal = _
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self, Acct.withBal]
  rw [concreteExitDebit_balance]
  decide +kernel

private theorem concreteExitCallResolved_code :
    concreteExitCallResolved.getCode concreteCreateSender = ByteArray.empty := by
  unfold concreteExitCallResolved
  rw [addAccessedAddress_getCode]
  change concreteExitTotalBase.getCode concreteCreateSender = _
  rw [concreteExitTotalBase_code, concreteDrippedSenderCode]

private theorem concreteExitCallResolved_senderBalance :
    concreteExitCallResolved.getBal concreteCreateSender = 999999999997823644 :=
  concreteExitTotalBase_senderBalance

private theorem concreteExitCallResolved_targetBalance :
    concreteExitCallResolved.getBal concreteCreateTarget = 100 :=
  concreteExitTotalBase_balance

private theorem concreteExitCall_warm :
    accessCost concreteCreateSender concreteExitTotalBase.accessedAddresses = 100 := by
  change accessCost concreteCreateSender ((Std.HashSet.ofList [0]).insertMany
    (pragueRules.precompiles ++ [concreteCreateSender, concreteCreateTarget])) = 100
  simp [accessCost, Std.HashSet.mem_insertMany_list, gasWarmAccess]

/-- Actual value-bearing empty-code child execution, with the exact parent gas split. -/
private theorem concreteExit_call_exists :
    ∃ post,
      Ninst.RunCompiled concreteExitSevm concreteExitCallInput (.exec .call) post ∧
      post.stack = [1, 40] ∧ post.memory = concreteExitLoopMemory ∧
      post.gasLeft = 451107 ∧
      post.error = concreteExitCallInput.error ∧ post.output = concreteExitCallInput.output ∧
      post.returnData = [] ∧ post.logs = concreteExitCallInput.logs ∧
      post.refundCounter = concreteExitCallInput.refundCounter ∧
      post.accountsToDelete.isEmpty = concreteExitCallInput.accountsToDelete.isEmpty ∧
      ∃ stmid, concreteExitCallInput.state.subBal concreteCreateTarget 40 = some stmid ∧
        post.state = stmid.addBal concreteCreateSender 40 := by
  have hc : (concreteCreateSender.toB256).toAdr = concreteCreateSender := by decide +kernel
  have hext : (concreteExitCallInput.setMach
      ⟨[40], concreteExitCallInput.memory, concreteExitCallInput.gasLeft⟩).extCost
      [(0, 0), (0, 0)] = 0 := by
    simp only [Devm.extCost, memExtsSize, memExtSize, if_true, Nat.sub_self]
  have hdel : accessDelegation concreteExitCallResolved concreteCreateSender =
      ⟨false, concreteCreateSender, ByteArray.empty, 0, concreteExitCallResolved⟩ := by
    rw [accessDelegation_of_not_delegation]
    · rw [concreteExitCallResolved_code]
    · rw [concreteExitCallResolved_code]
      decide +kernel
  have hempty : ¬ (concreteExitCallResolved.getAcct concreteCreateSender).Empty := by
    intro h
    have hb := h.2.2
    change concreteExitCallResolved.getBal concreteCreateSender = 0 at hb
    rw [concreteExitCallResolved_senderBalance] at hb
    exact (by decide +kernel : (999999999997823644 : B256) ≠ 0) hb
  have hsender : ¬ (concreteExitCallResolved.getAcct concreteExitSevm.currentTarget).bal < (40 : B256) := by
    change ¬ concreteExitCallResolved.getBal concreteCreateTarget < (40 : B256)
    rw [concreteExitCallResolved_targetBalance]
    decide +kernel
  have hh := Ninst.runCompiled_call_nonzero_codeFree
    (sevm := concreteExitSevm) (devm := concreteExitCallInput)
    (gw := 457907) (cw := concreteCreateSender.toB256) (vw := 40)
    (iiw := 0) (isw := 0) (oiw := 0) (osw := 0) (s := [40])
    (dp := false) (dadr := concreteCreateSender) (code := ByteArray.empty) (dgc := 0)
    (d1 := concreteExitCallResolved) (ext := 0) (acc := 100) (create := 0)
    (mcc := 450895) (mcs := 444095)
    rfl (by decide +kernel) hext
    (by
      simp only [hc, concreteExitCallInput, Devm.memory_setMach, Devm.gasLeft_setMach,
        Devm.setMach_setMach]
      exact hdel)
    (by rw [hc]; change accessCost concreteCreateSender concreteExitTotalBase.accessedAddresses + 0 = 100; exact concreteExitCall_warm)
    (by rw [hc, if_pos hempty])
    (by change calculateMsgCallGas 40 457907 457907 0 (100 + 0 + gasCallValue) = _; decide +kernel)
    (by change 450895 + 0 ≤ 457907; decide +kernel)
    rfl hsender (by decide +kernel) (by decide +kernel) rfl (by decide +kernel)
  have hm0 (M : Mem) : M.extends [(0, 0), (0, 0)] = M := by cases M; rfl
  have hm : concreteExitCallInput.memory.extends [(0, 0), (0, 0)] = concreteExitLoopMemory := by
    rw [hm0]
    simp only [concreteExitCallInput, Devm.memory_setMach]
  have hg : concreteExitCallResolved.gasLeft - (450895 + 0) + 444095 = 451107 := rfl
  have ht : concreteExitSevm.currentTarget = concreteCreateTarget := rfl
  simpa only [B256.toNat_zero, hm, hg, ht, hc] using hh

noncomputable def concreteExitCallPost : Devm := Classical.choose concreteExit_call_exists

theorem concreteExitCallPost_run :
    Ninst.RunCompiled concreteExitSevm concreteExitCallInput (.exec .call) concreteExitCallPost :=
  (Classical.choose_spec concreteExit_call_exists).1

private theorem concreteExitCallPost_machine :
    concreteExitCallPost.stack = [1, 40] ∧
    concreteExitCallPost.memory = concreteExitLoopMemory ∧
    concreteExitCallPost.gasLeft = 451107 := by
  have h := (Classical.choose_spec concreteExit_call_exists).2
  exact ⟨h.1, h.2.1, h.2.2.1⟩

private theorem concreteExitCallPost_meta :
    concreteExitCallPost.error = none ∧ concreteExitCallPost.logs = [] ∧
    concreteExitCallPost.refundCounter = 0 ∧ concreteExitCallPost.accountsToDelete.isEmpty = true := by
  have h := (Classical.choose_spec concreteExit_call_exists).2.2.2.2
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

private theorem concreteExitCallPost_transfer :
    ∃ stmid, concreteExitTotalBase.state.subBal concreteCreateTarget 40 = some stmid ∧
      concreteExitCallPost.state = stmid.addBal concreteCreateSender 40 :=
  (Classical.choose_spec concreteExit_call_exists).2.2.2.2.2.2.2.2.2.2

noncomputable def concreteExitRuntimePost : Devm :=
  (concreteExitCallPost.setMach
    ⟨[], concreteExitLoopMemory.write 0 (40 : B256).toBytes, 451083⟩).withOutput (40 : B256).toBytes

private theorem concreteExit_afterCall (sevm : Sevm) (base : Devm) (M : Mem) (G : Nat)
    (hsize : M.size = 288) :
    Func.RunCompiled (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨[1, 40], M, G + 24⟩)
      ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)
      ((base.setMach ⟨[], M.write 0 (40 : B256).toBytes, G⟩).withOutput (40 : B256).toBytes) := by
  func_run (5) [0]
  · simp only [Devm.extCost, Devm.memory_setMach, hsize]
    decide +kernel
  have hnsize : (M.write 0 (40 : B256).toBytes).size = 288 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hsize]; decide)]
    exact hsize
  have hnread : ((M.write 0 (40 : B256).toBytes).read 0 32).1 = (40 : B256).toBytes := by
    simpa only [B256.length_toBytes] using
      (Mem.read_write_zero M (ys := (40 : B256).toBytes) (by decide +kernel))
  have hnmem : ((M.write 0 (40 : B256).toBytes).read 0 32).2 = M.write 0 (40 : B256).toBytes := by
    apply Mem.read_snd_eq_self
    rw [hnsize]
    decide +kernel
  apply Func.runCompiled_return_of (G := G) (e := 0)
  · rfl
  · change calculateMemoryGasCost (memExtsSize (M.write 0 (40 : B256).toBytes).size [(0, 32)]) -
      calculateMemoryGasCost (M.write 0 (40 : B256).toBytes).size = 0
    rw [hnsize]
    decide +kernel
  · simp only [Devm.gasLeft_setMach]
    omega
  · change (((M.write 0 (40 : B256).toBytes).read 0 32).1,
      base.setMach ⟨[], ((M.write 0 (40 : B256).toBytes).read 0 32).2, G⟩) = _
    rw [hnread, hnmem]

private theorem concreteExit_callTail :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (concreteExitTotalBase.setMach ⟨[40], concreteExitLoopMemory, 457925⟩)
      (Ninst.dup 0 ::: sendToCaller +++ ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert))
      concreteExitRuntimePost := by
  have hprefix (sevm : Sevm) (base post : Devm) (M : Mem)
      (h : Func.RunCompiled (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[457907, sevm.caller.toB256, 40, 0, 0, 0, 0, 40], M, 457907⟩)
        (Ninst.call ::: ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)) post) :
      Func.RunCompiled (runtime.main :: runtime.aux) sevm
        (base.setMach ⟨[40], M, 457925⟩)
        (Ninst.dup 0 ::: sendToCaller +++ ((mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert)) post := by
    func_run (8)
    all_goals first
      | exact h
      | simp only [Devm.gasLeft_setMach, gVerylow, gBase]
  apply hprefix
  refine Func.RunCompiled.next (devm' := concreteExitCallPost) concreteExitCallPost_run ?_
  have heta (d : Devm) : d.setMach ⟨d.stack, d.memory, d.gasLeft⟩ = d := by cases d; rfl
  have hm : concreteExitCallPost.setMach ⟨[1, 40], concreteExitLoopMemory, 451083 + 24⟩ =
      concreteExitCallPost := by
    rw [← concreteExitCallPost_machine.1, ← concreteExitCallPost_machine.2.1]
    change concreteExitCallPost.setMach
      ⟨concreteExitCallPost.stack, concreteExitCallPost.memory, 451107⟩ = concreteExitCallPost
    rw [← concreteExitCallPost_machine.2.2]
    exact heta _
  have h := concreteExit_afterCall concreteExitSevm concreteExitCallPost concreteExitLoopMemory
    451083 concreteExit_loopSize
  rw [hm] at h
  exact h

theorem concreteExit_runtime :
    Func.RunCompiled (runtime.main :: runtime.aux) concreteExitSevm
      (concreteExitDevm.setMach ⟨[], Mem.empty, 478795⟩) main concreteExitRuntimePost := by
  exact concreteExit_dispatch _ _ _ 478639 rfl rfl
    (concreteExit_prefix 457925 concreteExitRuntimePost concreteExit_callTail)

theorem concreteExitDevm_gas : concreteExitDevm.gasLeft = 478796 := by
  change 500000 - deploymentIntrinsicGas concreteExitTx = 478796
  decide +kernel

theorem concreteExit_program :
    Prog.RunCompiled concreteExitSevm concreteExitDevm runtime concreteExitRuntimePost := by
  apply Prog.runCompiled_intro (G := 478795)
    (mid := concreteExitDevm.setMach ⟨[], Mem.empty, 478795⟩)
  · rw [concreteExitDevm_gas]
    decide
  · rfl
  exact concreteExit_runtime

theorem concreteExit_compiled : some concreteExitSevm.code.toList = Prog.compile runtime := by
  change some concreteExitMessage.code.toList = _
  rw [concreteExitMessage_code, code_compile]

theorem concreteExit_exec :
    exec (initEvm (concreteExitMessage.withBenv concreteExitEntry)) =
      .ok concreteExitRuntimePost :=
  Prog.exec_of_runCompiled concreteExit_program concreteExit_compiled

theorem concreteExit_frameEntry :
    (Frame.ofCall concreteExitMessage).enter =
      .run (initEvm (concreteExitMessage.withBenv concreteExitEntry)) := by
  have hnp : ¬ pragueRules.isPrecomp concreteCreateTarget :=
    concreteDeploymentBase.target_not_precompile (ChainConfig.pragueOnly_rulesAt 1 6)
  have he : executeCode.enter (concreteExitMessage.withBenv concreteExitEntry) =
      .inl (initEvm (concreteExitMessage.withBenv concreteExitEntry)) := by
    unfold executeCode.enter
    change (if !false && pragueRules.isPrecomp concreteCreateTarget then _ else _) = _
    simp only [Bool.not_false, Bool.true_and, hnp]
    rfl
  unfold Frame.enter Frame.ofCall
  rw [concreteExitEntry_run]
  dsimp only
  rw [he]

private theorem concreteExit_postError : concreteExitRuntimePost.error = none :=
  concreteExitCallPost_meta.1

theorem concreteExit_processMessage :
    processMessage concreteExitMessage = .ok concreteExitRuntimePost := by
  unfold processMessage runFrame
  rw [concreteExit_frameEntry]
  unfold Frame.settle Frame.settleMsg processMessage.settle executeCode.handleError
  simp only [concreteExit_exec, concreteExit_postError, Frame.ofCall, Option.isSome,
    Bool.false_eq_true, if_false, bind, Except.bind]

noncomputable def concreteExitMessageState : State := concreteExitRuntimePost.state

noncomputable def concreteExitMessageOutput : MsgCallOutput := {
  gasLeft := 451083
  refundCounter := 0
  logs := []
  accountsToDelete := concreteExitCallPost.accountsToDelete
  error := none
  returnData := (40 : B256).toBytes }

theorem concreteExit_messageCall :
    processMessageCall concreteExitMessage = .ok (concreteExitMessageState, concreteExitMessageOutput) := by
  have htarget : concreteExitMessage.target.isNone = false := rfl
  have hauths : concreteExitMessage.tenv.stat.auths = [] := rfl
  have hcode : some concreteExitMessage.code.toList = Prog.compile runtime := concreteExit_compiled
  have hdelegation : getDelegatedCodeAddress concreteExitMessage.code = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg (not_delegation_of_compile hcode)]
  have hrefund : concreteExitRuntimePost.refundCounter = 0 := concreteExitCallPost_meta.2.2.1
  have hlogs : concreteExitRuntimePost.logs = [] := concreteExitCallPost_meta.2.1
  unfold processMessageCall
  rw [htarget]
  unfold processMessageCall.call
  simp only [hauths, List.isEmpty, if_true, bind, Except.bind, hdelegation,
    concreteExit_processMessage, Except.bimap, id_eq, concreteExit_postError,
    Option.isNone, hrefund]
  simp only [concreteExitRuntimePost, Devm.withOutput_logs, Devm.setMach_logs,
    concreteExitCallPost_meta.2.1]
  rfl

noncomputable def concreteExitTransactionState : State :=
  deploymentFinalState concreteExitTxInput concreteExitTx concreteCreateSender
    concreteExitMessageState 48917

noncomputable def concreteExitTransactionBout : BlockOutput :=
  deploymentFinalBout .init concreteExitTx 0 concreteExitMessageOutput 48917

theorem concreteExit_transaction :
    processTransaction concreteExitTxInput .init concreteExitTx 0 =
      .ok (concreteExitTransactionState, concreteExitTransactionBout) := by
  have hchecked := concreteExitChecked
  change checkTransaction concreteExitTxInput.beginTransaction
    (deploymentTxPreludeBout .init concreteExitTx 0) concreteExitTx =
      .ok (concreteCreateSender, 2, [], 0) at hchecked
  have hdebit := concreteExitDebit_run
  simp only [Benv.beginTransaction] at hdebit
  have hprepare := concreteExitMessage_prepared
  have hrules : concreteExitTxInput.beginTransaction.stat.rules = pragueRules := rfl
  unfold processTransaction
  simp only [bind, Except.bind]
  rw [hrules, concreteExitValidated]
  simp only [Except.mapError]
  simp only [deploymentTxPreludeBout, ExecutionTrace.transactionPreludeBout] at hchecked
  rw [hchecked]
  simp only [Tx.isTypeThree, Tx.accessList, TxType.accessList, Tx.auths,
    concreteExitTx, Bool.false_eq_true, if_false, Nat.add_zero, Benv.beginTransaction]
  rw [show Nat.toB256 (500000 * 2) = 1000000 by decide +kernel, hdebit]
  simp only [Option.toExcept]
  simp only [concreteExitTenv, deploymentTenv, deploymentIntrinsicGas, Benv.beginTransaction,
    concreteExitTx] at hprepare
  simp only [List.map_nil, List.flatten_nil]
  simp only [deploymentEffectiveGasPrice] at hprepare ⊢
  have hprice : min 1 (8 - concreteExitTxInput.stat.baseFeePerGas) +
      concreteExitTxInput.stat.baseFeePerGas = 2 := by rfl
  rw [hprice] at hprepare
  simp only [hprepare, concreteExit_messageCall]
  have hgas : max (500000 - 451083 - min ((500000 - 451083) / 5) 0)
      (calculateIntrinsicCost concreteExitTx).2 = 48917 := by decide +kernel
  simp only [concreteExitTx] at hgas
  simp only [concreteExitMessageOutput]
  rw [show Int.toNat? 0 = some 0 by rfl]
  simp only [hgas]
  unfold concreteExitTransactionState concreteExitTransactionBout deploymentFinalState deploymentFinalBout
  simp only [deploymentEffectiveGasPrice, concreteExitTx, concreteExitMessageOutput, hprice]
  have hdelete : concreteExitCallPost.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    exact concreteExitCallPost_meta.2.2.2
  rw [hdelete]
  simp only [List.foldl_nil]
  rfl


/-- The selected actual child state has paid forty out of the funded four-store parent. -/
theorem concreteExitMessageState_paid :
    concreteExitMessageState = (concreteExitTotalBase.state.setBal concreteCreateTarget 60).addBal
      concreteCreateSender 40 := by
  obtain ⟨mid, hsub, hpost⟩ := concreteExitCallPost_transfer
  have hm := (State.of_subBal hsub).2
  have hb : concreteExitTotalBase.state.bal concreteCreateTarget = 100 := concreteExitTotalBase_balance
  change concreteExitCallPost.state = _
  rw [hpost, hm, hb, show (100 : B256) - 40 = 60 by decide +kernel]

theorem concreteExitTransactionCode (a : Adr) :
    concreteExitTransactionState.getCode a = concreteDripped.state.getCode a := by
  unfold concreteExitTransactionState deploymentFinalState
  rw [State.addBal_getCode, State.addBal_getCode, concreteExitMessageState_paid,
    State.addBal_getCode, State.setBal_getCode]
  exact concreteExitTotalBase_code a

theorem concreteExit_receiptEntry :
    concreteExitTransactionBout.receiptsTrie[deploymentReceiptKey 0]? =
      some (makeReceipt concreteExitTx none 48917 []) := by
  change (BlockOutput.init.receiptsTrie.insert (deploymentReceiptKey 0)
    (makeReceipt concreteExitTx none 48917 []))[deploymentReceiptKey 0]? = _
  rw [Std.TreeMap.getElem?_insert_self]

theorem concreteExit_requestSuffix :
    processGeneralPurposeRequests (concreteExitTxInput.withState concreteExitTransactionState)
      concreteExitTransactionBout = .ok (concreteExitTransactionState, concreteExitTransactionBout) := by
  have hcode (a : Adr) (ha : a ∈ [beaconRootsAddress, historyStorageAddress,
      withdrawalRequestPredeployAddress, consolidationRequestPredeployAddress]) :
      some (concreteExitTransactionState.getCode a).toList = Prog.compile deploymentSystemProgram := by
    rw [concreteExitTransactionCode]
    rw [concreteDrippedCode, concreteJoinedCode]
    exact concreteDeployedSystemCode a ha
  obtain ⟨withdrawalOut, hw, _, _, _, _, hwr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (concreteExitTxInput.withState concreteExitTransactionState) withdrawalRequestPredeployAddress []
      (hcode _ (by simp)) (by change ¬ pragueRules.isPrecomp withdrawalRequestPredeployAddress; decide)
  obtain ⟨consolidationOut, hc, _, _, _, _, hcr⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((concreteExitTxInput.withState concreteExitTransactionState).withState concreteExitTransactionState)
      consolidationRequestPredeployAddress [] (hcode _ (by simp))
      (by change ¬ pragueRules.isPrecomp consolidationRequestPredeployAddress; decide)
  have hd : parseDepositRequests concreteExitTransactionBout = .ok [] := by
    unfold parseDepositRequests
    have hk : concreteExitTransactionBout.receiptKeys = [deploymentReceiptKey 0] := rfl
    rw [hk]
    simp
    rw [concreteExit_receiptEntry]
    unfold makeReceipt
    rfl
  unfold processGeneralPurposeRequests
  rw [hd]
  simp only [List.length_nil, Nat.lt_irrefl, if_false, bind, Except.bind]
  rw [hw]
  simp only [hwr, List.length_nil, Nat.lt_irrefl, if_false]
  change (do
    let ⟨st, out⟩ ← processCheckedSystemTransaction
      ((concreteExitTxInput.withState concreteExitTransactionState).withState concreteExitTransactionState)
      consolidationRequestPredeployAddress []
    if out.returnData.length > 0 then
      .ok (st, {concreteExitTransactionBout with requests := concreteExitTransactionBout.requests ++
        [consolidationRequestType ++ out.returnData]})
    else .ok (st, {concreteExitTransactionBout with requests := concreteExitTransactionBout.requests})) = _
  simp only [hc, bind, Except.bind, hcr, List.length_nil, Nat.lt_irrefl, if_false]
  rfl

theorem concreteExit_body :
    applyBody concreteExitTxInput [.inl concreteExitTxRlp] [] =
      .ok (concreteExitTransactionState, concreteExitTransactionBout) := by
  obtain ⟨beaconOut, hb, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    concreteExitTxInput beaconRootsAddress concreteExitTxInput.stat.parentBeaconBlockRoot.toBytes
    (by change some (concreteDripped.state.getCode _).toList = _
        rw [concreteDrippedCode, concreteJoinedCode]; exact concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp beaconRootsAddress; decide)
  obtain ⟨historyOut, hh, _⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (concreteExitTxInput.withState concreteDripped.state) historyStorageAddress
    concreteDripBlock.header.hash.toBytes
    (by change some (concreteDripped.state.getCode _).toList = _
        rw [concreteDrippedCode, concreteJoinedCode]; exact concreteDeployedSystemCode _ (by simp))
    (by change ¬ pragueRules.isPrecomp historyStorageAddress; decide)
  have hl : (concreteExitTxInput.withState concreteDripped.state).stat.blockHashes.getLast? =
      some concreteDripBlock.header.hash := by rfl
  have hi : (concreteExitTxInput.withState concreteDripped.state).withState concreteDripped.state =
      concreteExitTxInput := rfl
  unfold applyBody
  rw [hb]
  simp only [Except.mapError, bind, Except.bind]
  change (do
    let lastHash ← (concreteExitTxInput.withState concreteDripped.state).stat.blockHashes.getLast?.toExcept
      (TransitionError.internal (.invariant (.text "block hashes is empty")))
    let ⟨stHistory, _⟩ ← Except.mapError TransitionError.vm
      (processUncheckedSystemTransaction (concreteExitTxInput.withState concreteDripped.state)
        historyStorageAddress lastHash.toBytes)
    let ⟨benvTxs, boutTxs⟩ ← applyTransactions
      (← ([.inl concreteExitTxRlp] : List (Bytes ⊕ Tx)).mapM decodeTx).putIndex
      ((concreteExitTxInput.withState concreteDripped.state).withState stHistory) .init
    let ⟨stWds, boutWds⟩ := processWithdrawals benvTxs boutTxs []
    processGeneralPurposeRequests (benvTxs.withState stWds) boutWds) = _
  rw [hl]
  simp only [Option.toExcept, hh, Except.mapError, bind, Except.bind]
  rw [show (concreteExitTxInput.withState concreteDripped.state).state =
    concreteDripped.state from rfl, hi]
  simp only [List.mapM_cons, List.mapM_nil, concreteExitDecode, pure, Except.pure, bind, Except.bind, List.putIndex, List.putIndex.aux,
    applyTransactions, concreteExit_transaction]
  have hwd (be : Benv) (bo : BlockOutput) : processWithdrawals be bo [] = (be.state, bo) := rfl
  rw [hwd]
  have hwith (be : Benv) : be.withState be.state = be := by cases be; rfl
  simp only [hwith]
  exact concreteExit_requestSuffix

noncomputable def concreteExitHeader (sr tr rr wr rh : B256) : Header :=
  { concreteExitExecutionHeader with
    gasUsed := 48917
    stateRoot := sr
    txsRoot := tr
    receiptRoot := rr
    withdrawalsRoot := wr
    requestsHash := some rh }

theorem concreteExitHeader_benv (sr tr rr wr rh : B256) :
    initBenv pragueRules concreteDripped (concreteExitHeader sr tr rr wr rh) = concreteExitTxInput := rfl

theorem concreteExitHeader_valid (sr tr rr wr rh : B256) :
    validateHeader pragueRules concreteDripped (concreteExitHeader sr tr rr wr rh) = .ok () := by
  have hlast : concreteDripped.blocks.getLast? = some concreteDripBlock :=
    appendBlock_getLast? concreteJoined.blocks concreteDripBlock
  simp only [validateHeader, hlast, Option.toExcept, bind, Except.bind,
    concreteExitHeader, concreteExitExecutionHeader, Header.hash, ne_eq, not_true_eq_false, ite_false]
  simp only [concreteDripBlock, concreteDripHeader, concreteDripExecutionHeader, concreteJoinBlock, concreteJoinHeader, concreteJoinExecutionHeader, concreteDeploymentEnvelope, concreteCanonicalBlock, CanonicalBlock.ofDecode,
    concreteDeploymentBlock, concreteDeploymentHeader, concreteExecutionHeader, concreteGenesisHeader]
  decide +kernel

noncomputable def concreteExitBlock : Block := {
  header := concreteExitHeader concreteExitTransactionState.root
    (getTransactionsRoot concreteExitTransactionBout) (getReceiptRoot concreteExitTransactionBout)
    (getWithdrawalsRoot concreteExitTransactionBout) (computeRequestsHash concreteExitTransactionBout.requests)
  txs := [.inl concreteExitTxRlp]
  ommers := []
  wds := [] }

noncomputable def concreteExited : BlockChain :=
  ⟨appendBlock concreteDripped.blocks concreteExitBlock, concreteExitTransactionState, concreteDripped.chainId⟩

theorem concreteExit_checks :
    stateTransitionChecks concreteExitTransactionBout concreteExitBlock.header
      (getTransactionsRoot concreteExitTransactionBout) concreteExitTransactionState.root
      (getReceiptRoot concreteExitTransactionBout) (logsBloom concreteExitTransactionBout.blockLogs)
      (getWithdrawalsRoot concreteExitTransactionBout)
      (computeRequestsHash concreteExitTransactionBout.requests) = .ok () := by
  have hg : concreteExitTransactionBout.blockGasUsed = 48917 := rfl
  have hl : concreteExitTransactionBout.blockLogs = [] := rfl
  have hb : concreteExitTransactionBout.blobGasUsed = 0 := rfl
  simp only [stateTransitionChecks, hg, hl, hb, concreteExitBlock, concreteExitHeader,
    concreteExitExecutionHeader, concreteDripBlock, concreteDripHeader, concreteDripExecutionHeader, concreteJoinBlock, concreteJoinHeader, concreteJoinExecutionHeader, concreteDeploymentEnvelope, concreteCanonicalBlock,
    CanonicalBlock.ofDecode, concreteDeploymentBlock, concreteDeploymentHeader,
    concreteExecutionHeader, concreteGenesisHeader, logsBloom, List.foldl_nil,
    ne_eq, not_true_eq_false, ite_false, pure, Bind.bind, Except.bind]
  rfl

theorem concreteExit_step :
    stateTransitionUsing concreteConfig concreteDripped concreteExitBlock = .ok concreteExited := by
  have hchain : concreteConfig.chainId = concreteDripped.chainId := concreteDeploymentRoot.deployed_chainId
  rw [stateTransitionUsing_eq_of_chainId_eq hchain]
  rw [show concreteConfig.rulesAt concreteExitBlock.header.timestamp = .ok pragueRules from
    ChainConfig.pragueOnly_rulesAt 1 _]
  change stateTransitionWith pragueRules concreteDripped concreteExitBlock = _
  rw [stateTransitionWith_eq_ok_iff, stateTransitionE]
  have hh : validateHeader pragueRules concreteDripped concreteExitBlock.header = .ok () :=
    concreteExitHeader_valid _ _ _ _ _
  rw [hh]
  change (do
    let output ← applyBody (initBenv pragueRules concreteDripped concreteExitBlock.header)
      concreteExitBlock.txs concreteExitBlock.wds
    Except.mapError TransitionError.block (stateTransitionChecks output.2
      concreteExitBlock.header (getTransactionsRoot output.2) output.1.root
      (getReceiptRoot output.2) (logsBloom output.2.blockLogs)
      (getWithdrawalsRoot output.2) (computeRequestsHash output.2.requests))
    .ok (⟨appendBlock concreteDripped.blocks concreteExitBlock, output.1,
      concreteDripped.chainId⟩ : BlockChain)) = .ok concreteExited
  have hbody : applyBody (initBenv pragueRules concreteDripped concreteExitBlock.header)
      concreteExitBlock.txs concreteExitBlock.wds =
      .ok (concreteExitTransactionState, concreteExitTransactionBout) := by
    change applyBody (initBenv pragueRules concreteDripped (concreteExitHeader _ _ _ _ _))
      [.inl concreteExitTxRlp] [] = _
    rw [concreteExitHeader_benv]
    exact concreteExit_body
  rw [hbody]
  simp only [Bind.bind, Except.bind, concreteExit_checks, Except.mapError]
  rfl


theorem concreteExited_storage : concreteExited.state.getStor concreteCreateTarget =
    ((((concreteDripped.state.getStor concreteCreateTarget).set chiSlot concreteExitChi).set rhoSlot 6).set
      concreteCreateSender.toB256 59).set totalUnitsSlot 59 := by
  change concreteExitTransactionState.getStor concreteCreateTarget = _
  unfold concreteExitTransactionState deploymentFinalState State.getStor State.addBal
  rw [State.setBal_get_stor, State.setBal_get_stor, concreteExitMessageState_paid]
  simp only [State.addBal, State.setBal_get_stor]
  exact concreteExitTotalBase_storage

theorem concreteExited_values :
    (concreteExited.state.getStor concreteCreateTarget).get chiSlot = concreteExitChi ∧
    (concreteExited.state.getStor concreteCreateTarget).get rhoSlot = 6 ∧
    (concreteExited.state.getStor concreteCreateTarget).get concreteCreateSender.toB256 = 59 ∧
    (concreteExited.state.getStor concreteCreateTarget).get totalUnitsSlot = 59 := by
  rw [concreteExited_storage]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel),
      Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  constructor
  · rw [Stor.get_set_ne _ (by decide +kernel), Stor.get_set_self]
  · exact Stor.get_set_self _ _ _

theorem concreteExitedTargetBalance : concreteExited.state.bal concreteCreateTarget = 60 := by
  change (concreteExitTransactionState.get concreteCreateTarget).bal = _
  unfold concreteExitTransactionState deploymentFinalState
  change (((concreteExitMessageState.addBal concreteCreateSender 902166).addBal 0 48917).get
    concreteCreateTarget).bal = _
  have hz : (0 : Adr) ≠ concreteCreateTarget := by decide +kernel
  have ht : concreteCreateSender ≠ concreteCreateTarget := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_ne ht]
  rw [concreteExitMessageState_paid]
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self, Acct.withBal]

theorem concreteExitedSenderBalance :
    concreteExited.state.bal concreteCreateSender = 999999999998725850 := by
  change (concreteExitTransactionState.get concreteCreateSender).bal = _
  unfold concreteExitTransactionState deploymentFinalState
  change (((concreteExitMessageState.addBal concreteCreateSender 902166).addBal 0 48917).get
    concreteCreateSender).bal = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  rw [concreteExitMessageState_paid]
  simp only [State.addBal, State.setBal_get_self, Acct.withBal,
    State.bal, State.setBal_get_ne ht]
  change (concreteExitTotalBase.getBal concreteCreateSender + 40) + 902166 = _
  rw [concreteExitTotalBase_senderBalance]
  decide +kernel

private theorem concreteExitTotalBase_sender :
    concreteExitTotalBase.state.get concreteCreateSender = concreteExitEntry.state.get concreteCreateSender := by
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  change (((((concreteExitEntry.state.setStorVal concreteCreateTarget chiSlot concreteExitChi).setStorVal
    concreteCreateTarget rhoSlot 6).setStorVal concreteCreateTarget concreteCreateSender.toB256 59).setStorVal
    concreteCreateTarget totalUnitsSlot 59).get concreteCreateSender) = _
  simp only [State.setStorVal, State.get_set_ne _ ht]

theorem concreteExitedSenderNonce : concreteExited.state.getNonce concreteCreateSender = 4 := by
  change (concreteExitTransactionState.get concreteCreateSender).nonce = _
  unfold concreteExitTransactionState deploymentFinalState
  change (((concreteExitMessageState.addBal concreteCreateSender 902166).addBal 0 48917).get
    concreteCreateSender).nonce = _
  have hz : (0 : Adr) ≠ concreteCreateSender := by decide +kernel
  have ht : concreteCreateTarget ≠ concreteCreateSender := by decide +kernel
  simp only [State.addBal, State.setBal_get_ne hz, State.setBal_get_self, Acct.withBal]
  rw [concreteExitMessageState_paid]
  simp only [State.addBal, State.setBal_get_self, State.setBal_get_ne ht, Acct.withBal]
  rw [concreteExitTotalBase_sender]
  change ((((concreteExitDebit.setBal concreteCreateSender
    (concreteExitDebit.bal concreteCreateSender - 0)).addBal concreteCreateTarget 0).get
    concreteCreateSender).nonce) = _
  simp only [State.addBal, State.setBal_get_ne ht, State.setBal_get_self]
  unfold concreteExitDebit
  simp only [State.setBal_get_self, State.incrNonce, State.get_set_self]
  change (concreteDripped.state.getNonce concreteCreateSender) + 1 = 4
  rw [concreteDrippedSenderNonce]
  rfl

theorem concreteExit_receiptSucceeded :
    (concreteExitTransactionBout.receiptsTrie[deploymentReceiptKey 0]?).map
      (fun entry => entry.2.succeeded) = some true := by
  rw [concreteExit_receiptEntry]
  rfl

theorem concreteExit_observations :
    concreteExitMessageOutput.returnData = (40 : B256).toBytes ∧
    concreteExitTransactionBout.blockGasUsed = 48917 ∧
    concreteExitTransactionBout.blockLogs = [] ∧
    concreteExitBlock.header.timestamp = 6 ∧ concreteExitBlock.header.number = 4 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One actual configured exit block, its funded child payment, and its observable accounting. -/
theorem concreteExit_checkpoint :
    stateTransitionUsing concreteConfig concreteDripped concreteExitBlock = .ok concreteExited ∧
    concreteExitMessageState = (concreteExitTotalBase.state.setBal concreteCreateTarget 60).addBal
      concreteCreateSender 40 ∧
    concreteExited.state.getStor concreteCreateTarget =
      ((((concreteDripped.state.getStor concreteCreateTarget).set chiSlot concreteExitChi).set rhoSlot 6).set
        concreteCreateSender.toB256 59).set totalUnitsSlot 59 ∧
    ((concreteExited.state.getStor concreteCreateTarget).get chiSlot = concreteExitChi ∧
      (concreteExited.state.getStor concreteCreateTarget).get rhoSlot = 6 ∧
      (concreteExited.state.getStor concreteCreateTarget).get concreteCreateSender.toB256 = 59 ∧
      (concreteExited.state.getStor concreteCreateTarget).get totalUnitsSlot = 59) ∧
    concreteExited.state.bal concreteCreateTarget = 60 ∧
    concreteExited.state.bal concreteCreateSender = 999999999998725850 ∧
    concreteExited.state.getNonce concreteCreateSender = 4 ∧
    (concreteExitTransactionBout.receiptsTrie[deploymentReceiptKey 0]?).map
      (fun entry => entry.2.succeeded) = some true ∧
    (concreteExitMessageOutput.returnData = (40 : B256).toBytes ∧
      concreteExitTransactionBout.blockGasUsed = 48917 ∧
      concreteExitTransactionBout.blockLogs = [] ∧
      concreteExitBlock.header.timestamp = 6 ∧ concreteExitBlock.header.number = 4) :=
  ⟨concreteExit_step, concreteExitMessageState_paid, concreteExited_storage, concreteExited_values,
    concreteExitedTargetBalance, concreteExitedSenderBalance, concreteExitedSenderNonce,
    concreteExit_receiptSucceeded, concreteExit_observations⟩

end Drip
end Blanc
