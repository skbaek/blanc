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

end Drip
end Blanc
