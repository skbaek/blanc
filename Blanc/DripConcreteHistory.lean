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

end Drip
end Blanc
