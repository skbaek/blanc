import Blanc.TransientSettlement

/-!
Concrete regression controls for transient cells, static propagation, direct
call provenance, frame-relative settlement, observable logs, and transaction
reset. The transaction controls use two independently signed legacy
transactions from the same sender with successive nonces; the first returned
state and block output are the exact inputs to the second.
-/

namespace Blanc.TransientSettlementRegression

open Jaune Blanc
open Jaune.Ninst Ninst

noncomputable section

private def addressA : Adr := 0x0000000000000000000000000000000000000a01
private def addressB : Adr := 0x0000000000000000000000000000000000000b02
private def delegateAddress : Adr := 0x0000000000000000000000000000000000000d03
private def key : B256 := 1
private def otherKey : B256 := 2

private def dynamicSevm : Sevm :=
  { (default : Sevm) with currentTarget := addressA, depth := 4, isStatic := false }

private def staticSevm : Sevm := { dynamicSevm with isStatic := true }

private def cellPre : Devm :=
  (((default : Devm).setTransVal addressA otherKey 7)
    |> fun d => d.setTransVal addressB key 9
    |> fun d => d.withGasLeft 100000
    |> fun d => d.withStack [key, 0])

private def cellClear : Execution :=
  Rinst.run ⟨0, dynamicSevm, cellPre⟩ .tstore

private def cellClearControl : Bool :=
  match cellClear with
  | .ok post =>
      post.getTransVal addressA key == 0 &&
      post.getTransVal addressA otherKey == 7 &&
      post.getTransVal addressB key == 9
  | _ => false

private def tloadPre : Devm :=
  ((default : Devm).setTransVal addressA key 42)
    |> fun d => d.withGasLeft 100000
    |> fun d => d.withStack [key]

private def tloadControl : Bool :=
  match Rinst.run ⟨0, dynamicSevm, tloadPre⟩ .tload with
  | .ok post => post.stack == [42] &&
      post.getTransVal addressA key == tloadPre.getTransVal addressA key &&
      post.getTransVal addressB otherKey ==
        tloadPre.getTransVal addressB otherKey
  | _ => false

private def isWriteInStatic : Execution → Bool
  | .error (.halt (.writeInStaticContext .none), _) => true
  | _ => false

private def writeInStaticPreservesWorld (pre : Devm) : Execution → Bool
  | .error (.halt (.writeInStaticContext .none), post) =>
      post.getStorVal addressA key == pre.getStorVal addressA key &&
      post.getTransVal addressA otherKey == pre.getTransVal addressA otherKey
  | _ => false

private def isStackUnderflow : Execution → Bool
  | .error (.halt (.stackUnderflow .none), _) => true
  | _ => false

private def isOutOfGas : Execution → Bool
  | .error (.halt (.outOfGas .none), _) => true
  | _ => false

private def staticTstoreControl : Bool :=
  let pre := (((default : Devm).setTransVal addressA otherKey 19)
    |> fun d : Devm => d.withGasLeft 100000).withStack [key, 5]
  writeInStaticPreservesWorld pre <| Rinst.run ⟨0, staticSevm, pre⟩ .tstore

private def staticSstoreControl : Bool :=
  let pre := { (((default : Devm).setTransVal addressA otherKey 23)
    |> fun d : Devm => d.withGasLeft 100000).withStack [key, 5] with
      world := { (default : Devm).world with
        state := State.setBal (Std.TreeMap.empty : State) addressA 7 } }
  writeInStaticPreservesWorld pre <| Rinst.run ⟨0, staticSevm, pre⟩ .sstore

private def staticTloadControl : Bool :=
  match Rinst.run ⟨0, staticSevm,
      ((default : Devm).setTransVal addressA key 11
        |> fun d => d.withGasLeft 100000
        |> fun d => d.withStack [key])⟩ .tload with
  | .ok post => post.stack == [11]
  | _ => false

private def staticUnderstackControl : Bool :=
  isStackUnderflow <| Rinst.run ⟨0, staticSevm,
    (default : Devm)⟩ .tstore

private def staticUndergasControl : Bool :=
  isOutOfGas <| Rinst.run ⟨0, staticSevm,
    ((default : Devm).withGasLeft 0).withStack [key, 5]⟩ .tstore

private def spawnedStatic : XStep → Bool
  | .spawn frame _ => frame.inner.isStatic
  | _ => false

private def staticCallPre : Devm :=
  ((default : Devm).withGasLeft 100000)
    |>.withStack [50000, addressA.toB256, 0, 0, 0, 0, 0]

private def staticDelcallPre : Devm :=
  ((default : Devm).withGasLeft 100000)
    |>.withStack [50000, addressA.toB256, 0, 0, 0, 0]

private def staticCallFamilyControls : Bool :=
  spawnedStatic (Xinst.step staticSevm staticCallPre .call) &&
  spawnedStatic (Xinst.step staticSevm staticCallPre .callcode) &&
  spawnedStatic (Xinst.step staticSevm staticDelcallPre .delcall) &&
  spawnedStatic (Xinst.step dynamicSevm staticDelcallPre .statcall)

private def isNotSpawn : XStep → Bool
  | .spawn _ _ => false
  | _ => true

private def staticCreateControl : Bool :=
  let createPre := ((default : Devm).withGasLeft 100000).withStack [0, 0, 0]
  let create2Pre := ((default : Devm).withGasLeft 100000).withStack [0, 0, 0, 0]
  isNotSpawn (Xinst.step staticSevm createPre .create) &&
  isNotSpawn (Xinst.step staticSevm create2Pre .create2)

private def directPre : Devm :=
  (((default : Devm).setTransVal addressA key 31).withGasLeft 100000)
    |>.withStack [50000, addressB.toB256, 0, 0, 0, 0, 0]

private def directCallControl : Bool :=
  match Xinst.step dynamicSevm directPre .call with
  | .spawn frame _ =>
      let child := frame.inner
      child.currentTarget == addressB &&
      child.codeAddress == some addressB &&
      child.caller == addressA && child.value == 0 &&
      child.shouldTransferValue && child.isStatic == false &&
      (child.tenv.transientStorage.getD addressA .empty).get key ==
        directPre.getTransVal addressA key
  | _ => false

private def directStatcallPre : Devm :=
  (((default : Devm).setTransVal addressA key 37).withGasLeft 100000)
    |>.withStack [50000, addressB.toB256, 0, 0, 0, 0]

private def directStatcallControl : Bool :=
  match Xinst.step dynamicSevm directStatcallPre .statcall with
  | .spawn frame _ =>
      let child := frame.inner
      child.currentTarget == addressB &&
      child.codeAddress == some addressB &&
      child.caller == addressA && child.value == 0 &&
      child.shouldTransferValue && child.isStatic &&
      (child.tenv.transientStorage.getD addressA .empty).get key ==
        directStatcallPre.getTransVal addressA key
  | _ => false

/-- Actual CALLCODE and DELEGATECALL edges can have the same target and code
address as the current frame. Their opcode edge—not a field inequality—is what
keeps them distinct from the direct CALL/STATICCALL projections. -/
private def coincidentIndirectEdgesControl : Bool :=
  match Xinst.step dynamicSevm staticCallPre .callcode,
      Xinst.step dynamicSevm staticDelcallPre .delcall with
  | .spawn callcodeFrame _, .spawn delegateFrame _ =>
      callcodeFrame.inner.currentTarget == addressA &&
      callcodeFrame.inner.codeAddress == some addressA &&
      callcodeFrame.inner.shouldTransferValue &&
      delegateFrame.inner.currentTarget == addressA &&
      delegateFrame.inner.codeAddress == some addressA &&
      !delegateFrame.inner.shouldTransferValue
  | _, _ => false

private def delegationCode : ByteArray :=
  ByteArray.mk <| (eoaDelegationMarker ++ delegateAddress.toBytes).toArray

private def delegatedBody : ByteArray := ByteArray.mk #[0x00]

private def delegatedState : State :=
  State.setCode (State.setCode (Std.TreeMap.empty : State)
    addressB delegationCode) delegateAddress delegatedBody

private def delegatedPre : Devm :=
  { directPre with world := { directPre.world with state := delegatedState } }

private def delegatedSevm : Sevm :=
  { dynamicSevm with benvStat := { dynamicSevm.benvStat with
      origState := delegatedState } }

private def delegatedDirectCallControl : Bool :=
  match Xinst.step delegatedSevm delegatedPre .call with
  | .spawn frame _ =>
      let child := frame.inner
      child.currentTarget == addressB &&
      -- EIP-7702: the storage owner stays the popped callee, while the code
      -- address is the account its designator names.  Before the conformance
      -- fix this read `some addressB`, fusing the two roles.
      child.codeAddress == some delegateAddress &&
      child.currentTarget != child.codeAddress.getD addressB &&
      child.code == delegatedBody && child.code != delegationCode
  | _ => false

private def sharedParent : Devm :=
  ((default : Devm).setTransVal addressA key 42)
    |> fun d => d.setTransVal addressB key 0
    |> fun d => d.withGasLeft 100000

private def foreignMsg : Msg :=
  callMsg dynamicSevm sharedParent 10000 0 addressA addressB addressB
    true false [] ByteArray.empty false

private def reentryMsg : Msg :=
  callMsg dynamicSevm sharedParent 10000 0 addressB addressA addressA
    true false [] ByteArray.empty false

private def sameTransactionAddressIsolation : Bool :=
  let foreign := initDevm foreignMsg
  let reentry := initDevm reentryMsg
  let foreignLoad := Rinst.run ⟨0, { dynamicSevm with currentTarget := addressB },
    (foreign.withGasLeft 100000).withStack [key]⟩ .tload
  let reentryLoad := Rinst.run ⟨0, dynamicSevm,
    (reentry.withGasLeft 100000).withStack [key]⟩ .tload
  foreign.getTransVal addressB key == 0 &&
  foreign.getTransVal addressA key == 42 &&
  match foreignLoad, reentryLoad with
  | .ok foreignPost, .ok reentryPost =>
      foreignPost.stack == [0] && reentryPost.stack == [42]
  | _, _ => false

private def resumedSharingControl : Bool :=
  let child := ((initDevm foreignMsg).setTransVal addressB otherKey 17)
  match (Resume.call sharedParent 0 0).run (.ok child) with
  | .ok resumed =>
      resumed.getTransVal addressA key == 42 &&
      resumed.getTransVal addressB otherKey == 17
  | _ => false

private def rawRollbackKeepsLogs : Bool :=
  let entryState := State.setBal (Std.TreeMap.empty : State) addressA 5
  let entryTra := Tra.setStorVal (Std.TreeMap.empty : Tra) addressA key 7
  let raw := ((default : Devm).withLogs
    [{ address := addressA, topics := [], data := [0xaa] }])
  let rolled := raw.rollback entryState entryTra
  match rolled.logs with
  | [log] => log.data == [0xaa] &&
      rolled.state.bal addressA == entryState.bal addressA &&
      rolled.getTransVal addressA key == 7
  | _ => false

private def failedCode : ByteArray := ByteArray.mk #[
  0x60,0x37,0x60,0x04,0x5d,
  0x60,0x42,0x60,0x05,0x55,
  0x60,0x04,0x5c,0x60,0x05,0x54,
  0x60,0x00,0x60,0x00,0xa2,
  0x60,0x01,0x60,0x00,0x53,
  0x60,0x01,0x60,0x00,0xfd]

private def cleanLogCode : ByteArray := ByteArray.mk #[
  0x60,0x00,0x60,0x00,0xa0,0x00]

private def messageWithCode (code : ByteArray) : Msg :=
  { (default : Msg) with target := some addressA, currentTarget := addressA, codeAddress := some addressA, code := code, gas := 100000, depth := 1024 }

private def parentLog : Log :=
  { address := addressA, topics := [], data := [0xbb] }

private def settlementParent : Devm :=
  let state := (State.setBal (Std.TreeMap.empty : State) addressA 13).setStorVal
    addressB 5 9
  let parent := sharedParent.setTransVal addressB 4 11
  { (parent.withState state).withLogs [parentLog] with
    mach := { sharedParent.mach with gasLeft := 100000 } }

private def childMessage (code : ByteArray) : Msg :=
  callMsg dynamicSevm settlementParent 80000 0 addressA addressB addressB
    true false [] code false

private def caughtChildSettlementControl : Bool :=
  let msg := childMessage failedCode
  match processMessage msg with
  | .ok child =>
      match (Resume.call settlementParent 0 0).run (.ok child) with
      | .ok resumed =>
          child.error.isSome && child.logs.length == 1 &&
          (match child.logs with
            | [log] => log.topics == [0x42, 0x37]
            | _ => false) &&
          child.getTransVal addressB 4 == 11 &&
          child.getStorVal addressB 5 == 9 &&
          child.state.bal addressA == msg.benv.state.bal addressA &&
          child.getTransVal addressA key ==
            (msg.tenv.transientStorage.getD addressA .empty).get key &&
          resumed.logs.length == settlementParent.logs.length &&
          resumed.state.bal addressA == msg.benv.state.bal addressA &&
          resumed.getTransVal addressA key == 42
      | _ => false
  | _ => false

private def cleanChildSettlementControl : Bool :=
  let msg := childMessage cleanLogCode
  match processMessage msg with
  | .ok child =>
      match (Resume.call settlementParent 0 0).run (.ok child) with
      | .ok resumed =>
          child.error.isNone && child.logs.length == 1 &&
          resumed.logs.length == settlementParent.logs.length + child.logs.length &&
          resumed.state.bal addressA == child.state.bal addressA &&
          resumed.getTransVal addressA key == child.getTransVal addressA key
      | _ => false
  | _ => false

private def outerRollbackControl : Bool :=
  let outerState := (State.setBal (Std.TreeMap.empty : State) addressA 3).setStorVal
    addressA 5 3
  let outerTra := Tra.setStorVal (Std.TreeMap.empty : Tra) addressA 4 6
  let msg := { (messageWithCode failedCode) with
    benv := { (default : Benv) with state := outerState }
    tenv := { (default : Tenv) with
      transientStorage := outerTra } }
  match processMessage msg with
  | .ok out =>
      out.error.isSome && out.logs.length == 1 &&
      out.state.bal addressA == msg.benv.state.bal addressA &&
      out.getTransVal addressA 4 == 6 && out.getStorVal addressA 5 == 3 &&
      out.getStorVal addressA 5 != settlementParent.getStorVal addressB 5
  | _ => false

private def failedTopLevelControl : Bool :=
  let msg := messageWithCode failedCode
  match processMessage msg, processMessageCall msg with
  | .ok raw, .ok (_, out) =>
      raw.logs.length == 1 && raw.output == [1] && raw.error.isSome &&
      out.logs.isEmpty && out.returnData == [1] && out.error.isSome
  | _, _ => false

private def cleanTopLevelControl : Bool :=
  match processMessageCall (messageWithCode cleanLogCode) with
  | .ok (_, out) => out.error.isNone && out.logs.length == 1
  | _ => false

private def fatalResumeControl : Bool :=
  match (Resume.call (default : Devm) 0 0).run
      (.error ⟨.crypto (.invalidSignature .none), (Std.TreeMap.empty : State),
        .emptyWithCapacity, (Std.TreeMap.empty : Tra)⟩) with
  | .error _ => true
  | _ => false

private def internalFatalResumeControl : Bool :=
  match (Resume.call (default : Devm) 0 0).run
      (.error ⟨.internal (.assertion .none), (Std.TreeMap.empty : State),
        .emptyWithCapacity, (Std.TreeMap.empty : Tra)⟩) with
  | .error _ => true
  | _ => false

/-! ## Two actual accepted transactions -/

private def fromHex (s : String) : Bytes := (Hex.toBytes s).getD []

private def signed0 : Bytes := fromHex
  "f860800a83030d409400000000000000000000000000000000dead0001808026a0c110143e674a68273614d920180e28deef6f56ff58f3a033cfa10decab08cd95a0222d5d6b7c5419a1330d46d402c74368a134abc95a391a5f541ad59aa35f8052"

private def signed1 : Bytes := fromHex
  "f860010a83030d409400000000000000000000000000000000dead0001808025a009835eead9ef60d95947adcfa59e56cacee1dbfd9e7a152a4b2882ccb3ca26b9a05fb6ef64fa01db1a6cdfe9e4a34005a3272878501ce97d3b3cf89fb6bc6ddf6d"

private def decodeLegacy (bs : Bytes) : Option Tx :=
  bs.toBLT?.bind fun blt => blt.toExTx.toOption

private def tx0 : Tx := (decodeLegacy signed0).get (by native_decide)
private def tx1 : Tx := (decodeLegacy signed1).get (by native_decide)
private def txSender : Adr := 0xcd09f75e2bf2a4d11f3ab23f1389fcc1621c0cc2
private def txTarget : Adr := 0x00000000000000000000000000000000dead0001

/-- Transaction one writes transient `42`, TLOADs it into persistent slot two,
and sets persistent flag zero. Transaction two follows the flag branch, first
TLOADs the same transient cell (freshly zero), clears slot two, and sets a
persistent marker. -/
private def resetProgram : ByteArray := ByteArray.mk #[
  0x60,0x00,0x54,0x60,0x17,0x57,
  0x60,0x2a,0x60,0x01,0x5d,0x60,0x01,0x5c,0x60,0x02,0x55,
  0x60,0x01,0x60,0x00,0x55,0x00,0x5b,
  0x60,0x01,0x5c,0x60,0x02,0x55,
  0x60,0x01,0x60,0x03,0x55,0x00]

private def transactionState : State :=
  State.set (State.set (Std.TreeMap.empty : State) txSender
    { Acct.nil with bal := Nat.toB256 100000000 }) txTarget
    { Acct.nil with nonce := 1, code := resetProgram }

private def transactionBenv : Benv :=
  { state := transactionState
    createdAccounts := .emptyWithCapacity
    stat := { (default : BenvStat) with chainId := 1, blockGasLimit := 1000000, origState := transactionState } }

/-- The exact message-producing prefix of `processTransaction`, retained in
the fixture so reset and receipt controls cannot substitute a freely built
empty transaction environment. -/
private def preparedMessageFor
    (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) :
    Except TransitionError Msg := do
  let benv := benv.beginTransaction
  let bout ← .ok { bout with transactionsTrie :=
    bout.transactionsTrie.insert (BLT.bytes index.toBytes).toBytes tx }
  let ⟨intrinsicGas, _⟩ ← Except.mapError TransitionError.transaction
    (validateTransaction benv.stat.rules tx)
  let ⟨sender, effectiveGasPrice, blobVersionedHashes, _⟩ ←
    checkTransaction benv bout tx
  let blobGasFee := if tx.isTypeThree then
    calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx else 0
  let effectiveGasFee := tx.gas * effectiveGasPrice
  let state := benv.state.incrNonce sender
  let state ← (state.subBal sender (effectiveGasFee + blobGasFee).toB256).toExcept
    (TransitionError.internal (.invariant (.text "balance underflow")))
  let tenv : Tenv := {
    transientStorage := .empty
    stat := {
      origin := sender
      gasPrice := effectiveGasPrice
      gas := tx.gas - intrinsicGas
      accessListAddresses := .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
      accessListStorageKeys := .ofList
        (tx.accessList.map (fun ⟨adr, keys⟩ => keys.map (⟨adr, ·⟩))).flatten
      blobVersionedHashes := blobVersionedHashes
      auths := tx.auths
      indexInBlock := index
      txHash := getTxHash tx } }
  prepareMessage { benv with state := state } tenv tx

private def firstTransaction := processTransaction transactionBenv .init tx0 0

private def secondTransaction := firstTransaction >>= fun (state, bout) =>
  processTransaction (transactionBenv.withState state) bout tx1 1

private def sequentialResetControl : Bool :=
  match preparedMessageFor transactionBenv .init tx0 0, firstTransaction with
  | .ok msg1, .ok (state1, bout1) =>
    match processMessage msg1,
        preparedMessageFor (transactionBenv.withState state1) bout1 tx1 1,
        secondTransaction with
    | .ok raw1, .ok msg2, .ok (state2, bout2) =>
      match processMessage msg2 with
      | .ok raw2 =>
      msg1.tenv.transientStorage.isEmpty &&
      raw1.getTransVal txTarget key == 42 &&
      (state1.get txTarget).stor.get 2 == 42 &&
      (state1.get txTarget).stor.get 0 == 1 &&
      msg2.tenv.transientStorage.isEmpty &&
      raw2.getTransVal txTarget key == 0 &&
      (state2.get txTarget).stor.get 2 == 0 &&
      (state2.get txTarget).stor.get 3 == 1 &&
      bout1.receiptKeys.length == 1 && bout2.receiptKeys.length == 2
      | _ => false
    | _, _, _ => false
  | _, _ => false

private def failedTransactionState : State :=
  State.setCode transactionState txTarget failedCode

private def failedTransactionBenv : Benv :=
  { transactionBenv with state := failedTransactionState, stat := { transactionBenv.stat with origState := failedTransactionState } }

private def failedInitialBout : BlockOutput :=
  { BlockOutput.init with blockLogs := [parentLog] }

private def sameLog (left right : Log) : Bool :=
  left.address == right.address && left.topics == right.topics &&
    left.data == right.data

private def sameLogs : List Log → List Log → Bool
  | [], [] => true
  | left :: ls, right :: rs => sameLog left right && sameLogs ls rs
  | _, _ => false

private def linkedFailedReceiptControl : Bool :=
  match preparedMessageFor failedTransactionBenv failedInitialBout tx0 0,
      processTransaction failedTransactionBenv failedInitialBout tx0 0 with
  | .ok msg, .ok (_, bout) =>
    match processMessage msg, processMessageCall msg with
    | .ok raw, .ok (_, out) =>
      raw.logs.length == 1 && raw.output == [1] && raw.error.isSome &&
      out.logs.isEmpty && out.returnData == [1] && out.error.isSome &&
      sameLogs bout.blockLogs failedInitialBout.blockLogs &&
      bout.receiptKeys.length == 1 &&
      match Std.TreeMap.get? bout.receiptsTrie bout.receiptKeys[0]! with
      | some (_, receipt) => receipt.logs.isEmpty && !receipt.succeeded
      | none => false
    | _, _ => false
  | _, _ => false

private def controls : List Bool := [
  cellClearControl,
  tloadControl,
  staticTstoreControl,
  staticSstoreControl,
  staticTloadControl,
  staticUnderstackControl,
  staticUndergasControl,
  staticCallFamilyControls,
  staticCreateControl,
  directCallControl,
  directStatcallControl,
  coincidentIndirectEdgesControl,
  delegatedDirectCallControl,
  sameTransactionAddressIsolation,
  resumedSharingControl,
  rawRollbackKeepsLogs,
  caughtChildSettlementControl,
  cleanChildSettlementControl,
  outerRollbackControl,
  failedTopLevelControl,
  cleanTopLevelControl,
  fatalResumeControl,
  internalFatalResumeControl,
  sequentialResetControl,
  linkedFailedReceiptControl]

private theorem concrete_controls : controls = List.replicate 25 true := by
  native_decide

/-- Lean-level positive manifest. Deleting any required common theorem makes
this fixture fail elaboration before the evaluator can run. -/
private theorem required_positive_controls : True := by
  let _tstore := @Blanc.tstore_run_cell
  let _zero := @Blanc.tstore_run_zero
  let _tload := @Blanc.tload_run_cell
  let _callNonzero := @Blanc.directCall_nonzero_spawn
  let _callZero := @Blanc.directCall_zero_spawn
  let _statcall := @Blanc.directStatcall_spawn
  let _caught := @Blanc.caughtCall_childSettlement
  let _clean := @Blanc.cleanCall_childSettlement
  let _prepared := @Blanc.preparedTransactionMessage_exists
  let _empty := @Blanc.PreparedTransactionMessage.transientStorage_eq_empty
  let _logs := @Blanc.processMessageCall_error_logs_eq_nil
  let _linked := @Blanc.PreparedTransactionMessage.error_logs_eq_nil
  let _sstore := @Blanc.of_run_sstore_not_static
  let _staticSpawn := @Blanc.Xinst.step_spawn_isStatic
  let _staticCall := @Blanc.Ninst.step_statcall_run_isStatic
  let _concrete := concrete_controls
  exact True.intro

#eval! controls

private theorem positive_deletion_witness : True := by
  let _ := concrete_controls
  let _ := required_positive_controls
  exact True.intro

-- ADDRESS-COORDINATE-MUTANT-CONTROL
-- KEY-COORDINATE-MUTANT-CONTROL
-- OPERAND-ORDER-MUTANT-CONTROL
-- WHOLE-MAP-CLEAR-MUTANT-CONTROL
-- STATIC-GUARD-MUTANT-CONTROL
-- STATIC-PRECEDENCE-MUTANT-CONTROL
-- FIELD-ONLY-DIRECT-CALL-MUTANT-CONTROL
-- CALLCODE-DIRECT-MUTANT-CONTROL
-- DELEGATECALL-DIRECT-MUTANT-CONTROL
-- STATIC-PARENT-MUTANT-CONTROL
-- STATIC-CREATE-MUTANT-CONTROL
-- DELEGATED-CODE-IDENTITY-MUTANT-CONTROL
-- CHILD-OUTER-ROLLBACK-MUTANT-CONTROL
-- RAW-LOG-CLEAR-MUTANT-CONTROL
-- CHILD-LOG-APPEND-MUTANT-CONTROL
-- FATAL-CAUGHT-MUTANT-CONTROL
-- TOP-LEVEL-LOG-LEAK-MUTANT-CONTROL
-- REVERT-DATA-ERASURE-MUTANT-CONTROL
-- UNLINKED-RECEIPT-MUTANT-CONTROL
-- UNRELATED-TRANSACTIONS-MUTANT-CONTROL
-- CROSS-TRANSACTION-INHERITANCE-MUTANT-CONTROL
-- PER-FRAME-CLEAR-MUTANT-CONTROL

end

end Blanc.TransientSettlementRegression
