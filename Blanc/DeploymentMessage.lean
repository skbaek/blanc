-- DeploymentMessage.lean : contract-neutral CREATE message plumbing.
--
-- Constructor-specific execution remains in each contract.  This owner keeps
-- the shared bridge from fresh-account preparation and zero-value transfer to
-- an ordinary successful `processMessage` result.

import Blanc.ExecutionOccurrence
import Init.Data.Ord.UInt

namespace Blanc

open Jaune

/-- Jaune's generic creation preparation clears the new account's storage
before incrementing its nonce. -/
theorem processCreateMessage_msg_getStor_currentTarget (msg : Msg) :
    (processCreateMessage.msg msg).benv.state.getStor msg.currentTarget =
      Stor.empty := by
  change (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
    msg.currentTarget).get msg.currentTarget).stor = .empty
  rw [State.incrNonce_get_stor]
  unfold State.setStor
  rw [State.get_set_self]

/-- A zero-value message can always cross its optional entry transfer. -/
theorem benvAfterTransfer_exists_zero
    {msg : Msg} (hvalue : msg.value = 0) :
    ∃ benv, msg.benvAfterTransfer = .ok benv := by
  have hnot : ¬ msg.benv.state.bal msg.caller < (0 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero]
    omega
  unfold Msg.benvAfterTransfer
  rw [hvalue]
  by_cases htransfer : msg.shouldTransferValue = true
  · rw [if_pos htransfer]
    unfold Benv.subBal State.subBal
    rw [if_neg hnot]
    exact ⟨_, rfl⟩
  · rw [if_neg htransfer]
    exact ⟨_, rfl⟩

/-- Message-entry balance transfer preserves the static block environment. -/
theorem benvAfterTransfer_stat
    {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) :
    benv.stat = msg.benv.stat := by
  by_cases htransfer : msg.shouldTransferValue = true
  · obtain ⟨middle, hsub, rfl⟩ := of_benvAfterTransfer htransfer h
    rfl
  · rw [of_benvAfterTransfer_no htransfer h]

/-- A successful raw `exec` with no frame error settles as the corresponding
ordinary message result. -/
theorem processMessage_ok_of_exec
    {msg : Msg} {benv : Benv} {post : Devm}
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hcodeAddress : msg.codeAddress = .none)
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post)
    (herror : post.error = .none) :
    processMessage msg = .ok post := by
  unfold processMessage runFrame Frame.enter Frame.ofCall
  rw [htransfer]
  unfold executeCode.enter
  simp only [Msg.withBenv, hcodeAddress]
  unfold Frame.settle Frame.settleMsg
  simp only [Msg.withBenv, hcodeAddress] at hexec
  rw [hexec]
  simp [executeCode.handleError, processMessage.settle, herror]

/-- Successful inner-message execution followed by successful code charging is
the successful CREATE settlement, with the charged output installed at the
new target. -/
theorem processCreateMessage_ok_of_processMessage_and_charge
    (msg : Msg) {raw charged : Devm}
    (hprocess : processMessage (processCreateMessage.msg msg) = .ok raw)
    (herror : raw.error = .none)
    (hcharge :
      processCreateMessage.chargeCodeGas msg.benv.stat.rules raw = .ok charged) :
    processCreateMessage msg =
      .ok (charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩) := by
  rw [processCreateMessage_eq, hprocess]
  unfold processCreateMessage.settle
  simp [herror, hcharge]

/-- An inner creation frame whose error marker is set bypasses code charging
and settles successfully with its entry world and transient storage restored.
Raw output, logs, and the error marker are intentionally retained by Jaune's
`Devm.rollback`; callers that need transaction-observable failed-CREATE logs
must use the outer call-settlement theorem instead. -/
theorem processCreateMessage_ok_of_processMessage_error
    (msg : Msg) {inner : Devm}
    (hprocess :
      processMessage (processCreateMessage.msg msg) = .ok inner)
    (herror : inner.error.isSome = true) :
    processCreateMessage msg =
      .ok (inner.rollback msg.benv.state msg.tenv.transientStorage) := by
  rw [processCreateMessage_eq, hprocess]
  unfold processCreateMessage.settle
  simp only [bind, Except.bind]
  have hnotNone : inner.error.isNone ≠ true := by
    intro hnone
    rw [Option.isNone_iff_eq_none] at hnone
    rw [hnone] at herror
    cases herror
  rw [if_neg hnotNone]

/-- The outer message result induced by a successful direct CREATE after code
charging.  Constructor families may retain their historical wrapper names,
but the projection itself is contract-neutral. -/
def directCreateMessageOutputOf (post : Devm) : MsgCallOutput :=
  { gasLeft := post.gasLeft
    refundCounter := 0
    logs := post.logs
    accountsToDelete := post.accountsToDelete
    error := post.error
    returnData := post.output }

/-! ## Contract-neutral protocol-deployment plumbing -/

private theorem deploymentListCompare_eq_compareLex {α : Type u} [Ord α]
    (xs ys : List α) :
    Jaune.List.compare xs ys = List.compareLex compare xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          cases h : compare x y <;>
            simp [Jaune.List.compare, List.compareLex, h, ih]

private instance : Std.TransCmp
    (compare : Bytes → Bytes → Ordering) := by
  rw [show (compare : Bytes → Bytes → Ordering) =
      List.compareLex (compare : UInt8 → UInt8 → Ordering) by
    funext xs ys
    exact deploymentListCompare_eq_compareLex xs ys]
  infer_instance

/-- The small nonempty program used at mandatory protocol system addresses in
strict private-chain deployment anchors. -/
def deploymentSystemProgram : Prog := ⟨Func.stop, []⟩

def deploymentReceiptKey (index : Nat) : Bytes :=
  BLT.toBytes (.bytes index.toBytes)

def deploymentTxPreludeBout
    (bout : BlockOutput) (tx : Tx) (index : Nat) : BlockOutput :=
  {bout with
    transactionsTrie :=
      bout.transactionsTrie.insert (BLT.bytes index.toBytes).toBytes tx}

def deploymentIntrinsicGas (tx : Tx) : Nat :=
  (calculateIntrinsicCost tx).1

def deploymentCalldataFloorGas (tx : Tx) : Nat :=
  (calculateIntrinsicCost tx).2

def deploymentEffectiveGasPrice (benv : Benv) (tx : Tx) : Nat :=
  match tx.type with
  | .two _ maxPriorityFee maxFee _ _ =>
      min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas
  | _ => 0

def deploymentTenv
    (benv : Benv) (tx : Tx) (sender : Adr) (index : Nat) : Tenv :=
  { transientStorage := .empty
    stat :=
      { origin := sender
        gasPrice := deploymentEffectiveGasPrice benv tx
        gas := tx.gas - deploymentIntrinsicGas tx
        accessListAddresses := .ofList [benv.stat.coinbase]
        accessListStorageKeys := .ofList []
        blobVersionedHashes := []
        auths := []
        indexInBlock := index
        txHash := getTxHash tx } }

def deploymentUsedGasFromMessage (tx : Tx) (out : MsgCallOutput) : Nat :=
  max
    (tx.gas - out.gasLeft -
      min ((tx.gas - out.gasLeft) / 5) out.refundCounter.toNat)
    (deploymentCalldataFloorGas tx)

def deploymentFinalState
    (benv : Benv) (tx : Tx) (sender : Adr)
    (messagePost : State) (usedGas : Nat) : State :=
  (messagePost.addBal sender
      ((tx.gas - usedGas) *
        deploymentEffectiveGasPrice benv tx).toB256).addBal
    benv.stat.coinbase
      (usedGas *
        (deploymentEffectiveGasPrice benv tx -
          benv.stat.baseFeePerGas)).toB256

def deploymentFinalBout
    (bout : BlockOutput) (tx : Tx) (index : Nat)
    (out : MsgCallOutput) (usedGas : Nat) : BlockOutput :=
  let prelude := deploymentTxPreludeBout bout tx index
  let charged :=
    {prelude with
      blockGasUsed := prelude.blockGasUsed + usedGas
      blobGasUsed := prelude.blobGasUsed}
  let receipt := makeReceipt tx out.error charged.blockGasUsed out.logs
  {charged with
    receiptKeys := charged.receiptKeys ++ [deploymentReceiptKey index]
    receiptsTrie := charged.receiptsTrie.insert
      (deploymentReceiptKey index) receipt
    blockLogs := charged.blockLogs ++ out.logs}

/-- Contract-neutral configured base and protocol-system-code facts.  The
schedule is the caller's `cfg` and every rule-sensitive fact is either stated
against the block's selected `rules` or quantified over every successful
`rulesAt`, so no named fork is fixed here.  Every field describes only the
supplied prestate. -/
structure CanonicalDeploymentBase
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (sender ca : Adr) : Prop where
  configValid : cfg.Valid
  chainId_eq : cfg.chainId = base.chainId
  validContext : base.ValidContext
  sumNof : SumNof base.state.bal
  target_eq : ca = computeContractAddress sender (base.state.getNonce sender)
  target_ne_zero : ca ≠ 0
  target_not_precompile : ∀ {timestamp selected},
    cfg.rulesAt timestamp = .ok selected → ¬ selected.isPrecomp ca
  beacon_not_precompile : ¬ rules.isPrecomp beaconRootsAddress
  history_not_precompile : ¬ rules.isPrecomp historyStorageAddress
  withdrawalRequest_not_precompile :
    ¬ rules.isPrecomp withdrawalRequestPredeployAddress
  consolidationRequest_not_precompile :
    ¬ rules.isPrecomp consolidationRequestPredeployAddress
  sender_ne_target : sender ≠ ca
  withdrawalRequest_ne_target : withdrawalRequestPredeployAddress ≠ ca
  consolidationRequest_ne_target : consolidationRequestPredeployAddress ≠ ca
  target_noCodeOrNonce : accountHasCodeOrNonce base.state ca = false
  target_noStorage : accountHasStorage base.state ca = false
  lastBlockHash : ∃ lastHash,
    List.getLast? (getLast256BlockHashes base) = some lastHash
  beaconCode :
    some (base.state.getCode beaconRootsAddress).toList =
      Prog.compile deploymentSystemProgram
  historyCode :
    some (base.state.getCode historyStorageAddress).toList =
      Prog.compile deploymentSystemProgram
  withdrawalRequestCode :
    some (base.state.getCode withdrawalRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  consolidationRequestCode :
    some (base.state.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram

/-- The mandatory beacon-roots and history-storage calls recovered from the
real block prefix, under the block's selected `rules`. This structure is
conclusion evidence, never input data. -/
structure DeploymentSystemPrefix
    (rules : ForkRules)
    (base : BlockChain) (block : Block) (txInput : Benv) : Type where
  stBeacon : State
  outBeacon : MsgCallOutput
  lastHash : B256
  stHistory : State
  outHistory : MsgCallOutput
  beaconRun :
    processUncheckedSystemTransaction
      (initBenv rules base block.header)
      beaconRootsAddress block.header.parentBeaconBlockRoot.toBytes =
      .ok (stBeacon, outBeacon)
  lastHashEq :
    List.getLast?
      ((initBenv rules base block.header).withState stBeacon).stat.blockHashes =
        some lastHash
  historyRun :
    processUncheckedSystemTransaction
      ((initBenv rules base block.header).withState stBeacon)
      historyStorageAddress lastHash.toBytes = .ok (stHistory, outHistory)
  txInput_eq :
    txInput =
      ((initBenv rules base block.header).withState stBeacon).withState
        stHistory
  environment_eq : txInput = initBenv rules base block.header
  state_eq : txInput.state = base.state
  createdAccounts_eq : txInput.createdAccounts = .emptyWithCapacity

private theorem processMessageCall_ok_of_compiled_exec
    {p : Prog} {msg : Msg} {child : Evm} {post : Devm}
    (hauths : msg.tenv.stat.auths = [])
    (htarget : msg.target.isNone = false)
    (hcompile : some msg.code.toList = Prog.compile p)
    (henter : (Frame.ofCall msg).enter = .run child)
    (hexec : exec child = .ok post)
    (herror : post.error = none)
    (hrefund : 0 ≤ post.refundCounter) :
    processMessageCall msg = .ok
      (post.state,
        { gasLeft := post.gasLeft
          refundCounter := post.refundCounter.toNat
          logs := post.logs
          accountsToDelete := post.accountsToDelete
          error := post.error
          returnData := post.output }) := by
  have hprocess : processMessage msg = .ok post := by
    unfold processMessage runFrame
    rw [henter]
    unfold Frame.settle Frame.settleMsg processMessage.settle
      executeCode.handleError
    simp only [hexec, herror, Frame.ofCall, Option.isSome,
      Bool.false_eq_true, if_false, bind, Except.bind]
  have hdelegation : getDelegatedCodeAddress msg.code = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg (not_delegation_of_compile hcompile)]
  have htoNat : Int.toNat? post.refundCounter =
      some post.refundCounter.toNat :=
    Int.mem_toNat?.mpr (Int.toNat_of_nonneg hrefund).symm
  unfold processMessageCall
  rw [htarget]
  unfold processMessageCall.call
  simp only [hauths, List.isEmpty, if_true, bind, Except.bind,
    hdelegation, hprocess, Except.bimap, id_eq, herror, Option.isNone,
    htoNat, Option.toExcept, Nat.cast_zero, zero_add]
  rfl

/-- The neutral two-instruction system program executes exactly and leaves the
world state unchanged. -/
theorem processUncheckedSystemTransaction_deploymentSystemProgram
    (benv : Benv) (target : Adr) (data : Bytes)
    (hcode : some (benv.state.getCode target).toList =
      Prog.compile deploymentSystemProgram)
    (hnp : ¬ benv.stat.rules.isPrecomp target) :
    ∃ out,
      processUncheckedSystemTransaction benv target data =
        .ok (benv.state, out) ∧
      out.error = none ∧
      out.refundCounter = 0 ∧
      out.logs = [] ∧
      out.accountsToDelete = .emptyWithCapacity ∧
      out.returnData = [] := by
  let begun := benv.beginTransaction
  let tenv := processSystemTransactionTenv begun
  let msg := processSystemTransactionMsg begun tenv target data
    (benv.state.getCode target)
  let post := (initDevm msg).setMach
    {(initDevm msg).mach with
      gasLeft := (initDevm msg).gasLeft - gJumpdest}
  have hcompile : some msg.code.toList =
      Prog.compile deploymentSystemProgram := by
    simpa [msg, processSystemTransactionMsg] using hcode
  have hrun : Prog.RunCompiled (initSevm msg) (initDevm msg)
      deploymentSystemProgram post := by
    apply Prog.runCompiled_stop
    change gJumpdest ≤ systemTransactionGas
    decide
  have hexec : exec (initEvm msg) = .ok post :=
    Prog.exec_of_runCompiled hrun hcompile
  have hnp' : ¬ benv.beginTransaction.stat.rules.isPrecomp target := by
    simpa [Benv.beginTransaction] using hnp
  have henter : (Frame.ofCall msg).enter = .run (initEvm msg) := by
    simp [Frame.enter, Frame.ofCall, executeCode.enter,
      Msg.benvAfterTransfer, Msg.withBenv, msg, begun,
      processSystemTransactionMsg, hnp']
  have hrefund : post.refundCounter = 0 := rfl
  have hcall := processMessageCall_ok_of_compiled_exec
    (p := deploymentSystemProgram) (msg := msg)
    (child := initEvm msg) (post := post)
    (by rfl) (by rfl) hcompile henter hexec
    (by rfl) (by simp [hrefund])
  let out : MsgCallOutput :=
    { gasLeft := post.gasLeft
      refundCounter := post.refundCounter.toNat
      logs := post.logs
      accountsToDelete := post.accountsToDelete
      error := post.error
      returnData := post.output }
  have hcallOut : processMessageCall msg = .ok (post.state, out) := by
    exact hcall
  have hpostState : post.state = benv.state := rfl
  rw [hpostState] at hcallOut
  refine ⟨out, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold processUncheckedSystemTransaction processSystemTransaction
    change processMessageCall msg = .ok (benv.state, out)
    exact hcallOut
  all_goals rfl

theorem processCheckedSystemTransaction_deploymentSystemProgram
    (benv : Benv) (target : Adr) (data : Bytes)
    (hcode : some (benv.state.getCode target).toList =
      Prog.compile deploymentSystemProgram)
    (hnp : ¬ benv.stat.rules.isPrecomp target) :
    ∃ out,
      processCheckedSystemTransaction benv target data =
        .ok (benv.state, out) ∧
      out.error = none ∧
      out.refundCounter = 0 ∧
      out.logs = [] ∧
      out.accountsToDelete = .emptyWithCapacity ∧
      out.returnData = [] := by
  obtain ⟨out, hrun, herr, hrefund, hlogs, hdelete, hreturn⟩ :=
    processUncheckedSystemTransaction_deploymentSystemProgram
      benv target data hcode hnp
  have hne : (benv.state.getCode target).isEmpty = false := by
    have hlistne : (benv.state.getCode target).toList ≠ [] := by
      intro hnil
      apply Prog.compile_ne_nil (p := deploymentSystemProgram)
      rw [← hcode, hnil]
    have hbytesne : benv.state.getCode target ≠ ByteArray.empty := by
      intro hempty
      apply hlistne
      rw [hempty]
      simp
    simpa [ByteArray.isEmpty] using hbytesne
  refine ⟨out, ?_, herr, hrefund, hlogs, hdelete, hreturn⟩
  unfold processCheckedSystemTransaction
  simp only [hne, Bool.false_eq_true, if_false]
  unfold processUncheckedSystemTransaction at hrun
  rw [hrun]
  simp [Except.mapError, herr]

/-- Reconstruct the mandatory beacon-roots and history-storage prefix from the
configured prestate; neither call is smuggled into the input record. -/
theorem canonicalDeploymentSystemPrefix
    (cfg : ChainConfig) (rules : ForkRules)
    (base : BlockChain) (cb : CanonicalBlock)
    (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg rules base sender ca) :
    Nonempty (Σ txInput, DeploymentSystemPrefix rules base cb.block txInput) := by
  let initial := initBenv rules base cb.block.header
  obtain ⟨outBeacon, hbeacon, _⟩ :=
    processUncheckedSystemTransaction_deploymentSystemProgram
      initial beaconRootsAddress cb.block.header.parentBeaconBlockRoot.toBytes
      (by simpa [initial, initBenv] using hbase.beaconCode)
      hbase.beacon_not_precompile
  obtain ⟨lastHash, hlast⟩ := hbase.lastBlockHash
  obtain ⟨outHistory, hhistory, _⟩ :=
    processUncheckedSystemTransaction_deploymentSystemProgram
      (initial.withState base.state) historyStorageAddress lastHash.toBytes
      (by simpa [initial, initBenv, Benv.withState] using hbase.historyCode)
      hbase.history_not_precompile
  refine ⟨⟨initial, {
    stBeacon := base.state
    outBeacon := outBeacon
    lastHash := lastHash
    stHistory := base.state
    outHistory := outHistory
    beaconRun := hbeacon
    lastHashEq := ?_
    historyRun := ?_
    txInput_eq := by rfl
    environment_eq := by rfl
    state_eq := by rfl
    createdAccounts_eq := by rfl }⟩⟩
  · simpa [initial, initBenv, initBenvStat, Benv.withState] using hlast
  · simpa [initial, Benv.withState] using hhistory

end Blanc
