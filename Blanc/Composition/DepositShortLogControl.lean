import Blanc.Composition.DepositShortLogInput
import Blanc.Forward
import Blanc.TransactionHistoricalForward
import Blanc.ExecutionKeptChain
import Blanc.DepositRequestParser
import Blanc.Corpus.Freeze.DepositCells
import Blanc.Lift.TransactionAmsterdam

/-! # An actual transaction emitting a malformed deposit log -/

namespace Blanc.Composition.DepositShortLogControl

open Jaune Blanc ExecutionTrace DepositShortLogInput

/-- PUSH32 topic; PUSH0 size; PUSH0 offset; LOG1; STOP. -/
def shortCode : ByteArray :=
  ⟨([0x7f] ++ depositEventSignatureHash.toBytes ++ [0x5f, 0x5f, 0xa1, 0x00]).toArray⟩

private def pushTopic : Ninst :=
  .push depositEventSignatureHash.toBytes (by rw [B256.length_toBytes])

private def program : Func :=
  .next pushTopic <| .next (.push [] (by decide)) <|
  .next (.push [] (by decide)) <| .next (.reg (.log 1)) <| .last .stop

theorem shortCode_size : shortCode.size = 37 := by
  simp only [shortCode, ByteArray.size, List.size_toArray, List.length_append,
    B256.length_toBytes]
  rfl

private theorem program_compile :
    Func.compile [] 0 program = some shortCode.toList := by
  simp only [program, pushTopic, Func.compile, Ninst.immAccepted, guard,
    ite_true, bind, Option.bind, pure, Ninst.toBytes, shortCode,
    ByteArray.toList_eq_toList_data, pushToB8L, pushToB8, B256.length_toBytes,
    List.append_assoc]
  rfl

/-- The malformed entry has the real topic and no event data. -/
def logAt (target : Adr) : Log := ⟨target, [depositEventSignatureHash], []⟩

def loggerPost (base : Devm) (target : Adr) (gas : Nat) : Devm :=
  (base.addLog (logAt target)).setMach ⟨[], .empty, gas, base.stateGas⟩

private theorem logger_run_any {sevm : Sevm} {base : Devm} {gas : Nat}
    (nonstatic : sevm.isStatic = false) :
    Func.RunCompiled [] sevm
      (base.setMach ⟨[], .empty, gas + 757, base.stateGas⟩) program
      (loggerPost base sevm.currentTarget gas) := by
  unfold program pushTopic
  refine .next (Ninst.runCompiled_pushB256Full (w := depositEventSignatureHash)
    (G := gas + 754) rfl (by change 0 < 1024; decide)) ?_
  func_run (3) [750]
  · change gLog + gLogdata * 0 + gLogtopic * 1 + Devm.extCost _ [⟨0, 0⟩] = 750
    rw [Devm.extCost_empty_window]
    rfl
  · simp only [Nat.add_sub_cancel]
    exact .last rfl

private theorem logger_run {sevm : Sevm} {base : Devm} {gas : Nat}
    (_covered : CoveredFork sevm.benvStat.fork) (nonstatic : sevm.isStatic = false) :
    Func.RunCompiled [] sevm
      (base.setMach ⟨[], .empty, gas + 757, base.stateGas⟩) program
      (loggerPost base sevm.currentTarget gas) :=
  logger_run_any nonstatic

/-- The original interpreter really emits the short log from this fresh message.
The world and inherited deletion set remain symbolic. -/
theorem logger_message {msg : Msg}
    (covered : CoveredFork msg.benv.stat.fork) (nonstatic : msg.isStatic = false)
    (code : msg.code = shortCode) (enough : 757 ≤ msg.gas) :
    ∃ post, exec (initEvm msg) = .ok post ∧
      post.state = msg.benv.state ∧ post.logs = [logAt msg.currentTarget] ∧
      post.error = none ∧ post.output = [] ∧ post.refundCounter = 0 ∧
      post.accountsToDelete = msg.inheritedDeletions ∧ post.gasLeft = msg.gas - 757 := by
  have run := logger_run (sevm := initSevm msg) (base := initDevm msg)
    (gas := msg.gas - 757) covered nonstatic
  rw [Nat.sub_add_cancel enough] at run
  change Func.RunCompiled [] (initSevm msg) (initDevm msg) program
    (loggerPost (initDevm msg) msg.currentTarget (msg.gas - 757)) at run
  have executed := Func.exec_of_runCompiled_prefix (sfx := []) run
    (show program.NoCalls by trivial) program_compile (by
      change msg.code.toList = shortCode.toList ++ []
      rw [code, List.append_nil])
  refine ⟨loggerPost (initDevm msg) msg.currentTarget (msg.gas - 757),
    executed, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [loggerPost, Devm.setMach_logs, Devm.addLog_logs]
  have hsg : msg.benv.stat.rules.stateGas = none := covered.stateGas_none
  change (match msg.benv.stat.rules.stateGas with
    | none => []
    | some _ => _) ++ [logAt msg.currentTarget] = _
  rw [hsg]
  rfl

private def senderAccount : Acct := ⟨2, 2147483648, .empty, ⟨#[]⟩⟩

private def loggerAccount : Acct := ⟨1, 0, .empty, shortCode⟩

def controlState (sender : Adr) : State :=
  State.setPresent (State.setPresent (.empty : State) sender senderAccount)
    depositContractAddress loggerAccount

def controlBenv (sender : Adr) : Benv :=
  { state := controlState sender, createdAccounts := .emptyWithCapacity
    stat := { fork := .prague, chainId := 1, origState := controlState sender
              blockGasLimit := 2 ^ 25, blockHashes := [], coinbase := 0, number := 0
              baseFeePerGas := 0, time := 0, prevRandao := 0, excessBlobGas := 0
              parentBeaconBlockRoot := 0 } }

private theorem sender_get {sender : Adr} (away : sender ≠ depositContractAddress) :
    (controlState sender).get sender = senderAccount := by
  rw [controlState, State.get_setPresent_ne _ (Ne.symm away), State.get_setPresent_self]

theorem logger_code (sender : Adr) :
    (controlBenv sender).state.getCode depositContractAddress = shortCode := by
  change ((controlState sender).get depositContractAddress).code = shortCode
  rw [controlState, State.get_setPresent_self]
  rfl

private theorem control_covered (sender : Adr) : CoveredFork (controlBenv sender).stat.fork := by
  change CoveredFork .prague
  decide

private theorem control_valid (sender : Adr) :
    validateTransaction (controlBenv sender).stat.rules controlTx 0 = .ok (21000, 21000) := by
  refine validateTransaction_ok_of_facts (control_covered sender).stateGas_none ?_
    (by decide) (by decide) rfl ?_
  · have cost := calculateIntrinsicCost_two_call (rules := (controlBenv sender).stat.rules)
      (tx := controlTx) (sender := 0) (control_covered sender).stateGas_none rfl rfl rfl
    have base : (controlBenv sender).stat.rules.gas.txBase = 21000 := rfl
    simpa only [controlTx, calldataTokens, List.foldl_nil, List.map_nil, List.sum_nil,
      Nat.zero_mul, Nat.zero_add, Nat.add_zero, base] using cost
  · exact (control_covered sender).shanghaiOnwards.checkTransactionGasCap_ok (by decide)

private theorem control_checked {sender : Adr}
    (recovered : recoverSender 1 controlTx = .ok sender)
    (away : sender ≠ depositContractAddress) :
    checkTransaction (controlBenv sender).beginTransaction
      (transactionPreludeBout BlockOutput.init controlTx 0) controlTx = .ok (sender, 1, [], 0) := by
  have htype : controlTx.type = .two 1 1 8 (some depositContractAddress) [] := rfl
  have hsg := (control_covered sender).stateGas_none
  have hgas := checkTransactionGasLimits_ok_of_room
    (benv := (controlBenv sender).beginTransaction)
    (bout := transactionPreludeBout BlockOutput.init controlTx 0) (tx := controlTx)
    hsg (by change 2 ^ 20 ≤ 2 ^ 25 - 0; decide)
    (by rw [calculateTotalBlobGas_two htype]; exact Nat.zero_le _)
  rw [calculateTotalBlobGas_two htype] at hgas
  refine checkTransaction_ok_of_parts hgas (checkTransactionChainId_two htype rfl)
    recovered (checkTransactionGasFee_two htype (by decide)
      (by change 0 ≤ 8; decide) (by decide +kernel))
    (checkTransactionBlobData_two htype _) (checkTransactionReceiver_two htype)
    (checkTransactionAuthorizationList_two htype) ?_
  apply checkTransactionSenderAccount_ok_of_noCode
  · change ((controlState sender).get sender).nonce = 2
    rw [sender_get away]
    rfl
  · change 2 ^ 20 * 8 + 0 ≤ ((controlState sender).get sender).bal.toNat
    rw [sender_get away]
    decide +kernel
  · change ((controlState sender).get sender).code.isEmpty = true
    rw [sender_get away]
    rfl

/-- Full original settlement, with its actual receipt and block-log projections. -/
theorem control_transaction {sender : Adr}
    (recovered : recoverSender 1 controlTx = .ok sender)
    (away : sender ≠ depositContractAddress) :
    ∃ state out,
      processTransaction (controlBenv sender) BlockOutput.init controlTx 0 = .ok (state, out) ∧
      out.receiptKeys = [BLT.toBytes (.bytes (0 : Nat).toBytes)] ∧
      out.receiptsTrie[BLT.toBytes (.bytes (0 : Nat).toBytes)]? =
        some (makeReceipt controlTx none out.cumulativeGasUsed [logAt depositContractAddress]) ∧
      out.blockLogs = [logAt depositContractAddress] := by
  let benv := controlBenv sender
  have funds : (1048576 : B256) ≤ benv.state.bal sender := by
    change (1048576 : B256) ≤ ((controlState sender).get sender).bal
    rw [sender_get away]
    decide +kernel
  let debit := (benv.state.incrNonce sender).setBal sender (benv.state.bal sender - 1048576)
  have debited : (benv.state.incrNonce sender).subBal sender
      (controlTx.gas * 1 + transactionBlobGasFee benv controlTx).toB256 = some debit := by
    change (benv.state.incrNonce sender).subBal sender (1048576 : B256) = some debit
    exact subBal_incrNonce_of_le funds
  have image : debit.getCode depositContractAddress = shortCode := by
    rw [State.subBal_getCode debited]
    unfold State.getCode
    rw [State.incrNonce_get_code]
    exact logger_code sender
  let msg := callMessage { benv.beginTransaction with state := debit }
    (transactionTenv benv.beginTransaction controlTx 0 sender 1 21000 [])
    controlTx depositContractAddress
  have prepared : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction controlTx 0 sender 1 21000 []) controlTx =
      .ok msg := prepareMessage_call rfl
  obtain ⟨post, executed, state, logs, error, output, refund, deletions, gas⟩ :=
    logger_message (msg := msg) (control_covered sender) rfl image
      (by change 757 ≤ 2 ^ 20 - 21000; decide)
  have entry : msg.benvAfterTransfer = .ok msg.benv :=
    Msg.benvAfterTransfer_of_value_zero rfl
  have process : processMessage msg = .ok post :=
    processMessage_call_of_exec entry rfl (by
      apply propext
      change (Fork.ruleSet .prague).isPrecomp depositContractAddress ↔ ((false : Bool) = true)
      decide) executed error rfl
  have call := processMessageCall_call_of_message
    (msg := msg) (refund := 0) (control_covered sender).stateGas_none rfl rfl
    (by change getDelegatedCodeAddress (debit.getCode depositContractAddress) = none
        rw [image]; rfl) process error
    (by rw [refund]; rfl)
  obtain ⟨out, settled, cumulative, blockGas, keys, receipt, blockLogs⟩ :=
    processTransaction_of_stages_selected_receipts
      (benv := benv) (bout := BlockOutput.init) (tx := controlTx) (index := 0)
      (control_covered sender).stateGas_none (control_covered sender).bal_none
      (control_valid sender) (control_checked recovered away) debited prepared call rfl
  refine ⟨_, out, settled, keys, ?_, ?_⟩
  · simpa only [logs, show msg.currentTarget = depositContractAddress from rfl] using receipt
  · simpa only [logs, show msg.currentTarget = depositContractAddress from rfl,
      show BlockOutput.init.blockLogs = [] from rfl, List.nil_append] using blockLogs

private theorem malformed_data : extractDepositData [] =
    .error (.depositEventLayout (.text "invalid deposit event data length")) := by
  rfl

private theorem control_parser_error {out : BlockOutput}
    (keys : out.receiptKeys = [BLT.toBytes (.bytes (0 : Nat).toBytes)])
    (receipt : out.receiptsTrie[BLT.toBytes (.bytes (0 : Nat).toBytes)]? =
      some (makeReceipt controlTx none out.cumulativeGasUsed [logAt depositContractAddress])) :
    parseDepositRequests out =
      .error (.block (.depositEventLayout (.text "invalid deposit event data length"))) := by
  unfold parseDepositRequests
  dsimp only
  rw [keys, List.forIn_cons]
  simp only [receipt, Option.toExcept, bind, Except.bind, makeReceipt,
    List.forIn_cons, logAt, List.getElem?_cons_zero, and_self, ite_true,
    malformed_data, Except.mapError]

private theorem short_log_control_of {F : Fork → Prop} {benv : Benv}
    (fork : F benv.stat.fork)
    (installed : benv.state.getCode depositContractAddress = shortCode)
    (txRun : ∃ state out,
      processTransaction benv BlockOutput.init controlTx 0 = .ok (state, out) ∧
      out.receiptKeys = [BLT.toBytes (.bytes (0 : Nat).toBytes)] ∧
      out.receiptsTrie[BLT.toBytes (.bytes (0 : Nat).toBytes)]? =
        some (makeReceipt controlTx none out.cumulativeGasUsed [logAt depositContractAddress]) ∧
      out.blockLogs = [logAt depositContractAddress]) :
    Blanc.Corpus.Freeze.Deposit.ShortLogControl F := by
  obtain ⟨state, out, processed, keys, receipt, logs⟩ := txRun
  obtain ⟨rootSender, roots, head⟩ := exists_transactionRoots processed
  refine ⟨shortCode, benv, [controlTx], BlockOutput.init.bal,
    benv.withState state, out, [(rootSender, controlTx)], roots, [],
    fork, installed, ?_, ?_, ?_, ?_⟩
  · change TransactionsRoots [(0, controlTx)] benv BlockOutput.init
      (benv.withState state) out [(rootSender, controlTx)] roots
    simpa only [List.append_nil] using
      (TransactionsRoots.cons head (TransactionsRoots.nil _ _))
  · obtain ⟨withdrawalKeys, withdrawalTrie⟩ := withdrawalsPass_receipts
      benv.stat.rules (benv.withState state) out []
    intro key member
    rw [withdrawalKeys, keys] at member
    obtain rfl := List.mem_singleton.mp member
    rw [withdrawalTrie, receipt]
    rfl
  · refine ⟨logAt depositContractAddress, ?_, rfl, rfl, ?_,
      .text "invalid deposit event data length", malformed_data⟩
    · rw [logs]
      exact List.mem_singleton_self _
    · decide
  · refine ⟨.text "invalid deposit event data length", ?_⟩
    rw [parseDepositRequests_withdrawalsPass]
    exact control_parser_error keys receipt

/-- A closed actual indexed transaction with all receipts present reaches the
specific malformed-event guard of the real block parser. -/
theorem short_log_control : Blanc.Corpus.Freeze.Deposit.D1Control := by
  obtain ⟨sender, recovered, away⟩ := controlTx_sender
  exact short_log_control_of (control_covered sender) (logger_code sender)
    (control_transaction recovered away)

/-- Original Amsterdam message-call execution of `shortCode` (zero-value, non-static, away from
precompiles, no EIP-7702 authorizations): `processMessageCall` succeeds cleanly with
`[logAt msg.currentTarget]`, zero refund, and `msg.inheritedDeletions` preserved. -/
theorem logger_message_amsterdam {msg : Msg}
    (hfork : msg.benv.stat.fork = .amsterdam) (hauth : msg.tenv.stat.auths.isEmpty = true)
    (htarget : msg.target.isNone = false)
    (installed : msg.benv.state.getCode msg.currentTarget = shortCode)
    (hprecomp : ¬ amsterdamRules.isPrecomp msg.currentTarget)
    (nonstatic : msg.isStatic = false) (hvalue : msg.value = 0)
    (enough : 757 ≤ msg.gas) :
    ∃ post,
      processMessageCall msg = .ok (post.state, Lift.systemCallOutputA msg post) ∧
      post.state = msg.benv.state ∧ post.logs = [logAt msg.currentTarget] ∧
      post.error = none ∧ post.output = [] ∧ post.refundCounter = 0 ∧
      post.accountsToDelete = msg.inheritedDeletions ∧ post.gasLeft = msg.gas - 757 := by
  let post := loggerPost (Lift.userEntry msg msg.benv) msg.currentTarget (msg.gas - 757)
  have run := logger_run_any (sevm := Lift.userSevm msg shortCode msg.benv)
    (base := Lift.userEntry msg msg.benv) (gas := msg.gas - 757) nonstatic
  rw [Nat.sub_add_cancel enough] at run
  change Func.RunCompiled [] (Lift.userSevm msg shortCode msg.benv)
    (Lift.userEntry msg msg.benv) program post at run
  have executed := Func.exec_of_runCompiled_prefix (sfx := []) run
    (show program.NoCalls by trivial) program_compile (by
      change shortCode.toList = shortCode.toList ++ []
      rw [List.append_nil])
  have nonempty : shortCode.isEmpty = false := by
    simp only [ByteArray.isEmpty, shortCode_size]
    rfl
  have nondelegated : getDelegatedCodeAddress shortCode = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg]
    intro ⟨hsize, _⟩
    rw [shortCode_size] at hsize
    revert hsize
    decide
  have hbase : (Lift.userEntry msg msg.benv).error = none ∧
      (Lift.userEntry msg msg.benv).output = [] ∧
      (Lift.userEntry msg msg.benv).refundCounter = 0 ∧
      (Lift.userEntry msg msg.benv).accountsToDelete = msg.inheritedDeletions := by
    unfold Lift.userEntry Lift.systemCallBase Devm.balReadAccount
    dsimp only
    by_cases h : msg.benv.stat.rules.bal.isSome = true <;>
      simp only [h, ↓reduceIte] <;>
      exact ⟨rfl, rfl, rfl, rfl⟩
  have hlogs : post.logs = [logAt msg.currentTarget] := by
    simp only [post, loggerPost, Devm.setMach_logs, Devm.addLog_logs]
    have hbaseLogs : (Lift.userEntry msg msg.benv).logs = (initDevm msg).logs := by
      unfold Lift.userEntry Lift.systemCallBase Devm.balReadAccount
      dsimp only
      by_cases h : msg.benv.stat.rules.bal.isSome = true <;> simp only [h, ↓reduceIte] <;> rfl
    have hinitLogs : (initDevm msg).logs = [] := by
      have hsg := amsterdam_stateGas hfork
      show (match msg.benv.stat.rules.stateGas with
        | none => []
        | some _ => if msg.shouldTransferValue then (Devm.emitTransferLog _ _ _ _).logs else []) = _
      rw [hsg]
      by_cases h : msg.shouldTransferValue = true
      · simp only [h, ↓reduceIte, Devm.emitTransferLog, hvalue, or_true]
        rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [hbaseLogs, hinitLogs, List.nil_append]
  have hcall := Lift.processMessageCall_ok hfork hauth htarget installed nonempty nondelegated
    hprecomp (Msg.benvAfterTransfer_of_value_zero hvalue) executed hbase.1
    (by change 0 ≤ (Lift.userEntry msg msg.benv).refundCounter; rw [hbase.2.2.1]; decide)
  exact ⟨post, hcall, rfl, hlogs, hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2, rfl⟩

/-- Closed Amsterdam block environment installing `shortCode` at the deposit contract address. -/
def controlBenvA (sender : Adr) : Benv :=
  { state := controlState sender, createdAccounts := .emptyWithCapacity
    stat := { fork := .amsterdam, chainId := 1, origState := controlState sender
              blockGasLimit := 2 ^ 25, blockHashes := [], coinbase := 0, number := 0
              baseFeePerGas := 0, time := 0, prevRandao := 0, excessBlobGas := 0
              parentBeaconBlockRoot := 0 } }

theorem logger_code_amsterdam (sender : Adr) :
    (controlBenvA sender).state.getCode depositContractAddress = shortCode :=
  logger_code sender

/-- Full original Amsterdam settlement for the closed short-log control transaction. -/
theorem control_transaction_amsterdam {sender : Adr}
    (recovered : recoverSender 1 controlTx = .ok sender)
    (away : sender ≠ depositContractAddress) :
    ∃ state out,
      processTransaction (controlBenvA sender) BlockOutput.init controlTx 0 = .ok (state, out) ∧
      out.receiptKeys = [BLT.toBytes (.bytes (0 : Nat).toBytes)] ∧
      out.receiptsTrie[BLT.toBytes (.bytes (0 : Nat).toBytes)]? =
        some (makeReceipt controlTx none out.cumulativeGasUsed [logAt depositContractAddress]) ∧
      out.blockLogs = [logAt depositContractAddress] := by
  let benv := controlBenvA sender
  have hd : Lift.DirectTx benv BlockOutput.init controlTx sender depositContractAddress
      1 1 8 15000 15000 :=
    { fork := rfl
      type := rfl
      chain := rfl
      prioLe := by decide
      baseLe := by decide
      cost := by
        have hrules : benv.stat.rules = amsterdamRules := amsterdam_rules (s := benv.stat) rfl
        have hsg : amsterdamRules.stateGas = some amsterdamStateGasRules :=
          hrules.symm ▸ amsterdam_stateGas (s := benv.stat) rfl
        rw [hrules]
        unfold calculateIntrinsicCost
        simp only [controlTx, hsg]
        unfold TxType.receiver?
        dsimp only
        simp only [if_neg (Ne.symm away)]
        decide +kernel
      intrinsic := by decide
      floor := by decide
      budget := by decide
      room := by decide
      stateRoom := by decide
      recover := recovered
      nonce := by
        change ((controlState sender).get sender).nonce = 2
        rw [sender_get away]
        rfl
      nonceMax := by decide
      noCode := by
        change ((controlState sender).get sender).code.isEmpty = true
        rw [sender_get away]
        rfl
      funds := by
        change 2 ^ 20 * 8 + 0 ≤ ((controlState sender).get sender).bal.toNat
        rw [sender_get away]
        decide +kernel }
  obtain ⟨hvs, hvalid, hchecked, halloc, hdebit, hprepared⟩ := hd.stages 0
  let price := Lift.twoPrice benv.stat.baseFeePerGas 1 8
  let msg := Lift.txMsg benv controlTx 0 sender depositContractAddress price 15000
  have image : msg.benv.state.getCode msg.currentTarget = shortCode := by
    change (Lift.txDebit benv.state sender (controlTx.gas * price)).getCode depositContractAddress =
      shortCode
    rw [State.subBal_getCode hdebit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
    exact logger_code_amsterdam sender
  obtain ⟨mpost, hcall, _, hlogs, _, _, hrefund, hdel, _⟩ := logger_message_amsterdam
    (msg := msg) rfl rfl rfl image
    (by change ¬ amsterdamRules.isPrecomp depositContractAddress; decide)
    rfl rfl (by change 757 ≤ 2 ^ 20 - 15000; decide)
  obtain ⟨out, settled, _, _, _, blockLogs, keys, receipt, _⟩ :=
    Lift.processTransaction_amsterdam_of_stages (benv := benv) (bout := BlockOutput.init)
      (tx := controlTx) (index := 0) rfl hvs hvalid hchecked halloc hdebit hprepared hcall
      (show (Lift.systemCallOutputA msg mpost).refundCounter.toNat? = some 0 by
        change (mpost.refundCounter.toNat : Int).toNat? = some 0
        rw [hrefund]
        rfl)
      (show Std.HashSet.toList (Lift.systemCallOutputA msg mpost).accountsToDelete = [] by
        change mpost.accountsToDelete.toList = []
        rw [hdel]
        exact Std.HashSet.toList_emptyWithCapacity)
  refine ⟨_, out, settled, ?_, ?_, ?_⟩
  · simpa only [show BlockOutput.init.receiptKeys = [] from rfl, List.nil_append] using keys
  · simpa only [Lift.systemCallOutputA, hlogs,
      show msg.currentTarget = depositContractAddress from rfl] using receipt
  · simpa only [Lift.systemCallOutputA, hlogs,
      show msg.currentTarget = depositContractAddress from rfl,
      show BlockOutput.init.blockLogs = [] from rfl, List.nil_append] using blockLogs

/-- A closed actual indexed Amsterdam transaction with all receipts present reaches the
specific malformed-event guard of the real block parser (`D10Control`). -/
theorem d10_control : Blanc.Corpus.Freeze.Deposit.D10Control := by
  obtain ⟨sender, recovered, away⟩ := controlTx_sender
  exact short_log_control_of (F := (· = .amsterdam)) rfl (logger_code_amsterdam sender)
    (control_transaction_amsterdam recovered away)

end Blanc.Composition.DepositShortLogControl
