import Blanc.Lift.Weth9.ClosedKeys
import Blanc.Lift.Weth9.ClosedSigning
import Blanc.Lift.Weth9.ClosedDeployment
import Blanc.Lift.Weth9.ClosedBlock
import Blanc.ExecutionTraceSystemCode
import Blanc.DeploymentMessage
import Blanc.ExecutionTraceRootFrame

/-! Actual transaction and protocol-root projections for the one-deposit block. -/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Admission and actual preparation fix the deposit transaction's message metadata. -/
theorem deposit_transaction_message {benv : Benv} {bout : BlockOutput} {index : Nat}
    {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout depositTx index state bout')
    (chain : benv.stat.chainId = 1) :
    trace.msg.target = some contractAddress ∧ trace.msg.currentTarget = contractAddress ∧
      trace.msg.caller = senderE ∧
      trace.msg.data = depositTx.data ∧ trace.msg.tenv.stat.auths.isEmpty = true := by
  have recovered := checkTransaction_sender trace.checked
  change recoverSender benv.stat.chainId depositTx = .ok trace.sender at recovered
  rw [chain, depositTx_recoveredSender] at recovered
  have sender : trace.sender = senderE := (Except.ok.inj recovered).symm
  have prepared := prepareMessage_call
    (benv := { benv.beginTransaction with state := trace.debitState })
    (tenv := transactionTenv benv.beginTransaction depositTx index trace.sender
      trace.effectiveGasPrice trace.intrinsicGas trace.blobVersionedHashes)
    (tx := depositTx) (t := contractAddress) (by rfl)
  have msgEq := Except.ok.inj (trace.prepared.symm.trans prepared)
  rw [msgEq]
  simp only [callMessage, transactionTenv, sender, Tx.auths, depositTx, List.isEmpty_nil,
    and_self]

/-- The admitted deposit's actual retained roots consist of its one genuine holder frame. -/
theorem deposit_transaction_rawFrames {benv : Benv} {bout : BlockOutput} {index : Nat}
    {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout depositTx index state bout')
    (chain : benv.stat.chainId = 1) (after : Benv) {post : Devm}
    (enter : (Frame.ofCall trace.msg).enter = .run (initEvm (trace.msg.withBenv after)))
    (execution : exec (initEvm (trace.msg.withBenv after)) = .ok post)
    (installed : trace.msg.code = code) (fork : CoveredFork after.stat.fork)
    (nodeleg : getDelegatedCodeAddress trace.msg.code = none) :
    ∃ root, trace.rawFrames = [root] ∧ root.sevm.currentTarget = contractAddress ∧
      root.sevm.caller = senderE ∧ root.sevm.data = depositTx.data := by
  obtain ⟨target, currentTarget, caller, data, auths⟩ := deposit_transaction_message trace chain
  have entryData : (initEvm (trace.msg.withBenv after)).sta.data = depositTx.data := data
  obtain ⟨root, roots, rootEq⟩ := deposit_call_rawFrames trace.message
    (by rw [target]; rfl) auths nodeleg enter execution rfl installed fork
    (deposit_decodeCall entryData)
  refine ⟨root, roots, ?_⟩
  rw [rootEq]
  exact ⟨currentTarget, caller, data⟩

/-- A protocol root running the selected STOP program cannot enter WETH9. -/
theorem deposit_system_foreign {benv : Benv} {target : Adr} {data : Bytes}
    {state : Jaune.State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (foreign : target ≠ contractAddress)
    (installed : some (benv.state.getCode target).toList = Prog.compile deploymentSystemProgram) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget ≠ contractAddress := by
  have bytes : benv.state.getCode target = (⟨#[0x5b, 0x00]⟩ : ByteArray) := by
    have image : Prog.compile deploymentSystemProgram = some [0x5b, 0x00] := by
      decide +kernel
    rw [image] at installed
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj installed
  have reach : SpawnFreeReach (benv.state.getCode target) := by
    rw [bytes]
    exact spawnFreeReach_of_check (by decide +kernel)
  have nodeleg : ¬ isValidDelegation (benv.state.getCode target) := by
    rw [bytes]
    decide +kernel
  intro root member
  rw [trace.rawFrames_target_of_code reach nodeleg root member]
  exact foreign

/-- A one-deposit transaction fold keeps the raw root of its actual admitted head transaction. -/
theorem deposit_fold_rawFrames {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (txsEq : txs = [(0, depositTx)])
    (headRoot : ∀ txState txBout,
      ∀ head : TransactionTrace benv bout depositTx 0 txState txBout,
      ∃ root, head.rawFrames = [root] ∧ root.sevm.currentTarget = contractAddress ∧
        root.sevm.caller = senderE ∧ root.sevm.data = depositTx.data) :
    ∃ root, trace.rawFrames = [root] ∧ root.sevm.currentTarget = contractAddress ∧
      root.sevm.caller = senderE ∧ root.sevm.data = depositTx.data := by
  subst txs
  cases trace with
  | cons head tail =>
    cases tail with
    | nil =>
      simpa only [ApplyTransactionsTrace.rawFrames, List.append_nil] using headRoot _ _ head

/-- The actual body decoder fixes the configured block's nonempty transaction fold. -/
theorem deposit_body_decoded {benv : Benv} {state : Jaune.State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv [.inr depositTx] [] state bout) :
    trace.decodedTxs.putIndex = [(0, depositTx)] := by
  have decoded : trace.decodedTxs = [depositTx] := by
    have run := trace.decodeRun
    change Except.ok [depositTx] = Except.ok trace.decodedTxs at run
    exact (Except.ok.inj run).symm
  rw [decoded]
  rfl

/-- Every WETH entry of the actual body is its admitted deposit root; that root really occurs. -/
theorem deposit_body_roots {benv : Benv} {state : Jaune.State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv [.inr depositTx] [] state bout)
    {root : Exec.Deriv} (roots : trace.transactions.rawFrames = [root])
    (caller : root.sevm.caller = senderE) (data : root.sevm.data = depositTx.data)
    (beaconCode : some (benv.state.getCode beaconRootsAddress).toList =
      Prog.compile deploymentSystemProgram)
    (historyCode : some (trace.beaconState.getCode historyStorageAddress).toList =
      Prog.compile deploymentSystemProgram)
    (withdrawalCode : some
      ((processWithdrawalsState trace.transactionBenv.state []).getCode
        withdrawalRequestPredeployAddress).toList = Prog.compile deploymentSystemProgram)
    (consolidationCode : some
      (trace.requests.withdrawalState.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram) :
    (∀ visited ∈ trace.rawFrames, visited.sevm.currentTarget = contractAddress →
      visited.sevm.caller = senderE ∧ visited.sevm.data = depositTx.data) ∧
      root ∈ trace.rawFrames := by
  have beacon := deposit_system_foreign trace.beacon (by decide +kernel) beaconCode
  have history := deposit_system_foreign trace.history (by decide +kernel) historyCode
  have withdrawal := deposit_system_foreign trace.requests.withdrawal
    (by decide +kernel) withdrawalCode
  have consolidation := deposit_system_foreign trace.requests.consolidation
    (by decide +kernel) consolidationCode
  constructor
  · intro visited member target
    simp only [AppliedBodyTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append] at member
    rcases member with ((hb | hh) | ht) | (hw | hc)
    · exact (beacon visited hb target).elim
    · exact (history visited hh target).elim
    · rw [roots] at ht
      simp only [List.mem_singleton] at ht
      subst visited
      exact ⟨caller, data⟩
    · exact (withdrawal visited hw target).elim
    · exact (consolidation visited hc target).elim
  · simp only [AppliedBodyTrace.rawFrames, List.mem_append]
    left; right
    rw [roots]
    exact List.mem_cons_self

/-- Determinism fixes the actual one-deposit fold's terminal environment. -/
theorem deposit_fold_terminal {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (txsEq : txs = [(0, depositTx)]) {post : Jaune.State} {out : BlockOutput}
    (transaction : processTransaction benv bout depositTx 0 = .ok (post, out)) :
    finalBenv = benv.withState post ∧ finalBout = out := by
  subst txs
  cases trace with
  | cons head tail =>
    cases tail with
    | nil =>
      have same := Prod.mk.inj (Except.ok.inj (head.result.symm.trans transaction))
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨rfl, rfl⟩

/-- Actual system-call entry code follows from the retained body and the two settled worlds. -/
theorem deposit_body_system_codes {st post : Jaune.State} {txBout bodyBout : BlockOutput}
    (trace : AppliedBodyTrace (input st) [.inr depositTx] [] post bodyBout)
    (beforeCodes : SystemCodes st) (afterCodes : SystemCodes post)
    (transaction : processTransaction (input st) .init depositTx 0 = .ok (post, txBout)) :
    (some ((input st).state.getCode beaconRootsAddress).toList =
      Prog.compile deploymentSystemProgram) ∧
    (some (trace.beaconState.getCode historyStorageAddress).toList =
      Prog.compile deploymentSystemProgram) ∧
    (some ((processWithdrawalsState trace.transactionBenv.state []).getCode
      withdrawalRequestPredeployAddress).toList = Prog.compile deploymentSystemProgram) ∧
    (some (trace.requests.withdrawalState.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram) := by
  have codeBefore (a : Adr) (ha : a ∈ systemAddresses) :
      some (st.getCode a).toList = Prog.compile deploymentSystemProgram := by
    rw [beforeCodes a ha]
    exact systemCode_compile
  have codeAfter (a : Adr) (ha : a ∈ systemAddresses) :
      some (post.getCode a).toList = Prog.compile deploymentSystemProgram := by
    rw [afterCodes a ha]
    exact systemCode_compile
  obtain ⟨outBeacon, runBeacon, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (input st) beaconRootsAddress (input st).stat.parentBeaconBlockRoot.toBytes
    (codeBefore _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp beaconRootsAddress; decide +kernel) CoveredFork.bpo2
  have beaconEq : trace.beaconState = st :=
    (Prod.mk.inj (Except.ok.inj (trace.beacon.run.symm.trans runBeacon))).1
  obtain ⟨outHistory, runHistory, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (input st) historyStorageAddress trace.lastHash.toBytes
    (codeBefore _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp historyStorageAddress; decide +kernel) CoveredFork.bpo2
  have historyRun := trace.history.run
  rw [beaconEq] at historyRun
  have historyEq : trace.historyState = st :=
    (Prod.mk.inj (Except.ok.inj (historyRun.symm.trans runHistory))).1
  have headRun : processTransaction
      (((input st).withState trace.beaconState).withState trace.historyState)
      .init depositTx 0 = .ok (post, txBout) := by
    have same : (input st).withState st = input st := rfl
    simpa only [beaconEq, historyEq, same] using transaction
  have terminal := (deposit_fold_terminal trace.transactions (deposit_body_decoded trace) headRun).1
  have terminalEq : trace.transactionBenv = (input st).withState post := by
    simpa only [beaconEq, historyEq, Benv.withState] using terminal
  obtain ⟨outWithdrawal, runWithdrawal, -⟩ :=
    processUncheckedSystemTransaction_deploymentSystemProgram
      ((input st).withState post) withdrawalRequestPredeployAddress []
      (codeAfter _ (by decide +kernel))
      (by change ¬ Fork.bpo2.ruleSet.isPrecomp withdrawalRequestPredeployAddress; decide +kernel)
      CoveredFork.bpo2
  have withdrawalRun : processUncheckedSystemTransaction
      ((input st).withState post) withdrawalRequestPredeployAddress [] =
      .ok (trace.requests.withdrawalState, trace.requests.withdrawalOut) := by
    simpa only [terminalEq, processWithdrawalsState, List.foldl_nil, Benv.withState]
      using trace.requests.withdrawal.run
  have withdrawalEq : trace.requests.withdrawalState = post :=
    (Prod.mk.inj (Except.ok.inj (withdrawalRun.symm.trans runWithdrawal))).1
  refine ⟨codeBefore _ (by decide +kernel), ?_, ?_, ?_⟩
  · rw [beaconEq]
    exact codeBefore _ (by decide +kernel)
  · rw [terminalEq]
    exact codeAfter _ (by decide +kernel)
  · rw [withdrawalEq]
    exact codeAfter _ (by decide +kernel)

/-- A genuinely successful nondelegating deposit contributes a settled WETH frame. -/
theorem deposit_call_settledFrame {msg : Msg} {state : Jaune.State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (target : msg.target.isNone = false)
    (auths : msg.tenv.stat.auths.isEmpty = true)
    (nodeleg : getDelegatedCodeAddress msg.code = none) (after : Benv) {post : Devm}
    (enter : (Frame.ofCall msg).enter = .run (initEvm (msg.withBenv after)))
    (execution : exec (initEvm (msg.withBenv after)) = .ok post) (error : post.error = none)
    (currentTarget : msg.currentTarget = contractAddress) (caller : msg.caller = senderE)
    (data : msg.data = depositTx.data) (value : msg.value = amount) (static : msg.isStatic = false) :
    ∃ frame ∈ trace.settledFrames, frame.sevm.currentTarget = contractAddress ∧
      frame.sevm.isStatic = false ∧
      decodeCall frame.sevm = some (.deposit senderE amount) ∧ frame.out = .ok post := by
  cases trace with
  | createCollision htarget => simp only [target, Bool.false_eq_true] at htarget
  | createRun htarget => simp only [target, Bool.false_eq_true] at htarget
  | callRun htarget delegated refund hdelegation execMsg execMsgEq evm core coreTrace result =>
    have delegatedEq : delegated = msg := by
      unfold messageCallDelegation at hdelegation
      simp only [auths, ↓reduceIte] at hdelegation
      exact (Prod.mk.inj (Except.ok.inj hdelegation)).1.symm
    subst delegated
    have execEq : execMsg = msg := by
      rw [execMsgEq]
      simp only [messageCallExecutionMessage, nodeleg]
    change ∃ frame ∈ coreTrace.settledFrames, frame.sevm.currentTarget = contractAddress ∧
      frame.sevm.isStatic = false ∧
      decodeCall frame.sevm = some (.deposit senderE amount) ∧ frame.out = .ok post
    clear execMsgEq
    subst execMsg
    obtain ⟨frame, member, _, sevmEq, _, outcome⟩ :=
      coreTrace.root_mem_settledFrames enter execution error
    refine ⟨frame, member, ?_, ?_, ?_, outcome⟩
    · rw [sevmEq]
      exact currentTarget
    · rw [sevmEq]
      exact static
    · rw [sevmEq]
      change decodeCall (initSevm (msg.withBenv after)) = some (.deposit senderE amount)
      have decoded := deposit_decodeCall (sevm := initSevm (msg.withBenv after)) data
      change decodeCall (initSevm (msg.withBenv after)) =
        some (.deposit msg.caller msg.value) at decoded
      simpa only [caller, value] using decoded

/-- Actual preparation also fixes positive value and non-static execution. -/
theorem deposit_transaction_parameters {benv : Benv} {bout : BlockOutput} {index : Nat}
    {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout depositTx index state bout') :
    trace.msg.value = amount ∧ trace.msg.isStatic = false := by
  have prepared := prepareMessage_call
    (benv := { benv.beginTransaction with state := trace.debitState })
    (tenv := transactionTenv benv.beginTransaction depositTx index trace.sender
      trace.effectiveGasPrice trace.intrinsicGas trace.blobVersionedHashes)
    (tx := depositTx) (t := contractAddress) (by rfl)
  have msgEq := Except.ok.inj (trace.prepared.symm.trans prepared)
  rw [msgEq]
  exact ⟨rfl, rfl⟩

/-- Successful execution of the actual admitted message survives settlement. -/
theorem deposit_transaction_settledFrame {benv : Benv} {bout : BlockOutput} {index : Nat}
    {state : Jaune.State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout depositTx index state bout')
    (chain : benv.stat.chainId = 1) (after : Benv) {post : Devm}
    (enter : (Frame.ofCall trace.msg).enter = .run (initEvm (trace.msg.withBenv after)))
    (execution : exec (initEvm (trace.msg.withBenv after)) = .ok post)
    (error : post.error = none) (nodeleg : getDelegatedCodeAddress trace.msg.code = none) :
    ∃ frame ∈ trace.settledFrames, frame.sevm.currentTarget = contractAddress ∧
      frame.sevm.isStatic = false ∧
      decodeCall frame.sevm = some (.deposit senderE amount) ∧ frame.out = .ok post := by
  obtain ⟨target, currentTarget, caller, data, auths⟩ := deposit_transaction_message trace chain
  obtain ⟨value, static⟩ := deposit_transaction_parameters trace
  exact deposit_call_settledFrame trace.message (by rw [target]; rfl) auths nodeleg after
    enter execution error currentTarget caller data value static

/-- The singleton body's actual admitted head keeps its successful deposit frame. -/
theorem deposit_body_settledFrame {benv : Benv} {state : Jaune.State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv [.inr depositTx] [] state bout)
    (headFrame : ∀ txState txBout,
      ∀ head : TransactionTrace
        ((benv.withState trace.beaconState).withState trace.historyState)
        BlockOutput.init depositTx 0 txState txBout,
      ∃ frame ∈ head.settledFrames, frame.sevm.currentTarget = contractAddress ∧
        frame.sevm.isStatic = false ∧ decodeCall frame.sevm = some (.deposit senderE amount)) :
    ∃ frame ∈ trace.settledFrames, frame.sevm.currentTarget = contractAddress ∧
      frame.sevm.isStatic = false ∧ decodeCall frame.sevm = some (.deposit senderE amount) := by
  obtain ⟨_, _, head, retained⟩ := trace.transactions.single_head (deposit_body_decoded trace)
  obtain ⟨frame, member, facts⟩ := headFrame _ _ head
  refine ⟨frame, ?_, facts⟩
  simp only [AppliedBodyTrace.settledFrames, List.mem_append]
  left
  right
  exact retained frame member

/-- A genuine settled positive deposit is extracted as an actual committed invocation. -/
theorem deposit_history_committed {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {frame : Exec.Frame}
    (member : frame ∈ trace.settledFrames)
    (target : frame.sevm.currentTarget = contractAddress)
    (static : frame.sevm.isStatic = false)
    (decoded : decodeCall frame.sevm = some (.deposit senderE amount)) :
    ∃ inv ∈ committedInvocations contractAddress trace,
      decodeCall inv.sevm = some (.deposit senderE amount) := by
  refine ⟨frameInvocation frame, ?_, decoded⟩
  apply List.mem_flatMap.mpr
  refine ⟨frame, member, ?_⟩
  simp only [committedFrameInvocations, target, static, decoded, Option.isSome_some,
    and_self, ↓reduceIte, List.mem_singleton]

end Blanc.Lift.Weth9.ClosedInstance
