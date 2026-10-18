import Blanc.Composition.Curve3Pool3CrvTxData
import Blanc.Lift.Weth9.ClosedBlock
import Blanc.Lift.Weth9.ClosedDeployment
import Blanc.ExecutionTraceSettledFrames
import Blanc.ExecutionTraceSystemCode
import Blanc.DeploymentMessage

/-!
# U9(b): one signed transaction in one configured BPO2 block

The closed block of U9(b) reuses the configured chain envelope of the WETH9 closed witness
(`Weth9.ClosedInstance`: the BPO2-from-genesis `config`, the checkpoint `checkpoint st` carrying the
supplied state unchanged, the execution header template) with a one-transaction body.  Everything
here is stated for an arbitrary transaction `tx`, run as the block's only transaction:

* `oneTxBlock tx st post bout`, `oneTxChain`: the block committing to the body result;
* `oneTx_body`: the body runs when the transaction runs and the four system addresses hold the
  STOP fixture before and after it (the system messages change no state);
* `oneTx_history`: the configured history from the checkpoint to the post-block chain, whose raw
  frames are those of one transaction trace of exactly that run, between frames at the system
  addresses.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.BlockForward Blanc.ExecutionTrace
open Blanc.Lift.Weth9.ClosedInstance (config config_valid config_forkAt checkpoint checkpointBlock
  checkpointHeader checkpoint_validContext executionHeader input input_lastHash depositBlock_header
  depositBlock_input systemCode systemCode_compile SystemCodes systemAddresses)

/-- **The closed block** after `checkpoint st`, carrying the one transaction `tx` and committing to
the body result `(post, bout)`. -/
def oneTxBlock (tx : Tx) (st post : Jaune.State) (bout : BlockOutput) : Block :=
  { header := commitHeader Fork.bpo2.ruleSet (checkpointBlock st) (executionHeader st) post bout
    txs := [.inr tx]
    wds := []
    ommers := [] }

/-- The chain after the block. -/
def oneTxChain (tx : Tx) (st post : Jaune.State) (bout : BlockOutput) : BlockChain :=
  ⟨appendBlock (checkpoint st).blocks (oneTxBlock tx st post bout), post, 1⟩

/-- **The block's state transition** succeeds from any successful body run within the gas
limit. -/
theorem oneTx_transition {tx : Tx} {st post : Jaune.State} {bout : BlockOutput}
    (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) [.inr tx] [] = .ok (post, bout)) :
    stateTransitionUsing config (checkpoint st) (oneTxBlock tx st post bout) =
      .ok (oneTxChain tx st post bout) := by
  have body' : applyBody
      (initBenv .bpo2 (checkpoint st) (oneTxBlock tx st post bout).header)
      (oneTxBlock tx st post bout).txs (oneTxBlock tx st post bout).wds = .ok (post, bout) := by
    rw [show initBenv .bpo2 (checkpoint st) (oneTxBlock tx st post bout).header = input st from
      depositBlock_input st post bout]
    exact body
  exact stateTransitionUsing_forward rfl (config_forkAt _) CoveredFork.bpo2
    (depositBlock_header (post := post) gas) rfl body' rfl rfl rfl rfl rfl rfl rfl rfl

/-- **The body from its one transaction**, the STOP fixture at the system addresses before and
after it. -/
theorem oneTx_body {tx : Tx} {st post : Jaune.State} {bout : BlockOutput}
    (beforeCodes : SystemCodes st) (afterCodes : SystemCodes post)
    (run : processTransaction (input st) BlockOutput.init tx 0 = .ok (post, bout))
    (requests : parseDepositRequests bout = .ok []) :
    applyBody (input st) [.inr tx] [] = .ok (post, requestsOutput bout [] []) := by
  have codeBefore (a : Adr) (ha : a ∈ systemAddresses) :
      some ((input st).state.getCode a).toList = Prog.compile deploymentSystemProgram := by
    change some (st.getCode a).toList = _
    rw [beforeCodes a ha]
    exact systemCode_compile
  have codeAfter (a : Adr) (ha : a ∈ systemAddresses) :
      some (((input st).withState post).state.getCode a).toList =
        Prog.compile deploymentSystemProgram := by
    change some (post.getCode a).toList = _
    rw [afterCodes a ha]
    exact systemCode_compile
  obtain ⟨_outB, beacon, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (input st) beaconRootsAddress (input st).stat.parentBeaconBlockRoot.toBytes
    (codeBefore _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp beaconRootsAddress; decide +kernel) CoveredFork.bpo2
  obtain ⟨_outH, history, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (input st) historyStorageAddress (checkpointHeader st).hash.toBytes
    (codeBefore _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp historyStorageAddress; decide +kernel)
    CoveredFork.bpo2
  obtain ⟨_outW, runW, _, _, _, _, returnW⟩ := processCheckedSystemTransaction_deploymentSystemProgram
    ((input st).withState post) withdrawalRequestPredeployAddress []
    (codeAfter _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp withdrawalRequestPredeployAddress; decide +kernel)
    CoveredFork.bpo2
  obtain ⟨_outC, runC, _, _, _, _, returnC⟩ := processCheckedSystemTransaction_deploymentSystemProgram
    ((input st).withState post) consolidationRequestPredeployAddress []
    (codeAfter _ (by decide +kernel))
    (by change ¬ Fork.bpo2.ruleSet.isPrecomp consolidationRequestPredeployAddress; decide +kernel)
    CoveredFork.bpo2
  have fold : applyTransactions [tx].putIndex (input st) BlockOutput.init =
      .ok ((input st).withState post, bout) := by
    change applyTransactions [(0, tx)] (input st) BlockOutput.init = _
    simp only [applyTransactions, run, bind, Except.bind]
  have same : (input st).withState (input st).state = input st := rfl
  have samePost : ((input st).withState post).withState ((input st).withState post).state =
      (input st).withState post := rfl
  have body := applyBody_forward (txs := [.inr tx]) (stHistory := (input st).state)
    CoveredFork.bpo2 beacon (input_lastHash st)
    (by rw [same]; exact history) (txList := [tx]) rfl
    (by rw [same, same]; exact fold) requests runW (by rw [samePost]; exact runC)
  rw [returnW, returnC] at body
  exact body

/-- The retained body trace of a successful body run. -/
noncomputable def oneTxBodyTrace {tx : Tx} {st post : Jaune.State} {bout : BlockOutput}
    (body : applyBody (input st) [.inr tx] [] = .ok (post, bout)) :
    AppliedBodyTrace (input st) [.inr tx] [] post bout :=
  Classical.choice (exists_appliedBodyTrace body CoveredFork.bpo2)

/-- The configured block trace of the closed block. -/
noncomputable def oneTxBlockTrace {tx : Tx} {st post : Jaune.State} {bout : BlockOutput}
    (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) [.inr tx] [] = .ok (post, bout)) :
    ConfiguredBlockTrace config (checkpoint st) (oneTxChain tx st post bout) where
  block := oneTxBlock tx st post bout
  bound := by
    change sum st.bal + 0 < 2 ^ 256
    rw [Nat.add_zero]
    exact bound
  fork := .bpo2
  forkAt := config_forkAt _
  rules := Fork.bpo2.ruleSet
  rulesEq := rfl
  rulesAt := by
    unfold ChainConfig.rulesAt
    rw [config_forkAt]
    rfl
  covered := CoveredFork.bpo2
  transition := oneTx_transition gas body
  bodyState := post
  blockOutput := bout
  bodyRun := body
  bodyTrace := oneTxBodyTrace body
  postEq := rfl

/-- The configured history: the checkpoint, then the closed block. -/
noncomputable def oneTxHistory {tx : Tx} {st post : Jaune.State} {bout : BlockOutput}
    (canonical : st.Canonical) (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) [.inr tx] [] = .ok (post, bout)) :
    ConfiguredHistoryTrace config (checkpoint st) (oneTxChain tx st post bout) :=
  .step (.refl config_valid (checkpoint_validContext canonical) rfl) (oneTxBlockTrace bound gas body)

/-- A system message to a STOP fixture enters only frames at its target. -/
theorem oneTx_systemRaw {benv : Benv} {target : Adr} {data : Bytes} {state : Jaune.State}
    {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out)
    (code : benv.state.getCode target = systemCode) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = target :=
  trace.rawFrames_target_of_code (by rw [code]; exact spawnFreeReach_of_check (by decide +kernel))
    (by rw [code]; decide +kernel)

/-- **A one-transaction fold is its transaction.** -/
theorem oneTx_fold {txs : List (Nat × Tx)} {B B0 finalB : Benv} {finalBout : BlockOutput}
    (t : ApplyTransactionsTrace txs B BlockOutput.init finalB finalBout) (hB : B = B0) {tx : Tx}
    {s1 : Jaune.State} {bout1 : BlockOutput} (htxs : txs = [(0, tx)])
    (run : processTransaction B0 BlockOutput.init tx 0 = .ok (s1, bout1)) :
    ∃ t1 : TransactionTrace B0 BlockOutput.init tx 0 s1 bout1,
      t.rawFrames = t1.rawFrames ∧ t.settledFrames = t1.settledFrames ∧ finalB.state = s1 := by
  subst hB htxs
  cases t with
  | cons head tail =>
    have e1 := head.result.symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    cases tail with
    | nil =>
      exact ⟨head, by simp only [ApplyTransactionsTrace.rawFrames, List.append_nil],
        by simp only [ApplyTransactionsTrace.settledFrames, List.append_nil], rfl⟩

/-- **The closed block in a configured history** (see the module note).  From any canonical
checkpoint state with representable total ether and the STOP fixture at the system addresses, a run
of `tx` as the block's only transaction creating no deposit request, within the gas limit and
keeping the fixture, gives a valid configured state transition and a configured history whose raw
frames are one transaction trace's of exactly that run, between frames at system addresses. -/
theorem oneTx_history {tx : Tx} {st s1 : Jaune.State} {bout1 : BlockOutput}
    (canonical : st.Canonical) (bound : SumNof st.bal)
    (beforeCodes : SystemCodes st) (afterCodes : SystemCodes s1)
    (run : processTransaction (input st) BlockOutput.init tx 0 = .ok (s1, bout1))
    (requests : parseDepositRequests bout1 = .ok [])
    (gas : bout1.blockGasUsed ≤ 1000000) :
    stateTransitionUsing config (checkpoint st) (oneTxBlock tx st s1 (requestsOutput bout1 [] [])) =
      .ok (oneTxChain tx st s1 (requestsOutput bout1 [] [])) ∧
    ∃ (trace : ConfiguredHistoryTrace config (checkpoint st)
        (oneTxChain tx st s1 (requestsOutput bout1 [] [])))
      (t1 : TransactionTrace (input st) BlockOutput.init tx 0 s1 bout1)
      (sysRaw sysRaw' : List Exec.Deriv),
      trace.rawFrames = sysRaw ++ t1.rawFrames ++ sysRaw' ∧
      trace.systemRawFrames = sysRaw ++ sysRaw' ∧
      (tx.auths = [] → ∀ a, trace.NoAuthorityAt a) ∧
      (∀ root ∈ sysRaw ++ sysRaw', root.sevm.currentTarget ∈ systemAddresses) ∧
      ∀ f ∈ t1.settledFrames, f ∈ trace.settledFrames := by
  have body := oneTx_body beforeCodes afterCodes run requests
  have gas' : (requestsOutput bout1 [] []).blockGasUsed ≤ 1000000 := gas
  refine ⟨oneTx_transition gas' body, oneTxHistory canonical bound gas' body, ?_⟩
  let tr := oneTxBodyTrace body
  have codeBefore (a : Adr) (ha : a ∈ systemAddresses) :
      some ((input st).state.getCode a).toList = Prog.compile deploymentSystemProgram := by
    change some (st.getCode a).toList = _
    rw [beforeCodes a ha]
    exact systemCode_compile
  have beaconState : tr.beaconState = st := by
    obtain ⟨_, run, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
      (input st) beaconRootsAddress (input st).stat.parentBeaconBlockRoot.toBytes
      (codeBefore _ (by decide +kernel))
      (by change ¬ Fork.bpo2.ruleSet.isPrecomp beaconRootsAddress; decide +kernel)
      CoveredFork.bpo2
    have e := tr.beacon.run.symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    exact e.1
  have historyState : tr.historyState = st := by
    obtain ⟨_, run, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
      ((input st).withState tr.beaconState) historyStorageAddress tr.lastHash.toBytes
      (by change some (tr.beaconState.getCode historyStorageAddress).toList = _
          rw [beaconState]
          exact codeBefore _ (by decide +kernel))
      (by change ¬ Fork.bpo2.ruleSet.isPrecomp historyStorageAddress; decide +kernel)
      CoveredFork.bpo2
    have e := tr.history.run.symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    exact e.1.trans beaconState
  have hB : ((input st).withState tr.beaconState).withState tr.historyState = input st := by
    rw [beaconState, historyState]
    rfl
  have decoded : tr.decodedTxs.putIndex = [(0, tx)] := by
    have run := tr.decodeRun
    change Except.ok [tx] = Except.ok tr.decodedTxs at run
    rw [← Except.ok.inj run]
    rfl
  obtain ⟨t1, raw, settled, final⟩ := oneTx_fold tr.transactions hB decoded run
  have requestCode (a : Adr) (ha : a ∈ systemAddresses) :
      (processWithdrawalsState tr.transactionBenv.state []).getCode a = systemCode := by
    rw [processWithdrawalsState_getCode, final]
    exact afterCodes a ha
  have withdrawalState : tr.requests.withdrawalState =
      processWithdrawalsState tr.transactionBenv.state [] := by
    obtain ⟨_, run, -⟩ := processCheckedSystemTransaction_deploymentSystemProgram
      (tr.transactionBenv.withState (processWithdrawalsState tr.transactionBenv.state []))
      withdrawalRequestPredeployAddress []
      (by change some ((processWithdrawalsState tr.transactionBenv.state []).getCode
              withdrawalRequestPredeployAddress).toList = _
          rw [requestCode _ (by decide +kernel)]
          exact systemCode_compile)
      (by change ¬ (Fork.ruleSet tr.transactionBenv.stat.fork).isPrecomp
              withdrawalRequestPredeployAddress
          rw [tr.transactions.stat_eq]
          change ¬ Fork.bpo2.ruleSet.isPrecomp withdrawalRequestPredeployAddress
          decide +kernel)
      (by change CoveredFork tr.transactionBenv.stat.fork
          rw [tr.transactions.stat_eq]
          exact CoveredFork.bpo2)
    have e := tr.requests.withdrawalRun.symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    exact e.1
  have beaconRaw := oneTx_systemRaw tr.beacon
    (by change st.getCode _ = _; exact beforeCodes _ (by decide +kernel))
  have historyRaw := oneTx_systemRaw tr.history
    (by change tr.beaconState.getCode _ = _
        rw [beaconState]
        exact beforeCodes _ (by decide +kernel))
  have withdrawalRaw := oneTx_systemRaw tr.requests.withdrawal
    (by change (processWithdrawalsState tr.transactionBenv.state []).getCode _ = _
        exact requestCode _ (by decide +kernel))
  have consolidationRaw := oneTx_systemRaw tr.requests.consolidation
    (by change tr.requests.withdrawalState.getCode _ = _
        rw [withdrawalState]
        exact requestCode _ (by decide +kernel))
  refine ⟨t1, tr.beacon.rawFrames ++ tr.history.rawFrames, tr.requests.rawFrames, ?_, ?_,
    fun hauth a => ⟨trivial, fun p hp auth hauthm => ?_⟩, ?_, fun f hf => ?_⟩
  · change [] ++ (tr.beacon.rawFrames ++ tr.history.rawFrames ++ tr.transactions.rawFrames ++
      tr.requests.rawFrames) = _
    rw [raw]
    simp only [List.nil_append]
  · change [] ++ (tr.beacon.rawFrames ++ tr.history.rawFrames ++ tr.requests.rawFrames) = _
    simp only [List.nil_append]
  · change p ∈ tr.decodedTxs.putIndex at hp
    rw [decoded, List.mem_singleton] at hp
    subst hp
    rw [hauth] at hauthm
    cases hauthm
  · intro root member
    simp only [RequestsTrace.rawFrames, List.mem_append] at member
    rcases member with (member | member) | member | member
    · rw [beaconRaw root member]; decide +kernel
    · rw [historyRaw root member]; decide +kernel
    · rw [withdrawalRaw root member]; decide +kernel
    · rw [consolidationRaw root member]; decide +kernel
  · change f ∈ [] ++ (tr.beacon.settledFrames ++ tr.history.settledFrames ++
      tr.transactions.settledFrames ++ tr.requests.settledFrames)
    rw [settled]
    simp only [List.nil_append, List.mem_append]
    exact .inl (.inr hf)

end Blanc.Composition.Curve3Pool3CrvInstance
