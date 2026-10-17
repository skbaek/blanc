import Blanc.Composition.UniswapV2PairWeth9BlockBody
import Blanc.ExecutionTraceSettledFrames

/-!
# The closed instance's configured history, parametric in the transactions' outcomes

`swap_history` (goal C6(b), block part): from any checkpoint state `st` (canonical, with
representable total ether, the STOP fixture at the four system addresses), if `signedTx1` runs as
the block's first transaction with outcome `(s1, bout1)` and `signedTx2` then runs with outcome
`(s2, bout2)`, with no deposit request, gas used within the limit and the fixture still in place
in `s2`, then the configured BPO2 block `swapBlock st s2 (requestsOutput bout2 [] [])` is a valid
state transition from `checkpoint st`, and a configured history from the checkpoint to the
post-block chain exists whose raw and settled frames are the system messages' frames (all at
system addresses) around exactly the frames of two transaction traces of those two runs.

The transactions' outcomes are hypotheses, so that the transaction units' results plug in.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.BlockForward Blanc.ExecutionTrace
open Blanc.Lift.Weth9.ClosedInstance (config config_valid config_forkAt checkpoint
  checkpoint_validContext input systemCode systemCode_compile SystemCodes systemAddresses)

/-- The retained body trace of a successful body run. -/
noncomputable def swapBodyTrace {st post : Jaune.State} {bout : BlockOutput}
    (body : applyBody (input st) swapTxs [] = .ok (post, bout)) :
    AppliedBodyTrace (input st) swapTxs [] post bout :=
  Classical.choice (exists_appliedBodyTrace body CoveredFork.bpo2)

/-- The configured block trace of the closed instance's block. -/
noncomputable def swapBlockTrace {st post : Jaune.State} {bout : BlockOutput}
    (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) swapTxs [] = .ok (post, bout)) :
    ConfiguredBlockTrace config (checkpoint st) (swapChain st post bout) where
  block := swapBlock st post bout
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
  transition := swapBlock_transition gas body
  bodyState := post
  blockOutput := bout
  bodyRun := body
  bodyTrace := swapBodyTrace body
  postEq := rfl

/-- The configured history: the checkpoint, then the closed instance's block. -/
noncomputable def swapHistory {st post : Jaune.State} {bout : BlockOutput}
    (canonical : st.Canonical) (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) swapTxs [] = .ok (post, bout)) :
    ConfiguredHistoryTrace config (checkpoint st) (swapChain st post bout) :=
  .step (.refl config_valid (checkpoint_validContext canonical) rfl) (swapBlockTrace bound gas body)

theorem mem_systemAddresses_beacon : beaconRootsAddress ∈ systemAddresses := by
  simp only [systemAddresses, List.mem_cons, true_or]

theorem mem_systemAddresses_history : historyStorageAddress ∈ systemAddresses := by
  simp only [systemAddresses, List.mem_cons, true_or, or_true]

theorem mem_systemAddresses_withdrawal : withdrawalRequestPredeployAddress ∈ systemAddresses := by
  simp only [systemAddresses, List.mem_cons, true_or, or_true]

theorem mem_systemAddresses_consolidation :
    consolidationRequestPredeployAddress ∈ systemAddresses := by
  simp only [systemAddresses, List.mem_cons, true_or, or_true]

/-- **The history's frames are the two transactions' frames between system frames.** -/
theorem swapHistory_frames {st s1 s2 : Jaune.State} {bout1 bout2 bout : BlockOutput}
    (canonical : st.Canonical) (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (beforeCodes : SystemCodes st) (afterCodes : SystemCodes s2)
    (run1 : processTransaction (input st) BlockOutput.init signedTx1 0 = .ok (s1, bout1))
    (run2 : processTransaction ((input st).withState s1) bout1 signedTx2 1 = .ok (s2, bout2))
    (body : applyBody (input st) swapTxs [] = .ok (s2, bout)) :
    ∃ (t1 : TransactionTrace (input st) BlockOutput.init signedTx1 0 s1 bout1)
      (t2 : TransactionTrace ((input st).withState s1) bout1 signedTx2 1 s2 bout2)
      (sysRaw sysRaw' : List Exec.Deriv) (sysSet sysSet' : List Exec.Frame),
      (swapHistory canonical bound gas body).rawFrames =
        sysRaw ++ t1.rawFrames ++ t2.rawFrames ++ sysRaw' ∧
      (swapHistory canonical bound gas body).settledFrames =
        sysSet ++ t1.settledFrames ++ t2.settledFrames ++ sysSet' ∧
      (∀ root ∈ sysRaw ++ sysRaw', root.sevm.currentTarget ∈ systemAddresses) ∧
      (∀ f ∈ sysSet ++ sysSet', f.sevm.currentTarget ∈ systemAddresses) := by
  let tr := swapBodyTrace body
  have codeBefore (a : Adr) (ha : a ∈ systemAddresses) :
      some ((input st).state.getCode a).toList = Prog.compile deploymentSystemProgram := by
    change some (st.getCode a).toList = _
    rw [beforeCodes a ha]
    exact systemCode_compile
  -- the two opening system messages change no state
  have beaconState : tr.beaconState = st := by
    obtain ⟨_, run, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
      (input st) beaconRootsAddress (input st).stat.parentBeaconBlockRoot.toBytes
      (codeBefore _ mem_systemAddresses_beacon)
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
          exact codeBefore _ mem_systemAddresses_history)
      (by change ¬ Fork.bpo2.ruleSet.isPrecomp historyStorageAddress; decide +kernel)
      CoveredFork.bpo2
    have e := tr.history.run.symm.trans run
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    exact e.1.trans beaconState
  have hB : ((input st).withState tr.beaconState).withState tr.historyState = input st := by
    rw [beaconState, historyState]
    rfl
  have decoded : tr.decodedTxs.putIndex = [(0, signedTx1), (1, signedTx2)] := by
    have run := tr.decodeRun
    change Except.ok [signedTx1, signedTx2] = Except.ok tr.decodedTxs at run
    rw [← Except.ok.inj run]
    rfl
  obtain ⟨t1, t2, raw, settled, final⟩ := fold_two tr.transactions hB decoded run1 run2
  -- the opening system messages' frames
  obtain ⟨beaconRaw, beaconSet⟩ := stop_frames tr.beacon
    (by change st.getCode _ = _; exact beforeCodes _ mem_systemAddresses_beacon)
  obtain ⟨historyRaw, historySet⟩ := stop_frames tr.history
    (by change tr.beaconState.getCode _ = _
        rw [beaconState]
        exact beforeCodes _ mem_systemAddresses_history)
  -- the request messages' frames
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
          rw [requestCode _ mem_systemAddresses_withdrawal]
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
  obtain ⟨withdrawalRaw, withdrawalSet⟩ := stop_frames tr.requests.withdrawal
    (by change (processWithdrawalsState tr.transactionBenv.state []).getCode _ = _
        exact requestCode _ mem_systemAddresses_withdrawal)
  obtain ⟨consolidationRaw, consolidationSet⟩ := stop_frames tr.requests.consolidation
    (by change tr.requests.withdrawalState.getCode _ = _
        rw [withdrawalState]
        exact requestCode _ mem_systemAddresses_consolidation)
  refine ⟨t1, t2, tr.beacon.rawFrames ++ tr.history.rawFrames, tr.requests.rawFrames,
    tr.beacon.settledFrames ++ tr.history.settledFrames, tr.requests.settledFrames,
    ?_, ?_, ?_, ?_⟩
  · change [] ++ (tr.beacon.rawFrames ++ tr.history.rawFrames ++ tr.transactions.rawFrames ++
      tr.requests.rawFrames) = _
    rw [raw]
    simp only [List.nil_append, List.append_assoc]
  · change [] ++ (tr.beacon.settledFrames ++ tr.history.settledFrames ++
      tr.transactions.settledFrames ++ tr.requests.settledFrames) = _
    rw [settled]
    simp only [List.nil_append, List.append_assoc]
  · intro root member
    simp only [RequestsTrace.rawFrames, List.mem_append] at member
    rcases member with (member | member) | member | member
    · rw [beaconRaw root member]; exact mem_systemAddresses_beacon
    · rw [historyRaw root member]; exact mem_systemAddresses_history
    · rw [withdrawalRaw root member]; exact mem_systemAddresses_withdrawal
    · rw [consolidationRaw root member]; exact mem_systemAddresses_consolidation
  · intro f member
    simp only [RequestsTrace.settledFrames, List.mem_append] at member
    rcases member with (member | member) | member | member
    · rw [beaconSet f member]; exact mem_systemAddresses_beacon
    · rw [historySet f member]; exact mem_systemAddresses_history
    · rw [withdrawalSet f member]; exact mem_systemAddresses_withdrawal
    · rw [consolidationSet f member]; exact mem_systemAddresses_consolidation

/-- **C6(b), block part: two signed transactions in one configured BPO2 block.**  From any
checkpoint state `st` (canonical, representable total ether, the STOP fixture at the system
addresses), if `signedTx1` runs first with outcome `(s1, bout1)` and `signedTx2` then runs with
outcome `(s2, bout2)` creating no deposit request, within the block gas limit, and `s2` keeps the
fixture, then `swapBlock st s2 (requestsOutput bout2 [] [])` is a valid configured state
transition from `checkpoint st`, and a configured history from the checkpoint to the post-block
chain exists whose raw and settled frames are those of two transaction traces of exactly these
runs, between frames at system addresses. -/
theorem swap_history {st s1 s2 : Jaune.State} {bout1 bout2 : BlockOutput}
    (canonical : st.Canonical) (bound : SumNof st.bal)
    (beforeCodes : SystemCodes st) (afterCodes : SystemCodes s2)
    (run1 : processTransaction (input st) BlockOutput.init signedTx1 0 = .ok (s1, bout1))
    (run2 : processTransaction ((input st).withState s1) bout1 signedTx2 1 = .ok (s2, bout2))
    (requests : parseDepositRequests bout2 = .ok [])
    (gas : bout2.blockGasUsed ≤ 1000000) :
    stateTransitionUsing config (checkpoint st) (swapBlock st s2 (requestsOutput bout2 [] [])) =
      .ok (swapChain st s2 (requestsOutput bout2 [] [])) ∧
    ∃ (trace : ConfiguredHistoryTrace config (checkpoint st)
        (swapChain st s2 (requestsOutput bout2 [] [])))
      (t1 : TransactionTrace (input st) BlockOutput.init signedTx1 0 s1 bout1)
      (t2 : TransactionTrace ((input st).withState s1) bout1 signedTx2 1 s2 bout2)
      (sysRaw sysRaw' : List Exec.Deriv) (sysSet sysSet' : List Exec.Frame),
      trace.rawFrames = sysRaw ++ t1.rawFrames ++ t2.rawFrames ++ sysRaw' ∧
      trace.settledFrames = sysSet ++ t1.settledFrames ++ t2.settledFrames ++ sysSet' ∧
      (∀ root ∈ sysRaw ++ sysRaw', root.sevm.currentTarget ∈ systemAddresses) ∧
      (∀ f ∈ sysSet ++ sysSet', f.sevm.currentTarget ∈ systemAddresses) := by
  have body := swap_body_of_transactions beforeCodes afterCodes run1 run2 requests
  have gas' : (requestsOutput bout2 [] []).blockGasUsed ≤ 1000000 := gas
  obtain ⟨t1, t2, sysRaw, sysRaw', sysSet, sysSet', frames⟩ :=
    swapHistory_frames canonical bound gas' beforeCodes afterCodes run1 run2 body
  exact ⟨swapBlock_transition gas' body,
    swapHistory canonical bound gas' body, t1, t2, sysRaw, sysRaw', sysSet, sysSet', frames⟩

end Blanc.Composition.UniswapV2PairWeth9Instance
