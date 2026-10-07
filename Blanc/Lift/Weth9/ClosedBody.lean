import Blanc.Lift.Weth9.ClosedDeployment
import Blanc.Lift.Weth9.ClosedBlock

/-! The real configured body, assembled from its admitted deposit and the
four mandatory system calls. The STOP system fixture preserves every account. -/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.BlockForward

/-- The checkpoint retains the entire actual settled deployment state. -/
noncomputable def deploymentCheckpoint : BlockChain := checkpoint deploymentPost.state

theorem deployment_checkpoint_connection :
    deploymentCheckpoint.state = deploymentPost.state := rfl

theorem deploymentCheckpoint_valid : deploymentCheckpoint.ValidContext :=
  checkpoint_validContext deployment_canonical

theorem deploymentCheckpoint_sumNof : SumNof deploymentCheckpoint.state.bal :=
  deployment_sumNof

/-- System processing connects the actual transaction settlement to the
body result, without installing or replacing any storage or balance. -/
theorem deposit_body_of_transaction {st post : Jaune.State} {bout : BlockOutput}
    (beforeCodes : SystemCodes st) (afterCodes : SystemCodes post)
    (transaction : processTransaction (input st) BlockOutput.init depositTx 0 = .ok (post, bout))
    (requests : parseDepositRequests bout = .ok []) :
    ∃ bodyBout, applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bodyBout) ∧
      bodyBout.blockGasUsed = bout.blockGasUsed := by
  have codeBefore (a : Adr) (ha : a ∈ systemAddresses) :
      some ((input st).state.getCode a).toList = Prog.compile deploymentSystemProgram := by
    change some (st.getCode a).toList = _
    rw [beforeCodes a ha]
    exact systemCode_compile
  have codeAfter (a : Adr) (ha : a ∈ systemAddresses) :
      some (((input st).withState post).state.getCode a).toList = Prog.compile deploymentSystemProgram := by
    change some (post.getCode a).toList = _
    rw [afterCodes a ha]
    exact systemCode_compile
  obtain ⟨outBeacon, beacon, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (input st) beaconRootsAddress (input st).stat.parentBeaconBlockRoot.toBytes
    (codeBefore _ (by decide +kernel)) (by change ¬ Fork.bpo2.ruleSet.isPrecomp beaconRootsAddress; decide +kernel) CoveredFork.bpo2
  obtain ⟨outHistory, history, -⟩ := processUncheckedSystemTransaction_deploymentSystemProgram
    (input st) historyStorageAddress (checkpointHeader st).hash.toBytes
    (codeBefore _ (by decide +kernel)) (by change ¬ Fork.bpo2.ruleSet.isPrecomp historyStorageAddress; decide +kernel) CoveredFork.bpo2
  obtain ⟨outW, runW, _, _, _, _, returnW⟩ := processCheckedSystemTransaction_deploymentSystemProgram
    ((input st).withState post) withdrawalRequestPredeployAddress []
    (codeAfter _ (by decide +kernel)) (by change ¬ Fork.bpo2.ruleSet.isPrecomp withdrawalRequestPredeployAddress; decide +kernel) CoveredFork.bpo2
  obtain ⟨outC, runC, _, _, _, _, returnC⟩ := processCheckedSystemTransaction_deploymentSystemProgram
    ((input st).withState post) consolidationRequestPredeployAddress []
    (codeAfter _ (by decide +kernel)) (by change ¬ Fork.bpo2.ruleSet.isPrecomp consolidationRequestPredeployAddress; decide +kernel) CoveredFork.bpo2
  have fold : applyTransactions [depositTx].putIndex (input st) BlockOutput.init =
      .ok ((input st).withState post, bout) := by
    change applyTransactions [(0, depositTx)] (input st) BlockOutput.init = _
    unfold applyTransactions
    rw [transaction]
    rfl
  have same : (input st).withState (input st).state = input st := rfl
  have samePost : ((input st).withState post).withState ((input st).withState post).state =
      (input st).withState post := rfl
  have body := applyBody_forward (txs := [Sum.inr depositTx]) (stHistory := (input st).state)
    CoveredFork.bpo2 beacon (input_lastHash st)
    (by rw [same]; exact history) (txList := [depositTx]) rfl
    (by rw [same, same]; exact fold) requests runW (by rw [samePost]; exact runC)
  rw [returnW, returnC] at body
  exact ⟨requestsOutput bout [] [], body, rfl⟩

end Blanc.Lift.Weth9.ClosedInstance
