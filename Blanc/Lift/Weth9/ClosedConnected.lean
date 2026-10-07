import Blanc.Lift.Weth9.ClosedDepositTx
import Blanc.Lift.Weth9.ClosedDepositTxEffects
import Blanc.Lift.Weth9.ClosedDepositStart
import Blanc.Lift.Weth9.ClosedHistoryCore

/-!
One connected deployment and configured positive-deposit history. The
named settlement expression below is justified by the actual admitted
transaction equation; no storage slot is credited as an input assumption.
-/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.ExecutionTrace

noncomputable def depositedState : Jaune.State := depositSettledState deploymentPost.state

structure ConnectedDepositFacts (bout : BlockOutput) : Prop where
  run : processTransaction (input deploymentPost.state) BlockOutput.init depositTx 0 =
    .ok (depositedState, bout)
  gas : bout.blockGasUsed = 45038
  requests : parseDepositRequests bout = .ok []

theorem connected_deposit_exists : ∃ bout, ConnectedDepositFacts bout := by
  obtain ⟨bout, event, run, gas, _, _, _, _, requests⟩ :=
    deposit_transaction deployment_deposit_context
  exact ⟨bout, ⟨run, gas, requests⟩⟩

noncomputable def depositBout : BlockOutput := Classical.choose connected_deposit_exists

theorem connected_deposit_facts : ConnectedDepositFacts depositBout :=
  Classical.choose_spec connected_deposit_exists

theorem deposited_systemCodes : SystemCodes depositedState := by
  intro a ha
  rw [depositedState, deposit_settled_code]
  exact deployment_systemCodes a ha

structure ConnectedBodyFacts (bout : BlockOutput) : Prop where
  run : applyBody (input deploymentPost.state) [Sum.inr depositTx] [] =
    .ok (depositedState, bout)
  gas : bout.blockGasUsed = 45038

theorem connected_body_exists : ∃ bout, ConnectedBodyFacts bout := by
  obtain ⟨bout, run, gas⟩ := deposit_body_of_transaction deployment_systemCodes
    deposited_systemCodes connected_deposit_facts.run connected_deposit_facts.requests
  exact ⟨bout, ⟨run, gas.trans connected_deposit_facts.gas⟩⟩

noncomputable def bodyBout : BlockOutput := Classical.choose connected_body_exists

theorem connected_body_facts : ConnectedBodyFacts bodyBout :=
  Classical.choose_spec connected_body_exists

noncomputable def historyFuture : BlockChain :=
  depositChain deploymentPost.state depositedState bodyBout

noncomputable def closedHistory :
    ConfiguredHistoryTrace config deploymentCheckpoint historyFuture :=
  retainedDepositHistory deployment_canonical deployment_sumNof
    (by rw [connected_body_facts.gas]; decide +kernel) connected_body_facts.run

theorem closedHistory_rawFrames : closedHistory.rawFrames =
    (retainedDepositBody connected_body_facts.run).rawFrames := rfl

theorem closedHistory_settledFrames : closedHistory.settledFrames =
    (retainedDepositBody connected_body_facts.run).settledFrames := rfl

theorem history_nonempty : historyFuture.blocks.length = 2 := rfl

theorem deposited_holder : depositedState.get senderE =
    { holderAccount with nonce := 1, bal := 909923 } := by
  rw [depositedState, deposit_settled_holder, deployment_holder]
  rfl

theorem deposited_weth_balance :
    (historyFuture.state.getStor contractAddress).get (balSlot senderE) = amount := by
  change ((depositSettledState deploymentPost.state).getStor contractAddress).get _ = _
  rw [deposit_settled_stor, Stor.get_set_self]
  rfl

theorem deposited_contract_ether : historyFuture.state.bal contractAddress = amount := by
  apply deposit_settled_contract_balance
  change (deploymentPost.state.get contractAddress).bal = 0
  rw [deployment_contract]
  rfl

/-- The final exit is processed at the history terminal state. This does not
place it inside, or validate, a successor block. -/
noncomputable def withdrawBenv : Benv := (input deploymentPost.state).withState historyFuture.state

end Blanc.Lift.Weth9.ClosedInstance
