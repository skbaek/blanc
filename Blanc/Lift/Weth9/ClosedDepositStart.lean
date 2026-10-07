import Blanc.Lift.Weth9.ClosedBody
import Blanc.Lift.Weth9.ClosedDepositTxData
import Blanc.Lift.Weth9.ClosedKeysBalanceSender

/-! The concrete deployment state discharges the deposit transaction's
initial account and slot requirements. No WETH holder is precredited. -/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc

theorem deployment_holder_slot_zero :
    (deploymentPost.state.getStor contractAddress).get (balSlot senderE) = 0 := by
  change (Devm.getStor deploymentPost contractAddress).get (balSlot senderE) = 0
  rw [deployment_facts.storage, deposit_bal_sender_slot]
  decide +kernel

theorem deployment_deposit_context : DepositTxContext (input deploymentPost.state) := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · change 50000 ≤ 1000000
    decide +kernel
  · change (deploymentPost.state.get senderE).nonce = 0
    rw [deployment_holder]
    rfl
  · change (deploymentPost.state.get senderE).bal = 1000000
    rw [deployment_holder]
    rfl
  · change (deploymentPost.state.get senderE).code.size = 0
    rw [deployment_holder]
    rfl
  · exact deployment_installed
  · exact deployment_holder_slot_zero
  · change (deploymentPost.state.get contractAddress).bal = 0
    rw [deployment_contract]
    rfl

end Blanc.Lift.Weth9.ClosedInstance
