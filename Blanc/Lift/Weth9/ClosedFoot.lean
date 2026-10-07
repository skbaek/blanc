import Blanc.Lift.Weth9.ClosedConnected
import Blanc.Lift.Weth9.ClosedKeysTransaction

/-! The actual connected history discharges trace-local freshness, holder
tracking, and the presence of its successful settlement-committed deposit. -/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.ExecutionTrace

theorem closedHistory_metadata :
    ∀ root ∈ closedHistory.rawFrames, root.sevm.currentTarget = contractAddress →
      root.sevm.caller = senderE ∧ root.sevm.data = depositTx.data := by
  rw [closedHistory_rawFrames]
  exact (deposit_context_body_frames (retainedDepositBody connected_body_facts.run)
    deployment_deposit_context deployment_systemCodes deposited_systemCodes
    connected_deposit_facts.run).1

theorem closedHistory_fresh :
    KeysFresh (fun _ => False) (historyTouchedKeys contractAddress closedHistory) :=
  deposit_history_fresh closedHistory closedHistory_metadata

theorem closedHistory_holder :
    historyKeyUniverse contractAddress closedHistory (fun _ => False) (.bal senderE) := by
  obtain ⟨root, member, target, caller⟩ :=
    (deposit_context_body_frames (retainedDepositBody connected_body_facts.run)
      deployment_deposit_context deployment_systemCodes deposited_systemCodes
      connected_deposit_facts.run).2.1
  exact deposit_history_holder closedHistory
    (by rw [closedHistory_rawFrames]; exact member) target caller

theorem closedHistory_committed_deposit :
    ∃ inv ∈ committedInvocations contractAddress closedHistory,
      decodeCall inv.sevm = some (.deposit senderE amount) := by
  obtain ⟨frame, member, target, static, decoded⟩ :=
    (deposit_context_body_frames (retainedDepositBody connected_body_facts.run)
      deployment_deposit_context deployment_systemCodes deposited_systemCodes
      connected_deposit_facts.run).2.2
  exact deposit_history_committed closedHistory
    (by rw [closedHistory_settledFrames]; exact member) target static decoded

end Blanc.Lift.Weth9.ClosedInstance
