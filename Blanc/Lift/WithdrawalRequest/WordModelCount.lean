import Blanc.Lift.WithdrawalRequest.WordModelReplay
import Blanc.Lift.WithdrawalRequest.ResetOccurrence
import Blanc.ExecutionRequestSegments
import Blanc.ExecutionBodyGas

/-!
A guarded occurrence whose caller is the system address is a system event.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionAccountingReplay ExecutionTrace Blanc.WithdrawalRequest

theorem WordReplayGuard.system_kind {storage : Stor} {event : WordReplayEvent}
    (guard : WordReplayGuard storage event)
    (caller : event.frame.sevm.caller = systemAddress) : event.kind = .system := by
  cases kind : event.kind with
  | system => rfl
  | submission entry iterations output =>
    have input := guard.input
    simp only [wordEventInput, kind] at input
    exact False.elim (input.1 caller)
  | getter iterations output =>
    have input := guard.input
    simp only [wordEventInput, kind] at input
    exact False.elim (input.1 caller)

end Blanc.Lift.WithdrawalRequest
