import Blanc.Lift.SystemExecution.ConsolidationRequest.Check

/-! Valid jump destinations: the jump checks run inside the Check module's range decisions
(`cert_rangeOk`, registry `check.fuse_jumps`), so `jumps_ok` is one projection. -/

namespace Blanc.Lift.SystemExecution.ConsolidationRequest

open Jaune

theorem code_eq : code = Blanc.consolidationRequestCode := by
  rfl

theorem jumps_ok : Cert.jumpsOk code cert = true :=
  Cert.jumpsOk_of_rangeOk cert_rangeOk

end Blanc.Lift.SystemExecution.ConsolidationRequest
