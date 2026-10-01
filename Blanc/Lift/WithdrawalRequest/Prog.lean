import Blanc.Lift.WithdrawalRequest.Cert

/-! The synthetic program selected by the canonical withdrawal-request certificate. -/

namespace Blanc.Lift.WithdrawalRequest

/-- The checked certificate's program, without any extra entry assumption. -/
def prog : List SFunc := cert.prog

/-- The certificate starts at the caller-dispatch tree. -/
theorem prog_root : prog[0]? = some t_0000_c0 := rfl

end Blanc.Lift.WithdrawalRequest
