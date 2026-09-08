import Blanc.CommonCore

namespace Blanc

open Jaune

/-- `chargeGas`, evaluated forward when the account cannot pay: the charge is
refused and the state is handed back untouched. -/
lemma chargeGas_eq_outOfGas {cost : Nat} {devm : Devm}
    (h : devm.gasLeft < cost) :
    chargeGas cost devm = .error ⟨.halt (.outOfGas .none), devm⟩ := by
  rw [chargeGas_def]
  have hs : safeSub devm.gasLeft cost = none := by
    unfold safeSub
    rw [if_neg (by omega)]
  rw [hs]

end Blanc
