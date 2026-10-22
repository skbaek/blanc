import Blanc.StaticStorage

/-!
# Representation-exact storage silence of actual STATICCALL

The shared direct argument in StaticStorage accounts for normalized balance
transfers, static child execution, precompiles and rollback. This module keeps
the representation-exact boundary used by storage-tree consumers.
-/

namespace Blanc

open Jaune

/-- Actual STATICCALL preserves raw storage whenever the selected rules have no state gas. -/
theorem Ninst.staticcall_inv_getStor_exact_noStateGas
    {sevm : Sevm} {pre post : Devm}
    (hstateGas : sevm.benvStat.rules.stateGas = none)
    (run : Ninst.Run sevm pre Ninst.staticcall post) :
    Devm.getStor pre = Devm.getStor post :=
  Ninst.staticcall_getStor_eq_noStateGas hstateGas run

/-- Every successful STATICCALL leaves every raw storage map equal on a covered fork. -/
theorem Ninst.staticcall_inv_getStor_exact
    {sevm : Sevm} {pre post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : Ninst.Run sevm pre Ninst.staticcall post) :
    Devm.getStor pre = Devm.getStor post :=
  Ninst.staticcall_inv_getStor_exact_noStateGas hfork.rules_stateGas_none run

end Blanc
