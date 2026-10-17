import Blanc.Lift.Curve3Pool.CheckPart0

/-!
# `remove_liquidity_imbalance`: checked-tree facts for the bridged callees

The imbalance walk crosses two bridged callees: `_A` (entry 27, `Callee/A.a_spec`)
and `get_D_mem` (entry 29, `Callee/GetDMem.getDMem_spec`). Their certificate entries
are checked by `CheckPart0.entry_27` / `entry_29`; the `rli_` wrappers below name
exactly those facts for the walk, proving nothing anew.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-- Entry 27 (`_A`) is checked. -/
theorem rli_entry_a :
    checkNodeM Blanc.Lift.Curve3Pool.code (Cert.entries Blanc.Lift.Curve3Pool.cert) Blanc.Lift.Curve3Pool.mems true
      (Blanc.Lift.Curve3Pool.cert[27]'(by decide +kernel)).1.rets (Blanc.Lift.Curve3Pool.cert[27]'(by decide +kernel)).1.pc
      (Blanc.Lift.Curve3Pool.cert[27]'(by decide +kernel)).1.frame (Blanc.Lift.Curve3Pool.mems.getD 27 []) (Blanc.Lift.Curve3Pool.cert[27]'(by decide +kernel)).2 = true :=
  entry_27

/-- Entry 29 (`get_D_mem`) is checked. -/
theorem rli_entry_gdm :
    checkNodeM Blanc.Lift.Curve3Pool.code (Cert.entries Blanc.Lift.Curve3Pool.cert) Blanc.Lift.Curve3Pool.mems true
      (Blanc.Lift.Curve3Pool.cert[29]'(by decide +kernel)).1.rets (Blanc.Lift.Curve3Pool.cert[29]'(by decide +kernel)).1.pc
      (Blanc.Lift.Curve3Pool.cert[29]'(by decide +kernel)).1.frame (Blanc.Lift.Curve3Pool.mems.getD 29 []) (Blanc.Lift.Curve3Pool.cert[29]'(by decide +kernel)).2 = true :=
  entry_29

end Blanc.Lift.Curve3Pool
