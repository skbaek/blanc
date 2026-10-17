import Blanc.Lift.Curve3Pool.Cert
import Blanc.Lift.SpawnKindsM

/-!
# Curve 3pool: spawn kinds

Every instruction start of the 3pool runtime (`code`, 21199 bytes) holds no external
instruction but `CALL` and `STATICCALL` (`code_callKinds`, one linear kernel decision of
`callKindsCheck`), so any code semantics whose runs execute `code` has `SpawnKinds`
(`pool_spawnKinds`).  The `0xF4` byte inside the `PUSH4` selector `0xf446c1d0` is immediate data
the walk steps over.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-- The 3pool runtime decodes no external instruction but `CALL`/`STATICCALL` at any
instruction start. -/
theorem code_callKinds : callKindsCheck code = true := by
  decide +kernel

/-- **3pool frames spawn only by `CALL`/`STATICCALL`.**  For any code semantics `sem` whose runs
execute the 3pool runtime. -/
theorem pool_spawnKinds {ca : Adr} {sem : CodeSem}
    (hcode : ∀ {sevm pre post}, sem.Run sevm pre post → sevm.code = code) :
    SpawnKinds ca sem :=
  spawnKinds_of_callKindsCheck hcode code_callKinds

end Blanc.Lift.Curve3Pool
