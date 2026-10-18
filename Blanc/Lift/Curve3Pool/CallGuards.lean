import Blanc.Lift.GuardedCalls
import Blanc.Lift.Curve3Pool.Cert

/-!
# Curve 3pool: every call site is flag-guarded or an identity copy

The 3pool runtime (`code`, 21199 bytes) passes the byte-level flag-guard check (`code_guardCheck`,
one linear kernel decision of `guardCheck`): at every instruction start, each `CALL`/`STATICCALL` is
followed by `PUSH2; JUMPI` falling through to `PUSH1 0; DUP1; REVERT` (69 sites), or is an identity
copy `PUSH1 4; GAS; CALL` (18 sites).  So in any successful pool frame every entered child commits
(`Exec.rawFrameDescendants_of_guardCheck`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-- **The 3pool runtime passes the flag-guard check** (kernel evaluation). -/
theorem code_guardCheck : guardCheck code = true := by
  decide +kernel

/-- The check's negative control: the runtime with its first flag-guarded `CALL`'s fall-through
`REVERT` (at byte `0x25da`, after the `transferFrom` pull of `exchange` at `0x25d2`) replaced by `STOP` fails it. -/
theorem code_guardCheck_mutant :
    guardCheck ⟨code.data.set! 0x25da 0x00⟩ = false := by
  decide +kernel

end Blanc.Lift.Curve3Pool
