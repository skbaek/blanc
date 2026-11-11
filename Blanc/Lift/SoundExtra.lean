import Blanc.Lift.Check
import Blanc.Lift.MemMap
import Blanc.LadderSem
import Blanc.ExecutionFrames
import Blanc.Lift.Sound

/-!
# The lifting theorem (safety direction)

`lift_sound`: if a certificate checks against the bytes, every successful Jaune
execution of those bytes from pc `0` with an empty stack is a synthetic run of
the certificate's program.  It is stated over arbitrary bytes and certificates;
a contract instantiates it with one kernel-checked `Cert.check … = true`.

The proof is one strong recursion over `Exec.Deriv` (`node_soundM`).  Its
invariant relates the concrete operand stack to an abstract frame: the stack is
`S ++ base`, where `S` matches the frame word by word (`FrameMatches ρ`, with
`.ret` read as the current function's return address `ρ`) and `base` belongs to
the callers and is left untouched.  A node either halts, or returns: the current
function jumps to `ρ` leaving exactly `m` words above `base`, and the remaining
derivation from `ρ` is strictly smaller, which is what lets the caller's
`callNext` continue by recursion.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-! ### Decided `JUMPI`s -/

/-! ### Folded instructions -/

/-! ### Where a lifted step's child derivation sits -/

/-! ### `PC` nodes -/

/-! ### Checked entries, with or without memory tracking -/

theorem lift_sound {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (exc : Exec 0 sevm pre (.ok post)) :
    SProg.Run c.prog sevm pre post :=
  lift_sound_noStateGas hc hcode hfork.rules_stateGas_none exc

end Blanc.Lift
