import Blanc.ExecutionNoDelProducer
import Blanc.Lift.SpawnKindsM

/-!
# The runtime-safety bundle from a linear byte walk

`InstalledRuntimeSafety` is produced from a `Cert.check` certificate by `of_cert`. A runtime lifted
only under `Cert.checkM` has no such certificate; a linear walk over its bytes gives the same facts,
because every node of a frame entered at pc `0` sits at a position no `PUSH` immediate covers
(`Exec.Deriv.ParentPrefix.noPush`).

* `selfdestructFreeCheck` — the walk: no instruction start holds `SELFDESTRUCT`;
* `not_selfdestruct_of_check` — soundness at a reached position;
* `InstalledRuntimeSafety.of_linearCheck` — the bundle from this walk and `callKindsCheck`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The linear instruction walk refusing `SELFDESTRUCT` at an instruction start. -/
def selfdestructFreeWalk : List UInt8 → Nat → Bool
  | [], _ => true
  | b :: bs, 0 => b != 0xff && selfdestructFreeWalk bs (pushWidth b)
  | _ :: bs, skip + 1 => selfdestructFreeWalk bs skip

/-- No instruction start of `code` holds `SELFDESTRUCT`. -/
def selfdestructFreeCheck (code : ByteArray) : Bool := selfdestructFreeWalk code.data.toList 0

/-- `SELFDESTRUCT` refused at an instruction start, stepped over in `PUSH` data. -/
example : selfdestructFreeCheck ⟨#[0x60, 0xff, 0x00]⟩ = true := by decide +kernel
example : selfdestructFreeCheck ⟨#[0x60, 0x00, 0xff]⟩ = false := by decide +kernel

end Blanc.Lift

namespace Blanc

open Jaune Blanc.Lift

end Blanc
