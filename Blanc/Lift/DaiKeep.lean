import Blanc.Lift.Dai.Check
import Blanc.Lift.StaticOnlyKeep

/-!
# A DAI frame keeps the foreign world

DAI's certified code executes no external instruction but `STATICCALL` (`ecrecover`, in `permit`), so
a committed DAI frame keeps the storage of every other address with code and the code of every other
address.
-/

namespace Blanc.Lift.Dai

open Jaune Blanc Blanc.Lift

/-- **DAI's certificate executes no external instruction but `STATICCALL`.** -/
theorem dai_cert_staticOnly : ∀ f ∈ cert.prog, f.execsSatisfy Xinst.isStaticcall = true := by
  have all : cert.prog.all (fun f => f.execsSatisfy Xinst.isStaticcall) = true := by
    decide +kernel
  exact fun f member => List.all_eq_true.mp all f member

/-- **A committed DAI frame keeps the foreign world.** -/
theorem dai_keepsForeign : KeepsForeign code :=
  keepsForeign_of_staticOnly cert_check dai_cert_staticOnly

theorem dai_code_ne : code.toList ≠ [] := by
  decide +kernel

theorem dai_not_delegation : ¬ isValidDelegation code := by
  intro h
  have h1 := h.1
  revert h1
  decide +kernel

end Blanc.Lift.Dai
