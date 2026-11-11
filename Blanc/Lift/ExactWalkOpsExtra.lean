import Blanc.Lift.ExactWalk
import Blanc.Lift.ExactWalkOps

/-!
# More forward walk steps for gas-exact lifted runs

Companions to `Blanc/Lift/ExactWalk.lean` for the instructions a solc 0.6
runtime uses beyond WETH9's: the shifts, `BYTE`, `NOT`, `GT`, `MSTORE8`,
`CALLDATACOPY`, `LOG1`, `EXP` with a nonzero exponent, and the `JUMP` goto.  Every
lemma has the same backwards shape as its siblings there: the run of the node
from `St b S M (G + c)` follows from the run of its continuation from
`St b S' M' G`.
-/

namespace Blanc.Lift

open Jaune

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {f g : SFunc} {o : Outcome}
  {S : List B256} {M : Mem} {G : Nat}

/-- `EXP` with its exponent's byte charge named. -/
theorem rx_exp' {x y : B256} {c : Nat} (hc : gExp + gExpbyte * y.bytecount = c)
    (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (B256.bexp x y :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: S) M (G + c)) (.next (.reg .exp) f) o := by
  subst hc
  refine .next ?_ k
  have h := Ninst.runCompiled_reg (sevm := sevm) (r := .exp) (by rintro ⟨⟩)
    (Rinst.runCore_exp_eq_ok (devm := St b (x :: y :: S) M (G + (gExp + gExpbyte * y.bytecount)))
      rfl (by simp only [St.gasLeft, le_add_iff_nonneg_left, zero_le]) hroom)
  simpa only [St, Devm.memory_setMach, Devm.setMach_gasLeft, add_tsub_cancel_right,
    Devm.stateGas_setMach, Devm.setMach_setMach] using h

end Steps

end Blanc.Lift
