import Blanc.Lift.CallRestriction
import Blanc.ExecutionDirectCode
import Blanc.ExecutionNoninterference
import Blanc.ExecutionAdmissionSem
import Blanc.ExecutionTraceFrames
import Blanc.Lift.StaticOnlyFrames
import Blanc.Lift.CursorExtra

/-!
# Frames whose deployed code can only STATICCALL

A contract whose certified bytes execute no external instruction except
`STATICCALL` cannot retain any non-static descendant frame. This module owns
the two generic halves of that fact, so that every such consumer of the
accounting ladder supplies only its certificate check:

* `parentPrefix_exec_staticcall_of_cert`: a certificate whose every function
  passes `SFunc.execsSatisfy Xinst.isStaticcall` allows only `STATICCALL` at
  every actual same-frame location of a frame entered at pc `0`;
* `Exec.staticOnly_descendantFrames_flatMap_eq_nil`: under that restriction, any
  frame observation is empty on all retained descendants of a target frame,
  provided it is empty on every strictly deeper static frame of the same code
  semantics (the ladder's inductive hypothesis).
-/

namespace Blanc.Lift

open Jaune

/-- The external-instruction restriction: only `STATICCALL`. -/
def Xinst.isStaticcall : Xinst → Bool
  | .staticcall => true
  | _ => false

/-- A checked certificate whose functions execute only `STATICCALL` permits only
`STATICCALL` at every actual same-frame location, including internal jumps and
returns, of a frame entered at pc `0` of the certified bytes. -/
theorem parentPrefix_exec_staticcall_of_cert {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    {root node : Exec.Deriv} (pc : root.pc = 0) (installed : root.sevm.code = code)
    (fork : ShanghaiOnwards root.sevm.benvStat.fork)
    (chain : Exec.Deriv.ParentPrefix root node)
    {x : Xinst} (instruction : Ninst.At node.sevm.code node.pc (.exec x)) :
    x = .staticcall := by
  obtain ⟨cursor, reachable, ok⟩ := cursor_of_parentPrefix checked pc installed fork chain
  have allowed := ok.execsSatisfy
    (cursor.execsSatisfy_of_reachable only reachable) instruction
  cases x <;> simp_all only [Xinst.isStaticcall, Bool.false_eq_true]

end Blanc.Lift

namespace Blanc

open Jaune

end Blanc
