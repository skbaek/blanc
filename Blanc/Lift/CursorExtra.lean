import Blanc.Lift.Sound
import Blanc.Lift.Reach
import Blanc.Lift.ObservedReach
import Jaune.ExecChronology
import Blanc.Lift.Cursor
import Blanc.Lift.SoundExtra

/-!
# The certificate cursor: the prefix form of the lift

`lift_sound` (`Blanc/Lift/Sound.lean`) relates only *successful* executions to
the certificate's synthetic program.  This module relates every node reached
along a frame's same-frame chain (`Exec.Deriv.ParentPrefix`) — whatever the
frame's eventual outcome: success, revert, exceptional halt — to a checked
node of the certificate.

A `Cursor` names a point of the synthetic program: the tree still to run, its
pc, its abstract frame, the current function's return arity, and the stack of
pending `callNext` continuations (`Cont`).  `CursorOK code c n κ` says the
concrete node `n` sits at `κ`: same pc, the tree checks there
(`checkNode … = true`), and the concrete operand stack decomposes into one
segment per pending function, each matched by its abstract frame
(`FrameMatches`) — `node_soundM`'s recursion invariant made explicit.

* `cursor_start`: a checked certificate places every frame entered at pc `0`
  at entry `0`;
* `cursor_step`: every same-frame edge out of a cursor-placed node is one
  synthetic step (`SStep`) to a cursor-placed node — including a `CALL`'s
  edge over its child frame, whatever the child's outcome;
* `cursor_of_parentPrefix`: hence every node of the frame's same-frame chain is
  cursor-placed, reached from entry `0` by synthetic steps.

No statement here has a success premise.  `CoveredFork` enters only through
the transfer soundness of the instruction steps (`ninstTransfer_run`).
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-! ### One same-frame edge, by instruction kind -/

namespace Cursor

/-! ### Frame bookkeeping for one step -/

end Cursor

/-! ### The cursor theorems -/

theorem cursor_of_parentPrefix {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {F n : Exec.Deriv} (hpc : F.pc = 0) (hcode : F.sevm.code = code)
    (hfork : ShanghaiOnwards F.sevm.benvStat.fork) (hp : Exec.Deriv.ParentPrefix F n) :
    ∃ κ, Relation.ReflTransGen (SStep c) (Cursor.start c) κ ∧ CursorOK code c n κ :=
  cursor_of_parentPrefix_noStateGas hc hpc hcode hfork.rules_stateGas_none hp

end Blanc.Lift
