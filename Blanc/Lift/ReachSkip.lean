import Blanc.Lift.ReachWalk
import Blanc.Lift.Silent
import Blanc.Lift.ShuffleSkip
import Blanc.Lift.FrameSkip

/-!
# Reach forms of the route-C skips

The node clause of `ImplStepLaw` is a statement about the machine at an external-instruction node
of a frame's own chain; `reach_of_parentPrefix` (`Blanc/Lift/Cursor.lean`) places that node at a
`Reach` of the certificate.  When the world at the node depends on a store before it (`_permit`'s
nonce bump), the reach is walked up to that store.  This module gives the two route-C skips in reach
form:

* `rr_shuffle`: a checked shuffle segment (`Blanc/Lift/ShuffleSkip.lean`) on a reach to an external
  instruction: the reach passes through the segment's target, with the same world and the carried
  stack;
* `rr_call_silent`: a silent, exec-free internal call on such a reach returns, with the same world
  and the declared number of words over the stack below the callee's frame.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

/-! ## Shuffle segments on a reach -/

section ReachShuffle

open AbstractStackSafety

variable {es : List Entry} {Fw : List Nat} {tgt : SFunc} {pB : Nat} {X R : List B256} {T : Conf}
  {K : List SFunc}

/-- What a checked result promises for a reach to an external instruction from `d0`. -/
def ShReachR (fs : List SFunc) (sevm : Sevm) (P : Sevm → Devm → Ninst → Devm → Prop)
    (X R : List B256) (d0 : Devm) (tgt : SFunc) (K : List SFunc) (T : Conf) :
    Option (List SVal) → Prop
  | none => False
  | some π => ∃ d, d.state = d0.state ∧ ∃ Y, d.stack = Y ++ R ∧ Carried X π Y ∧
      Reach P fs sevm ⟨d, tgt, K⟩ T

theorem ShReachR.state {d0 d1 : Devm} {o : Option (List SVal)}
    (h : ShReachR fs sevm P X R d1 tgt K T o) (hs : d1.state = d0.state) :
    ShReachR fs sevm P X R d0 tgt K T o := by
  match o, h with
  | some _, ⟨d, hd, rest⟩ => exact ⟨d, hd.trans hs, rest⟩

end ReachShuffle

end Blanc.Lift
