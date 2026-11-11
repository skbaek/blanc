import Blanc.Lift.ExactWalk
import Blanc.CommonProofs.Walk
import Blanc.Lift.Loop
import Blanc.CompiledWalkInversion
import Blanc.Lift.InvWalk

/-!
# Inverting successful synthetic runs, one tree node at a time

The converse of `ExactWalk.lean`: from a successful `SFunc.Run` (the safety relation `exec_lift`
produces) of a node at a state `St b S M G`, the successor state is again an `St` over the same
base `b` (for every step that does not touch the world), with the stack the step computes and
some gas.  Each lemma pairs with its `rx_*` counterpart; together they make an inversion walk as
mechanical as a liveness walk.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

end Steps

/-! ## Control nodes of cut runs -/

section Control

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f g : SFunc} {r : Seg}

theorem ric_jumpCut {k : Nat} {dd : B256} (hk : k ∈ C)
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) (.jump k) r) :
    ∃ G', r = .at k (St b S M G') := by
  cases run with
  | jumpCut d0 _ h =>
      exact ⟨_, congrArg _ (St.of_pop1 h).2⟩
  | jump _ hkC _ _ _ => exact absurd hk hkC

theorem ric_undefined {devm : Devm} (run : SFunc.RunCut fs sevm C devm .undefined r) : False := by
  cases run

end Control

/-! ## World-touching steps (frozen) -/

section World

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

-- SEGMENT: riSstore
end World

end Blanc.Lift
