import Blanc.Lift.CallSiteChildren
import Blanc.Lift.UniswapV2Pair.Cert

/-!
# The Pair certificate's CALL sites, kernel-checked

The Pair certificate executes `CALL` at exactly three tree nodes: the swap callback inside
`t_09aa_c4` and `_safeTransfer`'s CALL inside its two clones `t_20e1_c57` and `t_20e1_c71`.
`cert_callSites` checks this over every certificate function with one kernel `decide` per entry
(`SFunc.nodesSatisfy pairCallOk`).  Kept in its own module so that no language-server worker
elaborates the decisions.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The swap callback's CALL node, inside the straight prefix of `t_09aa_c4`. -/
def callbackCall : SFunc := SFunc.lineDrop 3 t_09aa_c4

/-- `_safeTransfer`'s CALL node in the clone `t_20e1_c57`. -/
def transferCall57 : SFunc := SFunc.lineDrop 44 t_20e1_c57

/-- `_safeTransfer`'s CALL node in the clone `t_20e1_c71`. -/
def transferCall71 : SFunc := SFunc.lineDrop 44 t_20e1_c71

/-- Every `CALL` node is one of the three call sites. -/
def pairCallOk : Ninst → SFunc → Bool
  | .exec .call, g =>
      (SFunc.next (.exec .call) g == callbackCall) ||
        (SFunc.next (.exec .call) g == transferCall57) ||
        (SFunc.next (.exec .call) g == transferCall71)
  | _, _ => true

/-- **The Pair certificate's CALL sites.**  Every function of the certificate passes the node check:
its only `CALL` nodes are `callbackCall`, `transferCall57` and `transferCall71`. -/
theorem cert_callSites : ∀ f ∈ cert.prog, f.nodesSatisfy pairCallOk = true := by
  intro f member
  simp only [Cert.prog, cert, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

end Blanc.Lift.UniswapV2Pair
