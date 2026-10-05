import Blanc.Lift.CallSite
import Blanc.Lift.UniswapV2Pair.Cert

/-!
# The Pair's `_safeTransfer` call sites: the interface fact

The Pair certificate has exactly three CALL sites: the swap callback (`t_09aa_c4`) and the two
clones of `_safeTransfer`'s CALL (`t_20e1_c57`, `t_20e1_c71`), one per return context.
`TransferSiteShape` is the fact about the latter two that the backward walk through the memcpy loop
(`t_20a4`/`t_20ad`) and the encoding block establishes: at either CALL, the input window carries the
`transfer` selector `0xa9059cbb`.

The premises are what every consumer has at hand for a successful Pair frame entered at pc `0` with
an empty stack and empty memory (`EntryCallShape`'s frames): the cursor placement and the stateful
reach from entry `0`, both from `reach_of_parentPrefix`.  The gas bound `gasLeft < 2 ^ 256` is
needed: with unbounded gas a token's huge return data can wrap the free-memory pointer modulo
`2 ^ 256`, after which the encoding can overwrite the pointer and the CALL window is arbitrary.
Under the bound, memory expansion keeps every written index far below `2 ^ 256`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- **Interface (proved by the `_safeTransfer` backward walk).**  Every node of a successful Pair
frame's same-frame chain that sits at the CALL of `t_20e1_c57` or `t_20e1_c71` sends calldata whose
selector is `transfer`'s, `0xa9059cbb`. -/
def TransferSiteShape : Prop :=
  ∀ {R N : Exec.Deriv} {κ : Cursor} {g : SFunc} {post : Devm},
    R.pc = 0 → R.sevm.code = code → CoveredFork R.sevm.benvStat.fork →
    R.devm.stack = [] → R.devm.memory = Mem.empty → R.devm.gasLeft < 2 ^ 256 → R.exn = .ok post →
    Exec.Deriv.ParentPrefix R N →
    Reach (StepIn R) cert.prog R.sevm ((Cursor.start cert).conf R.devm) (κ.conf N.devm) →
    CursorOK code cert N κ →
    κ.f = .next (.exec .call) g →
    (SFunc.LineSuffix κ.f t_20e1_c57 ∨ SFunc.LineSuffix κ.f t_20e1_c71) →
    CallInputSelector N 0xa9059cbb

end Blanc.Lift.UniswapV2Pair
