import Blanc.Lift.UniswapV2Pair.GetterScalarCore
import Blanc.Lift.UniswapV2Pair.PairDispatch
import Blanc.Lift.InvWalkDispatch

/-! Actual selector-tree paths for the ten scalar getter entries. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem getterScalar_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (s : ScalarGetter) (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (body : SFunc.RunExact cert.prog sevm (St b [s.selector] getterInitMemory G) s.entryTree o)
    (h_shifts : sevm.benvStat.rules.op.shifts = true) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + s.dispatchGas)) t_0000_c0 o :=
  by rcases s with (s | s | s) <;> cases s <;> exact pair_dispatch_exact value size selector (by kernel_rfl) (by decide +kernel) body h_shifts

theorem getterScalar_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (s : ScalarGetter) (selector : Blanc.Sevm.selector sevm = s.selector)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ G', SFunc.Run cert.prog sevm (St b [s.selector] M G') s.entryTree o :=
  by rcases s with (s | s | s) <;> cases s <;> exact pair_dispatch_inv selector (by kernel_rfl) run

end Blanc.Lift.UniswapV2Pair
