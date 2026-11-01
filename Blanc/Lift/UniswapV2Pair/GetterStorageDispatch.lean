import Blanc.Lift.UniswapV2Pair.GetterStorageMappingDecoder
import Blanc.Lift.UniswapV2Pair.PairDispatch

/-! Four actual checked pc-zero selector routes for the remaining storage getters. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive StorageGetter
  | balanceOf | nonces | allowance | getReserves

def StorageGetter.selector : StorageGetter → B256
  | .balanceOf => 0x70a08231
  | .nonces => 0x7ecebe00
  | .allowance => 0xdd62ed3e
  | .getReserves => 0x0902f1ac

def StorageGetter.entryTree : StorageGetter → SFunc
  | .balanceOf => t_049c_c87
  | .nonces => t_04d7_c82
  | .allowance => t_0640_c77
  | .getReserves => t_02d6_c101

def StorageGetter.dispatchGas : StorageGetter → Nat
  | .balanceOf => 187
  | .nonces => 164
  | .allowance => 207
  | .getReserves => 210

theorem getterStorage_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (s : StorageGetter) (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = s.selector)
    (body : SFunc.RunExact cert.prog sevm (St b [s.selector] getterInitMemory G) s.entryTree o)
    (h_shifts : sevm.benvStat.rules.op.shifts = true) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + s.dispatchGas)) t_0000_c0 o :=
  by cases s <;> exact pair_dispatch_exact value size selector (by kernel_rfl) (by decide +kernel) body h_shifts

theorem getterStorage_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (s : StorageGetter) (selector : Blanc.Sevm.selector sevm = s.selector)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ G', SFunc.Run cert.prog sevm (St b [s.selector] M G') s.entryTree o :=
  by cases s <;> exact pair_dispatch_inv selector (by kernel_rfl) run

end Blanc.Lift.UniswapV2Pair
