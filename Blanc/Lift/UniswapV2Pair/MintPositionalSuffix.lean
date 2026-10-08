import Blanc.Lift.CursorNoExecSuffix
import Blanc.Lift.UniswapV2Pair.Check

/-! Every remaining Mint parent instruction after feeTo is frame-free. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def mintFinalExecFreeEntries : List Nat :=
  [9, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
    58, 59, 60, 62, 65, 66, 69, 70, 72, 74]

theorem mintFinalExecFreeEntries_closed :
    ExecFreeSet cert.prog mintFinalExecFreeEntries = true := by decide

/-- The actual fee reply cursor and its original Mint continuations exclude
every later same-frame external instruction, including the public return. -/
theorem mint_fee_suffix_no_exec {F : Exec.Deriv} {κ : Cursor}
    (placed : CursorOK code cert F κ)
    (tree : κ.f = .next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero)
      (.next (.push [0x27,0x6b] (by decide)) (.branch t_2762_c68 t_276b_c68)))))
    (continuations : κ.K.map Cont.f = [t_1233_c41, t_039b_c86])
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∀ N, Exec.Deriv.ParentPrefix F N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  apply placed.noExecSuffix cert_check fork mintFinalExecFreeEntries_closed
  · rw [tree]
    decide
  · intro f member
    rw [continuations] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · decide
    · decide

end Blanc.Lift.UniswapV2Pair
