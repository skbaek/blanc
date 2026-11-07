import Blanc.Lift.RequestFee.Window
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.SystemCaller

/-!
# A request contract's caller dispatch

Every request contract starts `CALLER; PUSH20 SYSTEM; EQ; PUSH dest; JUMPI`: the system caller takes one
arm, every other caller the other. This is that tree and its exact forward walk.
-/

namespace Blanc.Lift.RequestSystem

open Jaune
open RequestFee (PushWord)

/-- `CALLER; PUSH20 SYSTEM; EQ; PUSH dest; JUMPI`. -/
def dispatchTree (dest : PushWord) (user system : SFunc) : SFunc :=
  (.next (.reg .caller) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] (by decide)) (.next (.reg .eq)
  (.next (.push (dest.head :: dest.tail) dest.le) (.branch user system)))))

/-- The charge of `dispatchTree`. -/
def dispatchGas : Nat := 21

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- The arm the caller selects. -/
def dispatchArm (sevm : Sevm) (user system : SFunc) : SFunc :=
  if sevm.caller = systemAddress then system else user

theorem system_push :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe] =
      systemAddress.toB256 := rfl

/-- Dispatch, forward, at its exact charge. -/
theorem dispatch_exact {dest : PushWord} {user system : SFunc}
    (tail : SFunc.RunExact fs sevm (St b [] M G) (dispatchArm sevm user system) o) :
    SFunc.RunExact fs sevm (St b [] M (G + dispatchGas)) (dispatchTree dest user system) o := by
  have hgas : G + dispatchGas = G + 10 + 3 + 3 + 3 + 2 := by
    simp only [dispatchGas, Nat.add_assoc]
  rw [hgas]
  unfold dispatchTree
  refine rx_caller (by decide) ?_
  refine rx_push system_push (by change 1 < 1024; decide) ?_
  refine rx_eq (adr_eqCheck systemAddress sevm.caller) (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  by_cases h : sevm.caller = systemAddress
  · simp only [ite_eq_left h, dispatchArm] at tail ⊢
    exact rx_branch_succ (by decide) tail
  · simp only [ite_eq_right h, dispatchArm] at tail ⊢
    exact rx_branch_zero tail

end Blanc.Lift.RequestSystem
