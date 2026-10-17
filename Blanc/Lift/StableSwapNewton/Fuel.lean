import Blanc.Lift.StableSwapNewton.Defs
import Blanc.Lift.FuelLoopWalk

/-! The checked StableSwap Newton loops are instances of the contract-neutral
fuel loop `Blanc.Lift.fuelLoop`, so the fuel-loop walk bridges
(`RunCut_fuelLoop_sound`, `RunExactCut_fuelLoop_exact` and their peeled forms)
apply to their compiled heads with `body` the checked body and `close` the
stopping test. -/

namespace Blanc.StableSwapNewton

open Blanc.Lift

/-- The checked `get_D` loop is the fuel loop over the checked body. -/
theorem loopDChk_eq_fuelLoop (x : Fin 3 → Nat) (ann S tol : Nat) :
    ∀ fuel D, loopDChk x ann S tol fuel D =
      fuelLoop (bodyDChk x ann S) (fun new prev => decide (closeEnough tol new prev)) fuel D := by
  intro fuel
  induction fuel with
  | zero => intro D; rfl
  | succ fuel ih =>
    intro D
    simp only [loopDChk, fuelLoop, ih]
    cases bodyDChk x ann S D <;>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, decide_eq_true_eq]

/-- The checked `y` loop (`get_y`, `get_y_D`) is the fuel loop over the
checked body. -/
theorem loopYChk_eq_fuelLoop (c b D tol : Nat) :
    ∀ fuel y, loopYChk c b D tol fuel y =
      fuelLoop (bodyYChk c b D) (fun new prev => decide (closeEnough tol new prev)) fuel y := by
  intro fuel
  induction fuel with
  | zero => intro y; rfl
  | succ fuel ih =>
    intro y
    simp only [loopYChk, fuelLoop, ih]
    cases bodyYChk c b D y <;>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, decide_eq_true_eq]

end Blanc.StableSwapNewton
