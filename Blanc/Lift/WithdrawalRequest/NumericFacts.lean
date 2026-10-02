import Blanc.FakeExponentialEval
import Blanc.WordFakeExponentialEval
import Blanc.Lift.WithdrawalRequest.Model

/-!
Concrete Nat-only evaluator facts used by the EIP-7002 counterexample.  The
closed computations in this file never evaluate B256 limb arithmetic.
-/

namespace Blanc.Lift.WithdrawalRequest

open Blanc
open Jaune

def wordFeeFuel (fuel excess : Nat) : Option Nat :=
  (WordFakeExponentialEval.runFuel fuel excess 17 1 17 0).map
    (fun result => result.2 / 17)

theorem word_fee_2893 :
    wordFeeFuel 1000 2893 =
      some 32087365885911168062721653499988857431024628719292649881555161070975172167 := by
  decide +kernel

theorem nat_fee_2893 :
    FakeExponentialEval.fakeExpFuel 1000 1 2893 17 =
      some 80668064690921409049190791237320678716946849613533250306370202067869504081 := by
  decide +kernel

theorem nat_run_2893 :
    FakeExponentialEval.runFuel 1000 2893 17 1 17 =
      some (462,
        1371357099745663953836243451034451538188096443430065255208293435153781569388) := by
  decide +kernel

theorem word_fee_2893_le_two_pow_245 :
    32087365885911168062721653499988857431024628719292649881555161070975172167 ≤
      2 ^ 245 := by
  decide +kernel

theorem two_pow_245_lt_nat_fee_2893 :
    2 ^ 245 < 80668064690921409049190791237320678716946849613533250306370202067869504081 := by
  decide +kernel

theorem fee_2893 {state : WithdrawalRequest.State}
    (excess : state.excess = 2893) :
    WithdrawalRequest.fee state =
      80668064690921409049190791237320678716946849613533250306370202067869504081 := by
  rw [WithdrawalRequest.fee, excess]
  have run : FakeExponential.Run 2893 17 1 (1 * 17) 462
      1371357099745663953836243451034451538188096443430065255208293435153781569388 := by
    simpa only [Nat.one_mul] using FakeExponentialEval.run_of_runFuel nat_run_2893
  have fuelEq := FakeExponentialEval.fakeExpFuel_eq_fakeExp
    (factor := 1) (numerator := 2893) (denominator := 17)
    (iterations := 462)
    (output := 1371357099745663953836243451034451538188096443430065255208293435153781569388)
    (fuel := 1000) run (by decide +kernel)
  have modelEq : fakeExp 1 2893 17 =
      80668064690921409049190791237320678716946849613533250306370202067869504081 := by
    apply Option.some.inj
    exact fuelEq.symm.trans nat_fee_2893
  exact modelEq

theorem fee_zero {state : WithdrawalRequest.State}
    (excess : state.excess = 0) : WithdrawalRequest.fee state = 1 := by
  exact WithdrawalRequest.fee_at_zero_excess state excess

end Blanc.Lift.WithdrawalRequest
