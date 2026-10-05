import Blanc.FakeExponential

/-!
Fuelled natural-number evaluation of the EELS fake-exponential recurrence.
The option is `none` precisely when the supplied fuel expires while the
accumulator is still active.
-/

namespace Blanc.FakeExponentialEval

open Jaune

def runFuel : Nat → Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _, accumulator =>
      if accumulator = 0 then some (0, 0) else none
  | fuel + 1, numerator, denominator, counter, accumulator =>
      if accumulator = 0 then some (0, 0)
      else
        match runFuel fuel numerator denominator (counter + 1)
          (accumulator * numerator / (denominator * counter)) with
        | none => none
        | some (iterations, output) => some (iterations + 1, accumulator + output)

def fakeExpFuel (fuel factor numerator denominator : Nat) : Option Nat :=
  (runFuel fuel numerator denominator 1 (factor * denominator)).map
    (fun result => result.2 / denominator)

theorem runFuel_of_run
    {numerator denominator counter accumulator iterations output : Nat}
    (run : FakeExponential.Run numerator denominator counter accumulator iterations output)
    {fuel : Nat} (enough : iterations ≤ fuel) :
    runFuel fuel numerator denominator counter accumulator =
      some (iterations, output) := by
  induction run generalizing fuel with
  | stop counter =>
    cases fuel with
    | zero => rfl
    | succ fuel => rfl
  | @step counter accumulator iterations output active next ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [runFuel, ite_eq_right active]
      rw [ih (by omega)]

theorem run_of_runFuel
    {numerator denominator counter accumulator iterations output fuel : Nat}
    (evaluates : runFuel fuel numerator denominator counter accumulator =
      some (iterations, output)) :
    FakeExponential.Run numerator denominator counter accumulator iterations output := by
  induction fuel generalizing numerator denominator counter accumulator iterations output with
  | zero =>
    simp only [runFuel] at evaluates
    by_cases active : accumulator = 0
    · rw [ite_eq_left active] at evaluates
      cases evaluates
      rw [active]
      exact FakeExponential.Run.stop counter
    · rw [ite_eq_right active] at evaluates
      contradiction
  | succ fuel ih =>
    by_cases active : accumulator = 0
    · rw [runFuel, ite_eq_left active] at evaluates
      cases evaluates
      rw [active]
      exact FakeExponential.Run.stop counter
    · rw [runFuel, ite_eq_right active] at evaluates
      cases htail : runFuel fuel numerator denominator (counter + 1)
          (accumulator * numerator / (denominator * counter)) with
      | none => rw [htail] at evaluates; contradiction
      | some result =>
        rw [htail] at evaluates
        cases result with
        | mk tailIterations tailOutput =>
          cases evaluates
          exact FakeExponential.Run.step active (ih htail)

theorem run_iff_runFuel
    {numerator denominator counter accumulator iterations output fuel : Nat}
    (enough : iterations ≤ fuel) :
    FakeExponential.Run numerator denominator counter accumulator iterations output ↔
      runFuel fuel numerator denominator counter accumulator =
        some (iterations, output) := by
  constructor
  · exact fun run => runFuel_of_run run enough
  · exact fun evaluates => run_of_runFuel evaluates

theorem fakeExpFuel_of_run
    {factor numerator denominator iterations output fuel : Nat}
    (run : FakeExponential.Run numerator denominator 1 (factor * denominator)
      iterations output)
    (enough : iterations ≤ fuel) :
    fakeExpFuel fuel factor numerator denominator =
      some (output / denominator) := by
  unfold fakeExpFuel
  rw [runFuel_of_run run enough]
  rfl

theorem fakeExpFuel_eq_fakeExp
    {factor numerator denominator iterations output fuel : Nat}
    (run : FakeExponential.Run numerator denominator 1 (factor * denominator)
      iterations output)
    (enough : iterations ≤ fuel) :
    fakeExpFuel fuel factor numerator denominator = some (fakeExp factor numerator denominator) := by
  rw [fakeExpFuel_of_run run enough, run.output_eq]
  rfl

end Blanc.FakeExponentialEval
