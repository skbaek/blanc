-- Evaluate the executable pinned-target controls without turning their
-- existence into theorem evidence.
--
-- Run from the repository root:
--
--   lake env lean --run scripts/eval-lido-circuit-breaker-pinned-target-controls.lean
--
-- Each Option constructor checks its control's complete witness: the benign
-- child-call choreography, the wrong returned Boolean, or the retained write
-- to the protected CircuitBreaker cell.  A missing witness exits nonzero.

import Blanc.LidoCircuitBreakerPinnedTargetControl

open Blanc.LidoCircuitBreaker.PinnedTargetControl

def pinnedTargetControlFixturesAvailable : Bool :=
  benignCallFixture?.isSome &&
    wrongBoolFixture?.isSome &&
    retainedWriteFixture?.isSome

def main : IO Unit := do
  if pinnedTargetControlFixturesAvailable then
    IO.println "PASS: pinned-target executable controls exist and bite"
  else
    throw (IO.userError
      "FAIL: a pinned-target executable control fixture is unavailable")
