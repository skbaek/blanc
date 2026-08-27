-- Evaluate the executable pinned-target controls without turning their
-- existence into theorem evidence.
--
-- Run from the repository root:
--
--   lake env lean --run scripts/eval-lido-circuit-breaker-pinned-target-controls.lean
--
-- Each Option constructor checks its control's complete witness.  In
-- particular, the benign Option starts at exact message entry, follows the
-- compiled parent's staged CALL through its inert child and root settlement,
-- and records the frame-owner equalities used by the account-level theorem.
-- The other Options check the wrong returned Boolean and the retained write
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
