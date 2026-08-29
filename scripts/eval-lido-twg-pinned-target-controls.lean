-- Execute the full-runtime TWG pause/query controls without treating their
-- values as theorem evidence.
--
-- Run from the repository root after the current hard calibration window:
--
--   lake env lean --run scripts/eval-lido-twg-pinned-target-controls.lean

import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTargetControl

open Blanc.LidoTriggerableWithdrawalsGateway.PinnedTargetControl

def main : IO Unit := do
  if productionPauseQueryAccepted then
    if wrappingMutationBites then
      IO.println
        "PASS: full-runtime TWG sentinel pause/query succeeds and clause (i) rejects the wrapping mutant"
      if wrappingQueryDiagnosticObserved then
        IO.println
          "DIAGNOSTIC: the wrapping mutant's downstream query returned canonical false"
      else
        IO.println
          "DIAGNOSTIC: no downstream canonical-false query observation was available"
    else
      throw (IO.userError
        "FAIL: clause (i) did not reject the full-runtime TWG wrapping-add mutant")
  else
    throw (IO.userError
      "FAIL: the full-runtime TWG sentinel pause/query control did not succeed")
