import Blanc.Lift.BuilderRequest.Revert
import Blanc.Lift.BuilderRequest.Deposit.Revert
import Blanc.Lift.BuilderRequest.Exit.Revert
import Blanc.Lift.BuilderRequest.FeePath
import Blanc.ForwardCall

/-!
# The builder contracts' reverting frames at the forks that run today (O35)

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

Outcome O35 of `blanc-eip8282-builder-requests-v1` §19: the `frameReverts_*` results at the covered
forks, obtained by generalizing the Amsterdam proofs over the steps, with no twins. The shared
generalization lives in `Blanc/Lift/BuilderRequest/Revert.lean` as the `*_on` variants, over a fork's
`StorageSteps.Valid` plus a state-gas premise; the Amsterdam statements there are thin corollaries.
This file instantiates them at `coveredSteps_valid`, reusing the contract-local cuts and `revert_at`
facts, which are fork-free (`decide +kernel` over the bytes, `kernel_rfl`).

**Plan (which steps differ, what is abstracted).** The only steps of these frames that differ between
covered forks and Amsterdam are `SLOAD` and `SSTORE`. Covered forks run `afterSload`/`afterSstore`
with no state gas; Amsterdam runs `afterSloadA`/`afterSstoreA` with the state-gas record. Everything
else in the reverting walks — caller dispatch, the inhibitor guard, the excess test, the fee window
and loop, the calldata getter and the guard trees — is fork-free and shared. What the `*_on`
generalization abstracts: the read/write carriers and their charges (`StorageSteps`), the
forward/inverse step laws (`Valid`: `push0`, `readRun`, `writeRun` and the state/log/output
projections), and the fee path's base meter (`feeBase`), whose state-gas preservation is a separate
premise because `Valid` does not project `stateGas`. The gas bound `revertBound` is already fork-free:
both meters price the two cold reads at `gasColdSload` (`Blanc.sloadCost_le`). The one direction that
does not generalize is `Submissions.message_reverts`: it is message-level Amsterdam machinery
(`processMessageCall_revert`, the returned state gas), with no covered-fork counterpart.

**Status.** Inhibited, bad-length and paid-read frames are proved at both codes. The not-admitted
frames (`frameReverts_not_admitted_covered`) are stated with `sorry`: their tails walk the
contract-local guard cuts (`lowCut`, `floorCut`, `coverCut`, exit `lowCut`) over `l.feeBase`, and
those walks live in `Deposit/Revert.lean` and `Exit/Revert.lean` over `(amsterdamSteps s).feeBase`,
which this run may not edit. Copying them here with `coveredSteps` swapped in would be the
concept-level twin O35 forbids. The lawful resolution, once Lean capacity is free, is to generalize
each contract's guard-tail walk over `(v : l.Valid)` in its own `Revert.lean` file and instantiate it
twice; the `DRAFT` notes below name the exact walks.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-- The fee path's base keeps the state-gas meter on covered steps, which read without state gas. -/
theorem feeBase_stateGas_covered (s : Sevm) (b : Devm) :
    ((coveredSteps s).feeBase b).stateGas = b.stateGas := by
  show (afterSload s (afterSload s b 0) 1).stateGas = _
  rw [afterSload_stateGas, afterSload_stateGas]

namespace Deposit

open Blanc.Lift.BuilderRequest.Deposit

/-- **While slot 0 holds the inhibitor, a non-system frame at the deposit code executes `REVERT`, under covered forks.** -/
theorem frameReverts_inhibited_covered {s : Sevm} {b : Devm} (hcode : s.code = code)
    (fork : CoveredFork s.benvStat.fork) (caller : s.caller ≠ systemAddress)
    (inhibited : b.getStorVal s.currentTarget 0 = B256.max) :
    FrameReverts s b (revertBound 0) :=
  frameReverts_inhibited_on (coveredSteps_valid fork) inhibit_cut revert_at hcode caller inhibited
    afterSload_stateGas

/-- **Calldata of neither form reverts at the deposit code, under covered forks.** -/
theorem frameReverts_badLength_covered {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = code) (fork : CoveredFork s.benvStat.fork)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 s b) 17 1 17 0 n out)
    (other : s.data.length.toB256 ≠ (184 : B256)) (nonzero : s.data.length.toB256 ≠ 0) :
    FrameReverts s b (revertBound n) :=
  UserPath.frameReverts_badLength_on (k := userPath) (coveredSteps_valid fork) rfl rfl badLength_cut
    revert_at hcode caller off wordRun (feeBase_stateGas_covered s b) other nonzero

/-- **A fee read carrying value reverts at the deposit code, under covered forks.** -/
theorem frameReverts_paidRead_covered {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = code) (fork : CoveredFork s.benvStat.fork)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 s b) 17 1 17 0 n out)
    (empty : s.data = []) (paid : s.value ≠ 0) :
    FrameReverts s b (revertBound n) :=
  UserPath.frameReverts_paidRead_on (k := userPath) (coveredSteps_valid fork) rfl rfl paidRead_cut
    revert_at hcode caller off wordRun (feeBase_stateGas_covered s b) empty paid

/-- **A submission the guards do not admit reverts at the deposit code, under covered forks.** -/
theorem frameReverts_not_admitted_covered {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = code) (fork : CoveredFork s.benvStat.fork)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 184)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 s b) 17 1 17 0 n out)
    (rejected : ¬ Admits s.data s.value (out / (17 : B256))) :
    FrameReverts s b (revertBound n) := by
  -- The three guard tails (`lowCut`, `floorCut`, `coverCut`) use only fork-free `rx_*` steps, so the
  -- covered walk differs from `Deposit/Revert.lean` only in the fee-path base and the `push0` source.
  -- Do not copy them here as twins: generalize `frameReverts_not_admitted` over `(v : l.Valid)` in
  -- `Deposit/Revert.lean` instead (constants: `lowCut` at `X = 5 + 10 + 3 + 3 + 2 + 3 + 1`, `floorCut`
  -- at `X = 5 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1`, `coverCut` at
  -- `X = 5 + 10 + 3 + 3 + 3 + 2 + 3 + 5 + 3 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1`).
  -- DRAFT: re-walk the three tails over `(coveredSteps s).feeBase b` and apply `UserPath.frameReverts_of_arm_on (coveredSteps_valid fork)`.
  sorry

end Deposit

namespace Exit

open Blanc.Lift.BuilderRequest.Exit

/-- **While slot 0 holds the inhibitor, a non-system frame at the exit code executes `REVERT`, under covered forks.** -/
theorem frameReverts_inhibited_covered {s : Sevm} {b : Devm} (hcode : s.code = code)
    (fork : CoveredFork s.benvStat.fork) (caller : s.caller ≠ systemAddress)
    (inhibited : b.getStorVal s.currentTarget 0 = B256.max) :
    FrameReverts s b (revertBound 0) :=
  frameReverts_inhibited_on (coveredSteps_valid fork) inhibit_cut revert_at hcode caller inhibited
    afterSload_stateGas

/-- **Calldata of neither form reverts at the exit code, under covered forks.** -/
theorem frameReverts_badLength_covered {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = code) (fork : CoveredFork s.benvStat.fork)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (other : s.data.length.toB256 ≠ (48 : B256)) (nonzero : s.data.length.toB256 ≠ 0) :
    FrameReverts s b (revertBound n) :=
  UserPath.frameReverts_badLength_on (k := userPath) (coveredSteps_valid fork) rfl rfl badLength_cut
    revert_at hcode caller off wordRun (feeBase_stateGas_covered s b) other nonzero

/-- **A fee read carrying value reverts at the exit code, under covered forks.** -/
theorem frameReverts_paidRead_covered {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = code) (fork : CoveredFork s.benvStat.fork)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (empty : s.data = []) (paid : s.value ≠ 0) :
    FrameReverts s b (revertBound n) :=
  UserPath.frameReverts_paidRead_on (k := userPath) (coveredSteps_valid fork) rfl rfl paidRead_cut
    revert_at hcode caller off wordRun (feeBase_stateGas_covered s b) empty paid

/-- **A submission below the fee reverts at the exit code, under covered forks.** -/
theorem frameReverts_not_admitted_covered {s : Sevm} {b : Devm} {n : Nat} {out : B256}
    (hcode : s.code = code) (fork : CoveredFork s.benvStat.fork)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 48)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 s b) 17 1 17 0 n out)
    (rejected : ¬ Admits s.data s.value (out / (17 : B256))) :
    FrameReverts s b (revertBound n) := by
  -- The `lowCut` tail uses only fork-free `rx_*` steps, so the covered walk differs from
  -- `Exit/Revert.lean` only in the fee-path base and the `push0` source. Do not copy it here as a twin:
  -- generalize `frameReverts_not_admitted` over `(v : l.Valid)` in `Exit/Revert.lean` instead (constant:
  -- `lowCut` at `X = 5 + 10 + 3 + 3 + 2 + 1`).
  -- DRAFT: re-walk the tail over `(coveredSteps s).feeBase b` and apply `UserPath.frameReverts_of_arm_on (coveredSteps_valid fork)`.
  sorry

end Exit

end Blanc.Lift.BuilderRequest
