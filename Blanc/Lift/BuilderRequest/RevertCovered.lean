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

**Status.** All four families (inhibited, bad-length, paid-read, not-admitted) are proved at both
codes with no twins: each code's guard-tail walk is generalized over `(v : l.Valid)` as
`frameReverts_not_admitted_on` in its own `Revert.lean` file, and this file instantiates it at
`coveredSteps_valid` alongside the shared `*_on` proofs.
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
    FrameReverts s b (revertBound n) :=
  frameReverts_not_admitted_on (coveredSteps_valid fork) hcode caller hlen off wordRun
    (feeBase_stateGas_covered s b) rejected

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
    FrameReverts s b (revertBound n) :=
  frameReverts_not_admitted_on (coveredSteps_valid fork) hcode caller hlen off wordRun
    (feeBase_stateGas_covered s b) rejected

end Exit

end Blanc.Lift.BuilderRequest
