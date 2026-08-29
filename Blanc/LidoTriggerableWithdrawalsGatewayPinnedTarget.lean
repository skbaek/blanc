import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTargetInterface
import Blanc.MessageExecutionInversion

/-!
# Account-level pinned-target boundary for the Triggerable Withdrawals Gateway

This family-owned module fixes the account protocol vocabulary that the TWG
runtime must discharge.  It intentionally imports no Circuit Breaker module:
the calldata builders, storage projection, and protected selector are the
gateway family's own definitions.

The final `PinnedPauseTarget` constructor is deliberately absent from this
checkpoint until the concrete A2 runtime proofs exist.  In particular, this
module does not introduce a structure of assumed semantic witnesses and does
not reflect an executable fixture into theorem evidence.  The remaining
declarations must be proved from actual `Prog.RunCompiledTo`/`Exec` walks and
retained `ProcessMessage` slots:

* a clean exact `pauseFor` execution stores `pauseForProjection`;
* a clean exact `isPaused` execution preserves `resumeSinceSlot` and returns
  the canonical boolean for its entry projection;
* a committing exact pause/query execution enters no child frame, while a
  noncommitting execution uses `Exec.noRetainedWriteTo_of_not_commits`;
* a selected trigger execution cannot settle cleanly while the entry
  projection is paused, including malformed and unauthorized calldata paths.

Once those source-derived facts are available, the intended public theorem is

```
theorem pinnedPauseTarget
    (dp : DeployParams) (circuitBreaker gateway : Adr)
    (circuitBreakerCells : List B256)
    (different : gateway ≠ circuitBreaker) :
    PinnedPauseTarget circuitBreaker gateway (runtime dp)
      pauseForCalldata isPausedCalldata pausedUntil
      circuitBreakerCells protectedSurface
```

The quantification over `dp` leaves the locator identity, its account, and all
callee code arbitrary.  The pause/query routes themselves are call-free; the
paused trigger must revert before consulting any of those accounts.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

end LidoTriggerableWithdrawalsGateway
end Blanc
