import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayRun

/-!
# Executed closed-world control for the CircuitBreaker × gateway composition

This module replays the production CircuitBreaker public pause from its concrete
entry world and closes the already-proved installed-gateway suffix.  The gas
ladder is derived from the real 15,948-byte gateway crossing rather than copied
from the ten-instruction stub control.

The run itself is the generic `LidoCircuitBreakerTwgRun.closedPublicPause`; this
module supplies the finite-duration world's spec (the stored duration word
`pauseWorldDuration` and the gateway's 25,598-gas finite child charge) and keeps
its public statement.
-/

namespace Blanc.Composition

open Jaune
open Blanc
open Blanc.LidoCircuitBreaker
open Blanc.LidoTriggerableWithdrawalsGateway

namespace LidoCircuitBreakerTwg

private def gatewayRunWorld : LidoCircuitBreakerTwgRun.GWorld :=
  ⟨pauseLastWorldStor, gatewayPauseWorldGas, pauseWorldDuration, 25598⟩

private theorem gatewayRunWorld_spec :
    LidoCircuitBreakerTwgRun.GWorldSpec gatewayRunWorld where
  assignment := pauseLastStor_assignment
  expiry := pauseLastStor_expiry
  duration := pauseLastStor_duration
  index := pauseLastStor_index
  length := pauseLastStor_length
  entry := pauseLastStor_entry
  count := pauseLastStor_count
  child := by decide +kernel
  gas := by decide +kernel
  premises := gatewayPauseWorld_publicPausePremises
  notPrecompile := gatewayPauseWorld_target_not_precompile
  timeLtExpiry := by decide
  durNe := by decide
  projNe := by decide
  timeLt := by decide

/-- A concrete production public pause with the installed pinned-target gateway.
The theorem exposes the production run, exact `pauseAfterSet` entry, actual
`pauseSuccess` subrun, explicit callback noninterference, combined hook,
committed outcome family, and the final pinned-target conclusion. -/
theorem gatewayPauseWorld_closedPublicPause :
    ∃ entry successPre final : Devm,
      Prog.RunCompiledTo gatewayPauseWorldSevm gatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256
          pauseWorldDuration (gatewayCode controlDeployParams) (.ok final) entry ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      PauseSuccessNoninterference gatewayPauseWorldSevm entry successPre ∧
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm entry pauseWorldCallee
          (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams) pauseWorldDuration (.ok final) ∧
      PublicPauseCommittedOutcomes gatewayPauseWorldSevm gatewayPauseWorldPre
          pauseWorldCallee.toB256 pauseWorldDuration
          (gatewayCode controlDeployParams) (.ok final) ∧
      PublicPausePinnedTargetConclusion gatewayPauseWorldSevm
          gatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldDuration
          (gatewayCode controlDeployParams) (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
          LidoTriggerableWithdrawalsGateway.pausedUntil (.ok final) final :=
  have := gatewayRunWorld_spec
  LidoCircuitBreakerTwgRun.closedPublicPause gatewayRunWorld

end LidoCircuitBreakerTwg

end Blanc.Composition
