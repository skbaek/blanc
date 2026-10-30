import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewaySentinelControl
import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayRun

/-!
# Executed closed-world control for the CircuitBreaker × gateway composition

This module replays the production CircuitBreaker public pause from its concrete
entry world and closes the already-proved installed-gateway suffix.  The gas
ladder is derived from the real 15,948-byte gateway crossing rather than copied
from the ten-instruction stub control.

The run itself is the generic `LidoCircuitBreakerTwgRun.closedPublicPause`; this
module supplies the infinite-sentinel world's spec (the stored duration word
`pauseInfiniteSentinel` and the gateway's 25,567-gas sentinel child charge) and
keeps its public statement.
-/

namespace Blanc.Composition

open Jaune
open Blanc
open Blanc.LidoCircuitBreaker
open Blanc.LidoTriggerableWithdrawalsGateway
open Blanc.Composition.LidoCircuitBreakerTwg

namespace LidoCircuitBreakerTwgSentinel

private def gatewayRunWorld : LidoCircuitBreakerTwgRun.GWorld :=
  ⟨sentinelPauseWorldStor, sentinelGatewayPauseWorldGas, pauseInfiniteSentinel, 25567⟩

private theorem gatewayRunWorld_spec :
    LidoCircuitBreakerTwgRun.GWorldSpec gatewayRunWorld where
  assignment := sentinelPauseLastStor_assignment
  expiry := sentinelPauseLastStor_expiry
  duration := sentinelPauseLastStor_duration
  index := sentinelPauseLastStor_index
  length := sentinelPauseLastStor_length
  entry := sentinelPauseLastStor_entry
  count := sentinelPauseLastStor_count
  child := by decide +kernel
  gas := by decide +kernel
  premises := sentinelGatewayPauseWorld_publicPausePremises
  notPrecompile := sentinelGatewayPauseWorld_target_not_precompile
  timeLtExpiry := by decide
  durNe := by decide
  projNe := by decide
  timeLt := by decide

/-- A concrete production public pause with the installed pinned-target gateway.
The theorem exposes the production run, exact `pauseAfterSet` entry, actual
`pauseSuccess` subrun, explicit callback noninterference, combined hook,
committed outcome family, and the final pinned-target conclusion. -/
theorem sentinelGatewayPauseWorld_closedPublicPause :
    ∃ entry successPre final : Devm,
      Prog.RunCompiledTo sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre pauseWorldCallee.toB256
          pauseInfiniteSentinel (gatewayCode controlDeployParams) (.ok final) entry ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      PauseSuccessNoninterference sentinelGatewayPauseWorldSevm entry successPre ∧
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm entry pauseWorldCallee
          (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams) pauseInfiniteSentinel (.ok final) ∧
      PublicPauseCommittedOutcomes sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          pauseWorldCallee.toB256 pauseInfiniteSentinel
          (gatewayCode controlDeployParams) (.ok final) ∧
      PublicPausePinnedTargetConclusion sentinelGatewayPauseWorldSevm
          sentinelGatewayPauseWorldPre pauseWorldCallee.toB256 pauseInfiniteSentinel
          (gatewayCode controlDeployParams) (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
          LidoTriggerableWithdrawalsGateway.pausedUntil (.ok final) final :=
  have := gatewayRunWorld_spec
  LidoCircuitBreakerTwgRun.closedPublicPause gatewayRunWorld

/-- The successful sentinel public pause stores the infinite sentinel itself,
not the modular sum of the block timestamp and the requested duration. -/
theorem sentinelGatewayPauseWorld_storesInfiniteSentinel :
    ∃ final : Devm,
      Prog.RunCompiledTo sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      final.getStorVal pauseWorldCallee
          LidoTriggerableWithdrawalsGateway.resumeSinceSlot = pauseInfiniteSentinel := by
  obtain ⟨_, _, final, hrun, _, _, _, _, _, _, hconclusion⟩ :=
    sentinelGatewayPauseWorld_closedPublicPause
  refine ⟨final, hrun, ?_⟩
  rcases hconclusion with ⟨_, _, hpinned, _⟩
  unfold PinnedTargetPauseWitness at hpinned
  rcases hpinned with
    ⟨_, _, _, child, _, _, _, _, _, _, _, _, _, _, _, _, hchild, hfinal⟩
  calc
    final.getStorVal pauseWorldCallee
          LidoTriggerableWithdrawalsGateway.resumeSinceSlot =
        LidoTriggerableWithdrawalsGateway.pausedUntil pauseWorldCallee
          (final.state.getStor pauseWorldCallee) := rfl
    _ = LidoTriggerableWithdrawalsGateway.pausedUntil pauseWorldCallee
          (child.state.getStor pauseWorldCallee) := by
        simpa only [toAdr_toB256] using hfinal
    _ = pauseForProjection sentinelGatewayPauseWorldSevm.benvStat.time
          pauseInfiniteSentinel := by
        simpa only [toAdr_toB256] using hchild
    _ = pauseInfiniteSentinel := by simp only [pauseForProjection, ↓reduceIte]

end LidoCircuitBreakerTwgSentinel

end Blanc.Composition
