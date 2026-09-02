import Blanc.LidoCircuitBreakerPinnedTargetComposition
import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTarget
import Blanc.LidoTriggerableWithdrawalsGatewayCode

/-!
# Composition: the Lido CircuitBreaker pinned to the Triggerable Withdrawals Gateway

This is the first module in Blanc's `COMPOSITION` stratum.  Composition is the
one place a theorem may name two contract families at once; the two families
themselves stay siblings and neither imports the other.  See
`README.md`, "Module hierarchy: contracts are siblings", and
`scripts/check-layering.py`.

Nothing here restates a family's own result.  The CircuitBreaker family owns
the public pause route, its boundary relations, and the generic pinned-target
theorem; the gateway family owns its compiled runtime, its account-level
bundle, and its pause/query/projection vocabulary.  This module supplies only
the two things neither family can state on its own:

* the exact ABI agreement between the CircuitBreaker's outbound calldata
  encoders and the gateway's own inbound encoders, and
* the specialization of the gateway's quantified bundle to the exact
  CircuitBreaker cell list `[countSlot pauser, heartbeatIntervalSlot]`.

The direct-installation adapter and the entry-3 headline theorem build on top
of these; they consume the gateway bundle through `gateway_lidoPinnedPauseTarget`
and never unfold one of its four clauses here.
-/

namespace Blanc.Composition

open Jaune
open Blanc
open Blanc.LidoCircuitBreaker

namespace LidoCircuitBreakerTwg

/-! ## The two exact ABI agreements

Both families define their calldata encoders independently: the CircuitBreaker
from its own `selector "pauseFor" [.uint256]` computation, the gateway from the
census-derived literal `selPauseFor`.  That independence is the point — the
equality below is a real check that the caller and the callee agree, not a
definitional coincidence arranged by sharing one definition. -/

/-- The CircuitBreaker's outbound `pauseFor(uint256)` selector is the gateway's
own census-derived selector literal. -/
theorem pauseForSelector_eq :
    LidoCircuitBreaker.pauseForSelector =
      LidoTriggerableWithdrawalsGateway.selPauseFor := by
  decide +kernel

/-- The CircuitBreaker's outbound `isPaused()` selector is the gateway's own
census-derived selector literal. -/
theorem isPausedSelector_eq :
    LidoCircuitBreaker.isPausedSelector =
      LidoTriggerableWithdrawalsGateway.selIsPaused := by
  decide +kernel

/-- Exact `pauseFor(uint256)` calldata agreement, at every duration. -/
theorem pauseForCalldata_eq (duration : B256) :
    LidoTriggerableWithdrawalsGateway.pauseForCalldata duration =
      LidoCircuitBreaker.pauseForCalldata duration := by
  unfold LidoTriggerableWithdrawalsGateway.pauseForCalldata
    LidoCircuitBreaker.pauseForCalldata
  rw [pauseForSelector_eq]

/-- The function-level form consumed when rewriting inside the bundle, whose
pause-calldata field is a `B256 → Bytes` parameter. -/
theorem pauseForCalldata_eq_fun :
    LidoTriggerableWithdrawalsGateway.pauseForCalldata =
      LidoCircuitBreaker.pauseForCalldata :=
  funext pauseForCalldata_eq

/-- Exact `isPaused()` calldata agreement. -/
theorem isPausedCalldata_eq :
    LidoTriggerableWithdrawalsGateway.isPausedCalldata =
      LidoCircuitBreaker.isPausedCalldata := by
  unfold LidoTriggerableWithdrawalsGateway.isPausedCalldata
    LidoCircuitBreaker.isPausedCalldata
  rw [isPausedSelector_eq]

/-! ## The specialized bundle

`LidoTriggerableWithdrawalsGateway.pinnedPauseTarget` is quantified over the
caller-supplied CircuitBreaker cell list.  Specializing it to the exact two
cells named by `PauseSuccessNoninterference` — the pauser's registry count and
the heartbeat interval — is the whole of the interface connection.  No clause
of the bundle is re-proved here. -/

/-- The compiled gateway runtime discharges the CircuitBreaker-specialized
pinned pause-target protocol at the exact cell list
`[countSlot pauser, heartbeatIntervalSlot]`. -/
theorem gateway_lidoPinnedPauseTarget
    (dp : LidoTriggerableWithdrawalsGateway.DeployParams)
    (circuitBreaker pauser gateway : Adr)
    (different : gateway ≠ circuitBreaker) :
    LidoPinnedPauseTarget circuitBreaker pauser gateway
      (LidoTriggerableWithdrawalsGateway.runtime dp)
      LidoTriggerableWithdrawalsGateway.pausedUntil
      LidoTriggerableWithdrawalsGateway.protectedSurface := by
  have bundle :=
    LidoTriggerableWithdrawalsGateway.pinnedPauseTarget dp circuitBreaker
      gateway [countSlot pauser.toB256, heartbeatIntervalSlot] different
  rwa [pauseForCalldata_eq_fun, isPausedCalldata_eq] at bundle

/-! ## Direct installation of the exact compiled gateway runtime

The bundle above says what the gateway account *does*.  It does not say that
the CircuitBreaker's actual outbound calls reached that account's code — and
the opening goal's hostile review established that asking a caller to hand over
the two `MessageExecutesProgram` witnesses is premise-shaped evidence, not a
closed installed target.  The adapter below derives both occurrences from
direct installation instead. -/

/-- The exact compiled gateway runtime as installed account code. -/
def gatewayCode (dp : LidoTriggerableWithdrawalsGateway.DeployParams) :
    ByteArray :=
  ByteArray.mk (LidoTriggerableWithdrawalsGateway.lidoTwgCode dp).toArray

/-- Compiler witness in the shape the direct crossing consumes. -/
theorem gatewayCode_compile
    (dp : LidoTriggerableWithdrawalsGateway.DeployParams) :
    Prog.compile (LidoTriggerableWithdrawalsGateway.runtime dp) =
      some (gatewayCode dp).toList := by
  rw [LidoTriggerableWithdrawalsGateway.lidoTwgCode_compile]
  simp [gatewayCode, ByteArray.toList_eq_toList_data]

/-- **The direct-target adapter.**  A successful `pauseAfterSet` suffix against
an account carrying the exact compiled gateway runtime supplies both actual
program occurrences.

**No** low-level code fact is asked of the caller.  Non-delegation and a
nonempty byte list follow from the compiler witness; nonzero installed width
follows from the successful terminal polarity, because the CircuitBreaker's own
`EXTCODESIZE` guard reverts on the zero arm; nonzero depth follows from the
successful suffix past the `CALL`, because the depth-limit arm's flag selects
the bubble and the bubble cannot end `.ok`.  Both `MessageExecutesProgram`
witnesses and the concrete CALL/STATICCALL linkage are derived. -/
theorem gatewayBoundaryExecutions_of_afterSet_ok
    {fs : List Func} {sevm : Sevm} {entry final : Devm}
    {target : Adr} {duration : B256}
    {dp : LidoTriggerableWithdrawalsGateway.DeployParams}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (targetNe : target ≠ sevm.currentTarget)
    (nonprecompile : sevm.benvStat.rules.isPrecomp target = false)
    (installed : entry.getCode target = gatewayCode dp)
    (targetWindow : MemWordAt entry
      (targetWord * 32).toNat target.toB256)
    (durationWindow : MemWordAt entry
      (durationWord * 32).toNat duration)
    (dynamic : sevm.isStatic = false)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet (.ok final)) :
    LidoPinnedBoundaryExecutions fs sevm entry target
      (LidoTriggerableWithdrawalsGateway.runtime dp) duration (.ok final) :=
  directBoundaryExecutions_of_afterSet_ok h_empty h_bubble
    (gatewayCode_compile dp) targetNe nonprecompile installed
    targetWindow durationWindow dynamic run

/-! ## Entry 3: the pinned-target closure

The headline theorem takes the ordinary public-entry premises, the production
run, exact gateway code identity, distinctness, non-precompile, and a
successful terminal polarity — and nothing else.  It carries no code-shape
premise at all.  In particular it has **no**
bundle premise (C2 supplies it), **no** program-occurrence premise (the adapter
derives both), no accepted-query premise, no callback-noninterference premise,
and no paused-result premise.  Its conclusion is the frozen entry-3 conclusion,
so the two CircuitBreaker cells are preserved by the gateway's own proved
semantic descendant-write noninterference rather than by an assumed callback
equality. -/

/-- **Entry 3.**  At a successful public `pause(target)` run of the production
Lido CircuitBreaker, with the exact compiled Triggerable Withdrawals Gateway
runtime directly installed at a distinct, non-precompile target account, the
committed outcome family holds, the actual gateway `pauseFor`/`isPaused`
executions occur, and the gateway account is left paused at exactly
`pauseForProjection entryTime duration` on the same successful final state. -/
theorem publicPause_gatewayPinnedTarget
    {sevm : Sevm} {pre final : Devm} {owner : Adr}
    {target duration idx0 len0 last0 : B256} {img : Bytes}
    {dp : LidoTriggerableWithdrawalsGateway.DeployParams}
    {ex : Execution}
    (premises : PublicPauseEntryPremises sevm pre owner target duration
      idx0 len0 last0 img (gatewayCode dp))
    (targetNe : target.toAdr ≠ sevm.currentTarget)
    (nonprecompile : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (publicRun : Prog.RunCompiledTo sevm pre (runtime officialParams) ex)
    (success : ex = .ok final) :
    PublicPausePinnedTargetConclusion sevm pre target duration (gatewayCode dp)
      (LidoTriggerableWithdrawalsGateway.runtime dp)
      LidoTriggerableWithdrawalsGateway.pausedUntil ex final := by
  obtain ⟨entry, reached⟩ :=
    publicPause_reaches_pauseAfterSet premises publicRun
  have canonicalTarget : target.toAdr.toB256 = target :=
    toB256_toAdr premises.targetCanonical
  rcases reached with
    ⟨targetWindow, durationWindow, targetCodeAt, countDecrement, afterSetRun⟩
  have reachedAt :
      PublicPauseAfterSetAt
        ((runtime officialParams).main :: (runtime officialParams).aux)
        sevm pre target duration (gatewayCode dp) ex entry :=
    ⟨targetWindow, durationWindow, targetCodeAt, countDecrement, afterSetRun⟩
  subst success
  have hook := gatewayBoundaryExecutions_of_afterSet_ok
    (fs := (runtime officialParams).main :: (runtime officialParams).aux)
    (by rfl) (by rfl) targetNe nonprecompile
    targetCodeAt (by rw [canonicalTarget]; exact targetWindow) durationWindow
    premises.dynamic afterSetRun
  exact publicPause_pinnedTarget premises targetNe publicRun
    (gateway_lidoPinnedPauseTarget dp sevm.currentTarget sevm.caller
      target.toAdr targetNe)
    entry reachedAt hook final rfl

end LidoCircuitBreakerTwg

end Blanc.Composition
