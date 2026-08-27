import Blanc.PinnedPauseTarget
import Blanc.LidoCircuitBreakerPublicPause

/-!
# Pinned-target composition interface for the Lido CircuitBreaker

This module only instantiates the shared account protocol with the production
CircuitBreaker calldata and the two cells named by
`PauseSuccessNoninterference`.  It selects no real target and proves no target
implementation correct.

`PublicPausePinnedTargetStatement` is the frozen entry-3 theorem *shape*.
It takes the T2 outcome family and the protocol as opaque propositions.  The
future target goal proves that statement after target selection; a proxy
revisit reuses the same statement by replacing only the bundle instantiation.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- The target-agnostic protocol specialized only to the CircuitBreaker's
fixed outbound ABI and the two success-classification storage cells. -/
abbrev LidoPinnedPauseTarget
    (circuitBreaker pauser target : Adr) (program : Prog)
    (pausedUntil : Devm → Adr → B256)
    (protectedSurface : List B256) : Prop :=
  PinnedPauseTarget circuitBreaker target program pauseForCalldata
    isPausedCalldata pausedUntil
    [countSlot pauser.toB256, heartbeatIntervalSlot] protectedSurface

/-- One settled successful target CALL, tied to the same parent CALL step and
carrying the account-level paused effect and truth at that boundary. -/
def PinnedTargetPauseWitness (sevm : Sevm) (target : Adr) (program : Prog)
    (duration : B256) (pausedUntil : Devm → Adr → B256)
    (callPre callPost : Devm) : Prop :=
  ∃ (msg : Msg) (xl : Xlot) (child : Devm),
    ExactTargetCall sevm.currentTarget target (pauseForCalldata duration)
      false msg ∧
    MessageUsesProgram msg program ∧
    msg.benv.stat.time = sevm.benvStat.time ∧
    Xlot.Filled xl ∧
    ProcessMessage msg xl (.ok child) ∧
    child.error.isSome = false ∧
    (∀ pc, Ninst.StepRun pc sevm callPre (.exec .call) xl (.ok callPost)) ∧
    pausedUntil child target = sevm.benvStat.time + duration ∧
    PausedAt pausedUntil child target sevm.benvStat.time

/-- The successful end-to-end conclusion expected from entry 3.  It retains
the exact T2 reached state and CALL boundary rather than naming an unrelated
target invocation. -/
def PublicPausePinnedTargetConclusion (sevm : Sevm) (pre : Devm)
    (target duration : B256) (targetCode : ByteArray)
    (program : Prog) (pausedUntil : Devm → Adr → B256)
    (ex : Execution) : Prop :=
  ∃ entry : Devm,
    PublicPauseAfterSetAt
      ((runtime officialParams).main :: (runtime officialParams).aux)
      sevm pre target duration targetCode ex entry ∧
    ∃ callPre callPost : Devm,
      PauseCallBoundary sevm target.toAdr duration callPre callPost ∧
      PinnedTargetPauseWitness sevm target.toAdr program duration pausedUntil
        callPre callPost

/-- Frozen entry-3 statement shape.  The bundle is consumed whole: none of
its four clauses is unfolded here.  `ProgramInstalledAt` is the one detachable
direct-code premise. -/
def PublicPausePinnedTargetStatement
    (sevm : Sevm) (pre : Devm) (target duration : B256)
    (targetCode : ByteArray) (program : Prog)
    (pausedUntil : Devm → Adr → B256)
    (protectedSurface : List B256) (ex : Execution) : Prop :=
  LidoPinnedPauseTarget sevm.currentTarget sevm.caller target.toAdr program
      pausedUntil protectedSurface →
    ProgramInstalledAt pre target.toAdr program →
    PublicPauseCommittedOutcomes sevm pre target duration targetCode ex →
    (∀ final, ex = .ok final →
      PublicPausePinnedTargetConclusion sevm pre target duration targetCode
        program pausedUntil ex)

end Blanc.LidoCircuitBreaker
