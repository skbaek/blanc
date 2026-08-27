import Blanc.PinnedPauseTarget
import Blanc.LidoCircuitBreakerPublicPause

/-!
# Pinned-target composition interface for the Lido CircuitBreaker

This module only instantiates the shared account protocol with the production
CircuitBreaker calldata and the two cells named by
`PauseSuccessNoninterference`.  It selects no real target and proves no target
implementation correct.

`PublicPausePinnedTargetStatement` is the frozen entry-3 theorem *shape*.
It starts before T2, from the public entry premises and actual production run,
then consumes the protocol and actual-invocation code hook opaquely.  Its
conclusion records the T2 family derived with target noninterference, the
actual target boundary, and the paused final account state.  A proxy revisit
reuses the same statement by replacing only the bundle and hook
instantiations.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- The target-agnostic protocol specialized only to the CircuitBreaker's
fixed outbound ABI and the two success-classification storage cells. -/
abbrev LidoPinnedPauseTarget
    (circuitBreaker pauser target : Adr) (program : Prog)
    (pausedUntil : Adr → Stor → B256)
    (protectedSurface : List B256) : Prop :=
  PinnedPauseTarget circuitBreaker target program pauseForCalldata
    isPausedCalldata pausedUntil
    [countSlot pauser.toB256, heartbeatIntervalSlot] protectedSurface

/-- Program-entry evidence for the actual pause CALL boundary.  The message is
tied to the parent instruction's concrete spawn, so an arbitrary exact-shape
message with unrelated code cannot discharge this predicate. -/
def PinnedPauseBoundaryExecutesProgram
    (sevm : Sevm) (target : Adr) (program : Prog) (duration : B256)
    (callPre callPost : Devm) : Prop :=
  ∃ (msg : Msg) (xl : Xlot) (child : Devm)
      (pc nextPc : Nat) (resume : Resume),
    ExactTargetCall sevm.currentTarget target (pauseForCalldata duration)
      false msg ∧
    MessageExecutesProgram msg xl program ∧
    msg.benv.stat.time = sevm.benvStat.time ∧
    Ninst.step ⟨pc, sevm, callPre⟩ Ninst.call =
      .spawn (Jaune.Frame.ofCall msg) resume nextPc ∧
    Xlot.Filled xl ∧
    ProcessMessage msg xl (.ok child) ∧
    Ninst.StepRun pc sevm callPre Ninst.call xl (.ok callPost) ∧
    callPost.state = child.state ∧
    callPost.returnData = child.output

/-- Program-entry evidence for the actual query STATICCALL boundary. -/
def PinnedStatBoundaryExecutesProgram
    (sevm : Sevm) (target : Adr) (program : Prog)
    (statPre statPost : Devm) : Prop :=
  ∃ (msg : Msg) (xl : Xlot) (child : Devm)
      (pc nextPc : Nat) (resume : Resume),
    ExactTargetCall sevm.currentTarget target isPausedCalldata true msg ∧
    MessageExecutesProgram msg xl program ∧
    msg.benv.stat.time = sevm.benvStat.time ∧
    Ninst.step ⟨pc, sevm, statPre⟩ Ninst.statcall =
      .spawn (Jaune.Frame.ofCall msg) resume nextPc ∧
    Xlot.Filled xl ∧
    ProcessMessage msg xl (.ok child) ∧
    Ninst.StepRun pc sevm statPre Ninst.statcall xl (.ok statPost) ∧
    statPost.state = child.state ∧
    statPost.returnData = child.output

/-- Program-entry evidence on the successful codeful trace of one exact
`pauseAfterSet` occurrence.  The guard and post-CALL branch joins connect its
boundary states to `entry` and to each other; no arbitrary boundary-shaped
message is quantified. -/
def LidoPinnedBoundaryExecutions
    (fs : List Func) (sevm : Sevm) (entry : Devm)
    (target : Adr) (program : Prog) (duration : B256)
    (ex : Execution) : Prop :=
  (entry.getCode target).size.toB256 ≠ 0 ∧
    ∃ guardTestPost guardPost callPre callPost branchTestPost
        armPre statPre statPost : Devm,
      Line.Run sevm entry pauseCodeGuard guardTestPost ∧
      Devm.PopBurnBy [0] (gVerylow + gHigh) guardTestPost guardPost ∧
      Line.Run sevm guardPost pauseCallStaging callPre ∧
      Ninst.RunCompiled sevm callPre (.exec .call) callPost ∧
      PauseCallBoundary sevm target duration callPre callPost ∧
      PinnedPauseBoundaryExecutesProgram sevm target program duration
        callPre callPost ∧
      Func.RunCompiledTo fs sevm callPost pauseAfterCallBranch ex ∧
      Ninst.RunCompiled sevm callPost Ninst.iszero branchTestPost ∧
      Devm.PopBurnBy [0] (gVerylow + gHigh) branchTestPost armPre ∧
      Line.Run sevm armPre pauseStatStaging statPre ∧
      Ninst.RunCompiled sevm statPre (.exec .statcall) statPost ∧
      PauseStatBoundary sevm target statPre statPost ∧
      PinnedStatBoundaryExecutesProgram sevm target program
        statPre statPost ∧
      Func.RunCompiledTo fs sevm statPost
        (Ninst.iszero :::
          ((Func.call bubbleRevertSlot) <?> decodePausedResult)) ex

/-- One settled successful target CALL tied to the actual parent spawn.  The
spawn equation prevents an unrelated message with the same terminal child
shape from serving as the target witness.  The final projection equality is
conclusion evidence, not a premise of the entry-3 statement. -/
def PinnedTargetPauseWitness (sevm : Sevm) (target : Adr) (program : Prog)
    (duration : B256) (pausedUntil : Adr → Stor → B256)
    (callPre callPost final : Devm) : Prop :=
  PauseCallBoundary sevm target duration callPre callPost ∧
  ∃ (msg : Msg) (xl : Xlot) (child : Devm)
      (pc nextPc : Nat) (resume : Resume),
    ExactTargetCall sevm.currentTarget target (pauseForCalldata duration)
      false msg ∧
    MessageExecutesProgram msg xl program ∧
    msg.benv.stat.time = sevm.benvStat.time ∧
    Ninst.step ⟨pc, sevm, callPre⟩ Ninst.call =
      .spawn (Jaune.Frame.ofCall msg) resume nextPc ∧
    ProcessMessage msg xl (.ok child) ∧
    Ninst.StepRun pc sevm callPre Ninst.call xl (.ok callPost) ∧
    callPost.state = child.state ∧
    callPost.returnData = child.output ∧
    child.error.isSome = false ∧
    pausedUntil target (child.state.getStor target) =
      sevm.benvStat.time + duration ∧
    pausedUntil target (final.state.getStor target) =
      pausedUntil target (child.state.getStor target)

/-- The successful end-to-end conclusion expected from entry 3.  It records
that T2's committed family was derived, exposes the actual target invocation,
and states pausedness on the same successful final state named by `ex`. -/
def PublicPausePinnedTargetConclusion (sevm : Sevm) (pre : Devm)
    (target duration : B256) (targetCode : ByteArray)
    (program : Prog) (pausedUntil : Adr → Stor → B256)
    (ex : Execution) (final : Devm) : Prop :=
  PublicPauseCommittedOutcomes sevm pre target duration targetCode ex ∧
    ∃ callPre callPost : Devm,
      PinnedTargetPauseWitness sevm target.toAdr program duration pausedUntil
        callPre callPost final ∧
      PausedAt pausedUntil final.state target.toAdr sevm.benvStat.time

/-- Frozen entry-3 statement shape.  The bundle is consumed whole: none of
its four clauses is unfolded here.  The actual-invocation hook is requested
only for the exact `pauseAfterSet` entry extracted from this public run. -/
def PublicPausePinnedTargetStatement
    (sevm : Sevm) (pre : Devm) (owner : Adr)
    (target duration idx0 len0 last0 : B256)
    (img : Bytes) (targetCode : ByteArray) (program : Prog)
    (pausedUntil : Adr → Stor → B256)
    (protectedSurface : List B256) (ex : Execution) : Prop :=
  PublicPauseEntryPremises sevm pre owner target duration idx0 len0 last0 img
      targetCode →
    target.toAdr ≠ sevm.currentTarget →
    Prog.RunCompiledTo sevm pre (runtime officialParams) ex →
    LidoPinnedPauseTarget sevm.currentTarget sevm.caller target.toAdr program
      pausedUntil protectedSurface →
    ∀ entry,
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sevm pre target duration targetCode ex entry →
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sevm entry target.toAdr program duration ex →
      ∀ final, ex = .ok final →
        PublicPausePinnedTargetConclusion sevm pre target duration targetCode
          program pausedUntil ex final

end Blanc.LidoCircuitBreaker
