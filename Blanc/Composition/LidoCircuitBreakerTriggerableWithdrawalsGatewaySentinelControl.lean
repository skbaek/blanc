import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayControl
import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayCrossing
import Blanc.LidoCircuitBreakerPinnedTargetCompositionControl

/-!
# Closed-world controls for the CircuitBreaker × gateway composition

This test-scoped composition module installs the **exact compiled Triggerable
Withdrawals Gateway runtime** at the CircuitBreaker's pause target, beside the
production CircuitBreaker runtime at its own account, and configures only the
explicit role, Registry, time and storage premises the entry-3 theorem names.

Its purpose is anti-vacuity: `publicPause_gatewayPinnedTarget` would be worth
nothing if its premise bundle were unsatisfiable, and in particular if the two
low-level code facts could not both hold of a real compiled gateway runtime.
Every fact below is a theorem about that concrete world — the gateway account's
code is the compiler's own output, kernel-reduced, and no evaluator output is
reflected into a theorem anywhere in this file.

`sentinelGatewayPauseWorld_closedPremises` isolates the public theorem's premise
closure.  The companion `LidoCircuitBreakerTriggerableWithdrawalsGatewayControlRun`
module constructs the production run itself from this exact world, using the
real gateway boundary walk and its derived gas schedule.
-/

namespace Blanc.Composition

open Jaune
open Blanc
open Blanc.LidoCircuitBreaker
open Blanc.Composition.LidoCircuitBreakerTwg

namespace LidoCircuitBreakerTwgSentinel

/-! ## The concrete deploy parameters and gateway storage -/

/-- A concrete locator for the control's gateway instance.  The entry-3 theorem
is quantified over `dp`; this control only needs one member of the family. -/
def controlDeployParams : LidoTriggerableWithdrawalsGateway.DeployParams :=
  ⟨0x800⟩

/-- The gateway's own configuration: unpaused, with the CircuitBreaker holding
the pause role.  These are exactly the role/storage premises the gateway
family's authorization route consumes. -/
def controlGatewayStor : Stor :=
  Blanc.Composition.LidoCircuitBreakerTwg.controlGatewayStor

/-! ## The closed world

Row 19 of the CircuitBreaker's own pause world, with the compiled gateway
runtime in place of the test stub. -/

/-- The finite control storage with only the public duration slot changed to
the all-ones sentinel. -/
def sentinelPauseWorldStor : Stor :=
  pauseLastWorldStor.set pauseDurationSlot pauseInfiniteSentinel

theorem sentinelPauseLastStor_interval :
    sentinelPauseWorldStor.get heartbeatIntervalSlot = pauseWorldInterval := by
  decide +kernel

theorem sentinelPauseLastStor_duration :
    sentinelPauseWorldStor.get pauseDurationSlot = pauseInfiniteSentinel := by
  decide +kernel

theorem sentinelPauseLastStor_length :
    sentinelPauseWorldStor.get arrayLengthSlot = 1 := by
  decide +kernel

theorem sentinelPauseLastStor_entry :
    sentinelPauseWorldStor.get (arrayEntrySlot 1) =
      pauseWorldCallee.toB256 := by
  decide +kernel

theorem sentinelPauseLastStor_assignment :
    sentinelPauseWorldStor.get (assignmentSlot pauseWorldCallee.toB256) =
      pauseWorldPauser := by
  decide +kernel

theorem sentinelPauseLastStor_index :
    sentinelPauseWorldStor.get (indexSlot pauseWorldCallee.toB256) = 1 := by
  decide +kernel

theorem sentinelPauseLastStor_count :
    sentinelPauseWorldStor.get (countSlot pauseWorldPauser) = 1 := by
  decide +kernel

theorem sentinelPauseLastStor_expiry :
    sentinelPauseWorldStor.get (expirySlot pauseWorldPauser) =
      pauseWorldExpiry := by
  decide +kernel

def sentinelGatewayPauseWorldState : State :=
  State.set
    (State.set (.empty : State) configWorldOwner
      { Acct.nil with stor := sentinelPauseWorldStor, code := configWorldCode })
    pauseWorldCallee
      { Acct.nil with
        stor := controlGatewayStor
        code := gatewayCode controlDeployParams }

def sentinelGatewayPauseWorldGas : Nat := 107604

def sentinelGatewayPauseWorldMsg : Msg :=
  { (pauseWorldMsg sentinelPauseWorldStor sentinelGatewayPauseWorldGas) with
    benv :=
      { (pauseWorldMsg sentinelPauseWorldStor sentinelGatewayPauseWorldGas).benv with
        state := sentinelGatewayPauseWorldState
        stat :=
          { (pauseWorldMsg sentinelPauseWorldStor
              sentinelGatewayPauseWorldGas).benv.stat with
            origState := sentinelGatewayPauseWorldState } } }

def sentinelGatewayPauseWorldSevm : Sevm := initSevm sentinelGatewayPauseWorldMsg

def sentinelGatewayPauseWorldPre : Devm := initDevm sentinelGatewayPauseWorldMsg

/-! ## The world's projections -/

theorem sentinelGatewayPauseWorldState_get_breaker :
    sentinelGatewayPauseWorldState.get configWorldOwner =
      { Acct.nil with stor := sentinelPauseWorldStor, code := configWorldCode } := by
  rw [sentinelGatewayPauseWorldState,
    State.get_set_ne _ pauseWorld_callee_ne_owner, State.get_set_self]

theorem sentinelGatewayPauseWorldState_get_target :
    sentinelGatewayPauseWorldState.get pauseWorldCallee =
      { Acct.nil with
        stor := controlGatewayStor
        code := gatewayCode controlDeployParams } := by
  rw [sentinelGatewayPauseWorldState, State.get_set_self]

theorem sentinelGatewayPauseWorld_targetCode :
    sentinelGatewayPauseWorldState.getCode pauseWorldCallee =
      gatewayCode controlDeployParams := by
  show (sentinelGatewayPauseWorldState.get pauseWorldCallee).code = _
  rw [sentinelGatewayPauseWorldState_get_target]

theorem sentinelGatewayPauseWorld_codeBytes :
    sentinelGatewayPauseWorldSevm.code.toList =
      lidoCircuitBreakerCode officialParams := by
  simpa only [sentinelGatewayPauseWorldSevm, sentinelGatewayPauseWorldMsg, initSevm] using
    pauseWorld_msgCode sentinelPauseWorldStor sentinelGatewayPauseWorldGas

theorem sentinelGatewayPauseWorld_currentTarget :
    sentinelGatewayPauseWorldSevm.currentTarget = configWorldOwner := rfl

theorem sentinelGatewayPauseWorld_callerWord :
    sentinelGatewayPauseWorldSevm.caller.toB256 = pauseWorldPauser :=
  pauseWorld_pauserAdr_toB256

theorem sentinelGatewayPauseWorld_getStorVal {key : B256} :
    sentinelGatewayPauseWorldPre.getStorVal configWorldOwner key =
      sentinelPauseWorldStor.get key := by
  change (sentinelGatewayPauseWorldState.get configWorldOwner).stor.get key = _
  rw [sentinelGatewayPauseWorldState_get_breaker]

theorem sentinelGatewayPauseWorld_targetCodeAt :
    CodeAt sentinelGatewayPauseWorldPre pauseWorldCallee
      (gatewayCode controlDeployParams) :=
  sentinelGatewayPauseWorld_targetCode

/-! ## No code facts are discharged here, because none are asked for

Entry 3 carries no code-shape premise.  Non-delegation and a nonempty byte list
follow from the compiler witness; nonzero installed width follows from the
successful run, because the CircuitBreaker's `EXTCODESIZE` guard reverts on the
zero arm.  A world-local restatement of any of them would be dead weight. -/

theorem sentinelGatewayPauseWorld_target_ne_owner :
    pauseWorldCallee.toB256.toAdr ≠ sentinelGatewayPauseWorldSevm.currentTarget := by
  rw [toAdr_toB256, sentinelGatewayPauseWorld_currentTarget]
  exact pauseWorld_callee_ne_owner

theorem sentinelGatewayPauseWorld_target_not_precompile :
    sentinelGatewayPauseWorldSevm.benvStat.rules.isPrecomp
      pauseWorldCallee.toB256.toAdr = false := by
  rw [toAdr_toB256]
  decide +kernel

/-! ## The complete public-entry premise bundle -/

theorem sentinelGatewayPauseWorld_publicPausePremises :
    PublicPauseEntryPremises sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      configWorldOwner pauseWorldCallee.toB256 pauseInfiniteSentinel 1 1
      pauseWorldCallee.toB256 [] (gatewayCode controlDeployParams) := by
  refine {
    productionBytes := sentinelGatewayPauseWorld_codeBytes
    currentTarget := sentinelGatewayPauseWorld_currentTarget
    codeAddress := rfl
    valueZero := rfl
    dynamic := rfl
    entered := ?_
    image := ?_
    calldata := rfl
    selectorEq := ?_
    targetCanonical := validAdr_toB256 pauseWorldCallee
    targetNonzero := by decide
    callerNonzero := ?_
    unlocked := rfl
    targetCodeAt := ?_
    assigned := ?_
    live := ?_
    durationRead := ?_
    indexRead := ?_
    lengthRead := ?_
    lastRead := ?_
    assignmentCountNe := ?_
    assignmentIndexNe := pauseWorld_assignCallee_ne_indexCallee
    assignmentLengthNe := pauseWorld_length_ne_assignCallee.symm
    assignmentEntryNe := pauseWorld_entryOne_ne_assignCallee.symm
    countRemovedEntryNe := ?_
    countMovedIndexNe := ?_
    countIndexNe := ?_
    countLengthNe := ?_
    countEntryNe := ?_
  }
  · decide
  · unfold MemImage
    exact ⟨Mem.wf_empty, Mem.reads_empty⟩
  · have dataEq : sentinelGatewayPauseWorldSevm.data =
        (pauseWorldSevm sentinelPauseWorldStor sentinelGatewayPauseWorldGas).data := by
      change sentinelGatewayPauseWorldMsg.data =
        (pauseWorldMsg sentinelPauseWorldStor sentinelGatewayPauseWorldGas).data
      rfl
    have selectorEq : Sevm.selector sentinelGatewayPauseWorldSevm =
        Sevm.selector
          (pauseWorldSevm sentinelPauseWorldStor sentinelGatewayPauseWorldGas) := by
      unfold Sevm.selector Sevm.dataWord
      rw [dataEq]
    exact selectorEq.trans
      (pauseWorld_selector sentinelPauseWorldStor sentinelGatewayPauseWorldGas)
  · rw [sentinelGatewayPauseWorld_callerWord]
    decide
  · rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from
      toAdr_toB256 pauseWorldCallee]
    exact sentinelGatewayPauseWorld_targetCodeAt
  · rw [sentinelGatewayPauseWorld_currentTarget, sentinelGatewayPauseWorld_callerWord,
      sentinelGatewayPauseWorld_getStorVal, sentinelPauseLastStor_assignment]
  · rw [sentinelGatewayPauseWorld_currentTarget, sentinelGatewayPauseWorld_callerWord,
      sentinelGatewayPauseWorld_getStorVal, sentinelPauseLastStor_expiry]
    decide
  · rw [sentinelGatewayPauseWorld_currentTarget, sentinelGatewayPauseWorld_getStorVal,
      sentinelPauseLastStor_duration]
  · rw [sentinelGatewayPauseWorld_currentTarget, sentinelGatewayPauseWorld_getStorVal,
      sentinelPauseLastStor_index]
  · rw [sentinelGatewayPauseWorld_currentTarget, sentinelGatewayPauseWorld_getStorVal,
      sentinelPauseLastStor_length]
  · rw [sentinelGatewayPauseWorld_currentTarget, sentinelGatewayPauseWorld_getStorVal,
      sentinelPauseLastStor_entry]
  · rw [sentinelGatewayPauseWorld_callerWord]
    exact pauseWorld_assignCallee_ne_count
  · rw [sentinelGatewayPauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm
  · rw [sentinelGatewayPauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · rw [sentinelGatewayPauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · rw [sentinelGatewayPauseWorld_callerWord]
    exact pauseWorld_length_ne_count.symm
  · rw [sentinelGatewayPauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm

/-! ## Every entry-3 premise except reachability

This is the exact residual: hand it any successful production run of this world
and entry 3's conclusion follows, with no further hypothesis. -/

theorem sentinelGatewayPauseWorld_closedPremises
    {ex : Execution} {final : Devm}
    (publicRun : Prog.RunCompiledTo sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
      (runtime officialParams) ex)
    (success : ex = .ok final) :
    PublicPausePinnedTargetConclusion sentinelGatewayPauseWorldSevm
      sentinelGatewayPauseWorldPre pauseWorldCallee.toB256 pauseInfiniteSentinel
      (gatewayCode controlDeployParams)
      (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
      LidoTriggerableWithdrawalsGateway.pausedUntil ex final :=
  publicPause_gatewayPinnedTarget sentinelGatewayPauseWorld_publicPausePremises
    sentinelGatewayPauseWorld_target_ne_owner sentinelGatewayPauseWorld_target_not_precompile
    publicRun success

/-! ## Falsifiers

Entry 3 has no code-shape premise left to refute, so there is deliberately no
delegation or empty-code mutant here: a mutant needs a hypothesis to falsify,
and both hypotheses are now consequences of the compiler witness and the
successful run. What remains falsifiable is the ABI agreement, which is a real
check between two independently defined encoders rather than a derived fact. -/

/-- **ABI independence.**  The two families define their selectors on separate
evidence — the CircuitBreaker computes `selector "pauseFor" [.uint256]`, the
gateway carries the census-derived literal — so the C2 agreement is a real
check.  Substituting the gateway's *other* public selector makes the two
calldata builders disagree at every duration, which is what a genuine check
looks like and what a tautology could not exhibit. -/
theorem pauseForSelector_ne_triggerSelector :
    LidoCircuitBreaker.pauseForSelector ≠
      LidoTriggerableWithdrawalsGateway.selTriggerFullWithdrawals := by
  decide +kernel

theorem isPausedSelector_ne_pauseForSelector :
    LidoCircuitBreaker.isPausedSelector ≠
      LidoTriggerableWithdrawalsGateway.selPauseFor := by
  decide +kernel

end LidoCircuitBreakerTwgSentinel

end Blanc.Composition
