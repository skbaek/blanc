import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGateway
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

`gatewayPauseWorld_closedPremises` isolates the public theorem's premise
closure.  The companion `LidoCircuitBreakerTriggerableWithdrawalsGatewayControlRun`
module constructs the production run itself from this exact world, using the
real gateway boundary walk and its derived gas schedule.
-/

namespace Blanc.Composition

open Jaune
open Blanc
open Blanc.LidoCircuitBreaker
open Blanc.Composition.LidoCircuitBreakerTwg

namespace LidoCircuitBreakerTwg

/-! ## The concrete deploy parameters and gateway storage -/

/-- A concrete locator for the control's gateway instance.  The entry-3 theorem
is quantified over `dp`; this control only needs one member of the family. -/
def controlDeployParams : LidoTriggerableWithdrawalsGateway.DeployParams :=
  ⟨0x800⟩

/-- The gateway's own configuration: unpaused, with the CircuitBreaker holding
the pause role.  These are exactly the role/storage premises the gateway
family's authorization route consumes. -/
def controlGatewayStor : Stor :=
  ((((Stor.empty : Stor).set LidoTriggerableWithdrawalsGateway.resumeSinceSlot
            0).set
        (LidoTriggerableWithdrawalsGateway.roleLookupIndexSlot
          LidoTriggerableWithdrawalsGateway.pauseRole
          configWorldOwner.toB256) 1).set
      (LidoTriggerableWithdrawalsGateway.roleLookupRoleSlot
        LidoTriggerableWithdrawalsGateway.pauseRole configWorldOwner.toB256)
      LidoTriggerableWithdrawalsGateway.pauseRole).set
    (LidoTriggerableWithdrawalsGateway.roleLookupAccountSlot
      LidoTriggerableWithdrawalsGateway.pauseRole configWorldOwner.toB256)
    configWorldOwner.toB256

/-! ## The closed world

Row 19 of the CircuitBreaker's own pause world, with the compiled gateway
runtime in place of the test stub. -/

def gatewayPauseWorldState : State :=
  State.set
    (State.set (.empty : State) configWorldOwner
      { Acct.nil with stor := pauseLastWorldStor, code := configWorldCode })
    pauseWorldCallee
      { Acct.nil with
        stor := controlGatewayStor
        code := gatewayCode controlDeployParams }

def gatewayPauseWorldGas : Nat := 107635

def gatewayPauseWorldMsg : Msg :=
  { (pauseWorldMsg pauseLastWorldStor gatewayPauseWorldGas) with
    benv :=
      { (pauseWorldMsg pauseLastWorldStor gatewayPauseWorldGas).benv with
        state := gatewayPauseWorldState
        stat :=
          { (pauseWorldMsg pauseLastWorldStor
              gatewayPauseWorldGas).benv.stat with
            origState := gatewayPauseWorldState } } }

def gatewayPauseWorldSevm : Sevm := initSevm gatewayPauseWorldMsg

def gatewayPauseWorldPre : Devm := initDevm gatewayPauseWorldMsg

/-! ## The world's projections -/

theorem gatewayPauseWorldState_get_breaker :
    gatewayPauseWorldState.get configWorldOwner =
      { Acct.nil with stor := pauseLastWorldStor, code := configWorldCode } := by
  rw [gatewayPauseWorldState,
    State.get_set_ne _ pauseWorld_callee_ne_owner, State.get_set_self]

theorem gatewayPauseWorldState_get_target :
    gatewayPauseWorldState.get pauseWorldCallee =
      { Acct.nil with
        stor := controlGatewayStor
        code := gatewayCode controlDeployParams } := by
  rw [gatewayPauseWorldState, State.get_set_self]

theorem gatewayPauseWorld_targetCode :
    gatewayPauseWorldState.getCode pauseWorldCallee =
      gatewayCode controlDeployParams := by
  show (gatewayPauseWorldState.get pauseWorldCallee).code = _
  rw [gatewayPauseWorldState_get_target]

theorem gatewayPauseWorld_codeBytes :
    gatewayPauseWorldSevm.code.toList =
      lidoCircuitBreakerCode officialParams := by
  simpa only [gatewayPauseWorldSevm, gatewayPauseWorldMsg, initSevm] using
    pauseWorld_msgCode pauseLastWorldStor gatewayPauseWorldGas

theorem gatewayPauseWorld_currentTarget :
    gatewayPauseWorldSevm.currentTarget = configWorldOwner := rfl

theorem gatewayPauseWorld_callerWord :
    gatewayPauseWorldSevm.caller.toB256 = pauseWorldPauser :=
  pauseWorld_pauserAdr_toB256

theorem gatewayPauseWorld_getStorVal {key : B256} :
    gatewayPauseWorldPre.getStorVal configWorldOwner key =
      pauseLastWorldStor.get key := by
  change (gatewayPauseWorldState.get configWorldOwner).stor.get key = _
  rw [gatewayPauseWorldState_get_breaker]

theorem gatewayPauseWorld_targetCodeAt :
    CodeAt gatewayPauseWorldPre pauseWorldCallee
      (gatewayCode controlDeployParams) :=
  gatewayPauseWorld_targetCode

/-! ## No code facts are discharged here, because none are asked for

Entry 3 carries no code-shape premise.  Non-delegation and a nonempty byte list
follow from the compiler witness; nonzero installed width follows from the
successful run, because the CircuitBreaker's `EXTCODESIZE` guard reverts on the
zero arm.  A world-local restatement of any of them would be dead weight. -/

theorem gatewayPauseWorld_target_ne_owner :
    pauseWorldCallee.toB256.toAdr ≠ gatewayPauseWorldSevm.currentTarget := by
  rw [toAdr_toB256, gatewayPauseWorld_currentTarget]
  exact pauseWorld_callee_ne_owner

theorem gatewayPauseWorld_target_not_precompile :
    gatewayPauseWorldSevm.benvStat.rules.isPrecomp
      pauseWorldCallee.toB256.toAdr = false := by
  rw [toAdr_toB256]
  decide +kernel

/-! ## The complete public-entry premise bundle -/

theorem gatewayPauseWorld_publicPausePremises :
    PublicPauseEntryPremises gatewayPauseWorldSevm gatewayPauseWorldPre
      configWorldOwner pauseWorldCallee.toB256 pauseWorldDuration 1 1
      pauseWorldCallee.toB256 [] (gatewayCode controlDeployParams) := by
  refine {
    productionBytes := gatewayPauseWorld_codeBytes
    currentTarget := gatewayPauseWorld_currentTarget
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
  · have dataEq : gatewayPauseWorldSevm.data =
        (pauseWorldSevm pauseLastWorldStor gatewayPauseWorldGas).data := by
      change gatewayPauseWorldMsg.data =
        (pauseWorldMsg pauseLastWorldStor gatewayPauseWorldGas).data
      rfl
    have selectorEq : Sevm.selector gatewayPauseWorldSevm =
        Sevm.selector
          (pauseWorldSevm pauseLastWorldStor gatewayPauseWorldGas) := by
      unfold Sevm.selector Sevm.dataWord
      rw [dataEq]
    exact selectorEq.trans
      (pauseWorld_selector pauseLastWorldStor gatewayPauseWorldGas)
  · rw [gatewayPauseWorld_callerWord]
    decide
  · rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from
      toAdr_toB256 pauseWorldCallee]
    exact gatewayPauseWorld_targetCodeAt
  · rw [gatewayPauseWorld_currentTarget, gatewayPauseWorld_callerWord,
      gatewayPauseWorld_getStorVal, pauseLastStor_assignment]
  · rw [gatewayPauseWorld_currentTarget, gatewayPauseWorld_callerWord,
      gatewayPauseWorld_getStorVal, pauseLastStor_expiry]
    decide
  · rw [gatewayPauseWorld_currentTarget, gatewayPauseWorld_getStorVal,
      pauseLastStor_duration]
  · rw [gatewayPauseWorld_currentTarget, gatewayPauseWorld_getStorVal,
      pauseLastStor_index]
  · rw [gatewayPauseWorld_currentTarget, gatewayPauseWorld_getStorVal,
      pauseLastStor_length]
  · rw [gatewayPauseWorld_currentTarget, gatewayPauseWorld_getStorVal,
      pauseLastStor_entry]
  · rw [gatewayPauseWorld_callerWord]
    exact pauseWorld_assignCallee_ne_count
  · rw [gatewayPauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm
  · rw [gatewayPauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · rw [gatewayPauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · rw [gatewayPauseWorld_callerWord]
    exact pauseWorld_length_ne_count.symm
  · rw [gatewayPauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm

/-! ## Every entry-3 premise except reachability

This is the exact residual: hand it any successful production run of this world
and entry 3's conclusion follows, with no further hypothesis. -/

theorem gatewayPauseWorld_closedPremises
    {ex : Execution} {final : Devm}
    (publicRun : Prog.RunCompiledTo gatewayPauseWorldSevm gatewayPauseWorldPre
      (runtime officialParams) ex)
    (success : ex = .ok final) :
    PublicPausePinnedTargetConclusion gatewayPauseWorldSevm
      gatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldDuration
      (gatewayCode controlDeployParams)
      (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
      LidoTriggerableWithdrawalsGateway.pausedUntil ex final :=
  publicPause_gatewayPinnedTarget gatewayPauseWorld_publicPausePremises
    gatewayPauseWorld_target_ne_owner gatewayPauseWorld_target_not_precompile
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

end LidoCircuitBreakerTwg

end Blanc.Composition
