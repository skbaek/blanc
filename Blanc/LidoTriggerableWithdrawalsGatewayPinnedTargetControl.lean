import Blanc.LidoTriggerableWithdrawalsGateway
import Blanc.PinnedPauseTarget

/-!
# Executable full-runtime controls for the TWG pinned-pause target

This test-scoped module installs the complete compiled
`LidoTriggerableWithdrawalsGateway.runtime` in one concrete account world.  It
then executes an authorized infinite `pauseFor` message followed by an
`isPaused` query against the pause message's settled state.

The second program below is also a complete TWG runtime.  It changes only the
first selector body's infinite-pause arm: instead of preserving the all-ones
sentinel it stores the unchecked wrapping sum `timestamp + sentinel`.  At the
fixed timestamp `10` that word is `9`, and the following query returns false.
All remaining selector entries and the complete auxiliary table are inherited
from the production runtime.

The `Option` values in this file are executable regression controls, not
theorem evidence: each can return `none`, the production predicate checks both
clean executions and code preservation, and the mutant is rejected solely by
its clean clause-(i) storage mismatch.  They therefore supply the finite
anti-vacuity and measurable-bite channel for the separately source-derived A3
bundle theorem.  This module deliberately contains no `Nonempty` theorem, no
`Exec` reflected from evaluator output, and no `PinnedPauseTarget` instance or
negation; the quantified proof remains in the family-owned pinned-target
module.
-/

namespace Blanc.LidoTriggerableWithdrawalsGateway.PinnedTargetControl

open Jaune
open Jaune.Ninst Ninst

/-! ## Concrete addresses and calldata -/

def controlParams : DeployParams := ⟨0x800⟩

def controlCircuitBreaker : Adr := 0x600

def controlTarget : Adr := 0x700

def controlTime : B256 := 10

def controlDuration : B256 := pauseInfinitely

def controlGas : Nat := 200000

def controlPauseCalldata (duration : B256) : Bytes :=
  abiSelectorBytes selPauseFor ++ duration.toBytes

def controlQueryCalldata : Bytes :=
  abiSelectorBytes selIsPaused

def controlPausedUntil (_target : Adr) (stor : Stor) : B256 :=
  stor.get resumeSinceSlot

def controlProtectedSurface : List B256 :=
  [selTriggerFullWithdrawals]

/-! ## Installed role and program world -/

def controlInitialStor : Stor :=
  ((((Stor.empty : Stor).set resumeSinceSlot 0).set
        (roleLookupIndexSlot pauseRole controlCircuitBreaker.toB256) 1).set
      (roleLookupRoleSlot pauseRole controlCircuitBreaker.toB256) pauseRole).set
    (roleLookupAccountSlot pauseRole controlCircuitBreaker.toB256)
    controlCircuitBreaker.toB256

/-- A non-nil caller account makes the transfer-enabled zero-value entry an
identity without identifying the CircuitBreaker and target addresses. -/
def controlCircuitBreakerAcct : Acct :=
  { Acct.nil with bal := 1 }

def controlTargetAcct (code : ByteArray) : Acct :=
  { Acct.nil with stor := controlInitialStor, code := code }

def controlState (code : ByteArray) : State :=
  State.set
    (State.set (.empty : State) controlCircuitBreaker controlCircuitBreakerAcct)
    controlTarget (controlTargetAcct code)

def controlBenv (state : State) : Benv :=
  { (default : Benv) with
    state := state
    stat :=
      { (default : BenvStat) with
        origState := state
        time := controlTime } }

def controlPauseMsg (code : ByteArray) : Msg :=
  { (default : Msg) with
    benv := controlBenv (controlState code)
    caller := controlCircuitBreaker
    target := some controlTarget
    currentTarget := controlTarget
    gas := controlGas
    value := 0
    data := controlPauseCalldata controlDuration
    codeAddress := some controlTarget
    code := code
    depth := 0
    shouldTransferValue := true
    isStatic := false
    disablePrecompiles := true }

def controlQueryMsg (code : ByteArray) (state : State) : Msg :=
  { (default : Msg) with
    benv := controlBenv state
    caller := controlCircuitBreaker
    target := some controlTarget
    currentTarget := controlTarget
    gas := controlGas
    value := 0
    data := controlQueryCalldata
    codeAddress := some controlTarget
    code := code
    depth := 0
    shouldTransferValue := true
    isStatic := true
    disablePrecompiles := true }

/-! ## The complete production program -/

def productionProgram : Prog :=
  runtime controlParams

/-! ## A full-runtime wrapping-add mutant

Only the sentinel body is different.  The finite arm retains the production
overflow check and all dispatch entries after `selPauseFor` are copied from
`funcs controlParams`. -/

def wrappingPauseForSentinel : Func :=
  ([timestamp, pushB256 pauseInfinitely, add,
      pushB256 resumeSinceSlot, sstore] ++
    emitOneWord (signatureHash "Paused" [.uint256]) pauseInfinitely) +++
    Func.stop

def wrappingPauseForUnpaused : Func :=
  (arg 0 ++ [iszero]) +++
    ((.call zeroPauseDurationSlot) <?>
      ((arg 0 ++ [pushB256 pauseInfinitely, eq]) +++
        (wrappingPauseForSentinel <?> pauseForFinite)))

def wrappingPauseFor : Func :=
  requireStaticArgs 1 <| onlyRole pauseRole <|
    ([pushB256 resumeSinceSlot, sload, timestamp, lt, iszero]) +++
      (wrappingPauseForUnpaused <?> .call resumedExpectedSlot)

/-- The production selector table begins with `selPauseFor`.  Replacing that
head and retaining its tail keeps the mutation local and leaves the trigger and
all other public entries intact. -/
def wrappingFuncs (dp : DeployParams) : List (B256 × Func) :=
  (selPauseFor, nonpayable wrappingPauseFor) :: (funcs dp).drop 1

def wrappingRuntimeMain (dp : DeployParams) : Func :=
  pushB256 4 ::: calldatasize ::: lt :::
    (Func.rev <?>
      (fsig +++ linearDispatchWith fallbackSlot (wrappingFuncs dp)))

def wrappingPauseRuntime : Prog :=
  ⟨wrappingRuntimeMain controlParams, aux controlParams⟩

/-! ## Executable pause-then-query observations -/

/-- The two settled dynamic states produced by the executable choreography. -/
structure PauseQueryResult where
  pausePost : Devm
  queryPost : Devm

/-- Enough retained executable data to diagnose the selected program, both
messages, and both settled results.  It intentionally contains no proof fields. -/
structure PauseQueryFixture where
  program : Prog
  code : ByteArray
  pauseMsg : Msg
  queryMsg : Msg
  result : PauseQueryResult

/-- Compile a complete program, install those exact bytes, execute the sentinel
pause, and feed the settled pause state to the static query. -/
def pauseQueryFixtureForProgram? (program : Prog) : Option PauseQueryFixture :=
  match Prog.compile program with
  | none => none
  | some bytes =>
      let code := ByteArray.mk bytes.toArray
      let pauseMsg := controlPauseMsg code
      match processMessage pauseMsg with
      | .error _ => none
      | .ok pausePost =>
          let queryMsg := controlQueryMsg code pausePost.state
          match processMessage queryMsg with
          | .error _ => none
          | .ok queryPost =>
              some
                { program := program
                  code := code
                  pauseMsg := pauseMsg
                  queryMsg := queryMsg
                  result := ⟨pausePost, queryPost⟩ }

def productionPauseQueryFixture? : Option PauseQueryFixture :=
  pauseQueryFixtureForProgram? productionProgram

def wrappingPauseQueryFixture? : Option PauseQueryFixture :=
  pauseQueryFixtureForProgram? wrappingPauseRuntime

def fixtureCodePreserved (fixture : PauseQueryFixture) : Bool :=
  fixture.pauseMsg.benv.state.getCode controlTarget == fixture.code &&
    fixture.result.pausePost.state.getCode controlTarget == fixture.code &&
    fixture.result.queryPost.state.getCode controlTarget == fixture.code

/-- The production acceptance predicate is deliberately stronger than
`AcceptedBoolWord`: this concrete control expects the exact 32-byte canonical
true output in addition to a clean pause and the amended sentinel projection. -/
def productionAcceptance (fixture : PauseQueryFixture) : Bool :=
  fixture.result.pausePost.error.isNone &&
    fixture.result.pausePost.getStorVal controlTarget resumeSinceSlot ==
      pauseForProjection controlTime controlDuration &&
    fixture.result.queryPost.error.isNone &&
    fixture.result.queryPost.output == (1 : B256).toBytes &&
    fixture.result.queryPost.getStorVal controlTarget resumeSinceSlot ==
      pauseForProjection controlTime controlDuration &&
    fixtureCodePreserved fixture

def productionPauseQueryAccepted : Bool :=
  match productionPauseQueryFixture? with
  | none => false
  | some fixture => productionAcceptance fixture

/-- The clause-(i)-specific observation: the clean pause stores the old
unchecked wrapping word, which differs from the amended sentinel projection. -/
def wrappingClauseOneViolationObserved (fixture : PauseQueryFixture) : Bool :=
  fixture.result.pausePost.error.isNone &&
    fixture.result.pausePost.getStorVal controlTarget resumeSinceSlot ==
      controlTime + controlDuration &&
    Bool.not
      (fixture.result.pausePost.getStorVal controlTarget resumeSinceSlot ==
        pauseForProjection controlTime controlDuration) &&
    fixture.result.pausePost.getStorVal controlTarget resumeSinceSlot == 9

/-- The false query is a downstream diagnostic, not the reason the mutant is
rejected by clause (i). -/
def wrappingQueryConsequenceObserved (fixture : PauseQueryFixture) : Bool :=
  fixture.result.queryPost.error.isNone &&
    fixture.result.queryPost.output == (0 : B256).toBytes &&
    fixtureCodePreserved fixture

/-- Optional downstream diagnostic for the wrapping mutant.  This is reported
by the evaluator but is deliberately not part of the biting condition. -/
def wrappingQueryDiagnosticObserved : Bool :=
  match wrappingPauseQueryFixture? with
  | none => false
  | some fixture => wrappingQueryConsequenceObserved fixture

/-- The full-runtime mutant bites solely because its clean pause violates the
clause-(i) projection.  Neither a later query nor failure of the broader
production regression predicate is needed to reject it. -/
def wrappingMutationBites : Bool :=
  match wrappingPauseQueryFixture? with
  | none => false
  | some fixture => wrappingClauseOneViolationObserved fixture

def pinnedTargetExecutableControlsPass : Bool :=
  productionPauseQueryAccepted && wrappingMutationBites

end Blanc.LidoTriggerableWithdrawalsGateway.PinnedTargetControl
