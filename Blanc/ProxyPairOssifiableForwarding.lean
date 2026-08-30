import Blanc.ProxyPairOssifiableProgram
import Blanc.DelegatecallEnvelope
import Blanc.ExecutionMessageEffects
import Blanc.MessageExecution

/-!
# Generic forwarding envelope for OssifiableProxy

The child named here is the exact message spawned by the runtime's
`DELEGATECALL`.  The wrapper observation deliberately omits gas and warm-set
bookkeeping.  Moving an implementation property from an ordinary direct call
to this child remains the separate `DirectTargetTransport` obligation from
`Blanc.DelegatecallEnvelope`.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- The compiler table in which the runtime fallback executes. -/
def ossifiableRuntimeFunctions : List Func :=
  runtimeBaseline.main :: runtimeBaseline.aux

/-- The state immediately after a clean delegated child is resumed. -/
def forwardingCleanResume
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm) : Devm :=
  (((incorporateChildOnSuccess d.parent child child.output).setMach
      ⟨1 :: d.parent.stack, d.parent.memory,
        d.parent.gasLeft + child.gasLeft⟩).memWrite
    d.outputOffsetWord.toNat (child.output.take d.outputSizeWord.toNat))

/-- The state immediately after a settled failing child is resumed. -/
def forwardingFailedResume
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) (child : Devm) : Devm :=
  (((incorporateChildOnError d.parent child child.output).setMach
      ⟨0 :: d.parent.stack, d.parent.memory,
        d.parent.gasLeft + child.gasLeft⟩).memWrite
    d.outputOffsetWord.toNat (child.output.take d.outputSizeWord.toNat))

/-- Memory left after the forwarding tail copies and reads the complete child
output at offset zero. -/
def forwardingCopiedMemory (resume : Devm) (output : Bytes) : Mem :=
  ((resume.memory.write 0 output).read 0 output.length).2

/-- Exact frame-local gas charged by the successful returndata tail. -/
def forwardingCleanTailCost (resume : Devm) : Nat :=
  30 + gReturnDataCopy * ceilDiv resume.returnData.length 32 +
    resume.extCost [⟨0, resume.returnData.length⟩]

/-- Exact frame-local gas charged by the reverting returndata tail. -/
def forwardingFailedTailCost (resume : Devm) : Nat :=
  29 + gReturnDataCopy * ceilDiv resume.returnData.length 32 +
    resume.extCost [⟨0, resume.returnData.length⟩]

/-- Exact clean raw endpoint of the wrapper tail. -/
def forwardingCleanPost
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) : Devm :=
  ((forwardingCleanResume d child).setMach
      ⟨d.parent.stack, forwardingCopiedMemory
        (forwardingCleanResume d child) child.output, gas⟩).withOutput
    child.output

/-- Exact reverting raw endpoint of the wrapper tail. -/
def forwardingFailedPost
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) : Devm :=
  ((forwardingFailedResume d child).setMach
      ⟨d.parent.stack, forwardingCopiedMemory
        (forwardingFailedResume d child) child.output, gas⟩).withOutput
    child.output

@[simp] theorem forwardingCleanPost_error
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).error = d.parent.error := rfl

@[simp] theorem forwardingCleanPost_output
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).output = child.output := rfl

@[simp] theorem forwardingCleanPost_logs
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).logs =
      d.parent.logs ++ child.logs := rfl

@[simp] theorem forwardingCleanPost_state
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).state = child.state := rfl

@[simp] theorem forwardingCleanPost_transientStorage
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingCleanPost d child gas).transientStorage =
      child.transientStorage := rfl

@[simp] theorem forwardingFailedPost_output
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingFailedPost d child gas).output = child.output := rfl

@[simp] theorem forwardingFailedPost_logs
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (gas : Nat) :
    (forwardingFailedPost d child gas).logs = d.parent.logs := rfl

/-- Proof that the exact compiled returndata tail has enough gas to finish.
It names only a compiled tail execution, never the outer message result. -/
inductive ForwardingTailRun
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) : Type
  | clean
      (status : child.error.isSome = false)
      (gas : Nat)
      (budget : (forwardingCleanResume d child).gasLeft =
        gas + forwardingCleanTailCost (forwardingCleanResume d child))
      (run : Func.RunCompiledTo ossifiableRuntimeFunctions sevm
        (forwardingCleanResume d child) proxyReturnTail
        (.ok (forwardingCleanPost d child gas))) :
      ForwardingTailRun d child
  | failed
      (status : child.error.isSome = true)
      (gas : Nat)
      (budget : (forwardingFailedResume d child).gasLeft =
        gas + forwardingFailedTailCost (forwardingFailedResume d child))
      (run : Func.RunCompiledTo ossifiableRuntimeFunctions sevm
        (forwardingFailedResume d child) proxyReturnTail
        (.error (.revert, forwardingFailedPost d child gas))) :
      ForwardingTailRun d child

/-- Frame facts established by the runtime prefix before the exact
`DELEGATECALL`.  Storage is compared with the outer message's saved world
because a payable entry transfer may have changed balances but not storage. -/
structure ForwardingSettlementContext
    (outer : Msg)
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre) : Prop where
  owner : sevm.currentTarget = outer.currentTarget
  parentStackRoom : d.parent.stack.length < 1024
  parentError : d.parent.error = none
  parentLogs : d.parent.logs = []
  parentStorage : MessageStorageEqualAt outer.currentTarget
    d.parent.state outer.benv.state
  parentTransient : MessageTransientEqualAt outer.currentTarget
    d.parent.transientStorage outer.tenv.transientStorage

private theorem clean_tail_relation
    (outer : Msg)
    {sevm : Sevm} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor sevm callPre}
    (context : ForwardingSettlementContext outer d)
    (child : Devm) (status : child.error.isSome = false) (gas : Nat) :
    ChildToWrapperSettledAt outer.currentTarget (.ok child)
      ((Frame.ofCall outer).settle
        (.ok (forwardingCleanPost d child gas))) := by
  have statusNone : child.error.isNone = true := by
    cases h : child.error <;> simp_all
  have statusEq : child.error = none := by
    cases h : child.error <;> simp_all
  have finalError : (forwardingCleanPost d child gas).error = none := by
    rw [forwardingCleanPost_error, context.parentError]
  have settledEq :
      (Frame.ofCall outer).settle
          (.ok (forwardingCleanPost d child gas)) =
        .ok (forwardingCleanPost d child gas) := by
    simp only [Frame.ofCall, Frame.settle, Frame.settleMsg,
      executeCode.handleError, processMessage.settle]
    change (if (forwardingCleanPost d child gas).error.isSome = true then
      Except.ok ((forwardingCleanPost d child gas).rollback
        outer.benv.state outer.tenv.transientStorage)
      else Except.ok (forwardingCleanPost d child gas)) =
        Except.ok (forwardingCleanPost d child gas)
    rw [finalError]
    rfl
  rw [settledEq]
  change ChildToWrapperOkAt outer.currentTarget child _
  refine {
    status := by
      rw [statusEq, forwardingCleanPost_error, context.parentError]
      exact DelegatecallStatusRelated.clean
    output := forwardingCleanPost_output d child gas
    logs := by
      rw [forwardingCleanPost_logs, context.parentLogs]
      simp [statusNone]
    storage := by
      intro key
      rw [forwardingCleanPost_state]
    transientStorage := by
      intro key
      rw [forwardingCleanPost_transientStorage] }

private theorem failed_tail_relation
    (outer : Msg)
    {sevm : Sevm} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor sevm callPre}
    (context : ForwardingSettlementContext outer d)
    (child : Devm)
    (certificate : DelegatedChildCertificate d.child (.ok child))
    (status : child.error.isSome = true) (gas : Nat) :
    ChildToWrapperSettledAt outer.currentTarget (.ok child)
      ((Frame.ofCall outer).settle
        (.error (.revert, forwardingFailedPost d child gas))) := by
  have childRollback := ProcessMessage.rollback_of_error
    certificate.process (by simpa [status])
  have statusNone : child.error.isNone = false := by
    cases h : child.error <;> simp_all
  have settledEq :
      (Frame.ofCall outer).settle
          (.error (.revert, forwardingFailedPost d child gas)) =
        .ok (MessageExecution.settledRevert outer
          (forwardingFailedPost d child gas)) := rfl
  rw [settledEq]
  change ChildToWrapperOkAt outer.currentTarget child _
  refine {
    status := DelegatecallStatusRelated.failed status
    output := by
      rw [MessageExecution.settledRevert_output,
        forwardingFailedPost_output]
    logs := by
      rw [MessageExecution.settledRevert_logs,
        forwardingFailedPost_logs, context.parentLogs]
      simp [statusNone]
    storage := by
      intro key
      rw [childRollback.1]
      exact context.parentStorage key
    transientStorage := by
      intro key
      rw [childRollback.2]
      exact context.parentTransient key }

/-- At the exact call site, an explicitly certified arbitrary child execution
is wrapped with the proxy's status, returndata, log, and proxy-owned storage
semantics.  The fatal non-consensus channel propagates without entering the
tail; settled child failures take the ordinary wrapper `REVERT` arm. -/
theorem forwarding_atCall_execSat
    (outer : Msg)
    {sevm : Sevm} {callPre : Devm}
    (d : DelegatecallSpawnDescriptor sevm callPre)
    (context : ForwardingSettlementContext outer d)
    (childOut : MessageResult)
    (tail : match childOut with
      | .ok child => ForwardingTailRun d child
      | .error _ => PUnit)
    (certificate : DelegatedChildCertificate d.child childOut) :
    Func.ExecSat ossifiableRuntimeFunctions sevm callPre
      (delcall ::: proxyReturnTail)
      (fun raw => ChildToWrapperSettledAt outer.currentTarget childOut
        ((Frame.ofCall outer).settle raw)) := by
  have childEnter := d.crossing.1
  have childResult :
      (Frame.ofCall d.child).settle (exec (initEvm d.child)) = childOut := by
    rw [← MessageExecution.processMessage_eq_settle_exec_of_enter
      d.child (initEvm d.child) childEnter]
    exact certificate.result
  cases childOut with
  | error failure =>
      rcases failure with ⟨error, state, created, tra⟩
      have resume : d.resume.run
          ((Frame.ofCall d.child).settle (exec (initEvm d.child))) =
          .error (error,
            (d.parent.withCreatedAccounts created).setWorld
              {d.parent.world with state := state, transientStorage := tra}) := by
        rw [childResult]
        rfl
      apply Func.execSat_next_error
        (Ninst.stepRun_exec_run_error d.step childEnter resume)
      have childNonConsensus : NonConsensus error := by
        exact handleError_error_inv
          (Frame.settle_error_inv (f := Frame.ofCall d.child) rfl childResult)
      have outerResult :
          (Frame.ofCall outer).settle
            (.error (error,
              (d.parent.withCreatedAccounts created).setWorld
                {d.parent.world with state := state, transientStorage := tra})) =
            .error (error, state, created, tra) := by
        cases error with
        | halt reason => exact (childNonConsensus (.halt reason) rfl).elim
        | revert => exact (childNonConsensus .revert rfl).elim
        | crypto reason => rfl
        | internal reason => rfl
      rw [outerResult]
      exact ⟨rfl, (fun _ => rfl), (fun _ => rfl)⟩
  | ok child =>
      cases tail with
      | clean status gas budget tailRun =>
          have resume : d.resume.run
              ((Frame.ofCall d.child).settle (exec (initEvm d.child))) =
              .ok (forwardingCleanResume d child) := by
            rw [childResult]
            simpa [DelegatecallSpawnDescriptor.resume,
              forwardingCleanResume] using
              (Resume.run_call_ok status context.parentStackRoom)
          have callRun : Ninst.RunCompiled sevm callPre
              (.exec .delcall) (forwardingCleanResume d child) :=
            Ninst.runCompiled_exec_run d.step childEnter resume
          apply Func.execSat_of_runCompiledTo
            (Func.RunCompiledTo.next callRun tailRun)
          exact clean_tail_relation outer context child status gas
      | failed status gas budget tailRun =>
          have resume : d.resume.run
              ((Frame.ofCall d.child).settle (exec (initEvm d.child))) =
              .ok (forwardingFailedResume d child) := by
            rw [childResult]
            simpa [DelegatecallSpawnDescriptor.resume,
              forwardingFailedResume] using
              (Resume.run_call_err status context.parentStackRoom)
          have callRun : Ninst.RunCompiled sevm callPre
              (.exec .delcall) (forwardingFailedResume d child) :=
            Ninst.runCompiled_exec_run d.step childEnter resume
          apply Func.execSat_of_runCompiledTo
            (Func.RunCompiledTo.next callRun tailRun)
          exact failed_tail_relation outer context child certificate status gas

/-- Exact outer-runtime route to the named delegatecall descriptor.  The
`prefix` transformer is execution evidence, not an assumed wrapper result. -/
structure OssifiableForwardingRoute
    (outer : Msg) (afterTransfer : Benv)
    (callPre : Devm)
    (d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre) : Prop where
  transfer : outer.benvAfterTransfer = .ok afterTransfer
  outerEntry : (Frame.ofCall outer).enter =
    .run (initEvm (outer.withBenv afterTransfer))
  target : outer.target = some outer.currentTarget
  codeAddress : outer.codeAddress = some outer.currentTarget
  runtimeInstalled : outer.code = runtimeBaselineCode
  runtimeCodeLink : outer.code =
    (outer.benv.state.get outer.currentTarget).code
  selectorMiss : ∀ selector ∈ runtimeSelectors,
    selector ≠ Sevm.selector (initSevm (outer.withBenv afterTransfer))
  implementationSlotValue :
    (afterTransfer.state.get outer.currentTarget).stor.get
      implementationSlot = d.codeWord.toAdr.toB256
  descriptorCode :
    d.code = afterTransfer.state.getCode d.resolvedCodeAddress
  executedCodeNonempty : d.code.toList ≠ []
  inputOffset : d.inputOffsetWord = 0
  inputSize : d.inputSizeWord.toNat = outer.data.length
  outputOffset : d.outputOffsetWord = 0
  outputSize : d.outputSizeWord = 0
  emptyTail : d.stackTail = []
  directContext : DirectToDelegatedContext outer
    (directTargetMessage outer d.codeWord.toAdr
      d.resolvedCodeAddress d.code) d
  settlement : ForwardingSettlementContext outer d
  compileLink : some
    (initSevm (outer.withBenv afterTransfer)).code.toList =
      Prog.compile runtimeBaseline
  compiledPrefix : ∀ raw,
    Func.ExecWitness ossifiableRuntimeFunctions
        (initSevm (outer.withBenv afterTransfer)) callPre
        (delcall ::: proxyReturnTail) raw →
      Prog.ExecWitness (initSevm (outer.withBenv afterTransfer))
        (initDevm (outer.withBenv afterTransfer)) runtimeBaseline raw

/-- The implementation-specific property transport left deliberately open by
the generic envelope.  Its context is the exact direct/delegated delta carried
by the runtime route, not an asserted message-result equivalence. -/
def OssifiableForwardingRoute.transportObligation
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d)
    (P : Msg → MessageResult → Prop) : Prop :=
  DirectTargetTransport P route.directContext

/-- The exact delegated child retains the proxy as storage owner and records
the descriptor's EIP-150 gas, depth, access, transfer, and code context. -/
theorem OssifiableForwardingRoute.childContext
    {outer : Msg} {afterTransfer : Benv} {callPre : Devm}
    {d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre}
    (route : OssifiableForwardingRoute outer afterTransfer callPre d) :
    d.child.currentTarget = outer.currentTarget ∧
      d.child.codeAddress = some d.resolvedCodeAddress ∧
      d.child.gas = d.childGas ∧
      d.child.depth = outer.depth - 1 ∧
      d.child.accessedAddresses = d.parent.accessedAddresses ∧
      d.child.accessedStorageKeys = d.parent.accessedStorageKeys ∧
      d.child.shouldTransferValue = false ∧
      d.child.code = d.code := by
  exact ⟨by rfl, rfl, rfl, by rfl, rfl, rfl, rfl, rfl⟩

/-- Reusable account-altitude forwarding envelope for the complete runtime.
The exact child execution is an input certificate; the outer result is an
existential conclusion derived from compiled execution and message settlement.
Gas and warm-set equality are intentionally absent from the observation. -/
theorem processMessage_forwardingEnvelope
    (outer : Msg) (afterTransfer : Benv)
    (callPre : Devm)
    (d : DelegatecallSpawnDescriptor
      (initSevm (outer.withBenv afterTransfer)) callPre)
    (route : OssifiableForwardingRoute outer afterTransfer callPre d)
    (childOut : MessageResult)
    (tail : match childOut with
      | .ok child => ForwardingTailRun d child
      | .error _ => PUnit)
    (certificate : DelegatedChildCertificate d.child childOut) :
    ∃ wrapperOut,
      processMessage outer = wrapperOut ∧
        ChildToWrapperSettledAt outer.currentTarget childOut wrapperOut := by
  let P : Execution → Prop := fun raw =>
    ChildToWrapperSettledAt outer.currentTarget childOut
      ((Frame.ofCall outer).settle raw)
  have atCall : Func.ExecSat ossifiableRuntimeFunctions
      (initSevm (outer.withBenv afterTransfer)) callPre
      (delcall ::: proxyReturnTail) P :=
    forwarding_atCall_execSat outer d route.settlement childOut
      tail certificate
  rcases atCall with ⟨raw, rawWitness, observation⟩
  have program : Prog.ExecSat
      (initSevm (outer.withBenv afterTransfer))
      (initDevm (outer.withBenv afterTransfer)) runtimeBaseline P :=
    ⟨raw, route.compiledPrefix raw rawWitness, observation⟩
  have executed : P (exec (initEvm (outer.withBenv afterTransfer))) := by
    exact Prog.execSat_out program route.compileLink
  refine ⟨(Frame.ofCall outer).settle
      (exec (initEvm (outer.withBenv afterTransfer))), ?_, executed⟩
  exact MessageExecution.processMessage_eq_settle_exec_of_enter
    outer (initEvm (outer.withBenv afterTransfer)) route.outerEntry

end Blanc.ProxyPair
