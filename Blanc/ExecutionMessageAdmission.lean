import Blanc.ContractAdmission
import Blanc.ExecutionMessageEffects

/-!
# Trace-local admission through message wrappers

The retained message carriers expose the exact recursive `Exec` selected by
Jaune's deterministic wrappers.  This module attaches an entry-only admission
condition to that concrete execution and transports an arbitrary
`ContractSpec` invariant through call, create, and settled message-call layers.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Admission for the concrete execution retained by a recursive slot.  A
slot-free precompile or entry failure has no interpreter frame to admit. -/
def RetainedXlot.FrameAdmitted {slot : Xlot}
    (trace : RetainedXlot slot) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  match trace with
  | .none => True
  | .some run => Exec.FrameAdmitted ca entry run

/-- Admission for the exact raw call-message core retained by a trace. -/
def ProcessMessageTrace.FrameAdmitted
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  trace.retained.FrameAdmitted ca entry

/-- Admission for the exact raw create-message core retained by a trace. -/
def ProcessCreateMessageTrace.FrameAdmitted
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  trace.retained.FrameAdmitted ca entry

/-- Admission for the only interpreter core, if any, selected by a settled
message-call trace.  Collision-only CREATEs have no core execution. -/
def MessageCallTrace.FrameAdmitted
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  match trace with
  | .createCollision .. => True
  | .createRun _ _ _ _ core _ => core.FrameAdmitted ca entry
  | .callRun _ _ _ _ _ _ _ _ core _ => core.FrameAdmitted ca entry

end ExecutionTrace

namespace ContractSpec

variable {c : ContractSpec}

/-- The trace-admitted counterpart of `StateInv.of_exec_precond`. -/
lemma StateInv.of_exec_precond_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {sevm : Sevm} {pre post : Devm}
    (preserves : c.PreservesAdmitted ca entry)
    (precond : c.Pre ca sevm pre)
    (code : sevm.currentTarget = ca →
      some sevm.code.toList = Prog.compile c.prog)
    (wf : sevm.currentTarget = ca → Mem.Wf pre.memory)
    (run : Exec 0 sevm pre (.ok post))
    (admitted : Exec.FrameAdmitted ca entry run) :
    c.StateInv ca post.state := by
  have postcond : c.Post ca sevm post :=
    preserves sevm pre post run admitted code wf precond
  apply StateInv.of_postcond postcond
  have codeEq : post.getCode ca = pre.getCode ca :=
    code_eq_of_exec run precond.code
  show some (post.state.getCode ca).toList = Prog.compile c.prog
  rw [show post.state.getCode ca = post.getCode ca from rfl, codeEq]
  exact precond.code

end ContractSpec

namespace ExecutionTrace

open ContractSpec

variable {c : ContractSpec}

/-- A successful retained raw message preserves the invariant when every
actual target-frame root in its concrete interpreter run is admitted. -/
theorem ProcessMessageTrace.stateInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (ready : c.MessageRunReady ca msg) :
    c.StateInv ca post.state := by
  rcases trace with ⟨slot, retained, run⟩
  have code : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile c.prog := by
    intro target
    rcases ready.codeOrForeign with targetSome | targetNe
    · exact ready.ready.code targetSome target
    · exact (targetNe target).elim
  obtain ⟨raw, body, settle⟩ := ProcessMessage.iff_body.mp run
  unfold FrameBody at body
  rcases transfer : msg.benvAfterTransfer with error | benv <;>
      rw [transfer] at body
  · rw [body.2, processMessage.settle_error] at settle
    cases settle
  have precond : c.Pre ca
      (initSevm (msg.withBenv benv)) (initDevm (msg.withBenv benv)) :=
    Pre.of_inv_benvAfterTransfer ready.ready.ne ready.ready.val0 transfer
      ready.ready.state
  have code' : (initSevm (msg.withBenv benv)).currentTarget = ca →
      some (initSevm (msg.withBenv benv)).code.toList =
        Prog.compile c.prog := code
  rcases raw with error | evm
  · rw [processMessage.settle_error] at settle
    cases settle
  unfold processMessage.settle at settle
  dsimp only [bind, Except.bind] at settle
  by_cases failed : evm.error.isSome = true
  · rw [if_pos failed] at settle
    rw [Except.ok.inj settle]
    exact ready.ready.state
  · rw [if_neg failed] at settle
    have postEq : evm = post := Except.ok.inj settle.symm
    subst postEq
    rcases of_executeCode_cases body with
      ⟨address, precompile⟩ | ⟨exception, slotEq, handled⟩
    · rw [state_of_executePrecomp_ok precompile failed]
      exact StateInv.of_benvAfterTransfer ready.ready.ne transfer
        ready.ready.state
    · subst slotEq
      cases retained with
      | some execution =>
          have admitted' : Exec.FrameAdmitted ca entry execution := by
            simpa [ExecutionTrace.ProcessMessageTrace.FrameAdmitted,
              ExecutionTrace.RetainedXlot.FrameAdmitted] using admitted
          have outputEq : exception = .ok evm :=
            exec_ok_of_handleError handled failed
          subst exception
          exact StateInv.of_exec_precond_admitted preserves precond code'
            (fun _ => Mem.wf_empty) execution admitted'

/-- A retained CREATE core preserves an invariant at a distinct installed
contract address under the same concrete frame admission. -/
theorem ProcessCreateMessageTrace.stateInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (ready : c.MsgInv ca msg) :
    c.StateInv ca post.state := by
  obtain ⟨raw, innerRun, settle⟩ :=
    ProcessCreateMessage.iff_processMessage.mp trace.run
  rcases raw with error | innerPost
  · rw [processCreateMessage.settle_error] at settle
    cases settle
  let innerTrace : ProcessMessageTrace
      (processCreateMessage.msg msg) (.ok innerPost) :=
    ⟨trace.slot, trace.retained, innerRun⟩
  have innerReady : c.MessageRunReady ca (processCreateMessage.msg msg) :=
    (ready.processCreateMessage_msg targetNone targetNe).runReady_of_foreign
      (by simpa [processCreateMessage.msg, Msg.withBenv] using targetNe)
  have innerInv : c.StateInv ca innerPost.state :=
    innerTrace.stateInv_admitted preserves admitted innerReady
  have rest := settle.symm
  unfold processCreateMessage.settle at rest
  dsimp only [bind, Except.bind] at rest
  by_cases clean : innerPost.error.isNone = true
  · rw [if_pos clean] at rest
    rcases codeGas : processCreateMessage.chargeCodeGas msg.benv.stat.rules
        innerPost with ⟨error, charged⟩ | charged
    · rw [codeGas] at rest
      cases error with
      | halt reason =>
          rw [← Except.ok.inj rest]
          exact ready.state
      | revert => cases rest
      | crypto reason => cases rest
      | internal reason => cases rest
    · rw [codeGas] at rest
      dsimp only at rest
      rw [← Except.ok.inj rest, Devm.setCode_state,
        chargeCodeGas_state_ok codeGas]
      exact StateInv.setCode_ne targetNe innerInv
  · rw [if_neg clean] at rest
    rw [← Except.ok.inj rest]
    exact ready.state

/-- A settled retained message call preserves the invariant, while the
existing no-self-destruction projection remains independent of admission. -/
theorem MessageCallTrace.stateInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (ready : c.MsgInv ca msg) :
    c.StateInv ca state ∧
      (∀ address ∈ out.accountsToDelete.toList, address ≠ ca) := by
  refine ⟨?_, processMessageCall_accountsToDelete_ne trace.result ready.nodel
    (not_delegation_of_compile ready.state.code)⟩
  cases trace with
  | createCollision target collision result =>
      rw [processMessageCall_createCollision_state_eq target collision result]
      exact ready.state
  | createRun target collision evm core coreTrace result =>
      rw [processMessageCall_createRun_state_eq target collision core result]
      exact coreTrace.stateInv_admitted preserves admitted target
        (StateInv.ne_of_messageCreateCollision_false ready.state collision)
        ready
  | callRun target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      rw [processMessageCall_callRun_state_eq target delegation execMsgEq core
        result]
      have delegatedReady : c.MsgInv ca delegated :=
        ready.of_messageCallDelegation delegation
      have execReady : c.MsgInv ca execMsg := by
        rw [execMsgEq]
        exact delegatedReady.messageCallExecutionMessage
      have execTarget : execMsg.target.isNone = false := by
        rw [execMsgEq, messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq delegation]
        exact target
      exact coreTrace.stateInv_admitted preserves admitted
        (execReady.runReady_of_call execTarget)

end ExecutionTrace

end Blanc
