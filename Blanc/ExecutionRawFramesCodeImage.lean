import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionBodyPrefixAdmission
import Blanc.ExecutionTraceCodeAt
import Blanc.LockExclusion
import Blanc.StorageOnlySpec

/-!
# A certified code image at every raw frame of a history (contract-neutral)

`ConfiguredHistoryTrace.rawFrames_codeImage`: if the checkpoint holds the image of `c.sem` at `ca`
and `c` is preserved under an admission the history meets, every raw frame of the history (rolled
back or not) starts with that image at `ca`.

The state invariant `c.StateInv` (which carries the image) reaches every message entry along the
admitted rungs (`*.stateInv_admitted_sem`, `MsgInv`); inside one message, an entered frame keeps
every nonempty code of its entry at each raw root (`Exec.rawFrameRoots_codePreserve`).
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

open ContractSpecSem

variable {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}

/-- The raw roots of a retained slot keep a code image of the frame's entry world. -/
theorem RetainedXlot.rawFrames_codeImage {sem : CodeSem} {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} (retained : RetainedXlot slot)
    (hrun : RunFrame frame slot out)
    (image : Option.some (frame.inner.benv.state.getCode ca).toList = sem.image) :
    ∀ root ∈ retained.rawFrames, Option.some (root.devm.getCode ca).toList = sem.image := by
  cases retained with
  | none => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hcode : pre.getCode ca = frame.inner.benv.state.getCode ca :=
        Frame.enter_run_getCode henter ca
      have nonempty : (pre.getCode ca).toList ≠ [] := fun empty =>
        sem.ne_nil (image.symm.trans (by rw [← hcode, empty])) rfl
      intro root member
      rw [Exec.rawFrameRoots_codePreserve run ca nonempty root member, hcode]
      exact image

theorem MessageCallTrace.rawFrames_codeImage {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (ready : c.MsgInv ca msg) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  cases trace with
  | createCollision target collision result =>
      intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | createRun target collision evm core coreTrace result =>
      intro root member
      refine RetainedXlot.rawFrames_codeImage coreTrace.retained coreTrace.run ?_ root member
      change some ((processCreateMessage.msg msg).benv.state.getCode ca).toList = _
      rw [processCreateMessage.msg_getCode]
      exact ready.state.code
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      have execReady : c.MsgInv ca execMsg := by
        rw [execMsgEq]
        exact (ready.of_messageCallDelegation delegation).messageCallExecutionMessage
      intro root member
      exact RetainedXlot.rawFrames_codeImage coreTrace.retained coreTrace.run execReady.state.code
        root member

theorem TransactionTrace.rawFrames_codeImage {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') (inv : c.BenvInv ca benv) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image :=
  trace.message.rawFrames_codeImage (trace.msgInv_sem inv.state inv.ca)

theorem SystemMessageTrace.rawFrames_codeImage {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput} (trace : SystemMessageTrace benv target data state out)
    (inv : c.BenvInv ca benv) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image :=
  trace.message.rawFrames_codeImage (systemTransactionMessage_msgInv_sem inv.state inv.ca)

end ExecutionTrace

end Blanc
