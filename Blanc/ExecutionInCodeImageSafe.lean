import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionInCodeImage
import Blanc.ExecutionInOwnCode

/-!
# Safe-parametric per-frame code image over In-carrier staged histories

Contract-neutral analogue of `ConfiguredHistoryTraceIn.rawFrames_codeImage_of_installedIn`
(`Blanc/ExecutionInCodeImage.lean`) with the installed certificate replaced by
what the proof actually consumes, following `Blanc/ExecutionNoDelSafeHistory.lean`
(G4a): a raw-frame safety premise (`ExecutionTrace.SafeRawFrames`,
reused as stated — no new definition) plus the code facts on `C` at `wa`
(`C.toList ≠ []`, `¬ isValidDelegation C`).

Route: G4a gives no-deletion and code survival block by block
(`ConfiguredHistoryTraceIn.noDel_of_safe`); per raw frame, the code at `wa`
equals `C` at every raw-frame start because no transaction in between deletes
or re-creates `wa`. Concretely each message-level entry world still holds `C`
(threaded forward with G4a's `…_of_safe` chain), and inside one message every
raw root keeps its entry world's code (`Exec.rawFrameRoots_codePreserve`,
as in `RetainedXlot.rawFrames_codeImage`). No `CoveredFork`, no
`InstalledCert`, no `callOnly`, no fixed access or delegation premise — so a
proxy whose runtime `DELEGATECALL`s can produce `safe` (via per-frame execution
evidence) together with the two code facts.

Reused (not copied): `ExecutionTrace.SafeRawFrames` and the whole
`…_of_safe` / `…_code_of_safe` threading chain from
`Blanc/ExecutionNoDelSafeHistory.lean`; `Exec.rawFrameRoots_codePreserve`
from `Blanc/LockExclusion.lean`; `messageCallExecutionMessage_getCode` and
`processCreateMessage.msg_getCode` from `Blanc/ExecutionTraceCodeAt.lean`;
the public `setDelegation_benv_equiv` from `Blanc/LadderBase.lean` for the
one delegation-prefix step below. The only local helper is
`delegation_keeps_code` (EIP-7702 prefix keeps `wa`'s code), since G4a's
version is private to its file.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Every raw root of a retained slot keeps its entry world's code at `wa`.
This is the `getCode wa = C` analogue of `RetainedXlot.rawFrames_codeImage`,
stated with the entry equation so each message arm can supply its own. -/
theorem RetainedXlot.codeImage_of_safe_entry {wa : Adr} {C : ByteArray}
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (entryCode : frame.inner.benv.state.getCode wa = C) (hCne : C.toList ≠ []) :
    ∀ root ∈ retained.rawFrames, root.devm.getCode wa = C := by
  cases retained with
  | none => intro root member; simp only [RetainedXlot.rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hcode : pre.getCode wa = frame.inner.benv.state.getCode wa :=
        Frame.enter_run_getCode henter wa
      have nonempty : (pre.getCode wa).toList ≠ [] := by
        rw [hcode, entryCode]
        exact hCne
      intro root member
      rw [Exec.rawFrameRoots_codePreserve run wa nonempty root member, hcode]
      exact entryCode

/-- The EIP-7702 authorization prefix keeps `wa`'s code: without authorizations
it is the identity, otherwise the public `setDelegation_benv_equiv` keeps the
nonempty undesignated code. G4a proves this as a private four-conjunct
theorem; only the code equation is needed here. -/
private theorem delegation_keeps_code {wa : Adr}
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (h : Msg.NoDel wa msg) (hCdel : ¬ isValidDelegation (msg.benv.state.getCode wa)) :
    delegated.benv.state.getCode wa = msg.benv.state.getCode wa := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, -⟩
    rfl
  · obtain ⟨⟨middle, counter⟩, hdel, rest⟩ := Except.bind_eq_ok run
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, -⟩
    exact (setDelegation_benv_equiv hdel).2 wa h.code hCdel

/-- **A settled message call keeps a protected code at every raw frame.**
The collision arm retains nothing; the create arm enters the prepared inner
message (whose world holds `msg`'s code); the call arm enters the resolved
execution message (authorization prefix and code-delegation resolution keep
`wa`'s undesignated code). Inside each arm the retained roots keep their
entry code. -/
theorem MessageCallTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (installed : msg.benv.state.getCode wa = C) (h : Msg.NoDel wa msg) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  cases trace with
  | createCollision =>
      intro R hR
      simp only [MessageCallTrace.rawFrames, List.not_mem_nil] at hR
  | createRun target collision evm core coreTrace result =>
      have hentry : (Frame.ofCreate msg).inner.benv.state.getCode wa = C := by
        rw [show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
          processCreateMessage.msg_getCode]
        exact installed
      intro R hR
      simp only [MessageCallTrace.rawFrames, ProcessCreateMessageTrace.rawFrames] at hR
      exact RetainedXlot.codeImage_of_safe_entry coreTrace.retained coreTrace.run
        hentry hCne R hR
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      have hdCode : delegated.benv.state.getCode wa = msg.benv.state.getCode wa :=
        delegation_keeps_code delegation h (by rw [installed]; exact hCdel)
      have execState : execMsg.benv.state.getCode wa = C := by
        rw [execMsgEq, messageCallExecutionMessage_getCode, hdCode, installed]
      intro R hR
      simp only [MessageCallTrace.rawFrames, ProcessMessageTrace.rawFrames] at hR
      exact RetainedXlot.codeImage_of_safe_entry coreTrace.retained coreTrace.run
        execState hCne R hR

/-- **A selected transaction keeps a protected code at every raw frame.**
The message entry world holds `C` across the nonce/balance debit, as in
`TransactionTrace.noDel_of_safe`; the transaction enumerates its message's
roots. -/
theorem TransactionTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  have hbenv := prepareMessage_benv trace.prepared
  have hdebit : trace.debitState.getCode wa = benv.state.getCode wa := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode wa = C := by
    rw [hbenv]
    exact hdebit.trans installed
  have hnodel : Msg.NoDel wa trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using notCreated
    · rw [hmsgState]
      exact hCne
  exact trace.message.codeImage_of_safe hCdel hCne hmsgState hnodel

end ExecutionTrace

end Blanc
