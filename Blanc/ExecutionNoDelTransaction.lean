import Blanc.ExecutionNoDelProducer
import Blanc.ExecutionTraceCodeKeep

/-!
# Protected-account no-deletion through messages and one selected transaction

`Blanc/ExecutionNoDelProducer.lean` proves all-outcome `Execution.NoDel wa` for any execution
under `stateGas = none` when `wa` holds a code `C` checked by a certificate without SELFDESTRUCT
terminals that spawns only by `CALL`/`STATICCALL`. This module carries that fact, with no fork
premise, through

* the raw message cores (`ProcessMessage`, `ProcessCreateMessage`, all outcomes including error
  payloads and rollback snapshots), reusing the fork-neutral `ProcessMessage.inv_noDel` and
  `ProcessCreateMessage.inv_noDel` with the slot obligation produced from the certificate in place
  of the modern `Exec.inv_noDel`;
* the settled message-call wrapper (`MessageCallTrace`): its collision arm, its CREATE arm (a
  create cannot target `wa`, whose code is nonempty) and its call arm (EIP-7702 authorizations keep
  `wa`'s undesignated code, and resolution keeps `wa`'s own code at a call to `wa`);
* one selected transaction (`TransactionTrace`) under `stateGas = none`: `wa` is not scheduled
  for deletion, and `wa`'s code survives the deletion fold and the touched sweep, which can never
  erase an account with nonempty code.

The transaction theorem is what carries `pre.getCode wa = C` from one transaction to the next.
-/

namespace Blanc

open Jaune

section InstalledCert

variable {wa : Adr} {C : ByteArray} {c : Lift.Cert}

/-- A filled frame slot meets its no-deletion obligation when `wa` holds the checked code and a
frame entered at `wa` runs that code. -/
theorem RunFrame.invNoDel_of_installedCert
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {f : Frame} {xl : Xlot} {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (filled : xl.Filled) (run : RunFrame f xl r)
    (hsg : f.inner.benv.stat.rules.stateGas = none)
    (installed : f.inner.benv.state.getCode wa = C)
    (hcode : f.inner.currentTarget = wa → f.inner.code = C) :
    Xlot.InvNoDel wa xl := by
  rcases xl with _ | ⟨evm, raw⟩
  · trivial
  · obtain ⟨exc⟩ := filled
    obtain ⟨henter, -⟩ := RunFrame.some_inv run
    intro hnd
    exact Exec.inv_noDel_of_installedCert hc callOnly noSelfdestruct hCdel exc
      (by rw [Frame.enter_run_benvStat henter]; exact hsg)
      (by rw [Frame.enter_run_getCode henter]; exact installed)
      (fun htgt => ⟨Frame.enter_run_pc henter, by
        rw [Frame.enter_run_code henter]
        exact hcode (by rw [← Frame.enter_run_currentTarget henter]; exact htgt)⟩)
      hnd

/-- **Raw call-message no-deletion**, every outcome (including error payloads and the rollback
snapshot), from the actual message facts and inherited-deletion exclusion. -/
theorem ProcessMessage.inv_noDel_of_installedCert
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {xl : Xlot} {ex : Except (EvmError × State × AdrSet × Tra) Devm}
    (filled : xl.Filled) (run : ProcessMessage msg xl ex)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (installed : msg.benv.state.getCode wa = C)
    (hcode : msg.currentTarget = wa → msg.code = C)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions) :
    MsgResult.NoDel wa ex :=
  ProcessMessage.inv_noDel
    (RunFrame.invNoDel_of_installedCert hc callOnly noSelfdestruct hCdel filled run hsg
      installed hcode)
    run h h_inherited

/-- **Raw create-message no-deletion**, every outcome, for a create not targeting `wa`. -/
theorem ProcessCreateMessage.inv_noDel_of_installedCert
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {xl : Xlot} {ex : Except (EvmError × State × AdrSet × Tra) Devm}
    (filled : xl.Filled) (run : ProcessCreateMessage msg xl ex)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (installed : msg.benv.state.getCode wa = C)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions) :
    MsgResult.NoDel wa ex :=
  ProcessCreateMessage.inv_noDel
    (RunFrame.invNoDel_of_installedCert hc callOnly noSelfdestruct hCdel filled run
      (by rw [show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
        processCreateMessage.msg_benvStat]; exact hsg)
      (by rw [show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
        processCreateMessage.msg_getCode]; exact installed)
      (fun htgt => absurd htgt h_ct))
    run h_ct h h_inherited

/-- The executable call-message form. -/
theorem processMessage_preserves_noDel_of_installedCert
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {evm : Devm}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (h_run : processMessage msg = .ok evm)
    (installed : msg.benv.state.getCode wa = C)
    (hcode : msg.currentTarget = wa → msg.code = C)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions) :
    Devm.NoDel wa evm := by
  obtain ⟨xl, hfill, hrel⟩ := of_processMessage msg (.ok evm) h_run
  exact ProcessMessage.inv_noDel_of_installedCert hc callOnly noSelfdestruct hCdel hfill hrel
    hsg installed hcode h h_inherited

/-- The executable create-message form. -/
theorem processCreateMessage_preserves_noDel_of_installedCert
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {evm : Devm}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (h_run : processCreateMessage msg = .ok evm)
    (installed : msg.benv.state.getCode wa = C)
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions) :
    Devm.NoDel wa evm := by
  obtain ⟨xl, hfill, hrel⟩ := of_processCreateMessage msg (.ok evm) h_run
  exact ProcessCreateMessage.inv_noDel_of_installedCert hc callOnly noSelfdestruct hCdel hfill
    hrel hsg installed h_ct h h_inherited

end InstalledCert

/-- A filled slot keeps every nonempty code (fork-free). -/
theorem Xlot.invGetCode_of_filled {xl : Xlot} (filled : xl.Filled) : Xlot.InvGetCode xl := by
  apply Xlot.invGetCode_of_rel
  rcases xl with _ | ⟨evm, raw⟩
  · trivial
  · obtain ⟨exc⟩ := filled
    exact Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
      Ninst.codePreserve_effectRec Jinst.codePreserve_effect Linst.codePreserve_effect exc

/-- Removing touched empty accounts never removes an account with nonempty code. -/
theorem sweepTouchedAccounts_getCode_of_nonempty (rules : ForkRules) (addresses : List Adr)
    {state : State} {a : Adr} (h : (state.getCode a).toList ≠ []) :
    (sweepTouchedAccounts rules addresses state).getCode a = state.getCode a := by
  unfold sweepTouchedAccounts
  split
  · induction addresses generalizing state with
    | nil => rfl
    | cons x xs ih =>
      rw [List.foldl_cons]
      split
      · rename_i hempty
        have hne : x ≠ a := by
          rintro rfl
          apply h
          have hsize : (state.getCode x).size = 0 := hempty.2.1
          rw [ByteArray.size_eq_length_toList] at hsize
          exact List.eq_nil_of_length_eq_zero hsize
        have hcode := ExecutionTrace.destroyAccount_getCode_ne (w := state) hne
        rw [ih (by rw [hcode]; exact h), hcode]
      · exact ih h
  · rfl

namespace ExecutionTrace

/-! ## The settled message-call wrapper -/

/-- The create arm settles at the core state and schedules the core's deletions only on
success. -/
private theorem processMessageCall_createRun_noDel {wa : Adr}
    {msg : Msg} {evm : Devm} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = false)
    (core : processCreateMessage msg = .ok evm)
    (result : processMessageCall msg = .ok ⟨state, out⟩)
    (hnd : wa ∉ evm.accountsToDelete) :
    state = evm.state ∧ wa ∉ out.accountsToDelete := by
  unfold processMessageCall at result
  simp only [target, ↓reduceIte] at result
  unfold processMessageCall.create at result
  rw [hsg] at result
  unfold messageCreateCollision at collision
  simp only [collision, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at result
  rcases Except.bind_eq_ok result with ⟨actual, actualMap, tail⟩
  have actualEq : actual = evm := Except.ok.inj
    ((Except.bimap_id_eq_ok actualMap).symm.trans core)
  subst actual
  split at tail
  · rcases Except.bind_eq_ok tail with ⟨_, _, output⟩
    have hout := Prod.mk.inj (Except.ok.inj output)
    refine ⟨hout.1.symm, ?_⟩
    rw [← hout.2]
    exact hnd
  · have hout := Prod.mk.inj (Except.ok.inj tail)
    refine ⟨hout.1.symm, ?_⟩
    rw [← hout.2]
    exact AdrSet.not_mem_empty

/-- The call arm settles at the core state and schedules the core's deletions only on success. -/
private theorem processMessageCall_callRun_noDel {wa : Adr}
    {msg delegated execMsg : Msg} {refund : Nat}
    {evm : Devm} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (target : msg.target.isNone = false)
    (delegation : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (execMsgEq : execMsg = messageCallExecutionMessage delegated)
    (core : processMessage execMsg = .ok evm)
    (result : processMessageCall msg = .ok ⟨state, out⟩)
    (hnd : wa ∉ evm.accountsToDelete) :
    state = evm.state ∧ wa ∉ out.accountsToDelete := by
  unfold processMessageCall at result
  simp only [target, Bool.false_eq_true, ↓reduceIte] at result
  unfold processMessageCall.call at result
  simp only [hsg] at result
  rw [show processMessageCall.legacyAuthorization msg = .ok ⟨delegated, refund⟩ from delegation]
    at result
  simp only [Except.bind_ok] at result
  have coreExec : processMessage (messageCallExecutionMessage delegated) = .ok evm :=
    (congrArg processMessage execMsgEq).symm.trans core
  rcases Except.bind_eq_ok result with ⟨actual, actualMap, tail⟩
  have actualEq : actual = evm := Except.ok.inj
    ((Except.bimap_id_eq_ok actualMap).symm.trans coreExec)
  subst actual
  split at tail
  · rcases Except.bind_eq_ok tail with ⟨_, _, output⟩
    have hout := Prod.mk.inj (Except.ok.inj output)
    refine ⟨hout.1.symm, ?_⟩
    rw [← hout.2]
    exact hnd
  · have hout := Prod.mk.inj (Except.ok.inj tail)
    refine ⟨hout.1.symm, ?_⟩
    rw [← hout.2]
    exact AdrSet.not_mem_empty

/-- The EIP-7702 authorization prefix keeps `wa`'s undesignated nonempty code, its creation and
inherited-deletion exclusions, and the executing message's own-code relation. -/
private theorem messageCallDelegation_installed {wa : Adr} {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (h : Msg.NoDel wa msg) (hnd : ¬ isValidDelegation (msg.benv.state.getCode wa))
    (h_inherited : wa ∉ msg.inheritedDeletions)
    (address : msg.codeAddress = some msg.currentTarget)
    (own : msg.code = msg.benv.state.getCode msg.currentTarget) :
    Msg.NoDel wa delegated ∧
      delegated.benv.state.getCode wa = msg.benv.state.getCode wa ∧
      wa ∉ delegated.inheritedDeletions ∧
      delegated.code = delegated.benv.state.getCode delegated.currentTarget := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, -⟩
    exact ⟨h, rfl, h_inherited, own⟩
  · obtain ⟨⟨middle, counter⟩, hdel, rest⟩ := Except.bind_eq_ok run
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, -⟩
    refine ⟨setDelegation_msg_noDel hdel h hnd, (setDelegation_benv_equiv hdel).2 wa h.code hnd,
      (setDelegation_inheritedDeletions hdel) ▸ h_inherited, ?_⟩
    unfold setDelegation at hdel
    obtain ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩ := Except.bind_eq_ok hdel
    have fields := setDelegationLoop_fields loop
    have loopAddress : loopMsg.codeAddress = some loopMsg.currentTarget := by
      rw [fields.2.2.2.2.2, address, fields.2.2.1]
    simp only [loopAddress, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, _⟩
    rfl

/-- Code-delegation resolution keeps the installed undesignated code at a message to `wa`. -/
private theorem messageCallExecutionMessage_code_installed {wa : Adr} {C : ByteArray} {m : Msg}
    (own : m.code = m.benv.state.getCode m.currentTarget)
    (installed : m.benv.state.getCode wa = C) (hCdel : ¬ isValidDelegation C) :
    (messageCallExecutionMessage m).currentTarget = wa →
      (messageCallExecutionMessage m).code = C := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  split
  · intro htgt
    rw [own, htgt, installed]
  · rename_i address resolved
    intro htgt
    have code : m.code = C := by rw [own, htgt, installed]
    have none : getDelegatedCodeAddress C = Option.none := by
      simp only [getDelegatedCodeAddress, hCdel, ↓reduceIte]
    simp only [ForkRules.delegatedCodeAddress, code, none, ite_self, reduceCtorEq] at resolved

/-- **Settled message-call no-deletion and code survival** for a protected account holding an
installed checked runtime, under `stateGas = none` with no fork premise. Covers the collision
arm, the create arm (a create cannot target `wa`) and the call arm (authorizations and
code-delegation resolution keep `wa`'s code). -/
theorem MessageCallTrace.noDel_of_installedCert {wa : Adr} {C : ByteArray} {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (installed : msg.benv.state.getCode wa = C)
    (own : msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget)
    (h : Msg.NoDel wa msg) (h_inherited : wa ∉ msg.inheritedDeletions) :
    wa ∉ out.accountsToDelete ∧ state.getCode wa = C := by
  have hCne : C.toList ≠ [] := installed ▸ h.code
  cases trace with
  | createCollision target collision result =>
      unfold processMessageCall at result
      simp only [target, ↓reduceIte] at result
      unfold processMessageCall.create at result
      rw [hsg] at result
      unfold messageCreateCollision at collision
      simp only [collision, ↓reduceIte, pure] at result
      have hout := Prod.mk.inj (Except.ok.inj result)
      refine ⟨by rw [← hout.2]; exact AdrSet.not_mem_empty, by rw [← hout.1]; exact installed⟩
  | createRun target collision evm core coreTrace result =>
      have h_ct : msg.currentTarget ≠ wa := ne_wa_of_not_hasCodeOrNonce h.code
        (by simpa only [messageCreateCollision] using collision)
      have hevm := processCreateMessage_preserves_noDel_of_installedCert hc callOnly
        noSelfdestruct hCdel hsg core installed h_ct h h_inherited
      obtain ⟨hstate, hdel⟩ :=
        processMessageCall_createRun_noDel hsg target collision core result hevm.atd
      refine ⟨hdel, ?_⟩
      have keep := ProcessCreateMessage.codePreserve
        (Xlot.invGetCode_of_filled coreTrace.retained.toFilled) coreTrace.run wa
        (Ne.symm h_ct) (by rw [installed]; exact hCne)
      rw [hstate, ← installed]
      exact keep
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      obtain ⟨address, ownCode⟩ := own target
      obtain ⟨hdNoDel, hdCode, hdInherited, hdOwn⟩ := messageCallDelegation_installed
        delegation h (by rw [installed]; exact hCdel) h_inherited address ownCode
      have execState : execMsg.benv.state.getCode wa = C := by
        rw [execMsgEq, messageCallExecutionMessage_getCode, hdCode, installed]
      have execSg : execMsg.benv.stat.rules.stateGas = none := by
        rw [execMsgEq, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hsg
      have execNoDel : Msg.NoDel wa execMsg := by
        rw [execMsgEq]
        unfold messageCallExecutionMessage Msg.resolveCodeDelegation
        split <;> exact ⟨hdNoDel.ca, hdNoDel.code⟩
      have execInherited : wa ∉ execMsg.inheritedDeletions := by
        rw [execMsgEq]
        unfold messageCallExecutionMessage Msg.resolveCodeDelegation
        split <;> exact hdInherited
      have execCode : execMsg.currentTarget = wa → execMsg.code = C := by
        rw [execMsgEq]
        exact messageCallExecutionMessage_code_installed hdOwn (hdCode.trans installed) hCdel
      have hevm := processMessage_preserves_noDel_of_installedCert hc callOnly noSelfdestruct
        hCdel execSg core execState execCode execNoDel execInherited
      obtain ⟨hstate, hdel⟩ := processMessageCall_callRun_noDel hsg target delegation execMsgEq
        core result hevm.atd
      refine ⟨hdel, ?_⟩
      have keep := ProcessMessage.codePreserve
        (Xlot.invGetCode_of_filled coreTrace.retained.toFilled) coreTrace.run wa
        (by rw [execState]; exact hCne)
      rw [hstate, ← execState]
      exact keep

/-! ## One selected transaction -/

/-- A transaction's top-level message runs its call target's own code. -/
private theorem prepareMessage_own {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h : prepareMessage benv tenv tx = .ok msg) :
    msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget := by
  intro htarget
  unfold prepareMessage at h
  rcases hr : tx.type.receiver? with _ | target
  · simp only [hr] at h
    obtain rfl := Except.ok.inj h
    simp only [Option.isNone_none, Bool.true_eq_false] at htarget
  · simp only [hr] at h
    obtain rfl := Except.ok.inj h
    exact ⟨rfl, rfl⟩

/-- **Protected-account survival across one selected transaction**, under `stateGas = none`
with no fork premise. If `wa` holds a code `C` checked by a certificate without SELFDESTRUCT
terminals that spawns only by `CALL`/`STATICCALL`, `C` is nonempty and undesignated, and `wa` was
not created in the block, then the transaction never schedules `wa` for deletion, and `wa` holds
`C` after the message and in the final state: the deletion fold and the touched sweep keep it. -/
theorem TransactionTrace.noDel_of_installedCert {wa : Adr} {C : ByteArray} {c : Lift.Cert}
    (hc : Lift.Cert.check C c = true) (callOnly : c.callOnly = true)
    (noSelfdestruct : c.noSelfdestruct = true) (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    wa ∉ trace.messageOut.accountsToDelete ∧ trace.messageState.getCode wa = C ∧
      state.getCode wa = C := by
  have hbenv := prepareMessage_benv trace.prepared
  have hdebit : trace.debitState.getCode wa = benv.state.getCode wa := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode wa = C := by
    rw [hbenv]
    exact hdebit.trans installed
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]
    exact hsg
  have hnodel : Msg.NoDel wa trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using notCreated
    · rw [hmsgState]
      exact hCne
  obtain ⟨hnot, hmsg⟩ := trace.message.noDel_of_installedCert hc callOnly noSelfdestruct hCdel
    hmsgSg hmsgState (prepareMessage_own trace.prepared) hnodel
    (trace.not_mem_msg_inheritedDeletions wa)
  refine ⟨hnot, hmsg, ?_⟩
  obtain ⟨refundCounter, -, hfinal⟩ := trace.exists_selectedFinalStateForm hsg
  have hnotList : ∀ x ∈ trace.messageOut.accountsToDelete.toList, x ≠ wa :=
    fun x hx heq => hnot (heq ▸ Std.HashSet.mem_toList.mp hx)
  rw [hfinal, sweepTouchedAccounts_getCode_of_nonempty, foldl_destroyAccount_getCode_ne _ hnotList,
    State.addBal_getCode, State.addBal_getCode, hmsg]
  rw [foldl_destroyAccount_getCode_ne _ hnotList, State.addBal_getCode, State.addBal_getCode, hmsg]
  exact hCne

end ExecutionTrace

end Blanc
