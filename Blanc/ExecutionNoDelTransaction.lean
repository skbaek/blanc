import Blanc.ExecutionNoDelProducer
import Blanc.ExecutionNoDelSafeHistory
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
    have hCne : C.toList ≠ [] := by
      have hpre : evm.dyna.getCode wa = C := by
        rw [Frame.enter_run_getCode henter]; exact installed
      exact hpre ▸ hnd.code
    exact RunFrame.invNoDel_of_safe (e := rfl) exc run hsg
      (Exec.safe_of_installedCert hc callOnly noSelfdestruct hCdel exc
        (by rw [Frame.enter_run_benvStat henter]; exact hsg)
        (by rw [Frame.enter_run_getCode henter]; exact installed)
        hCne
        (fun htgt => ⟨Frame.enter_run_pc henter, by
          rw [Frame.enter_run_code henter]
          exact hcode (show f.inner.currentTarget = wa from by
            rw [← Frame.enter_run_currentTarget henter]; exact htgt)⟩))
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
    MsgResult.NoDel wa ex := by
  have hCne : C.toList ≠ [] := installed ▸ h.code
  rcases xl with _ | ⟨evm, raw⟩
  · have obl : Xlot.InvNoDel wa .none := by trivial
    exact ProcessMessage.inv_noDel obl run h h_inherited
  · obtain ⟨exc⟩ := filled
    obtain ⟨henter, -⟩ := RunFrame.some_inv run
    exact ProcessMessage.inv_noDel_of_safe (e := rfl) exc run hsg h h_inherited
      (Exec.safe_of_installedCert hc callOnly noSelfdestruct hCdel exc
        (by rw [Frame.enter_run_benvStat henter]; exact hsg)
        (by rw [Frame.enter_run_getCode henter]; exact installed)
        hCne
        (fun htgt => ⟨Frame.enter_run_pc henter, by
          rw [Frame.enter_run_code henter]
          exact hcode (show (Frame.ofCall msg).inner.currentTarget = wa from by
            rw [← Frame.enter_run_currentTarget henter]; exact htgt)⟩))

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
    MsgResult.NoDel wa ex := by
  have hCne : C.toList ≠ [] := installed ▸ h.code
  rcases xl with _ | ⟨evm, raw⟩
  · have obl : Xlot.InvNoDel wa .none := by trivial
    exact ProcessCreateMessage.inv_noDel obl run h_ct h h_inherited
  · obtain ⟨exc⟩ := filled
    obtain ⟨henter, -⟩ := RunFrame.some_inv run
    exact ProcessCreateMessage.inv_noDel_of_safe (e := rfl) exc run hsg h_ct h h_inherited
      (Exec.safe_of_installedCert hc callOnly noSelfdestruct hCdel exc
        (by rw [Frame.enter_run_benvStat henter,
          show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
          processCreateMessage.msg_benvStat]; exact hsg)
        (by rw [Frame.enter_run_getCode henter,
          show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
          processCreateMessage.msg_getCode]; exact installed)
        hCne
        (fun htgt => absurd (show msg.currentTarget = wa from by
          have hinner : (Frame.ofCreate msg).inner.currentTarget = wa := by
            rw [← Frame.enter_run_currentTarget henter]; exact htgt
          exact hinner) h_ct))

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
  have hCne : C.toList ≠ [] := installed ▸ h.code
  obtain ⟨xl, hfill, hrel⟩ := of_processMessage msg (.ok evm) h_run
  rcases xl with _ | ⟨evm', raw⟩
  · have obl : Xlot.InvNoDel wa .none := by trivial
    exact ProcessMessage.inv_noDel obl hrel h h_inherited
  · obtain ⟨exc⟩ := hfill
    obtain ⟨henter, -⟩ := RunFrame.some_inv hrel
    exact ProcessMessage.inv_noDel_of_safe (e := rfl) exc hrel hsg h h_inherited
      (Exec.safe_of_installedCert hc callOnly noSelfdestruct hCdel exc
        (by rw [Frame.enter_run_benvStat henter]; exact hsg)
        (by rw [Frame.enter_run_getCode henter]; exact installed)
        hCne
        (fun htgt => ⟨Frame.enter_run_pc henter, by
          rw [Frame.enter_run_code henter]
          exact hcode (show (Frame.ofCall msg).inner.currentTarget = wa from by
            rw [← Frame.enter_run_currentTarget henter]; exact htgt)⟩))

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
  have hCne : C.toList ≠ [] := installed ▸ h.code
  obtain ⟨xl, hfill, hrel⟩ := of_processCreateMessage msg (.ok evm) h_run
  rcases xl with _ | ⟨evm', raw⟩
  · have obl : Xlot.InvNoDel wa .none := by trivial
    exact ProcessCreateMessage.inv_noDel obl hrel h_ct h h_inherited
  · obtain ⟨exc⟩ := hfill
    obtain ⟨henter, -⟩ := RunFrame.some_inv hrel
    exact ProcessCreateMessage.inv_noDel_of_safe (e := rfl) exc hrel hsg h_ct h h_inherited
      (Exec.safe_of_installedCert hc callOnly noSelfdestruct hCdel exc
        (by rw [Frame.enter_run_benvStat henter,
          show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
          processCreateMessage.msg_benvStat]; exact hsg)
        (by rw [Frame.enter_run_getCode henter,
          show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
          processCreateMessage.msg_getCode]; exact installed)
        hCne
        (fun htgt => absurd (show msg.currentTarget = wa from by
          have hinner : (Frame.ofCreate msg).inner.currentTarget = wa := by
            rw [← Frame.enter_run_currentTarget henter]; exact htgt
          exact hinner) h_ct))

end InstalledCert

namespace ExecutionTrace

/-! ## The settled message-call wrapper -/

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
  exact trace.noDel_of_safe hCdel hsg installed own h h_inherited
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel hsg installed
      own h h_inherited)

/-! ## One selected transaction -/

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
  exact trace.noDel_of_safe hCdel hCne hsg installed notCreated
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct hCdel hCne hsg
      installed notCreated)

end ExecutionTrace

end Blanc
