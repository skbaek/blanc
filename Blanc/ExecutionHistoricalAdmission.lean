import Blanc.ExecutionTransactionAdmission
import Blanc.ExecutionNoDelHistory
import Blanc.ExecutionSelectedTransactionStateTrace
import Blanc.ExecutionBodyAdmission
import Blanc.ExecutionStagedAdmission

/-!
# Historical admitted preservation through messages and one selected transaction

The modern admitted-preservation stack (`ContractSpecSem.SoundAdmitted`/`PreservesAdmitted`,
`ExecutionMessageAdmission`, `ExecutionTransactionAdmission`) quantifies `CoveredFork` at every
frame and settles NoDel through the modern `processMessageCall_accountsToDelete_ne`, which is
`CoveredFork`-bound. This module is its additive historical counterpart.

* `SoundAdmittedIn F` / `PreservesAdmittedIn F` replace each `CoveredFork` frame position by a
  selected fork domain `F` (the old definitions are untouched; `PreservesAdmitted` is
  `PreservesAdmittedIn CoveredFork` by `PreservesAdmitted.toIn`).
* The message wrappers split the old `hfork` into domain routing `F fork` (handed to
  `PreservesAdmittedIn`) and `stateGas = none` (settlement). The deletion exclusion of the
  protected account comes from an installed checked runtime (`InstalledCert C` with
  `c.sem.image = some C.toList`) through the E2 producer, never from a fork premise or an assumed
  endpoint fact.
* The selected transaction rung threads the invariant through debit, the settled message, the
  two funded credits (`selected_settlement_sum_bounds`, `stateGas = none` only), the deletion fold
  (proved exclusion) and the touched sweep (`StateInv.sweepTouchedAccounts`: the sweep never erases
  an account with nonempty code), with no sweep-off assumption.

* The staged body (D1 stage order: beacon, history, selected transactions, withdrawals, requests,
  `payRewards` credits), the configured In-block and the In-history carry the invariant with
  per-block `F`/`stateGas = none` from `forkIn` and `BodyStageCapabilities F`, withdrawal funding
  from the retained reward-inclusive bound, and reward funding as the explicit Mac-owned premise
  `RewardCreditsFunded` (no reward arithmetic here). Admission is the staged/In raw-entry
  `FrameAdmitted` of `ExecutionStagedAdmission`.

The historical frame ladder producing `PreservesAdmittedIn F` from a contract's own-frame
`SoundAdmittedIn F` obligation lives in `Blanc/ExecutionHistoricalLadder.lean`.
-/

namespace Blanc

open Jaune

namespace ContractSpecSem

/-- `SoundAdmitted` over a selected fork domain `F`, at the outer and every entered child frame. -/
def SoundAdmittedIn (F : Fork → Prop) (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  ∀ {sevm pre post},
    F sevm.benvStat.fork →
    (execution : Exec 0 sevm pre (.ok post)) →
    c.sem.Run sevm pre post →
    sevm.currentTarget = ca →
    Exec.FrameAdmitted ca entry execution →
    (∀ pc' sevm' pre' post'
        (child : Exec pc' sevm' pre' (.ok post')),
      sevm'.depth < sevm.depth →
      c.sem.At ca pc' sevm' pre' →
      F sevm'.benvStat.fork →
      Exec.FrameAdmitted ca entry child →
      c.PreWf ca sevm' pre' →
      c.Post ca sevm' post') →
    Mem.Wf pre.memory →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- `PreservesAdmitted` over a selected fork domain `F`. -/
def PreservesAdmittedIn (F : Fork → Prop) (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  ∀ sevm pre post,
    F sevm.benvStat.fork →
    (execution : Exec 0 sevm pre (.ok post)) →
    Exec.FrameAdmitted ca entry execution →
    (sevm.currentTarget = ca → some sevm.code.toList = c.sem.image) →
    (sevm.currentTarget = ca → Mem.Wf pre.memory) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- The modern predicate is the `CoveredFork` instance. -/
theorem PreservesAdmitted.toIn {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    (h : c.PreservesAdmitted ca entry) : c.PreservesAdmittedIn CoveredFork ca entry := h

/-- The modern soundness predicate is the `CoveredFork` instance. -/
theorem SoundAdmitted.toIn {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    (h : c.SoundAdmitted ca entry) : c.SoundAdmittedIn CoveredFork ca entry := h

/-- Preservation over a larger domain restricts to a smaller one. -/
theorem PreservesAdmittedIn.mono {F G : Fork → Prop} {c : ContractSpecSem} {ca : Adr}
    {entry : Sevm → Devm → Prop} (sub : ∀ {f}, F f → G f)
    (h : c.PreservesAdmittedIn G ca entry) : c.PreservesAdmittedIn F ca entry :=
  fun sevm pre post hF => h sevm pre post (sub hF)

variable {c : ContractSpecSem}

/-- Two byte arrays with the same byte list are equal. -/
private theorem byteArray_eq_of_toList {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  have hdata : a.data.toList = b.data.toList := by
    simpa only [ByteArray.toList_eq_toList_data] using h
  cases a; cases b
  exact congrArg ByteArray.mk (Array.toList_inj.mp hdata)

/-- An invariant's code image pins the installed runtime. -/
theorem StateInv.getCode_eq_of_image {ca : Adr} {C : ByteArray} {w : State}
    (image : c.sem.image = some C.toList) (h : c.StateInv ca w) : w.getCode ca = C :=
  byteArray_eq_of_toList (Option.some.inj (h.code.trans image))

/-- **The touched sweep preserves a maintained invariant.** The sweep erases only existing empty
accounts; the protected account has nonempty code (its image), so it is never erased, and erasing
any other account preserves the invariant (`StateInv.destroyAccount`). No sweep-off assumption. -/
theorem StateInv.sweepTouchedAccounts {ca : Adr} {w : State} (rules : ForkRules)
    (addresses : List Adr) (h : c.StateInv ca w) :
    c.StateInv ca (Jaune.sweepTouchedAccounts rules addresses w) := by
  unfold Jaune.sweepTouchedAccounts
  split
  · induction addresses generalizing w with
    | nil => exact h
    | cons x xs ih =>
      rw [List.foldl_cons]
      split
      · rename_i hempty
        have hne : x ≠ ca := by
          rintro rfl
          have hsize : (w.getCode x).size = 0 := hempty.2.1
          rw [ByteArray.size_eq_length_toList] at hsize
          exact c.sem.ne_nil h.code.symm (List.eq_nil_of_length_eq_zero hsize)
        exact ih (h.destroyAccount hne)
      · exact ih h
  · exact h

/-- The historical counterpart of `StateInv.of_exec_precond_admitted_sem`. -/
lemma StateInv.of_exec_precond_admitted_semIn {F : Fork → Prop}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {sevm : Sevm} {pre post : Devm}
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F sevm.benvStat.fork)
    (precond : c.Pre ca sevm pre)
    (code : sevm.currentTarget = ca →
      some sevm.code.toList = c.sem.image)
    (wf : sevm.currentTarget = ca → Mem.Wf pre.memory)
    (run : Exec 0 sevm pre (.ok post))
    (admitted : Exec.FrameAdmitted ca entry run) :
    c.StateInv ca post.state := by
  have postcond : c.Post ca sevm post :=
    preserves sevm pre post hF run admitted code wf precond
  apply StateInv.of_postcond postcond
  have codeEq : post.getCode ca = pre.getCode ca :=
    code_eq_of_exec_sem run precond.code
  show some (post.state.getCode ca).toList = c.sem.image
  rw [show post.state.getCode ca = post.getCode ca from rfl, codeEq]
  exact precond.code

end ContractSpecSem

namespace ContractSpec

/-- `ContractSpec.SoundAdmitted` over a selected fork domain. -/
def SoundAdmittedIn (F : Fork → Prop) (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  ∀ {sevm pre post},
    F sevm.benvStat.fork →
    (execution : Exec 0 sevm pre (.ok post)) →
    Prog.Run sevm pre c.prog post →
    sevm.currentTarget = ca →
    Exec.FrameAdmitted ca entry execution →
    (∀ pc' sevm' pre' post'
        (child : Exec pc' sevm' pre' (.ok post')),
      sevm'.depth < sevm.depth →
      Prog.At c.prog ca pc' sevm' pre' →
      F sevm'.benvStat.fork →
      Exec.FrameAdmitted ca entry child →
      c.PreWf ca sevm' pre' →
      c.Post ca sevm' post') →
    Mem.Wf pre.memory →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- `ContractSpec.PreservesAdmitted` over a selected fork domain. -/
def PreservesAdmittedIn (F : Fork → Prop) (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  ∀ sevm pre post,
    F sevm.benvStat.fork →
    (execution : Exec 0 sevm pre (.ok post)) →
    Exec.FrameAdmitted ca entry execution →
    (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
    (sevm.currentTarget = ca → Mem.Wf pre.memory) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

theorem soundAdmittedIn_toSem {F : Fork → Prop} (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (h : c.SoundAdmittedIn F ca entry) : c.toSem.SoundAdmittedIn F ca entry := by
  intro sevm pre post hF execution hrun target admitted body hwf hpre
  apply post_toSem
  apply h hF execution (by simpa only [toSem, Prog.codeSem] using hrun)
    target admitted
  · intro pc' sevm' pre' post' child depth childAt hF' childAdmitted hpre'
    exact post_ofSem (body (pc' := pc') (sevm' := sevm') (pre' := pre')
      (post' := post') (child := child) depth
      (by simpa only [CodeSem.At, toSem, Prog.codeSem, Prog.At] using childAt)
      hF' childAdmitted (preWf_toSem hpre'))
  · exact hwf
  · exact pre_ofSem hpre

theorem preservesAdmittedIn_toSem {F : Fork → Prop} (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (h : c.PreservesAdmittedIn F ca entry) : c.toSem.PreservesAdmittedIn F ca entry := by
  intro sevm pre post hF execution admitted h_code h_wf hpre
  apply post_toSem
  apply h sevm pre post hF execution admitted
    (fun target => by simpa only [toSem, Prog.codeSem] using h_code target)
    h_wf (pre_ofSem hpre)

theorem preservesAdmittedIn_ofSem {F : Fork → Prop} (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (h : c.toSem.PreservesAdmittedIn F ca entry) : c.PreservesAdmittedIn F ca entry := by
  intro sevm pre post hF execution admitted h_code h_wf hpre
  apply post_ofSem
  apply h sevm pre post hF execution admitted
    (fun target => by simpa only [toSem, Prog.codeSem] using h_code target)
    h_wf (pre_toSem hpre)

end ContractSpec

namespace ExecutionTrace

/-! ## Settled wrapper outputs under `stateGas = none` -/

/-- A create collision leaves the state and schedules no deletion (`stateGas = none` twin of
`processMessageCall_createCollision_state_eq`, with the deletion output). -/
theorem processMessageCall_createCollision_out_noStateGas
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = true)
    (result : processMessageCall msg = .ok ⟨state, out⟩) :
    state = msg.benv.state ∧ ∀ a, a ∉ out.accountsToDelete := by
  unfold processMessageCall at result
  simp only [target, ↓reduceIte] at result
  unfold processMessageCall.create at result
  rw [hsg] at result
  unfold messageCreateCollision at collision
  simp only [collision, ↓reduceIte, pure] at result
  have hout := Prod.mk.inj (Except.ok.inj result)
  refine ⟨hout.1.symm, fun a => ?_⟩
  rw [← hout.2]
  exact AdrSet.not_mem_empty

/-- A create run settles at its core state, and schedules only deletions the core scheduled. -/
theorem processMessageCall_createRun_out_noStateGas
    {msg : Msg} {evm : Devm} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = false)
    (core : processCreateMessage msg = .ok evm)
    (result : processMessageCall msg = .ok ⟨state, out⟩) :
    state = evm.state ∧ ∀ a, a ∈ out.accountsToDelete → a ∈ evm.accountsToDelete := by
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
    refine ⟨hout.1.symm, fun a ha => ?_⟩
    rw [← hout.2] at ha
    exact ha
  · have hout := Prod.mk.inj (Except.ok.inj tail)
    refine ⟨hout.1.symm, fun a ha => ?_⟩
    rw [← hout.2] at ha
    exact absurd ha AdrSet.not_mem_empty

/-- A call run settles at its core state, and schedules only deletions the core scheduled. -/
theorem processMessageCall_callRun_out_noStateGas
    {msg delegated execMsg : Msg} {refund : Nat}
    {evm : Devm} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (target : msg.target.isNone = false)
    (delegation : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (execMsgEq : execMsg = messageCallExecutionMessage delegated)
    (core : processMessage execMsg = .ok evm)
    (result : processMessageCall msg = .ok ⟨state, out⟩) :
    state = evm.state ∧ ∀ a, a ∈ out.accountsToDelete → a ∈ evm.accountsToDelete := by
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
    refine ⟨hout.1.symm, fun a ha => ?_⟩
    rw [← hout.2] at ha
    exact ha
  · have hout := Prod.mk.inj (Except.ok.inj tail)
    refine ⟨hout.1.symm, fun a ha => ?_⟩
    rw [← hout.2] at ha
    exact absurd ha AdrSet.not_mem_empty

/-- EIP-7702 authorization and code resolution keep the inherited deletions. -/
theorem messageCallExecutionMessage_inherited {msg delegated : Msg} {refund : Nat}
    (delegation : messageCallDelegation msg = .ok ⟨delegated, refund⟩) :
    (messageCallExecutionMessage delegated).inheritedDeletions = msg.inheritedDeletions := by
  have hres : (messageCallExecutionMessage delegated).inheritedDeletions =
      delegated.inheritedDeletions := by
    unfold messageCallExecutionMessage Msg.resolveCodeDelegation
    split <;> rfl
  rw [hres]
  unfold messageCallDelegation processMessageCall.legacyAuthorization at delegation
  split at delegation
  · simp only [Except.ok.injEq, Prod.mk.injEq] at delegation
    rcases delegation with ⟨rfl, -⟩
    rfl
  · obtain ⟨⟨middle, counter⟩, hdel, rest⟩ := Except.bind_eq_ok delegation
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, -⟩
    exact setDelegation_inheritedDeletions hdel

open ContractSpecSem

variable {c : ContractSpecSem}

/-! ## Message wrappers -/

theorem ProcessMessageTrace.stateInv_admitted_semIn {F : Fork → Prop}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F msg.benv.stat.fork)
    (admitted : trace.FrameAdmitted ca entry)
    (ready : c.MessageRunReady ca msg) :
    c.StateInv ca post.state := by
  rcases trace with ⟨slot, retained, run⟩
  have code : msg.currentTarget = ca →
      some msg.code.toList = c.sem.image := by
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
        c.sem.image := code
  rcases raw with error | evm
  · rw [processMessage.settle_error] at settle
    cases settle
  unfold processMessage.settle at settle
  dsimp only [bind, Except.bind] at settle
  by_cases failed : evm.error.isSome = true
  · rw [ite_eq_left failed] at settle
    rw [Except.ok.inj settle]
    exact ready.ready.state
  · rw [ite_eq_right failed] at settle
    rw [Except.ok.inj settle, Devm.recordTouch_state]
    rcases of_executeCode_cases body with
      ⟨address, precompile⟩ | ⟨exception, slotEq, handled⟩
    · rw [state_of_executePrecomp_ok precompile failed]
      exact StateInv.of_benvAfterTransfer ready.ready.ne transfer
        ready.ready.state
    · subst slotEq
      cases retained with
      | some execution =>
          have admitted' : Exec.FrameAdmitted ca entry execution := by
            simpa only [FrameAdmitted, RetainedXlot.FrameAdmitted] using admitted
          have outputEq : exception = .ok evm :=
            exec_ok_of_handleError handled failed
          subst exception
          have hF' : F (initSevm (msg.withBenv benv)).benvStat.fork := by
            rw [initSevm_benvStat, Msg.withBenv_benvStat,
              benvAfterTransfer_stat transfer]
            exact hF
          exact StateInv.of_exec_precond_admitted_semIn preserves hF' precond code'
            (fun _ => Mem.wf_empty) execution admitted'

theorem ProcessCreateMessageTrace.stateInv_admitted_semIn {F : Fork → Prop}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F msg.benv.stat.fork)
    (hsg : msg.benv.stat.rules.stateGas = none)
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
      (by simpa only [processCreateMessage.msg, Msg.withBenv, ne_eq] using targetNe)
  have hF' : F (processCreateMessage.msg msg).benv.stat.fork := by
    rw [processCreateMessage.msg_benvStat]
    exact hF
  have innerInv : c.StateInv ca innerPost.state :=
    innerTrace.stateInv_admitted_semIn preserves hF' admitted innerReady
  have rest := settle.symm
  unfold processCreateMessage.settle at rest
  dsimp only [bind, Except.bind] at rest
  by_cases clean : innerPost.error.isNone = true
  · rw [ite_eq_left clean] at rest
    rcases codeGas : processCreateMessage.chargeCodeGas msg.benv.stat.rules
        innerPost with ⟨error, charged⟩ | charged
    · rw [codeGas] at rest
      cases error with
      | halt reason =>
          rw [hsg] at rest
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
  · rw [ite_eq_right clean] at rest
    rw [← Except.ok.inj rest]
    exact ready.state

/-- **Protected-account deletion exclusion of a settled message call from the message
invariant**, under `stateGas = none`, for an installed checked runtime matching the contract's
code image. Replaces the modern `processMessageCall_accountsToDelete_ne hfork`. -/
theorem MessageCallTrace.accountsToDelete_ne_of_installedCert {C : ByteArray}
    (K : InstalledCert C) (image : c.sem.image = some C.toList)
    {ca : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (ready : c.MsgInv ca msg)
    (h_inherited : ca ∉ msg.inheritedDeletions) :
    ∀ address ∈ out.accountsToDelete.toList, address ≠ ca := by
  obtain ⟨cert, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  suffices hnot : ca ∉ out.accountsToDelete by
    intro address member heq
    subst heq
    exact hnot (Std.HashSet.mem_toList.mp member)
  cases trace with
  | createCollision target collision result =>
      exact (processMessageCall_createCollision_out_noStateGas hsg target collision result).2 ca
  | createRun target collision evm core coreTrace result =>
      have targetNe := StateInv.ne_of_messageCreateCollision_false ready.state collision
      have hevm := processCreateMessage_preserves_noDel_of_installedCert hc callOnly
        noSelfdestruct K.notDelegation hsg core (ready.state.getCode_eq_of_image image)
        targetNe ready.nodel h_inherited
      exact fun member => hevm.atd
        ((processMessageCall_createRun_out_noStateGas hsg target collision core result).2
          ca member)
  | callRun target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      have execReady : c.MsgInv ca execMsg := by
        rw [execMsgEq]
        exact (ready.of_messageCallDelegation delegation).messageCallExecutionMessage
      have execTarget : execMsg.target.isNone = false := by
        rw [execMsgEq, messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq delegation]
        exact target
      have execSg : execMsg.benv.stat.rules.stateGas = none := by
        rw [execMsgEq, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hsg
      have execInherited : ca ∉ execMsg.inheritedDeletions := by
        rw [execMsgEq, messageCallExecutionMessage_inherited delegation]
        exact h_inherited
      have execCode : execMsg.currentTarget = ca → execMsg.code = C := fun current =>
        byteArray_eq_of_toList (Option.some.inj ((execReady.code execTarget current).trans image))
      have hevm := processMessage_preserves_noDel_of_installedCert hc callOnly noSelfdestruct
        K.notDelegation execSg core (execReady.state.getCode_eq_of_image image) execCode
        execReady.nodel execInherited
      exact fun member => hevm.atd
        ((processMessageCall_callRun_out_noStateGas hsg target delegation execMsgEq core
          result).2 ca member)

/-- **Historical settled message-call preservation**: the invariant survives and the protected
account is not scheduled for deletion, under a selected fork domain `F` (routing) and
`stateGas = none` (settlement), with no `CoveredFork`. -/
theorem MessageCallTrace.stateInv_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F msg.benv.stat.fork)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (ready : c.MsgInv ca msg)
    (h_inherited : ca ∉ msg.inheritedDeletions)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca state ∧
      (∀ address ∈ out.accountsToDelete.toList, address ≠ ca) := by
  refine ⟨?_, trace.accountsToDelete_ne_of_installedCert K image hsg ready h_inherited⟩
  cases trace with
  | createCollision target collision result =>
      rw [(processMessageCall_createCollision_out_noStateGas hsg target collision result).1]
      exact ready.state
  | createRun target collision evm core coreTrace result =>
      rw [(processMessageCall_createRun_out_noStateGas hsg target collision core result).1]
      exact coreTrace.stateInv_admitted_semIn preserves hF hsg admitted target
        (StateInv.ne_of_messageCreateCollision_false ready.state collision)
        ready
  | callRun target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      rw [(processMessageCall_callRun_out_noStateGas hsg target delegation execMsgEq core
        result).1]
      have execReady : c.MsgInv ca execMsg := by
        rw [execMsgEq]
        exact (ready.of_messageCallDelegation delegation).messageCallExecutionMessage
      have execTarget : execMsg.target.isNone = false := by
        rw [execMsgEq, messageCallExecutionMessage_target_eq,
          messageCallDelegation_target_eq delegation]
        exact target
      have execF : F execMsg.benv.stat.fork := by
        rw [execMsgEq, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hF
      exact coreTrace.stateInv_admitted_semIn preserves execF admitted
        (execReady.runReady_of_call execTarget)

/-! ## One selected transaction -/

/-- **Historical selected-transaction preservation.** Under a selected fork domain `F` and
`stateGas = none`, an admitted transaction preserves `BenvInv`: debit and preparation (fork-free
readiness), the settled message (`MessageCallTrace.stateInv_admitted_semIn`), the two credits funded
by the checked debit, the deletion fold (proved exclusion of `ca`) and the touched sweep. -/
theorem TransactionTrace.benvInv_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.BenvInv ca (benv.withState state) := by
  have msgInv : c.MsgInv ca trace.msg :=
    trace.msgInv_sem inv.state inv.ca
  have msgF : F trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hF
  have msgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [BenvStat.rules, Benv.beginTransaction] using hsg
  have inherited : ca ∉ trace.msg.inheritedDeletions :=
    trace.not_mem_msg_inheritedDeletions ca
  have messageInv :=
    trace.message.stateInv_admitted_semIn preserves msgF msgSg admitted msgInv inherited K image
  rcases trace.exists_selectedStateChronology hsg with ⟨chronology⟩
  have bounds := trace.selected_settlement_sum_bounds chronology.refundCounter sumNof hsg
  have refundInv : c.StateInv ca (trace.selectedRefundedState chronology.refundCounter) :=
    StateInv.addBal bounds.1 messageInv.1
  have coinbaseInv : c.StateInv ca (trace.selectedCoinbaseState chronology.refundCounter) :=
    StateInv.addBal bounds.2 refundInv
  have deletionInv : c.StateInv ca
      (trace.messageOut.accountsToDelete.toList.foldl destroyAccount
        (trace.selectedCoinbaseState chronology.refundCounter)) :=
    StateInv.foldl_destroyAccount messageInv.2 coinbaseInv
  refine ⟨?_, by simpa only [Benv.withState] using inv.ca⟩
  change c.StateInv ca state
  rw [chronology.finalState_eq]
  exact deletionInv.sweepTouchedAccounts _ _

/-- A selected transaction list threads historical preservation and the balance-sum bound. -/
theorem ApplyTransactionsTrace.benvInv_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.BenvInv ca finalBenv := by
  induction trace with
  | nil => exact inv
  | @cons index tx txs benv bout txState txBout finalBenv finalBout
      head tail ih =>
      have headInv : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted_semIn preserves hF hsg admitted.1 sumNof inv K image
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa only [Benv.withState] using processTransaction_sum_le head.result hsg)
          sumNof
      exact ih hF hsg admitted.2 nextSum headInv

end ExecutionTrace

namespace ExecutionTrace

open ContractSpec

variable {c : ContractSpec}

/-- `ContractSpec` form of `MessageCallTrace.stateInv_admitted_semIn`. -/
theorem MessageCallTrace.stateInv_admittedIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F msg.benv.stat.fork)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (ready : c.MsgInv ca msg)
    (h_inherited : ca ∉ msg.inheritedDeletions)
    (K : InstalledCert C) (image : Prog.compile c.prog = some C.toList) :
    c.StateInv ca state ∧
      (∀ address ∈ out.accountsToDelete.toList, address ≠ ca) := by
  rcases trace.stateInv_admitted_semIn (c := c.toSem)
    (preservesAdmittedIn_toSem c ca entry preserves) hF hsg admitted
    (msgInv_toSem ready) h_inherited K image with ⟨hstate, hdelete⟩
  exact ⟨stateInv_ofSem hstate, hdelete⟩

/-- `ContractSpec` form of `TransactionTrace.benvInv_admitted_semIn`. -/
theorem TransactionTrace.benvInv_admittedIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : Prog.compile c.prog = some C.toList) :
    c.BenvInv ca (benv.withState state) :=
  benvInv_ofSem (trace.benvInv_admitted_semIn (c := c.toSem)
    (preservesAdmittedIn_toSem c ca entry preserves) hF hsg admitted sumNof
    (benvInv_toSem inv) K image)

/-- `ContractSpec` form of `ApplyTransactionsTrace.benvInv_admitted_semIn`. -/
theorem ApplyTransactionsTrace.benvInv_admittedIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork)
    (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : Prog.compile c.prog = some C.toList) :
    c.BenvInv ca finalBenv :=
  benvInv_ofSem (trace.benvInv_admitted_semIn (c := c.toSem)
    (preservesAdmittedIn_toSem c ca entry preserves) hF hsg admitted sumNof
    (benvInv_toSem inv) K image)

end ExecutionTrace

/-! ## Proof-of-work reward funding (Mac-owned premise shape) -/

/-- Each ommer credit of `payRewards`, in fold order, is funded at the state it is applied to. -/
def OmmerCreditsFunded (pow : PowRules) (number : Nat) : State → List Header → Prop
  | _, [] => True
  | s, ommer :: ommers =>
      sum s.bal + (ExecutionTrace.stagedOmmerRewardValue pow number ommer).toNat < 2 ^ 256 ∧
        OmmerCreditsFunded pow number
          (s.addBal ommer.coinbase (ExecutionTrace.stagedOmmerRewardValue pow number ommer)) ommers

/-- Every `payRewards` credit (the miner credit, then each ommer credit in fold order) is funded
at the state it is applied to. This is the premise shape that the Mac-owned reward budget
(`request_budget` / `request_reward_budget` / `reward_preserves_and_sum`, source `7a82f5b8`)
discharges from the retained reward-inclusive block bound; no reward arithmetic is proved here. -/
def RewardCreditsFunded (pow : PowRules) (number : Nat) (coinbase : Adr)
    (ommers : List Header) (st : State) : Prop :=
  sum st.bal + (ExecutionTrace.stagedMinerRewardValue pow ommers).toNat < 2 ^ 256 ∧
    OmmerCreditsFunded pow number
      (st.addBal coinbase (ExecutionTrace.stagedMinerRewardValue pow ommers)) ommers

namespace ContractSpecSem

variable {c : ContractSpecSem}

/-- Funded `payRewards` credits preserve the invariant, one `StateInv.addBal` per credit in fold
order. -/
theorem StateInv.payRewards {ca : Adr} {pow : PowRules} {number : Nat} {coinbase : Adr}
    {ommers : List Header} {st : State}
    (funded : RewardCreditsFunded pow number coinbase ommers st) (h : c.StateInv ca st) :
    c.StateInv ca (Jaune.payRewards pow number coinbase ommers st) := by
  have fold : ∀ (os : List Header) (s : State), OmmerCreditsFunded pow number s os →
      c.StateInv ca s →
      c.StateInv ca (os.foldl (fun acc ommer => acc.addBal ommer.coinbase
        (ExecutionTrace.stagedOmmerRewardValue pow number ommer)) s) := by
    intro os
    induction os with
    | nil => intro s _ hs; exact hs
    | cons o os ih =>
        intro s hfund hs
        exact ih _ hfund.2 (StateInv.addBal hfund.1 hs)
  exact fold ommers _ funded.2 (StateInv.addBal funded.1 h)

end ContractSpecSem

namespace ExecutionTrace

open ContractSpecSem

variable {c : ContractSpecSem}

/-! ## Body stages -/

/-- `stateGas = none` twin of `ApplyTransactionsTrace.sum_le`. -/
theorem ApplyTransactionsTrace.sum_le_noStateGas
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none) :
    sum finalBenv.state.bal ≤ sum benv.state.bal := by
  induction trace with
  | nil => exact le_rfl
  | cons head tail ih =>
      exact le_trans (ih (by simpa only [Benv.withState] using hsg))
        (by simpa only [Benv.withState] using processTransaction_sum_le head.result hsg)

theorem SystemMessageTrace.stateInv_and_sum_le_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have msgInv : c.MsgInv ca (systemTransactionMessage benv target data) :=
    systemTransactionMessage_msgInv_sem inv.state inv.ca
  have msgSg : (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    simpa only [BenvStat.rules, systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hsg
  have stateInv := trace.message.stateInv_admitted_semIn preserves
    (by simpa only [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hF)
    msgSg admitted msgInv AdrSet.not_mem_empty K image
  have sumLe := processMessageCall_sum_le msgSg trace.message.result
  refine ⟨stateInv.1, ?_⟩
  simpa only [systemTransactionMessage, processSystemTransactionMsg, Benv.beginTransaction] using
    sumLe

theorem RequestsTrace.stateInv_and_sum_le_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  have withdrawal := trace.withdrawal.stateInv_and_sum_le_admitted_semIn
    preserves hF hsg admitted.withdrawal inv K image
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    ⟨withdrawal.1, by simpa only [Benv.withState] using inv.ca⟩
  have consolidation := trace.consolidation.stateInv_and_sum_le_admitted_semIn
    (benv := benv.withState trace.withdrawalState) preserves
    (by simpa only [Benv.withState] using hF) (by simpa only [Benv.withState] using hsg)
    admitted.consolidation withdrawalInv K image
  rw [trace.state_eq_consolidationState]
  exact ⟨consolidation.1, le_trans consolidation.2 withdrawal.2⟩

/-- A beacon stage: skipped is the identity, called is the retained system message. -/
theorem BeaconStageTrace.stateInv_and_sum_le_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  cases trace with
  | skipped => exact ⟨inv.state, le_rfl⟩
  | called _ _ message _ _ =>
      exact message.stateInv_and_sum_le_admitted_semIn preserves hF hsg admitted inv K image

/-- A history-storage stage: skipped is the identity, called is the retained system message. -/
theorem HistoryStageTrace.stateInv_and_sum_le_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  cases trace with
  | skipped => exact ⟨inv.state, le_rfl⟩
  | called _ _ _ _ message _ _ =>
      exact message.stateInv_and_sum_le_admitted_semIn preserves hF hsg admitted inv K image

/-- A request stage: skipped is the identity, called is the two retained checked calls. -/
theorem RequestStageTrace.stateInv_and_sum_le_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal := by
  cases trace with
  | skipped => exact ⟨inv.state, le_rfl⟩
  | called _ requests _ =>
      exact requests.stateInv_and_sum_le_admitted_semIn preserves hF hsg admitted inv K image

/-- The reward-funding premise of one staged body, at its actual request-stage state. -/
def StagedBodyTrace.RewardCreditsFunded
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) : Prop :=
  ∀ pow, benv.stat.rules.pow = some pow →
    Blanc.RewardCreditsFunded pow benv.stat.number benv.stat.coinbase ommers trace.requestState

/-- **Historical staged-body preservation**, in D1 stage order: beacon, history, the selected
transaction list, withdrawals (fork-free donor), requests, then `payRewards` credits. Withdrawal
funding comes from the body bound; reward funding is the explicit Mac-owned premise. -/
theorem StagedBodyTrace.stateInv_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (rewards : trace.RewardCreditsFunded)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca state := by
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_semIn
    preserves hF hsg admitted.beacon inv K image
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, by simpa only [Benv.withState] using inv.ca⟩
  have history := trace.history.stateInv_and_sum_le_admitted_semIn
    preserves (by simpa only [Benv.withState] using hF)
    (by simpa only [Benv.withState] using hsg) admitted.history beaconInv K image
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historyLe : sum trace.historyState.bal ≤ sum benv.state.bal :=
    le_trans (by simpa only [Benv.withState] using history.2) beacon.2
  have transactionsInv : c.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv_admitted_semIn preserves
      (by simpa only [Benv.withState] using hF) (by simpa only [Benv.withState] using hsg)
      admitted.transactions (by change sum trace.historyState.bal < 2 ^ 256; omega)
      historyInv K image
  have transactionLe : sum trace.transactionBenv.state.bal ≤ sum benv.state.bal :=
    le_trans (trace.transactions.sum_le_noStateGas (by simpa only [Benv.withState] using hsg))
      historyLe
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have withdrawalInv : c.BenvInv ca (trace.transactionBenv.withState trace.withdrawalState) := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact ⟨transactionsInv.state, by simpa only [Benv.withState] using transactionsInv.ca⟩
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1]
        exact benvInv_processWithdrawalsState_sem transactionsInv (by omega)
  have requests := trace.requests.stateInv_and_sum_le_admitted_semIn preserves
    (by change F trace.transactionBenv.stat.fork; rw [txStat]; exact hF)
    (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    admitted.requests withdrawalInv K image
  rw [trace.finalState_eq]
  have rewardEq := trace.rewardState_eq
  cases hpow : benv.stat.rules.pow with
  | none =>
      rw [hpow] at rewardEq
      rw [rewardEq]
      exact requests.1
  | some pow =>
      rw [hpow] at rewardEq
      rw [rewardEq]
      exact StateInv.payRewards (rewards pow hpow) requests.1

/-! ## Configured In-blocks and In-histories -/

/-- The reward-funding premise of one retained configured block. -/
def ConfiguredBlockTraceIn.RewardCreditsFunded {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post) : Prop :=
  trace.bodyTrace.RewardCreditsFunded

/-- **Historical configured-block preservation**: per-block domain membership and
`stateGas = none` from `forkIn` and `BodyStageCapabilities F`, withdrawal funding from the retained
reward-inclusive bound, reward funding from the Mac-owned premise, post state via `postEq`. -/
theorem ConfiguredBlockTraceIn.stateInv_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : trace.FrameAdmitted ca entry)
    (rewards : trace.RewardCreditsFunded)
    (inv : c.StateInv ca pre.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca post.state := by
  have hstate := trace.bodyTrace.stateInv_admitted_semIn preserves trace.forkIn
    (capabilities.stateGas_none trace.forkIn) admitted trace.withdrawalsBound rewards
    ⟨inv, AdrSet.not_mem_empty⟩ K image
  rw [trace.postEq]
  exact hstate

/-- The reward-funding premise at every block of a retained history. -/
def ConfiguredHistoryTraceIn.RewardCreditsFunded {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.RewardCreditsFunded ∧ block.RewardCreditsFunded

/-- **Historical configured-history preservation** by refl/step induction. -/
theorem ConfiguredHistoryTraceIn.stateInv_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : history.FrameAdmitted ca entry)
    (rewards : history.RewardCreditsFunded)
    (inv : c.StateInv ca checkpoint.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca future.state := by
  induction history with
  | refl => exact inv
  | step prior block ih =>
      exact block.stateInv_admitted_semIn preserves capabilities admitted.2 rewards.2
        (ih admitted.1 rewards.1) K image

end ExecutionTrace

namespace ExecutionTrace

open ContractSpec

variable {c : ContractSpec}

/-- `ContractSpec` form of `StagedBodyTrace.stateInv_admitted_semIn`. -/
theorem StagedBodyTrace.stateInv_admittedIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (rewards : trace.RewardCreditsFunded)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : Prog.compile c.prog = some C.toList) :
    c.StateInv ca state :=
  stateInv_ofSem (trace.stateInv_admitted_semIn (c := c.toSem)
    (preservesAdmittedIn_toSem c ca entry preserves) hF hsg admitted bound rewards
    (benvInv_toSem inv) K image)

/-- `ContractSpec` form of `ConfiguredBlockTraceIn.stateInv_admitted_semIn`. -/
theorem ConfiguredBlockTraceIn.stateInv_admittedIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : trace.FrameAdmitted ca entry)
    (rewards : trace.RewardCreditsFunded)
    (inv : c.StateInv ca pre.state)
    (K : InstalledCert C) (image : Prog.compile c.prog = some C.toList) :
    c.StateInv ca post.state :=
  stateInv_ofSem (trace.stateInv_admitted_semIn (c := c.toSem)
    (preservesAdmittedIn_toSem c ca entry preserves) capabilities admitted rewards
    (stateInv_toSem inv) K image)

/-- `ContractSpec` form of `ConfiguredHistoryTraceIn.stateInv_admitted_semIn`. -/
theorem ConfiguredHistoryTraceIn.stateInv_admittedIn {F : Fork → Prop} {C : ByteArray}
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : history.FrameAdmitted ca entry)
    (rewards : history.RewardCreditsFunded)
    (inv : c.StateInv ca checkpoint.state)
    (K : InstalledCert C) (image : Prog.compile c.prog = some C.toList) :
    c.StateInv ca future.state :=
  stateInv_ofSem (history.stateInv_admitted_semIn (c := c.toSem)
    (preservesAdmittedIn_toSem c ca entry preserves) capabilities admitted rewards
    (stateInv_toSem inv) K image)

end ExecutionTrace

end Blanc
