import Blanc.ExecutionHistoryInSystemCodeKeep
import Blanc.ExecutionHistoryInSystemOpenings
import Blanc.ExecutionTraceCalldata

/-!
# Present code is never a CREATE target along selected-domain (`In`) histories

The CREATE-avoidance premise of the code-keep chain
(`Exec.codeAt_avoid_noStateGas` and its lifts: no frame without a code address
targets `a`) is derived here from the code at `a` itself. A nested CREATE spawns
only after its EIP-684 collision check found empty code at the new address
(`genericCreate.step_spawn_frame`), and a top-level creation runs only when
`messageCreateCollision` is false, so the target is unprotected
(`messageCreateCollision_false_target_unprotected`). Every call-family frame
carries a code address, so it is never a CREATE frame.

Each layer is a joint induction with the existing keep: nonempty code at the
start of a sub-run excludes CREATE frames at `a` in it, and that exclusion keeps
the code for the next sub-run. The block and history forms run on
Cancun-onwards forks, where the existing keep applies; the installed-target form
`ConfiguredBlockTraceIn.installedNoFrame_of_opening` discharges
`ConfiguredBlockTraceIn.InstalledNoFrame` from the block's actual opening code.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune

/-! ## Delegation keeps the code address -/

/-- A delegation step never touches the code address. -/
theorem setDelegationStep_codeAddress {auth : Auth} {msg : Msg} {rc : B256}
    {p : Msg × B256} (h : setDelegationStep auth msg rc = .ok p) :
    p.1.codeAddress = msg.codeAddress := by
  unfold setDelegationStep at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases hrec : recoverAuthority auth with
      | error err =>
        cases err <;> simp only [hrec] at h
        all_goals (cases h; try rfl)
      | ok authority =>
        simp only [hrec] at h
        repeat' split at h
        all_goals (cases h; rfl)

/-- The delegation loop never touches the code address. -/
theorem setDelegationLoop_codeAddress :
    ∀ (auths : List Auth) {msg : Msg} {rc : B256} {p : Msg × B256},
      setDelegationLoop auths msg rc = .ok p → p.1.codeAddress = msg.codeAddress
  | [], _, _, _, hp => by cases hp; rfl
  | _ :: _, _, _, _, hp => by
    unfold setDelegationLoop at hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    exact (setDelegationLoop_codeAddress _ hp).trans (setDelegationStep_codeAddress hq)

/-- The call wrapper's delegation keeps the code address. -/
theorem messageCallDelegation_codeAddress {msg : Msg} {p : Msg × Nat}
    (h : messageCallDelegation msg = .ok p) : p.1.codeAddress = msg.codeAddress := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at h
  split at h
  · cases h; rfl
  · obtain ⟨q, hq, h⟩ := Except.bind_eq_ok h
    unfold setDelegation at hq
    obtain ⟨⟨q1, q2⟩, hq1, hq⟩ := Except.bind_eq_ok hq
    have h1 := setDelegationLoop_codeAddress _ hq1
    dsimp only at hq
    split at hq
    · obtain ⟨_, hbad, _⟩ := Except.bind_eq_ok hq
      cases hbad
    · cases hq
      dsimp only at h
      cases h
      exact h1

/-- Resolving a delegation designator only ever sets a code address. -/
theorem messageCallExecutionMessage_codeAddress_ne_none {msg : Msg}
    (h : msg.codeAddress ≠ none) : (messageCallExecutionMessage msg).codeAddress ≠ none := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  split
  · exact h
  · exact Option.some_ne_none _

/-- A transaction message has no code address only for a creation. -/
theorem prepareMessage_target_of_codeAddress {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h : prepareMessage benv tenv tx = .ok msg) :
    msg.codeAddress = none → msg.target.isNone = true := by
  intro hnone
  unfold prepareMessage at h
  cases hr : tx.type.receiver? with
  | none =>
      simp only [hr] at h
      obtain rfl := Except.ok.inj h
      simp only [Option.isNone_none]
  | some t =>
      simp only [hr] at h
      obtain rfl := Except.ok.inj h
      cases hnone

/-! ## The interpreter -/

/-- A call-family child frame has a code address. -/
theorem genericCall.step_spawn_codeAddress_ne_none
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool}
    {f : Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress stv isSt ii isz oi osz
      code dp = .spawn f rsm) :
    f.inner.codeAddress ≠ none := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals exact Option.some_ne_none _

/-- A child frame without a code address is a CREATE-family frame, under `stateGas = none`. -/
theorem Xinst.step_spawn_isCreate_of_codeAddress_noStateGas {sevm : Sevm} {devm : Devm}
    {x : Xinst} (hsg : sevm.benvStat.rules.stateGas = none) {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm) (hnone : f.inner.codeAddress = none) :
    f.isCreate = true := by
  rcases Xinst.step_shapeNoStateGas sevm devm x hsg with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · exact genericCreate.step_spawn_isCreate hs
  · exact absurd hnone (genericCall.step_spawn_codeAddress_ne_none hs)

/-- An instruction run on a world with nonempty code at `a` enters no CREATE frame at `a`:
a nested CREATE spawns only after finding empty code at its new address. -/
theorem Xinst.avoidsAt_of_code_noStateGas {a : Adr} {sevm : Sevm} {devm : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none) (hcode : (devm.getCode a).toList ≠ [])
    (x : Xinst) : Xinst.AvoidsAt a sevm devm x := by
  intro f rsm cevm hs _ hc
  rcases Xinst.step_shapeNoStateGas sevm devm x hsg with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · obtain ⟨-, target, empty⟩ := genericCreate.step_spawn_frame hs
    intro hat
    rw [target] at hat
    subst hat
    apply hcode
    rw [hf.getCode, empty]
    simp
  · exact absurd (genericCall.step_spawn_isCreate_false hs) (by rw [hc]; decide)

/-- **An execution that starts with nonempty code at `a` enters no CREATE frame at `a`**,
given that its own frame is not one. -/
theorem Exec.createAvoid_noStateGas {a : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (hcode : (pre.getCode a).toList ≠ [])
    (self : sevm.codeAddress = none → sevm.currentTarget ≠ a) :
    ∀ root ∈ Exec.rawFrameRoots run,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a := by
  revert hsg hcode self
  induction run with
  | halt hstep =>
      intro hsg hcode self root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact self
  | @cont pc sevm devm pc' devm' ex hstep next ih =>
      intro hsg hcode self
      have hc : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none) (out := .ok _)
        hsg (fun x _ => Xinst.avoidsAt_of_code_noStateGas hsg hcode x)
        trivial (by rw [hstep]; exact ⟨rfl, rfl⟩)
      have rest := ih hsg (by
        have h : devm'.getCode a = devm.getCode a := hc
        rw [h]; exact hcode) self
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact self
      · exact rest root (by simp only [Exec.rawFrameRoots, List.mem_cons, member, or_true])
  | doneErr hstep henter hresume =>
      intro hsg hcode self root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact self
  | @doneOk pc sevm devm f rsm pc' r devm' ex hstep henter hresume next ih =>
      intro hsg hcode self
      have hc : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none) (out := .ok _) hsg
        (fun x _ => Xinst.avoidsAt_of_code_noStateGas hsg hcode x)
        trivial (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hresume.symm⟩)
      have rest := ih hsg (by
        have h : devm'.getCode a = devm.getCode a := hc
        rw [h]; exact hcode) self
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact self
      · exact rest root (by simp only [Exec.rawFrameRoots, List.mem_cons, member, or_true])
  | @runErr pc sevm devm f rsm pc' cevm raw e hstep henter child hresume ih =>
      intro hsg hcode self
      have hsg_c : cevm.sta.benvStat.rules.stateGas = none := by
        rw [Evm.step_spawn_child_benvStat hstep henter]
        exact hsg
      have hstart := (Evm.step_spawn_child hstep henter).2.1 a
      have hcodeEq : cevm.sta.codeAddress = f.inner.codeAddress := by
        obtain ⟨benv, -, h⟩ := Frame.enter_run_inv henter
        rw [h]
        rfl
      obtain ⟨x, -, hxs, -⟩ := Evm.step_spawn_inv hstep
      have childSelf : cevm.sta.codeAddress = none → cevm.sta.currentTarget ≠ a := by
        intro hnone
        rw [Frame.enter_run_currentTarget henter]
        exact Xinst.avoidsAt_of_code_noStateGas hsg hcode x f rsm cevm hxs henter
          (Xinst.step_spawn_isCreate_of_codeAddress_noStateGas hsg hxs (hcodeEq ▸ hnone))
      have rest := ih hsg_c (by rw [hstart]; exact hcode) childSelf
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact self
      · exact rest root (by simpa only [Exec.rawFrameRoots, List.mem_cons] using member)
  | @runOk pc sevm devm f rsm pc' cevm raw devm' ex hstep henter child hresume next
      ihChild ihNext =>
      intro hsg hcode self
      have hsg_c : cevm.sta.benvStat.rules.stateGas = none := by
        rw [Evm.step_spawn_child_benvStat hstep henter]
        exact hsg
      have hstart := (Evm.step_spawn_child hstep henter).2.1 a
      have hcodeEq : cevm.sta.codeAddress = f.inner.codeAddress := by
        obtain ⟨benv, -, h⟩ := Frame.enter_run_inv henter
        rw [h]
        rfl
      obtain ⟨x, -, hxs, -⟩ := Evm.step_spawn_inv hstep
      have childSelf : cevm.sta.codeAddress = none → cevm.sta.currentTarget ≠ a := by
        intro hnone
        rw [Frame.enter_run_currentTarget henter]
        exact Xinst.avoidsAt_of_code_noStateGas hsg hcode x f rsm cevm hxs henter
          (Xinst.step_spawn_isCreate_of_codeAddress_noStateGas hsg hxs (hcodeEq ▸ hnone))
      have childAvoid := ihChild hsg_c (by rw [hstart]; exact hcode) childSelf
      obtain ⟨hrelChild, -⟩ := Exec.codeAt_avoid_noStateGas child hsg_c childAvoid
      have hc : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .some ⟨_, _⟩)
        (out := .ok _) hsg (fun x _ => Xinst.avoidsAt_of_code_noStateGas hsg hcode x)
        hrelChild (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
      have rest := ihNext hsg (by
        have h : devm'.getCode a = devm.getCode a := hc
        rw [h]; exact hcode) self
      intro root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | rfl | member | member
      · exact self
      · exact childAvoid _ (by simp only [Exec.rawFrameRoots, List.mem_cons, true_or])
      · exact childAvoid root (by simp only [Exec.rawFrameRoots, List.mem_cons, member, or_true])
      · exact rest root (by simp only [Exec.rawFrameRoots, List.mem_cons, member, or_true])

/-! ## Messages -/

/-- A retained frame slot whose frame starts with nonempty code at `a` enters no CREATE frame
at `a`, given that the frame itself is not one. -/
theorem RetainedXlot.createAvoid_noStateGas
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} {a : Adr}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (hsg : frame.inner.benv.stat.rules.stateGas = Option.none)
    (hcode : (frame.inner.benv.state.getCode a).toList ≠ [])
    (self : frame.inner.codeAddress = Option.none → frame.inner.currentTarget ≠ a) :
    ∀ root ∈ retained.rawFrames, root.sevm.codeAddress = Option.none →
      root.sevm.currentTarget ≠ a := by
  cases retained with
  | none => intro root member; simp only [RetainedXlot.rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hstat := Frame.enter_run_benvStat henter
      have hpre := Frame.enter_run_getCode henter a
      have hca : sevm.codeAddress = frame.inner.codeAddress := by
        obtain ⟨benv, -, h⟩ := Frame.enter_run_inv henter
        have := congrArg (fun e : Evm => e.sta.codeAddress) h
        exact this
      exact Exec.createAvoid_noStateGas run (by rw [hstat]; exact hsg)
        (by rw [hpre]; exact hcode)
        (fun hnone => by
          rw [Frame.enter_run_currentTarget henter]
          exact self (hca ▸ hnone))

/-- A settled message call starting with nonempty code at `a` enters no CREATE frame at `a`.
A call carries a code address; a creation passed its collision check. -/
theorem MessageCallTrace.createAvoid_noStateGas
    {a : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hcall : msg.codeAddress = none → msg.target.isNone = true)
    (hauth : msg.benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ msg.tenv.stat.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (hcode : (msg.benv.state.getCode a).toList ≠ []) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a := by
  cases trace with
  | createCollision target collision result =>
      intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | createRun target collision evm core coreTrace result =>
      have unprotected := messageCreateCollision_false_target_unprotected collision
      have targetNe : msg.currentTarget ≠ a := by
        intro hat
        rw [hat] at unprotected
        exact unprotected (State.Protected.of_code_ne_nil hcode)
      exact RetainedXlot.createAvoid_noStateGas coreTrace.retained coreTrace.run
        (by
          change (processCreateMessage.msg msg).benv.stat.rules.stateGas = none
          rw [processCreateMessage.msg_benvStat]; exact hsg)
        (by
          change ((processCreateMessage.msg msg).benv.state.getCode a).toList ≠ []
          rw [processCreateMessage.msg_getCode]; exact hcode)
        (fun _ => targetNe)
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      have hsgExec : execMsg.benv.stat.rules.stateGas = none := by
        rw [execMsgEq, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat delegation]
        exact hsg
      have hcodeExec : execMsg.benv.state.getCode a = msg.benv.state.getCode a := by
        rcases hauth with hdis | hauth
        · have hleg : messageCallDelegation msg = .ok ⟨msg, 0⟩ :=
            processMessageCall.legacyAuthorization_disabled msg hdis
          have hdel : delegated = msg :=
            (Prod.mk.inj (Except.ok.inj (hleg.symm.trans delegation))).1.symm
          rw [execMsgEq, hdel]
          exact messageCallExecutionMessage_getCode msg a
        · rw [execMsgEq, messageCallExecutionMessage_getCode]
          exact messageCallDelegation_getCode hauth delegation
      have hcaMsg : msg.codeAddress ≠ none := fun hnone => by
        have := hcall hnone
        rw [target] at this
        cases this
      have hcaExec : execMsg.codeAddress ≠ none := by
        rw [execMsgEq]
        apply messageCallExecutionMessage_codeAddress_ne_none
        rw [messageCallDelegation_codeAddress delegation]
        exact hcaMsg
      exact RetainedXlot.createAvoid_noStateGas coreTrace.retained coreTrace.run hsgExec
        (by change (execMsg.benv.state.getCode a).toList ≠ []; rw [hcodeExec]; exact hcode)
        (fun hnone => absurd hnone hcaExec)

/-! ## Transactions and system messages -/

/-- A transaction starting with nonempty code at `a` enters no CREATE frame at `a`. -/
theorem TransactionTrace.createAvoid_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hdis : benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
        authority ≠ a)
    (hne : (benv.state.getCode a).toList ≠ []) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a := by
  have hbenv := prepareMessage_benv trace.prepared
  obtain ⟨htenv, -⟩ := prepareMessage_fields trace.prepared
  have hdebit : trace.debitState.getCode a = benv.state.getCode a := by
    have h1 := State.subBal_getCode trace.debit (a := a)
    rw [h1]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode a = benv.state.getCode a := by
    rw [hbenv]
    exact hdebit
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]
    exact hsg
  have hdis_msg : trace.msg.benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ trace.msg.tenv.stat.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a := by
    rcases hdis with hdis | hauth
    · exact Or.inl (by rw [hbenv]; exact hdis)
    · exact Or.inr (by
        rw [htenv]
        simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using hauth)
  exact trace.message.createAvoid_noStateGas hmsgSg
    (prepareMessage_target_of_codeAddress trace.prepared) hdis_msg
    (by rw [hmsgState]; exact hne)

/-- A transaction list starting with nonempty, non-delegating code at `a` enters no CREATE
frame at `a`: each transaction keeps the code for the next. -/
theorem ApplyTransactionsTrace.createAvoid_noStateGas
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (hflag : benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (hrefund : benv.stat.fork.ruleSet.settle.refundQuotient = 5)
    (hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false) {a : Adr}
    (hdis : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (hne : (benv.state.getCode a).toList ≠ [])
    (hnd : ¬ isValidDelegation (benv.state.getCode a))
    (notCreated : a ∉ benv.createdAccounts) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a := by
  induction trace with
  | nil => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      have hdis_head : benv.stat.rules.delegationEnabled = false ∨
          ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
            authority ≠ a := by
        rcases hdis with hdis | hdis
        · exact Or.inl hdis
        · exact Or.inr (hdis _ (List.mem_cons_self ..))
      have hdis_tail :
          (benv.withState txState).stat.rules.delegationEnabled = false ∨
            ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
              recoverAuthority auth = .ok authority → authority ≠ a := by
        rcases hdis with hdis | hdis
        · exact Or.inl hdis
        · exact Or.inr (fun p hp => hdis p (List.mem_cons_of_mem _ hp))
      have headAvoid := head.createAvoid_noStateGas hsg hdis_head hne
      obtain ⟨-, hstate⟩ := head.codeAt_keep_noStateGas hsg hflag hrefund hsweep
        hdis_head headAvoid hne hnd notCreated
      have hcode : (benv.withState txState).state.getCode a = benv.state.getCode a :=
        hstate
      have tailAvoid := ih hsg hflag hrefund hsweep hdis_tail
        (by rw [hcode]; exact hne) (by rw [hcode]; exact hnd) notCreated
      intro root member
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact headAvoid root member
      · exact tailAvoid root member

/-- A system message starting with nonempty code at `a` enters no CREATE frame at `a`. -/
theorem SystemMessageTrace.createAvoid_noStateGas
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hne : (benv.state.getCode a).toList ≠ []) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a := by
  have hmsgSg : (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    unfold systemTransactionMessage processSystemTransactionMsg Benv.beginTransaction
    exact hsg
  have hcall : (systemTransactionMessage benv target data).codeAddress = none →
      (systemTransactionMessage benv target data).target.isNone = true := by
    intro h
    simp only [systemTransactionMessage, processSystemTransactionMsg, reduceCtorEq] at h
  have hdis : (systemTransactionMessage benv target data).benv.stat.rules.delegationEnabled =
      false ∨ ∀ auth ∈ (systemTransactionMessage benv target data).tenv.stat.auths,
        ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a := by
    refine Or.inr ?_
    intro auth hauth
    simp only [systemTransactionMessage, processSystemTransactionMsg, processSystemTransactionTenv,
      Std.TreeMap.empty_eq_emptyc, List.not_mem_nil] at hauth
  exact trace.message.createAvoid_noStateGas hmsgSg hcall hdis hne

/-- A beacon stage starting with nonempty code at `a` enters no CREATE frame at `a`. -/
theorem BeaconStageTrace.createAvoid_noStateGas
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hne : (benv.state.getCode a).toList ≠ []) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ message _ _ => exact message.createAvoid_noStateGas hsg hne

/-- A history-storage stage starting with nonempty code at `a` enters no CREATE frame at `a`. -/
theorem HistoryStageTrace.createAvoid_noStateGas
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hne : (benv.state.getCode a).toList ≠ []) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ _ _ message _ _ => exact message.createAvoid_noStateGas hsg hne

/-- A request stage starting with nonempty code at `a` enters no CREATE frame at `a`. -/
theorem RequestStageTrace.createAvoid_noStateGas
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hne : (benv.state.getCode a).toList ≠ []) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ requests _ =>
      have first := requests.withdrawal.createAvoid_noStateGas hsg hne
      obtain ⟨hw, -⟩ := requests.withdrawal.codeAt_empty_noStateGas hsg first
      have second := requests.consolidation.createAvoid_noStateGas
        (benv := benv.withState requests.withdrawalState) hsg
        (by change (requests.withdrawalState.getCode a).toList ≠ []; rw [hw]; exact hne)
      intro root member
      simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact first root member
      · exact second root member

/-! ## Bodies, blocks and histories -/

/-- **A staged body starting with canonical (nonempty, non-delegating) code at `a` enters no
CREATE frame at `a`**: each stage keeps the code for the next. -/
theorem StagedBodyTrace.createAvoid_noStateGas
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (hflag : benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (hrefund : benv.stat.fork.ruleSet.settle.refundQuotient = 5)
    (hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false)
    {a : Adr} {c : ByteArray}
    (hdis : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (hkeep : benv.state.getCode a = c)
    (hc_ne : c.toList ≠ [])
    (hc_nd : ¬ isValidDelegation c)
    (notCreated : a ∉ benv.createdAccounts) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a := by
  have avoidBeacon := trace.beacon.createAvoid_noStateGas hsg (by rw [hkeep]; exact hc_ne)
  have hbeacon : trace.beaconState.getCode a = c :=
    trace.beacon.codeAt_keep_noStateGas hsg hkeep avoidBeacon
  have avoidHistory := trace.history.createAvoid_noStateGas
    (benv := benv.withState trace.beaconState) hsg
    (by change (trace.beaconState.getCode a).toList ≠ []; rw [hbeacon]; exact hc_ne)
  have hhistory : trace.historyState.getCode a = c :=
    trace.history.codeAt_keep_noStateGas (benv := benv.withState trace.beaconState)
      hsg hbeacon avoidHistory
  have hstart : ((benv.withState trace.beaconState).withState
      trace.historyState).state.getCode a = c := by
    simpa only [Benv.withState] using hhistory
  have hne : (((benv.withState trace.beaconState).withState
      trace.historyState).state.getCode a).toList ≠ [] := by
    rw [hstart]
    exact hc_ne
  have hnd : ¬ isValidDelegation (((benv.withState trace.beaconState).withState
      trace.historyState).state.getCode a) := by
    rw [hstart]
    exact hc_nd
  have avoidTx := trace.transactions.createAvoid_noStateGas (benv :=
      (benv.withState trace.beaconState).withState trace.historyState)
    hsg hflag hrefund hsweep hdis hne hnd notCreated
  have hfinalTx : trace.transactionBenv.state.getCode a = c :=
    (trace.transactions.codeAt_keep_noStateGas (benv :=
        (benv.withState trace.beaconState).withState trace.historyState)
      hsg hflag hrefund hsweep hdis avoidTx hne hnd notCreated).trans hstart
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have hwithdrawal : trace.withdrawalState.getCode a = c := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact hfinalTx
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
        exact hfinalTx
  have avoidRequests := trace.requests.createAvoid_noStateGas
    (benv := trace.transactionBenv.withState trace.withdrawalState)
    (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    (by change (trace.withdrawalState.getCode a).toList ≠ []; rw [hwithdrawal]; exact hc_ne)
  intro root member
  simp only [StagedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact avoidBeacon root member
  · exact avoidHistory root member
  · exact avoidTx root member
  · exact avoidRequests root member

/-- **A retained `In`-block on a Cancun-onwards fork that opens with canonical code at `a`
enters no CREATE frame at `a`.** -/
theorem ConfiguredBlockTraceIn.createAvoid_of_cancunOnwards
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (hHist : HistFork trace.fork) (hC : CancunOnwards trace.fork)
    {a : Adr} {c : ByteArray}
    (hdis : trace.fork.ruleSet.delegationEnabled = false ∨
      ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
        ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a)
    (hkeep : pre.state.getCode a = c)
    (hc_ne : c.toList ≠ [])
    (hc_nd : ¬ isValidDelegation c) :
    ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a :=
  trace.bodyTrace.createAvoid_noStateGas
    (capabilities.stateGas_none trace.forkIn)
    (HistFork.selfdestructOnlyCreated_of_cancunOnwards hHist hC)
    (HistFork.refundQuotient_five_of_cancunOnwards hHist hC)
    (HistFork.touchedSweep_false_of_cancunOnwards hHist hC)
    hdis hkeep hc_ne hc_nd AdrSet.not_mem_empty

/-- **A retained historical block opening with its fork's installed system code enters no
CREATE frame at an installed system contract**: vacuous before Cancun; from Cancun on the
installed code is canonical, so CREATE collides there. -/
theorem ConfiguredBlockTraceIn.installedNoFrame_of_opening
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn HistFork cfg pre post)
    (opening : trace.SystemCodeAtOpening)
    (hauth : ∀ p ∈ systemContracts, trace.PragueNoAuthorityAt p.1) :
    trace.InstalledNoFrame := by
  intro q hq
  rcases trace.forkIn.preCancun_cancunOnwards with hpreC | hC
  · rw [HistFork.installedAt_empty_of_preCancun trace.forkIn hpreC] at hq
    simp only [List.not_mem_nil] at hq
  · have hqmem := mem_systemContracts_of_mem_installedAt trace.forkIn hq
    have hqfacts := systemContracts_facts q hqmem
    have hdis : trace.fork.ruleSet.delegationEnabled = false ∨
        ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
          ∀ authority, recoverAuthority auth = .ok authority → authority ≠ q.1 := by
      by_cases hpp : PrePrague trace.fork
      · exact Or.inl (trace.forkIn.delegationDisabled_of_prePrague hpp)
      · exact Or.inr (hauth q hqmem hpp)
    exact trace.createAvoid_of_cancunOnwards BodyStageCapabilities.historical trace.forkIn hC
      hdis (opening q hq) hqfacts.2.2 hqfacts.2.1

/-- A retained historical history opening every block with its fork's installed system code
enters no CREATE frame at an installed system contract. -/
theorem ConfiguredHistoryTraceIn.installedNoFrame_of_openings
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (openings : history.SystemCodeAtOpenings)
    (hauth : ∀ p ∈ systemContracts, history.PragueNoAuthorityAt p.1) :
    history.InstalledNoFrame := by
  induction history with
  | refl => trivial
  | step prior block ih =>
      exact ⟨ih openings.1 (fun p hp => (hauth p hp).1),
        block.installedNoFrame_of_opening openings.2 (fun p hp => (hauth p hp).2)⟩

/-- **The actual Cancun spine obtains every opening from one initial beacon-code anchor**,
with no frame-exclusion premise: the present beacon-roots code excludes CREATE at it. -/
theorem ConfiguredHistoryTraceIn.systemCodeAtOpenings_of_cancun_present
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (forks : trace.ForksSatisfy (fun f => f = .cancun))
    (installed : checkpoint.state.getCode beaconRootsAddress = beaconRootsCode) :
    trace.SystemCodeAtOpenings ∧ future.state.getCode beaconRootsAddress = beaconRootsCode := by
  induction trace with
  | refl => exact ⟨trivial, installed⟩
  | step prior block ih =>
      obtain ⟨priorOpenings, priorCode⟩ := ih forks.1
      have opening : block.SystemCodeAtOpening := by
        intro p member
        rw [HistFork.installedAt_beacon_of_cancun block.forkIn forks.2] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        subst p
        exact priorCode
      have facts := systemContracts_facts _ beaconRoots_mem_systemContracts
      have hC : CancunOnwards block.fork := by rw [forks.2]; decide
      have hdis : block.fork.ruleSet.delegationEnabled = false ∨
          ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ beaconRootsAddress :=
        Or.inl (block.forkIn.delegationDisabled_of_prePrague (by rw [forks.2]; decide))
      have avoid := block.createAvoid_of_cancunOnwards BodyStageCapabilities.historical
        block.forkIn hC hdis priorCode facts.2.2 facts.2.1
      have keep := block.codeAt_keep_of_cancunOnwards BodyStageCapabilities.historical
        block.forkIn hC hdis avoid priorCode facts.2.2 facts.2.1
      exact ⟨⟨priorOpenings, opening⟩, keep⟩

/-- **A modern configured history opening with the canonical system code keeps it and enters
no CREATE frame at any system contract**: CREATE collides with the present code. Delegation
to a system address remains excluded by the no-authority premise. -/
theorem ConfiguredHistoryTrace.systemCreateAvoid
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : SystemCodeInstalled checkpoint.state)
    (hauth : ∀ p ∈ systemContracts, history.NoAuthorityAt p.1) :
    SystemCodeInstalled future.state ∧
      ∀ p ∈ systemContracts, ∀ root ∈ history.rawFrames, root.sevm.codeAddress = none →
        root.sevm.currentTarget ≠ p.1 := by
  induction history with
  | refl => exact ⟨installed, fun p _ root member => by
      simp only [ConfiguredHistoryTrace.rawFrames, List.not_mem_nil] at member⟩
  | step prior block ih =>
      obtain ⟨priorInstalled, priorAvoid⟩ := ih (fun p hp => (hauth p hp).1)
      have hHist : HistFork block.toIn.fork := block.covered.histFork
      have hC : CancunOnwards block.toIn.fork := by
        have covered : CoveredFork block.toIn.fork := block.covered
        revert covered
        generalize block.toIn.fork = f
        cases f <;> decide
      have blockFacts : ∀ p ∈ systemContracts,
          (∀ root ∈ block.rawFrames, root.sevm.codeAddress = none →
            root.sevm.currentTarget ≠ p.1) ∧ _ := fun p hp => by
        have facts := systemContracts_facts p hp
        have hdis : block.toIn.fork.ruleSet.delegationEnabled = false ∨
            ∀ q ∈ block.toIn.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ q.2.auths,
              ∀ authority, recoverAuthority auth = .ok authority → authority ≠ p.1 :=
          Or.inr (hauth p hp).2
        have avoid := block.toIn.createAvoid_of_cancunOnwards BodyStageCapabilities.covered
          hHist hC hdis (priorInstalled p hp) facts.2.2 facts.2.1
        have keep := block.toIn.codeAt_keep_of_cancunOnwards BodyStageCapabilities.covered
          hHist hC hdis avoid (priorInstalled p hp) facts.2.2 facts.2.1
        rw [ConfiguredBlockTrace.toIn_rawFrames] at avoid
        exact ⟨avoid, keep⟩
      refine ⟨fun p hp => (blockFacts p hp).2, fun p hp root member => ?_⟩
      simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact priorAvoid p hp root member
      · exact (blockFacts p hp).1 root member

end ExecutionTrace

end Blanc
