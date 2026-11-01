-- CommonProofs/Messages.lean : message-level code-effect masters, step shapes and lift cores.

import Blanc.CommonProofs.Frames

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

/-! ## Step 7.2 — message-level code-effect masters

Relational code-preservation over message results.  `CodePreserve` says every
nonempty-code address is left untouched; `CodePreserveExcept w` weakens that by
also excluding the single write target `w` (the freshly-created contract). -/

def MsgResult.CodePreserve (base : State)
    (exn : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a : Adr, (base.getCode a).toList ≠ [] → MsgResult.getCode exn a = base.getCode a

def MsgResult.CodePreserveExcept (base : State) (w : Adr)
    (exn : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a : Adr, a ≠ w → (base.getCode a).toList ≠ [] →
    MsgResult.getCode exn a = base.getCode a

/-- Relational code-preservation over an `Execution` outcome (used by the
Step 7.3 generic-operation masters): every nonempty-code address of `base` has
the same code in the result, on both the ok and error branches. -/
def Execution.CodePreserve (base : Devm) (exn : Execution) : Prop :=
  ∀ a : Adr, (base.getCode a).toList ≠ [] → Execution.getCode exn a = base.getCode a

/-- Writer leaf: `handleError` reshuffles error payloads into ok results and
selects states, but never installs new code. -/
lemma executeCode.handleError_code_created (exn : Execution) (a : Adr) :
    MsgResult.getCode (executeCode.handleError exn) a = Execution.getCode exn a ∧
      MsgResult.createdAccounts (executeCode.handleError exn) = Execution.createdAccounts exn := by
  cases exn with
  | ok d => exact ⟨rfl, rfl⟩
  | error p =>
    rcases p with ⟨err, evm⟩
    cases err <;> exact ⟨rfl, rfl⟩

lemma executeCode.handleError_getCode (exn : Execution) (a : Adr) :
    MsgResult.getCode (executeCode.handleError exn) a = Execution.getCode exn a := by
  exact (executeCode.handleError_code_created exn a).1

lemma executeCode.handleErrorWith_code_created (sg : Option StateGasRules)
    (exn : Execution) (a : Adr) :
    MsgResult.getCode (executeCode.handleErrorWith sg exn) a =
      Execution.getCode exn a ∧
      MsgResult.createdAccounts (executeCode.handleErrorWith sg exn) = Execution.createdAccounts exn := by
  cases sg with
  | none => exact executeCode.handleError_code_created exn a
  | some _ =>
      cases exn with
      | ok d => exact ⟨rfl, rfl⟩
      | error p =>
          rcases p with ⟨err, evm⟩
          cases err <;> exact ⟨rfl, rfl⟩

lemma executeCode.handleErrorWith_getCode (sg : Option StateGasRules)
    (exn : Execution) (a : Adr) :
    MsgResult.getCode (executeCode.handleErrorWith sg exn) a =
      Execution.getCode exn a := by
  exact (executeCode.handleErrorWith_code_created sg exn a).1

/-- Writer leaf: rollback installs the selected state, so its code map is that
state's code map. -/
lemma Devm.rollback_getCode (devm : Devm) (st : State) (tra : Tra) (a : Adr) :
    (devm.rollback st tra).getCode a = st.getCode a := rfl

/-- **Frame-level state restoration.**  A message frame that settles `.ok` with
its error flag set has had its world rolled back to the values `msg` entered
with: `msg.benv.state` and `msg.tenv.transientStorage`.

**The frame named is `msg`'s own**, and naming it is the whole content of the
statement.  This is *not* "the transaction was rolled back", which would be a
different and often false claim — a failed inner call can be caught by its
caller while the surrounding transaction succeeds, and this theorem is
deliberately silent about every frame but `msg`'s.

**No error kind is named, and none can be.**  The hypothesis is
`out.error.isSome` and nothing more.  Two reasons, and both are load-bearing:
the settled error is `.ok`-level only, so nothing about *which* error occurred
survives the frame boundary; and a claim naming a failure shape would be
coupled to compiled bytes that this shared-layer lemma has no business knowing.

**This is not liveness and not a claim that any frame ever fails.**  Both
`ProcessMessage msg xl (.ok out)` and `out.error.isSome` are hypotheses.  The
theorem rules a world-state *in* given a settled error; it says nothing about
whether any particular message reaches one.

The mechanism is `processMessage.settle`, whose rollback arm installs exactly
these two components (`Devm.rollback` writes `world` and nothing else, so the
error flag it is conditioned on survives it untouched).  No slot derivation is
involved: the `out.error.isSome` hypothesis selects the rollback arm on its
own, which is why this needs neither `Xlot.Filled` nor anything above it. -/
theorem ProcessMessage.rollback_of_error {msg : Msg} {xl : Xlot} {out : Devm}
    (h : ProcessMessage msg xl (.ok out)) (herr : out.error.isSome) :
    out.state = msg.benv.state ∧
      out.transientStorage = msg.tenv.transientStorage := by
  obtain ⟨r0, -, hset⟩ := ProcessMessage.iff_body.mp h
  rcases r0 with x | evm'
  -- `processMessage.settle_error` says exactly this, but it is declared far
  -- below in this file; the settle of an `.error` reduces on its own.
  · cases hset
  unfold processMessage.settle at hset
  dsimp only [bind, Except.bind] at hset
  by_cases herr' : evm'.error.isSome = true
  · rw [ite_eq_left herr'] at hset
    rw [Except.ok.inj hset]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right herr'] at hset
    exfalso
    apply herr'
    rw [Except.ok.inj hset] at herr
    exact herr

/-- Settlement agrees on crypto failures: both fork handlers rethrow them. -/
lemma executeCode.handleErrorWith_crypto (sg : Option StateGasRules)
    (reason : CryptoError) (raw : Devm) :
    executeCode.handleErrorWith sg (.error (.crypto reason, raw)) =
      .error ⟨.crypto reason, raw.state, raw.createdAccounts,
        raw.transientStorage⟩ := by
  cases sg <;> rfl

/-- Settlement agrees on internal failures: both fork handlers rethrow them. -/
lemma executeCode.handleErrorWith_internal (sg : Option StateGasRules)
    (reason : InternalError) (raw : Devm) :
    executeCode.handleErrorWith sg (.error (.internal reason, raw)) =
      .error ⟨.internal reason, raw.state, raw.createdAccounts,
        raw.transientStorage⟩ := by
  cases sg <;> rfl

/-- A halted child settles to a handled devm with its error marker set, on
either fork handler. -/
lemma executeCode.handleErrorWith_halt_isSome (sg : Option StateGasRules)
    (reason : ExceptionalHalt) (raw : Devm) :
    ∃ handled : Devm,
      executeCode.handleErrorWith sg (.error (.halt reason, raw)) =
        .ok handled ∧ handled.error.isSome = true := by
  cases sg with
  | none =>
      simp only [executeCode.handleErrorWith, executeCode.handleError, Devm.setMeta,
        Except.ok.injEq, Devm.error, exists_eq_left', Option.isSome_some]
  | some _ =>
      simp only [executeCode.handleErrorWith, executeCode.handleErrorAmsterdam, Devm.setMeta,
        Except.ok.injEq, Devm.error, exists_eq_left', Option.isSome_some]

/-- A reverted child settles to a handled devm with its error marker set, on
either fork handler. -/
lemma executeCode.handleErrorWith_revert_isSome (sg : Option StateGasRules)
    (raw : Devm) :
    ∃ handled : Devm,
      executeCode.handleErrorWith sg (.error (.revert, raw)) =
        .ok handled ∧ handled.error.isSome = true := by
  cases sg with
  | none =>
      simp only [executeCode.handleErrorWith, executeCode.handleError, Devm.withError, Devm.setMeta,
        Except.ok.injEq, Devm.error, exists_eq_left', Option.isSome_some]
  | some _ =>
      simp only [executeCode.handleErrorWith, executeCode.handleErrorAmsterdam, Devm.withError,
        Devm.setMeta, Except.ok.injEq, Devm.error, exists_eq_left', Option.isSome_some]

/-- A clean retained child message installs exactly the committed raw child's
world state.  Message settlement changes only wrapper metadata on this path. -/
theorem ProcessMessage.ok_state_eq_committedPost
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hcommit : Execution.commits out = true) :
    post.state = (Execution.committedPost out hcommit).state := by
  have hsettle := (RunFrame.some_inv hprocess).2
  cases out with
  | error err =>
      simp only [Execution.commits, Bool.false_eq_true] at hcommit
  | ok raw =>
      simp only [Execution.commits] at hcommit
      cases herr : raw.error with
      | none =>
          simp only [Frame.settle, Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
            processMessage.settle, executeCode.handleErrorWith_ok, Except.bind_ok, herr,
            Option.isSome_none, Except.ok.injEq] at hsettle
          have hstate := congrArg Devm.state hsettle
          exact hstate
      | some error =>
          simp only [herr, Option.isNone_some, Bool.false_eq_true] at hcommit

/-- A raw child execution that does not commit is rolled back to the message
entry world before its parent resumes. -/
theorem ProcessMessage.ok_state_eq_of_not_commits
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hnot : Execution.commits out ≠ true) :
    post.state = msg.benv.state := by
  have hsettle := (RunFrame.some_inv hprocess).2
  cases out with
  | error err =>
      rcases err with ⟨error, raw⟩
      cases error with
      | halt reason =>
          rcases executeCode.handleErrorWith_halt_isSome
            msg.benv.stat.rules.stateGas reason raw with
            ⟨handled, hhandle, hhandled⟩
          have hsettle' :
              (.ok post) = processMessage.settle msg (.ok handled) := by
            simpa only [Frame.settle, Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
              hhandle] using hsettle
          unfold processMessage.settle at hsettle'
          simp only [bind, Except.bind] at hsettle'
          rw [ite_eq_left hhandled] at hsettle'
          have heq := Except.ok.inj hsettle'
          calc
            post.state =
                (handled.rollback msg.benv.state
                  msg.tenv.transientStorage).state :=
              by rw [heq]; rfl
            _ = msg.benv.state := rfl
      | revert =>
          rcases executeCode.handleErrorWith_revert_isSome
            msg.benv.stat.rules.stateGas raw with
            ⟨handled, hhandle, hhandled⟩
          have hsettle' :
              (.ok post) = processMessage.settle msg (.ok handled) := by
            simpa only [Frame.settle, Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
              hhandle] using hsettle
          unfold processMessage.settle at hsettle'
          simp only [bind, Except.bind] at hsettle'
          rw [ite_eq_left hhandled] at hsettle'
          have heq := Except.ok.inj hsettle'
          calc
            post.state =
                (handled.rollback msg.benv.state
                  msg.tenv.transientStorage).state :=
              by rw [heq]; rfl
            _ = msg.benv.state := rfl
      | crypto reason =>
          simp only [Frame.settle, Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
            processMessage.settle, executeCode.handleErrorWith_crypto, Except.bind_error,
            reduceCtorEq] at hsettle
      | internal reason =>
          simp only [Frame.settle, Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
            processMessage.settle, executeCode.handleErrorWith_internal, Except.bind_error,
            reduceCtorEq] at hsettle
  | ok raw =>
      cases herr : raw.error with
      | none =>
          simp only [Execution.commits, herr, Option.isNone_none, ne_eq, not_true_eq_false] at hnot
      | some error =>
          simp only [Frame.settle, Frame.settleMsg, Frame.ofCall, Bool.false_eq_true, ↓reduceIte,
            processMessage.settle, executeCode.handleErrorWith_ok, Except.bind_ok, herr,
            Option.isSome_some, Except.ok.injEq] at hsettle
          have hstate := congrArg Devm.state hsettle
          exact hstate

/-- Handling a synchronous precompile result preserves the message-entry world
state; precompiles only determine gas, output, and error metadata. -/
theorem executeCode.handle_precompile_ok_state
    {msg : Msg} {address : Adr} {post : Devm} {stateGas : Option StateGasRules}
    (h : executeCode.handleErrorWith stateGas
        (executePrecomp (initEvm msg) address) = .ok post) :
    post.state = msg.benv.state := by
  cases hsg : stateGas
  · simp only [hsg, executeCode.handleErrorWith] at h
    unfold executePrecomp applyPrecompResult at h
    cases hpre : precompileRun (initEvm msg) address with
    | error error cost =>
        simp only [hpre] at h
        cases error <;> simp only [executeCode.handleError, Except.ok.injEq, reduceCtorEq] at h
        · exact (congrArg Devm.state h).symm.trans rfl
        · exact (congrArg Devm.state h).symm.trans rfl
    | ok cost output =>
        simp only [executeCode.handleError, hpre, Except.ok.injEq] at h
        exact (congrArg Devm.state h).symm.trans rfl
  · simp only [hsg, executeCode.handleErrorWith] at h
    unfold executePrecomp applyPrecompResult at h
    cases hpre : precompileRun (initEvm msg) address with
    | error error cost =>
        simp only [hpre] at h
        cases error <;> simp only [executeCode.handleErrorAmsterdam, Except.ok.injEq, reduceCtorEq] at h
        · exact (congrArg Devm.state h).symm.trans rfl
        · exact (congrArg Devm.state h).symm.trans rfl
    | ok cost output =>
        simp only [executeCode.handleErrorAmsterdam, hpre, Except.ok.injEq] at h
        exact (congrArg Devm.state h).symm.trans rfl

/-- Successful CREATE code-gas charging preserves the frame error marker. -/
theorem processCreateMessage.chargeCodeGas_error_eq
    {rules : ForkRules} {pre post : Devm}
    (h : processCreateMessage.chargeCodeGas rules pre = .ok post) :
    post.error = pre.error := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · cases h
      · rcases Except.bind_eq_ok h with ⟨charged, hcharge, hrest⟩
        split at hrest
        · cases hrest
        · cases hrest
          rw [chargeGas_def] at hcharge
          split at hcharge
          · cases hcharge
          · cases hcharge
            rfl
    · rcases Except.bind_eq_ok h with ⟨charged, hcharge, hrest⟩
      split at hrest
      · cases hrest
      · cases hrest
        rw [chargeGas_def] at hcharge
        split at hcharge
        · cases hcharge
        · cases hcharge
          rfl
  · split at h
    · cases h
    · split at h
      · cases h
      · rcases Except.bind_eq_ok h with ⟨charged, hcharge, hrest⟩
        have h1 : charged.error = pre.error := by
          rw [chargeGas_def] at hcharge
          split at hcharge
          · cases hcharge
          · cases hcharge
            rfl
        exact (chargeStateGas_error_eq hrest).trans h1

/-- A CREATE frame that settles with its error marker set restores the world
saved at CREATE-message entry, including code-deposit failure. -/
theorem ProcessCreateMessage.rollback_of_error
    {msg : Msg} {slot : Xlot} {post : Devm}
    (hprocess : ProcessCreateMessage msg slot (.ok post))
    (herror : post.error.isSome = true) :
    post.state = msg.benv.state := by
  rcases ProcessCreateMessage.iff_processMessage.mp hprocess with
    ⟨result, _hinner, hsettle⟩
  cases result with
  | error error =>
      simp only [processCreateMessage.settle, Option.isNone_iff_eq_none, ExceptT.stM_eq,
        Except.bind_error, reduceCtorEq] at hsettle
  | ok inner =>
      unfold processCreateMessage.settle at hsettle
      simp only [bind, Except.bind] at hsettle
      by_cases hinnerNone : inner.error.isNone = true
      · rw [ite_eq_left hinnerNone] at hsettle
        cases hcharge :
          processCreateMessage.chargeCodeGas
            msg.benv.stat.rules inner with
        | error error =>
            rw [hcharge] at hsettle
            rcases error with ⟨error, charged⟩
            cases error with
            | halt reason =>
                have heq := Except.ok.inj hsettle
                split at heq
                · calc
                    post.state =
                        (processCreateMessage.exceptionalHalt charged reason
                          msg.benv.state msg.tenv.transientStorage).state :=
                      by rw [heq]; rfl
                    _ = msg.benv.state := rfl
                · calc
                    post.state =
                        (processCreateMessage.exceptionalHaltAmsterdam charged
                          reason msg.benv.state
                          msg.tenv.transientStorage).state :=
                      by rw [heq]; rfl
                    _ = msg.benv.state := rfl
            | revert => cases hsettle
            | crypto reason => cases hsettle
            | internal reason => cases hsettle
        | ok charged =>
            rw [hcharge] at hsettle
            simp only [Except.ok.injEq] at hsettle
            have hchargedError :=
              processCreateMessage.chargeCodeGas_error_eq hcharge
            cases hinner : inner.error <;>
              simp only [hinner, Option.isNone_none, Option.isNone_some, Bool.false_eq_true] at hinnerNone hchargedError
            rw [hsettle] at herror
            change charged.error.isSome = true at herror
            simp only [hchargedError, Option.isSome_none, Bool.false_eq_true] at herror
      · rw [ite_eq_right hinnerNone] at hsettle
        have heq := Except.ok.inj hsettle
        calc
          post.state =
              (inner.rollback msg.benv.state
                msg.tenv.transientStorage).state :=
            by rw [heq]; rfl
          _ = msg.benv.state := rfl

/-- Writer leaf: create preparation (nonce bump, created-account marking, empty
storage) preserves code. -/
lemma processCreateMessage.msg_getCode (msg : Msg) (a : Adr) :
    (processCreateMessage.msg msg).benv.state.getCode a = msg.benv.state.getCode a := by
  dsimp only [processCreateMessage.msg, Msg.withBenv]
  rw [Benv.incrNonce_getCode, addCreatedAccount_getCode, Benv.setStor_getCode]

lemma processCreateMessage.msg_benvStat (msg : Msg) :
    (processCreateMessage.msg msg).benv.stat = msg.benv.stat := by
  rfl

/-- Master: `executeCode` preserves the code of every nonempty-code address.
The suspended child's oracle invariant (`inv`) supplies the interpreted-code
case; `handleError_getCode` covers precompile and error selection. -/
lemma ExecuteCode.accountPreserve {track : Bool}
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : (Blanc.Xlot.InvAccountPreserve track xl))
    (run : ExecuteCode msg xl exn) :
    MsgResult.AccountPreserve track msg.benv exn := by
  intro a ha
  unfold ExecuteCode at run
  rcases henter : executeCode.enter msg with evm | raw <;> rw [henter] at run
  · rcases run with ⟨raw, h_xl, h_err⟩
    subst h_err
    rw [(executeCode.handleErrorWith_code_created _ _ a).1,
      (executeCode.handleErrorWith_code_created _ _ a).2]
    rw [h_xl] at inv
    dsimp only [ExceptT.stM_eq, Xlot.InvAccountPreserve, ne_eq] at inv
    rw [executeCode.enter_inl henter] at inv
    exact inv a ha
  · rcases run with ⟨h_xl, h_err⟩
    subst h_err
    rw [(executeCode.handleErrorWith_code_created _ _ a).1,
      (executeCode.handleErrorWith_code_created _ _ a).2]
    obtain ⟨adr, hraw⟩ := executeCode.enter_inr henter
    rw [hraw]
    refine ⟨executePrecomp_preserves_getCode (initEvm msg) adr _ rfl a, ?_⟩
    intro _ notCreated
    rw [(applyPrecompResult_code_created (initEvm msg)
      (precompileRun (initEvm msg) adr) (executePrecomp (initEvm msg) adr) rfl a).2]
    exact notCreated

lemma ExecuteCode.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : (Blanc.Xlot.InvGetCode xl))
    (run : ExecuteCode msg xl exn) :
    MsgResult.CodePreserve msg.benv.state exn := by
  intro a code
  exact (ExecuteCode.accountPreserve (Xlot.invAccountPreserve_false inv) run a code).1

lemma benvAfterTransfer_ok_createdAccounts {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) :
    benv.createdAccounts = msg.benv.createdAccounts := by
  by_cases zero : msg.value = 0
  · rw [Msg.benvAfterTransfer_of_value_zero zero] at h
    cases h
    rfl
  by_cases transfer : msg.shouldTransferValue = true
  · obtain ⟨st, subtract, rfl⟩ := of_benvAfterTransfer transfer zero h
    rfl
  · rw [of_benvAfterTransfer_no transfer h]

lemma ProcessMessage.accountPreserve {track : Bool}
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : (Blanc.Xlot.InvAccountPreserve track xl))
    (run : ProcessMessage msg xl exn) :
    MsgResult.AccountPreserve track msg.benv exn := by
  intro a ha
  obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp run
  unfold FrameBody at hbody
  rcases h_benv : msg.benvAfterTransfer with e | benv <;> rw [h_benv] at hbody
  · rw [hbody.2]
    dsimp only [processMessage.settle, Except.bind_error, MsgResult.getCode, MsgResult.createdAccounts]
    dsimp only [Msg.benvAfterTransfer] at h_benv
    split at h_benv
    · cases h_sub : msg.benv.subBal msg.caller msg.value
      · simp only [bind, Except.bind, Option.toExcept, h_sub, Except.error.injEq] at h_benv
        subst h_benv
        exact ⟨rfl, fun _ notCreated => notCreated⟩
      · simp only [bind, Except.bind, Option.toExcept, h_sub, reduceCtorEq] at h_benv
    · contradiction
  · have h_benv_created := benvAfterTransfer_ok_createdAccounts h_benv
    have h_benv_code := benvAfterTransfer_ok_getCode h_benv a
    have ha' : ( (msg.withBenv benv).benv.state.getCode a ).toList ≠ [] := by
      dsimp only [Msg.withBenv, ne_eq]
      rw [h_benv_code]
      exact ha
    have h_exec_cond := ExecuteCode.accountPreserve inv hbody a ha'
    dsimp only [Msg.withBenv] at h_exec_cond
    rw [h_benv_code, h_benv_created] at h_exec_cond
    unfold processMessage.settle
    rcases r0 with e' | evm
    · exact h_exec_cond
    · dsimp only [bind, Except.bind]
      split
      · exact ⟨Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a,
          h_exec_cond.2⟩
      · exact h_exec_cond

lemma ProcessMessage.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : (Blanc.Xlot.InvGetCode xl))
    (run : ProcessMessage msg xl exn) :
    MsgResult.CodePreserve msg.benv.state exn := by
  intro a code
  exact (ProcessMessage.accountPreserve (Xlot.invAccountPreserve_false inv) run a code).1

lemma ProcessMessage.preserves_getCode_gen
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : (Blanc.Xlot.InvGetCode xl))
    (run : ProcessMessage msg xl exn) :
    ∀ a : Adr,
      (msg.benv.state.getCode a).toList ≠ [] →
      MsgResult.getCode exn a = msg.benv.state.getCode a :=
  ProcessMessage.codePreserve inv run


/-- Master: `processCreateMessage` preserves the code of every nonempty-code
address *other than* the create target.  Create preparation
(`processCreateMessage.msg_getCode`) and the interpreted body
(`ProcessMessage.codePreserve`) preserve code; code-gas charging preserves it
(`chargeCodeGas_getCode_gen`); create completion writes only `msg.currentTarget`
through `setCode` (`setCode_getCode`, excluded by `a ≠ msg.currentTarget`); the
halt/error paths select states via rollback (`Devm.rollback_getCode`). -/

lemma processCreateMessage.chargeCodeGas_createdAccounts {rules : ForkRules}
    {pre : Devm} {out : Execution} (h : processCreateMessage.chargeCodeGas rules pre = out) :
    Execution.createdAccounts out = pre.createdAccounts := by
  have frame := processCreateMessage.chargeCodeGas_instructionFrame rules pre
  rw [h] at frame
  cases out <;> exact frame.createdAccounts.symm

lemma ProcessCreateMessage.accountPreserveExcept {track : Bool}
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : Xlot.InvAccountPreserve track xl)
    (run : ProcessCreateMessage msg xl exn) :
    MsgResult.AccountPreserveExcept track msg.benv msg.currentTarget exn := by
  intro a h_a ha
  have h_benv_code := processCreateMessage.msg_getCode msg a
  have ha' : ((processCreateMessage.msg msg).benv.state.getCode a).toList ≠ [] := by
    rw [h_benv_code]; exact ha
  obtain ⟨ex', h_exec, rfl⟩ := ProcessCreateMessage.iff_processMessage.mp run
  have h_exec_cond := ProcessMessage.accountPreserve inv h_exec a ha'
  have h_created : track = true → a ∉ msg.benv.createdAccounts →
      a ∉ MsgResult.createdAccounts ex' := by
    intro enabled fresh
    exact h_exec_cond.2 enabled (AdrSet.not_mem_insert h_a fresh)
  have h_code := h_exec_cond.1
  rw [h_benv_code] at h_code
  unfold processCreateMessage.settle
  rcases ex' with x | evm
  · exact ⟨h_code, h_created⟩
  · dsimp only [bind, Except.bind]
    split
    · rename_i h_none
      cases h_charge : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
      | error err =>
        rcases err with ⟨err_msg, err_evm⟩
        have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
        have h_ca := processCreateMessage.chargeCodeGas_createdAccounts h_charge
        change err_evm.state.getCode a = evm.state.getCode a at h_getCode
        change err_evm.createdAccounts = evm.createdAccounts at h_ca
        have h_created_err : track = true → a ∉ msg.benv.createdAccounts →
            a ∉ err_evm.createdAccounts := by
          rw [h_ca]; exact h_created
        cases err_msg with
        | halt reason =>
            simp only [MsgResult.getCode, processCreateMessage.exceptionalHalt]
            split
            · exact ⟨rfl, h_created_err⟩
            · exact ⟨rfl, h_created_err⟩
        | _ =>
            simp only [MsgResult.getCode]
            refine ⟨?_, ?_⟩
            · rw [h_getCode]; exact h_code
            · exact h_created_err
      | ok devm_charge =>
        refine ⟨?_, ?_⟩
        · dsimp only [MsgResult.getCode]
          have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
          dsimp only [Execution.getCode] at h_getCode
          rw [setCode_getCode h_a.symm]
          rw [h_getCode]
          exact h_code
        · have h_ca := processCreateMessage.chargeCodeGas_createdAccounts h_charge
          change devm_charge.createdAccounts = evm.createdAccounts at h_ca
          change track = true → a ∉ msg.benv.createdAccounts → a ∉ devm_charge.createdAccounts
          rw [h_ca]; exact h_created
    · rename_i h_some
      exact ⟨Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a, h_created⟩

lemma ProcessCreateMessage.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : (Blanc.Xlot.InvGetCode xl))
    (run : ProcessCreateMessage msg xl exn) :
    MsgResult.CodePreserveExcept msg.benv.state msg.currentTarget exn := by
  intro a different code
  exact (ProcessCreateMessage.accountPreserveExcept
    (Xlot.invAccountPreserve_false inv) run a different code).1

lemma createMsg_benv_state_getCode
    {sevm : Sevm} {devm : Devm} {createGas : Nat} {endowment : B256}
    {newAddress : Adr} {calldata : Bytes} (a : Adr) :
    (createMsg sevm devm createGas endowment newAddress calldata).benv.state.getCode a
      = devm.getCode a := rfl

lemma createMsgAmsterdam_benv_state_getCode
    {sevm : Sevm} {devm : Devm} {createGas : Nat} {endowment : B256}
    {newAddress : Adr} {calldata : Bytes} {reservoir : Nat} (a : Adr) :
    ( { createMsg sevm devm createGas endowment newAddress calldata
        with stateGasGrant := reservoir } ).benv.state.getCode a
      = devm.getCode a := rfl

/-- The CREATE-family return path preserves code at every address other than
the freshly created one, given the child frame preserved it. -/
lemma Resume.create_accountPreserve {track : Bool} {parent : Devm} {newAddress a : Adr}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a)
    (hca : track = true → a ∉ parent.createdAccounts → a ∉ MsgResult.createdAccounts r) :
    Execution.getCode ((Resume.create parent newAddress).run r) a =
      parent.getCode a ∧
      (track = true → a ∉ parent.createdAccounts →
        a ∉ Execution.createdAccounts ((Resume.create parent newAddress).run r)) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind]
  · dsimp only [MsgResult.getCode] at h
    dsimp only [Execution.getCode]
    exact ⟨h, hca⟩
  · dsimp only [MsgResult.getCode] at h
    split
    · rw [Devm.push_createdAccounts_eq rfl, Devm.push_getCode_gen rfl a]
      dsimp only [incorporateChildOnError]
      exact ⟨h, hca⟩
    · rw [Devm.push_createdAccounts_eq rfl, Devm.push_getCode_gen rfl a]
      dsimp only [incorporateChildOnSuccess]
      exact ⟨h, hca⟩

lemma Resume.create_getCode {parent : Devm} {newAddress a : Adr}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a) :
    Execution.getCode ((Resume.create parent newAddress).run r) a =
      parent.getCode a := by
  exact (Resume.create_accountPreserve (track := false) h
    (by intro impossible; cases impossible)).1

lemma Resume.createAmsterdam_accountPreserve {track : Bool} {state : StateGasRules} {parent : Devm}
    {newAddress a : Adr} {nac : Bool}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a)
    (hca : track = true → a ∉ parent.createdAccounts → a ∉ MsgResult.createdAccounts r) :
    Execution.getCode
      ((Resume.createAmsterdam state parent newAddress nac).run r) a =
      parent.getCode a ∧
      (track = true → a ∉ parent.createdAccounts →
        a ∉ Execution.createdAccounts ((Resume.createAmsterdam state parent newAddress nac).run r)) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind, Except.assert]
  · dsimp only [MsgResult.getCode] at h
    dsimp only [Execution.getCode]
    exact ⟨h, hca⟩
  · dsimp only [MsgResult.getCode] at h
    split
    · -- Error path: guard, optional refund credit, status push.
      by_cases hP : child.AmsterdamFailedChildSettled
      · rw [ite_eq_left hP]
        dsimp only
        split
        · rw [Devm.push_createdAccounts_eq rfl, Devm.push_getCode_gen rfl a,
            Devm.creditStateGasRefund_getCode]
          dsimp only [incorporateChildAmsterdamOnError]
          exact ⟨h, hca⟩
        · rw [Devm.push_createdAccounts_eq rfl, Devm.push_getCode_gen rfl a]
          dsimp only [incorporateChildAmsterdamOnError]
          exact ⟨h, hca⟩
      · rw [ite_eq_right hP]
        dsimp only [Execution.getCode]
        exact ⟨h, hca⟩
    · -- Success path: guard, incorporation, status push.
      by_cases hP : child.AmsterdamChildUncommitted
      · rw [ite_eq_left hP]
        dsimp only
        rw [Devm.push_createdAccounts_eq rfl, Devm.push_getCode_gen rfl a]
        dsimp only [incorporateChildAmsterdamOnSuccess]
        exact ⟨h, hca⟩
      · rw [ite_eq_right hP]
        dsimp only [Execution.getCode]
        exact ⟨h, hca⟩

lemma Resume.createAmsterdam_getCode {state : StateGasRules} {parent : Devm}
    {newAddress a : Adr} {nac : Bool}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a) :
    Execution.getCode
      ((Resume.createAmsterdam state parent newAddress nac).run r) a =
      parent.getCode a := by
  exact (Resume.createAmsterdam_accountPreserve (track := false) h
    (by intro impossible; cases impossible)).1

lemma GenericCreate.accountPreserve {track : Bool}
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {xl : Xlot} {exn : Execution} (inv : Xlot.InvAccountPreserve track xl)
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl exn) :
    Execution.AccountPreserve track devm exn := by
  intro a ha
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- init-code-size assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    exact ⟨rfl, fun _ fresh => fresh⟩
  -- static-context assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    exact ⟨rfl, fun _ fresh => fresh⟩
  -- balance / max-nonce / depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a]
    exact ⟨rfl, fun _ fresh => fresh⟩
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a]
    exact ⟨rfl, fun _ fresh => fresh⟩
  -- address-collision early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a]
    rw [addAccessedAddress_getCode]
    exact ⟨Devm.incrNonce_getCode, fun _ fresh => fresh⟩
  -- address-collision early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a]
    rw [addAccessedAddress_getCode]
    exact ⟨Devm.incrNonce_getCode, fun _ fresh => fresh⟩
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    rename_i h_collision
    have h_parent : ∀ b : Adr,
        (addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode b = devm.getCode b := by
      intro b
      rw [addAccessedAddress_getCode]
      exact Devm.incrNonce_getCode
    have h_a_ne : a ≠ newAddress := by
      intro h_eq
      push Not at h_collision
      have h_code_size : ((addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode newAddress).size = 0 :=
        h_collision.2
      have h_empty : devm.getCode newAddress = .empty := by
        rw [← h_parent newAddress]
        cases h_code' : (addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode newAddress with
        | mk data =>
          rw [h_code'] at h_code_size
          cases data with
          | mk l =>
            cases l
            · rfl
            · contradiction
      rw [h_eq, h_empty] at ha
      exact ha (by unfold ByteArray.toList ByteArray.toList.loop; rfl)
    have result := ProcessCreateMessage.accountPreserveExcept inv hframe a h_a_ne
      (by rw [createMsg_benv_state_getCode, h_parent a]; exact ha)
    rw [createMsg_benv_state_getCode] at result
    have returned := Resume.create_accountPreserve (newAddress := newAddress) result.1 result.2
    rw [h_parent a] at returned
    exact returned

lemma GenericCreate.codePreserve
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {xl : Xlot} {exn : Execution} (inv : (Blanc.Xlot.InvGetCode xl))
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl exn) :
    Execution.CodePreserve devm exn := by
  intro a code
  exact (GenericCreate.accountPreserve (Xlot.invAccountPreserve_false inv) run a code).1

lemma GenericCreateAmsterdam.accountPreserve {track : Bool}
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {memoryIndex memorySize : Nat} {xl : Xlot}
    {exn : Execution} (inv : Xlot.InvAccountPreserve track xl)
    (run : GenericCreateAmsterdam sevm state devm endowment newAddress
      memoryIndex memorySize xl exn) :
    Execution.AccountPreserve track devm exn := by
  intro a ha
  unfold GenericCreateAmsterdam genericCreateAmsterdam.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  all_goals first
    | obtain ⟨-, rfl⟩ := run
      rename_i heq
      rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a, Devm.balReadAccount_getCode,
        Devm.balReadAccount_createdAccounts]
      exact ⟨rfl, fun _ fresh => fresh⟩
    | obtain ⟨-, rfl⟩ := run
      rename_i heq
      refine ⟨?_, ?_⟩
      · dsimp only [Execution.getCode]
        rw [((chargeStateGas_worldEq_of_error heq).getCode a).symm,
          Devm.balReadAccount_getCode, addAccessedAddress_getCode,
          Devm.balReadAccount_getCode]
        rfl
      · have hc := chargeStateGas_createdAccounts_eq heq
        intro enabled fresh
        rw [hc]
        simp only [Devm.balReadAccount_createdAccounts, addAccessedAddress_createdAccounts]
        exact fresh
    | obtain ⟨-, rfl⟩ := run
      rename_i v hchg _ _ _ hpush
      rw [Devm.push_createdAccounts_eq hpush]
      refine ⟨?_, ?_⟩
      · rw [Devm.push_getCode_gen hpush a, Devm.incrNonce_getCode,
          Devm.withholdCreateGas_getCode,
          ((chargeStateGas_worldEq_of_ok hchg).getCode a).symm,
          Devm.balReadAccount_getCode, addAccessedAddress_getCode,
          Devm.balReadAccount_getCode]
        rfl
      · intro enabled fresh
        change a ∉ v.createdAccounts
        have hc := chargeStateGas_createdAccounts_eq hchg
        change v.createdAccounts = _ at hc
        rw [hc]
        simp only [Devm.balReadAccount_createdAccounts, addAccessedAddress_createdAccounts]
        exact fresh
    | obtain ⟨-, rfl⟩ := run
      rename_i hpush
      rw [Devm.push_createdAccounts_eq hpush]
      refine ⟨?_, ?_⟩
      · rw [Devm.push_getCode_gen hpush a, Devm.incrNonce_getCode,
          Devm.withholdCreateGas_getCode,
          Devm.balReadAccount_getCode, addAccessedAddress_getCode,
          Devm.balReadAccount_getCode]
        rfl
      · intro enabled fresh
        change a ∉ (Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
            sevm.currentTarget (devm.withReturnData [])) newAddress)).createdAccounts
        simp only [Devm.balReadAccount_createdAccounts, addAccessedAddress_createdAccounts]
        exact fresh
    | refine Exists.elim run (fun r hr => ?_)
      obtain ⟨hframe, rfl⟩ := hr
      rename_i v hchg hnc
      have h_parent : ∀ a : Adr,
          (v.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce
            sevm.currentTarget).getCode a = devm.getCode a := by
        intro a
        rw [Devm.incrNonce_getCode, Devm.drainStateGasReservoir_getCode,
          Devm.withholdCreateGas_getCode,
          ((chargeStateGas_worldEq_of_ok hchg).getCode a).symm,
          Devm.balReadAccount_getCode, addAccessedAddress_getCode,
          Devm.balReadAccount_getCode]
        rfl
      have h_a_ne : a ≠ newAddress := by
        intro h_eq
        push Not at hnc
        have h_code_size :
            (v.withholdCreateGas.2.getCode newAddress).size = 0 := hnc.2
        have h_empty : devm.getCode newAddress = .empty := by
          have h0 : v.withholdCreateGas.2.getCode newAddress = .empty := by
            cases h_code' : v.withholdCreateGas.2.getCode newAddress with
            | mk data =>
              rw [h_code'] at h_code_size
              cases data with
              | mk l =>
                cases l
                · rfl
                · contradiction
          rw [Devm.withholdCreateGas_getCode,
            ((chargeStateGas_worldEq_of_ok hchg).getCode newAddress).symm,
            Devm.balReadAccount_getCode, addAccessedAddress_getCode,
            Devm.balReadAccount_getCode] at h0
          exact h0
        rw [h_eq, h_empty] at ha
        exact ha (by unfold ByteArray.toList ByteArray.toList.loop; rfl)
      have result := ProcessCreateMessage.accountPreserveExcept inv hframe a h_a_ne
        (by rw [createMsgAmsterdam_benv_state_getCode, h_parent a]; exact ha)
      rw [createMsgAmsterdam_benv_state_getCode] at result
      have returned := Resume.createAmsterdam_accountPreserve
        (state := state) (newAddress := newAddress)
        (nac := decide ((Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
            sevm.currentTarget (devm.withReturnData [])) newAddress)).getAcct newAddress).Empty)
        result.1 result.2
      rw [h_parent a] at returned
      refine ⟨returned.1, ?_⟩
      intro enabled fresh
      apply returned.2 enabled
      change a ∉ v.createdAccounts
      have hc := chargeStateGas_createdAccounts_eq hchg
      change v.createdAccounts = _ at hc
      rw [hc]
      simp only [Devm.balReadAccount_createdAccounts, addAccessedAddress_createdAccounts]
      exact fresh
    | refine Exists.elim run (fun r hr => ?_)
      obtain ⟨hframe, rfl⟩ := hr
      rename_i hnc
      have h_parent : ∀ a : Adr,
          ((Devm.balReadAccount sevm.benvStat.rules newAddress
            (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
              sevm.currentTarget (devm.withReturnData []))
              newAddress)).withholdCreateGas.2.drainStateGasReservoir.2.incrNonce
            sevm.currentTarget).getCode a = devm.getCode a := by
        intro a
        rw [Devm.incrNonce_getCode, Devm.drainStateGasReservoir_getCode,
          Devm.withholdCreateGas_getCode,
          Devm.balReadAccount_getCode, addAccessedAddress_getCode,
          Devm.balReadAccount_getCode]
        rfl
      have h_a_ne : a ≠ newAddress := by
        intro h_eq
        push Not at hnc
        have h_code_size :
            ((Devm.balReadAccount sevm.benvStat.rules newAddress
              (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
                sevm.currentTarget (devm.withReturnData []))
                newAddress)).withholdCreateGas.2.getCode
              newAddress).size = 0 := hnc.2
        have h_empty : devm.getCode newAddress = .empty := by
          have h0 : (Devm.balReadAccount sevm.benvStat.rules newAddress
              (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
                sevm.currentTarget (devm.withReturnData []))
                newAddress)).withholdCreateGas.2.getCode newAddress
              = .empty := by
            cases h_code' : (Devm.balReadAccount sevm.benvStat.rules newAddress
              (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
                sevm.currentTarget (devm.withReturnData []))
                newAddress)).withholdCreateGas.2.getCode newAddress with
            | mk data =>
              rw [h_code'] at h_code_size
              cases data with
              | mk l =>
                cases l
                · rfl
                · contradiction
          rw [Devm.withholdCreateGas_getCode,
            Devm.balReadAccount_getCode, addAccessedAddress_getCode,
            Devm.balReadAccount_getCode] at h0
          exact h0
        rw [h_eq, h_empty] at ha
        exact ha (by unfold ByteArray.toList ByteArray.toList.loop; rfl)
      have result := ProcessCreateMessage.accountPreserveExcept inv hframe a h_a_ne
        (by rw [createMsgAmsterdam_benv_state_getCode, h_parent a]; exact ha)
      rw [createMsgAmsterdam_benv_state_getCode] at result
      have returned := Resume.createAmsterdam_accountPreserve
        (state := state) (newAddress := newAddress)
        (nac := decide ((Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
            sevm.currentTarget (devm.withReturnData [])) newAddress)).getAcct newAddress).Empty)
        result.1 result.2
      rw [h_parent a] at returned
      refine ⟨returned.1, ?_⟩
      intro enabled fresh
      apply returned.2 enabled
      change a ∉ (Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (devm.withReturnData [])) newAddress)).createdAccounts
      simp only [Devm.balReadAccount_createdAccounts, addAccessedAddress_createdAccounts]
      exact fresh


lemma GenericCreateAmsterdam.codePreserve
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {memoryIndex memorySize : Nat} {xl : Xlot}
    {exn : Execution} (inv : (Blanc.Xlot.InvGetCode xl))
    (run : GenericCreateAmsterdam sevm state devm endowment newAddress
      memoryIndex memorySize xl exn) :
    Execution.CodePreserve devm exn := by
  intro a code
  exact (GenericCreateAmsterdam.accountPreserve
    (Xlot.invAccountPreserve_false inv) run a code).1

lemma callMsg_benv_state_getCode
    {sevm : Sevm} {evm1 : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {calldata : Bytes} {code : ByteArray} {disablePrecompiles : Bool} (a : Adr) :
    ( callMsg sevm evm1 gas value caller target codeAddress shouldTransferValue
        isStaticcall calldata code disablePrecompiles ).benv.state.getCode a
      = evm1.getCode a := rfl

lemma callMsgAmsterdam_benv_state_getCode
    {sevm : Sevm} {evm1 : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {calldata : Bytes} {code : ByteArray} {disablePrecompiles : Bool}
    {reservoir : Nat} (a : Adr) :
    ( { callMsg sevm evm1 gas value caller target codeAddress
          shouldTransferValue isStaticcall calldata code disablePrecompiles
        with stateGasGrant := reservoir } ).benv.state.getCode a
      = evm1.getCode a := rfl

/-- The CALL-family return path preserves code at every address, given the child
frame preserved it: `memWrite` touches memory only, and `incorporateChild*`
installs the child's state, whose code map the child preserved. -/
lemma Resume.call_accountPreserve {track : Bool} {parent : Devm} {a : Adr} {outputIndex outputSize : Nat}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a)
    (hca : track = true → a ∉ parent.createdAccounts → a ∉ MsgResult.createdAccounts r) :
    Execution.getCode ((Resume.call parent outputIndex outputSize).run r) a =
      parent.getCode a ∧
      (track = true → a ∉ parent.createdAccounts →
        a ∉ Execution.createdAccounts ((Resume.call parent outputIndex outputSize).run r)) := by
  have hmw : ∀ (d : Devm) (o : Bytes),
      (d.memWrite outputIndex o).getCode a = d.getCode a := fun d o =>
    (liftMachPure_worldEq (Mach.memWrite · outputIndex o) d).getCode a |>.symm
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind]
  · dsimp only [MsgResult.getCode] at h
    dsimp only [Execution.getCode]
    exact ⟨h, hca⟩
  · dsimp only [MsgResult.getCode] at h
    split
    · rcases hpush : (incorporateChildOnError parent child child.output).push 0 with
        e | evm2 <;> have hp := Devm.push_getCode_gen hpush a
      all_goals have hpc := Devm.push_createdAccounts_eq hpush
      · exact ⟨hp.trans h, by rw [hpc]; exact hca⟩
      · refine ⟨?_, ?_⟩
        · show (evm2.memWrite outputIndex _).getCode a = parent.getCode a
          rw [hmw]
          exact hp.trans h
        · change track = true → a ∉ parent.createdAccounts → a ∉ evm2.createdAccounts
          change evm2.createdAccounts = _ at hpc
          rw [hpc]; exact hca
    · rcases hpush : (incorporateChildOnSuccess parent child child.output).push 1 with
        e | evm2 <;> have hp := Devm.push_getCode_gen hpush a
      all_goals have hpc := Devm.push_createdAccounts_eq hpush
      · exact ⟨hp.trans h, by rw [hpc]; exact hca⟩
      · refine ⟨?_, ?_⟩
        · show (evm2.memWrite outputIndex _).getCode a = parent.getCode a
          rw [hmw]
          exact hp.trans h
        · change track = true → a ∉ parent.createdAccounts → a ∉ evm2.createdAccounts
          change evm2.createdAccounts = _ at hpc
          rw [hpc]; exact hca


lemma Resume.call_getCode {parent : Devm} {a : Adr} {outputIndex outputSize : Nat}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a) :
    Execution.getCode ((Resume.call parent outputIndex outputSize).run r) a =
      parent.getCode a := by
  exact (Resume.call_accountPreserve (track := false) h
    (by intro impossible; cases impossible)).1

/-- The Amsterdam CALL-family return path preserves code at every address,
given the child frame preserved it: the guards fail with the child itself, the
refund credit touches gas only, and `incorporateChildAmsterdam*` installs the
child's state. -/
lemma Resume.callAmsterdam_accountPreserve {track : Bool} {state : StateGasRules} {parent : Devm}
    {a : Adr} {outputIndex outputSize : Nat} {nac : Bool}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a)
    (hca : track = true → a ∉ parent.createdAccounts → a ∉ MsgResult.createdAccounts r) :
    Execution.getCode
      ((Resume.callAmsterdam state parent outputIndex outputSize nac).run r) a =
      parent.getCode a ∧
      (track = true → a ∉ parent.createdAccounts →
        a ∉ Execution.createdAccounts ((Resume.callAmsterdam state parent outputIndex outputSize nac).run r)) := by
  have hmw : ∀ (d : Devm) (o : Bytes),
      (d.memWrite outputIndex o).getCode a = d.getCode a := fun d o =>
    (liftMachPure_worldEq (Mach.memWrite · outputIndex o) d).getCode a |>.symm
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind, Except.assert]
  · dsimp only [MsgResult.getCode] at h
    dsimp only [Execution.getCode]
    exact ⟨h, hca⟩
  · dsimp only [MsgResult.getCode] at h
    split
    · -- Error path: guard, optional refund credit, status push, memory write.
      by_cases hP : child.AmsterdamFailedChildSettled
      · rw [ite_eq_left hP]
        dsimp only
        by_cases hnac : nac = true
        · rw [ite_eq_left hnac]
          rcases hpush : (Devm.creditStateGasRefund state.newAccount
              (incorporateChildAmsterdamOnError parent child
                child.output)).push 0 with
            e | evm2 <;> have hp := Devm.push_getCode_gen hpush a
          all_goals have hpc := Devm.push_createdAccounts_eq hpush
          · exact ⟨hp.trans h, by rw [hpc]; exact hca⟩
          · refine ⟨?_, ?_⟩
            · show (evm2.memWrite outputIndex _).getCode a = parent.getCode a
              rw [hmw]
              exact hp.trans h
            · change track = true → a ∉ parent.createdAccounts → a ∉ evm2.createdAccounts
              change evm2.createdAccounts = _ at hpc
              rw [hpc]; exact hca
        · rw [ite_eq_right hnac]
          rcases hpush : (incorporateChildAmsterdamOnError parent child
              child.output).push 0 with
            e | evm2 <;> have hp := Devm.push_getCode_gen hpush a
          all_goals have hpc := Devm.push_createdAccounts_eq hpush
          · exact ⟨hp.trans h, by rw [hpc]; exact hca⟩
          · refine ⟨?_, ?_⟩
            · show (evm2.memWrite outputIndex _).getCode a = parent.getCode a
              rw [hmw]
              exact hp.trans h
            · change track = true → a ∉ parent.createdAccounts → a ∉ evm2.createdAccounts
              change evm2.createdAccounts = _ at hpc
              rw [hpc]; exact hca
      · rw [ite_eq_right hP]
        dsimp only [Execution.getCode]
        exact ⟨h, hca⟩
    · -- Success path: guard, incorporation, status push, memory write.
      by_cases hP : child.AmsterdamChildUncommitted
      · rw [ite_eq_left hP]
        dsimp only
        rcases hpush : (incorporateChildAmsterdamOnSuccess parent child
            child.output).push 1 with
          e | evm2 <;> have hp := Devm.push_getCode_gen hpush a
        all_goals have hpc := Devm.push_createdAccounts_eq hpush
        · exact ⟨hp.trans h, by rw [hpc]; exact hca⟩
        · refine ⟨?_, ?_⟩
          · show (evm2.memWrite outputIndex _).getCode a = parent.getCode a
            rw [hmw]
            exact hp.trans h
          · change track = true → a ∉ parent.createdAccounts → a ∉ evm2.createdAccounts
            change evm2.createdAccounts = _ at hpc
            rw [hpc]; exact hca
      · rw [ite_eq_right hP]
        dsimp only [Execution.getCode]
        exact ⟨h, hca⟩


lemma Resume.callAmsterdam_getCode {state : StateGasRules} {parent : Devm}
    {a : Adr} {outputIndex outputSize : Nat} {nac : Bool}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a) :
    Execution.getCode
      ((Resume.callAmsterdam state parent outputIndex outputSize nac).run r) a =
      parent.getCode a := by
  exact (Resume.callAmsterdam_accountPreserve (track := false) h
    (by intro impossible; cases impossible)).1



/-- On the successful path the CREATE-family return installs the child's
world; the status push leaves it alone. -/
lemma Resume.create_state {parent child : Devm} {newAddress : Adr} {sf : Devm}
    (h : (Resume.create parent newAddress).run (.ok child) = .ok sf) :
    sf.state = child.state := by
  have key : ∀ d : Devm, d.state = child.state → ∀ v : B256,
      Devm.push v d = .ok sf → sf.state = child.state := by
    intro d hd v hh
    have hframe := Devm.push_instructionFrame v d
    rw [hh] at hframe
    have hframe' : Devm.InstructionFrame d sf := hframe
    rw [← hframe'.state, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child []) rfl _ h

/-- A failed child message aborts the CALL-family return path. -/
lemma Resume.call_run_error {parent : Devm} {oi os : Nat}
    {e : EvmError × Jaune.State × AdrSet × Tra} {sf : Devm}
    (h : (Resume.call parent oi os).run (.error e) = .ok sf) : False := by
  rcases e with ⟨err, st, ac, tra⟩
  unfold Resume.run liftToExecution at h
  cases h

/-- On the successful path the CALL-family return installs the child's world;
the status push and the memory write leave it alone. -/
lemma Resume.call_state {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    sf.state = child.state := by
  have key : ∀ d : Devm, d.state = child.state → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      sf.state = child.state := by
    intro d hd v hh
    have hframe := Devm.push_instructionFrame v d
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh hframe
    · cases hh
    · injection hh with hh
      subst hh
      have hframe' : Devm.InstructionFrame d evm2 := hframe
      rw [← (Devm.memWrite_instructionFrame evm2 oi (child.output.take os)).state,
        ← hframe'.state, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

lemma GenericCall.accountPreserve {track : Bool}
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvAccountPreserve track xl)
    (run : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue isStaticcall input_index input_size output_index output_size code disablePrecompiles xl exn) :
    Execution.AccountPreserve track devm exn := by
  intro a ha
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a]
    exact ⟨rfl, fun _ fresh => fresh⟩
  -- depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a]
    exact ⟨rfl, fun _ fresh => fresh⟩
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    have result := ProcessMessage.accountPreserve inv hframe a
      (by rw [callMsg_benv_state_getCode]; exact ha)
    rw [callMsg_benv_state_getCode] at result
    exact Resume.call_accountPreserve result.1 result.2

lemma GenericCall.codePreserve
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {exn : Execution}
    (inv : (Blanc.Xlot.InvGetCode xl))
    (run : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue isStaticcall input_index input_size output_index output_size code disablePrecompiles xl exn) :
    Execution.CodePreserve devm exn := by
  intro a code
  exact (GenericCall.accountPreserve (Xlot.invAccountPreserve_false inv) run a code).1

lemma GenericCallAmsterdam.accountPreserve {track : Bool}
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {gas reservoir : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvAccountPreserve track xl)
    (run : GenericCallAmsterdam sevm state devm gas reservoir value caller
      target codeAddress shouldTransferValue isStaticcall input_index
      input_size output_index output_size code disablePrecompiles
      newAccountCharged insufficientBalance xl exn) :
    Execution.AccountPreserve track devm exn := by
  intro a ha
  unfold GenericCallAmsterdam genericCallAmsterdam.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    by_cases hnac : newAccountCharged = true
    · rw [ite_eq_left hnac] at heq
      rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a, Devm.creditStateGasRefund_getCode,
        Devm.restoreChildGas_getCode]
      exact ⟨rfl, fun _ fresh => fresh⟩
    · rw [ite_eq_right hnac] at heq
      rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a, Devm.restoreChildGas_getCode]
      exact ⟨rfl, fun _ fresh => fresh⟩
  -- early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    by_cases hnac : newAccountCharged = true
    · rw [ite_eq_left hnac] at heq
      rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a, Devm.creditStateGasRefund_getCode,
        Devm.restoreChildGas_getCode]
      exact ⟨rfl, fun _ fresh => fresh⟩
    · rw [ite_eq_right hnac] at heq
      rw [Devm.push_createdAccounts_eq heq, Devm.push_getCode_gen heq a, Devm.restoreChildGas_getCode]
      exact ⟨rfl, fun _ fresh => fresh⟩
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    have result := ProcessMessage.accountPreserve inv hframe a
      (by rw [callMsgAmsterdam_benv_state_getCode]; exact ha)
    rw [callMsgAmsterdam_benv_state_getCode] at result
    exact Resume.callAmsterdam_accountPreserve result.1 result.2

lemma GenericCallAmsterdam.codePreserve
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {gas reservoir : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {xl : Xlot} {exn : Execution}
    (inv : (Blanc.Xlot.InvGetCode xl))
    (run : GenericCallAmsterdam sevm state devm gas reservoir value caller
      target codeAddress shouldTransferValue isStaticcall input_index
      input_size output_index output_size code disablePrecompiles
      newAccountCharged insufficientBalance xl exn) :
    Execution.CodePreserve devm exn := by
  intro a code
  exact (GenericCallAmsterdam.accountPreserve (Xlot.invAccountPreserve_false inv) run a code).1

/-- A call-type step whose `Except` prefix failed carries that failure. -/
lemma XStep.run_ofExcept_error {e : EvmError × Devm} {xl : Xlot} {ex : Execution}
    (h : XStep.Run (XStep.ofExcept (.error e)) xl ex) : ex = .error e := h.2

/-- The call-family error arms route through a `stateGas` match whose two arms
are the same `ofExcept`, so the error equation holds in both lanes. -/
lemma XStep.run_ofExcept_error_stateGas {sg : Option StateGasRules}
    {e : EvmError × Devm} {xl : Xlot} {ex : Execution}
    (h : XStep.Run (match sg with
      | none => XStep.ofExcept (.error e)
      | some _ => XStep.ofExcept (.error e)) xl ex) :
    ex = .error e := by
  cases hsg : sg <;> simp only [hsg] at h
  · exact XStep.run_ofExcept_error h
  · exact XStep.run_ofExcept_error h

/-! ### The dispatch shape of a call-type instruction

Everything `Xinst.step` does before dispatching — popping operands, charging
gas, extending memory, recording accesses, resolving delegations — stays inside
the instruction frame.  Recording that once, together with the two dispatch
targets and the provenance of the child's code, is what replaces the six
per-constructor bind walks the old mirrors forced: every `Xinst`-level master
below is a three-case argument over `Shape`. -/

def Xinst.Shape (sevm : Sevm) (devm : Devm) (s : XStep) : Prop :=
  (∃ ex, s = .done ex ∧ Execution.Rel Devm.InstructionFrame devm ex) ∨
  (∃ d endowment newAddress mi ms,
      Devm.InstructionFrame devm d ∧
      s = genericCreate.step sevm d endowment newAddress mi ms) ∨
  (∃ d d₀ gas value caller target codeAddress stv isSt ii isz oi osz code dp,
      Devm.InstructionFrame devm d ∧
      Devm.InstructionFrame devm d₀ ∧
      ( (stv = true ∧ caller = sevm.currentTarget) ∨
        (stv = false ∧ target = sevm.currentTarget) ) ∧
      ( target = sevm.currentTarget ∨
        ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target ) ) ∧
      s = genericCall.step sevm d gas value caller target codeAddress stv isSt
            ii isz oi osz code dp) ∨
  (∃ d state endowment newAddress mi ms,
      Devm.InstructionFrame devm d ∧
      s = genericCreateAmsterdam.step sevm state d endowment newAddress
            mi ms) ∨
  (∃ d d₀ state gas reservoir value caller target codeAddress stv isSt ii isz
      oi osz code dp nac ib,
      Devm.InstructionFrame devm d ∧
      Devm.InstructionFrame devm d₀ ∧
      ( (stv = true ∧ caller = sevm.currentTarget) ∨
        (stv = false ∧ target = sevm.currentTarget) ) ∧
      ( target = sevm.currentTarget ∨
        ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target ) ) ∧
      s = genericCallAmsterdam.step sevm state d gas reservoir value caller
            target codeAddress stv isSt ii isz oi osz code dp nac ib)

/-- The ordinary-lane restriction of `Xinst.Shape`: only done/create/call arms.
These are the shapes selected by `rules.stateGas = none`; the established
`ShapeCovered` name is retained for existing consumers. -/
def Xinst.ShapeCovered (sevm : Sevm) (devm : Devm) (s : XStep) : Prop :=
  (∃ ex, s = .done ex ∧ Execution.Rel Devm.InstructionFrame devm ex) ∨
  (∃ d endowment newAddress mi ms,
      Devm.InstructionFrame devm d ∧
      s = genericCreate.step sevm d endowment newAddress mi ms) ∨
  (∃ d d₀ gas value caller target codeAddress stv isSt ii isz oi osz code dp,
      Devm.InstructionFrame devm d ∧
      Devm.InstructionFrame devm d₀ ∧
      ( (stv = true ∧ caller = sevm.currentTarget) ∨
        (stv = false ∧ target = sevm.currentTarget) ) ∧
      ( target = sevm.currentTarget ∨
        ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target ) ) ∧
      s = genericCall.step sevm d gas value caller target codeAddress stv isSt
            ii isz oi osz code dp)

lemma Xinst.shape_done {sevm : Sevm} {devm : Devm} {ex : Execution}
    (h : Execution.Rel Devm.InstructionFrame devm ex) :
    Xinst.Shape sevm devm (.done ex) := Or.inl ⟨ex, rfl, h⟩

lemma Xinst.shape_error {sevm : Sevm} {devm : Devm} {err : EvmError × Devm}
    (h : Devm.InstructionFrame devm err.2) :
    Xinst.Shape sevm devm (XStep.ofExcept (.error err)) := Xinst.shape_done h

lemma Xinst.shape_create {sevm : Sevm} {devm d : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (genericCreate.step sevm d endowment newAddress mi ms) :=
  Or.inr (Or.inl ⟨d, endowment, newAddress, mi, ms, hf, rfl⟩)

lemma Xinst.shape_call {sevm : Sevm} {devm d d₀ : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp : Bool}
    (hf : Devm.InstructionFrame devm d) (hf₀ : Devm.InstructionFrame devm d₀)
    (hcal : (stv = true ∧ caller = sevm.currentTarget) ∨
      (stv = false ∧ target = sevm.currentTarget))
    (hsrc : target = sevm.currentTarget ∨
      ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target )) :
    Xinst.Shape sevm devm
      (genericCall.step sevm d gas value caller target codeAddress stv isSt
        ii isz oi osz code dp) :=
  Or.inr (Or.inr (Or.inl ⟨d, d₀, gas, value, caller, target, codeAddress, stv,
    isSt, ii, isz, oi, osz, code, dp, hf, hf₀, hcal, hsrc, rfl⟩))

lemma Xinst.shape_createAmsterdam {sevm : Sevm} {devm d : Devm}
    {state : StateGasRules} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (genericCreateAmsterdam.step sevm state d endowment newAddress mi ms) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨d, state, endowment, newAddress, mi, ms, hf,
    rfl⟩)))

lemma Xinst.shape_callAmsterdam {sevm : Sevm} {devm d d₀ : Devm}
    {state : StateGasRules} {gas reservoir : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp nac ib : Bool}
    (hf : Devm.InstructionFrame devm d) (hf₀ : Devm.InstructionFrame devm d₀)
    (hcal : (stv = true ∧ caller = sevm.currentTarget) ∨
      (stv = false ∧ target = sevm.currentTarget))
    (hsrc : target = sevm.currentTarget ∨
      ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target )) :
    Xinst.Shape sevm devm
      (genericCallAmsterdam.step sevm state d gas reservoir value caller target
        codeAddress stv isSt ii isz oi osz code dp nac ib) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨d, d₀, state, gas, reservoir, value, caller,
    target, codeAddress, stv, isSt, ii, isz, oi, osz, code, dp, nac, ib,
    hf, hf₀, hcal, hsrc, rfl⟩)))

lemma Xinst.shape_bind {sevm : Sevm} {devm d : Devm} {α : Type}
    {x : Except (EvmError × Devm) (α × Devm)}
    {f : α × Devm → Except (EvmError × Devm) XStep}
    (hd : Devm.InstructionFrame devm d)
    (hx : Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d x)
    (hf : ∀ (v : α) (d' : Devm), Devm.InstructionFrame devm d' →
      Xinst.Shape sevm devm (XStep.ofExcept (f ⟨v, d'⟩))) :
    Xinst.Shape sevm devm (XStep.ofExcept (x >>= f)) := by
  rcases x with e | ⟨v, d'⟩
  · exact Xinst.shape_error (Devm.instructionFrame_trans hd hx)
  · exact hf v d' (Devm.instructionFrame_trans hd hx)

lemma Xinst.shape_bindE {sevm : Sevm} {devm d : Devm} {x : Execution}
    {f : Devm → Except (EvmError × Devm) XStep}
    (hd : Devm.InstructionFrame devm d)
    (hx : Execution.Rel Devm.InstructionFrame d x)
    (hf : ∀ d' : Devm, Devm.InstructionFrame devm d' →
      Xinst.Shape sevm devm (XStep.ofExcept (f d'))) :
    Xinst.Shape sevm devm (XStep.ofExcept (x >>= f)) := by
  rcases x with e | d'
  · exact Xinst.shape_error (Devm.instructionFrame_trans hd hx)
  · exact hf d' (Devm.instructionFrame_trans hd hx)

lemma Xinst.shape_assert {sevm : Sevm} {devm : Devm} {p : Prop} [Decidable p]
    {err : EvmError × Devm} {f : Unit → Except (EvmError × Devm) XStep}
    (herr : Devm.InstructionFrame devm err.2)
    (hf : Xinst.Shape sevm devm (XStep.ofExcept (f ()))) :
    Xinst.Shape sevm devm (XStep.ofExcept (Except.assert p err >>= f)) := by
  unfold Except.assert
  split
  · exact hf
  · exact Xinst.shape_error herr

lemma Xinst.shape_assertDynamic {sevm : Sevm} {devm : Devm}
    {f : Unit → Except (EvmError × Devm) XStep}
    (hf : Xinst.Shape sevm devm (XStep.ofExcept (f ()))) :
    Xinst.Shape sevm devm
      (XStep.ofExcept (assertDynamic sevm devm >>= f)) := by
  simp only [assertDynamic]
  exact Xinst.shape_assert (Devm.instructionFrame_refl devm) hf

/-- The early exit taken when the caller cannot cover the transferred value:
a push onto a machine whose world is untouched. -/
lemma Xinst.shape_shortfall {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withReturnData []).withGasLeft
            (d'.gasLeft + stipend)))))) := by
  refine Xinst.shape_bindE hf (Devm.push_instructionFrame 0 d) fun d' hf' => ?_
  exact Xinst.shape_done
    (Devm.instructionFrame_trans hf'
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl))

lemma Xinst.shape_shortfall' {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withGasLeft
            (d'.gasLeft + stipend)).withReturnData []))))) := by
  refine Xinst.shape_bindE hf (Devm.push_instructionFrame 0 d) fun d' hf' => ?_
  exact Xinst.shape_done
    (Devm.instructionFrame_trans hf'
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl))

lemma Xinst.shapeCovered_done {sevm : Sevm} {devm : Devm} {ex : Execution}
    (h : Execution.Rel Devm.InstructionFrame devm ex) :
    Xinst.ShapeCovered sevm devm (.done ex) := Or.inl ⟨ex, rfl, h⟩

lemma Xinst.shapeCovered_error {sevm : Sevm} {devm : Devm} {err : EvmError × Devm}
    (h : Devm.InstructionFrame devm err.2) :
    Xinst.ShapeCovered sevm devm (XStep.ofExcept (.error err)) :=
  Xinst.shapeCovered_done h

lemma Xinst.shapeCovered_create {sevm : Sevm} {devm d : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} (hf : Devm.InstructionFrame devm d) :
    Xinst.ShapeCovered sevm devm
      (genericCreate.step sevm d endowment newAddress mi ms) :=
  Or.inr (Or.inl ⟨d, endowment, newAddress, mi, ms, hf, rfl⟩)

lemma Xinst.shapeCovered_call {sevm : Sevm} {devm d d₀ : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp : Bool}
    (hf : Devm.InstructionFrame devm d) (hf₀ : Devm.InstructionFrame devm d₀)
    (hcal : (stv = true ∧ caller = sevm.currentTarget) ∨
      (stv = false ∧ target = sevm.currentTarget))
    (hsrc : target = sevm.currentTarget ∨
      ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target )) :
    Xinst.ShapeCovered sevm devm
      (genericCall.step sevm d gas value caller target codeAddress stv isSt
        ii isz oi osz code dp) :=
  Or.inr (Or.inr ⟨d, d₀, gas, value, caller, target, codeAddress, stv,
    isSt, ii, isz, oi, osz, code, dp, hf, hf₀, hcal, hsrc, rfl⟩)

lemma Xinst.shapeCovered_bind {sevm : Sevm} {devm d : Devm} {α : Type}
    {x : Except (EvmError × Devm) (α × Devm)}
    {f : α × Devm → Except (EvmError × Devm) XStep}
    (hd : Devm.InstructionFrame devm d)
    (hx : Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d x)
    (hf : ∀ (v : α) (d' : Devm), Devm.InstructionFrame devm d' →
      Xinst.ShapeCovered sevm devm (XStep.ofExcept (f ⟨v, d'⟩))) :
    Xinst.ShapeCovered sevm devm (XStep.ofExcept (x >>= f)) := by
  rcases x with e | ⟨v, d'⟩
  · exact Xinst.shapeCovered_error (Devm.instructionFrame_trans hd hx)
  · exact hf v d' (Devm.instructionFrame_trans hd hx)

lemma Xinst.shapeCovered_bindE {sevm : Sevm} {devm d : Devm} {x : Execution}
    {f : Devm → Except (EvmError × Devm) XStep}
    (hd : Devm.InstructionFrame devm d)
    (hx : Execution.Rel Devm.InstructionFrame d x)
    (hf : ∀ d' : Devm, Devm.InstructionFrame devm d' →
      Xinst.ShapeCovered sevm devm (XStep.ofExcept (f d'))) :
    Xinst.ShapeCovered sevm devm (XStep.ofExcept (x >>= f)) := by
  rcases x with e | d'
  · exact Xinst.shapeCovered_error (Devm.instructionFrame_trans hd hx)
  · exact hf d' (Devm.instructionFrame_trans hd hx)

lemma Xinst.shapeCovered_assert {sevm : Sevm} {devm : Devm} {p : Prop} [Decidable p]
    {err : EvmError × Devm} {f : Unit → Except (EvmError × Devm) XStep}
    (herr : Devm.InstructionFrame devm err.2)
    (hf : Xinst.ShapeCovered sevm devm (XStep.ofExcept (f ()))) :
    Xinst.ShapeCovered sevm devm (XStep.ofExcept (Except.assert p err >>= f)) := by
  unfold Except.assert
  split
  · exact hf
  · exact Xinst.shapeCovered_error herr

lemma Xinst.shapeCovered_shortfall {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : Devm.InstructionFrame devm d) :
    Xinst.ShapeCovered sevm devm
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withReturnData []).withGasLeft
            (d'.gasLeft + stipend)))))) := by
  refine Xinst.shapeCovered_bindE hf (Devm.push_instructionFrame 0 d) fun d' hf' => ?_
  exact Xinst.shapeCovered_done
    (Devm.instructionFrame_trans hf'
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl))

lemma Xinst.shapeCovered_shortfall' {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : Devm.InstructionFrame devm d) :
    Xinst.ShapeCovered sevm devm
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withGasLeft
            (d'.gasLeft + stipend)).withReturnData []))))) := by
  refine Xinst.shapeCovered_bindE hf (Devm.push_instructionFrame 0 d) fun d' hf' => ?_
  exact Xinst.shapeCovered_done
    (Devm.instructionFrame_trans hf'
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl))

/-- Delegation resolution is the identity when the callee is not a delegating
EOA, so the child's code is exactly the callee's own code. -/
lemma accessDelegation_of_not_delegation {d : Devm} {adr : Adr}
    (h : ¬ isValidDelegation (d.getCode adr)) :
    accessDelegation d adr = ⟨false, adr, d.getCode adr, 0, d⟩ := by
  have hnone : getDelegatedCodeAddress (d.state.getCode adr) = none := by
    dsimp only [getDelegatedCodeAddress]
    rw [ite_eq_right (show ¬ isValidDelegation (d.state.getCode adr) from h)]
  dsimp only [accessDelegation]
  rw [hnone]
  rfl

/-- Delegation resolution is the identity when the callee is not a delegating
EOA, so the child's code is exactly the callee's own code (schedule version). -/
lemma GasSchedule.accessDelegation_of_not_delegation {gas : GasSchedule}
    {d : Devm} {adr : Adr} (h : ¬ isValidDelegation (d.getCode adr)) :
    gas.accessDelegation d adr = ⟨false, adr, d.getCode adr, 0, d⟩ := by
  have hnone : getDelegatedCodeAddress (d.state.getCode adr) = none := by
    dsimp only [getDelegatedCodeAddress]
    rw [ite_eq_right (show ¬ isValidDelegation (d.state.getCode adr) from h)]
  dsimp only [GasSchedule.accessDelegation]
  rw [hnone]
  rfl

/-- Without a valid EIP-7702 designator there is no delegation to price. -/
lemma GasSchedule.delegationCost_of_not_delegation {gas : GasSchedule} {d : Devm}
    {adr : Adr} (h : ¬ isValidDelegation (d.getCode adr)) :
    gas.delegationCost d adr = (false, adr, 0) := by
  unfold GasSchedule.delegationCost
  have hnone : getDelegatedCodeAddress (d.state.getCode adr) = none := by
    dsimp only [getDelegatedCodeAddress]
    rw [ite_eq_right (show ¬ isValidDelegation (d.state.getCode adr) from h)]
  simp only [hnone]

/-- A fork-gated lookup is the identity without a delegation designator. -/
lemma ForkRules.accessDelegation_of_not_delegation {rules : ForkRules}
    {d : Devm} {adr : Adr} (h : ¬ isValidDelegation (d.getCode adr)) :
    rules.accessDelegation d adr = ⟨false, adr, d.getCode adr, 0, d⟩ := by
  unfold ForkRules.accessDelegation
  split
  · exact GasSchedule.accessDelegation_of_not_delegation h
  · rfl

/-- Without a designator, fork-gated price discovery selects the original address. -/
lemma ForkRules.delegationCost_of_not_delegation {rules : ForkRules}
    {d : Devm} {adr : Adr} (h : ¬ isValidDelegation (d.getCode adr)) :
    rules.delegationCost d adr = (false, adr, 0) := by
  unfold ForkRules.delegationCost
  split
  · exact GasSchedule.delegationCost_of_not_delegation h
  · rfl

/-- Undelegated Amsterdam completion reads the target's own code. -/
lemma completeDelegationAccess_code_of_not_delegated {d : Devm} {adr : Adr} :
    (completeDelegationAccess d false adr).1 = d.state.getCode adr := by
  simp only [completeDelegationAccess, Bool.false_eq_true, ↓reduceIte]

/-- Amsterdam call code resolution under no delegation: the completed code is
    the target's own code. -/
lemma amsterdamCallCode_of_not_delegation {rules : ForkRules} {d₀ : Devm}
    {tgt : Adr} (hnd : ¬ isValidDelegation (d₀.getCode tgt)) :
    (completeDelegationAccess
      (Devm.balReadAccount rules
        (rules.delegationCost d₀ tgt).2.1
        (Devm.balReadAccount rules tgt d₀))
      (rules.delegationCost d₀ tgt).1
      (rules.delegationCost d₀ tgt).2.1).1
      = d₀.getCode tgt := by
  have hdc := ForkRules.delegationCost_of_not_delegation
    (rules := rules) (d := d₀) (adr := tgt) hnd
  have hdp : (rules.delegationCost d₀ tgt).1 = false := by
    rw [hdc]
  have hnac : (rules.delegationCost d₀ tgt).2.1 = tgt := by
    rw [hdc]
  rw [hdp, hnac, completeDelegationAccess_code_of_not_delegated]
  have hB : (Devm.balReadAccount rules tgt
      (Devm.balReadAccount rules tgt d₀)).getCode tgt = d₀.getCode tgt := by
    rw [Devm.balReadAccount_getCode, Devm.balReadAccount_getCode]
  exact hB

lemma Xinst.step_shape (sevm : Sevm) (devm : Devm) (x : Xinst) :
    Xinst.Shape sevm devm (Xinst.step sevm devm x) := by
  cases x with
  | create =>
    simp only [Xinst.step]
    cases sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bindE h3 (chargeGas_instructionFrame _ d3) fun d4 h4 => ?_
      exact Xinst.shape_create
        (Devm.instructionFrame_trans h4 (Devm.memExtends_instructionFrame d4 _))
    | some state =>
      refine Xinst.shape_assertDynamic ?_
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bindE h3 (chargeGas_instructionFrame _ d3) fun d4 h4 => ?_
      refine Xinst.shape_assert h4 ?_
      exact Xinst.shape_createAmsterdam
        (Devm.instructionFrame_trans h4 (Devm.memExtends_instructionFrame d4 _))
  | create2 =>
    simp only [Xinst.step]
    split
    ·
      cases sevm.benvStat.rules.stateGas with
      | none =>
        refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
          (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
        refine Xinst.shape_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
        refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
        refine Xinst.shape_bind h3 (Devm.pop_instructionFrame d3) fun _ d4 h4 => ?_
        refine Xinst.shape_bindE h4 (chargeGas_instructionFrame _ d4) fun d5 h5 => ?_
        exact Xinst.shape_create
          (Devm.instructionFrame_trans h5 (Devm.memExtends_instructionFrame d5 _))
      | some state =>
        refine Xinst.shape_assertDynamic ?_
        refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
          (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
        refine Xinst.shape_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
        refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
        refine Xinst.shape_bind h3 (Devm.pop_instructionFrame d3) fun _ d4 h4 => ?_
        refine Xinst.shape_bindE h4 (chargeGas_instructionFrame _ d4) fun d5 h5 => ?_
        refine Xinst.shape_assert h5 ?_
        exact Xinst.shape_createAmsterdam
          (Devm.instructionFrame_trans h5 (Devm.memExtends_instructionFrame d5 _))
    · exact Xinst.shape_error (Devm.instructionFrame_refl devm)
  | call =>
    simp only [Xinst.step]
    cases sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun callee d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      refine Xinst.shape_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
      dsimp only
      let dAccess : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d7 callee
        | .flat _ => d7
      have h7' : Devm.InstructionFrame devm dAccess := by
        dsimp only [dAccess]
        split
        · exact Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 callee)
        · exact h7
      have hacc :=
        ForkRules.accessDelegation_instructionFrame sevm.benvStat.rules
          dAccess callee
      rcases hdel : sevm.benvStat.rules.accessDelegation
          dAccess callee with
        ⟨dpv, na, cd, dagc, d8⟩
      rw [hdel] at hacc
      have h8 : Devm.InstructionFrame devm d8 :=
        Devm.instructionFrame_trans h7' hacc
      refine Xinst.shape_bindE h8 (chargeGas_instructionFrame _ d8) fun d9 h9 => ?_
      refine Xinst.shape_assert h9 ?_
      split
      · exact Xinst.shape_shortfall
          (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
      · refine Xinst.shape_call
          (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
          h7' (Or.inl ⟨rfl, rfl⟩) (Or.inr fun hnd => ?_)
        rw [ForkRules.accessDelegation_of_not_delegation hnd] at hdel
        exact (congrArg (fun t => t.2.2.1) hdel).symm
    | some state =>
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun callee d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      refine Xinst.shape_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
      have h7' : Devm.InstructionFrame devm (addAccessedAddress d7 callee) :=
        Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 callee)
      have hB1 : Devm.InstructionFrame devm
          (Devm.balReadAccount sevm.benvStat.rules callee
            (addAccessedAddress d7 callee)) :=
        Devm.instructionFrame_trans h7'
          (Devm.balReadAccount_instructionFrame _ _ _)
      refine Xinst.shape_assert h7 ?_
      refine Xinst.shape_assert h7 ?_
      refine Xinst.shape_assert hB1 ?_
      have hB2 : Devm.InstructionFrame devm
          (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d7 callee)
              callee).2.1
            (Devm.balReadAccount sevm.benvStat.rules callee
              (addAccessedAddress d7 callee))) :=
        Devm.instructionFrame_trans hB1
          (Devm.balReadAccount_instructionFrame _ _ _)
      have hC : Devm.InstructionFrame devm
          (completeDelegationAccess
            (Devm.balReadAccount sevm.benvStat.rules
              (sevm.benvStat.rules.delegationCost (addAccessedAddress d7 callee)
                callee).2.1
              (Devm.balReadAccount sevm.benvStat.rules callee
                (addAccessedAddress d7 callee)))
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d7 callee)
              callee).1
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d7 callee)
              callee).2.1).2 :=
        Devm.instructionFrame_trans hB2
          (completeDelegationAccess_instructionFrame _ _ _)
      refine Xinst.shape_bindE hC (chargeGas_instructionFrame _ _) fun dc hc => ?_
      split
      · refine Xinst.shape_bindE hc (chargeStateGas_instructionFrame _ _)
          fun d1' h1' => ?_
        refine Xinst.shape_bindE h1' (chargeGas_instructionFrame _ _)
          fun d2' h2' => ?_
        refine Xinst.shape_callAmsterdam
          (Devm.instructionFrame_trans h2'
            (Devm.instructionFrame_trans
              (Devm.drainStateGasReservoir_instructionFrame _)
              (Devm.memExtends_instructionFrame _ _)))
          h7' (Or.inl ⟨rfl, rfl⟩)
          (Or.inr fun hnd => amsterdamCallCode_of_not_delegation hnd)
      · simp only [Except.bind_ok]
        refine Xinst.shape_bindE hc (chargeGas_instructionFrame _ _)
          fun d2' h2' => ?_
        refine Xinst.shape_callAmsterdam
          (Devm.instructionFrame_trans h2'
            (Devm.instructionFrame_trans
              (Devm.drainStateGasReservoir_instructionFrame _)
              (Devm.memExtends_instructionFrame _ _)))
          h7' (Or.inl ⟨rfl, rfl⟩)
          (Or.inr fun hnd => amsterdamCallCode_of_not_delegation hnd)
  | callcode =>
    simp only [Xinst.step]
    cases sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun cadr d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      refine Xinst.shape_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
      dsimp only
      let dAccess : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d7 cadr
        | .flat _ => d7
      have h7' : Devm.InstructionFrame devm dAccess := by
        dsimp only [dAccess]
        split
        · exact Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 cadr)
        · exact h7
      have hacc :=
        ForkRules.accessDelegation_instructionFrame sevm.benvStat.rules
          dAccess cadr
      rcases hdel : sevm.benvStat.rules.accessDelegation
          dAccess cadr with
        ⟨dpv, na, cd, dagc, d8⟩
      rw [hdel] at hacc
      have h8 : Devm.InstructionFrame devm d8 :=
        Devm.instructionFrame_trans h7' hacc
      refine Xinst.shape_bindE h8 (chargeGas_instructionFrame _ d8) fun d9 h9 => ?_
      split
      · exact Xinst.shape_shortfall'
          (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
      · exact Xinst.shape_call
          (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
          h7' (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)
    | some state =>
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun cadr d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      refine Xinst.shape_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
      have h7' : Devm.InstructionFrame devm (addAccessedAddress d7 cadr) :=
        Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 cadr)
      have hB1 : Devm.InstructionFrame devm
          (Devm.balReadAccount sevm.benvStat.rules cadr
            (addAccessedAddress d7 cadr)) :=
        Devm.instructionFrame_trans h7'
          (Devm.balReadAccount_instructionFrame _ _ _)
      refine Xinst.shape_assert h7 ?_
      refine Xinst.shape_assert hB1 ?_
      have hB2 : Devm.InstructionFrame devm
          (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d7 cadr)
              cadr).2.1
            (Devm.balReadAccount sevm.benvStat.rules cadr
              (addAccessedAddress d7 cadr))) :=
        Devm.instructionFrame_trans hB1
          (Devm.balReadAccount_instructionFrame _ _ _)
      have hC : Devm.InstructionFrame devm
          (completeDelegationAccess
            (Devm.balReadAccount sevm.benvStat.rules
              (sevm.benvStat.rules.delegationCost (addAccessedAddress d7 cadr)
                cadr).2.1
              (Devm.balReadAccount sevm.benvStat.rules cadr
                (addAccessedAddress d7 cadr)))
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d7 cadr)
              cadr).1
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d7 cadr)
              cadr).2.1).2 :=
        Devm.instructionFrame_trans hB2
          (completeDelegationAccess_instructionFrame _ _ _)
      refine Xinst.shape_bindE hC (chargeGas_instructionFrame _ _) fun dc hc => ?_
      refine Xinst.shape_callAmsterdam
        (Devm.instructionFrame_trans hc
          (Devm.instructionFrame_trans
            (Devm.drainStateGasReservoir_instructionFrame _)
            (Devm.memExtends_instructionFrame _ _)))
        h7' (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)
  | delegatecall =>
    simp only [Xinst.step]
    cases sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun cadr d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      dsimp only
      let dAccess : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d6 cadr
        | .flat _ => d6
      have h6' : Devm.InstructionFrame devm dAccess := by
        dsimp only [dAccess]
        split
        · exact Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 cadr)
        · exact h6
      have hacc :=
        ForkRules.accessDelegation_instructionFrame sevm.benvStat.rules
          dAccess cadr
      rcases hdel : sevm.benvStat.rules.accessDelegation
          dAccess cadr with
        ⟨dpv, na, cd, dagc, d7⟩
      rw [hdel] at hacc
      have h7 : Devm.InstructionFrame devm d7 :=
        Devm.instructionFrame_trans h6' hacc
      refine Xinst.shape_bindE h7 (chargeGas_instructionFrame _ d7) fun d8 h8 => ?_
      exact Xinst.shape_call
        (Devm.instructionFrame_trans h8 (Devm.memExtends_instructionFrame d8 _))
        h6' (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
    | some state =>
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun cadr d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      have h6' : Devm.InstructionFrame devm (addAccessedAddress d6 cadr) :=
        Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 cadr)
      have hB1 : Devm.InstructionFrame devm
          (Devm.balReadAccount sevm.benvStat.rules cadr
            (addAccessedAddress d6 cadr)) :=
        Devm.instructionFrame_trans h6'
          (Devm.balReadAccount_instructionFrame _ _ _)
      refine Xinst.shape_assert h6 ?_
      refine Xinst.shape_assert hB1 ?_
      have hB2 : Devm.InstructionFrame devm
          (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d6 cadr)
              cadr).2.1
            (Devm.balReadAccount sevm.benvStat.rules cadr
              (addAccessedAddress d6 cadr))) :=
        Devm.instructionFrame_trans hB1
          (Devm.balReadAccount_instructionFrame _ _ _)
      have hC : Devm.InstructionFrame devm
          (completeDelegationAccess
            (Devm.balReadAccount sevm.benvStat.rules
              (sevm.benvStat.rules.delegationCost (addAccessedAddress d6 cadr)
                cadr).2.1
              (Devm.balReadAccount sevm.benvStat.rules cadr
                (addAccessedAddress d6 cadr)))
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d6 cadr)
              cadr).1
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d6 cadr)
              cadr).2.1).2 :=
        Devm.instructionFrame_trans hB2
          (completeDelegationAccess_instructionFrame _ _ _)
      refine Xinst.shape_bindE hC (chargeGas_instructionFrame _ _) fun dc hc => ?_
      exact Xinst.shape_callAmsterdam
        (Devm.instructionFrame_trans hc
          (Devm.instructionFrame_trans
            (Devm.drainStateGasReservoir_instructionFrame _)
            (Devm.memExtends_instructionFrame _ _)))
        h6' (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
  | staticcall =>
    simp only [Xinst.step]
    cases sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun tgt d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      dsimp only
      let dAccess : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d6 tgt
        | .flat _ => d6
      have h6' : Devm.InstructionFrame devm dAccess := by
        dsimp only [dAccess]
        split
        · exact Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 tgt)
        · exact h6
      have hacc :=
        ForkRules.accessDelegation_instructionFrame sevm.benvStat.rules
          dAccess tgt
      rcases hdel : sevm.benvStat.rules.accessDelegation
          dAccess tgt with
        ⟨dpv, na, cd, dagc, d7⟩
      rw [hdel] at hacc
      have h7 : Devm.InstructionFrame devm d7 :=
        Devm.instructionFrame_trans h6' hacc
      refine Xinst.shape_bindE h7 (chargeGas_instructionFrame _ d7) fun d8 h8 => ?_
      refine Xinst.shape_call
        (Devm.instructionFrame_trans h8 (Devm.memExtends_instructionFrame d8 _))
        h6' (Or.inl ⟨rfl, rfl⟩) (Or.inr fun hnd => ?_)
      rw [ForkRules.accessDelegation_of_not_delegation hnd] at hdel
      exact (congrArg (fun t => t.2.2.1) hdel).symm
    | some state =>
      refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun tgt d2 h2 => ?_
      refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      have h6' : Devm.InstructionFrame devm (addAccessedAddress d6 tgt) :=
        Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 tgt)
      have hB1 : Devm.InstructionFrame devm
          (Devm.balReadAccount sevm.benvStat.rules tgt
            (addAccessedAddress d6 tgt)) :=
        Devm.instructionFrame_trans h6'
          (Devm.balReadAccount_instructionFrame _ _ _)
      refine Xinst.shape_assert h6 ?_
      refine Xinst.shape_assert hB1 ?_
      have hB2 : Devm.InstructionFrame devm
          (Devm.balReadAccount sevm.benvStat.rules
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d6 tgt)
              tgt).2.1
            (Devm.balReadAccount sevm.benvStat.rules tgt
              (addAccessedAddress d6 tgt))) :=
        Devm.instructionFrame_trans hB1
          (Devm.balReadAccount_instructionFrame _ _ _)
      have hC : Devm.InstructionFrame devm
          (completeDelegationAccess
            (Devm.balReadAccount sevm.benvStat.rules
              (sevm.benvStat.rules.delegationCost (addAccessedAddress d6 tgt)
                tgt).2.1
              (Devm.balReadAccount sevm.benvStat.rules tgt
                (addAccessedAddress d6 tgt)))
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d6 tgt)
              tgt).1
            (sevm.benvStat.rules.delegationCost (addAccessedAddress d6 tgt)
              tgt).2.1).2 :=
        Devm.instructionFrame_trans hB2
          (completeDelegationAccess_instructionFrame _ _ _)
      refine Xinst.shape_bindE hC (chargeGas_instructionFrame _ _) fun dc hc => ?_
      refine Xinst.shape_callAmsterdam
        (Devm.instructionFrame_trans hc
          (Devm.instructionFrame_trans
            (Devm.drainStateGasReservoir_instructionFrame _)
            (Devm.memExtends_instructionFrame _ _)))
        h6' (Or.inl ⟨rfl, rfl⟩)
        (Or.inr fun hnd => amsterdamCallCode_of_not_delegation hnd)

/-- Without state gas, actual execution has only the ordinary done/create/call
shapes. An unavailable CREATE2 is retained as its actual error outcome. -/
lemma Xinst.step_shapeNoStateGas (sevm : Sevm) (devm : Devm) (x : Xinst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    Xinst.ShapeCovered sevm devm (Xinst.step sevm devm x) := by
  cases x with
  | create =>
    simp only [Xinst.step]
    cases hcase : sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shapeCovered_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shapeCovered_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
      refine Xinst.shapeCovered_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shapeCovered_bindE h3 (chargeGas_instructionFrame _ d3) fun d4 h4 => ?_
      exact Xinst.shapeCovered_create
        (Devm.instructionFrame_trans h4 (Devm.memExtends_instructionFrame d4 _))
    | some _state =>
      rw [hsg] at hcase; cases hcase
  | create2 =>
    by_cases hc2 : sevm.benvStat.rules.op.create2 = true
    ·
      simp only [Xinst.step, hc2, ↓reduceIte]
      cases hcase : sevm.benvStat.rules.stateGas with
      | none =>
        refine Xinst.shapeCovered_bind (Devm.instructionFrame_refl devm)
          (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
        refine Xinst.shapeCovered_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
        refine Xinst.shapeCovered_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
        refine Xinst.shapeCovered_bind h3 (Devm.pop_instructionFrame d3) fun _ d4 h4 => ?_
        refine Xinst.shapeCovered_bindE h4 (chargeGas_instructionFrame _ d4) fun d5 h5 => ?_
        exact Xinst.shapeCovered_create
          (Devm.instructionFrame_trans h5 (Devm.memExtends_instructionFrame d5 _))
      | some _state =>
        rw [hsg] at hcase; cases hcase
    · simp only [Xinst.step, hc2]
      exact Xinst.shapeCovered_error (Devm.instructionFrame_refl devm)
  | call =>
    simp only [Xinst.step]
    cases hcase : sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shapeCovered_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shapeCovered_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun callee d2 h2 => ?_
      refine Xinst.shapeCovered_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shapeCovered_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shapeCovered_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shapeCovered_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      refine Xinst.shapeCovered_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
      dsimp only
      let dAccess : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d7 callee
        | .flat _ => d7
      have h7' : Devm.InstructionFrame devm dAccess := by
        dsimp only [dAccess]
        split
        · exact Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 callee)
        · exact h7
      have hacc :=
        ForkRules.accessDelegation_instructionFrame sevm.benvStat.rules
          dAccess callee
      rcases hdel : sevm.benvStat.rules.accessDelegation
          dAccess callee with
        ⟨dpv, na, cd, dagc, d8⟩
      rw [hdel] at hacc
      have h8 : Devm.InstructionFrame devm d8 :=
        Devm.instructionFrame_trans h7' hacc
      refine Xinst.shapeCovered_bindE h8 (chargeGas_instructionFrame _ d8) fun d9 h9 => ?_
      refine Xinst.shapeCovered_assert h9 ?_
      split
      · exact Xinst.shapeCovered_shortfall
          (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
      · refine Xinst.shapeCovered_call
          (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
          h7' (Or.inl ⟨rfl, rfl⟩) (Or.inr fun hnd => ?_)
        rw [ForkRules.accessDelegation_of_not_delegation hnd] at hdel
        exact (congrArg (fun t => t.2.2.1) hdel).symm
    | some _state =>
      rw [hsg] at hcase; cases hcase
  | callcode =>
    simp only [Xinst.step]
    cases hcase : sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shapeCovered_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shapeCovered_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun cadr d2 h2 => ?_
      refine Xinst.shapeCovered_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shapeCovered_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shapeCovered_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shapeCovered_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      refine Xinst.shapeCovered_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
      dsimp only
      let dAccess : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d7 cadr
        | .flat _ => d7
      have h7' : Devm.InstructionFrame devm dAccess := by
        dsimp only [dAccess]
        split
        · exact Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 cadr)
        · exact h7
      have hacc :=
        ForkRules.accessDelegation_instructionFrame sevm.benvStat.rules
          dAccess cadr
      rcases hdel : sevm.benvStat.rules.accessDelegation
          dAccess cadr with
        ⟨dpv, na, cd, dagc, d8⟩
      rw [hdel] at hacc
      have h8 : Devm.InstructionFrame devm d8 :=
        Devm.instructionFrame_trans h7' hacc
      refine Xinst.shapeCovered_bindE h8 (chargeGas_instructionFrame _ d8) fun d9 h9 => ?_
      split
      · exact Xinst.shapeCovered_shortfall'
          (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
      · exact Xinst.shapeCovered_call
          (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
          h7' (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)
    | some _state =>
      rw [hsg] at hcase; cases hcase
  | delegatecall =>
    simp only [Xinst.step]
    cases hcase : sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shapeCovered_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shapeCovered_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun cadr d2 h2 => ?_
      refine Xinst.shapeCovered_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shapeCovered_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shapeCovered_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shapeCovered_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      dsimp only
      let dAccess : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d6 cadr
        | .flat _ => d6
      have h6' : Devm.InstructionFrame devm dAccess := by
        dsimp only [dAccess]
        split
        · exact Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 cadr)
        · exact h6
      have hacc :=
        ForkRules.accessDelegation_instructionFrame sevm.benvStat.rules
          dAccess cadr
      rcases hdel : sevm.benvStat.rules.accessDelegation
          dAccess cadr with
        ⟨dpv, na, cd, dagc, d7⟩
      rw [hdel] at hacc
      have h7 : Devm.InstructionFrame devm d7 :=
        Devm.instructionFrame_trans h6' hacc
      refine Xinst.shapeCovered_bindE h7 (chargeGas_instructionFrame _ d7) fun d8 h8 => ?_
      exact Xinst.shapeCovered_call
        (Devm.instructionFrame_trans h8 (Devm.memExtends_instructionFrame d8 _))
        h6' (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
    | some _state =>
      rw [hsg] at hcase; cases hcase
  | staticcall =>
    simp only [Xinst.step]
    cases hcase : sevm.benvStat.rules.stateGas with
    | none =>
      refine Xinst.shapeCovered_bind (Devm.instructionFrame_refl devm)
        (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
      refine Xinst.shapeCovered_bind h1 (Devm.popToAdr_instructionFrame d1)
        fun tgt d2 h2 => ?_
      refine Xinst.shapeCovered_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
      refine Xinst.shapeCovered_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
      refine Xinst.shapeCovered_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
      refine Xinst.shapeCovered_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
      dsimp only
      let dAccess : Devm := match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress d6 tgt
        | .flat _ => d6
      have h6' : Devm.InstructionFrame devm dAccess := by
        dsimp only [dAccess]
        split
        · exact Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 tgt)
        · exact h6
      have hacc :=
        ForkRules.accessDelegation_instructionFrame sevm.benvStat.rules
          dAccess tgt
      rcases hdel : sevm.benvStat.rules.accessDelegation
          dAccess tgt with
        ⟨dpv, na, cd, dagc, d7⟩
      rw [hdel] at hacc
      have h7 : Devm.InstructionFrame devm d7 :=
        Devm.instructionFrame_trans h6' hacc
      refine Xinst.shapeCovered_bindE h7 (chargeGas_instructionFrame _ d7) fun d8 h8 => ?_
      refine Xinst.shapeCovered_call
        (Devm.instructionFrame_trans h8 (Devm.memExtends_instructionFrame d8 _))
        h6' (Or.inl ⟨rfl, rfl⟩) (Or.inr fun hnd => ?_)
      rw [ForkRules.accessDelegation_of_not_delegation hnd] at hdel
      exact (congrArg (fun t => t.2.2.1) hdel).symm
    | some _state =>
      rw [hsg] at hcase; cases hcase

lemma Xinst.step_shapeCovered (sevm : Sevm) (devm : Devm) (x : Xinst)
    (hfork : CoveredFork sevm.benvStat.fork) :
    Xinst.ShapeCovered sevm devm (Xinst.step sevm devm x) :=
  Xinst.step_shapeNoStateGas sevm devm x hfork.rules_stateGas_none

/-! ### What a spawned child frame starts from

`Prog.At` bookkeeping has to survive a suspension: the child's initial machine
must still see the contract's code, and — when the child *is* the contract —
must start at `pc = 0` with that code loaded.  With the interpreter flattened
all of this is read off the frame-entry equation plus one dispatch-level case
split, which is what the old six-lemma `prep_*` family did by hand. -/

lemma ByteArray.eq_empty_of_size_eq_zero {b : ByteArray} (h : b.size = 0) :
    b = .empty := by
  cases b with
  | mk data =>
    cases data with
    | mk l =>
      cases l with
      | nil => rfl
      | cons _ _ => contradiction

lemma Frame.enter_run_pc {f : Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    cevm.pc = 0 := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

lemma Frame.enter_run_code {f : Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    cevm.sta.code = f.inner.code := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

lemma Frame.enter_run_currentTarget {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) :
    cevm.sta.currentTarget = f.inner.currentTarget := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

lemma Frame.enter_run_getCode {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) (a : Adr) :
    cevm.dyna.getCode a = f.inner.benv.state.getCode a := by
  obtain ⟨benv, hbenv, rfl⟩ := Frame.enter_run_inv h
  exact benvAfterTransfer_ok_getCode hbenv a

lemma genericCreate.step_spawn_frame
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress mi ms
      = .spawn f rsm) :
    (∀ a : Adr, f.inner.benv.state.getCode a = devm.getCode a) ∧
      f.inner.currentTarget = newAddress ∧
      devm.getCode newAddress = .empty := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rename_i h_collision
  have hpar : ∀ b : Adr,
      (addAccessedAddress
        (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress).getCode b
        = devm.getCode b := by
    intro b
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode
  refine ⟨fun a => ?_, rfl, ?_⟩
  · simp only [Frame.ofCreate]
    rw [processCreateMessage.msg_getCode, createMsg_benv_state_getCode]
    exact hpar a
  · push Not at h_collision
    rw [← hpar newAddress]
    exact ByteArray.eq_empty_of_size_eq_zero h_collision.2

lemma genericCall.step_spawn_frame
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool}
    {f : Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress stv
      isSt ii isz oi osz code dp = .spawn f rsm) :
    (∀ a : Adr, f.inner.benv.state.getCode a = devm.getCode a) ∧
      f.inner.currentTarget = target ∧ f.inner.code = code := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  exact ⟨fun _ => rfl, rfl, rfl⟩

lemma genericCallAmsterdam.step_spawn_frame
    {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp nac ib : Bool}
    {f : Frame} {rsm : Resume}
    (hs : genericCallAmsterdam.step sevm state devm gas reservoir value caller
      target codeAddress stv isSt ii isz oi osz code dp nac ib
      = .spawn f rsm) :
    (∀ a : Adr, f.inner.benv.state.getCode a = devm.getCode a) ∧
      f.inner.currentTarget = target ∧ f.inner.code = code := by
  simp only [genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  exact ⟨fun _ => rfl, rfl, rfl⟩

lemma genericCreateAmsterdam.step_spawn_frame
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreateAmsterdam.step sevm state devm endowment newAddress
      mi ms = .spawn f rsm) :
    (∀ a : Adr, f.inner.benv.state.getCode a = devm.getCode a) ∧
      f.inner.currentTarget = newAddress ∧
      devm.getCode newAddress = .empty := by
  simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  · rename_i v heq h_coll
    have hpar : ∀ b : Adr,
        (v.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce
          sevm.currentTarget).getCode b = devm.getCode b := by
      intro b
      rw [Devm.incrNonce_getCode, Devm.drainStateGasReservoir_getCode,
        Devm.withholdCreateGas_getCode, chargeStateGas_getCode_eq heq,
        Devm.balReadAccount_getCode, addAccessedAddress_getCode,
        Devm.balReadAccount_getCode, Devm.withReturnData_getCode]
    have hcode : (v.withholdCreateGas.2).getCode newAddress
        = devm.getCode newAddress := by
      rw [Devm.withholdCreateGas_getCode, chargeStateGas_getCode_eq heq,
        Devm.balReadAccount_getCode, addAccessedAddress_getCode,
        Devm.balReadAccount_getCode, Devm.withReturnData_getCode]
    refine ⟨fun a => ?_, rfl, ?_⟩
    · simp only [Frame.ofCreate]
      rw [processCreateMessage.msg_getCode, createMsg_benv_state_getCode]
      exact hpar a
    · push Not at h_coll
      rw [← hcode]
      exact ByteArray.eq_empty_of_size_eq_zero h_coll.2
  · rename_i h_coll
    have hpar : ∀ b : Adr,
        ((Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
            sevm.currentTarget (devm.withReturnData [])) newAddress)
          ).withholdCreateGas.2.drainStateGasReservoir.2.incrNonce
          sevm.currentTarget).getCode b = devm.getCode b := by
      intro b
      rw [Devm.incrNonce_getCode, Devm.drainStateGasReservoir_getCode,
        Devm.withholdCreateGas_getCode, Devm.balReadAccount_getCode,
        addAccessedAddress_getCode, Devm.balReadAccount_getCode,
        Devm.withReturnData_getCode]
    have hcode : ((Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
            sevm.currentTarget (devm.withReturnData [])) newAddress)
          ).withholdCreateGas.2).getCode newAddress
        = devm.getCode newAddress := by
      rw [Devm.withholdCreateGas_getCode, Devm.balReadAccount_getCode,
        addAccessedAddress_getCode, Devm.balReadAccount_getCode,
        Devm.withReturnData_getCode]
    refine ⟨fun a => ?_, rfl, ?_⟩
    · simp only [Frame.ofCreate]
      rw [processCreateMessage.msg_getCode, createMsg_benv_state_getCode]
      exact hpar a
    · push Not at h_coll
      rw [← hcode]
      exact ByteArray.eq_empty_of_size_eq_zero h_coll.2

lemma Xinst.step_spawn_getCode {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (hs : Xinst.step sevm devm x = .spawn f rsm)
    (a : Adr) : f.inner.benv.state.getCode a = devm.getCode a := by
  rcases Xinst.step_shape sevm devm x with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hsh⟩ |
    ⟨d, st, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, st, g, r, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      nac, ib, hf, -, -, -, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · rw [(genericCreate.step_spawn_frame hs).1 a, hf.getCode a]
  · rw [(genericCall.step_spawn_frame hs).1 a, hf.getCode a]
  · rw [(genericCreateAmsterdam.step_spawn_frame hs).1 a, hf.getCode a]
  · rw [(genericCallAmsterdam.step_spawn_frame hs).1 a, hf.getCode a]

private lemma ForkRules.accessDelegation_codeAddress_of_none
    {rules : ForkRules} {d : Devm} {adr : Adr}
    (h : getDelegatedCodeAddress (d.getCode adr) = none) :
    (rules.accessDelegation d adr).2.1 = adr := by
  unfold ForkRules.accessDelegation
  split
  · dsimp only [GasSchedule.accessDelegation]
    rw [show getDelegatedCodeAddress (d.state.getCode adr) = none from h]
  · rfl

private lemma ForkRules.delegationCost_codeAddress_of_none
    {rules : ForkRules} {d : Devm} {adr : Adr}
    (h : getDelegatedCodeAddress (d.getCode adr) = none) :
    (rules.delegationCost d adr).2.1 = adr := by
  unfold ForkRules.delegationCost
  split
  · have hnone : getDelegatedCodeAddress (d.state.getCode adr) = none := h
    unfold GasSchedule.delegationCost
    simp only [hnone]
  · rfl

/-- An actual call-type spawn aimed away from the current account and at an
already-code-bearing account is a direct CALL/STATICCALL child. CREATE and
CREATE2 are excluded by freshness, while CALLCODE and DELEGATECALL retain the
parent's target. The CALL/STATICCALL arms additionally need the callee to carry
no EIP-7702 delegation designator: a designator would resolve the child's code
address to the delegate rather than to the callee. -/
theorem Xinst.step_spawn_codeAddress_eq_currentTarget
    {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm)
    (hne : sevm.currentTarget ≠ f.inner.currentTarget)
    (hcode : devm.getCode f.inner.currentTarget ≠ .empty)
    (hnodel :
      getDelegatedCodeAddress (devm.getCode f.inner.currentTarget) = none) :
    f.inner.codeAddress = some f.inner.currentTarget := by
  have horig := hs
  cases x with
  | create =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have hfresh := genericCreate.step_spawn_frame hs
          apply False.elim
          apply hcode
          calc
            devm.getCode f.inner.currentTarget =
                f.inner.benv.state.getCode f.inner.currentTarget :=
              (Xinst.step_spawn_getCode horig _).symm
            _ = _ := hfresh.1 _
            _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
        | have hfresh := genericCreateAmsterdam.step_spawn_frame hs
          apply False.elim
          apply hcode
          calc
            devm.getCode f.inner.currentTarget =
                f.inner.benv.state.getCode f.inner.currentTarget :=
              (Xinst.step_spawn_getCode horig _).symm
            _ = _ := hfresh.1 _
            _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
  | create2 =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have hfresh := genericCreate.step_spawn_frame hs
          apply False.elim
          apply hcode
          calc
            devm.getCode f.inner.currentTarget =
                f.inner.benv.state.getCode f.inner.currentTarget :=
              (Xinst.step_spawn_getCode horig _).symm
            _ = _ := hfresh.1 _
            _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
        | have hfresh := genericCreateAmsterdam.step_spawn_frame hs
          apply False.elim
          apply hcode
          calc
            devm.getCode f.inner.currentTarget =
                f.inner.benv.state.getCode f.inner.currentTarget :=
              (Xinst.step_spawn_getCode horig _).symm
            _ = _ := hfresh.1 _
            _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
  | call =>
      simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hs
      split at hs
      · -- Legacy: no state gas.
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vgas hgas
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vcallee hcallee
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vval hval
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vii hii
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vis his
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ voi hoi
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vos hos
        -- The delegation lookup runs on the popped-and-recorded machine, so the
        -- premise's code fact has to travel down the operand pops first.
        have hgc : ∀ a : Adr,
            vos.2.getCode a = devm.getCode a := by
          intro a
          rw [Devm.popToNat_getCode hos,
            Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
            Devm.popToNat_getCode hii, Devm.pop_getCode hval,
            Devm.popToAdr_getCode hcallee, Devm.pop_getCode hgas]
        repeat' split at hs
        all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
        all_goals first
          | cases hs
          | simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
              Except.pure] at hs
            repeat' split at hs
            all_goals
              simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
            all_goals obtain ⟨rfl, rfl⟩ := hs
            all_goals
              refine congrArg some
                (ForkRules.accessDelegation_codeAddress_of_none ?_)
              simpa only [Frame.ofCall, callMsg, addAccessedAddress_getCode, hgc] using hnodel
      · -- Amsterdam: delegation priced without warming.
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vgas hgas
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vcallee hcallee
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vval hval
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vii hii
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vis his
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ voi hoi
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vos hos
        have hgc : ∀ a : Adr,
            vos.2.getCode a = devm.getCode a := by
          intro a
          rw [Devm.popToNat_getCode hos,
            Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
            Devm.popToNat_getCode hii, Devm.pop_getCode hval,
            Devm.popToAdr_getCode hcallee, Devm.pop_getCode hgas]
        repeat' split at hs
        all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
        all_goals first
          | cases hs
          | simp only [genericCallAmsterdam.step, Bind.bind, Except.bind,
              Pure.pure, Except.pure] at hs
            repeat' split at hs
            all_goals
              simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
            all_goals obtain ⟨rfl, rfl⟩ := hs
            all_goals
              refine congrArg some
                (ForkRules.delegationCost_codeAddress_of_none ?_)
              simpa only [Frame.ofCall, callMsg, addAccessedAddress_getCode, hgc] using hnodel
  | callcode =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have htgt := (genericCall.step_spawn_frame hs).2.1
          exact False.elim (hne htgt.symm)
        | have htgt := (genericCallAmsterdam.step_spawn_frame hs).2.1
          exact False.elim (hne htgt.symm)
  | delegatecall =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have htgt := (genericCall.step_spawn_frame hs).2.1
          exact False.elim (hne htgt.symm)
        | have htgt := (genericCallAmsterdam.step_spawn_frame hs).2.1
          exact False.elim (hne htgt.symm)
  | staticcall =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      split at hs
      · -- Legacy: no state gas.
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vgas hgas
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vtgt htgt
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vii hii
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vis his
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ voi hoi
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vos hos
        have hgc : ∀ a : Adr,
            vos.2.getCode a = devm.getCode a := by
          intro a
          rw [Devm.popToNat_getCode hos,
            Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
            Devm.popToNat_getCode hii, Devm.popToAdr_getCode htgt,
            Devm.pop_getCode hgas]
        repeat' split at hs
        all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
        all_goals first
          | cases hs
          | simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
              Except.pure] at hs
            repeat' split at hs
            all_goals
              simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
            all_goals obtain ⟨rfl, rfl⟩ := hs
            all_goals
              refine congrArg some
                (ForkRules.accessDelegation_codeAddress_of_none ?_)
              simpa only [Frame.ofCall, callMsg, addAccessedAddress_getCode, hgc] using hnodel
      · -- Amsterdam: delegation priced without warming.
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vgas hgas
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vtgt htgt
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vii hii
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vis his
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ voi hoi
        split at hs
        · simp only [XStep.ofExcept, reduceCtorEq] at hs
        rename_i _ vos hos
        have hgc : ∀ a : Adr,
            vos.2.getCode a = devm.getCode a := by
          intro a
          rw [Devm.popToNat_getCode hos,
            Devm.popToNat_getCode hoi, Devm.popToNat_getCode his,
            Devm.popToNat_getCode hii, Devm.popToAdr_getCode htgt,
            Devm.pop_getCode hgas]
        repeat' split at hs
        all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
        all_goals first
          | cases hs
          | simp only [genericCallAmsterdam.step, Bind.bind, Except.bind,
              Pure.pure, Except.pure] at hs
            repeat' split at hs
            all_goals
              simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
            all_goals obtain ⟨rfl, rfl⟩ := hs
            all_goals
              refine congrArg some
                (ForkRules.delegationCost_codeAddress_of_none ?_)
              simpa only [Frame.ofCall, callMsg, addAccessedAddress_getCode, hgc] using hnodel
/-- Where a spawned child's code comes from.  Create frames enter fresh code at
an address that had none; `CALLCODE`/`DELEGATECALL` keep the parent's target;
the remaining call kinds load the callee's own code unless it delegates. -/
lemma Xinst.step_spawn_source {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (hs : Xinst.step sevm devm x = .spawn f rsm) :
    devm.getCode f.inner.currentTarget = .empty ∨
    f.inner.currentTarget = sevm.currentTarget ∨
    ( ¬ isValidDelegation (devm.getCode f.inner.currentTarget) →
        f.inner.code = devm.getCode f.inner.currentTarget ) := by
  rcases Xinst.step_shape sevm devm x with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, hf₀, -, hsrc, hsh⟩ |
    ⟨d, st, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, st, g, r, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      nac, ib, hf, hf₀, -, hsrc, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · obtain ⟨-, htgt, hempty⟩ := genericCreate.step_spawn_frame hs
    exact Or.inl (by rw [htgt, hf.getCode na]; exact hempty)
  · obtain ⟨-, htgt, hcode⟩ := genericCall.step_spawn_frame hs
    rcases hsrc with rfl | hsrc
    · exact Or.inr (Or.inl htgt)
    · refine Or.inr (Or.inr fun hnd => ?_)
      rw [htgt] at hnd ⊢
      rw [hf₀.getCode t] at hnd ⊢
      rw [hcode]
      exact hsrc hnd
  · obtain ⟨-, htgt, hempty⟩ := genericCreateAmsterdam.step_spawn_frame hs
    exact Or.inl (by rw [htgt, hf.getCode na]; exact hempty)
  · obtain ⟨-, htgt, hcode⟩ := genericCallAmsterdam.step_spawn_frame hs
    rcases hsrc with rfl | hsrc
    · exact Or.inr (Or.inl htgt)
    · refine Or.inr (Or.inr fun hnd => ?_)
      rw [htgt] at hnd ⊢
      rw [hf₀.getCode t] at hnd ⊢
      rw [hcode]
      exact hsrc hnd

/-- Everything the child slot has to know about its own program location. -/
lemma Evm.step_spawn_child {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (he : f.enter = .run cevm) :
    cevm.pc = 0 ∧
    (∀ a : Adr, cevm.dyna.getCode a = devm.getCode a) ∧
    ( sevm.currentTarget ≠ cevm.sta.currentTarget →
      devm.getCode cevm.sta.currentTarget ≠ .empty →
      ¬ isValidDelegation (devm.getCode cevm.sta.currentTarget) →
      cevm.sta.code = devm.getCode cevm.sta.currentTarget ) := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hs
  have htgt := Frame.enter_run_currentTarget he
  have hcode := Frame.enter_run_code he
  refine ⟨Frame.enter_run_pc he, fun a => ?_, fun hne hnotEmpty hnotDel => ?_⟩
  · rw [Frame.enter_run_getCode he a]
    exact Xinst.step_spawn_getCode hx a
  · rw [htgt] at hne hnotEmpty hnotDel ⊢
    rw [hcode]
    rcases Xinst.step_spawn_source hx with hempty | hsame | hsrc
    · exact absurd hempty hnotEmpty
    · exact absurd hsame.symm hne
    · exact hsrc hnotDel

lemma Linst.selfdestruct_preserves_code_created {sevm : Sevm} {devm : Devm} {exn : Execution}
    (run : Linst.Run sevm devm .selfdestruct exn) :
    ∀ adr : Adr, Execution.getCode exn adr = devm.getCode adr ∧
      Execution.createdAccounts exn = devm.createdAccounts := by
  intro adr
  dsimp only [Linst.Run, Linst.run, ne_eq, Except.bind_ok, ite_not, Lean.Elab.WF.paramLet,
    Devm.balReadAccount_accessedAddresses, Devm.balReadAccount_getAcct] at run
  revert run
  cases hsg : sevm.benvStat.rules.stateGas
  · -- Covered-fork lane: pop, read both accounts, price, charge, sweep.
    intro run
    dsimp only [Devm.balReadAccount_accessedAddresses, ite_not, bind, Except.bind] at run
    revert run
    cases h1 : devm.popToAdr <;> dsimp only [Devm.balReadAccount_accessedAddresses, ite_not]
    case error err =>
      intro run; rw [← run]; exact ⟨Devm.popToAdr_getCode_err h1 adr, Devm.popToAdr_createdAccounts_err h1⟩
    case ok res1 =>
      have h_br2 : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).getCode adr = res1.2.getCode adr :=
        Devm.balReadAccount_getCode.trans Devm.balReadAccount_getCode
      have h_acc : (match sevm.benvStat.rules.access with | .eip2929 => (if res1.1 ∉ (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).accessedAddresses then (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)) res1.1, gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess) else ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)) | .flat _ => ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)).1.getCode adr = res1.2.getCode adr := by
        cases haccess : sevm.benvStat.rules.access with
        | flat _ => exact h_br2
        | eip2929 =>
          dsimp only
          split
          · exact (addAccessedAddress_getCode ..).trans h_br2
          · exact h_br2
      have h_acc_ca : (match sevm.benvStat.rules.access with | .eip2929 => (if res1.1 ∉ (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).accessedAddresses then (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)) res1.1, gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess) else ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)) | .flat _ => ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)), gasSelfDestruct)).1.createdAccounts = res1.2.createdAccounts := by
        cases haccess : sevm.benvStat.rules.access with
        | flat _ => simp only [Devm.balReadAccount_createdAccounts]
        | eip2929 =>
          dsimp only
          split <;> change (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
            (Devm.balReadAccount sevm.benvStat.rules res1.1 res1.2)).createdAccounts =
              res1.2.createdAccounts
          all_goals simp only [Devm.balReadAccount_createdAccounts]
      cases h2 : chargeGas _ _ <;> dsimp only
      case error err =>
        intro run; rw [← run]
        change err.2.getCode adr = devm.getCode adr ∧ err.2.createdAccounts = devm.createdAccounts
        exact ⟨(chargeGas_getCode_err h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr)), (chargeGas_createdAccounts_eq h2).trans (h_acc_ca.trans (Devm.popToAdr_createdAccounts_eq h1))⟩
      case ok res2 =>
        cases h3 : assertDynamic sevm res2
        case error err =>
          intro run; rw [← run]
          dsimp only [assertDynamic, assert, Bool.not_eq_eq_eq_not, Bool.not_true] at h3
          split at h3
          · contradiction
          · simp only [Except.error.injEq] at h3; subst h3
            change res2.getCode adr = devm.getCode adr ∧ res2.createdAccounts = devm.createdAccounts
            exact ⟨(chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr)), (chargeGas_createdAccounts_eq h2).trans (h_acc_ca.trans (Devm.popToAdr_createdAccounts_eq h1))⟩
        case ok _ =>
          cases h4 : res2.subBal _ _ <;> dsimp only [Option.toExcept]
          case none =>
            intro run; rw [← run]
            change res2.getCode adr = devm.getCode adr ∧ res2.createdAccounts = devm.createdAccounts
            exact ⟨(chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr)), (chargeGas_createdAccounts_eq h2).trans (h_acc_ca.trans (Devm.popToAdr_createdAccounts_eq h1))⟩
          case some res3 =>
            have h_sub : res3.getCode adr = res2.getCode adr := by
              dsimp only [Devm.subBal, Option.bind_eq_bind] at h4
              cases h_st : res2.state.subBal _ _
              case none =>
                rw [h_st] at h4; contradiction
              case some st =>
                rw [h_st] at h4; dsimp only [Option.bind_some] at h4
                simp only [Option.some.injEq] at h4; subst h4
                change st.getCode adr = res2.getCode adr
                exact State.subBal_getCode h_st
            let credited := res3.creditBeneficiary sevm.benvStat.rules res1.1
              (res1.2.getAcct sevm.currentTarget).bal
            have hcredit : credited.getCode adr = devm.getCode adr :=
              (Devm.creditBeneficiary_getCode _ _ _ _ _).trans
                (h_sub.trans ((chargeGas_getCode_eq h2 adr).trans
                  (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))))
            change (if sevm.currentTarget ∈ credited.createdAccounts ∨
                sevm.benvStat.rules.settle.selfdestructOnlyCreated = false then
              .ok (creditSelfdestructRefund sevm.benvStat.rules
                (sevm.currentTarget ∈ credited.accountsToDelete)
                (addAccountToDelete (credited.setBal sevm.currentTarget 0)
                  sevm.currentTarget)) else .ok credited) = exn → _
            split
            · intro run; rw [← run]
              constructor
              · change (creditSelfdestructRefund _ _ _).getCode adr = _
                rw [creditSelfdestructRefund_getCode]
                change (credited.setBal sevm.currentTarget 0).getCode adr = _
                exact (State.setBal_getCode credited.state sevm.currentTarget adr 0).trans hcredit
              · change (creditSelfdestructRefund _ _ _).createdAccounts = _
                rw [show (creditSelfdestructRefund sevm.benvStat.rules
                    (sevm.currentTarget ∈ credited.accountsToDelete)
                    (addAccountToDelete (credited.setBal sevm.currentTarget 0) sevm.currentTarget)).createdAccounts =
                    credited.createdAccounts from congrArg Prod.snd (creditSelfdestructRefund_delSets _ _ _)]
                exact (congrArg Prod.snd (Devm.creditBeneficiary_delSets _ _ _ _)).trans
                  ((Devm.subBal_createdAccounts_eq h4).trans
                    ((chargeGas_createdAccounts_eq h2).trans
                      (h_acc_ca.trans (Devm.popToAdr_createdAccounts_eq h1))))
            · intro run; rw [← run]
              refine ⟨hcredit, ?_⟩
              exact (congrArg Prod.snd (Devm.creditBeneficiary_delSets _ _ _ _)).trans
                ((Devm.subBal_createdAccounts_eq h4).trans
                  ((chargeGas_createdAccounts_eq h2).trans
                    (h_acc_ca.trans (Devm.popToAdr_createdAccounts_eq h1))))
  · -- Amsterdam lane: static check first, priced access, state charges, logging sweep.
    rename_i state
    intro run
    dsimp only [Devm.balReadAccount_accessedAddresses, ite_not, bind, Except.bind] at run
    revert run
    cases h0 : assertDynamic sevm devm <;> dsimp only [ite_not]
    case error err =>
      intro run; rw [← run]
      dsimp only [assertDynamic, assert, Bool.not_eq_eq_eq_not, Bool.not_true] at h0
      split at h0
      · contradiction
      · simp only [Except.error.injEq] at h0; subst h0
        exact ⟨rfl, rfl⟩
    case ok _ =>
      cases h1 : devm.popToAdr <;> dsimp only [ite_not]
      case error err =>
        intro run; rw [← run]; exact ⟨Devm.popToAdr_getCode_err h1 adr, Devm.popToAdr_createdAccounts_err h1⟩
      case ok res1 =>
        cases hg : Except.assert (gasSelfDestruct + (if res1.1 ∉ res1.2.accessedAddresses then sevm.benvStat.rules.gas.coldAccountAccess else 0) ≤ res1.2.gasLeft) (⟨.halt (.outOfGas .none), res1.2⟩ : EvmError × Devm) <;> dsimp only [ite_not]
        case error err =>
          intro run; rw [← run]
          dsimp only [assert, ite_not] at hg
          by_cases hle : gasSelfDestruct + (if res1.1 ∉ res1.2.accessedAddresses then sevm.benvStat.rules.gas.coldAccountAccess else 0) ≤ res1.2.gasLeft
          · simp only [hle, ite_true] at hg
            contradiction
          · simp only [hle, ite_false] at hg
            simp only [Except.error.injEq] at hg; subst hg
            exact ⟨Devm.popToAdr_getCode_eq h1 adr, Devm.popToAdr_createdAccounts_eq h1⟩
        case ok _ =>
          have h_warm : (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2).getCode adr = res1.2.getCode adr := by
            split
            · exact addAccessedAddress_getCode ..
            · rfl
          have h_wb : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (Devm.balReadAccount sevm.benvStat.rules res1.1 (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2))).getCode adr = res1.2.getCode adr :=
            Devm.balReadAccount_getCode.trans (Devm.balReadAccount_getCode.trans h_warm)
          have h_wb_ca : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
              (Devm.balReadAccount sevm.benvStat.rules res1.1
                (if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2))).createdAccounts =
              res1.2.createdAccounts := by
            simp only [Devm.balReadAccount_createdAccounts]
            split <;> rfl
          cases hchg : chargeGas _ _ <;> dsimp only [ite_not]
          case error err =>
            intro run; rw [← run]
            exact ⟨(chargeGas_getCode_err hchg adr).trans (h_wb.trans (Devm.popToAdr_getCode_eq h1 adr)), (chargeGas_createdAccounts_eq hchg).trans (h_wb_ca.trans (Devm.popToAdr_createdAccounts_eq h1))⟩
          case ok res2 =>
            cases hstg : chargeStateGas _ _ <;> dsimp only [ite_not]
            case error err =>
              intro run; rw [← run]
              exact ⟨(chargeStateGas_getCode_err hstg adr).trans ((chargeGas_getCode_eq hchg adr).trans (h_wb.trans (Devm.popToAdr_getCode_eq h1 adr))), (chargeStateGas_createdAccounts_eq hstg).trans ((chargeGas_createdAccounts_eq hchg).trans (h_wb_ca.trans (Devm.popToAdr_createdAccounts_eq h1)))⟩
            case ok res2b =>
              cases h4 : res2b.subBal _ _ <;> dsimp only [Option.toExcept, ite_not]
              case none =>
                intro run; rw [← run]
                exact ⟨(chargeStateGas_getCode_eq hstg adr).trans ((chargeGas_getCode_eq hchg adr).trans (h_wb.trans (Devm.popToAdr_getCode_eq h1 adr))), (chargeStateGas_createdAccounts_eq hstg).trans ((chargeGas_createdAccounts_eq hchg).trans (h_wb_ca.trans (Devm.popToAdr_createdAccounts_eq h1)))⟩
              case some res3 =>
                have h_sub : res3.getCode adr = res2b.getCode adr := by
                  dsimp only [Devm.subBal, Option.bind_eq_bind] at h4
                  cases h_st : res2b.state.subBal _ _
                  case none =>
                    rw [h_st] at h4; contradiction
                  case some st =>
                    rw [h_st] at h4; dsimp only [Option.bind_some] at h4
                    simp only [Option.some.injEq] at h4; subst h4
                    change st.getCode adr = res2b.getCode adr
                    exact State.subBal_getCode h_st
                have h_add : (res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).getCode adr = res3.getCode adr := by
                  dsimp only [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
                have h_emit : ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).getCode adr = (res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).getCode adr :=
                  ((Devm.emitTransferLog_instructionFrame _ _ _ _).getCode adr).symm
                have h_emit_ca : ((res3.addBal res1.1
                    (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1
                      else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog
                    sevm.currentTarget res1.1
                    (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1
                      else res1.2)).getAcct sevm.currentTarget).bal).createdAccounts =
                    res3.createdAccounts :=
                  (Devm.emitTransferLog_instructionFrame _ _ _ _).createdAccounts.symm
                by_cases h_if : sevm.currentTarget ∈ ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).createdAccounts
                · simp only [h_if, ite_eq_left]
                  intro run; rw [← run]
                  have h_del : (addAccountToDelete ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal) sevm.currentTarget).getCode adr = ((res3.addBal res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).emitTransferLog sevm.currentTarget res1.1 (((if res1.1 ∉ res1.2.accessedAddresses then addAccessedAddress res1.2 res1.1 else res1.2)).getAcct sevm.currentTarget).bal).getCode adr := by
                    rfl
                  exact ⟨h_del.trans (h_emit.trans (h_add.trans (h_sub.trans ((chargeStateGas_getCode_eq hstg adr).trans ((chargeGas_getCode_eq hchg adr).trans (h_wb.trans (Devm.popToAdr_getCode_eq h1 adr))))))), h_emit_ca.trans ((Devm.subBal_createdAccounts_eq h4).trans ((chargeStateGas_createdAccounts_eq hstg).trans ((chargeGas_createdAccounts_eq hchg).trans (h_wb_ca.trans (Devm.popToAdr_createdAccounts_eq h1)))))⟩
                · simp only [h_if, ite_false]
                  intro run; rw [← run]
                  exact ⟨h_emit.trans (h_add.trans (h_sub.trans ((chargeStateGas_getCode_eq hstg adr).trans ((chargeGas_getCode_eq hchg adr).trans (h_wb.trans (Devm.popToAdr_getCode_eq h1 adr)))))), h_emit_ca.trans ((Devm.subBal_createdAccounts_eq h4).trans ((chargeStateGas_createdAccounts_eq hstg).trans ((chargeGas_createdAccounts_eq hchg).trans (h_wb_ca.trans (Devm.popToAdr_createdAccounts_eq h1)))))⟩

lemma Linst.selfdestruct_preserves_getCode {sevm : Sevm} {devm : Devm} {exn : Execution}
    (run : Linst.Run sevm devm .selfdestruct exn) :
    ∀ adr : Adr, Execution.getCode exn adr = devm.getCode adr := by
  intro adr
  exact (Linst.selfdestruct_preserves_code_created run adr).1

/-- Pointwise equality of code maps: the frame every non-create step keeps. -/
def Devm.CodeFrame (before after : Devm) : Prop :=
  ∀ a : Adr, after.getCode a = before.getCode a

theorem Linst.run_code_created {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution} (run : Linst.Run sevm devm l exn) :
    ∀ a : Adr, Execution.getCode exn a = devm.getCode a ∧
      Execution.createdAccounts exn = devm.createdAccounts := by
  rcases eq_or_ne l .selfdestruct with rfl | h_not_selfdestruct
  · exact Linst.selfdestruct_preserves_code_created run
  · have hf := Linst.run_instructionFrame sevm devm l h_not_selfdestruct
    rw [run] at hf
    cases exn <;> exact fun a => ⟨(hf.getCode a).symm, hf.createdAccounts.symm⟩

theorem Linst.run_codeFrame {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution} (run : Linst.Run sevm devm l exn) :
    Execution.Rel Devm.CodeFrame devm exn := by
  cases exn <;> exact fun a => (Linst.run_code_created run a).1

/-- Relational invariant carried by a filled recursive execution slot. -/
def Xlot.Rel (R : Devm → Devm → Prop) : Xlot → Prop
  | .none => True
  | .some ⟨evm, out⟩ => Execution.Rel R evm.dyna out

/-- Canonical outcome-aware effect of a regular instruction. -/
def Rinst.Effect (R : Devm → Devm → Prop) (r : Rinst) : Prop :=
  ∀ {pc sevm pre out},
    Rinst.run ⟨pc, sevm, pre⟩ r = out → Execution.Rel R pre out

/-- Canonical outcome-aware effect of a jump instruction. -/
def Jinst.Effect (R : Devm → Devm → Prop) (j : Jinst) : Prop :=
  ∀ {evm out},
    Jinst.Run evm j out →
      Outcome.Rel Prod.snd Prod.snd R evm.dyna out

/-- Canonical outcome-aware effect of a terminal instruction. -/
def Linst.Effect (R : Devm → Devm → Prop) (l : Linst) : Prop :=
  ∀ {sevm pre out},
    Linst.Run sevm pre l out → Execution.Rel R pre out

/-- Recursive-execution effect, parameterized by the relation on its child slot. -/
def Xinst.EffectRec (R : Devm → Devm → Prop) (x : Xinst) : Prop :=
  ∀ {sevm pre xl out},
    Xlot.Rel R xl → Xinst.Run sevm pre x xl out → Execution.Rel R pre out

/-- Nonterminal effect consumed by the mutual `Exec.effect` traversal. -/
def Ninst.EffectRec (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {pc sevm pre xl out},
    Xlot.Rel R xl → Ninst.StepRun pc sevm pre n xl out → Execution.Rel R pre out

/-- Successful-run relational projection used by `Func.effect`. -/
def Ninst.Effect (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {sevm pre post}, Ninst.Run sevm pre n post → R pre post

lemma Ninst.effectRec_reg {R : Devm → Devm → Prop} {r : Rinst}
    (hr : Rinst.Effect R r) : Ninst.EffectRec R (.reg r) := by
  intro pc sevm pre xl out hxl hrun
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hrun
  obtain ⟨-, rfl⟩ := hrun
  exact hr rfl

lemma Ninst.effectRec_exec {R : Devm → Devm → Prop} {x : Xinst}
    (hx : Xinst.EffectRec R x) : Ninst.EffectRec R (.exec x) := by
  intro pc sevm pre xl out hxl hrun
  simp only [Ninst.StepRun, Ninst.step_exec] at hrun
  exact hx hxl (XStep.run_toStep.mp hrun)

/-- One step of the driver, related through whichever instruction the program
counter decodes to.  With the interpreter flattened this is the single place
where the four decode branches are enumerated; `Exec.effect` below then only
has to compose steps. -/
lemma Evm.step_effect {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {devm : Devm} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel R xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl out) :
    Execution.Rel R devm out := by
  rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
  · rw [Evm.step_invOp hgi] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact hrefl _
  · cases i with
    | next n =>
      rw [Evm.step_next (n := n) hgi] at hrun
      exact hn n hxl hrun
    | jump j =>
      rw [Evm.step_jump (j := j) hgi] at hrun
      obtain ⟨-, hcase⟩ := Step.run_ofJump hrun
      have hjr := hj j (evm := ⟨pc, sevm, devm⟩) (out := j.run ⟨pc, sevm, devm⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;> rw [hje] at hjr <;>
        exact hjr
    | last l =>
      rw [Evm.step_last (l := l) hgi] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact hl l rfl

/-- The load-bearing traversal: per-instruction canonical effects compose into
`Execution.Rel` for a complete `Exec` derivation.  Where the old proof had one
case per mutual-block constructor, it now has one per driver outcome. -/
theorem Exec.effect {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Execution.Rel R pre out := by
  have hcomp : ∀ {a b : Devm} {o : Execution},
      R a b → Execution.Rel R b o → Execution.Rel R a o := by
    intro a b o hab hbo
    cases o <;> exact htrans hab hbo
  induction run with
  | halt hstep =>
    exact Evm.step_effect hrefl hn hj hl (xl := .none) trivial
      (by rw [hstep]; exact ⟨rfl, rfl⟩)
  | cont hstep _ ih =>
    refine hcomp (?_ : R _ _) ih
    exact Evm.step_effect hrefl hn hj hl (xl := .none) (out := .ok _) trivial
      (by rw [hstep]; exact ⟨rfl, rfl⟩)
  | doneErr hstep henter hr =>
    exact Evm.step_effect hrefl hn hj hl (xl := .none) trivial
      (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
  | doneOk hstep henter hr _ ih =>
    refine hcomp (?_ : R _ _) ih
    exact Evm.step_effect hrefl hn hj hl (xl := .none) (out := .ok _) trivial
      (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
  | runErr hstep henter _ hr ihc =>
    exact Evm.step_effect hrefl hn hj hl (xl := .some ⟨_, _⟩) ihc
      (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
  | runOk hstep henter _ hr _ ihc ih =>
    refine hcomp (?_ : R _ _) ih
    exact Evm.step_effect hrefl hn hj hl (xl := .some ⟨_, _⟩) (out := .ok _) ihc
      (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)

/-- Fork-indexed nonterminal effect: `Ninst.EffectRec` with the covered-fork
premise for the frame. Consumed by `Exec.effectFork`. -/
def Ninst.EffectRecFork (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {pc sevm pre xl out}, CoveredFork sevm.benvStat.fork → Xlot.Rel R xl →
    Ninst.StepRun pc sevm pre n xl out → Execution.Rel R pre out

/-- Terminal effect restricted to a frame whose fork is covered. -/
def Linst.EffectFork (R : Devm → Devm → Prop) (l : Linst) : Prop :=
  ∀ {sevm pre out}, CoveredFork sevm.benvStat.fork →
    Linst.Run sevm pre l out → Execution.Rel R pre out

lemma Evm.step_effectForkTerminal {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R)
    (hn : ∀ n, Ninst.EffectRecFork R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.EffectFork R l)
    {pc : Nat} {sevm : Sevm} {devm : Devm} {xl : Xlot} {out : Execution}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hxl : Xlot.Rel R xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl out) :
    Execution.Rel R devm out := by
  rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
  · rw [Evm.step_invOp hgi] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact hrefl _
  · cases i with
    | next n =>
      rw [Evm.step_next (n := n) hgi] at hrun
      exact hn n hfork hxl hrun
    | jump j =>
      rw [Evm.step_jump (j := j) hgi] at hrun
      obtain ⟨-, hcase⟩ := Step.run_ofJump hrun
      have hjr := hj j (evm := ⟨pc, sevm, devm⟩) (out := j.run ⟨pc, sevm, devm⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;> rw [hje] at hjr <;>
        exact hjr
    | last l =>
      rw [Evm.step_last (l := l) hgi] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact hl l hfork rfl

/-- The fork-indexed traversal: `Exec.effect` where the per-instruction
`Ninst` effect may assume the frame's fork is covered. Child-frame coverage
is transported across each spawn by `Evm.step_spawn_child_fork`; tails keep
the same frame. -/
theorem Exec.effectForkTerminal {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRecFork R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.EffectFork R l)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hfork : CoveredFork sevm.benvStat.fork) :
    Execution.Rel R pre out := by
  have hcomp : ∀ {a b : Devm} {o : Execution},
      R a b → Execution.Rel R b o → Execution.Rel R a o := by
    intro a b o hab hbo
    cases o <;> exact htrans hab hbo
  have aux : ∀ {pc sevm pre out}, Exec pc sevm pre out →
      CoveredFork sevm.benvStat.fork → Execution.Rel R pre out := by
    intro pc sevm pre out run hfork
    revert hfork
    induction run with
    | halt hstep =>
      intro hfork
      exact Evm.step_effectForkTerminal hrefl hn hj hl hfork (xl := .none) trivial
        (by rw [hstep]; exact ⟨rfl, rfl⟩)
    | cont hstep _ ih =>
      intro hfork
      refine hcomp (?_ : R _ _) (ih hfork)
      exact Evm.step_effectForkTerminal hrefl hn hj hl hfork (xl := .none) (out := .ok _) trivial
        (by rw [hstep]; exact ⟨rfl, rfl⟩)
    | doneErr hstep henter hr =>
      intro hfork
      exact Evm.step_effectForkTerminal hrefl hn hj hl hfork (xl := .none) trivial
        (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
    | doneOk hstep henter hr _ ih =>
      intro hfork
      refine hcomp (?_ : R _ _) (ih hfork)
      exact Evm.step_effectForkTerminal hrefl hn hj hl hfork (xl := .none) (out := .ok _) trivial
        (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
    | runErr hstep henter _ hr ihc =>
      intro hfork
      have hfork_c := Evm.step_spawn_child_fork hstep henter hfork
      exact Evm.step_effectForkTerminal hrefl hn hj hl hfork (xl := .some ⟨_, _⟩) (ihc hfork_c)
        (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
    | runOk hstep henter _ hr _ ihc ih =>
      intro hfork
      have hfork_c := Evm.step_spawn_child_fork hstep henter hfork
      refine hcomp (?_ : R _ _) (ih hfork)
      exact Evm.step_effectForkTerminal hrefl hn hj hl hfork (xl := .some ⟨_, _⟩) (out := .ok _) (ihc hfork_c)
        (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
  exact aux run hfork

lemma Evm.step_effectFork {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R)
    (hn : ∀ n, Ninst.EffectRecFork R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {devm : Devm} {xl : Xlot} {out : Execution}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hxl : Xlot.Rel R xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl out) :
    Execution.Rel R devm out := by
  apply Evm.step_effectForkTerminal hrefl hn hj ?_ hfork hxl hrun
  intro l sevm pre out _ run
  exact hl l run

/-- The fork-indexed traversal: `Exec.effect` where the per-instruction
`Ninst` effect may assume the frame's fork is covered. Child-frame coverage
is transported across each spawn by `Evm.step_spawn_child_fork`; tails keep
the same frame. -/
theorem Exec.effectFork {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRecFork R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hfork : CoveredFork sevm.benvStat.fork) :
    Execution.Rel R pre out := by
  apply Exec.effectForkTerminal hrefl htrans hn hj ?_ run hfork
  intro l sevm pre out _ run
  exact hl l run

lemma Xlot.rel_of_filled {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {xl : Xlot} (hfilled : xl.Filled) : Xlot.Rel R xl := by
  cases xl with
  | none => trivial
  | some slot =>
    rcases slot with ⟨evm, out⟩
    rcases hfilled with ⟨hrun⟩
    exact Exec.effect hrefl htrans hn hj hl hrun

lemma Ninst.effect_of_effectRec {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l) :
    ∀ n, Ninst.Effect R n := by
  intro n sevm pre post hrun
  rcases hrun with ⟨xl, hfilled, pc, hrun'⟩
  have hrel := Xlot.rel_of_filled hrefl htrans hn hj hl hfilled
  exact hn n hrel hrun'

theorem Func.effect {R : Devm → Devm → Prop}
    (htrans : TransitiveRel R)
    (hpop : ∀ xs pre post, Devm.PopBurn xs pre post → R pre post)
    (hburn : ∀ pre post, Devm.Burn pre post → R pre post)
    (hn : ∀ n, Ninst.Effect R n)
    (hl : ∀ l, Linst.Effect R l)
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : R pre post := by
  induction run with
  | zero pop run' ih =>
    exact htrans (hpop _ _ _ pop) ih
  | succ neq pop burn run' ih =>
    exact htrans (hpop _ _ _ pop) (htrans (hburn _ _ burn) ih)
  | last run' =>
    exact hl _ run'
  | next runi run' ih =>
    exact htrans (hn _ runi) ih
  | call eq burn run' ih =>
    exact htrans (hburn _ _ burn) ih

-- Relational form of code preservation: nonempty code is never modified.
def Devm.CodePreserve (pre post : Devm) : Prop :=
  ∀ a : Adr, (pre.getCode a).toList ≠ [] → post.getCode a = pre.getCode a

/-- Code preservation, optionally carrying exclusion from the created set. -/
def Devm.AccountPreserve (track : Bool) (pre post : Devm) : Prop :=
  ∀ a : Adr, (pre.getCode a).toList ≠ [] →
    post.getCode a = pre.getCode a ∧
      (track = true → a ∉ pre.createdAccounts → a ∉ post.createdAccounts)

lemma accountPreserve_refl_trans (track : Bool) :
    ReflexiveRel (Devm.AccountPreserve track) ∧ TransitiveRel (Devm.AccountPreserve track) := by
  constructor
  · intro pre a _
    exact ⟨rfl, fun _ fresh => fresh⟩
  · intro pre mid post first second a code
    have hfirst := first a code
    have hmid : (mid.getCode a).toList ≠ [] := by rw [hfirst.1]; exact code
    have hsecond := second a hmid
    exact ⟨hsecond.1.trans hfirst.1, fun enabled fresh =>
      hsecond.2 enabled (hfirst.2 enabled fresh)⟩

lemma Devm.InstructionFrame.accountPreserve {track : Bool} {pre post : Devm}
    (frame : Devm.InstructionFrame pre post) : Devm.AccountPreserve track pre post := by
  intro a _
  exact ⟨(frame.getCode a).symm, by rw [frame.createdAccounts]; exact fun _ fresh => fresh⟩

lemma Execution.accountPreserve_code {pre : Devm} {out : Execution}
    (h : Execution.Rel (Devm.AccountPreserve false) pre out) :
    Execution.Rel Devm.CodePreserve pre out := by
  cases out <;> exact fun a code => (h a code).1

lemma Xlot.accountPreserve_false_of_rel {xl : Xlot}
    (h : Xlot.Rel Devm.CodePreserve xl) : Xlot.Rel (Devm.AccountPreserve false) xl := by
  cases xl with
  | none => trivial
  | some slot =>
    rcases slot with ⟨evm, out⟩
    cases out <;> exact fun a code => ⟨h a code, by intro impossible; cases impossible⟩

lemma Xlot.invAccountPreserve_of_rel {track : Bool} {xl : Xlot}
    (h : Xlot.Rel (Devm.AccountPreserve track) xl) : Xlot.InvAccountPreserve track xl := by
  cases xl with
  | none => trivial
  | some slot =>
    rcases slot with ⟨evm, out⟩
    cases out <;> exact h

lemma codePreserve_refl_trans :
    ReflexiveRel Devm.CodePreserve ∧ TransitiveRel Devm.CodePreserve := by
  constructor
  · intro d a _; rfl
  · intro a b c hab hbc adr ha
    have h1 := hab adr ha
    have h2 : (b.getCode adr).toList ≠ [] := by rw [h1]; exact ha
    exact (hbc adr h2).trans h1

lemma Xlot.invGetCode_of_rel {xl : Xlot}
    (h : Xlot.Rel Devm.CodePreserve xl) : (Blanc.Xlot.InvGetCode xl) := by
  rcases xl with _ | ⟨evm, exn⟩
  · trivial
  · intro a ha
    cases exn with
    | error e => exact (h a ha).symm
    | ok d => exact (h a ha).symm

/-- Reverse bridge: the observation invariant `InvGetCode` implies the
relational `Xlot.Rel Devm.CodePreserve`.  Together with
`Xlot.invGetCode_of_rel` this makes the two forms interchangeable, so the
legacy `Xinst.preserves_getCode_gen` can project through the relational master. -/
lemma Xlot.rel_of_invGetCode {xl : Xlot}
    (h : (Blanc.Xlot.InvGetCode xl)) : Xlot.Rel Devm.CodePreserve xl := by
  rcases xl with _ | ⟨evm, exn⟩
  · trivial
  · cases exn with
    | error e => exact fun a ha => (h a ha).symm
    | ok d => exact fun a ha => (h a ha).symm

lemma Rinst.accountPreserve_effect (track : Bool) (r : Rinst) :
    Rinst.Effect (Devm.AccountPreserve track) r := by
  intro pc sevm pre out run
  have result := Rinst.run_code_created run
  cases out <;> exact fun a _ => ⟨(result a).1, fun _ fresh => (congrArg (fun created => a ∉ created) (result a).2).mpr fresh⟩

lemma Rinst.codePreserve_effect (r : Rinst) :
    Rinst.Effect Devm.CodePreserve r := by
  intro pc sevm pre out run
  exact Execution.accountPreserve_code (Rinst.accountPreserve_effect false r run)

/-- Canonical relational code-preservation master for `Xinst`.  This carries the
full per-constructor case analysis, composing the world-silent primitive frames
(pops, gas, memory, access bookkeeping) with the Step 7.3 generic-operation
masters `GenericCall.codePreserve` / `GenericCreate.codePreserve`.  The legacy
observation theorem `Xinst.preserves_getCode_gen` is a projection of this master via
the `Xlot.InvGetCode` / `Xlot.Rel Devm.CodePreserve` bridge. -/
lemma Xinst.accountPreserve_effectRec (track : Bool) (x : Xinst) :
    Xinst.EffectRec (Devm.AccountPreserve track) x := by
  intro sevm devm xl exn hxl run
  have inv := Xlot.invAccountPreserve_of_rel hxl
  have lift : ∀ {d : Devm}, Devm.InstructionFrame devm d →
      Execution.AccountPreserve track d exn →
      Execution.Rel (Devm.AccountPreserve track) devm exn := by
    intro d hf h
    have key : ∀ a : Adr, (devm.getCode a).toList ≠ [] →
        Execution.getCode exn a = devm.getCode a ∧
          (track = true → a ∉ devm.createdAccounts → a ∉ Execution.createdAccounts exn) := by
      intro a ha
      rw [hf.getCode a] at ha ⊢
      rw [hf.createdAccounts]
      exact h a ha
    cases exn with
    | error e => exact fun a ha => key a ha
    | ok d' => exact fun a ha => key a ha
  unfold Xinst.Run at run
  rcases Xinst.step_shape sevm devm x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ |
    ⟨d, st, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, st, g, r, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      nac, ib, hf, -, -, -, hs⟩ <;>
    rw [hs] at run
  -- the whole step stayed inside the instruction frame
  · obtain ⟨-, rfl⟩ := run
    exact Outcome.Rel.mono (fun _ _ hfr => hfr.accountPreserve) hframe
  -- dispatched to the CREATE family
  · exact lift hf (GenericCreate.accountPreserve inv run)
  -- dispatched to the CALL family
  · exact lift hf (GenericCall.accountPreserve inv run)
  -- dispatched to the Amsterdam CREATE family
  · exact lift hf (GenericCreateAmsterdam.accountPreserve inv run)
  -- dispatched to the Amsterdam CALL family
  · exact lift hf (GenericCallAmsterdam.accountPreserve inv run)

lemma Xinst.codePreserve_effectRec (x : Xinst) :
    Xinst.EffectRec Devm.CodePreserve x := by
  intro sevm devm xl exn hxl run
  exact Execution.accountPreserve_code
    (Xinst.accountPreserve_effectRec false x (Xlot.accountPreserve_false_of_rel hxl) run)

lemma Ninst.push_instructionFrame_effectRec
    {xs : Bytes} {hxs : xs.length ≤ 32} :
    Ninst.EffectRec Devm.InstructionFrame (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  simp only [Ninst.StepRun, Ninst.step_push] at hRun
  split at hRun
  · simp only [Step.run_ofExecution] at hRun
    obtain ⟨-, rfl⟩ := hRun
    exact Devm.instructionFrame_refl pre
  · simp only [Step.run_ofExecution] at hRun
    obtain ⟨-, rfl⟩ := hRun
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame (if xs = [] then gBase else gVerylow) pre)
    exact Devm.push_instructionFrame xs.toB256

lemma Ninst.push_effectRec_of_instructionFrame
    {R : Devm → Devm → Prop} {xs : Bytes} {hxs : xs.length ≤ 32}
    (hIR : ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → R d d') :
    Ninst.EffectRec R (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  have h0 : xl = .none := by
    simp only [Ninst.StepRun, Ninst.step_push] at hRun
    split at hRun <;> simp only [Step.run_ofExecution] at hRun <;> exact hRun.1
  subst h0
  exact Outcome.Rel.mono hIR
    (Ninst.push_instructionFrame_effectRec (hxs := hxs) (xl := .none)
      trivial hRun)

lemma Ninst.push_codePreserve_effectRec {xs : Bytes} {hxs : xs.length ≤ 32} :
  Ninst.EffectRec Devm.CodePreserve (.push xs hxs) := by
  exact Ninst.push_effectRec_of_instructionFrame (R := Devm.CodePreserve)
    (fun _ _ hf a _ => (hf.getCode a).symm)

lemma Devm.withStack_instructionFrame (d : Devm) (stack : List B256) :
    Devm.InstructionFrame d (d.withStack stack) := by
  unfold Devm.withStack
  exact Devm.machFrame_refines_instructionFrame (Devm.machFrame_setMach d _)

lemma Ninst.dupn_instructionFrame_effectRec {imm : UInt8} :
    Ninst.EffectRec Devm.InstructionFrame (.dupn imm) := by
  intro pc sevm pre xl out hxl hRun
  simp only [Ninst.StepRun, Ninst.step_dupn, Step.run_ofExecution] at hRun
  obtain ⟨-, rfl⟩ := hRun
  split
  · refine Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame _ _) fun devm => ?_
    split
    · exact Devm.instructionFrame_refl devm
    · rename_i n
      split
      · exact Devm.instructionFrame_refl devm
      · exact Devm.push_instructionFrame _ _
  · exact Devm.instructionFrame_refl pre

lemma Ninst.swapn_instructionFrame_effectRec {imm : UInt8} :
    Ninst.EffectRec Devm.InstructionFrame (.swapn imm) := by
  intro pc sevm pre xl out hxl hRun
  simp only [Ninst.StepRun, Ninst.step_swapn, Step.run_ofExecution] at hRun
  obtain ⟨-, rfl⟩ := hRun
  split
  · refine Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame _ _) fun devm => ?_
    split
    · exact Devm.instructionFrame_refl devm
    · rename_i n
      split
      · exact Devm.instructionFrame_refl devm
      · exact Devm.withStack_instructionFrame _ _
  · exact Devm.instructionFrame_refl pre

lemma Ninst.exchange_instructionFrame_effectRec {imm : UInt8} :
    Ninst.EffectRec Devm.InstructionFrame (.exchange imm) := by
  intro pc sevm pre xl out hxl hRun
  simp only [Ninst.StepRun, Ninst.step_exchange, Step.run_ofExecution] at hRun
  obtain ⟨-, rfl⟩ := hRun
  split
  · refine Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame _ _) fun devm => ?_
    split
    · exact Devm.instructionFrame_refl devm
    · rename_i nm
      split
      · exact Devm.instructionFrame_refl devm
      · exact Devm.withStack_instructionFrame _ _
  · exact Devm.instructionFrame_refl pre

lemma Ninst.dupn_effectRec_of_instructionFrame
    {R : Devm → Devm → Prop} {imm : UInt8}
    (hIR : ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → R d d') :
    Ninst.EffectRec R (.dupn imm) := by
  intro pc sevm pre xl out hxl hRun
  have h0 : xl = .none := by
    simp only [Ninst.StepRun, Ninst.step_dupn, Step.run_ofExecution] at hRun
    exact hRun.1
  subst h0
  exact Outcome.Rel.mono hIR
    (Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial hRun)

lemma Ninst.swapn_effectRec_of_instructionFrame
    {R : Devm → Devm → Prop} {imm : UInt8}
    (hIR : ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → R d d') :
    Ninst.EffectRec R (.swapn imm) := by
  intro pc sevm pre xl out hxl hRun
  have h0 : xl = .none := by
    simp only [Ninst.StepRun, Ninst.step_swapn, Step.run_ofExecution] at hRun
    exact hRun.1
  subst h0
  exact Outcome.Rel.mono hIR
    (Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial hRun)

lemma Ninst.exchange_effectRec_of_instructionFrame
    {R : Devm → Devm → Prop} {imm : UInt8}
    (hIR : ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → R d d') :
    Ninst.EffectRec R (.exchange imm) := by
  intro pc sevm pre xl out hxl hRun
  have h0 : xl = .none := by
    simp only [Ninst.StepRun, Ninst.step_exchange, Step.run_ofExecution] at hRun
    exact hRun.1
  subst h0
  exact Outcome.Rel.mono hIR
    (Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial hRun)

lemma Ninst.dupn_codePreserve_effectRec {imm : UInt8} :
  Ninst.EffectRec Devm.CodePreserve (.dupn imm) := by
  exact Ninst.dupn_effectRec_of_instructionFrame (R := Devm.CodePreserve)
    (fun _ _ hf a _ => (hf.getCode a).symm)

lemma Ninst.swapn_codePreserve_effectRec {imm : UInt8} :
  Ninst.EffectRec Devm.CodePreserve (.swapn imm) := by
  exact Ninst.swapn_effectRec_of_instructionFrame (R := Devm.CodePreserve)
    (fun _ _ hf a _ => (hf.getCode a).symm)

lemma Ninst.exchange_codePreserve_effectRec {imm : UInt8} :
  Ninst.EffectRec Devm.CodePreserve (.exchange imm) := by
  exact Ninst.exchange_effectRec_of_instructionFrame (R := Devm.CodePreserve)
    (fun _ _ hf a _ => (hf.getCode a).symm)

lemma Ninst.accountPreserve_effectRec (track : Bool) (n : Ninst) :
    Ninst.EffectRec (Devm.AccountPreserve track) n := by
  cases n with
  | reg r => exact Ninst.effectRec_reg (Rinst.accountPreserve_effect track r)
  | exec x => exact Ninst.effectRec_exec (Xinst.accountPreserve_effectRec track x)
  | push xs hxs =>
    exact Ninst.push_effectRec_of_instructionFrame
      (fun _ _ frame => frame.accountPreserve)
  | dupn imm =>
    exact Ninst.dupn_effectRec_of_instructionFrame
      (fun _ _ frame => frame.accountPreserve)
  | swapn imm =>
    exact Ninst.swapn_effectRec_of_instructionFrame
      (fun _ _ frame => frame.accountPreserve)
  | exchange imm =>
    exact Ninst.exchange_effectRec_of_instructionFrame
      (fun _ _ frame => frame.accountPreserve)

lemma Ninst.codePreserve_effectRec (n : Ninst) :
    Ninst.EffectRec Devm.CodePreserve n := by
  intro pc sevm pre xl out hxl run
  exact Execution.accountPreserve_code
    (Ninst.accountPreserve_effectRec false n (Xlot.accountPreserve_false_of_rel hxl) run)

lemma Jinst.accountPreserve_effect (track : Bool) (j : Jinst) :
    Jinst.Effect (Devm.AccountPreserve track) j := by
  intro evm out run
  have frame := Jinst.run_instructionFrame evm j
  rw [run] at frame
  cases out <;> exact frame.accountPreserve

lemma Jinst.codePreserve_effect (j : Jinst) :
    Jinst.Effect Devm.CodePreserve j := by
  intro evm out run
  have result := Jinst.accountPreserve_effect false j run
  cases out <;> exact fun a code => (result a code).1

lemma Linst.accountPreserve_effect (track : Bool) (l : Linst) :
    Linst.Effect (Devm.AccountPreserve track) l := by
  intro sevm pre out run
  have result := Linst.run_code_created run
  cases out <;> exact fun a _ => ⟨(result a).1, fun _ fresh => (congrArg (fun created => a ∉ created) (result a).2).mpr fresh⟩

lemma Linst.codePreserve_effect (l : Linst) :
    Linst.Effect Devm.CodePreserve l := by
  intro sevm pre out run
  exact Execution.accountPreserve_code (Linst.accountPreserve_effect false l run)

lemma Exec.preserves_getCode {pc} {sevm} {devm} {exn}
    (run : Exec pc sevm devm exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      Execution.getCode exn a = devm.getCode a := by
  intro a ha
  have h := Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
    Ninst.codePreserve_effectRec Jinst.codePreserve_effect
    Linst.codePreserve_effect run
  cases exn with
  | error e => exact h a ha
  | ok d => exact h a ha

lemma not_empty_of_compile {p : Prog} {code : ByteArray} (h : some code.toList = Prog.compile p) : code ≠ .empty := by
  intro hc
  have h_ne : Prog.compile p ≠ some [] := Prog.compile_ne_nil
  rw [←h, hc] at h_ne
  have h_empty_toList : ByteArray.empty.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    rfl
  rw [h_empty_toList] at h_ne
  exact h_ne rfl

lemma not_delegation_of_compile {p : Prog} {code : ByteArray}
    (h : some code.toList = Prog.compile p) : ¬ isValidDelegation code := by
  unfold isValidDelegation
  unfold Prog.compile at h
  unfold table at h
  simp only [Table.compile] at h
  simp only [bind] at h
  symm at h
  rcases of_bind_eq_some h with ⟨bs, h_bs, h'⟩
  rcases of_bind_eq_some h' with ⟨bss, h_bss, h_eq⟩
  injection h_eq with h_eq
  intro h_del
  rcases h_del with ⟨h_size, h_slice⟩
  have h_slice_eq : code.sliceD 0 3 0 = code.toList.sliceD 0 3 0 := ByteArray.sliceD_eq _ _ _ _
  rw [h_slice_eq, ←h_eq, eoaDelegationMarker] at h_slice
  revert h_slice
  simp only [List.sliceD]
  intro h_false
  injection h_false with h_false
  change (91 : UInt8) = 239 at h_false
  contradiction

/-- The certified semantics of a compiled Blanc program. -/
def Prog.codeSem (p : Prog) : CodeSem :=
  { image := Prog.compile p
    Run := fun sevm pre post => Prog.Run sevm pre p post
    correct := by
      intro sevm pre post h_run h_code
      exact correct sevm pre p post h_run h_code
    ne_nil := fun h => by
      intro h_nil
      apply Prog.compile_ne_nil (p := p)
      exact h.trans (congrArg some h_nil)
    not_delegation := fun h => not_delegation_of_compile h }

lemma not_empty_of_codeSem {sem : CodeSem} {code : ByteArray}
    (h : some code.toList = sem.image) : code ≠ .empty := by
  intro hc
  have h_ne : sem.image ≠ some [] := by
    intro h_nil
    exact (sem.ne_nil h_nil) rfl
  apply h_ne
  rw [← h, hc]
  have h_empty_toList : ByteArray.empty.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    rfl
  exact congrArg some h_empty_toList

/-- The "we are inside the contract" case, shared by every driver outcome:
either the run failed (nothing to prove) or it completed a program run at
`pc = 0`, which the depth induction turns into the contract-level invariant. -/
private lemma lift_core_sem.atTarget
    {ε : Nat → Sevm → Devm → Execution → Prop} {π : Sevm → Devm → Devm → Prop}
    {ca : Adr} {sem : CodeSem}
    (analog : ∀ {sevm pre post}, π sevm pre post → ε 0 sevm pre (.ok post))
    ( depth_ind :
      ∀ {sevm pre post},
        sem.Run sevm pre post →
        sevm.currentTarget = ca →
        ForallDeeperAtSem sevm.depth ca sem (fun pc s d e _ => ε pc s d e) →
        π sevm pre post )
    ( errAtTarget :
      ∀ {pc sevm devm err devm'},
        sevm.currentTarget = ca → ε pc sevm devm (.error ⟨err, devm'⟩) )
    {pc : Nat} {sevm : Sevm} {devm : Devm} {exn : Execution}
    (ex : Exec pc sevm devm exn)
    (h_fa : ForallDeeperAtSem sevm.depth ca sem (fun pc s d e _ => ε pc s d e))
    (h_at_p : sem.At ca pc sevm devm) (h_eq : sevm.currentTarget = ca)
    : ε pc sevm devm exn := by
  cases exn with
  | error e => exact errAtTarget h_eq
  | ok post =>
    have h_pc : pc = 0 := (h_at_p.right h_eq).right
    subst h_pc
    exact analog
      (depth_ind (sem.correct ex (h_at_p.right h_eq).left) h_eq h_fa)

/-- Code preservation across one driver step, in the form the `CodeSem.At`
bookkeeping needs. -/
lemma lift_core_sem.stepCode {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    {xl : Xlot} (hxl : Xlot.Rel Devm.CodePreserve xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl (.ok devm'))
    (a : Adr) (ha : (devm.getCode a).toList ≠ []) :
    devm'.getCode a = devm.getCode a :=
  Evm.step_effect codePreserve_refl_trans.1 Ninst.codePreserve_effectRec
    Jinst.codePreserve_effect Linst.codePreserve_effect hxl hrun a ha

/-- The eliminator every contract-level invariant proof runs on: strong
induction on frame depth combined with the driver's case analysis, carrying the
program-location bookkeeping (`CodeSem.At`) across steps and across suspensions.
Its handlers stay indexed by *instruction kind*, so the decode dispatch happens
here once and `lift`/`lift_inv` are insulated from the flattening. -/
lemma lift_core_sem
    (ε : Nat → Sevm → Devm → Execution → Prop)
    (π : Sevm → Devm → Devm → Prop)
    (analog : ∀ {sevm pre post}, π sevm pre post → ε 0 sevm pre (.ok post))
    (ca : Adr) (sem : CodeSem)
    ( depth_ind :
      ∀ {sevm pre post},
        sem.Run sevm pre post →
        sevm.currentTarget = ca →
        ForallDeeperAtSem sevm.depth ca sem (fun pc s d e _ => ε pc s d e) →
        π sevm pre post )
    ( errAtTarget :
      ∀ {pc sevm devm err devm'},
        sevm.currentTarget = ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( invOp :
      ∀ {pc sevm devm},
        sevm.code.getInst pc = none →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨.halt (.invalidOpcode .none), devm⟩) )
    ( nextNoneErr :
      ∀ {pc sevm devm n err devm'},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n .none (.error ⟨err, devm'⟩) →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( nextSomeErr :
      ∀ {pc sevm devm n evm_ exn_ err devm'},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n (.some ⟨evm_, exn_⟩) (.error ⟨err, devm'⟩) →
        Exec evm_.pc evm_.sta evm_.dyna exn_ →
        sevm.currentTarget ≠ ca →
        ε evm_.pc evm_.sta evm_.dyna exn_ →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( nextNoneRec :
      ∀ {pc sevm devm n devm' exn},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n .none (.ok devm') →
        Exec (pc + n.size) sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε (pc + n.size) sevm devm' exn →
        ε pc sevm devm exn )
    ( nextSomeRec :
      ∀ {pc sevm devm n evm_ exn_ devm' exn},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n (.some ⟨evm_, exn_⟩) (.ok devm') →
        Exec evm_.pc evm_.sta evm_.dyna exn_ →
        Exec (pc + n.size) sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε evm_.pc evm_.sta evm_.dyna exn_ →
        ε (pc + n.size) sevm devm' exn →
        ε pc sevm devm exn )
    ( jumpErr :
      ∀ {pc sevm devm j err devm'},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩) →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( jumpRec :
      ∀ {pc sevm devm j pc' devm' exn},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩) →
        Exec pc' sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε pc' sevm devm' exn →
        ε pc sevm devm exn )
    ( last :
      ∀ {pc sevm devm l exn},
        Linst.At sevm.code pc l →
        Linst.Run sevm devm l exn →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm exn ) :
    Exec.Fa (Exec.WknSem ca sem (fun pc s d e _ => ε pc s d e)) := by
  apply Exec.strong_rec
  apply @Exec.rec (Fortify (Exec.WknSem ca sem (fun pc s d e _ => ε pc s d e)))
  -- halt
  · intro pc sevm devm ex hstep h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core_sem.atTarget analog depth_ind errAtTarget
        (.halt hstep) h_fa h_at_p h_eq
    · rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
      · rw [Evm.step_invOp hgi] at hstep
        cases hstep
        exact invOp hgi h_ne
      · cases i with
        | next n =>
          have hns : Ninst.step ⟨pc, sevm, devm⟩ n = .halt ex := by
            rw [← Evm.step_next (n := n) hgi]; exact hstep
          have hrun : Ninst.StepRun pc sevm devm n .none ex := by
            unfold Ninst.StepRun; rw [hns]; exact ⟨rfl, rfl⟩
          cases ex with
          | error e => exact nextNoneErr hgi hrun h_ne
          | ok d => exact absurd hns Ninst.step_ne_halt_ok
        | jump j =>
          rw [Evm.step_jump (j := j) hgi] at hstep
          rcases hj : j.run ⟨pc, sevm, devm⟩ with e | ⟨pc', devm'⟩ <;>
            rw [hj] at hstep <;> simp only [Step.ofJump] at hstep
          · cases hstep; exact jumpErr hgi hj h_ne
          · cases hstep
        | last l =>
          rw [Evm.step_last (l := l) hgi] at hstep
          cases hstep
          exact last hgi rfl h_ne
  -- cont
  · intro pc sevm devm pc' devm' exn hstep ex ih h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core_sem.atTarget analog depth_ind errAtTarget
        (.cont hstep ex) h_fa h_at_p h_eq
    · have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc =>
        (sem.ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))) rfl
      have hcode : devm'.getCode ca = devm.getCode ca :=
        lift_core_sem.stepCode (xl := .none) trivial
          (by rw [hstep]; exact ⟨rfl, rfl⟩) ca h_ne_code
      have h_at' : sem.At ca pc' sevm devm' :=
        ⟨by rw [hcode]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
      rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
      · rw [Evm.step_invOp hgi] at hstep; cases hstep
      · cases i with
        | next n =>
          have hns : Ninst.step ⟨pc, sevm, devm⟩ n = .cont pc' devm' := by
            rw [← Evm.step_next (n := n) hgi]; exact hstep
          have hpc : pc' = pc + n.size := Ninst.step_cont_pc hns
          subst hpc
          have hrun : Ninst.StepRun pc sevm devm n .none (.ok devm') := by
            unfold Ninst.StepRun; rw [hns]; exact ⟨rfl, rfl⟩
          exact nextNoneRec hgi hrun ex h_ne (ih h_fa h_at')
        | jump j =>
          rw [Evm.step_jump (j := j) hgi] at hstep
          exact jumpRec hgi (Step.ofJump_cont hstep) ex h_ne (ih h_fa h_at')
        | last l =>
          rw [Evm.step_last (l := l) hgi] at hstep; cases hstep
  -- doneErr
  · intro pc sevm devm f rsm pc' r e hstep henter hr h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core_sem.atTarget analog depth_ind errAtTarget
        (.doneErr hstep henter hr) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, -⟩ := Evm.step_spawn_inv hstep
      have hrun : Ninst.StepRun pc sevm devm (.exec x) .none (.error e) := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨r, RunFrame.of_done henter, hr.symm⟩
      exact nextNoneErr hxat hrun h_ne
  -- doneOk
  · intro pc sevm devm f rsm pc' r devm' exn hstep henter hr ex ih h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core_sem.atTarget analog depth_ind errAtTarget
        (.doneOk hstep henter hr ex) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, hpc'⟩ := Evm.step_spawn_inv hstep
      subst hpc'
      have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc =>
        (sem.ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))) rfl
      have hrun : Ninst.StepRun pc sevm devm (.exec x) .none (.ok devm') := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨r, RunFrame.of_done henter, hr.symm⟩
      have hcode : devm'.getCode ca = devm.getCode ca :=
        lift_core_sem.stepCode (xl := .none) trivial
          (by rw [hstep]; exact ⟨r, RunFrame.of_done henter, hr.symm⟩) ca h_ne_code
      have h_at' : sem.At ca (pc + 1) sevm devm' :=
        ⟨by rw [hcode]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
      exact nextNoneRec hxat hrun ex h_ne (ih h_fa h_at')
  -- runErr
  · intro pc sevm devm f rsm pc' cevm raw e hstep henter child hr ihc h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core_sem.atTarget analog depth_ind errAtTarget
        (.runErr hstep henter child hr) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, -⟩ := Evm.step_spawn_inv hstep
      obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hstep henter
      have hdepth : cevm.sta.depth < sevm.depth := by
        rw [Frame.enter_run_depth henter]; exact Step.spawn_depth_lt hstep
      have h_at_child : sem.At ca cevm.pc cevm.sta cevm.dyna := by
        refine ⟨by rw [hgc ca]; exact h_at_p.left, fun hct => ⟨?_, hpc0⟩⟩
        have hne' : sevm.currentTarget ≠ cevm.sta.currentTarget := by
          rw [hct]; exact h_ne
        have hcode := hsrc hne'
          (by rw [hct]; exact not_empty_of_codeSem h_at_p.left)
          (by rw [hct]; exact sem.not_delegation h_at_p.left)
        rw [hcode, hct]
        exact h_at_p.left
      have hrun :
          Ninst.StepRun pc sevm devm (.exec x) (.some ⟨cevm, raw⟩) (.error e) := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨f.settle raw, RunFrame.of_run henter, hr.symm⟩
      exact nextSomeErr hxat hrun child h_ne
        (h_fa cevm.pc cevm.sta cevm.dyna raw child hdepth h_at_child)
  -- runOk
  · intro pc sevm devm f rsm pc' cevm raw devm' exn hstep henter child hr ex
      ihc ih h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core_sem.atTarget analog depth_ind errAtTarget
        (.runOk hstep henter child hr ex) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, hpc'⟩ := Evm.step_spawn_inv hstep
      subst hpc'
      obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hstep henter
      have hdepth : cevm.sta.depth < sevm.depth := by
        rw [Frame.enter_run_depth henter]; exact Step.spawn_depth_lt hstep
      have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc =>
        (sem.ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))) rfl
      have h_at_child : sem.At ca cevm.pc cevm.sta cevm.dyna := by
        refine ⟨by rw [hgc ca]; exact h_at_p.left, fun hct => ⟨?_, hpc0⟩⟩
        have hne' : sevm.currentTarget ≠ cevm.sta.currentTarget := by
          rw [hct]; exact h_ne
        have hcode := hsrc hne'
          (by rw [hct]; exact not_empty_of_codeSem h_at_p.left)
          (by rw [hct]; exact sem.not_delegation h_at_p.left)
        rw [hcode, hct]
        exact h_at_p.left
      have hchild : Xlot.Rel Devm.CodePreserve (.some ⟨cevm, raw⟩) :=
        Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
          Ninst.codePreserve_effectRec Jinst.codePreserve_effect
          Linst.codePreserve_effect child
      have hrun :
          Ninst.StepRun pc sevm devm (.exec x) (.some ⟨cevm, raw⟩) (.ok devm') := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨f.settle raw, RunFrame.of_run henter, hr.symm⟩
      have hcode : devm'.getCode ca = devm.getCode ca :=
        lift_core_sem.stepCode (xl := .some ⟨cevm, raw⟩) hchild
          (by rw [hstep]; exact ⟨f.settle raw, RunFrame.of_run henter, hr.symm⟩)
          ca h_ne_code
      have h_at' : sem.At ca (pc + 1) sevm devm' :=
        ⟨by rw [hcode]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
      exact nextSomeRec hxat hrun child ex h_ne
        (h_fa cevm.pc cevm.sta cevm.dyna raw child hdepth h_at_child)
        (ih h_fa h_at')

lemma lift_sem
    (R : Sevm → Devm → Devm → Prop)
    (ca : Adr) -- contract address
    (sem : CodeSem)
    ( depth_ind :
      ∀ {sevm pre post},
        sem.Run sevm pre post →
        sevm.currentTarget = ca →
        ForallSubExecSem sevm.depth ca sem R →
        R sevm pre post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n .none (.ok inter) →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {evm'}
        {exn' : Execution} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n
          (.some ⟨evm', exn'⟩)
          (.ok inter) →
        Exec evm'.pc evm'.sta evm'.dyna exn' →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        ifOk (R evm'.sta evm'.dyna) exn' →
        R sevm inter post →
        R sevm pre post )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter} {post},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        Exec pc' sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        Linst.At sevm.code pc l →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm pre post ) :
    ∀ pc sevm pre post,
      Exec pc sevm pre (.ok post) →
      CodeSem.At sem ca pc sevm pre →
      R sevm pre post := by
  intro pc sevm pre post h_exc h_at
  refine lift_core_sem (fun _ sevm pre exn => ifOk (R sevm pre) exn) R (fun h => h) ca sem
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pc sevm pre (.ok post) h_exc h_at
  · intro sevm' pre' post' h_run h_eq h_fa
    apply depth_ind h_run h_eq
    intro pc_ sevm_ devm_ post_ h_exc' h_lt h_at'
    exact h_fa pc_ sevm_ devm_ (.ok post_) h_exc' h_lt h_at'
  · intro pc' sevm' devm' err devm'' h_eq; exact trivial
  · intro pc' sevm' devm' h_get h_ne; exact trivial
  · intro pc' sevm' devm' n err devm'' h_at' h_run h_ne; exact trivial
  · intro pc' sevm' devm' n evm_ exn_ err devm'' h_at' h_run ex_sub h_ne h_ih; exact trivial
  · intro pc' sevm' devm' n devm'' exn h_at' h_run ex h_ne h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact nextNone h_at' h_run ex h_ne h_ih
  · intro pc' sevm' devm' n evm_ exn_ devm'' exn h_at' h_run ex_sub ex h_ne h_ih_sub h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact nextSome h_at' h_run ex_sub ex h_ne h_ih_sub h_ih
  · intro pc' sevm' devm' j err devm'' h_at' h_run h_ne; exact trivial
  · intro pc' sevm' devm' j pc_ devm'' exn h_at' h_run ex h_ne h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact jump h_at' h_run ex h_ne h_ih
  · intro pc' sevm' devm' l exn h_at' h_run h_ne
    cases exn with
    | error e => exact trivial
    | ok post' => exact last h_at' h_run h_ne

lemma lift_inv_sem
    (ca : Adr) (sem : CodeSem)
    (σ : Sevm → Devm → Prop)
    (ρ : Sevm → Devm → Prop)
    ( with_depth_ind :
      ∀ {sevm pre post},
        sem.Run sevm pre post →
        sevm.currentTarget = ca →
        ( ∀ pc' sevm' pre' post',
            Exec pc' sevm' pre' (.ok post') →
            sevm'.depth < sevm.depth →
            CodeSem.At sem ca pc' sevm' pre' →
            σ sevm' pre' →
            ρ sevm' post' ) →
        σ sevm pre →
        ρ sevm post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n .none (.ok inter) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {evm'} {exn'} {inter},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n (.some ⟨evm', exn'⟩) (.ok inter) →
        Exec evm'.pc evm'.sta evm'.dyna exn' →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ evm'.sta evm'.dyna ∧ (ifOk (ρ evm'.sta) exn' → σ sevm inter) )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        Linst.At sevm.code pc l →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        ρ sevm post ) :
    ∀ pc sevm devm post,
      Exec pc sevm devm (.ok post) →
      CodeSem.At sem ca pc sevm devm →
      σ sevm devm →
      ρ sevm post := by
  apply @Blanc.lift_sem (fun sevm pre post => σ sevm pre → ρ sevm post) ca sem with_depth_ind
  · intro pc sevm pre n inter post h_at h_run _ h_ne h_ih h_pi
    exact h_ih (nextNone h_at h_run h_ne h_pi)
  · intro pc sevm pre n evm' exn' inter post h_at h_run ex_sub _ h_ne h_ifOk h_ih h_pi
    rcases nextSome h_at h_run ex_sub h_ne h_pi with ⟨h_pi_sub, h_imp⟩
    apply h_ih; apply h_imp
    cases exn' with
    | error e => exact trivial
    | ok post' => exact h_ifOk h_pi_sub
  · intro pc sevm pre j pc' inter post h_at h_run _ h_ne h_ih h_pi
    exact h_ih (jump h_at h_run h_ne h_pi)
  · intro pc sevm pre l post h_at h_run h_ne h_pi
    exact last h_at h_run h_ne h_pi

/-- Code preservation across one driver step, in the form the `Prog.At`
bookkeeping needs. -/
lemma lift_core.stepCode {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    {xl : Xlot} (hxl : Xlot.Rel Devm.CodePreserve xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl (.ok devm'))
    (a : Adr) (ha : (devm.getCode a).toList ≠ []) :
    devm'.getCode a = devm.getCode a := lift_core_sem.stepCode hxl hrun a ha

/-- The eliminator every contract-level invariant proof runs on: strong
induction on frame depth combined with the driver's case analysis, carrying the
program-location bookkeeping (`Prog.At`) across steps and across suspensions.
Its handlers stay indexed by *instruction kind*, so the decode dispatch happens
here once and `lift`/`lift_inv` are insulated from the flattening. -/
lemma lift_core
    (ε : Nat → Sevm → Devm → Execution → Prop)
    (π : Sevm → Devm → Devm → Prop)
    (analog : ∀ {sevm pre post}, π sevm pre post → ε 0 sevm pre (.ok post))
    (ca : Adr) (p : Prog)
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallDeeperAt sevm.depth ca p (fun pc s d e _ => ε pc s d e) →
        π sevm pre post )
    ( errAtTarget :
      ∀ {pc sevm devm err devm'},
        sevm.currentTarget = ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( invOp :
      ∀ {pc sevm devm},
        sevm.code.getInst pc = none →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨.halt (.invalidOpcode .none), devm⟩) )
    ( nextNoneErr :
      ∀ {pc sevm devm n err devm'},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n .none (.error ⟨err, devm'⟩) →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( nextSomeErr :
      ∀ {pc sevm devm n evm_ exn_ err devm'},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n (.some ⟨evm_, exn_⟩) (.error ⟨err, devm'⟩) →
        Exec evm_.pc evm_.sta evm_.dyna exn_ →
        sevm.currentTarget ≠ ca →
        ε evm_.pc evm_.sta evm_.dyna exn_ →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( nextNoneRec :
      ∀ {pc sevm devm n devm' exn},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n .none (.ok devm') →
        Exec (pc + n.size) sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε (pc + n.size) sevm devm' exn →
        ε pc sevm devm exn )
    ( nextSomeRec :
      ∀ {pc sevm devm n evm_ exn_ devm' exn},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n (.some ⟨evm_, exn_⟩) (.ok devm') →
        Exec evm_.pc evm_.sta evm_.dyna exn_ →
        Exec (pc + n.size) sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε evm_.pc evm_.sta evm_.dyna exn_ →
        ε (pc + n.size) sevm devm' exn →
        ε pc sevm devm exn )
    ( jumpErr :
      ∀ {pc sevm devm j err devm'},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩) →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( jumpRec :
      ∀ {pc sevm devm j pc' devm' exn},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩) →
        Exec pc' sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε pc' sevm devm' exn →
        ε pc sevm devm exn )
    ( last :
      ∀ {pc sevm devm l exn},
        Linst.At sevm.code pc l →
        Linst.Run sevm devm l exn →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm exn ) :
    Exec.Fa (Exec.Wkn ca p (fun pc s d e _ => ε pc s d e)) := by
  change Exec.Fa (Exec.WknSem ca p.codeSem (fun pc s d e _ => ε pc s d e))
  exact lift_core_sem ε π analog ca p.codeSem depth_ind errAtTarget invOp
    nextNoneErr nextSomeErr nextNoneRec nextSomeRec jumpErr jumpRec last


lemma lift
    (R : Sevm → Devm → Devm → Prop)
    (ca : Adr) -- contract address
    (p : Prog)
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallSubExec sevm.depth ca p R →
        R sevm pre post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n .none (.ok inter) →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {evm'}
        {exn' : Execution} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n
          (.some ⟨evm', exn'⟩)
          (.ok inter) →
        Exec evm'.pc evm'.sta evm'.dyna exn' →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        ifOk (R evm'.sta evm'.dyna) exn' →
        R sevm inter post →
        R sevm pre post )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter} {post},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        Exec pc' sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        Linst.At sevm.code pc l →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm pre post ) :
    ∀ pc sevm pre post,
      Exec pc sevm pre (.ok post) →
      Prog.At p ca pc sevm pre →
      R sevm pre post := by
  simpa only [Prog.At, and_imp, CodeSem.At, Prog.codeSem] using
    (lift_sem R ca p.codeSem depth_ind nextNone nextSome jump last)

end Blanc
