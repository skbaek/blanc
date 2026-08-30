import Blanc.Semantics

/-!
# From raw code execution to settled message results

Contract-neutral adapters between `exec (initEvm msg)` and top-level
`processMessage msg`, including canonical settled machines for REVERT and
exceptional-halt outcomes.
-/

namespace Blanc

open Jaune

namespace MessageExecution

/-- A message with an ordinary code address enters the interpreter whenever
that address is not a precompile.  This covers normal transaction messages
with `disablePrecompiles = false`; the flag is deliberately not a premise. -/
theorem executeCode_enter_of_codeAddress_not_precompile
    (msg : Msg) (benv : Benv) (codeAddress : Adr)
    (hcodeAddress : msg.codeAddress = some codeAddress)
    (hnotPrecompile :
      decide (benv.stat.rules.isPrecomp codeAddress) = false) :
    executeCode.enter (msg.withBenv benv) =
      .inl (initEvm (msg.withBenv benv)) := by
  unfold executeCode.enter
  simp only [Msg.withBenv, hcodeAddress, hnotPrecompile, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

/-- After successful value transfer, an exact interpreter-entry equation is
enough to expose `processMessage` as settlement of the raw execution from the
actual post-transfer environment. -/
theorem processMessage_eq_settle_exec_afterTransfer_of_codeEntry
    (msg : Msg) (benv : Benv)
    (hentry : msg.benvAfterTransfer = .ok benv)
    (hcodeEntry : executeCode.enter (msg.withBenv benv) =
      .inl (initEvm (msg.withBenv benv))) :
    processMessage msg =
      (Frame.ofCall msg).settle
        (exec (initEvm (msg.withBenv benv))) := by
  have henter :
      (Frame.ofCall msg).enter =
        .run (initEvm (msg.withBenv benv)) := by
    unfold Frame.enter Frame.ofCall
    rw [hentry]
    simp only
    rw [hcodeEntry]
  unfold processMessage runFrame
  rw [henter]

/-- After a successful value-transfer entry, a message with precompiles
disabled is the call frame's settlement of the raw execution from the actual
post-transfer environment.  Unlike `processMessage_eq_settle_exec`, this form
does not identify the post-transfer environment with the message's pre-state,
so it is suitable for payable calls. -/
theorem processMessage_eq_settle_exec_afterTransfer
    (msg : Msg) (benv : Benv)
    (hentry : msg.benvAfterTransfer = .ok benv)
    (hdisable : msg.disablePrecompiles = true) :
    processMessage msg =
      (Frame.ofCall msg).settle
        (exec (initEvm (msg.withBenv benv))) := by
  have henter :
      (Frame.ofCall msg).enter =
        .run (initEvm (msg.withBenv benv)) := by
    unfold Frame.enter Frame.ofCall
    rw [hentry]
    simp only
    unfold executeCode.enter
    have hdisable' :
        (msg.withBenv benv).disablePrecompiles = true := by
      simpa [Msg.withBenv] using hdisable
    rw [hdisable']
    cases (msg.withBenv benv).codeAddress <;> rfl
  unfold processMessage runFrame
  rw [henter]

/-- Under the ordinary entry identity with precompiles disabled,
`processMessage` is the call frame's settlement of the raw code execution. -/
theorem processMessage_eq_settle_exec
    (msg : Msg)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true) :
    processMessage msg =
      (Frame.ofCall msg).settle (exec (initEvm msg)) := by
  have hself : msg.withBenv msg.benv = msg := by
    cases msg
    rfl
  have henter : executeCode.enter msg = .inl (initEvm msg) := by
    unfold executeCode.enter
    rw [hdisable]
    cases msg.codeAddress <;> rfl
  have hframe :
      (Frame.ofCall msg).enter = .run (initEvm msg) := by
    unfold Frame.enter Frame.ofCall
    rw [hentry]
    simp only
    rw [hself, henter]
  unfold processMessage runFrame
  rw [hframe]

/-- The message-settled machine produced by a raw REVERT outcome. -/
def settledRevert (msg : Msg) (raw : Devm) : Devm :=
  (raw.withError (some .revert)).rollback
    msg.benv.state msg.tenv.transientStorage

/-- The message-settled machine produced by a raw exceptional halt. -/
def settledHalt
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) : Devm :=
  (((raw.withGasLeft 0).setMeta
      {raw.meta with output := [], error := some (.halt reason)}).rollback
    msg.benv.state msg.tenv.transientStorage)

/-- A clean raw execution settles to the same clean machine. -/
theorem processMessage_clean_of_exec
    (msg : Msg) (post : Devm)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true)
    (hexec : exec (initEvm msg) = .ok post)
    (herror : post.error = none) :
    processMessage msg = .ok post := by
  rw [processMessage_eq_settle_exec msg hentry hdisable, hexec]
  simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
    executeCode.handleError, processMessage.settle]
  change (if post.error.isSome = true then
    Except.ok (post.rollback msg.benv.state msg.tenv.transientStorage)
    else Except.ok post) = Except.ok post
  rw [herror]
  rfl

/-- A clean raw execution from the actual post-transfer message entry settles
successfully to that same machine.  This is the payable-call counterpart of
`processMessage_clean_of_exec`: the caller supplies the environment produced
by value transfer rather than assuming entry-state identity. -/
theorem processMessage_clean_of_exec_afterTransfer
    (msg : Msg) (benv : Benv) (post : Devm)
    (hentry : msg.benvAfterTransfer = .ok benv)
    (hdisable : msg.disablePrecompiles = true)
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post)
    (herror : post.error = none) :
    processMessage msg = .ok post := by
  rw [processMessage_eq_settle_exec_afterTransfer msg benv hentry hdisable,
    hexec]
  simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
    executeCode.handleError, processMessage.settle]
  change (if post.error.isSome = true then
    Except.ok (post.rollback msg.benv.state msg.tenv.transientStorage)
    else Except.ok post) = Except.ok post
  rw [herror]
  rfl

/-- A clean raw execution from an exact post-transfer interpreter entry
settles successfully to the same clean machine. -/
theorem processMessage_clean_of_exec_afterTransfer_of_codeEntry
    (msg : Msg) (benv : Benv) (post : Devm)
    (hentry : msg.benvAfterTransfer = .ok benv)
    (hcodeEntry : executeCode.enter (msg.withBenv benv) =
      .inl (initEvm (msg.withBenv benv)))
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post)
    (herror : post.error = none) :
    processMessage msg = .ok post := by
  rw [processMessage_eq_settle_exec_afterTransfer_of_codeEntry
    msg benv hentry hcodeEntry, hexec]
  simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
    executeCode.handleError, processMessage.settle]
  change (if post.error.isSome = true then
    Except.ok (post.rollback msg.benv.state msg.tenv.transientStorage)
    else Except.ok post) = Except.ok post
  rw [herror]
  rfl

/-- A raw REVERT settles to `settledRevert`. -/
theorem processMessage_revert_of_exec
    (msg : Msg) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true)
    (hexec : exec (initEvm msg) = .error (.revert, raw)) :
    processMessage msg = .ok (settledRevert msg raw) := by
  rw [processMessage_eq_settle_exec msg hentry hdisable, hexec]
  rfl

/-- A raw exceptional halt settles to `settledHalt`. -/
theorem processMessage_halt_of_exec
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true)
    (hexec : exec (initEvm msg) = .error (.halt reason, raw)) :
    processMessage msg = .ok (settledHalt msg reason raw) := by
  rw [processMessage_eq_settle_exec msg hentry hdisable, hexec]
  rfl

@[simp] theorem settledRevert_error (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).error = some .revert := rfl

@[simp] theorem settledRevert_output (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).output = raw.output := rfl

@[simp] theorem settledRevert_logs (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).logs = raw.logs := rfl

@[simp] theorem settledRevert_state (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).state = msg.benv.state := rfl

@[simp] theorem settledRevert_transientStorage (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).transientStorage =
      msg.tenv.transientStorage := rfl

@[simp] theorem settledHalt_error
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).error = some (.halt reason) := rfl

@[simp] theorem settledHalt_output
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).output = [] := rfl

@[simp] theorem settledHalt_logs
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).logs = raw.logs := rfl

@[simp] theorem settledHalt_state
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).state = msg.benv.state := rfl

@[simp] theorem settledHalt_transientStorage
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).transientStorage =
      msg.tenv.transientStorage := rfl

end MessageExecution

/-! ## Canonical message-entry projections -/

@[simp] theorem Msg.initDevm_stack (msg : Msg) :
    (initDevm msg).stack = [] := rfl

@[simp] theorem Msg.initDevm_memory (msg : Msg) :
    (initDevm msg).memory = Mem.empty := rfl

@[simp] theorem Msg.initDevm_accessedStorageKeys (msg : Msg) :
    (initDevm msg).accessedStorageKeys = msg.accessedStorageKeys := rfl

@[simp] theorem Msg.initSevm_data (msg : Msg) :
    (initSevm msg).data = msg.data := rfl

@[simp] theorem Msg.initSevm_currentTarget (msg : Msg) :
    (initSevm msg).currentTarget = msg.currentTarget := rfl

end Blanc
