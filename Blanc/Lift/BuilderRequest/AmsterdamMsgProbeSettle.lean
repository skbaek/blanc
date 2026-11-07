import Blanc.Lift.SystemCallAmsterdam

/-!
# Probe: an ordinary value-bearing call under Amsterdam, success and revert

Disposable (goal `blanc-eip8282-builder-requests-v1`, O16). `Blanc/Lift/SystemCallAmsterdam.lean` is the
zero-value system call's envelope. This is the same path for a user's message: value transfer, the
EIP-7708 log `initDevm` seeds, and the settlement of a clean frame and of a reverted one, generic in
the frame. Nothing here mentions a contract.
-/

namespace Blanc.Lift.BuilderRequest.AmsterdamMsgProbe

open Jaune

open private preparedTopLevelMsg resolveTopLevelCallAmsterdam dispatchTopLevelAmsterdam
  finishTopLevelAmsterdam runPreparedTopFrame msgCallOutputAmsterdam from Jaune.Transaction

/-- The message the top-level path runs: the code resolved at the target, undelegated. -/
def userMsg (M : Msg) (code : ByteArray) : Msg :=
  { M with codeAddress := some M.currentTarget, code := code, disablePrecompiles := false }

/-- The machine preparation leaves: two read records on `initDevm`. -/
def userBase (M : Msg) : Devm :=
  let rules := M.benv.stat.rules
  ((initDevm M).balReadAccount rules M.currentTarget).balReadAccount rules M.currentTarget

/-- The frame's entry machine: the prepared one, over the state after the value moved. -/
def userEntry (M : Msg) (benv : Benv) : Devm :=
  (((userBase M).withState benv.state).withStorageWrites benv.storageWrites).withCreatedAccounts
    benv.createdAccounts

/-- The frame's static environment. -/
def userSevm (M : Msg) (code : ByteArray) (benv : Benv) : Sevm :=
  initSevm ((userMsg M code).withBenv benv)

/-- What `processTopLevelAmsterdam` renders from a raw `REVERT`. -/
def revertOutput (M : Msg) (raw : Devm) : MsgCallOutput :=
  let handled := raw.restoreStateGas.withError (some .revert)
  { accountReads := handled.meta.accountReads
    storageReads := handled.meta.storageReads
    storageWrites := M.benv.storageWrites
    gasLeft := handled.gasLeft
    refundCounter := 0
    logs := []
    accountsToDelete := .emptyWithCapacity
    error := some .revert
    returnData := handled.output
    stateGasLeft := handled.stateGasLeft
    stateGasUsed := Int.ofNat M.stateGasGrant - Int.ofNat handled.stateGasLeft +
      Int.ofNat handled.mach.stateGas.spilled + Int.ofNat handled.mach.stateGas.committedSpill }

variable {M : Msg} {code : ByteArray} {benv : Benv}

private theorem preparedTopLevelMsg_user :
    preparedTopLevelMsg M (userBase M) = M := by
  unfold preparedTopLevelMsg userBase
  simp only [Devm.balReadAccount_accessedAddresses, Devm.balReadAccount_accessedStorageKeys,
    Devm.balReadAccount_createdAccounts, Devm.balReadAccount_transientStorage]
  rfl

private theorem delegationCost_user (hfork : M.benv.stat.fork = .amsterdam)
    (installed : M.benv.state.getCode M.currentTarget = code)
    (hdel : getDelegatedCodeAddress code = none) (d : Devm)
    (hstate : d.state = M.benv.state) :
    M.benv.stat.rules.delegationCost d M.currentTarget = (false, M.currentTarget, 0) := by
  have hen : M.benv.stat.rules.delegationEnabled = true := by
    rw [Blanc.amsterdam_rules hfork]
    rfl
  simp only [ForkRules.delegationCost, hen, ↓reduceIte, GasSchedule.delegationCost]
  show (match getDelegatedCodeAddress (d.state.getCode M.currentTarget) with
    | some delegated => _
    | none => _) = _
  rw [hstate, installed, hdel]

/-- Preparation of a non-delegated call, no authorizations, at an account that is not empty. -/
theorem prepare_user (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code)
    (hdel : getDelegatedCodeAddress code = none)
    (hnew : (M.value != 0 && decide (M.benv.state.get M.currentTarget).Empty) = false) :
    prepareTopLevelAmsterdam amsterdamStateGasRules M = .ok (userMsg M code, userBase M) := by
  unfold prepareTopLevelAmsterdam finishTopLevelAmsterdam dispatchTopLevelAmsterdam
    resolveTopLevelCallAmsterdam
  have hcost := delegationCost_user hfork installed hdel
    (Devm.balReadAccount M.benv.stat.rules M.currentTarget (initDevm M)) rfl
  have hz : ∀ d : Devm, chargeGas 0 d = .ok d := fun d => by
    rw [chargeGas_eq_ok (Nat.zero_le _)]
    rfl
  have hnew' : (M.value != 0 && decide (Devm.state (Devm.balReadAccount M.benv.stat.rules
      M.currentTarget (initDevm M)) |>.get M.currentTarget).Empty) = false := hnew
  simp only [hauth, ↓reduceIte]
  simp only [htarget, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, Except.bind]
  simp only [hnew', Bool.false_eq_true, ↓reduceIte]
  rw [hcost]
  simp only [hz, completeDelegationAccess, Bool.false_eq_true, ↓reduceIte]
  rw [show (Devm.balReadAccount M.benv.stat.rules M.currentTarget
      (Devm.balReadAccount M.benv.stat.rules M.currentTarget (initDevm M))) = userBase M from rfl,
    preparedTopLevelMsg_user]
  show Except.ok ({ M with
    codeAddress := some M.currentTarget
    code := (initDevm M).state.getCode M.currentTarget
    disablePrecompiles := false }, userBase M) = _
  rw [show (initDevm M).state = M.benv.state from rfl, installed]
  rfl

private theorem runPrepared_raw (hfork : M.benv.stat.fork = .amsterdam)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget)
    (entry : M.benvAfterTransfer = .ok benv) (hstat : benv.stat = M.benv.stat) :
    runPreparedTopFrame (Frame.ofCall (userMsg M code)) (userBase M) =
      (Frame.ofCall (userMsg M code)).settle
        (exec ⟨0, userSevm M code benv, userEntry M benv⟩) := by
  have hrules := Blanc.amsterdam_rules hfork
  have hentry : (userMsg M code).benvAfterTransfer = .ok benv := entry
  unfold runPreparedTopFrame
  have hinner : (Frame.ofCall (userMsg M code)).inner = userMsg M code := rfl
  rw [hinner, hentry]
  have hnot : ¬ benv.stat.rules.isPrecomp M.currentTarget := by
    rw [hstat, hrules]
    exact hprecomp
  show (Frame.ofCall (userMsg M code)).settle
    (if (!false && benv.stat.rules.isPrecomp M.currentTarget) = true then
      executePrecomp ⟨0, userSevm M code benv, userEntry M benv⟩ M.currentTarget
    else exec ⟨0, userSevm M code benv, userEntry M benv⟩) = _
  simp only [Bool.not_false, Bool.true_and, hnot, decide_false, Bool.false_eq_true, ite_false]

/-- **A user's call whose frame is clean, under Amsterdam.** -/
theorem processMessageCall_ok {post : Devm}
    (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code)
    (hdel : getDelegatedCodeAddress code = none)
    (hnew : (M.value != 0 && decide (M.benv.state.get M.currentTarget).Empty) = false)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget)
    (entry : M.benvAfterTransfer = .ok benv) (hstat : benv.stat = M.benv.stat)
    (run : exec ⟨0, userSevm M code benv, userEntry M benv⟩ = .ok post)
    (clean : post.error = none) (nonneg : 0 ≤ post.refundCounter) :
    processMessageCall M = .ok (post.state, systemCallOutputA M post) := by
  have hsg := Blanc.amsterdam_stateGas hfork
  unfold processMessageCall
  simp only [htarget, Bool.false_eq_true, ↓reduceIte]
  unfold processMessageCall.call
  rw [hsg]
  simp only
  unfold processTopLevelAmsterdam
  rw [prepare_user hfork hauth htarget installed hdel hnew]
  simp only [bind, Except.bind]
  rw [runPrepared_raw hfork hprecomp entry hstat, run]
  have hsweep : (userMsg M code).benv.stat.rules.settle.touchedSweep = false := by
    show M.benv.stat.rules.settle.touchedSweep = false
    rw [Blanc.amsterdam_rules hfork]
    rfl
  have hsg' : (userMsg M code).benv.stat.rules.stateGas = some amsterdamStateGasRules := hsg
  unfold Frame.settle Frame.settleMsg
  simp only [Frame.ofCall, Bool.false_eq_true, ite_false]
  rw [hsg']
  simp only [executeCode.handleErrorWith, executeCode.handleErrorAmsterdam,
    processMessage.settle, bind, Except.bind, clean, Option.isSome_none, Bool.false_eq_true,
    ite_false, Devm.recordTouch_of_not_touchedSweep hsweep, Except.bimap, id]
  unfold msgCallOutputAmsterdam
  simp only [clean, Option.isNone_none, ↓reduceIte, bind, Except.bind,
    Int.toNat?_eq_some_of_nonneg nonneg, Option.toExcept]
  rfl

/-- **A user's call whose frame executes `REVERT`, under Amsterdam.** The state is the pre-call state,
so the value is back; no log survives; the refund counter is gone; the reservoir is at its baseline
and the spill is back in `gasLeft`. -/
theorem processMessageCall_revert {raw : Devm}
    (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code)
    (hdel : getDelegatedCodeAddress code = none)
    (hnew : (M.value != 0 && decide (M.benv.state.get M.currentTarget).Empty) = false)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget)
    (entry : M.benvAfterTransfer = .ok benv) (hstat : benv.stat = M.benv.stat)
    (run : exec ⟨0, userSevm M code benv, userEntry M benv⟩ = .error (.revert, raw)) :
    processMessageCall M = .ok (M.benv.state, revertOutput M raw) := by
  have hsg := Blanc.amsterdam_stateGas hfork
  unfold processMessageCall
  simp only [htarget, Bool.false_eq_true, ↓reduceIte]
  unfold processMessageCall.call
  rw [hsg]
  simp only
  unfold processTopLevelAmsterdam
  rw [prepare_user hfork hauth htarget installed hdel hnew]
  simp only [bind, Except.bind]
  rw [runPrepared_raw hfork hprecomp entry hstat, run]
  have hsweep : (userMsg M code).benv.stat.rules.settle.touchedSweep = false := by
    show M.benv.stat.rules.settle.touchedSweep = false
    rw [Blanc.amsterdam_rules hfork]
    rfl
  have hsg' : (userMsg M code).benv.stat.rules.stateGas = some amsterdamStateGasRules := hsg
  unfold Frame.settle Frame.settleMsg
  simp only [Frame.ofCall, Bool.false_eq_true, ite_false]
  rw [hsg']
  simp only [executeCode.handleErrorWith, executeCode.handleErrorAmsterdam, processMessage.settle,
    bind, Except.bind, Devm.recordTouch_of_not_touchedSweep hsweep]
  rfl

/-- `processMessage` itself on a raw `REVERT` under a state-gas fork: the form Jaune's `API.md` does
not claim. Same shape as `processMessage_revert_of_exec`, with the state-gas refill. -/
theorem processMessage_revert_stateGas {msg : Msg} {after : Benv} {raw : Devm} {state : StateGasRules}
    (entry : msg.benvAfterTransfer = .ok after)
    (codeEntry : executeCode.enter (msg.withBenv after) = .inl (initEvm (msg.withBenv after)))
    (hgas : msg.benv.stat.rules.stateGas = some state)
    (hsweep : msg.benv.stat.rules.settle.touchedSweep = false)
    (hexec : exec (initEvm (msg.withBenv after)) = .error (.revert, raw)) :
    processMessage msg =
      .ok (((raw.restoreStateGas.withError (some .revert)).rollback msg.benv.state
        msg.tenv.transientStorage).withStorageWrites msg.benv.storageWrites) := by
  rw [MessageExecution.processMessage_eq_settle_exec_afterTransfer_of_codeEntry
    msg after entry codeEntry, hexec]
  simp only [Frame.settle_eq_settleMsg_handleErrorWith, Frame.ofCall, hgas]
  simp only [Frame.settleMsg, processMessage.settle, Devm.recordTouch_of_not_touchedSweep hsweep]
  rfl

end Blanc.Lift.BuilderRequest.AmsterdamMsgProbe
