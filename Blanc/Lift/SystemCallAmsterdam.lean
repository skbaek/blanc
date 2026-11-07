import Blanc.Lift.AmsterdamWalk
import Blanc.SystemCallForward
import Blanc.HistoricalFork
import Batteries.Tactic.OpenPrivate

/-!
# The system-call envelope under Amsterdam

`Blanc/SystemCallForward.lean` is the envelope on a covered fork. Under Amsterdam
`processMessageCall.call` takes `processTopLevelAmsterdam` instead, and the frame does not start at
`initDevm`: `prepareTopLevelAmsterdam` records two reads first. This module takes a compiled frame
from that real base, `systemCallBase`, to `processSystemTransaction`
and `processCheckedSystemTransaction`, generic in the target, its
code and the frame.

`open private` on Jaune's top-level path is isolated here. A pin move can break these names, and
only this module would then need repair.
-/

namespace Blanc.Lift

open Jaune

open private preparedTopLevelMsg resolveTopLevelCallAmsterdam dispatchTopLevelAmsterdam
  finishTopLevelAmsterdam runPreparedTopFrame msgCallOutputAmsterdam checkTransactionGasLimit
  checkTransactionPriorityFeeRelation checkTransactionBlobShape from Jaune.Transaction

/-- The machine a top-level Amsterdam system call prepares: two read records on `initDevm`. -/
def systemCallBase (msg : Msg) : Devm :=
  let rules := msg.benv.stat.rules
  ((initDevm msg).balReadAccount rules msg.currentTarget).balReadAccount rules msg.currentTarget

/-- The output `processTopLevelAmsterdam` renders from a clean frame. -/
def systemCallOutputA (msg : Msg) (post : Devm) : MsgCallOutput :=
  { accountReads := post.meta.accountReads
    storageReads := post.meta.storageReads
    storageWrites := post.world.storageWrites
    gasLeft := post.gasLeft
    refundCounter := post.refundCounter.toNat
    logs := post.logs
    accountsToDelete := post.accountsToDelete
    error := none
    returnData := post.output
    stateGasLeft := post.stateGasLeft
    stateGasUsed := Int.ofNat msg.stateGasGrant - Int.ofNat post.stateGasLeft +
      Int.ofNat post.mach.stateGas.spilled + Int.ofNat post.mach.stateGas.committedSpill }

section

variable {benv : Benv} {target : Adr} {code : ByteArray} {data : Bytes}

local notation "M" => systemCallMsg benv target code data

/-! ## The prepared base -/

/-- The prepared base is `St` over itself at the system gas, so a walk from
`St b [] .empty systemTransactionGas` starts there. -/
theorem systemCallBase_St :
    St (systemCallBase M) [] .empty systemTransactionGas = systemCallBase M := by
  unfold systemCallBase Devm.balReadAccount
  rfl

theorem systemCallBase_error (msg : Msg) : (systemCallBase msg).error = none := by
  simp only [systemCallBase, balReadAccount_error]
  rfl

theorem systemCallBase_refundCounter (msg : Msg) : (systemCallBase msg).refundCounter = 0 := by
  simp only [systemCallBase, Devm.balReadAccount_refundCounter]
  rfl

/-- A top-level frame's base records no storage read, and holds the write ledger the message started with. -/
theorem systemCallBase_record (msg : Msg) :
    (systemCallBase msg).meta.storageReads = .emptyWithCapacity ∧
      (systemCallBase msg).world.storageWrites = msg.benv.storageWrites := by
  unfold systemCallBase Devm.balReadAccount
  dsimp only
  by_cases h : msg.benv.stat.rules.bal.isSome = true <;> simp only [h, ↓reduceIte] <;> exact ⟨rfl, rfl⟩

/-- The reservoir starts at the system grant, with no spill. -/
theorem systemCallBase_stateGas (hfork : benv.stat.fork = .amsterdam) :
    (systemCallBase M).stateGas.spilled = 0 ∧
      (systemCallBase M).stateGas.left =
        amsterdamStateGasRules.systemReservoir := by
  have hs : (benv.beginTransaction).stat.rules.stateGas = some amsterdamStateGasRules :=
    amsterdam_stateGas hfork
  refine ⟨rfl, ?_⟩
  show (match (benv.beginTransaction).stat.rules.stateGas with
    | none => 0
    | some state => state.systemReservoir) = _
  rw [hs]

/-- On the prepared base a slot's current value is its original value, unless the account was
created in this transaction and its original is zero. -/
theorem systemCallBase_orig {sevm : Sevm} (hsevm : sevm = initSevm M) (a : Adr) (k : B256) :
    (systemCallBase M).getOrigStorVal sevm a k =
        (systemCallBase M).getStorVal a k ∨
      (systemCallBase M).getOrigStorVal sevm a k = 0 := by
  subst hsevm
  unfold Devm.getOrigStorVal
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

end

/-! ## A user's call

The same top-level path for an ordinary message: value transfer before the frame, the EIP-7708 log
`initDevm` seeds, and the settlement of a clean, a reverted and a halted frame, generic in the frame. -/

/-- The message the top-level path runs: the code resolved at the target, undelegated. -/
def userMsg (M : Msg) (code : ByteArray) : Msg :=
  { M with codeAddress := some M.currentTarget, code := code, disablePrecompiles := false }

/-- The frame's entry machine: the prepared one (`systemCallBase`, two read records on `initDevm`), over
the state after the value moved. -/
def userEntry (M : Msg) (benv : Benv) : Devm :=
  (((systemCallBase M).withState benv.state).withStorageWrites benv.storageWrites).withCreatedAccounts
    benv.createdAccounts

/-- The frame's static environment. -/
def userSevm (M : Msg) (code : ByteArray) (benv : Benv) : Sevm :=
  initSevm ((userMsg M code).withBenv benv)

/-- What `processTopLevelAmsterdam` renders from a frame settled as failed, `handled`: no log survives, the
refund counter is gone, the transaction's write ledger is the one the call started with, and the reads the
frame recorded stay. -/
def failedOutput (M : Msg) (handled : Devm) : MsgCallOutput :=
  { accountReads := handled.meta.accountReads
    storageReads := handled.meta.storageReads
    storageWrites := M.benv.storageWrites
    gasLeft := handled.gasLeft
    refundCounter := 0
    logs := []
    accountsToDelete := .emptyWithCapacity
    error := handled.error
    returnData := handled.output
    stateGasLeft := handled.stateGasLeft
    stateGasUsed := Int.ofNat M.stateGasGrant - Int.ofNat handled.stateGasLeft +
      Int.ofNat handled.mach.stateGas.spilled + Int.ofNat handled.mach.stateGas.committedSpill }

/-- A raw `REVERT` settled: the spill back in `gasLeft`, the reservoir at its baseline. -/
def revertedFrame (raw : Devm) : Devm := raw.restoreStateGas.withError (some .revert)

/-- A raw exceptional halt settled: the same refill, then the remaining gas forfeited and the output gone. -/
def haltedFrame (reason : ExceptionalHalt) (raw : Devm) : Devm :=
  let evm := raw.restoreStateGas.forfeitRemainingGas
  evm.setMeta {evm.meta with output := [], error := some (.halt reason)}

section User

variable {M : Msg} {code : ByteArray} {benv : Benv}

private theorem preparedTopLevelMsg_user : preparedTopLevelMsg M (systemCallBase M) = M := by
  unfold preparedTopLevelMsg systemCallBase
  simp only [Devm.balReadAccount_accessedAddresses, Devm.balReadAccount_accessedStorageKeys,
    Devm.balReadAccount_createdAccounts, Devm.balReadAccount_transientStorage]
  rfl

/-- An account with code is not empty, so a value-bearing call to it is charged no new-account state gas. -/
theorem not_new_of_code (installed : M.benv.state.getCode M.currentTarget = code)
    (hnonempty : code.isEmpty = false) :
    (M.value != 0 && decide (M.benv.state.get M.currentTarget).Empty) = false := by
  have hne : ¬ (M.benv.state.get M.currentTarget).Empty := by
    intro h
    have hsize : (M.benv.state.get M.currentTarget).code.size = 0 := h.1
    have hcode : (M.benv.state.get M.currentTarget).code = code := installed
    rw [hcode] at hsize
    have : code.isEmpty = true := by
      simp only [ByteArray.isEmpty, hsize]
      rfl
    rw [this] at hnonempty
    cases hnonempty
  simp only [hne, decide_false, Bool.and_false]

/-- Preparation of a non-delegated call with no authorizations, charged no new-account state gas. -/
theorem prepare_user (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code)
    (hold : (M.value != 0 && decide (M.benv.state.get M.currentTarget).Empty) = false)
    (hdel : getDelegatedCodeAddress code = none) :
    prepareTopLevelAmsterdam amsterdamStateGasRules M = .ok (userMsg M code, systemCallBase M) := by
  unfold prepareTopLevelAmsterdam finishTopLevelAmsterdam dispatchTopLevelAmsterdam
    resolveTopLevelCallAmsterdam
  have hen : M.benv.stat.rules.delegationEnabled = true := by
    rw [amsterdam_rules hfork]
    rfl
  have hcost : M.benv.stat.rules.delegationCost
      (Devm.balReadAccount M.benv.stat.rules M.currentTarget (initDevm M)) M.currentTarget =
        (false, M.currentTarget, 0) := by
    simp only [ForkRules.delegationCost, hen, ↓reduceIte, GasSchedule.delegationCost]
    show (match getDelegatedCodeAddress (M.benv.state.getCode M.currentTarget) with
      | some delegated => _
      | none => _) = _
    rw [installed, hdel]
  have hz : ∀ d : Devm, chargeGas 0 d = .ok d := fun d => by
    rw [chargeGas_eq_ok (Nat.zero_le _)]
    rfl
  have hnew : (M.value != 0 && decide (Devm.state (Devm.balReadAccount M.benv.stat.rules
      M.currentTarget (initDevm M)) |>.get M.currentTarget).Empty) = false := hold
  simp only [hauth, ↓reduceIte]
  simp only [htarget, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, Except.bind]
  simp only [hnew, Bool.false_eq_true, ↓reduceIte]
  rw [hcost]
  simp only [hz, completeDelegationAccess, Bool.false_eq_true, ↓reduceIte]
  rw [show (Devm.balReadAccount M.benv.stat.rules M.currentTarget
      (Devm.balReadAccount M.benv.stat.rules M.currentTarget (initDevm M))) = systemCallBase M from rfl,
    preparedTopLevelMsg_user]
  show Except.ok ({ M with
    codeAddress := some M.currentTarget
    code := (initDevm M).state.getCode M.currentTarget
    disablePrecompiles := false }, systemCallBase M) = _
  rw [show (initDevm M).state = M.benv.state from rfl, installed]
  rfl

private theorem runPrepared_raw (hfork : M.benv.stat.fork = .amsterdam)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv) :
    runPreparedTopFrame (Frame.ofCall (userMsg M code)) (systemCallBase M) =
      (Frame.ofCall (userMsg M code)).settle
        (exec ⟨0, userSevm M code benv, userEntry M benv⟩) := by
  have hstat : benv.stat = M.benv.stat := benvAfterTransfer_stat entry
  have hrules := amsterdam_rules hfork
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

/-- The top-level path of a prepared call, down to the raw frame. -/
private theorem processMessageCall_prepared (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code)
    (hold : (M.value != 0 && decide (M.benv.state.get M.currentTarget).Empty) = false)
    (hdel : getDelegatedCodeAddress code = none)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv) :
    processMessageCall M =
      (Except.bimap Prod.fst id ((Frame.ofCall (userMsg M code)).settle
        (exec ⟨0, userSevm M code benv, userEntry M benv⟩))) >>=
          msgCallOutputAmsterdam (userMsg M code) := by
  have hsg := amsterdam_stateGas hfork
  unfold processMessageCall
  simp only [htarget, Bool.false_eq_true, ↓reduceIte]
  unfold processMessageCall.call
  rw [hsg]
  simp only
  unfold processTopLevelAmsterdam
  rw [prepare_user hfork hauth htarget installed hold hdel]
  simp only [bind, Except.bind]
  rw [runPrepared_raw hfork hprecomp entry]

/-- The settlement of a raw outcome on a state-gas fork. -/
private theorem settle_user (hfork : M.benv.stat.fork = .amsterdam) (raw : Execution) :
    (Frame.ofCall (userMsg M code)).settle raw =
      processMessage.settle (userMsg M code) (executeCode.handleErrorAmsterdam raw) := by
  have hsg' : (userMsg M code).benv.stat.rules.stateGas = some amsterdamStateGasRules :=
    amsterdam_stateGas hfork
  unfold Frame.settle Frame.settleMsg
  simp only [Frame.ofCall, Bool.false_eq_true, ite_false]
  rw [hsg']
  rfl

private theorem processMessageCall_clean {post : Devm} (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code)
    (hold : (M.value != 0 && decide (M.benv.state.get M.currentTarget).Empty) = false)
    (hdel : getDelegatedCodeAddress code = none)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (run : exec ⟨0, userSevm M code benv, userEntry M benv⟩ = .ok post)
    (clean : post.error = none) (nonneg : 0 ≤ post.refundCounter) :
    processMessageCall M = .ok (post.state, systemCallOutputA M post) := by
  rw [processMessageCall_prepared hfork hauth htarget installed hold hdel hprecomp entry, run,
    settle_user hfork]
  have hsweep : (userMsg M code).benv.stat.rules.settle.touchedSweep = false := by
    show M.benv.stat.rules.settle.touchedSweep = false
    rw [amsterdam_rules hfork]
    rfl
  simp only [executeCode.handleErrorAmsterdam, processMessage.settle, bind, Except.bind, clean,
    Option.isSome_none, Bool.false_eq_true, ite_false, Devm.recordTouch_of_not_touchedSweep hsweep,
    Except.bimap, id]
  unfold msgCallOutputAmsterdam
  simp only [clean, Option.isNone_none, ↓reduceIte, bind, Except.bind,
    Int.toNat?_eq_some_of_nonneg nonneg, Option.toExcept]
  rfl

/-- **A user's call whose frame is clean, under Amsterdam.** The value moved first (`entry`); the frame ran from
that state; the output is the frame's. -/
theorem processMessageCall_ok {post : Devm} (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code) (hnonempty : code.isEmpty = false)
    (hdel : getDelegatedCodeAddress code = none)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (run : exec ⟨0, userSevm M code benv, userEntry M benv⟩ = .ok post)
    (clean : post.error = none) (nonneg : 0 ≤ post.refundCounter) :
    processMessageCall M = .ok (post.state, systemCallOutputA M post) :=
  processMessageCall_clean hfork hauth htarget installed (not_new_of_code installed hnonempty) hdel hprecomp
    entry run clean nonneg

/-- **A user's call whose frame fails, reverted or halted, under Amsterdam.** Whatever the frame did, the state
is the pre-call state, so the value is back; no log survives, the transfer log included; the refund counter is
gone. `handled` is the machine the fork's error handler made of the raw failure. -/
private theorem processMessageCall_failed {raw : Execution} {handled : Devm}
    (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code) (hnonempty : code.isEmpty = false)
    (hdel : getDelegatedCodeAddress code = none)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (run : exec ⟨0, userSevm M code benv, userEntry M benv⟩ = raw)
    (handle : executeCode.handleErrorAmsterdam raw = .ok handled)
    (failed : handled.error.isSome = true) :
    processMessageCall M = .ok (M.benv.state, failedOutput M handled) := by
  rw [processMessageCall_prepared hfork hauth htarget installed (not_new_of_code installed hnonempty) hdel
    hprecomp entry, run, settle_user hfork, handle]
  have hsweep : (userMsg M code).benv.stat.rules.settle.touchedSweep = false := by
    show M.benv.stat.rules.settle.touchedSweep = false
    rw [amsterdam_rules hfork]
    rfl
  simp only [processMessage.settle, bind, Except.bind, failed, ↓reduceIte,
    Devm.recordTouch_of_not_touchedSweep hsweep]
  simp only [Except.bimap, id]
  unfold msgCallOutputAmsterdam
  have hnone : (((handled.rollback (userMsg M code).benv.state
      (userMsg M code).tenv.transientStorage).withStorageWrites
      (userMsg M code).benv.storageWrites).error).isNone = false := by
    show handled.error.isNone = false
    cases h : handled.error with
    | none => simp only [h, Option.isSome_none, Bool.false_eq_true] at failed
    | some _ => rfl
  simp only [hnone, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  rfl

/-- **A user's call whose frame executes `REVERT`, under Amsterdam.** The state is the pre-call state, so the
value is back; no log survives, the transfer log included; the refund counter is gone; the reservoir is at its
baseline and the spill is back in `gasLeft`. -/
theorem processMessageCall_revert {raw : Devm} (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code) (hnonempty : code.isEmpty = false)
    (hdel : getDelegatedCodeAddress code = none)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (run : exec ⟨0, userSevm M code benv, userEntry M benv⟩ = .error (.revert, raw)) :
    processMessageCall M = .ok (M.benv.state, failedOutput M (revertedFrame raw)) :=
  processMessageCall_failed hfork hauth htarget installed hnonempty hdel hprecomp entry run rfl rfl

/-- **A user's call whose frame halts exceptionally, under Amsterdam.** The state is the pre-call state, no log
survives, and the remaining gas is forfeited, with the spill and reservoir refilled first. -/
theorem processMessageCall_halt {raw : Devm} {reason : ExceptionalHalt}
    (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code) (hnonempty : code.isEmpty = false)
    (hdel : getDelegatedCodeAddress code = none)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (run : exec ⟨0, userSevm M code benv, userEntry M benv⟩ = .error (.halt reason, raw)) :
    processMessageCall M = .ok (M.benv.state, failedOutput M (haltedFrame reason raw)) :=
  processMessageCall_failed hfork hauth htarget installed hnonempty hdel hprecomp entry run rfl rfl

/-- Under Amsterdam a value-moving call's entry log is the EIP-7708 transfer log. -/
theorem initDevm_logs_transfer (hfork : M.benv.stat.fork = .amsterdam) (transfer : M.shouldTransferValue = true)
    (distinct : M.caller ≠ M.currentTarget) (nonzero : M.value ≠ 0) :
    (initDevm M).logs = [transferLog M.caller M.currentTarget M.value] := by
  have hsg := amsterdam_stateGas hfork
  show (match M.benv.stat.rules.stateGas with
    | none => []
    | some _ => if M.shouldTransferValue then (Devm.emitTransferLog _ _ _ _).logs else []) = _
  rw [hsg]
  simp only [transfer, ↓reduceIte, Devm.emitTransferLog, distinct, nonzero, or_self]
  rfl

/-- The settled meter of a revert: the reservoir at its baseline, the spill back in `gasLeft`. No log, no refund.
Regular gas and state gas are the two distinct figures here. -/
theorem failedOutput_revert (M : Msg) (raw : Devm) :
    (failedOutput M (revertedFrame raw)).stateGasLeft = raw.stateGas.baseline ∧
      (failedOutput M (revertedFrame raw)).gasLeft = raw.gasLeft + raw.stateGas.spilled ∧
      (failedOutput M (revertedFrame raw)).refundCounter = 0 ∧
      (failedOutput M (revertedFrame raw)).logs = [] ∧
      (failedOutput M (revertedFrame raw)).error = some .revert ∧
      (failedOutput M (revertedFrame raw)).stateGasUsed =
        Int.ofNat M.stateGasGrant - Int.ofNat raw.stateGas.baseline + Int.ofNat 0 +
          Int.ofNat raw.stateGas.committedSpill :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The inverse at message level.** A call under Amsterdam whose transfer succeeded and whose output carries no
error came from a clean frame: the machine's run ended `.ok`, and the state and output are that machine's. -/
theorem processMessageCall_inv {post : State} {out : MsgCallOutput} (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = code) (hnonempty : code.isEmpty = false)
    (hdel : getDelegatedCodeAddress code = none)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (call : processMessageCall M = .ok (post, out)) (ok : out.error = none) :
    ∃ frame, exec ⟨0, userSevm M code benv, userEntry M benv⟩ = .ok frame ∧ frame.error = none ∧
      post = frame.state ∧ out = systemCallOutputA M frame := by
  have hsweep : (userMsg M code).benv.stat.rules.settle.touchedSweep = false := by
    show M.benv.stat.rules.settle.touchedSweep = false
    rw [amsterdam_rules hfork]
    rfl
  have prepared := processMessageCall_prepared (M := M) (code := code) (benv := benv) hfork hauth htarget
    installed (not_new_of_code installed hnonempty) hdel hprecomp entry
  rw [settle_user hfork] at prepared
  rcases hraw : exec ⟨0, userSevm M code benv, userEntry M benv⟩ with ⟨e, raw⟩ | frame
  · exfalso
    cases e with
    | halt reason =>
      rw [processMessageCall_failed (raw := .error (.halt reason, raw)) hfork hauth htarget installed
        hnonempty hdel hprecomp entry hraw rfl rfl] at call
      have hout := congrArg Prod.snd (Except.ok.inj call)
      subst hout
      cases ok
    | revert =>
      rw [processMessageCall_failed (raw := .error (.revert, raw)) hfork hauth htarget installed
        hnonempty hdel hprecomp entry hraw rfl rfl] at call
      have hout := congrArg Prod.snd (Except.ok.inj call)
      subst hout
      cases ok
    | crypto reason =>
      rw [prepared, hraw] at call
      cases call
    | internal reason =>
      rw [prepared, hraw] at call
      cases call
  · rw [prepared, hraw] at call
    simp only [executeCode.handleErrorAmsterdam, processMessage.settle, bind, Except.bind,
      Except.bimap, id] at call
    cases herr : frame.error with
    | some e =>
      exfalso
      simp only [herr, Option.isSome_some, ↓reduceIte, Devm.recordTouch_of_not_touchedSweep hsweep] at call
      unfold msgCallOutputAmsterdam at call
      simp only [bind, Except.bind] at call
      have hnone : (((frame.rollback (userMsg M code).benv.state
          (userMsg M code).tenv.transientStorage).withStorageWrites
          (userMsg M code).benv.storageWrites).error).isNone = false := by
        show frame.error.isNone = false
        rw [herr]
        rfl
      simp only [hnone, Bool.false_eq_true, ↓reduceIte] at call
      have hout := congrArg Prod.snd (Except.ok.inj call)
      have herror := congrArg MsgCallOutput.error hout
      rw [ok] at herror
      have : frame.error = none := herror
      rw [herr] at this
      cases this
    | none =>
      simp only [herr, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        Devm.recordTouch_of_not_touchedSweep hsweep] at call
      unfold msgCallOutputAmsterdam at call
      simp only [bind, Except.bind, herr, Option.isNone_none, ↓reduceIte] at call
      cases hrefund : Int.toNat? frame.refundCounter with
      | none =>
        simp only [hrefund, Option.toExcept] at call
        cases call
      | some refund =>
        simp only [hrefund, Option.toExcept, Except.ok.injEq, Prod.mk.injEq] at call
        obtain ⟨hstate, hout⟩ := call
        refine ⟨frame, rfl, herr, hstate.symm, ?_⟩
        subst hout
        have hrc : frame.refundCounter.toNat = refund := by
          unfold Int.toNat? at hrefund
          split at hrefund <;> simp only [Option.some.injEq, reduceCtorEq] at hrefund
          rename_i n hn
          rw [hn, ← hrefund]
          rfl
        simp only [systemCallOutputA, hrc]
        rfl

end User

/-! ## Validation of a plain call transaction -/

/-- **Validation of a type-2 call under Amsterdam, from its facts.** A receiver, no access list, priority fee at most the
fee cap, a nonce below the maximum, its gas at most the 2^32 - 1 total cap, and its gas covering the intrinsic cost and the
calldata floor, each of them within the 2^24 execution budget. -/
theorem validateTransaction_amsterdam_two {rules : ForkRules} {tx : Tx} {sender t : Adr} {chainId : UInt64}
    {prio maxFee i f : Nat} (hrules : rules = amsterdamRules)
    (htype : tx.type = .two chainId prio maxFee (some t) [])
    (hprio : prio ≤ maxFee) (hnonce : tx.nonce ≠ UInt64.max) (hcap : tx.gas ≤ 4294967295)
    (hcost : calculateIntrinsicCost rules tx sender = (i, f)) (hi : i ≤ tx.gas) (hf : f ≤ tx.gas)
    (himax : i ≤ 16777216) (hfmax : f ≤ 16777216) :
    validateTransaction rules tx sender = .ok (i, f) := by
  subst hrules
  have hrec : tx.type.receiver? = some t := by rw [htype]; rfl
  have hinit : checkInitcodeLimit amsterdamRules tx.type.receiver? tx.data.length = .ok () := by
    rw [hrec]
    rfl
  have htotal : checkTransactionTotalGasCap amsterdamRules.tx tx.gas = .ok () := by
    unfold checkTransactionTotalGasCap checkTransactionGasLimit
    show (if tx.gas > 4294967295 then _ else _) = _
    simp only [gt_iff_lt, Nat.not_lt.mpr hcap, ↓reduceIte]
  have hrel : checkTransactionPriorityFeeRelation tx = .ok () := by
    unfold checkTransactionPriorityFeeRelation
    rw [htype]
    simp only [Nat.not_lt.mpr hprio, ↓reduceIte]
  have hshape : checkTransactionBlobShape amsterdamRules tx = .ok () := by
    unfold checkTransactionBlobShape
    rw [htype]
  have hrecv : checkTransactionReceiver tx = .ok () := by
    unfold checkTransactionReceiver Tx.isTypeThree
    rw [htype]
    rfl
  have hauth : checkTransactionAuthorizationList tx = .ok () := by
    unfold checkTransactionAuthorizationList
    rw [htype]
  unfold validateTransaction
  show (do
    if tx.nonce = UInt64.max then .error _
    checkInitcodeLimit amsterdamRules tx.type.receiver? tx.data.length
    checkTransactionTotalGasCap amsterdamRules.tx tx.gas
    checkTransactionPriorityFeeRelation tx
    checkTransactionBlobShape amsterdamRules tx
    checkTransactionReceiver tx
    checkTransactionAuthorizationList tx
    let ⟨intrinsicGas, callDataFloorGasCost⟩ := calculateIntrinsicCost amsterdamRules tx sender
    if intrinsicGas > tx.gas then .error _
    if callDataFloorGasCost > tx.gas then .error _
    if intrinsicGas > 16777216 then .error _
    if callDataFloorGasCost > 16777216 then .error _
    .ok (intrinsicGas, callDataFloorGasCost) : Except TxValidationError (Nat × Nat)) = _
  rw [hinit, htotal, hrel, hshape, hrecv, hauth, hcost]
  simp only [hnonce, gt_iff_lt, Nat.not_lt.mpr hi, Nat.not_lt.mpr hf, Nat.not_lt.mpr himax,
    Nat.not_lt.mpr hfmax, ↓reduceIte, bind, Except.bind, pure, Except.pure]

/-! ## The system-call envelope -/

section

variable {benv : Benv} {target : Adr} {code : ByteArray} {data : Bytes}

local notation "SM" => systemCallMsg benv target code data

/-- **The system-call wrapper over a compiled frame under Amsterdam.** The frame runs from the real
prepared base. -/
theorem processSystemTransaction_amsterdam_of_exec {post : Devm}
    (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode target = code)
    (hdel : getDelegatedCodeAddress code = none)
    (hprecomp : ¬ amsterdamRules.isPrecomp target)
    (run : exec ⟨0, initSevm (systemCallMsg benv target code data),
      systemCallBase (systemCallMsg benv target code data)⟩ = .ok post)
    (clean : post.error = none) (nonneg : 0 ≤ post.refundCounter) :
    processSystemTransaction benv target code data =
      .ok (post.state, systemCallOutputA (systemCallMsg benv target code data) post) := by
  have hbal : (SM).benv.stat.rules.bal.isSome = true := by
    rw [amsterdam_rules (s := (SM).benv.stat) hfork]
    rfl
  have hentry : userEntry SM (SM).benv = systemCallBase SM := by
    unfold userEntry systemCallBase Devm.balReadAccount
    simp only [hbal, ↓reduceIte]
    rfl
  have hold : ((SM).value != 0 && decide ((SM).benv.state.get (SM).currentTarget).Empty) = false := by
    show ((0 : B256) != 0 && _) = false
    simp only [bne_self_eq_false, Bool.false_and]
  have hrun : exec ⟨0, userSevm SM code (SM).benv, userEntry SM (SM).benv⟩ = .ok post := by
    rw [hentry]
    exact run
  show processMessageCall SM = _
  exact processMessageCall_clean (code := code) hfork rfl rfl installed hold hdel hprecomp
    (Msg.benvAfterTransfer_of_value_zero rfl) hrun clean nonneg

/-- The checked block-level system call under Amsterdam over installed nonempty code: neither checked
error arm is reachable. -/
theorem processCheckedSystemTransaction_amsterdam_of_exec {post : Devm}
    (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode target = code)
    (hnonempty : code.isEmpty = false)
    (hdel : getDelegatedCodeAddress code = none)
    (hprecomp : ¬ amsterdamRules.isPrecomp target)
    (run : exec ⟨0, initSevm (systemCallMsg benv target code data),
      systemCallBase (systemCallMsg benv target code data)⟩ = .ok post)
    (clean : post.error = none) (nonneg : 0 ≤ post.refundCounter) :
    processCheckedSystemTransaction benv target data =
      .ok (post.state, systemCallOutputA (systemCallMsg benv target code data) post) := by
  unfold processCheckedSystemTransaction
  simp only [installed, hnonempty, Bool.false_eq_true, ite_false]
  rw [processSystemTransaction_amsterdam_of_exec hfork installed hdel hprecomp run clean nonneg]
  rfl

end

end Blanc.Lift
