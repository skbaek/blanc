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
  finishTopLevelAmsterdam runPreparedTopFrame msgCallOutputAmsterdam from Jaune.Transaction

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

/-! ## The private top-level path -/

private theorem preparedTopLevelMsg_system :
    preparedTopLevelMsg M (systemCallBase M) =
      M := by
  unfold preparedTopLevelMsg systemCallBase
  simp only [Devm.balReadAccount_accessedAddresses, Devm.balReadAccount_accessedStorageKeys,
    Devm.balReadAccount_createdAccounts, Devm.balReadAccount_transientStorage]
  rfl

private theorem delegationCost_system (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode target = code)
    (hdel : getDelegatedCodeAddress code = none) :
    (M).benv.stat.rules.delegationCost
      (Devm.balReadAccount (M).benv.stat.rules target
        (initDevm M)) target = (false, target, 0) := by
  have hen : (M).benv.stat.rules.delegationEnabled = true := by
    rw [amsterdam_rules (s := (M).benv.stat) hfork]
    rfl
  simp only [ForkRules.delegationCost, hen, ↓reduceIte, GasSchedule.delegationCost]
  show (match getDelegatedCodeAddress (benv.state.getCode target) with
    | some delegated => _
    | none => _) = _
  rw [installed, hdel]

private theorem prepare_system (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode target = code)
    (hdel : getDelegatedCodeAddress code = none) :
    prepareTopLevelAmsterdam amsterdamStateGasRules M =
      .ok (M, systemCallBase M) := by
  unfold prepareTopLevelAmsterdam finishTopLevelAmsterdam dispatchTopLevelAmsterdam
    resolveTopLevelCallAmsterdam
  have hauth : (M).tenv.stat.auths.isEmpty = true := rfl
  have htarget : (M).target.isNone = false := rfl
  have hvalue : ((M).value != 0) = false := by
    show ((0 : B256) != 0) = false
    simp only [bne_self_eq_false]
  have hcost := delegationCost_system (data := data) hfork installed hdel
  have hz : ∀ d : Devm, chargeGas 0 d = .ok d := fun d => by
    rw [chargeGas_eq_ok (Nat.zero_le _)]
    rfl
  simp only [hauth, ↓reduceIte]
  simp only [htarget, Bool.false_eq_true, ↓reduceIte]
  simp only [hvalue, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, Except.bind]
  rw [show (M).currentTarget = target from rfl, hcost]
  simp only [hz, completeDelegationAccess, Bool.false_eq_true, ↓reduceIte]
  rw [show (Devm.balReadAccount (M).benv.stat.rules target
      (Devm.balReadAccount (M).benv.stat.rules target
        (initDevm M))) = systemCallBase M from rfl,
    preparedTopLevelMsg_system]
  show Except.ok ({ M with code := benv.state.getCode target },
    systemCallBase M) = _
  rw [installed]
  rfl

private theorem runPrepared_system (hfork : benv.stat.fork = .amsterdam)
    (hprecomp : ¬ amsterdamRules.isPrecomp target) {post : Devm}
    (run : exec ⟨0, initSevm M, systemCallBase M⟩ =
      .ok post)
    (clean : post.error = none) :
    runPreparedTopFrame (Frame.ofCall M)
      (systemCallBase M) = .ok post := by
  have hrules := amsterdam_rules (s := (M).benv.stat) hfork
  have hnot : ¬ (M).benv.stat.rules.isPrecomp target := by
    rw [hrules]
    exact hprecomp
  have hsweep : (M).benv.stat.rules.settle.touchedSweep = false := by
    rw [hrules]
    rfl
  have hentry : (M).benvAfterTransfer = .ok (M).benv :=
    Msg.benvAfterTransfer_of_value_zero rfl
  have hbal : (M).benv.stat.rules.bal.isSome = true := by
    rw [hrules]
    rfl
  have hdyna : (((systemCallBase M).withState
      (M).benv.state).withStorageWrites
      (M).benv.storageWrites).withCreatedAccounts
        (M).benv.createdAccounts =
      systemCallBase M := by
    unfold systemCallBase Devm.balReadAccount
    simp only [hbal, ↓reduceIte]
    rfl
  unfold runPreparedTopFrame
  have hinner : (Frame.ofCall M).inner = M := rfl
  rw [hinner, hentry]
  show (Frame.ofCall M).settle
    (if (!false && (M).benv.stat.rules.isPrecomp target) = true then
      executePrecomp ⟨0, initSevm M,
        (((systemCallBase M).withState
          (M).benv.state).withStorageWrites
          (M).benv.storageWrites).withCreatedAccounts
            (M).benv.createdAccounts⟩ target
    else exec ⟨0, initSevm M,
        (((systemCallBase M).withState
          (M).benv.state).withStorageWrites
          (M).benv.storageWrites).withCreatedAccounts
            (M).benv.createdAccounts⟩) = _
  simp only [Bool.not_false, Bool.true_and, hnot, decide_false, Bool.false_eq_true, ite_false]
  rw [hdyna, run]
  unfold Frame.settle Frame.settleMsg
  simp only [Frame.ofCall, Bool.false_eq_true, ite_false]
  show processMessage.settle M (executeCode.handleErrorWith
    (M).benv.stat.rules.stateGas (.ok post)) = _
  rw [show (M).benv.stat.rules.stateGas = some amsterdamStateGasRules from
    amsterdam_stateGas hfork]
  simp only [executeCode.handleErrorWith, executeCode.handleErrorAmsterdam,
    processMessage.settle, bind, Except.bind, clean, Option.isSome_none, Bool.false_eq_true,
    ite_false, Devm.recordTouch_of_not_touchedSweep hsweep]

/-! ## The envelope -/

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
  have hsg := amsterdam_stateGas (s := (M).benv.stat) hfork
  show processMessageCall.call M = _
  unfold processMessageCall.call
  rw [hsg]
  simp only
  unfold processTopLevelAmsterdam
  rw [prepare_system hfork installed hdel]
  simp only [bind, Except.bind]
  rw [runPrepared_system hfork hprecomp run clean]
  simp only [Except.bimap, id]
  unfold msgCallOutputAmsterdam
  simp only [clean, Option.isNone_none, ↓reduceIte, bind, Except.bind,
    Int.toNat?_eq_some_of_nonneg nonneg, Option.toExcept]
  rfl

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
