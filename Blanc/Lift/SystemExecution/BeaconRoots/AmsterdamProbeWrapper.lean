import Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbeWalk

/-!
# W1 probe, step 3: the top-level Amsterdam wrapper over the EIP-4788 frame

Probe only; does not land. `open private` reaches Jaune's private top-level path.
-/

namespace Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe

open Jaune
open Blanc.Lift

open private runPreparedTopFrame msgCallOutputAmsterdam from Jaune.Transaction

/-! ## Observers of `afterSstoreA` -/

theorem afterSstoreA_state (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstoreA state sevm b k v).state = b.state.setStorVal sevm.currentTarget k v := by
  unfold afterSstoreA
  split <;> rfl

theorem balReadAccount_error (r : ForkRules) (a : Adr) (d : Devm) :
    (d.balReadAccount r a).error = d.error := by
  unfold Devm.balReadAccount
  split <;> rfl

theorem balReadStorage_error (r : ForkRules) (a : Adr) (k : B256) (d : Devm) :
    (d.balReadStorage r a k).error = d.error := by
  unfold Devm.balReadStorage
  split <;> rfl

theorem afterSstoreA_error (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstoreA state sevm b k v).error = b.error := by
  unfold afterSstoreA
  dsimp only
  show (Devm.balReadAccount _ _ _).error = _
  rw [balReadAccount_error]
  show (Devm.balReadStorage _ _ _ _).error = _
  rw [balReadStorage_error]
  split <;> rfl

theorem afterSstoreA_refundCounter (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstoreA state sevm b k v).refundCounter =
      sstoreAmsterdamRefundCounter sevm.benvStat.rules.gas state v
        (b.getOrigStorVal sevm sevm.currentTarget k) (b.getStorVal sevm.currentTarget k)
        b.refundCounter := by
  unfold afterSstoreA
  dsimp only
  show (Devm.balReadAccount _ _ _).refundCounter = _
  rw [Devm.balReadAccount_refundCounter]
  rfl

/-- The Amsterdam refund never lowers the counter on a slot not changed earlier in the
transaction. Hoist debt: generic, the Amsterdam `RefundSafe`. -/
theorem sstoreAmsterdamRefund_ge (gas : GasSchedule) (state : StateGasRules) {v o c : B256}
    {rc : Int} (h : o = c ∨ o = 0) :
    rc ≤ sstoreAmsterdamRefundCounter gas state v o c rc := by
  unfold sstoreAmsterdamRefundCounter
  by_cases hcv : c ≠ v
  · rw [if_pos hcv]
    simp only
    have h1 : ¬ (o ≠ 0 ∧ c = 0) := by
      rintro ⟨ho, hc⟩
      rcases h with h | h
      · exact ho (h.trans hc)
      · exact ho h
    rw [if_neg h1]
    split <;> split <;> omega
  · rw [if_neg hcv]

/-! ## The frame's post-facts -/

section post

variable (benv : Benv)

/-- The frame's static machine and prepared base. -/
abbrev SA := systemSevm benv
abbrev BA := preparedBase benv

/-- The prepared base carries the initial meter and refund. -/
theorem BA_refund : (BA benv).refundCounter = 0 := by
  simp only [preparedBase, Devm.balReadAccount_refundCounter]
  rfl

/-- The Amsterdam halted frame on the prepared base. -/
def postB : Devm := postA (SA benv) (BA benv)

theorem postB_error : (postB benv).error = none := by
  show (endA (SA benv) (BA benv)).error = none
  rw [endA, afterSstoreA_error, midA, afterSstoreA_error]
  show (preparedBase benv).error = none
  simp only [preparedBase, balReadAccount_error]
  rfl

theorem postB_state : (postB benv).state =
    (benv.state.setStorVal beaconRootsAddress (keyA (SA benv)) (SA benv).benvStat.time).setStorVal
      beaconRootsAddress (rootKeyA (SA benv)) (Sevm.dataWord (SA benv) 0) := by
  show (endA (SA benv) (BA benv)).state = _
  rw [endA, afterSstoreA_state, midA, afterSstoreA_state]
  rfl

theorem postB_refund : 0 ≤ (postB benv).refundCounter := by
  show 0 ≤ (endA (SA benv) (BA benv)).refundCounter
  have s1 : (BA benv).getOrigStorVal (SA benv) (SA benv).currentTarget (keyA (SA benv)) =
        (BA benv).getStorVal (SA benv).currentTarget (keyA (SA benv)) ∨
      (BA benv).getOrigStorVal (SA benv) (SA benv).currentTarget (keyA (SA benv)) = 0 := by
    unfold Devm.getOrigStorVal
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have s2 : (midA (SA benv) (BA benv)).getOrigStorVal (SA benv) (SA benv).currentTarget
        (rootKeyA (SA benv)) =
        (midA (SA benv) (BA benv)).getStorVal (SA benv).currentTarget (rootKeyA (SA benv)) ∨
      (midA (SA benv) (BA benv)).getOrigStorVal (SA benv) (SA benv).currentTarget
        (rootKeyA (SA benv)) = 0 := by
    unfold Devm.getOrigStorVal
    split
    · exact Or.inr rfl
    · refine Or.inl ?_
      have hne : keyA (SA benv) ≠ rootKeyA (SA benv) := systemKey_ne benv
      have : (midA (SA benv) (BA benv)).getStorVal (SA benv).currentTarget (rootKeyA (SA benv)) =
          (BA benv).getStorVal (SA benv).currentTarget (rootKeyA (SA benv)) := by
        rw [getStorVal_eq_getStor, getStorVal_eq_getStor]
        unfold Devm.getStor Devm.getAcct
        rw [midA, afterSstoreA_state, State.get_setStorVal_self]
        exact Stor.get_set_ne _ hne _
      rw [this]
      rfl
  have h1 := sstoreAmsterdamRefund_ge (SA benv).benvStat.rules.gas A (v := (SA benv).benvStat.time)
    (rc := (BA benv).refundCounter) s1
  have h2 := sstoreAmsterdamRefund_ge (SA benv).benvStat.rules.gas A
    (v := Sevm.dataWord (SA benv) 0) (rc := (midA (SA benv) (BA benv)).refundCounter) s2
  rw [endA, afterSstoreA_refundCounter]
  refine le_trans ?_ h2
  rw [midA, afterSstoreA_refundCounter, ]
  refine le_trans ?_ h1
  rw [BA_refund]

/-- The raw frame from the prepared base. -/
theorem exec_prepared (hfork : benv.stat.fork = .amsterdam) :
    exec ⟨0, SA benv, St (BA benv) [] .empty systemTransactionGas⟩ = .ok (postB benv) := by
  refine system_execA hfork rfl rfl rfl rfl ?_
  have hs : (benv.beginTransaction).stat.rules.stateGas = some amsterdamStateGasRules :=
    amsterdam_stateGas hfork
  show 2 * A.storageSet ≤ (match (benv.beginTransaction).stat.rules.stateGas with
    | none => 0
    | some state => state.systemReservoir)
  rw [hs]
  decide

/-- **The prepared top frame settles to the post frame.** -/
theorem runPrepared_beacon (hfork : benv.stat.fork = .amsterdam) :
    runPreparedTopFrame (Frame.ofCall (systemMsg benv)) (BA benv) = .ok (postB benv) := by
  have hnot : ¬ (systemMsg benv).benv.stat.rules.isPrecomp beaconRootsAddress := by
    show ¬ (Fork.ruleSet (systemMsg benv).benv.stat.fork).isPrecomp beaconRootsAddress
    rw [show (systemMsg benv).benv.stat.fork = .amsterdam from hfork]
    decide
  have hsweep : (systemMsg benv).benv.stat.rules.settle.touchedSweep = false := by
    show (Fork.ruleSet (systemMsg benv).benv.stat.fork).settle.touchedSweep = false
    rw [show (systemMsg benv).benv.stat.fork = .amsterdam from hfork]
    rfl
  have hentry : (systemMsg benv).benvAfterTransfer = .ok (systemMsg benv).benv :=
    Msg.benvAfterTransfer_of_value_zero rfl
  have hbal : (systemMsg benv).benv.stat.rules.bal.isSome = true := by
    show (Fork.ruleSet (systemMsg benv).benv.stat.fork).bal.isSome = true
    rw [show (systemMsg benv).benv.stat.fork = .amsterdam from hfork]
    rfl
  have hdyna : (((BA benv).withState (systemMsg benv).benv.state).withStorageWrites
      (systemMsg benv).benv.storageWrites).withCreatedAccounts
        (systemMsg benv).benv.createdAccounts =
      St (BA benv) [] .empty systemTransactionGas := by
    show (((preparedBase benv).withState (systemMsg benv).benv.state).withStorageWrites
      (systemMsg benv).benv.storageWrites).withCreatedAccounts
        (systemMsg benv).benv.createdAccounts = St (preparedBase benv) [] .empty systemTransactionGas
    unfold preparedBase Devm.balReadAccount
    simp only [hbal, ↓reduceIte]
    rfl
  unfold runPreparedTopFrame
  have hinner : (Frame.ofCall (systemMsg benv)).inner = systemMsg benv := rfl
  rw [hinner, hentry]
  show (Frame.ofCall (systemMsg benv)).settle
    (if (!false && (systemMsg benv).benv.stat.rules.isPrecomp beaconRootsAddress) = true then
      executePrecomp ⟨0, SA benv,
        (((BA benv).withState (systemMsg benv).benv.state).withStorageWrites
          (systemMsg benv).benv.storageWrites).withCreatedAccounts
            (systemMsg benv).benv.createdAccounts⟩ beaconRootsAddress
    else exec ⟨0, SA benv, ((((BA benv).withState (systemMsg benv).benv.state).withStorageWrites
          (systemMsg benv).benv.storageWrites).withCreatedAccounts
            (systemMsg benv).benv.createdAccounts)⟩) = _
  simp only [Bool.not_false, Bool.true_and, hnot, decide_false, Bool.false_eq_true, ite_false]
  rw [hdyna, exec_prepared benv hfork]
  have hclean := postB_error benv
  unfold Frame.settle Frame.settleMsg
  simp only [Frame.ofCall, Bool.false_eq_true, ite_false]
  show processMessage.settle (systemMsg benv) (executeCode.handleErrorWith
    (systemMsg benv).benv.stat.rules.stateGas (.ok (postB benv))) = _
  rw [show (systemMsg benv).benv.stat.rules.stateGas = some amsterdamStateGasRules from
    amsterdam_stateGas hfork]
  simp only [executeCode.handleErrorWith, executeCode.handleErrorAmsterdam,
    processMessage.settle, bind, Except.bind, hclean, Option.isSome_none, Bool.false_eq_true,
    ite_false, Devm.recordTouch_of_not_touchedSweep hsweep]

end post

/-- **Step 3: the unchecked system call under Amsterdam** on the installed code. -/
theorem processUnchecked_beacon_amsterdam {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode beaconRootsAddress = beaconRootsCode) :
    ∃ out : MsgCallOutput,
      processUncheckedSystemTransaction benv beaconRootsAddress
          benv.stat.parentBeaconBlockRoot.toBytes = .ok ((postB benv).state, out) ∧
        out.error = none ∧ out.gasLeft = (postB benv).gasLeft ∧
        out.returnData = (postB benv).output ∧
        out.stateGasLeft = (postB benv).stateGasLeft := by
  have hsg := amsterdam_stateGas (s := (systemMsg benv).benv.stat) hfork
  have hclean := postB_error benv
  have hrefund := postB_refund benv
  show ∃ out : MsgCallOutput, processSystemTransaction benv beaconRootsAddress
      (benv.state.getCode beaconRootsAddress) benv.stat.parentBeaconBlockRoot.toBytes = _ ∧ _
  rw [installed]
  show ∃ out : MsgCallOutput, processMessageCall.call (systemMsg benv) = _ ∧ _
  unfold processMessageCall.call
  rw [hsg]
  simp only
  unfold processTopLevelAmsterdam
  rw [prepare_systemMsg hfork installed]
  simp only [bind, Except.bind]
  rw [runPrepared_beacon benv hfork]
  simp only [Except.bimap, id]
  unfold msgCallOutputAmsterdam
  simp only [hclean, Option.isNone_none, ↓reduceIte, bind, Except.bind,
    Int.toNat?_eq_some_of_nonneg hrefund, Option.toExcept]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

end Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe
