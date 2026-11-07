import Blanc.Lift.BuilderRequest.AmsterdamMsgProbeCall
import Blanc.Lift.BuilderRequest.Deposit.Creation.Address
import Blanc.ConcreteRun

/-!
# Probe: `deposit_call_ok` at a closed message

Disposable (goal `blanc-eip8282-builder-requests-v1`, O16). An explicit pre-state: a depositor with 2^100
wei and the deposit code at its address with empty storage. `call_ok` meets every premise of
`deposit_call_ok`. Gas goes through a bound, not evaluation: a closed `SLOAD` cost tests a `HashSet` of keys
and `mixHash` is opaque, so the kernel cannot read it.
-/

namespace Blanc.Lift.BuilderRequest.AmsterdamMsgProbe.Witness

open Jaune
open Blanc.Lift.BuilderRequest.Deposit

def depositor : Adr := 0x1234

def preState : State :=
  Jaune.State.setPresent (Jaune.State.setPresent .empty depositor
      { nonce := 1, bal := (2 ^ 100 : Nat).toB256, stor := .empty, code := .empty })
    Creation.address { nonce := 1, bal := 0, stor := .empty, code := Deposit.code }

def preBenv : Benv :=
  { (default : Benv) with
    state := preState
    stat := { (default : Benv).stat with fork := .amsterdam, origState := preState, blockGasLimit := 60000000 } }

def callMsg (value : Nat) : Msg :=
  { (default : Msg) with
    benv := preBenv
    caller := depositor
    target := some Creation.address
    currentTarget := Creation.address
    gas := 1000000
    value := value.toB256
    data := List.replicate 184 0xff
    codeAddress := some Creation.address
    code := Deposit.code
    depth := 1024
    shouldTransferValue := true
    isStatic := false
    accessedAddresses := (Std.HashSet.emptyWithCapacity.insert depositor).insert Creation.address
    disablePrecompiles := false
    stateGasGrant := 800000 }

/-- Enough for all-ones calldata: the credit plus the fee of one wei. -/
def goodValue : Nat := (2 ^ 64 - 1) * 10 ^ 9 + 1

def afterOf (m : Msg) : Benv := match m.benvAfterTransfer with | .ok b => b | _ => default

def okMsg : Msg := callMsg goodValue
abbrev okS : Sevm := userSevm okMsg Deposit.code (afterOf okMsg)
abbrev okE : Devm := userEntry okMsg (afterOf okMsg)

theorem logGas_closed : logGas okS .empty = 375 + 8 * 184 := by kernel_rfl
theorem copyGas_closed : Deposit.copyGas (.empty : Mem) = 3 + 3 * 6 + 18 := by decide +kernel

local notation "Bd" => gasColdSload + amsterdamStateGasRules.storageWrite

theorem rec_le (s : Sevm) (d : Devm) (K : B256) : recordWritesGasA s d K ≤ Bd + Bd + Bd + Bd + Bd + Bd :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (sstoreCostA_le _ _ _ _ _) (sstoreCostA_le _ _ _ _ _)) (sstoreCostA_le _ _ _ _ _))
    (sstoreCostA_le _ _ _ _ _)) (sstoreCostA_le _ _ _ _ _)) (sstoreCostA_le _ _ _ _ _)

theorem body_le (s : Sevm) (d : Devm) (M : Mem) : bodyGasA s d M ≤
    136 + gasColdSload + Bd + gasColdSload + (Bd + Bd + Bd + Bd + Bd + Bd) + Deposit.copyGas M + logGas s M + Bd :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.le_refl 136) (sloadCost_le _ _ _)) (sstoreCostA_le _ _ _ _ _))
    (sloadCost_le _ _ _)) (rec_le _ _ _)) (Nat.le_refl _)) (Nat.le_refl _)) (sstoreCostA_le _ _ _ _ _)

/-- The charge, bounded from the rule record. -/
theorem okGas_le : submissionGasA okS okE .empty 1 ≤ 150000 := by
  have hb := body_le okS (Deposit.feeBaseA okS okE) .empty
  have h1 := sloadCost_le okS okE 0
  have h2 := sloadCost_le okS (afterSloadA okS okE 0) 1
  have hcold : gasColdSload = 2100 := rfl
  have hw : amsterdamStateGasRules.storageWrite = 10000 := rfl
  have hloop : RequestFee.feeLoopGas 1 ≤ 1000 := by decide
  have hd : RequestSystem.dispatchGas = 21 := rfl
  have hf : feePathFixedGas = 133 := rfl
  rw [copyGas_closed, logGas_closed] at hb
  simp only [submissionGasA, feePathGasA]
  omega

def okG : Nat := 1000000 - submissionGasA okS okE .empty 1

theorem okG_eq : okG = 1000000 - submissionGasA okS okE .empty 1 := rfl

attribute [local irreducible] okG submissionGasA

theorem okE_slot (k : B256) (h : (okE.getStor Creation.address) = .empty) :
    okE.getStorVal Creation.address k = 0 := by
  show (okE.getStor Creation.address).get k = 0
  rw [h]
  rfl

theorem okE_stor : okE.getStor Creation.address = .empty := by kernel_rfl

theorem ok_tail : tailWordA okS (Deposit.feeBaseA okS okE) = 0 := by
  rw [tailWordA_eq]
  unfold Deposit.feeBaseA
  rw [afterSloadA_getStorVal, afterSloadA_getStorVal]
  exact okE_slot 3 okE_stor

/-- **`deposit_call_ok` has a model.** -/
theorem call_ok :
    let post := submissionPostA okS (Deposit.feeBaseA okS okE) .empty okG
    processMessageCall okMsg = .ok (post.state, systemCallOutputA okMsg post) ∧
      post.state = submittedState okS (afterOf okMsg).state ∧
      post.logs = (initDevm okMsg).logs ++ [⟨Creation.address, [], List.replicate 184 0xff⟩] ∧
      post.gasLeft = okG ∧ post.stateGas.spilled = 0 ∧ 16640 ≤ post.stateGas.left := by
  have excess : storedExcess 8 okS okE = 0 := by kernel_rfl
  have hle := okGas_le
  have hgas : okMsg.gas = okG + submissionGasA okS okE .empty 1 := by
    show 1000000 = _
    rw [okG_eq]
    omega
  have hstip : gCallStipend < okG := by
    have : gCallStipend = 2300 := rfl
    rw [okG_eq]
    omega
  refine deposit_call_ok (M' := okMsg) (benv := afterOf okMsg) (G := okG) (iterations := 1) (finalOutput := 17) (X := 16640) rfl rfl rfl (by kernel_rfl)
    (by kernel_rfl) (by decide +kernel) (by kernel_rfl) (by kernel_rfl) (by decide +kernel) rfl rfl
    hstip hgas ?_ (by rw [show storedExcess 8 _ _ = (0 : B256) from excess]; exact quote_zero_excess)
    ?_ (by decide +kernel) ?_ ?_
  · rw [show (userEntry okMsg (afterOf okMsg)).getStorVal okMsg.currentTarget 0 = 0 from
      okE_slot 0 okE_stor]
    decide +kernel
  · rw [show (17 : B256) / (17 : B256) = 1 by decide]
    exact admitted_witness rfl (by decide +kernel)
  · intro k
    refine Or.inr ?_
    unfold Devm.getOrigStorVal
    split
    · rfl
    · unfold Jaune.getOrigStorVal
      rw [show (getOrigAcct okS okS.currentTarget).stor = .empty by kernel_rfl]
      rfl
  · rw [show tailWordA (userSevm okMsg Deposit.code (afterOf okMsg))
        (Deposit.feeBaseA (userSevm okMsg Deposit.code (afterOf okMsg))
          (userEntry okMsg (afterOf okMsg))) = 0 from ok_tail]
    decide +kernel

/-- The world after the call: the balances moved at frame entry and the frame moved none. -/
theorem call_ok_balances :
    (((afterOf okMsg).state.get depositor).bal).toNat = 2 ^ 100 - goodValue ∧
      (((afterOf okMsg).state.get Creation.address).bal).toNat = goodValue := by
  refine ⟨by kernel_rfl, by kernel_rfl⟩

theorem call_ok_logs :
    (initDevm okMsg).logs =
      [transferLog depositor Creation.address goodValue.toB256] :=
  initDevm_logs_transfer rfl rfl (by decide +kernel) (by decide +kernel)

end Blanc.Lift.BuilderRequest.AmsterdamMsgProbe.Witness
