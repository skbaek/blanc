import Blanc.Lift.WithdrawalRequest.Creation.Check
import Blanc.Lift.WithdrawalRequest.Creation.Walk
import Blanc.Lift.WithdrawalRequest.Creation.Init
import Blanc.Lift.WithdrawalRequest.Creation.Address

/-! Actual modeled CREATE installs the canonical runtime and inhibitor state.
This is message execution, without a historical inclusion or signature claim. -/

namespace Blanc.Lift.WithdrawalRequest.Creation

open Jaune Blanc.Lift Blanc.WithdrawalRequest

/-- Canonical construction under its actual selected rule capabilities, including Cancun.
The runtime, initial storage and settlement bookkeeping are execution results. The gas
requirement covers the 22217 constructor bound plus the 100800 runtime deposit. -/
theorem create_initialH (msg : Msg)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hpush0 : msg.benv.stat.rules.op.push0 = true)
    (hflat : ∀ g, msg.benv.stat.rules.access = .flat g → g.sload ≤ 2100)
    (hsize : 504 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (haddress : msg.codeAddress = none) (hcode : msg.code = creationCode)
    (hstatic : msg.isStatic = false) (hvalue : msg.value = 0) (hgas : 123017 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧
      post.getCode msg.currentTarget = Blanc.withdrawalRequestCode ∧
      RepresentsStorage (post.getStor msg.currentTarget).get initial ∧ post.error = none ∧
      post.accountsToDelete = msg.inheritedDeletions ∧ post.refundCounter = 0 := by
  obtain ⟨benv, htransfer⟩ := benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  let sevm := initSevm (createSeed msg benv)
  let b := initDevm (createSeed msg benv)
  let G := msg.gas - constructorGas sevm b
  have hstat : sevm.benvStat = msg.benv.stat := by
    change benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have hflatSevm : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 2100 := by
    rw [hstat]
    exact hflat
  have hcost : constructorGas sevm b ≤ msg.gas :=
    Nat.le_trans (constructorGas_le sevm b hflatSevm) (Nat.le_trans (by decide) hgas)
  have hremaining : 100800 ≤ G := by
    apply Nat.le_sub_of_add_le
    exact Nat.le_trans (Nat.add_le_add_left (constructorGas_le sevm b hflatSevm) 100800)
      (Nat.le_trans (by decide) hgas)
  have hsentry : gCallStipend < G := Nat.lt_of_lt_of_le (by decide) hremaining
  have hrun := constructor_runH sevm b G (hstat ▸ hsg) (hstat ▸ hpush0) hstatic hcode hsentry
  have hpre : St b [] Mem.empty (G + constructorGas sevm b) = b :=
    pre_eq_St rfl rfl (Nat.sub_add_cancel hcost)
  rw [hpre] at hrun
  have facts := constructorPost_facts sevm b G
  have hvalue0 : (processCreateMessage.msg msg).value = 0 := hvalue
  have hempty : b.getStor sevm.currentTarget = Stor.empty := by
    change benv.state.getStor msg.currentTarget = Stor.empty
    rw [benvAfterTransfer_ok_getStor htransfer _ (Or.inl hvalue0),
      processCreateMessage_msg_getStor_currentTarget]
  have herror : (constructorPost sevm b G).error = none := facts.2.1.trans rfl
  have hprefix : (constructorPost sevm b G).output.head? ≠ some 0xEF := by
    rw [facts.1]
    unfold Blanc.withdrawalRequestCode
    rw [ByteArray.toList_eq_toList_data, List.toList_toArray]
    decide
  have hdeposit : (constructorPost sevm b G).output.length * gasCodeDeposit ≤
      (constructorPost sevm b G).gasLeft := by
    rw [facts.1, runtime_length, facts.2.2.2]
    exact hremaining
  have hmax : (constructorPost sevm b G).output.length ≤ msg.benv.stat.rules.code.maxCodeSize := by
    rw [facts.1, runtime_length]
    exact hsize
  obtain ⟨post, hcreate, hinstalled, hstorage, hposterror⟩ := liftCreate_okH cert_check jumps_ok msg
    haddress hcode hsg htransfer hrun herror hprefix hdeposit hmax
  have hnamed := liftCreate_postH cert_check jumps_ok msg haddress hcode hsg htransfer
    hrun herror hprefix hdeposit hmax
  have hpostEq := Except.ok.inj (hcreate.symm.trans hnamed)
  refine ⟨post, hcreate, ?_, ?_, hposterror, ?_, ?_⟩
  · rw [facts.1] at hinstalled
    rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at hinstalled
    exact congrArg ByteArray.mk (Array.toList_inj.mp hinstalled)
  · rw [hstorage, facts.1]
    have hne : (⟨⟨Blanc.withdrawalRequestCode.toList⟩⟩ : ByteArray).size ≠ 0 := by
      show (List.toArray Blanc.withdrawalRequestCode.toList).size ≠ 0
      rw [List.size_toArray, runtime_length]
      decide
    have hnotempty : ¬ ({ (constructorPost sevm b G).state.get msg.currentTarget with
        code := ⟨⟨Blanc.withdrawalRequestCode.toList⟩⟩ } : Acct).Empty :=
      fun hacc => hne hacc.1
    rw [Acct.clearIfEmpty_stor, ite_eq_right hnotempty]
    change RepresentsStorage (constructorPost sevm b G |>.getStor sevm.currentTarget).get initial
    rw [facts.2.2.1, hempty]
    exact initial_storage
  · rw [hpostEq, (liftCreatePost_meta _ _).1, (recordTouch_meta _ _ _ _).1,
      constructorPost_accountsToDelete]
    rfl
  · have h0 : (processCreateMessage.msg msg).benvAfterTransfer =
        .ok (processCreateMessage.msg msg).benv :=
      Msg.benvAfterTransfer_of_value_zero hvalue0
    have hbenv_eq : benv = (processCreateMessage.msg msg).benv :=
      Except.ok.inj (htransfer.symm.trans h0)
    have hmem : sevm.currentTarget ∈ b.createdAccounts := by
      have h1 : b.createdAccounts = benv.createdAccounts := rfl
      rw [h1, hbenv_eq]
      show msg.currentTarget ∈ (processCreateMessage.msg msg).benv.createdAccounts
      unfold processCreateMessage.msg addCreatedAccount
      show msg.currentTarget ∈ (msg.benv.createdAccounts.insert msg.currentTarget)
      exact Std.HashSet.mem_insert_self
    have horig : b.getOrigStorVal sevm sevm.currentTarget 0 = 0 := by
      unfold Devm.getOrigStorVal
      rw [ite_eq_left hmem]
    rw [hpostEq, (liftCreatePost_meta _ _).2.1, (recordTouch_meta _ _ _ _).2.1,
      constructorPost_refundCounter sevm b G horig]
    rfl

end Blanc.Lift.WithdrawalRequest.Creation
