import Blanc.Lift.WithdrawalRequest.Creation.Check
import Blanc.Lift.WithdrawalRequest.Creation.Walk
import Blanc.Lift.WithdrawalRequest.Creation.Init
import Blanc.Lift.WithdrawalRequest.Creation.Address

/-! Actual modeled CREATE installs the canonical runtime and inhibitor state.
This is message execution, without a historical inclusion or signature claim. -/

namespace Blanc.Lift.WithdrawalRequest.Creation

open Jaune Blanc.Lift Blanc.WithdrawalRequest

theorem create_initial (msg : Msg) (hfork : CoveredFork msg.benv.stat.fork)
    (haddress : msg.codeAddress = none) (hcode : msg.code = creationCode)
    (hstatic : msg.isStatic = false) (hvalue : msg.value = 0) (hgas : 250000 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧
      post.getCode msg.currentTarget = Blanc.withdrawalRequestCode ∧
      RepresentsStorage (post.getStor msg.currentTarget).get initial ∧ post.error = none := by
  obtain ⟨benv, htransfer⟩ := benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  let sevm := initSevm (createSeed msg benv)
  let b := initDevm (createSeed msg benv)
  let G := msg.gas - constructorGas sevm b
  have hstat : sevm.benvStat = msg.benv.stat := by
    change benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have hcost : constructorGas sevm b ≤ msg.gas :=
    Nat.le_trans (constructorGas_le sevm b) (Nat.le_trans (by decide) hgas)
  have hremaining : 100800 ≤ G := by
    apply Nat.le_sub_of_add_le
    exact Nat.le_trans (Nat.add_le_add_left (constructorGas_le sevm b) 100800)
      (Nat.le_trans (by decide) hgas)
  have hsentry : gCallStipend < G := Nat.lt_of_lt_of_le (by decide) hremaining
  have hrun := constructor_run sevm b G (hstat ▸ hfork) hstatic hcode hsentry
  have hpre : St b [] Mem.empty (G + constructorGas sevm b) = b :=
    pre_eq_St rfl rfl (Nat.sub_add_cancel hcost)
  rw [hpre] at hrun
  have facts := constructorPost_facts sevm b G
  have hempty : b.getStor sevm.currentTarget = Stor.empty := by
    change benv.state.getStor msg.currentTarget = Stor.empty
    rw [benvAfterTransfer_ok_getStor htransfer, processCreateMessage_msg_getStor_currentTarget]
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
    exact CoveredFork.cases (motive := fun f => 504 ≤ (Fork.ruleSet f).code.maxCodeSize)
      hfork (by decide) (by decide) (by decide) (by decide)
  obtain ⟨post, hcreate, hinstalled, hstorage, hposterror⟩ := liftCreate_ok cert_check jumps_ok msg
    haddress hcode hfork htransfer hrun herror hprefix hdeposit hmax
  refine ⟨post, hcreate, ?_, ?_, hposterror⟩
  · rw [facts.1] at hinstalled
    rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at hinstalled
    exact congrArg ByteArray.mk (Array.toList_inj.mp hinstalled)
  · rw [hstorage]
    change RepresentsStorage (constructorPost sevm b G |>.getStor sevm.currentTarget).get initial
    rw [facts.2.2.1, hempty]
    exact initial_storage

/-- A closed zero-value CREATE message with the recorded sender and nonce-zero target.
The gas grant is the retained deployment input's 250000; transaction validation is separate. -/
def deployMsg (fork : Fork) : Msg where
  benv := { (default : Benv) with stat := { (default : BenvStat) with fork := fork } }
  tenv := default
  caller := deployer
  target := none
  currentTarget := computeContractAddress deployer 0
  gas := 250000
  value := 0
  data := []
  codeAddress := none
  code := creationCode
  depth := 0
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

theorem deployMsg_fresh (fork : Fork) :
    (deployMsg fork).benv.state.getNonce deployer = 0 ∧
    (deployMsg fork).benv.state.getNonce (deployMsg fork).currentTarget = 0 ∧
    (deployMsg fork).benv.state.getCode (deployMsg fork).currentTarget = ByteArray.empty := by
  exact ⟨rfl, rfl, rfl⟩

/-- Every covered fork admits the closed constructor message and reaches actual INIT. -/
theorem deploy_initial (fork : Fork) (hfork : CoveredFork fork) :
    (deployMsg fork).currentTarget = withdrawalRequestPredeployAddress ∧
    ∃ post, processCreateMessage (deployMsg fork) = .ok post ∧
      post.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      RepresentsStorage (post.getStor withdrawalRequestPredeployAddress).get initial ∧
      post.error = none := by
  have target : (deployMsg fork).currentTarget = withdrawalRequestPredeployAddress := deployer_address
  refine ⟨target, ?_⟩
  obtain ⟨post, hcreate, hcode, hstorage, herror⟩ := create_initial (deployMsg fork) hfork rfl rfl rfl rfl (Nat.le_refl _)
  rw [target] at hcode hstorage
  exact ⟨post, hcreate, hcode, hstorage, herror⟩

end Blanc.Lift.WithdrawalRequest.Creation
