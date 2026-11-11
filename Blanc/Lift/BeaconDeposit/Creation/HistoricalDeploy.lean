import Blanc.Lift.BeaconDeposit.Creation.HistoricalTxRaw
import Blanc.TransactionForward
import Blanc.Lift.BeaconDeposit.Creation.HistoricalWalk

/-! Historical transaction gas uses the actual recovered legacy record. The transaction
and block pre-state are supplied by a later producer. -/

namespace Blanc.Lift.BeaconDeposit.Creation.HistoricalTx

open Jaune

/-- Muir intrinsic gas of the exact constructor payload is at most 53,000 plus
sixteen gas per byte. No calldata floor or init-code word charge applies. -/
theorem muir_intrinsic_le (sender : Adr) :
    (calculateIntrinsicCost muirGlacierRules tx sender).1 ≤ 159128 ∧
      (calculateIntrinsicCost muirGlacierRules tx sender).2 = 0 := by
  exact calculateIntrinsicCost_legacy_create_le (tx := tx) (sender := sender)
    (price := 147000000000) (n := 6633) rfl rfl rfl rfl rfl rfl rfl
    (Nat.le_of_eq data_length)

/-- Actual transaction message allocation, derived without unfolding its concrete payload. -/
theorem muir_allocation_bounds (sender : Adr) :
    2982464 ≤ (allocateEvmGas muirGlacierRules tx.gas
      (calculateIntrinsicCost muirGlacierRules tx sender).1).executionGas ∧
    (allocateEvmGas muirGlacierRules tx.gas
      (calculateIntrinsicCost muirGlacierRules tx sender).1).executionGas ≤ 3141592 ∧
    (allocateEvmGas muirGlacierRules tx.gas
      (calculateIntrinsicCost muirGlacierRules tx sender).1).stateGasReservoir = 0 :=
  allocateEvmGas_bounds_of_intrinsic_le (rules := muirGlacierRules)
    (txGas := 3141592) (intrinsic := (calculateIntrinsicCost muirGlacierRules tx sender).1)
    (cap := 159128) rfl (muir_intrinsic_le sender).1

/-- The actual transaction's message-gas allocation covers the re-derived historical
constructor bound, including the code-deposit reserve. -/
theorem muir_gas_sufficient (sender : Adr) :
    Historical.need 0 + 45 ≤ (allocateEvmGas muirGlacierRules tx.gas
      (calculateIntrinsicCost muirGlacierRules tx sender).1).executionGas ∧
    (allocateEvmGas muirGlacierRules tx.gas
      (calculateIntrinsicCost muirGlacierRules tx sender).1).executionGas < 2 ^ 64 + 45 := by
  have h := muir_allocation_bounds sender
  exact ⟨le_trans (by decide) h.1, lt_of_le_of_lt h.2.1 (by decide)⟩


end Blanc.Lift.BeaconDeposit.Creation.HistoricalTx

namespace Blanc.Lift.BeaconDeposit.Creation

open Jaune Blanc.BeaconDeposit Blanc.Lift.BeaconDeposit

/-- Real Muir Glacier CREATE-message execution of the certified constructor. The message
and pre-state remain explicit; this proves no transaction inclusion or block suffix result. -/
theorem beacon_create_muir_meta (msg : Msg) (hvalue : msg.value = 0) (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code = code) (hgas : Historical.need 0 + 45 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64 + 45)
    (hmuir : msg.benv.stat.rules = muirGlacierRules) (hstatic : msg.isStatic = false)
    (hdepth : msg.depth ≠ 0) (hmax : 6358 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv (Devm.getStor post msg.currentTarget) [] ∧
      post.error = none ∧ post.refundCounter = 0 ∧ post.logs = [] ∧
      post.accountsToDelete = msg.inheritedDeletions := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  set sevm := initSevm (createSeed msg benv) with hsevm
  set b := initDevm (createSeed msg benv) with hb
  have hstat : sevm.benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have hrules : sevm.benvStat.rules = muirGlacierRules := by rw [hstat]; exact hmuir
  have st : Historical.CtorStart sevm b := by
    refine ⟨hcode, hvalue, fun x => ?_, rfl⟩
    · show (benv.state.getStor msg.currentTarget).get x = 0
      rw [benvAfterTransfer_ok_getStor htransfer _
          (Or.inl (show (processCreateMessage.msg msg).value = 0 from hvalue)),
        processCreateMessage_msg_getStor_currentTarget]
      rfl
  have hinit : CreateRunMeta sevm.currentTarget msg.inheritedDeletions b := by
    refine ⟨rfl, ?_, rfl, ?_⟩
    · change (initDevm (createSeed msg benv)).logs = []
      exact initDevm_logs (by
        change sevm.benvStat.rules.stateGas = none
        rw [hrules]
        rfl)
    · have heq := Msg.benvAfterTransfer_of_value_zero
        (msg := processCreateMessage.msg msg) hvalue
      have hbenv : benv = (processCreateMessage.msg msg).benv :=
        Except.ok.inj (htransfer.symm.trans heq)
      change msg.currentTarget ∈ benv.createdAccounts
      rw [hbenv]
      change msg.currentTarget ∈ msg.benv.createdAccounts.insert msg.currentTarget
      exact Std.HashSet.mem_insert_self
  obtain ⟨raw, hrun, hdone, hmetadata⟩ :=
    Historical.ctor_run_meta hrules hdepth hstatic st (G := msg.gas - 45) (by omega) (by omega)
  obtain ⟨hout, herr, hstor, hgasLeft, -⟩ := hdone
  have hmeta := hmetadata msg.inheritedDeletions hinit
  have hpre0 : St b [] Mem.empty (msg.gas - 45 + 45) = b :=
    pre_eq_St rfl rfl (by show msg.gas - 45 + 45 = msg.gas; omega)
  rw [hpre0] at hrun
  have hwin : raw.output = Blanc.Lift.BeaconDeposit.code.toList := by
    rw [hout, runtimeWindow, ByteArray.sliceD_eq]
    exact runtime_window
  have hlen : raw.output.length = 6358 := by rw [hout]; exact runtimeWindow_length
  obtain ⟨post, hpost, hcodePost, hstorPost, herror⟩ := liftCreate_okH cert_check jumps_ok msg
    hcodeAddress hcode (by rw [hmuir]; rfl) htransfer hrun herr
    (by rw [hwin, ByteArray.toList_eq_toList_data]; decide) (by rw [hlen]; exact le_trans (by decide) hgasLeft)
    (by rw [hlen]; exact hmax)
  have hexact := liftCreate_postH cert_check jumps_ok msg
    hcodeAddress hcode (by rw [hmuir]; rfl) htransfer hrun herr
    (by rw [hwin, ByteArray.toList_eq_toList_data]; decide)
    (by rw [hlen]; exact le_trans (by decide) hgasLeft) (by rw [hlen]; exact hmax)
  have hpostEq : post = liftCreatePost msg.currentTarget
      (raw.recordTouch msg.benv.stat.rules true msg.currentTarget) :=
    Except.ok.inj (hpost.symm.trans hexact)
  have hrefund : post.refundCounter = 0 := by
    rw [hpostEq]
    exact hmeta.refund
  have hlogs : post.logs = [] := by
    rw [hpostEq]
    exact hmeta.logs
  have hdeletions : post.accountsToDelete = msg.inheritedDeletions := by
    rw [hpostEq]
    exact hmeta.deletions
  have hcode_ne :
      ({ raw.state.get msg.currentTarget with code := ⟨⟨raw.output⟩⟩ } : Acct).code.size ≠ 0 := by
    show (⟨⟨raw.output⟩⟩ : ByteArray).size ≠ 0
    have hsize : (⟨⟨raw.output⟩⟩ : ByteArray).size = raw.output.length := rfl
    rw [hsize, hlen]
    decide
  refine ⟨post, hpost, hcodePost.trans hwin, ?_, herror, hrefund, hlogs, hdeletions⟩
  rw [hstorPost, Acct.clearIfEmpty_stor, ite_eq_right (fun hE => hcode_ne hE.1)]
  exact solInv_of_ctorStor hstor

/-- Compatibility projection of historical creation without settlement metadata. -/
theorem beacon_create_muir (msg : Msg) (hvalue : msg.value = 0) (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code = code) (hgas : Historical.need 0 + 45 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64 + 45)
    (hmuir : msg.benv.stat.rules = muirGlacierRules) (hstatic : msg.isStatic = false)
    (hdepth : msg.depth ≠ 0) (hmax : 6358 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv (Devm.getStor post msg.currentTarget) [] := by
  obtain ⟨post, run, installed, inv, -⟩ := beacon_create_muir_meta msg hvalue hcodeAddress hcode
    hgas hgasb hmuir hstatic hdepth hmax
  exact ⟨post, run, installed, inv⟩


end Blanc.Lift.BeaconDeposit.Creation
