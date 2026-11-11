import Blanc.Composition.BuilderRequestClassification
import Blanc.Lift.SystemWordWriter
import Blanc.Lift.Witness
import Blanc.Lift.WithdrawalRequest.DrainTx
import Blanc.BlockForward
import Blanc.ConcreteRunKept

/-! A signed ordinary transaction entering SYSTEM code, whose actual children
exercise the builder latch followed by its dirty reset. The later block/history
assembly is separate; this module does not assert a synthetic history. -/

namespace Blanc.Composition.BuilderRequestApplicabilityCalls

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.BuilderRequest
open Blanc.Composition.BuilderRequestPublic (depositAddr exitAddr)
open Blanc.Lift.WithdrawalRequest.FloodTx (txD senderE txD_recoveredSender txD_intrinsic)

-- Reuse the exact shared writer prefix, replacing its STOP with POP and a
-- second zero-value CALL with empty calldata. No builder runtime is modified.
private def writerCode : ByteArray :=
  ⟨((SystemWordWriter.code depositAddr 0).toList.take 64 ++
    [0x50, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x73] ++ depositAddr.toBytes ++
    [0x5a, 0xf1, 0x00]).toArray⟩

private def senderAcct (nonce : UInt64) (funds : Nat) : Acct :=
  { Acct.nil with nonce := nonce, bal := funds.toB256 }

private def builderWorld : State :=
  State.setPresent (State.setPresent (State.setPresent .empty
    systemAddress { Acct.nil with nonce := 1, code := writerCode })
    depositAddr { Acct.nil with nonce := 1, code := Deposit.code })
    exitAddr { Acct.nil with nonce := 1, code := Exit.code }

private def state : State := builderWorld.setPresent senderE (senderAcct 2 (2 ^ 100))
private def debit : State := builderWorld.setPresent senderE (senderAcct 3 (2 ^ 100 - 2 ^ 21))

private def benv : Benv :=
  { (default : Benv) with
    state := state
    stat := { (default : Benv).stat with
      fork := .prague
      chainId := 1
      origState := state
      blockGasLimit := 60000000
      baseFeePerGas := 1 } }

private def msg : Msg :=
  callMessage { benv.beginTransaction with state := debit }
    (transactionTenv benv.beginTransaction txD 0 senderE 2 21000 []) txD systemAddress

private theorem prepared :
    prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction txD 0 senderE 2 21000 []) txD = .ok msg :=
  prepareMessage_call rfl

private theorem after_transfer : msg.benvAfterTransfer = .ok msg.benv :=
  Msg.benvAfterTransfer_of_value_zero rfl

private theorem recovered : recoverSender benv.stat.chainId txD = .ok senderE :=
  txD_recoveredSender

-- Closed entry facts are checked outside LSP by the owned narrow build.
private theorem debit_eq : (state.incrNonce senderE).subBal senderE (2 ^ 21 : Nat).toB256 = some debit := by
  kernel_rfl

private theorem message_code : msg.code = writerCode := by
  kernel_rfl

private def base : Devm := initDevm msg
private def sevm : Sevm := initSevm msg
private def firstGas : Nat := 1027576 - 27
private def callState : Devm :=
  base.setMach ⟨[firstGas.toB256, depositAddr.toBytes.toB256, 0, 0, 32, 0, 0],
    SystemWordWriter.wordMemory 0, firstGas, base.stateGas⟩

private theorem first_prefix : ConcreteRun.stepN 10 (initEvm msg) = some ⟨63, sevm, callState⟩ := by
  kernel_rfl

private def firstMsg : Msg := SystemWordWriter.childMsg sevm base depositAddr 0 firstGas Deposit.code

private theorem first_cost : accessCost depositAddr base.accessedAddresses = 2600 := by
  have absent : depositAddr ∉ base.accessedAddresses := by
    change depositAddr ∉ (Std.HashSet.ofList [(0 : Adr)]).insertMany
      (pragueRules.precompiles ++ [senderE, systemAddress])
    simp only [Std.HashSet.mem_insertMany_list, Std.HashSet.mem_ofList,
      List.contains_iff_mem, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    decide
  unfold accessCost
  rw [ite_eq_right absent]
  rfl

private theorem first_forwarded : SystemWordWriter.forwardedGas base depositAddr firstGas = 1008935 := by
  unfold SystemWordWriter.forwardedGas
  rw [first_cost]
  rfl

private theorem first_data : firstMsg.data = (0 : B256).toBytes :=
  SystemWordWriter.childMsg_data _ _ _ _ _ _

private theorem first_caller : firstMsg.caller = systemAddress := rfl

private theorem deposit_code : base.getCode depositAddr = Deposit.code := by
  kernel_rfl

private theorem first_call_at : Ninst.At sevm.code 63 (.exec .call) := by
  unfold Ninst.At
  kernel_rfl

private def firstBare : Devm :=
  base.setMach ⟨[], SystemWordWriter.wordMemory 0, firstGas, base.stateGas⟩

private theorem first_delegation :
    accessDelegation (addAccessedAddress firstBare depositAddr) depositAddr =
      (false, depositAddr, Deposit.code, 0, addAccessedAddress firstBare depositAddr) := by
  kernel_rfl

private theorem first_split :
    calculateMsgCallGas 0 firstGas.toB256.toNat firstGas 0
      (accessCost depositAddr base.accessedAddresses) =
      (SystemWordWriter.forwardedGas base depositAddr firstGas + accessCost depositAddr base.accessedAddresses,
        SystemWordWriter.forwardedGas base depositAddr firstGas) := by
  have affordable : accessCost depositAddr base.accessedAddresses ≤ firstGas := by
    have h := accessCost_le (x := depositAddr) (a := base.accessedAddresses)
    change _ ≤ 2600 at h
    change _ ≤ 1027549
    omega
  rw [calculateMsgCallGas_zero (by omega), B256.toNat_toB256_of_lt (by decide : firstGas < 2 ^ 256)]
  simp only [Nat.sub_zero]
  have bound : SystemWordWriter.forwardedGas base depositAddr firstGas ≤ firstGas := by
    unfold SystemWordWriter.forwardedGas except64th
    omega
  unfold SystemWordWriter.forwardedGas at bound
  rw [Nat.min_eq_right bound]
  rfl

private theorem first_spawn :
    Evm.step ⟨63, sevm, callState⟩ =
      .spawn (Frame.ofCall firstMsg) (.call (SystemWordWriter.parent base depositAddr 0 firstGas) 0 0) 64 := by
  have spawn := Xinst.step_call_zero_value_spawn
    (sevm := sevm) (devm := callState) (gw := firstGas.toB256) (cw := depositAddr.toBytes.toB256)
    (iiw := 0) (isw := 32) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := depositAddr) (code := Deposit.code) (dgc := 0)
    (d1 := addAccessedAddress firstBare depositAddr) (ext := 0)
    (acc := accessCost depositAddr base.accessedAddresses)
    (mcs := SystemWordWriter.forwardedGas base depositAddr firstGas)
    (mcc := SystemWordWriter.forwardedGas base depositAddr firstGas + accessCost depositAddr base.accessedAddresses)
    (CoveredFork.prague.callEra false) rfl ?_ ?_ ?_ first_split ?_ (by decide)
  · rw [Evm.step_next first_call_at]
    simp only [Ninst.step_exec, spawn, XStep.toStep, SystemWordWriter.childMsg,
      SystemWordWriter.parent, firstMsg, firstBare, SystemWordWriter.target_word, Nat.add_zero,
      B256.toNat_zero, show (32 : B256).toNat = 32 from rfl, Nat.reduceAdd]
  · apply Devm.extCost_covered
    change memExtsSize (SystemWordWriter.wordMemory 0).size [(0, 32), (0, 0)] =
      (SystemWordWriter.wordMemory 0).size
    rw [show (SystemWordWriter.wordMemory 0).size = 32 from Mem.size_write_word]
    rfl
  · rw [SystemWordWriter.target_word]
    exact first_delegation
  · rw [SystemWordWriter.target_word]
    rfl
  · change SystemWordWriter.forwardedGas base depositAddr firstGas +
        accessCost depositAddr base.accessedAddresses + 0 ≤ firstGas
    have h := accessCost_le (x := depositAddr) (a := base.accessedAddresses)
    change _ ≤ 2600 at h
    unfold SystemWordWriter.forwardedGas except64th
    unfold firstGas at *
    change _ ≤ 1027549
    omega

private def accounts : Witness.AcctShadow :=
  [(senderE, senderAcct 3 (2 ^ 100 - 2 ^ 21)),
    (exitAddr, { Acct.nil with nonce := 1, code := Exit.code }),
    (depositAddr, { Acct.nil with nonce := 1, code := Deposit.code }),
    (systemAddress, { Acct.nil with nonce := 1, code := writerCode })]

private theorem debit_accounts (a : Adr) : debit.get a = Witness.lookupA accounts a := by
  simp only [debit, builderWorld, accounts, Witness.lookupA]
  by_cases hE : senderE = a
  · subst a
    rw [State.get_setPresent_self, ite_eq_left rfl]
  · rw [State.get_setPresent_ne _ hE, ite_eq_right hE]
    by_cases hX : exitAddr = a
    · subst a
      rw [State.get_setPresent_self, ite_eq_left rfl]
    · rw [State.get_setPresent_ne _ hX, ite_eq_right hX]
      by_cases hD : depositAddr = a
      · subst a
        rw [State.get_setPresent_self, ite_eq_left rfl]
      · rw [State.get_setPresent_ne _ hD, ite_eq_right hD]
        by_cases hS : systemAddress = a
        · subst a
          rw [State.get_setPresent_self, ite_eq_left rfl]
        · rw [State.get_setPresent_ne _ hS, ite_eq_right hS]
          rfl

private def firstAddresses : List Adr := depositAddr :: (0 :: pragueRules.precompiles ++ [senderE, systemAddress])
private def firstCfg : Witness.Cfg :=
  ⟨initDevm firstMsg, Deposit.t_0000_c0, [], [], firstAddresses, [], accounts⟩

private theorem first_agree : Witness.Agree firstCfg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    change k ∈ (∅ : Std.HashSet (Adr × B256)) ↔ k ∈ ([] : List (Adr × B256))
    exact ⟨fun h => (Std.HashSet.not_mem_empty h).elim, fun h => (List.not_mem_nil h).elim⟩
  · intro a
    change a ∈ ((Std.HashSet.ofList [(0 : Adr)]).insertMany
      (pragueRules.precompiles ++ [senderE, systemAddress])).insert depositAddr ↔ a ∈ firstAddresses
    simp only [Std.HashSet.mem_insert, Std.HashSet.mem_insertMany_list, Std.HashSet.mem_ofList,
      firstAddresses, List.contains_iff_mem, beq_iff_eq, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false]
    simp only [eq_comm]
    tauto
  · intro a k
    change (debit.get a).stor.get k = 0
    rw [debit_accounts]
    simp only [accounts, Witness.lookupA]
    split_ifs <;> rfl
  · intro a
    change Witness.acctView (debit.get a) = Witness.lookupA accounts a
    rw [debit_accounts]
    simp only [accounts, Witness.lookupA]
    split_ifs <;> rfl

private def firstResult : Witness.Res := Witness.wrun Deposit.cert.prog (initSevm firstMsg) 512 firstCfg
private def firstPost : Devm := match firstResult with | .done (.halted post) _ => post | _ => default
private def firstFinal : Witness.Cfg := match firstResult with | .done _ cl => cl | _ => firstCfg

private def firstCheck : Bool :=
  match firstResult with
  | .done (.halted post) cl => post.error.isNone && decide (0 ≤ post.refundCounter) &&
      decide (Witness.lookupS cl.stor depositAddr 0 = B256.max) && decide (post.output = []) &&
      post.accountsToDelete.isEmpty
  | _ => false

private theorem first_check : firstCheck = true := by
  unfold firstCheck firstResult firstCfg firstMsg SystemWordWriter.childMsg
  rw [first_forwarded]
  kernel_rfl

private theorem first_status :
    (match firstResult with
      | .done (.halted post) cl => post.error.isNone ∧ post.refundCounter ≥ 0 ∧
          Witness.lookupS cl.stor depositAddr 0 = B256.max ∧ post.output = [] ∧
          post.accountsToDelete.isEmpty = true
      | _ => False) := by
  have check := first_check
  cases h : firstResult with
  | cont c => simp only [firstCheck, h, Bool.false_eq_true] at check
  | stuck => simp only [firstCheck, h, Bool.false_eq_true] at check
  | done outcome cl =>
      cases outcome with
      | returned d => simp only [firstCheck, h, Bool.false_eq_true] at check
      | halted post =>
          simp only [firstCheck, h, Bool.and_eq_true, decide_eq_true_eq] at check
          tauto

private theorem first_result : firstResult = .done (.halted firstPost) firstFinal := by
  have status := first_status
  cases h : firstResult with
  | cont c => rw [h] at status; contradiction
  | stuck => rw [h] at status; contradiction
  | done outcome cl =>
      cases outcome with
      | returned d => rw [h] at status; contradiction
      | halted post => simp only [firstPost, firstFinal, h]

private theorem first_facts : firstPost.error = none ∧ 0 ≤ firstPost.refundCounter ∧
    firstPost.getStorVal depositAddr 0 = B256.max := by
  have status := first_status
  rw [first_result] at status
  refine ⟨Option.isNone_iff_eq_none.mp status.1, status.2.1, ?_⟩
  have done := Witness.wrun_done first_result first_agree
  change Witness.storOf firstPost.state depositAddr 0 = B256.max
  rw [done.2.2 firstPost rfl]
  exact (done.2.1.2.2.1 depositAddr 0).trans status.2.2.1

private theorem first_exec : Nonempty (Exec 0 (initSevm firstMsg) (initDevm firstMsg) (.ok firstPost)) := by
  exact lift_exact_noExec Deposit.userPath.check Deposit.userPath.jumps rfl Deposit.userPath.noExec
    (Witness.wrun_exact rfl first_agree first_result)

private theorem first_enter : (Frame.ofCall firstMsg).enter = .run (initEvm firstMsg) := by
  exact Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl (by decide)

private theorem first_settle : (Frame.ofCall firstMsg).settle (.ok firstPost) = .ok firstPost := by
  rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
  simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, first_facts.1,
    Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind,
    Devm.recordTouch_of_not_touchedSweep (show firstMsg.benv.stat.rules.settle.touchedSweep = false from rfl)]

private def afterFirst : Devm := SystemWordWriter.post base depositAddr 0 firstGas firstPost

private theorem first_resume :
    Resume.run (.call (SystemWordWriter.parent base depositAddr 0 firstGas) 0 0)
      ((Frame.ofCall firstMsg).settle (.ok firstPost)) = .ok afterFirst := by
  rw [first_settle, Resume.run_call_ok (by rw [first_facts.1]; rfl) (by decide)]
  rfl

private theorem first_output : firstPost.output = [] := by
  have status := first_status
  rw [first_result] at status
  exact status.2.2.2.1

private def secondGas : Nat := afterFirst.gasLeft - 17
private def secondState : Devm :=
  afterFirst.setMach ⟨[secondGas.toB256, depositAddr.toBytes.toB256, 0, 0, 0, 0, 0],
    afterFirst.memory, secondGas, afterFirst.stateGas⟩
private def secondBare : Devm :=
  afterFirst.setMach ⟨[], afterFirst.memory, secondGas, afterFirst.stateGas⟩
private def secondForwarded : Nat := except64th (secondGas - 100)
private def secondParent : Devm :=
  callSpawnParent (addAccessedAddress secondBare depositAddr) (secondForwarded + 100) 0 0 0 0
private def secondMsg : Msg :=
  callSpawnMsg sevm secondParent secondForwarded depositAddr depositAddr 0 0 Deposit.code false

private theorem second_cost : accessCost depositAddr afterFirst.accessedAddresses = 100 := by
  have present : depositAddr ∈ afterFirst.accessedAddresses := by
    change depositAddr ∈ ((base.accessedAddresses.insert depositAddr).union firstPost.accessedAddresses)
    exact Std.HashSet.mem_union_of_left Std.HashSet.mem_insert_self
  unfold accessCost
  rw [ite_eq_left present]
  rfl

private theorem second_gas_range : 101 ≤ secondGas ∧ secondGas < 2 ^ 256 := by
  unfold secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
    firstPost firstResult firstCfg firstMsg SystemWordWriter.childMsg
  simp only [first_forwarded, first_cost]
  decide +kernel

private theorem second_prefix : ConcreteRun.stepN 8 ⟨64, sevm, afterFirst⟩ = some ⟨92, sevm, secondState⟩ := by
  unfold secondState secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
    firstPost firstResult firstCfg firstMsg SystemWordWriter.childMsg
  simp only [first_forwarded, first_cost]
  kernel_rfl

private theorem second_call_at : Ninst.At sevm.code 92 (.exec .call) := by
  unfold Ninst.At
  kernel_rfl

private theorem first_accounts : firstFinal.acs = accounts := by
  unfold firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
  rw [first_forwarded]
  kernel_rfl

private theorem afterFirst_code : afterFirst.getCode depositAddr = Deposit.code := by
  have done := Witness.wrun_done first_result first_agree
  have h := congrArg Acct.code (done.2.1.2.2.2 depositAddr)
  change (firstFinal.devm.state.get depositAddr).code = (Witness.lookupA firstFinal.acs depositAddr).code at h
  rw [← done.2.2 firstPost rfl, first_accounts] at h
  change (firstPost.state.get depositAddr).code = Deposit.code
  rw [h]
  simp only [accounts, Witness.lookupA]
  rw [ite_eq_right (by decide : senderE ≠ depositAddr),
    ite_eq_right (by decide : exitAddr ≠ depositAddr)]
  rfl

private theorem second_delegation :
    accessDelegation (addAccessedAddress secondBare depositAddr) depositAddr =
      (false, depositAddr, Deposit.code, 0, addAccessedAddress secondBare depositAddr) := by
  unfold accessDelegation
  change (match getDelegatedCodeAddress (afterFirst.getCode depositAddr) with
    | some adr => _ | none => _) = _
  rw [afterFirst_code]
  have nd : getDelegatedCodeAddress Deposit.code = none := Deposit.submissions.undelegated
  rw [nd]
  change (false, depositAddr, afterFirst.getCode depositAddr, 0,
    addAccessedAddress secondBare depositAddr) = _
  rw [afterFirst_code]

private theorem second_split :
    calculateMsgCallGas 0 secondGas.toB256.toNat secondGas 0 100 =
      (secondForwarded + 100, secondForwarded) := by
  rw [calculateMsgCallGas_zero (by have h := second_gas_range.1; omega),
    B256.toNat_toB256_of_lt second_gas_range.2]
  simp only [Nat.sub_zero]
  have bound : except64th (secondGas - 100) ≤ secondGas := by
    unfold except64th
    omega
  rw [Nat.min_eq_right bound]
  rfl

private theorem second_spawn :
    Evm.step ⟨92, sevm, secondState⟩ =
      .spawn (Frame.ofCall secondMsg) (.call secondParent 0 0) 93 := by
  have spawn := Xinst.step_call_zero_value_spawn
    (sevm := sevm) (devm := secondState) (gw := secondGas.toB256) (cw := depositAddr.toBytes.toB256)
    (iiw := 0) (isw := 0) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := depositAddr) (code := Deposit.code) (dgc := 0)
    (d1 := addAccessedAddress secondBare depositAddr) (ext := 0)
    (acc := 100) (mcs := secondForwarded) (mcc := secondForwarded + 100)
    (CoveredFork.prague.callEra false) rfl ?_ ?_ ?_ second_split ?_ (by decide)
  · rw [Evm.step_next second_call_at]
    simp only [Ninst.step_exec, spawn, XStep.toStep, secondMsg, secondParent, secondBare,
      SystemWordWriter.target_word, B256.toNat_zero, Nat.add_zero, Nat.reduceAdd]
  · apply Devm.extCost_covered
    simp only [secondState, Devm.memory_setMach, B256.toNat_zero]
    rcases SystemWordWriter.post_facts base firstPost depositAddr 0 firstGas first_output with
      ⟨_, _, _, _, _, _, _, memory, _⟩
    rw [show afterFirst.memory = SystemWordWriter.wordMemory 0 from memory,
      show (SystemWordWriter.wordMemory 0).size = 32 from Mem.size_write_word]
    rfl
  · rw [SystemWordWriter.target_word]
    simpa only [secondState, secondBare, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.setMach_setMach] using second_delegation
  · rw [SystemWordWriter.target_word]
    simpa only [secondState, Devm.setMach_accessedAddresses, Nat.add_zero] using second_cost
  · change secondForwarded + 100 + 0 ≤ secondGas
    have range := second_gas_range.1
    unfold secondForwarded except64th
    omega

private def secondAddresses : List Adr := depositAddr :: (firstAddresses ++ firstFinal.adrs)
private def secondCfg : Witness.Cfg :=
  ⟨initDevm secondMsg, Deposit.t_0000_c0, [], firstFinal.keys, secondAddresses,
    firstFinal.stor, firstFinal.acs⟩

private theorem second_world : (initDevm secondMsg).state = firstPost.state := rfl

private theorem second_keys : (initDevm secondMsg).accessedStorageKeys =
    (∅ : Std.HashSet (Adr × B256)).union firstPost.accessedStorageKeys := rfl

private theorem second_addresses : (initDevm secondMsg).accessedAddresses =
    ((base.accessedAddresses.insert depositAddr).union firstPost.accessedAddresses).insert depositAddr := rfl

private theorem first_accesses : firstPost.accessedStorageKeys = firstFinal.devm.accessedStorageKeys ∧
    firstPost.accessedAddresses = firstFinal.devm.accessedAddresses := by
  unfold firstPost firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
  simp only [first_forwarded]
  constructor <;> kernel_rfl

private theorem second_agree : Witness.Agree secondCfg := by
  have done := Witness.wrun_done first_result first_agree
  have world := done.2.2 firstPost rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    change k ∈ (initDevm secondMsg).accessedStorageKeys ↔ k ∈ firstFinal.keys
    have union : k ∈ (∅ : Std.HashSet (Adr × B256)).union firstPost.accessedStorageKeys ↔
        k ∈ (∅ : Std.HashSet (Adr × B256)) ∨ k ∈ firstPost.accessedStorageKeys := Std.HashSet.mem_union_iff
    rw [second_keys, union, first_accesses.1]
    rw [done.2.1.1 k]
    exact ⟨fun h => h.elim (fun h => (Std.HashSet.not_mem_empty h).elim) id, Or.inr⟩
  · intro a
    change a ∈ (initDevm secondMsg).accessedAddresses ↔ a ∈ secondAddresses
    have union : a ∈ (base.accessedAddresses.insert depositAddr).union firstPost.accessedAddresses ↔
        a ∈ base.accessedAddresses.insert depositAddr ∨ a ∈ firstPost.accessedAddresses := Std.HashSet.mem_union_iff
    rw [second_addresses, Std.HashSet.mem_insert, union, first_accesses.2]
    rw [done.2.1.2.1 a]
    have initial := first_agree.2.1 a
    change a ∈ base.accessedAddresses.insert depositAddr ↔ a ∈ firstAddresses at initial
    rw [initial]
    simp only [secondAddresses, List.mem_cons, List.mem_append, beq_iff_eq]
    tauto
  · intro a k
    change Witness.storOf (initDevm secondMsg).state a k = Witness.lookupS firstFinal.stor a k
    rw [second_world, world]
    exact done.2.1.2.2.1 a k
  · intro a
    change Witness.acctView ((initDevm secondMsg).state.get a) = Witness.lookupA firstFinal.acs a
    rw [second_world, world]
    exact done.2.1.2.2.2 a

private def secondResult : Witness.Res := Witness.wrun Deposit.cert.prog (initSevm secondMsg) 512 secondCfg
private def secondPost : Devm := match secondResult with | .done (.halted post) _ => post | _ => default
private def secondFinal : Witness.Cfg := match secondResult with | .done _ cl => cl | _ => secondCfg
private def secondCheck : Bool :=
  match secondResult with
  | .done (.halted post) cl => decide (post.error = none ∧ 0 ≤ post.refundCounter ∧
      Witness.lookupS cl.stor depositAddr 0 = 0 ∧ post.output = [] ∧
      post.accountsToDelete.isEmpty = true)
  | _ => false

private theorem second_check : secondCheck = true := by
  unfold secondCheck secondResult secondCfg secondMsg secondParent secondBare
    secondForwarded secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
    firstPost firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
  simp only [first_forwarded, first_cost]
  kernel_rfl

private theorem second_status :
    (match secondResult with
      | .done (.halted post) cl => post.error = none ∧ 0 ≤ post.refundCounter ∧
          Witness.lookupS cl.stor depositAddr 0 = 0 ∧ post.output = [] ∧
          post.accountsToDelete.isEmpty = true
      | _ => False) := by
  have check := second_check
  cases h : secondResult with
  | cont c => simp only [secondCheck, h, Bool.false_eq_true] at check
  | stuck => simp only [secondCheck, h, Bool.false_eq_true] at check
  | done outcome cl =>
      cases outcome with
      | returned d => simp only [secondCheck, h, Bool.false_eq_true] at check
      | halted post => simpa only [secondCheck, h, decide_eq_true_eq] using check

private theorem second_result : secondResult = .done (.halted secondPost) secondFinal := by
  have status := second_status
  cases h : secondResult with
  | cont c => rw [h] at status; contradiction
  | stuck => rw [h] at status; contradiction
  | done outcome cl =>
      cases outcome with
      | returned d => rw [h] at status; contradiction
      | halted post => simp only [secondPost, secondFinal, h]

private theorem second_facts : secondPost.error = none ∧ 0 ≤ secondPost.refundCounter ∧
    secondPost.getStorVal depositAddr 0 = 0 ∧ secondPost.output = [] := by
  have status := second_status
  rw [second_result] at status
  refine ⟨status.1, status.2.1, ?_, status.2.2.2.1⟩
  have done := Witness.wrun_done second_result second_agree
  change Witness.storOf secondPost.state depositAddr 0 = 0
  rw [done.2.2 secondPost rfl]
  exact (done.2.1.2.2.1 depositAddr 0).trans status.2.2.1

private theorem second_exec : Nonempty (Exec 0 (initSevm secondMsg) (initDevm secondMsg) (.ok secondPost)) := by
  exact lift_exact_noExec Deposit.userPath.check Deposit.userPath.jumps rfl Deposit.userPath.noExec
    (Witness.wrun_exact rfl second_agree second_result)

private theorem second_enter : (Frame.ofCall secondMsg).enter = .run (initEvm secondMsg) := by
  exact Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl (by decide)

private theorem second_settle : (Frame.ofCall secondMsg).settle (.ok secondPost) = .ok secondPost := by
  rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
  simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, second_facts.1,
    Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind,
    Devm.recordTouch_of_not_touchedSweep (show secondMsg.benv.stat.rules.settle.touchedSweep = false from rfl)]

private def afterSecond : Devm := callChildPost secondParent secondPost 0 0

private theorem second_resume :
    Resume.run (.call secondParent 0 0) ((Frame.ofCall secondMsg).settle (.ok secondPost)) =
      .ok afterSecond := by
  rw [second_settle, Resume.run_call_ok (by rw [second_facts.1]; rfl) (by decide)]
  rfl

private theorem stop_at : sevm.code.getInst 93 = some (.last .stop) := by
  kernel_rfl

private theorem stop_step : Evm.step ⟨93, sevm, afterSecond⟩ = .halt (.ok afterSecond) := by
  exact Evm.step_last stop_at

private theorem full_exec : Nonempty (Exec 0 sevm base (.ok afterSecond)) := by
  exact ConcreteRun.exec_of_stepN_spawn_runOk first_prefix first_spawn first_enter first_exec first_resume
    (ConcreteRun.exec_of_stepN_spawn_runOk second_prefix second_spawn second_enter second_exec second_resume
      ⟨Exec.halt stop_step⟩)

private noncomputable def firstRun : Exec 0 (initSevm firstMsg) (initDevm firstMsg) (.ok firstPost) :=
  Classical.choice first_exec
private noncomputable def secondRun : Exec 0 (initSevm secondMsg) (initDevm secondMsg) (.ok secondPost) :=
  Classical.choice second_exec
private noncomputable def tailRun : Exec 92 sevm secondState (.ok afterSecond) :=
  .runOk second_spawn second_enter secondRun second_resume (.halt stop_step)
private noncomputable def middleRun : Exec 64 sevm afterFirst (.ok afterSecond) :=
  ConcreteRun.Exec.ofStepN 8 second_prefix tailRun
private noncomputable def callRun : Exec 63 sevm callState (.ok afterSecond) :=
  .runOk first_spawn first_enter firstRun first_resume middleRun
private noncomputable def fullRun : Exec 0 sevm base (.ok afterSecond) :=
  ConcreteRun.Exec.ofStepN 10 first_prefix callRun

private theorem first_commits : Execution.commits (.ok firstPost) = true := by
  change firstPost.error.isNone = true
  rw [first_facts.1]
  rfl
private theorem second_commits : Execution.commits (.ok secondPost) = true := by
  change secondPost.error.isNone = true
  rw [second_facts.1]
  rfl

private noncomputable def latchFrame : Exec.Frame := .ofRun firstRun first_commits
private noncomputable def resetFrame : Exec.Frame := .ofRun secondRun second_commits

private theorem retained : Exec.keptAt depositAddr fullRun = [latchFrame, resetFrame] := by
  have firstSettles : Frame.settlementCommits (Frame.ofCall firstMsg) (.ok firstPost) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits first_commits
  have secondSettles : Frame.settlementCommits (Frame.ofCall secondMsg) (.ok secondPost) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits second_commits
  calc
    Exec.keptAt depositAddr fullRun = Exec.keptAt depositAddr callRun :=
      ConcreteRun.Exec.keptAt_ofStepN depositAddr 10 first_prefix callRun
    _ = latchFrame :: Exec.keptAt depositAddr middleRun :=
      Exec.keptAt_settled_here (a := depositAddr) first_spawn first_enter firstRun
        first_resume middleRun firstSettles rfl
    _ = latchFrame :: Exec.keptAt depositAddr tailRun :=
      congrArg (List.cons latchFrame)
        (ConcreteRun.Exec.keptAt_ofStepN depositAddr 8 second_prefix tailRun)
    _ = latchFrame :: resetFrame :: Exec.keptAt depositAddr (.halt stop_step) :=
      congrArg (List.cons latchFrame)
        (Exec.keptAt_settled_here (a := depositAddr) second_spawn second_enter secondRun
          second_resume (.halt stop_step) secondSettles rfl)
    _ = [latchFrame, resetFrame] := by rw [Exec.keptAt]

private theorem full_facts : afterSecond.error = none ∧ 0 ≤ afterSecond.refundCounter ∧
    afterSecond.output = [] := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · change 0 ≤ (0 + firstPost.refundCounter) + secondPost.refundCounter
    have one := first_facts.2.1
    have two := second_facts.2.1
    omega
  · rfl

private theorem message_enter : (Frame.ofCall msg).enter = .run (initEvm msg) := by
  exact Frame.enter_run_of_nonprecompile after_transfer rfl (by decide)

private noncomputable def root : Root := ⟨Frame.ofCall msg, initEvm msg, .ok afterSecond, fullRun⟩

private theorem root_retained : Root.keptAt depositAddr root = [latchFrame, resetFrame] := by
  have commits : Frame.settlementCommits (Frame.ofCall msg) (.ok afterSecond) = true := by
    apply Frame.settlementCommits_ofCall_of_raw_commits
    change afterSecond.error.isNone = true
    rw [full_facts.1]
    rfl
  change (if h : Frame.settlementCommits (Frame.ofCall msg) (.ok afterSecond) = true then
    if (initSevm msg).currentTarget = depositAddr then _ else Exec.keptAt depositAddr fullRun else []) = _
  rw [dite_eq_left commits, ite_eq_right (show (initSevm msg).currentTarget ≠ depositAddr from by decide)]
  exact retained

private theorem writer_undelegated : getDelegatedCodeAddress writerCode = none := by
  have len : (SystemWordWriter.code depositAddr 0).toList.length = 65 := by
    rw [ByteArray.toList_eq_toList_data, ← Array.size_eq_length_toList]
    exact SystemWordWriter.code_size _ _
  have size : writerCode.size = 94 := by
    simp only [writerCode, ByteArray.size, List.size_toArray, List.length_append,
      List.length_take, len]
    rfl
  unfold getDelegatedCodeAddress
  apply ite_eq_right
  intro h
  have bad := h.1
  rw [size] at bad
  contradiction

private theorem message_undelegated : getDelegatedCodeAddress msg.code = none := by
  rw [message_code]
  exact writer_undelegated

private theorem message_resolved : messageCallExecutionMessage msg = msg := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  have nd : msg.benv.stat.rules.delegatedCodeAddress msg.code = none := by
    unfold ForkRules.delegatedCodeAddress
    rw [message_undelegated]
    split <;> rfl
  rw [nd]

private theorem message_entry : messageEntry msg = some (Frame.ofCall msg, initEvm msg) := by
  unfold messageEntry legacyEntry
  change (match messageCallDelegation msg with
    | .ok (d, _) => enteredFrame (Frame.ofCall (messageCallExecutionMessage d))
    | .error _ => none) = _
  have delegated : messageCallDelegation msg = .ok (msg, 0) := by
    unfold messageCallDelegation processMessageCall.legacyAuthorization
    rfl
  rw [delegated]
  change enteredFrame (Frame.ofCall (messageCallExecutionMessage msg)) = _
  rw [message_resolved]
  unfold enteredFrame
  rw [message_enter]

private def messageOut : MsgCallOutput :=
  { gasLeft := afterSecond.gasLeft, refundCounter := ((0 + afterSecond.refundCounter.toNat : Nat) : Int)
    logs := afterSecond.logs, accountsToDelete := afterSecond.accountsToDelete
    error := none, returnData := afterSecond.output, touchedAccounts := afterSecond.meta.touchedAccounts }

private theorem message_process : processMessageCall msg = .ok (afterSecond.state, messageOut) := by
  apply processMessageCall_call_of_message rfl rfl rfl message_undelegated
  · apply processMessage_call_of_exec after_transfer rfl (by decide)
      ((exec_iff_exec_eq 0 sevm base (.ok afterSecond)).mp ⟨fullRun⟩) full_facts.1 rfl
  · exact full_facts.1
  · exact Int.toNat?_eq_some_of_nonneg full_facts.2.1

private theorem message_roots : MessageRoots msg afterSecond.state messageOut [root] := by
  refine ⟨message_process, ?_⟩
  rw [message_entry]
  rfl

private theorem tx_valid : validateTransaction benv.stat.rules txD 0 = .ok (21000, 21000) := by
  exact validateTransaction_ok_of_facts rfl
    (txD_intrinsic rfl rfl rfl rfl rfl 0) (by decide) (by decide) rfl rfl

private theorem sender_account : benv.beginTransaction.state.get senderE = senderAcct 2 (2 ^ 100) := by
  change state.get senderE = _
  exact State.get_setPresent_self _ _ _

private theorem tx_checked : checkTransaction benv.beginTransaction
    (transactionPreludeBout .init txD 0) txD = .ok (senderE, 2, [], 0) := by
  apply checkTransaction_ok_of_parts (maxFee := 2 ^ 20 * 8) (maxFee' := 2 ^ 20 * 8)
  · exact checkTransactionGasLimits_ok_of_room rfl (by decide) (by decide)
  · exact checkTransactionChainId_two rfl rfl
  · exact recovered
  · exact checkTransactionGasFee_two (benv := benv.beginTransaction) (tx := txD)
      (maxPriorityFee := 1) (maxFee := 8) rfl (by decide) (by decide) (by decide)
  · exact checkTransactionBlobData_two rfl _
  · exact checkTransactionReceiver_two rfl
  · exact checkTransactionAuthorizationList_two rfl
  · rw [sender_account]
    exact checkTransactionSenderAccount_ok_of_noCode rfl (by decide) rfl

private theorem tx_debit : (benv.state.incrNonce senderE).subBal senderE
    (txD.gas * 2 + transactionBlobGasFee benv txD).toB256 = some debit := by
  exact debit_eq

private theorem tx_message : transactionMessage benv .init txD 0 = .ok (senderE, msg) := by
  have valid : validateTransaction benv.beginTransaction.stat.rules txD 0 = .ok (21000, 21000) := tx_valid
  have debit : (benv.beginTransaction.state.incrNonce senderE).subBal senderE
      (txD.gas * 2 + transactionBlobGasFee benv.beginTransaction txD).toB256 = some debit := debit_eq
  have tenv : transactionTenvAt benv.beginTransaction txD 0 senderE 2 21000 [] =
      transactionTenv benv.beginTransaction txD 0 senderE 2 21000 [] := rfl
  unfold transactionMessage
  dsimp only
  rw [recoverValidationSender_of_stateGas_none txD rfl]
  simp only [valid, tx_checked, debit, Except.mapError, bind, Except.bind, Option.toExcept]
  rw [tenv, prepared]

private theorem transaction_roots : ∃ stop bout,
    TransactionRoots benv .init txD 0 stop bout senderE [root] := by
  have refund : Int.toNat? messageOut.refundCounter = some afterSecond.refundCounter.toNat := by
    change Int.toNat? ((0 + afterSecond.refundCounter.toNat : Nat) : Int) = _
    simp only [Nat.zero_add]
    exact Int.toNat?_eq_some_of_nonneg (i := (afterSecond.refundCounter.toNat : Int)) (by omega)
  obtain ⟨bout, process, _, _⟩ := processTransaction_of_stages_gasUsed
    (bout := .init) (index := 0) rfl rfl rfl rfl tx_valid tx_checked tx_debit prepared message_process refund
  exact ⟨_, bout, process, msg, afterSecond.state, messageOut, tx_message, message_roots⟩

private theorem reset_original :
    (initDevm secondMsg).getOrigStorVal (initSevm secondMsg) depositAddr 0 = 0 := by
  unfold Devm.getOrigStorVal
  split
  · rfl
  · change (state.get depositAddr).stor.get 0 = 0
    unfold state builderWorld
    rw [State.get_setPresent_ne _ (by decide : senderE ≠ depositAddr),
      State.get_setPresent_ne _ (by decide : exitAddr ≠ depositAddr), State.get_setPresent_self]
    rfl

/-- An unchanged signed transaction has an actual retained latch followed immediately
by a warm reset whose current word is max while its transaction-original word is zero.
This is the deposit pair prefix; the full two-contract history is a separate obligation. -/
theorem exists_deposit_latch_reset :
    ∃ (entry : Benv) (stop : State) (bout : BlockOutput) (sender : Adr)
      (r : Root) (latch reset : Exec.Frame),
      entry.stat.fork = .prague ∧
      entry.state.getCode depositAddr = Deposit.code ∧ entry.state.getCode exitAddr = Exit.code ∧
      recoverSender entry.stat.chainId txD = .ok sender ∧
      TransactionRoots entry .init txD 0 stop bout sender [r] ∧
      Root.keptAt depositAddr r = [latch, reset] ∧
      latch.sevm.caller = systemAddress ∧ latch.sevm.data.length = 32 ∧
      latch.pre.getStorVal depositAddr 0 = 0 ∧ latch.post.getStorVal depositAddr 0 = B256.max ∧
      reset.sevm.caller = systemAddress ∧ reset.sevm.data = [] ∧
      reset.pre.getStorVal depositAddr 0 = B256.max ∧
      reset.pre.getOrigStorVal reset.sevm depositAddr 0 = 0 ∧
      reset.post.getStorVal depositAddr 0 = 0 := by
  obtain ⟨stop, bout, roots⟩ := transaction_roots
  refine ⟨benv, stop, bout, senderE, root, latchFrame, resetFrame, rfl,
    ?_, ?_, recovered, roots, root_retained, rfl, ?_, ?_, first_facts.2.2,
    rfl, rfl, ?_, reset_original, second_facts.2.2.1⟩
  · change (state.get depositAddr).code = Deposit.code
    unfold state builderWorld
    rw [State.get_setPresent_ne _ (by decide : senderE ≠ depositAddr),
      State.get_setPresent_ne _ (by decide : exitAddr ≠ depositAddr), State.get_setPresent_self]
  · change (state.get exitAddr).code = Exit.code
    unfold state builderWorld
    rw [State.get_setPresent_ne _ (by decide : senderE ≠ exitAddr), State.get_setPresent_self]
  · change firstMsg.data.length = 32
    rw [first_data, B256.length_toBytes]
  · exact first_agree.2.2.1 depositAddr 0
  · change ((initDevm secondMsg).state.getStor depositAddr).get 0 = B256.max
    rw [second_world]
    exact first_facts.2.2

end Blanc.Composition.BuilderRequestApplicabilityCalls
