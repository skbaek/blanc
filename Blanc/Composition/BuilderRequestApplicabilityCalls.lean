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

-- Two concrete family contexts share this exact builder-pair prefix.
variable (full : Bool)

private def ordinaryAddr : Adr := 0x1234

-- Empty static fee read, then a 184-byte deposit with 10^9 gwei credited;
-- empty static exit fee read, then a 48-byte exit paid at its returned fee.
private def ordinaryCode : ByteArray :=
  ⟨([0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x73] ++ depositAddr.toBytes ++
    [0x5a, 0xfa, 0x50, 0x63, 0x3b, 0x9a, 0xca, 0x00, 0x60, 0x38, 0x52,
     0x5f, 0x5f, 0x60, 0xb8, 0x5f, 0x5f, 0x51, 0x67,
     0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00, 0x01, 0x73] ++
    depositAddr.toBytes ++ [0x5a, 0xf1, 0x50,
     0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x73] ++ exitAddr.toBytes ++
    [0x5a, 0xfa, 0x50, 0x5f, 0x5f, 0x60, 0x30, 0x5f, 0x5f, 0x51, 0x73] ++
    exitAddr.toBytes ++ [0x5a, 0xf1, 0x50, 0x00]).toArray⟩

private def ordinaryAcct : Acct :=
  { Acct.nil with nonce := 1, bal := (2 ^ 100 : Nat).toB256, code := ordinaryCode }

-- Remaining SYSTEM calls: Exit latch/reset, then the funded ordinary helper.
-- Only their bytes/context are selected here; their executions are later work.
private def writerSuffix : Bytes :=
  [0x50, 0x5f, 0x5f, 0x60, 0x20, 0x5f, 0x5f, 0x73] ++ exitAddr.toBytes ++
  [0x5a, 0xf1, 0x50, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x73] ++ exitAddr.toBytes ++
  [0x5a, 0xf1, 0x50, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x73] ++ ordinaryAddr.toBytes ++
  [0x5a, 0xf1, 0x50, 0x00]

private def writerPrefix : Bytes :=
  (SystemWordWriter.code depositAddr 0).toList.take 64 ++
    [0x50, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x73] ++ depositAddr.toBytes ++ [0x5a, 0xf1]

private def writerCode : ByteArray :=
  ⟨(writerPrefix ++ if full then writerSuffix else [0x00]).toArray⟩

private theorem writer_prefix_size : writerPrefix.length = 93 := by
  kernel_rfl

private theorem writer_prefix : (writerCode full).toList.take 93 = writerPrefix := by
  cases full <;> kernel_rfl

private def senderAcct (nonce : UInt64) (funds : Nat) : Acct :=
  { Acct.nil with nonce := nonce, bal := funds.toB256 }

private def builderWorld : State :=
  State.setPresent (State.setPresent (State.setPresent (State.setPresent .empty ordinaryAddr ordinaryAcct)
    systemAddress { Acct.nil with nonce := 1, code := (writerCode full) })
    depositAddr { Acct.nil with nonce := 1, code := Deposit.code })
    exitAddr { Acct.nil with nonce := 1, code := Exit.code }

private def state : State := (builderWorld full).setPresent senderE (senderAcct 2 (2 ^ 100))
private def debit : State := (builderWorld full).setPresent senderE (senderAcct 3 (2 ^ 100 - 2 ^ 21))

private theorem ordinary_context : (state full).get ordinaryAddr = ordinaryAcct := by
  unfold state builderWorld
  rw [State.get_setPresent_ne _ (by decide : senderE ≠ ordinaryAddr),
    State.get_setPresent_ne _ (by decide : exitAddr ≠ ordinaryAddr),
    State.get_setPresent_ne _ (by decide : depositAddr ≠ ordinaryAddr),
    State.get_setPresent_ne _ (by decide : systemAddress ≠ ordinaryAddr), State.get_setPresent_self]

private theorem ordinary_funding : (state full).getCode ordinaryAddr = ordinaryCode ∧
    ((state full).get ordinaryAddr).bal = (2 ^ 100 : Nat).toB256 := by
  exact ⟨congrArg Acct.code (ordinary_context full), congrArg Acct.bal (ordinary_context full)⟩

private def benv : Benv :=
  { (default : Benv) with
    state := (state full)
    stat := { (default : Benv).stat with
      fork := .prague
      chainId := 1
      origState := (state full)
      blockGasLimit := 60000000
      baseFeePerGas := 1 } }

private def msg : Msg :=
  callMessage { (benv full).beginTransaction with state := (debit full) }
    (transactionTenv (benv full).beginTransaction txD 0 senderE 2 21000 []) txD systemAddress

private theorem prepared :
    prepareMessage { (benv full).beginTransaction with state := (debit full) }
      (transactionTenv (benv full).beginTransaction txD 0 senderE 2 21000 []) txD = .ok (msg full) :=
  prepareMessage_call rfl

private theorem after_transfer : (msg full).benvAfterTransfer = .ok (msg full).benv :=
  Msg.benvAfterTransfer_of_value_zero rfl

private theorem recovered : recoverSender (benv full).stat.chainId txD = .ok senderE :=
  txD_recoveredSender

-- Closed entry facts are checked outside LSP by the owned narrow build.
private theorem debit_eq : ((state full).incrNonce senderE).subBal senderE (2 ^ 21 : Nat).toB256 = some (debit full) := by
  cases full <;> kernel_rfl

private theorem message_code : (msg full).code = (writerCode full) := by
  cases full <;> kernel_rfl

private def base : Devm := initDevm (msg full)
private def sevm : Sevm := initSevm (msg full)
private def firstGas : Nat := 1027576 - 27
private def callState : Devm :=
  (base full).setMach ⟨[firstGas.toB256, depositAddr.toBytes.toB256, 0, 0, 32, 0, 0],
    SystemWordWriter.wordMemory 0, firstGas, (base full).stateGas⟩

private theorem first_prefix : ConcreteRun.stepN 10 (initEvm (msg full)) = some ⟨63, (sevm full), (callState full)⟩ := by
  cases full <;> kernel_rfl

private def firstMsg : Msg := SystemWordWriter.childMsg (sevm full) (base full) depositAddr 0 firstGas Deposit.code

private theorem first_cost : accessCost depositAddr (base full).accessedAddresses = 2600 := by
  have absent : depositAddr ∉ (base full).accessedAddresses := by
    change depositAddr ∉ (Std.HashSet.ofList [(0 : Adr)]).insertMany
      (pragueRules.precompiles ++ [senderE, systemAddress])
    simp only [Std.HashSet.mem_insertMany_list, Std.HashSet.mem_ofList,
      List.contains_iff_mem, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    decide
  unfold accessCost
  rw [ite_eq_right absent]
  rfl

private theorem first_forwarded : SystemWordWriter.forwardedGas (base full) depositAddr firstGas = 1008935 := by
  unfold SystemWordWriter.forwardedGas
  rw [(first_cost full)]
  rfl

private theorem first_data : (firstMsg full).data = (0 : B256).toBytes :=
  SystemWordWriter.childMsg_data _ _ _ _ _ _

private theorem first_caller : (firstMsg full).caller = systemAddress := rfl

private theorem deposit_code : (base full).getCode depositAddr = Deposit.code := by
  cases full <;> kernel_rfl

private theorem first_call_at : Ninst.At (sevm full).code 63 (.exec .call) := by
  cases full
  all_goals
    unfold Ninst.At
    kernel_rfl

private def firstBare : Devm :=
  (base full).setMach ⟨[], SystemWordWriter.wordMemory 0, firstGas, (base full).stateGas⟩

private theorem first_delegation :
    accessDelegation (addAccessedAddress (firstBare full) depositAddr) depositAddr =
      (false, depositAddr, Deposit.code, 0, addAccessedAddress (firstBare full) depositAddr) := by
  cases full <;> kernel_rfl

private theorem first_split :
    calculateMsgCallGas 0 firstGas.toB256.toNat firstGas 0
      (accessCost depositAddr (base full).accessedAddresses) =
      (SystemWordWriter.forwardedGas (base full) depositAddr firstGas + accessCost depositAddr (base full).accessedAddresses,
        SystemWordWriter.forwardedGas (base full) depositAddr firstGas) := by
  have affordable : accessCost depositAddr (base full).accessedAddresses ≤ firstGas := by
    have h := accessCost_le (x := depositAddr) (a := (base full).accessedAddresses)
    change _ ≤ 2600 at h
    change _ ≤ 1027549
    omega
  rw [calculateMsgCallGas_zero (by omega), B256.toNat_toB256_of_lt (by decide : firstGas < 2 ^ 256)]
  simp only [Nat.sub_zero]
  have bound : SystemWordWriter.forwardedGas (base full) depositAddr firstGas ≤ firstGas := by
    unfold SystemWordWriter.forwardedGas except64th
    omega
  unfold SystemWordWriter.forwardedGas at bound
  rw [Nat.min_eq_right bound]
  rfl

private theorem first_spawn :
    Evm.step ⟨63, (sevm full), (callState full)⟩ =
      .spawn (Frame.ofCall (firstMsg full)) (.call (SystemWordWriter.parent (base full) depositAddr 0 firstGas) 0 0) 64 := by
  have spawn := Xinst.step_call_zero_value_spawn
    (sevm := (sevm full)) (devm := (callState full)) (gw := firstGas.toB256) (cw := depositAddr.toBytes.toB256)
    (iiw := 0) (isw := 32) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := depositAddr) (code := Deposit.code) (dgc := 0)
    (d1 := addAccessedAddress (firstBare full) depositAddr) (ext := 0)
    (acc := accessCost depositAddr (base full).accessedAddresses)
    (mcs := SystemWordWriter.forwardedGas (base full) depositAddr firstGas)
    (mcc := SystemWordWriter.forwardedGas (base full) depositAddr firstGas + accessCost depositAddr (base full).accessedAddresses)
    (CoveredFork.prague.callEra false) rfl ?_ ?_ ?_ (first_split full) ?_ (by change (1024 : Nat) ≠ 0; decide)
  · rw [Evm.step_next (first_call_at full)]
    simp only [Ninst.step_exec, spawn, XStep.toStep, SystemWordWriter.childMsg,
      SystemWordWriter.parent, firstMsg, firstBare, SystemWordWriter.target_word, Nat.add_zero,
      B256.toNat_zero, show (32 : B256).toNat = 32 from rfl, Nat.reduceAdd]
  · apply Devm.extCost_covered
    change memExtsSize (SystemWordWriter.wordMemory 0).size [(0, 32), (0, 0)] =
      (SystemWordWriter.wordMemory 0).size
    rw [show (SystemWordWriter.wordMemory 0).size = 32 from Mem.size_write_word]
    rfl
  · rw [SystemWordWriter.target_word]
    exact (first_delegation full)
  · rw [SystemWordWriter.target_word]
    simp only [callState, Devm.setMach_accessedAddresses, Nat.add_zero]
  · rw [first_forwarded full, first_cost full]
    change 1008935 + 2600 + 0 ≤ 1027549
    decide

private def accounts : Witness.AcctShadow :=
  [(senderE, senderAcct 3 (2 ^ 100 - 2 ^ 21)),
    (exitAddr, { Acct.nil with nonce := 1, code := Exit.code }),
    (depositAddr, { Acct.nil with nonce := 1, code := Deposit.code }),
    (systemAddress, { Acct.nil with nonce := 1, code := (writerCode full) }),
    (ordinaryAddr, ordinaryAcct)]

private theorem debit_accounts (a : Adr) : (debit full).get a = Witness.lookupA (accounts full) a := by
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
          by_cases hU : ordinaryAddr = a
          · subst a
            rw [State.get_setPresent_self, ite_eq_left rfl]
          · rw [State.get_setPresent_ne _ hU, ite_eq_right hU]
            rfl

private def firstAddresses : List Adr := depositAddr :: (0 :: pragueRules.precompiles ++ [senderE, systemAddress])
private def firstCfg : Witness.Cfg :=
  ⟨initDevm (firstMsg full), Deposit.t_0000_c0, [], [], firstAddresses, [], (accounts full)⟩

private theorem first_agree : Witness.Agree (firstCfg full) := by
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
    change ((debit full).get a).stor.get k = 0
    rw [(debit_accounts full)]
    simp only [accounts, Witness.lookupA]
    split_ifs <;> rfl
  · intro a
    change Witness.acctView ((debit full).get a) = Witness.lookupA (accounts full) a
    rw [(debit_accounts full)]
    simp only [accounts, Witness.lookupA]
    split_ifs <;> rfl

private def firstResult : Witness.Res := Witness.wrun Deposit.cert.prog (initSevm (firstMsg full)) 512 (firstCfg full)
private def firstPost : Devm := match (firstResult full) with | .done (.halted post) _ => post | _ => default
private def firstFinal : Witness.Cfg := match (firstResult full) with | .done _ cl => cl | _ => (firstCfg full)

private def firstCheck : Bool :=
  match (firstResult full) with
  | .done (.halted post) cl => post.error.isNone && decide (0 ≤ post.refundCounter) &&
      decide (Witness.lookupS cl.stor depositAddr 0 = B256.max) && decide (post.output = []) &&
      post.accountsToDelete.isEmpty
  | _ => false

private theorem first_check : (firstCheck full) = true := by
  cases full
  all_goals
    unfold firstCheck firstResult firstCfg firstMsg SystemWordWriter.childMsg
    rw [first_forwarded]
    kernel_rfl

private theorem first_status :
    (match (firstResult full) with
      | .done (.halted post) cl => post.error.isNone ∧ post.refundCounter ≥ 0 ∧
          Witness.lookupS cl.stor depositAddr 0 = B256.max ∧ post.output = [] ∧
          post.accountsToDelete.isEmpty = true
      | _ => False) := by
  have check := (first_check full)
  cases h : (firstResult full) with
  | cont c => simp only [firstCheck, h, Bool.false_eq_true] at check
  | stuck => simp only [firstCheck, h, Bool.false_eq_true] at check
  | done outcome cl =>
      cases outcome with
      | returned d => simp only [firstCheck, h, Bool.false_eq_true] at check
      | halted post =>
          simp only [firstCheck, h, Bool.and_eq_true, decide_eq_true_eq] at check
          tauto

private theorem first_result : (firstResult full) = .done (.halted (firstPost full)) (firstFinal full) := by
  have status := (first_status full)
  cases h : (firstResult full) with
  | cont c => rw [h] at status; contradiction
  | stuck => rw [h] at status; contradiction
  | done outcome cl =>
      cases outcome with
      | returned d => rw [h] at status; contradiction
      | halted post => simp only [firstPost, firstFinal, h]

private theorem first_facts : (firstPost full).error = none ∧ 0 ≤ (firstPost full).refundCounter ∧
    (firstPost full).getStorVal depositAddr 0 = B256.max := by
  have status := (first_status full)
  rw [(first_result full)] at status
  refine ⟨Option.isNone_iff_eq_none.mp status.1, status.2.1, ?_⟩
  have done := Witness.wrun_done (first_result full) (first_agree full)
  change Witness.storOf (firstPost full).state depositAddr 0 = B256.max
  rw [done.2.2 (firstPost full) rfl]
  exact (done.2.1.2.2.1 depositAddr 0).trans status.2.2.1

private theorem first_exec : Nonempty (Exec 0 (initSevm (firstMsg full)) (initDevm (firstMsg full)) (.ok (firstPost full))) := by
  exact lift_exact_noExec Deposit.userPath.check Deposit.userPath.jumps rfl Deposit.userPath.noExec
    (Witness.wrun_exact rfl (first_agree full) (first_result full))

private theorem first_enter : (Frame.ofCall (firstMsg full)).enter = .run (initEvm (firstMsg full)) := by
  exact Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl (by change pragueRules.isPrecomp depositAddr = false; decide)

private theorem first_settle : (Frame.ofCall (firstMsg full)).settle (.ok (firstPost full)) = .ok (firstPost full) := by
  rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
  simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, (first_facts full).1,
    Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind,
    Devm.recordTouch_of_not_touchedSweep (show (firstMsg full).benv.stat.rules.settle.touchedSweep = false from rfl)]

private def afterFirst : Devm := SystemWordWriter.post (base full) depositAddr 0 firstGas (firstPost full)

private theorem first_resume :
    Resume.run (.call (SystemWordWriter.parent (base full) depositAddr 0 firstGas) 0 0)
      ((Frame.ofCall (firstMsg full)).settle (.ok (firstPost full))) = .ok (afterFirst full) := by
  rw [(first_settle full), Resume.run_call_ok (by rw [(first_facts full).1]; rfl) (by change (0 : Nat) < 1024; decide)]
  rfl

private theorem first_output : (firstPost full).output = [] := by
  have status := (first_status full)
  rw [(first_result full)] at status
  exact status.2.2.2.1

private def secondGas : Nat := (afterFirst full).gasLeft - 17
private def secondState : Devm :=
  (afterFirst full).setMach ⟨[(secondGas full).toB256, depositAddr.toBytes.toB256, 0, 0, 0, 0, 0],
    (afterFirst full).memory, (secondGas full), (afterFirst full).stateGas⟩
private def secondBare : Devm :=
  (afterFirst full).setMach ⟨[], (afterFirst full).memory, (secondGas full), (afterFirst full).stateGas⟩
private def secondForwarded : Nat := except64th ((secondGas full) - 100)
private def secondParent : Devm :=
  callSpawnParent (addAccessedAddress (secondBare full) depositAddr) ((secondForwarded full) + 100) 0 0 0 0
private def secondMsg : Msg :=
  callSpawnMsg (sevm full) (secondParent full) (secondForwarded full) depositAddr depositAddr 0 0 Deposit.code false

private theorem second_cost : accessCost depositAddr (afterFirst full).accessedAddresses = 100 := by
  have present : depositAddr ∈ (afterFirst full).accessedAddresses := by
    change depositAddr ∈ (((base full).accessedAddresses.insert depositAddr).union (firstPost full).accessedAddresses)
    exact Std.HashSet.mem_union_of_left Std.HashSet.mem_insert_self
  unfold accessCost
  rw [ite_eq_left present]
  rfl

private theorem second_gas_range : 101 ≤ (secondGas full) ∧ (secondGas full) < 2 ^ 256 := by
  cases full
  all_goals
    unfold secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
      firstPost firstResult firstCfg firstMsg SystemWordWriter.childMsg
    simp only [first_forwarded, first_cost]
    decide +kernel

private theorem second_prefix : ConcreteRun.stepN 8 ⟨64, (sevm full), (afterFirst full)⟩ = some ⟨92, (sevm full), (secondState full)⟩ := by
  cases full
  all_goals
    unfold secondState secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
      firstPost firstResult firstCfg firstMsg SystemWordWriter.childMsg
    simp only [first_forwarded, first_cost]
    kernel_rfl

private theorem second_call_at : Ninst.At (sevm full).code 92 (.exec .call) := by
  cases full
  all_goals
    unfold Ninst.At
    kernel_rfl

private theorem first_accounts : (firstFinal full).acs = (accounts full) := by
  cases full
  all_goals
    unfold firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
    rw [first_forwarded]
    kernel_rfl

private theorem afterFirst_code : (afterFirst full).getCode depositAddr = Deposit.code := by
  have done := Witness.wrun_done (first_result full) (first_agree full)
  have h := congrArg Acct.code (done.2.1.2.2.2 depositAddr)
  change ((firstFinal full).devm.state.get depositAddr).code = (Witness.lookupA (firstFinal full).acs depositAddr).code at h
  rw [← done.2.2 (firstPost full) rfl, (first_accounts full)] at h
  change ((firstPost full).state.get depositAddr).code = Deposit.code
  rw [h]
  simp only [accounts, Witness.lookupA]
  rw [ite_eq_right (by decide : senderE ≠ depositAddr),
    ite_eq_right (by decide : exitAddr ≠ depositAddr)]
  rfl

private theorem second_delegation :
    accessDelegation (addAccessedAddress (secondBare full) depositAddr) depositAddr =
      (false, depositAddr, Deposit.code, 0, addAccessedAddress (secondBare full) depositAddr) := by
  unfold accessDelegation
  change (match getDelegatedCodeAddress ((afterFirst full).getCode depositAddr) with
    | some adr => _ | none => _) = _
  rw [(afterFirst_code full)]
  have nd : getDelegatedCodeAddress Deposit.code = none := Deposit.submissions.undelegated
  rw [nd]
  change (false, depositAddr, (afterFirst full).getCode depositAddr, 0,
    addAccessedAddress (secondBare full) depositAddr) = _
  rw [(afterFirst_code full)]

private theorem second_split :
    calculateMsgCallGas 0 (secondGas full).toB256.toNat (secondGas full) 0 100 =
      ((secondForwarded full) + 100, (secondForwarded full)) := by
  rw [calculateMsgCallGas_zero (by have h := (second_gas_range full).1; omega),
    B256.toNat_toB256_of_lt (second_gas_range full).2]
  simp only [Nat.sub_zero]
  have bound : except64th ((secondGas full) - 100) ≤ (secondGas full) := by
    unfold except64th
    omega
  rw [Nat.min_eq_right bound]
  rfl

private theorem second_spawn :
    Evm.step ⟨92, (sevm full), (secondState full)⟩ =
      .spawn (Frame.ofCall (secondMsg full)) (.call (secondParent full) 0 0) 93 := by
  have spawn := Xinst.step_call_zero_value_spawn
    (sevm := (sevm full)) (devm := (secondState full)) (gw := (secondGas full).toB256) (cw := depositAddr.toBytes.toB256)
    (iiw := 0) (isw := 0) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := depositAddr) (code := Deposit.code) (dgc := 0)
    (d1 := addAccessedAddress (secondBare full) depositAddr) (ext := 0)
    (acc := 100) (mcs := (secondForwarded full)) (mcc := (secondForwarded full) + 100)
    (CoveredFork.prague.callEra false) rfl ?_ ?_ ?_ (second_split full) ?_ (by change (1024 : Nat) ≠ 0; decide)
  · rw [Evm.step_next (second_call_at full)]
    simp only [Ninst.step_exec, spawn, XStep.toStep, secondMsg, secondParent, secondBare,
      SystemWordWriter.target_word, B256.toNat_zero, Nat.add_zero, Nat.reduceAdd]
  · apply Devm.extCost_covered
    simp only [secondState, Devm.memory_setMach, B256.toNat_zero]
    rcases SystemWordWriter.post_facts (base full) (firstPost full) depositAddr 0 firstGas (first_output full) with
      ⟨_, _, _, _, _, _, _, memory, _⟩
    rw [show (afterFirst full).memory = SystemWordWriter.wordMemory 0 from memory,
      show (SystemWordWriter.wordMemory 0).size = 32 from Mem.size_write_word]
    rfl
  · rw [SystemWordWriter.target_word]
    simpa only [secondState, secondBare, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.setMach_setMach] using (second_delegation full)
  · rw [SystemWordWriter.target_word]
    simpa only [secondState, Devm.setMach_accessedAddresses, Nat.add_zero] using (second_cost full)
  · change (secondForwarded full) + 100 + 0 ≤ (secondGas full)
    have range := (second_gas_range full).1
    unfold secondForwarded except64th
    omega

private def secondAddresses : List Adr := depositAddr :: (firstAddresses ++ (firstFinal full).adrs)
private def secondCfg : Witness.Cfg :=
  ⟨initDevm (secondMsg full), Deposit.t_0000_c0, [], (firstFinal full).keys, (secondAddresses full),
    (firstFinal full).stor, (firstFinal full).acs⟩

private theorem second_world : (initDevm (secondMsg full)).state = (firstPost full).state := rfl

private theorem second_keys : (initDevm (secondMsg full)).accessedStorageKeys =
    (∅ : Std.HashSet (Adr × B256)).union (firstPost full).accessedStorageKeys := rfl

private theorem second_addresses : (initDevm (secondMsg full)).accessedAddresses =
    (((base full).accessedAddresses.insert depositAddr).union (firstPost full).accessedAddresses).insert depositAddr := rfl

private theorem first_accesses : (firstPost full).accessedStorageKeys = (firstFinal full).devm.accessedStorageKeys ∧
    (firstPost full).accessedAddresses = (firstFinal full).devm.accessedAddresses := by
  cases full
  all_goals
    unfold firstPost firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
    simp only [first_forwarded]
    constructor <;> kernel_rfl

private theorem second_agree : Witness.Agree (secondCfg full) := by
  have done := Witness.wrun_done (first_result full) (first_agree full)
  have world := done.2.2 (firstPost full) rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    change k ∈ (initDevm (secondMsg full)).accessedStorageKeys ↔ k ∈ (firstFinal full).keys
    have union : k ∈ (∅ : Std.HashSet (Adr × B256)).union (firstPost full).accessedStorageKeys ↔
        k ∈ (∅ : Std.HashSet (Adr × B256)) ∨ k ∈ (firstPost full).accessedStorageKeys := Std.HashSet.mem_union_iff
    rw [(second_keys full), union, (first_accesses full).1]
    rw [done.2.1.1 k]
    exact ⟨fun h => h.elim (fun h => (Std.HashSet.not_mem_empty h).elim) id, Or.inr⟩
  · intro a
    change a ∈ (initDevm (secondMsg full)).accessedAddresses ↔ a ∈ (secondAddresses full)
    have union : a ∈ ((base full).accessedAddresses.insert depositAddr).union (firstPost full).accessedAddresses ↔
        a ∈ (base full).accessedAddresses.insert depositAddr ∨ a ∈ (firstPost full).accessedAddresses := by
      simpa only [Std.HashSet.mem_iff_contains, Union.union, Std.HashSet.instUnion] using
        (Std.HashSet.mem_union_iff (m₁ := (base full).accessedAddresses.insert depositAddr)
          (m₂ := (firstPost full).accessedAddresses) (k := a))
    rw [(second_addresses full), Std.HashSet.mem_insert, union, (first_accesses full).2]
    rw [done.2.1.2.1 a]
    have initial := (first_agree full).2.1 a
    change a ∈ (base full).accessedAddresses.insert depositAddr ↔ a ∈ firstAddresses at initial
    rw [initial]
    simp only [secondAddresses, List.mem_cons, List.mem_append, beq_iff_eq]
    exact or_congr eq_comm Iff.rfl
  · intro a k
    change Witness.storOf (initDevm (secondMsg full)).state a k = Witness.lookupS (firstFinal full).stor a k
    rw [(second_world full), world]
    exact done.2.1.2.2.1 a k
  · intro a
    change Witness.acctView ((initDevm (secondMsg full)).state.get a) = Witness.lookupA (firstFinal full).acs a
    rw [(second_world full), world]
    exact done.2.1.2.2.2 a

private def secondResult : Witness.Res := Witness.wrun Deposit.cert.prog (initSevm (secondMsg full)) 512 (secondCfg full)
private def secondPost : Devm := match (secondResult full) with | .done (.halted post) _ => post | _ => default
private def secondFinal : Witness.Cfg := match (secondResult full) with | .done _ cl => cl | _ => (secondCfg full)
private def secondCheck : Bool :=
  match (secondResult full) with
  | .done (.halted post) cl => decide (post.error = none ∧ 0 ≤ post.refundCounter ∧
      Witness.lookupS cl.stor depositAddr 0 = 0 ∧ post.output = [] ∧
      post.accountsToDelete.isEmpty = true)
  | _ => false

private theorem second_check : (secondCheck full) = true := by
  cases full
  all_goals
    unfold secondCheck secondResult secondCfg secondMsg secondParent secondBare
      secondForwarded secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
      firstPost firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
    simp only [first_forwarded, first_cost]
    kernel_rfl

private theorem second_status :
    (match (secondResult full) with
      | .done (.halted post) cl => post.error = none ∧ 0 ≤ post.refundCounter ∧
          Witness.lookupS cl.stor depositAddr 0 = 0 ∧ post.output = [] ∧
          post.accountsToDelete.isEmpty = true
      | _ => False) := by
  have check := (second_check full)
  cases h : (secondResult full) with
  | cont c => simp only [secondCheck, h, Bool.false_eq_true] at check
  | stuck => simp only [secondCheck, h, Bool.false_eq_true] at check
  | done outcome cl =>
      cases outcome with
      | returned d => simp only [secondCheck, h, Bool.false_eq_true] at check
      | halted post => simpa only [secondCheck, h, decide_eq_true_eq] using check

private theorem second_result : (secondResult full) = .done (.halted (secondPost full)) (secondFinal full) := by
  have status := (second_status full)
  cases h : (secondResult full) with
  | cont c => rw [h] at status; contradiction
  | stuck => rw [h] at status; contradiction
  | done outcome cl =>
      cases outcome with
      | returned d => rw [h] at status; contradiction
      | halted post => simp only [secondPost, secondFinal, h]

private theorem second_facts : (secondPost full).error = none ∧ 0 ≤ (secondPost full).refundCounter ∧
    (secondPost full).getStorVal depositAddr 0 = 0 ∧ (secondPost full).output = [] := by
  have status := (second_status full)
  rw [(second_result full)] at status
  refine ⟨status.1, status.2.1, ?_, status.2.2.2.1⟩
  have done := Witness.wrun_done (second_result full) (second_agree full)
  change Witness.storOf (secondPost full).state depositAddr 0 = 0
  rw [done.2.2 (secondPost full) rfl]
  exact (done.2.1.2.2.1 depositAddr 0).trans status.2.2.1

private theorem second_exec : Nonempty (Exec 0 (initSevm (secondMsg full)) (initDevm (secondMsg full)) (.ok (secondPost full))) := by
  exact lift_exact_noExec Deposit.userPath.check Deposit.userPath.jumps rfl Deposit.userPath.noExec
    (Witness.wrun_exact rfl (second_agree full) (second_result full))

private theorem second_enter : (Frame.ofCall (secondMsg full)).enter = .run (initEvm (secondMsg full)) := by
  exact Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl (by change pragueRules.isPrecomp depositAddr = false; decide)

private theorem second_settle : (Frame.ofCall (secondMsg full)).settle (.ok (secondPost full)) = .ok (secondPost full) := by
  rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
  simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, (second_facts full).1,
    Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind,
    Devm.recordTouch_of_not_touchedSweep (show (secondMsg full).benv.stat.rules.settle.touchedSweep = false from rfl)]

private def afterSecond : Devm := callChildPost (secondParent full) (secondPost full) 0 0

private theorem pair_gas : (afterSecond full).gasLeft = 994955 := by
  cases full
  all_goals
    unfold afterSecond secondPost secondResult secondCfg secondMsg secondParent secondBare
      secondForwarded secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
      firstPost firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
    simp only [first_forwarded, first_cost]
    kernel_rfl

private theorem pair_snapshot : (initSevm (secondMsg full)).benvStat.origState = state full := rfl

private theorem pair_original :
    (initDevm (secondMsg full)).getOrigStorVal (initSevm (secondMsg full)) depositAddr 0 = 0 := by
  unfold Devm.getOrigStorVal
  split
  · rfl
  · change ((state full).get depositAddr).stor.get 0 = 0
    unfold state builderWorld
    rw [State.get_setPresent_ne _ (by decide : senderE ≠ depositAddr),
      State.get_setPresent_ne _ (by decide : exitAddr ≠ depositAddr), State.get_setPresent_self]
    rfl

private theorem pair_dirty : (initDevm (secondMsg full)).getStorVal depositAddr 0 = B256.max := by
  change ((initDevm (secondMsg full)).state.getStor depositAddr).get 0 = B256.max
  rw [second_world full]
  exact (first_facts full).2.2

private theorem second_resume :
    Resume.run (.call (secondParent full) 0 0) ((Frame.ofCall (secondMsg full)).settle (.ok (secondPost full))) =
      .ok (afterSecond full) := by
  rw [(second_settle full), Resume.run_call_ok (by rw [(second_facts full).1]; rfl) (by change (0 : Nat) < 1024; decide)]
  rfl

private theorem stop_at : (sevm false).code.getInst 93 = some (.last .stop) := by
  kernel_rfl

private theorem full_tail_at : Ninst.At (sevm true).code 93 (.reg .pop) := by
  unfold Ninst.At
  kernel_rfl

private theorem stop_step : Evm.step ⟨93, sevm false, afterSecond false⟩ =
    .halt (.ok (afterSecond false)) := Evm.step_last stop_at

private noncomputable def firstRun : Exec 0 (initSevm (firstMsg full))
    (initDevm (firstMsg full)) (.ok (firstPost full)) := Classical.choice (first_exec full)
private noncomputable def secondRun : Exec 0 (initSevm (secondMsg full))
    (initDevm (secondMsg full)) (.ok (secondPost full)) := Classical.choice (second_exec full)

private noncomputable def pairTail {out : Execution}
    (rest : Exec 93 (sevm full) (afterSecond full) out) : Exec 92 (sevm full) (secondState full) out :=
  .runOk (second_spawn full) (second_enter full) (secondRun full) (second_resume full) rest
private noncomputable def pairMiddle {out : Execution}
    (rest : Exec 93 (sevm full) (afterSecond full) out) : Exec 64 (sevm full) (afterFirst full) out :=
  ConcreteRun.Exec.ofStepN 8 (second_prefix full) (pairTail full rest)
private noncomputable def pairCall {out : Execution}
    (rest : Exec 93 (sevm full) (afterSecond full) out) : Exec 63 (sevm full) (callState full) out :=
  .runOk (first_spawn full) (first_enter full) (firstRun full) (first_resume full) (pairMiddle full rest)
private noncomputable def pairRun {out : Execution}
    (rest : Exec 93 (sevm full) (afterSecond full) out) : Exec 0 (sevm full) (base full) out :=
  ConcreteRun.Exec.ofStepN 10 (first_prefix full) (pairCall full rest)

private theorem first_commits : Execution.commits (.ok (firstPost full)) = true := by
  change (firstPost full).error.isNone = true
  rw [(first_facts full).1]
  rfl
private theorem second_commits : Execution.commits (.ok (secondPost full)) = true := by
  change (secondPost full).error.isNone = true
  rw [(second_facts full).1]
  rfl

private noncomputable def latchFrame : Exec.Frame := .ofRun (firstRun full) (first_commits full)
private noncomputable def resetFrame : Exec.Frame := .ofRun (secondRun full) (second_commits full)

private theorem pair_kept {out : Execution}
    (rest : Exec 93 (sevm full) (afterSecond full) out) :
    Exec.keptAt depositAddr (pairRun full rest) =
      latchFrame full :: resetFrame full :: Exec.keptAt depositAddr rest := by
  have firstSettles : Frame.settlementCommits (Frame.ofCall (firstMsg full)) (.ok (firstPost full)) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits (first_commits full)
  have secondSettles : Frame.settlementCommits (Frame.ofCall (secondMsg full)) (.ok (secondPost full)) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits (second_commits full)
  calc
    Exec.keptAt depositAddr (pairRun full rest) = Exec.keptAt depositAddr (pairCall full rest) :=
      ConcreteRun.Exec.keptAt_ofStepN depositAddr 10 (first_prefix full) (pairCall full rest)
    _ = latchFrame full :: Exec.keptAt depositAddr (pairMiddle full rest) :=
      Exec.keptAt_settled_here (a := depositAddr) (first_spawn full) (first_enter full) (firstRun full)
        (first_resume full) (pairMiddle full rest) firstSettles rfl
    _ = latchFrame full :: Exec.keptAt depositAddr (pairTail full rest) :=
      congrArg (List.cons (latchFrame full))
        (ConcreteRun.Exec.keptAt_ofStepN depositAddr 8 (second_prefix full) (pairTail full rest))
    _ = latchFrame full :: resetFrame full :: Exec.keptAt depositAddr rest :=
      congrArg (List.cons (latchFrame full))
        (Exec.keptAt_settled_here (a := depositAddr) (second_spawn full) (second_enter full) (secondRun full)
          (second_resume full) rest secondSettles rfl)

private noncomputable def fullRun : Exec 0 (sevm false) (base false) (.ok (afterSecond false)) :=
  pairRun false (.halt stop_step)

private theorem retained : Exec.keptAt depositAddr fullRun = [latchFrame false, resetFrame false] := by
  have kept := pair_kept false (.halt stop_step)
  rw [Exec.keptAt] at kept
  exact kept

private theorem full_facts : (afterSecond false).error = none ∧ 0 ≤ (afterSecond false).refundCounter ∧
    (afterSecond false).output = [] := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · change 0 ≤ (0 + (firstPost false).refundCounter) + (secondPost false).refundCounter
    have one := (first_facts false).2.1
    have two := (second_facts false).2.1
    omega
  · rfl

private theorem message_enter : (Frame.ofCall (msg false)).enter = .run (initEvm (msg false)) := by
  exact Frame.enter_run_of_nonprecompile (after_transfer false) rfl (by decide)

private noncomputable def root : Root := ⟨Frame.ofCall (msg false), initEvm (msg false), .ok (afterSecond false), fullRun⟩

private theorem root_retained : Root.keptAt depositAddr root = [(latchFrame false), (resetFrame false)] := by
  have commits : Frame.settlementCommits (Frame.ofCall (msg false)) (.ok (afterSecond false)) = true := by
    apply Frame.settlementCommits_ofCall_of_raw_commits
    change (afterSecond false).error.isNone = true
    rw [full_facts.1]
    rfl
  change (if h : Frame.settlementCommits (Frame.ofCall (msg false)) (.ok (afterSecond false)) = true then
    if (initSevm (msg false)).currentTarget = depositAddr then _ else Exec.keptAt depositAddr fullRun else []) = _
  rw [dite_eq_left commits, ite_eq_right (show (initSevm (msg false)).currentTarget ≠ depositAddr from by decide)]
  exact retained

private theorem writer_undelegated : getDelegatedCodeAddress (writerCode false) = none := by
  have len : (SystemWordWriter.code depositAddr 0).toList.length = 65 := by
    rw [ByteArray.toList_eq_toList_data, ← Array.size_eq_length_toList]
    exact SystemWordWriter.code_size _ _
  have size : (writerCode false).size = 94 := by
    simp only [writerCode, writerPrefix, Bool.false_eq_true, ite_false, ByteArray.size,
      List.size_toArray, List.length_append, List.length_take, len]
    rfl
  unfold getDelegatedCodeAddress
  apply ite_eq_right
  intro h
  have bad := h.1
  rw [size] at bad
  contradiction

private theorem message_undelegated : getDelegatedCodeAddress (msg false).code = none := by
  rw [(message_code false)]
  exact writer_undelegated

private theorem message_resolved : messageCallExecutionMessage (msg false) = (msg false) := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  have nd : (msg false).benv.stat.rules.delegatedCodeAddress (msg false).code = none := by
    unfold ForkRules.delegatedCodeAddress
    rw [message_undelegated]
    split <;> rfl
  rw [nd]

private theorem message_entry : messageEntry (msg false) = some (Frame.ofCall (msg false), initEvm (msg false)) := by
  unfold messageEntry legacyEntry
  change (match messageCallDelegation (msg false) with
    | .ok (d, _) => enteredFrame (Frame.ofCall (messageCallExecutionMessage d))
    | .error _ => none) = _
  have delegated : messageCallDelegation (msg false) = .ok ((msg false), 0) := by
    unfold messageCallDelegation processMessageCall.legacyAuthorization
    rfl
  rw [delegated]
  change enteredFrame (Frame.ofCall (messageCallExecutionMessage (msg false))) = _
  rw [message_resolved]
  unfold enteredFrame
  rw [message_enter]

private def messageOut : MsgCallOutput :=
  { gasLeft := (afterSecond false).gasLeft, refundCounter := ((0 + (afterSecond false).refundCounter.toNat : Nat) : Int)
    logs := (afterSecond false).logs, accountsToDelete := (afterSecond false).accountsToDelete
    error := none, returnData := (afterSecond false).output, touchedAccounts := (afterSecond false).meta.touchedAccounts }

private theorem message_process : processMessageCall (msg false) = .ok ((afterSecond false).state, messageOut) := by
  apply processMessageCall_call_of_message rfl rfl rfl message_undelegated
  · apply processMessage_call_of_exec (after_transfer false) rfl (by decide)
      ((exec_iff_exec_eq 0 (sevm false) (base false) (.ok (afterSecond false))).mp ⟨fullRun⟩) full_facts.1 rfl
  · exact full_facts.1
  · exact Int.toNat?_eq_some_of_nonneg full_facts.2.1

private theorem message_roots : MessageRoots (msg false) (afterSecond false).state messageOut [root] := by
  refine ⟨message_process, ?_⟩
  rw [message_entry]
  rfl

private theorem tx_valid : validateTransaction (benv false).stat.rules txD 0 = .ok (21000, 21000) := by
  exact validateTransaction_ok_of_facts rfl
    (txD_intrinsic rfl rfl rfl rfl rfl 0) (by decide) (by decide) rfl rfl

private theorem sender_account : (benv false).beginTransaction.state.get senderE = senderAcct 2 (2 ^ 100) := by
  change (state false).get senderE = _
  exact State.get_setPresent_self _ _ _

private theorem tx_checked : checkTransaction (benv false).beginTransaction
    (transactionPreludeBout .init txD 0) txD = .ok (senderE, 2, [], 0) := by
  apply checkTransaction_ok_of_parts (maxFee := 2 ^ 20 * 8) (maxFee' := 2 ^ 20 * 8)
  · exact checkTransactionGasLimits_ok_of_room rfl (by decide) (by decide)
  · exact checkTransactionChainId_two rfl rfl
  · exact (recovered false)
  · exact checkTransactionGasFee_two (benv := (benv false).beginTransaction) (tx := txD)
      (maxPriorityFee := 1) (maxFee := 8) rfl (by decide) (by decide) (by decide)
  · exact checkTransactionBlobData_two rfl _
  · exact checkTransactionReceiver_two rfl
  · exact checkTransactionAuthorizationList_two rfl
  · rw [sender_account]
    exact checkTransactionSenderAccount_ok_of_noCode rfl (by decide) rfl

private theorem tx_debit : ((benv false).state.incrNonce senderE).subBal senderE
    (txD.gas * 2 + transactionBlobGasFee (benv false) txD).toB256 = some (debit false) := by
  exact (debit_eq false)

private theorem tx_message : transactionMessage (benv false) .init txD 0 = .ok (senderE, (msg false)) := by
  have valid : validateTransaction (benv false).beginTransaction.stat.rules txD 0 = .ok (21000, 21000) := tx_valid
  have debit : ((benv false).beginTransaction.state.incrNonce senderE).subBal senderE
      (txD.gas * 2 + transactionBlobGasFee (benv false).beginTransaction txD).toB256 = some (debit false) := (debit_eq false)
  have tenv : transactionTenvAt (benv false).beginTransaction txD 0 senderE 2 21000 [] =
      transactionTenv (benv false).beginTransaction txD 0 senderE 2 21000 [] := rfl
  unfold transactionMessage
  dsimp only
  rw [recoverValidationSender_of_stateGas_none txD rfl]
  simp only [valid, tx_checked, debit, Except.mapError, bind, Except.bind, Option.toExcept]
  rw [tenv, (prepared false)]

private theorem transaction_roots : ∃ stop bout,
    TransactionRoots (benv false) .init txD 0 stop bout senderE [root] := by
  have refund : Int.toNat? messageOut.refundCounter = some (afterSecond false).refundCounter.toNat := by
    change Int.toNat? ((0 + (afterSecond false).refundCounter.toNat : Nat) : Int) = _
    simp only [Nat.zero_add]
    exact Int.toNat?_eq_some_of_nonneg (i := ((afterSecond false).refundCounter.toNat : Int)) (by omega)
  obtain ⟨bout, process, _, _⟩ := processTransaction_of_stages_gasUsed
    (bout := .init) (index := 0) rfl rfl rfl rfl tx_valid tx_checked tx_debit (prepared false) message_process refund
  exact ⟨_, bout, process, (msg false), (afterSecond false).state, messageOut, tx_message, message_roots⟩

private theorem reset_original :
    (initDevm (secondMsg false)).getOrigStorVal (initSevm (secondMsg false)) depositAddr 0 = 0 :=
  pair_original false

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
  refine ⟨(benv false), stop, bout, senderE, root, (latchFrame false), (resetFrame false), rfl,
    ?_, ?_, (recovered false), roots, root_retained, rfl, ?_, ?_, (first_facts false).2.2,
    rfl, rfl, ?_, reset_original, (second_facts false).2.2.1⟩
  · change ((state false).get depositAddr).code = Deposit.code
    unfold state builderWorld
    rw [State.get_setPresent_ne _ (by decide : senderE ≠ depositAddr),
      State.get_setPresent_ne _ (by decide : exitAddr ≠ depositAddr), State.get_setPresent_self]
  · change ((state false).get exitAddr).code = Exit.code
    unfold state builderWorld
    rw [State.get_setPresent_ne _ (by decide : senderE ≠ exitAddr), State.get_setPresent_self]
  · change (firstMsg false).data.length = 32
    rw [(first_data false), B256.length_toBytes]
  · exact (first_agree false).2.2.1 depositAddr 0
  · change ((initDevm (secondMsg false)).state.getStor depositAddr).get 0 = B256.max
    rw [(second_world false)]
    exact (first_facts false).2.2

end Blanc.Composition.BuilderRequestApplicabilityCalls
