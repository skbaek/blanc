import Blanc.Composition.BuilderRequestApplicabilityInput
import Blanc.Composition.BuilderRequestClassification
import Blanc.Lift.SystemWordWriter
import Blanc.Lift.Witness
import Blanc.Lift.WithdrawalRequest.DrainTx
import Blanc.BlockForward
import Blanc.ConcreteRunKept
import Blanc.Lift.KernelBatchForall
import Blanc.Lift.NodeWalkOrig
import Jaune.MemoryAccounting

/-! A signed ordinary transaction entering SYSTEM code, whose actual children
exercise the builder latch followed by its dirty reset. The later block/history
assembly is separate; this module does not assert a synthetic history. -/

namespace Blanc.Composition.BuilderRequestApplicabilityCalls

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.BuilderRequest
open Blanc.Composition.BuilderRequestApplicabilityInput
open Blanc.Composition.BuilderRequestPublic (depositAddr exitAddr)
open Blanc.Lift.WithdrawalRequest.FloodTx (txD senderE txD_recoveredSender txD_intrinsic)

-- Two concrete family contexts share this exact builder-pair prefix.
variable (full : Bool) (parentHash : Option B256)

private theorem writer_prefix_size : writerPrefix.length = 93 := by
  kernel_rfl

private theorem writer_prefix : (writerCode full).toList.take 93 = writerPrefix := by
  cases full <;> kernel_rfl

private theorem ordinary_context : (state full parentHash).get ordinaryAddr = ordinaryAcct := by
  cases parentHash <;> simp only [state, builderWorld, baseWorld]
  all_goals repeat rw [State.get_setPresent_ne _ (by decide)]
  all_goals exact State.get_setPresent_self _ _ _

private theorem ordinary_funding : (state full parentHash).getCode ordinaryAddr = ordinaryCode ∧
    ((state full parentHash).get ordinaryAddr).bal = (2 ^ 100 : Nat).toB256 := by
  exact ⟨congrArg Acct.code (ordinary_context full parentHash), congrArg Acct.bal (ordinary_context full parentHash)⟩

private theorem prepared :
    prepareMessage { (benv full parentHash).beginTransaction with state := (debit full parentHash) }
      (transactionTenv (benv full parentHash).beginTransaction txD 0 senderE 2 21000 []) txD = .ok (msg full parentHash) :=
  prepareMessage_call rfl

private theorem after_transfer : (msg full parentHash).benvAfterTransfer = .ok (msg full parentHash).benv :=
  Msg.benvAfterTransfer_of_value_zero rfl

private theorem recovered : recoverSender (benv full parentHash).stat.chainId txD = .ok senderE :=
  txD_recoveredSender

-- Closed entry facts are checked outside LSP by the owned narrow build.
private theorem debit_eq : ((state full parentHash).incrNonce senderE).subBal senderE (2 ^ 21 : Nat).toB256 = some (debit full parentHash) := by
  cases full <;> cases parentHash <;> simp only [state, debit, builderWorld]
  all_goals
    unfold State.incrNonce
    rw [State.get_setPresent_self]
    kernel_rfl

private theorem message_code : (msg full parentHash).code = (writerCode full) := by
  cases full
  all_goals
    cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private def base : Devm := initDevm (msg full parentHash)
private def sevm : Sevm := initSevm (msg full parentHash)
private def firstGas : Nat := 1027576 - 27
private def callState : Devm :=
  (base full parentHash).setMach ⟨[firstGas.toB256, depositAddr.toBytes.toB256, 0, 0, 32, 0, 0],
    SystemWordWriter.wordMemory 0, firstGas, (base full parentHash).stateGas⟩

private theorem first_prefix : ConcreteRun.stepN 10 (initEvm (msg full parentHash)) = some ⟨63, (sevm full parentHash), (callState full parentHash)⟩ := by
  cases full
  all_goals
    cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private def firstMsg : Msg := SystemWordWriter.childMsg (sevm full parentHash) (base full parentHash) depositAddr 0 firstGas Deposit.code

private theorem first_cost : accessCost depositAddr (base full parentHash).accessedAddresses = 2600 := by
  have absent : depositAddr ∉ (base full parentHash).accessedAddresses := by
    change depositAddr ∉ (Std.HashSet.ofList [(0 : Adr)]).insertMany
      (pragueRules.precompiles ++ [senderE, systemAddress])
    simp only [Std.HashSet.mem_insertMany_list, Std.HashSet.mem_ofList,
      List.contains_iff_mem, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    decide
  unfold accessCost
  rw [ite_eq_right absent]
  rfl

private theorem first_forwarded : SystemWordWriter.forwardedGas (base full parentHash) depositAddr firstGas = 1008935 := by
  unfold SystemWordWriter.forwardedGas
  rw [(first_cost full parentHash)]
  rfl

private theorem first_data : (firstMsg full parentHash).data = (0 : B256).toBytes :=
  SystemWordWriter.childMsg_data _ _ _ _ _ _

private theorem first_caller : (firstMsg full parentHash).caller = systemAddress := rfl

private theorem deposit_code : (base full parentHash).getCode depositAddr = Deposit.code := by
  cases full
  all_goals
    cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private theorem first_call_at : Ninst.At (sevm full parentHash).code 63 (.exec .call) := by
  cases full
  all_goals
    unfold Ninst.At
    cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private def firstBare : Devm :=
  (base full parentHash).setMach ⟨[], SystemWordWriter.wordMemory 0, firstGas, (base full parentHash).stateGas⟩

private theorem first_delegation :
    accessDelegation (addAccessedAddress (firstBare full parentHash) depositAddr) depositAddr =
      (false, depositAddr, Deposit.code, 0, addAccessedAddress (firstBare full parentHash) depositAddr) := by
  cases full
  all_goals
    cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private theorem first_split :
    calculateMsgCallGas 0 firstGas.toB256.toNat firstGas 0
      (accessCost depositAddr (base full parentHash).accessedAddresses) =
      (SystemWordWriter.forwardedGas (base full parentHash) depositAddr firstGas + accessCost depositAddr (base full parentHash).accessedAddresses,
        SystemWordWriter.forwardedGas (base full parentHash) depositAddr firstGas) := by
  have affordable : accessCost depositAddr (base full parentHash).accessedAddresses ≤ firstGas := by
    have h := accessCost_le (x := depositAddr) (a := (base full parentHash).accessedAddresses)
    change _ ≤ 2600 at h
    change _ ≤ 1027549
    omega
  rw [calculateMsgCallGas_zero (by omega), B256.toNat_toB256_of_lt (by decide : firstGas < 2 ^ 256)]
  simp only [Nat.sub_zero]
  have bound : SystemWordWriter.forwardedGas (base full parentHash) depositAddr firstGas ≤ firstGas := by
    unfold SystemWordWriter.forwardedGas except64th
    omega
  unfold SystemWordWriter.forwardedGas at bound
  rw [Nat.min_eq_right bound]
  rfl

private theorem first_spawn :
    Evm.step ⟨63, (sevm full parentHash), (callState full parentHash)⟩ =
      .spawn (Frame.ofCall (firstMsg full parentHash)) (.call (SystemWordWriter.parent (base full parentHash) depositAddr 0 firstGas) 0 0) 64 := by
  have spawn := Xinst.step_call_zero_value_spawn
    (sevm := (sevm full parentHash)) (devm := (callState full parentHash)) (gw := firstGas.toB256) (cw := depositAddr.toBytes.toB256)
    (iiw := 0) (isw := 32) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := depositAddr) (code := Deposit.code) (dgc := 0)
    (d1 := addAccessedAddress (firstBare full parentHash) depositAddr) (ext := 0)
    (acc := accessCost depositAddr (base full parentHash).accessedAddresses)
    (mcs := SystemWordWriter.forwardedGas (base full parentHash) depositAddr firstGas)
    (mcc := SystemWordWriter.forwardedGas (base full parentHash) depositAddr firstGas + accessCost depositAddr (base full parentHash).accessedAddresses)
    (CoveredFork.prague.callEra false) rfl ?_ ?_ ?_ (first_split full parentHash) ?_ (by change (1024 : Nat) ≠ 0; decide)
  · rw [Evm.step_next (first_call_at full parentHash)]
    simp only [Ninst.step_exec, spawn, XStep.toStep, SystemWordWriter.childMsg,
      SystemWordWriter.parent, firstMsg, firstBare, SystemWordWriter.target_word, Nat.add_zero,
      B256.toNat_zero, show (32 : B256).toNat = 32 from rfl, Nat.reduceAdd]
  · apply Devm.extCost_covered
    change memExtsSize (SystemWordWriter.wordMemory 0).size [(0, 32), (0, 0)] =
      (SystemWordWriter.wordMemory 0).size
    rw [show (SystemWordWriter.wordMemory 0).size = 32 from Mem.size_write_word]
    rfl
  · rw [SystemWordWriter.target_word]
    exact (first_delegation full parentHash)
  · rw [SystemWordWriter.target_word]
    simp only [callState, Devm.setMach_accessedAddresses, Nat.add_zero]
  · rw [(first_forwarded full parentHash), (first_cost full parentHash)]
    change 1008935 + 2600 + 0 ≤ 1027549
    decide

private theorem debit_accounts (a : Adr) :
    (debit full parentHash).get a = Witness.lookupA (accounts full parentHash) a := by
  cases parentHash <;> simp only [debit, builderWorld, baseWorld, accounts, Option.elim, List.append_nil,
    List.cons_append, List.nil_append, Witness.lookupA]
  all_goals split_ifs <;> subst_vars
  all_goals try rfl
  all_goals repeat rw [State.get_setPresent_ne _ (by assumption)]
  all_goals rw [State.get_eq_getD]
  all_goals change ((∅ : State)[a]?).getD Acct.nil = Acct.nil
  all_goals rw [Std.TreeMap.getElem?_emptyc]
  all_goals rfl

private def firstAddresses : List Adr := depositAddr :: (0 :: pragueRules.precompiles ++ [senderE, systemAddress])
private def firstCfg : Witness.Cfg :=
  ⟨initDevm (firstMsg full parentHash), Deposit.t_0000_c0, [], [], firstAddresses, [], (accounts full parentHash)⟩

private theorem first_agree : Witness.Agree (firstCfg full parentHash) := by
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
    change ((debit full parentHash).get a).stor.get k = 0
    rw [(debit_accounts full parentHash)]
    cases parentHash <;> simp only [accounts, Option.elim, List.append_nil,
      List.cons_append, List.nil_append, Witness.lookupA]
    all_goals split_ifs <;> rfl
  · intro a
    change Witness.acctView ((debit full parentHash).get a) = Witness.lookupA (accounts full parentHash) a
    rw [(debit_accounts full parentHash)]
    cases parentHash <;> simp only [accounts, Option.elim, List.append_nil,
      List.cons_append, List.nil_append, Witness.lookupA]
    all_goals split_ifs <;> rfl

/-- Every account in the chosen original snapshot has zero storage. The sender
nonce/balance debit changes no storage, so the existing exact account shadow
supplies agreement for the registered witness original-state transport. -/
private theorem original_empty : NodeWalk.OrigAgree (.empty : State) (state full parentHash) := by
  intro a k
  have empty : ((State.get (.empty : State) a).stor.get k) = 0 := by
    rw [State.get_eq_getD]
    change (((∅ : State)[a]?).getD Acct.nil).stor.get k = 0
    rw [Std.TreeMap.getElem?_emptyc]
    rfl
  have same : ((state full parentHash).get a).stor = ((debit full parentHash).get a).stor := by
    unfold state debit
    by_cases atSender : senderE = a
    · subst a
      rw [State.get_setPresent_self, State.get_setPresent_self]
      rfl
    · rw [State.get_setPresent_ne _ atSender, State.get_setPresent_ne _ atSender]
  rw [empty, same, debit_accounts full parentHash]
  cases parentHash <;> simp only [accounts, Option.elim, List.append_nil,
    List.cons_append, List.nil_append, Witness.lookupA]
  all_goals split_ifs <;> rfl

private def firstResult : Witness.Res := Witness.wrun Deposit.cert.prog ((initSevm (firstMsg full parentHash)).withOrig .empty) 512 (firstCfg full parentHash)
private def firstPost : Devm := match (firstResult full parentHash) with | .done (.halted post) _ => post | _ => default
private def firstFinal : Witness.Cfg := match (firstResult full parentHash) with | .done _ cl => cl | _ => (firstCfg full parentHash)

private def firstCheck : Bool :=
  match (firstResult full parentHash) with
  | .done (.halted post) cl => post.error.isNone && decide (0 ≤ post.refundCounter) &&
      decide (Witness.lookupS cl.stor depositAddr 0 = B256.max) && decide (post.output = []) &&
      post.accountsToDelete.isEmpty
  | _ => false

private theorem first_check : (firstCheck full parentHash) = true := by
  cases full
  all_goals
    unfold firstCheck firstResult firstCfg firstMsg SystemWordWriter.childMsg
    rw [first_forwarded]
    cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private theorem first_status :
    (match (firstResult full parentHash) with
      | .done (.halted post) cl => post.error.isNone ∧ post.refundCounter ≥ 0 ∧
          Witness.lookupS cl.stor depositAddr 0 = B256.max ∧ post.output = [] ∧
          post.accountsToDelete.isEmpty = true
      | _ => False) := by
  have check := (first_check full parentHash)
  cases h : (firstResult full parentHash) with
  | cont c => simp only [firstCheck, h, Bool.false_eq_true] at check
  | stuck => simp only [firstCheck, h, Bool.false_eq_true] at check
  | done outcome cl =>
      cases outcome with
      | returned d => simp only [firstCheck, h, Bool.false_eq_true] at check
      | halted post =>
          simp only [firstCheck, h, Bool.and_eq_true, decide_eq_true_eq] at check
          tauto

private theorem first_result : (firstResult full parentHash) = .done (.halted (firstPost full parentHash)) (firstFinal full parentHash) := by
  have status := (first_status full parentHash)
  cases h : (firstResult full parentHash) with
  | cont c => rw [h] at status; contradiction
  | stuck => rw [h] at status; contradiction
  | done outcome cl =>
      cases outcome with
      | returned d => rw [h] at status; contradiction
      | halted post => simp only [firstPost, firstFinal, h]

/-- The computation is tied to the original spawned message before lifting. -/
private theorem first_result_actual :
    Witness.wrun Deposit.cert.prog (initSevm (firstMsg full parentHash)) 512 (firstCfg full parentHash) =
      .done (.halted (firstPost full parentHash)) (firstFinal full parentHash) := by
  have orig : NodeWalk.OrigAgree (.empty : State)
      (initSevm (firstMsg full parentHash)).benvStat.origState := by
    change NodeWalk.OrigAgree (.empty : State) (state full parentHash)
    exact original_empty full parentHash
  rw [← Witness.wrun_withOrig orig Deposit.cert.prog 512 (firstCfg full parentHash)]
  exact first_result full parentHash

private theorem first_facts : (firstPost full parentHash).error = none ∧ 0 ≤ (firstPost full parentHash).refundCounter ∧
    (firstPost full parentHash).getStorVal depositAddr 0 = B256.max := by
  have status := (first_status full parentHash)
  rw [(first_result full parentHash)] at status
  refine ⟨Option.isNone_iff_eq_none.mp status.1, status.2.1, ?_⟩
  have done := Witness.wrun_done (first_result full parentHash) (first_agree full parentHash)
  change Witness.storOf (firstPost full parentHash).state depositAddr 0 = B256.max
  rw [done.2.2 (firstPost full parentHash) rfl]
  exact (done.2.1.2.2.1 depositAddr 0).trans status.2.2.1

private theorem first_exec : Nonempty (Exec 0 (initSevm (firstMsg full parentHash)) (initDevm (firstMsg full parentHash)) (.ok (firstPost full parentHash))) := by
  exact lift_exact_noExec Deposit.userPath.check Deposit.userPath.jumps rfl Deposit.userPath.noExec
    (Witness.wrun_exact rfl (first_agree full parentHash) (first_result_actual full parentHash))

private theorem first_enter : (Frame.ofCall (firstMsg full parentHash)).enter = .run (initEvm (firstMsg full parentHash)) := by
  exact Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl (by change pragueRules.isPrecomp depositAddr = false; decide)

private theorem first_settle : (Frame.ofCall (firstMsg full parentHash)).settle (.ok (firstPost full parentHash)) = .ok (firstPost full parentHash) := by
  rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
  simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, (first_facts full parentHash).1,
    Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind,
    Devm.recordTouch_of_not_touchedSweep (show (firstMsg full parentHash).benv.stat.rules.settle.touchedSweep = false from rfl)]

/-- The actual raw child and its complete settlement bound its returned gas. -/
private theorem first_gas_bound : (firstPost full parentHash).gasLeft ≤ 1008935 := by
  have settled := Frame.settle_gasLe
    (Classical.choice (first_exec full parentHash)).settledGasLe (first_settle full parentHash)
  have gas := Nat.le_trans (Devm.gasLeft_le_gasMeasure (firstPost full parentHash)) settled
  change (firstPost full parentHash).gasLeft ≤
    SystemWordWriter.forwardedGas (base full parentHash) depositAddr firstGas at gas
  rw [first_forwarded full parentHash] at gas
  exact gas

private def afterFirst : Devm := SystemWordWriter.post (base full parentHash) depositAddr 0 firstGas (firstPost full parentHash)

private theorem first_resume :
    Resume.run (.call (SystemWordWriter.parent (base full parentHash) depositAddr 0 firstGas) 0 0)
      ((Frame.ofCall (firstMsg full parentHash)).settle (.ok (firstPost full parentHash))) = .ok (afterFirst full parentHash) := by
  rw [(first_settle full parentHash), Resume.run_call_ok (by rw [(first_facts full parentHash).1]; rfl) (by change (0 : Nat) < 1024; decide)]
  rfl

private theorem first_output : (firstPost full parentHash).output = [] := by
  have status := (first_status full parentHash)
  rw [(first_result full parentHash)] at status
  exact status.2.2.2.1

private def secondGas : Nat := (afterFirst full parentHash).gasLeft - 17
private def secondState : Devm :=
  (afterFirst full parentHash).setMach ⟨[(secondGas full parentHash).toB256, depositAddr.toBytes.toB256, 0, 0, 0, 0, 0],
    (afterFirst full parentHash).memory, (secondGas full parentHash), (afterFirst full parentHash).stateGas⟩
private def secondBare : Devm :=
  (afterFirst full parentHash).setMach ⟨[], (afterFirst full parentHash).memory, (secondGas full parentHash), (afterFirst full parentHash).stateGas⟩
private def secondForwarded : Nat := except64th ((secondGas full parentHash) - 100)
private def secondParent : Devm :=
  callSpawnParent (addAccessedAddress (secondBare full parentHash) depositAddr) ((secondForwarded full parentHash) + 100) 0 0 0 0
private def secondMsg : Msg :=
  callSpawnMsg (sevm full parentHash) (secondParent full parentHash) (secondForwarded full parentHash) depositAddr depositAddr 0 0 Deposit.code false

private theorem second_cost : accessCost depositAddr (afterFirst full parentHash).accessedAddresses = 100 := by
  have present : depositAddr ∈ (afterFirst full parentHash).accessedAddresses := by
    change depositAddr ∈ (((base full parentHash).accessedAddresses.insert depositAddr).union (firstPost full parentHash).accessedAddresses)
    exact Std.HashSet.mem_union_of_left Std.HashSet.mem_insert_self
  unfold accessCost
  rw [ite_eq_left present]
  rfl

/-- Only the fixed writer bytes are evaluated here; worlds and metadata stay opaque. -/
private theorem pure_reset_prefix (full : Bool) (s : Sevm) (d : Devm) (g : Nat) :
    let sta := { s with code := writerCode full, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 8 ⟨64, sta, d.setMach ⟨[1], d.memory, g + 17, d.stateGas⟩⟩ =
      some ⟨92, sta, d.setMach ⟨[g.toB256, depositAddr.toBytes.toB256, 0, 0, 0, 0, 0],
        d.memory, g, d.stateGas⟩⟩ := by
  dsimp only
  cases full
  all_goals revert s d g
  all_goals kernel_forall_rfl_and

private theorem reset_prefix (full : Bool) (s : Sevm) (d : Devm) (g : Nat)
    (code : s.code = writerCode full) (fork : s.benvStat.fork = .prague)
    (stack : d.stack = [1]) (gas : d.gasLeft = g + 17) :
    ConcreteRun.stepN 8 ⟨64, s, d⟩ =
      some ⟨92, s, d.setMach ⟨[g.toB256, depositAddr.toBytes.toB256, 0, 0, 0, 0, 0],
        d.memory, g, d.stateGas⟩⟩ := by
  have sta : ({ s with
      code := writerCode full
      benvStat := { s.benvStat with fork := .prague } } : Sevm) = s := by
    rw [← code, ← fork]
  have mach : d.setMach ⟨[1], d.memory, g + 17, d.stateGas⟩ = d := by
    rw [← stack, ← gas]
    rfl
  have run := pure_reset_prefix full s d g
  dsimp only at run
  rw [sta, mach] at run
  exact run
private theorem second_gas_range : 101 ≤ (secondGas full parentHash) ∧ (secondGas full parentHash) < 2 ^ 256 := by
  have bound := first_gas_bound full parentHash
  have scalar : secondGas full parentHash = (16014 + (firstPost full parentHash).gasLeft) - 17 := by
    unfold secondGas afterFirst
    change (firstGas - (SystemWordWriter.forwardedGas (base full parentHash) depositAddr firstGas +
      accessCost depositAddr (base full parentHash).accessedAddresses) +
        (firstPost full parentHash).gasLeft) - 17 = _
    rw [first_forwarded full parentHash, first_cost full parentHash]
    rfl
  rw [scalar]
  have top : 1027549 < 2 ^ 256 := by decide
  constructor <;> omega

private theorem second_prefix : ConcreteRun.stepN 8 ⟨64, (sevm full parentHash), (afterFirst full parentHash)⟩ = some ⟨92, (sevm full parentHash), (secondState full parentHash)⟩ := by
  have stack : (afterFirst full parentHash).stack = [1] :=
    (SystemWordWriter.post_facts (base full parentHash) (firstPost full parentHash)
      depositAddr 0 firstGas (first_output full parentHash)).2.2.2.2.2.2.2.2
  have gas : (afterFirst full parentHash).gasLeft = secondGas full parentHash + 17 := by
    have bound := (second_gas_range full parentHash).1
    unfold secondGas at bound ⊢
    omega
  exact reset_prefix full (sevm full parentHash) (afterFirst full parentHash)
    (secondGas full parentHash) (message_code full parentHash) rfl stack gas

private theorem second_call_at : Ninst.At (sevm full parentHash).code 92 (.exec .call) := by
  cases full
  all_goals
    unfold Ninst.At
    cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private theorem first_accounts : (firstFinal full parentHash).acs = (accounts full parentHash) := by
  cases full
  all_goals
    unfold firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
    rw [first_forwarded]
    cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private theorem afterFirst_code : (afterFirst full parentHash).getCode depositAddr = Deposit.code := by
  have done := Witness.wrun_done (first_result full parentHash) (first_agree full parentHash)
  have h := congrArg Acct.code (done.2.1.2.2.2 depositAddr)
  change ((firstFinal full parentHash).devm.state.get depositAddr).code = (Witness.lookupA (firstFinal full parentHash).acs depositAddr).code at h
  rw [← done.2.2 (firstPost full parentHash) rfl, (first_accounts full parentHash)] at h
  change ((firstPost full parentHash).state.get depositAddr).code = Deposit.code
  rw [h]
  cases parentHash <;> simp only [accounts, Option.elim, List.append_nil,
    List.cons_append, List.nil_append, Witness.lookupA]
  all_goals rw [ite_eq_right (by decide : senderE ≠ depositAddr),
    ite_eq_right (by decide : exitAddr ≠ depositAddr)]
  all_goals rfl

private theorem second_delegation :
    accessDelegation (addAccessedAddress (secondBare full parentHash) depositAddr) depositAddr =
      (false, depositAddr, Deposit.code, 0, addAccessedAddress (secondBare full parentHash) depositAddr) := by
  unfold accessDelegation
  change (match getDelegatedCodeAddress ((afterFirst full parentHash).getCode depositAddr) with
    | some adr => _ | none => _) = _
  rw [(afterFirst_code full parentHash)]
  have nd : getDelegatedCodeAddress Deposit.code = none := Deposit.submissions.undelegated
  rw [nd]
  change (false, depositAddr, (afterFirst full parentHash).getCode depositAddr, 0,
    addAccessedAddress (secondBare full parentHash) depositAddr) = _
  rw [(afterFirst_code full parentHash)]

private theorem second_split :
    calculateMsgCallGas 0 (secondGas full parentHash).toB256.toNat (secondGas full parentHash) 0 100 =
      ((secondForwarded full parentHash) + 100, (secondForwarded full parentHash)) := by
  rw [calculateMsgCallGas_zero (by have h := (second_gas_range full parentHash).1; omega),
    B256.toNat_toB256_of_lt (second_gas_range full parentHash).2]
  simp only [Nat.sub_zero]
  have bound : except64th ((secondGas full parentHash) - 100) ≤ (secondGas full parentHash) := by
    unfold except64th
    omega
  rw [Nat.min_eq_right bound]
  rfl

private theorem second_spawn :
    Evm.step ⟨92, (sevm full parentHash), (secondState full parentHash)⟩ =
      .spawn (Frame.ofCall (secondMsg full parentHash)) (.call (secondParent full parentHash) 0 0) 93 := by
  have spawn := Xinst.step_call_zero_value_spawn
    (sevm := (sevm full parentHash)) (devm := (secondState full parentHash)) (gw := (secondGas full parentHash).toB256) (cw := depositAddr.toBytes.toB256)
    (iiw := 0) (isw := 0) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := depositAddr) (code := Deposit.code) (dgc := 0)
    (d1 := addAccessedAddress (secondBare full parentHash) depositAddr) (ext := 0)
    (acc := 100) (mcs := (secondForwarded full parentHash)) (mcc := (secondForwarded full parentHash) + 100)
    (CoveredFork.prague.callEra false) rfl ?_ ?_ ?_ (second_split full parentHash) ?_ (by change (1024 : Nat) ≠ 0; decide)
  · rw [Evm.step_next (second_call_at full parentHash)]
    simp only [Ninst.step_exec, spawn, XStep.toStep, secondMsg, secondParent, secondBare,
      SystemWordWriter.target_word, B256.toNat_zero, Nat.add_zero, Nat.reduceAdd]
  · apply Devm.extCost_covered
    simp only [secondState, Devm.memory_setMach, B256.toNat_zero]
    rcases SystemWordWriter.post_facts (base full parentHash) (firstPost full parentHash) depositAddr 0 firstGas (first_output full parentHash) with
      ⟨_, _, _, _, _, _, _, memory, _⟩
    rw [show (afterFirst full parentHash).memory = SystemWordWriter.wordMemory 0 from memory,
      show (SystemWordWriter.wordMemory 0).size = 32 from Mem.size_write_word]
    rfl
  · rw [SystemWordWriter.target_word]
    simpa only [secondState, secondBare, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.setMach_setMach] using (second_delegation full parentHash)
  · rw [SystemWordWriter.target_word]
    simpa only [secondState, Devm.setMach_accessedAddresses, Nat.add_zero] using (second_cost full parentHash)
  · change (secondForwarded full parentHash) + 100 + 0 ≤ (secondGas full parentHash)
    have range := (second_gas_range full parentHash).1
    unfold secondForwarded except64th
    omega

private def secondAddresses : List Adr := depositAddr :: (firstAddresses ++ (firstFinal full parentHash).adrs)
private def secondCfg : Witness.Cfg :=
  ⟨initDevm (secondMsg full parentHash), Deposit.t_0000_c0, [], (firstFinal full parentHash).keys, (secondAddresses full parentHash),
    (firstFinal full parentHash).stor, (firstFinal full parentHash).acs⟩

private theorem second_world : (initDevm (secondMsg full parentHash)).state = (firstPost full parentHash).state := rfl

private theorem second_keys : (initDevm (secondMsg full parentHash)).accessedStorageKeys =
    (∅ : Std.HashSet (Adr × B256)).union (firstPost full parentHash).accessedStorageKeys := rfl

private theorem second_addresses : (initDevm (secondMsg full parentHash)).accessedAddresses =
    (((base full parentHash).accessedAddresses.insert depositAddr).union (firstPost full parentHash).accessedAddresses).insert depositAddr := rfl

private theorem first_accesses : (firstPost full parentHash).accessedStorageKeys = (firstFinal full parentHash).devm.accessedStorageKeys ∧
    (firstPost full parentHash).accessedAddresses = (firstFinal full parentHash).devm.accessedAddresses := by
  cases full
  all_goals
    unfold firstPost firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
    simp only [first_forwarded]
    constructor
    all_goals cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private theorem second_agree : Witness.Agree (secondCfg full parentHash) := by
  have done := Witness.wrun_done (first_result full parentHash) (first_agree full parentHash)
  have world := done.2.2 (firstPost full parentHash) rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    change k ∈ (initDevm (secondMsg full parentHash)).accessedStorageKeys ↔ k ∈ (firstFinal full parentHash).keys
    have union : k ∈ (∅ : Std.HashSet (Adr × B256)).union (firstPost full parentHash).accessedStorageKeys ↔
        k ∈ (∅ : Std.HashSet (Adr × B256)) ∨ k ∈ (firstPost full parentHash).accessedStorageKeys := Std.HashSet.mem_union_iff
    rw [(second_keys full parentHash), union, (first_accesses full parentHash).1]
    rw [done.2.1.1 k]
    exact ⟨fun h => h.elim (fun h => (Std.HashSet.not_mem_empty h).elim) id, Or.inr⟩
  · intro a
    change a ∈ (initDevm (secondMsg full parentHash)).accessedAddresses ↔ a ∈ (secondAddresses full parentHash)
    have union : a ∈ ((base full parentHash).accessedAddresses.insert depositAddr).union (firstPost full parentHash).accessedAddresses ↔
        a ∈ (base full parentHash).accessedAddresses.insert depositAddr ∨ a ∈ (firstPost full parentHash).accessedAddresses := by
      simpa only [Std.HashSet.mem_iff_contains, Union.union, Std.HashSet.instUnion] using
        (Std.HashSet.mem_union_iff (m₁ := (base full parentHash).accessedAddresses.insert depositAddr)
          (m₂ := (firstPost full parentHash).accessedAddresses) (k := a))
    rw [(second_addresses full parentHash), Std.HashSet.mem_insert, union, (first_accesses full parentHash).2]
    rw [done.2.1.2.1 a]
    have initial := (first_agree full parentHash).2.1 a
    change a ∈ (base full parentHash).accessedAddresses.insert depositAddr ↔ a ∈ firstAddresses at initial
    rw [initial]
    simp only [secondAddresses, List.mem_cons, List.mem_append, beq_iff_eq]
    exact or_congr eq_comm Iff.rfl
  · intro a k
    change Witness.storOf (initDevm (secondMsg full parentHash)).state a k = Witness.lookupS (firstFinal full parentHash).stor a k
    rw [(second_world full parentHash), world]
    exact done.2.1.2.2.1 a k
  · intro a
    change Witness.acctView ((initDevm (secondMsg full parentHash)).state.get a) = Witness.lookupA (firstFinal full parentHash).acs a
    rw [(second_world full parentHash), world]
    exact done.2.1.2.2.2 a

private def secondResult : Witness.Res := Witness.wrun Deposit.cert.prog ((initSevm (secondMsg full parentHash)).withOrig .empty) 512 (secondCfg full parentHash)
private def secondPost : Devm := match (secondResult full parentHash) with | .done (.halted post) _ => post | _ => default
private def secondFinal : Witness.Cfg := match (secondResult full parentHash) with | .done _ cl => cl | _ => (secondCfg full parentHash)
private def secondCheck : Bool :=
  match (secondResult full parentHash) with
  | .done (.halted post) cl => decide (post.error = none ∧ 0 ≤ post.refundCounter ∧
      Witness.lookupS cl.stor depositAddr 0 = 0 ∧ post.output = [] ∧
      post.accountsToDelete.isEmpty = true)
  | _ => false

private theorem second_check : (secondCheck full parentHash) = true := by
  cases full
  all_goals
    unfold secondCheck secondResult secondCfg secondMsg secondParent secondBare
      secondForwarded secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
      firstPost firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
    simp only [first_forwarded, first_cost]
    cases parentHash with
    | none => kernel_rfl
    | some h =>
      revert h
      kernel_forall_rfl_and

private theorem second_status :
    (match (secondResult full parentHash) with
      | .done (.halted post) cl => post.error = none ∧ 0 ≤ post.refundCounter ∧
          Witness.lookupS cl.stor depositAddr 0 = 0 ∧ post.output = [] ∧
          post.accountsToDelete.isEmpty = true
      | _ => False) := by
  have check := (second_check full parentHash)
  cases h : (secondResult full parentHash) with
  | cont c => simp only [secondCheck, h, Bool.false_eq_true] at check
  | stuck => simp only [secondCheck, h, Bool.false_eq_true] at check
  | done outcome cl =>
      cases outcome with
      | returned d => simp only [secondCheck, h, Bool.false_eq_true] at check
      | halted post => simpa only [secondCheck, h, decide_eq_true_eq] using check

private theorem second_result : (secondResult full parentHash) = .done (.halted (secondPost full parentHash)) (secondFinal full parentHash) := by
  have status := (second_status full parentHash)
  cases h : (secondResult full parentHash) with
  | cont c => rw [h] at status; contradiction
  | stuck => rw [h] at status; contradiction
  | done outcome cl =>
      cases outcome with
      | returned d => rw [h] at status; contradiction
      | halted post => simp only [secondPost, secondFinal, h]

/-- The computation is tied to the original spawned message before lifting. -/
private theorem second_result_actual :
    Witness.wrun Deposit.cert.prog (initSevm (secondMsg full parentHash)) 512 (secondCfg full parentHash) =
      .done (.halted (secondPost full parentHash)) (secondFinal full parentHash) := by
  have orig : NodeWalk.OrigAgree (.empty : State)
      (initSevm (secondMsg full parentHash)).benvStat.origState := by
    change NodeWalk.OrigAgree (.empty : State) (state full parentHash)
    exact original_empty full parentHash
  rw [← Witness.wrun_withOrig orig Deposit.cert.prog 512 (secondCfg full parentHash)]
  exact second_result full parentHash

private theorem second_facts : (secondPost full parentHash).error = none ∧ 0 ≤ (secondPost full parentHash).refundCounter ∧
    (secondPost full parentHash).getStorVal depositAddr 0 = 0 ∧ (secondPost full parentHash).output = [] := by
  have status := (second_status full parentHash)
  rw [(second_result full parentHash)] at status
  refine ⟨status.1, status.2.1, ?_, status.2.2.2.1⟩
  have done := Witness.wrun_done (second_result full parentHash) (second_agree full parentHash)
  change Witness.storOf (secondPost full parentHash).state depositAddr 0 = 0
  rw [done.2.2 (secondPost full parentHash) rfl]
  exact (done.2.1.2.2.1 depositAddr 0).trans status.2.2.1

private theorem second_exec : Nonempty (Exec 0 (initSevm (secondMsg full parentHash)) (initDevm (secondMsg full parentHash)) (.ok (secondPost full parentHash))) := by
  exact lift_exact_noExec Deposit.userPath.check Deposit.userPath.jumps rfl Deposit.userPath.noExec
    (Witness.wrun_exact rfl (second_agree full parentHash) (second_result_actual full parentHash))

private theorem second_enter : (Frame.ofCall (secondMsg full parentHash)).enter = .run (initEvm (secondMsg full parentHash)) := by
  exact Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl (by change pragueRules.isPrecomp depositAddr = false; decide)

private theorem second_settle : (Frame.ofCall (secondMsg full parentHash)).settle (.ok (secondPost full parentHash)) = .ok (secondPost full parentHash) := by
  rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
  simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, (second_facts full parentHash).1,
    Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind,
    Devm.recordTouch_of_not_touchedSweep (show (secondMsg full parentHash).benv.stat.rules.settle.touchedSweep = false from rfl)]

private def afterSecond : Devm := callChildPost (secondParent full parentHash) (secondPost full parentHash) 0 0

/-- Retained original private scalar fact. The successor context uses derived
bounds; its all-eight history does not require this exact intermediate numeral. -/
private theorem pair_gas : (afterSecond full none).gasLeft = 994955 := by
  cases full
  all_goals
    unfold afterSecond secondPost secondResult secondCfg secondMsg secondParent secondBare
      secondForwarded secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
      firstPost firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
    simp only [first_forwarded, first_cost]
    kernel_rfl

private theorem pair_snapshot : (initSevm (secondMsg full parentHash)).benvStat.origState = (state full parentHash) := rfl

private theorem pair_original :
    (initDevm (secondMsg full parentHash)).getOrigStorVal (initSevm (secondMsg full parentHash)) depositAddr 0 = 0 := by
  unfold Devm.getOrigStorVal
  split
  · rfl
  · change ((state full parentHash).get depositAddr).stor.get 0 = 0
    cases parentHash <;> simp only [state, builderWorld, baseWorld]
    all_goals repeat rw [State.get_setPresent_ne _ (by decide)]
    all_goals rw [State.get_setPresent_self]
    all_goals rfl

private theorem pair_dirty : (initDevm (secondMsg full parentHash)).getStorVal depositAddr 0 = B256.max := by
  change ((initDevm (secondMsg full parentHash)).state.getStor depositAddr).get 0 = B256.max
  rw [(second_world full parentHash)]
  exact (first_facts full parentHash).2.2

private theorem second_resume :
    Resume.run (.call (secondParent full parentHash) 0 0) ((Frame.ofCall (secondMsg full parentHash)).settle (.ok (secondPost full parentHash))) =
      .ok (afterSecond full parentHash) := by
  rw [(second_settle full parentHash), Resume.run_call_ok (by rw [(second_facts full parentHash).1]; rfl) (by change (0 : Nat) < 1024; decide)]
  rfl

private theorem stop_at : (sevm false parentHash).code.getInst 93 = some (.last .stop) := by
  cases parentHash with
  | none => kernel_rfl
  | some h =>
    revert h
    kernel_forall_rfl_and

private theorem full_tail_at : Ninst.At (sevm true parentHash).code 93 (.reg .pop) := by
  unfold Ninst.At
  cases parentHash with
  | none => kernel_rfl
  | some h =>
    revert h
    kernel_forall_rfl_and

private theorem stop_step : Evm.step ⟨93, (sevm false parentHash), (afterSecond false parentHash)⟩ =
    .halt (.ok (afterSecond false parentHash)) := Evm.step_last (stop_at parentHash)

private noncomputable def firstRun : Exec 0 (initSevm (firstMsg full parentHash))
    (initDevm (firstMsg full parentHash)) (.ok (firstPost full parentHash)) := Classical.choice (first_exec full parentHash)
private noncomputable def secondRun : Exec 0 (initSevm (secondMsg full parentHash))
    (initDevm (secondMsg full parentHash)) (.ok (secondPost full parentHash)) := Classical.choice (second_exec full parentHash)

private noncomputable def pairTail {out : Execution}
    (rest : Exec 93 (sevm full parentHash) (afterSecond full parentHash) out) : Exec 92 (sevm full parentHash) (secondState full parentHash) out :=
  .runOk (second_spawn full parentHash) (second_enter full parentHash) (secondRun full parentHash) (second_resume full parentHash) rest
private noncomputable def pairMiddle {out : Execution}
    (rest : Exec 93 (sevm full parentHash) (afterSecond full parentHash) out) : Exec 64 (sevm full parentHash) (afterFirst full parentHash) out :=
  ConcreteRun.Exec.ofStepN 8 (second_prefix full parentHash) ((pairTail full parentHash) rest)
private noncomputable def pairCall {out : Execution}
    (rest : Exec 93 (sevm full parentHash) (afterSecond full parentHash) out) : Exec 63 (sevm full parentHash) (callState full parentHash) out :=
  .runOk (first_spawn full parentHash) (first_enter full parentHash) (firstRun full parentHash) (first_resume full parentHash) ((pairMiddle full parentHash) rest)
private noncomputable def pairRun {out : Execution}
    (rest : Exec 93 (sevm full parentHash) (afterSecond full parentHash) out) : Exec 0 (sevm full parentHash) (base full parentHash) out :=
  ConcreteRun.Exec.ofStepN 10 (first_prefix full parentHash) ((pairCall full parentHash) rest)

private theorem first_commits : Execution.commits (.ok (firstPost full parentHash)) = true := by
  change (firstPost full parentHash).error.isNone = true
  rw [(first_facts full parentHash).1]
  rfl
private theorem second_commits : Execution.commits (.ok (secondPost full parentHash)) = true := by
  change (secondPost full parentHash).error.isNone = true
  rw [(second_facts full parentHash).1]
  rfl

private noncomputable def latchFrame : Exec.Frame := .ofRun (firstRun full parentHash) (first_commits full parentHash)
private noncomputable def resetFrame : Exec.Frame := .ofRun (secondRun full parentHash) (second_commits full parentHash)

private theorem pair_kept {out : Execution}
    (rest : Exec 93 (sevm full parentHash) (afterSecond full parentHash) out) :
    Exec.keptAt depositAddr ((pairRun full parentHash) rest) =
      (latchFrame full parentHash) :: (resetFrame full parentHash) :: Exec.keptAt depositAddr rest := by
  have firstSettles : Frame.settlementCommits (Frame.ofCall (firstMsg full parentHash)) (.ok (firstPost full parentHash)) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits (first_commits full parentHash)
  have secondSettles : Frame.settlementCommits (Frame.ofCall (secondMsg full parentHash)) (.ok (secondPost full parentHash)) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits (second_commits full parentHash)
  calc
    Exec.keptAt depositAddr ((pairRun full parentHash) rest) = Exec.keptAt depositAddr ((pairCall full parentHash) rest) :=
      ConcreteRun.Exec.keptAt_ofStepN depositAddr 10 (first_prefix full parentHash) ((pairCall full parentHash) rest)
    _ = (latchFrame full parentHash) :: Exec.keptAt depositAddr ((pairMiddle full parentHash) rest) :=
      Exec.keptAt_settled_here (a := depositAddr) (first_spawn full parentHash) (first_enter full parentHash) (firstRun full parentHash)
        (first_resume full parentHash) ((pairMiddle full parentHash) rest) firstSettles rfl
    _ = (latchFrame full parentHash) :: Exec.keptAt depositAddr ((pairTail full parentHash) rest) :=
      congrArg (List.cons (latchFrame full parentHash))
        (ConcreteRun.Exec.keptAt_ofStepN depositAddr 8 (second_prefix full parentHash) ((pairTail full parentHash) rest))
    _ = (latchFrame full parentHash) :: (resetFrame full parentHash) :: Exec.keptAt depositAddr rest :=
      congrArg (List.cons (latchFrame full parentHash))
        (Exec.keptAt_settled_here (a := depositAddr) (second_spawn full parentHash) (second_enter full parentHash) (secondRun full parentHash)
          (second_resume full parentHash) rest secondSettles rfl)

private noncomputable def fullRun : Exec 0 (sevm false parentHash) (base false parentHash) (.ok (afterSecond false parentHash)) :=
  (pairRun false parentHash) (.halt (stop_step parentHash))

private theorem retained : Exec.keptAt depositAddr (fullRun parentHash) = [(latchFrame false parentHash), (resetFrame false parentHash)] := by
  have kept := (pair_kept false parentHash) (.halt (stop_step parentHash))
  rw [Exec.keptAt] at kept
  exact kept

private theorem full_facts : (afterSecond false parentHash).error = none ∧ 0 ≤ (afterSecond false parentHash).refundCounter ∧
    (afterSecond false parentHash).output = [] := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · change 0 ≤ (0 + (firstPost false parentHash).refundCounter) + (secondPost false parentHash).refundCounter
    have one := (first_facts false parentHash).2.1
    have two := (second_facts false parentHash).2.1
    omega
  · rfl

private theorem message_enter : (Frame.ofCall (msg false parentHash)).enter = .run (initEvm (msg false parentHash)) := by
  exact Frame.enter_run_of_nonprecompile (after_transfer false parentHash) rfl (by change pragueRules.isPrecomp systemAddress = false; decide)

private noncomputable def root : Root := ⟨Frame.ofCall (msg false parentHash), initEvm (msg false parentHash), .ok (afterSecond false parentHash), (fullRun parentHash)⟩

private theorem root_retained : Root.keptAt depositAddr (root parentHash) = [(latchFrame false parentHash), (resetFrame false parentHash)] := by
  have commits : Frame.settlementCommits (Frame.ofCall (msg false parentHash)) (.ok (afterSecond false parentHash)) = true := by
    apply Frame.settlementCommits_ofCall_of_raw_commits
    change (afterSecond false parentHash).error.isNone = true
    rw [(full_facts parentHash).1]
    rfl
  change (if h : Frame.settlementCommits (Frame.ofCall (msg false parentHash)) (.ok (afterSecond false parentHash)) = true then
    if (initSevm (msg false parentHash)).currentTarget = depositAddr then _ else Exec.keptAt depositAddr (fullRun parentHash) else []) = _
  rw [dite_eq_left commits, ite_eq_right (show (initSevm (msg false parentHash)).currentTarget ≠ depositAddr from by change systemAddress ≠ depositAddr; decide)]
  exact (retained parentHash)

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

private theorem message_undelegated : getDelegatedCodeAddress (msg false parentHash).code = none := by
  rw [(message_code false parentHash)]
  exact writer_undelegated

private theorem message_resolved : messageCallExecutionMessage (msg false parentHash) = (msg false parentHash) := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  have nd : (msg false parentHash).benv.stat.rules.delegatedCodeAddress (msg false parentHash).code = none := by
    unfold ForkRules.delegatedCodeAddress
    rw [(message_undelegated parentHash)]
    split <;> rfl
  rw [nd]

private theorem message_entry : messageEntry (msg false parentHash) = some (Frame.ofCall (msg false parentHash), initEvm (msg false parentHash)) := by
  unfold messageEntry legacyEntry
  change (match messageCallDelegation (msg false parentHash) with
    | .ok (d, _) => enteredFrame (Frame.ofCall (messageCallExecutionMessage d))
    | .error _ => none) = _
  have delegated : messageCallDelegation (msg false parentHash) = .ok ((msg false parentHash), 0) := by
    unfold messageCallDelegation processMessageCall.legacyAuthorization
    rfl
  rw [delegated]
  change enteredFrame (Frame.ofCall (messageCallExecutionMessage (msg false parentHash))) = _
  rw [(message_resolved parentHash)]
  unfold enteredFrame
  rw [(message_enter parentHash)]

private def messageOut : MsgCallOutput :=
  { gasLeft := (afterSecond false parentHash).gasLeft, refundCounter := ((0 + (afterSecond false parentHash).refundCounter.toNat : Nat) : Int)
    logs := (afterSecond false parentHash).logs, accountsToDelete := (afterSecond false parentHash).accountsToDelete
    error := none, returnData := (afterSecond false parentHash).output, touchedAccounts := (afterSecond false parentHash).meta.touchedAccounts }

private theorem message_process : processMessageCall (msg false parentHash) = .ok ((afterSecond false parentHash).state, (messageOut parentHash)) := by
  apply processMessageCall_call_of_message rfl rfl rfl (message_undelegated parentHash)
  · apply processMessage_call_of_exec (after_transfer false parentHash) rfl (by change pragueRules.isPrecomp systemAddress = false; decide)
      ((exec_iff_exec_eq 0 (sevm false parentHash) (base false parentHash) (.ok (afterSecond false parentHash))).mp ⟨(fullRun parentHash)⟩) (full_facts parentHash).1 rfl
  · exact (full_facts parentHash).1
  · exact Int.toNat?_eq_some_of_nonneg (full_facts parentHash).2.1

private theorem message_roots : MessageRoots (msg false parentHash) (afterSecond false parentHash).state (messageOut parentHash) [(root parentHash)] := by
  refine ⟨(message_process parentHash), ?_⟩
  rw [(message_entry parentHash)]
  rfl

private theorem tx_valid : validateTransaction (benv false parentHash).stat.rules txD 0 = .ok (21000, 21000) := by
  exact validateTransaction_ok_of_facts rfl
    (txD_intrinsic rfl rfl rfl rfl rfl 0) (by decide) (by decide) rfl rfl

private theorem sender_account : (benv false parentHash).beginTransaction.state.get senderE = senderAcct 2 (2 ^ 100) := by
  change (state false parentHash).get senderE = _
  exact State.get_setPresent_self _ _ _

private theorem tx_checked : checkTransaction (benv false parentHash).beginTransaction
    (transactionPreludeBout .init txD 0) txD = .ok (senderE, 2, [], 0) := by
  apply checkTransaction_ok_of_parts (maxFee := 2 ^ 20 * 8) (maxFee' := 2 ^ 20 * 8)
  · exact checkTransactionGasLimits_ok_of_room rfl (by change (1048576 : Nat) ≤ 60000000; decide) (by exact Nat.zero_le _)
  · exact checkTransactionChainId_two rfl rfl
  · exact (recovered false parentHash)
  · exact checkTransactionGasFee_two (benv := (benv false parentHash).beginTransaction) (tx := txD)
      (maxPriorityFee := 1) (maxFee := 8) rfl (by decide) (by change (1 : Nat) ≤ 8; decide) (by decide)
  · exact checkTransactionBlobData_two rfl _
  · exact checkTransactionReceiver_two rfl
  · exact checkTransactionAuthorizationList_two rfl
  · rw [(sender_account parentHash)]
    exact checkTransactionSenderAccount_ok_of_noCode rfl (by decide) rfl

private theorem tx_debit : ((benv false parentHash).state.incrNonce senderE).subBal senderE
    (txD.gas * 2 + transactionBlobGasFee (benv false parentHash) txD).toB256 = some (debit false parentHash) := by
  exact (debit_eq false parentHash)

private theorem tx_message : transactionMessage (benv false parentHash) .init txD 0 = .ok (senderE, (msg false parentHash)) := by
  have valid : validateTransaction (benv false parentHash).beginTransaction.stat.rules txD 0 = .ok (21000, 21000) := (tx_valid parentHash)
  have debit : ((benv false parentHash).beginTransaction.state.incrNonce senderE).subBal senderE
      (txD.gas * 2 + transactionBlobGasFee (benv false parentHash).beginTransaction txD).toB256 = some (debit false parentHash) := (debit_eq false parentHash)
  have tenv : transactionTenvAt (benv false parentHash).beginTransaction txD 0 senderE 2 21000 [] =
      transactionTenv (benv false parentHash).beginTransaction txD 0 senderE 2 21000 [] := rfl
  unfold transactionMessage
  dsimp only
  rw [recoverValidationSender_of_stateGas_none txD rfl]
  simp only [valid, (tx_checked parentHash), debit, Except.mapError, bind, Except.bind, Option.toExcept]
  rw [tenv, (prepared false parentHash)]

private theorem transaction_roots : ∃ stop bout,
    TransactionRoots (benv false parentHash) .init txD 0 stop bout senderE [(root parentHash)] := by
  have refund : Int.toNat? (messageOut parentHash).refundCounter = some (afterSecond false parentHash).refundCounter.toNat := by
    change Int.toNat? ((0 + (afterSecond false parentHash).refundCounter.toNat : Nat) : Int) = _
    simp only [Nat.zero_add]
    exact Int.toNat?_eq_some_of_nonneg (i := ((afterSecond false parentHash).refundCounter.toNat : Int)) (by omega)
  obtain ⟨bout, process, _, _⟩ := processTransaction_of_stages_gasUsed
    (bout := .init) (index := 0) rfl rfl rfl rfl (tx_valid parentHash) (tx_checked parentHash) (tx_debit parentHash) (prepared false parentHash) (message_process parentHash) refund
  exact ⟨_, bout, process, (msg false parentHash), (afterSecond false parentHash).state, (messageOut parentHash), (tx_message parentHash), (message_roots parentHash)⟩

private theorem reset_original :
    (initDevm (secondMsg false parentHash)).getOrigStorVal (initSevm (secondMsg false parentHash)) depositAddr 0 = 0 :=
  (pair_original false parentHash)

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
  obtain ⟨stop, bout, roots⟩ := (transaction_roots none)
  refine ⟨(benv false none), stop, bout, senderE, (root none), (latchFrame false none), (resetFrame false none), rfl,
    ?_, ?_, (recovered false none), roots, (root_retained none), rfl, ?_, ?_, (first_facts false none).2.2,
    rfl, rfl, ?_, (reset_original none), (second_facts false none).2.2.1⟩
  · change ((state false none).get depositAddr).code = Deposit.code
    unfold state builderWorld baseWorld
    rw [State.get_setPresent_ne _ (by decide : senderE ≠ depositAddr),
      State.get_setPresent_ne _ (by decide : exitAddr ≠ depositAddr), State.get_setPresent_self]
  · change ((state false none).get exitAddr).code = Exit.code
    unfold state builderWorld baseWorld
    rw [State.get_setPresent_ne _ (by decide : senderE ≠ exitAddr), State.get_setPresent_self]
  · change (firstMsg false none).data.length = 32
    rw [(first_data false none), B256.length_toBytes]
  · exact (first_agree false none).2.2.1 depositAddr 0
  · change ((initDevm (secondMsg false none)).state.getStor depositAddr).get 0 = B256.max
    rw [(second_world false none)]
    exact (first_facts false none).2.2

end Blanc.Composition.BuilderRequestApplicabilityCalls
