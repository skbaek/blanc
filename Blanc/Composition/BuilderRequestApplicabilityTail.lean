import Blanc.Composition.BuilderRequestApplicabilityCalls
import Blanc.Lift.BuilderRequest.Delivery
import Blanc.Lift.BuilderRequest.Exit.Frames
import Blanc.Lift.BuilderRequest.Exit.SystemCall
import Blanc.Lift.RequestSystem.CoveredCall
import Blanc.Lift.RequestSystem.Effects
import Blanc.SystemWordWriterKept

/-! Continuation of the signed SYSTEM transaction: Exit latch and warm dirty reset. -/
namespace Blanc.Composition.BuilderRequestApplicabilityTail

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.BuilderRequest Blanc.Lift.RequestSystem
open Blanc.Composition.BuilderRequestApplicabilityInput
open Blanc.Composition.BuilderRequestPublic (depositAddr exitAddr)
open Blanc.Lift.WithdrawalRequest.FloodTx (senderE)
open private sevm base firstGas firstMsg firstCfg firstPost firstFinal firstResult
  first_forwarded first_cost firstAddresses secondAddresses secondGas secondForwarded
  secondParent secondBare secondMsg secondCfg secondResult secondPost secondFinal
  second_result second_agree second_facts second_exec second_settle first_facts
  afterFirst afterSecond pairRun latchFrame resetFrame original_empty first_output
  message_code second_gas_range from Blanc.Composition.BuilderRequestApplicabilityCalls

def writer (h : B256) : Sevm := sevm true (some h)
def afterDeposit (h : B256) : Devm := afterSecond true (some h)

private theorem writer_sta (h : B256) :
    ({ writer h with code := writerCode true, benvStat := { (writer h).benvStat with fork := .prague } } : Sevm) =
      writer h := by rw [← message_code true (some h)]; rfl
private theorem lookupA_accounts_some (h : B256) : accounts true (some h) = accounts true (some 0) := rfl
private theorem getCode_eq_state (d : Devm) (a : Adr) : d.getCode a = d.state.getCode a := rfl
private theorem state_getCode_of_acctView (s : State) (a : Adr) : s.getCode a = (Witness.acctView (s.get a)).code := rfl
private theorem getCode_of_acctView (d : Devm) (a : Adr) : d.getCode a = (Witness.acctView (d.state.get a)).code := rfl
private theorem getBal_of_acctView (d : Devm) (a : Adr) : d.getBal a = (Witness.acctView (d.state.get a)).bal := rfl
private theorem getStorVal_eq_getStor (d : Devm) (a : Adr) (k : B256) : d.getStorVal a k = (d.state.getStor a).get k := rfl
private theorem storOf_eq_getStorVal (d : Devm) (a : Adr) (k : B256) : d.getStorVal a k = Witness.storOf d.state a k := rfl
private theorem acctView_of_state {d : Devm} {s : State} (hs : d.state = s) (x : Adr) :
    Witness.acctView (d.state.get x) = Witness.acctView (s.get x) := by rw [hs]
private theorem sysState_get_ne (p : SysShape) (s : State) (a x : Adr) (hne : a ≠ x) : (sysState p s a).get x = s.get x := by
  rw [State.get_eq_getD, State.get_eq_getD, sysState_getElem_ne p s hne]
private theorem hashSet_mem_union {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (m₁ m₂ : Std.HashSet α) (x : α) : x ∈ m₁.union m₂ ↔ x ∈ m₁ ∨ x ∈ m₂ := by
  simpa only [Std.HashSet.mem_iff_contains, Union.union, Std.HashSet.instUnion] using
    (Std.HashSet.mem_union_iff (m₁ := m₁) (m₂ := m₂) (k := x))
private theorem setMach_mem (d : Devm) (m : Mach) : (d.setMach m).memory = m.memory := rfl
private theorem setMach_state (d : Devm) (m : Mach) : (d.setMach m).state = d.state := rfl
private theorem setMach_logs (d : Devm) (m : Mach) : (d.setMach m).logs = d.logs := rfl
private theorem setMach_refund (d : Devm) (m : Mach) : (d.setMach m).refundCounter = d.refundCounter := rfl
private theorem callSpawnParent_mem_zero (d : Devm) (a : Adr) (g : Nat) :
    (callSpawnParent (addAccessedAddress d a) g 0 0 0 0).memory = d.memory.extends [(0, 0), (0, 0)] := rfl
private theorem callSpawnParent_state (d : Devm) (a : Adr) (g : Nat) :
    (callSpawnParent (addAccessedAddress d a) g 0 0 0 0).state = d.state := rfl
private theorem callSpawnParent_logs (d : Devm) (a : Adr) (g : Nat) :
    (callSpawnParent (addAccessedAddress d a) g 0 0 0 0).logs = d.logs := rfl
private theorem callSpawnParent_refund (d : Devm) (a : Adr) (g : Nat) :
    (callSpawnParent (addAccessedAddress d a) g 0 0 0 0).refundCounter = d.refundCounter := rfl
private theorem callSpawnMsg_empty_data (s : Sevm) (p : Devm) (g : Nat) (c d : Adr) (code : ByteArray) (dp : Bool) :
    (initSevm (callSpawnMsg s p g c d 0 0 code dp)).data = [] := rfl
private theorem callSpawnMsg_init_state (s : Sevm) (p : Devm) (g : Nat) (c d : Adr) (code : ByteArray) (dp : Bool) :
    (initDevm (callSpawnMsg s p g c d 0 0 code dp)).state = p.state := rfl
private theorem childMsg_init_adrs (s : Sevm) (d : Devm) (t : Adr) (w : B256) (g : Nat) (c : ByteArray) :
    (initDevm (SystemWordWriter.childMsg s d t w g c)).accessedAddresses = d.accessedAddresses.insert t := rfl
private theorem childMsg_init_keys (s : Sevm) (d : Devm) (t : Adr) (w : B256) (g : Nat) (c : ByteArray) :
    (initDevm (SystemWordWriter.childMsg s d t w g c)).accessedStorageKeys = d.accessedStorageKeys := rfl
private theorem childMsg_init_state (s : Sevm) (d : Devm) (t : Adr) (w : B256) (g : Nat) (c : ByteArray) :
    (initDevm (SystemWordWriter.childMsg s d t w g c)).state = d.state := rfl
private theorem post_mem_target (d child : Devm) (t : Adr) (w : B256) (g : Nat) (ho : child.output = []) :
    t ∈ (SystemWordWriter.post d t w g child).accessedAddresses := by
  unfold SystemWordWriter.post; rw [(callChildPost_facts _ _ 0 0 ho).2.2.2.2.2.2.2.2.2.2.2.1]
  exact Std.HashSet.mem_union_of_left (m₁ := d.accessedAddresses.insert t) Std.HashSet.mem_insert_self

theorem accessDelegation_of_code {d : Devm} {a : Adr} {c : ByteArray}
    (hc : d.getCode a = c) (hu : getDelegatedCodeAddress c = none) :
    accessDelegation (addAccessedAddress d a) a = (false, a, c, 0, addAccessedAddress d a) := by
  unfold accessDelegation; change (match getDelegatedCodeAddress (d.getCode a) with | some _ => _ | none => _) = _
  rw [hc, hu]; change (false, a, d.getCode a, 0, _) = _; rw [hc]

private theorem frame_settle_ok (m : Msg) (post : Devm) (he : post.error = none)
    (ht : m.benv.stat.rules.settle.touchedSweep = false) : (Frame.ofCall m).settle (.ok post) = .ok post := by
  rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
  simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, he, Option.isSome_none,
    Bool.false_eq_true, ite_false, bind, Except.bind, Devm.recordTouch_of_not_touchedSweep ht]

private def depositKeys (h : B256) := (secondCfg true (some h)).keys ++ (secondFinal true (some h)).keys
private def depositAddresses (h : B256) := (secondCfg true (some h)).adrs ++ (secondFinal true (some h)).adrs
private def depositCfg (h : B256) : Witness.Cfg :=
  ⟨afterDeposit h, .undefined, [], depositKeys h, depositAddresses h,
    (secondFinal true (some h)).stor, (secondFinal true (some h)).acs⟩

private theorem deposit_views (h : B256) :
    (secondPost true (some h)).accessedStorageKeys = (secondFinal true (some h)).devm.accessedStorageKeys ∧
    (secondPost true (some h)).accessedAddresses = (secondFinal true (some h)).devm.accessedAddresses ∧
    (secondFinal true (some h)).acs = accounts true (some h) ∧ decide (exitAddr ∈ depositAddresses h) = false ∧
    (firstPost true (some h)).logs = [] ∧ (secondPost true (some h)).logs = [] ∧
    Witness.lookupS (secondFinal true (some h)).stor exitAddr 0 = 0 ∧
    decide (900000 ≤ (secondPost true (some h)).gasLeft) = true := by
  unfold depositAddresses secondPost secondFinal secondResult secondCfg secondAddresses
    firstAddresses secondMsg secondParent secondBare secondForwarded secondGas afterFirst
    SystemWordWriter.post SystemWordWriter.parent firstPost firstFinal firstResult firstCfg
    firstMsg SystemWordWriter.childMsg
  rewrite [first_forwarded, first_cost]; dsimp only; revert h; kernel_forall_rfl_and

private theorem after_deposit_gas (h : B256) : 900000 ≤ (afterDeposit h).gasLeft ∧ (afterDeposit h).gasLeft < 2 ^ 256 := by
  have lower : 900000 ≤ (secondPost true (some h)).gasLeft := of_decide_eq_true (deposit_views h).2.2.2.2.2.2.2
  have settled := Frame.settle_gasLe (Classical.choice (second_exec true (some h))).settledGasLe (second_settle true (some h))
  have returned : (secondPost true (some h)).gasLeft ≤ secondForwarded true (some h) :=
    Nat.le_trans (Devm.gasLeft_le_gasMeasure (secondPost true (some h))) settled
  have range := second_gas_range true (some h)
  have forwarded : secondForwarded true (some h) ≤ secondGas true (some h) - 100 := by unfold secondForwarded except64th; omega
  have scalar : (afterDeposit h).gasLeft =
      (secondGas true (some h) - (secondForwarded true (some h) + 100)) + (secondPost true (some h)).gasLeft := rfl
  rw [scalar]; constructor <;> omega

private def exitLatchGas (h : B256) : Nat := (afterDeposit h).gasLeft - 18
private def exitLatchState (h : B256) : Devm :=
  (afterDeposit h).setMach ⟨[(exitLatchGas h).toB256, exitAddr.toBytes.toB256, 0, 0, 32, 0, 0],
    (afterDeposit h).memory, exitLatchGas h, (afterDeposit h).stateGas⟩
private theorem exit_latch_prefix_core (s : Sevm) (d : Devm) (g : Nat) :
    let sta := { s with code := writerCode true, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 8 ⟨93, sta, d.setMach ⟨[1], d.memory, g + 18, d.stateGas⟩⟩ =
      some ⟨122, sta, d.setMach ⟨[g.toB256, exitAddr.toBytes.toB256, 0, 0, 32, 0, 0], d.memory, g, d.stateGas⟩⟩ := by
  dsimp only; revert s d g; kernel_forall_rfl_and
theorem exit_latch_prefix (h : B256) :
    ConcreteRun.stepN 8 ⟨93, writer h, afterDeposit h⟩ = some ⟨122, writer h, exitLatchState h⟩ := by
  have sta := writer_sta h
  have stack : (afterDeposit h).stack = [1] :=
    (callChildPost_facts (secondParent true (some h)) (secondPost true (some h)) 0 0 (second_facts true (some h)).2.2.2).1
  have gas : (afterDeposit h).gasLeft = exitLatchGas h + 18 := by have b := (after_deposit_gas h).1; unfold exitLatchGas; omega
  have mach : (afterDeposit h).setMach ⟨[1], (afterDeposit h).memory, exitLatchGas h + 18,
      (afterDeposit h).stateGas⟩ = afterDeposit h := by rw [← stack, ← gas]; rfl
  have run := exit_latch_prefix_core (writer h) (afterDeposit h) (exitLatchGas h)
  dsimp only at run; rw [sta, mach] at run; exact run
private theorem exit_gas_range (h : B256) : 2600 < exitLatchGas h ∧ exitLatchGas h < 2 ^ 256 := by
  have r := after_deposit_gas h; unfold exitLatchGas; constructor <;> omega
theorem exit_memory (h : B256) : (afterDeposit h).memory = SystemWordWriter.wordMemory 0 := by
  unfold afterDeposit afterSecond
  rw [(callChildPost_facts (secondParent true (some h)) (secondPost true (some h)) 0 0 (second_facts true (some h)).2.2.2).2.1]
  unfold secondParent secondBare; rw [callSpawnParent_mem_zero, setMach_mem]; dsimp only; unfold afterFirst
  rw [(SystemWordWriter.post_facts (base true (some h)) (firstPost true (some h)) depositAddr 0
      firstGas (first_output true (some h))).2.2.2.2.2.2.2.1]
  exact Mem.extends_covered (by rw [show (SystemWordWriter.wordMemory 0).size = 32 from Mem.size_write_word]; rfl)
private theorem deposit_cfg_agree (h : B256) : Witness.Agree (depositCfg h) := by
  have keys := (deposit_views h).1; have adrs := (deposit_views h).2.1
  have start := second_agree true (some h); have done := Witness.wrun_done (second_result true (some h)) start
  have cf := callChildPost_facts (secondParent true (some h)) (secondPost true (some h)) 0 0 (second_facts true (some h)).2.2.2
  have wk : (secondParent true (some h)).accessedStorageKeys = (secondCfg true (some h)).devm.accessedStorageKeys := rfl
  have wa : (secondParent true (some h)).accessedAddresses = (secondCfg true (some h)).devm.accessedAddresses := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k; dsimp only [depositCfg]; unfold afterDeposit afterSecond
    rw [cf.2.2.2.2.2.2.2.2.2.2.2.2.1, hashSet_mem_union, wk, keys, start.1 k, done.2.1.1 k]; exact List.mem_append.symm
  · intro a; dsimp only [depositCfg]; unfold afterDeposit afterSecond
    rw [cf.2.2.2.2.2.2.2.2.2.2.2.1, hashSet_mem_union, wa, adrs, start.2.1 a, done.2.1.2.1 a]; exact List.mem_append.symm
  · intro a k; dsimp only [depositCfg]; unfold afterDeposit afterSecond
    rw [cf.2.2.2.1, done.2.2 (secondPost true (some h)) rfl]; exact done.2.1.2.2.1 a k
  · intro a; dsimp only [depositCfg]; unfold afterDeposit afterSecond
    rw [cf.2.2.2.1, done.2.2 (secondPost true (some h)) rfl]; exact done.2.1.2.2.2 a
private theorem exit_installed (h : B256) : (afterDeposit h).getCode exitAddr = Exit.code := by
  have view := (deposit_cfg_agree h).2.2.2 exitAddr; dsimp only [depositCfg] at view
  rw [getCode_of_acctView, view, (deposit_views h).2.2.1, lookupA_accounts_some h]; decide +kernel
def exitLatchMsg (h : B256) : Msg :=
  SystemWordWriter.childMsg (writer h) (afterDeposit h) exitAddr 0 (exitLatchGas h) Exit.code
private def exitLatchParent (h : B256) : Devm :=
  SystemWordWriter.parent (afterDeposit h) exitAddr 0 (exitLatchGas h)
theorem exit_latch_spawn (h : B256) :
    Evm.step ⟨122, writer h, exitLatchState h⟩ =
      .spawn (Frame.ofCall (exitLatchMsg h)) (.call (exitLatchParent h) 0 0) 123 := by
  have atCall : Ninst.At (writer h).code 122 (.exec .call) := by
    unfold Ninst.At; rw [show (writer h).code = writerCode true from message_code true (some h)]; kernel_rfl
  rw [Evm.step_next atCall]; simp only [Ninst.step_exec, XStep.toStep]
  have spawned := SystemWordWriter.call_spawn
    (sevm := writer h) (base := afterDeposit h) (target := exitAddr) (word := 0)
    (gas := exitLatchGas h) (childCode := Exit.code) CoveredFork.prague
    (by change (1024 : Nat) ≠ 0; decide) (exit_gas_range h).2
    (by have b := accessCost_le (x := exitAddr) (a := (afterDeposit h).accessedAddresses)
        change accessCost exitAddr (afterDeposit h).accessedAddresses ≤ 2600 at b; have r := (exit_gas_range h).1; omega)
    (exit_installed h) Exit.submissions.undelegated
  simp only [exitLatchState, exit_memory h]; rw [spawned]; rfl

private def exitLatchCfg (h : B256) : Witness.Cfg :=
  ⟨initDevm (exitLatchMsg h), Exit.t_0000_c0, [], depositKeys h,
    exitAddr :: depositAddresses h, (secondFinal true (some h)).stor, (secondFinal true (some h)).acs⟩

private theorem exit_latch_agree (h : B256) : Witness.Agree (exitLatchCfg h) := by
  have before := deposit_cfg_agree h; dsimp only [depositCfg] at before
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k; dsimp only [exitLatchCfg, exitLatchMsg]; rw [childMsg_init_keys]; exact before.1 k
  · intro a; dsimp only [exitLatchCfg, exitLatchMsg]
    rw [childMsg_init_adrs, Std.HashSet.mem_insert, before.2.1 a, List.mem_cons, beq_iff_eq]; exact or_congr eq_comm Iff.rfl
  · intro a k; dsimp only [exitLatchCfg, exitLatchMsg]; rw [childMsg_init_state]; exact before.2.2.1 a k
  · intro a; dsimp only [exitLatchCfg, exitLatchMsg]; rw [childMsg_init_state]; exact before.2.2.2 a

private def exitLatchResult (h : B256) : Witness.Res :=
  Witness.wrun Exit.cert.prog ((initSevm (exitLatchMsg h)).withOrig .empty) 512 (exitLatchCfg h)
def exitLatchPost (h : B256) : Devm := match exitLatchResult h with | .done (.halted post) _ => post | _ => default
private def exitLatchFinal (h : B256) : Witness.Cfg := match exitLatchResult h with | .done _ final => final | _ => exitLatchCfg h
private def exitLatchCheck (h : B256) : Bool :=
  match exitLatchResult h with
  | .done (.halted post) final => decide (post.error = none ∧ 0 ≤ post.refundCounter ∧
      Witness.lookupS final.stor exitAddr 0 = B256.max ∧ Witness.lookupS final.stor exitAddr 2 = 0 ∧
      Witness.lookupS final.stor exitAddr 3 = 0 ∧ Witness.lookupS final.stor depositAddr 0 = 0 ∧
      Witness.lookupS final.stor depositAddr 1 = 0 ∧ post.output = [] ∧ post.logs = [] ∧ 850000 ≤ post.gasLeft)
  | _ => false

private theorem exit_latch_cost (h : B256) : accessCost exitAddr (afterDeposit h).accessedAddresses = 2600 := by
  have addr := (deposit_cfg_agree h).2.1 exitAddr; dsimp only [depositCfg] at addr
  have absent : exitAddr ∉ (afterDeposit h).accessedAddresses :=
    fun m => absurd (addr.mp m) (of_decide_eq_false (deposit_views h).2.2.2.1)
  unfold accessCost; rw [ite_eq_right absent]; rfl

private theorem exit_latch_views (h : B256) :
    exitLatchCheck h = true ∧
    (exitLatchPost h).accessedStorageKeys = (exitLatchFinal h).devm.accessedStorageKeys ∧
    (exitLatchPost h).accessedAddresses = (exitLatchFinal h).devm.accessedAddresses ∧
    (exitLatchFinal h).acs = (secondFinal true (some h)).acs := by
  unfold exitLatchCheck exitLatchPost exitLatchFinal exitLatchResult exitLatchCfg
    exitLatchMsg SystemWordWriter.childMsg SystemWordWriter.parent SystemWordWriter.forwardedGas
  rewrite [exit_latch_cost]
  unfold exitLatchGas afterDeposit afterSecond depositKeys depositAddresses
    secondPost secondFinal secondResult secondCfg secondMsg secondParent secondBare
    secondForwarded secondGas afterFirst SystemWordWriter.post SystemWordWriter.parent
    firstPost firstFinal firstResult firstCfg firstMsg SystemWordWriter.childMsg
  rewrite [first_forwarded, first_cost]; dsimp only; revert h; kernel_forall_rfl_and

private theorem exit_latch_done (h : B256) :
    exitLatchResult h = .done (.halted (exitLatchPost h)) (exitLatchFinal h) ∧
    (exitLatchPost h).error = none ∧ 0 ≤ (exitLatchPost h).refundCounter ∧
    Witness.lookupS (exitLatchFinal h).stor exitAddr 0 = B256.max ∧
    Witness.lookupS (exitLatchFinal h).stor exitAddr 2 = 0 ∧ Witness.lookupS (exitLatchFinal h).stor exitAddr 3 = 0 ∧
    Witness.lookupS (exitLatchFinal h).stor depositAddr 0 = 0 ∧ Witness.lookupS (exitLatchFinal h).stor depositAddr 1 = 0 ∧
    (exitLatchPost h).output = [] ∧ (exitLatchPost h).logs = [] ∧ 850000 ≤ (exitLatchPost h).gasLeft := by
  have check := (exit_latch_views h).1
  cases e : exitLatchResult h with
  | cont _ | stuck => simp only [exitLatchCheck, e, Bool.false_eq_true] at check
  | done outcome final =>
    cases outcome with
    | returned _ => simp only [exitLatchCheck, e, Bool.false_eq_true] at check
    | halted post =>
      simp only [exitLatchCheck, e, decide_eq_true_eq] at check
      simp only [exitLatchPost, exitLatchFinal, e]; exact ⟨trivial, check⟩

private theorem exit_latch_stor_lookup (h : B256) (a : Adr) (k : B256) :
    (exitLatchPost h).getStorVal a k = Witness.lookupS (exitLatchFinal h).stor a k := by
  have done := Witness.wrun_done (exit_latch_done h).1 (exit_latch_agree h)
  change Witness.storOf (exitLatchPost h).state a k = _; rw [done.2.2 (exitLatchPost h) rfl]; exact done.2.1.2.2.1 a k

private theorem exit_latch_acct_view (h : B256) (a : Adr) :
    Witness.acctView ((exitLatchPost h).state.get a) = Witness.lookupA (accounts true (some 0)) a := by
  have done := Witness.wrun_done (exit_latch_done h).1 (exit_latch_agree h); rw [done.2.2 (exitLatchPost h) rfl]
  exact (done.2.1.2.2.2 a).trans (by rw [(exit_latch_views h).2.2.2, (deposit_views h).2.2.1, lookupA_accounts_some h])

theorem exit_latch_facts (h : B256) :
    (exitLatchPost h).error = none ∧ 0 ≤ (exitLatchPost h).refundCounter ∧
    (exitLatchPost h).getStorVal exitAddr 0 = B256.max ∧
    (exitLatchPost h).getStorVal exitAddr 2 = 0 ∧ (exitLatchPost h).getStorVal exitAddr 3 = 0 ∧
    (exitLatchPost h).getStorVal depositAddr 0 = 0 ∧ (exitLatchPost h).getStorVal depositAddr 1 = 0 ∧
    (exitLatchPost h).output = [] ∧ (exitLatchPost h).logs = [] ∧ 850000 ≤ (exitLatchPost h).gasLeft := by
  have s := (exit_latch_done h).2
  exact ⟨s.1, s.2.1, (exit_latch_stor_lookup h exitAddr 0).trans s.2.2.1,
    (exit_latch_stor_lookup h exitAddr 2).trans s.2.2.2.1, (exit_latch_stor_lookup h exitAddr 3).trans s.2.2.2.2.1,
    (exit_latch_stor_lookup h depositAddr 0).trans s.2.2.2.2.2.1,
    (exit_latch_stor_lookup h depositAddr 1).trans s.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2⟩

theorem exit_latch_init_zero (h : B256) : (initDevm (exitLatchMsg h)).getStorVal exitAddr 0 = 0 := by
  have ag := (exit_latch_agree h).2.2.1 exitAddr 0; dsimp only [exitLatchCfg] at ag
  rw [storOf_eq_getStorVal, ag]; exact (deposit_views h).2.2.2.2.2.2.1

theorem exit_latch_exec (h : B256) :
    Nonempty (Exec 0 (initSevm (exitLatchMsg h)) (initDevm (exitLatchMsg h)) (.ok (exitLatchPost h))) := by
  have actual : Witness.wrun Exit.cert.prog (initSevm (exitLatchMsg h)) 512 (exitLatchCfg h) =
      .done (.halted (exitLatchPost h)) (exitLatchFinal h) := by
    rw [← Witness.wrun_withOrig (original_empty true (some h)) Exit.cert.prog 512 (exitLatchCfg h)]; exact (exit_latch_done h).1
  exact lift_exact_noExec Exit.userPath.check Exit.userPath.jumps rfl Exit.userPath.noExec
    (Witness.wrun_exact rfl (exit_latch_agree h) actual)

theorem exit_latch_enter (h : B256) : (Frame.ofCall (exitLatchMsg h)).enter = .run (initEvm (exitLatchMsg h)) :=
  Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl
    (by change pragueRules.isPrecomp exitAddr = false; decide)
theorem exit_latch_settle (h : B256) : (Frame.ofCall (exitLatchMsg h)).settle (.ok (exitLatchPost h)) = .ok (exitLatchPost h) :=
  frame_settle_ok (exitLatchMsg h) (exitLatchPost h) (exit_latch_facts h).1 rfl
def afterExitLatch (h : B256) : Devm := SystemWordWriter.post (afterDeposit h) exitAddr 0 (exitLatchGas h) (exitLatchPost h)
theorem exit_latch_resume (h : B256) :
    Resume.run (.call (exitLatchParent h) 0 0)
      ((Frame.ofCall (exitLatchMsg h)).settle (.ok (exitLatchPost h))) = .ok (afterExitLatch h) := by
  rw [exit_latch_settle h, Resume.run_call_ok (by rw [(exit_latch_facts h).1]; rfl) (by change (0 : Nat) < 1024; decide)]; rfl
private theorem after_exit_latch_gas (h : B256) : 850000 ≤ (afterExitLatch h).gasLeft ∧ (afterExitLatch h).gasLeft < 2 ^ 256 := by
  have lower := (exit_latch_facts h).2.2.2.2.2.2.2.2.2
  have settled := Frame.settle_gasLe (Classical.choice (exit_latch_exec h)).settledGasLe (exit_latch_settle h)
  have returned : (exitLatchPost h).gasLeft ≤ SystemWordWriter.forwardedGas (afterDeposit h) exitAddr (exitLatchGas h) :=
    Nat.le_trans (Devm.gasLeft_le_gasMeasure (exitLatchPost h)) settled
  have range := exit_gas_range h
  have forwarded : SystemWordWriter.forwardedGas (afterDeposit h) exitAddr (exitLatchGas h) ≤
      exitLatchGas h - 2600 := by unfold SystemWordWriter.forwardedGas except64th; rw [exit_latch_cost h]; omega
  have scalar : (afterExitLatch h).gasLeft =
      (exitLatchGas h - (SystemWordWriter.forwardedGas (afterDeposit h) exitAddr (exitLatchGas h) +
        accessCost exitAddr (afterDeposit h).accessedAddresses)) + (exitLatchPost h).gasLeft := rfl
  rw [scalar, exit_latch_cost h]; constructor <;> omega
private def exitResetGas (h : B256) : Nat := (afterExitLatch h).gasLeft - 17
private def exitResetState (h : B256) : Devm :=
  (afterExitLatch h).setMach ⟨[(exitResetGas h).toB256, exitAddr.toBytes.toB256, 0, 0, 0, 0, 0],
    (afterExitLatch h).memory, exitResetGas h, (afterExitLatch h).stateGas⟩
private def exitResetBare (h : B256) : Devm :=
  (afterExitLatch h).setMach ⟨[], (afterExitLatch h).memory, exitResetGas h, (afterExitLatch h).stateGas⟩
private def exitResetForwarded (h : B256) : Nat := except64th (exitResetGas h - 100)
private def exitResetParent (h : B256) : Devm :=
  callSpawnParent (addAccessedAddress (exitResetBare h) exitAddr) (exitResetForwarded h + 100) 0 0 0 0
def exitResetMsg (h : B256) : Msg :=
  callSpawnMsg (writer h) (exitResetParent h) (exitResetForwarded h) exitAddr exitAddr 0 0 Exit.code false
private theorem exit_reset_prefix_core (s : Sevm) (d : Devm) (g : Nat) :
    let sta := { s with code := writerCode true, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 8 ⟨123, sta, d.setMach ⟨[1], d.memory, g + 17, d.stateGas⟩⟩ =
      some ⟨151, sta, d.setMach ⟨[g.toB256, exitAddr.toBytes.toB256, 0, 0, 0, 0, 0], d.memory, g, d.stateGas⟩⟩ := by
  dsimp only; revert s d g; kernel_forall_rfl_and

theorem exit_reset_prefix (h : B256) :
    ConcreteRun.stepN 8 ⟨123, writer h, afterExitLatch h⟩ = some ⟨151, writer h, exitResetState h⟩ := by
  have sta := writer_sta h
  have stack : (afterExitLatch h).stack = [1] :=
    (SystemWordWriter.post_facts (afterDeposit h) (exitLatchPost h) exitAddr 0
      (exitLatchGas h) (exit_latch_facts h).2.2.2.2.2.2.2.1).2.2.2.2.2.2.2.2
  have gas : (afterExitLatch h).gasLeft = exitResetGas h + 17 := by have b := (after_exit_latch_gas h).1; unfold exitResetGas; omega
  have mach : (afterExitLatch h).setMach ⟨[1], (afterExitLatch h).memory, exitResetGas h + 17,
      (afterExitLatch h).stateGas⟩ = afterExitLatch h := by rw [← stack, ← gas]; rfl
  have run := exit_reset_prefix_core (writer h) (afterExitLatch h) (exitResetGas h)
  dsimp only at run; rw [sta, mach] at run; exact run

private theorem exit_reset_cost (h : B256) : accessCost exitAddr (afterExitLatch h).accessedAddresses = 100 := by
  have present := post_mem_target (afterDeposit h) (exitLatchPost h) exitAddr 0 (exitLatchGas h)
    (exit_latch_facts h).2.2.2.2.2.2.2.1
  unfold accessCost afterExitLatch; rw [ite_eq_left present]; rfl

private theorem afterExitLatch_code (h : B256) : (afterExitLatch h).getCode exitAddr = Exit.code := by
  unfold afterExitLatch; rw [SystemWordWriter.post_code, getCode_of_acctView, exit_latch_acct_view h exitAddr]; decide +kernel

private theorem exit_reset_gas_range (h : B256) : 840000 ≤ exitResetGas h ∧ exitResetGas h < 2 ^ 256 := by
  have r := after_exit_latch_gas h; unfold exitResetGas; constructor <;> omega

theorem exit_reset_spawn (h : B256) :
    Evm.step ⟨151, writer h, exitResetState h⟩ =
      .spawn (Frame.ofCall (exitResetMsg h)) (.call (exitResetParent h) 0 0) 152 := by
  have atCall : Ninst.At (writer h).code 151 (.exec .call) := by
    unfold Ninst.At; rw [show (writer h).code = writerCode true from message_code true (some h)]; kernel_rfl
  have range := exit_reset_gas_range h
  have split : calculateMsgCallGas 0 (exitResetGas h).toB256.toNat (exitResetGas h) 0 100 =
      (exitResetForwarded h + 100, exitResetForwarded h) := by
    rw [calculateMsgCallGas_zero (by omega), B256.toNat_toB256_of_lt range.2]; simp only [Nat.sub_zero]
    have bound : except64th (exitResetGas h - 100) ≤ exitResetGas h := by unfold except64th; omega
    rw [Nat.min_eq_right bound]; rfl
  have del := accessDelegation_of_code (d := exitResetBare h) (afterExitLatch_code h) Exit.submissions.undelegated
  have mem : (afterExitLatch h).memory = SystemWordWriter.wordMemory 0 :=
    (SystemWordWriter.post_facts (afterDeposit h) (exitLatchPost h) exitAddr 0
      (exitLatchGas h) (exit_latch_facts h).2.2.2.2.2.2.2.1).2.2.2.2.2.2.2.1
  have spawn := Xinst.step_call_zero_value_spawn
    (sevm := writer h) (devm := exitResetState h) (gw := (exitResetGas h).toB256)
    (cw := exitAddr.toBytes.toB256) (iiw := 0) (isw := 0) (oiw := 0) (osw := 0) (s := [])
    (dp := false) (dadr := exitAddr) (code := Exit.code) (dgc := 0)
    (d1 := addAccessedAddress (exitResetBare h) exitAddr) (ext := 0) (acc := 100)
    (mcs := exitResetForwarded h) (mcc := exitResetForwarded h + 100) (CoveredFork.prague.callEra false) rfl
    (by apply Devm.extCost_covered; simp only [exitResetState, Devm.memory_setMach, B256.toNat_zero, mem]
        rw [show (SystemWordWriter.wordMemory 0).size = 32 from Mem.size_write_word]; rfl)
    (by rw [SystemWordWriter.target_word]; simpa only [exitResetState, exitResetBare,
      Devm.memory_setMach, Devm.gasLeft_setMach, Devm.stateGas_setMach, Devm.setMach_setMach] using del)
    (by rw [SystemWordWriter.target_word]; simpa only [exitResetState, Devm.setMach_accessedAddresses,
      Nat.add_zero] using exit_reset_cost h)
    split
    (by change exitResetForwarded h + 100 + 0 ≤ exitResetGas h; unfold exitResetForwarded except64th; omega)
    (by change (1024 : Nat) ≠ 0; decide)
  rw [Evm.step_next atCall]
  simp only [Ninst.step_exec, spawn, XStep.toStep, exitResetMsg, exitResetParent, exitResetBare,
    SystemWordWriter.target_word, B256.toNat_zero, Nat.add_zero, Nat.reduceAdd]

theorem snapshot_zero (h : B256) (a : Adr) (k : B256) : ((state true (some h)).get a).stor.get k = 0 := by
  have orig := original_empty true (some h) a k
  have empty : ((State.get (.empty : State) a).stor.get k) = 0 := by
    rw [State.get_eq_getD]; change (((∅ : State)[a]?).getD Acct.nil).stor.get k = 0
    rw [Std.TreeMap.getElem?_emptyc]; rfl
  exact orig.symm.trans empty

private def exitResetSevm (h : B256) : Sevm := initSevm (exitResetMsg h)
private def exitResetInit (h : B256) : Devm := initDevm (exitResetMsg h)
private def exitResetCost (h : B256) : Nat := Exit.sysPath.frameCostOn (exitResetInit h) (coveredStores (exitResetSevm h))
def exitResetPost (h : B256) : Devm :=
  Exit.sysPath.framePostOn (exitResetInit h) (coveredStores (exitResetSevm h)) (exitResetForwarded h - exitResetCost h)

private theorem exit_reset_ready (h : B256) : CoveredReady (exitResetSevm h) (exitResetInit h) [2, 3, 0, 1] where
  error := rfl
  refund := Int.le_refl 0
  clean := fun k _ => Or.inr (actualOrigStorVal_eq_zero_of_raw
    (show getOrigStorVal (exitResetSevm h) (exitResetSevm h).currentTarget k = 0 from snapshot_zero h exitAddr k))

private theorem exit_reset_cost_le (h : B256) : exitResetCost h ≤ 210000 :=
  Nat.le_trans (Exit.sysPath.frameCost_leOn Exit.sysMemory (coveredStores_laws (exitResetSevm h)) (exitResetInit h))
    (by change Exit.sysPath.frameBoundOn Exit.sysMemory.alloc (gasColdSload + gasStorageSet) ≤ 210000; decide)

private theorem exit_reset_forwarded_ge (h : B256) : 820000 ≤ exitResetForwarded h := by
  have r := (exit_reset_gas_range h).1; unfold exitResetForwarded except64th; omega

theorem exit_reset_exec (h : B256) :
    Nonempty (Exec 0 (exitResetSevm h) (exitResetInit h) (.ok (exitResetPost h))) := by
  have fwd := exit_reset_forwarded_ge h; have cost := exit_reset_cost_le h
  have fork : CoveredFork (exitResetSevm h).benvStat.fork := CoveredFork.prague
  have data : (exitResetSevm h).data = [] :=
    callSpawnMsg_empty_data (writer h) (exitResetParent h) (exitResetForwarded h) exitAddr exitAddr Exit.code false
  have run := Exit.sysPath.frame_runOn (sevm := exitResetSevm h) (b := exitResetInit h)
    (w := coveredStores (exitResetSevm h)) (coveredStores_runs fork)
    (coveredStores_laws (exitResetSevm h)) fork.rules_access fork.rules_push0 fork.rules_shifts
    rfl rfl data (exit_reset_ready h) (G := exitResetForwarded h - exitResetCost h) (by unfold gCallStipend; omega)
  rw [show Exit.sysPath.frameCostOn (exitResetInit h) (coveredStores (exitResetSevm h)) = exitResetCost h from rfl,
    show exitResetForwarded h - exitResetCost h + exitResetCost h = exitResetForwarded h by omega,
    show St (exitResetInit h) [] .empty (exitResetForwarded h) = exitResetInit h from rfl] at run
  exact lift_exact_noExec Exit.sysPath.check Exit.sysPath.jumps rfl Exit.sysPath.noExec ⟨_, Exit.sysPath.root, run⟩

private theorem exit_reset_end_ready (h : B256) :
    CoveredReady (exitResetSevm h)
      (finalBaseOn (coveredStores (exitResetSevm h))
        (Exit.sysPath.excessReadOn (exitResetInit h) (coveredStores (exitResetSevm h)))
        (Exit.sysPath.excessStoredOn (exitResetInit h) (coveredStores (exitResetSevm h)))) [] := by
  let s := exitResetSevm h; let b := exitResetInit h; let laws := coveredStores_laws s
  have rSetup := laws.read (laws.read (exit_reset_ready h) 3) 2
  have rDrain := Exit.sysPath.fold_readyOn laws (h := SysPath.rd s b 2) 0 (Exit.sysPath.count s b).toNat (M := .empty) rSetup
  have rBooked := ready_bookOn laws rDrain (SysPath.rd s b 2) (Exit.sysPath.count s b) (SysPath.rd s b 3)
  exact laws.write (laws.write (laws.read (laws.read rBooked 0) 1) (by decide) _) (by decide) (0 : B256)

private theorem chargedRetPost_logs (b : Devm) (S : List B256) (M : Mem) (G : Nat) (i sz : B256) :
    (chargedRetPost b S M G i sz).logs = b.logs := rfl

private theorem covered_framePostOn_logs (s : Sevm) (b : Devm) (G : Nat)
    (hc : (Exit.sysPath.count s b).toNat = 0) (hl : b.logs = []) :
    (Exit.sysPath.framePostOn b (coveredStores s) G).logs = [] := by
  have hd0 : (Exit.sysPath.drain s b).base = setupBase s b := by unfold SysPath.drain; rw [hc]; rfl
  rw [SysPath.framePostOn, chargedRetPost_logs]
  simp only [finalBaseOn, coveredStores, afterSstore_logs, SysPath.excessReadOn,
    afterSloadA_logs, SysPath.bookedOn, bookBaseOn]
  split <;> simp only [afterSstore_logs, hd0, setupBase, afterSloadA_logs, hl]

theorem exit_reset_init_state (h : B256) : (exitResetInit h).state = (exitLatchPost h).state := by
  dsimp only [exitResetInit, exitResetMsg, exitResetParent, exitResetBare]
  rw [callSpawnMsg_init_state, callSpawnParent_state, setMach_state]; unfold afterExitLatch
  exact (SystemWordWriter.post_facts (afterDeposit h) (exitLatchPost h) exitAddr 0
    (exitLatchGas h) (exit_latch_facts h).2.2.2.2.2.2.2.1).1

theorem exit_reset_facts (h : B256) :
    (exitResetPost h).error = none ∧ 0 ≤ (exitResetPost h).refundCounter ∧
    (exitResetPost h).state = sysState Exit.sysShape (exitLatchPost h).state exitAddr ∧
    (exitResetPost h).getStorVal exitAddr 0 = 0 ∧ (exitResetPost h).getStorVal exitAddr 1 = 0 ∧
    (exitResetPost h).output = [] ∧ (exitResetPost h).logs = [] ∧ 600000 ≤ (exitResetPost h).gasLeft := by
  let s := exitResetSevm h; let b := exitResetInit h; have laws := coveredStores_laws s; have rEnd := exit_reset_end_ready h
  have stEq : (exitResetPost h).state = sysState Exit.sysShape (exitLatchPost h).state exitAddr := by
    dsimp only [exitResetPost]
    exact (Exit.sysPath.framePostOn_state laws b _).trans
      (by rw [exit_reset_init_state h, show Exit.sysPath.shape = Exit.sysShape from rfl, show s.currentTarget = exitAddr from rfl])
  have storEq : (exitResetPost h).state.getStor exitAddr =
      Delivery.drainStor Exit.sysShape ((exitLatchPost h).state.getStor exitAddr) := by rw [stEq, Delivery.sysState_getStor]
  have slot0Latch : ((exitLatchPost h).state.getStor exitAddr).get 0 = B256.max := (exit_latch_facts h).2.2.1
  have rdEq : ∀ k, SysPath.rd s b k = (exitLatchPost h).getStorVal exitAddr k := by
    intro k; unfold SysPath.rd Devm.getStorVal Devm.getAcct; dsimp only [s, b, exitResetSevm, exitResetMsg]
    rw [exit_reset_init_state h]; rfl
  have countZero : (Exit.sysPath.count s b).toNat = 0 := by
    unfold SysPath.count; rw [rdEq 2, rdEq 3, (exit_latch_facts h).2.2.2.1, (exit_latch_facts h).2.2.2.2.1]; decide
  have logsEq := covered_framePostOn_logs s b (exitResetForwarded h - exitResetCost h) countZero rfl
  have outEq := Exit.sysOutput.framePostOn_output (coveredStores s) b (exitResetForwarded h - exitResetCost h)
  refine ⟨?_, ?_, stEq, ?_, ?_, ?_, logsEq, ?_⟩
  · rw [exitResetPost, SysPath.framePostOn, chargedRetPost_error]; exact laws.error rEnd
  · rw [exitResetPost, SysPath.framePostOn, chargedRetPost_refundCounter]; exact laws.refund rEnd
  · rw [getStorVal_eq_getStor, storEq]; unfold Delivery.drainStor
    rw [Stor.get_set_ne _ (by decide : (1 : B256) ≠ 0), Stor.get_set_self, slot0Latch]; rfl
  · rw [getStorVal_eq_getStor, storEq]; unfold Delivery.drainStor; exact Stor.get_set_self _ _ _
  · dsimp only [exitResetPost]; rw [outEq, countZero]; rfl
  · change 600000 ≤ exitResetForwarded h - exitResetCost h
    have fwd := exit_reset_forwarded_ge h; have cost := exit_reset_cost_le h; omega

theorem exit_reset_enter (h : B256) : (Frame.ofCall (exitResetMsg h)).enter = .run (initEvm (exitResetMsg h)) :=
  Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl
    (by change pragueRules.isPrecomp exitAddr = false; decide)

theorem exit_reset_settle (h : B256) : (Frame.ofCall (exitResetMsg h)).settle (.ok (exitResetPost h)) = .ok (exitResetPost h) :=
  frame_settle_ok (exitResetMsg h) (exitResetPost h) (exit_reset_facts h).1 rfl

def afterExitReset (h : B256) : Devm := callChildPost (exitResetParent h) (exitResetPost h) 0 0

theorem exit_reset_resume (h : B256) :
    Resume.run (.call (exitResetParent h) 0 0)
      ((Frame.ofCall (exitResetMsg h)).settle (.ok (exitResetPost h))) = .ok (afterExitReset h) := by
  rw [exit_reset_settle h, Resume.run_call_ok (by rw [(exit_reset_facts h).1]; rfl) (by change (0 : Nat) < 1024; decide)]; rfl

theorem afterExitReset_facts (h : B256) :
    (afterExitReset h).stack = [1] ∧ (afterExitReset h).memory = SystemWordWriter.wordMemory 0 ∧
    600000 ≤ (afterExitReset h).gasLeft ∧ (afterExitReset h).gasLeft < 2 ^ 256 ∧
    (afterExitReset h).error = none ∧ 0 ≤ (afterExitReset h).refundCounter ∧ (afterExitReset h).logs = [] ∧
    (afterExitReset h).getStorVal depositAddr 0 = 0 ∧ (afterExitReset h).getStorVal depositAddr 1 = 0 ∧
    (afterExitReset h).getStorVal exitAddr 0 = 0 ∧ (afterExitReset h).getStorVal exitAddr 1 = 0 := by
  have rf := exit_reset_facts h; have lf := exit_latch_facts h
  have cf := callChildPost_facts (exitResetParent h) (exitResetPost h) 0 0 rf.2.2.2.2.2.1
  have pf1 := SystemWordWriter.post_facts (base true (some h)) (firstPost true (some h))
    depositAddr 0 firstGas (first_output true (some h))
  have cf2 := callChildPost_facts (secondParent true (some h)) (secondPost true (some h)) 0 0 (second_facts true (some h)).2.2.2
  have pf3 := SystemWordWriter.post_facts (afterDeposit h) (exitLatchPost h) exitAddr 0 (exitLatchGas h) lf.2.2.2.2.2.2.2.1
  have memReset : (afterExitReset h).memory = SystemWordWriter.wordMemory 0 := by
    unfold afterExitReset; rw [cf.2.1]; unfold exitResetParent exitResetBare
    rw [callSpawnParent_mem_zero, setMach_mem]; dsimp only; unfold afterExitLatch; rw [pf3.2.2.2.2.2.2.2.1]
    exact Mem.extends_covered (by rw [show (SystemWordWriter.wordMemory 0).size = 32 from Mem.size_write_word]; rfl)
  have settled := Frame.settle_gasLe (Classical.choice (exit_reset_exec h)).settledGasLe (exit_reset_settle h)
  have retLe : (exitResetPost h).gasLeft ≤ exitResetForwarded h :=
    Nat.le_trans (Devm.gasLeft_le_gasMeasure (exitResetPost h)) settled
  have range := exit_reset_gas_range h
  have fwdLe : exitResetForwarded h ≤ exitResetGas h - 100 := by unfold exitResetForwarded except64th; omega
  have gasEq : (afterExitReset h).gasLeft = (exitResetGas h - (exitResetForwarded h + 100)) + (exitResetPost h).gasLeft := by
    unfold afterExitReset; rw [cf.2.2.1]; rfl
  have logsDep : (afterDeposit h).logs = [] := by
    unfold afterDeposit afterSecond; rw [cf2.2.2.2.2.2.1]; unfold secondParent secondBare
    rw [callSpawnParent_logs, setMach_logs]; unfold afterFirst
    rw [pf1.2.1, (deposit_views h).2.2.2.2.1, (deposit_views h).2.2.2.2.2.1]; rfl
  have logsLatch : (afterExitLatch h).logs = [] := by
    unfold afterExitLatch; rw [pf3.2.1, logsDep, lf.2.2.2.2.2.2.2.2.1]; rfl
  have logsReset : (afterExitReset h).logs = [] := by
    unfold afterExitReset; rw [cf.2.2.2.2.2.1]; unfold exitResetParent exitResetBare
    rw [callSpawnParent_logs, setMach_logs, logsLatch, rf.2.2.2.2.2.2.1]; rfl
  have refReset : 0 ≤ (afterExitReset h).refundCounter := by
    unfold afterExitReset; rw [cf.2.2.2.2.2.2.1]; unfold exitResetParent exitResetBare
    rw [callSpawnParent_refund, setMach_refund]; unfold afterExitLatch; rw [pf3.2.2.1]
    unfold afterDeposit afterSecond; rw [cf2.2.2.2.2.2.2.1]; unfold secondParent secondBare
    rw [callSpawnParent_refund, setMach_refund]; unfold afterFirst; rw [pf1.2.2.1]
    have b0 : (base true (some h)).refundCounter = 0 := rfl
    have r1 := (first_facts true (some h)).2.1; have r2 := (second_facts true (some h)).2.1
    have r3 := lf.2.1; have r4 := rf.2.1; rw [b0]; omega
  have errReset : (afterExitReset h).error = none := by unfold afterExitReset; rw [cf.2.2.2.2.2.2.2.1]; rfl
  have stReset : (afterExitReset h).state = (exitResetPost h).state := cf.2.2.2.1
  have depStor : (afterExitReset h).state.getStor depositAddr = (exitLatchPost h).state.getStor depositAddr := by
    rw [stReset, rf.2.2.1]; exact sysState_getStor_other Exit.sysShape _ (by decide : exitAddr ≠ depositAddr)
  refine ⟨cf.1, memReset, ?_, ?_, errReset, refReset, logsReset, ?_, ?_, ?_, ?_⟩
  · rw [gasEq]; have g := rf.2.2.2.2.2.2.2; omega
  · rw [gasEq]; omega
  · rw [getStorVal_eq_getStor, depStor]; exact lf.2.2.2.2.2.1
  · rw [getStorVal_eq_getStor, depStor]; exact lf.2.2.2.2.2.2.1
  · rw [getStorVal_eq_getStor, stReset]; exact rf.2.2.2.1
  · rw [getStorVal_eq_getStor, stReset]; exact rf.2.2.2.2.1

private theorem accounts_code_bal :
    (Witness.lookupA (accounts true (some 0)) ordinaryAddr).code = ordinaryCode ∧
    (Witness.lookupA (accounts true (some 0)) ordinaryAddr).bal = (2 ^ 100 : Nat).toB256 ∧
    (Witness.lookupA (accounts true (some 0)) depositAddr).code = Deposit.code ∧
    (Witness.lookupA (accounts true (some 0)) exitAddr).code = Exit.code ∧
    (Witness.lookupA (accounts true (some 0)) withdrawalRequestPredeployAddress).code = stopCode ∧
    (Witness.lookupA (accounts true (some 0)) consolidationRequestPredeployAddress).code = stopCode :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

theorem afterExitReset_code_bal (h : B256) :
    (afterExitReset h).getCode ordinaryAddr = ordinaryCode ∧
    (afterExitReset h).getBal ordinaryAddr = (2 ^ 100 : Nat).toB256 ∧
    (afterExitReset h).getCode depositAddr = Deposit.code ∧ (afterExitReset h).getCode exitAddr = Exit.code ∧
    (afterExitReset h).getCode withdrawalRequestPredeployAddress = stopCode ∧
    (afterExitReset h).getCode consolidationRequestPredeployAddress = stopCode := by
  have rf := exit_reset_facts h; have ac := accounts_code_bal
  have cf := callChildPost_facts (exitResetParent h) (exitResetPost h) 0 0 rf.2.2.2.2.2.1
  have stEq : (afterExitReset h).state = sysState Exit.sysShape (exitLatchPost h).state exitAddr :=
    cf.2.2.2.1.trans rf.2.2.1
  have otherView : ∀ x : Adr, exitAddr ≠ x →
      Witness.acctView ((afterExitReset h).state.get x) = Witness.lookupA (accounts true (some 0)) x :=
    fun x hne => by rw [acctView_of_state stEq x, sysState_get_ne Exit.sysShape _ _ x hne]; exact exit_latch_acct_view h x
  exact ⟨by rw [getCode_of_acctView, otherView ordinaryAddr (by decide)]; exact ac.1,
    by rw [getBal_of_acctView, otherView ordinaryAddr (by decide)]; exact ac.2.1,
    by rw [getCode_of_acctView, otherView depositAddr (by decide)]; exact ac.2.2.1,
    by rw [getCode_eq_state, stEq, sysState_getCode, state_getCode_of_acctView, exit_latch_acct_view h exitAddr]; exact ac.2.2.2.1,
    by rw [getCode_of_acctView, otherView withdrawalRequestPredeployAddress (by decide)]; exact ac.2.2.2.2.1,
    by rw [getCode_of_acctView, otherView consolidationRequestPredeployAddress (by decide)]; exact ac.2.2.2.2.2⟩

noncomputable def exitLatchRun (h : B256) :
    Exec 0 (initSevm (exitLatchMsg h)) (initDevm (exitLatchMsg h)) (.ok (exitLatchPost h)) :=
  Classical.choice (exit_latch_exec h)
noncomputable def exitResetRun (h : B256) :
    Exec 0 (exitResetSevm h) (exitResetInit h) (.ok (exitResetPost h)) :=
  Classical.choice (exit_reset_exec h)
theorem exit_latch_commits (h : B256) : Execution.commits (.ok (exitLatchPost h)) = true := by
  change (exitLatchPost h).error.isNone = true; rw [(exit_latch_facts h).1]; rfl
theorem exit_reset_commits (h : B256) : Execution.commits (.ok (exitResetPost h)) = true := by
  change (exitResetPost h).error.isNone = true; rw [(exit_reset_facts h).1]; rfl
noncomputable def dLatchFrame (h : B256) : Exec.Frame := latchFrame true (some h)
noncomputable def dResetFrame (h : B256) : Exec.Frame := resetFrame true (some h)
noncomputable def eLatchFrame (h : B256) : Exec.Frame := .ofRun (exitLatchRun h) (exit_latch_commits h)
noncomputable def eResetFrame (h : B256) : Exec.Frame := .ofRun (exitResetRun h) (exit_reset_commits h)

noncomputable def exitSuffixRun (h : B256) {out : Execution}
    (rest : Exec 152 (writer h) (afterExitReset h) out) : Exec 93 (writer h) (afterDeposit h) out :=
  ConcreteRun.Exec.ofStepN 8 (exit_latch_prefix h)
    (.runOk (exit_latch_spawn h) (exit_latch_enter h) (exitLatchRun h) (exit_latch_resume h)
      (ConcreteRun.Exec.ofStepN 8 (exit_reset_prefix h)
        (.runOk (exit_reset_spawn h) (exit_reset_enter h) (exitResetRun h) (exit_reset_resume h) rest)))

noncomputable def prefixFourRun (h : B256) {out : Execution}
    (rest : Exec 152 (writer h) (afterExitReset h) out) : Exec 0 (writer h) (base true (some h)) out :=
  pairRun true (some h) (exitSuffixRun h rest)

end Blanc.Composition.BuilderRequestApplicabilityTail
