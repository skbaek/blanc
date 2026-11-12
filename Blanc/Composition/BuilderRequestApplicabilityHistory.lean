import Batteries.Tactic.OpenPrivate
import Blanc.Composition.BuilderRequestApplicabilityTail
import Blanc.ExecutionKeptChildless
import Blanc.ExecutionKeptConfigured
import Blanc.SyntheticBpo2Envelope
import Blanc.SystemCallEmpty
import Blanc.Lift.CallRestriction
import Blanc.Lift.CallMessageFacts
import Blanc.Lift.BuilderRequest.Deposit.Message
import Blanc.Lift.Quiet
import Blanc.Lift.BuilderRequest.Deposit.Frames
import Blanc.Lift.BuilderRequest.Exit.Frames

/-!
# B-S2 all eight success arms in one original signed kept history

Constructs one Prague `CodesKept` / `KeptHistory` with the original signed `txD`,
its complete writer/root execution, and exactly four settled frames retained at
each builder contract. The actual fee reads, funded 184-byte Deposit submission,
48-byte Exit submission, protocol calls, receipt and header commitments belong
to that same history.

This is arbitrary-checkpoint applicability for unrestricted Form B. It makes no
mainnet, Amsterdam/Gloas history-inhabitation, or full P5 claim.
-/

namespace Blanc.Composition.BuilderRequestApplicabilityHistory

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.BuilderRequest Blanc.Lift.RequestSystem
open Blanc.Composition.BuilderRequestApplicabilityInput
open Blanc.Composition.BuilderRequestApplicabilityTail
open Blanc.Composition.BuilderRequestPublic (depositAddr exitAddr CodesKept)
open Blanc.Lift.WithdrawalRequest.FloodTx (txD senderE txD_intrinsic)
open private sevm base firstMsg first_facts first_data
  first_spawn first_enter first_resume firstRun first_commits first_prefix
  secondMsg second_facts second_world second_spawn second_enter
  second_resume secondRun second_commits second_prefix
  pairCall pairMiddle pairTail pairRun pair_kept original_empty
  message_code after_transfer prepared recovered debit_eq
  from Blanc.Composition.BuilderRequestApplicabilityCalls
open private exitResetInit frame_settle_ok writer_sta getStorVal_eq_getStor getCode_eq_state
  callSpawnMsg_init_state callSpawnParent_state
  from Blanc.Composition.BuilderRequestApplicabilityTail

/-! ## Childless retention and clean-state helpers -/

private theorem deposit_keptAt_nil (a : Adr) {s : Sevm} {d : Devm} {out : Execution}
    (hc : s.code = Deposit.code) (hf : s.benvStat.rules.stateGas = none)
    (run : Exec 0 s d out) : Exec.keptAt a run = [] := by
  apply Exec.keptAt_nil_of_parent_noExec ⟨0,s,d,out,run⟩ a
  intro n pref x hat
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas Deposit.cert_check rfl hc hf pref
  have all : ∀ f ∈ Deposit.cert.prog, f.execsSatisfy (fun _ => false) = true := by
    intro f hmem
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hmem
    rw [← treeNoExec_eq_execsSatisfy_false]
    exact Deposit.userPath.noExec j f hj
  exact Bool.noConfusion (ok.execsSatisfy (Cursor.execsSatisfy_of_reachable all reach) hat)

private theorem exit_keptAt_nil (a : Adr) {s : Sevm} {d : Devm} {out : Execution}
    (hc : s.code = Exit.code) (hf : s.benvStat.rules.stateGas = none)
    (run : Exec 0 s d out) : Exec.keptAt a run = [] := by
  apply Exec.keptAt_nil_of_parent_noExec ⟨0,s,d,out,run⟩ a
  intro n pref x hat
  obtain ⟨κ, reach, ok⟩ := cursor_of_parentPrefix_noStateGas Exit.cert_check rfl hc hf pref
  have all : ∀ f ∈ Exit.cert.prog, f.execsSatisfy (fun _ => false) = true := by
    intro f hmem
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hmem
    rw [← treeNoExec_eq_execsSatisfy_false]
    exact Exit.userPath.noExec j f hj
  exact Bool.noConfusion (ok.execsSatisfy (Cursor.execsSatisfy_of_reachable all reach) hat)

private theorem origStorVal_zero {h : B256} {s : Sevm} (d : Devm)
    (hos : s.benvStat.origState = state true (some h)) (a : Adr) (k : B256) :
    d.getOrigStorVal s a k = 0 := by
  unfold Devm.getOrigStorVal
  split
  · rfl
  · change (s.benvStat.origState.get a).stor.get k = 0
    rw [hos, ← original_empty true (some h) a k, State.get_eq_getD]
    change (((∅ : State)[a]?).getD Acct.nil).stor.get k = 0
    rw [Std.TreeMap.getElem?_emptyc]; rfl

/-! ## Literal program facts -/

private theorem Deposit_not_delegated : getDelegatedCodeAddress Deposit.code = none := by decide +kernel
private theorem Exit_not_delegated : getDelegatedCodeAddress Exit.code = none := by decide +kernel
private theorem ordinary_not_delegated : getDelegatedCodeAddress ordinaryCode = none := by decide +kernel

/-! ## Concrete `writerCode true` tail and `ordinaryCode` (`PC 0 -> 138`) -/

private def writerCallGas (h : B256) : Nat := (afterExitReset h).gasLeft - 17
private def writerCallAcc (h : B256) : Nat := accessCost ordinaryAddr (afterExitReset h).accessedAddresses
private def writerCallFwd (h : B256) : Nat := except64th (writerCallGas h - writerCallAcc h)
private def writerCallState (h : B256) : Devm :=
  (afterExitReset h).setMach ⟨[(writerCallGas h).toB256, ordinaryAddr.toBytes.toB256, 0, 0, 0, 0, 0],
    (afterExitReset h).memory, writerCallGas h, (afterExitReset h).stateGas⟩
private def writerCallBare (h : B256) : Devm :=
  addAccessedAddress ((afterExitReset h).setMach
    ⟨[], (afterExitReset h).memory, writerCallGas h, (afterExitReset h).stateGas⟩) ordinaryAddr
private def writerCallParent (h : B256) : Devm :=
  callSpawnParent (writerCallBare h) (writerCallFwd h + writerCallAcc h) 0 0 0 0
private def ordMsg (h : B256) : Msg :=
  callSpawnMsg (writer h) (writerCallParent h) (writerCallFwd h) ordinaryAddr ordinaryAddr 0 0 ordinaryCode false
private def ordSevm (h : B256) : Sevm := initSevm (ordMsg h)
private def ordBase (h : B256) : Devm := initDevm (ordMsg h)

private theorem ordBase_state (h : B256) : (ordBase h).state = (afterExitReset h).state := by
  unfold ordBase ordMsg
  rw [callSpawnMsg_init_state]
  unfold writerCallParent writerCallBare
  rw [callSpawnParent_state, Devm.setMach_state]

private theorem writerCallBare_code (h : B256) : ((afterExitReset h).setMach ⟨[], (afterExitReset h).memory, writerCallGas h, (afterExitReset h).stateGas⟩).getCode ordinaryAddr = ordinaryCode := by
  rw [getCode_eq_state, Devm.setMach_state]
  exact (afterExitReset_code_bal h).1

private theorem ord_sta (h : B256) :
    ({ ordSevm h with code := ordinaryCode, benvStat := { (ordSevm h).benvStat with fork := .prague } } : Sevm) =
      ordSevm h := rfl

private theorem writer_call_gas_bounds (h : B256) :
    599983 ≤ writerCallGas h ∧ writerCallGas h < 2 ^ 256 ∧ writerCallAcc h ≤ 2600 ∧
    580000 ≤ writerCallFwd h ∧ writerCallFwd h ≤ writerCallGas h - writerCallAcc h := by
  have f := afterExitReset_facts h
  have accLe : writerCallAcc h ≤ 2600 := by unfold writerCallAcc accessCost; split <;> decide
  unfold writerCallFwd writerCallGas except64th; exact ⟨by omega, by omega, accLe, by omega, by omega⟩

private theorem writer_ord_prefix_core (s : Sevm) (d : Devm) (g : Nat) :
    let sta := { s with code := writerCode true, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 8 ⟨152, sta, d.setMach ⟨[1], d.memory, g + 17, d.stateGas⟩⟩ =
      some ⟨180, sta, d.setMach ⟨[g.toB256, ordinaryAddr.toBytes.toB256, 0, 0, 0, 0, 0], d.memory, g, d.stateGas⟩⟩ := by
  dsimp only; revert s d g; kernel_forall_rfl_and

private theorem writer_ord_prefix (h : B256) :
    ConcreteRun.stepN 8 ⟨152, writer h, afterExitReset h⟩ = some ⟨180, writer h, writerCallState h⟩ := by
  have f := afterExitReset_facts h
  have mach : (afterExitReset h).setMach ⟨[1],(afterExitReset h).memory,
      ((afterExitReset h).gasLeft-17)+17,(afterExitReset h).stateGas⟩ = afterExitReset h := by
    rw [Nat.sub_add_cancel (by omega : 17 ≤ (afterExitReset h).gasLeft)]
    exact (St.self f.1 rfl).symm
  have core := writer_ord_prefix_core (writer h) (afterExitReset h) (writerCallGas h)
  dsimp only at core; rw [writer_sta h, show writerCallGas h + 17 = ((afterExitReset h).gasLeft - 17) + 17 from rfl, mach] at core
  exact core

private theorem writer_ord_spawn_enter (h : B256) :
    Evm.step ⟨180, writer h, writerCallState h⟩ =
      .spawn (Frame.ofCall (ordMsg h)) (.call (writerCallParent h) 0 0) 181 ∧
    (Frame.ofCall (ordMsg h)).enter = .run ⟨0, ordSevm h, ordBase h⟩ := by
  have gb := writer_call_gas_bounds h; have cb := afterExitReset_code_bal h
  have atCall : Ninst.At (writer h).code 180 (.exec .call) := by
    change Ninst.At (msg true (some h)).code 180 (.exec .call); rw [message_code true (some h)]; unfold Ninst.At; kernel_rfl
  constructor
  · rw [Evm.step_next atCall]
    have bndG : writerCallFwd h ≤ writerCallGas h := by omega
    have splitGas : calculateMsgCallGas 0 (writerCallGas h).toB256.toNat (writerCallGas h) 0 (writerCallAcc h) =
        (writerCallFwd h + writerCallAcc h, writerCallFwd h) := by
      rw [calculateMsgCallGas_zero (by omega), B256.toNat_toB256_of_lt gb.2.1, Nat.sub_zero]
      change (min (writerCallGas h) (writerCallFwd h) + writerCallAcc h, min (writerCallGas h) (writerCallFwd h)) = _
      rw [Nat.min_eq_right bndG]
    have sp := Xinst.step_call_zero_value_spawn (sevm := writer h) (devm := writerCallState h)
      (gw := (writerCallGas h).toB256) (cw := ordinaryAddr.toBytes.toB256)
      (iiw := 0) (isw := 0) (oiw := 0) (osw := 0) (s := []) (dp := false)
      (dadr := ordinaryAddr) (code := ordinaryCode) (dgc := 0) (d1 := writerCallBare h)
      (ext := 0) (acc := writerCallAcc h) (mcs := writerCallFwd h)
      (mcc := writerCallFwd h + writerCallAcc h) (CoveredFork.prague.callEra false) rfl
      (Devm.extCost_covered (by simp only [B256.toNat_zero, memExtsSize, memExtSize, ite_true]))
      (by rw [SystemWordWriter.target_word]
          have del := accessDelegation_of_code (writerCallBare_code h) ordinary_not_delegated
          simpa only [writerCallState, writerCallBare, Devm.setMach_setMach, Devm.memory_setMach,
            Devm.gasLeft_setMach, Devm.stateGas_setMach] using del)
      (by rw [SystemWordWriter.target_word]; simp only [writerCallState, Devm.setMach_accessedAddresses, writerCallAcc, Nat.add_zero])
      (by simpa only [writerCallBare, addAccessedAddress_gasLeft, Devm.setMach_gasLeft] using splitGas)
      (by simp only [writerCallBare, addAccessedAddress_gasLeft, Devm.setMach_gasLeft]; unfold writerCallFwd except64th; omega)
      (by change (1024 : Nat) ≠ 0; decide)
    simp only [Ninst.step_exec, sp, XStep.toStep, ordMsg, writerCallParent,
      SystemWordWriter.target_word, B256.toNat_zero, Nat.add_zero]
  · exact Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl
      (by change pragueRules.isPrecomp ordinaryAddr = false; decide)

-- Call 1: Deposit static fee read (PC 0 -> 27 -> 28)
private def ord1Gas (h : B256) : Nat := (ordBase h).gasLeft - 14
private def ord1Acc (h : B256) : Nat := accessCost depositAddr (ordBase h).accessedAddresses
private def ord1Fwd (h : B256) : Nat := except64th (ord1Gas h - 3 - ord1Acc h)
private def ord1State (h : B256) : Devm :=
  (ordBase h).setMach ⟨[(ord1Gas h).toB256, depositAddr.toBytes.toB256, 0, 0, 0, 32], .empty, ord1Gas h, (ordBase h).stateGas⟩
private def ord1Bare (h : B256) : Devm :=
  addAccessedAddress ((ordBase h).setMach ⟨[], .empty, ord1Gas h, (ordBase h).stateGas⟩) depositAddr
private def ord1Parent (h : B256) : Devm :=
  callSpawnParent (ord1Bare h) (ord1Fwd h + ord1Acc h + 3) 0 0 0 32
private def dFeeMsg (h : B256) : Msg :=
  staticcallSpawnMsg (ordSevm h) (ord1Parent h) (ord1Fwd h) depositAddr depositAddr 0 0 Deposit.code false
private def dFeeSevm (h : B256) : Sevm := initSevm (dFeeMsg h)
private def dFeeInit (h : B256) : Devm := initDevm (dFeeMsg h)
private def dFeeRem (h : B256) : Nat := ord1Fwd h - UserPath.feeReadGas (dFeeSevm h) (dFeeInit h) .empty 1
private def dFeePost (h : B256) : Devm := RequestFee.feeGetterPost (feeBase (dFeeSevm h) (dFeeInit h)) .empty 1 (dFeeRem h)
private def afterDFee (h : B256) : Devm := callChildPost (ord1Parent h) (dFeePost h) 0 32
private def mem1 : Mem := (Mem.empty.extends [⟨0, 0⟩, ⟨0, 32⟩]).write 0 (1 : B256).toBytes

private theorem ord1Bare_code (h : B256) : ((ordBase h).setMach ⟨[], .empty, ord1Gas h, (ordBase h).stateGas⟩).getCode depositAddr = Deposit.code := by
  rw [getCode_eq_state, Devm.setMach_state, ordBase_state]
  exact (afterExitReset_code_bal h).2.2.1

private theorem ord_p1_core (s : Sevm) (d : Devm) (g : Nat) :
    let sta := { s with code := ordinaryCode, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 6 ⟨0, sta, d.setMach ⟨[], .empty, g + 14, d.stateGas⟩⟩ =
      some ⟨27, sta, d.setMach ⟨[g.toB256, depositAddr.toBytes.toB256, 0, 0, 0, 32], .empty, g, d.stateGas⟩⟩ := by
  dsimp only; revert s d g; kernel_forall_rfl_and

private theorem ord_p1 (h : B256) :
    ConcreteRun.stepN 6 ⟨0, ordSevm h, ordBase h⟩ = some ⟨27, ordSevm h, ord1State h⟩ := by
  have gb := writer_call_gas_bounds h
  have gl : (ordBase h).gasLeft = writerCallFwd h := rfl
  have mach : (ordBase h).setMach ⟨[],.empty,((ordBase h).gasLeft-14)+14,(ordBase h).stateGas⟩ = ordBase h := by
    rw [Nat.sub_add_cancel (by omega : 14 ≤ (ordBase h).gasLeft)]
    exact (St.self rfl rfl).symm
  have core := ord_p1_core (ordSevm h) (ordBase h) (ord1Gas h)
  dsimp only at core; rw [ord_sta h, show ord1Gas h + 14 = ((ordBase h).gasLeft - 14) + 14 from rfl, mach] at core
  exact core

private theorem dFeeInit_state (h : B256) : (dFeeInit h).state = (afterExitReset h).state := by
  unfold dFeeInit dFeeMsg
  rw [scsm_state]
  unfold ord1Parent callSpawnParent ord1Bare
  change (ordBase h).state = (afterExitReset h).state
  exact ordBase_state h

private theorem dFee_xstep (h : B256) :
    Xinst.step (ordSevm h) (ord1State h) .staticcall =
      .spawn (Frame.ofCall (dFeeMsg h)) (.call (ord1Parent h) 0 32) := by
  have gb := writer_call_gas_bounds h
  have accLe : ord1Acc h ≤ 2600 := by unfold ord1Acc accessCost; split <;> decide
  have gl : (ordBase h).gasLeft = writerCallFwd h := rfl
  have splitGas : calculateMsgCallGas 0 (ord1Gas h).toB256.toNat (ord1Gas h) 3 (ord1Acc h) =
      (ord1Fwd h + ord1Acc h, ord1Fwd h) := by
    rw [calculateMsgCallGas_zero (by unfold ord1Gas; omega), B256.toNat_toB256_of_lt (by unfold ord1Gas; omega)]
    change (min (ord1Gas h) (ord1Fwd h) + ord1Acc h, min (ord1Gas h) (ord1Fwd h)) = _
    rw [Nat.min_eq_right (by unfold ord1Fwd except64th; omega)]
  have sp : Xinst.step (ordSevm h) (ord1State h) .staticcall =
      .spawn (Frame.ofCall (dFeeMsg h)) (.call (ord1Parent h) 0 32) := by
    have raw := Xinst.step_staticcall_spawn (sevm := ordSevm h) (devm := ord1State h)
      (gw := (ord1Gas h).toB256) (tw := depositAddr.toBytes.toB256)
      (iiw := 0) (isw := 0) (oiw := 0) (osw := 32) (s := []) (dp := false)
      (dadr := depositAddr) (code := Deposit.code) (dgc := 0) (d1 := ord1Bare h)
      (ext := 3) (acc := ord1Acc h) (mcs := ord1Fwd h) (mcc := ord1Fwd h + ord1Acc h)
      (CoveredFork.prague.callEra false) rfl
      (by simp only [ord1State, Devm.setMach_setMach, Devm.extCost, Devm.memory_setMach]; decide)
      (by rw [SystemWordWriter.target_word]
          have del := accessDelegation_of_code (ord1Bare_code h) Deposit_not_delegated
          simpa only [ord1State, ord1Bare, Devm.setMach_setMach, Devm.memory_setMach,
            Devm.gasLeft_setMach, Devm.stateGas_setMach] using del)
      (by rw [SystemWordWriter.target_word]; simp only [ord1State, Devm.setMach_accessedAddresses, ord1Acc, Nat.add_zero])
      (by simpa only [ord1Bare, addAccessedAddress_gasLeft, Devm.setMach_gasLeft] using splitGas)
      (by simp only [ord1Bare, addAccessedAddress_gasLeft, Devm.setMach_gasLeft]; unfold ord1Fwd ord1Gas except64th; omega)
      (by change (1023 : Nat) ≠ 0; decide)
    simpa only [dFeeMsg, ord1Parent, SystemWordWriter.target_word, B256.toNat_zero, show (32 : B256).toNat = 32 from rfl] using raw
  exact sp

private theorem dFee_resume_facts (h : B256)
    (hstack : (ord1Parent h).stack = []) (hp : (((ord1Parent h)).error = none ∧ 0 ≤ ((ord1Parent h)).refundCounter)) (hb : (((dFeeInit h)).error = none ∧ 0 ≤ ((dFeeInit h)).refundCounter)) (hblog : (dFeeInit h).logs = [])
    (ht : (dFeeMsg h).benv.stat.rules.settle.touchedSweep = false) :
    let post := RequestFee.feeGetterPost (feeBase (dFeeSevm h) (dFeeInit h)) .empty 1 (dFeeRem h)
    let after := callChildPost (ord1Parent h) post 0 32
    ((post).error = none ∧ 0 ≤ (post).refundCounter) ∧
    Resume.run (.call (ord1Parent h) 0 32) ((Frame.ofCall (dFeeMsg h)).settle (.ok post)) = .ok after ∧
    after.stack = [1] ∧ after.memory = (ord1Parent h).memory.write 0 (1 : B256).toBytes ∧
    after.state = (dFeeInit h).state ∧ after.logs = (ord1Parent h).logs ∧ ((after).error = none ∧ 0 ≤ (after).refundCounter) ∧ after.gasLeft = (ord1Parent h).gasLeft + (dFeeRem h) := by
  generalize hMsg : dFeeMsg h = m at *
  generalize hPar : ord1Parent h = p at *
  generalize hSevm : dFeeSevm h = s at *
  generalize hInit : dFeeInit h = b at *
  generalize hRem : dFeeRem h = rem at *
  intro post after
  have fb : (((feeBase s b)).error = none ∧ 0 ≤ ((feeBase s b)).refundCounter) := by
    constructor
    · simp only [feeBase,StorageSteps.feeBase,coveredSteps,afterSload_error]; exact hb.1
    · simp only [feeBase,StorageSteps.feeBase,coveredSteps,afterSload_refundCounter]; exact hb.2
  have fbLogs : (feeBase s b).logs = [] := by
    simp only [feeBase, StorageSteps.feeBase, coveredSteps, afterSload_logs, hblog]
  have ff := RequestFee.feeGetterPost_facts (feeBase s b) .empty 1 rem Mem.wf_empty (by decide)
  have pErr : post.error = none := by change post.meta.error = none; rw [ff.2.2.1]; exact fb.1
  have pRef : 0 ≤ post.refundCounter := by change 0 ≤ post.meta.refundCounter; rw [ff.2.2.1]; exact fb.2
  have pLogs : post.logs = [] := by change post.meta.logs = []; rw [ff.2.2.1]; exact fbLogs
  have cPost : ((post).error = none ∧ 0 ≤ (post).refundCounter) := ⟨pErr, pRef⟩
  have settleOk := frame_settle_ok m post pErr ht
  have resOk : Resume.run (.call p 0 32) ((Frame.ofCall m).settle (.ok post)) = .ok after := by
    rw [settleOk, Resume.run_call_ok (by rw [pErr]; rfl) (by rw [hstack]; decide)]; rfl
  have outEq : post.output = (1 : B256).toBytes := ff.1
  have ne : ((1 : B256).toBytes.take 32).isEmpty = false := by decide
  have takeEq : (1 : B256).toBytes.take 32 = (1 : B256).toBytes :=
    List.take_of_length_le (by rw [B256.length_toBytes])
  have r0 := hp.2
  refine ⟨cPost, resOk, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩ <;>
    (unfold after callChildPost incorporateChildOnSuccess Devm.memWrite liftMachPure Mach.memWrite
     simp only [outEq, takeEq, Devm.stack, Devm.memory, Devm.state,
       Devm.logs, Devm.error, Devm.refundCounter, Devm.gasLeft, Devm.setMach, Devm.setMeta, Devm.setWorld])
  · change 1 :: p.stack = [1]; rw [hstack]
  · change post.state = b.state; change (RequestFee.feeGetterPost (feeBase s b) .empty 1 rem).state = b.state; change (RequestFee.feeGetterPost (feeBase s b) .empty 1 rem).world.state = b.state; rw [ff.2.1]; change (feeBase s b).state = b.state; simp only [feeBase, StorageSteps.feeBase, coveredSteps, RequestFee.afterSload_state]
  · change p.logs ++ post.logs = p.logs; rw [pLogs, List.append_nil]
  · exact hp.1
  · change 0 ≤ p.refundCounter + post.refundCounter; omega
  · change p.gasLeft + post.gasLeft = p.gasLeft + rem; change p.gasLeft + (RequestFee.feeGetterPost (feeBase s b) .empty 1 rem).gasLeft = _; rw [ff.2.2.2.2.2.1]


private theorem dFeeGas_bound (h : B256) :
    UserPath.feeReadGas (dFeeSevm h) (dFeeInit h) .empty 1 ≤ 6000 := by
  generalize hs : dFeeSevm h = s
  generalize hb : dFeeInit h = b
  have a := sloadCost_le s b 0
  have z := sloadCost_le s (afterSload s b 0) 1
  unfold UserPath.feeReadGas UserPath.feeReadGasOn StorageSteps.feePathGas
  rw [RequestFee.feeGetterGas_empty, RequestFee.feeLoopGas_eq]
  change 13 + 30 + (133 + (25 + 87 * 1) + sloadCost s b 0 + sloadCost s (afterSload s b 0) 1) + 21 ≤ 6000
  change sloadCost s b 0 ≤ 2100 at a
  change sloadCost s (afterSload s b 0) 1 ≤ 2100 at z
  omega

private theorem dFee_step (h : B256) :
    Evm.step ⟨27, ordSevm h, ord1State h⟩ =
      .spawn (Frame.ofCall (dFeeMsg h)) (.call (ord1Parent h) 0 32) 28 ∧
    (Frame.ofCall (dFeeMsg h)).enter = .run ⟨0, dFeeSevm h, dFeeInit h⟩ ∧
    Nonempty (Exec 0 (dFeeSevm h) (dFeeInit h) (.ok (dFeePost h))) ∧
    Resume.run (.call (ord1Parent h) 0 32) ((Frame.ofCall (dFeeMsg h)).settle (.ok (dFeePost h))) = .ok (afterDFee h) ∧
    (((dFeePost h)).error = none ∧ 0 ≤ ((dFeePost h)).refundCounter) ∧ (afterDFee h).stack = [1] ∧ (afterDFee h).memory = mem1 ∧
    (afterDFee h).state = (afterExitReset h).state ∧ (afterDFee h).logs = [] ∧ (afterDFee h).output = [] ∧
    (((afterDFee h)).error = none ∧ 0 ≤ ((afterDFee h)).refundCounter) ∧ 550000 ≤ (afterDFee h).gasLeft ∧ (afterDFee h).gasLeft < 2 ^ 256 := by
  have gb := writer_call_gas_bounds h; have af := afterExitReset_facts h; have cb := afterExitReset_code_bal h
  have accLe : ord1Acc h ≤ 2600 := by unfold ord1Acc accessCost; split <;> decide
  have gl : (ordBase h).gasLeft = writerCallFwd h := rfl
  have fwdGe : 560000 ≤ ord1Fwd h := by unfold ord1Fwd ord1Gas except64th; omega
  have fwdLe : ord1Fwd h ≤ ord1Gas h - 3 - ord1Acc h := by unfold ord1Fwd except64th; omega
  have ogas : ord1Gas h ≤ writerCallFwd h := by unfold ord1Gas; rw [gl]; omega
  have fgLe := dFeeGas_bound h
  have sp := dFee_xstep h
  have s0 : (dFeeInit h).getStorVal depositAddr 0 = 0 := by
    change ((dFeeInit h).state.getStor depositAddr).get 0 = 0
    rw [dFeeInit_state]; exact af.2.2.2.2.2.2.2.1
  have s1 : (dFeeInit h).getStorVal depositAddr 1 = 0 := by
    change ((dFeeInit h).state.getStor depositAddr).get 1 = 0
    rw [dFeeInit_state]; exact af.2.2.2.2.2.2.2.2.1
  have initSt : dFeeInit h = St (dFeeInit h) [] .empty (dFeeRem h + UserPath.feeReadGas (dFeeSevm h) (dFeeInit h) .empty 1) := by
    have igl : (dFeeInit h).gasLeft = ord1Fwd h := rfl
    exact (pre_eq_St rfl rfl (by unfold dFeeRem; omega)).symm
  have fee1 : ((17 : B256) / (17 : B256)) = 1 := by decide
  have ex : Nonempty (Exec 0 (dFeeSevm h) (dFeeInit h) (.ok (dFeePost h))) := by
    rw [initSt]; unfold dFeePost; rw [← fee1]
    exact Deposit.exec_fee_read_exact (sevm := dFeeSevm h) (b := dFeeInit h) (M := .empty) (G := dFeeRem h)
      (iterations := 1) (finalOutput := 17) rfl CoveredFork.prague (by decide)
      (by change ordinaryAddr ≠ systemAddress; decide) rfl rfl
      (by change (dFeeInit h).getStorVal depositAddr 0 ≠ B256.max; rw [s0]; decide)
      (by rw [show storedExcess 8 (dFeeSevm h) (dFeeInit h) = 0 from by
            unfold storedExcess; change targetExcess 8 ((dFeeInit h).getStorVal depositAddr 0) ((dFeeInit h).getStorVal depositAddr 1) = 0
            rw [s0, s1]; decide]; exact quote_zero_excess)
  have rf := dFee_resume_facts h rfl ⟨rfl, by change (0 : Int) ≤ 0; omega⟩ ⟨rfl, by change (0 : Int) ≤ 0; omega⟩ rfl rfl
  have atSC : Ninst.At (ordSevm h).code 27 (.exec .staticcall) := by
    change Ninst.At ordinaryCode 27 (.exec .staticcall); unfold Ninst.At; kernel_rfl
  have pgl : (ord1Parent h).gasLeft = ord1Gas h - (ord1Fwd h + ord1Acc h + 3) := rfl
  exact ⟨by rw [Evm.step_next atSC]; simp only [Ninst.step_exec, sp, XStep.toStep],
    Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl
      (by change pragueRules.isPrecomp depositAddr = false; decide),
    ex, rf.2.1, rf.1, rf.2.2.1, rf.2.2.2.1, rf.2.2.2.2.1.trans (dFeeInit_state h), rf.2.2.2.2.2.1, rfl,
    rf.2.2.2.2.2.2.1,
    by unfold afterDFee dFeePost; rw [rf.2.2.2.2.2.2.2, pgl]; unfold dFeeRem ord1Gas; omega,
    by unfold afterDFee dFeePost; rw [rf.2.2.2.2.2.2.2, pgl]; unfold dFeeRem ord1Gas; omega⟩

-- Call 2: Deposit 184-byte paid submission (PC 28 -> 76 -> 77)
private def dSubVal : B256 := (10 ^ 18 + 1 : Nat).toB256
private def mem2Pre : Mem := mem1.write 56 ((10 ^ 9 : Nat).toB256).toBytes
private def mem2 : Mem := mem2Pre.extends [⟨0, 184⟩, ⟨0, 0⟩]
private theorem mem2_amount : Deposit.amountMask &&& Bytes.toB256 (((mem2.read 0 184).1).sliceD 56 32 0) = (10^9 : Nat).toB256 := by
  have wf1 : Mem.Wf mem1 := Mem.Wf.write (Mem.Wf.extends _ Mem.wf_empty) _ _
  have rd1 : Mem.Reads mem1 (Bytes.writeAt [] 0 (1 : B256).toBytes) :=
    Mem.Reads.write (Mem.Wf.extends _ Mem.wf_empty) (Mem.Reads.extends _ Mem.reads_empty) _ _
  have rd2 : Mem.Reads mem2 (Bytes.writeAt (Bytes.writeAt [] 0 (1 : B256).toBytes) 56 ((10^9 : Nat).toB256).toBytes) :=
    Mem.Reads.extends _ (Mem.Reads.write wf1 rd1 _ _)
  rw [rd2.read, Bytes.sliceD_sliceD_of_le _ 0 184 56 32 (by decide), Nat.zero_add, Bytes.readWord_writeAt_self]
  decide

private def ord2Gas (h : B256) : Nat := (afterDFee h).gasLeft - 42
private def ord2Acc (h : B256) : Nat := accessCost depositAddr (afterDFee h).accessedAddresses
private def ord2Extra (h : B256) : Nat := ord2Acc h + 9000
private def ord2Fwd (h : B256) : Nat := except64th (ord2Gas h - 9 - ord2Extra h) + 2300
private def ord2State (h : B256) : Devm :=
  (afterDFee h).setMach ⟨[(ord2Gas h).toB256, depositAddr.toBytes.toB256, dSubVal, 0, (184 : B256), 0, 0],
    mem2Pre, ord2Gas h, (afterDFee h).stateGas⟩
private def ord2Bare (h : B256) : Devm :=
  addAccessedAddress ((afterDFee h).setMach ⟨[], mem2Pre, ord2Gas h, (afterDFee h).stateGas⟩) depositAddr
private def ord2Parent (h : B256) : Devm :=
  callSpawnParent (ord2Bare h) (ord2Fwd h - 2300 + ord2Extra h + 9) 0 184 0 0
private def dSubMsg (h : B256) : Msg :=
  valueCallSpawnMsg (ordSevm h) (ord2Parent h) (ord2Fwd h) dSubVal depositAddr depositAddr 0 184 Deposit.code false
private def dSubNextBenv (h : B256) : Benv :=
  match (dSubMsg h).benvAfterTransfer with | .ok b => b | .error _ => (dSubMsg h).benv
private def dSubSevm (h : B256) : Sevm := initSevm ((dSubMsg h).withBenv (dSubNextBenv h))
private def dSubInit (h : B256) : Devm := initDevm ((dSubMsg h).withBenv (dSubNextBenv h))
private def dSubRem (h : B256) : Nat := ord2Fwd h - Deposit.submissionGas (dSubSevm h) (dSubInit h) .empty 1
private def dSubPost (h : B256) : Devm := Deposit.submissionPost (dSubSevm h) (feeBase (dSubSevm h) (dSubInit h)) .empty (dSubRem h)
private def afterDSub (h : B256) : Devm := callChildPost (ord2Parent h) (dSubPost h) 0 0

private theorem ord_p2_core (s : Sevm) (d : Devm) (g : Nat) :
    let sta := { s with code := ordinaryCode, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 14 ⟨28, sta, d.setMach ⟨[1], mem1, g + 42, d.stateGas⟩⟩ =
      some ⟨76, sta, d.setMach ⟨[g.toB256, depositAddr.toBytes.toB256, dSubVal, 0, (184 : B256), 0, 0], mem2Pre, g, d.stateGas⟩⟩ := by
  dsimp only; revert s d g; kernel_forall_rfl_and

private theorem ord_p2 (h : B256) :
    ConcreteRun.stepN 14 ⟨28, ordSevm h, afterDFee h⟩ = some ⟨76, ordSevm h, ord2State h⟩ := by
  have df := dFee_step h
  have mach : (afterDFee h).setMach ⟨[1],mem1,((afterDFee h).gasLeft-42)+42,(afterDFee h).stateGas⟩ = afterDFee h := by
    rw [Nat.sub_add_cancel (by omega : 42 ≤ (afterDFee h).gasLeft)]
    exact (St.self df.2.2.2.2.2.1 df.2.2.2.2.2.2.1).symm
  have core := ord_p2_core (ordSevm h) (afterDFee h) (ord2Gas h)
  dsimp only at core; rw [ord_sta h, show ord2Gas h + 42 = ((afterDFee h).gasLeft - 42) + 42 from rfl, mach] at core
  exact core

private theorem mem2Pre_size : mem2Pre.size = 96 := by
  have first : mem1.size = 32 := by
    unfold mem1
    rw [Mem.size_write_of_length (B256.length_toBytes _) (by decide)]
    rfl
  unfold mem2Pre
  rw [Mem.size_write_of_length (B256.length_toBytes _) (by decide), first]
  rfl

private theorem afterDFee_code_bal (h : B256) :
    (afterDFee h).getCode depositAddr = Deposit.code ∧
    (afterDFee h).getBal ordinaryAddr = (2^100 : Nat).toB256 ∧
    (afterDFee h).getCode exitAddr = Exit.code := by
  have df := dFee_step h
  have cb := afterExitReset_code_bal h
  refine ⟨?_,?_,?_⟩
  · rw [getCode_eq_state, df.2.2.2.2.2.2.2.1]; exact cb.2.2.1
  · change ((afterDFee h).state.get ordinaryAddr).bal = _
    rw [df.2.2.2.2.2.2.2.1]; exact cb.2.1
  · rw [getCode_eq_state, df.2.2.2.2.2.2.2.1]; exact cb.2.2.2.1

private theorem ord2_precode (h : B256) :
    ((afterDFee h).setMach ⟨[],mem2Pre,ord2Gas h,(afterDFee h).stateGas⟩).getCode depositAddr = Deposit.code := by
  rw [getCode_eq_state, Devm.setMach_state]
  exact (afterDFee_code_bal h).1

private theorem dSubMsg_state (h : B256) : (dSubMsg h).benv.state = (afterDFee h).state := by
  unfold dSubMsg
  generalize hp : ord2Parent h = p
  change (initDevm (valueCallSpawnMsg (ordSevm h) p (ord2Fwd h) dSubVal
    depositAddr depositAddr 0 184 Deposit.code false)).state = (afterDFee h).state
  rw [vcsm_state, ← hp]
  unfold ord2Parent callSpawnParent ord2Bare
  rfl

private theorem ord2_range (h : B256) : 549958 ≤ ord2Gas h ∧ ord2Gas h < 2^256 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,lower,upper⟩ := dFee_step h
  unfold ord2Gas
  generalize hg : (afterDFee h).gasLeft = g at lower upper ⊢
  constructor <;> omega

private theorem dSub_xstep (h : B256) :
    Xinst.step (ordSevm h) (ord2State h) .call =
      .spawn (Frame.ofCall (dSubMsg h)) (.call (ord2Parent h) 0 0) := by
  have range := ord2_range h
  have cb := afterDFee_code_bal h
  have accLe : ord2Acc h ≤ 2600 := by unfold ord2Acc accessCost; split <;> decide
  have splitGas : calculateMsgCallGas dSubVal.toNat (ord2Gas h).toB256.toNat (ord2Gas h) 9
      (ord2Acc h + 0 + gasCallValue) = (ord2Fwd h - 2300 + ord2Extra h, ord2Fwd h) := by
    unfold ord2Fwd ord2Extra
    generalize hg : ord2Gas h = g at range ⊢
    generalize ha : ord2Acc h = acc at accLe ⊢
    unfold calculateMsgCallGas
    rw [ite_eq_right (by decide : dSubVal.toNat ≠ 0),
      ite_eq_right (by change ¬ g < acc + 0 + 9000 + 9; omega),
      B256.toNat_toB256_of_lt range.2]
    have le : except64th (g - 9 - (acc + 9000)) ≤ g := by unfold except64th; omega
    change (min g (except64th (g - 9 - (acc + 9000))) + (acc + 9000),
      min g (except64th (g - 9 - (acc + 9000))) + 2300) = _
    rw [Nat.min_eq_right le]
    simp only [Nat.add_sub_cancel]
  have cBare : (ord2Bare h).getCode depositAddr = Deposit.code := by
    unfold ord2Bare; rw [addAccessedAddress_getCode]; exact ord2_precode h
  have notEmpty : ¬ ((ord2Bare h).getAcct depositAddr).Empty := by
    intro bad
    have sz : ((ord2Bare h).getCode depositAddr).size = 0 := bad.1
    rw [cBare] at sz
    exact (by decide +kernel : Deposit.code.size ≠ 0) sz
  have affordable : ¬ ((ord2Bare h).getAcct (ordSevm h).currentTarget).bal < dSubVal := by
    change ¬ ((ord2Bare h).state.get ordinaryAddr).bal < dSubVal
    unfold ord2Bare
    rw [addAccessedAddress_state, Devm.setMach_state]
    change ¬ (afterDFee h).getBal ordinaryAddr < dSubVal
    rw [cb.2.1]; decide
  have raw := Xinst.step_call_nonzero_spawn (sevm := ordSevm h) (devm := ord2State h)
    (gw := (ord2Gas h).toB256) (cw := depositAddr.toBytes.toB256) (vw := dSubVal)
    (iiw := 0) (isw := 184) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := depositAddr) (code := Deposit.code) (dgc := 0) (d1 := ord2Bare h)
    (ext := 9) (acc := ord2Acc h) (create := 0) (mcs := ord2Fwd h)
    (mcc := ord2Fwd h - 2300 + ord2Extra h)
    (CoveredFork.prague.callEra false) rfl (by decide)
    (by simp only [ord2State, Devm.setMach_setMach, Devm.extCost, Devm.memory_setMach, mem2Pre_size]; decide)
    (by rw [SystemWordWriter.target_word]
        have del := accessDelegation_of_code (ord2_precode h) Deposit_not_delegated
        simpa only [ord2State, ord2Bare, Devm.setMach_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach, Devm.stateGas_setMach] using del)
    (by rw [SystemWordWriter.target_word]; simp only [ord2State, Devm.setMach_accessedAddresses, ord2Acc, Nat.add_zero])
    (by rw [SystemWordWriter.target_word, ite_eq_left notEmpty])
    (by simpa only [ord2Bare, addAccessedAddress_gasLeft, Devm.setMach_gasLeft] using splitGas)
    (by simp only [ord2Bare, addAccessedAddress_gasLeft, Devm.setMach_gasLeft]
        unfold ord2Fwd ord2Extra
        generalize hg : ord2Gas h = g at range ⊢
        generalize ha : ord2Acc h = acc at accLe ⊢
        unfold except64th; omega)
    rfl affordable (by change (1023 : Nat) ≠ 0; decide)
  simpa only [dSubMsg, ord2Parent, SystemWordWriter.target_word, B256.toNat_zero,
    show (184 : B256).toNat = 184 from rfl] using raw

private theorem dSubInit_state (h : B256) : (dSubInit h).state = (dSubNextBenv h).state := by
  unfold dSubInit
  generalize hm : dSubMsg h = m
  generalize hb : dSubNextBenv h = nb
  rfl

private theorem dSubSevm_data (h : B256) : (dSubSevm h).data = (mem2.read 0 184).1 := by
  unfold dSubSevm
  generalize hm : dSubMsg h = m
  generalize hb : dSubNextBenv h = nb
  change m.data = _
  rw [← hm]
  change (ord2Parent h).memory.data.sliceD 0 184 0 = _
  unfold ord2Parent
  rw [callSpawnParent_memory_data]
  unfold ord2Bare
  rw [addAccessedAddress_setMach_memory]
  simp only [mem_read_fst, mem2, Mem.extends]

private theorem dSub_transfer (h : B256) :
    (dSubMsg h).benvAfterTransfer = .ok (dSubNextBenv h) ∧
    (∀ a, (dSubNextBenv h).state.getCode a = (afterDFee h).state.getCode a) ∧
    (∀ a, ((afterDFee h).state.getCode a).size ≠ 0 →
      (dSubNextBenv h).state.getStor a = (afterDFee h).state.getStor a) ∧
    ((dSubNextBenv h).state.get ordinaryAddr).bal = (dSubMsg h).benv.state.bal ordinaryAddr - dSubVal ∧
    CoveredFork (dSubSevm h).benvStat.fork ∧
    (dSubSevm h).benvStat.origState = state true (some h) ∧ (dSubInit h).logs = [] := by
  have balOrd : (dSubMsg h).benv.state.bal ordinaryAddr = (2 ^ 100 : Nat).toB256 := by
    rw [dSubMsg_state]; exact (afterDFee_code_bal h).2.1
  have affordableMsg : ¬ (dSubMsg h).benv.state.bal (dSubMsg h).caller < (dSubMsg h).value := by
    change ¬ (dSubMsg h).benv.state.bal ordinaryAddr < dSubVal
    rw [balOrd]; decide
  obtain ⟨mid, sub, bt⟩ := Msg.benvAfterTransfer_of_affordable (dSubMsg h) rfl affordableMsg
    (by change dSubVal ≠ 0; decide)
  have htr : (dSubMsg h).benvAfterTransfer = .ok (dSubNextBenv h) := by
    unfold dSubNextBenv; rw [bt]
  have trCode (a : Adr) : (dSubNextBenv h).state.getCode a = (afterDFee h).state.getCode a := by
    rw [benvAfterTransfer_ok_getCode htr a, dSubMsg_state]
  have trStor (a : Adr) (hc : ((afterDFee h).state.getCode a).size ≠ 0) :
      (dSubNextBenv h).state.getStor a = (afterDFee h).state.getStor a := by
    have codeLive : ((dSubMsg h).benv.state.get a).code.size ≠ 0 := by
      change ((dSubMsg h).benv.state.getCode a).size ≠ 0
      rw [dSubMsg_state]; exact hc
    rw [benvAfterTransfer_ok_getStor htr a (Or.inr (Or.inr codeLive)), dSubMsg_state]
  have trBal : ((dSubNextBenv h).state.get ordinaryAddr).bal =
      (dSubMsg h).benv.state.bal ordinaryAddr - dSubVal := by
    have nbState : (dSubNextBenv h).state = mid.addBal depositAddr dSubVal := by
      unfold dSubNextBenv; rw [bt]; rfl
    have midEq : mid = (dSubMsg h).benv.state.setBal ordinaryAddr
        ((dSubMsg h).benv.state.bal ordinaryAddr - dSubVal) := by
      change (dSubMsg h).benv.state.subBal ordinaryAddr dSubVal = some mid at sub
      have aff : ¬ (dSubMsg h).benv.state.bal ordinaryAddr < dSubVal := by rw [balOrd]; decide
      simp only [State.subBal, aff, ite_false, Option.some.injEq] at sub
      exact sub.symm
    rw [nbState, addBal_get_ne _ (by decide : depositAddr ≠ ordinaryAddr), midEq]
    exact setBal_bal_self _ _ _
  have calleeFork : CoveredFork (dSubSevm h).benvStat.fork := by
    unfold dSubSevm
    rw [initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat htr]
    exact CoveredFork.prague
  have calleeOrig : (dSubSevm h).benvStat.origState = state true (some h) := by
    unfold dSubSevm
    rw [initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat htr]
    rfl
  have initLogs : (dSubInit h).logs = [] := by
    unfold dSubInit
    apply Lift.initDevm_logs
    change (dSubNextBenv h).stat.rules.stateGas = none
    rw [benvAfterTransfer_stat htr]
    exact CoveredFork.prague.rules_stateGas_none
  exact ⟨htr,trCode,trStor,trBal,calleeFork,calleeOrig,initLogs⟩

private theorem ord2Parent_memory (h : B256) : (ord2Parent h).memory = mem2 := by
  unfold ord2Parent
  rw [callSpawnParent_memory]
  unfold ord2Bare
  rw [addAccessedAddress_setMach_memory]
  rfl

private theorem ord2Parent_gas (h : B256) :
    (ord2Parent h).gasLeft = ord2Gas h - (ord2Fwd h - 2300 + ord2Extra h + 9) := by
  unfold ord2Parent
  rw [callSpawnParent_gasLeft]
  simp only [ord2Bare, addAccessedAddress_gasLeft, Devm.setMach_gasLeft]

open Deposit in
private theorem dSubGas_bound (h : B256) :
    submissionGas (dSubSevm h) (dSubInit h) .empty 1 ≤ 200000 := by
  generalize hs : dSubSevm h = s
  generalize hb : dSubInit h = b
  have W : ∀ d k v, (coveredSteps s).writeCharge d k v ≤ 22100 :=
    fun d k v => (sstoreCost_le_value s d k v).trans
      (Nat.add_le_add_left (sstoreValueCost_le _ _ _) _)
  have L := sloadCost_le s
  have R : ∀ d K, Steps.recordWritesGas (coveredSteps s) d K ≤
      6 * 22100 :=
    fun d K => (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (W _ _ _) (W _ _ _)) (W _ _ _)) (W _ _ _)) (W _ _ _)) (W _ _ _)).trans (by omega)
  have CL := copyLog_gas s
  unfold submissionGas submissionGasOn Steps.bodyGas StorageSteps.feePathGas
  rw [RequestFee.feeLoopGas_eq, feePathFixedGas, RequestSystem.dispatchGas]
  have a1 := L b 0
  have a2 := L ((coveredSteps s).afterRead b 0) 1
  have a3 := L ((coveredSteps s).feeBase b) 1
  have a4 := L ((coveredSteps s).countStore ((coveredSteps s).feeBase b)) 3
  have w1 := W ((coveredSteps s).afterRead ((coveredSteps s).feeBase b) 1) 1
    (1 + countWord s ((coveredSteps s).feeBase b))
  have w2 := W (Steps.logged (coveredSteps s) ((coveredSteps s).feeBase b) .empty) 3
    (1 + (coveredSteps s).tailWord ((coveredSteps s).feeBase b))
  have w3 := R ((coveredSteps s).tailRead ((coveredSteps s).feeBase b))
    (submissionKey ((coveredSteps s).tailWord ((coveredSteps s).feeBase b)))
  simp only [gasColdSload] at a1 a2 a3 a4
  omega



private theorem dSubPost_clean (h : B256) : (((dSubPost h)).error = none ∧ 0 ≤ ((dSubPost h)).refundCounter) := by
  have hos : (dSubSevm h).benvStat.origState = state true (some h) := (dSub_transfer h).2.2.2.2.2.1
  have hd : (((dSubInit h)).error = none ∧ 0 ≤ ((dSubInit h)).refundCounter) := ⟨rfl, by change (0 : Int) ≤ 0; omega⟩
  have clean_st {d : Devm} {st : List B256} {m : Mem} {g : Nat} (hd : ((d).error = none ∧ 0 ≤ (d).refundCounter)) :
      (((St d st m g)).error = none ∧ 0 ≤ ((St d st m g)).refundCounter) := ⟨hd.1, hd.2⟩

  have clean_addLog {d : Devm} {l : Log} (hd : ((d).error = none ∧ 0 ≤ (d).refundCounter)) :
      (((d.addLog l)).error = none ∧ 0 ≤ ((d.addLog l)).refundCounter) := ⟨hd.1, hd.2⟩

  have clean_sload {d : Devm} {k : B256} (hd : ((d).error = none ∧ 0 ≤ (d).refundCounter)) :
      (((afterSload (dSubSevm h) d k)).error = none ∧ 0 ≤ ((afterSload (dSubSevm h) d k)).refundCounter) := by
    unfold afterSload; split <;> exact ⟨hd.1, hd.2⟩

  have clean_sstore {d : Devm} {k v : B256}
      (hd : ((d).error = none ∧ 0 ≤ (d).refundCounter)) :
      (((afterSstore (dSubSevm h) d k v)).error = none ∧ 0 ≤ ((afterSstore (dSubSevm h) d k v)).refundCounter) := by
    have origZero : d.getOrigStorVal (dSubSevm h) (dSubSevm h).currentTarget k = 0 := origStorVal_zero d hos (dSubSevm h).currentTarget k
    exact ⟨(afterSstore_error (dSubSevm h) d k v).trans hd.1,
      hd.2.trans (afterSstore_refundCounter_ge_of_safe (dSubSevm h) d k v (Or.inr (Or.inl origZero)))⟩

  unfold dSubPost
  unfold Deposit.submissionPost Deposit.Steps.submissionPost Deposit.Steps.submissionBase
    Deposit.Steps.logged Deposit.Steps.recordsWritten Deposit.Steps.recordStore Deposit.Steps.wordStore
    StorageSteps.tailRead StorageSteps.countStore feeBase StorageSteps.feeBase coveredSteps
  dsimp only
  apply clean_st
  apply clean_sstore
  apply clean_addLog
  apply clean_sstore
  apply clean_sstore
  apply clean_sstore
  apply clean_sstore
  apply clean_sstore
  apply clean_sstore
  apply clean_sload
  apply clean_sstore
  apply clean_sload
  apply clean_sload
  apply clean_sload
  exact hd

private theorem dSub_resume_facts (h : B256)
    (hstack : (ord2Parent h).stack = []) (hpout : (ord2Parent h).output = []) (hp : (((ord2Parent h)).error = none ∧ 0 ≤ ((ord2Parent h)).refundCounter)) (hc : (((dSubPost h)).error = none ∧ 0 ≤ ((dSubPost h)).refundCounter))
    (hout : (dSubPost h).output = []) (hlogs : (dSubPost h).logs = [(⟨(dSubSevm h).currentTarget,[],(dSubSevm h).data⟩ : Log)]) (haddr : (⟨(dSubSevm h).currentTarget,[],(dSubSevm h).data⟩ : Log).address ≠ depositContractAddress)
    (hpAvoid : ∀ l ∈ (ord2Parent h).logs, l.address ≠ depositContractAddress)
    (ht : (dSubMsg h).benv.stat.rules.settle.touchedSweep = false) :
    let after := callChildPost (ord2Parent h) (dSubPost h) 0 0
    Resume.run (.call (ord2Parent h) 0 0) ((Frame.ofCall (dSubMsg h)).settle (.ok (dSubPost h))) = .ok after ∧
    after.stack = [1] ∧ after.memory = (ord2Parent h).memory ∧ after.state = (dSubPost h).state ∧ after.output = [] ∧
    (∀ l ∈ after.logs, l.address ≠ depositContractAddress) ∧ ((after).error = none ∧ 0 ≤ (after).refundCounter) ∧
    after.gasLeft = (ord2Parent h).gasLeft + (dSubPost h).gasLeft := by
  intro after
  have settleOk := frame_settle_ok (dSubMsg h) (dSubPost h) hc.1 ht
  have resOk : Resume.run (.call (ord2Parent h) 0 0) ((Frame.ofCall (dSubMsg h)).settle (.ok (dSubPost h))) = .ok after := by
    rw [settleOk, Resume.run_call_ok (by rw [hc.1]; rfl) (by rw [hstack]; decide)]; rfl
  have cf := callChildPost_facts (ord2Parent h) (dSubPost h) 0 0 hout
  have r0 := hp.2; have r1 := hc.2
  refine ⟨resOk, by rw [cf.1, hstack], cf.2.1, cf.2.2.2.1, cf.2.2.2.2.2.2.2.2.1.trans hpout, ?_,
    ⟨cf.2.2.2.2.2.2.2.1.trans hp.1, by rw [cf.2.2.2.2.2.2.1]; omega⟩, cf.2.2.1⟩
  intro l hl; rw [cf.2.2.2.2.2.1, hlogs, List.mem_append] at hl
  rcases hl with hl | hl
  · exact hpAvoid l hl
  · obtain rfl := List.mem_singleton.mp hl; exact haddr

private theorem dSub_step (h : B256) :
    Evm.step ⟨76, ordSevm h, ord2State h⟩ =
      .spawn (Frame.ofCall (dSubMsg h)) (.call (ord2Parent h) 0 0) 77 ∧
    (Frame.ofCall (dSubMsg h)).enter = .run ⟨0, dSubSevm h, dSubInit h⟩ ∧
    Nonempty (Exec 0 (dSubSevm h) (dSubInit h) (.ok (dSubPost h))) ∧
    Resume.run (.call (ord2Parent h) 0 0) ((Frame.ofCall (dSubMsg h)).settle (.ok (dSubPost h))) = .ok (afterDSub h) ∧
    (((dSubPost h)).error = none ∧ 0 ≤ ((dSubPost h)).refundCounter) ∧ (afterDSub h).stack = [1] ∧ (afterDSub h).memory = mem2 ∧
    (afterDSub h).getCode exitAddr = Exit.code ∧
    (afterDSub h).getBal ordinaryAddr = (2 ^ 100 : Nat).toB256 - dSubVal ∧
    (afterDSub h).getStorVal exitAddr 0 = 0 ∧ (afterDSub h).getStorVal exitAddr 1 = 0 ∧
    (afterDSub h).output = [] ∧ (∀ l ∈ (afterDSub h).logs, l.address ≠ depositContractAddress) ∧
    (((afterDSub h)).error = none ∧ 0 ≤ ((afterDSub h)).refundCounter) ∧ 300000 ≤ (afterDSub h).gasLeft ∧ (afterDSub h).gasLeft < 2 ^ 256 := by
  have range := ord2_range h
  have df := dFee_step h; have af := afterExitReset_facts h; have cb := afterExitReset_code_bal h
  have accLe : ord2Acc h ≤ 2600 := by unfold ord2Acc accessCost; split <;> decide
  have fwdGe : 520000 ≤ ord2Fwd h := by unfold ord2Fwd ord2Gas ord2Extra except64th; omega
  have codeDep : (afterDFee h).getCode depositAddr = Deposit.code := by
    change (afterDFee h).state.getCode depositAddr = _; rw [df.2.2.2.2.2.2.2.1]; exact cb.2.2.1
  have balOrd : (dSubMsg h).benv.state.bal ordinaryAddr = (2^100 : Nat).toB256 := by
    rw [dSubMsg_state]; exact (afterDFee_code_bal h).2.1
  obtain ⟨htr,trCode,trStor,trBal,calleeFork,calleeOrig,initLogs⟩ := dSub_transfer h
  have sp := dSub_xstep h
  have depStor : (dSubInit h).state.getStor depositAddr = (afterExitReset h).state.getStor depositAddr := by
    rw [dSubInit_state]
    rw [trStor depositAddr (by rw [← getCode_eq_state, codeDep]; decide +kernel)]
    exact congrArg (fun s => s.getStor depositAddr) df.2.2.2.2.2.2.2.1
  have exitStorInit : (dSubInit h).state.getStor exitAddr = (afterExitReset h).state.getStor exitAddr := by
    rw [dSubInit_state]
    rw [trStor exitAddr (by rw [df.2.2.2.2.2.2.2.1, show (afterExitReset h).state.getCode exitAddr = Exit.code from cb.2.2.2.1]; decide +kernel)]
    exact congrArg (fun s => s.getStor exitAddr) df.2.2.2.2.2.2.2.1
  have s0 : (dSubInit h).getStorVal depositAddr 0 = 0 := by
    change ((dSubInit h).state.getStor depositAddr).get 0 = 0
    rw [depStor]; exact af.2.2.2.2.2.2.2.1
  have s1 : (dSubInit h).getStorVal depositAddr 1 = 0 := by
    change ((dSubInit h).state.getStor depositAddr).get 1 = 0
    rw [depStor]; exact af.2.2.2.2.2.2.2.2.1
  have sgBound := dSubGas_bound h
  have hlen : (dSubSevm h).data.length = 184 := by
    rw [dSubSevm_data]
    change (mem2.data.sliceD 0 184 0).length = 184
    rw [Array.sliceD_eq_map, List.length_map, List.length_range]
  have initSt : dSubInit h = St (dSubInit h) [] .empty (dSubRem h + Deposit.submissionGas (dSubSevm h) (dSubInit h) .empty 1) := by
    have igl : (dSubInit h).gasLeft = ord2Fwd h := rfl
    exact (pre_eq_St rfl rfl (by unfold dSubRem; omega)).symm
  have amount : Deposit.amountGwei (dSubSevm h) = (10^9 : Nat).toB256 := by
    rw [Deposit.amountGwei, Sevm.dataWord, dSubSevm_data]
    simpa only [show (56 : B256).toNat = 56 from rfl] using mem2_amount
  have credit : Deposit.creditedWei (dSubSevm h) = 10^18 := by
    rw [Deposit.creditedWei, amount]; decide
  have admitted : Deposit.Admitted (dSubSevm h) ((17 : B256) / 17) := by
    constructor
    · rw [credit]
    · rw [credit]
      change 10^18 + ((17 : B256) / 17).toNat ≤ dSubVal.toNat
      decide
  have ex : Nonempty (Exec 0 (dSubSevm h) (dSubInit h) (.ok (dSubPost h))) := by
    rw [initSt]; unfold dSubPost
    exact Deposit.exec_submission_exact (sevm := dSubSevm h) (b := dSubInit h) (M := .empty)
      (G := dSubRem h) (iterations := 1) (finalOutput := 17) rfl calleeFork
      (by change ordinaryAddr ≠ systemAddress; decide) hlen rfl
      (by unfold gCallStipend dSubRem; omega) (by change (dSubInit h).getStorVal depositAddr 0 ≠ B256.max; rw [s0]; decide)
      (by rw [show storedExcess 8 (dSubSevm h) (dSubInit h) = 0 from by
            unfold storedExcess; change targetExcess 8 ((dSubInit h).getStorVal depositAddr 0) ((dSubInit h).getStorVal depositAddr 1) = 0
            rw [s0, s1]; decide]; exact quote_zero_excess)
      admitted
  have cPost : (((dSubPost h)).error = none ∧ 0 ≤ ((dSubPost h)).refundCounter) := dSubPost_clean h
  have eff : Deposit.SubmissionEffects (dSubSevm h) (dSubInit h) (dSubPost h) := by
    simpa only [dSubPost, Deposit.submissionPost, feeBase] using
      (Deposit.submissionPost_effects (sevm := dSubSevm h) (b := dSubInit h) (M := .empty)
        (coveredSteps_valid calleeFork) hlen Mem.wf_empty (dSubRem h))
  have pOut : (ord2Parent h).output = [] := df.2.2.2.2.2.2.2.2.2.1
  have pClean : (((ord2Parent h)).error = none ∧ 0 ≤ ((ord2Parent h)).refundCounter) := ⟨df.2.2.2.2.2.2.2.2.2.2.1.1, df.2.2.2.2.2.2.2.2.2.2.1.2⟩
  have sr := dSub_resume_facts h rfl pOut pClean cPost
    (eff.output.trans rfl) (by rw [eff.logs, initLogs]; rfl) (by change depositAddr ≠ depositContractAddress; decide)
    (by change ∀ l ∈ (afterDFee h).logs, _; rw [df.2.2.2.2.2.2.2.2.1]; intro _ hm; nomatch hm) rfl
  have afterState : (afterDSub h).state = (dSubPost h).state := by
    simpa only [afterDSub] using sr.2.2.2.1
  have nonprecomp : ((dSubMsg h).withBenv (dSubNextBenv h)).benv.stat.rules.isPrecomp depositAddr = false := by
    change (dSubNextBenv h).stat.rules.isPrecomp depositAddr = false
    rw [benvAfterTransfer_stat htr]
    change pragueRules.isPrecomp depositAddr = false
    decide
  have enters : (Frame.ofCall (dSubMsg h)).enter = .run ⟨0,dSubSevm h,dSubInit h⟩ := by
    simpa only [Frame.ofCall,initEvm,dSubSevm,dSubInit] using
      (Frame.enter_run_of_nonprecompile (f := Frame.ofCall (dSubMsg h))
        (benv := dSubNextBenv h) (adr := depositAddr) htr rfl nonprecomp)
  have stBase := Deposit.submissionBase_state (sevm := dSubSevm h) (b := dSubInit h) (M := .empty)
    (coveredSteps_valid calleeFork)
  have exitCode : (afterDSub h).getCode exitAddr = Exit.code := by
    change (afterDSub h).state.getCode exitAddr = _; rw [afterState]
    simp only [dSubPost, Deposit.submissionPost, Deposit.Steps.submissionPost, St_state, feeBase]
    rw [stBase]; simp only [State.getCode_setStorVal]
    rw [dSubInit_state]
    exact (trCode exitAddr).trans (by rw [df.2.2.2.2.2.2.2.1]; exact cb.2.2.2.1)
  have exitStorAfter : (afterDSub h).state.getStor exitAddr = (afterExitReset h).state.getStor exitAddr := by
    rw [afterState]; exact (eff.otherStorage exitAddr (by change exitAddr ≠ depositAddr; decide)).trans exitStorInit
  have initBal : (dSubInit h).getBal ordinaryAddr = (2^100 : Nat).toB256 - dSubVal := by
    simp only [Devm.getBal, Devm.getAcct]
    rw [dSubInit_state]
    exact trBal.trans (by rw [balOrd])
  have afterBal : (afterDSub h).getBal ordinaryAddr = (2^100 : Nat).toB256 - dSubVal :=
    (getBal_eq_of_state_eq afterState ordinaryAddr).trans ((eff.balance ordinaryAddr).trans initBal)
  have atCall : Ninst.At (ordSevm h).code 76 (.exec .call) := by
    change Ninst.At ordinaryCode 76 (.exec .call); unfold Ninst.At; kernel_rfl
  have postGas : (dSubPost h).gasLeft = dSubRem h := by
    simp only [dSubPost, Deposit.submissionPost, Deposit.Steps.submissionPost, St.gasLeft]
  have pgl : (ord2Parent h).gasLeft + (dSubPost h).gasLeft =
      (ord2Gas h - (ord2Fwd h - 2300 + ord2Extra h + 9)) + dSubRem h := by rw [postGas, ord2Parent_gas]
  have gasWindow :
      300000 ≤ (ord2Gas h - (ord2Fwd h - 2300 + ord2Extra h + 9)) + dSubRem h ∧
      (ord2Gas h - (ord2Fwd h - 2300 + ord2Extra h + 9)) + dSubRem h < 2^256 := by
    unfold dSubRem ord2Fwd ord2Extra
    generalize hg : ord2Gas h = g at range ⊢
    generalize ha : ord2Acc h = acc at accLe ⊢
    generalize hc : Deposit.submissionGas (dSubSevm h) (dSubInit h) .empty 1 = cost at sgBound ⊢
    unfold except64th
    constructor <;> omega
  exact ⟨by rw [Evm.step_next atCall]; simp only [Ninst.step_exec, sp, XStep.toStep],
    enters,
    ex, sr.1, cPost, sr.2.1, sr.2.2.1.trans (ord2Parent_memory h), exitCode,
    afterBal,
    by change ((afterDSub h).state.getStor exitAddr).get _ = _; rw [exitStorAfter]; exact af.2.2.2.2.2.2.2.2.2.1,
    by change ((afterDSub h).state.getStor exitAddr).get _ = _; rw [exitStorAfter]; exact af.2.2.2.2.2.2.2.2.2.2,
    sr.2.2.2.2.1, sr.2.2.2.2.2.1, sr.2.2.2.2.2.2.1,
    by unfold afterDSub; rw [sr.2.2.2.2.2.2.2, pgl]; exact gasWindow.1,
    by unfold afterDSub; rw [sr.2.2.2.2.2.2.2, pgl]; exact gasWindow.2⟩


/-! ## Complete Exit child continuation from the same settled paid state

The following exact `paidState_eq` cut preserves the settled Deposit state while keeping its
concrete gas/refund/storage internals out of later kernel normalization. Both Exit child components
prove actual spawn, entry, raw execution, complete settlement and resume. The full ordinary/writer
execution, retained frames, transaction/body/header and nonempty kept history remain mandatory.
-/

-- The exact settled paid state, hidden behind an equality witness to keep its
-- concrete storage/refund/gas internals out of later kernel normalization.
private theorem paidState_exists (h : B256) : ∃ d : Devm, d = afterDSub h :=
  ⟨afterDSub h,rfl⟩
private noncomputable def paidState (h : B256) : Devm := Classical.choose (paidState_exists h)
private theorem paidState_eq (h : B256) : paidState h = afterDSub h :=
  Classical.choose_spec (paidState_exists h)

-- Call 3: Exit static fee read (PC 77 -> 105 -> 106)
private noncomputable def ord3Gas (h : B256) : Nat := (paidState h).gasLeft - 16
private noncomputable def ord3Acc (h : B256) : Nat := accessCost exitAddr (paidState h).accessedAddresses
private noncomputable def ord3Fwd (h : B256) : Nat := except64th (ord3Gas h - ord3Acc h)
private noncomputable def ord3State (h : B256) : Devm :=
  St (paidState h) [(ord3Gas h).toB256, exitAddr.toBytes.toB256, 0, 0, 0, 32] mem2 (ord3Gas h)
private noncomputable def ord3Bare (h : B256) : Devm :=
  addAccessedAddress (St (ord3State h) [] (ord3State h).memory (ord3State h).gasLeft) exitAddr
private noncomputable def ord3Parent (h : B256) : Devm :=
  callSpawnParent (ord3Bare h) (ord3Fwd h + ord3Acc h) 0 0 0 32
private noncomputable def eFeeMsg (h : B256) : Msg :=
  staticcallSpawnMsg (ordSevm h) (ord3Parent h) (ord3Fwd h) exitAddr exitAddr 0 0 Exit.code false
private noncomputable def eFeeSevm (h : B256) : Sevm := initSevm (eFeeMsg h)
private noncomputable def eFeeInit (h : B256) : Devm := initDevm (eFeeMsg h)
private noncomputable def eFeeRem (h : B256) : Nat := ord3Fwd h - UserPath.feeReadGas (eFeeSevm h) (eFeeInit h) .empty 1
private noncomputable def eFeePost (h : B256) : Devm := RequestFee.feeGetterPost (feeBase (eFeeSevm h) (eFeeInit h)) .empty 1 (eFeeRem h)
private noncomputable def afterEFee (h : B256) : Devm := callChildPost (ord3Parent h) (eFeePost h) 0 32
private def mem3 : Mem := (mem2.extends [⟨0, 0⟩, ⟨0, 32⟩]).write 0 (1 : B256).toBytes

private theorem ord_p3_core (s : Sevm) (d : Devm) (g : Nat) :
    let sta := { s with code := ordinaryCode, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 7 ⟨77, sta, d.setMach ⟨[1], mem2, g + 16, d.stateGas⟩⟩ =
      some ⟨105, sta, d.setMach ⟨[g.toB256, exitAddr.toBytes.toB256, 0, 0, 0, 32], mem2, g, d.stateGas⟩⟩ := by
  dsimp only; revert s d g; kernel_forall_rfl_and

private theorem ord_p3 (h : B256) :
    ConcreteRun.stepN 7 ⟨77, ordSevm h, paidState h⟩ = some ⟨105, ordSevm h, ord3State h⟩ := by
  have ds := dSub_step h
  rw [← paidState_eq] at ds
  have mach : (paidState h).setMach ⟨[1],mem2,((paidState h).gasLeft-16)+16,(paidState h).stateGas⟩ = paidState h := by
    rw [Nat.sub_add_cancel (by omega : 16 ≤ (paidState h).gasLeft)]
    exact (St.self ds.2.2.2.2.2.1 ds.2.2.2.2.2.2.1).symm
  have core := ord_p3_core (ordSevm h) (paidState h) (ord3Gas h)
  dsimp only at core; rw [ord_sta h, show ord3Gas h + 16 = ((paidState h).gasLeft - 16) + 16 from rfl, mach] at core
  exact core

private theorem mem2_size : mem2.size = 192 := by
  unfold mem2
  change memExtsSize mem2Pre.size [(0,184),(0,0)] = 192
  rw [mem2Pre_size]
  rfl

private theorem ord3_range (h : B256) : 299984 ≤ ord3Gas h ∧ ord3Gas h < 2^256 := by
  have ds := dSub_step h
  rw [← paidState_eq] at ds
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,lower,upper⟩ := ds
  unfold ord3Gas
  generalize hg : (paidState h).gasLeft = g at lower upper ⊢
  constructor <;> omega

private theorem eFeeInit_state (h : B256) : (eFeeInit h).state = (paidState h).state := by
  unfold eFeeInit eFeeMsg
  rw [scsm_state]
  unfold ord3Parent callSpawnParent ord3Bare
  rfl

private theorem ord3_precode (h : B256) :
    ((paidState h).setMach ⟨[],mem2,ord3Gas h,(paidState h).stateGas⟩).getCode exitAddr = Exit.code := by
  rw [getCode_eq_state, Devm.setMach_state]
  have ds := dSub_step h
  rw [← paidState_eq] at ds
  exact ds.2.2.2.2.2.2.2.1

private theorem ord3State_memory (h : B256) : (ord3State h).memory = mem2 := by
  unfold ord3State
  exact St.memory

private theorem ord3State_gas (h : B256) : (ord3State h).gasLeft = ord3Gas h := by
  unfold ord3State
  exact St.gasLeft

private theorem ord3Parent_memory (h : B256) :
    (ord3Parent h).memory = mem2.extends [(0,0),(0,32)] := by
  unfold ord3Parent
  rw [callSpawnParent_memory]
  unfold ord3Bare St
  rw [addAccessedAddress_setMach_memory,ord3State_memory]

private theorem ord3_stack (h : B256) :
    (ord3State h).stack = [(ord3Gas h).toB256,exitAddr.toBytes.toB256,0,0,0,32] := by
  simp only [ord3State,St.stack]

private theorem ord3_ext (h : B256) :
    ((ord3State h).setMach ⟨[],(ord3State h).memory,(ord3State h).gasLeft,(ord3State h).stateGas⟩).extCost
      [(0,0),(0,32)] = 0 := by
  simp only [Devm.extCost,Devm.memory_setMach,ord3State_memory,mem2_size]
  decide

private theorem ord3_popped_code (h : B256) :
    (St (ord3State h) [] (ord3State h).memory (ord3State h).gasLeft).getCode exitAddr = Exit.code := by
  rw [getCode_eq_state,St_state]
  unfold ord3State
  rw [St_state,← getCode_eq_state]
  have ds := dSub_step h
  rw [← paidState_eq] at ds
  exact ds.2.2.2.2.2.2.2.1

private theorem ord3_delegation (h : B256) :
    accessDelegation (addAccessedAddress
      ((ord3State h).setMach ⟨[],(ord3State h).memory,(ord3State h).gasLeft,(ord3State h).stateGas⟩)
      exitAddr) exitAddr = ⟨false,exitAddr,Exit.code,0,ord3Bare h⟩ := by
  simpa only [ord3Bare,St] using accessDelegation_of_code (ord3_popped_code h) Exit_not_delegated

private theorem ord3_access (h : B256) :
    accessCost exitAddr
      ((ord3State h).setMach ⟨[],(ord3State h).memory,(ord3State h).gasLeft,(ord3State h).stateGas⟩).accessedAddresses
      + 0 = ord3Acc h := by
  simp only [Devm.setMach_accessedAddresses]
  unfold ord3State St
  simp only [Devm.setMach_accessedAddresses,Nat.add_zero,ord3Acc]

private theorem ord3_bare_gas (h : B256) : (ord3Bare h).gasLeft = ord3Gas h := by
  unfold ord3Bare
  rw [addAccessedAddress_gasLeft]
  exact (St.gasLeft (b := ord3State h) (S := []) (M := (ord3State h).memory)
    (G := (ord3State h).gasLeft)).trans (ord3State_gas h)

private theorem ord3_split (h : B256) :
    calculateMsgCallGas 0 (ord3Gas h).toB256.toNat (ord3Bare h).gasLeft 0 (ord3Acc h) =
      (ord3Fwd h + ord3Acc h,ord3Fwd h) := by
  have range := ord3_range h
  have accLe : ord3Acc h ≤ 2600 := by unfold ord3Acc accessCost; split <;> decide
  rw [ord3_bare_gas]
  unfold ord3Fwd
  generalize hg : ord3Gas h = g at range ⊢
  generalize ha : ord3Acc h = acc at accLe ⊢
  rw [calculateMsgCallGas_zero (by omega),B256.toNat_toB256_of_lt range.2,Nat.sub_zero]
  change (min g (except64th (g-acc)) + acc,min g (except64th (g-acc))) = _
  rw [Nat.min_eq_right (by unfold except64th; omega)]

private theorem ord3_room (h : B256) : ord3Fwd h + ord3Acc h + 0 ≤ (ord3Bare h).gasLeft := by
  have range := ord3_range h
  have accLe : ord3Acc h ≤ 2600 := by unfold ord3Acc accessCost; split <;> decide
  rw [ord3_bare_gas,Nat.add_zero]
  unfold ord3Fwd
  generalize hg : ord3Gas h = g at range ⊢
  generalize ha : ord3Acc h = acc at accLe ⊢
  unfold except64th
  omega

private theorem eFee_xstep (h : B256) :
    Xinst.step (ordSevm h) (ord3State h) .staticcall =
      .spawn (Frame.ofCall (eFeeMsg h)) (.call (ord3Parent h) 0 32) := by
  have raw := Xinst.step_staticcall_spawn (sevm := ordSevm h) (devm := ord3State h)
    (gw := (ord3Gas h).toB256) (tw := exitAddr.toBytes.toB256)
    (iiw := 0) (isw := 0) (oiw := 0) (osw := 32) (s := []) (dp := false)
    (dadr := exitAddr) (code := Exit.code) (dgc := 0) (d1 := ord3Bare h)
    (ext := 0) (acc := ord3Acc h) (mcs := ord3Fwd h) (mcc := ord3Fwd h + ord3Acc h)
    (CoveredFork.prague.callEra false) (ord3_stack h)
    (by simpa only [B256.toNat_zero,show (32 : B256).toNat = 32 from rfl] using ord3_ext h)
    (by rw [SystemWordWriter.target_word]; exact ord3_delegation h)
    (by rw [SystemWordWriter.target_word]; exact ord3_access h)
    (ord3_split h) (ord3_room h) (by change (1023 : Nat) ≠ 0; decide)
  simpa only [eFeeMsg,ord3Parent,SystemWordWriter.target_word,B256.toNat_zero,
    show (32 : B256).toNat = 32 from rfl,Nat.add_zero] using raw

private theorem eFee_resume_facts (h : B256)
    (hstack : (ord3Parent h).stack = []) (hp : (((ord3Parent h)).error = none ∧ 0 ≤ ((ord3Parent h)).refundCounter)) (hb : (((eFeeInit h)).error = none ∧ 0 ≤ ((eFeeInit h)).refundCounter)) (hblog : (eFeeInit h).logs = [])
    (ht : (eFeeMsg h).benv.stat.rules.settle.touchedSweep = false) :
    let post := RequestFee.feeGetterPost (feeBase (eFeeSevm h) (eFeeInit h)) .empty 1 (eFeeRem h)
    let after := callChildPost (ord3Parent h) post 0 32
    ((post).error = none ∧ 0 ≤ (post).refundCounter) ∧
    Resume.run (.call (ord3Parent h) 0 32) ((Frame.ofCall (eFeeMsg h)).settle (.ok post)) = .ok after ∧
    after.stack = [1] ∧ after.memory = (ord3Parent h).memory.write 0 (1 : B256).toBytes ∧
    after.state = (eFeeInit h).state ∧ after.logs = (ord3Parent h).logs ∧ ((after).error = none ∧ 0 ≤ (after).refundCounter) ∧ after.gasLeft = (ord3Parent h).gasLeft + (eFeeRem h) := by
  generalize hMsg : eFeeMsg h = m at *
  generalize hPar : ord3Parent h = p at *
  generalize hSevm : eFeeSevm h = s at *
  generalize hInit : eFeeInit h = b at *
  generalize hRem : eFeeRem h = rem at *
  intro post after
  have fb : (((feeBase s b)).error = none ∧ 0 ≤ ((feeBase s b)).refundCounter) := by
    constructor
    · simp only [feeBase,StorageSteps.feeBase,coveredSteps,afterSload_error]; exact hb.1
    · simp only [feeBase,StorageSteps.feeBase,coveredSteps,afterSload_refundCounter]; exact hb.2
  have fbLogs : (feeBase s b).logs = [] := by
    simp only [feeBase, StorageSteps.feeBase, coveredSteps, afterSload_logs, hblog]
  have ff := RequestFee.feeGetterPost_facts (feeBase s b) .empty 1 rem Mem.wf_empty (by decide)
  have pErr : post.error = none := by change post.meta.error = none; rw [ff.2.2.1]; exact fb.1
  have pRef : 0 ≤ post.refundCounter := by change 0 ≤ post.meta.refundCounter; rw [ff.2.2.1]; exact fb.2
  have pLogs : post.logs = [] := by change post.meta.logs = []; rw [ff.2.2.1]; exact fbLogs
  have cPost : ((post).error = none ∧ 0 ≤ (post).refundCounter) := ⟨pErr, pRef⟩
  have settleOk := frame_settle_ok m post pErr ht
  have resOk : Resume.run (.call p 0 32) ((Frame.ofCall m).settle (.ok post)) = .ok after := by
    rw [settleOk, Resume.run_call_ok (by rw [pErr]; rfl) (by rw [hstack]; decide)]; rfl
  have outEq : post.output = (1 : B256).toBytes := ff.1
  have ne : ((1 : B256).toBytes.take 32).isEmpty = false := by decide
  have takeEq : (1 : B256).toBytes.take 32 = (1 : B256).toBytes :=
    List.take_of_length_le (by rw [B256.length_toBytes])
  have r0 := hp.2
  refine ⟨cPost, resOk, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩ <;>
    (unfold after callChildPost incorporateChildOnSuccess Devm.memWrite liftMachPure Mach.memWrite
     simp only [outEq, takeEq, Devm.stack, Devm.memory, Devm.state,
       Devm.logs, Devm.error, Devm.refundCounter, Devm.gasLeft, Devm.setMach, Devm.setMeta, Devm.setWorld])
  · change 1 :: p.stack = [1]; rw [hstack]
  · change post.state = b.state; change (RequestFee.feeGetterPost (feeBase s b) .empty 1 rem).state = b.state; change (RequestFee.feeGetterPost (feeBase s b) .empty 1 rem).world.state = b.state; rw [ff.2.1]; change (feeBase s b).state = b.state; simp only [feeBase, StorageSteps.feeBase, coveredSteps, RequestFee.afterSload_state]
  · change p.logs ++ post.logs = p.logs; rw [pLogs, List.append_nil]
  · exact hp.1
  · change 0 ≤ p.refundCounter + post.refundCounter; omega
  · change p.gasLeft + post.gasLeft = p.gasLeft + rem; change p.gasLeft + (RequestFee.feeGetterPost (feeBase s b) .empty 1 rem).gasLeft = _; rw [ff.2.2.2.2.2.1]


private theorem eFeeGas_bound (h : B256) :
    UserPath.feeReadGas (eFeeSevm h) (eFeeInit h) .empty 1 ≤ 6000 := by
  generalize hs : eFeeSevm h = s
  generalize hb : eFeeInit h = b
  have a := sloadCost_le s b 0
  have z := sloadCost_le s (afterSload s b 0) 1
  unfold UserPath.feeReadGas UserPath.feeReadGasOn StorageSteps.feePathGas
  rw [RequestFee.feeGetterGas_empty, RequestFee.feeLoopGas_eq]
  change 13 + 30 + (133 + (25 + 87 * 1) + sloadCost s b 0 + sloadCost s (afterSload s b 0) 1) + 21 ≤ 6000
  change sloadCost s b 0 ≤ 2100 at a
  change sloadCost s (afterSload s b 0) 1 ≤ 2100 at z
  omega

private theorem eFee_step (h : B256) :
    Evm.step ⟨105, ordSevm h, ord3State h⟩ =
      .spawn (Frame.ofCall (eFeeMsg h)) (.call (ord3Parent h) 0 32) 106 ∧
    (Frame.ofCall (eFeeMsg h)).enter = .run ⟨0, eFeeSevm h, eFeeInit h⟩ ∧
    Nonempty (Exec 0 (eFeeSevm h) (eFeeInit h) (.ok (eFeePost h))) ∧
    Resume.run (.call (ord3Parent h) 0 32) ((Frame.ofCall (eFeeMsg h)).settle (.ok (eFeePost h))) = .ok (afterEFee h) ∧
    (((eFeePost h)).error = none ∧ 0 ≤ ((eFeePost h)).refundCounter) ∧ (afterEFee h).stack = [1] ∧ (afterEFee h).memory = mem3 ∧
    (afterEFee h).state = (paidState h).state ∧ (afterEFee h).output = [] ∧
    (∀ l ∈ (afterEFee h).logs, l.address ≠ depositContractAddress) ∧
    (((afterEFee h)).error = none ∧ 0 ≤ ((afterEFee h)).refundCounter) ∧ 250000 ≤ (afterEFee h).gasLeft ∧ (afterEFee h).gasLeft < 2 ^ 256 := by
  have ds := dSub_step h
  rw [← paidState_eq] at ds
  have range := ord3_range h
  have accLe : ord3Acc h ≤ 2600 := by unfold ord3Acc accessCost; split <;> decide
  have fwdGe : 280000 ≤ ord3Fwd h := by unfold ord3Fwd except64th; omega
  have fgLe := eFeeGas_bound h
  have sp := eFee_xstep h
  have s0 : (eFeeInit h).getStorVal exitAddr 0 = 0 := by
    change ((eFeeInit h).state.getStor exitAddr).get 0 = 0
    rw [eFeeInit_state]; exact ds.2.2.2.2.2.2.2.2.2.1
  have s1 : (eFeeInit h).getStorVal exitAddr 1 = 0 := by
    change ((eFeeInit h).state.getStor exitAddr).get 1 = 0
    rw [eFeeInit_state]; exact ds.2.2.2.2.2.2.2.2.2.2.1
  have initSt : eFeeInit h = St (eFeeInit h) [] .empty (eFeeRem h + UserPath.feeReadGas (eFeeSevm h) (eFeeInit h) .empty 1) := by
    have igl : (eFeeInit h).gasLeft = ord3Fwd h := rfl
    exact (pre_eq_St rfl rfl (by unfold eFeeRem; omega)).symm
  have fee1 : ((17 : B256) / (17 : B256)) = 1 := by decide
  have ex : Nonempty (Exec 0 (eFeeSevm h) (eFeeInit h) (.ok (eFeePost h))) := by
    rw [initSt]; unfold eFeePost; rw [← fee1]
    exact Exit.exec_fee_read_exact (sevm := eFeeSevm h) (b := eFeeInit h) (M := .empty) (G := eFeeRem h)
      (iterations := 1) (finalOutput := 17) rfl CoveredFork.prague (by decide)
      (by change ordinaryAddr ≠ systemAddress; decide) rfl rfl
      (by change (eFeeInit h).getStorVal exitAddr 0 ≠ B256.max; rw [s0]; decide)
      (by rw [show storedExcess 2 (eFeeSevm h) (eFeeInit h) = 0 from by
            unfold storedExcess; change targetExcess 2 ((eFeeInit h).getStorVal exitAddr 0) ((eFeeInit h).getStorVal exitAddr 1) = 0
            rw [s0, s1]; decide]; exact quote_zero_excess)
  have pClean : (((ord3Parent h)).error = none ∧ 0 ≤ ((ord3Parent h)).refundCounter) := ⟨ds.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1, ds.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2⟩
  have rf := eFee_resume_facts h rfl pClean ⟨rfl, by change (0 : Int) ≤ 0; omega⟩ rfl rfl
  have afterLogs : (afterEFee h).logs = (ord3Parent h).logs := by
    simpa only [afterEFee,eFeePost] using rf.2.2.2.2.2.1
  have afterGas : (afterEFee h).gasLeft = (ord3Parent h).gasLeft + eFeeRem h := by
    simpa only [afterEFee,eFeePost] using rf.2.2.2.2.2.2.2
  have atSC : Ninst.At (ordSevm h).code 105 (.exec .staticcall) := by
    change Ninst.At ordinaryCode 105 (.exec .staticcall); unfold Ninst.At; kernel_rfl
  have pgl : (ord3Parent h).gasLeft = ord3Gas h - (ord3Fwd h + ord3Acc h) := by
    unfold ord3Parent
    rw [callSpawnParent_gasLeft]
    rw [ord3_bare_gas]
  have outEq : (afterEFee h).output = [] := by
    unfold afterEFee callChildPost incorporateChildOnSuccess Devm.memWrite liftMachPure Mach.memWrite
    simp only [Devm.output, Devm.setMach, Devm.setMeta, Devm.setWorld]
    exact ds.2.2.2.2.2.2.2.2.2.2.2.1
  have afterMemory : (afterEFee h).memory = mem3 := by
    have eq := rf.2.2.2.1.trans
      (congrArg (fun m : Mem => m.write 0 (1 : B256).toBytes) (ord3Parent_memory h))
    simpa only [afterEFee,eFeePost,mem3] using eq
  have gasWindow :
      250000 ≤ (ord3Gas h - (ord3Fwd h + ord3Acc h)) + eFeeRem h ∧
      (ord3Gas h - (ord3Fwd h + ord3Acc h)) + eFeeRem h < 2^256 := by
    unfold eFeeRem ord3Fwd
    generalize hg : ord3Gas h = g at range ⊢
    generalize ha : ord3Acc h = acc at accLe ⊢
    generalize hc : UserPath.feeReadGas (eFeeSevm h) (eFeeInit h) .empty 1 = cost at fgLe ⊢
    unfold except64th
    constructor <;> omega
  exact ⟨by rw [Evm.step_next atSC]; simp only [Ninst.step_exec, sp, XStep.toStep],
    Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl
      (by change pragueRules.isPrecomp exitAddr = false; decide),
    ex, rf.2.1, rf.1, rf.2.2.1, afterMemory, rf.2.2.2.2.1.trans (eFeeInit_state h), outEq,
    by rw [afterLogs]; exact ds.2.2.2.2.2.2.2.2.2.2.2.2.1, rf.2.2.2.2.2.2.1,
    by rw [afterGas, pgl]; exact gasWindow.1,
    by rw [afterGas, pgl]; exact gasWindow.2⟩


-- Call 4: Exit 48-byte paid submission (PC 106 -> 136 -> 137 -> 138)
private noncomputable def ord4Gas (h : B256) : Nat := (afterEFee h).gasLeft - 21
private noncomputable def ord4Acc (h : B256) : Nat := accessCost exitAddr (afterEFee h).accessedAddresses
private noncomputable def ord4Extra (h : B256) : Nat := ord4Acc h + 9000
private noncomputable def ord4Fwd (h : B256) : Nat := except64th (ord4Gas h - ord4Extra h) + 2300
private noncomputable def ord4State (h : B256) : Devm :=
  (afterEFee h).setMach ⟨[(ord4Gas h).toB256, exitAddr.toBytes.toB256, 1, 0, (48 : B256), 0, 0], mem3, ord4Gas h, (afterEFee h).stateGas⟩
private noncomputable def ord4Bare (h : B256) : Devm :=
  addAccessedAddress ((afterEFee h).setMach ⟨[], mem3, ord4Gas h, (afterEFee h).stateGas⟩) exitAddr
private noncomputable def ord4Parent (h : B256) : Devm :=
  callSpawnParent (ord4Bare h) (ord4Fwd h - 2300 + ord4Extra h) 0 48 0 0
private noncomputable def eSubMsg (h : B256) : Msg :=
  valueCallSpawnMsg (ordSevm h) (ord4Parent h) (ord4Fwd h) 1 exitAddr exitAddr 0 48 Exit.code false
private noncomputable def eSubNextBenv (h : B256) : Benv :=
  match (eSubMsg h).benvAfterTransfer with | .ok b => b | .error _ => (eSubMsg h).benv
private noncomputable def eSubSevm (h : B256) : Sevm := initSevm ((eSubMsg h).withBenv (eSubNextBenv h))
private noncomputable def eSubInit (h : B256) : Devm := initDevm ((eSubMsg h).withBenv (eSubNextBenv h))
private noncomputable def eSubRem (h : B256) : Nat := ord4Fwd h - Exit.submissionGas (eSubSevm h) (eSubInit h) .empty 1
private noncomputable def eSubPost (h : B256) : Devm := Exit.submissionPost (eSubSevm h) (feeBase (eSubSevm h) (eSubInit h)) .empty (eSubRem h)
private noncomputable def afterESub (h : B256) : Devm := callChildPost (ord4Parent h) (eSubPost h) 0 0
private noncomputable def ordEnd (h : B256) : Devm :=
  (afterESub h).setMach ⟨[], (afterESub h).memory, (afterESub h).gasLeft - 2, (afterESub h).stateGas⟩

private theorem ord_p4_core (s : Sevm) (d : Devm) (g : Nat) :
    let sta := { s with code := ordinaryCode, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 9 ⟨106, sta, d.setMach ⟨[1], mem3, g + 21, d.stateGas⟩⟩ =
      some ⟨136, sta, d.setMach ⟨[g.toB256, exitAddr.toBytes.toB256, 1, 0, (48 : B256), 0, 0], mem3, g, d.stateGas⟩⟩ := by
  dsimp only; revert s d g; kernel_forall_rfl_and

private theorem ord_p4 (h : B256) :
    ConcreteRun.stepN 9 ⟨106, ordSevm h, afterEFee h⟩ = some ⟨136, ordSevm h, ord4State h⟩ := by
  have ef := eFee_step h
  have mach : (afterEFee h).setMach ⟨[1],mem3,((afterEFee h).gasLeft-21)+21,(afterEFee h).stateGas⟩ = afterEFee h := by
    rw [Nat.sub_add_cancel (by omega : 21 ≤ (afterEFee h).gasLeft)]
    exact (St.self ef.2.2.2.2.2.1 ef.2.2.2.2.2.2.1).symm
  have core := ord_p4_core (ordSevm h) (afterEFee h) (ord4Gas h)
  dsimp only at core; rw [ord_sta h, show ord4Gas h + 21 = ((afterEFee h).gasLeft - 21) + 21 from rfl, mach] at core
  exact core

private theorem mem3_size : mem3.size = 192 := by
  have oldSize : (mem2.extends [(0,0),(0,32)]).size = 192 := by
    change memExtsSize mem2.size [(0,0),(0,32)] = 192
    rw [mem2_size]
    rfl
  unfold mem3
  rw [Mem.size_write_of_length (B256.length_toBytes _) (by decide),oldSize]
  rfl

private theorem afterEFee_code_bal (h : B256) :
    (afterEFee h).getCode exitAddr = Exit.code ∧
    (afterEFee h).getBal ordinaryAddr = (2^100 : Nat).toB256 - dSubVal := by
  have ef := eFee_step h
  have ds := dSub_step h
  rw [← paidState_eq] at ds
  refine ⟨?_,?_⟩
  · rw [getCode_eq_state, ef.2.2.2.2.2.2.2.1]; exact ds.2.2.2.2.2.2.2.1
  · change ((afterEFee h).state.get ordinaryAddr).bal = _
    rw [ef.2.2.2.2.2.2.2.1]; exact ds.2.2.2.2.2.2.2.2.1

private theorem ord4_precode (h : B256) :
    ((afterEFee h).setMach ⟨[],mem3,ord4Gas h,(afterEFee h).stateGas⟩).getCode exitAddr = Exit.code := by
  rw [getCode_eq_state, Devm.setMach_state]
  exact (afterEFee_code_bal h).1

private theorem eSubMsg_state (h : B256) : (eSubMsg h).benv.state = (afterEFee h).state := by
  unfold eSubMsg
  generalize hp : ord4Parent h = p
  change (initDevm (valueCallSpawnMsg (ordSevm h) p (ord4Fwd h) (1 : B256)
    exitAddr exitAddr 0 48 Exit.code false)).state = (afterEFee h).state
  rw [vcsm_state, ← hp]
  unfold ord4Parent callSpawnParent ord4Bare
  rfl

private theorem ord4_range (h : B256) : 249979 ≤ ord4Gas h ∧ ord4Gas h < 2^256 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,lower,upper⟩ := eFee_step h
  unfold ord4Gas
  generalize hg : (afterEFee h).gasLeft = g at lower upper ⊢
  constructor <;> omega

private theorem eSub_xstep (h : B256) :
    Xinst.step (ordSevm h) (ord4State h) .call =
      .spawn (Frame.ofCall (eSubMsg h)) (.call (ord4Parent h) 0 0) := by
  have range := ord4_range h
  have cb := afterEFee_code_bal h
  have accLe : ord4Acc h ≤ 2600 := by unfold ord4Acc accessCost; split <;> decide
  have splitGas : calculateMsgCallGas (1 : B256).toNat (ord4Gas h).toB256.toNat (ord4Gas h) 0
      (ord4Acc h + 0 + gasCallValue) = (ord4Fwd h - 2300 + ord4Extra h, ord4Fwd h) := by
    unfold ord4Fwd ord4Extra
    generalize hg : ord4Gas h = g at range ⊢
    generalize ha : ord4Acc h = acc at accLe ⊢
    unfold calculateMsgCallGas
    rw [ite_eq_right (by decide : (1 : B256).toNat ≠ 0),
      ite_eq_right (by change ¬ g < acc + 0 + 9000 + 0; omega),
      B256.toNat_toB256_of_lt range.2]
    have le : except64th (g - 0 - (acc + 9000)) ≤ g := by unfold except64th; omega
    change (min g (except64th (g - 0 - (acc + 9000))) + (acc + 9000),
      min g (except64th (g - 0 - (acc + 9000))) + 2300) = _
    rw [Nat.min_eq_right le]
    simp only [Nat.add_sub_cancel,Nat.sub_zero]
  have cBare : (ord4Bare h).getCode exitAddr = Exit.code := by
    unfold ord4Bare; rw [addAccessedAddress_getCode]; exact ord4_precode h
  have notEmpty : ¬ ((ord4Bare h).getAcct exitAddr).Empty := by
    intro bad
    have sz : ((ord4Bare h).getCode exitAddr).size = 0 := bad.1
    rw [cBare] at sz
    exact (by decide +kernel : Exit.code.size ≠ 0) sz
  have affordable : ¬ ((ord4Bare h).getAcct (ordSevm h).currentTarget).bal < (1 : B256) := by
    change ¬ ((ord4Bare h).state.get ordinaryAddr).bal < (1 : B256)
    unfold ord4Bare
    rw [addAccessedAddress_state, Devm.setMach_state]
    change ¬ (afterEFee h).getBal ordinaryAddr < (1 : B256)
    rw [cb.2]; decide
  have raw := Xinst.step_call_nonzero_spawn (sevm := ordSevm h) (devm := ord4State h)
    (gw := (ord4Gas h).toB256) (cw := exitAddr.toBytes.toB256) (vw := (1 : B256))
    (iiw := 0) (isw := 48) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := exitAddr) (code := Exit.code) (dgc := 0) (d1 := ord4Bare h)
    (ext := 0) (acc := ord4Acc h) (create := 0) (mcs := ord4Fwd h)
    (mcc := ord4Fwd h - 2300 + ord4Extra h)
    (CoveredFork.prague.callEra false) rfl (by decide)
    (by simp only [ord4State, Devm.setMach_setMach, Devm.extCost, Devm.memory_setMach, mem3_size]; decide)
    (by rw [SystemWordWriter.target_word]
        have del := accessDelegation_of_code (ord4_precode h) Exit_not_delegated
        simpa only [ord4State, ord4Bare, Devm.setMach_setMach, Devm.memory_setMach,
          Devm.gasLeft_setMach, Devm.stateGas_setMach] using del)
    (by rw [SystemWordWriter.target_word]; simp only [ord4State, Devm.setMach_accessedAddresses, ord4Acc, Nat.add_zero])
    (by rw [SystemWordWriter.target_word, ite_eq_left notEmpty])
    (by simpa only [ord4Bare, addAccessedAddress_gasLeft, Devm.setMach_gasLeft] using splitGas)
    (by simp only [ord4Bare, addAccessedAddress_gasLeft, Devm.setMach_gasLeft]
        unfold ord4Fwd ord4Extra
        generalize hg : ord4Gas h = g at range ⊢
        generalize ha : ord4Acc h = acc at accLe ⊢
        unfold except64th; omega)
    rfl affordable (by change (1023 : Nat) ≠ 0; decide)
  simpa only [eSubMsg, ord4Parent, SystemWordWriter.target_word, B256.toNat_zero,
    show (48 : B256).toNat = 48 from rfl,Nat.add_zero] using raw

private theorem eSubInit_state (h : B256) : (eSubInit h).state = (eSubNextBenv h).state := by
  unfold eSubInit
  generalize hm : eSubMsg h = m
  generalize hb : eSubNextBenv h = nb
  rfl

private theorem eSubSevm_data (h : B256) : (eSubSevm h).data = (mem3.read 0 48).1 := by
  unfold eSubSevm
  generalize hm : eSubMsg h = m
  generalize hb : eSubNextBenv h = nb
  change m.data = _
  rw [← hm]
  change (ord4Parent h).memory.data.sliceD 0 48 0 = _
  unfold ord4Parent
  rw [callSpawnParent_memory_data]
  unfold ord4Bare
  rw [addAccessedAddress_setMach_memory]
  simp only [mem_read_fst]

private theorem eSub_transfer (h : B256) :
    (eSubMsg h).benvAfterTransfer = .ok (eSubNextBenv h) ∧
    (∀ a, (eSubNextBenv h).state.getCode a = (afterEFee h).state.getCode a) ∧
    (∀ a, ((afterEFee h).state.getCode a).size ≠ 0 →
      (eSubNextBenv h).state.getStor a = (afterEFee h).state.getStor a) ∧
    ((eSubNextBenv h).state.get ordinaryAddr).bal = (eSubMsg h).benv.state.bal ordinaryAddr - (1 : B256) ∧
    CoveredFork (eSubSevm h).benvStat.fork ∧
    (eSubSevm h).benvStat.origState = state true (some h) ∧ (eSubInit h).logs = [] := by
  have balOrd : (eSubMsg h).benv.state.bal ordinaryAddr = ((2 ^ 100 : Nat).toB256 - dSubVal) := by
    rw [eSubMsg_state]; exact (afterEFee_code_bal h).2
  have affordableMsg : ¬ (eSubMsg h).benv.state.bal (eSubMsg h).caller < (eSubMsg h).value := by
    change ¬ (eSubMsg h).benv.state.bal ordinaryAddr < (1 : B256)
    rw [balOrd]; decide
  obtain ⟨mid, sub, bt⟩ := Msg.benvAfterTransfer_of_affordable (eSubMsg h) rfl affordableMsg
    (by change (1 : B256) ≠ 0; decide)
  have htr : (eSubMsg h).benvAfterTransfer = .ok (eSubNextBenv h) := by
    unfold eSubNextBenv; rw [bt]
  have trCode (a : Adr) : (eSubNextBenv h).state.getCode a = (afterEFee h).state.getCode a := by
    rw [benvAfterTransfer_ok_getCode htr a, eSubMsg_state]
  have trStor (a : Adr) (hc : ((afterEFee h).state.getCode a).size ≠ 0) :
      (eSubNextBenv h).state.getStor a = (afterEFee h).state.getStor a := by
    have codeLive : ((eSubMsg h).benv.state.get a).code.size ≠ 0 := by
      change ((eSubMsg h).benv.state.getCode a).size ≠ 0
      rw [eSubMsg_state]; exact hc
    rw [benvAfterTransfer_ok_getStor htr a (Or.inr (Or.inr codeLive)), eSubMsg_state]
  have trBal : ((eSubNextBenv h).state.get ordinaryAddr).bal =
      (eSubMsg h).benv.state.bal ordinaryAddr - (1 : B256) := by
    have nbState : (eSubNextBenv h).state = mid.addBal exitAddr (1 : B256) := by
      unfold eSubNextBenv; rw [bt]; rfl
    have midEq : mid = (eSubMsg h).benv.state.setBal ordinaryAddr
        ((eSubMsg h).benv.state.bal ordinaryAddr - (1 : B256)) := by
      change (eSubMsg h).benv.state.subBal ordinaryAddr (1 : B256) = some mid at sub
      have aff : ¬ (eSubMsg h).benv.state.bal ordinaryAddr < (1 : B256) := by rw [balOrd]; decide
      simp only [State.subBal, aff, ite_false, Option.some.injEq] at sub
      exact sub.symm
    rw [nbState, addBal_get_ne _ (by decide : exitAddr ≠ ordinaryAddr), midEq]
    exact setBal_bal_self _ _ _
  have calleeFork : CoveredFork (eSubSevm h).benvStat.fork := by
    unfold eSubSevm
    rw [initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat htr]
    exact CoveredFork.prague
  have calleeOrig : (eSubSevm h).benvStat.origState = state true (some h) := by
    unfold eSubSevm
    rw [initSevm_benvStat, Msg.withBenv_benvStat, benvAfterTransfer_stat htr]
    rfl
  have initLogs : (eSubInit h).logs = [] := by
    unfold eSubInit
    apply Lift.initDevm_logs
    change (eSubNextBenv h).stat.rules.stateGas = none
    rw [benvAfterTransfer_stat htr]
    exact CoveredFork.prague.rules_stateGas_none
  exact ⟨htr,trCode,trStor,trBal,calleeFork,calleeOrig,initLogs⟩


open Exit in
private theorem eSubGas_bound (h : B256) :
    submissionGas (eSubSevm h) (eSubInit h) .empty 1 ≤ 150000 := by
  generalize hs : eSubSevm h = s
  generalize hb : eSubInit h = b
  have W : ∀ d k v, (coveredSteps s).writeCharge d k v ≤ 22100 :=
    fun d k v => (sstoreCost_le_value s d k v).trans
      (Nat.add_le_add_left (sstoreValueCost_le _ _ _) _)
  have L := sloadCost_le s
  have R : ∀ d K, Steps.recordWritesGas (coveredSteps s) d K ≤
      3 * 22100 :=
    fun d K => (Nat.add_le_add (Nat.add_le_add (W _ _ _) (W _ _ _)) (W _ _ _)).trans (by omega)
  have CL := memory_gas s
  unfold submissionGas submissionGasOn Steps.bodyGas StorageSteps.feePathGas
  rw [RequestFee.feeLoopGas_eq, feePathFixedGas, RequestSystem.dispatchGas]
  have a1 := L b 0
  have a2 := L ((coveredSteps s).afterRead b 0) 1
  have a3 := L ((coveredSteps s).feeBase b) 1
  have a4 := L ((coveredSteps s).countStore ((coveredSteps s).feeBase b)) 3
  have w1 := W ((coveredSteps s).afterRead ((coveredSteps s).feeBase b) 1)
    1 (1 + countWord s ((coveredSteps s).feeBase b))
  have w2 := W (Steps.logged (coveredSteps s) ((coveredSteps s).feeBase b) .empty) 3
    (1 + (coveredSteps s).tailWord ((coveredSteps s).feeBase b))
  have w3 := R ((coveredSteps s).tailRead ((coveredSteps s).feeBase b))
    (submissionKey ((coveredSteps s).tailWord ((coveredSteps s).feeBase b)))
  simp only [gasColdSload] at a1 a2 a3 a4
  omega



private theorem eSubPost_clean (h : B256) : (((eSubPost h)).error = none ∧ 0 ≤ ((eSubPost h)).refundCounter) := by
  have hos : (eSubSevm h).benvStat.origState = state true (some h) := (eSub_transfer h).2.2.2.2.2.1
  have hd : (((eSubInit h)).error = none ∧ 0 ≤ ((eSubInit h)).refundCounter) := ⟨rfl, by change (0 : Int) ≤ 0; omega⟩
  have clean_st {d : Devm} {st : List B256} {m : Mem} {g : Nat} (hd : ((d).error = none ∧ 0 ≤ (d).refundCounter)) :
      (((St d st m g)).error = none ∧ 0 ≤ ((St d st m g)).refundCounter) := ⟨hd.1, hd.2⟩

  have clean_addLog {d : Devm} {l : Log} (hd : ((d).error = none ∧ 0 ≤ (d).refundCounter)) :
      (((d.addLog l)).error = none ∧ 0 ≤ ((d.addLog l)).refundCounter) := ⟨hd.1, hd.2⟩

  have clean_sload {d : Devm} {k : B256} (hd : ((d).error = none ∧ 0 ≤ (d).refundCounter)) :
      (((afterSload (eSubSevm h) d k)).error = none ∧ 0 ≤ ((afterSload (eSubSevm h) d k)).refundCounter) := by
    unfold afterSload; split <;> exact ⟨hd.1, hd.2⟩

  have clean_sstore {d : Devm} {k v : B256}
      (hd : ((d).error = none ∧ 0 ≤ (d).refundCounter)) :
      (((afterSstore (eSubSevm h) d k v)).error = none ∧ 0 ≤ ((afterSstore (eSubSevm h) d k v)).refundCounter) := by
    have origZero : d.getOrigStorVal (eSubSevm h) (eSubSevm h).currentTarget k = 0 := origStorVal_zero d hos (eSubSevm h).currentTarget k
    exact ⟨(afterSstore_error (eSubSevm h) d k v).trans hd.1,
      hd.2.trans (afterSstore_refundCounter_ge_of_safe (eSubSevm h) d k v (Or.inr (Or.inl origZero)))⟩

  unfold eSubPost
  unfold Exit.submissionPost Exit.Steps.submissionPost Exit.Steps.submissionBase
    Exit.Steps.logged Exit.Steps.recordsWritten Exit.Steps.recordStore
    StorageSteps.tailRead StorageSteps.countStore feeBase StorageSteps.feeBase coveredSteps
  dsimp only
  apply clean_st
  apply clean_sstore
  apply clean_addLog
  apply clean_sstore
  apply clean_sstore
  apply clean_sstore
  apply clean_sload
  apply clean_sstore
  apply clean_sload
  apply clean_sload
  apply clean_sload
  exact hd


private theorem eSub_resume_facts (h : B256)
    (hstack : (ord4Parent h).stack = []) (hpout : (ord4Parent h).output = []) (hp : (((ord4Parent h)).error = none ∧ 0 ≤ ((ord4Parent h)).refundCounter)) (hc : (((eSubPost h)).error = none ∧ 0 ≤ ((eSubPost h)).refundCounter))
    (hout : (eSubPost h).output = []) (hlogs : (eSubPost h).logs = [(⟨(eSubSevm h).currentTarget,[],(eSubSevm h).caller.toBytes ++ (eSubSevm h).data⟩ : Log)]) (haddr : (⟨(eSubSevm h).currentTarget,[],(eSubSevm h).caller.toBytes ++ (eSubSevm h).data⟩ : Log).address ≠ depositContractAddress)
    (hpAvoid : ∀ l ∈ (ord4Parent h).logs, l.address ≠ depositContractAddress)
    (ht : (eSubMsg h).benv.stat.rules.settle.touchedSweep = false) :
    let after := callChildPost (ord4Parent h) (eSubPost h) 0 0
    Resume.run (.call (ord4Parent h) 0 0) ((Frame.ofCall (eSubMsg h)).settle (.ok (eSubPost h))) = .ok after ∧
    after.stack = [1] ∧ after.memory = (ord4Parent h).memory ∧ after.state = (eSubPost h).state ∧ after.output = [] ∧
    (∀ l ∈ after.logs, l.address ≠ depositContractAddress) ∧ ((after).error = none ∧ 0 ≤ (after).refundCounter) ∧
    after.gasLeft = (ord4Parent h).gasLeft + (eSubPost h).gasLeft := by
  intro after
  have settleOk := frame_settle_ok (eSubMsg h) (eSubPost h) hc.1 ht
  have resOk : Resume.run (.call (ord4Parent h) 0 0) ((Frame.ofCall (eSubMsg h)).settle (.ok (eSubPost h))) = .ok after := by
    rw [settleOk, Resume.run_call_ok (by rw [hc.1]; rfl) (by rw [hstack]; decide)]; rfl
  have cf := callChildPost_facts (ord4Parent h) (eSubPost h) 0 0 hout
  have r0 := hp.2; have r1 := hc.2
  refine ⟨resOk, by rw [cf.1, hstack], cf.2.1, cf.2.2.2.1, cf.2.2.2.2.2.2.2.2.1.trans hpout, ?_,
    ⟨cf.2.2.2.2.2.2.2.1.trans hp.1, by rw [cf.2.2.2.2.2.2.1]; omega⟩, cf.2.2.1⟩
  intro l hl; rw [cf.2.2.2.2.2.1, hlogs, List.mem_append] at hl
  rcases hl with hl | hl
  · exact hpAvoid l hl
  · obtain rfl := List.mem_singleton.mp hl; exact haddr

private theorem eSub_step (h : B256) :
    Evm.step ⟨136,ordSevm h,ord4State h⟩ =
      .spawn (Frame.ofCall (eSubMsg h)) (.call (ord4Parent h) 0 0) 137 ∧
    (Frame.ofCall (eSubMsg h)).enter = .run ⟨0,eSubSevm h,eSubInit h⟩ ∧
    Nonempty (Exec 0 (eSubSevm h) (eSubInit h) (.ok (eSubPost h))) ∧
    Resume.run (.call (ord4Parent h) 0 0) ((Frame.ofCall (eSubMsg h)).settle (.ok (eSubPost h))) = .ok (afterESub h) ∧
    ((eSubPost h).error = none ∧ 0 ≤ (eSubPost h).refundCounter) ∧
    (afterESub h).stack = [1] ∧ (afterESub h).output = [] ∧
    (∀ l ∈ (afterESub h).logs,l.address ≠ depositContractAddress) ∧
    ((afterESub h).error = none ∧ 0 ≤ (afterESub h).refundCounter) ∧
    50000 ≤ (afterESub h).gasLeft ∧ (afterESub h).gasLeft < 2^256 := by
  have ef := eFee_step h
  have ds := dSub_step h
  rw [← paidState_eq] at ds
  have range := ord4_range h
  have accLe : ord4Acc h ≤ 2600 := by unfold ord4Acc accessCost; split <;> decide
  have fwdGe : 220000 ≤ ord4Fwd h := by unfold ord4Fwd ord4Extra except64th; omega
  obtain ⟨htr,trCode,trStor,trBal,calleeFork,calleeOrig,initLogs⟩ := eSub_transfer h
  have codeExit := (afterEFee_code_bal h).1
  have exitStor : (eSubInit h).state.getStor exitAddr = (paidState h).state.getStor exitAddr := by
    rw [eSubInit_state,trStor exitAddr (by rw [← getCode_eq_state,codeExit]; decide +kernel)]
    exact congrArg (fun w => w.getStor exitAddr) ef.2.2.2.2.2.2.2.1
  have s0 : (eSubInit h).getStorVal exitAddr 0 = 0 := by
    change ((eSubInit h).state.getStor exitAddr).get 0 = 0
    rw [exitStor]; exact ds.2.2.2.2.2.2.2.2.2.1
  have s1 : (eSubInit h).getStorVal exitAddr 1 = 0 := by
    change ((eSubInit h).state.getStor exitAddr).get 1 = 0
    rw [exitStor]; exact ds.2.2.2.2.2.2.2.2.2.2.1
  have sgBound := eSubGas_bound h
  have hlen : (eSubSevm h).data.length = 48 := by
    rw [eSubSevm_data,mem_read_fst,Array.sliceD_eq_map,List.length_map,List.length_range]
  have initSt : eSubInit h = St (eSubInit h) [] .empty
      (eSubRem h + Exit.submissionGas (eSubSevm h) (eSubInit h) .empty 1) := by
    have igl : (eSubInit h).gasLeft = ord4Fwd h := rfl
    exact (pre_eq_St rfl rfl (by unfold eSubRem; omega)).symm
  have ex : Nonempty (Exec 0 (eSubSevm h) (eSubInit h) (.ok (eSubPost h))) := by
    rw [initSt]
    unfold eSubPost
    exact Exit.exec_submission_witness (sevm := eSubSevm h) (b := eSubInit h) (M := .empty) (G := eSubRem h)
      rfl calleeFork (by change ordinaryAddr ≠ systemAddress; decide) hlen
      (by change 1 ≤ (1 : B256).toNat; decide) rfl (by unfold gCallStipend eSubRem; omega) s0 s1
  have cPost := eSubPost_clean h
  have eff : Exit.SubmissionEffects (eSubSevm h) (eSubInit h) (eSubPost h) := by
    simpa only [eSubPost,Exit.submissionPost,feeBase] using
      (Exit.submissionPost_effects (sevm := eSubSevm h) (b := eSubInit h) (M := .empty)
        (coveredSteps_valid calleeFork) hlen Mem.wf_empty (eSubRem h))
  have pOut : (ord4Parent h).output = [] := ef.2.2.2.2.2.2.2.2.1
  have pClean : (ord4Parent h).error = none ∧ 0 ≤ (ord4Parent h).refundCounter :=
    ⟨ef.2.2.2.2.2.2.2.2.2.2.1.1,ef.2.2.2.2.2.2.2.2.2.2.1.2⟩
  have sr := eSub_resume_facts h rfl pOut pClean cPost (eff.output.trans rfl)
    (by rw [eff.logs,initLogs]; rfl) (by change exitAddr ≠ depositContractAddress; decide)
    ef.2.2.2.2.2.2.2.2.2.1 rfl
  have nonprecomp : ((eSubMsg h).withBenv (eSubNextBenv h)).benv.stat.rules.isPrecomp exitAddr = false := by
    change (eSubNextBenv h).stat.rules.isPrecomp exitAddr = false
    rw [benvAfterTransfer_stat htr]
    change pragueRules.isPrecomp exitAddr = false
    decide
  have enters : (Frame.ofCall (eSubMsg h)).enter = .run ⟨0,eSubSevm h,eSubInit h⟩ := by
    simpa only [Frame.ofCall,initEvm,eSubSevm,eSubInit] using
      (Frame.enter_run_of_nonprecompile (f := Frame.ofCall (eSubMsg h))
        (benv := eSubNextBenv h) (adr := exitAddr) htr rfl nonprecomp)
  have atCall : Ninst.At (ordSevm h).code 136 (.exec .call) := by
    change Ninst.At ordinaryCode 136 (.exec .call)
    unfold Ninst.At
    kernel_rfl
  have postGas : (eSubPost h).gasLeft = eSubRem h := by
    simp only [eSubPost,Exit.submissionPost,Exit.Steps.submissionPost,St.gasLeft]
  have pgl : (ord4Parent h).gasLeft + (eSubPost h).gasLeft =
      (ord4Gas h - (ord4Fwd h - 2300 + ord4Extra h)) + eSubRem h := by
    rw [postGas]
    unfold ord4Parent
    rw [callSpawnParent_gasLeft]
    simp only [ord4Bare,addAccessedAddress_gasLeft,Devm.setMach_gasLeft]
  have afterGas : (afterESub h).gasLeft = (ord4Parent h).gasLeft + (eSubPost h).gasLeft := by
    simpa only [afterESub] using sr.2.2.2.2.2.2.2
  have gasWindow :
      50000 ≤ (ord4Gas h - (ord4Fwd h - 2300 + ord4Extra h)) + eSubRem h ∧
      (ord4Gas h - (ord4Fwd h - 2300 + ord4Extra h)) + eSubRem h < 2^256 := by
    unfold eSubRem ord4Fwd ord4Extra
    generalize hg : ord4Gas h = g at range ⊢
    generalize ha : ord4Acc h = acc at accLe ⊢
    generalize hc : Exit.submissionGas (eSubSevm h) (eSubInit h) .empty 1 = cost at sgBound ⊢
    unfold except64th
    constructor <;> omega
  exact ⟨by rw [Evm.step_next atCall]; simp only [Ninst.step_exec,eSub_xstep,XStep.toStep],
    enters,ex,sr.1,cPost,sr.2.1,sr.2.2.2.2.1,sr.2.2.2.2.2.1,sr.2.2.2.2.2.2.1,
    by rw [afterGas,pgl]; exact gasWindow.1,
    by rw [afterGas,pgl]; exact gasWindow.2⟩

-- Runs, frames, and retention
private noncomputable def dFeeRun (h : B256) := Classical.choice (dFee_step h).2.2.1
private noncomputable def dSubRun (h : B256) := Classical.choice (dSub_step h).2.2.1
private noncomputable def eFeeRun (h : B256) := Classical.choice (eFee_step h).2.2.1
private noncomputable def eSubRun (h : B256) := Classical.choice (eSub_step h).2.2.1

private theorem dFee_commits (h : B256) : Execution.commits (.ok (dFeePost h)) = true := by
  change (dFeePost h).error.isNone = true; rw [(dFee_step h).2.2.2.2.1.1]; rfl
private theorem dSub_commits (h : B256) : Execution.commits (.ok (dSubPost h)) = true := by
  change (dSubPost h).error.isNone = true; rw [(dSub_step h).2.2.2.2.1.1]; rfl
private theorem eFee_commits (h : B256) : Execution.commits (.ok (eFeePost h)) = true := by
  change (eFeePost h).error.isNone = true; rw [(eFee_step h).2.2.2.2.1.1]; rfl
private theorem eSub_commits (h : B256) : Execution.commits (.ok (eSubPost h)) = true := by
  change (eSubPost h).error.isNone = true; rw [(eSub_step h).2.2.2.2.1.1]; rfl

noncomputable def dFeeFrame (h : B256) : Exec.Frame := .ofRun (dFeeRun h) (dFee_commits h)
noncomputable def dSubFrame (h : B256) : Exec.Frame := .ofRun (dSubRun h) (dSub_commits h)
noncomputable def eFeeFrame (h : B256) : Exec.Frame := .ofRun (eFeeRun h) (eFee_commits h)
noncomputable def eSubFrame (h : B256) : Exec.Frame := .ofRun (eSubRun h) (eSub_commits h)

private theorem ord_end_core (s : Sevm) (d : Devm) (m : Mem) (g : Nat) :
    let sta := { s with code := ordinaryCode, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 1 ⟨137, sta, d.setMach ⟨[1],m,g+2,d.stateGas⟩⟩ =
      some ⟨138,sta,d.setMach ⟨[],m,g,d.stateGas⟩⟩ ∧
    Evm.step ⟨138,sta,d.setMach ⟨[],m,g,d.stateGas⟩⟩ =
      .halt (.ok (d.setMach ⟨[],m,g,d.stateGas⟩)) := by
  dsimp only; revert s d m g; kernel_forall_rfl_and

private theorem writer_end_core (s : Sevm) (d : Devm) (m : Mem) (g : Nat) :
    let sta := { s with code := writerCode true, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 1 ⟨181, sta, d.setMach ⟨[1],m,g+2,d.stateGas⟩⟩ =
      some ⟨182,sta,d.setMach ⟨[],m,g,d.stateGas⟩⟩ ∧
    Evm.step ⟨182,sta,d.setMach ⟨[],m,g,d.stateGas⟩⟩ =
      .halt (.ok (d.setMach ⟨[],m,g,d.stateGas⟩)) := by
  dsimp only; revert s d m g; kernel_forall_rfl_and

private theorem ord_end (h : B256) :
    ConcreteRun.stepN 1 ⟨137,ordSevm h,afterESub h⟩ = some ⟨138,ordSevm h,ordEnd h⟩ ∧
    Evm.step ⟨138,ordSevm h,ordEnd h⟩ = .halt (.ok (ordEnd h)) := by
  have es := eSub_step h
  have mach : (afterESub h).setMach ⟨[1],(afterESub h).memory,((afterESub h).gasLeft-2)+2,(afterESub h).stateGas⟩ = afterESub h := by
    rw [Nat.sub_add_cancel (by omega : 2 ≤ (afterESub h).gasLeft)]
    exact (St.self es.2.2.2.2.2.1 rfl).symm
  have ps := ord_end_core (ordSevm h) (afterESub h) (afterESub h).memory ((afterESub h).gasLeft-2)
  dsimp only at ps
  rw [ord_sta h,mach] at ps
  exact ps

private noncomputable def ordFinalRun (h : B256) : Exec 137 (ordSevm h) (afterESub h) (.ok (ordEnd h)) :=
  ConcreteRun.Exec.ofStepN 1 (ord_end h).1 (.halt (ord_end h).2)

private noncomputable def ordFromESub (h : B256) : Exec 136 (ordSevm h) (ord4State h) (.ok (ordEnd h)) :=
  .runOk (eSub_step h).1 (eSub_step h).2.1 (eSubRun h) (eSub_step h).2.2.2.1
    (ordFinalRun h)

private noncomputable def ordFromEFee (h : B256) : Exec 105 (ordSevm h) (ord3State h) (.ok (ordEnd h)) :=
  .runOk (eFee_step h).1 (eFee_step h).2.1 (eFeeRun h) (eFee_step h).2.2.2.1
    (ConcreteRun.Exec.ofStepN 9 (ord_p4 h) (ordFromESub h))

private noncomputable def ordFromDSub (h : B256) : Exec 76 (ordSevm h) (ord2State h) (.ok (ordEnd h)) := by
  have resumed := (dSub_step h).2.2.2.1
  rw [←paidState_eq] at resumed
  exact .runOk (dSub_step h).1 (dSub_step h).2.1 (dSubRun h) resumed
    (ConcreteRun.Exec.ofStepN 7 (ord_p3 h) (ordFromEFee h))

private noncomputable def ordFromDFee (h : B256) : Exec 27 (ordSevm h) (ord1State h) (.ok (ordEnd h)) :=
  .runOk (dFee_step h).1 (dFee_step h).2.1 (dFeeRun h) (dFee_step h).2.2.2.1
    (ConcreteRun.Exec.ofStepN 14 (ord_p2 h) (ordFromDSub h))

private noncomputable def ordRun (h : B256) : Exec 0 (ordSevm h) (ordBase h) (.ok (ordEnd h)) :=
  ConcreteRun.Exec.ofStepN 6 (ord_p1 h) (ordFromDFee h)

private noncomputable def afterOrd (h : B256) : Devm := callChildPost (writerCallParent h) (ordEnd h) 0 0
private noncomputable def writerEnd (h : B256) : Devm :=
  (afterOrd h).setMach ⟨[], (afterOrd h).memory, (afterOrd h).gasLeft - 2, (afterOrd h).stateGas⟩

private theorem ordEnd_clean (h : B256) : (ordEnd h).error = none ∧ 0 ≤ (ordEnd h).refundCounter := by
  have es := eSub_step h
  simp only [ordEnd,Devm.setMach_error,Devm.setMach_refundCounter]
  exact es.2.2.2.2.2.2.2.2.1

private theorem ordEnd_output (h : B256) : (ordEnd h).output = [] := by
  simp only [ordEnd,Devm.setMach_output]
  exact (eSub_step h).2.2.2.2.2.2.1

private theorem ordEnd_logs (h : B256) : (ordEnd h).logs = (afterESub h).logs := by
  simp only [ordEnd,Devm.setMach_logs]

private theorem writerParent_stack (h : B256) : (writerCallParent h).stack = [] := by
  unfold writerCallParent
  rw [callSpawnParent_stack]
  unfold writerCallBare
  rfl

private theorem writerParent_error (h : B256) : (writerCallParent h).error = (afterExitReset h).error := by
  unfold writerCallParent
  rw [callSpawnParent_error]
  simp only [writerCallBare,addAccessedAddress_error,Devm.setMach_error]

private theorem writerBare_refund (h : B256) : (writerCallBare h).refundCounter = (afterExitReset h).refundCounter := by
  unfold writerCallBare
  generalize hb : afterExitReset h = b
  generalize hg : writerCallGas h = g
  rfl

private theorem writerParent_refund (h : B256) : (writerCallParent h).refundCounter = (afterExitReset h).refundCounter := by
  unfold writerCallParent
  have same : (callSpawnParent (writerCallBare h) (writerCallFwd h + writerCallAcc h) 0 0 0 0).refundCounter =
      (writerCallBare h).refundCounter := by
    generalize hd : writerCallBare h = d
    generalize hc : writerCallFwd h + writerCallAcc h = c
    rfl
  exact same.trans (writerBare_refund h)

private theorem writerBare_logs (h : B256) : (writerCallBare h).logs = (afterExitReset h).logs := by
  unfold writerCallBare
  generalize hb : afterExitReset h = b
  generalize hg : writerCallGas h = g
  rw [addAccessedAddress_logs,Devm.setMach_logs]

private theorem writerParent_logs (h : B256) : (writerCallParent h).logs = (afterExitReset h).logs := by
  unfold writerCallParent
  have same : (callSpawnParent (writerCallBare h) (writerCallFwd h + writerCallAcc h) 0 0 0 0).logs =
      (writerCallBare h).logs := by
    generalize hd : writerCallBare h = d
    generalize hc : writerCallFwd h + writerCallAcc h = c
    unfold callSpawnParent
    rw [Devm.withReturnData_logs,Devm.memExtends_logs,Devm.setMach_logs]
  exact same.trans (writerBare_logs h)

private theorem ord_settles (h : B256) :
    Frame.settlementCommits (Frame.ofCall (ordMsg h)) (.ok (ordEnd h)) = true ∧
    Resume.run (.call (writerCallParent h) 0 0) ((Frame.ofCall (ordMsg h)).settle (.ok (ordEnd h))) = .ok (afterOrd h) := by
  have clean := ordEnd_clean h
  have settles := frame_settle_ok (ordMsg h) (ordEnd h) clean.1 rfl
  refine ⟨Frame.settlementCommits_ofCall_of_raw_commits ?_,?_⟩
  · change (ordEnd h).error.isNone = true
    rw [clean.1]
    rfl
  · rw [settles,Resume.run_call_ok (by rw [clean.1]; rfl) (by rw [writerParent_stack]; decide)]
    rfl

private theorem afterOrd_clean_logs (h : B256) :
    ((afterOrd h).error = none ∧ 0 ≤ (afterOrd h).refundCounter) ∧
    (∀ l ∈ (afterOrd h).logs,l.address ≠ depositContractAddress) := by
  have af := afterExitReset_facts h
  have oc := ordEnd_clean h
  have cf := callChildPost_facts (writerCallParent h) (ordEnd h) 0 0 (ordEnd_output h)
  have err : (afterOrd h).error = (writerCallParent h).error := by simpa only [afterOrd] using cf.2.2.2.2.2.2.2.1
  have refund : (afterOrd h).refundCounter = (writerCallParent h).refundCounter + (ordEnd h).refundCounter := by
    simpa only [afterOrd] using cf.2.2.2.2.2.2.1
  have logs : (afterOrd h).logs = (writerCallParent h).logs ++ (ordEnd h).logs := by
    simpa only [afterOrd] using cf.2.2.2.2.2.1
  refine ⟨⟨by rw [err,writerParent_error]; exact af.2.2.2.2.1,
    by rw [refund,writerParent_refund]; exact Int.add_nonneg af.2.2.2.2.2.1 oc.2⟩,?_⟩
  intro l hl
  rw [logs,writerParent_logs,ordEnd_logs,af.2.2.2.2.2.2.1,List.nil_append] at hl
  exact (eSub_step h).2.2.2.2.2.2.2.1 l hl

private theorem ord_settle_resume (h : B256) :
    Frame.settlementCommits (Frame.ofCall (ordMsg h)) (.ok (ordEnd h)) = true ∧
    Resume.run (.call (writerCallParent h) 0 0) ((Frame.ofCall (ordMsg h)).settle (.ok (ordEnd h))) = .ok (afterOrd h) ∧
    ((writerEnd h).error = none ∧ 0 ≤ (writerEnd h).refundCounter) ∧
    (∀ l ∈ (writerEnd h).logs,l.address ≠ depositContractAddress) ∧ (ordEnd h).output = [] := by
  have sr := ord_settles h
  have observed := afterOrd_clean_logs h
  refine ⟨sr.1,sr.2,?_,?_,ordEnd_output h⟩
  · simpa only [writerEnd,Devm.setMach_error,Devm.setMach_refundCounter] using observed.1
  · simpa only [writerEnd,Devm.setMach_logs] using observed.2

private theorem writerParent_gas (h : B256) : (writerCallParent h).gasLeft =
    writerCallGas h - (writerCallFwd h + writerCallAcc h) := by
  unfold writerCallParent
  rw [callSpawnParent_gasLeft]
  simp only [writerCallBare,addAccessedAddress_gasLeft,Devm.setMach_gasLeft]

private theorem ordEnd_gas (h : B256) : (ordEnd h).gasLeft = (afterESub h).gasLeft - 2 := by
  unfold ordEnd
  exact St.gasLeft

private theorem afterOrd_gas (h : B256) : (afterOrd h).gasLeft =
    (writerCallGas h - (writerCallFwd h + writerCallAcc h)) + ((afterESub h).gasLeft - 2) := by
  have cf := callChildPost_facts (writerCallParent h) (ordEnd h) 0 0 (ordEnd_output h)
  change (callChildPost (writerCallParent h) (ordEnd h) 0 0).gasLeft = _
  rw [cf.2.2.1,writerParent_gas,ordEnd_gas]

private theorem afterOrd_gas_room (h : B256) : 2 ≤ (afterOrd h).gasLeft := by
  have es := eSub_step h
  rw [afterOrd_gas]
  omega

private theorem afterOrd_stack (h : B256) : (afterOrd h).stack = [1] := by
  have cf := callChildPost_facts (writerCallParent h) (ordEnd h) 0 0 (ordEnd_output h)
  simpa only [afterOrd,writerParent_stack] using cf.1

private theorem afterOrd_mach (h : B256) :
    (afterOrd h).setMach ⟨[1],(afterOrd h).memory,((afterOrd h).gasLeft-2)+2,(afterOrd h).stateGas⟩ = afterOrd h := by
  rw [Nat.sub_add_cancel (afterOrd_gas_room h)]
  exact (St.self (afterOrd_stack h) rfl).symm

private theorem writer_end (h : B256) :
    ConcreteRun.stepN 1 ⟨181, writer h, afterOrd h⟩ = some ⟨182, writer h, writerEnd h⟩ ∧
    Evm.step ⟨182,writer h,writerEnd h⟩ = .halt (.ok (writerEnd h)) := by
  have ps := writer_end_core (writer h) (afterOrd h) (afterOrd h).memory ((afterOrd h).gasLeft-2)
  dsimp only at ps
  rw [writer_sta h, afterOrd_mach] at ps
  exact ps

private noncomputable def writerRestRun (h : B256) :
    Exec 152 (writer h) (afterExitReset h) (.ok (writerEnd h)) :=
  ConcreteRun.Exec.ofStepN 8 (writer_ord_prefix h)
    (.runOk (writer_ord_spawn_enter h).1 (writer_ord_spawn_enter h).2 (ordRun h) (ord_settles h).2
      (ConcreteRun.Exec.ofStepN 1 (writer_end h).1 (.halt (writer_end h).2)))

private noncomputable def fullTxRun (h : B256) :
    Exec 0 (writer h) (base true (some h)) (.ok (writerEnd h)) :=
  prefixFourRun h (writerRestRun h)




private theorem dFee_childless (h : B256) (a : Adr) : Exec.keptAt a (dFeeRun h) = [] :=
  deposit_keptAt_nil a rfl rfl (dFeeRun h)
private theorem dSub_childless (h : B256) (a : Adr) : Exec.keptAt a (dSubRun h) = [] :=
  deposit_keptAt_nil a rfl ((dSub_transfer h).2.2.2.2.1.rules_stateGas_none) (dSubRun h)
private theorem eFee_childless (h : B256) (a : Adr) : Exec.keptAt a (eFeeRun h) = [] :=
  exit_keptAt_nil a rfl rfl (eFeeRun h)
private theorem eSub_childless (h : B256) (a : Adr) : Exec.keptAt a (eSubRun h) = [] :=
  exit_keptAt_nil a rfl ((eSub_transfer h).2.2.2.2.1.rules_stateGas_none) (eSubRun h)

private theorem dFee_settles (h : B256) : Frame.settlementCommits (Frame.ofCall (dFeeMsg h)) (.ok (dFeePost h)) = true :=
  Frame.settlementCommits_ofCall_of_raw_commits (dFee_commits h)

private theorem dSub_settles (h : B256) : Frame.settlementCommits (Frame.ofCall (dSubMsg h)) (.ok (dSubPost h)) = true :=
  Frame.settlementCommits_ofCall_of_raw_commits (dSub_commits h)

private theorem eFee_settles (h : B256) : Frame.settlementCommits (Frame.ofCall (eFeeMsg h)) (.ok (eFeePost h)) = true :=
  Frame.settlementCommits_ofCall_of_raw_commits (eFee_commits h)

private theorem eSub_settles (h : B256) : Frame.settlementCommits (Frame.ofCall (eSubMsg h)) (.ok (eSubPost h)) = true :=
  Frame.settlementCommits_ofCall_of_raw_commits (eSub_commits h)

private theorem ordFinalRun_kept (h : B256) (a : Adr) : Exec.keptAt a (ordFinalRun h) = [] :=
  (ConcreteRun.Exec.keptAt_ofStepN a 1 (ord_end h).1 (.halt (ord_end h).2)).trans (by rw [Exec.keptAt])

private theorem ordFromESub_deposit_kept (h : B256) : Exec.keptAt depositAddr (ordFromESub h) = [] := by
  calc
    Exec.keptAt depositAddr (ordFromESub h) = Exec.keptAt depositAddr (eSubRun h) ++ Exec.keptAt depositAddr (ordFinalRun h) :=
      Exec.keptAt_settled_away (a := depositAddr) (eSub_step h).1 (eSub_step h).2.1 (eSubRun h)
        (eSub_step h).2.2.2.1 (ordFinalRun h) (eSub_settles h) (by change exitAddr ≠ depositAddr; decide)
    _ = [] := by rw [eSub_childless,ordFinalRun_kept]; rfl

private theorem ordFromESub_exit_kept (h : B256) : Exec.keptAt exitAddr (ordFromESub h) = [eSubFrame h] := by
  calc
    Exec.keptAt exitAddr (ordFromESub h) = eSubFrame h :: Exec.keptAt exitAddr (ordFinalRun h) :=
      Exec.keptAt_settled_here (a := exitAddr) (eSub_step h).1 (eSub_step h).2.1 (eSubRun h)
        (eSub_step h).2.2.2.1 (ordFinalRun h) (eSub_settles h) rfl
    _ = [eSubFrame h] := by rw [ordFinalRun_kept]

private theorem ordFromESub_kept (h : B256) :
    Exec.keptAt depositAddr (ordFromESub h) = [] ∧
    Exec.keptAt exitAddr (ordFromESub h) = [eSubFrame h] :=
  ⟨ordFromESub_deposit_kept h,ordFromESub_exit_kept h⟩

private theorem ordFromEFee_kept (h : B256) :
    Exec.keptAt depositAddr (ordFromEFee h) = [] ∧
    Exec.keptAt exitAddr (ordFromEFee h) = [eFeeFrame h,eSubFrame h] := by
  constructor
  · unfold ordFromEFee
    erw [Exec.keptAt_settled_away (a := depositAddr) _ _ _ _ _ (eFee_settles h) (by change exitAddr ≠ depositAddr; decide)]
    simp only [eFee_childless,List.nil_append]
    erw [ConcreteRun.Exec.keptAt_ofStepN]
    rw [(ordFromESub_kept h).1]
  · unfold ordFromEFee
    erw [Exec.keptAt_settled_here (a := exitAddr) _ _ _ _ _ (eFee_settles h) rfl]
    erw [ConcreteRun.Exec.keptAt_ofStepN]
    rw [(ordFromESub_kept h).2]
    rfl

private theorem ordFromDSub_kept (h : B256) :
    Exec.keptAt depositAddr (ordFromDSub h) = [dSubFrame h] ∧
    Exec.keptAt exitAddr (ordFromDSub h) = [eFeeFrame h,eSubFrame h] := by
  constructor
  · unfold ordFromDSub; dsimp only
    erw [Exec.keptAt_settled_here (a := depositAddr) _ _ _ _ _ (dSub_settles h) rfl]
    erw [ConcreteRun.Exec.keptAt_ofStepN]
    rw [(ordFromEFee_kept h).1]
    rfl
  · unfold ordFromDSub; dsimp only
    erw [Exec.keptAt_settled_away (a := exitAddr) _ _ _ _ _ (dSub_settles h) (by change depositAddr ≠ exitAddr; decide)]
    simp only [dSub_childless,List.nil_append]
    erw [ConcreteRun.Exec.keptAt_ofStepN]
    rw [(ordFromEFee_kept h).2]

private theorem ordFromDFee_kept (h : B256) :
    Exec.keptAt depositAddr (ordFromDFee h) = [dFeeFrame h,dSubFrame h] ∧
    Exec.keptAt exitAddr (ordFromDFee h) = [eFeeFrame h,eSubFrame h] := by
  constructor
  · unfold ordFromDFee
    erw [Exec.keptAt_settled_here (a := depositAddr) _ _ _ _ _ (dFee_settles h) rfl]
    erw [ConcreteRun.Exec.keptAt_ofStepN]
    rw [(ordFromDSub_kept h).1]
    rfl
  · unfold ordFromDFee
    erw [Exec.keptAt_settled_away (a := exitAddr) _ _ _ _ _ (dFee_settles h) (by change depositAddr ≠ exitAddr; decide)]
    simp only [dFee_childless,List.nil_append]
    erw [ConcreteRun.Exec.keptAt_ofStepN]
    rw [(ordFromDSub_kept h).2]

private theorem ordRun_deposit_kept (h : B256) : Exec.keptAt depositAddr (ordRun h) = [dFeeFrame h,dSubFrame h] :=
  (ConcreteRun.Exec.keptAt_ofStepN depositAddr 6 (ord_p1 h) (ordFromDFee h)).trans (ordFromDFee_kept h).1
private theorem ordRun_exit_kept (h : B256) : Exec.keptAt exitAddr (ordRun h) = [eFeeFrame h,eSubFrame h] :=
  (ConcreteRun.Exec.keptAt_ofStepN exitAddr 6 (ord_p1 h) (ordFromDFee h)).trans (ordFromDFee_kept h).2

private theorem writerRestRun_kept (h : B256) : ∀ a : Adr, ordinaryAddr ≠ a → Exec.keptAt a (writerRestRun h) = Exec.keptAt a (ordRun h) := by
  intro a hne
  let last := ConcreteRun.Exec.ofStepN 1 (writer_end h).1 (.halt (writer_end h).2)
  have lastNil : Exec.keptAt a last = [] := by
    exact (ConcreteRun.Exec.keptAt_ofStepN a 1 (writer_end h).1 (.halt (writer_end h).2)).trans (by rw [Exec.keptAt])
  calc
    Exec.keptAt a (writerRestRun h) = Exec.keptAt a
        (.runOk (writer_ord_spawn_enter h).1 (writer_ord_spawn_enter h).2 (ordRun h) (ord_settles h).2 last) :=
      ConcreteRun.Exec.keptAt_ofStepN a 8 (writer_ord_prefix h) _
    _ = Exec.keptAt a (ordRun h) ++ Exec.keptAt a last :=
      Exec.keptAt_settled_away (a := a) (writer_ord_spawn_enter h).1 (writer_ord_spawn_enter h).2
        (ordRun h) (ord_settles h).2 last (ord_settles h).1 hne
    _ = Exec.keptAt a (ordRun h) := by rw [lastNil,List.append_nil]

private theorem fullTxRun_kept (h : B256) :
    Exec.keptAt depositAddr (fullTxRun h) = [dLatchFrame h, dResetFrame h, dFeeFrame h, dSubFrame h] ∧
    Exec.keptAt exitAddr (fullTxRun h) = [eLatchFrame h, eResetFrame h, eFeeFrame h, eSubFrame h] := by
  have elS : Frame.settlementCommits (Frame.ofCall (exitLatchMsg h)) _ = true :=
    Frame.settlementCommits_ofCall_of_raw_commits (exit_latch_commits h)
  have erS : Frame.settlementCommits (Frame.ofCall (exitResetMsg h)) _ = true :=
    Frame.settlementCommits_ofCall_of_raw_commits (exit_reset_commits h)
  have ordDep := ordRun_deposit_kept h
  have ordExit := ordRun_exit_kept h
  have restAt := writerRestRun_kept h
  constructor
  · unfold fullTxRun prefixFourRun
    erw [pair_kept true (some h)]; unfold exitSuffixRun
    erw [ConcreteRun.Exec.keptAt_ofStepN, Exec.keptAt_settled_away _ _ _ _ _ elS (by change exitAddr ≠ depositAddr; decide),
      exit_keptAt_nil depositAddr rfl rfl (exitLatchRun h), List.nil_append,
      ConcreteRun.Exec.keptAt_ofStepN, Exec.keptAt_settled_away _ _ _ _ _ erS (by change exitAddr ≠ depositAddr; decide),
      exit_keptAt_nil depositAddr rfl rfl (exitResetRun h), List.nil_append,
      restAt depositAddr (by decide), ordDep]; rfl
  · unfold fullTxRun prefixFourRun pairRun pairCall pairMiddle pairTail
    have d1S : Frame.settlementCommits (Frame.ofCall (firstMsg true (some h))) _ = true :=
      Frame.settlementCommits_ofCall_of_raw_commits (first_commits true (some h))
    have d2S : Frame.settlementCommits (Frame.ofCall (secondMsg true (some h))) _ = true :=
      Frame.settlementCommits_ofCall_of_raw_commits (second_commits true (some h))
    erw [ConcreteRun.Exec.keptAt_ofStepN, Exec.keptAt_settled_away _ _ _ _ _ d1S (by change depositAddr ≠ exitAddr; decide),
      deposit_keptAt_nil exitAddr rfl rfl (firstRun true (some h)), List.nil_append,
      ConcreteRun.Exec.keptAt_ofStepN, Exec.keptAt_settled_away _ _ _ _ _ d2S (by change depositAddr ≠ exitAddr; decide),
      deposit_keptAt_nil exitAddr rfl rfl (secondRun true (some h)), List.nil_append]
    unfold exitSuffixRun
    erw [ConcreteRun.Exec.keptAt_ofStepN, Exec.keptAt_settled_here (a := exitAddr) _ _ _ _ _ elS rfl,
      ConcreteRun.Exec.keptAt_ofStepN, Exec.keptAt_settled_here (a := exitAddr) _ _ _ _ _ erS rfl,
      restAt exitAddr (by decide), ordExit]; rfl



private theorem writer_full_undelegated : getDelegatedCodeAddress (writerCode true) = none := by decide +kernel

private noncomputable def txRoot (h : B256) : Root :=
  ⟨Frame.ofCall (msg true (some h)), initEvm (msg true (some h)), .ok (writerEnd h), fullTxRun h⟩

private theorem tx_stage (h : B256) :
    ∃ st bout, TransactionRoots (benv true (some h)) .init txD 0 st bout senderE [txRoot h] ∧
      bout.blockGasUsed ≤ 2 ^ 20 ∧ parseDepositRequests bout = .ok [] := by
  have osr := ord_settle_resume h
  have mUndel : getDelegatedCodeAddress (msg true (some h)).code = none := by
    rw [message_code true (some h)]; exact writer_full_undelegated
  have mEnter : (Frame.ofCall (msg true (some h))).enter = .run (initEvm (msg true (some h))) :=
    Frame.enter_run_of_nonprecompile (after_transfer true (some h)) rfl
      (by change pragueRules.isPrecomp systemAddress = false; decide)
  let mOut : MsgCallOutput :=
    { gasLeft := (writerEnd h).gasLeft, refundCounter := ((0 + (writerEnd h).refundCounter.toNat : Nat) : Int)
      logs := (writerEnd h).logs, accountsToDelete := (writerEnd h).accountsToDelete
      error := none, returnData := (writerEnd h).output, touchedAccounts := (writerEnd h).meta.touchedAccounts }
  have mProc : processMessageCall (msg true (some h)) = .ok ((writerEnd h).state, mOut) :=
    processMessageCall_call_of_message rfl rfl rfl mUndel
      (processMessage_call_of_exec (after_transfer true (some h)) rfl
        (by change pragueRules.isPrecomp systemAddress = false; decide)
        ((exec_iff_exec_eq 0 (writer h) (base true (some h)) (.ok (writerEnd h))).mp ⟨fullTxRun h⟩)
        osr.2.2.1.1 rfl)
      osr.2.2.1.1 (Int.toNat?_eq_some_of_nonneg osr.2.2.1.2)
  have mRes : messageCallExecutionMessage (msg true (some h)) = msg true (some h) := by
    unfold messageCallExecutionMessage Msg.resolveCodeDelegation
    have nd : (msg true (some h)).benv.stat.rules.delegatedCodeAddress (msg true (some h)).code = none := by
      unfold ForkRules.delegatedCodeAddress; rw [mUndel]; split <;> rfl
    rw [nd]
  have mEntry : messageEntry (msg true (some h)) = some (Frame.ofCall (msg true (some h)), initEvm (msg true (some h))) := by
    unfold messageEntry legacyEntry
    have delOk : messageCallDelegation (msg true (some h)) = .ok (msg true (some h), 0) := rfl
    change (match messageCallDelegation (msg true (some h)) with
      | .ok (d, _) => enteredFrame (Frame.ofCall (messageCallExecutionMessage d)) | .error _ => none) = _
    rw [delOk]; dsimp only; rw [mRes]; unfold enteredFrame; rw [mEnter]
  have tValid : validateTransaction (benv true (some h)).stat.rules txD 0 = .ok (21000, 21000) :=
    validateTransaction_ok_of_facts rfl (txD_intrinsic rfl rfl rfl rfl rfl 0) (by decide) (by decide) rfl rfl
  have tCheck : checkTransaction (benv true (some h)).beginTransaction
      (transactionPreludeBout .init txD 0) txD = .ok (senderE, 2, [], 0) :=
    checkTransaction_ok_of_parts (maxFee := 2 ^ 20 * 8) (maxFee' := 2 ^ 20 * 8)
      (checkTransactionGasLimits_ok_of_room rfl (by change 1048576 ≤ 60000000; decide) (Nat.zero_le _))
      (checkTransactionChainId_two rfl rfl) (recovered true (some h))
      (checkTransactionGasFee_two (benv := (benv true (some h)).beginTransaction) (tx := txD)
        (maxPriorityFee := 1) (maxFee := 8) rfl (by decide) (by change (1 : Nat) ≤ 8; decide) (by decide))
      (checkTransactionBlobData_two rfl _) (checkTransactionReceiver_two rfl)
      (checkTransactionAuthorizationList_two rfl)
      (by change checkTransactionSenderAccountFor _ ((state true (some h)).get senderE) _ _ = _
          have sa : (state true (some h)).get senderE = senderAcct 2 (2 ^ 100) := State.get_setPresent_self _ _ _
          rw [sa]; exact checkTransactionSenderAccount_ok_of_noCode rfl (by decide) rfl)
  have refundOk : Int.toNat? mOut.refundCounter = some (writerEnd h).refundCounter.toNat := by
    change Int.toNat? ((0 + (writerEnd h).refundCounter.toNat : Nat) : Int) = _
    simp only [Nat.zero_add]; exact Int.toNat?_eq_some_of_nonneg (by omega)
  obtain ⟨bout, proc, _, gasUsed, keys, receipt⟩ := processTransaction_of_stages_receipts
    (bout := .init) (index := 0) rfl rfl rfl rfl tValid tCheck (debit_eq true (some h))
    (prepared true (some h)) mProc refundOk
  have tValidBegin : validateTransaction (benv true (some h)).beginTransaction.stat.rules txD 0 = .ok (21000,21000) := tValid
  have tDebitBegin : ((benv true (some h)).beginTransaction.state.incrNonce senderE).subBal senderE
      (txD.gas * 2 + transactionBlobGasFee (benv true (some h)).beginTransaction txD).toB256 = some (debit true (some h)) := debit_eq true (some h)
  have tMsg : transactionMessage (benv true (some h)) .init txD 0 = .ok (senderE, msg true (some h)) := by
    unfold transactionMessage; dsimp only; rw [recoverValidationSender_of_stateGas_none txD rfl]
    simp only [tValidBegin, tCheck, tDebitBegin, Except.mapError, bind, Except.bind, Option.toExcept]
    have tenv : transactionTenvAt (benv true (some h)).beginTransaction txD 0 senderE 2 21000 [] =
        transactionTenv (benv true (some h)).beginTransaction txD 0 senderE 2 21000 [] := rfl
    rw [tenv, prepared true (some h)]
  refine ⟨_, bout, ⟨proc, msg true (some h), (writerEnd h).state, mOut, tMsg, ⟨mProc, by rw [mEntry]; rfl⟩⟩, ?_, ?_⟩
  · rw [gasUsed, show BlockOutput.init.blockGasUsed = 0 from rfl, Nat.zero_add]; exact txGasUsed_le (by decide)
  · apply BlockForward.parseDepositRequests_of_no_deposit_logs
    intro k hk; rw [keys] at hk; obtain rfl := List.mem_singleton.mp hk; exact ⟨_, receipt, osr.2.2.2.1⟩



private def parentHeader : Header :=
  { SyntheticBpo2Envelope.checkpointHeader .empty with stateRoot := 0, gasLimit := 60000000, gasUsed := 30000000 }
private def parentBlock : Block := { header := parentHeader, txs := [], wds := [], ommers := [] }
private def h0 : B256 := parentHeader.hash
private def startChain : BlockChain := ⟨[parentBlock], state true (some h0), 1⟩
private def template : Header := { parentHeader with number := 1, timestamp := 1 }

private theorem state_codes (h : B256) :
    (state true (some h)).getCode depositAddr = Deposit.code ∧
    (state true (some h)).getCode exitAddr = Exit.code ∧
    (state true (some h)).getCode beaconRootsAddress = ByteArray.empty ∧
    (state true (some h)).getCode historyStorageAddress = ByteArray.empty ∧
    (state true (some h)).getCode withdrawalRequestPredeployAddress = stopCode ∧
    (state true (some h)).getCode consolidationRequestPredeployAddress = stopCode := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold state builderWorld baseWorld State.getCode
     repeat (first | rw [State.get_setPresent_self] | rw [State.get_setPresent_ne _ (by decide)]))
  all_goals (rw [State.get_eq_getD]; change (((∅ : State)[_]?.getD Acct.nil).code) = _; rw [Std.TreeMap.getElem?_emptyc]; rfl)


private theorem block_context (st : State) (bout : BlockOutput) :
    initBenv .prague startChain (BlockForward.commitHeader Fork.prague.ruleSet parentBlock template st bout) =
      benv true (some h0) := by
  trans initBenv .prague startChain (BlockForward.commitHeader Fork.prague.ruleSet parentBlock template (state true (some h0)) .init)
  · exact BlockForward.initBenv_commitHeader_body_eq .prague startChain Fork.prague.ruleSet parentBlock template st (state true (some h0)) bout .init
  · rfl


private theorem beacon_message_entry (h : B256) :
    messageEntry (systemCallMsg (benv true (some h)) beaconRootsAddress ByteArray.empty (0 : B256).toBytes) = some (Frame.ofCall (systemCallMsg (benv true (some h)) beaconRootsAddress ByteArray.empty (0 : B256).toBytes),initEvm (systemCallMsg (benv true (some h)) beaconRootsAddress ByteArray.empty (0 : B256).toBytes)) := by
  rfl

private theorem history_message_entry (h : B256) :
    messageEntry (systemCallMsg (benv true (some h)) historyStorageAddress ByteArray.empty h.toBytes) = some (Frame.ofCall (systemCallMsg (benv true (some h)) historyStorageAddress ByteArray.empty h.toBytes),initEvm (systemCallMsg (benv true (some h)) historyStorageAddress ByteArray.empty h.toBytes)) := by
  rfl

private theorem withdrawal_message_entry (h : B256) (st : State) :
    messageEntry (systemCallMsg ((benv true (some h)).withState st) withdrawalRequestPredeployAddress stopCode []) = some (Frame.ofCall (systemCallMsg ((benv true (some h)).withState st) withdrawalRequestPredeployAddress stopCode []),initEvm (systemCallMsg ((benv true (some h)).withState st) withdrawalRequestPredeployAddress stopCode [])) := by
  rfl

private theorem consolidation_message_entry (h : B256) (st : State) :
    messageEntry (systemCallMsg ((benv true (some h)).withState st) consolidationRequestPredeployAddress stopCode []) = some (Frame.ofCall (systemCallMsg ((benv true (some h)).withState st) consolidationRequestPredeployAddress stopCode []),initEvm (systemCallMsg ((benv true (some h)).withState st) consolidationRequestPredeployAddress stopCode [])) := by
  rfl


private theorem dFee_guard (h : B256) :
    (dFeeFrame h).sevm.caller = ordinaryAddr ∧ (dFeeFrame h).sevm.data = [] ∧
    (dFeeFrame h).sevm.value = 0 ∧ (dFeeFrame h).sevm.isStatic = true ∧
    (dFeeFrame h).post.output = (1 : B256).toBytes := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  exact (RequestFee.feeGetterPost_facts (feeBase (dFeeSevm h) (dFeeInit h)) .empty 1 (dFeeRem h) Mem.wf_empty (by decide)).1

private theorem dSub_guard (h : B256) :
    (dSubFrame h).sevm.caller = ordinaryAddr ∧ (dSubFrame h).sevm.data.length = 184 ∧
    (dSubFrame h).sevm.value = (10^18 + 1 : Nat).toB256 ∧ (dSubFrame h).sevm.isStatic = false := by
  refine ⟨rfl,?_,rfl,rfl⟩
  change (dSubSevm h).data.length = 184
  rw [dSubSevm_data,mem_read_fst,Array.sliceD_eq_map,List.length_map,List.length_range]

private theorem eFee_guard (h : B256) :
    (eFeeFrame h).sevm.caller = ordinaryAddr ∧ (eFeeFrame h).sevm.data = [] ∧
    (eFeeFrame h).sevm.value = 0 ∧ (eFeeFrame h).sevm.isStatic = true ∧
    (eFeeFrame h).post.output = (1 : B256).toBytes := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  exact (RequestFee.feeGetterPost_facts (feeBase (eFeeSevm h) (eFeeInit h)) .empty 1 (eFeeRem h) Mem.wf_empty (by decide)).1

private theorem eSub_guard (h : B256) :
    (eSubFrame h).sevm.caller = ordinaryAddr ∧ (eSubFrame h).sevm.data.length = 48 ∧
    (eSubFrame h).sevm.value = 1 ∧ (eSubFrame h).sevm.isStatic = false := by
  refine ⟨rfl,?_,rfl,rfl⟩
  change (eSubSevm h).data.length = 48
  rw [eSubSevm_data,mem_read_fst,Array.sliceD_eq_map,List.length_map,List.length_range]

private theorem dReset_guard (h : B256) :
    (dResetFrame h).sevm.caller = systemAddress ∧ (dResetFrame h).sevm.data = [] ∧
    (dResetFrame h).pre.getStorVal depositAddr 0 = B256.max ∧
    (dResetFrame h).pre.getOrigStorVal (dResetFrame h).sevm depositAddr 0 = 0 ∧
    (dResetFrame h).post.getStorVal depositAddr 0 = 0 := by
  refine ⟨rfl,rfl,?_,origStorVal_zero _ rfl depositAddr 0,(second_facts true (some h)).2.2.1⟩
  change ((initDevm (secondMsg true (some h))).state.getStor depositAddr).get 0 = B256.max
  rw [second_world]; exact (first_facts true (some h)).2.2

private theorem eReset_guard (h : B256) :
    (eResetFrame h).sevm.caller = systemAddress ∧ (eResetFrame h).sevm.data = [] ∧
    (eResetFrame h).pre.getStorVal exitAddr 0 = B256.max ∧
    (eResetFrame h).pre.getOrigStorVal (eResetFrame h).sevm exitAddr 0 = 0 ∧
    (eResetFrame h).post.getStorVal exitAddr 0 = 0 := by
  refine ⟨rfl,rfl,?_,origStorVal_zero _ rfl exitAddr 0,(exit_reset_facts h).2.2.2.1⟩
  change ((exitResetInit h).state.getStor exitAddr).get 0 = B256.max
  rw [exit_reset_init_state]; exact (exit_latch_facts h).2.2.1

private theorem dLatch_guard (h : B256) :
    (dLatchFrame h).sevm.caller = systemAddress ∧ (dLatchFrame h).sevm.data ≠ [] := by
  refine ⟨rfl,?_⟩
  change (firstMsg true (some h)).data ≠ []
  rw [first_data]
  decide +kernel

private theorem eLatch_guard (h : B256) :
    (eLatchFrame h).sevm.caller = systemAddress ∧ (eLatchFrame h).sevm.data ≠ [] := by
  refine ⟨rfl,?_⟩
  change (exitLatchMsg h).data ≠ []
  unfold exitLatchMsg
  rw [SystemWordWriter.childMsg_data]
  decide +kernel



private theorem history_stage : ∃ (cfg : ChainConfig) (start stop : BlockChain) (b : KeptBlock),
    KeptHistory cfg start [b] stop ∧ CodesKept cfg start [b] stop ∧ b.fork = .prague ∧
    b.run.senders = [(senderE,txD)] ∧ b.run.txRoots = [txRoot h0] ∧
    b.keptAt depositAddr = [dLatchFrame h0,dResetFrame h0,dFeeFrame h0,dSubFrame h0] ∧
    b.keptAt exitAddr = [eLatchFrame h0,eResetFrame h0,eFeeFrame h0,eSubFrame h0] := by
  have sc := state_codes h0
  obtain ⟨txSt, txBout, txRoots, gasLe, noDepLogs⟩ := tx_stage h0
  let inBenv := benv true (some h0)
  have ist : inBenv.state = state true (some h0) := rfl
  obtain ⟨outB, bCall⟩ := processUncheckedSystemTransaction_empty (benv := inBenv) CoveredFork.prague sc.2.2.1 (by decide)
  obtain ⟨outH, hCall⟩ := processUncheckedSystemTransaction_empty (benv := inBenv) (data := h0.toBytes) CoveredFork.prague sc.2.2.2.1 (by decide)
  let txEnv := inBenv.withState txSt
  have wKept : txSt.getCode withdrawalRequestPredeployAddress = stopCode :=
    (txRoots.chain (KeptFork.rules (Or.inl CoveredFork.prague))
      (by rw [ist, sc.2.2.2.2.1]; decide +kernel)
      (by rw [ist, sc.2.2.2.2.1]; intro bad; exact absurd bad.1 (by decide))
      AdrSet.not_mem_empty).2.trans sc.2.2.2.2.1
  have cKept : txSt.getCode consolidationRequestPredeployAddress = stopCode :=
    (txRoots.chain (KeptFork.rules (Or.inl CoveredFork.prague))
      (by rw [ist, sc.2.2.2.2.2]; decide +kernel)
      (by rw [ist, sc.2.2.2.2.2]; intro bad; exact absurd bad.1 (by decide))
      AdrSet.not_mem_empty).2.trans sc.2.2.2.2.2
  let wm := systemCallMsg txEnv withdrawalRequestPredeployAddress stopCode []
  have wStep : Evm.step (initEvm wm) = .halt (.ok (initDevm wm)) :=
    Evm.step_last (pc := 0) (sevm := initSevm wm) (devm := initDevm wm) (l := .stop)
      (by change Linst.At stopCode 0 .stop; unfold Linst.At; kernel_rfl)
  have wCall : processCheckedSystemTransaction txEnv withdrawalRequestPredeployAddress [] =
      .ok (txSt,systemCallOutput (initDevm wm)) :=
    processCheckedSystemTransaction_of_exec_nondelegated CoveredFork.prague wKept rfl
      (by change ¬ pragueRules.isPrecomp withdrawalRequestPredeployAddress; decide)
      (by decide +kernel)
      ((exec_iff_exec_eq _ _ _ _).mp ⟨Exec.halt wStep⟩) rfl (by change (0 : Int) ≤ 0; decide)
  let outW := systemCallOutput (initDevm wm)
  let cm := systemCallMsg txEnv consolidationRequestPredeployAddress stopCode []
  have cStep : Evm.step (initEvm cm) = .halt (.ok (initDevm cm)) :=
    Evm.step_last (pc := 0) (sevm := initSevm cm) (devm := initDevm cm) (l := .stop)
      (by change Linst.At stopCode 0 .stop; unfold Linst.At; kernel_rfl)
  have cCall : processCheckedSystemTransaction txEnv consolidationRequestPredeployAddress [] =
      .ok (txSt,systemCallOutput (initDevm cm)) :=
    processCheckedSystemTransaction_of_exec_nondelegated CoveredFork.prague cKept rfl
      (by change ¬ pragueRules.isPrecomp consolidationRequestPredeployAddress; decide)
      (by decide +kernel)
      ((exec_iff_exec_eq _ _ _ _).mp ⟨Exec.halt cStep⟩) rfl (by change (0 : Int) ≤ 0; decide)
  let outC := systemCallOutput (initDevm cm)
  have txApply : applyTransactions [txD].putIndex ((inBenv.withState inBenv.state).withState inBenv.state) .init = .ok (txEnv, txBout) := by
    change applyTransactions [(0, txD)] (benv true (some h0)) .init = _
    unfold applyTransactions; rw [txRoots.1]; rfl
  have bodyOk : applyBody inBenv [Sum.inr txD] [] [] =
      .ok (txSt, BlockForward.requestsOutput txBout outW.returnData outC.returnData) :=
    BlockForward.applyBody_forward CoveredFork.prague bCall rfl hCall rfl txApply noDepLogs wCall cCall
  have hB : beaconRootsCall inBenv.stat.rules inBenv = .ok (inBenv.state,({} : BalBuilder)) := by
    unfold beaconRootsCall
    simp only [show inBenv.stat.rules.sys.beaconRoots = true from rfl,ite_true,Except.mapError,bCall,bind,Except.bind]
    rfl
  have hH : historyStorageCall inBenv.stat.rules inBenv {} = .ok (inBenv.state,({} : BalBuilder)) := by
    unfold historyStorageCall
    simp only [show inBenv.stat.rules.sys.historyStorage = true from rfl,ite_true,
      show inBenv.stat.blockHashes.getLast? = some h0 from rfl,Option.toExcept,Except.mapError,hCall,bind,Except.bind]
    rfl
  obtain ⟨rb,rbPre⟩ := exists_beaconRoots hB
  obtain ⟨rh,rhPre⟩ := exists_historyRoots h0.toBytes (by rfl) hH
  obtain ⟨_,wr,wRoots⟩ := exists_systemRoots wCall
  obtain ⟨_,cr,cRoots⟩ := exists_systemRoots cCall
  let requests : List RequestStep := [⟨1,withdrawalRequestPredeployAddress,txSt,outW,wr⟩,
    ⟨2,consolidationRequestPredeployAddress,txSt,outC,cr⟩]
  have reqRoots : RequestRoots (txBout.receiptKeys.length + 1) pragueRequests txEnv txBout.requests txBout.bal txSt
      (txBout.requests ++ optionalRequestEntry 1 outW.returnData ++ optionalRequestEntry 2 outC.returnData)
      txBout.bal requests := by
    rw [BlockForward.pragueRequests_eq]
    exact .cons wCall wRoots (.cons cCall cRoots (.nil _ _ _))
  let run : BodyRun := ⟨inBenv.state,{},rb ++ rh,txEnv,txBout,[(senderE,txD)],[txRoot h0],requests⟩
  let finBout := BlockForward.requestsOutput txBout outW.returnData outC.returnData
  have bodyRoots : BodyRoots inBenv [Sum.inr txD] [] [] txSt finBout run := by
    refine ⟨bodyOk,?_,?_,?_⟩
    · exact ⟨inBenv.state,{},rb,rh,hB,rbPre,hH,rhPre,rfl⟩
    · refine ⟨[txD],rfl,?_⟩
      change TransactionsRoots [(0,txD)] (benv true (some h0)) .init txEnv txBout [(senderE,txD)] [txRoot h0]
      simpa only [List.append_nil] using TransactionsRoots.cons txRoots (TransactionsRoots.nil _ _)
    · have noWd : withdrawalsPass inBenv.stat.rules txEnv txBout [] = (txEnv.state,txBout) := by
        unfold withdrawalsPass
        rw [ite_eq_left (show inBenv.stat.rules.header.withdrawalsRoot = true from rfl)]
        unfold BalBuilder.incorporateSystem
        rw [show inBenv.stat.rules.bal = none from rfl]
        rfl
      change ∃ st out,RequestPass (txEnv.withState (withdrawalsPass inBenv.stat.rules txEnv txBout []).1)
        (withdrawalsPass inBenv.stat.rules txEnv txBout []).2 st out requests
      rw [noWd]
      change ∃ st out,RequestPass txEnv txBout st out requests
      refine ⟨txSt,{txBout with requests := txBout.requests ++ optionalRequestEntry 1 outW.returnData ++ optionalRequestEntry 2 outC.returnData},?_⟩
      unfold RequestPass
      rw [ite_eq_left (show txEnv.stat.rules.header.requestsHash = true from rfl)]
      exact ⟨[],txBout.requests ++ optionalRequestEntry 1 outW.returnData ++ optionalRequestEntry 2 outC.returnData,txBout.bal,noDepLogs,reqRoots,rfl⟩
  let cfg := ChainConfig.single 1 .prague
  let header := BlockForward.commitHeader Fork.prague.ruleSet parentBlock template txSt finBout
  let blk : Block := { header := header, txs := [Sum.inr txD], wds := [], ommers := [] }
  let stopChain : BlockChain := ⟨appendBlock startChain.blocks blk,txSt,1⟩
  let kb : KeptBlock := ⟨startChain,blk,.prague,finBout,run⟩
  have envEq : kb.benv = inBenv := block_context txSt finBout
  have hdrOk : validateHeader Fork.prague.ruleSet startChain header = .ok () :=
    BlockForward.commitHeader_ok CoveredFork.prague rfl rfl rfl
      (BlockForward.calculateBaseFeePerGas_unit (by decide) (by decide) (by decide) (by decide))
      rfl (Nat.le_trans gasLe (by decide)) (by decide) rfl rfl
  have forkAt : cfg.forkAt blk.header.number blk.header.timestamp = .ok .prague :=
    ChainConfig.single_forkAt 1 .prague _ _
  have step : KeptStep cfg kb stopChain :=
    ⟨BlockForward.stateTransitionUsing_forward rfl forkAt CoveredFork.prague hdrOk rfl
      (by change applyBody kb.benv [Sum.inr txD] [] [] = _; rw [envEq]; exact bodyOk)
      rfl rfl rfl rfl rfl rfl rfl rfl,
     forkAt,Or.inl CoveredFork.prague,
     by change BodyRoots kb.benv [Sum.inr txD] [] [] txSt finBout run; rw [envEq]; exact bodyRoots⟩
  have hist : KeptHistory cfg startChain [kb] stopChain := KeptHistory.step KeptHistory.refl step
  have codes : CodesKept cfg startChain [kb] stopChain := ⟨hist,sc.1,sc.2.1⟩
  let bm := systemCallMsg inBenv beaconRootsAddress ByteArray.empty (0 : B256).toBytes
  let hm := systemCallMsg inBenv historyStorageAddress ByteArray.empty h0.toBytes
  have bMsg : systemTransactionMessage inBenv beaconRootsAddress inBenv.stat.parentBeaconBlockRoot.toBytes = bm := by
    unfold systemTransactionMessage
    dsimp only [bm,systemCallMsg]
    have bc : inBenv.state.getCode beaconRootsAddress = ByteArray.empty := sc.2.2.1
    rw [bc]
    rfl
  have hMsg : systemTransactionMessage inBenv historyStorageAddress h0.toBytes = hm := by
    unfold systemTransactionMessage
    dsimp only [hm,systemCallMsg]
    have hc : inBenv.state.getCode historyStorageAddress = ByteArray.empty := sc.2.2.2.1
    rw [hc]
  have wMsg : systemTransactionMessage txEnv withdrawalRequestPredeployAddress [] = wm := by
    unfold systemTransactionMessage
    dsimp only [wm,systemCallMsg]
    change processSystemTransactionMsg _ _ _ _ (txSt.getCode withdrawalRequestPredeployAddress) = _
    rw [wKept]
  have cMsg : systemTransactionMessage txEnv consolidationRequestPredeployAddress [] = cm := by
    unfold systemTransactionMessage
    dsimp only [cm,systemCallMsg]
    change processSystemTransactionMsg _ _ _ _ (txSt.getCode consolidationRequestPredeployAddress) = _
    rw [cKept]
  have bEntry : messageEntry (systemTransactionMessage inBenv beaconRootsAddress inBenv.stat.parentBeaconBlockRoot.toBytes) =
      some (Frame.ofCall bm,initEvm bm) := by rw [bMsg]; exact beacon_message_entry h0
  have hEntry : messageEntry (systemTransactionMessage inBenv historyStorageAddress h0.toBytes) =
      some (Frame.ofCall hm,initEvm hm) := by rw [hMsg]; exact history_message_entry h0
  have wEntry : messageEntry (systemTransactionMessage txEnv withdrawalRequestPredeployAddress []) =
      some (Frame.ofCall wm,initEvm wm) := by rw [wMsg]; exact withdrawal_message_entry h0 txSt
  have cEntry : messageEntry (systemTransactionMessage txEnv consolidationRequestPredeployAddress []) =
      some (Frame.ofCall cm,initEvm cm) := by rw [cMsg]; exact consolidation_message_entry h0 txSt
  have bStep : Evm.step (initEvm bm) = .halt (.ok (initDevm bm)) :=
    Evm.step_last (pc := 0) (sevm := initSevm bm) (devm := initDevm bm) (l := .stop) rfl
  have hStep : Evm.step (initEvm hm) = .halt (.ok (initDevm hm)) :=
    Evm.step_last (pc := 0) (sevm := initSevm hm) (devm := initDevm hm) (l := .stop) rfl
  unfold PreCall at rbPre rhPre
  rw [ite_eq_left (show inBenv.stat.rules.sys.beaconRoots = true from rfl)] at rbPre
  rw [ite_eq_left (show inBenv.stat.rules.sys.historyStorage = true from rfl)] at rhPre
  obtain ⟨rbOut,rbRoots⟩ := rbPre
  obtain ⟨rhOut,rhRoots⟩ := rhPre
  have preNil (a : Adr) (ha : a = depositAddr ∨ a = exitAddr) :
      (rb ++ rh).flatMap (Root.keptAt a) = [] := by
    have bn := MessageRoots.keptAt_nil_of_entry_halt rbRoots bEntry bStep (a := a) (by
      rcases ha with rfl | rfl
      · change beaconRootsAddress ≠ depositAddr; decide
      · change beaconRootsAddress ≠ exitAddr; decide)
    have hn := MessageRoots.keptAt_nil_of_entry_halt rhRoots hEntry hStep (a := a) (by
      rcases ha with rfl | rfl
      · change historyStorageAddress ≠ depositAddr; decide
      · change historyStorageAddress ≠ exitAddr; decide)
    rw [List.flatMap_append,bn,hn,List.nil_append]
  have reqNil (a : Adr) (ha : a = depositAddr ∨ a = exitAddr) :
      (requestRootsOf requests).flatMap (Root.keptAt a) = [] := by
    have wn := MessageRoots.keptAt_nil_of_entry_halt wRoots wEntry wStep (a := a) (by
      rcases ha with rfl | rfl
      · change withdrawalRequestPredeployAddress ≠ depositAddr; decide
      · change withdrawalRequestPredeployAddress ≠ exitAddr; decide)
    have cn := MessageRoots.keptAt_nil_of_entry_halt cRoots cEntry cStep (a := a) (by
      rcases ha with rfl | rfl
      · change consolidationRequestPredeployAddress ≠ depositAddr; decide
      · change consolidationRequestPredeployAddress ≠ exitAddr; decide)
    simp only [requests,requestRootsOf,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.flatMap_append]
    rw [wn,cn,List.nil_append]
  have keptBoth (a : Adr) (ha : a = depositAddr ∨ a = exitAddr) : kb.keptAt a = (txRoot h0).keptAt a := by
    change ((rb ++ rh) ++ [txRoot h0] ++ requestRootsOf requests).flatMap (Root.keptAt a) = _
    rw [List.flatMap_append,List.flatMap_append,preNil a ha,reqNil a ha]
    simp only [List.nil_append,List.append_nil,List.flatMap_cons,List.flatMap_nil]
  have txCommits : Frame.settlementCommits (Frame.ofCall (msg true (some h0))) (.ok (writerEnd h0)) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits (by
      change (writerEnd h0).error.isNone = true
      rw [(ord_settle_resume h0).2.2.1.1]; rfl)
  have keptDep : kb.keptAt depositAddr = [dLatchFrame h0,dResetFrame h0,dFeeFrame h0,dSubFrame h0] := by
    rw [keptBoth depositAddr (Or.inl rfl)]
    unfold txRoot Root.keptAt
    rw [dite_eq_left txCommits,ite_eq_right (by change systemAddress ≠ depositAddr; decide)]
    exact (fullTxRun_kept h0).1
  have keptExit : kb.keptAt exitAddr = [eLatchFrame h0,eResetFrame h0,eFeeFrame h0,eSubFrame h0] := by
    rw [keptBoth exitAddr (Or.inr rfl)]
    unfold txRoot Root.keptAt
    rw [dite_eq_left txCommits,ite_eq_right (by change systemAddress ≠ exitAddr; decide)]
    exact (fullTxRun_kept h0).2
  exact ⟨cfg,startChain,stopChain,kb,hist,codes,rfl,rfl,rfl,keptDep,keptExit⟩


/-- **B-S2 all-eight-arms KeptHistory applicability witness.**
A single-block Prague `KeptHistory` satisfying `CodesKept` whose retained frames at `depositAddr`
are `[dLatch, dDequeue, dFee, dSub]` and at `exitAddr` are `[eLatch, eDequeue, eFee, eSub]`,
inhabiting all four disjoint arms of `DepositSettled` and all four disjoint arms of `ExitSettled`,
including dirty inhibitor-to-zero resets on both dequeues. -/
theorem b_s2_all_eight_arms_applicable :
    ∃ (cfg : ChainConfig) (start stop : BlockChain) (b : KeptBlock)
      (dLatch dDequeue dFee dSub eLatch eDequeue eFee eSub : Exec.Frame),
      KeptHistory cfg start [b] stop ∧ CodesKept cfg start [b] stop ∧ b.fork = .prague ∧
      b.keptAt depositAddr = [dLatch, dDequeue, dFee, dSub] ∧
      b.keptAt exitAddr = [eLatch, eDequeue, eFee, eSub] ∧
      Corpus.Freeze.Builder.DepositSettled b dLatch ∧ (dLatch.sevm.caller = systemAddress ∧ dLatch.sevm.data ≠ []) ∧
      Corpus.Freeze.Builder.DepositSettled b dDequeue ∧
      (dDequeue.sevm.caller = systemAddress ∧ dDequeue.sevm.data = [] ∧
        dDequeue.pre.getStorVal depositAddr 0 = B256.max ∧
        dDequeue.pre.getOrigStorVal dDequeue.sevm depositAddr 0 = 0 ∧
        dDequeue.post.getStorVal depositAddr 0 = 0) ∧
      Corpus.Freeze.Builder.DepositSettled b dFee ∧
      (dFee.sevm.caller ≠ systemAddress ∧ dFee.sevm.data = [] ∧
        dFee.sevm.isStatic = true ∧ dFee.post.output = (1 : B256).toBytes) ∧
      Corpus.Freeze.Builder.DepositSettled b dSub ∧
      (dSub.sevm.caller ≠ systemAddress ∧ dSub.sevm.data.length = 184 ∧ dSub.sevm.isStatic = false) ∧
      Corpus.Freeze.Builder.ExitSettled b eLatch ∧ (eLatch.sevm.caller = systemAddress ∧ eLatch.sevm.data ≠ []) ∧
      Corpus.Freeze.Builder.ExitSettled b eDequeue ∧
      (eDequeue.sevm.caller = systemAddress ∧ eDequeue.sevm.data = [] ∧
        eDequeue.pre.getStorVal exitAddr 0 = B256.max ∧
        eDequeue.pre.getOrigStorVal eDequeue.sevm exitAddr 0 = 0 ∧
        eDequeue.post.getStorVal exitAddr 0 = 0) ∧
      Corpus.Freeze.Builder.ExitSettled b eFee ∧
      (eFee.sevm.caller ≠ systemAddress ∧ eFee.sevm.data = [] ∧
        eFee.sevm.isStatic = true ∧ eFee.post.output = (1 : B256).toBytes) ∧
      Corpus.Freeze.Builder.ExitSettled b eSub ∧
      (eSub.sevm.caller ≠ systemAddress ∧ eSub.sevm.data.length = 48 ∧ eSub.sevm.isStatic = false) := by
  obtain ⟨cfg,start,stop,kb,hist,codes,forkAt,senders,txRoots,keptDep,keptExit⟩ := history_stage
  have clsD := fun f (hf : f ∈ kb.keptAt depositAddr) => BuilderRequestClassification.b_s2.1 codes kb (List.mem_singleton_self kb) f hf
  have clsE := fun f (hf : f ∈ kb.keptAt exitAddr) => BuilderRequestClassification.b_s2.2 codes kb (List.mem_singleton_self kb) f hf
  have ordinaryNotSystem : ordinaryAddr ≠ systemAddress := by decide +kernel
  refine ⟨cfg,start,stop,kb,
    dLatchFrame h0,dResetFrame h0,dFeeFrame h0,dSubFrame h0,
    eLatchFrame h0,eResetFrame h0,eFeeFrame h0,eSubFrame h0,
    hist,codes,forkAt,keptDep,keptExit,
    clsD _ (by rw [keptDep]; simp only [List.mem_cons,true_or]), dLatch_guard h0,
    clsD _ (by rw [keptDep]; simp only [List.mem_cons,true_or,or_true]), dReset_guard h0,
    clsD _ (by rw [keptDep]; simp only [List.mem_cons,true_or,or_true]),
    ⟨by rw [(dFee_guard h0).1]; exact ordinaryNotSystem,
      (dFee_guard h0).2.1,(dFee_guard h0).2.2.2.1,(dFee_guard h0).2.2.2.2⟩,
    clsD _ (by rw [keptDep]; simp only [List.mem_cons,true_or,or_true]),
    ⟨by rw [(dSub_guard h0).1]; exact ordinaryNotSystem,(dSub_guard h0).2.1,(dSub_guard h0).2.2.2⟩,
    clsE _ (by rw [keptExit]; simp only [List.mem_cons,true_or]), eLatch_guard h0,
    clsE _ (by rw [keptExit]; simp only [List.mem_cons,true_or,or_true]), eReset_guard h0,
    clsE _ (by rw [keptExit]; simp only [List.mem_cons,true_or,or_true]),
    ⟨by rw [(eFee_guard h0).1]; exact ordinaryNotSystem,
      (eFee_guard h0).2.1,(eFee_guard h0).2.2.2.1,(eFee_guard h0).2.2.2.2⟩,
    clsE _ (by rw [keptExit]; simp only [List.mem_cons,true_or,or_true]),
    ⟨by rw [(eSub_guard h0).1]; exact ordinaryNotSystem,(eSub_guard h0).2.1,(eSub_guard h0).2.2.2⟩⟩


end Blanc.Composition.BuilderRequestApplicabilityHistory
