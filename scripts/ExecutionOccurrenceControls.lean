import Blanc.ExecutionOccurrence

/-!
Concrete controls for the common direct spawned-code-address theorem. Every
row is tied to an actual `Xinst.step` spawn. CALL and STATICCALL inhabit the
theorem; CREATE/CREATE2 expose the empty installed target-code boundary; and
CALLCODE/DELEGATECALL expose the retained storage-target boundary.
-/

namespace Blanc.ExecutionOccurrenceControls

open Jaune Blanc

set_option maxHeartbeats 1000000

private def addressA : Adr :=
  0x0000000000000000000000000000000000000a01
private def addressB : Adr :=
  0x0000000000000000000000000000000000000b02

private def targetCode : ByteArray := ByteArray.mk #[0x00]
private def parentCode : ByteArray := ByteArray.mk #[0x5b, 0x00]

private def dynamicSevm : Sevm :=
  { (default : Sevm) with
      currentTarget := addressA
      depth := 4
      isStatic := false }

private def directCallPre : Devm :=
  (((default : Devm).setCode addressB targetCode).withGasLeft 100000)
    |>.withStack [50000, addressB.toB256, 0, 0, 0, 0, 0]

private def directStatcallPre : Devm :=
  (((default : Devm).setCode addressB targetCode).withGasLeft 100000)
    |>.withStack [50000, addressB.toB256, 0, 0, 0, 0]

private def callcodePre : Devm :=
  ((((default : Devm).setCode addressA parentCode).setCode addressB targetCode)
      |>.withGasLeft 100000)
    |>.withStack [50000, addressB.toB256, 0, 0, 0, 0, 0]

private def delegatecallPre : Devm :=
  ((((default : Devm).setCode addressA parentCode).setCode addressB targetCode)
      |>.withGasLeft 100000)
    |>.withStack [50000, addressB.toB256, 0, 0, 0, 0]

private def spawned : XStep → Bool
  | .spawn _ _ => true
  | _ => false

private def spawnedFrame : XStep → Frame
  | .spawn frame _ => frame
  | _ => Frame.ofCall default

private def spawnedResume : XStep → Resume
  | .spawn _ resume => resume
  | _ => .call default 0 0

private def callStep : XStep := Xinst.step dynamicSevm directCallPre .call
private def callFrame : Frame := spawnedFrame callStep
private def callResume : Resume := spawnedResume callStep

private def staticcallStep : XStep :=
  Xinst.step dynamicSevm directStatcallPre .staticcall
private def staticcallFrame : Frame := spawnedFrame staticcallStep
private def staticcallResume : Resume := spawnedResume staticcallStep

private def callcodeStep : XStep :=
  Xinst.step dynamicSevm callcodePre .callcode
private def callcodeFrame : Frame := spawnedFrame callcodeStep
private def callcodeResume : Resume := spawnedResume callcodeStep

private def delegatecallStep : XStep :=
  Xinst.step dynamicSevm delegatecallPre .delegatecall
private def delegatecallFrame : Frame := spawnedFrame delegatecallStep
private def delegatecallResume : Resume := spawnedResume delegatecallStep

private theorem eq_spawn_of_spawned (step : XStep)
    (h : spawned step = true) :
    step = .spawn (spawnedFrame step) (spawnedResume step) := by
  cases step <;> simp only [spawned, spawnedFrame, spawnedResume, Bool.false_eq_true] at h ⊢

private theorem call_spawn :
    Xinst.step dynamicSevm directCallPre .call =
      .spawn callFrame callResume := by
  exact eq_spawn_of_spawned callStep (by simp only [spawned, callStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, directCallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.getAcct, Devm.extCost, Devm.memory, except64th, Except.assert, Bool.not_false, true_or, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, Except.bind_ok, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, or_true, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false] <;> decide)

/-- A concrete foreign CALL with nonempty installed target code inhabits the
common theorem and obtains its exact child code address from that theorem. -/
theorem call_direct_codeAddress_control :
    Xinst.step dynamicSevm directCallPre .call =
        .spawn callFrame callResume ∧
      dynamicSevm.currentTarget ≠ callFrame.inner.currentTarget ∧
      directCallPre.getCode callFrame.inner.currentTarget ≠ .empty ∧
      callFrame.inner.codeAddress = some callFrame.inner.currentTarget := by
  refine ⟨call_spawn, by simp only [dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, callFrame, spawnedFrame, callStep, Xinst.step, BenvStat.rules, Fork.ruleSet, pragueRules, pragueGasSchedule, XStep.ofExcept, directCallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.getAcct, Devm.extCost, Devm.memory, except64th, Except.assert, Bool.not_false, true_or, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, Except.bind_ok, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, or_true, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide, by simp only [directCallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, default, Std.TreeMap.empty_eq_emptyc, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, callFrame, spawnedFrame, callStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.getAcct, Devm.extCost, Devm.memory, except64th, Except.assert, Bool.not_false, true_or, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, Except.bind_ok, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, or_true, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide, ?_⟩
  exact Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget
    call_spawn (by simp only [dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, callFrame, spawnedFrame, callStep, Xinst.step, BenvStat.rules, Fork.ruleSet, pragueRules, pragueGasSchedule, XStep.ofExcept, directCallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.getAcct, Devm.extCost, Devm.memory, except64th, Except.assert, Bool.not_false, true_or, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, Except.bind_ok, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, or_true, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide) (by simp only [directCallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, default, Std.TreeMap.empty_eq_emptyc, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, callFrame, spawnedFrame, callStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.getAcct, Devm.extCost, Devm.memory, except64th, Except.assert, Bool.not_false, true_or, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, Except.bind_ok, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, or_true, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide)
    (by simp only [getDelegatedCodeAddress, directCallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, default, Std.TreeMap.empty_eq_emptyc, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, callFrame, spawnedFrame, callStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.getAcct, Devm.extCost, Devm.memory, except64th, Except.assert, Bool.not_false, true_or, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, Except.bind_ok, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, or_true, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false, ite_eq_right_iff] <;> decide)

private theorem staticcall_spawn :
    Xinst.step dynamicSevm directStatcallPre .staticcall =
      .spawn staticcallFrame staticcallResume := by
  exact eq_spawn_of_spawned staticcallStep (by simp only [spawned, staticcallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, directStatcallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_false, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false] <;> decide)

/-- A concrete foreign STATICCALL is the second positive direct-code control. -/
theorem staticcall_direct_codeAddress_control :
    Xinst.step dynamicSevm directStatcallPre .staticcall =
        .spawn staticcallFrame staticcallResume ∧
      dynamicSevm.currentTarget ≠ staticcallFrame.inner.currentTarget ∧
      directStatcallPre.getCode staticcallFrame.inner.currentTarget ≠ .empty ∧
      staticcallFrame.inner.codeAddress = some staticcallFrame.inner.currentTarget := by
  refine ⟨staticcall_spawn, by simp only [dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, staticcallFrame, spawnedFrame, staticcallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, pragueRules, pragueGasSchedule, XStep.ofExcept, directStatcallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_false, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide, by simp only [directStatcallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, default, Std.TreeMap.empty_eq_emptyc, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, staticcallFrame, spawnedFrame, staticcallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_false, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide, ?_⟩
  exact Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget
    staticcall_spawn (by simp only [dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, staticcallFrame, spawnedFrame, staticcallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, pragueRules, pragueGasSchedule, XStep.ofExcept, directStatcallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_false, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide) (by simp only [directStatcallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, default, Std.TreeMap.empty_eq_emptyc, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, staticcallFrame, spawnedFrame, staticcallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_false, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide)
    (by simp only [getDelegatedCodeAddress, directStatcallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, default, Std.TreeMap.empty_eq_emptyc, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, targetCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, List.cons_ne_self, and_false, ↓reduceIte, staticcallFrame, spawnedFrame, staticcallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_false, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false, ite_eq_right_iff] <;> decide)

/-- Every actual CREATE spawn has empty installed target code and no direct
code address. This kernel proof avoids evaluating the CREATE address hash. -/
theorem create_empty_target_control
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (hs : Xinst.step sevm devm .create = .spawn frame resume) :
    devm.getCode frame.inner.currentTarget = .empty ∧
      frame.inner.codeAddress = none := by
  have horig := hs
  simp only [Xinst.step, Bind.bind, Except.bind] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, Pure.pure, Except.pure, reduceCtorEq] at hs
  all_goals first
    | cases hs
    | have hfresh := genericCreate.step_spawn_frame hs
      constructor
      · calc
          devm.getCode frame.inner.currentTarget =
              frame.inner.benv.state.getCode frame.inner.currentTarget :=
            (Xinst.step_spawn_getCode horig _).symm
          _ = _ := hfresh.1 _
          _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
      · have hshape := hs
        simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
          assertDynamic, Pure.pure, Except.pure] at hshape
        repeat' split at hshape
        all_goals
          simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hshape
        all_goals obtain ⟨rfl, rfl⟩ := hshape
        all_goals rfl
    | have hfresh := genericCreateAmsterdam.step_spawn_frame hs
      constructor
      · calc
          devm.getCode frame.inner.currentTarget =
              frame.inner.benv.state.getCode frame.inner.currentTarget :=
            (Xinst.step_spawn_getCode horig _).symm
          _ = _ := hfresh.1 _
          _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
      · have hshape := hs
        simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at hshape
        repeat' split at hshape
        all_goals
          simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hshape
        all_goals obtain ⟨rfl, rfl⟩ := hshape
        all_goals rfl

/-- Every actual CREATE2 spawn has the same empty-code/no-direct-address
boundary as CREATE. -/
theorem create2_empty_target_control
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (hs : Xinst.step sevm devm .create2 = .spawn frame resume) :
    devm.getCode frame.inner.currentTarget = .empty ∧
      frame.inner.codeAddress = none := by
  have horig := hs
  simp only [Xinst.step, Bind.bind, Except.bind] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, Pure.pure, Except.pure, reduceCtorEq] at hs
  all_goals first
    | cases hs
    | have hfresh := genericCreate.step_spawn_frame hs
      constructor
      · calc
          devm.getCode frame.inner.currentTarget =
              frame.inner.benv.state.getCode frame.inner.currentTarget :=
            (Xinst.step_spawn_getCode horig _).symm
          _ = _ := hfresh.1 _
          _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
      · have hshape := hs
        simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
          assertDynamic, Pure.pure, Except.pure] at hshape
        repeat' split at hshape
        all_goals
          simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hshape
        all_goals obtain ⟨rfl, rfl⟩ := hshape
        all_goals rfl
    | have hfresh := genericCreateAmsterdam.step_spawn_frame hs
      constructor
      · calc
          devm.getCode frame.inner.currentTarget =
              frame.inner.benv.state.getCode frame.inner.currentTarget :=
            (Xinst.step_spawn_getCode horig _).symm
          _ = _ := hfresh.1 _
          _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
      · have hshape := hs
        simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at hshape
        repeat' split at hshape
        all_goals
          simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hshape
        all_goals obtain ⟨rfl, rfl⟩ := hshape
        all_goals rfl

private theorem callcode_spawn :
    Xinst.step dynamicSevm callcodePre .callcode =
      .spawn callcodeFrame callcodeResume := by
  exact eq_spawn_of_spawned callcodeStep (by simp only [spawned, callcodeStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, callcodePre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, except64th, Devm.getAcct, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, Except.bind_ok, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false] <;> decide)

/-- CALLCODE can execute code at `addressB`, but retains the parent's storage
target `addressA`; the nonempty-code premise holds while the foreign-target
premise and direct-code conclusion both fail. -/
theorem callcode_same_target_control :
    Xinst.step dynamicSevm callcodePre .callcode =
        .spawn callcodeFrame callcodeResume ∧
      callcodeFrame.inner.currentTarget = dynamicSevm.currentTarget ∧
      callcodePre.getCode callcodeFrame.inner.currentTarget ≠ .empty ∧
      callcodeFrame.inner.codeAddress = some addressB ∧
      callcodeFrame.inner.codeAddress ≠ some callcodeFrame.inner.currentTarget := by
  exact ⟨callcode_spawn, by simp only [callcodeFrame, spawnedFrame, callcodeStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, callcodePre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, except64th, Devm.getAcct, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, Except.bind_ok, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false] <;> decide, by simp only [callcodePre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, default, Std.TreeMap.empty_eq_emptyc, State.setCode, State.set, State.get, Devm.state, addressA, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, callcodeFrame, spawnedFrame, callcodeStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, pragueRules, pragueGasSchedule, XStep.ofExcept, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, except64th, Devm.getAcct, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, Except.bind_ok, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide,
    by simp only [callcodeFrame, spawnedFrame, callcodeStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, callcodePre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, except64th, Devm.getAcct, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, Except.bind_ok, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false] <;> decide, by simp only [callcodeFrame, spawnedFrame, callcodeStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, callcodePre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, except64th, Devm.getAcct, Devm.memExtends, Devm.withReturnData, Devm.setMeta, bind_pure_comp, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Nat.add_one_sub_one, Bool.or_self, bind_map_left, Prod.map_snd, id_eq, Prod.map_fst, Except.bind_ok, add_zero, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide⟩

private theorem delegatecall_spawn :
    Xinst.step dynamicSevm delegatecallPre .delegatecall =
      .spawn delegatecallFrame delegatecallResume := by
  exact eq_spawn_of_spawned delegatecallStep (by simp only [spawned, delegatecallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, delegatecallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_self, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false] <;> decide)

/-- DELEGATECALL exposes the same retained-target boundary independently. -/
theorem delegatecall_same_target_control :
    Xinst.step dynamicSevm delegatecallPre .delegatecall =
        .spawn delegatecallFrame delegatecallResume ∧
      delegatecallFrame.inner.currentTarget = dynamicSevm.currentTarget ∧
      delegatecallPre.getCode delegatecallFrame.inner.currentTarget ≠ .empty ∧
      delegatecallFrame.inner.codeAddress = some addressB ∧
      delegatecallFrame.inner.codeAddress ≠
        some delegatecallFrame.inner.currentTarget := by
  exact ⟨delegatecall_spawn, by simp only [delegatecallFrame, spawnedFrame, delegatecallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, delegatecallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_self, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false] <;> decide, by simp only [delegatecallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, default, Std.TreeMap.empty_eq_emptyc, State.setCode, State.set, State.get, Devm.state, addressA, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, delegatecallFrame, spawnedFrame, delegatecallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, pragueRules, pragueGasSchedule, XStep.ofExcept, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_self, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide,
    by simp only [delegatecallFrame, spawnedFrame, delegatecallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, delegatecallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_self, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false] <;> decide, by simp only [delegatecallFrame, spawnedFrame, delegatecallStep, Xinst.step, BenvStat.rules, Fork.ruleSet, dynamicSevm, default, Std.TreeMap.empty_eq_emptyc, addressA, pragueRules, pragueGasSchedule, XStep.ofExcept, delegatecallPre, Devm.withStack, Devm.setMach, addressB, Devm.withGasLeft, Devm.setCode, Devm.withState, Devm.setWorld, State.setCode, State.set, State.get, Devm.state, Acct.nil, Std.TreeMap.getD_emptyc, parentCode, Acct.mk.injEq, ByteArray.mk.injEq, Array.mk.injEq, reduceCtorEq, and_false, ↓reduceIte, Std.TreeMap.getD_insert, Std.LawfulEqCmp.compare_eq_iff_eq, targetCode, List.cons_ne_self, Devm.pop_def, Devm.stack, Devm.popToAdr_def, Prod.mapFst, Devm.popToNat_def, chargeGas, calculateMsgCallGas, Devm.gasLeft, GasSchedule.accessDelegation, getDelegatedCodeAddress, addAccessedAddress, liftMachMetaPure, Meta.addAccessedAddress, GasSchedule.accessCost, Devm.accessedAddresses, Std.HashSet.mem_insert, beq_iff_eq, Devm.extCost, Devm.memory, add_zero, except64th, genericCall.step, OfNat.ofNat_ne_zero, callMsg, Devm.withReturnData, Devm.setMeta, Devm.memExtends, Nat.add_one_sub_one, Bool.or_self, bind_pure_comp, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq, Except.bind_ok, Std.HashSet.not_mem_emptyWithCapacity, or_false, ne_eq] <;> decide⟩

/-- Keeps the exact six boundary statements live as one typed conjunction. -/
theorem required_positive_controls :
    (Xinst.step dynamicSevm directCallPre .call =
          .spawn callFrame callResume ∧
        dynamicSevm.currentTarget ≠ callFrame.inner.currentTarget ∧
        directCallPre.getCode callFrame.inner.currentTarget ≠ .empty ∧
        callFrame.inner.codeAddress = some callFrame.inner.currentTarget) ∧
    (Xinst.step dynamicSevm directStatcallPre .staticcall =
          .spawn staticcallFrame staticcallResume ∧
        dynamicSevm.currentTarget ≠ staticcallFrame.inner.currentTarget ∧
        directStatcallPre.getCode staticcallFrame.inner.currentTarget ≠ .empty ∧
        staticcallFrame.inner.codeAddress = some staticcallFrame.inner.currentTarget) ∧
    (∀ {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume},
      Xinst.step sevm devm .create = .spawn frame resume →
        devm.getCode frame.inner.currentTarget = .empty ∧
          frame.inner.codeAddress = none) ∧
    (∀ {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume},
      Xinst.step sevm devm .create2 = .spawn frame resume →
        devm.getCode frame.inner.currentTarget = .empty ∧
          frame.inner.codeAddress = none) ∧
    (Xinst.step dynamicSevm callcodePre .callcode =
          .spawn callcodeFrame callcodeResume ∧
        callcodeFrame.inner.currentTarget = dynamicSevm.currentTarget ∧
        callcodePre.getCode callcodeFrame.inner.currentTarget ≠ .empty ∧
        callcodeFrame.inner.codeAddress = some addressB ∧
        callcodeFrame.inner.codeAddress ≠
          some callcodeFrame.inner.currentTarget) ∧
    (Xinst.step dynamicSevm delegatecallPre .delegatecall =
          .spawn delegatecallFrame delegatecallResume ∧
        delegatecallFrame.inner.currentTarget = dynamicSevm.currentTarget ∧
        delegatecallPre.getCode delegatecallFrame.inner.currentTarget ≠ .empty ∧
        delegatecallFrame.inner.codeAddress = some addressB ∧
        delegatecallFrame.inner.codeAddress ≠
          some delegatecallFrame.inner.currentTarget) := by
  exact ⟨call_direct_codeAddress_control, staticcall_direct_codeAddress_control,
    @create_empty_target_control, @create2_empty_target_control,
    callcode_same_target_control, delegatecall_same_target_control⟩

-- DIRECT-CODE-HCODE-MUTANT-CONTROL
-- DIRECT-CODE-HFOREIGN-MUTANT-CONTROL

end Blanc.ExecutionOccurrenceControls
