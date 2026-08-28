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

private def statcallStep : XStep :=
  Xinst.step dynamicSevm directStatcallPre .statcall
private def statcallFrame : Frame := spawnedFrame statcallStep
private def statcallResume : Resume := spawnedResume statcallStep

private def callcodeStep : XStep :=
  Xinst.step dynamicSevm callcodePre .callcode
private def callcodeFrame : Frame := spawnedFrame callcodeStep
private def callcodeResume : Resume := spawnedResume callcodeStep

private def delegatecallStep : XStep :=
  Xinst.step dynamicSevm delegatecallPre .delcall
private def delegatecallFrame : Frame := spawnedFrame delegatecallStep
private def delegatecallResume : Resume := spawnedResume delegatecallStep

macro "dca_kernel_decide" : tactic => `(tactic|
  (simp [spawned, spawnedFrame, spawnedResume, callStep, statcallStep,
      callcodeStep, delegatecallStep,
      callFrame, callResume, statcallFrame, statcallResume,
      callcodeFrame, callcodeResume, delegatecallFrame, delegatecallResume,
      directCallPre, directStatcallPre, callcodePre,
      delegatecallPre, dynamicSevm, addressA, addressB, targetCode, parentCode,
      Xinst.step, genericCall.step, genericCreate.step, callMsg, createMsg,
      default, Prod.mapFst, Devm.pop_def, Devm.popToAdr_def,
      Devm.popToNat_def, Devm.withStack, Devm.withGasLeft, Devm.setCode,
      Devm.withState, Devm.withReturnData, Devm.withMemory, Devm.setMach,
      Devm.setMeta, Devm.setWorld, Devm.getAcct, State.setCode, Acct.nil,
      Devm.stack, Devm.memory, Devm.gasLeft, Devm.state,
      Devm.accessedAddresses, State.set, State.get, accessDelegation,
      getDelegatedCodeAddress, addAccessedAddress, Meta.addAccessedAddress,
      liftMachMetaPure, accessCost, Devm.extCost, Devm.memExtends,
      Mem.extends, chargeGas, safeSub, calculateMsgCallGas, except64th,
      Std.TreeMap.getD_emptyc, Std.TreeMap.getD_insert,
      Std.TreeMap.getD_erase]
    <;> decide))

private theorem eq_spawn_of_spawned (step : XStep)
    (h : spawned step = true) :
    step = .spawn (spawnedFrame step) (spawnedResume step) := by
  cases step <;> simp [spawned, spawnedFrame, spawnedResume] at h ⊢

private theorem call_spawn :
    Xinst.step dynamicSevm directCallPre .call =
      .spawn callFrame callResume := by
  exact eq_spawn_of_spawned callStep (by dca_kernel_decide)

/-- A concrete foreign CALL with nonempty installed target code inhabits the
common theorem and obtains its exact child code address from that theorem. -/
theorem call_direct_codeAddress_control :
    Xinst.step dynamicSevm directCallPre .call =
        .spawn callFrame callResume ∧
      dynamicSevm.currentTarget ≠ callFrame.inner.currentTarget ∧
      directCallPre.getCode callFrame.inner.currentTarget ≠ .empty ∧
      callFrame.inner.codeAddress = some callFrame.inner.currentTarget := by
  refine ⟨call_spawn, by dca_kernel_decide, by dca_kernel_decide, ?_⟩
  exact Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget
    call_spawn (by dca_kernel_decide) (by dca_kernel_decide)
    (by dca_kernel_decide)

private theorem statcall_spawn :
    Xinst.step dynamicSevm directStatcallPre .statcall =
      .spawn statcallFrame statcallResume := by
  exact eq_spawn_of_spawned statcallStep (by dca_kernel_decide)

/-- A concrete foreign STATICCALL is the second positive direct-code control. -/
theorem statcall_direct_codeAddress_control :
    Xinst.step dynamicSevm directStatcallPre .statcall =
        .spawn statcallFrame statcallResume ∧
      dynamicSevm.currentTarget ≠ statcallFrame.inner.currentTarget ∧
      directStatcallPre.getCode statcallFrame.inner.currentTarget ≠ .empty ∧
      statcallFrame.inner.codeAddress = some statcallFrame.inner.currentTarget := by
  refine ⟨statcall_spawn, by dca_kernel_decide, by dca_kernel_decide, ?_⟩
  exact Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget
    statcall_spawn (by dca_kernel_decide) (by dca_kernel_decide)
    (by dca_kernel_decide)

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
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
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
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
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

private theorem callcode_spawn :
    Xinst.step dynamicSevm callcodePre .callcode =
      .spawn callcodeFrame callcodeResume := by
  exact eq_spawn_of_spawned callcodeStep (by dca_kernel_decide)

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
  exact ⟨callcode_spawn, by dca_kernel_decide, by dca_kernel_decide,
    by dca_kernel_decide, by dca_kernel_decide⟩

private theorem delegatecall_spawn :
    Xinst.step dynamicSevm delegatecallPre .delcall =
      .spawn delegatecallFrame delegatecallResume := by
  exact eq_spawn_of_spawned delegatecallStep (by dca_kernel_decide)

/-- DELEGATECALL exposes the same retained-target boundary independently. -/
theorem delegatecall_same_target_control :
    Xinst.step dynamicSevm delegatecallPre .delcall =
        .spawn delegatecallFrame delegatecallResume ∧
      delegatecallFrame.inner.currentTarget = dynamicSevm.currentTarget ∧
      delegatecallPre.getCode delegatecallFrame.inner.currentTarget ≠ .empty ∧
      delegatecallFrame.inner.codeAddress = some addressB ∧
      delegatecallFrame.inner.codeAddress ≠
        some delegatecallFrame.inner.currentTarget := by
  exact ⟨delegatecall_spawn, by dca_kernel_decide, by dca_kernel_decide,
    by dca_kernel_decide, by dca_kernel_decide⟩

/-- Keeps the exact six boundary statements live as one typed conjunction. -/
theorem required_positive_controls :
    (Xinst.step dynamicSevm directCallPre .call =
          .spawn callFrame callResume ∧
        dynamicSevm.currentTarget ≠ callFrame.inner.currentTarget ∧
        directCallPre.getCode callFrame.inner.currentTarget ≠ .empty ∧
        callFrame.inner.codeAddress = some callFrame.inner.currentTarget) ∧
    (Xinst.step dynamicSevm directStatcallPre .statcall =
          .spawn statcallFrame statcallResume ∧
        dynamicSevm.currentTarget ≠ statcallFrame.inner.currentTarget ∧
        directStatcallPre.getCode statcallFrame.inner.currentTarget ≠ .empty ∧
        statcallFrame.inner.codeAddress = some statcallFrame.inner.currentTarget) ∧
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
    (Xinst.step dynamicSevm delegatecallPre .delcall =
          .spawn delegatecallFrame delegatecallResume ∧
        delegatecallFrame.inner.currentTarget = dynamicSevm.currentTarget ∧
        delegatecallPre.getCode delegatecallFrame.inner.currentTarget ≠ .empty ∧
        delegatecallFrame.inner.codeAddress = some addressB ∧
        delegatecallFrame.inner.codeAddress ≠
          some delegatecallFrame.inner.currentTarget) := by
  exact ⟨call_direct_codeAddress_control, statcall_direct_codeAddress_control,
    @create_empty_target_control, @create2_empty_target_control,
    callcode_same_target_control, delegatecall_same_target_control⟩

-- DIRECT-CODE-HCODE-MUTANT-CONTROL
-- DIRECT-CODE-HFOREIGN-MUTANT-CONTROL

end Blanc.ExecutionOccurrenceControls
