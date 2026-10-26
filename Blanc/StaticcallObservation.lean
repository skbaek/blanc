import Blanc.Lift.CallChildren
import Blanc.Lift.TargetLogEvents

/-!
# Actual STATICCALL observations on every outcome

The dispatch, original recursive slot and raw/settled boundary are retained
before looking at a success flag or returndata. A synchronous native invocation
is different from an instruction that never spawned a frame.
-/

namespace Blanc

open Jaune

/-- Every actual STATICCALL spawn selects a call frame with zero value. -/
theorem Xinst.step_staticcall_spawn_frame_zero
    {sevm : Sevm} {pre : Devm} {frame : Frame} {resume : Resume}
    (spawn : Xinst.step sevm pre .staticcall = .spawn frame resume) :
    frame = Frame.ofCall frame.inner ∧ frame.inner.value = 0 := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals
    first
      | cases spawn
      | rw [(genericCall_step_spawn_exact spawn).1]; exact ⟨rfl, rfl⟩
      | rw [(genericCallAmsterdam_step_spawn_exact spawn).1]; exact ⟨rfl, rfl⟩

/-- The exact entered route, with synchronous native execution kept distinct
from its absent VM slot. Raw and settled outcomes are unrestricted. -/
inductive StaticcallRouting (msg : Msg) (slot : Xlot)
    (settled : Except (EvmError × State × AdrSet × Tra) Devm) : Prop
  | native (address : Adr) (raw : Execution)
      (codeAddress : msg.codeAddress = some address)
      (enabled : msg.disablePrecompiles = false)
      (active : msg.benv.stat.rules.isPrecomp address)
      (execution : executeCode.enter msg = .inr raw)
      (rawNative : raw = executePrecomp (initEvm msg) address)
      (entry : (Frame.ofCall msg).enter = .done ((Frame.ofCall msg).settle raw))
      (originalSlot : slot = .none)
      (settlement : settled = (Frame.ofCall msg).settle raw)
  | vm (child : Evm) (raw : Execution)
      (entry : (Frame.ofCall msg).enter = .run child)
      (originalSlot : slot = .some ⟨child, raw⟩)
      (execution : Exec child.pc child.sta child.dyna raw)
      (settlement : settled = (Frame.ofCall msg).settle raw)

/-- Zero-value STATICCALL entry always crosses its transfer. A done entry is
therefore the actual enabled precompile, not a transfer-error shortcut. -/
theorem staticcall_routing_of_process
    {msg : Msg} {slot : Xlot}
    {settled : Except (EvmError × State × AdrSet × Tra) Devm}
    (zero : msg.value = 0) (filled : slot.Filled)
    (process : ProcessMessage msg slot settled) :
    StaticcallRouting msg slot settled := by
  have transfer := Msg.benvAfterTransfer_of_value_zero zero
  have enter : (Frame.ofCall msg).enter =
      match executeCode.enter msg with
      | .inl child => .run child
      | .inr raw => .done ((Frame.ofCall msg).settle raw) := by
    unfold Frame.enter Frame.ofCall
    rw [transfer]
    rfl
  cases execution : executeCode.enter msg with
  | inl child =>
      have entry : (Frame.ofCall msg).enter = .run child := by rw [enter, execution]
      change RunFrame (Frame.ofCall msg) slot settled at process
      rw [RunFrame, entry] at process
      obtain ⟨raw, originalSlot, settlement⟩ := process
      rw [originalSlot] at filled
      obtain ⟨actual⟩ := filled
      exact .vm child raw entry originalSlot actual settlement
  | inr raw =>
      have entry : (Frame.ofCall msg).enter =
          .done ((Frame.ofCall msg).settle raw) := by rw [enter, execution]
      change RunFrame (Frame.ofCall msg) slot settled at process
      rw [RunFrame, entry] at process
      obtain ⟨originalSlot, settlement⟩ := process
      obtain ⟨address, codeAddress, enabled, active⟩ := executeCode.enter_inr_routing execution
      have rawNative : raw = executePrecomp (initEvm msg) address := by
        have actual := execution
        simp only [executeCode.enter, codeAddress, enabled, Bool.not_false,
          Bool.true_and, decide_eq_true active, ↓reduceIte] at actual
        exact (Sum.inr.inj actual).symm
      exact .native address raw codeAddress enabled active execution rawNative entry
        originalSlot settlement

/-- Per-instruction observation: no invocation, or the exact entered message
and its actual native/VM route. No success flag or output filter is applied. -/
def StaticcallObservation (pc : Nat) (sevm : Sevm) (pre : Devm)
    (slot : Xlot) (out : Execution) : Prop :=
  (∃ raw, Xinst.step sevm pre .staticcall = .done raw ∧
    slot = .none ∧ out = raw) ∨
  ∃ (msg : Msg) (resume : Resume)
    (settled : Except (EvmError × State × AdrSet × Tra) Devm),
    Ninst.step ⟨pc, sevm, pre⟩ Ninst.staticcall =
      .spawn (Frame.ofCall msg) resume (pc + 1) ∧
    msg.value = 0 ∧ msg.isStatic = true ∧ msg.caller = sevm.currentTarget ∧
    ProcessMessage msg slot settled ∧ resume.run settled = out ∧
    StaticcallRouting msg slot settled

/-- Actual STATICCALL dispatch determines the full observation on every result. -/
theorem Ninst.staticcall_observation
    {pc : Nat} {sevm : Sevm} {pre : Devm} {slot : Xlot} {out : Execution}
    (filled : slot.Filled)
    (run : Ninst.StepRun pc sevm pre Ninst.staticcall slot out) :
    StaticcallObservation pc sevm pre slot out := by
  have driver : XStep.Run (Xinst.step sevm pre .staticcall) slot out := by
    exact XStep.run_toStep.mp run
  cases dispatch : Xinst.step sevm pre .staticcall with
  | done raw =>
      rw [dispatch] at driver
      exact Or.inl ⟨raw, dispatch, driver⟩
  | spawn frame resume =>
      rw [dispatch] at driver
      obtain ⟨settled, process, resumed⟩ := driver
      obtain ⟨frameEq, zero⟩ := Xinst.step_staticcall_spawn_frame_zero dispatch
      have forcedStatic := Xinst.step_staticcall_spawn_isStatic dispatch
      have caller := Xinst.step_staticcall_spawn_caller dispatch
      have exactProcess : ProcessMessage frame.inner slot settled := by
        change RunFrame (Frame.ofCall frame.inner) slot settled
        rw [← frameEq]
        exact process
      refine Or.inr ⟨frame.inner, resume, settled, ?_, zero, forcedStatic, caller,
        exactProcess, resumed.symm, staticcall_routing_of_process zero filled exactProcess⟩
      change XStep.toStep (pc + 1) (Xinst.step sevm pre .staticcall) = _
      rw [dispatch]
      change Step.spawn frame resume (pc + 1) =
        Step.spawn (Frame.ofCall frame.inner) resume (pc + 1)
      rw [frameEq]
      rfl

/-- The full actual occurrence supplies its own slot and result; even a
noncommitting or outer-error instruction is observed without filtering. -/
theorem Exec.NinstOccurrence.staticcall_observation
    {root : Exec.Deriv} (occurrence : Exec.NinstOccurrence root)
    (instruction : occurrence.instruction = Ninst.staticcall) :
    StaticcallObservation occurrence.node.pc occurrence.node.sevm
      occurrence.node.devm occurrence.slot occurrence.stepResult := by
  apply Ninst.staticcall_observation occurrence.filled
  rw [← instruction]
  exact occurrence.stepRun

end Blanc
