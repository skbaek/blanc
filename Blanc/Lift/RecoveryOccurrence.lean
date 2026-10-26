import Blanc.Lift.CursorOccurrence
import Blanc.Lift.Ecrecover

/-! Actual synchronous ECRECOVER invocations at reached call occurrences. -/

namespace Blanc.Lift

open Jaune

/-- A successful synchronous recovery invocation at this actual instruction.
The returned bytes may be empty. This is not a relevance or completeness
certificate for a history, nor does it assert that the enclosing root commits. -/
structure RecoveryInvocation {root : Exec.Deriv}
    (step : CallOccurrenceStep root .staticcall) (g ii is oi os : B256) where
  parent : Devm
  child : Devm
  available : Nat
  code : ByteArray
  message : Msg
  stack : step.occurrence.node.devm.stack =
    g :: 1 :: ii :: is :: oi :: os :: parent.stack
  parentState : parent.state = step.occurrence.node.devm.state
  parentMemory : parent.memory = step.occurrence.node.devm.memory.extends
    [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]
  messageEq : message = callMsg step.occurrence.node.sevm parent
    (min g.toNat (except64th available)) 0 step.occurrence.node.sevm.currentTarget
    1 1 true true (step.occurrence.node.devm.memory.read ii.toNat is.toNat).1 code false
  spawn : Evm.step ⟨step.occurrence.node.pc, step.occurrence.node.sevm,
      step.occurrence.node.devm⟩ =
    .spawn (Frame.ofCall message) (.call parent oi.toNat os.toNat)
      (step.occurrence.node.pc + 1)
  transfer : message.benvAfterTransfer = .ok message.benv
  direct : (Frame.ofCall message).enter = .done (.ok child)
  slotNone : step.occurrence.slot = .none
  clean : child.error.isSome = false
  resume : (Resume.call parent oi.toNat os.toNat).run (.ok child) =
    .ok step.returned.devm
  returnedState : step.returned.devm.state = child.state
  returnData : step.returned.devm.returnData = child.output
  memory : step.returned.devm.memory = parent.memory.write oi.toNat
    (child.output.take os.toNat)
  flag : step.returned.devm.stack = 1 :: parent.stack
  paid : gasEcrecover ≤ min g.toNat (except64th available)
  output : child.output = ecrecoverOutput
    (step.occurrence.node.devm.memory.read ii.toNat is.toNat).1

/-- Invert the actual static call, retaining its failed cause or its exact
synchronous recovery invocation. An empty failed answer does not imply that
no precompile was invoked; in particular this is not a failed-query census. -/
theorem recoveryInvocation_of_callOccurrence {root : Exec.Deriv}
    (step : CallOccurrenceStep root .staticcall) {g ii is oi os : B256} {xs : Stack}
    (fork : CoveredFork step.occurrence.node.sevm.benvStat.fork)
    (operands : (g :: 1 :: ii :: is :: oi :: os :: xs) <<+
      step.occurrence.node.devm.stack)
    (undelegated : getDelegatedCodeAddress (step.occurrence.node.devm.getCode 1) = none) :
    (((0 : B256) :: xs <<+ step.returned.devm.stack) ∧
      Devm.WorldEq step.occurrence.node.devm step.returned.devm ∧
      ∃ out : Bytes, step.returned.devm.returnData = out ∧
        step.returned.devm.memory =
          (step.occurrence.node.devm.memory.extends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat
              (out.take os.toNat) ∧
        StatcallFailureCause step.occurrence.node.sevm step.occurrence.node.devm
          g 1 ii is oi os out) ∨
      Nonempty (RecoveryInvocation step g ii is oi os) := by
  have primitive := step.occurrence.stepRun
  rw [step.instruction, step.result] at primitive
  rcases of_step_staticcall_val_with_depth_frame_cause operands
      step.occurrence.filled primitive fork with failed | success
  · exact Or.inl failed
  · obtain ⟨parent, child, dp, na, code, available, _, stack, state, memory, _, _,
        routed, _, process, clean, resume, childState, returnData, childMemory,
        childStack, spawned⟩ := success
    have one : (1 : B256).toAdr = 1 := by decide
    rw [one] at routed process spawned
    rcases routed with ⟨_, rfl, rfl, rfl⟩ | ⟨a, delegated, _⟩
    · let msg := callMsg step.occurrence.node.sevm parent
        (min g.toNat (except64th available)) 0 step.occurrence.node.sevm.currentTarget
        1 1 true true (step.occurrence.node.devm.memory.read ii.toNat is.toNat).1
        (step.occurrence.node.devm.getCode 1) false
      have transfer : msg.benvAfterTransfer = .ok msg.benv :=
        Msg.benvAfterTransfer_of_value_zero rfl
      have active :
          (!((msg.withBenv msg.benv).disablePrecompiles) &&
            decide ((msg.withBenv msg.benv).benv.stat.rules.isPrecomp 1)) = true := by
        exact ecrecover_active fork
      have entered := Frame.enter_eq_done_executePrecomp
        (f := Frame.ofCall msg) transfer (adr := 1) rfl active
      have processed := process
      change RunFrame (Frame.ofCall msg) step.occurrence.slot (.ok child) at processed
      unfold RunFrame at processed
      rw [entered] at processed
      obtain ⟨slotNone, settled⟩ := processed
      rw [← settled] at entered
      obtain ⟨paid, output⟩ := ecrecover_output_of_processMessage_clean
        (ecrecover_active fork) process clean fork
      have decoded := step.occurrence.decoded
      rw [step.instruction] at decoded
      exact Or.inr ⟨{
        parent := parent, child := child, available := available,
        code := step.occurrence.node.devm.getCode 1, message := msg,
        stack := stack, parentState := state, parentMemory := memory,
        messageEq := rfl, spawn := (Evm.step_next decoded).trans spawned,
        transfer := transfer, direct := entered, slotNone := slotNone,
        clean := clean, resume := resume, returnedState := childState,
        returnData := returnData, memory := childMemory, flag := childStack,
        paid := paid, output := output }⟩
    · rw [undelegated] at delegated
      cases delegated

/-- A set flag selects the invocation branch, without asserting a nonempty
answer or any recovered owner. Concrete bytecode must establish this flag. -/
theorem recoveryInvocation_of_successFlag {root : Exec.Deriv}
    (step : CallOccurrenceStep root .staticcall) {g ii is oi os : B256} {xs : Stack}
    (fork : CoveredFork step.occurrence.node.sevm.benvStat.fork)
    (operands : (g :: 1 :: ii :: is :: oi :: os :: xs) <<+
      step.occurrence.node.devm.stack)
    (undelegated : getDelegatedCodeAddress (step.occurrence.node.devm.getCode 1) = none)
    (success : ∃ flag rest, step.returned.devm.stack = flag :: rest ∧ flag ≠ 0) :
    Nonempty (RecoveryInvocation step g ii is oi os) := by
  rcases recoveryInvocation_of_callOccurrence step fork operands undelegated with
    ⟨failed, _⟩ | invoked
  · obtain ⟨flag, rest, stack, nonzero⟩ := success
    rw [stack] at failed
    exact (nonzero (pref_head_unique failed (pref_append [flag] rest)).symm).elim
  · exact invoked

/-- The EVM actually entered after this occurrence's zero-value transfer. -/
def RecoveryInvocation.entryEvm {root : Exec.Deriv}
    {step : CallOccurrenceStep root .staticcall} {g ii is oi os : B256}
    (invocation : RecoveryInvocation step g ii is oi os) : Evm :=
  initEvm (invocation.message.withBenv invocation.message.benv)

theorem RecoveryInvocation.entry_data {root : Exec.Deriv}
    {step : CallOccurrenceStep root .staticcall} {g ii is oi os : B256}
    (invocation : RecoveryInvocation step g ii is oi os) :
    invocation.entryEvm.sta.data =
      (step.occurrence.node.devm.memory.read ii.toNat is.toNat).1 := by
  unfold entryEvm
  rw [invocation.messageEq]
  rfl

/-- The exact reached query returned the actual parent's complete returndata.
This equality does not assert that the output authenticates any address. -/
theorem RecoveryInvocation.executed {root : Exec.Deriv}
    {step : CallOccurrenceStep root .staticcall} {g ii is oi os : B256}
    (invocation : RecoveryInvocation step g ii is oi os) :
    executeEcrecover invocation.entryEvm =
      .ok gasEcrecover step.returned.devm.returnData := by
  have gas : gasEcrecover ≤ invocation.entryEvm.dyna.gasLeft := by
    unfold entryEvm
    rw [invocation.messageEq]
    exact invocation.paid
  rw [executeEcrecover_eq gas, invocation.entry_data, ← invocation.output,
    ← invocation.returnData]

/-- Only exclusion of this actual recovery query is used. Proving that old
bytecode consumes an address answer is a separate concrete obligation. -/
theorem RecoveryInvocation.answer_ne_of_excluded {root : Exec.Deriv}
    {step : CallOccurrenceStep root .staticcall} {g ii is oi os : B256}
    (invocation : RecoveryInvocation step g ii is oi os) {a : Adr}
    (excluded : executeEcrecover invocation.entryEvm ≠
      .ok gasEcrecover a.toB256.toBytes) :
    step.returned.devm.returnData ≠ a.toB256.toBytes := by
  intro answer
  exact excluded (invocation.executed.trans (congrArg (PrecompResult.ok gasEcrecover) answer))

end Blanc.Lift
