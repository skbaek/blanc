import Blanc.StaticcallObservation

/-!
# Actual STATICCALL operand and payload inversion

The six words and original memory are recovered from an actual spawn, before
any child outcome is inspected. The selected rules retain both continuation
constructors and the Amsterdam state-gas grant.
-/

namespace Blanc

open Jaune

/-- Operand, original-payload and continuation facts about the exact supplied
STATICCALL spawn. The parent keeps its actual access and accounting metadata. -/
def StaticcallSpawnOperands (sevm : Sevm) (pre : Devm)
    (frame : Frame) (resume : Resume) : Prop :=
  ∃ (g t ii isz oi os : B256) (parent : Devm)
    (dp : Bool) (na : Adr) (code : ByteArray) (avail : Nat),
    pre.stack = g :: t :: ii :: isz :: oi :: os :: parent.stack ∧
    0 < sevm.depth ∧
    parent.state = pre.state ∧
    parent.memory = pre.memory.extends
      [(ii.toNat, isz.toNat), (oi.toNat, os.toNat)] ∧
    parent.returnData = [] ∧
    ((sevm.benvStat.rules.delegatedCodeAddress (pre.getCode t.toAdr) = none ∧
        na = t.toAdr ∧ code = pre.getCode t.toAdr ∧ dp = false) ∨
      (∃ d, sevm.benvStat.rules.delegatedCodeAddress
          (pre.getCode t.toAdr) = some d ∧
        na = d ∧ code = pre.getCode d ∧ dp = true)) ∧
    let child := callMsg sevm parent (min g.toNat (except64th avail)) 0
      sevm.currentTarget t.toAdr na true true
      (pre.memory.read ii.toNat isz.toNat).1 code dp
    ((sevm.benvStat.rules.stateGas = none ∧
        frame = Frame.ofCall child ∧
        resume = .call parent oi.toNat os.toNat) ∨
      (∃ state reservoir,
        sevm.benvStat.rules.stateGas = some state ∧
        reservoir = pre.stateGas.left ∧ parent.stateGas.left = 0 ∧
        frame = Frame.ofCall {child with stateGasGrant := reservoir} ∧
        resume = .callAmsterdam state parent oi.toNat os.toNat false))

private theorem accessDelegation_selection (rules : ForkRules) (d : Devm) (t : Adr) :
    let lookup := rules.accessDelegation d t
    ((rules.delegatedCodeAddress (d.getCode t) = none ∧
        lookup.2.1 = t ∧ lookup.2.2.1 = d.getCode t ∧ lookup.1 = false) ∨
      (∃ a, rules.delegatedCodeAddress (d.getCode t) = some a ∧
        lookup.2.1 = a ∧ lookup.2.2.1 = d.getCode a ∧ lookup.1 = true)) := by
  dsimp only [ForkRules.accessDelegation, ForkRules.delegatedCodeAddress, Devm.getCode]
  split
  · dsimp only [GasSchedule.accessDelegation]
    cases selected : getDelegatedCodeAddress (d.state.getCode t) with
    | none => exact Or.inl ⟨selected, rfl, rfl, rfl⟩
    | some a => exact Or.inr ⟨a, selected, rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩

private theorem delegationCost_selection (rules : ForkRules) (d : Devm) (t : Adr) :
    let priced := rules.delegationCost d t
    ((rules.delegatedCodeAddress (d.getCode t) = none ∧
        priced.2.1 = t ∧ priced.1 = false) ∨
      (∃ a, rules.delegatedCodeAddress (d.getCode t) = some a ∧
        priced.2.1 = a ∧ priced.1 = true)) := by
  dsimp only [ForkRules.delegationCost, ForkRules.delegatedCodeAddress, Devm.getCode]
  split
  · dsimp only [GasSchedule.delegationCost]
    cases selected : getDelegatedCodeAddress (d.state.getCode t) with
    | none => exact Or.inl ⟨selected, rfl, rfl⟩
    | some a => exact Or.inr ⟨a, selected, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩

/-- Invert only the actual spawn; no flag, child outcome or fork premise. -/
theorem Xinst.step_staticcall_spawn_operands
    {sevm : Sevm} {pre : Devm} {frame : Frame} {resume : Resume}
    (spawn : Xinst.step sevm pre .staticcall = .spawn frame resume) :
    StaticcallSpawnOperands sevm pre frame resume := by
  have depth := Xinst.step_spawn_depth spawn
  have depthPos : 0 < sevm.depth := by omega
  cases mode : sevm.benvStat.rules.stateGas <;>
    simp only [Xinst.step, mode, Bind.bind, Except.bind, Except.assert] at spawn
  all_goals
    rcases pop1 : pre.pop with _ | ⟨g, d1⟩ <;> simp only [pop1] at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    rcases pop2 : d1.popToAdr with _ | ⟨target, d2⟩ <;> simp only [pop2] at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    obtain ⟨t, targetEq, pop2'⟩ := Devm.pop_of_popToAdr pop2
    subst target
    rcases pop3 : d2.popToNat with _ | ⟨inputIndex, d3⟩ <;> simp only [pop3] at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    obtain ⟨ii, p3, indexEq⟩ := Devm.pop_of_popToNat_val pop3
    subst inputIndex
    rcases pop4 : d3.popToNat with _ | ⟨inputSize, d4⟩ <;> simp only [pop4] at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    obtain ⟨isz, p4, sizeEq⟩ := Devm.pop_of_popToNat_val pop4
    subst inputSize
    rcases pop5 : d4.popToNat with _ | ⟨outputIndex, d5⟩ <;> simp only [pop5] at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    obtain ⟨oi, p5, indexEq⟩ := Devm.pop_of_popToNat_val pop5
    subst outputIndex
    rcases pop6 : d5.popToNat with _ | ⟨outputSize, d6⟩ <;> simp only [pop6] at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    obtain ⟨os, p6, sizeEq⟩ := Devm.pop_of_popToNat_val pop6
    subst outputSize
    have pops := Devm.pop_append (Devm.pop_of_pop pop1)
      (Devm.pop_append (Devm.pop_of_pop pop2')
        (Devm.pop_append p3 (Devm.pop_append p4 (Devm.pop_append p5 p6))))
    have stackEq : pre.stack = g :: t :: ii :: isz :: oi :: os :: d6.stack := by
      simpa only [Stack.Pop, Split, List.nil_append, List.cons_append] using pops.stack
  case none =>
    let accessed : Devm := match sevm.benvStat.rules.access with
      | .eip2929 => addAccessedAddress d6 t.toAdr
      | .flat _ => d6
    have accessed_state : accessed.state = d6.state := by
      dsimp only [accessed]
      split <;> rfl
    have accessed_stack : accessed.stack = d6.stack := by
      dsimp only [accessed]
      split <;> rfl
    have accessed_memory : accessed.memory = d6.memory := by
      dsimp only [accessed]
      split <;> rfl
    let lookup := sevm.benvStat.rules.accessDelegation accessed t.toAdr
    split at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    rename_i paid charge
    simp only [Pure.pure, Except.pure, XStep.ofExcept] at spawn
    have exactSpawn := genericCall_step_spawn_exact spawn
    have looked_state : lookup.2.2.2.2.state = d6.state := by
      dsimp only [lookup, ForkRules.accessDelegation]
      split
      · rw [GasSchedule.accessDelegation_state, accessed_state]
      · exact accessed_state
    have looked_stack : lookup.2.2.2.2.stack = d6.stack := by
      dsimp only [lookup, ForkRules.accessDelegation]
      split
      · rw [GasSchedule.accessDelegation_stack, accessed_stack]
      · exact accessed_stack
    have looked_memory : lookup.2.2.2.2.memory = d6.memory := by
      dsimp only [lookup, ForkRules.accessDelegation]
      split
      · rw [GasSchedule.accessDelegation_memory, accessed_memory]
      · exact accessed_memory
    have burn := Devm.burn_of_chargeGas charge
    obtain ⟨avail, grant⟩ := calculateMsgCallGas_stipend (chargeGas_le charge)
    simp only [↓reduceIte, Nat.add_zero] at grant
    let parent := (paid.memExtends
      [(ii.toNat, isz.toNat), (oi.toNat, os.toNat)]).withReturnData []
    have parent_stack : parent.stack = d6.stack :=
      burn.stack.symm.trans looked_stack
    have parent_state : parent.state = pre.state :=
      burn.state.symm.trans (looked_state.trans pops.state.symm)
    have parent_memory : parent.memory = pre.memory.extends
        [(ii.toNat, isz.toNat), (oi.toNat, os.toNat)] := by
      exact congrArg (fun memory => memory.extends
        [(ii.toNat, isz.toNat), (oi.toNat, os.toNat)])
        (burn.memory.symm.trans (looked_memory.trans pops.memory.symm))
    have original_data : (parent.memory.read ii.toNat isz.toNat).1 =
        (pre.memory.read ii.toNat isz.toNat).1 := by
      rw [parent_memory]
      rfl
    have selected := accessDelegation_selection sevm.benvStat.rules accessed t.toAdr
    have code_at : ∀ a, accessed.getCode a = pre.getCode a := by
      intro a
      change accessed.state.getCode a = pre.state.getCode a
      rw [accessed_state, ← pops.state]
    simp only [code_at] at selected
    rw [grant] at exactSpawn
    refine ⟨g, t, ii, isz, oi, os, parent, lookup.1, lookup.2.1,
      lookup.2.2.1, avail, ?_, depthPos, parent_state, parent_memory, rfl,
      selected, Or.inl ⟨mode, ?_, exactSpawn.2⟩⟩
    · rw [parent_stack]
      exact stackEq
    · rw [exactSpawn.1]
      change Frame.ofCall (callMsg sevm parent _ _ _ _ _ _ _
        (parent.memory.read ii.toNat isz.toNat).1 _ _) = _
      rw [original_data]
      rfl
  case some state =>
    let priced := sevm.benvStat.rules.delegationCost
      (addAccessedAddress d6 t.toAdr) t.toAdr
    let reads := Devm.balReadAccount sevm.benvStat.rules priced.2.1
      (Devm.balReadAccount sevm.benvStat.rules t.toAdr
        (addAccessedAddress d6 t.toAdr))
    let completed := completeDelegationAccess reads priced.1 priced.2.1
    split at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    split at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    split at spawn
    · simp only [XStep.ofExcept, reduceCtorEq] at spawn
    rename_i paid charge
    simp only [Pure.pure, Except.pure, XStep.ofExcept] at spawn
    have exactSpawn := genericCallAmsterdam_step_spawn_exact spawn
    have completed_state : completed.2.state = d6.state := by
      dsimp only [completed, completeDelegationAccess]
      split <;> rfl
    have completed_stack : completed.2.stack = d6.stack := by
      dsimp only [completed, completeDelegationAccess]
      split <;> rfl
    have completed_memory : completed.2.memory = d6.memory := by
      dsimp only [completed, completeDelegationAccess]
      split <;> rfl
    have completed_stateGas : completed.2.stateGas = d6.stateGas := by
      dsimp only [completed, completeDelegationAccess]
      split <;> rfl
    have completed_code : completed.1 = pre.getCode priced.2.1 := by
      dsimp only [completed, completeDelegationAccess]
      split <;> change d6.state.getCode priced.2.1 = pre.state.getCode priced.2.1
      all_goals rw [← pops.state]
    have burn := Devm.burn_of_chargeGas charge
    obtain ⟨avail, grant⟩ := calculateMsgCallGas_stipend (chargeGas_le charge)
    simp only [↓reduceIte, Nat.add_zero] at grant
    let parent := (paid.drainStateGasReservoir.2.memExtends
      [(ii.toNat, isz.toNat), (oi.toNat, os.toNat)]).withReturnData []
    have parent_stack : parent.stack = d6.stack :=
      burn.stack.symm.trans completed_stack
    have parent_state : parent.state = pre.state :=
      burn.state.symm.trans (completed_state.trans pops.state.symm)
    have parent_memory : parent.memory = pre.memory.extends
        [(ii.toNat, isz.toNat), (oi.toNat, os.toNat)] := by
      exact congrArg (fun memory => memory.extends
        [(ii.toNat, isz.toNat), (oi.toNat, os.toNat)])
        (burn.memory.symm.trans (completed_memory.trans pops.memory.symm))
    have reservoir : paid.drainStateGasReservoir.1 = pre.stateGas.left :=
      congrArg StateGasMeter.left
        (burn.stateGas.symm.trans (completed_stateGas.trans pops.stateGas.symm))
    have original_data : parent.memory.data.sliceD ii.toNat isz.toNat 0 =
        (pre.memory.read ii.toNat isz.toNat).1 := by
      rw [parent_memory]
      rfl
    have chosen := delegationCost_selection sevm.benvStat.rules
      (addAccessedAddress d6 t.toAdr) t.toAdr
    have original_code : ∀ a, (addAccessedAddress d6 t.toAdr).getCode a =
        pre.getCode a := by
      intro a
      change d6.state.getCode a = pre.state.getCode a
      rw [← pops.state]
    simp only [original_code] at chosen
    have selected :
        (sevm.benvStat.rules.delegatedCodeAddress (pre.getCode t.toAdr) = none ∧
          priced.2.1 = t.toAdr ∧ completed.1 = pre.getCode t.toAdr ∧ priced.1 = false) ∨
        (∃ a, sevm.benvStat.rules.delegatedCodeAddress (pre.getCode t.toAdr) = some a ∧
          priced.2.1 = a ∧ completed.1 = pre.getCode a ∧ priced.1 = true) := by
      rcases chosen with ⟨hn, ha, hd⟩ | ⟨a, hn, ha, hd⟩
      · exact Or.inl ⟨hn, ha, completed_code.trans (congrArg pre.getCode ha), hd⟩
      · exact Or.inr ⟨a, hn, ha, completed_code.trans (congrArg pre.getCode ha), hd⟩
    simp only [Nat.add_zero] at exactSpawn
    rw [grant] at exactSpawn
    refine ⟨g, t, ii, isz, oi, os, parent, priced.1, priced.2.1,
      completed.1, avail, ?_, depthPos, parent_state, parent_memory, rfl,
      selected, Or.inr ⟨state, paid.drainStateGasReservoir.1, mode,
        reservoir, rfl, ?_, exactSpawn.2⟩⟩
    · rw [parent_stack]
      exact stackEq
    · rw [exactSpawn.1]
      change Frame.ofCall {callMsg sevm parent _ _ _ _ _ _ _
        (parent.memory.data.sliceD ii.toNat isz.toNat 0) _ _
          with stateGasGrant := paid.drainStateGasReservoir.1} = _
      rw [original_data]

/-- Primitive-step transport of the exact operand inversion and successor pc. -/
theorem Ninst.step_staticcall_spawn_operands
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm} {frame : Frame} {resume : Resume}
    (spawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.staticcall =
      .spawn frame resume pc') :
    pc' = pc + 1 ∧ StaticcallSpawnOperands sevm pre frame resume := by
  change XStep.toStep (pc + 1) (Xinst.step sevm pre .staticcall) = _ at spawn
  have dispatch := XStep.toStep_spawn spawn
  have operands := Xinst.step_staticcall_spawn_operands dispatch
  rw [dispatch] at spawn
  change Step.spawn frame resume (pc + 1) = Step.spawn frame resume pc' at spawn
  exact ⟨(Step.spawn.inj spawn).2.2.symm, operands⟩

/-- Enrich the actual all-outcome observation's same message and original slot
with its popped operands and original payload, without a success filter. -/
theorem Ninst.staticcall_observation_with_operands
    {pc : Nat} {sevm : Sevm} {pre : Devm} {slot : Xlot} {out : Execution}
    (filled : slot.Filled)
    (run : Ninst.StepRun pc sevm pre Ninst.staticcall slot out) :
    (∃ raw, Xinst.step sevm pre .staticcall = .done raw ∧
      slot = .none ∧ out = raw) ∨
    ∃ (msg : Msg) (resume : Resume)
      (settled : Except (EvmError × State × AdrSet × Tra) Devm),
      Ninst.step ⟨pc, sevm, pre⟩ Ninst.staticcall =
        .spawn (Frame.ofCall msg) resume (pc + 1) ∧
      StaticcallSpawnOperands sevm pre (Frame.ofCall msg) resume ∧
      msg.value = 0 ∧ msg.isStatic = true ∧ msg.caller = sevm.currentTarget ∧
      ProcessMessage msg slot settled ∧ resume.run settled = out ∧
      StaticcallRouting msg slot settled := by
  rcases Ninst.staticcall_observation filled run with unentered | entered
  · exact Or.inl unentered
  · obtain ⟨msg, resume, settled, spawn, zero, static, caller, process,
      resumed, routing⟩ := entered
    exact Or.inr ⟨msg, resume, settled, spawn,
      (Ninst.step_staticcall_spawn_operands spawn).2, zero, static, caller,
      process, resumed, routing⟩

/-- The full actual occurrence retains its arbitrary original result and slot. -/
theorem Exec.NinstOccurrence.staticcall_observation_with_operands
    {root : Exec.Deriv} (occurrence : Exec.NinstOccurrence root)
    (instruction : occurrence.instruction = Ninst.staticcall) :
    (∃ raw, Xinst.step occurrence.node.sevm occurrence.node.devm .staticcall =
      .done raw ∧ occurrence.slot = .none ∧ occurrence.stepResult = raw) ∨
    ∃ (msg : Msg) (resume : Resume)
      (settled : Except (EvmError × State × AdrSet × Tra) Devm),
      Ninst.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩
          Ninst.staticcall =
        .spawn (Frame.ofCall msg) resume (occurrence.node.pc + 1) ∧
      StaticcallSpawnOperands occurrence.node.sevm occurrence.node.devm
        (Frame.ofCall msg) resume ∧
      msg.value = 0 ∧ msg.isStatic = true ∧
      msg.caller = occurrence.node.sevm.currentTarget ∧
      ProcessMessage msg occurrence.slot settled ∧
      resume.run settled = occurrence.stepResult ∧ StaticcallRouting msg occurrence.slot settled := by
  apply Ninst.staticcall_observation_with_operands occurrence.filled
  rw [← instruction]
  exact occurrence.stepRun

end Blanc
