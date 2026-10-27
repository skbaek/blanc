import Blanc.ExecutionMessageEffects

/-!
# Inverting a nonzero result of an actual internal CREATE

The returned stack word selects clean CREATE settlement, including code deposit,
of the same recursive slot. This does not extract that word from a factory
receipt, nor establish retention by an enclosing transaction.
-/

namespace Blanc

open Jaune

/-- A nonzero CREATE status comes from the same clean settled child. -/
theorem Resume.create_nonzero_inv
    {parent post : Devm} {address : Adr} {word : B256}
    {result : Except (EvmError × State × AdrSet × Tra) Devm}
    (run : (Resume.create parent address).run result = .ok post)
    (stack : post.stack = word :: parent.stack) (nonzero : word ≠ 0) :
    ∃ child, result = .ok child ∧ child.error = none ∧
      word = address.toB256 ∧ post.state = child.state := by
  cases result with
  | error error => exact (Resume.create_run_error run).elim
  | ok child =>
    have state := Resume.create_state run
    unfold Resume.run liftToExecution at run
    dsimp only [bind, Except.bind] at run
    split at run
    · have pushed := (Devm.push_of_push run).stack
      change post.stack = 0 :: parent.stack at pushed
      exact (nonzero (List.cons.inj (stack.symm.trans pushed)).1).elim
    · have pushed := (Devm.push_of_push run).stack
      change post.stack = address.toB256 :: parent.stack at pushed
      refine ⟨child, rfl, ?_, (List.cons.inj (stack.symm.trans pushed)).1, state⟩
      rename_i clean
      cases error : child.error with
      | none => rfl
      | some error => simp only [error, Option.isSome_some, not_true_eq_false] at clean

/-- Invert the actual generic CREATE and keep its recursive slot through code
settlement. Target nonce/code exclusion is derived from the actual spawn.
The stack premise is an intermediate observation to be produced by a consumer. -/
theorem GenericCreate.nonzero_inv
    {sevm : Sevm} {pre post : Devm} {endowment word : B256}
    {address : Adr} {mi ms : Nat} {slot : Xlot}
    (run : GenericCreate sevm pre endowment address mi ms slot (.ok post))
    (stack : post.stack = word :: pre.stack) (nonzero : word ≠ 0) :
    let parent := addAccessedAddress
      (((pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)).withReturnData
        []).incrNonce sevm.currentTarget) address
    let msg := createMsg sevm parent (except64th pre.gasLeft) endowment address
      ((pre.memory.read mi ms).1)
    ∃ child,
      genericCreate.step sevm pre endowment address mi ms =
        .spawn (Frame.ofCreate msg) (.create parent address) ∧
      ProcessCreateMessage msg slot (.ok child) ∧ child.error = none ∧
      (Resume.create parent address).run (.ok child) = .ok post ∧
      word = address.toB256 ∧ post.state = child.state ∧
      ¬ State.Protected pre.state address ∧
      ∃ inner charged,
        ProcessMessage (processCreateMessage.msg msg) slot (.ok inner) ∧
        inner.error.isSome = false ∧
        processCreateMessage.chargeCodeGas msg.benv.stat.rules inner = .ok charged ∧
        child = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩ := by
  dsimp only
  cases spawn : genericCreate.step sevm pre endowment address mi ms with
  | spawn frame resume =>
    change XStep.Run _ slot (.ok post) at run
    rw [spawn] at run
    obtain ⟨result, process, resumed⟩ := run
    obtain ⟨frameEq, resumeEq⟩ := genericCreate_step_spawn_exact spawn
    rw [resumeEq] at resumed
    have stack' : post.stack = word ::
        (addAccessedAddress
          (((pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) address).stack := stack
    obtain ⟨child, resultEq, clean, wordEq, stateEq⟩ :=
      Resume.create_nonzero_inv resumed.symm stack' nonzero
    subst result
    rw [frameEq] at process
    refine ⟨child, ?_, process, clean, resumed.symm, wordEq, stateEq,
      genericCreate_step_spawn_target_unprotected spawn, ?_⟩
    · rw [frameEq, resumeEq]
    · exact ProcessCreateMessage.ok_charge_of_clean process (by rw [clean]; rfl)
  | done result =>
    change XStep.Run _ slot (.ok post) at run
    rw [spawn] at run
    obtain ⟨-, resultEq⟩ := run
    subst result
    simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
      assertDynamic, Pure.pure, Except.pure] at spawn
    repeat' split at spawn
    all_goals simp only [XStep.ofExcept, XStep.done.injEq, reduceCtorEq,
      Except.ok.injEq] at spawn
    all_goals subst spawn
    all_goals rename_i pushed pushEq
    all_goals
      have pushedStack := (Devm.push_of_push pushEq).stack
      change pushed.stack = 0 :: pre.stack at pushedStack
      exact (nonzero (List.cons.inj (stack.symm.trans pushedStack)).1).elim

/-- An actual CREATE2 run exposes its exact gas-paid generic CREATE, retaining
its original slot. Only the selected pre-Amsterdam rule facts are used. -/
theorem Xinst.create2_run_generic
    {sevm : Sevm} {pre post : Devm} {slot : Xlot}
    {value index size salt : B256} {rest : Stack}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (enabled : sevm.benvStat.rules.op.create2 = true)
    (stack : pre.stack = value :: index :: size :: salt :: rest)
    (run : Xinst.Run sevm pre .create2 slot (.ok post)) :
    let popped := pre.setMach ⟨rest, pre.memory, pre.gasLeft, pre.stateGas⟩
    let cost := sevm.benvStat.rules.gas.createAccess +
      gasKeccak256Word * ceilDiv size.toNat 32 +
      popped.extCost [(index.toNat, size.toNat)] +
      (if sevm.benvStat.rules.creation.initCodeLimit then
        gasInitCodeWordCost * ceilDiv size.toNat 32 else 0)
    ∃ paid,
      chargeGas cost popped = .ok paid ∧
      let base := paid.memExtends [(index.toNat, size.toNat)]
      let address := create2NewAddress sevm.currentTarget salt
        (base.memory.data.sliceD index.toNat size.toNat 0)
      Xinst.step sevm pre .create2 =
        genericCreate.step sevm base value address index.toNat size.toNat ∧
      GenericCreate sevm base value address index.toNat size.toNat slot (.ok post) ∧
      base.stack = rest ∧ base.state = pre.state := by
  let popped := pre.setMach ⟨rest, pre.memory, pre.gasLeft, pre.stateGas⟩
  have step : Xinst.step sevm pre .create2 =
      XStep.ofExcept (do
        let paid ← chargeGas
          (sevm.benvStat.rules.gas.createAccess +
            gasKeccak256Word * ceilDiv size.toNat 32 +
            popped.extCost [(index.toNat, size.toNat)] +
            (if sevm.benvStat.rules.creation.initCodeLimit then
              gasInitCodeWordCost * ceilDiv size.toNat 32 else 0)) popped
        let base := paid.memExtends [(index.toNat, size.toNat)]
        return genericCreate.step sevm base value
          (create2NewAddress sevm.currentTarget salt
            (base.memory.data.sliceD index.toNat size.toNat 0)) index.toNat size.toNat) := by
    simp only [Xinst.step, hsg, enabled, ↓reduceIte]
    rw [Devm.pop_eq_ok stack]
    simp only [bind, Except.bind]
    rw [Devm.popToNat_def, Devm.pop_eq_ok rfl]
    simp only [Functor.mapRev, Functor.map, Except.map, Prod.mapFst, Prod.map]
    rw [Devm.popToNat_def, Devm.pop_eq_ok rfl]
    simp only [Functor.mapRev, Functor.map, Except.map, Prod.mapFst, Prod.map]
    rw [Devm.pop_eq_ok rfl]
    rfl
  change XStep.Run _ slot (.ok post) at run
  rw [step] at run
  cases charge : chargeGas
      (sevm.benvStat.rules.gas.createAccess +
        gasKeccak256Word * ceilDiv size.toNat 32 +
        popped.extCost [(index.toNat, size.toNat)] +
        (if sevm.benvStat.rules.creation.initCodeLimit then
          gasInitCodeWordCost * ceilDiv size.toNat 32 else 0)) popped with
  | error error =>
    rw [charge] at run
    cases XStep.run_ofExcept_error run
  | ok paid =>
    have step' := step
    rw [charge] at step' run
    simp only [bind, Except.bind, pure, Except.pure, XStep.ofExcept] at step' run
    refine ⟨paid, charge, step', run, ?_, ?_⟩
    · change paid.stack = rest
      rw [← (Devm.burn_of_chargeGas charge).stack]
      rfl
    · change paid.state = pre.state
      rw [← (Devm.burn_of_chargeGas charge).state]
      rfl

/-- The actual CREATE2 result binds its nonzero address to the same clean
creation slot, including the actual successful code-deposit charge. -/
theorem Xinst.create2_nonzero_inv
    {sevm : Sevm} {pre post : Devm} {slot : Xlot}
    {value index size salt word : B256} {rest : Stack}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (enabled : sevm.benvStat.rules.op.create2 = true)
    (before : pre.stack = value :: index :: size :: salt :: rest)
    (run : Xinst.Run sevm pre .create2 slot (.ok post))
    (after : post.stack = word :: rest) (nonzero : word ≠ 0) :
    ∃ base : Devm, base.state = pre.state ∧ base.stack = rest ∧
      let address := create2NewAddress sevm.currentTarget salt
        (base.memory.data.sliceD index.toNat size.toNat 0)
      let parent := addAccessedAddress
        (((base.withGasLeft (base.gasLeft - except64th base.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) address
      let msg := createMsg sevm parent (except64th base.gasLeft) value address
        ((base.memory.read index.toNat size.toNat).1)
      ∃ child,
        Xinst.step sevm pre .create2 =
          .spawn (Frame.ofCreate msg) (.create parent address) ∧
        ProcessCreateMessage msg slot (.ok child) ∧ child.error = none ∧
        (Resume.create parent address).run (.ok child) = .ok post ∧
        word = address.toB256 ∧ post.state = child.state ∧
        ¬ State.Protected pre.state address ∧
        ∃ inner charged,
          ProcessMessage (processCreateMessage.msg msg) slot (.ok inner) ∧
          inner.error.isSome = false ∧
          processCreateMessage.chargeCodeGas msg.benv.stat.rules inner = .ok charged ∧
          child = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩ := by
  obtain ⟨paid, charge, step, generic, stack, state⟩ :=
    Xinst.create2_run_generic hsg enabled before run
  obtain ⟨child, spawn, process, clean, resumed, wordEq, stateEq, unprotected, deposit⟩ :=
    GenericCreate.nonzero_inv generic (by rw [stack]; exact after) nonzero
  refine ⟨_, state, stack, child, step.trans spawn, process, clean, resumed,
    wordEq, stateEq, ?_, deposit⟩
  rw [← state]
  exact unprotected

/-- A compiled CREATE2 uses one slot for all program counters. Its selected
slot is retained by `Xinst.create2_run_generic` and `Xinst.create2_nonzero_inv`. -/
theorem Ninst.RunCompiled.create2_run
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.RunCompiled sevm pre (.exec .create2) post) :
    ∃ slot, slot.Filled ∧ Xinst.Run sevm pre .create2 slot (.ok post) := by
  obtain ⟨slot, filled, steps⟩ := run
  refine ⟨slot, filled, ?_⟩
  simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using steps 0

end Blanc
