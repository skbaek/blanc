import Blanc.Lift.MemMap
import Blanc.Lift.CallEffects

/-!
# What one instruction step does to memory (contract-neutral)

The memory a successful lifted step (`Ninst.Run`) leaves, read off Jaune's step functions for the
instructions whose memory effect no shared lemma states yet:

* the writers: `MSTORE8`, `CODECOPY`, `RETURNDATACOPY` (beside `mstore_run_memory` and
  `calldatacopy_run_memory` in `Blanc/Lift/MemMap.lean`), and the output windows of `CALL`,
  `DELEGATECALL` and `STATICCALL`: at most `outputSize` bytes at `outputIndex`, over the memory
  extended for the input and output windows, on every arm (failed balance or depth check, child
  error, child success);
* the instructions that keep memory although `rinstMemKeeps` does not list them: `EXP`, `BALANCE`,
  `EXTCODESIZE` (and `MLOAD`'s extension, `CREATE2`'s extension).

The stack pops are computed on a known stack (`Devm.pop_cons` and its `withStack` forms), so each
inversion is a short `simp only` over the step and a split on its few branches.
-/

namespace Blanc.Lift

open Jaune
theorem Devm.pop_cons {d : Devm} {x : B256} {xs : List B256} (h : d.stack = x :: xs) :
    d.pop = .ok (x, d.withStack xs) :=
  CallEffects.Devm.pop_cons h

theorem Devm.popToNat_cons {d : Devm} {x : B256} {xs : List B256} (h : d.stack = x :: xs) :
    d.popToNat = .ok (x.toNat, d.withStack xs) :=
  CallEffects.Devm.popToNat_cons h

theorem Devm.popToAdr_cons {d : Devm} {x : B256} {xs : List B256} (h : d.stack = x :: xs) :
    d.popToAdr = .ok (x.toAdr, d.withStack xs) :=
  CallEffects.Devm.popToAdr_cons h

theorem Devm.withStack_pop (d : Devm) (x : B256) (xs : List B256) :
    (d.withStack (x :: xs)).pop = .ok (x, d.withStack xs) :=
  CallEffects.Devm.withStack_pop d x xs

theorem Devm.withStack_popToNat (d : Devm) (x : B256) (xs : List B256) :
    (d.withStack (x :: xs)).popToNat = .ok (x.toNat, d.withStack xs) :=
  CallEffects.Devm.withStack_popToNat d x xs

theorem Devm.withStack_popToAdr (d : Devm) (x : B256) (xs : List B256) :
    (d.withStack (x :: xs)).popToAdr = .ok (x.toAdr, d.withStack xs) :=
  CallEffects.Devm.withStack_popToAdr d x xs

/-- Every covered fork enables EIP-7702 delegation. -/
private theorem coveredFork_delegationEnabled {sevm : Sevm}
    (hfork : CoveredFork sevm.benvStat.fork) : sevm.benvStat.rules.delegationEnabled = true :=
  hfork.cases (motive := fun f => (Fork.ruleSet f).delegationEnabled = true) rfl rfl rfl rfl

/-- The tail of every `CALL`-family step: the result is the given parent memory with at most
`os` bytes written at `oi`. -/
theorem genericCall_memory {sevm : Sevm} {devm d' : Devm} {gas : Nat} {value : B256}
    {caller target ca : Adr} {st isc : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot}
    (h : XStep.Run (genericCall.step sevm devm gas value caller target ca st isc ii is oi os code dp)
      xl (.ok d')) :
    ∃ ys : Bytes, ys.length ≤ os ∧ d'.memory = devm.memory.write oi ys :=
  CallEffects.genericCall_memory h

/-- `CALL` writes at most `os` bytes at `oi` over its (extended) memory. -/
theorem run_call_memory {sevm : Sevm} {d d' : Devm} {g c v ii is oi os : B256} {rest : List B256}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hs : d.stack = g :: c :: v :: ii :: is :: oi :: os :: rest)
    (run : Ninst.Run sevm d (.exec .call) d') :
    ∃ ys : Bytes, ys.length ≤ os.toNat ∧
      d'.memory = (d.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat ys :=
  (CallEffects.call_run_effects hfork.rules_stateGas_none hs run).2

/-- `DELEGATECALL` writes at most `os` bytes at `oi` over its (extended) memory. -/
theorem run_delegatecall_memory {sevm : Sevm} {d d' : Devm} {g c ii is oi os : B256}
    {rest : List B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hs : d.stack = g :: c :: ii :: is :: oi :: os :: rest)
    (run : Ninst.Run sevm d (.exec .delegatecall) d') :
    ∃ ys : Bytes, ys.length ≤ os.toNat ∧
      d'.memory = (d.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat ys :=
  (CallEffects.call6_run_effects (Or.inl rfl) hfork.rules_stateGas_none hs run).2

/-- `STATICCALL` writes at most `os` bytes at `oi` over its (extended) memory. -/
theorem run_staticcall_memory {sevm : Sevm} {d d' : Devm} {g c ii is oi os : B256}
    {rest : List B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hs : d.stack = g :: c :: ii :: is :: oi :: os :: rest)
    (run : Ninst.Run sevm d (.exec .staticcall) d') :
    ∃ ys : Bytes, ys.length ≤ os.toNat ∧
      d'.memory = (d.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat ys :=
  (CallEffects.call6_run_effects (Or.inr rfl) hfork.rules_stateGas_none hs run).2

/-- The `CREATE`-family return path leaves the parent's memory as it was. -/
theorem resume_create_memory {parent child sf : Devm} {a : Adr}
    (h : (Resume.create parent a).run (.ok child) = .ok sf) : sf.memory = parent.memory := by
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact (Devm.push_of_push h).memory.symm
  · exact (Devm.push_of_push h).memory.symm

theorem genericCreate_memory {sevm : Sevm} {devm d' : Devm} {e : B256} {a : Adr} {mi ms : Nat}
    {xl : Xlot} (h : XStep.Run (genericCreate.step sevm devm e a mi ms) xl (.ok d')) :
    d'.memory = devm.memory := by
  unfold genericCreate.step at h
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic] at h
  repeat' split at h
  all_goals first
    | cases XStep.run_ofExcept_error h
    | (rename_i hp
       have hd : d' = _ := Except.ok.inj h.2
       subst hd
       exact (Devm.push_of_push hp).memory.symm)
    | (obtain ⟨r, -, hr⟩ := h
       rcases r with _ | child
       · exact (Resume.create_run_error hr.symm).elim
       · exact (resume_create_memory hr.symm).trans rfl)

/-- `CREATE2` only extends memory. -/
theorem run_create2_memory {sevm : Sevm} {d d' : Devm} {e mi ms salt : B256} {rest : List B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hs : d.stack = e :: mi :: ms :: salt :: rest)
    (run : Ninst.Run sevm d (.exec .create2) d') :
    d'.memory = d.memory.extends [(mi.toNat, ms.toNat)] := by
  obtain ⟨xl, -, pc, h⟩ := run
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    hfork.rules_stateGas_none, Bind.bind, Except.bind,
    Devm.pop_cons hs, Devm.withStack_pop, Devm.withStack_popToNat] at h
  split at h
  swap
  · cases XStep.run_ofExcept_error h
  split at h
  · cases XStep.run_ofExcept_error h
  rename_i d5 hc
  rw [genericCreate_memory h]
  change d5.memory.extends _ = _
  rw [← (Devm.burn_of_chargeGas hc).memory]
  rfl

theorem run_balance_memory {sevm : Sevm} {d d' : Devm}
    (run : Ninst.Run sevm d (.reg .balance) d') : d'.memory = d.memory := by
  rcases of_run_reg run with ⟨pc, h⟩
  rcases d with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  simp only [Rinst.run, Rinst.runCore, liftMachMetaWorldExecution, liftMachMetaExecution,
    liftMachMeta, Rinst.balanceCore, Footprint.toExecution, Footprint.liftOutcome, Mach.pop,
    Mach.chargeGas, Mach.push] at h
  cases stack with
  | nil => cases h
  | cons x xs =>
    revert h
    generalize sevm.benvStat.rules.access = acc
    intro h
    cases acc with
    | eip2929 =>
      dsimp only at h
      cases hg : safeSub gasLeft (if x.toAdr ∈ view.accessedAddresses then gasWarmAccess
          else sevm.benvStat.rules.gas.coldAccountAccess) with
      | none => simp only [hg, reduceCtorEq] at h
      | some g =>
        by_cases hl : xs.length < 1024
        · simp only [hg, hl, ↓reduceIte, Except.ok.injEq] at h
          subst h
          rfl
        · simp only [hg, hl, ↓reduceIte, reduceCtorEq] at h
    | flat fg =>
      dsimp only at h
      cases hg : safeSub gasLeft fg.balance with
      | none => simp only [hg, reduceCtorEq] at h
      | some g =>
        by_cases hl : xs.length < 1024
        · simp only [hg, hl, ↓reduceIte, Except.ok.injEq] at h
          subst h
          rfl
        · simp only [hg, hl, ↓reduceIte, reduceCtorEq] at h

theorem run_extcodesize_memory {sevm : Sevm} {d d' : Devm}
    (run : Ninst.Run sevm d (.reg .extcodesize) d') : d'.memory = d.memory := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨a, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  have m1 : d1.memory = d.memory := by
    obtain ⟨_, _, hp⟩ := Devm.pop_of_popToAdr h1
    exact (Devm.pop_of_pop hp).memory.symm
  dsimp only at h
  repeat' split at h
  all_goals
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    rw [← (Devm.push_of_push h3).memory, ← m1]
    exact (Devm.burn_of_chargeGas h2).memory.symm

theorem run_extcodehash_memory {sevm : Sevm} {d d' : Devm}
    (run : Ninst.Run sevm d (.reg .extcodehash) d') : d'.memory = d.memory := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  split at h
  swap
  · cases h
  obtain ⟨⟨a, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  have m1 : d1.memory = d.memory := by
    obtain ⟨_, _, hp⟩ := Devm.pop_of_popToAdr h1
    exact (Devm.pop_of_pop hp).memory.symm
  dsimp only at h
  repeat' split at h
  all_goals
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    rw [← (Devm.push_of_push h3).memory, ← m1]
    exact (Devm.burn_of_chargeGas h2).memory.symm

theorem run_exp_memory {sevm : Sevm} {d d' : Devm}
    (run : Ninst.Run sevm d (.reg .exp) d') : d'.memory = d.memory := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨a, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨b, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
  rw [← (Devm.push_of_push h4).memory, ← (Devm.burn_of_chargeGas h3).memory,
    ← (Devm.pop_of_pop h2).memory, ← (Devm.pop_of_pop h1).memory]

theorem run_mstore8_memory {sevm : Sevm} {d d' : Devm} {o v : B256} {rest : List B256}
    (hs : d.stack = o :: v :: rest) (run : Ninst.Run sevm d (.reg .mstore8) d') :
    ∃ ys : Bytes, ys.length = 1 ∧ d'.memory = d.memory.write o.toNat ys := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore, Bind.bind, Except.bind, Devm.popToNat_cons hs,
    Devm.withStack_pop] at h
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
  cases h4
  refine ⟨[v.2.2.toUInt8], rfl, ?_⟩
  simp only [Devm.memWrite_memory]
  rw [← (Devm.burn_of_chargeGas h3).memory]
  rfl

theorem run_codecopy_memory {sevm : Sevm} {d d' : Devm} {o src z : B256} {rest : List B256}
    (hs : d.stack = o :: src :: z :: rest) (run : Ninst.Run sevm d (.reg .codecopy) d') :
    ∃ ys : Bytes, ys.length = z.toNat ∧ d'.memory = d.memory.write o.toNat ys := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore, Bind.bind, Except.bind, Devm.popToNat_cons hs,
    Devm.withStack_popToNat] at h
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
  cases h4
  refine ⟨sevm.code.sliceD src.toNat z.toNat (Linst.toUInt8 .stop),
    ByteArray.length_sliceD .., ?_⟩
  simp only [Devm.memWrite_memory]
  rw [← (Devm.burn_of_chargeGas h3).memory]
  rfl

theorem run_returndatacopy_memory {sevm : Sevm} {d d' : Devm} {o src z : B256}
    {rest : List B256} (hs : d.stack = o :: src :: z :: rest)
    (run : Ninst.Run sevm d (.reg .returndatacopy) d') :
    ∃ ys : Bytes, ys.length = z.toNat ∧ d'.memory = d.memory.write o.toNat ys := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore, Bind.bind, Except.bind, Devm.popToNat_cons hs,
    Devm.withStack_popToNat] at h
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
  split at h4
  · cases h4
  cases h4
  refine ⟨d3.returnData.sliceD src.toNat z.toNat 0, List.takeD_length _ _ _, ?_⟩
  simp only [Devm.memWrite_memory]
  rw [← (Devm.burn_of_chargeGas h3).memory]
  rfl

theorem run_mload_memory {sevm : Sevm} {d d' : Devm} {o : B256} {rest : List B256}
    (hs : d.stack = o :: rest) (run : Ninst.Run sevm d (.reg .mload) d') :
    d'.memory = d.memory.extend o.toNat 32 := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore, Bind.bind, Except.bind, Devm.popToNat_cons hs] at h
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
  rw [← (Devm.push_of_push h4).memory]
  change (d3.memory.read _ _).2 = _
  rw [← (Devm.burn_of_chargeGas h3).memory]
  rfl

/-- A nonempty write covers its window. -/
theorem Mem.write_size_ge (μ : Mem) (o : Nat) {ys : Bytes} (hne : ys ≠ []) :
    o + ys.length ≤ (μ.write o ys).size :=
  (Mem.write_base μ o hne).choose_spec.2.2.2.1

end Blanc.Lift
