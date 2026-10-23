import Blanc.Ladder

/-!
# Call effects under the actual fork rules

Success-only stack and memory observations for the call family. Flat and
EIP-2929 access, enabled and disabled delegation, and both child outcomes are
retained. The no-state-gas premise selects the ordinary call lane; it does not
assert opcode availability or modern settlement semantics.
-/

namespace Blanc.Lift.CallEffects

open Jaune

theorem Devm.pop_cons {d : Devm} {x : B256} {xs : List B256} (h : d.stack = x :: xs) :
    d.pop = .ok (x, d.withStack xs) := by
  rcases d with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  change stack = x :: xs at h
  subst h
  rfl

theorem Devm.popToNat_cons {d : Devm} {x : B256} {xs : List B256} (h : d.stack = x :: xs) :
    d.popToNat = .ok (x.toNat, d.withStack xs) := by
  rcases d with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  change stack = x :: xs at h
  subst h
  rfl

theorem Devm.popToAdr_cons {d : Devm} {x : B256} {xs : List B256} (h : d.stack = x :: xs) :
    d.popToAdr = .ok (x.toAdr, d.withStack xs) := by
  rcases d with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  change stack = x :: xs at h
  subst h
  rfl

theorem Devm.withStack_pop (d : Devm) (x : B256) (xs : List B256) :
    (d.withStack (x :: xs)).pop = .ok (x, d.withStack xs) := Devm.pop_cons rfl

theorem Devm.withStack_popToNat (d : Devm) (x : B256) (xs : List B256) :
    (d.withStack (x :: xs)).popToNat = .ok (x.toNat, d.withStack xs) := Devm.popToNat_cons rfl

theorem Devm.withStack_popToAdr (d : Devm) (x : B256) (xs : List B256) :
    (d.withStack (x :: xs)).popToAdr = .ok (x.toAdr, d.withStack xs) := Devm.popToAdr_cons rfl

/-- A successful `genericCall` step leaves exactly one word (the success flag) on its input
stack. -/
theorem genericCall_stack {sevm : Sevm} {d : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {transfer static : Bool} {ii is oi os : Nat}
    {code : ByteArray} {dp : Bool} {xl : Xlot} {sf : Devm}
    (h : XStep.Run (genericCall.step sevm d gas value caller target codeAddress transfer static
      ii is oi os code dp) xl (.ok sf)) :
    ∃ w, sf.stack = w :: d.stack := by
  simp only [genericCall.step] at h
  split at h
  · simp only [Bind.bind, Except.bind] at h
    split at h
    · cases XStep.run_ofExcept_error h
    · rename_i e hpush
      refine ⟨0, ?_⟩
      rw [Except.ok.inj h.2, (Devm.push_of_push hpush).stack]
      rfl
  · simp only [XStep.Run] at h
    rcases h with ⟨ex, -, hsplit⟩
    rcases ex with err | child
    · cases Resume.call_run_error hsplit.symm
    · exact ⟨_, Resume.call_stack_flag hsplit.symm⟩

/-- A generic call writes only a bounded reply inside its output window. -/
theorem genericCall_memory {sevm : Sevm} {devm d' : Devm} {gas : Nat} {value : B256}
    {caller target ca : Adr} {st isc : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot}
    (h : XStep.Run (genericCall.step sevm devm gas value caller target ca st isc ii is oi os code dp)
      xl (.ok d')) :
    ∃ ys : Bytes, ys.length ≤ os ∧ d'.memory = devm.memory.write oi ys := by
  unfold genericCall.step at h
  split at h
  · simp only [Bind.bind, Except.bind] at h
    split at h
    · cases XStep.run_ofExcept_error h
    rename_i d1 hp
    obtain ⟨-, hd⟩ := h
    cases hd
    exact ⟨[], Nat.zero_le _, (Devm.push_of_push hp).memory.symm⟩
  · obtain ⟨r, -, hr⟩ := h
    rcases r with e | child
    · exact (Resume.call_run_error hr.symm).elim
    · exact ⟨_, List.length_take_le _ _, Resume.call_memory hr.symm⟩

/-- The six-operand call forms pop their operands, push one status word, and
write at most the selected output size. No modern access/delegation premise is used. -/
theorem call6_run_effects {op : Xinst} {sevm : Sevm} {d d' : Devm}
    {g c ii is oi os : B256} {rest : Stack}
    (hop : op = .delegatecall ∨ op = .staticcall)
    (hstateGas : sevm.benvStat.rules.stateGas = none)
    (hs : d.stack = g :: c :: ii :: is :: oi :: os :: rest)
    (run : Ninst.Run sevm d (.exec op) d') :
    (∃ w, d'.stack = w :: rest) ∧
    ∃ ys : Bytes, ys.length ≤ os.toNat ∧
      d'.memory = (d.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat ys := by
  rcases hop with rfl | rfl
  all_goals
    obtain ⟨xl, -, pc, h⟩ := run
    simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
      hstateGas, Bind.bind, Except.bind,
      Devm.pop_cons hs, Devm.withStack_popToNat, Devm.withStack_popToAdr] at h
    split at h
    · cases XStep.run_ofExcept_error h
    rename_i d5 hc
    have hs5 : d5.stack = rest := by
      rw [← (Devm.burn_of_chargeGas hc).stack, ForkRules.accessDelegation_stack]
      cases sevm.benvStat.rules.access <;> rfl
    have hm5 : d5.memory = d.memory := by
      rw [← (Devm.burn_of_chargeGas hc).memory, ForkRules.accessDelegation_memory]
      cases sevm.benvStat.rules.access <;> rfl
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw⟩ := genericCall_stack h
      exact ⟨w, hw.trans (congrArg (w :: ·) hs5)⟩
    · obtain ⟨ys, hl, hm⟩ := genericCall_memory h
      refine ⟨ys, hl, ?_⟩
      rw [hm]
      change (d5.memory.extends _).write _ _ = _
      rw [hm5]

/-- A successful seven-operand CALL has the same stack/output-window effects,
including insufficient balance, depth failure, and both child outcomes. -/
theorem call_run_effects {sevm : Sevm} {d d' : Devm}
    {g c v ii is oi os : B256} {rest : Stack}
    (hstateGas : sevm.benvStat.rules.stateGas = none)
    (hs : d.stack = g :: c :: v :: ii :: is :: oi :: os :: rest)
    (run : Ninst.Run sevm d (.exec .call) d') :
    (∃ w, d'.stack = w :: rest) ∧
    ∃ ys : Bytes, ys.length ≤ os.toNat ∧
      d'.memory = (d.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat ys := by
  obtain ⟨xl, -, pc, h⟩ := run
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    hstateGas, Bind.bind, Except.bind, Except.assert,
    Devm.pop_cons hs, Devm.withStack_pop, Devm.withStack_popToNat,
    Devm.withStack_popToAdr] at h
  split at h
  · cases XStep.run_ofExcept_error h
  rename_i d5 hc
  have hs5 : d5.stack = rest := by
    rw [← (Devm.burn_of_chargeGas hc).stack, ForkRules.accessDelegation_stack]
    cases sevm.benvStat.rules.access <;> rfl
  have hm5 : d5.memory = d.memory := by
    rw [← (Devm.burn_of_chargeGas hc).memory, ForkRules.accessDelegation_memory]
    cases sevm.benvStat.rules.access <;> rfl
  split at h
  · cases XStep.run_ofExcept_error h
  split at h
  · split at h
    · cases XStep.run_ofExcept_error h
    rename_i d7 hp
    have hd : d' = _ := Except.ok.inj h.2
    subst hd
    refine ⟨⟨0, ?_⟩, ⟨[], Nat.zero_le _, ?_⟩⟩
    · change d7.stack = 0 :: rest
      rw [(Devm.push_of_push hp).stack]
      change 0 :: d5.stack = 0 :: rest
      rw [hs5]
    · change d7.memory = _
      rw [← (Devm.push_of_push hp).memory]
      change d5.memory.extends _ = _
      rw [hm5]
      rfl
  · refine ⟨?_, ?_⟩
    · obtain ⟨w, hw⟩ := genericCall_stack h
      exact ⟨w, hw.trans (congrArg (w :: ·) hs5)⟩
    · obtain ⟨ys, hl, hm⟩ := genericCall_memory h
      refine ⟨ys, hl, ?_⟩
      rw [hm]
      change (d5.memory.extends _).write _ _ = _
      rw [hm5]

end Blanc.Lift.CallEffects
