import Blanc.Lift.MemMap

/-!
# Every memory writer writes one window at its destination operand

A successful step of a memory-writing instruction leaves memory as the old bytes, possibly grown
by expansion, with one window written at the destination operand (`Mem.WritesAt`).  Memory is
indexed by naturals (`Mem.write` at `dst.toNat`), so the written window never reaches below its
destination: every byte below it, inside the old logical size, is unchanged (`Mem.AgreeBelow`).
This holds whether or not the window would cross `2 ^ 256`; no gas argument is needed.

Covered: `MSTORE8`, the copies `CODECOPY`, `RETURNDATACOPY`, `EXTCODECOPY`, `MCOPY` (the
`MSTORE`/`CALLDATACOPY` equations are in `Blanc/Lift/MemMap.lean`), and the output windows of
`CALL`, `DELEGATECALL` and `STATICCALL` on Blanc's covered forks.  Contract-neutral.
-/

namespace Blanc.Lift

open Jaune

/-- `μ'` is `μ`'s bytes, possibly grown, with one window (perhaps empty) written at `dst`. -/
def Mem.WritesAt (μ μ' : Mem) (dst : Nat) : Prop :=
  ∃ (ν : Mem) (ys : Bytes), ν.data = μ.data ∧ μ.size ≤ ν.size ∧ μ' = ν.write dst ys

/-- `μ'` is at least as large as `μ` and agrees with it below `lo` inside `μ`'s size. -/
def Mem.AgreeBelow (μ μ' : Mem) (lo : Nat) : Prop :=
  μ.size ≤ μ'.size ∧ ∀ i, i < μ.size → i < lo → μ'.data.getD i 0 = μ.data.getD i 0

theorem Mem.WritesAt.agreeBelow {μ μ' : Mem} {dst : Nat} (h : Mem.WritesAt μ μ' dst) :
    Mem.AgreeBelow μ μ' dst := by
  obtain ⟨ν, ys, hd, hs, rfl⟩ := h
  have hag := Mem.write_agree ν dst ys
  refine ⟨le_trans hs hag.1, fun i hi hlo => ?_⟩
  rw [hag.2 i (by omega) (.inl hlo), hd]

theorem Mem.AgreeBelow.mono {μ μ' : Mem} {b b' : Nat} (h : Mem.AgreeBelow μ μ' b) (hb : b' ≤ b) :
    Mem.AgreeBelow μ μ' b' :=
  ⟨h.1, fun i hi hlo => h.2 i hi (by omega)⟩

theorem Mem.WritesAt.write (μ : Mem) (dst : Nat) (ys : Bytes) :
    Mem.WritesAt μ (μ.write dst ys) dst :=
  ⟨μ, ys, rfl, Nat.le_refl _, rfl⟩

theorem Mem.WritesAt.extends_write (μ : Mem) (ps : List (Nat × Nat)) (dst : Nat) (ys : Bytes) :
    Mem.WritesAt μ ((μ.extends ps).write dst ys) dst :=
  ⟨μ.extends ps, ys, rfl, memExtsSize_ge _ _, rfl⟩

theorem Mem.WritesAt.extends (μ : Mem) (ps : List (Nat × Nat)) (dst : Nat) :
    Mem.WritesAt μ (μ.extends ps) dst :=
  ⟨μ.extends ps, [], rfl, memExtsSize_ge _ _, rfl⟩

theorem Mem.WritesAt.of_keep {d d' : Devm} (h : MemKeep d d') (dst : Nat) :
    Mem.WritesAt d.memory d'.memory dst :=
  ⟨d'.memory, [], h.1, h.2, rfl⟩

/-! ## Regular writers -/

section Regular

variable {sevm : Sevm} {pre post : Devm}

/-- `MSTORE8` writes one byte at its first operand. -/
theorem mstore8_run_memory {o v : B256} {rest : List B256}
    (run : Ninst.Run sevm pre (.reg .mstore8) post) (hs : pre.stack = o :: v :: rest) :
    post.memory = pre.memory.write o.toNat [v.2.2.toUInt8] := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨w, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok e2
  cases h4
  obtain ⟨x, hp1, hi⟩ := Devm.pop_of_popToNat_val h1
  have hp2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  have hs1 := hp1.stack
  have hs2 := hp2.stack
  simp only [Stack.Pop, Split, List.cons_append, List.nil_append] at hs1 hs2
  rw [hs] at hs1
  simp only [List.cons.injEq] at hs1
  obtain ⟨rfl, hs1⟩ := hs1
  rw [← hs1] at hs2
  simp only [List.cons.injEq] at hs2
  obtain ⟨rfl, _⟩ := hs2
  subst hi
  simp only [Devm.memWrite_memory]
  rw [← hb.memory, ← hp2.memory, ← hp1.memory]

/-- The three popped operands of a copy, the first one its destination. -/
private theorem pop3 {d d1 d2 d3 : Devm} {i j k : Nat} {a : B256}
    (hs : d.stack.head? = some a)
    (h1 : Devm.popToNat d = .ok ⟨i, d1⟩) (h2 : Devm.popToNat d1 = .ok ⟨j, d2⟩)
    (h3 : Devm.popToNat d2 = .ok ⟨k, d3⟩) :
    i = a.toNat ∧ d3.memory = d.memory := by
  obtain ⟨x, hp1, hi⟩ := Devm.pop_of_popToNat_val h1
  obtain ⟨y, hp2, _⟩ := Devm.pop_of_popToNat_val h2
  obtain ⟨z, hp3, _⟩ := Devm.pop_of_popToNat_val h3
  have hs1 := hp1.stack
  simp only [Stack.Pop, Split, List.cons_append, List.nil_append] at hs1
  rw [hs1, List.head?_cons, Option.some.injEq] at hs
  subst hs
  exact ⟨hi, by rw [← hp3.memory, ← hp2.memory, ← hp1.memory]⟩

/-- `CALLDATACOPY` writes at its first operand. -/
theorem calldatacopy_run_writesAt {d : B256}
    (run : Ninst.Run sevm pre (.reg .calldatacopy) post) (hs : pre.stack.head? = some d) :
    Mem.WritesAt pre.memory post.memory d.toNat := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨j, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨⟨k, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
  obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok e3
  cases h5
  obtain ⟨rfl, hm⟩ := pop3 hs h1 h2 h3
  simp only [Devm.memWrite_memory]
  rw [← (Devm.burn_of_chargeGas h4).memory, hm]
  exact Mem.WritesAt.write _ _ _

/-- `CODECOPY` writes at its first operand. -/
theorem codecopy_run_writesAt {d : B256}
    (run : Ninst.Run sevm pre (.reg .codecopy) post) (hs : pre.stack.head? = some d) :
    Mem.WritesAt pre.memory post.memory d.toNat := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨j, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨⟨k, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
  obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok e3
  cases h5
  obtain ⟨rfl, hm⟩ := pop3 hs h1 h2 h3
  simp only [Devm.memWrite_memory]
  rw [← (Devm.burn_of_chargeGas h4).memory, hm]
  exact Mem.WritesAt.write _ _ _

/-- `RETURNDATACOPY` writes at its first operand. -/
theorem returndatacopy_run_writesAt {d : B256}
    (run : Ninst.Run sevm pre (.reg .returndatacopy) post)
    (hs : pre.stack.head? = some d) :
    Mem.WritesAt pre.memory post.memory d.toNat := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨j, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨⟨k, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
  obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok e3
  obtain ⟨rfl, hm⟩ := pop3 hs h1 h2 h3
  split at h5
  · cases h5
  · cases h5
    simp only [Devm.memWrite_memory]
    rw [← (Devm.burn_of_chargeGas h4).memory, hm]
    exact Mem.WritesAt.write _ _ _

/-- `MCOPY` writes at its first operand (after expanding over its source window). -/
theorem mcopy_run_writesAt {d : B256}
    (run : Ninst.Run sevm pre (.reg .mcopy) post) (hs : pre.stack.head? = some d) :
    Mem.WritesAt pre.memory post.memory d.toNat := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨j, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨⟨k, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
  obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok e3
  cases h5
  obtain ⟨rfl, hm⟩ := pop3 hs h1 h2 h3
  simp only [Devm.memWrite_memory]
  have hk := MemKeep.memRead d4 j k
  refine ⟨(d4.memRead j k).2.memory, _, ?_, ?_, rfl⟩
  · rw [hk.1, ← (Devm.burn_of_chargeGas h4).memory, hm]
  · rw [← hm, (Devm.burn_of_chargeGas h4).memory]; exact hk.2

/-- `EXTCODECOPY` writes at its second operand. -/
theorem extcodecopy_run_writesAt {d : B256}
    (run : Ninst.Run sevm pre (.reg .extcodecopy) post)
    (hs : pre.stack[1]? = some d) :
    Mem.WritesAt pre.memory post.memory d.toNat := by
  rcases of_run_reg run with ⟨pc, h⟩
  simp only [Rinst.run, Rinst.runCore] at h
  obtain ⟨⟨adr, d0⟩, h0, e0⟩ := Except.bind_eq_ok h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok e0
  obtain ⟨⟨j, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨⟨k, d3⟩, h3, e3⟩ := Except.bind_eq_ok e2
  have key : ∃ d4, d4.memory = d3.memory ∧ post = (Devm.balReadAccount sevm.benvStat.rules adr d4).memWrite i
      (ByteArray.sliceD ((Devm.balReadAccount sevm.benvStat.rules adr d4).getCode adr) j k
        Linst.stop.toUInt8) := by
    split at e3
    · obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok e3
      cases h5
      exact ⟨d4, (Devm.burn_of_chargeGas h4).memory.symm, rfl⟩
    · obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok e3
      cases h5
      exact ⟨d4, (Devm.burn_of_chargeGas h4).memory.symm, rfl⟩
  obtain ⟨d4, hm4, rfl⟩ := key
  rcases Devm.pop_of_popToAdr h0 with ⟨x0, -, hp0⟩
  have hs0 := (Devm.pop_of_pop hp0).stack
  simp only [Stack.Pop, Split, List.cons_append, List.nil_append] at hs0
  rw [hs0, List.getElem?_cons_succ, ← List.head?_eq_getElem?] at hs
  obtain ⟨rfl, hm⟩ := pop3 hs h1 h2 h3
  simp only [Devm.memWrite_memory]
  have hb : ∀ (rl : ForkRules) (x : Adr) (e : Devm), (Devm.balReadAccount rl x e).memory = e.memory :=
    fun _ _ _ => rfl
  rw [hb, hm4, hm, ← (Devm.pop_of_pop hp0).memory]
  exact Mem.WritesAt.write _ _ _

end Regular

/-! ## The calls' output windows -/

section Calls

variable {sevm : Sevm} {pre post : Devm}

/-- The memory a CALL-family resumption leaves: the parent's, with the output window written. -/
private theorem resume_writesAt {μ : Mem} {parent : Devm} {oi os : Nat} {r : Except _ Devm}
    {sf : Devm} (hpar : parent.memory = μ) (h : (Resume.call parent oi os).run r = .ok sf) :
    ∃ ys, sf.memory = μ.write oi ys := by
  rcases r with e | child
  · cases Resume.call_run_error h
  · exact ⟨_, by rw [Resume.call_memory h, hpar]⟩

/-- `CALL` writes only its output window, at its sixth operand. -/
theorem call_run_writesAt {oi : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (run : Ninst.Run sevm pre (.exec .call) post)
    (hs : pre.stack[5]? = some oi) :
    Mem.WritesAt pre.memory post.memory oi.toNat := by
  rcases run with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, Except.assert] at h_run
  rcases eq1 : Devm.pop pre with _ | ⟨gas1, s1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  have f1 := Devm.pop_of_pop eq1
  rcases eq2 : Devm.popToAdr s1 with _ | ⟨callee2, s2⟩ <;> simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, hp2⟩
  have f2 := Devm.pop_of_pop hp2
  rcases eq3 : Devm.pop s2 with _ | ⟨value3, s3⟩ <;> simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  have f3 := Devm.pop_of_pop eq3
  rcases eq4 : Devm.popToNat s3 with _ | ⟨n4, s4⟩ <;> simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, hk4⟩
  rcases eq5 : Devm.popToNat s4 with _ | ⟨n5, s5⟩ <;> simp only [eq5] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, hk5⟩
  rcases eq6 : Devm.popToNat s5 with _ | ⟨n6, s6⟩ <;> simp only [eq6] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, hk6⟩
  rcases eq7 : Devm.popToNat s6 with _ | ⟨n7, s7⟩ <;> simp only [eq7] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToNat_val eq7 with ⟨x7, f7, hk7⟩
  have e1 := f1.stack
  have e2 := f2.stack
  have e3 := f3.stack
  have e4 := f4.stack
  have e5 := f5.stack
  have e6 := f6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1 e2 e3 e4 e5 e6
  have estack : pre.stack = gas1 :: x2 :: value3 :: x4 :: x5 :: x6 :: s6.stack := by
    rw [e1, e2, e3, e4, e5, e6]
  have hoi : oi = x6 := by
    rw [estack] at hs
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
    exact hs.symm
  subst hoi hk6
  have hm7 : pre.memory = s7.memory :=
    f1.memory.trans (f2.memory.trans (f3.memory.trans (f4.memory.trans
      (f5.memory.trans (f6.memory.trans f7.memory)))))
  rw [hfork.rules_stateGas_none] at h_run
  split at h_run
  · rename_i _ heq
    cases heq
    split at h_run
    · cases XStep.run_ofExcept_error h_run
    · rename_i s10 eq10
      rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
          (addAccessedAddress s7 callee2) callee2 with
        ⟨dp, na, code0, dagc, s9⟩
      simp only [hp11] at eq10 h_run
      have hm9 : s9.memory = s7.memory := by
        have h := congrArg (fun q => (q.2.2.2.2 : Devm).memory) hp11
        dsimp only at h
        rw [← h, GasSchedule.accessDelegation_memory]
        rfl
      have hm10 : s10.memory = pre.memory :=
        (Devm.burn_of_chargeGas eq10).memory.symm.trans (hm9.trans hm7.symm)
      have hext : (s10.memExtends [(n4, n5), (oi.toNat, n7)]).memory =
          pre.memory.extends [(n4, n5), (oi.toNat, n7)] := by
        show s10.memory.extends _ = _
        rw [hm10]
      split at h_run
      · cases XStep.run_ofExcept_error h_run
      · split at h_run
        · rcases eq12 : Devm.push 0 (s10.memExtends [(n4, n5), (oi.toNat, n7)]) with
              _ | s12 <;> simp only [eq12] at h_run
          · cases XStep.run_ofExcept_error h_run
          · have h_ex := Except.ok.inj h_run.2
            subst h_ex
            show Mem.WritesAt pre.memory s12.memory oi.toNat
            rw [← (Devm.push_of_push eq12).memory, hext]
            exact Mem.WritesAt.extends _ _ _
        · simp only [genericCall.step] at h_run
          split at h_run
          · simp only [Bind.bind, Except.bind] at h_run
            split at h_run
            · cases XStep.run_ofExcept_error h_run
            · rename_i s12 hpush
              have h_ex := Except.ok.inj h_run.2
              subst h_ex
              rw [← (Devm.push_of_push hpush).memory]
              show Mem.WritesAt pre.memory (s10.memExtends [(n4, n5), (oi.toNat, n7)]).memory _
              rw [hext]
              exact Mem.WritesAt.extends _ _ _
          · simp only [XStep.Run] at h_run
            rcases h_run with ⟨r, -, h_split⟩
            have hext' : ((s10.memExtends [(n4, n5), (oi.toNat, n7)]).withReturnData []).memory =
                pre.memory.extends [(n4, n5), (oi.toNat, n7)] := hext
            obtain ⟨ys, hys⟩ := resume_writesAt hext' h_split.symm
            rw [hys]
            exact Mem.WritesAt.extends_write _ _ _ _
  · rename_i heq
    cases heq

/-- `genericCall.step` from a parent whose memory is `μ` leaves `μ` with the output window
written (or untouched, when no frame opens). -/
private theorem genericCall_writesAt {sevm : Sevm} {d post : Devm} {μ : Mem} {xl : Xlot}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr} {tv st : Bool}
    {ii is oi os : Nat} {code : ByteArray} {dp : Bool} (hd : d.memory = μ)
    (h : XStep.Run (genericCall.step sevm d gas value caller target codeAddress tv st ii is oi os
      code dp) xl (.ok post)) :
    ∃ ys, post.memory = μ.write oi ys := by
  simp only [genericCall.step] at h
  split at h
  · simp only [XStep.ofExcept, Bind.bind, Except.bind] at h
    split at h
    · cases XStep.run_ofExcept_error h
    · rename_i s12 hm
      split at hm
      · cases hm
      · rename_i s13 hpush
        cases hm
        have h_ex := Except.ok.inj h.2
        subst h_ex
        exact ⟨[], by rw [← (Devm.push_of_push hpush).memory, ← hd]; rfl⟩
  · simp only [XStep.Run] at h
    rcases h with ⟨r, -, h_split⟩
    have hpar : (d.withReturnData []).memory = μ := hd
    exact resume_writesAt hpar h_split.symm

/-- `DELEGATECALL` and `STATICCALL` write only their output window, at their fifth operand. -/
private theorem call6_run_writesAt {x : Xinst} (hx : x = .delegatecall ∨ x = .staticcall)
    {oi : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (run : Ninst.Run sevm pre (.exec x) post)
    (hs : pre.stack[4]? = some oi) :
    Mem.WritesAt pre.memory post.memory oi.toNat := by
  rcases hx with rfl | rfl
  all_goals
    rcases run with ⟨xl, h_fill, pc, h_run⟩
    simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
      Bind.bind, Except.bind, Except.assert] at h_run
    rcases eq1 : Devm.pop pre with _ | ⟨gas1, s1⟩ <;> simp only [eq1] at h_run
    · cases XStep.run_ofExcept_error_stateGas h_run
    have f1 := Devm.pop_of_pop eq1
    rcases eq2 : Devm.popToAdr s1 with _ | ⟨callee2, s2⟩ <;> simp only [eq2] at h_run
    · cases XStep.run_ofExcept_error_stateGas h_run
    rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, hp2⟩
    have f2 := Devm.pop_of_pop hp2
    rcases eq4 : Devm.popToNat s2 with _ | ⟨n4, s4⟩ <;> simp only [eq4] at h_run
    · cases XStep.run_ofExcept_error_stateGas h_run
    rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, hk4⟩
    rcases eq5 : Devm.popToNat s4 with _ | ⟨n5, s5⟩ <;> simp only [eq5] at h_run
    · cases XStep.run_ofExcept_error_stateGas h_run
    rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, hk5⟩
    rcases eq6 : Devm.popToNat s5 with _ | ⟨n6, s6⟩ <;> simp only [eq6] at h_run
    · cases XStep.run_ofExcept_error_stateGas h_run
    rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, hk6⟩
    rcases eq7 : Devm.popToNat s6 with _ | ⟨n7, s7⟩ <;> simp only [eq7] at h_run
    · cases XStep.run_ofExcept_error_stateGas h_run
    rcases Devm.pop_of_popToNat_val eq7 with ⟨x7, f7, hk7⟩
    have e1 := f1.stack
    have e2 := f2.stack
    have e4 := f4.stack
    have e5 := f5.stack
    have e6 := f6.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1 e2 e4 e5 e6
    have estack : pre.stack = gas1 :: x2 :: x4 :: x5 :: x6 :: s6.stack := by
      rw [e1, e2, e4, e5, e6]
    have hoi : oi = x6 := by
      rw [estack] at hs
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hs
      exact hs.symm
    subst hoi hk6
    have hm7 : pre.memory = s7.memory :=
      f1.memory.trans (f2.memory.trans (f4.memory.trans
        (f5.memory.trans (f6.memory.trans f7.memory))))
    rw [hfork.rules_stateGas_none] at h_run
    split at h_run
    · rename_i _ heq
      cases heq
      split at h_run
      · cases XStep.run_ofExcept_error h_run
      · rename_i s10 eq10
        rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
            (addAccessedAddress s7 callee2) callee2 with
          ⟨dp, na, code0, dagc, s9⟩
        simp only [hp11] at eq10 h_run
        have hm9 : s9.memory = s7.memory := by
          have h := congrArg (fun q => (q.2.2.2.2 : Devm).memory) hp11
          dsimp only at h
          rw [← h, GasSchedule.accessDelegation_memory]
          rfl
        have hext : (s10.memExtends [(n4, n5), (oi.toNat, n7)]).memory =
            pre.memory.extends [(n4, n5), (oi.toNat, n7)] := by
          show s10.memory.extends _ = _
          rw [(Devm.burn_of_chargeGas eq10).memory.symm.trans (hm9.trans hm7.symm)]
        obtain ⟨ys, hys⟩ := genericCall_writesAt hext h_run
        rw [hys]
        exact Mem.WritesAt.extends_write _ _ _ _
    · rename_i heq
      cases heq

/-- `DELEGATECALL` writes only its output window, at its fifth operand. -/
theorem delegatecall_run_writesAt {oi : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (run : Ninst.Run sevm pre (.exec .delegatecall) post)
    (hs : pre.stack[4]? = some oi) :
    Mem.WritesAt pre.memory post.memory oi.toNat :=
  call6_run_writesAt (.inl rfl) hfork run hs

/-- `STATICCALL` writes only its output window, at its fifth operand. -/
theorem staticcall_run_writesAt {oi : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (run : Ninst.Run sevm pre (.exec .staticcall) post)
    (hs : pre.stack[4]? = some oi) :
    Mem.WritesAt pre.memory post.memory oi.toNat :=
  call6_run_writesAt (.inr rfl) hfork run hs

end Calls

end Blanc.Lift
