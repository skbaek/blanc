import Blanc.Ladder

namespace Blanc

open Jaune

/-- Exports the exact CALL frame and resumption selected by a spawned
`Ninst.step`, mirroring `of_run_call_val_with_depth_frame`. -/
theorem Ninst.step_call_spawn_exact
    {pc pc' : Nat} {sevm : Sevm} {s : Devm}
    {g c v ii is oi os : B256} {rest : Stack}
    {f : Frame} {rsm : Resume}
    (hspawn : Ninst.step ⟨pc, sevm, s⟩ Ninst.call = .spawn f rsm pc')
    (hstack : s.stack = g :: c :: v :: ii :: is :: oi :: os :: rest)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∃ (parent : Devm) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: c :: v :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory =
        s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      ((getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
          na = c.toAdr ∧ code = s.getCode c.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
          na = d ∧ code = s.getCode d ∧ dp = true)) ∧
      f = Frame.ofCall
        (callMsg sevm parent
          (min g.toNat (except64th avail)
            + (if v.toNat = 0 then 0 else gCallStipend))
          v sevm.currentTarget c.toAdr na true false
          ((s.memory.read ii.toNat is.toNat).1) code dp) ∧
      rsm = .call parent oi.toNat os.toNat := by
  have hx : Xinst.step sevm s .call = .spawn f rsm :=
    XStep.toStep_spawn (by
      simpa only [Ninst.call, Ninst.step_exec] using hspawn)
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  rw [hsg] at hx
  have hp : (g :: c :: v :: ii :: is :: oi :: os :: rest) <<+ s.stack := by
    rw [hstack]
    simpa only [List.append_nil] using
      (pref_append (g :: c :: v :: ii :: is :: oi :: os :: rest) [])
  rcases eq1 : Devm.pop s with _ | ⟨gas1, devm1⟩ <;>
    simp only [eq1] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have hv1 : g = gas1 := pref_head_unique hp (pref_append [gas1] devm1.stack)
  subst hv1
  replace hp := cons_pref_cons_inv hp
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;>
    simp only [eq2] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have f2 := Devm.pop_of_pop h_pop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  have hv2 : c = x2 := pref_head_unique hp (pref_append [x2] devm2.stack)
  subst hv2
  subst hx2
  replace hp := cons_pref_cons_inv hp
  rcases eq3 : Devm.pop devm2 with _ | ⟨value, devm3⟩ <;>
    simp only [eq3] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  have f3 := Devm.pop_of_pop eq3
  have e3 := f3.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hp
  have hv3 : v = value := pref_head_unique hp (pref_append [value] devm3.stack)
  subst hv3
  replace hp := cons_pref_cons_inv hp
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputIndex, devm4⟩ <;>
    simp only [eq4] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, hk4⟩
  have e4 := f4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rw [e4] at hp
  have hv4 : ii = x4 := pref_head_unique hp (pref_append [x4] devm4.stack)
  subst hv4
  subst hk4
  replace hp := cons_pref_cons_inv hp
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;>
    simp only [eq5] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, hk5⟩
  have e5 := f5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rw [e5] at hp
  have hv5 : is = x5 := pref_head_unique hp (pref_append [x5] devm5.stack)
  subst hv5
  subst hk5
  replace hp := cons_pref_cons_inv hp
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;>
    simp only [eq6] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, hk6⟩
  have e6 := f6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rw [e6] at hp
  have hv6 : oi = x6 := pref_head_unique hp (pref_append [x6] devm6.stack)
  subst hv6
  subst hk6
  replace hp := cons_pref_cons_inv hp
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;>
    simp only [eq7] at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rcases Devm.pop_of_popToNat_val eq7 with ⟨x7, f7, hk7⟩
  have e7 := f7.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e7
  rw [e7] at hp
  have hv7 : os = x7 := pref_head_unique hp (pref_append [x7] devm7.stack)
  subst hv7
  subst hk7
  replace hp := cons_pref_cons_inv hp
  have e_stack : s.stack
      = g :: c :: v :: ii :: is :: oi :: os :: devm7.stack := by
    rw [e1, e2, e3, e4, e5, e6, e7]
  have h_st7 : s.state = devm7.state :=
    (f1.state).trans ((f2.state).trans ((f3.state).trans ((f4.state).trans
      ((f5.state).trans ((f6.state).trans f7.state)))))
  have h_mem7 : s.memory = devm7.memory :=
    (f1.memory).trans ((f2.memory).trans ((f3.memory).trans ((f4.memory).trans
      ((f5.memory).trans ((f6.memory).trans f7.memory)))))
  clear e1 e2 e3 e4 e5 e6 e7 f1 f2 f3 f4 f5 f6 f7
  clear eq1 eq2 eq3 eq4 eq5 eq6 eq7 h_pop2
  rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress devm7 c.toAdr) c.toAdr with
    ⟨dp, na, code0, dagc, devm9⟩
  simp only [hp11] at hx
  have h_st9 : devm9.state = devm7.state := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_state]
    rfl
  have h_stk9 : devm9.stack = devm7.stack := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).stack) hp11
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_stack]
    rfl
  have h_mem9 : devm9.memory = devm7.memory := by
    have h := congrArg (fun q => (q.2.2.2.2 : Devm).memory) hp11
    dsimp at h
    rw [← h, GasSchedule.accessDelegation_memory]
    rfl
  have h_gc7 : (addAccessedAddress devm7 c.toAdr).state.getCode c.toAdr
      = s.getCode c.toAdr := by
    show devm7.state.getCode c.toAdr = s.getCode c.toAdr
    rw [← h_st7]
    rfl
  have h_del :
      (getDelegatedCodeAddress (s.getCode c.toAdr) = none ∧
        na = c.toAdr ∧ code0 = s.getCode c.toAdr ∧ dp = false) ∨
      (∃ d, getDelegatedCodeAddress (s.getCode c.toAdr) = some d ∧
        na = d ∧ code0 = s.getCode d ∧ dp = true) := by
    have h_acc := hp11
    dsimp only [GasSchedule.accessDelegation] at h_acc
    rw [h_gc7] at h_acc
    rcases hdel : getDelegatedCodeAddress (s.getCode c.toAdr) with _ | d <;>
      rw [hdel] at h_acc <;>
      simp only [Prod.mk.injEq] at h_acc
    · exact Or.inl ⟨rfl, h_acc.2.1.symm, h_acc.2.2.1.symm, h_acc.1.symm⟩
    · refine Or.inr ⟨d, rfl, h_acc.2.1.symm, ?_, h_acc.1.symm⟩
      rw [← h_acc.2.2.1]
      show (addAccessedAddress devm7 c.toAdr).state.getCode d = s.getCode d
      show devm7.state.getCode d = s.getCode d
      rw [← h_st7]
      rfl
  split at hx
  · simp only [XStep.ofExcept, reduceCtorEq] at hx
  rename_i devm10 eq16
  have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
  have h_stk10 : devm9.stack = devm10.stack := (Devm.burn_of_chargeGas eq16).stack
  have h_mem10 : devm9.memory = devm10.memory := (Devm.burn_of_chargeGas eq16).memory
  split at hx
  case h_1 => simp only [XStep.ofExcept, reduceCtorEq] at hx
  case h_2 =>
  split at hx
  · rcases eq20 : Devm.push 0
        (devm10.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]) with _ |
      ⟨devm12, eq20⟩ <;> simp only [eq20] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    · simp only [Pure.pure, Except.pure, XStep.ofExcept,
        reduceCtorEq] at hx
  · simp only [genericCall.step] at hx
    simp only [Pure.pure, Except.pure, XStep.ofExcept] at hx
    split at hx
    · simp only [Bind.bind, Except.bind] at hx
      rcases eq21 : Devm.push 0
          (((devm10.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []).withGasLeft
            (((devm10.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []).gasLeft +
              (calculateMsgCallGas v.toNat g.toNat devm9.gasLeft
                (devm7.extCost [(ii.toNat, is.toNat), (oi.toNat, os.toNat)])
                ((sevm.benvStat.rules.gas.accessCost c.toAdr devm7.accessedAddresses + dagc +
                    if ¬(devm9.getAcct c.toAdr).Empty ∨ v = 0 then 0 else gNewAccount) +
                  if v = 0 then 0 else sevm.benvStat.rules.gas.callValue)).2))
        with _ | ⟨devm13, eq21⟩ <;>
        simp only [eq21] at hx
      · simp only [reduceCtorEq] at hx
      · simp only [reduceCtorEq] at hx
    · simp only [XStep.spawn.injEq] at hx
      obtain ⟨avail, hstip⟩ :=
        calculateMsgCallGas_stipend (chargeGas_le eq16)
      rw [hstip] at hx
      let parent :=
        (devm10.memExtends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []
      have h_st_par : parent.state = s.state := by
        dsimp only [parent]
        show devm10.state = s.state
        rw [← h_st10, h_st9, ← h_st7]
      have h_stk_par : parent.stack = devm7.stack := by
        dsimp only [parent]
        show devm10.stack = devm7.stack
        rw [← h_stk10, h_stk9]
      have h_mem_par : parent.memory =
          s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] := by
        dsimp only [parent]
        show (devm10.memory).extends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] = _
        rw [← h_mem10, h_mem9, ← h_mem7]
      have h_cd : Array.sliceD parent.memory.data ii.toNat is.toNat 0 =
          (s.memory.read ii.toNat is.toNat).1 := by
        rw [h_mem_par]
        rfl
      rcases hx with ⟨hf, hr⟩
      refine ⟨parent, dp, na, code0, avail, by omega, ?_, h_st_par,
        h_mem_par, h_del, ?_, ?_⟩
      · rw [e_stack, h_stk_par]
      · rw [h_cd] at hf
        exact hf.symm
      · exact hr.symm

open Jaune.Ninst Ninst in
/-- An entered, successful value `CALL` to the frame's caller whose success word has been
consumed before the caller's return suffix.  The carrier retains the exact EIP-150 child
message, delegation choice, empty calldata/output windows, clean child settlement and caller
resumption, without imposing a callback-final storage delta.  DRIP's and PRORATA's
`AcceptedPayout` both unfold to it. -/
def AcceptedCallerPayout (sevm : Sevm) (p : B256)
    (callPre callPost guardPost returnPre : Devm) : Prop :=
  ∃ (gasWord : B256) (xs : Stack) (parent child : Devm) (xl : Xlot)
    (delegated : Bool) (nextAddress : Adr) (code : ByteArray) (avail pc : Nat),
    (gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: xs) <<+
      callPre.stack ∧
    Ninst.Run sevm callPre call callPost ∧
    Devm.PopBurn [1] callPost guardPost ∧
    Devm.Burn guardPost returnPre ∧
    Ninst.StepRun pc sevm callPre call xl (.ok callPost) ∧
    0 < sevm.depth ∧
    callPre.stack = gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 ::
      parent.stack ∧
    parent.state = callPre.state ∧
    parent.memory = callPre.memory.extends [(0, 0), (0, 0)] ∧
    parent.logs = callPre.logs ∧
    parent.output = callPre.output ∧
    ((getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) = none ∧
        nextAddress = sevm.caller.toB256.toAdr ∧
        code = callPre.getCode sevm.caller.toB256.toAdr ∧ delegated = false) ∨
      (∃ d, getDelegatedCodeAddress (callPre.getCode sevm.caller.toB256.toAdr) = some d ∧
        nextAddress = d ∧ code = callPre.getCode d ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg sevm parent
        (min gasWord.toNat (except64th avail) +
          (if p.toNat = 0 then 0 else gCallStipend))
        p sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
        ((callPre.memory.read 0 0).1) code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    (Resume.call parent 0 0).run (.ok child) = .ok callPost ∧
    callPost.state = child.state ∧
    callPost.returnData = child.output ∧
    callPost.memory = parent.memory.write 0 (child.output.take 0) ∧
    callPost.stack = (1 : B256) :: parent.stack

end Blanc
