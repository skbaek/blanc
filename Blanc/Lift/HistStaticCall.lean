import Blanc.Lift.StaticCall
import Blanc.Lift.CallEffects

/-!
# Historical `STATICCALL` inversions

The value-carrying `STATICCALL` inversion of `LadderBase`
(`of_step_staticcall_val_with_depth_frame_cause`) and the walk step `ri_staticcall_bounded` take
`CoveredFork`, which fixes the EIP-2929 access schedule and enabled delegation. This module proves
them from `rules.stateGas = none` alone, under the frame's actual access schedule and delegation
flag:

* `CallCodeH` — call-code resolution under the actual delegation flag (the modern disjunction
  when enabled, `CallCodeH_enabled`; the target's own code otherwise), with
  `accessDelegation_fields` and `callCodeH_of_accessDelegation`;
* `of_step_staticcall_val_with_depth_frame_causeH`, `of_run_staticcall_val_with_depth_causeH`
  and `StatcallFailureCauseH`; `of_step_staticcall_val_with_depth_frame_causeH_covered`
  recovers the modern statement;
* the log-list decomposition under the actual rules (`Xinst.step_shapeLogsH`,
  `Xinst.logs_of_okH`, `Exec.logs_eq_of_static_okH`, `Exec.logs_committedPost_eq_of_staticH`)
  and `Ninst.world_of_quietH`;
* `ReturnDataBound.staticcall_returnData_length_ltH` / `call_returnData_length_ltH`;
* `StaticAnsweredH` (`StaticAnsweredH.of_covered`), `ri_staticcallH`, `ri_staticcall_boundedH`,
  `rx_staticcallH`, and `ri_staticcall_boundedH_covered` recovering the modern statement.

Nothing here mentions a contract.
-/

namespace Blanc

open Jaune

/-- The code resolution of a call target under the actual delegation flag: EIP-7702 designator
resolution when enabled, the target's own code (no precompile disabling) otherwise. -/
def CallCodeH (deleg : Bool) (s : Devm) (t na : Adr) (code : ByteArray) (dp : Bool) : Prop :=
  if deleg = true then
    (getDelegatedCodeAddress (s.getCode t) = none ∧ na = t ∧ code = s.getCode t ∧ dp = false) ∨
      (∃ d, getDelegatedCodeAddress (s.getCode t) = some d ∧ na = d ∧ code = s.getCode d ∧
        dp = true)
  else na = t ∧ code = s.getCode t ∧ dp = false

theorem CallCodeH_enabled {s : Devm} {t na : Adr} {code : ByteArray} {dp : Bool} :
    CallCodeH true s t na code dp ↔
      ((getDelegatedCodeAddress (s.getCode t) = none ∧ na = t ∧ code = s.getCode t ∧
          dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode t) = some d ∧ na = d ∧ code = s.getCode d ∧
          dp = true)) := by
  simp only [CallCodeH, ↓reduceIte]

/-- Why a value-carrying `STATICCALL` returned its failure flag, under the actual delegation
flag (`StatcallFailureCause` with `CallCodeH`). -/
def StatcallFailureCauseH (sevm : Sevm) (s : Devm)
    (g t ii is oi os : B256) (out : Bytes) : Prop :=
  out = [] ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      CallCodeH sevm.benvStat.rules.delegationEnabled s t.toAdr na code dp ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr na true true
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = true ∧
      out = child.output

theorem StatcallFailureCauseH.of_covered {sevm : Sevm} {s : Devm} {g t ii is oi os : B256}
    {out : Bytes} (hfork : CoveredFork sevm.benvStat.fork)
    (h : StatcallFailureCauseH sevm s g t ii is oi os out) :
    StatcallFailureCause sevm s g t ii is oi os out := by
  have hdeleg : sevm.benvStat.rules.delegationEnabled = true :=
    hfork.cases (motive := fun f => f.ruleSet.delegationEnabled = true) rfl rfl rfl rfl
  rcases h with h | ⟨parent, child, xl, dp, na, code, avail, h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl h
  · rw [hdeleg, CallCodeH_enabled] at h5
    exact Or.inr ⟨parent, child, xl, dp, na, code, avail, h1, h2, h3, h4, h5, h6⟩

/-- Delegation access keeps the frame's state, stack, memory, transient storage, logs and output,
whichever delegation flag is selected. -/
theorem accessDelegation_fields {rules : ForkRules} {D D' : Devm} {t na : Adr}
    {code : ByteArray} {dp : Bool} {dagc : Nat}
    (h : rules.accessDelegation D t = (dp, na, code, dagc, D')) :
    D'.state = D.state ∧ D'.stack = D.stack ∧ D'.memory = D.memory ∧
      D'.transientStorage = D.transientStorage ∧ D'.logs = D.logs ∧ D'.output = D.output := by
  have e : D' = (rules.accessDelegation D t).2.2.2.2 := by rw [h]
  subst e
  have frame := ForkRules.accessDelegation_instructionFrame rules D t
  refine ⟨frame.state.symm, ForkRules.accessDelegation_stack,
    ForkRules.accessDelegation_memory, frame.transientStorage.symm, ?_, ?_⟩
  · unfold ForkRules.accessDelegation
    split
    · exact GasSchedule.accessDelegation_logs
    · rfl
  · unfold ForkRules.accessDelegation
    split
    · exact GasSchedule.accessDelegation_output
    · rfl

/-- Delegation access resolves the call code as `CallCodeH` states, over any frame whose state is
the caller's. -/
theorem callCodeH_of_accessDelegation {rules : ForkRules} {D D' s : Devm} {t na : Adr}
    {code : ByteArray} {dp : Bool} {dagc : Nat} (hstate : D.state = s.state)
    (h : rules.accessDelegation D t = (dp, na, code, dagc, D')) :
    CallCodeH rules.delegationEnabled s t na code dp := by
  have hgc : ∀ a, D.state.getCode a = s.getCode a := fun a => by
    rw [hstate]
    rfl
  unfold ForkRules.accessDelegation at h
  unfold CallCodeH
  split at h
  · rename_i hdeleg
    rw [ite_eq_left hdeleg]
    dsimp only [GasSchedule.accessDelegation] at h
    rw [hgc t] at h
    rcases hdel : getDelegatedCodeAddress (s.getCode t) with _ | d <;>
      rw [hdel] at h <;>
      simp only [Prod.mk.injEq] at h
    · exact Or.inl ⟨rfl, h.2.1.symm, h.2.2.1.symm, h.1.symm⟩
    · refine Or.inr ⟨d, rfl, h.2.1.symm, ?_, h.1.symm⟩
      rw [← h.2.2.1]
      exact hgc d
  · rename_i hdeleg
    rw [ite_eq_right hdeleg]
    simp only [Prod.mk.injEq] at h
    exact ⟨h.2.1.symm, by rw [← h.2.2.1]; exact hgc t, h.1.symm⟩


theorem of_step_staticcall_val_with_depth_frame_causeH
    {pc : Nat} {xl : Xlot} {sevm : Sevm} {s sf : Devm} {g t ii is oi os : B256} {xs : Stack}
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_fill : Xlot.Filled xl)
    (h_run : Ninst.StepRun pc sevm s Ninst.staticcall xl (.ok sf))
    (hsg : sevm.benvStat.rules.stateGas = none) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf ∧
      ∃ out : Bytes,
        sf.returnData = out ∧
        sf.memory = (s.memory.extends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
            oi.toNat (out.take os.toNat) ∧
        StatcallFailureCauseH sevm s g t ii is oi os out) ∨
    ∃ (parent child : Devm) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      parent.logs = s.logs ∧
      parent.output = s.output ∧
      CallCodeH sevm.benvStat.rules.delegationEnabled s t.toAdr na code dp ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr na true true
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack ∧
      Ninst.step ⟨pc, sevm, s⟩ Ninst.staticcall =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0
            sevm.currentTarget t.toAdr na true true
            (s.memory.read ii.toNat is.toNat).1 code dp))
          (Resume.call parent oi.toNat os.toNat) (pc + 1) := by
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind] at h_run
  -- pop gas
  rcases eq1 : Devm.pop s with _ | ⟨gas1, devm1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have hv1 : g = gas1 := pref_head_unique hp (pref_append [gas1] devm1.stack)
  subst hv1
  replace hp := cons_pref_cons_inv hp
  -- pop target
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨target, devm2⟩ <;>
    simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToAdr eq2 with ⟨x2, hx2, h_pop2⟩
  have f2 := Devm.pop_of_pop h_pop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hp
  have hv2 : t = x2 := pref_head_unique hp (pref_append [x2] devm2.stack)
  subst hv2
  subst hx2
  replace hp := cons_pref_cons_inv hp
  -- pop the four indices/sizes
  rcases eq3 : Devm.popToNat devm2 with _ | ⟨inputIndex, devm3⟩ <;>
    simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToNat_val eq3 with ⟨x3, f3, hk3⟩
  have e3 := f3.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hp
  have hv3 : ii = x3 := pref_head_unique hp (pref_append [x3] devm3.stack)
  subst hv3
  subst hk3
  replace hp := cons_pref_cons_inv hp
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputSize, devm4⟩ <;>
    simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToNat_val eq4 with ⟨x4, f4, hk4⟩
  have e4 := f4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  rw [e4] at hp
  have hv4 : is = x4 := pref_head_unique hp (pref_append [x4] devm4.stack)
  subst hv4
  subst hk4
  replace hp := cons_pref_cons_inv hp
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨outputIndex, devm5⟩ <;>
    simp only [eq5] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToNat_val eq5 with ⟨x5, f5, hk5⟩
  have e5 := f5.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e5
  rw [e5] at hp
  have hv5 : oi = x5 := pref_head_unique hp (pref_append [x5] devm5.stack)
  subst hv5
  subst hk5
  replace hp := cons_pref_cons_inv hp
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputSize, devm6⟩ <;>
    simp only [eq6] at h_run
  · cases XStep.run_ofExcept_error_stateGas h_run
  rcases Devm.pop_of_popToNat_val eq6 with ⟨x6, f6, hk6⟩
  have e6 := f6.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e6
  rw [e6] at hp
  have hv6 : os = x6 := pref_head_unique hp (pref_append [x6] devm6.stack)
  subst hv6
  subst hk6
  replace hp := cons_pref_cons_inv hp
  have e_stack : s.stack = g :: t :: ii :: is :: oi :: os :: devm6.stack := by
    rw [e1, e2, e3, e4, e5, e6]
  have h_st6 : s.state = devm6.state :=
    (f1.state).trans ((f2.state).trans ((f3.state).trans
      ((f4.state).trans ((f5.state).trans f6.state))))
  have h_mem6 : s.memory = devm6.memory :=
    (f1.memory).trans ((f2.memory).trans ((f3.memory).trans
      ((f4.memory).trans ((f5.memory).trans f6.memory))))
  have h_tra6 : s.transientStorage = devm6.transientStorage :=
    (f1.transientStorage).trans ((f2.transientStorage).trans
      ((f3.transientStorage).trans ((f4.transientStorage).trans
        ((f5.transientStorage).trans f6.transientStorage))))
  have h_logs6 : s.logs = devm6.logs :=
    (f1.logs).trans ((f2.logs).trans ((f3.logs).trans
      ((f4.logs).trans ((f5.logs).trans f6.logs))))
  have h_output6 : s.output = devm6.output :=
    (f1.output).trans ((f2.output).trans ((f3.output).trans
      ((f4.output).trans ((f5.output).trans f6.output))))
  clear e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 f5 f6
  clear h_pop2
  -- the access image and delegation resolution, under the actual rules
  simp only [hsg] at h_run
  rcases hac : sevm.benvStat.rules.access with gflat | _
  swap
  -- EIP-2929 access: the target is warmed before delegation resolution
  simp only [hac] at h_run
  rcases hp10 : sevm.benvStat.rules.accessDelegation (addAccessedAddress devm6 t.toAdr)
      t.toAdr with ⟨dp, na, code0, dagc, devm8⟩
  simp only [hp10] at h_run
  have hbase := accessDelegation_fields hp10
  have h_del : CallCodeH sevm.benvStat.rules.delegationEnabled s t.toAdr na code0 dp :=
    callCodeH_of_accessDelegation (D := addAccessedAddress devm6 t.toAdr) h_st6.symm hp10
  swap
  -- flat access: no warming
  simp only [hac] at h_run
  rcases hp10 : sevm.benvStat.rules.accessDelegation devm6 t.toAdr with
    ⟨dp, na, code0, dagc, devm8⟩
  simp only [hp10] at h_run
  have hbase := accessDelegation_fields hp10
  have h_del : CallCodeH sevm.benvStat.rules.delegationEnabled s t.toAdr na code0 dp :=
    callCodeH_of_accessDelegation (D := devm6) h_st6.symm hp10
  all_goals
    have h_st8 : devm8.state = devm6.state := hbase.1
    have h_stk8 : devm8.stack = devm6.stack := hbase.2.1
    have h_mem8 : devm8.memory = devm6.memory := hbase.2.2.1
    have h_tra8 : devm8.transientStorage = devm6.transientStorage := hbase.2.2.2.1
    have h_logs8 : devm8.logs = devm6.logs := hbase.2.2.2.2.1
    have h_output8 : devm8.output = devm6.output := hbase.2.2.2.2.2
    split at h_run
    · cases XStep.run_ofExcept_error h_run
    rename_i devm9 eq14
    have h_st9 : devm8.state = devm9.state := (Devm.burn_of_chargeGas eq14).state
    have h_stk9 : devm8.stack = devm9.stack := (Devm.burn_of_chargeGas eq14).stack
    have h_mem9 : devm8.memory = devm9.memory := (Devm.burn_of_chargeGas eq14).memory
    have h_tra9 : devm8.transientStorage = devm9.transientStorage :=
      (Devm.burn_of_chargeGas eq14).transientStorage
    have h_logs9 : devm8.logs = devm9.logs :=
      (Devm.burn_of_chargeGas eq14).logs
    have h_output9 : devm8.output = devm9.output :=
      (Devm.burn_of_chargeGas eq14).output
    simp only [genericCall.step] at h_run
    split at h_run
    · -- depth limit: no frame opened
      simp only [Bind.bind, Except.bind] at h_run
      split at h_run
      case h_1 => cases XStep.run_ofExcept_error h_run
      case h_2 =>
      rename_i devm11 h_push
      left
      have h_ex := Except.ok.inj h_run.2
      rw [h_ex]
      have h_stk := (Devm.push_of_push h_push).stack
      refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
      · show ((0 : B256) :: xs) <<+ devm11.stack
        rw [h_stk]
        show ((0 : B256) :: xs) <<+ (0 : B256) ::
          ((devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []).stack
        show ((0 : B256) :: xs) <<+ (0 : B256) ::
          (devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).stack
        have h_stk10 :
            (devm9.memExtends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).stack
              = devm6.stack := by
          show devm9.stack = devm6.stack
          rw [← h_stk9, h_stk8]
        rw [h_stk10]
        exact pref_cons hp
      · show s.state = devm11.state
        rw [← (Devm.push_of_push h_push).state]
        show s.state = devm9.state
        rw [← h_st9, h_st8, ← h_st6]
      · show s.transientStorage = devm11.transientStorage
        rw [← (Devm.push_of_push h_push).transientStorage]
        show s.transientStorage = devm9.transientStorage
        rw [← h_tra9, h_tra8, ← h_tra6]
      · refine ⟨[], ?_, ?_, Or.inl rfl⟩
        · show devm11.returnData = []
          exact (Devm.push_of_push h_push).returnData.symm
        · show devm11.memory =
            (s.memory.extends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
                oi.toNat (([] : Bytes).take os.toNat)
          simp only [List.take_nil]
          change devm11.memory =
            s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]
          rw [← (Devm.push_of_push h_push).memory]
          show devm9.memory.extends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] = _
          rw [← h_mem9, h_mem8, ← h_mem6]
    · -- the static child is executed (synchronously for precompiles)
      rename_i h_depth_ne
      simp only [XStep.Run] at h_run
      rcases h_run with ⟨ex', run_pm₀, h_split⟩
      rcases ex' with err' | child
      · cases Resume.call_run_error h_split.symm
      have h_stk_par :
          ((devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []).stack
            = devm6.stack := by
        show devm9.stack = devm6.stack
        rw [← h_stk9, h_stk8]
      have h_st_par :
          ((devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []).state
            = s.state := by
        show devm9.state = s.state
        rw [← h_st9, h_st8, ← h_st6]
      have h_tra_par :
          ((devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
            []).transientStorage = s.transientStorage := by
        show devm9.transientStorage = s.transientStorage
        rw [← h_tra9, h_tra8, ← h_tra6]
      have h_mem_par :
          ((devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
            []).memory
            = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] := by
        show devm9.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]
          = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]
        rw [← h_mem9, h_mem8, ← h_mem6]
      have h_logs_par :
          ((devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
            []).logs = s.logs := by
        show devm9.logs = s.logs
        rw [← h_logs9, h_logs8, ← h_logs6]
      have h_output_par :
          ((devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
            []).output = s.output := by
        show devm9.output = s.output
        rw [← h_output9, h_output8, ← h_output6]
      obtain ⟨avail, hstip⟩ := calculateMsgCallGas_stipend (chargeGas_le eq14)
      rw [hstip] at run_pm₀
      have h_cd : Array.sliceD
          ((devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData
            []).memory.data ii.toNat is.toNat 0
          = (s.memory.read ii.toNat is.toNat).1 := by
        rw [h_mem_par]
        rfl
      rw [h_cd] at run_pm₀
      by_cases herr : child.error.isSome
      · left
        have h_roll : Devm.WorldEq child
            ((devm9.memExtends
              [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData []) :=
          ProcessMessage.rollback_of_error run_pm₀ herr
        refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
        · have hsf := Resume.call_stack_flag h_split.symm
          rw [ite_eq_left herr] at hsf
          rw [hsf, h_stk_par]
          exact pref_cons hp
        · rw [Resume.call_state h_split.symm, h_roll.1, h_st_par]
        · rw [Resume.call_transientStorage h_split.symm, h_roll.2, h_tra_par]
        · refine ⟨child.output, Resume.call_returnData h_split.symm, ?_,
            Or.inr ?_⟩
          · rw [Resume.call_memory h_split.symm, h_mem_par]
          · refine ⟨
              (devm9.memExtends
                [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData [],
              child, xl, dp, na, code0, avail,
              by omega, by rw [e_stack, h_stk_par], h_st_par, h_mem_par,
              h_del, h_fill, ?_, herr, rfl⟩
            simpa only [ProcessMessage, ite_true, Nat.add_zero] using run_pm₀
      · right
        have spawned : Ninst.step ⟨pc, sevm, s⟩ Ninst.staticcall =
            .spawn (Frame.ofCall
              (callMsg sevm
                ((devm9.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData [])
                (min g.toNat (except64th avail)) 0 sevm.currentTarget t.toAdr na true true
                (s.memory.read ii.toNat is.toNat).1 code0 dp))
              (Resume.call
                ((devm9.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData [])
                oi.toNat os.toNat) (pc + 1) := by
          simp only [Ninst.staticcall, Ninst.step_exec, Xinst.step, hsg, hac,
            Bind.bind, Except.bind, eq1, eq2, eq3, eq4, eq5, eq6, hp10, eq14,
            Except.pure, Pure.pure, XStep.ofExcept, genericCall.step,
            ite_eq_right h_depth_ne, XStep.toStep]
          rw [hstip, h_cd]
          simp only [ite_true, Nat.add_zero]
        refine ⟨(devm9.memExtends
            [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).withReturnData [],
          child, dp, na, code0, avail,
          by omega, by rw [e_stack, h_stk_par], h_st_par, h_mem_par,
          h_logs_par, h_output_par, h_del,
          h_fill, ?_, by cases h : child.error.isSome <;> first | rfl | exact (herr h).elim, h_split.symm,
          Resume.call_state h_split.symm, Resume.call_returnData h_split.symm,
          Resume.call_memory h_split.symm,
          by rw [Resume.call_stack_flag h_split.symm, ite_eq_right herr], spawned⟩
        simpa only [ProcessMessage, ite_true, Nat.add_zero] using run_pm₀



/-- The H inversion recovers the modern `of_step_staticcall_val_with_depth_frame_cause`
statement on a covered fork. -/
theorem of_step_staticcall_val_with_depth_frame_causeH_covered
    {pc : Nat} {xl : Xlot} {sevm : Sevm} {s sf : Devm} {g t ii is oi os : B256} {xs : Stack}
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_fill : Xlot.Filled xl)
    (h_run : Ninst.StepRun pc sevm s Ninst.staticcall xl (.ok sf))
    (hfork : CoveredFork sevm.benvStat.fork) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf ∧
      ∃ out : Bytes,
        sf.returnData = out ∧
        sf.memory = (s.memory.extends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
            oi.toNat (out.take os.toNat) ∧
        StatcallFailureCause sevm s g t ii is oi os out) ∨
    ∃ (parent child : Devm) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      parent.logs = s.logs ∧
      parent.output = s.output ∧
      ((getDelegatedCodeAddress (s.getCode t.toAdr) = none ∧
          na = t.toAdr ∧ code = s.getCode t.toAdr ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (s.getCode t.toAdr) = some d ∧
          na = d ∧ code = s.getCode d ∧ dp = true)) ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr na true true
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack ∧
      Ninst.step ⟨pc, sevm, s⟩ Ninst.staticcall =
        .spawn (Frame.ofCall
          (callMsg sevm parent (min g.toNat (except64th avail)) 0
            sevm.currentTarget t.toAdr na true true
            (s.memory.read ii.toNat is.toNat).1 code dp))
          (Resume.call parent oi.toNat os.toNat) (pc + 1) := by
  have hdeleg : sevm.benvStat.rules.delegationEnabled = true :=
    hfork.cases (motive := fun f => f.ruleSet.delegationEnabled = true) rfl rfl rfl rfl
  rcases of_step_staticcall_val_with_depth_frame_causeH hp h_fill h_run
      hfork.rules_stateGas_none with ⟨h1, h2, out, h3, h4, cause⟩ | ⟨parent, child, dp, na,
      code, avail, h1, h2, h3, h4, h5, h6, hdel, rest⟩
  · exact Or.inl ⟨h1, h2, out, h3, h4, cause.of_covered hfork⟩
  · rw [hdeleg, CallCodeH_enabled] at hdel
    exact Or.inr ⟨parent, child, dp, na, code, avail, h1, h2, h3, h4, h5, h6, hdel, rest⟩

/-- `of_run_staticcall_val_with_depth_cause` under `rules.stateGas = none` and the actual rules. -/
theorem of_run_staticcall_val_with_depth_causeH
    {sevm : Sevm} {s sf : Devm} {g t ii is oi os : B256} {xs : Stack}
    (hp : (g :: t :: ii :: is :: oi :: os :: xs) <<+ s.stack)
    (h_run : Ninst.Run sevm s Ninst.staticcall sf)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    (((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf ∧
      ∃ out : Bytes,
        sf.returnData = out ∧
        sf.memory = (s.memory.extends
          [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write
            oi.toNat (out.take os.toNat) ∧
        StatcallFailureCauseH sevm s g t ii is oi os out) ∨
    ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr)
      (code : ByteArray) (avail : Nat),
      0 < sevm.depth ∧
      s.stack = g :: t :: ii :: is :: oi :: os :: parent.stack ∧
      parent.state = s.state ∧
      parent.memory
        = s.memory.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)] ∧
      parent.logs = s.logs ∧
      parent.output = s.output ∧
      CallCodeH sevm.benvStat.rules.delegationEnabled s t.toAdr na code dp ∧
      Xlot.Filled xl ∧
      ProcessMessage
        (callMsg sevm parent (min g.toNat (except64th avail)) 0
          sevm.currentTarget t.toAdr na true true
          ((s.memory.read ii.toNat is.toNat).1) code dp)
        xl (.ok child) ∧
      child.error.isSome = false ∧
      (Resume.call parent oi.toNat os.toNat).run (.ok child) = .ok sf ∧
      sf.state = child.state ∧
      sf.returnData = child.output ∧
      sf.memory = parent.memory.write oi.toNat (child.output.take os.toNat) ∧
      sf.stack = (1 : B256) :: parent.stack := by
  rcases h_run with ⟨xl, filled, pc, primitive⟩
  rcases of_step_staticcall_val_with_depth_frame_causeH hp filled primitive hsg with failed | success
  · exact Or.inl failed
  · obtain ⟨parent, child, dp, na, code, avail, depth, stack, state, memory, logs, output,
      delegated, filled, process, clean, resumed, childState, childOutput, childMemory,
      childStack, spawned⟩ := success
    exact Or.inr ⟨parent, child, xl, dp, na, code, avail, depth, stack, state, memory,
      logs, output, delegated, filled, process, clean, resumed, childState, childOutput,
      childMemory, childStack⟩

end Blanc

namespace Blanc.Lift

open Jaune AbstractStackSafety
open scoped LogOutputHinv

/-! ## Log lists under the actual rules

`Quiet.lean`'s log-list decomposition (`Xinst.step_shapeLogs` .. `Ninst.world_of_quiet`) takes
`CoveredFork`; the twins below need only `rules.stateGas = none` and keep the actual access
schedule and delegation flag inside the call arms. -/

/-- Every executable instruction without state gas has a log-list shape, under the actual
access schedule and delegation flag. -/
theorem Xinst.step_shapeLogsH (sevm : Sevm) (devm : Devm) (x : Xinst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    Xinst.ShapeLogs sevm devm (x = .create ∨ x = .create2) (Xinst.step sevm devm x) := by
  cases x with
  | create =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToNat d1) fun _ d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.popToNat d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bindE h3 (LogsWalk.chargeGas _ d3) fun d4 h4 => ?_
    exact ShapeLogs.create (Or.inl trivial) h4
  | create2 =>
    simp only [Xinst.step, hsg]
    split
    · refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
      refine ShapeLogs.bind h1 (LogsWalk.popToNat d1) fun _ d2 h2 => ?_
      refine ShapeLogs.bind h2 (LogsWalk.popToNat d2) fun _ d3 h3 => ?_
      refine ShapeLogs.bind h3 (LogsWalk.pop d3) fun _ d4 h4 => ?_
      refine ShapeLogs.bindE h4 (LogsWalk.chargeGas _ d4) fun d5 h5 => ?_
      exact ShapeLogs.create (Or.inr trivial) h5
    · exact ShapeLogs.error rfl
  | call =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToAdr d1) fun callee d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.pop d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bind h3 (LogsWalk.popToNat d3) fun _ d4 h4 => ?_
    refine ShapeLogs.bind h4 (LogsWalk.popToNat d4) fun _ d5 h5 => ?_
    refine ShapeLogs.bind h5 (LogsWalk.popToNat d5) fun _ d6 h6 => ?_
    refine ShapeLogs.bind h6 (LogsWalk.popToNat d6) fun _ d7 h7 => ?_
    dsimp only
    let dAccess : Devm := match sevm.benvStat.rules.access with
      | .eip2929 => addAccessedAddress d7 callee
      | .flat _ => d7
    have hAccess : dAccess.logs = devm.logs := by
      dsimp only [dAccess]
      split
      · exact h7
      · exact h7
    rcases hdel : sevm.benvStat.rules.accessDelegation dAccess callee with
      ⟨dpv, na, cd, dagc, d8⟩
    have h8 : d8.logs = devm.logs :=
      (Blanc.accessDelegation_fields hdel).2.2.2.2.1.trans hAccess
    refine ShapeLogs.bindE h8 (LogsWalk.chargeGas _ d8) fun d9 h9 => ?_
    refine ShapeLogs.assert h9 ?_
    split
    · exact ShapeLogs.shortfall h9
    · exact ShapeLogs.call h9
  | callcode =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToAdr d1) fun cadr d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.pop d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bind h3 (LogsWalk.popToNat d3) fun _ d4 h4 => ?_
    refine ShapeLogs.bind h4 (LogsWalk.popToNat d4) fun _ d5 h5 => ?_
    refine ShapeLogs.bind h5 (LogsWalk.popToNat d5) fun _ d6 h6 => ?_
    refine ShapeLogs.bind h6 (LogsWalk.popToNat d6) fun _ d7 h7 => ?_
    dsimp only
    let dAccess : Devm := match sevm.benvStat.rules.access with
      | .eip2929 => addAccessedAddress d7 cadr
      | .flat _ => d7
    have hAccess : dAccess.logs = devm.logs := by
      dsimp only [dAccess]
      split
      · exact h7
      · exact h7
    rcases hdel : sevm.benvStat.rules.accessDelegation dAccess cadr with
      ⟨dpv, na, cd, dagc, d8⟩
    have h8 : d8.logs = devm.logs :=
      (Blanc.accessDelegation_fields hdel).2.2.2.2.1.trans hAccess
    refine ShapeLogs.bindE h8 (LogsWalk.chargeGas _ d8) fun d9 h9 => ?_
    split
    · exact ShapeLogs.shortfall' h9
    · exact ShapeLogs.call h9
  | delegatecall =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToAdr d1) fun cadr d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.popToNat d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bind h3 (LogsWalk.popToNat d3) fun _ d4 h4 => ?_
    refine ShapeLogs.bind h4 (LogsWalk.popToNat d4) fun _ d5 h5 => ?_
    refine ShapeLogs.bind h5 (LogsWalk.popToNat d5) fun _ d6 h6 => ?_
    dsimp only
    let dAccess : Devm := match sevm.benvStat.rules.access with
      | .eip2929 => addAccessedAddress d6 cadr
      | .flat _ => d6
    have hAccess : dAccess.logs = devm.logs := by
      dsimp only [dAccess]
      split
      · exact h6
      · exact h6
    rcases hdel : sevm.benvStat.rules.accessDelegation dAccess cadr with
      ⟨dpv, na, cd, dagc, d7⟩
    have h7 : d7.logs = devm.logs :=
      (Blanc.accessDelegation_fields hdel).2.2.2.2.1.trans hAccess
    refine ShapeLogs.bindE h7 (LogsWalk.chargeGas _ d7) fun d8 h8 => ?_
    exact ShapeLogs.call h8
  | staticcall =>
    simp only [Xinst.step, hsg]
    refine ShapeLogs.bind rfl (LogsWalk.pop devm) fun _ d1 h1 => ?_
    refine ShapeLogs.bind h1 (LogsWalk.popToAdr d1) fun tgt d2 h2 => ?_
    refine ShapeLogs.bind h2 (LogsWalk.popToNat d2) fun _ d3 h3 => ?_
    refine ShapeLogs.bind h3 (LogsWalk.popToNat d3) fun _ d4 h4 => ?_
    refine ShapeLogs.bind h4 (LogsWalk.popToNat d4) fun _ d5 h5 => ?_
    refine ShapeLogs.bind h5 (LogsWalk.popToNat d5) fun _ d6 h6 => ?_
    dsimp only
    let dAccess : Devm := match sevm.benvStat.rules.access with
      | .eip2929 => addAccessedAddress d6 tgt
      | .flat _ => d6
    have hAccess : dAccess.logs = devm.logs := by
      dsimp only [dAccess]
      split
      · exact h6
      · exact h6
    rcases hdel : sevm.benvStat.rules.accessDelegation dAccess tgt with
      ⟨dpv, na, cd, dagc, d7⟩
    have h7 : d7.logs = devm.logs :=
      (Blanc.accessDelegation_fields hdel).2.2.2.2.1.trans hAccess
    refine ShapeLogs.bindE h7 (LogsWalk.chargeGas _ d7) fun d8 h8 => ?_
    exact ShapeLogs.call h8

theorem Xinst.logs_of_okH {sevm : Sevm} {pre post : Devm} {x : Xinst} {xl : Xlot}
    (hsg : sevm.benvStat.rules.stateGas = none) (hx : sevm.isStatic = true ∨ x = .staticcall)
    (run : Xinst.Run sevm pre x xl (.ok post)) (body : Xlot.KeepsLogs xl) :
    post.logs = pre.logs := by
  unfold Xinst.Run at run
  rcases Xinst.step_shapeLogsH sevm pre x hsg with ⟨ex, hs, hex⟩ |
    ⟨hc, d, e, na, mi, ms, hd, hs⟩ |
    ⟨d, g, v, c, t, ca, stv, isSt, ii, isz, oi, osz, code, dp, hd, hs⟩ <;> rw [hs] at run
  · obtain ⟨-, hpost⟩ := run
    subst hpost
    exact hex.symm
  · exfalso
    rcases hx with hst | rfl
    · exact GenericCreate.not_ok_of_static hst run
    · rcases hc with h | h <;> cases h
  · exact (GenericCall.logs_of_ok hsg run body).trans hd

/-- `SELFDESTRUCT` cannot succeed in a static frame without state gas. -/
theorem Linst.selfdestruct_not_ok_of_staticH {sevm : Sevm} {pre post : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none) (hs : sevm.isStatic = true)
    (run : Linst.Run sevm pre .selfdestruct (.ok post)) : False := by
  simp only [Linst.Run, Linst.run, hsg] at run
  rcases Except.bind_eq_ok run with ⟨_, _, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨_, _, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨_, _, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨_, _, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, _, run₅⟩
  rcases Except.bind_eq_ok run₅ with ⟨_, hassert, _⟩
  simp only [assertDynamic, Except.assert, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq] at hassert

/-- One successful same-frame driver step of a static frame without state gas keeps the
log list. -/
private theorem staticStep_cont_logsH
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (static : sevm.isStatic = true) (hsg : sevm.benvStat.rules.stateGas = none) :
    post.logs = pre.logs := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | last last =>
          rw [Evm.step_last decoded] at step
          cases step
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error =>
              rw [jumpEq] at step
              cases step
          | ok pair =>
              rcases pair with ⟨actualPc, actualPost⟩
              rw [jumpEq] at step
              cases step
              exact Jinst.logs_of_ok jumpEq
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction = .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have pcEq : pc' = pc + instruction.size := Ninst.step_cont_pc nstep
          subst pc'
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          cases instruction with
          | push bytes bound =>
              exact (Ninst.Hinv.inv (f := Devm.logs)
                (show Ninst.Run sevm pre (.push bytes bound) post from
                  ⟨.none, trivial, pc, nrun⟩)).symm
          | exec executable =>
              exact Xinst.logs_of_okH hsg (Or.inl static) (XStep.run_toStep.mp nrun) trivial
          | dupn imm => exact Ninst.dupn_logs ⟨.none, trivial, pc, nrun⟩
          | swapn imm => exact Ninst.swapn_logs ⟨.none, trivial, pc, nrun⟩
          | exchange imm => exact Ninst.exchange_logs ⟨.none, trivial, pc, nrun⟩
          | reg regular =>
              have rrun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
                (Step.run_ofExecution.mp nrun).2.symm
              by_cases hlog : ∃ n, regular = .log n
              · rcases hlog with ⟨n, rfl⟩
                exact (Rinst.log_not_ok_of_static static rrun).elim
              · exact Rinst.logs_of_ok (fun n h => hlog ⟨n, h⟩) rrun

/-- A successfully halted node of a static frame without state gas keeps the log list. -/
private theorem staticHalt_logsH
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out)
    (static : sevm.isStatic = true) (hsg : sevm.benvStat.rules.stateGas = none) :
    ∀ post, out = .ok post → post.logs = pre.logs := by
  intro post hout
  subst hout
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | next next =>
          rw [Evm.step_next decoded] at step
          exact (Ninst.step_ne_halt_ok step).elim
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst <;>
            rw [jumpEq] at step <;> cases step
      | last last =>
          rw [Evm.step_last decoded] at step
          have run : Linst.Run sevm pre last (.ok post) := Step.halt.inj step
          change post.logs = pre.logs
          cases last with
          | stop => exact (Linst.Hinv.inv run).symm
          | return_ => exact (Linst.Hinv.inv run).symm
          | revert => exact (Linst.revert_not_ok run).elim
          | selfdestruct =>
              exact (Linst.selfdestruct_not_ok_of_staticH hsg static run).elim

/-- Any fact about every successful outcome holds for the committed post. -/
theorem Execution.committedPost_of_okFact {P : Devm → Prop} {out : Execution}
    (h : ∀ post, out = .ok post → P post) (committed : Execution.commits out = true) :
    P (Execution.committedPost out committed) := by
  cases out with
  | error _ => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post => exact h post rfl

/-- **Static execution keeps the log list.**  A successful execution (`.ok post`, committing
or not) of a static frame without state gas ends with exactly its entry log list: `LOG`
cannot complete in a static frame, every other step keeps the list, and every child is
static and merges its (empty) log list only on success. -/
theorem Exec.logs_eq_of_static_okH
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    ∀ post, out = .ok post → post.logs = pre.logs := by
  induction run with
  | halt step => exact staticHalt_logsH step static hsg
  | cont step _ ih =>
      intro post hout
      exact (ih static hsg post hout).trans (staticStep_cont_logsH step static hsg)
  | doneErr _ _ _ => intro post hout; cases hout
  | @doneOk _ nodeSevm nodePre _ _ _ _ nodePost _ step enter resumeRun _ ih =>
      intro post hout
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have xrun : Xinst.Run nodeSevm nodePre x .none (.ok nodePost) := by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_done enter, resumeRun.symm⟩
      exact (ih static hsg post hout).trans
        (Xinst.logs_of_okH hsg (Or.inl static) xrun trivial)
  | runErr _ _ _ _ _ => intro post hout; cases hout
  | runOk step enter _ resumeRun _ childIH nextIH =>
      intro post hout
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have xrun := (show Xinst.Run _ _ x (.some ⟨_, _⟩) (.ok _) by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_run enter, resumeRun.symm⟩)
      have childStatic := Evm.step_run_isStatic step enter static
      have childFork : _ = none :=
        (congrArg (fun b => b.rules.stateGas) (Evm.step_spawn_child_benvStat step enter)).trans hsg
      exact (nextIH static hsg post hout).trans
        (Xinst.logs_of_okH hsg (Or.inl static) xrun
          (fun childCommitted => Execution.committedPost_of_okFact (P := fun d => d.logs = _)
            (childIH childStatic childFork) childCommitted))

/-- **Static execution keeps the log list**, committed form: a committing execution of a
static frame without state gas ends with exactly its entry log list
(`Exec.logs_eq_of_static_okH`). -/
theorem Exec.logs_committedPost_eq_of_staticH
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    (Execution.committedPost out committed).logs = pre.logs :=
  Execution.committedPost_of_okFact (P := fun d => d.logs = pre.logs)
    (Exec.logs_eq_of_static_okH run static hsg) committed

theorem Ninst.world_of_quietH {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hsg : sevm.benvStat.rules.stateGas = none) (hn : n.quiet = true)
    (run : Ninst.Run sevm pre n post) :
    Devm.getStor post = Devm.getStor pre ∧ post.logs = pre.logs := by
  cases n with
  | push bytes bound =>
      exact ⟨(Ninst.Hinv.inv (f := Devm.getStor) run).symm,
             (Ninst.Hinv.inv (f := Devm.logs) run).symm⟩
  | dupn imm =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_dupn, Step.run_ofExecution] at hrun
        exact hrun.1
      subst hxl
      have frame := Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial hrun
      exact ⟨(funext (Devm.InstructionFrame.getStor frame)).symm,
             Ninst.dupn_logs ⟨.none, trivial, pc, hrun⟩⟩
  | swapn imm =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_swapn, Step.run_ofExecution] at hrun
        exact hrun.1
      subst hxl
      have frame := Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial hrun
      exact ⟨(funext (Devm.InstructionFrame.getStor frame)).symm,
             Ninst.swapn_logs ⟨.none, trivial, pc, hrun⟩⟩
  | exchange imm =>
      rcases run with ⟨xl, -, pc, hrun⟩
      have hxl : xl = .none := by
        simp only [Ninst.StepRun, Ninst.step_exchange, Step.run_ofExecution] at hrun
        exact hrun.1
      subst hxl
      have frame := Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial hrun
      exact ⟨(funext (Devm.InstructionFrame.getStor frame)).symm,
             Ninst.exchange_logs ⟨.none, trivial, pc, hrun⟩⟩
  | exec x =>
      have hx : x = .staticcall := by simpa only [Ninst.quiet, beq_iff_eq] using hn
      subst hx
      refine ⟨(Ninst.staticcall_inv_getStor_exact_noStateGas hsg run).symm, ?_⟩
      rcases run with ⟨slot, filled, pc, stepRun⟩
      have xrun : Xinst.Run sevm pre .staticcall slot (.ok post) := by
        simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run] using stepRun
      have body : Xlot.KeepsLogs slot := by
        cases slot with
        | none => trivial
        | some child =>
            rcases child with ⟨cevm, out⟩
            rcases filled with ⟨childRun⟩
            rcases XStep.Run.some_inv xrun with ⟨frame, resume, spawn, enter, -⟩
            have childStatic : cevm.sta.isStatic = true :=
              (Frame.enter_run_isStatic enter).trans
                (Xinst.step_staticcall_spawn_isStatic spawn)
            exact fun committed => Exec.logs_committedPost_eq_of_staticH childRun childStatic
              committed ((congrArg (fun b => b.rules.stateGas)
                (Xinst.Run.some_child_benvStat xrun)).trans hsg)
      exact Xinst.logs_of_okH hsg (Or.inr rfl) xrun body
  | reg r =>
      have hs : r ≠ .sstore := by
        rintro rfl
        simp only [Ninst.quiet, Bool.false_eq_true] at hn
      have hr : ∀ n, r ≠ .log n := by
        rintro n rfl
        simp only [Ninst.quiet, Bool.false_eq_true] at hn
      rcases of_run_reg run with ⟨pc, rrun⟩
      exact ⟨(Rinst.preserves_stor hs rrun).symm, Rinst.logs_of_ok hr rrun⟩


/-! ## `STATICCALL` to an arbitrary callee under the actual rules -/

/-- `StaticAnswered` under the actual delegation flag (`CallCodeH`). -/
def StaticAnsweredH (sevm : Sevm) (b : Devm) (t : Adr) (input out : Bytes) : Prop :=
  ∃ (parent child : Devm) (xl : Xlot) (dp : Bool) (na : Adr) (code : ByteArray) (gas : Nat),
    parent.state = b.state ∧
    CallCodeH sevm.benvStat.rules.delegationEnabled b t na code dp ∧
    Xlot.Filled xl ∧
    ProcessMessage (callMsg sevm parent gas 0 sevm.currentTarget t na true true input code dp)
      xl (.ok child) ∧
    child.error.isSome = false ∧ child.output = out

/-- On a covered fork, `StaticAnsweredH` is the modern `StaticAnswered`. -/
theorem StaticAnsweredH.of_covered {sevm : Sevm} {b : Devm} {t : Adr} {input out : Bytes}
    (hfork : CoveredFork sevm.benvStat.fork) (h : StaticAnsweredH sevm b t input out) :
    StaticAnswered sevm b t input out := by
  have hdeleg : sevm.benvStat.rules.delegationEnabled = true :=
    hfork.cases (motive := fun f => f.ruleSet.delegationEnabled = true) rfl rfl rfl rfl
  obtain ⟨parent, child, xl, dp, na, code, gas, h1, h2, h3⟩ := h
  rw [hdeleg, CallCodeH_enabled] at h2
  exact ⟨parent, child, xl, dp, na, code, gas, h1, h2, h3⟩

/-- `ReturnDataBound.staticcall_returnData_length_lt` under `rules.stateGas = none`. -/
theorem ReturnDataBound.staticcall_returnData_length_ltH {sevm : Sevm} {pre post : Devm}
    (hrun : Ninst.Run sevm pre Ninst.staticcall post)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    post.returnData.length < 2 ^ 256 := by
  obtain ⟨xl, hf, pc, hr⟩ := hrun
  exact ReturnDataBound.call_step_returnData_length_lt (Or.inr rfl) hsg hf hr

/-- `ReturnDataBound.call_returnData_length_lt` under `rules.stateGas = none`. -/
theorem ReturnDataBound.call_returnData_length_ltH {sevm : Sevm} {pre post : Devm}
    (hrun : Ninst.Run sevm pre Ninst.call post)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    post.returnData.length < 2 ^ 256 := by
  obtain ⟨xl, hf, pc, hr⟩ := hrun
  exact ReturnDataBound.call_step_returnData_length_lt (Or.inl rfl) hsg hf hr

section StaticCallH

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- **`STATICCALL` to an arbitrary callee, inverted.**  A successful step leaves a flag and a
returned byte string `out` (`StaticCallPost`); a set flag comes from a successful static child
message to `t` with the input window as calldata. -/
theorem ri_staticcallH {g t ii is oi os : B256} {d : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (h : Ninst.Run sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall) d) :
    ∃ flag out, StaticCallPost b d S M ii is oi os flag out ∧
      (flag = 1 → StaticAnsweredH sevm b t.toAdr (M.read ii.toNat is.toNat).1 out) := by
  obtain ⟨flag, hstack⟩ := (CallEffects.call6_run_effects (Or.inr rfl) hsg rfl h).1
  have hw := Ninst.world_of_quietH hsg rfl h
  have hp : (g :: t :: ii :: is :: oi :: os :: S) <<+
      (St b (g :: t :: ii :: is :: oi :: os :: S) M G).stack := by
    simpa only [List.append_nil, St.stack] using
      (pref_append (g :: t :: ii :: is :: oi :: os :: S) [])
  rcases of_run_staticcall_val_with_depth_causeH hp h hsg with hfail | hsucc
  · obtain ⟨hpf, -, out, hret, hmem, -⟩ := hfail
    rw [hstack] at hpf
    have h0 : flag = 0 := (pref_head_unique hpf (pref_append [flag] S)).symm
    refine ⟨flag, out, ⟨hstack, hmem, hret, fun a => congrFun hw.1 a, hw.2,
      fun h1 => False.elim (by rw [h0] at h1; exact (by decide : (0 : B256) ≠ 1) h1), .inl h0⟩, ?_⟩
    intro h1
    rw [h0] at h1
    exact absurd h1 (by decide)
  · obtain ⟨parent, child, xl, dp, na, code, avail, -, hs, hstate, hpm, -, houtput, hdel, hfill, hproc,
      hclean, hresume, -, hret, hmem, hpst⟩ := hsucc
    have hS : parent.stack = S := by
      have := hs
      simp only [St.stack, List.cons.injEq] at this
      exact this.2.2.2.2.2.2.symm
    rw [hpst, hS] at hstack
    have h1 : flag = 1 := (List.cons.inj hstack).1.symm
    refine ⟨flag, child.output, ⟨by rw [← h1] at hstack; rw [hpst, hS, h1],
      by rw [hmem, hpm]; rfl,
      hret, fun a => congrFun hw.1 a, hw.2,
      fun _ => (Resume.call_output hresume).trans houtput, .inr h1⟩, fun _ => ?_⟩
    exact ⟨parent, child, xl, dp, na, code, _, hstate, hdel, hfill, hproc, hclean, rfl⟩

/-- The actual static-call producer bounds the full return data in the same outcome. -/
theorem ri_staticcall_boundedH {g t ii is oi os : B256} {d : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (h : Ninst.Run sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall) d) :
    ∃ flag out, StaticCallPost b d S M ii is oi os flag out ∧
      out.length < 2^256 ∧
      (flag = 1 → StaticAnsweredH sevm b t.toAdr (M.read ii.toNat is.toNat).1 out) := by
  obtain ⟨flag, out, hpost, hans⟩ := ri_staticcallH hsg h
  have bound := ReturnDataBound.staticcall_returnData_length_ltH h hsg
  rw [hpost.returnData] at bound
  exact ⟨flag, out, hpost, bound, hans⟩

/-- **`STATICCALL` to an arbitrary callee, forward.**  Given the step itself (a premise about the
callee), the run continues from its outcome as `ri_staticcall` describes it. -/
theorem rx_staticcallH {fs : List SFunc} {f : SFunc} {o : Outcome} {g t ii is oi os : B256}
    {d : Devm} (hsg : sevm.benvStat.rules.stateGas = none)
    (hcall : Ninst.RunCompiled sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G)
      (.exec .staticcall) d)
    (k : ∀ flag out, StaticCallPost b d S M ii is oi os flag out →
      (flag = 1 → StaticAnsweredH sevm b t.toAdr (M.read ii.toNat is.toNat).1 out) →
      SFunc.RunExact fs sevm (St d (flag :: S)
        ((M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat
          (out.take os.toNat)) d.gasLeft) f o) :
    SFunc.RunExact fs sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .staticcall) f) o := by
  obtain ⟨xl, hf, hr⟩ := hcall
  obtain ⟨flag, out, hpost, hans⟩ := ri_staticcallH hsg ⟨xl, hf, 0, hr 0⟩
  refine .next ⟨xl, hf, hr⟩ ?_
  rw [hpost.eq_St]
  exact k flag out hpost hans

/-- `ri_staticcall_boundedH` recovers the modern `ri_staticcall_bounded` on a covered fork. -/
theorem ri_staticcall_boundedH_covered {g t ii is oi os : B256} {d : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall) d) :
    ∃ flag out, StaticCallPost b d S M ii is oi os flag out ∧
      out.length < 2^256 ∧
      (flag = 1 → StaticAnswered sevm b t.toAdr (M.read ii.toNat is.toNat).1 out) := by
  obtain ⟨flag, out, post, bound, ans⟩ := ri_staticcall_boundedH hfork.rules_stateGas_none h
  exact ⟨flag, out, post, bound, fun h1 => (ans h1).of_covered hfork⟩

end StaticCallH

end Blanc.Lift
