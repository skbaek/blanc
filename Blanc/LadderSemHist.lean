import Blanc.LadderSem

/-!
# Historical `post_of_call_self`: the CALL postcondition without coverage

`ContractSpecSem.post_of_call_self_withIn` is the historical form of
`ContractSpecSem.post_of_call_self_with` (`Blanc/LadderSem.lean`): the
deeper-frame hypothesis is quantified over a selected fork-domain fact `F`
instead of `CoveredFork`, and the only rule fact is
`stateGas = none`.  Where the modern proof derives
`access = .eip2929` and `delegationEnabled = true` from
`CoveredFork.cases`, this proof cases on the actual
`sevm.benvStat.rules.access` (`.flat` / `.eip2929`) and on the actual
`delegationEnabled` flag, so every premise discharges on `HistFork`
(`Blanc/HistoricalFork.lean`) with `stateGas = none`.

Consumer: the WETH9 `withdraw` self-CALL
(`Blanc/Lift/Weth9/Withdraw.lean`), via `Weth9.withdraw_post_gen`.
-/

namespace Blanc

open Jaune

namespace ContractSpecSem

variable {c : ContractSpecSem}

/-- Local copy of LadderSem's private `post_of_state_eq_debited` (which this
module cannot see, and may not expose by editing LadderSem): the invariant
at the debited balance survives when the state is unchanged.  The state
equation comes last here, matching the historical leaves' `apply` shape. -/
private lemma post_of_state_eq_debited {ca : Adr} {sevm : Sevm} {s sf : Devm}
    {value : B256}
    (hside : c.Side s.getBal)
    (hle : value ≤ s.getBal ca)
    (hinv : c.Inv (Devm.getStor s ca) 0 (s.getBal ca - value))
    (hstate : sf.state = s.state) :
    c.Post ca sevm sf := by
  have hbal : sf.getBal = s.getBal := funext (getBal_eq_of_state_eq hstate)
  refine ⟨hbal ▸ hside, ?_⟩
  show c.Inv (Devm.getStor sf ca) 0 (sf.getBal ca)
  rw [getStor_eq_of_state_eq hstate ca, getBal_eq_of_state_eq hstate ca]
  apply c.inv_mono hinv
  rw [B256.toNat_sub_eq_of_le _ _ hle]
  omega

/-- `post_of_call_self` for a `CALL` step on a historical fork: the child
derivation satisfies `Q`, and the deeper-frame hypothesis needs only the
selected fork-domain fact `F` at children.  The access schedule and the
delegation flag are cased on, never assumed. -/
theorem post_of_call_self_withIn {F : Fork → Prop}
    {Q : ∀ pc sevm devm exn, Exec pc sevm devm exn → Prop}
    {ca : Adr} {sevm : Sevm} {s sf : Devm}
    {gas dst value : B256} {xs : Stack}
    (hsg : sevm.benvStat.rules.stateGas = none) (hF : F sevm.benvStat.fork)
    (hca : sevm.currentTarget = ca)
    (ih : ∀ pc' sevm' pre' post' (child : Exec pc' sevm' pre' (.ok post')),
        Q _ _ _ _ child →
        sevm'.depth < sevm.depth →
        CodeSem.At c.sem ca pc' sevm' pre' →
        F sevm'.benvStat.fork →
        c.PreWf ca sevm' pre' →
        c.Post ca sevm' post')
    (hp : gas :: dst :: value :: xs <<+ s.stack)
    (hcode : some (s.getCode ca).toList = c.sem.image)
    (hside : c.Side s.getBal)
    (hle : value ≤ s.getBal ca)
    (hinv : c.Inv (Devm.getStor s ca) 0 (s.getBal ca - value))
    (run : Ninst.RunWith Q sevm s (.exec .call) sf) :
    c.Post ca sevm sf := by
  subst hca
  rcases run with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    Bind.bind, Except.bind, Except.assert] at h_run
  rw [hsg] at h_run
  -- pop gas
  rcases eq1 : Devm.pop s with _ | ⟨gas', devm1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e1 := (Devm.pop_of_pop eq1).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at hp
  have h_gas : gas = gas' := pref_head_unique hp (pref_append [gas'] devm1.stack)
  subst h_gas
  have hs₂ : dst :: value :: xs <<+ devm1.stack := cons_pref_cons_inv hp
  -- pop callee
  rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;> simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToAdr eq2 with ⟨x, -, h_pop2⟩
  have e2 := (Devm.pop_of_pop h_pop2).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at hs₂
  have h_x : dst = x := pref_head_unique hs₂ (pref_append [x] devm2.stack)
  subst h_x
  have hs₃ : value :: xs <<+ devm2.stack := cons_pref_cons_inv hs₂
  -- pop value
  rcases eq3 : Devm.pop devm2 with _ | ⟨value', devm3⟩ <;> simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e3 := (Devm.pop_of_pop eq3).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rw [e3] at hs₃
  have h_val : value = value' := pref_head_unique hs₃ (pref_append [value'] devm3.stack)
  subst h_val
  -- pop the four indices/sizes
  rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputIndex, devm4⟩ <;> simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩ <;> simp only [eq5] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases eq6 : Devm.popToNat devm5 with _ | ⟨outputIndex, devm6⟩ <;> simp only [eq6] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases eq7 : Devm.popToNat devm6 with _ | ⟨outputSize, devm7⟩ <;> simp only [eq7] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat eq4 with ⟨_, h_pop4⟩
  rcases Devm.pop_of_popToNat eq5 with ⟨_, h_pop5⟩
  rcases Devm.pop_of_popToNat eq6 with ⟨_, h_pop6⟩
  rcases Devm.pop_of_popToNat eq7 with ⟨_, h_pop7⟩
  have h_st7 : s.state = devm7.state :=
    ((Devm.pop_of_pop eq1).state).trans
      (((Devm.pop_of_pop h_pop2).state).trans
        (((Devm.pop_of_pop eq3).state).trans
          ((h_pop4.state).trans
            ((h_pop5.state).trans ((h_pop6.state).trans h_pop7.state)))))
  clear e1 e2 e3 hp hs₂ hs₃ eq1 eq2 eq3 eq4 eq5 eq6 eq7
  clear h_pop2 h_pop4 h_pop5 h_pop6 h_pop7
  -- Historical case split: the modern proof reads both facts off
  -- `CoveredFork.cases`.  Here the access schedule and the delegation flag
  -- are cased on as they stand.
  cases ha : sevm.benvStat.rules.access with
  | eip2929 =>
    cases hd : sevm.benvStat.rules.delegationEnabled with
    | true =>
      simp only [ha, ForkRules.accessDelegation, hd, ↓reduceIte] at h_run
      -- delegation resolution
      rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
          (addAccessedAddress devm7 callee) callee with
        ⟨dp, na, code0, dagc, devm9⟩
      simp only [hp11] at h_run
      have h_code0 :
          code0 = (sevm.benvStat.rules.gas.accessDelegation
            (addAccessedAddress devm7 callee) callee).2.2.1 := by
        rw [hp11]
      have h_st9 : devm9.state = (addAccessedAddress devm7 callee).state := by
        have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
        dsimp only at h
        rw [← h, GasSchedule.accessDelegation_state]
      have h_st8 : (addAccessedAddress devm7 callee).state = s.state := by
        show devm7.state = s.state
        exact h_st7.symm
      -- charge the call gas
      split at h_run
      · cases XStep.run_ofExcept_error h_run
      rename_i devm10 eq16
      have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
      have h_st11 :
          (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
            = s.state := by
        show devm10.state = s.state
        rw [← h_st10, h_st9, h_st8]
      clear h_st10 h_st9 h_st7 eq16
      -- static-context assertion
      split at h_run
      case h_1 => cases XStep.run_ofExcept_error h_run
      case h_2 =>
      split at h_run
      · -- insufficient balance : call fails, state unchanged
        split at h_run
        case h_1 => cases XStep.run_ofExcept_error h_run
        case h_2 =>
        rename_i devm12 eq20
        apply post_of_state_eq_debited hside hle hinv _
        have h_ex := Except.ok.inj h_run.2
        rw [h_ex]
        show devm12.state = s.state
        rw [← (Devm.push_of_push eq20).state]
        exact h_st11
      · -- balance is sufficient : the call goes through
        simp only [genericCall.step] at h_run
        split at h_run
        · -- depth limit reached : call fails, state unchanged
          simp only [Bind.bind, Except.bind] at h_run
          split at h_run
          case h_1 => cases XStep.run_ofExcept_error h_run
          case h_2 =>
          rename_i devm12 h_push
          apply post_of_state_eq_debited hside hle hinv _
          have h_ex := Except.ok.inj h_run.2
          rw [h_ex]
          show devm12.state = s.state
          rw [← (Devm.push_of_push h_push).state]
          exact h_st11
        · -- the call is executed
          simp only [XStep.Run] at h_run
          rcases h_run with ⟨ex', run_pm₀, h_split⟩
          obtain ⟨childMsg, run_pm, hc_stv, hc_state, hc_stat, hc_caller, hc_value, hc_ct,
              hc_ca, hc_code, hc_depth⟩ :
              ∃ m : Msg, ProcessMessage m xl ex' ∧
                m.shouldTransferValue = true ∧ m.benv.state = s.state ∧
                m.benv.stat = sevm.benvStat ∧
                m.caller = sevm.currentTarget ∧ m.value = value ∧
                m.currentTarget = callee ∧ m.codeAddress = some na ∧
                m.code = code0 ∧ m.depth = sevm.depth - 1 :=
            ⟨_, run_pm₀, rfl, h_st11, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          clear run_pm₀
          rcases ex' with err' | child
          · cases Resume.call_run_error h_split.symm
          have h_sf_state : sf.state = child.state := Resume.call_state h_split.symm
          obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run_pm
          unfold FrameBody at hbody
          rcases eq_bt : childMsg.benvAfterTransfer with e | benv' <;>
            rw [eq_bt] at hbody
          · rw [hbody.2, processMessage.settle_error] at hset
            cases hset
          have run_ec : ExecuteCode (childMsg.withBenv benv') xl r0 := hbody
          -- the child's initial state satisfies the precondition: after the value
          -- transfer, or unchanged when no value moves (zero-value entry)
          have hchildPre : c.Pre sevm.currentTarget (initSevm (childMsg.withBenv benv'))
              (initDevm (childMsg.withBenv benv')) := by
            by_cases h_nz : value ≠ 0
            · rcases of_benvAfterTransfer hc_stv (by rw [hc_value]; exact h_nz) eq_bt with
                ⟨st_mid, h_sub, hB⟩
              rw [hc_state, hc_caller, hc_value] at h_sub
              have hBs : benv'.state = st_mid.addBal callee value := by
                rw [hB, hc_ct, hc_value]; rfl
              apply Pre.child_of_outbound_transfer (st := s.state) (st_mid := st_mid)
                (target := callee) (value := value)
              · exact hcode
              · exact hside
              · exact hinv
              · exact h_sub
              · exact hBs
              · exact hc_ct
              · exact hc_value
            · have hv0 : value = 0 := not_not.mp h_nz
              have hbenv : benv' = childMsg.benv :=
                benvAfterTransfer_eq_of_not_transfer
                  (fun h => h_nz (by rw [← hc_value]; exact h.2)) eq_bt
              have hstate : (initDevm (childMsg.withBenv benv')).state = s.state := by
                show benv'.state = _
                rw [hbenv, hc_state]
              refine Pre.of_inv_eqs ?_ (fun _ => by show childMsg.value = 0; rw [hc_value, hv0])
              rw [hstate]
              refine ⟨hcode, hside, ?_⟩
              have hinv0 := hinv
              rw [hv0, B256.sub_zero] at hinv0
              exact hinv0
          -- resolve the settlement : rollback or a clean sub-message result
          obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
          subst h_r0
          rcases h_settle with ⟨h_err2, h_if⟩ | ⟨h_err2, h_if⟩
          · -- sub-message failed : state rolled back to the pre-transfer state
            apply post_of_state_eq_debited hside hle hinv _
            rw [h_sf_state, ← h_if]
            exact hc_state
          have h_if' := h_if.symm
          subst h_if'
          simp only [Devm.recordTouch_state] at h_sf_state
          have h_wb_ca : (childMsg.withBenv benv').codeAddress = some na := hc_ca
          have hchildPost : c.Post sevm.currentTarget
              (initSevm (childMsg.withBenv benv')) evm2 := by
            rcases of_executeCode_someCode h_wb_ca run_ec with
              ⟨_, _, h_he⟩ | ⟨_, ex''', h_xl_some, h_he⟩
            · -- precompile : only the transfer
              have h_child_state :
                  evm2.state = (initDevm (childMsg.withBenv benv')).state := by
                exact state_of_executePrecomp_ok h_he h_err2
              exact post_of_pre (hchildPre.state_eq h_child_state)
            · -- regular callee : a sub-execution takes place
              rw [h_xl_some] at h_fill
              dsimp only [Xlot.FilledWith] at h_fill
              have hstat : (childMsg.withBenv benv').benv.stat = sevm.benvStat := by
                show benv'.stat = sevm.benvStat
                rw [benvAfterTransfer_stat eq_bt, hc_stat]
              have hexn : ex''' = .ok evm2 := exec_ok_of_handleError h_he h_err2
              subst hexn
              obtain ⟨ex_sub, hq⟩ := h_fill
              have h_ss_ct : (initSevm (childMsg.withBenv benv')).currentTarget = callee :=
                hc_ct
              have hat : CodeSem.At c.sem sevm.currentTarget 0
                  (initSevm (childMsg.withBenv benv'))
                  (initDevm (childMsg.withBenv benv')) := by
                refine ⟨hchildPre.code, ?_⟩
                intro h_eq_ct
                rw [h_ss_ct] at h_eq_ct
                refine ⟨?_, rfl⟩
                show some (initSevm (childMsg.withBenv benv')).code.toList = c.sem.image
                have h_code_c : (initSevm (childMsg.withBenv benv')).code = code0 := hc_code
                rw [h_code_c, h_code0]
                have h_ad : (addAccessedAddress devm7 callee).state.getCode callee
                    = s.getCode sevm.currentTarget := by
                  have h8 := h_st8
                  rw [h8, h_eq_ct]; rfl
                have h_notdel : ¬ isValidDelegation
                    ((addAccessedAddress devm7 callee).state.getCode callee) := by
                  rw [h_ad]; exact c.sem.not_delegation hcode
                have h_none : getDelegatedCodeAddress
                    ((addAccessedAddress devm7 callee).state.getCode callee) = none := by
                  dsimp only [getDelegatedCodeAddress]
                  exact ite_eq_right_of_eq_false _ _ (eq_false h_notdel)
                have h_gas_code :
                    (sevm.benvStat.rules.gas.accessDelegation
                      (addAccessedAddress devm7 callee) callee).2.2.1 =
                      (addAccessedAddress devm7 callee).state.getCode callee := by
                  unfold GasSchedule.accessDelegation
                  dsimp only
                  rw [h_none]
                rw [h_gas_code, h_ad]
                exact hcode
              have h_depth_lt : (initSevm (childMsg.withBenv benv')).depth < sevm.depth := by
                have h_dep : (initSevm (childMsg.withBenv benv')).depth = sevm.depth - 1 :=
                  hc_depth
                rw [h_dep]
                omega
              have hchildFork : F (initSevm (childMsg.withBenv benv')).benvStat.fork := by
                change F (childMsg.withBenv benv').benv.stat.fork
                rw [hstat]
                exact hF
              exact ih 0 (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv'))
                evm2 ex_sub hq h_depth_lt hat hchildFork ⟨hchildPre, fun _ => Mem.wf_empty⟩
          exact Post.of_state_eq hchildPost h_sf_state
    | false =>
      simp only [ha] at h_run
      -- delegation resolution: disabled, so the machine is unchanged
      rcases hp11 : sevm.benvStat.rules.accessDelegation
          (addAccessedAddress devm7 callee) callee with
        ⟨dp, na, code0, dagc, devm9⟩
      simp only [hp11] at h_run
      have hdis : sevm.benvStat.rules.accessDelegation
          (addAccessedAddress devm7 callee) callee =
          ⟨false, callee, (addAccessedAddress devm7 callee).state.getCode callee,
            0, addAccessedAddress devm7 callee⟩ :=
        ForkRules.accessDelegation_disabled hd _ _
      have h_eq : (⟨dp, na, code0, dagc, devm9⟩ :
          Bool × Adr × ByteArray × Nat × Devm) =
          ⟨false, callee, (addAccessedAddress devm7 callee).state.getCode callee,
            0, addAccessedAddress devm7 callee⟩ :=
        hp11.symm.trans hdis
      have h_code0 : code0 =
          (addAccessedAddress devm7 callee).state.getCode callee :=
        congrArg (·.2.2.1) h_eq
      have h_st9 : devm9.state = (addAccessedAddress devm7 callee).state :=
        congrArg (fun q => (q.2.2.2.2 : Devm).state) h_eq
      have h_st8 : (addAccessedAddress devm7 callee).state = s.state := by
        show devm7.state = s.state
        exact h_st7.symm
      -- charge the call gas
      split at h_run
      · cases XStep.run_ofExcept_error h_run
      rename_i devm10 eq16
      have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
      have h_st11 :
          (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
            = s.state := by
        show devm10.state = s.state
        rw [← h_st10, h_st9, h_st8]
      clear h_st10 h_st9 h_st7 eq16
      -- static-context assertion
      split at h_run
      case h_1 => cases XStep.run_ofExcept_error h_run
      case h_2 =>
      split at h_run
      · -- insufficient balance : call fails, state unchanged
        split at h_run
        case h_1 => cases XStep.run_ofExcept_error h_run
        case h_2 =>
        rename_i devm12 eq20
        apply post_of_state_eq_debited hside hle hinv _
        have h_ex := Except.ok.inj h_run.2
        rw [h_ex]
        show devm12.state = s.state
        rw [← (Devm.push_of_push eq20).state]
        exact h_st11
      · -- balance is sufficient : the call goes through
        simp only [genericCall.step] at h_run
        split at h_run
        · -- depth limit reached : call fails, state unchanged
          simp only [Bind.bind, Except.bind] at h_run
          split at h_run
          case h_1 => cases XStep.run_ofExcept_error h_run
          case h_2 =>
          rename_i devm12 h_push
          apply post_of_state_eq_debited hside hle hinv _
          have h_ex := Except.ok.inj h_run.2
          rw [h_ex]
          show devm12.state = s.state
          rw [← (Devm.push_of_push h_push).state]
          exact h_st11
        · -- the call is executed
          simp only [XStep.Run] at h_run
          rcases h_run with ⟨ex', run_pm₀, h_split⟩
          obtain ⟨childMsg, run_pm, hc_stv, hc_state, hc_stat, hc_caller, hc_value, hc_ct,
              hc_ca, hc_code, hc_depth⟩ :
              ∃ m : Msg, ProcessMessage m xl ex' ∧
                m.shouldTransferValue = true ∧ m.benv.state = s.state ∧
                m.benv.stat = sevm.benvStat ∧
                m.caller = sevm.currentTarget ∧ m.value = value ∧
                m.currentTarget = callee ∧ m.codeAddress = some na ∧
                m.code = code0 ∧ m.depth = sevm.depth - 1 :=
            ⟨_, run_pm₀, rfl, h_st11, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          clear run_pm₀
          rcases ex' with err' | child
          · cases Resume.call_run_error h_split.symm
          have h_sf_state : sf.state = child.state := Resume.call_state h_split.symm
          obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run_pm
          unfold FrameBody at hbody
          rcases eq_bt : childMsg.benvAfterTransfer with e | benv' <;>
            rw [eq_bt] at hbody
          · rw [hbody.2, processMessage.settle_error] at hset
            cases hset
          have run_ec : ExecuteCode (childMsg.withBenv benv') xl r0 := hbody
          -- the child's initial state satisfies the precondition: after the value
          -- transfer, or unchanged when no value moves (zero-value entry)
          have hchildPre : c.Pre sevm.currentTarget (initSevm (childMsg.withBenv benv'))
              (initDevm (childMsg.withBenv benv')) := by
            by_cases h_nz : value ≠ 0
            · rcases of_benvAfterTransfer hc_stv (by rw [hc_value]; exact h_nz) eq_bt with
                ⟨st_mid, h_sub, hB⟩
              rw [hc_state, hc_caller, hc_value] at h_sub
              have hBs : benv'.state = st_mid.addBal callee value := by
                rw [hB, hc_ct, hc_value]; rfl
              apply Pre.child_of_outbound_transfer (st := s.state) (st_mid := st_mid)
                (target := callee) (value := value)
              · exact hcode
              · exact hside
              · exact hinv
              · exact h_sub
              · exact hBs
              · exact hc_ct
              · exact hc_value
            · have hv0 : value = 0 := not_not.mp h_nz
              have hbenv : benv' = childMsg.benv :=
                benvAfterTransfer_eq_of_not_transfer
                  (fun h => h_nz (by rw [← hc_value]; exact h.2)) eq_bt
              have hstate : (initDevm (childMsg.withBenv benv')).state = s.state := by
                show benv'.state = _
                rw [hbenv, hc_state]
              refine Pre.of_inv_eqs ?_ (fun _ => by show childMsg.value = 0; rw [hc_value, hv0])
              rw [hstate]
              refine ⟨hcode, hside, ?_⟩
              have hinv0 := hinv
              rw [hv0, B256.sub_zero] at hinv0
              exact hinv0
          -- resolve the settlement : rollback or a clean sub-message result
          obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
          subst h_r0
          rcases h_settle with ⟨h_err2, h_if⟩ | ⟨h_err2, h_if⟩
          · -- sub-message failed : state rolled back to the pre-transfer state
            apply post_of_state_eq_debited hside hle hinv _
            rw [h_sf_state, ← h_if]
            exact hc_state
          have h_if' := h_if.symm
          subst h_if'
          simp only [Devm.recordTouch_state] at h_sf_state
          have h_wb_ca : (childMsg.withBenv benv').codeAddress = some na := hc_ca
          have hchildPost : c.Post sevm.currentTarget
              (initSevm (childMsg.withBenv benv')) evm2 := by
            rcases of_executeCode_someCode h_wb_ca run_ec with
              ⟨_, _, h_he⟩ | ⟨_, ex''', h_xl_some, h_he⟩
            · -- precompile : only the transfer
              have h_child_state :
                  evm2.state = (initDevm (childMsg.withBenv benv')).state := by
                exact state_of_executePrecomp_ok h_he h_err2
              exact post_of_pre (hchildPre.state_eq h_child_state)
            · -- regular callee : a sub-execution takes place
              rw [h_xl_some] at h_fill
              dsimp only [Xlot.FilledWith] at h_fill
              have hstat : (childMsg.withBenv benv').benv.stat = sevm.benvStat := by
                show benv'.stat = sevm.benvStat
                rw [benvAfterTransfer_stat eq_bt, hc_stat]
              have hexn : ex''' = .ok evm2 := exec_ok_of_handleError h_he h_err2
              subst hexn
              obtain ⟨ex_sub, hq⟩ := h_fill
              have h_ss_ct : (initSevm (childMsg.withBenv benv')).currentTarget = callee :=
                hc_ct
              have hat : CodeSem.At c.sem sevm.currentTarget 0
                  (initSevm (childMsg.withBenv benv'))
                  (initDevm (childMsg.withBenv benv')) := by
                refine ⟨hchildPre.code, ?_⟩
                intro h_eq_ct
                rw [h_ss_ct] at h_eq_ct
                refine ⟨?_, rfl⟩
                show some (initSevm (childMsg.withBenv benv')).code.toList = c.sem.image
                have h_code_c : (initSevm (childMsg.withBenv benv')).code = code0 := hc_code
                rw [h_code_c, h_code0]
                have h_ad : (addAccessedAddress devm7 callee).state.getCode callee
                    = s.getCode sevm.currentTarget := by
                  have h8 := h_st8
                  rw [h8, h_eq_ct]; rfl
                have h_notdel : ¬ isValidDelegation
                    ((addAccessedAddress devm7 callee).state.getCode callee) := by
                  rw [h_ad]; exact c.sem.not_delegation hcode
                have h_none : getDelegatedCodeAddress
                    ((addAccessedAddress devm7 callee).state.getCode callee) = none := by
                  dsimp only [getDelegatedCodeAddress]
                  exact ite_eq_right_of_eq_false _ _ (eq_false h_notdel)
                rw [h_ad]
                exact hcode
              have h_depth_lt : (initSevm (childMsg.withBenv benv')).depth < sevm.depth := by
                have h_dep : (initSevm (childMsg.withBenv benv')).depth = sevm.depth - 1 :=
                  hc_depth
                rw [h_dep]
                omega
              have hchildFork : F (initSevm (childMsg.withBenv benv')).benvStat.fork := by
                change F (childMsg.withBenv benv').benv.stat.fork
                rw [hstat]
                exact hF
              exact ih 0 (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv'))
                evm2 ex_sub hq h_depth_lt hat hchildFork ⟨hchildPre, fun _ => Mem.wf_empty⟩
          exact Post.of_state_eq hchildPost h_sf_state
  | flat g =>
    -- Under `.flat` the accessed set is untouched, so delegation resolves
    -- straight off `devm7`.
    cases hd : sevm.benvStat.rules.delegationEnabled with
    | true =>
      simp only [ha, ForkRules.accessDelegation, hd, ↓reduceIte] at h_run
      -- delegation resolution
      rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
          devm7 callee with
        ⟨dp, na, code0, dagc, devm9⟩
      simp only [hp11] at h_run
      have h_code0 :
          code0 = (sevm.benvStat.rules.gas.accessDelegation
            devm7 callee).2.2.1 := by
        rw [hp11]
      have h_st9 : devm9.state = devm7.state := by
        have h := congrArg (fun q => (q.2.2.2.2 : Devm).state) hp11
        dsimp only at h
        rw [← h, GasSchedule.accessDelegation_state]
      have h_st8 : devm7.state = s.state := h_st7.symm
      -- charge the call gas
      split at h_run
      · cases XStep.run_ofExcept_error h_run
      rename_i devm10 eq16
      have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
      have h_st11 :
          (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
            = s.state := by
        show devm10.state = s.state
        rw [← h_st10, h_st9, h_st8]
      clear h_st10 h_st9 h_st7 eq16
      -- static-context assertion
      split at h_run
      case h_1 => cases XStep.run_ofExcept_error h_run
      case h_2 =>
      split at h_run
      · -- insufficient balance : call fails, state unchanged
        split at h_run
        case h_1 => cases XStep.run_ofExcept_error h_run
        case h_2 =>
        rename_i devm12 eq20
        apply post_of_state_eq_debited hside hle hinv _
        have h_ex := Except.ok.inj h_run.2
        rw [h_ex]
        show devm12.state = s.state
        rw [← (Devm.push_of_push eq20).state]
        exact h_st11
      · -- balance is sufficient : the call goes through
        simp only [genericCall.step] at h_run
        split at h_run
        · -- depth limit reached : call fails, state unchanged
          simp only [Bind.bind, Except.bind] at h_run
          split at h_run
          case h_1 => cases XStep.run_ofExcept_error h_run
          case h_2 =>
          rename_i devm12 h_push
          apply post_of_state_eq_debited hside hle hinv _
          have h_ex := Except.ok.inj h_run.2
          rw [h_ex]
          show devm12.state = s.state
          rw [← (Devm.push_of_push h_push).state]
          exact h_st11
        · -- the call is executed
          simp only [XStep.Run] at h_run
          rcases h_run with ⟨ex', run_pm₀, h_split⟩
          obtain ⟨childMsg, run_pm, hc_stv, hc_state, hc_stat, hc_caller, hc_value, hc_ct,
              hc_ca, hc_code, hc_depth⟩ :
              ∃ m : Msg, ProcessMessage m xl ex' ∧
                m.shouldTransferValue = true ∧ m.benv.state = s.state ∧
                m.benv.stat = sevm.benvStat ∧
                m.caller = sevm.currentTarget ∧ m.value = value ∧
                m.currentTarget = callee ∧ m.codeAddress = some na ∧
                m.code = code0 ∧ m.depth = sevm.depth - 1 :=
            ⟨_, run_pm₀, rfl, h_st11, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          clear run_pm₀
          rcases ex' with err' | child
          · cases Resume.call_run_error h_split.symm
          have h_sf_state : sf.state = child.state := Resume.call_state h_split.symm
          obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run_pm
          unfold FrameBody at hbody
          rcases eq_bt : childMsg.benvAfterTransfer with e | benv' <;>
            rw [eq_bt] at hbody
          · rw [hbody.2, processMessage.settle_error] at hset
            cases hset
          have run_ec : ExecuteCode (childMsg.withBenv benv') xl r0 := hbody
          -- the child's initial state satisfies the precondition: after the value
          -- transfer, or unchanged when no value moves (zero-value entry)
          have hchildPre : c.Pre sevm.currentTarget (initSevm (childMsg.withBenv benv'))
              (initDevm (childMsg.withBenv benv')) := by
            by_cases h_nz : value ≠ 0
            · rcases of_benvAfterTransfer hc_stv (by rw [hc_value]; exact h_nz) eq_bt with
                ⟨st_mid, h_sub, hB⟩
              rw [hc_state, hc_caller, hc_value] at h_sub
              have hBs : benv'.state = st_mid.addBal callee value := by
                rw [hB, hc_ct, hc_value]; rfl
              apply Pre.child_of_outbound_transfer (st := s.state) (st_mid := st_mid)
                (target := callee) (value := value)
              · exact hcode
              · exact hside
              · exact hinv
              · exact h_sub
              · exact hBs
              · exact hc_ct
              · exact hc_value
            · have hv0 : value = 0 := not_not.mp h_nz
              have hbenv : benv' = childMsg.benv :=
                benvAfterTransfer_eq_of_not_transfer
                  (fun h => h_nz (by rw [← hc_value]; exact h.2)) eq_bt
              have hstate : (initDevm (childMsg.withBenv benv')).state = s.state := by
                show benv'.state = _
                rw [hbenv, hc_state]
              refine Pre.of_inv_eqs ?_ (fun _ => by show childMsg.value = 0; rw [hc_value, hv0])
              rw [hstate]
              refine ⟨hcode, hside, ?_⟩
              have hinv0 := hinv
              rw [hv0, B256.sub_zero] at hinv0
              exact hinv0
          -- resolve the settlement : rollback or a clean sub-message result
          obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
          subst h_r0
          rcases h_settle with ⟨h_err2, h_if⟩ | ⟨h_err2, h_if⟩
          · -- sub-message failed : state rolled back to the pre-transfer state
            apply post_of_state_eq_debited hside hle hinv _
            rw [h_sf_state, ← h_if]
            exact hc_state
          have h_if' := h_if.symm
          subst h_if'
          simp only [Devm.recordTouch_state] at h_sf_state
          have h_wb_ca : (childMsg.withBenv benv').codeAddress = some na := hc_ca
          have hchildPost : c.Post sevm.currentTarget
              (initSevm (childMsg.withBenv benv')) evm2 := by
            rcases of_executeCode_someCode h_wb_ca run_ec with
              ⟨_, _, h_he⟩ | ⟨_, ex''', h_xl_some, h_he⟩
            · -- precompile : only the transfer
              have h_child_state :
                  evm2.state = (initDevm (childMsg.withBenv benv')).state := by
                exact state_of_executePrecomp_ok h_he h_err2
              exact post_of_pre (hchildPre.state_eq h_child_state)
            · -- regular callee : a sub-execution takes place
              rw [h_xl_some] at h_fill
              dsimp only [Xlot.FilledWith] at h_fill
              have hstat : (childMsg.withBenv benv').benv.stat = sevm.benvStat := by
                show benv'.stat = sevm.benvStat
                rw [benvAfterTransfer_stat eq_bt, hc_stat]
              have hexn : ex''' = .ok evm2 := exec_ok_of_handleError h_he h_err2
              subst hexn
              obtain ⟨ex_sub, hq⟩ := h_fill
              have h_ss_ct : (initSevm (childMsg.withBenv benv')).currentTarget = callee :=
                hc_ct
              have hat : CodeSem.At c.sem sevm.currentTarget 0
                  (initSevm (childMsg.withBenv benv'))
                  (initDevm (childMsg.withBenv benv')) := by
                refine ⟨hchildPre.code, ?_⟩
                intro h_eq_ct
                rw [h_ss_ct] at h_eq_ct
                refine ⟨?_, rfl⟩
                show some (initSevm (childMsg.withBenv benv')).code.toList = c.sem.image
                have h_code_c : (initSevm (childMsg.withBenv benv')).code = code0 := hc_code
                rw [h_code_c, h_code0]
                have h_ad : devm7.state.getCode callee
                    = s.getCode sevm.currentTarget := by
                  have h8 := h_st8
                  rw [h8, h_eq_ct]; rfl
                have h_notdel : ¬ isValidDelegation
                    (devm7.state.getCode callee) := by
                  rw [h_ad]; exact c.sem.not_delegation hcode
                have h_none : getDelegatedCodeAddress
                    (devm7.state.getCode callee) = none := by
                  dsimp only [getDelegatedCodeAddress]
                  exact ite_eq_right_of_eq_false _ _ (eq_false h_notdel)
                have h_gas_code :
                    (sevm.benvStat.rules.gas.accessDelegation
                      devm7 callee).2.2.1 =
                      devm7.state.getCode callee := by
                  unfold GasSchedule.accessDelegation
                  dsimp only
                  rw [h_none]
                rw [h_gas_code, h_ad]
                exact hcode
              have h_depth_lt : (initSevm (childMsg.withBenv benv')).depth < sevm.depth := by
                have h_dep : (initSevm (childMsg.withBenv benv')).depth = sevm.depth - 1 :=
                  hc_depth
                rw [h_dep]
                omega
              have hchildFork : F (initSevm (childMsg.withBenv benv')).benvStat.fork := by
                change F (childMsg.withBenv benv').benv.stat.fork
                rw [hstat]
                exact hF
              exact ih 0 (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv'))
                evm2 ex_sub hq h_depth_lt hat hchildFork ⟨hchildPre, fun _ => Mem.wf_empty⟩
          exact Post.of_state_eq hchildPost h_sf_state
    | false =>
      simp only [ha] at h_run
      -- delegation resolution: disabled, so the machine is unchanged
      rcases hp11 : sevm.benvStat.rules.accessDelegation
          devm7 callee with
        ⟨dp, na, code0, dagc, devm9⟩
      simp only [hp11] at h_run
      have hdis : sevm.benvStat.rules.accessDelegation
          devm7 callee =
          ⟨false, callee, devm7.state.getCode callee, 0, devm7⟩ :=
        ForkRules.accessDelegation_disabled hd _ _
      have h_eq : (⟨dp, na, code0, dagc, devm9⟩ :
          Bool × Adr × ByteArray × Nat × Devm) =
          ⟨false, callee, devm7.state.getCode callee, 0, devm7⟩ :=
        hp11.symm.trans hdis
      have h_code0 : code0 = devm7.state.getCode callee :=
        congrArg (·.2.2.1) h_eq
      have h_st9 : devm9.state = devm7.state :=
        congrArg (fun q => (q.2.2.2.2 : Devm).state) h_eq
      have h_st8 : devm7.state = s.state := h_st7.symm
      -- charge the call gas
      split at h_run
      · cases XStep.run_ofExcept_error h_run
      rename_i devm10 eq16
      have h_st10 : devm9.state = devm10.state := (Devm.burn_of_chargeGas eq16).state
      have h_st11 :
          (devm10.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).state
            = s.state := by
        show devm10.state = s.state
        rw [← h_st10, h_st9, h_st8]
      clear h_st10 h_st9 h_st7 eq16
      -- static-context assertion
      split at h_run
      case h_1 => cases XStep.run_ofExcept_error h_run
      case h_2 =>
      split at h_run
      · -- insufficient balance : call fails, state unchanged
        split at h_run
        case h_1 => cases XStep.run_ofExcept_error h_run
        case h_2 =>
        rename_i devm12 eq20
        apply post_of_state_eq_debited hside hle hinv _
        have h_ex := Except.ok.inj h_run.2
        rw [h_ex]
        show devm12.state = s.state
        rw [← (Devm.push_of_push eq20).state]
        exact h_st11
      · -- balance is sufficient : the call goes through
        simp only [genericCall.step] at h_run
        split at h_run
        · -- depth limit reached : call fails, state unchanged
          simp only [Bind.bind, Except.bind] at h_run
          split at h_run
          case h_1 => cases XStep.run_ofExcept_error h_run
          case h_2 =>
          rename_i devm12 h_push
          apply post_of_state_eq_debited hside hle hinv _
          have h_ex := Except.ok.inj h_run.2
          rw [h_ex]
          show devm12.state = s.state
          rw [← (Devm.push_of_push h_push).state]
          exact h_st11
        · -- the call is executed
          simp only [XStep.Run] at h_run
          rcases h_run with ⟨ex', run_pm₀, h_split⟩
          obtain ⟨childMsg, run_pm, hc_stv, hc_state, hc_stat, hc_caller, hc_value, hc_ct,
              hc_ca, hc_code, hc_depth⟩ :
              ∃ m : Msg, ProcessMessage m xl ex' ∧
                m.shouldTransferValue = true ∧ m.benv.state = s.state ∧
                m.benv.stat = sevm.benvStat ∧
                m.caller = sevm.currentTarget ∧ m.value = value ∧
                m.currentTarget = callee ∧ m.codeAddress = some na ∧
                m.code = code0 ∧ m.depth = sevm.depth - 1 :=
            ⟨_, run_pm₀, rfl, h_st11, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          clear run_pm₀
          rcases ex' with err' | child
          · cases Resume.call_run_error h_split.symm
          have h_sf_state : sf.state = child.state := Resume.call_state h_split.symm
          obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp run_pm
          unfold FrameBody at hbody
          rcases eq_bt : childMsg.benvAfterTransfer with e | benv' <;>
            rw [eq_bt] at hbody
          · rw [hbody.2, processMessage.settle_error] at hset
            cases hset
          have run_ec : ExecuteCode (childMsg.withBenv benv') xl r0 := hbody
          -- the child's initial state satisfies the precondition: after the value
          -- transfer, or unchanged when no value moves (zero-value entry)
          have hchildPre : c.Pre sevm.currentTarget (initSevm (childMsg.withBenv benv'))
              (initDevm (childMsg.withBenv benv')) := by
            by_cases h_nz : value ≠ 0
            · rcases of_benvAfterTransfer hc_stv (by rw [hc_value]; exact h_nz) eq_bt with
                ⟨st_mid, h_sub, hB⟩
              rw [hc_state, hc_caller, hc_value] at h_sub
              have hBs : benv'.state = st_mid.addBal callee value := by
                rw [hB, hc_ct, hc_value]; rfl
              apply Pre.child_of_outbound_transfer (st := s.state) (st_mid := st_mid)
                (target := callee) (value := value)
              · exact hcode
              · exact hside
              · exact hinv
              · exact h_sub
              · exact hBs
              · exact hc_ct
              · exact hc_value
            · have hv0 : value = 0 := not_not.mp h_nz
              have hbenv : benv' = childMsg.benv :=
                benvAfterTransfer_eq_of_not_transfer
                  (fun h => h_nz (by rw [← hc_value]; exact h.2)) eq_bt
              have hstate : (initDevm (childMsg.withBenv benv')).state = s.state := by
                show benv'.state = _
                rw [hbenv, hc_state]
              refine Pre.of_inv_eqs ?_ (fun _ => by show childMsg.value = 0; rw [hc_value, hv0])
              rw [hstate]
              refine ⟨hcode, hside, ?_⟩
              have hinv0 := hinv
              rw [hv0, B256.sub_zero] at hinv0
              exact hinv0
          -- resolve the settlement : rollback or a clean sub-message result
          obtain ⟨evm2, h_r0, h_settle⟩ := processMessage.settle_ok_cases hset.symm
          subst h_r0
          rcases h_settle with ⟨h_err2, h_if⟩ | ⟨h_err2, h_if⟩
          · -- sub-message failed : state rolled back to the pre-transfer state
            apply post_of_state_eq_debited hside hle hinv _
            rw [h_sf_state, ← h_if]
            exact hc_state
          have h_if' := h_if.symm
          subst h_if'
          simp only [Devm.recordTouch_state] at h_sf_state
          have h_wb_ca : (childMsg.withBenv benv').codeAddress = some na := hc_ca
          have hchildPost : c.Post sevm.currentTarget
              (initSevm (childMsg.withBenv benv')) evm2 := by
            rcases of_executeCode_someCode h_wb_ca run_ec with
              ⟨_, _, h_he⟩ | ⟨_, ex''', h_xl_some, h_he⟩
            · -- precompile : only the transfer
              have h_child_state :
                  evm2.state = (initDevm (childMsg.withBenv benv')).state := by
                exact state_of_executePrecomp_ok h_he h_err2
              exact post_of_pre (hchildPre.state_eq h_child_state)
            · -- regular callee : a sub-execution takes place
              rw [h_xl_some] at h_fill
              dsimp only [Xlot.FilledWith] at h_fill
              have hstat : (childMsg.withBenv benv').benv.stat = sevm.benvStat := by
                show benv'.stat = sevm.benvStat
                rw [benvAfterTransfer_stat eq_bt, hc_stat]
              have hexn : ex''' = .ok evm2 := exec_ok_of_handleError h_he h_err2
              subst hexn
              obtain ⟨ex_sub, hq⟩ := h_fill
              have h_ss_ct : (initSevm (childMsg.withBenv benv')).currentTarget = callee :=
                hc_ct
              have hat : CodeSem.At c.sem sevm.currentTarget 0
                  (initSevm (childMsg.withBenv benv'))
                  (initDevm (childMsg.withBenv benv')) := by
                refine ⟨hchildPre.code, ?_⟩
                intro h_eq_ct
                rw [h_ss_ct] at h_eq_ct
                refine ⟨?_, rfl⟩
                show some (initSevm (childMsg.withBenv benv')).code.toList = c.sem.image
                have h_code_c : (initSevm (childMsg.withBenv benv')).code = code0 := hc_code
                rw [h_code_c, h_code0]
                have h_ad : devm7.state.getCode callee
                    = s.getCode sevm.currentTarget := by
                  have h8 := h_st8
                  rw [h8, h_eq_ct]; rfl
                have h_notdel : ¬ isValidDelegation
                    (devm7.state.getCode callee) := by
                  rw [h_ad]; exact c.sem.not_delegation hcode
                have h_none : getDelegatedCodeAddress
                    (devm7.state.getCode callee) = none := by
                  dsimp only [getDelegatedCodeAddress]
                  exact ite_eq_right_of_eq_false _ _ (eq_false h_notdel)
                rw [h_ad]
                exact hcode
              have h_depth_lt : (initSevm (childMsg.withBenv benv')).depth < sevm.depth := by
                have h_dep : (initSevm (childMsg.withBenv benv')).depth = sevm.depth - 1 :=
                  hc_depth
                rw [h_dep]
                omega
              have hchildFork : F (initSevm (childMsg.withBenv benv')).benvStat.fork := by
                change F (childMsg.withBenv benv').benv.stat.fork
                rw [hstat]
                exact hF
              exact ih 0 (initSevm (childMsg.withBenv benv')) (initDevm (childMsg.withBenv benv'))
                evm2 ex_sub hq h_depth_lt hat hchildFork ⟨hchildPre, fun _ => Mem.wf_empty⟩
          exact Post.of_state_eq hchildPost h_sf_state

end ContractSpecSem

end Blanc
