-- Weth10Sound.lean : backing-invariant walks for the concrete WETH10 runtime.

import Blanc.CommonProofs
import Blanc.Weth10
import Blanc.Weth10Spec

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Nonpayable entry seam -/

/-- A successful WETH10 nonpayable wrapper factors through the endpoint body
at a world-state- and memory-equivalent machine state, and only with zero
callvalue. The memory equation lets functional observations cross the wrapper
without assuming a pristine scratch area. -/
theorem run_body_of_run_nonpayable_frame
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧
      s.memory = mid.memory ∧ Func.Run fs sevm mid body r := by
  unfold nonpayable at run
  refine run_prepend_elim _ [callvalue, iszero] ?_ run
  intro s1 hline hbranch
  rcases Line.of_run_cons hline with ⟨s0, hcv, hline'⟩
  rcases Line.of_run_cons hline' with ⟨s1', hiz, hnil⟩
  cases hnil
  have hpv : [sevm.value] <<+ s0.stack :=
    prefix_of_push (of_run_callvalue hcv) nil_pref
  have hpflag : [sevm.value =? 0] <<+ s1.stack :=
    prefix_of_iszero hiz hpv
  rcases of_run_branch hbranch with
    ⟨s2, hpop, hrev⟩ | ⟨w, s2, s3, hnz, hpop, hburn, hbody⟩
  · exact absurd hrev not_run_rev
  · have hpop' := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop'
    rw [hpop'] at hpflag
    have hw : (sevm.value =? 0) = w :=
      pref_head_unique hpflag (pref_append [w] s2.stack)
    have hflag : (sevm.value =? 0) ≠ 0 := by
      rw [hw]
      exact hnz
    have hv : sevm.value = 0 := by
      by_cases hv : sevm.value = 0
      · exact hv
      · simp [B256.eqCheck, hv] at hflag
    refine ⟨s3, hv, ?_, ?_, hbody⟩
    · exact (Line.of_inv Devm.state (by line_inv) hline).trans
        (hpop.state.trans hburn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
        (hpop.memory.trans hburn.memory)

/-- Compatibility projection of `run_body_of_run_nonpayable_frame` retaining
the original state-level API used by backing proofs. -/
theorem run_body_of_run_nonpayable
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧
      Func.Run fs sevm mid body r := by
  rcases run_body_of_run_nonpayable_frame run with
    ⟨mid, hv, hstate, _, hbody⟩
  exact ⟨mid, hv, hstate, hbody⟩

/-- A successful run through WETH10's shared nonpayable wrapper can only take
the endpoint arm, so the frame value is zero. -/
theorem value_eq_zero_of_run_nonpayable
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    sevm.value = 0 :=
  (run_body_of_run_nonpayable run).choose_spec.1

/-- A state-silent nonpayable endpoint preserves WETH10 backing.  The two
`Func.Inv` premises are deliberately over the wrapped endpoint: callers can
usually discharge them with `func_inv`, while endpoints containing an
auxiliary tail call must supply their own fixed-context walk. -/
theorem backedSpec_nonpayable_funcSound_of_inv
    (dp : DeployParams) (ca : Adr) (body : Func)
    (h_stor : Func.Inv Devm.getStor Devm.getStor (nonpayable body))
    (h_bal : Func.Inv Devm.getBal Devm.getBal (nonpayable body)) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable body) := by
  intro sevm s r h_target h_pre h_ih run
  subst ca
  refine ⟨Func.preserves_nof run h_pre.side, ?_⟩
  change Stor.Weth10Inv
    (Devm.getStor r sevm.currentTarget) 0
    (Devm.getBal r sevm.currentTarget)
  have h_value : sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable run
  have h_inv : Stor.Weth10Inv
      (Devm.getStor s sevm.currentTarget) sevm.value
      (Devm.getBal s sevm.currentTarget) :=
    h_pre.inv.1 rfl
  have hs : Devm.getStor s = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor h_stor run
  have hb : Devm.getBal s = Devm.getBal r :=
    Func.of_inv Devm.getBal Devm.getBal h_bal run
  rw [← congrFun hs sevm.currentTarget, ← congrFun hb sevm.currentTarget]
  simpa only [h_value] using h_inv

/-! ## Receive / mint-caller backing proof -/

/-- A successful `mintCaller` run credits the caller by the frame value and
leaves the disjoint flash-minted counter unchanged.  The later deposit proof
can reuse the same concrete runtime walk because `receiveEther` and `deposit`
are definitionally this body. -/
theorem mintCaller_storage {fs : List Func} {sevm : Sevm} {s r : Devm}
    (run : Func.Run fs sevm s mintCaller r) :
    Increase sevm.caller sevm.value
        (Stor.rest (Devm.getStor s sevm.currentTarget))
        (Stor.rest (Devm.getStor r sevm.currentTarget)) ∧
      (Devm.getStor r sevm.currentTarget).get flashMintedSlot =
        (Devm.getStor s sevm.currentTarget).get flashMintedSlot := by
  unfold mintCaller at run
  rcases of_run_next run with ⟨s1, h_caller, run1⟩
  rcases of_run_next run1 with ⟨s2, h_sload, run2⟩
  rcases of_run_next run2 with ⟨s3, h_callvalue, run3⟩
  rcases of_run_next run3 with ⟨s4, h_add, run4⟩
  rcases of_run_next run4 with ⟨s5, h_caller2, run5⟩
  rcases of_run_next run5 with ⟨s6, h_sstore, run6⟩
  have hp0 : [] <<+ s.stack := nil_pref
  have hp1 : [sevm.caller.toB256] <<+ s1.stack :=
    prefix_of_push (of_run_caller h_caller) hp0
  have hs1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons h_caller Line.Run.nil)
  rcases prefix_of_sload h_sload hp1 with ⟨callerBal, hp2, hcallerBal⟩
  have hs2 : Devm.getStor s1 = Devm.getStor s2 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons h_sload Line.Run.nil)
  have hp3 : [sevm.value, callerBal] <<+ s3.stack :=
    prefix_of_push (of_run_callvalue h_callvalue) hp2
  have hs3 : Devm.getStor s2 = Devm.getStor s3 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons h_callvalue Line.Run.nil)
  have hp4 : [sevm.value + callerBal] <<+ s4.stack :=
    prefix_of_add h_add hp3
  have hs4 : Devm.getStor s3 = Devm.getStor s4 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons h_add Line.Run.nil)
  have hp5 : [sevm.caller.toB256, sevm.value + callerBal] <<+ s5.stack :=
    prefix_of_push (of_run_caller h_caller2) hp4
  have hs5 : Devm.getStor s4 = Devm.getStor s5 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons h_caller2 Line.Run.nil)
  have hs_before : Devm.getStor s = Devm.getStor s5 := by
    rw [hs1, hs2, hs3, hs4, hs5]
  have hcallerBal' :
      callerBal =
        (Devm.getStor s5 sevm.currentTarget).get sevm.caller.toB256 := by
    rw [hcallerBal]
    show (Devm.getStor s1 sevm.currentTarget).get sevm.caller.toB256 = _
    rw [hs2, hs3, hs4, hs5]
  have h_set :
      Devm.getStor s6 sevm.currentTarget =
        (Devm.getStor s5 sevm.currentTarget).set sevm.caller.toB256
          (sevm.value + callerBal) :=
    sstore_getStor_set h_sstore hp5
  have hs_after : Devm.getStor s6 = Devm.getStor r := by
    apply Func.of_inv _ _ _ run6
    func_inv
  constructor
  · rw [hs_before, ← hs_after]
    intro a
    constructor
    · intro h_eq
      simp only [Stor.rest, Function.comp_apply, h_set]
      rw [← h_eq, Stor.get_set_self, ← hcallerBal', B256.add_comm]
    · intro h_ne
      simp only [Stor.rest, Function.comp_apply, h_set]
      exact (Stor.get_set_ne _
        (fun hc => h_ne (Adr.toB256_inj hc)) _).symm
  · have h_flash_ne : sevm.caller.toB256 ≠ flashMintedSlot := by
      simpa only [balanceKey] using
        balanceKey_ne_flashMintedSlot sevm.caller
    rw [← hs_after, h_set, Stor.get_set_ne _ h_flash_ne _, ← hs_before]

/-- The receive-specific `FuncSound` premise of the generic receive-aware
dispatcher theorem.  It is uniform in both deployment parameters and contract
address: neither affects the concrete receive body. -/
theorem backedSpec_receiveEther_funcSound
    (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux receiveEther := by
  intro sevm s r h_target h_pre _ run
  subst ca
  refine ⟨?_, ?_⟩
  · change sum r.getBal < 2 ^ 256
    exact Func.preserves_nof run h_pre.side
  · change Stor.Weth10Inv
      (Devm.getStor r sevm.currentTarget) 0
      (r.getBal sevm.currentTarget)
    have h_inv : Stor.Weth10Inv
        (Devm.getStor s sevm.currentTarget) sevm.value
        (s.getBal sevm.currentTarget) :=
      h_pre.inv.1 rfl
    have h_bal : s.getBal = r.getBal :=
      Func.of_inv Devm.getBal Devm.getBal (by func_inv) run
    obtain ⟨h_inc, h_flash⟩ :=
      mintCaller_storage (by simpa only [receiveEther] using run)
    rw [← h_bal]
    exact Stor.Weth10Inv.deposit h_inv h_inc h_flash

theorem backedSpec_deposit_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux deposit :=
  backedSpec_receiveEther_funcSound dp ca

/-! ## State-silent nonpayable selectors -/

theorem backedSpec_name_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable name) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca name (by func_inv) (by func_inv)

theorem backedSpec_totalSupply_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable totalSupply) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca totalSupply (by func_inv) (by func_inv)

theorem backedSpec_permitTypehash_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable permitTypehash) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca permitTypehash (by func_inv) (by func_inv)

theorem backedSpec_decimals_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable decimals) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca decimals (by func_inv) (by func_inv)

theorem backedSpec_domainSeparator_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux
      (nonpayable (domainSeparator dp)) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca (domainSeparator dp)
    (by
      unfold nonpayable domainSeparator returnDeployWord pushDeployWord
      func_inv)
    (by
      unfold nonpayable domainSeparator returnDeployWord pushDeployWord
      func_inv)

theorem backedSpec_maxFlashLoan_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable maxFlashLoan) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca maxFlashLoan
    (by func_inv) (by func_inv)

theorem backedSpec_balanceOf_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux
      (nonpayable balanceOfEndpoint) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca balanceOfEndpoint
    (by func_inv) (by func_inv)

theorem backedSpec_nonces_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable nonces) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca nonces (by func_inv) (by func_inv)

theorem backedSpec_callbackSuccess_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux
      (nonpayable callbackSuccess) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca callbackSuccess
    (by func_inv) (by func_inv)

theorem backedSpec_flashMinted_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable flashMinted) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca flashMinted
    (by func_inv) (by func_inv)

theorem backedSpec_symbol_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable symbol) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca symbol (by func_inv) (by func_inv)

theorem backedSpec_deploymentChainId_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux
      (nonpayable (deploymentChainId dp)) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca (deploymentChainId dp)
    (by
      unfold nonpayable deploymentChainId returnDeployWord pushDeployWord
      func_inv)
    (by
      unfold nonpayable deploymentChainId returnDeployWord pushDeployWord
      func_inv)

theorem backedSpec_allowance_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux (nonpayable allowance) :=
  backedSpec_nonpayable_funcSound_of_inv dp ca allowance (by func_inv) (by func_inv)

/-! ## Fixed-error view selector -/

/-- A successful `flashFee` walk cannot have taken its wrong-token error arm:
that arm reaches the fixed `flashTokenError` reverter in the exact auxiliary
table.  The only successful arm returns zero and leaves persistent state
unchanged. -/
theorem run_flashFee_observations_eq
    (dp : DeployParams) {sevm : Sevm} {s r : Devm}
    (run : Func.Run ((weth10 dp).main :: weth10Aux) sevm s flashFee r) :
    Devm.getStor s = Devm.getStor r ∧
      Devm.getBal s = Devm.getBal r := by
  unfold flashFee at run
  refine run_prepend_elim _ (arg 0 ++ [address, eq, iszero]) ?_ run
  intro mid hline hbranch
  rcases of_run_branch hbranch with
      ⟨s1, hpop, hret⟩ |
      ⟨w, s1, s2, hnz, hpop, hburn, hcall⟩
  · constructor
    · exact (Line.of_inv Devm.getStor (by line_inv) hline).trans
        ((PopBurn.Inv.inv hpop).trans
          (Func.of_inv Devm.getStor Devm.getStor (by func_inv) hret))
    · exact (Line.of_inv Devm.getBal (by line_inv) hline).trans
        ((PopBurn.Inv.inv hpop).trans
          (Func.of_inv Devm.getBal Devm.getBal (by func_inv) hret))
  · rcases of_run_call hcall with ⟨f, s3, hget, hcallBurn, hrev⟩
    have hf : f = flashTokenError := by
      simpa [weth10, weth10Aux, flashTokenErrorSlot] using hget.symm
    subst f
    exact absurd hrev Func.not_run_revWith

theorem backedSpec_flashFee_funcSound (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).FuncSound ca weth10Aux
      (nonpayable flashFee) := by
  intro sevm s r h_target h_pre h_ih run
  subst ca
  refine ⟨Func.preserves_nof run h_pre.side, ?_⟩
  change Stor.Weth10Inv
    (Devm.getStor r sevm.currentTarget) 0
    (Devm.getBal r sevm.currentTarget)
  obtain ⟨mid, h_value, h_state_mid, h_body⟩ :=
    run_body_of_run_nonpayable run
  have h_stor_mid : Devm.getStor s = Devm.getStor mid := by
    funext a
    change (s.state.get a).stor = (mid.state.get a).stor
    rw [h_state_mid]
  have h_bal_mid : Devm.getBal s = Devm.getBal mid := by
    funext a
    change (s.state.get a).bal = (mid.state.get a).bal
    rw [h_state_mid]
  obtain ⟨h_stor_body, h_bal_body⟩ :=
    run_flashFee_observations_eq dp h_body
  have h_stor := h_stor_mid.trans h_stor_body
  have h_bal := h_bal_mid.trans h_bal_body
  have h_inv : Stor.Weth10Inv
      (Devm.getStor s sevm.currentTarget) sevm.value
      (Devm.getBal s sevm.currentTarget) :=
    h_pre.inv.1 rfl
  rw [← congrFun h_stor sevm.currentTarget,
      ← congrFun h_bal sevm.currentTarget]
  simpa only [h_value] using h_inv

/-! ## Receive-aware dispatcher assembly -/

/-- With receive and the reverting fallback discharged here, the exact WETH10
runtime has one remaining RL4 premise: `FuncSound` for every member of its
27-entry selector list. -/
theorem backedSpec_sound_of_funcSound_all
    (dp : DeployParams) (ca : Adr)
    (h_funcs : ∀ p ∈ weth10Funcs dp,
      (backedSpec weth10 dp).FuncSound ca weth10Aux p.2) :
    (backedSpec weth10 dp).Sound ca := by
  refine ContractSpec.sound_of_receive_dispatch
    (k := fallbackSlot) (funcs := weth10Funcs dp) (aux := weth10Aux)
    (fallback := Func.rev) (receive := receiveEther)
    rfl (List.cons_ne_nil _ _) rfl h_funcs ?_
    (backedSpec_receiveEther_funcSound dp ca)
  intro sevm s r h_target h_pre h_ih run
  exact absurd run not_run_rev

/-- The frame-level RL4 result has the same sole remaining selector-family
premise; all receive-aware dispatcher and ladder plumbing is discharged. -/
theorem backedSpec_preserves_of_funcSound_all
    (dp : DeployParams) (ca : Adr)
    (h_funcs : ∀ p ∈ weth10Funcs dp,
      (backedSpec weth10 dp).FuncSound ca weth10Aux p.2) :
    (backedSpec weth10 dp).Preserves ca :=
  (backedSpec weth10 dp).preserves_inv ca
    (backedSpec_sound_of_funcSound_all dp ca h_funcs)

end Weth10

end Blanc
