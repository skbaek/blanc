-- WETH10's reusable selector-entry route and functional observations.

import Blanc.Weth10Sound

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

private lemma entryFlag_logs {e : Sevm} {s t : Devm}
    (run : Line.Run e s [calldatasize, iszero] t) : s.logs = t.logs := by
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨s2, q2, hnil⟩
  cases hnil
  exact (of_run_calldatasize q1).logs.trans
    (Ninst.Hinv.inv (f := Devm.logs) q2)

private lemma entryFlag_output {e : Sevm} {s t : Devm}
    (run : Line.Run e s [calldatasize, iszero] t) : s.output = t.output := by
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨s2, q2, hnil⟩
  cases hnil
  exact (of_run_calldatasize q1).output.trans
    (Ninst.Hinv.inv (f := Devm.output) q2)

/-! ## Selector entry

Functional endpoint theorems start below the dispatcher, but their public
statements concern executions of the compiled program. This route factors any
successful recognized-selector execution through the exact selected leaf. It
also records that entry, selector extraction, and dispatch do not alter world
state or memory.

The nonempty premise is stated in the machine word observed by CALLDATASIZE.
Canonical ABI calls discharge it immediately, while avoiding an artificial
theorem about impossible Nat-sized calldata beyond 2^256.
-/

theorem exec_enters_weth10Selector_logs
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    {sig : B256} {body : Func}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = sig)
    (h_nonempty : sevm.data.length.toB256 ≠ 0)
    (h_mem : (sig, body) ∈ weth10Funcs dp) :
    ∃ s',
      Devm.getStor s' = Devm.getStor pre ∧
      Devm.getBal s' = Devm.getBal pre ∧
      Devm.getCode s' = Devm.getCode pre ∧
      s'.memory = pre.memory ∧
      s'.logs = pre.logs ∧
      s'.output = pre.output ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm s' body post := by
  have h_run : Prog.Run sevm pre (weth10 dp) post :=
    correct sevm pre (weth10 dp) post exc h_code
  dsimp only [Prog.Run] at h_run
  cases h_run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases h_eq
  have run' : Func.Run ((weth10 dp).main :: weth10Aux) sevm s₀
      (calldatasize ::: iszero :::
        (receiveEther <?>
          (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)))) post := by
    simpa only [weth10, weth10Main] using run
  clear run
  refine run_prepend_elim _ [calldatasize, iszero] ?_ run'
  intro s₁ h₁ run₁
  rcases Line.of_run_cons h₁ with ⟨t, h_size, h_rest⟩
  rcases Line.of_run_cons h_rest with ⟨u, h_zero, h_nil⟩
  cases h_nil
  have hp_size : [sevm.data.length.toB256] <<+ t.stack :=
    prefix_of_push (of_run_calldatasize h_size) nil_pref
  have hp_flag : [sevm.data.length.toB256 =? 0] <<+ s₁.stack :=
    prefix_of_iszero h_zero hp_size
  rcases of_run_branch run₁ with
      ⟨s₂, h_pop, h_dispatch⟩ |
      ⟨w, s₂, s₃, h_nz, h_pop, h_burn, h_receive⟩
  · refine run_prepend_elim _ fsig ?_ h_dispatch
    intro s₃ h_fsig h_dispatch'
    have hp_fsig : sig :: [] <<+ s₃.stack := by
      rw [← h_sel]
      exact prefix_of_fsig nil_pref h_fsig
    rcases reach_of_dispatchWith_logs (weth10Funcs_sorted dp) h_mem hp_fsig
        h_dispatch' with
      ⟨s', _, h_state, h_smem, h_slogs, h_soutput, h_runf⟩
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, h_runf⟩
    · have h5 : Devm.getStor s₃ = Devm.getStor s' := by
        funext a
        show (s₃.state.get a).stor = (s'.state.get a).stor
        rw [h_state]
      have h4 : Devm.getStor s₂ = Devm.getStor s₃ :=
        Line.of_inv Devm.getStor (by line_inv) h_fsig
      have h3 : Devm.getStor s₁ = Devm.getStor s₂ := by
        funext a
        show (s₁.state.get a).stor = (s₂.state.get a).stor
        rw [h_pop.state]
      have h2 : Devm.getStor s₀ = Devm.getStor s₁ :=
        Line.of_inv Devm.getStor (by line_inv) h₁
      have h1 : Devm.getStor pre = Devm.getStor s₀ := by
        funext a
        show (pre.state.get a).stor = (s₀.state.get a).stor
        rw [burn.state]
      rw [← h5, ← h4, ← h3, ← h2, ← h1]
    · have h5 : Devm.getBal s₃ = Devm.getBal s' := by
        funext a
        show (s₃.state.get a).bal = (s'.state.get a).bal
        rw [h_state]
      have h4 : Devm.getBal s₂ = Devm.getBal s₃ :=
        Line.of_inv Devm.getBal (by line_inv) h_fsig
      have h3 : Devm.getBal s₁ = Devm.getBal s₂ := by
        funext a
        show (s₁.state.get a).bal = (s₂.state.get a).bal
        rw [h_pop.state]
      have h2 : Devm.getBal s₀ = Devm.getBal s₁ :=
        Line.of_inv Devm.getBal (by line_inv) h₁
      have h1 : Devm.getBal pre = Devm.getBal s₀ := by
        funext a
        show (pre.state.get a).bal = (s₀.state.get a).bal
        rw [burn.state]
      rw [← h5, ← h4, ← h3, ← h2, ← h1]
    · have h5 : Devm.getCode s₃ = Devm.getCode s' := by
        funext a
        show (s₃.state.get a).code = (s'.state.get a).code
        rw [h_state]
      have h4 : Devm.getCode s₂ = Devm.getCode s₃ :=
        Line.of_inv Devm.getCode (by line_inv) h_fsig
      have h3 : Devm.getCode s₁ = Devm.getCode s₂ := by
        funext a
        show (s₁.state.get a).code = (s₂.state.get a).code
        rw [h_pop.state]
      have h2 : Devm.getCode s₀ = Devm.getCode s₁ :=
        Line.of_inv Devm.getCode (by line_inv) h₁
      have h1 : Devm.getCode pre = Devm.getCode s₀ := by
        funext a
        show (pre.state.get a).code = (s₀.state.get a).code
        rw [burn.state]
      rw [← h5, ← h4, ← h3, ← h2, ← h1]
    · have h4 : s₂.memory = s₃.memory :=
        Line.of_inv Devm.memory (by line_inv) h_fsig
      have h3 : s₁.memory = s₂.memory := h_pop.memory
      have h2 : s₀.memory = s₁.memory :=
        Line.of_inv Devm.memory (by line_inv) h₁
      rw [← h_smem, ← h4, ← h3, ← h2, ← burn.memory]
    · have h4 : s₂.logs = s₃.logs := fsig_logs h_fsig
      have h3 : s₁.logs = s₂.logs := h_pop.logs
      have h2 : s₀.logs = s₁.logs := entryFlag_logs h₁
      have h1 : pre.logs = s₀.logs := burn.logs
      rw [← h_slogs, ← h4, ← h3, ← h2, ← h1]
    · have h4 : s₂.output = s₃.output := fsig_output h_fsig
      have h3 : s₁.output = s₂.output := h_pop.output
      have h2 : s₀.output = s₁.output := entryFlag_output h₁
      have h1 : pre.output = s₀.output := burn.output
      rw [← h_soutput, ← h4, ← h3, ← h2, ← h1]
  · have hpop' := h_pop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop'
    rw [hpop'] at hp_flag
    have hw : (sevm.data.length.toB256 =? 0) = w :=
      pref_head_unique hp_flag (pref_append [w] s₂.stack)
    have hflag : (sevm.data.length.toB256 =? 0) ≠ 0 := by
      rw [hw]
      exact h_nz
    have hz : (sevm.data.length.toB256 =? 0) = 0 := by
      simp [B256.eqCheck, h_nonempty]
    exact absurd hz hflag

/-- Empty calldata enters the payable receive body rather than selector
dispatch.  The ingress flag, branch pop, and jump burn preserve world state,
scratch memory, and the existing log prefix. -/
theorem exec_enters_weth10Receive_logs
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_empty : sevm.data.length.toB256 = 0) :
    ∃ s',
      Devm.getStor s' = Devm.getStor pre ∧
      Devm.getBal s' = Devm.getBal pre ∧
      Devm.getCode s' = Devm.getCode pre ∧
      s'.memory = pre.memory ∧
      s'.logs = pre.logs ∧
      s'.output = pre.output ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm s'
        receiveEther post := by
  have h_run : Prog.Run sevm pre (weth10 dp) post :=
    correct sevm pre (weth10 dp) post exc h_code
  dsimp only [Prog.Run] at h_run
  cases h_run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s0
  cases h_eq
  have run' : Func.Run ((weth10 dp).main :: weth10Aux) sevm s0
      (calldatasize ::: iszero :::
        (receiveEther <?>
          (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)))) post := by
    simpa only [weth10, weth10Main] using run
  clear run
  refine run_prepend_elim _ [calldatasize, iszero] ?_ run'
  intro s1 h1 run1
  rcases Line.of_run_cons h1 with ⟨t, hsize, hrest⟩
  rcases Line.of_run_cons hrest with ⟨u, hzero, hnil⟩
  cases hnil
  have hpSize : [sevm.data.length.toB256] <<+ t.stack :=
    prefix_of_push (of_run_calldatasize hsize) nil_pref
  have hpFlag : [sevm.data.length.toB256 =? 0] <<+ s1.stack :=
    prefix_of_iszero hzero hpSize
  rcases of_run_branch run1 with
      ⟨s2, hpop, hdispatch⟩ |
      ⟨w, s2, s3, hnz, hpop, hburn, hreceive⟩
  · have hpop' := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop'
    rw [hpop'] at hpFlag
    have hz : (sevm.data.length.toB256 =? 0) = 0 :=
      pref_head_unique hpFlag (pref_append [0] s2.stack)
    have hone : (sevm.data.length.toB256 =? 0) = 1 := by
      rw [h_empty]
      decide +kernel
    rw [hone] at hz
    exact (B256.zero_ne_one hz.symm).elim
  · have hzeroState : t.state = s1.state :=
      Ninst.Hinv.inv (f := Devm.state) hzero
    have hentryState : s0.state = s1.state :=
      (of_run_calldatasize hsize).state.trans hzeroState
    refine ⟨s3, ?_, ?_, ?_, ?_, ?_, ?_, hreceive⟩
    · funext a
      show (s3.state.get a).stor = (pre.state.get a).stor
      rw [← hburn.state, ← hpop.state,
        ← hentryState, ← burn.state]
    · funext a
      show (s3.state.get a).bal = (pre.state.get a).bal
      rw [← hburn.state, ← hpop.state,
        ← hentryState, ← burn.state]
    · funext a
      show (s3.state.get a).code = (pre.state.get a).code
      rw [← hburn.state, ← hpop.state,
        ← hentryState, ← burn.state]
    · rw [← hburn.memory, ← hpop.memory,
        ← (Line.of_inv Devm.memory (by line_inv) h1), ← burn.memory]
    · rw [← hburn.logs, ← hpop.logs,
        ← entryFlag_logs h1, ← burn.logs]
    · rw [← hburn.output, ← hpop.output,
        ← entryFlag_output h1, ← burn.output]

/-- Compatibility projection of `exec_enters_weth10Selector_logs` preserving
the original selector-entry API. -/
theorem exec_enters_weth10Selector
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    {sig : B256} {body : Func}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = sig)
    (h_nonempty : sevm.data.length.toB256 ≠ 0)
    (h_mem : (sig, body) ∈ weth10Funcs dp) :
    ∃ s',
      Devm.getStor s' = Devm.getStor pre ∧
      Devm.getBal s' = Devm.getBal pre ∧
      Devm.getCode s' = Devm.getCode pre ∧
      s'.memory = pre.memory ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm s' body post := by
  rcases exec_enters_weth10Selector_logs exc h_code h_sel h_nonempty h_mem with
    ⟨s', hstor, hbal, hcode, hmemory, _, _, hrun⟩
  exact ⟨s', hstor, hbal, hcode, hmemory, hrun⟩

/-- Log-carrying companion of `run_body_of_run_nonpayable_frame`.  The wrapper
itself is log-silent, so public event theorems can relate a selected body's
append to the frame-entry log. -/
theorem run_body_of_run_nonpayable_frame_logs
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧
      s.memory = mid.memory ∧ s.logs = mid.logs ∧
      s.output = mid.output ∧
      Func.Run fs sevm mid body r := by
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
    refine ⟨s3, hv, ?_, ?_, ?_, ?_, hbody⟩
    · exact (Line.of_inv Devm.state (by line_inv) hline).trans
        (hpop.state.trans hburn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
        (hpop.memory.trans hburn.memory)
    · have hlineLogs : s.logs = s1.logs :=
        (of_run_callvalue hcv).logs.trans
          (Ninst.Hinv.inv (f := Devm.logs) hiz)
      exact hlineLogs.trans (hpop.logs.trans hburn.logs)
    · have hlineOutput : s.output = s1.output :=
        (of_run_callvalue hcv).output.trans
          (Ninst.Hinv.inv (f := Devm.output) hiz)
      exact hlineOutput.trans (hpop.output.trans hburn.output)

/-- Public recognized-selector entry through the nonpayable guard, carrying
the frame-entry log to the exact endpoint body. -/
theorem exec_enters_weth10Nonpayable_logs
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    {sig : B256} {body : Func}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = sig)
    (h_nonempty : sevm.data.length.toB256 ≠ 0)
    (h_mem : (sig, nonpayable body) ∈ weth10Funcs dp) :
    ∃ mid,
      sevm.value = 0 ∧
      Devm.getStor mid = Devm.getStor pre ∧
      Devm.getBal mid = Devm.getBal pre ∧
      Devm.getCode mid = Devm.getCode pre ∧
      mid.memory = pre.memory ∧
      mid.logs = pre.logs ∧
      mid.output = pre.output ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm mid body post := by
  rcases exec_enters_weth10Selector_logs exc h_code h_sel h_nonempty h_mem with
    ⟨s', hstor, hbal, hcode, hmemory, hlogs, houtput, hrun⟩
  rcases run_body_of_run_nonpayable_frame_logs hrun with
    ⟨mid, hvalue, hstate, hframeMemory, hframeLogs, hframeOutput, hbody⟩
  have hs : Devm.getStor s' = Devm.getStor mid := by
    funext a
    show (s'.state.get a).stor = (mid.state.get a).stor
    rw [hstate]
  have hb : Devm.getBal s' = Devm.getBal mid := by
    funext a
    show (s'.state.get a).bal = (mid.state.get a).bal
    rw [hstate]
  have hc : Devm.getCode s' = Devm.getCode mid := by
    funext a
    show (s'.state.get a).code = (mid.state.get a).code
    rw [hstate]
  exact ⟨mid, hvalue, hs.symm.trans hstor, hb.symm.trans hbal,
    hc.symm.trans hcode, hframeMemory.symm.trans hmemory,
    hframeLogs.symm.trans hlogs, hframeOutput.symm.trans houtput, hbody⟩

/-- A public successful execution of a recognized nonpayable selector reaches
its endpoint body with zero value, while selector ingress and the payability
guard preserve the entry world and scratch-memory image. -/
theorem exec_enters_weth10Nonpayable
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    {sig : B256} {body : Func}
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = sig)
    (h_nonempty : sevm.data.length.toB256 ≠ 0)
    (h_mem : (sig, nonpayable body) ∈ weth10Funcs dp) :
    ∃ mid,
      sevm.value = 0 ∧
      Devm.getStor mid = Devm.getStor pre ∧
      Devm.getBal mid = Devm.getBal pre ∧
      Devm.getCode mid = Devm.getCode pre ∧
      mid.memory = pre.memory ∧
      Func.Run ((weth10 dp).main :: weth10Aux) sevm mid body post := by
  rcases exec_enters_weth10Selector exc h_code h_sel h_nonempty h_mem with
    ⟨s', hstor, hbal, hcode, hmemory, hrun⟩
  rcases run_body_of_run_nonpayable_frame hrun with
    ⟨mid, hvalue, hstate, hframeMemory, hbody⟩
  have hs : Devm.getStor s' = Devm.getStor mid := by
    funext a
    show (s'.state.get a).stor = (mid.state.get a).stor
    rw [hstate]
  have hb : Devm.getBal s' = Devm.getBal mid := by
    funext a
    show (s'.state.get a).bal = (mid.state.get a).bal
    rw [hstate]
  have hc : Devm.getCode s' = Devm.getCode mid := by
    funext a
    show (s'.state.get a).code = (mid.state.get a).code
    rw [hstate]
  exact ⟨mid, hvalue, hs.symm.trans hstor, hb.symm.trans hbal,
    hc.symm.trans hcode, hframeMemory.symm.trans hmemory, hbody⟩

/-- Lift an exact successful body observation to the compiled public selector.
Besides the observation, the result records the recognized-selector value
boundary and the read-only world effects. -/
theorem of_exec_nonpayableObservation
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    {sig : B256} {body : Func} {P : Devm → Prop} {img : Bytes}
    (h_stor : Func.Inv Devm.getStor Devm.getStor body)
    (h_bal : Func.Inv Devm.getBal Devm.getBal body)
    (observe : ∀ {s r : Devm} {img : Bytes},
      Mem.Wf s.memory →
      Mem.Reads s.memory img →
      Func.Run ((weth10 dp).main :: weth10Aux) sevm s body r →
      P r ∧ Devm.getCode s = Devm.getCode r)
    (h_wf : Mem.Wf pre.memory)
    (h_reads : Mem.Reads pre.memory img)
    (exc : Exec 0 sevm pre (.ok post))
    (h_code : some sevm.code.toList = Prog.compile (weth10 dp))
    (h_sel : Sevm.selector sevm = sig)
    (h_nonempty : sevm.data.length.toB256 ≠ 0)
    (h_mem : (sig, nonpayable body) ∈ weth10Funcs dp) :
    sevm.value = 0 ∧ P post ∧
      Devm.getStor post = Devm.getStor pre ∧
      Devm.getBal post = Devm.getBal pre ∧
      Devm.getCode post = Devm.getCode pre := by
  rcases exec_enters_weth10Nonpayable exc h_code h_sel h_nonempty h_mem with
    ⟨mid, hvalue, hstor0, hbal0, hcode0, hmemory, run⟩
  have hwf : Mem.Wf mid.memory := by
    rw [hmemory]
    exact h_wf
  have hrd : Mem.Reads mid.memory img := by
    rw [hmemory]
    exact h_reads
  rcases observe hwf hrd run with ⟨hobs, hcode⟩
  have hstor : Devm.getStor mid = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor h_stor run
  have hbal : Devm.getBal mid = Devm.getBal post :=
    Func.of_inv Devm.getBal Devm.getBal h_bal run
  exact ⟨hvalue, hobs, hstor.symm.trans hstor0,
    hbal.symm.trans hbal0, hcode.symm.trans hcode0⟩

/-! ## Return observations -/

/-- The exact output of WETH10's shared one-word return fragment. The initial
memory image is arbitrary: the fragment overwrites the complete returned
window before reading it back. -/
lemma of_returnWord {fs : List Func} {sevm : Sevm} {s r : Devm}
    {w : B256} {img : Bytes} {xs}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (h : Func.Run fs sevm s (returnWord w) r) :
    ReturnsWord w r ∧ Devm.getCode s = Devm.getCode r := by
  simp only [returnWord] at h
  rcases of_run_next h with ⟨s1, r1, h⟩
  have hp1 : w :: xs <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 r1) hp
  have hm1 : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) r1
  rcases of_run_prepend (mstoreAt 0) _ h with ⟨s2, h2, h⟩
  rcases of_run_mstoreAt_val h2 hp1 with ⟨hp2, hm2⟩
  have hwf2 : Mem.Wf s2.memory := by
    rw [hm2, ← hm1]
    exact h_wf.write _ _
  have hrd2 : Mem.Reads s2.memory (Bytes.writeAt img 0 w.toBytes) := by
    rw [hm2, ← hm1]
    exact Mem.Reads.write h_wf h_reads 0 _
  rcases of_run_prepend (pushList [32, 0]) _ h with ⟨s3, h3, h⟩
  rcases Line.of_run_cons h3 with ⟨u1, q1, h3'⟩
  rcases Line.of_run_cons h3' with ⟨u2, q2, hnil⟩
  cases hnil
  have hu1 : (32 : B256) :: xs <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp2
  have hu2 : (0 : B256) :: (32 : B256) :: xs <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 q2) hu1
  have hm3 : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv) h3
  have hgc : Devm.getCode s = Devm.getCode s3 :=
    ((Ninst.Hinv.inv (f := Devm.getCode) r1).trans
      (Line.of_inv Devm.getCode (by line_inv) h2)).trans
      (Line.of_inv Devm.getCode (by line_inv) h3)
  refine ⟨?_, hgc.trans (of_run_ret_val hu2 h).2⟩
  show Devm.output r = _
  rw [(of_run_ret_val hu2 h).1,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    Mem.Reads.read (hm3 ▸ hrd2) 0 32,
    show (32 : Nat) = w.toBytes.length from
      (B256.length_toBytes w).symm,
    Bytes.sliceD_writeAt]

/-- Fixed-width deployment parameters use `pushDeployWord` so compiler shape
is independent of the parameter bytes, but their one-word return behavior is
the same as an ordinary constant getter. -/
lemma of_returnDeployWord {fs : List Func} {sevm : Sevm} {s r : Devm}
    {w : B256} {img : Bytes} {xs}
    (hp : xs <<+ s.stack)
    (h_wf : Mem.Wf s.memory)
    (h_reads : Mem.Reads s.memory img)
    (h : Func.Run fs sevm s (returnDeployWord w) r) :
    ReturnsWord w r ∧ Devm.getCode s = Devm.getCode r := by
  simp only [returnDeployWord] at h
  rcases of_run_next h with ⟨s1, hpush, h⟩
  unfold pushDeployWord at hpush
  have hp1 : w :: xs <<+ s1.stack := by
    rw [← B256.toB256_toBytes w]
    exact prefix_of_push (of_run_push hpush) hp
  have hm : s.memory = s1.memory :=
    Ninst.Hinv.inv (f := Devm.memory) hpush
  have hwf1 : Mem.Wf s1.memory := hm ▸ h_wf
  have hrd1 : Mem.Reads s1.memory img := hm ▸ h_reads
  obtain ⟨hout, hcode⟩ := of_storeReturnWord hp1 hwf1 hrd1 h
  exact ⟨hout,
    (Ninst.Hinv.inv (f := Devm.getCode) hpush).trans hcode⟩

end Weth10

end Blanc
