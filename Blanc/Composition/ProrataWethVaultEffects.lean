import Blanc.Composition.ProrataWethVaultBoundary
import Blanc.Ladder
import Blanc.Solvent
import Blanc.WethLive

/-!
# Exact effects of the PRORATA vault's WETH children

This module turns the retained occurrence proved at the call boundary back
into a gas-exact run of the inherited WETH program.  The later entrypoint
effects therefore start from actual WETH source execution, never from a token
behaviour premise supplied by a caller.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

/-- A successful retained child, projected to the exact WETH run and the
storage row that the parent world observes before and after it. -/
def SuccessfulWethProgramRun
    (caller : Adr) (calldata output : Bytes) (initial final : Stor) : Prop :=
  ∃ (childSevm : Sevm) (childPre rawPost : Devm),
    childSevm.currentTarget = wethAccount ∧
    childSevm.codeAddress = some wethAccount ∧
    childSevm.caller = caller ∧
    childSevm.value = 0 ∧
    childSevm.data = calldata ∧
    childPre.stack = [] ∧
    childPre.memory = Mem.empty ∧
    childPre.state.getStor wethAccount = initial ∧
    Prog.RunCompiled childSevm childPre Blanc.weth rawPost ∧
    rawPost.error = none ∧
    final = rawPost.state.getStor wethAccount ∧
    rawPost.output = output

private theorem weth_pcFree : Prog.pcFree Blanc.weth = true := by
  decide +kernel

/-- Every successful execution of the inherited `returnTrue` source fragment
returns exactly one canonical ABI word, without a memory well-formedness
premise. -/
private theorem returnTrue_output
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre returnTrue post) :
    AbiReturnsTrue post := by
  simp only [returnTrue] at run
  obtain ⟨afterPush, pushOne, tail⟩ := of_run_next run
  have onePrefix : (1 : B256) :: [] <<+ afterPush.stack :=
    prefix_of_push (of_run_pushB256 pushOne) nil_pref
  exact (returnsWord_of_storeReturn onePrefix tail).1

/-- All three successful branches of WETH's allowance update terminate in
the same exact `returnTrue` fragment: caller-is-owner, infinite allowance, and
finite decrement. -/
private theorem updateAllowance_output
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre updateAllowance post) :
    AbiReturnsTrue post := by
  rcases of_run_prepend [caller, dup 2, eq] _ run with ⟨_, _, run⟩
  rcases of_run_branch run with
    ⟨_, _, run⟩ | ⟨_, _, _, _, _, _, callerReturn⟩
  · rcases of_run_prepend (swap 0 :: mstoreAt 0) _ run with
      ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_prepend (mstoreAt 1) _ run with ⟨_, _, run⟩
    rcases of_run_prepend (pushList [64, 0]) _ run with ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_prepend checkAddress _ run with ⟨_, _, run⟩
    rcases of_run_branch_rev run with ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_prepend isMax _ run with ⟨_, _, run⟩
    rcases of_run_branch run with
      ⟨_, _, finiteRun⟩ | ⟨_, _, _, _, _, _, maxReturn⟩
    · rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_branch_rev finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, trueRun⟩
      exact returnTrue_output trueRun
    · exact returnTrue_output maxReturn
  · exact returnTrue_output callerReturn

/-! ## Exact selector entry -/

/-- The shared nonpayable wrapper is silent in the log and output frames in
addition to preserving the state and memory exported by the neutral inversion
theorem. -/
private theorem run_body_of_run_nonpayable_frame_logs
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧
      s.memory = mid.memory ∧ s.logs = mid.logs ∧
      s.output = mid.output ∧ Func.Run fs sevm mid body r := by
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
    ⟨s2, hpop, hrev⟩ |
    ⟨w, s2, s3, hnz, hpop, hburn, hbody⟩
  · exact absurd hrev not_run_rev
  · have hpop' := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop'
    rw [hpop'] at hpflag
    have hw : (sevm.value =? 0) = w :=
      pref_head_unique hpflag (pref_append [w] s2.stack)
    have hflag : (sevm.value =? 0) ≠ 0 := by
      rw [hw]
      exact hnz
    have hvalue : sevm.value = 0 := by
      by_cases hvalue : sevm.value = 0
      · exact hvalue
      · simp [B256.eqCheck, hvalue] at hflag
    refine ⟨s3, hvalue, ?_, ?_, ?_, ?_, hbody⟩
    · exact (Line.of_inv Devm.state (by line_inv) hline).trans
        (hpop.state.trans hburn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
        (hpop.memory.trans hburn.memory)
    · exact ((of_run_callvalue hcv).logs.trans
        (Ninst.Hinv.inv (f := Devm.logs) hiz)).trans
          (hpop.logs.trans hburn.logs)
    · exact ((of_run_callvalue hcv).output.trans
        (Ninst.Hinv.inv (f := Devm.output) hiz)).trans
          (hpop.output.trans hburn.output)

/-- A successful exact compiled WETH run with a recognized selector reaches
that selector's actual nonpayable body.  This is the composition-owned WETH
specialization of Blanc's neutral sorted-dispatch and wrapper seams. -/
private theorem runCompiled_enters_wethNonpayable
    {sevm : Sevm} {pre post : Devm} {sig : B256} {body : Func}
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (hselector : Sevm.selector sevm = sig)
    (hmember : (sig, nonpayable body) ∈ Blanc.wethFuncs) :
    ∃ mid,
      sevm.value = 0 ∧
      pre.state = mid.state ∧
      pre.memory = mid.memory ∧
      pre.logs = mid.logs ∧
      pre.output = mid.output ∧
      Func.Run (Blanc.weth.main :: Blanc.weth.aux) sevm mid body post := by
  have sourceRun : Prog.Run sevm pre Blanc.weth post :=
    Prog.Run.of_runCompiled run
  dsimp only [Prog.Run] at sourceRun
  cases sourceRun
  rename (_ = _) => rootLookup
  rename (Func.Run _ _ _ _ _) => rootRun
  rename (Devm.Burn _ _) => rootBurn
  rename Devm => rootPre
  cases rootLookup
  have mainRun :
      Func.Run (Blanc.weth.main :: Blanc.weth.aux) sevm rootPre
        (fsig +++ dispatchWith 1 Blanc.wethTree) post := by
    simpa only [Blanc.weth, Func.mainWith] using rootRun
  refine run_prepend_elim _ fsig ?_ mainRun
  intro dispatchPre hfsig hdispatch
  have selectorPrefix : sig :: [] <<+ dispatchPre.stack := by
    rw [← hselector]
    exact prefix_of_fsig nil_pref hfsig
  rcases reach_of_dispatchWith_logs Blanc.wethFuncs_sorted hmember
      selectorPrefix hdispatch with
    ⟨selectedPre, -, dispatchState, dispatchMemory, dispatchLogs,
      dispatchOutput, selectedRun⟩
  rcases run_body_of_run_nonpayable_frame_logs selectedRun with
    ⟨mid, hvalue, wrapperState, wrapperMemory, wrapperLogs,
      wrapperOutput, bodyRun⟩
  refine ⟨mid, hvalue, ?_, ?_, ?_, ?_, bodyRun⟩
  · exact rootBurn.state.trans
      ((Line.of_inv Devm.state (by line_inv) hfsig).trans
        (dispatchState.trans wrapperState))
  · exact rootBurn.memory.trans
      ((Line.of_inv Devm.memory (by line_inv) hfsig).trans
        (dispatchMemory.trans wrapperMemory))
  · exact rootBurn.logs.trans
      ((fsig_logs hfsig).trans (dispatchLogs.trans wrapperLogs))
  · exact rootBurn.output.trans
      ((fsig_output hfsig).trans (dispatchOutput.trans wrapperOutput))

/-- Exact read-only effect of the inherited WETH `balanceOf` body. -/
private theorem balanceOfBody_effect
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    (run : Func.Run fs sevm s balanceOf r) :
    ReturnsWord
        (Devm.getStorVal s sevm.currentTarget (Sevm.argWord sevm 0)) r ∧
      Devm.getStor s = Devm.getStor r := by
  have storage : Devm.getStor s = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold balanceOf
      func_inv) run
  simp only [balanceOf] at run
  rcases of_run_prepend (arg 0) _ run with ⟨s1, harg, run1⟩
  have hp1 : Sevm.argWord sevm 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref harg
  rcases of_run_next run1 with ⟨s2, hsload, run2⟩
  rcases prefix_of_sload hsload hp1 with ⟨balance, hp2, hbalance⟩
  obtain ⟨output, -⟩ := returnsWord_of_storeReturn hp2 run2
  rw [hbalance] at output
  have entryStorage : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) harg
  change ReturnsWord
    ((Devm.getStor s1 sevm.currentTarget).get (Sevm.argWord sevm 0)) r
      at output
  rw [← entryStorage] at output
  exact ⟨output, storage⟩

/-! ## Exact ordinary-transfer effect -/

/-- The destination guard retains the exact first ABI word rather than an
existential calldata word. -/
private theorem transferTestDst_exact
    {sevm : Sevm} {s s' : Devm} :
    Line.Run sevm s transferTestDst s' →
    ∃ invalid,
      ([invalid, Sevm.argWord sevm 0] <<+ s'.stack) ∧
      (invalid = 0 ↔ ValidAdr (Sevm.argWord sevm 0)) := by
  simp only [transferTestDst]
  line_execute_with (arg 0)
  have hp1 : Sevm.argWord sevm 0 :: [] <<+ s₁.stack :=
    prefix_of_arg nil_pref h₁
  clear h₁
  line_execute 1
  have hp2 : [Sevm.argWord sevm 0, Sevm.argWord sevm 0] <<+
      s₂.stack := by
    generalize_line_prefix
  clear hp1 h₂
  intro h
  rcases of_check_non_address hp2 h with ⟨invalid, hp, valid⟩
  exact ⟨invalid, hp, valid⟩

/-- The balance guard retains the exact caller and amount words. -/
private theorem transferTestLt_exact
    {sevm : Sevm} {s s' : Devm} {dst : B256}
    (hstack : [dst] <<+ s.stack) :
    Line.Run sevm s transferTestLt s' →
    ∃ less,
      ([less, sevm.caller.toB256,
          Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 -
            Sevm.argWord sevm 1,
          Sevm.argWord sevm 1, dst] <<+ s'.stack) ∧
      (less = 0 ↔
        Sevm.argWord sevm 1 ≤
          Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256) := by
  simp only [transferTestLt]
  line_execute_with (arg 1)
  have hp1 : Sevm.argWord sevm 1 :: dst :: [] <<+ s₁.stack :=
    prefix_of_arg hstack h₁
  clear h₁
  line_execute 2
  have hp2 : [sevm.caller.toB256, sevm.caller.toB256,
      Sevm.argWord sevm 1, dst] <<+ s₂.stack := by
    generalize_line_prefix
  clear h₂
  line_execute 1
  rcases prefix_of_sload (of_run_singleton h₃) hp2 with
    ⟨balance, hp3, hbalance⟩
  have storage23 : Devm.getStor s₂ = Devm.getStor s₃ :=
    Line.of_inv Devm.getStor (by line_inv) h₃
  clear h₃
  intro h₄
  have hp4 : [balance <? Sevm.argWord sevm 1, sevm.caller.toB256,
      balance - Sevm.argWord sevm 1, Sevm.argWord sevm 1, dst] <<+
        s'.stack := by
    generalize_line_prefix
  have storage34 : Devm.getStor s₃ = Devm.getStor s' :=
    Line.of_inv Devm.getStor (by line_inv) h₄
  have balanceEq : balance =
      Devm.getStorVal s' sevm.currentTarget sevm.caller.toB256 := by
    rw [hbalance]
    show (Devm.getStor s₂ _).get _ = (Devm.getStor s' _).get _
    rw [storage23, storage34]
  refine ⟨balance <? Sevm.argWord sevm 1, ?_, ?_⟩
  · rw [← balanceEq]
    exact hp4
  · rw [← balanceEq, B256.ltCheck,
      Ne.ite_eq_right_iff B256.zero_ne_one.symm, B256.not_lt]

/-- Exact storage effect of the inherited WETH `transfer` body.  The debit is
from the actual frame caller, the amount is ABI word one, and the credit is to
ABI word zero. -/
private theorem transferBody_exactEffect
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    (run : Func.Run fs sevm s transfer r) :
    Transfer (Stor.rest (Devm.getStor s sevm.currentTarget)) sevm.caller
        (Sevm.argWord sevm 1) (Sevm.argWord sevm 0).toAdr
        (Stor.rest (Devm.getStor r sevm.currentTarget)) ∧
      Stor.AgreeOffAdr (Devm.getStor s sevm.currentTarget)
        (Devm.getStor r sevm.currentTarget) ∧
      AbiReturnsTrue r := by
  simp only [transfer] at run
  rcases of_run_prepend transferTestDst _ run with ⟨s1, h1, run⟩
  rcases transferTestDst_exact h1 with ⟨invalid, hp1, valid⟩
  have storage1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) h1
  clear h1
  rcases of_run_branch_rev run with ⟨s2, pop2, run⟩
  have popStack2 := pop2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at popStack2
  rw [popStack2] at hp1
  have dstValid : ValidAdr (Sevm.argWord sevm 0) :=
    valid.mp (pref_head_unique hp1 (pref_append [0] s2.stack))
  rw [pref_head_unique hp1 (pref_append [0] s2.stack)] at hp1
  have hp2 : [Sevm.argWord sevm 0] <<+ s2.stack :=
    cons_pref_cons_inv hp1
  have storage2 : Devm.getStor s = Devm.getStor s2 :=
    storage1.trans (funext (fun a => (Devm.PopBurn.getStor pop2 a).symm))
  clear hp1 popStack2 pop2 valid
  rcases of_run_prepend transferTestLt _ run with ⟨s3, h3, run⟩
  rcases transferTestLt_exact hp2 h3 with ⟨less, hp3, covered⟩
  have storage3 : Devm.getStor s = Devm.getStor s3 :=
    storage2.trans (Line.of_inv Devm.getStor (by line_inv) h3)
  clear h3 hp2
  rcases of_run_branch_rev run with ⟨s4, pop4, run⟩
  have popStack4 := pop4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at popStack4
  rw [popStack4] at hp3
  have lessZero : less = 0 :=
    pref_head_unique hp3 (pref_append [0] s4.stack)
  have amountCovered : Sevm.argWord sevm 1 ≤
      Devm.getStorVal s3 sevm.currentTarget sevm.caller.toB256 :=
    covered.mp lessZero
  rw [lessZero] at hp3
  have hp4 : [sevm.caller.toB256,
      Devm.getStorVal s3 sevm.currentTarget sevm.caller.toB256 -
        Sevm.argWord sevm 1,
      Sevm.argWord sevm 1, Sevm.argWord sevm 0] <<+ s4.stack :=
    cons_pref_cons_inv hp3
  have storage4 : Devm.getStor s = Devm.getStor s4 :=
    storage3.trans (funext (fun a => (Devm.PopBurn.getStor pop4 a).symm))
  clear hp3 popStack4 pop4 covered lessZero
  simp only [transferCore] at run
  rcases of_run_next run with ⟨s5, store5, run⟩
  have callerSet : Devm.getStor s5 sevm.currentTarget =
      (Devm.getStor s4 sevm.currentTarget).set sevm.caller.toB256
        (Devm.getStorVal s3 sevm.currentTarget sevm.caller.toB256 -
          Sevm.argWord sevm 1) :=
    sstore_getStor_set store5 hp4
  have hp5 : [Sevm.argWord sevm 1, Sevm.argWord sevm 0] <<+ s5.stack :=
    prefix_of_sstore store5 hp4
  clear hp4
  rcases of_run_prepend incrWbal _ run with ⟨s6, h6, run⟩
  rcases incrAt_of_incrWbal dstValid h6 hp5 with
    ⟨destinationIncrease, offAddress6⟩
  obtain ⟨_, _, trueRun⟩ := of_run_prepend logTransfer returnTrue run
  have outputTrue := returnTrue_output trueRun
  have tailStorage : Devm.getStor s6 sevm.currentTarget =
      Devm.getStor r sevm.currentTarget :=
    congrFun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run)
      sevm.currentTarget
  have exactTransfer :
      Transfer (Stor.rest (Devm.getStor s sevm.currentTarget))
        sevm.caller.toB256.toAdr (Sevm.argWord sevm 1)
        (Sevm.argWord sevm 0).toAdr
        (Stor.rest (Devm.getStor r sevm.currentTarget)) := by
    refine ⟨?_, Stor.rest (Devm.getStor s5 sevm.currentTarget), ?_, ?_⟩
    · show Sevm.argWord sevm 1 ≤
          (Stor.rest (Devm.getStor s sevm.currentTarget))
            sevm.caller.toB256.toAdr
      simp only [Stor.rest, Function.comp_apply]
      rw [toB256_toAdr (validAdr_toB256 sevm.caller),
        congrFun storage3 sevm.currentTarget]
      exact amountCovered
    · intro a
      constructor
      · intro same
        subst same
        simp only [Stor.rest, Function.comp_apply]
        rw [toB256_toAdr (validAdr_toB256 sevm.caller), callerSet,
          Stor.get_set_self, congrFun storage3 sevm.currentTarget]
        rfl
      · intro different
        simp only [Stor.rest, Function.comp_apply]
        rw [callerSet]
        have keyDifferent : a.toB256 ≠ sevm.caller.toB256 := by
          intro same
          apply different
          rw [← toAdr_toB256 a, same]
        rw [Stor.get_set_ne _ keyDifferent.symm,
          congrFun storage4 sevm.currentTarget]
    · rw [← tailStorage]
      exact destinationIncrease
  refine ⟨?_, ?_, outputTrue⟩
  · simpa only [toAdr_toB256] using exactTransfer
  · refine Stor.AgreeOffAdr.trans
      (Stor.AgreeOffAdr.of_eq (congrFun storage4 sevm.currentTarget)) ?_
    refine Stor.AgreeOffAdr.trans ?_
      (offAddress6.trans (Stor.AgreeOffAdr.of_eq tailStorage))
    rw [callerSet]
    exact Stor.AgreeOffAdr.set (validAdr_toB256 sevm.caller)

/-- Exact balance-row movement of the inherited WETH `transferFrom` body.
Unlike the older existential projection, the source, destination, and amount
remain the three actual ABI words throughout the proof. -/
private theorem transferFromBody_exactEffect
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    (run : Func.Run fs sevm s transferFrom r) :
    Transfer (Stor.rest (Devm.getStor s sevm.currentTarget))
      (Sevm.argWord sevm 0).toAdr (Sevm.argWord sevm 2)
      (Sevm.argWord sevm 1).toAdr
      (Stor.rest (Devm.getStor r sevm.currentTarget)) ∧
    AbiReturnsTrue r := by
  let src := Sevm.argWord sevm 0
  let dst := Sevm.argWord sevm 1
  let wad := Sevm.argWord sevm 2
  simp only [transferFrom] at run
  rcases of_run_prepend (arg 0) _ run with ⟨a1, h1, run⟩
  have hs1 : src :: [] <<+ a1.stack := by
    simpa only [src] using prefix_of_arg nil_pref h1
  have storage : Devm.getStor s = Devm.getStor a1 :=
    Line.of_inv Devm.getStor (by line_inv) h1
  clear h1
  rcases of_run_next run with ⟨a2, r2, run⟩
  rcases of_run_dup r2 with ⟨y, hy2, pb2⟩
  have ySrc : y = src := by
    have getSrc : a1.stack[(0 : Fin 16).val]? = some src :=
      Stack.nth_getElem (Stack.Nth.head src []) hs1
    rw [getSrc] at hy2
    injection hy2 with hy2
    exact hy2.symm
  subst y
  have hs2 : [src, src] <<+ a2.stack := prefix_of_push pb2 hs1
  have storage := storage.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  clear r2 pb2 hs1
  rcases of_run_prepend checkNonAddress _ run with ⟨a3, h3, run⟩
  rcases of_check_non_address hs2 h3 with ⟨invalidSrc, hs3, srcIff⟩
  have storage := storage.trans (Line.of_inv Devm.getStor (by line_inv) h3)
  clear h3 hs2
  rcases of_run_branch_rev run with ⟨a4, pop4, run⟩
  have popStack4 := pop4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at popStack4
  rw [popStack4] at hs3
  have srcValid : ValidAdr src :=
    srcIff.mp (pref_head_unique hs3 (pref_append [0] a4.stack))
  rw [pref_head_unique hs3 (pref_append [0] a4.stack)] at hs3
  have hs4 : [src] <<+ a4.stack := cons_pref_cons_inv hs3
  have storage := storage.trans
    (funext (fun a => (Devm.PopBurn.getStor pop4 a).symm))
  clear hs3 popStack4 pop4 srcIff
  rcases of_run_prepend (arg 2) _ run with ⟨a5, h5, run⟩
  have hs5 : wad :: src :: [] <<+ a5.stack := by
    simpa only [wad] using prefix_of_arg hs4 h5
  have storage := storage.trans (Line.of_inv Devm.getStor (by line_inv) h5)
  clear h5 hs4
  rcases of_run_next run with ⟨a6, r6, run⟩
  rcases of_run_dup r6 with ⟨y, hy6, pb6⟩
  have yWad : y = wad := by
    have getWad : a5.stack[(0 : Fin 16).val]? = some wad :=
      Stack.nth_getElem (Stack.Nth.head wad [src]) hs5
    rw [getWad] at hy6
    injection hy6 with hy6
    exact hy6.symm
  subst y
  have hs6 : [wad, wad, src] <<+ a6.stack := prefix_of_push pb6 hs5
  have storage := storage.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r6 Line.Run.nil))
  clear r6 pb6 hs5
  rcases of_run_next run with ⟨a7, r7, run⟩
  rcases of_run_dup r7 with ⟨y, hy7, pb7⟩
  have ySrc : y = src := by
    have getSrc : a6.stack[(2 : Fin 16).val]? = some src :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 src wad [wad, src]
          (Stack.Nth.tail 0 src wad [src] (Stack.Nth.head src []))) hs6
    rw [getSrc] at hy7
    injection hy7 with hy7
    exact hy7.symm
  subst y
  have hs7 : [src, wad, wad, src] <<+ a7.stack :=
    prefix_of_push pb7 hs6
  have storage7 : Devm.getStor s = Devm.getStor a7 :=
    storage.trans
      (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  clear r7 pb7 hs6
  rcases of_run_next run with ⟨a8, r8, run⟩
  rcases prefix_of_sload r8 hs7 with ⟨sourceBalance, hs8, sourceBalanceEq⟩
  have storage := storage7.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r8 Line.Run.nil))
  clear r8 hs7
  rcases of_run_next run with ⟨a9, r9, run⟩
  rcases of_run_dup r9 with ⟨y, hy9, pb9⟩
  have yWad : y = wad := by
    have getWad : a8.stack[(1 : Fin 16).val]? = some wad :=
      Stack.nth_getElem
        (Stack.Nth.tail 0 wad sourceBalance [wad, wad, src]
          (Stack.Nth.head wad [wad, src])) hs8
    rw [getWad] at hy9
    injection hy9 with hy9
    exact hy9.symm
  subst y
  have hs9 : [wad, sourceBalance, wad, wad, src] <<+ a9.stack :=
    prefix_of_push pb9 hs8
  have storage := storage.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  clear r9 pb9 hs8
  rcases of_run_next run with ⟨a10, r10, run⟩
  rcases of_run_dup r10 with ⟨y, hy10, pb10⟩
  have yBalance : y = sourceBalance := by
    have getBalance : a9.stack[(1 : Fin 16).val]? = some sourceBalance :=
      Stack.nth_getElem
        (Stack.Nth.tail 0 sourceBalance wad [sourceBalance, wad, wad, src]
          (Stack.Nth.head sourceBalance [wad, wad, src])) hs9
    rw [getBalance] at hy10
    injection hy10 with hy10
    exact hy10.symm
  subst y
  have hs10 : [sourceBalance, wad, sourceBalance, wad, wad, src] <<+
      a10.stack := prefix_of_push pb10 hs9
  have storage := storage.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  clear r10 pb10 hs9
  rcases of_run_next run with ⟨a11, r11, run⟩
  have hs11 : (sourceBalance <? wad) ::
      [sourceBalance, wad, wad, src] <<+ a11.stack :=
    prefix_of_lt r11 hs10
  have storage := storage.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  clear r11 hs10
  rcases of_run_branch_rev run with ⟨a12, pop12, run⟩
  have popStack12 := pop12.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at popStack12
  rw [popStack12] at hs11
  have lessZero : (sourceBalance <? wad) = 0 :=
    pref_head_unique hs11 (pref_append [0] a12.stack)
  have covered : wad ≤ sourceBalance := by
    rw [← B256.not_lt]
    intro less
    rw [B256.ltCheck, if_pos less] at lessZero
    exact B256.zero_ne_one lessZero.symm
  rw [lessZero] at hs11
  have hs12 : [sourceBalance, wad, wad, src] <<+ a12.stack :=
    cons_pref_cons_inv hs11
  have storage12 : Devm.getStor s = Devm.getStor a12 :=
    storage.trans (funext (fun a => (Devm.PopBurn.getStor pop12 a).symm))
  clear hs11 popStack12 pop12 lessZero
  rcases of_run_prepend transferFromUpdateSbal _ run with ⟨a13, h13, run⟩
  have sourceBalanceEq' : sourceBalance =
      (Devm.getStor a12 sevm.currentTarget).get src := by
    rw [sourceBalanceEq]
    show (Devm.getStor a7 sevm.currentTarget).get src = _
    rw [congrFun (storage7.symm.trans storage12) sevm.currentTarget]
  rcases of_transferFromUpdateSbal srcValid sourceBalanceEq' covered hs12 h13
      with ⟨sourceDecrease, covered', -⟩
  have hs13 : [wad, src] <<+ a13.stack := by
    generalize_line_prefix
  clear h13 hs12 sourceBalanceEq sourceBalanceEq' covered
  rcases of_run_prepend (arg 1) _ run with ⟨a14, h14, run⟩
  have hs14 : dst :: wad :: src :: [] <<+ a14.stack := by
    simpa only [dst] using prefix_of_arg hs13 h14
  have storage' : Devm.getStor a13 = Devm.getStor a14 :=
    Line.of_inv Devm.getStor (by line_inv) h14
  clear h14 hs13
  rcases of_run_next run with ⟨a15, r15, run⟩
  rcases of_run_dup r15 with ⟨y, hy15, pb15⟩
  have yDst : y = dst := by
    have getDst : a14.stack[(0 : Fin 16).val]? = some dst :=
      Stack.nth_getElem (Stack.Nth.head dst [wad, src]) hs14
    rw [getDst] at hy15
    injection hy15 with hy15
    exact hy15.symm
  subst y
  have hs15 : [dst, dst, wad, src] <<+ a15.stack :=
    prefix_of_push pb15 hs14
  have storage' := storage'.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  clear r15 pb15 hs14
  rcases of_run_prepend checkNonAddress _ run with ⟨a16, h16, run⟩
  rcases of_check_non_address hs15 h16 with ⟨invalidDst, hs16, dstIff⟩
  have storage' := storage'.trans
    (Line.of_inv Devm.getStor (by line_inv) h16)
  clear h16 hs15
  rcases of_run_branch_rev run with ⟨a17, pop17, run⟩
  have popStack17 := pop17.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at popStack17
  rw [popStack17] at hs16
  have dstValid : ValidAdr dst :=
    dstIff.mp (pref_head_unique hs16 (pref_append [0] a17.stack))
  rw [pref_head_unique hs16 (pref_append [0] a17.stack)] at hs16
  have hs17 : [dst, wad, src] <<+ a17.stack := cons_pref_cons_inv hs16
  have storage' := storage'.trans
    (funext (fun a => (Devm.PopBurn.getStor pop17 a).symm))
  clear hs16 popStack17 pop17 dstIff
  rcases of_run_next run with ⟨a18, r18, run⟩
  rcases of_run_dup r18 with ⟨y, hy18, pb18⟩
  have yDst : y = dst := by
    have getDst : a17.stack[(0 : Fin 16).val]? = some dst :=
      Stack.nth_getElem (Stack.Nth.head dst [wad, src]) hs17
    rw [getDst] at hy18
    injection hy18 with hy18
    exact hy18.symm
  subst y
  have hs18 : [dst, dst, wad, src] <<+ a18.stack :=
    prefix_of_push pb18 hs17
  have storage' := storage'.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  clear r18 pb18 hs17
  rcases of_run_next run with ⟨a19, r19, run⟩
  rcases of_run_dup r19 with ⟨y, hy19, pb19⟩
  have yWad : y = wad := by
    have getWad : a18.stack[(2 : Fin 16).val]? = some wad :=
      Stack.nth_getElem
        (Stack.Nth.tail 1 wad dst [dst, wad, src]
          (Stack.Nth.tail 0 wad dst [wad, src]
            (Stack.Nth.head wad [src]))) hs18
    rw [getWad] at hy19
    injection hy19 with hy19
    exact hy19.symm
  subst y
  have hs19 : [wad, dst, dst, wad, src] <<+ a19.stack :=
    prefix_of_push pb19 hs18
  have storage19 : Devm.getStor a13 = Devm.getStor a19 :=
    storage'.trans
      (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  clear r19 pb19 hs18
  rcases of_run_prepend incrWbal _ run with ⟨a20, h20, run⟩
  have destinationIncrease :
      Increase dst.toAdr wad (Stor.rest (Devm.getStor a19 sevm.currentTarget))
        (Stor.rest (Devm.getStor a20 sevm.currentTarget)) :=
    (incrAt_of_incrWbal dstValid h20
      (pref_trans ⟨[dst, wad, src], rfl⟩ hs19)).left
  have hs20 : [dst, wad, src] <<+ a20.stack := by
    rcases of_run_append [dup 1, sload, add, swap 0] h20 with
      ⟨am, ham, hend⟩
    rcases Line.of_run_cons ham with ⟨b1, rd1, ham⟩
    rcases Line.of_run_cons ham with ⟨b2, rsl, ham⟩
    rcases Line.of_run_cons ham with ⟨b3, radd, ham⟩
    rcases Line.of_run_cons ham with ⟨b4, rsw, ham⟩
    cases ham
    rcases Line.of_run_cons hend with ⟨a20', store20, hend⟩
    cases hend
    rcases of_run_dup rd1 with ⟨y, hy, pushDup⟩
    have yDst : y = dst := by
      have getDst : a19.stack[(1 : Fin 16).val]? = some dst :=
        Stack.nth_getElem
          (Stack.Nth.tail 0 dst wad [dst, dst, wad, src]
            (Stack.Nth.head dst [dst, wad, src])) hs19
      rw [getDst] at hy
      injection hy with hy
      exact hy.symm
    subst y
    have hb1 : [dst, wad, dst, dst, wad, src] <<+ b1.stack :=
      prefix_of_push pushDup hs19
    rcases prefix_of_sload rsl hb1 with ⟨destinationBalance, hb2, -⟩
    have hb3 : (destinationBalance + wad) ::
        [dst, dst, wad, src] <<+ b3.stack := prefix_of_add radd hb2
    have swapShape : Stack.Swap (0 : Fin 16).val
        [destinationBalance + wad, dst, dst, wad, src]
        [dst, destinationBalance + wad, dst, wad, src] :=
      Stack.swapCore_zero
    have hb4 : [dst, destinationBalance + wad, dst, wad, src] <<+
        am.stack := Stack.prefix_of_swap swapShape (of_run_swap rsw) hb3
    exact prefix_of_sstore store20 hb4
  clear h20 hs19
  rcases of_run_prepend transferFromLog _ run with ⟨a21, h21, run⟩
  have hs21 : [wad, src] <<+ a21.stack := by
    generalize_line_prefix
  have logStorage : Devm.getStor a20 = Devm.getStor a21 :=
    Line.of_inv Devm.getStor (by line_inv) h21
  clear h21
  have allowanceRest :
      Stor.rest (Devm.getStor a21 sevm.currentTarget) =
        Stor.rest (Devm.getStor r sevm.currentTarget) :=
    updateAllowance_preserves_stor_rest hs21 run
  have outputTrue := updateAllowance_output run
  have effect :
      Transfer (Stor.rest (Devm.getStor s sevm.currentTarget))
        src.toAdr wad dst.toAdr
        (Stor.rest (Devm.getStor r sevm.currentTarget)) := by
    refine ⟨?_, Stor.rest (Devm.getStor a13 sevm.currentTarget), ?_, ?_⟩
    · rw [congrFun storage12 sevm.currentTarget]
      exact covered'
    · rw [congrFun storage12 sevm.currentTarget]
      exact sourceDecrease
    · rw [congrFun storage19 sevm.currentTarget, ← allowanceRest,
        ← congrFun logStorage sevm.currentTarget]
      exact destinationIncrease
  exact ⟨by simpa only [src, dst, wad] using effect, outputTrue⟩

/-- Recover the successful compiled WETH run from the actual retained child
slot and the parent's raw status/returndata refinement. -/
theorem ExactWethChildSuccess.programRun
    {parentSevm : Sevm} {parentPre parentPost : Devm}
    {instruction : Ninst} {calldata output : Bytes} {static : Bool}
    (success : ExactWethChildSuccess parentSevm parentPre parentPost
      instruction calldata output static) :
    SuccessfulWethProgramRun parentSevm.currentTarget calldata output
      (parentPre.state.getStor wethAccount)
      (parentPost.state.getStor wethAccount) := by
  unfold ExactWethChildSuccess ExactWethChildExecution at success
  rcases success with ⟨msg, xl, child, pc, nextPc, resume,
    target, executes, childWorld, childRules, spawn, filled, process,
    stepRun, postState, postReturnData, statusTail, statusEq, childClean⟩
  rcases executes with ⟨uses, childEvm, raw, slotEq, childExec⟩
  subst xl
  obtain ⟨errorNone, childOutput⟩ := childClean
  have clean : child.error.isSome = false := by simp [errorNone]
  obtain ⟨rawPost, rawEq, rawError, settledState, settledOutput⟩ :=
    Blanc.MessageExecution.processMessage_clean_rawPost process clean
  subst raw
  obtain ⟨pcZero, codeEq, currentTarget, codeAddress, dataEq, -, storageEq,
    -⟩ := Blanc.MessageExecution.processMessage_entry_facts
      wethAccount process
  have stackEq := Blanc.MessageExecution.processMessage_entry_stack process
  have memoryEq := Blanc.MessageExecution.processMessage_entry_memory process
  have enter := (RunFrame.some_inv process).1
  rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
  have callerEq := congrArg (fun evm : Evm => evm.sta.caller) evmEq
  have valueEq := congrArg (fun evm : Evm => evm.sta.value) evmEq
  dsimp [Jaune.Frame.ofCall, initEvm, initSevm, initDevm, Msg.withBenv]
    at callerEq valueEq
  have exactCode : some childEvm.sta.code.toList = Prog.compile Blanc.weth := by
    rw [codeEq]
    exact uses
  obtain ⟨run⟩ := childExec
  rw [pcZero] at run
  have compiled : Prog.RunCompiled childEvm.sta childEvm.dyna Blanc.weth
      rawPost :=
    Prog.runCompiled_of_exec childEvm.sta childEvm.dyna Blanc.weth rawPost
      weth_pcFree run exactCode
  refine ⟨childEvm.sta, childEvm.dyna, rawPost, ?_, ?_, ?_, ?_, ?_,
    stackEq, memoryEq, ?_, compiled, rawError, ?_, ?_⟩
  · exact currentTarget.trans target.currentTarget
  · exact codeAddress.trans target.codeAddress
  · exact callerEq.trans target.callerAddress
  · exact valueEq.trans target.valueZero
  · exact dataEq.trans target.data
  · rw [storageEq, childWorld]
  · rw [postState, settledState]
  · exact settledOutput.symm.trans childOutput

/-! ## Asset-query effect -/

/-- The exact successful WETH child for `balanceOf(vault)` reads precisely the
configured vault's WETH balance, changes no WETH storage, and returns that
word.  The caller is the vault itself by the first argument of
`SuccessfulWethProgramRun`; neither the query effect nor its program
occurrence is supplied as a premise. -/
theorem SuccessfulWethProgramRun.balanceOf_effect
    {vault : Adr} {output : Bytes} {initial final : Stor}
    (run : SuccessfulWethProgramRun vault (balanceOfCalldata vault)
      output initial final) :
    final = initial ∧
      output = (initial.get vault.toB256).toBytes := by
  rcases run with ⟨childSevm, childPre, rawPost,
    currentTarget, codeAddress, caller, valueZero, dataEq, stackEmpty,
    memoryEmpty, initialEq, compiled, rawError, finalEq, outputEq⟩
  obtain ⟨selectorEq, vaultArg⟩ := balanceOfCalldata_facts dataEq
  have member :
      (selector "balanceOf" [.address], nonpayable balanceOf) ∈
        Blanc.wethFuncs := by
    simp [Blanc.wethFuncs]
  obtain ⟨bodyPre, -, entryState, entryMemory, entryLogs,
      entryOutput, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable compiled selectorEq member
  obtain ⟨bodyOutput, bodyStorage⟩ := balanceOfBody_effect bodyRun
  have entryStor : Devm.getStor childPre wethAccount =
      Devm.getStor bodyPre wethAccount :=
    getStor_eq_of_state_eq entryState wethAccount
  have bodyInitial : Devm.getStor bodyPre wethAccount = initial :=
    entryStor.symm.trans initialEq
  have finalInitial : final = initial :=
    finalEq.trans
      ((congrFun bodyStorage wethAccount).symm.trans bodyInitial)
  change rawPost.output =
      ((Devm.getStor bodyPre childSevm.currentTarget).get
        (Sevm.dataWord childSevm 4)).toBytes at bodyOutput
  rw [currentTarget, vaultArg, bodyInitial] at bodyOutput
  exact ⟨finalInitial, outputEq.symm.trans bodyOutput⟩

/-! ## Outbound transfer effect -/

/-- An exact successful WETH `transfer(receiver,assets)` child debits the vault
caller and credits precisely the canonical receiver.  Both the storage effect
and canonical-true output are derived from the selected WETH body, not from a
token-behaviour premise or from the vault's later return check. -/
theorem SuccessfulWethProgramRun.transfer_effect
    {vault receiver : Adr} {assets : B256} {output : Bytes}
    {initial final : Stor}
    (run : SuccessfulWethProgramRun vault
      (transferCalldata receiver assets) output initial final) :
    Transfer (Stor.rest initial) vault assets receiver (Stor.rest final) ∧
      Stor.AgreeOffAdr initial final ∧
      output = (1 : B256).toBytes := by
  rcases run with ⟨childSevm, childPre, rawPost,
    currentTarget, codeAddress, caller, valueZero, dataEq, stackEmpty,
    memoryEmpty, initialEq, compiled, rawError, finalEq, outputEq⟩
  obtain ⟨selectorEq, receiverArg, assetsArg⟩ :=
    transferCalldata_facts dataEq
  have receiverWord : Sevm.argWord childSevm 0 = receiver.toB256 := by
    unfold Sevm.argWord
    rw [show (32 * (0 : B256) + 4) = (4 : B256) by decide +kernel]
    exact receiverArg
  have assetsWord : Sevm.argWord childSevm 1 = assets := by
    unfold Sevm.argWord
    rw [show (32 * (1 : B256) + 4) = (36 : B256) by decide +kernel]
    exact assetsArg
  have member :
      (selector "transfer" [.address, .uint256], nonpayable transfer) ∈
        Blanc.wethFuncs := by
    simp [Blanc.wethFuncs]
  obtain ⟨bodyPre, -, entryState, entryMemory, entryLogs,
      entryOutput, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable compiled selectorEq member
  obtain ⟨movement, offAddress, bodyOutput⟩ :=
    transferBody_exactEffect bodyRun
  have entryStor : Devm.getStor childPre wethAccount =
      Devm.getStor bodyPre wethAccount :=
    getStor_eq_of_state_eq entryState wethAccount
  have bodyInitial : Devm.getStor bodyPre wethAccount = initial :=
    entryStor.symm.trans initialEq
  have bodyFinal : Devm.getStor rawPost wethAccount = final :=
    finalEq.symm
  rw [currentTarget, caller, receiverWord, assetsWord,
    bodyInitial, bodyFinal] at movement
  rw [currentTarget, bodyInitial, bodyFinal] at offAddress
  exact ⟨by simpa only [toAdr_toB256] using movement, offAddress,
    outputEq.symm.trans bodyOutput⟩

/-! ## Delegated transfer effect -/

/-- An exact successful WETH `transferFrom(owner,vault,assets)` child moves
precisely that balance-row amount and returns canonical true.  The selected
WETH frame caller is the vault, which is the spender used by the allowance
path; the three movement roles come from the exact calldata words. -/
theorem SuccessfulWethProgramRun.transferFrom_effect
    {vault owner : Adr} {assets : B256} {output : Bytes}
    {initial final : Stor}
    (run : SuccessfulWethProgramRun vault
      (transferFromCalldata owner vault assets) output initial final) :
    Transfer (Stor.rest initial) owner assets vault (Stor.rest final) ∧
      output = (1 : B256).toBytes := by
  rcases run with ⟨childSevm, childPre, rawPost,
    currentTarget, codeAddress, caller, valueZero, dataEq, stackEmpty,
    memoryEmpty, initialEq, compiled, rawError, finalEq, outputEq⟩
  obtain ⟨selectorEq, ownerArg, vaultArg, assetsArg⟩ :=
    transferFromCalldata_facts dataEq
  have ownerWord : Sevm.argWord childSevm 0 = owner.toB256 := by
    unfold Sevm.argWord
    rw [show (32 * (0 : B256) + 4) = (4 : B256) by decide +kernel]
    exact ownerArg
  have vaultWord : Sevm.argWord childSevm 1 = vault.toB256 := by
    unfold Sevm.argWord
    rw [show (32 * (1 : B256) + 4) = (36 : B256) by decide +kernel]
    exact vaultArg
  have assetsWord : Sevm.argWord childSevm 2 = assets := by
    unfold Sevm.argWord
    rw [show (32 * (2 : B256) + 4) = (68 : B256) by decide +kernel]
    exact assetsArg
  have member :
      (selector "transferFrom" [.address, .address, .uint256],
        nonpayable transferFrom) ∈ Blanc.wethFuncs := by
    simp [Blanc.wethFuncs]
  obtain ⟨bodyPre, -, entryState, entryMemory, entryLogs,
      entryOutput, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable compiled selectorEq member
  obtain ⟨movement, bodyOutput⟩ := transferFromBody_exactEffect bodyRun
  have entryStor : Devm.getStor childPre wethAccount =
      Devm.getStor bodyPre wethAccount :=
    getStor_eq_of_state_eq entryState wethAccount
  have bodyInitial : Devm.getStor bodyPre wethAccount = initial :=
    entryStor.symm.trans initialEq
  have bodyFinal : Devm.getStor rawPost wethAccount = final :=
    finalEq.symm
  rw [currentTarget, ownerWord, vaultWord, assetsWord,
    bodyInitial, bodyFinal] at movement
  exact ⟨by simpa only [toAdr_toB256] using movement,
    outputEq.symm.trans bodyOutput⟩

end Blanc.Composition.ProrataWethVault
