import Blanc.Composition.ProrataWethVaultBoundary
import Blanc.CompiledFixedInvariance
import Blanc.Ladder
import Blanc.NonpayableInversion
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

/-- The same exact child execution at the frame strength needed by composed
read-only views.  `State` equality would be too strong here: even a zero-value
message entry may normalize an account map.  The observable storage world and
log frame are retained instead. -/
def SuccessfulWethWorldProgramRun
    (caller : Adr) (calldata output : Bytes)
    (initial final : Adr → Stor) (initialLogs finalLogs : List Log) : Prop :=
  ∃ (childSevm : Sevm) (childPre rawPost : Devm),
    childSevm.currentTarget = wethAccount ∧
    childSevm.codeAddress = some wethAccount ∧
    childSevm.caller = caller ∧
    childSevm.value = 0 ∧
    childSevm.data = calldata ∧
    childPre.stack = [] ∧
    childPre.memory = Mem.empty ∧
    childPre.logs = [] ∧
    Devm.getStor childPre = initial ∧
    Prog.RunCompiled childSevm childPre Blanc.weth rawPost ∧
    rawPost.error = none ∧
    final = Devm.getStor rawPost ∧
    finalLogs = initialLogs ++ rawPost.logs ∧
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
    rcases of_run_branch_revert run with ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_next run with ⟨_, _, run⟩
    rcases of_run_prepend isMax _ run with ⟨_, _, run⟩
    rcases of_run_branch run with
      ⟨_, _, finiteRun⟩ | ⟨_, _, _, _, _, _, maxReturn⟩
    · rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_branch_revert finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, finiteRun⟩
      rcases of_run_next finiteRun with ⟨_, _, trueRun⟩
      exact returnTrue_output trueRun
    · exact returnTrue_output maxReturn
  · exact returnTrue_output callerReturn

/-! ## Exact selector entry -/

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

/-- The exact untagged two-word key used by inherited WETH. -/
def wethAllowanceKey (owner spender : B256) : B256 :=
  (owner.toBytes ++ spender.toBytes).keccak

/-- The three successful paths through inherited WETH's allowance suffix.
The finite arm retains the executed SSTORE, even when its value is unchanged.
The pre-state here is entry to the suffix, after the balance movement. -/
def WethAllowanceUpdateEffect (sevm : Sevm) (src wad : B256)
    (pre post : Devm) : Prop :=
  if src = sevm.caller.toB256 then Devm.getStor post = Devm.getStor pre
  else
    let key := wethAllowanceKey src sevm.caller.toB256
    let allowed := pre.getStorVal sevm.currentTarget key
    ¬ ValidAdr key ∧
      ((allowed = B256.max ∧ Devm.getStor post = Devm.getStor pre) ∨
       (allowed ≠ B256.max ∧ wad ≤ allowed ∧
        Devm.getStor post sevm.currentTarget =
          (Devm.getStor pre sevm.currentTarget).set key (allowed - wad) ∧
        ∃ writePre writePost,
          Ninst.Run sevm writePre sstore writePost ∧
          [key, allowed - wad] <<+ writePre.stack ∧
          Devm.getStor writePre = Devm.getStor pre ∧
          Devm.getStor post = Devm.getStor writePost))

private theorem updateAllowance_exact
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {src wad : B256}
    (wf : Mem.Wf pre.memory) (hp : [wad, src] <<+ pre.stack)
    (run : Func.Run fs sevm pre updateAllowance post) :
    WethAllowanceUpdateEffect sevm src wad pre post := by
  unfold WethAllowanceUpdateEffect
  rcases of_run_prepend [caller, dup 2, eq] _ run with ⟨a, ha, run⟩
  have pa : [src =? sevm.caller.toB256, wad, src] <<+ a.stack := by
    generalize_line_prefix
  have storage : Devm.getStor pre = Devm.getStor a :=
    Line.of_inv Devm.getStor (by line_inv) ha
  rcases of_run_branch run with
    ⟨b, hb, run⟩ | ⟨flag, b, c, flagNe, hb, hc, run⟩
  · have pop := hb.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at pop
    rw [pop] at pa
    have flagZero := pref_head_unique pa (pref_append [0] b.stack)
    have different : src ≠ sevm.caller.toB256 := by
      intro same
      simp only [B256.eqCheck, same, ↓reduceIte] at flagZero
      exact B256.zero_ne_one flagZero.symm
    rw [if_neg different]
    dsimp only
    rw [flagZero] at pa
    have pb : [wad, src] <<+ b.stack := cons_pref_cons_inv pa
    have storage := storage.trans
      (funext (fun account => (Devm.PopBurn.getStor hb account).symm))
    have bWf : Mem.Wf b.memory := by
      rw [← hb.memory, ← Line.of_inv Devm.memory (by line_inv) ha]
      exact wf
    rcases of_run_prepend (swap 0 :: mstoreAt 0) _ run with ⟨c, hc, run⟩
    rcases Line.of_run_cons hc with ⟨b', hswap, hstore⟩
    have pb' : [src, wad] <<+ b'.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap (0 : Fin 16).val [wad, src] [src, wad] from Stack.swapCore_zero)
        (of_run_swap hswap) pb
    obtain ⟨pc, mc⟩ := of_run_mstoreAt_val hstore pb'
    have storage := storage.trans (Line.of_inv Devm.getStor (by line_inv) hc)
    rcases of_run_next run with ⟨d, hd, run⟩
    have pd := prefix_of_push (of_run_caller hd) pc
    have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hd)
    rcases of_run_prepend (mstoreAt 1) _ run with ⟨e, he, run⟩
    obtain ⟨pe, me⟩ := of_run_mstoreAt_val he pd
    have storage := storage.trans (Line.of_inv Devm.getStor (by line_inv) he)
    rcases of_run_prepend (pushList [64, 0]) _ run with ⟨f, hf, run⟩
    have pf : [0, 64, wad] <<+ f.stack := by
      rcases Line.of_run_cons hf with ⟨f', h64, hf'⟩
      rcases Line.of_run_cons hf' with ⟨f'', h0, hnil⟩
      cases hnil
      exact prefix_of_push (of_run_pushB256 h0)
        (prefix_of_push (of_run_pushB256 h64) pe)
    have window : (f.memory.read 0 64).1 = src.toBytes ++ sevm.caller.toB256.toBytes := by
      rw [← Line.of_inv Devm.memory (by line_inv) hf, me,
        ← (of_run_caller hd).memory, mc,
        ← Ninst.Hinv.inv (f := Devm.memory) hswap]
      exact Mem.read_two_word_writes bWf (image := b.memory.data.toList)
        (by intro i; simp) _ _
    have storage := storage.trans (Line.of_inv Devm.getStor (by line_inv) hf)
    rcases of_run_next run with ⟨g, hg, run⟩
    have pg := (prefix_of_keccak256_val hg pf).1
    change (f.memory.read 0 64).1.keccak :: [wad] <<+ g.stack at pg
    rw [window] at pg
    change [wethAllowanceKey src sevm.caller.toB256, wad] <<+ g.stack at pg
    have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hg)
    rcases of_run_next run with ⟨h, hh, run⟩
    have ph : [wad, wethAllowanceKey src sevm.caller.toB256] <<+ h.stack :=
      Stack.prefix_of_swap
        (show Stack.Swap (0 : Fin 16).val
          [wethAllowanceKey src sevm.caller.toB256, wad]
          [wad, wethAllowanceKey src sevm.caller.toB256] from Stack.swapCore_zero)
        (of_run_swap hh) pg
    have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hh)
    rcases of_run_next run with ⟨i, hi, run⟩
    have pi := prefix_of_dup_val hi (by show_nth) ph
    have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hi)
    rcases of_run_prepend checkAddress _ run with ⟨j, hj, run⟩
    obtain ⟨valid, pj, validIff⟩ := of_check_address pi hj
    have storage := storage.trans (Line.of_inv Devm.getStor (by line_inv) hj)
    rcases of_run_branch_revert run with ⟨k, hk, run⟩
    have pop := hk.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at pop
    rw [pop] at pj
    have validZero := pref_head_unique pj (pref_append [0] k.stack)
    refine ⟨validIff.mp validZero, ?_⟩
    rw [validZero] at pj
    have pk := cons_pref_cons_inv pj
    have storage := storage.trans
      (funext (fun account => (Devm.PopBurn.getStor hk account).symm))
    rcases of_run_next run with ⟨l, hl, run⟩
    have pl := prefix_of_dup_val hl (by show_nth) pk
    have storageL := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hl)
    rcases of_run_next run with ⟨m, hm, run⟩
    obtain ⟨allowed, pm, read⟩ := prefix_of_sload hm pl
    have readEntry : allowed = pre.getStorVal sevm.currentTarget
        (wethAllowanceKey src sevm.caller.toB256) := by
      rw [read]
      change (Devm.getStor l sevm.currentTarget).get _ = _
      rw [← storageL]
      rfl
    rw [← readEntry]
    have storage := storageL.trans (Ninst.Hinv.inv (f := Devm.getStor) hm)
    rcases of_run_next run with ⟨n, hn, run⟩
    have pn := prefix_of_dup_val hn (Stack.Nth.head _ _) pm
    have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hn)
    rcases of_run_prepend isMax _ run with ⟨o, ho, run⟩
    have po : [((~~~ allowed) =? 0), allowed, wad,
        wethAllowanceKey src sevm.caller.toB256] <<+ o.stack := by
      rcases Line.of_run_cons ho with ⟨o', hnot, ho'⟩
      rcases Line.of_run_cons ho' with ⟨o'', hzero, hnil⟩
      cases hnil
      exact prefix_of_iszero hzero (prefix_of_not hnot pn)
    have storage := storage.trans (Line.of_inv Devm.getStor (by line_inv) ho)
    rcases of_run_branch run with
      ⟨p, hp, run⟩ | ⟨flag, p, q, flagNe, hp, hq, run⟩
    · have pop := hp.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at pop
      rw [pop] at po
      have zero := pref_head_unique po (pref_append [0] p.stack)
      have finite : allowed ≠ B256.max := by
        intro maximum
        rw [maximum, B256.not_max] at zero
        simp only [B256.eqCheck, ↓reduceIte] at zero
        exact B256.zero_ne_one zero.symm
      rw [zero] at po
      have pp := cons_pref_cons_inv po
      have storage := storage.trans
        (funext (fun account => (Devm.PopBurn.getStor hp account).symm))
      rcases of_run_next run with ⟨q, hq, run⟩
      have pq := prefix_of_dup_val hq (by show_nth) pp
      have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hq)
      rcases of_run_next run with ⟨r, hr, run⟩
      have pr := prefix_of_dup_val hr (by show_nth) pq
      have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hr)
      rcases of_run_next run with ⟨t, ht, run⟩
      have pt := prefix_of_lt ht pr
      have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) ht)
      rcases of_run_branch_revert run with ⟨u, hu, run⟩
      have pop := hu.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at pop
      rw [pop] at pt
      have zero := pref_head_unique pt (pref_append [0] u.stack)
      have covered : wad ≤ allowed := by
        rw [← B256.not_lt]
        intro less
        rw [B256.ltCheck, if_pos less] at zero
        exact B256.zero_ne_one zero.symm
      rw [zero] at pt
      have pu := cons_pref_cons_inv pt
      have storage := storage.trans
        (funext (fun account => (Devm.PopBurn.getStor hu account).symm))
      rcases of_run_next run with ⟨v, hv, run⟩
      have pv := prefix_of_sub hv pu
      have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hv)
      rcases of_run_next run with ⟨w, hw, run⟩
      have pw : [wethAllowanceKey src sevm.caller.toB256, allowed - wad] <<+ w.stack :=
        Stack.prefix_of_swap
          (show Stack.Swap (0 : Fin 16).val
            [allowed - wad, wethAllowanceKey src sevm.caller.toB256]
            [wethAllowanceKey src sevm.caller.toB256, allowed - wad] from Stack.swapCore_zero)
          (of_run_swap hw) pv
      have storage := storage.trans (Ninst.Hinv.inv (f := Devm.getStor) hw)
      rcases of_run_next run with ⟨z, hz, run⟩
      have after : Devm.getStor z = Devm.getStor post :=
        Func.of_inv Devm.getStor Devm.getStor (by func_inv) run
      refine Or.inr ⟨finite, covered, ?_, w, z, hz, pw, storage.symm, after.symm⟩
      rw [← after, sstore_getStor_set hz pw, ← storage]
    · have pop := hp.stack
      simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at pop
      rw [pop] at po
      have flagEq := pref_head_unique po (pref_append [flag] p.stack)
      have complementZero : ~~~ allowed = 0 := by
        by_contra different
        simp only [B256.eqCheck, if_neg different] at flagEq
        exact flagNe flagEq.symm
      refine Or.inl ⟨B256.eq_max_of_not_eq_zero complementZero, ?_⟩
      exact (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run).symm.trans
        ((funext (Devm.Burn.getStor hq)).trans
          ((funext (Devm.PopBurn.getStor hp)).trans storage.symm))
  · have pop := hb.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at pop
    rw [pop] at pa
    have flagEq := pref_head_unique pa (pref_append [flag] b.stack)
    have same : src = sevm.caller.toB256 := by
      by_contra different
      simp only [B256.eqCheck, if_neg different] at flagEq
      exact flagNe flagEq.symm
    rw [if_pos same]
    exact (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run).symm.trans
      ((funext (Devm.Burn.getStor hc)).trans
        ((funext (Devm.PopBurn.getStor hb)).trans storage.symm))

/-- Retain the raw key and amount that the successful approval staging computes. -/
private theorem prepApprove_exact {sevm : Sevm} {pre post : Devm}
    (wf : Mem.Wf pre.memory) (run : Line.Run sevm pre prepApprove post) :
    ∃ flag, [flag, wethAllowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0),
      Sevm.argWord sevm 1] <<+ post.stack ∧
      (flag = 0 ↔ ¬ ValidAdr
        (wethAllowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0))) := by
  unfold prepApprove at run
  rcases Line.of_run_cons run with ⟨c1, hcaller, run⟩
  have callerPush := of_run_caller hcaller
  rcases of_run_append (mstoreAt 0) run with ⟨c2, hstore, run⟩
  obtain ⟨tail, storeMemory⟩ := of_run_mstoreAt_val hstore
    (prefix_of_push callerPush nil_pref)
  change [] <<+ c2.stack at tail
  rcases of_run_append (argCopy 1 0 1) run with ⟨c6, hcopyLine, run⟩
  simp only [argCopy, cdc] at hcopyLine
  rcases Line.of_run_cons hcopyLine with ⟨c3, hsize, hcopyLine⟩
  rcases Line.of_run_cons hcopyLine with ⟨c4, hsrc, hcopyLine⟩
  rcases Line.of_run_cons hcopyLine with ⟨c5, hdst, hcopyLine⟩
  rcases Line.of_run_cons hcopyLine with ⟨c6', hcopy, hnil⟩
  cases hnil
  have pcopy : [32, 4, 32] <<+ c5.stack := by
    have p := prefix_of_push (of_run_pushB256 hdst)
      (prefix_of_push (of_run_pushB256 hsrc)
        (prefix_of_push (of_run_pushB256 hsize) tail))
    simpa only [show (1 * 32 : B256) = 32 by decide +kernel,
      show (0 * 32 + 4 : B256) = 4 by decide +kernel,
      List.cons_append, List.nil_append] using p
  obtain ⟨copyTail, copyMemory⟩ := prefix_of_calldatacopy_val hcopy pcopy
  rcases of_run_append (arg 1) run with ⟨c7, harg, run⟩
  have amountPrefix := prefix_of_arg copyTail harg
  rcases of_run_append (pushList [64, 0]) run with ⟨c9, hwindow, run⟩
  have windowPrefix : [0, 64, Sevm.argWord sevm 1] <<+ c9.stack := by
    rcases Line.of_run_cons hwindow with ⟨c8, h64, hw⟩
    rcases Line.of_run_cons hw with ⟨c9', h0, hn⟩
    cases hn
    exact prefix_of_push (of_run_pushB256 h0)
      (prefix_of_push (of_run_pushB256 h64) amountPrefix)
  rcases Line.of_run_cons run with ⟨c10, hhash, run⟩
  have hashPrefix := (prefix_of_keccak256_val hhash windowPrefix).1
  have copiedWord : sevm.data.sliceD 4 32 0 = (Sevm.argWord sevm 0).toBytes := by
    change sevm.data.sliceD 4 32 0 = (Bytes.toB256 (sevm.data.sliceD 4 32 0)).toBytes
    exact (Bytes.toBytes_toB256_of_length (List.takeD_length _ _ _)).symm
  have window : (c9.memory.read 0 64).1 =
      sevm.caller.toB256.toBytes ++ (Sevm.argWord sevm 0).toBytes := by
    rw [← Line.of_inv Devm.memory (by line_inv) hwindow,
      ← Line.of_inv Devm.memory (by line_inv) harg, copyMemory,
      ← (of_run_pushB256 hdst).memory, ← (of_run_pushB256 hsrc).memory,
      ← (of_run_pushB256 hsize).memory, storeMemory, ← callerPush.memory]
    change (((pre.memory.write 0 sevm.caller.toB256.toBytes).write 32
      (sevm.data.sliceD 4 32 0)).read 0 64).1 = _
    rw [copiedWord]
    exact Mem.read_two_word_writes wf (image := pre.memory.data.toList)
      (by intro i; simp) _ _
  change (c9.memory.read 0 64).1.keccak :: [Sevm.argWord sevm 1] <<+
    c10.stack at hashPrefix
  rw [window] at hashPrefix
  change wethAllowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0) ::
    [Sevm.argWord sevm 1] <<+ c10.stack at hashPrefix
  rcases Line.of_run_cons run with ⟨c11, hdup, hcheck⟩
  have dupPrefix : [wethAllowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0),
      wethAllowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0),
      Sevm.argWord sevm 1] <<+ c11.stack := by
    exact prefix_of_dup_val hdup (Stack.Nth.head _ _) hashPrefix
  exact of_check_address dupPrefix hcheck

/-- An actual successful exact compiled WETH approval writes precisely the
caller/spender raw allowance cell, unconditionally in the hash model. -/
theorem weth_approve_compiled_raw_effect {sevm : Sevm} {pre post : Devm}
    (wf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (selected : Sevm.selector sevm = selector "approve" [.address, .uint256]) :
    ¬ ValidAdr (wethAllowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0)) ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set
          (wethAllowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0))
          (Sevm.argWord sevm 1) := by
  obtain ⟨bodyPre, -, entryState, entryMemory, -, -, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable (body := Blanc.approve) run selected
      (by simp [wethFuncs])
  rcases of_run_prepend (arg 0 ++ checkNonAddress) _ bodyRun with
    ⟨a, ha, run⟩
  rcases of_run_branch_revert run with ⟨b, hb, run⟩
  rcases of_run_prepend prepApprove _ run with ⟨c, hc, run⟩
  have bMemory : pre.memory = b.memory := entryMemory.trans
    ((Line.of_inv Devm.memory (by line_inv) ha).trans hb.memory)
  obtain ⟨flag, hp, flagIff⟩ := prepApprove_exact (bMemory ▸ wf) hc
  rcases of_run_branch_revert run with ⟨d, hd, run⟩
  have pop := hd.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at pop
  rw [pop] at hp
  have flagZero : flag = 0 := pref_head_unique hp (pref_append [0] d.stack)
  rw [flagZero] at hp
  have storedPrefix := cons_pref_cons_inv hp
  rcases of_run_next run with ⟨f, hs, run⟩
  have stored := sstore_getStor_set hs storedPrefix
  have before : Devm.getStor pre = Devm.getStor d :=
    (funext (getStor_eq_of_state_eq entryState)).trans
      ((Line.of_inv Devm.getStor (by line_inv) ha).trans
        ((funext (fun account => (Devm.PopBurn.getStor hb account).symm)).trans
          ((Line.of_inv Devm.getStor (by line_inv) hc).trans
            (funext (fun account => (Devm.PopBurn.getStor hd account).symm)))))
  have after : Devm.getStor f = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) run
  refine ⟨flagIff.mp flagZero, ?_⟩
  rw [← congrFun after sevm.currentTarget, stored, ← congrFun before sevm.currentTarget]

/-! ## Finite allowance-key attribution

The records below retain successful compiled invocations rather than assumed
storage effects. Their list is an allowance-call projection; chronological
completeness and world-state continuity must still be supplied by a retained
history adapter. In particular this list is not itself `PairReach`.
-/

/-- A successful exact WETH invocation that can touch an allowance key.
`approval = false` selects `transferFrom`. -/
structure WethAllowanceInvocation where
  sevm : Sevm
  pre : Devm
  post : Devm
  approval : Bool
  target : sevm.currentTarget = wethAccount
  memoryWf : Mem.Wf pre.memory
  run : Prog.RunCompiled sevm pre Blanc.weth post
  selected : Sevm.selector sevm =
    if approval then selector "approve" [.address, .uint256]
    else selector "transferFrom" [.address, .address, .uint256]

/-- Raw words, without address normalization. A self `transferFrom` bypasses
allowance hashing; all other successful allowance invocations visit one pair.
Both finite-decrement and maximum-allowance visits retain their pair. -/
def WethAllowanceInvocation.pair? (call : WethAllowanceInvocation) :
    Option (B256 × B256) :=
  if call.approval then
    some (call.sevm.caller.toB256, Sevm.argWord call.sevm 0)
  else if Sevm.argWord call.sevm 0 = call.sevm.caller.toB256 then none
  else some (Sevm.argWord call.sevm 0, call.sevm.caller.toB256)

/-- The finite allowance-pair projection, preserving repeated visits. -/
def touchedWethAllowancePairs (history : List WethAllowanceInvocation) :
    List (B256 × B256) := history.filterMap WethAllowanceInvocation.pair?

/-- The write projection drops maximum-allowance reads as well as self
bypasses. `allowance_effect` and `transferFrom_writer_has_sstore` below
justify this filter from each compiled invocation. Chronological completeness
remains an obligation of the retained-history adapter. -/
def WethAllowanceInvocation.writtenPair? (call : WethAllowanceInvocation) :
    Option (B256 × B256) :=
  if call.approval then call.pair?
  else call.pair?.filter fun p =>
    call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) != B256.max

/-- Only allowance invocations whose selected path writes the cell. -/
def writtenWethAllowancePairs (history : List WethAllowanceInvocation) :
    List (B256 × B256) := history.filterMap WethAllowanceInvocation.writtenPair?

/-- D9's vault-local key separation: only a touched pair owned by the vault
must be distinguished from a different touched pair that can write WETH
allowance storage. No relation between two foreign pairs is required.
The explicit finite predicate is kept separate from reachability. -/
def NoVaultAllowanceKeyCollision (history : List WethAllowanceInvocation)
    (vault : Adr) : Prop :=
  ∀ p ∈ touchedWethAllowancePairs history, p.1 = vault.toB256 →
    ∀ q ∈ writtenWethAllowancePairs history, p ≠ q →
      wethAllowanceKey p.1 p.2 ≠ wethAllowanceKey q.1 q.2

instance (history : List WethAllowanceInvocation) (vault : Adr) :
    Decidable (NoVaultAllowanceKeyCollision history vault) := by
  unfold NoVaultAllowanceKeyCollision
  infer_instance

/-- A foreign approval in the recorded exact executions cannot forge any
vault-owned allowance pair touched by that record, under D9. The raw write is
derived from the invocation's successful compiled run, never supplied as an
effect premise. This is the approval preservation rung, not yet the rooted
chronological no-foreign-debit theorem. -/
theorem foreign_approve_preserves_vault_allowance
    {history : List WethAllowanceInvocation} {vault : Adr}
    (collision : NoVaultAllowanceKeyCollision history vault)
    (call : WethAllowanceInvocation) (member : call ∈ history)
    (approval : call.approval = true)
    (foreign : call.sevm.caller ≠ vault)
    (p : B256 × B256) (touched : p ∈ touchedWethAllowancePairs history)
    (owner : p.1 = vault.toB256) :
    Devm.getStorVal call.post wethAccount (wethAllowanceKey p.1 p.2) =
      Devm.getStorVal call.pre wethAccount (wethAllowanceKey p.1 p.2) := by
  have selected : Sevm.selector call.sevm =
      selector "approve" [.address, .uint256] := by
    simpa only [approval, Bool.true_eq, ↓reduceIte] using call.selected
  have effect := (weth_approve_compiled_raw_effect call.memoryWf call.run selected).2
  have writer : (call.sevm.caller.toB256, Sevm.argWord call.sevm 0) ∈
      writtenWethAllowancePairs history := by
    apply List.mem_filterMap.mpr
    refine ⟨call, member, ?_⟩
    simp only [WethAllowanceInvocation.writtenPair?, WethAllowanceInvocation.pair?,
      approval, ↓reduceIte]
  have different : p ≠ (call.sevm.caller.toB256, Sevm.argWord call.sevm 0) := by
    intro equal
    have callerWord : vault.toB256 = call.sevm.caller.toB256 :=
      owner.symm.trans (congrArg Prod.fst equal)
    have callerAdr := congrArg B256.toAdr callerWord
    exact foreign (by simpa only [toAdr_toB256] using callerAdr.symm)
  have keys := collision p touched owner _ writer different
  rw [← call.target]
  change (Devm.getStor call.post call.sevm.currentTarget).get _ =
    (Devm.getStor call.pre call.sevm.currentTarget).get _
  rw [effect, Stor.get_set_ne _ (Ne.symm keys)]

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

/-! ## Foreign-account storage frame

The vault's own share ledger must survive its WETH child.  The inherited
`transferFrom` body writes storage only at its own `currentTarget`, so every
other account -- the vault included -- keeps its exact storage.  Each fragment
that contains an `SSTORE` gets its own frame lemma here; every other fragment
is already covered by the whole-world equalities the movement walk carries. -/

private theorem sstore_foreignStorage
    {sevm : Sevm} {s r : Devm} {account : Adr}
    (run : Ninst.Run sevm s Ninst.sstore r)
    (foreign : sevm.currentTarget ≠ account) :
    Devm.getStor r account = Devm.getStor s account := by
  obtain ⟨pc, registerRun⟩ := of_run_reg run
  exact sstore_preserves_getStor_ne registerRun foreign

private theorem transferFromUpdateSbal_foreignStorage
    {sevm : Sevm} {s r : Devm} {account : Adr}
    (run : Line.Run sevm s transferFromUpdateSbal r)
    (foreign : sevm.currentTarget ≠ account) :
    Devm.getStor r account = Devm.getStor s account := by
  simp only [transferFromUpdateSbal] at run
  rcases Line.of_run_cons run with ⟨s1, subRun, run⟩
  rcases Line.of_run_cons run with ⟨s2, dupRun, run⟩
  rcases Line.of_run_cons run with ⟨s3, storeRun, nil⟩
  cases nil
  have prefixStorage : Devm.getStor s = Devm.getStor s2 :=
    (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons subRun Line.Run.nil)).trans
      (Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons dupRun Line.Run.nil))
  rw [sstore_foreignStorage storeRun foreign,
    ← congrFun prefixStorage account]

private theorem incrWbal_foreignStorage
    {sevm : Sevm} {s r : Devm} {account : Adr}
    (run : Line.Run sevm s incrWbal r)
    (foreign : sevm.currentTarget ≠ account) :
    Devm.getStor r account = Devm.getStor s account := by
  simp only [incrWbal] at run
  rcases Line.of_run_cons run with ⟨s1, dupRun, run⟩
  rcases Line.of_run_cons run with ⟨s2, sloadRun, run⟩
  rcases Line.of_run_cons run with ⟨s3, addRun, run⟩
  rcases Line.of_run_cons run with ⟨s4, swapRun, run⟩
  rcases Line.of_run_cons run with ⟨s5, storeRun, nil⟩
  cases nil
  have prefixStorage : Devm.getStor s = Devm.getStor s4 :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons dupRun (Line.Run.cons sloadRun (Line.Run.cons addRun
        (Line.Run.cons swapRun Line.Run.nil))))
  rw [sstore_foreignStorage storeRun foreign,
    ← congrFun prefixStorage account]

/-- All three successful arms of WETH's allowance update leave every account
other than the WETH contract itself untouched: two arms write no storage at
all, and the finite-decrement arm writes only its own allowance slot. -/
private theorem updateAllowance_foreignStorage
    {fs : List Func} {sevm : Sevm} {s r : Devm} {account : Adr}
    (run : Func.Run fs sevm s updateAllowance r)
    (foreign : sevm.currentTarget ≠ account) :
    Devm.getStor r account = Devm.getStor s account := by
  have returnTrueStorage : ∀ {a b : Devm},
      Func.Run fs sevm a returnTrue b →
      Devm.getStor b account = Devm.getStor a account := by
    intro a b trueRun
    refine (congrFun ?_ account).symm
    refine Func.of_inv Devm.getStor Devm.getStor ?_ trueRun
    unfold returnTrue
    func_inv
  simp only [updateAllowance] at run
  rcases of_run_prepend [caller, dup 2, eq] _ run with ⟨p1, prefixRun, run⟩
  have prefixStorage : Devm.getStor s = Devm.getStor p1 :=
    Line.of_inv Devm.getStor (by line_inv) prefixRun
  rcases of_run_branch run with
    ⟨p2, pop2, run⟩ |
    ⟨callerWord, callerPop, callerBurnPost, callerNe, pop2, callerBurn,
      callerReturn⟩
  · have popStorage : Devm.getStor p1 = Devm.getStor p2 :=
      funext (fun a => (Devm.PopBurn.getStor pop2 a).symm)
    rcases of_run_prepend (swap 0 :: mstoreAt 0) _ run with ⟨p3, r3, run⟩
    rcases of_run_next run with ⟨p4, r4, run⟩
    rcases of_run_prepend (mstoreAt 1) _ run with ⟨p5, r5, run⟩
    rcases of_run_prepend (pushList [64, 0]) _ run with ⟨p6, r6, run⟩
    rcases of_run_next run with ⟨p7, r7, run⟩
    rcases of_run_next run with ⟨p8, r8, run⟩
    rcases of_run_next run with ⟨p9, r9, run⟩
    rcases of_run_prepend checkAddress _ run with ⟨p10, r10, run⟩
    rcases of_run_branch_revert run with ⟨p11, pop11, run⟩
    rcases of_run_next run with ⟨p12, r12, run⟩
    rcases of_run_next run with ⟨p13, r13, run⟩
    rcases of_run_next run with ⟨p14, r14, run⟩
    rcases of_run_prepend isMax _ run with ⟨p15, r15, run⟩
    have bodyStorage : Devm.getStor p2 = Devm.getStor p15 :=
      (Line.of_inv Devm.getStor (by line_inv) r3).trans
        ((Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons r4 Line.Run.nil)).trans
          ((Line.of_inv Devm.getStor (by line_inv) r5).trans
            ((Line.of_inv Devm.getStor (by line_inv) r6).trans
              ((Line.of_inv Devm.getStor (by line_inv)
                  (Line.Run.cons r7 Line.Run.nil)).trans
                ((Line.of_inv Devm.getStor (by line_inv)
                    (Line.Run.cons r8 Line.Run.nil)).trans
                  ((Line.of_inv Devm.getStor (by line_inv)
                      (Line.Run.cons r9 Line.Run.nil)).trans
                    ((Line.of_inv Devm.getStor (by line_inv) r10).trans
                      ((funext (fun a =>
                          (Devm.PopBurn.getStor pop11 a).symm)).trans
                        ((Line.of_inv Devm.getStor (by line_inv)
                            (Line.Run.cons r12 Line.Run.nil)).trans
                          ((Line.of_inv Devm.getStor (by line_inv)
                              (Line.Run.cons r13 Line.Run.nil)).trans
                            ((Line.of_inv Devm.getStor (by line_inv)
                                (Line.Run.cons r14 Line.Run.nil)).trans
                              (Line.of_inv Devm.getStor (by line_inv)
                                r15))))))))))))
    have entryStorage : Devm.getStor s = Devm.getStor p15 :=
      prefixStorage.trans (popStorage.trans bodyStorage)
    rcases of_run_branch run with
      ⟨p16, pop16, finiteRun⟩ |
      ⟨maxWord, maxPop, maxBurnPost, maxNe, pop16, maxBurn, maxReturn⟩
    · rcases of_run_next finiteRun with ⟨p17, r17, finiteRun⟩
      rcases of_run_next finiteRun with ⟨p18, r18, finiteRun⟩
      rcases of_run_next finiteRun with ⟨p19, r19, finiteRun⟩
      rcases of_run_branch_revert finiteRun with ⟨p20, pop20, finiteRun⟩
      rcases of_run_next finiteRun with ⟨p21, r21, finiteRun⟩
      rcases of_run_next finiteRun with ⟨p22, r22, finiteRun⟩
      rcases of_run_next finiteRun with ⟨p23, storeRun, trueRun⟩
      have preStoreStorage : Devm.getStor p15 = Devm.getStor p22 :=
        (funext (fun a => (Devm.PopBurn.getStor pop16 a).symm)).trans
          ((Line.of_inv Devm.getStor (by line_inv)
              (Line.Run.cons r17 Line.Run.nil)).trans
            ((Line.of_inv Devm.getStor (by line_inv)
                (Line.Run.cons r18 Line.Run.nil)).trans
              ((Line.of_inv Devm.getStor (by line_inv)
                  (Line.Run.cons r19 Line.Run.nil)).trans
                ((funext (fun a =>
                    (Devm.PopBurn.getStor pop20 a).symm)).trans
                  ((Line.of_inv Devm.getStor (by line_inv)
                      (Line.Run.cons r21 Line.Run.nil)).trans
                    (Line.of_inv Devm.getStor (by line_inv)
                      (Line.Run.cons r22 Line.Run.nil)))))))
      rw [returnTrueStorage trueRun, sstore_foreignStorage storeRun foreign,
        ← congrFun preStoreStorage account, ← congrFun entryStorage account]
    · rw [returnTrueStorage maxReturn, Devm.Burn.getStor maxBurn account,
        Devm.PopBurn.getStor pop16 account,
        ← congrFun entryStorage account]
  · rw [returnTrueStorage callerReturn, Devm.Burn.getStor callerBurn account,
      Devm.PopBurn.getStor pop2 account, ← congrFun prefixStorage account]

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
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor r account = Devm.getStor s account) ∧
      r.logs = s.logs ++
        [transferLogEntry sevm sevm.caller.toB256 (Sevm.argWord sevm 0)
          (Sevm.argWord sevm 1)] ∧
      AbiReturnsTrue r := by
  simp only [transfer] at run
  rcases of_run_prepend transferTestDst _ run with ⟨s1, h1, run⟩
  rcases transferTestDst_exact h1 with ⟨invalid, hp1, valid⟩
  have storage1 : Devm.getStor s = Devm.getStor s1 :=
    Line.of_inv Devm.getStor (by line_inv) h1
  have logs1 : s.logs = s1.logs :=
    Line.of_inv Devm.logs (by line_inv) h1
  clear h1
  rcases of_run_branch_revert run with ⟨s2, pop2, run⟩
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
  have logs2 : s.logs = s2.logs := logs1.trans pop2.logs
  clear hp1 popStack2 pop2 valid
  rcases of_run_prepend transferTestLt _ run with ⟨s3, h3, run⟩
  rcases transferTestLt_exact hp2 h3 with ⟨less, hp3, covered⟩
  have storage3 : Devm.getStor s = Devm.getStor s3 :=
    storage2.trans (Line.of_inv Devm.getStor (by line_inv) h3)
  have logs3 : s.logs = s3.logs :=
    logs2.trans (Line.of_inv Devm.logs (by line_inv) h3)
  clear h3 hp2
  rcases of_run_branch_revert run with ⟨s4, pop4, run⟩
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
  have logs4 : s.logs = s4.logs := logs3.trans pop4.logs
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
  have logs5 : s4.logs = s5.logs := Ninst.Hinv.inv (f := Devm.logs) store5
  have logs6 : s5.logs = s6.logs :=
    Line.of_inv Devm.logs (by line_inv) h6
  obtain ⟨s7, h7, trueRun⟩ := of_run_prepend logTransfer returnTrue run
  obtain ⟨-, emitted⟩ := logTransfer_effect nil_pref h7
  have tailLogs : s7.logs = r.logs := by
    refine Func.of_inv Devm.logs Devm.logs ?_ trueRun
    unfold returnTrue
    func_inv
  have tailStorageFull : Devm.getStor s6 = Devm.getStor r :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) run
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
  refine ⟨?_, ?_, ?_, ?_, outputTrue⟩
  · simpa only [toAdr_toB256] using exactTransfer
  · refine Stor.AgreeOffAdr.trans
      (Stor.AgreeOffAdr.of_eq (congrFun storage4 sevm.currentTarget)) ?_
    refine Stor.AgreeOffAdr.trans ?_
      (offAddress6.trans (Stor.AgreeOffAdr.of_eq tailStorage))
    rw [callerSet]
    exact Stor.AgreeOffAdr.set (validAdr_toB256 sevm.caller)
  · intro account accountNe
    rw [← congrFun tailStorageFull account,
      incrWbal_foreignStorage h6 accountNe,
      sstore_foreignStorage store5 accountNe, ← congrFun storage4 account]
  · rw [← tailLogs, emitted, ← logs6, ← logs5, ← logs4]

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
    (∀ account, sevm.currentTarget ≠ account →
      Devm.getStor r account = Devm.getStor s account) ∧
    r.logs = s.logs ++
      [transferLogEntry sevm (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
        (Sevm.argWord sevm 2)] ∧
    AbiReturnsTrue r ∧
    (Mem.Wf s.memory → ∃ allowancePre,
      Stor.AgreeOffAdr (Devm.getStor s sevm.currentTarget)
        (Devm.getStor allowancePre sevm.currentTarget) ∧
      WethAllowanceUpdateEffect sevm (Sevm.argWord sevm 0)
        (Sevm.argWord sevm 2) allowancePre r) := by
  let src := Sevm.argWord sevm 0
  let dst := Sevm.argWord sevm 1
  let wad := Sevm.argWord sevm 2
  simp only [transferFrom] at run
  rcases of_run_prepend (arg 0) _ run with ⟨a1, h1, run⟩
  have hs1 : src :: [] <<+ a1.stack := by
    simpa only [src] using prefix_of_arg nil_pref h1
  have storage : Devm.getStor s = Devm.getStor a1 :=
    Line.of_inv Devm.getStor (by line_inv) h1
  have logs : s.logs = a1.logs :=
    Line.of_inv Devm.logs (by line_inv) h1
  have memory : s.memory = a1.memory :=
    Line.of_inv Devm.memory (by line_inv) h1
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
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r2 Line.Run.nil))
  clear r2 pb2 hs1
  rcases of_run_prepend checkNonAddress _ run with ⟨a3, h3, run⟩
  rcases of_check_non_address hs2 h3 with ⟨invalidSrc, hs3, srcIff⟩
  have storage := storage.trans (Line.of_inv Devm.getStor (by line_inv) h3)
  have logs := logs.trans (Line.of_inv Devm.logs (by line_inv) h3)
  have memory := memory.trans (Line.of_inv Devm.memory (by line_inv) h3)
  clear h3 hs2
  rcases of_run_branch_revert run with ⟨a4, pop4, run⟩
  have popStack4 := pop4.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at popStack4
  rw [popStack4] at hs3
  have srcValid : ValidAdr src :=
    srcIff.mp (pref_head_unique hs3 (pref_append [0] a4.stack))
  rw [pref_head_unique hs3 (pref_append [0] a4.stack)] at hs3
  have hs4 : [src] <<+ a4.stack := cons_pref_cons_inv hs3
  have storage := storage.trans
    (funext (fun a => (Devm.PopBurn.getStor pop4 a).symm))
  have logs := logs.trans pop4.logs
  have memory := memory.trans pop4.memory
  clear hs3 popStack4 pop4 srcIff
  rcases of_run_prepend (arg 2) _ run with ⟨a5, h5, run⟩
  have hs5 : wad :: src :: [] <<+ a5.stack := by
    simpa only [wad] using prefix_of_arg hs4 h5
  have storage := storage.trans (Line.of_inv Devm.getStor (by line_inv) h5)
  have logs := logs.trans (Line.of_inv Devm.logs (by line_inv) h5)
  have memory := memory.trans (Line.of_inv Devm.memory (by line_inv) h5)
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
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r6 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r6 Line.Run.nil))
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
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r7 Line.Run.nil))
  clear r7 pb7 hs6
  rcases of_run_next run with ⟨a8, r8, run⟩
  rcases prefix_of_sload r8 hs7 with ⟨sourceBalance, hs8, sourceBalanceEq⟩
  have storage := storage7.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r8 Line.Run.nil))
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r8 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r8 Line.Run.nil))
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
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r9 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r9 Line.Run.nil))
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
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r10 Line.Run.nil))
  clear r10 pb10 hs9
  rcases of_run_next run with ⟨a11, r11, run⟩
  have hs11 : (sourceBalance <? wad) ::
      [sourceBalance, wad, wad, src] <<+ a11.stack :=
    prefix_of_lt r11 hs10
  have storage := storage.trans
    (Line.of_inv Devm.getStor (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r11 Line.Run.nil))
  clear r11 hs10
  rcases of_run_branch_revert run with ⟨a12, pop12, run⟩
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
  have logs := logs.trans pop12.logs
  have memory := memory.trans pop12.memory
  clear hs11 popStack12 pop12 lessZero
  rcases of_run_prepend transferFromUpdateSbal _ run with ⟨a13, h13, run⟩
  have sourceBalanceEq' : sourceBalance =
      (Devm.getStor a12 sevm.currentTarget).get src := by
    rw [sourceBalanceEq]
    show (Devm.getStor a7 sevm.currentTarget).get src = _
    rw [congrFun (storage7.symm.trans storage12) sevm.currentTarget]
  rcases of_transferFromUpdateSbal srcValid sourceBalanceEq' covered hs12 h13
      with ⟨sourceDecrease, covered', off13⟩
  have hs13 : [wad, src] <<+ a13.stack := by
    generalize_line_prefix
  have logs := logs.trans (Line.of_inv Devm.logs (by line_inv) h13)
  have memory := memory.trans (Line.of_inv Devm.memory (by line_inv) h13)
  have foreign13 : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor a13 account = Devm.getStor a12 account :=
    fun _ ne => transferFromUpdateSbal_foreignStorage h13 ne
  clear h13 hs12 sourceBalanceEq sourceBalanceEq' covered
  rcases of_run_prepend (arg 1) _ run with ⟨a14, h14, run⟩
  have hs14 : dst :: wad :: src :: [] <<+ a14.stack := by
    simpa only [dst] using prefix_of_arg hs13 h14
  have storage' : Devm.getStor a13 = Devm.getStor a14 :=
    Line.of_inv Devm.getStor (by line_inv) h14
  have logs := logs.trans (Line.of_inv Devm.logs (by line_inv) h14)
  have memory := memory.trans (Line.of_inv Devm.memory (by line_inv) h14)
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
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r15 Line.Run.nil))
  clear r15 pb15 hs14
  rcases of_run_prepend checkNonAddress _ run with ⟨a16, h16, run⟩
  rcases of_check_non_address hs15 h16 with ⟨invalidDst, hs16, dstIff⟩
  have storage' := storage'.trans
    (Line.of_inv Devm.getStor (by line_inv) h16)
  have logs := logs.trans (Line.of_inv Devm.logs (by line_inv) h16)
  have memory := memory.trans (Line.of_inv Devm.memory (by line_inv) h16)
  clear h16 hs15
  rcases of_run_branch_revert run with ⟨a17, pop17, run⟩
  have popStack17 := pop17.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at popStack17
  rw [popStack17] at hs16
  have dstValid : ValidAdr dst :=
    dstIff.mp (pref_head_unique hs16 (pref_append [0] a17.stack))
  rw [pref_head_unique hs16 (pref_append [0] a17.stack)] at hs16
  have hs17 : [dst, wad, src] <<+ a17.stack := cons_pref_cons_inv hs16
  have storage' := storage'.trans
    (funext (fun a => (Devm.PopBurn.getStor pop17 a).symm))
  have logs := logs.trans pop17.logs
  have memory := memory.trans pop17.memory
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
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r18 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r18 Line.Run.nil))
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
  have logs := logs.trans
    (Line.of_inv Devm.logs (by line_inv) (Line.Run.cons r19 Line.Run.nil))
  have memory := memory.trans
    (Line.of_inv Devm.memory (by line_inv) (Line.Run.cons r19 Line.Run.nil))
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
  have logs20 : s.logs = a20.logs :=
    logs.trans (Line.of_inv Devm.logs (by line_inv) h20)
  have memory20 : s.memory = a20.memory :=
    memory.trans (Line.of_inv Devm.memory (by line_inv) h20)
  have foreign20 : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor a20 account = Devm.getStor a19 account :=
    fun _ ne => incrWbal_foreignStorage h20 ne
  have off20 := (incrAt_of_incrWbal dstValid h20
    (pref_trans ⟨[dst, wad, src], rfl⟩ hs19)).right
  clear h20 hs19
  rcases of_run_prepend transferFromLog _ run with ⟨a21, h21, run⟩
  obtain ⟨hs21, emitted⟩ := transferFromLog_effect hs20 h21
  have logStorage : Devm.getStor a20 = Devm.getStor a21 :=
    Line.of_inv Devm.getStor (by line_inv) h21
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
  have tailLogs : a21.logs = r.logs := by
    refine Func.of_inv Devm.logs Devm.logs ?_ run
    unfold updateAllowance
    func_inv
  refine ⟨by simpa only [src, dst, wad] using effect, ?_, ?_, outputTrue, ?_⟩
  · intro account accountNe
    rw [updateAllowance_foreignStorage run accountNe,
      ← congrFun logStorage account, foreign20 account accountNe,
      ← congrFun storage19 account, foreign13 account accountNe,
      ← congrFun storage12 account]
  · rw [← tailLogs, emitted, ← logs20]

  · intro wf
    have wf20 : Mem.Wf a20.memory := memory20 ▸ wf
    have wf21 := (transferFromLog_effect_frame hs20 wf20
      (img := a20.memory.data.toList) (by intro i; simp) h21).2.2.2.2.2.2.1
    refine ⟨a21, ?_, updateAllowance_exact wf21 hs21 run⟩
    exact (Stor.AgreeOffAdr.of_eq (congrFun storage12 sevm.currentTarget)).trans
      (off13.trans ((Stor.AgreeOffAdr.of_eq
        (congrFun storage19 sevm.currentTarget)).trans
          (off20.trans (Stor.AgreeOffAdr.of_eq
            (congrFun logStorage sevm.currentTarget)))))

/-- Exact allowance classification from the compiled transferFrom selector.
Balance writes precede the allowance read, but cannot change its guarded
non-address key. Self-bypass preserves every non-address cell; maximum
allowance is read-only; the finite branch retains the actual decrement write.
No logical pair-separation premise is needed at this raw-key altitude. -/
theorem weth_transferFrom_compiled_allowance_effect
    {sevm : Sevm} {pre post : Devm}
    (wf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.weth post)
    (selected : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]) :
    let key := wethAllowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256
    let allowed := pre.getStorVal sevm.currentTarget key
    if Sevm.argWord sevm 0 = sevm.caller.toB256 then
      Stor.AgreeOffAdr (Devm.getStor pre sevm.currentTarget)
        (Devm.getStor post sevm.currentTarget)
    else ¬ ValidAdr key ∧
      ((allowed = B256.max ∧
        Stor.AgreeOffAdr (Devm.getStor pre sevm.currentTarget)
          (Devm.getStor post sevm.currentTarget)) ∨
       (allowed ≠ B256.max ∧ Sevm.argWord sevm 2 ≤ allowed ∧
        Stor.AgreeOffAdr
          ((Devm.getStor pre sevm.currentTarget).set key (allowed - Sevm.argWord sevm 2))
          (Devm.getStor post sevm.currentTarget) ∧
        ∃ writePre writePost,
          Ninst.Run sevm writePre sstore writePost ∧
          [key, allowed - Sevm.argWord sevm 2] <<+ writePre.stack ∧
          Stor.AgreeOffAdr (Devm.getStor pre sevm.currentTarget)
            (Devm.getStor writePre sevm.currentTarget) ∧
          Devm.getStor post = Devm.getStor writePost)) := by
  obtain ⟨bodyPre, -, entryState, entryMemory, -, -, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable (body := transferFrom) run selected
      (by simp [wethFuncs])
  obtain ⟨allowancePre, off, effect⟩ :=
    (transferFromBody_exactEffect bodyRun).2.2.2.2 (entryMemory ▸ wf)
  have off := (Stor.AgreeOffAdr.of_eq
    (getStor_eq_of_state_eq entryState sevm.currentTarget)).trans off
  dsimp only
  by_cases same : Sevm.argWord sevm 0 = sevm.caller.toB256
  · rw [if_pos same]
    simp only [WethAllowanceUpdateEffect, if_pos same] at effect
    exact off.trans (Stor.AgreeOffAdr.of_eq (congrFun effect.symm sevm.currentTarget))
  · rw [if_neg same]
    simp only [WethAllowanceUpdateEffect, if_neg same] at effect
    obtain ⟨valid, result⟩ := effect
    have read := off _ valid
    change pre.getStorVal sevm.currentTarget _ = allowancePre.getStorVal sevm.currentTarget _ at read
    rw [← read] at result
    refine ⟨valid, ?_⟩
    rcases result with ⟨maximum, silent⟩ | ⟨finite, covered, stored, w, z, write, hp, before, after⟩
    · exact Or.inl ⟨maximum, off.trans
        (Stor.AgreeOffAdr.of_eq (congrFun silent.symm sevm.currentTarget))⟩
    · refine Or.inr ⟨finite, covered, ?_, w, z, write, hp, ?_, after⟩
      · intro k hk
        rw [stored]
        by_cases sameKey : wethAllowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256 = k
        · subst k
          rw [Stor.get_set_self, Stor.get_set_self]
        · rw [Stor.get_set_ne _ sameKey, Stor.get_set_ne _ sameKey]
          exact off k hk
      · exact off.trans (Stor.AgreeOffAdr.of_eq (congrFun before.symm sevm.currentTarget))

/-- The invocation's finite writer filter agrees with its compiled storage
classification. A retained pair writes the stated raw cell; omitted self and
maximum branches preserve all non-address cells. -/
theorem WethAllowanceInvocation.allowance_effect (call : WethAllowanceInvocation) :
    match call.writtenPair? with
    | none => Stor.AgreeOffAdr (Devm.getStor call.pre wethAccount)
        (Devm.getStor call.post wethAccount)
    | some p => ¬ ValidAdr (wethAllowanceKey p.1 p.2) ∧
        Stor.AgreeOffAdr
          ((Devm.getStor call.pre wethAccount).set (wethAllowanceKey p.1 p.2)
            (if call.approval then Sevm.argWord call.sevm 1 else
              call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) -
                Sevm.argWord call.sevm 2))
          (Devm.getStor call.post wethAccount) := by
  cases approval : call.approval with
  | true =>
    have selected := call.selected
    simp only [approval, ↓reduceIte] at selected
    obtain ⟨valid, effect⟩ :=
      weth_approve_compiled_raw_effect call.memoryWf call.run selected
    rw [call.target] at effect
    simp only [writtenPair?, pair?, approval, ↓reduceIte]
    exact ⟨valid, Stor.AgreeOffAdr.of_eq effect.symm⟩
  | false =>
    have selected := call.selected
    simp only [approval, Bool.false_eq_true, ↓reduceIte] at selected
    have effect := weth_transferFrom_compiled_allowance_effect
      call.memoryWf call.run selected
    dsimp only at effect
    rw [call.target] at effect
    by_cases same : Sevm.argWord call.sevm 0 = call.sevm.caller.toB256
    · simpa [writtenPair?, pair?, approval, same] using effect
    · simp only [if_neg same] at effect
      obtain ⟨valid, result⟩ := effect
      rcases result with ⟨maximum, silent⟩ | ⟨finite, covered, stored, witness⟩
      · simpa [writtenPair?, pair?, approval, same, Option.filter, maximum] using silent
      · simpa [writtenPair?, pair?, approval, same, Option.filter, finite] using And.intro valid stored

/-- A retained transferFrom writer is backed by the executed SSTORE, even
when a zero amount leaves its value unchanged. -/
theorem WethAllowanceInvocation.transferFrom_writer_has_sstore
    (call : WethAllowanceInvocation) (approval : call.approval = false)
    {p : B256 × B256} (writer : call.writtenPair? = some p) :
    call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) ≠ B256.max ∧
      Sevm.argWord call.sevm 2 ≤
        call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) ∧
      ∃ writePre writePost,
        Ninst.Run call.sevm writePre sstore writePost ∧
        [wethAllowanceKey p.1 p.2,
          call.pre.getStorVal wethAccount (wethAllowanceKey p.1 p.2) -
            Sevm.argWord call.sevm 2] <<+ writePre.stack ∧
        Stor.AgreeOffAdr (Devm.getStor call.pre wethAccount)
          (Devm.getStor writePre wethAccount) ∧
        Devm.getStor call.post = Devm.getStor writePost := by
  have selected := call.selected
  simp only [approval, Bool.false_eq_true, ↓reduceIte] at selected
  have effect := weth_transferFrom_compiled_allowance_effect
    call.memoryWf call.run selected
  dsimp only at effect
  rw [call.target] at effect
  by_cases same : Sevm.argWord call.sevm 0 = call.sevm.caller.toB256
  · simp [writtenPair?, pair?, approval, same] at writer
  · simp only [if_neg same] at effect
    rcases effect.2 with ⟨maximum, silent⟩ | ⟨finite, covered, stored, witness⟩
    · simp [writtenPair?, pair?, approval, same, Option.filter, maximum] at writer
    · have pairEq : (Sevm.argWord call.sevm 0, call.sevm.caller.toB256) = p := by
        simpa [writtenPair?, pair?, approval, same, Option.filter, finite] using writer
      subst p
      exact ⟨finite, covered, witness⟩

/-- Recover the successful compiled WETH run together with the parent-visible
storage world and log frame.  This is the strong occurrence projection used
by composed read-only endpoints. -/
theorem ExactWethChildSuccess.worldProgramRun
    {parentSevm : Sevm} {parentPre parentPost : Devm}
    {instruction : Ninst} {calldata output : Bytes} {static : Bool}
    (success : ExactWethChildSuccess parentSevm parentPre parentPost
      instruction calldata output static) :
    SuccessfulWethWorldProgramRun parentSevm.currentTarget calldata output
      (Devm.getStor parentPre) (Devm.getStor parentPost)
      parentPre.logs parentPost.logs := by
  unfold ExactWethChildSuccess ExactWethChildExecution at success
  rcases success with ⟨msg, xl, child, pc, nextPc, resume,
    target, executes, childWorld, childRules, spawn, filled, process,
    stepRun, postState, postReturnData, postLogs, statusTail, statusEq,
    childClean⟩
  rcases executes with ⟨uses, childEvm, raw, slotEq, childExec⟩
  subst xl
  obtain ⟨errorNone, childOutput⟩ := childClean
  have clean : child.error.isSome = false := by simp [errorNone]
  obtain ⟨rawPost, rawEq, rawError, settledState, settledOutput⟩ :=
    Blanc.MessageExecution.processMessage_clean_rawPost process clean
  subst raw
  have settleEq := (RunFrame.some_inv process).2
  have settledLogs : child.logs = rawPost.logs := by
    simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
      executeCode.handleError, processMessage.settle, rawError] at settleEq
    exact congrArg Devm.logs settleEq
  obtain ⟨pcZero, codeEq, currentTarget, codeAddress, dataEq, -, storageEq,
    -⟩ := Blanc.MessageExecution.processMessage_entry_facts
      wethAccount process
  have stackEq := Blanc.MessageExecution.processMessage_entry_stack process
  have memoryEq := Blanc.MessageExecution.processMessage_entry_memory process
  have enter := (RunFrame.some_inv process).1
  rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
  have callerEq := congrArg (fun evm : Evm => evm.sta.caller) evmEq
  have valueEq := congrArg (fun evm : Evm => evm.sta.value) evmEq
  have logsEq := congrArg (fun evm : Evm => evm.dyna.logs) evmEq
  dsimp [Jaune.Frame.ofCall, initEvm, initSevm, initDevm, Msg.withBenv]
    at callerEq valueEq logsEq
  have storageWorld : Devm.getStor childEvm.dyna =
      Devm.getStor parentPre := by
    funext owner
    obtain ⟨-, -, -, -, -, -, ownerStorage, -⟩ :=
      Blanc.MessageExecution.processMessage_entry_facts owner process
    exact ownerStorage.trans
      (congrArg (fun state : State => state.getStor owner) childWorld)
  have exactCode : some childEvm.sta.code.toList = Prog.compile Blanc.weth := by
    rw [codeEq]
    exact uses
  obtain ⟨run⟩ := childExec
  rw [pcZero] at run
  have compiled : Prog.RunCompiled childEvm.sta childEvm.dyna Blanc.weth
      rawPost :=
    Prog.runCompiled_of_exec childEvm.sta childEvm.dyna Blanc.weth rawPost
      weth_pcFree run exactCode
  have finalStorage : Devm.getStor parentPost = Devm.getStor rawPost := by
    exact funext (getStor_eq_of_state_eq (postState.trans settledState))
  have childNotError : ¬ child.error.isSome := by
    simpa using clean
  have finalLogs : parentPost.logs = parentPre.logs ++ rawPost.logs := by
    rw [if_neg childNotError, settledLogs] at postLogs
    exact postLogs
  refine ⟨childEvm.sta, childEvm.dyna, rawPost, ?_, ?_, ?_, ?_, ?_,
    stackEq, memoryEq, logsEq, storageWorld, compiled, rawError,
    finalStorage, finalLogs, ?_⟩
  · exact currentTarget.trans target.currentTarget
  · exact codeAddress.trans target.codeAddress
  · exact callerEq.trans target.callerAddress
  · exact valueEq.trans target.valueZero
  · exact dataEq.trans target.data
  · exact settledOutput.symm.trans childOutput

/-- Compatibility projection retaining the established WETH-row interface for
the mutating call effects. -/
theorem ExactWethChildSuccess.programRun
    {parentSevm : Sevm} {parentPre parentPost : Devm}
    {instruction : Ninst} {calldata output : Bytes} {static : Bool}
    (success : ExactWethChildSuccess parentSevm parentPre parentPost
      instruction calldata output static) :
    SuccessfulWethProgramRun parentSevm.currentTarget calldata output
      (parentPre.state.getStor wethAccount)
      (parentPost.state.getStor wethAccount) := by
  rcases ExactWethChildSuccess.worldProgramRun success with
    ⟨childSevm, childPre, rawPost, currentTarget, codeAddress, caller,
      valueZero, dataEq, stackEmpty, memoryEmpty, logsEmpty, initialEq,
      compiled, rawError, finalEq, finalLogs, outputEq⟩
  exact ⟨childSevm, childPre, rawPost, currentTarget, codeAddress, caller,
    valueZero, dataEq, stackEmpty, memoryEmpty,
    congrFun initialEq wethAccount, compiled, rawError,
    congrFun finalEq wethAccount, outputEq⟩

/-! ## Asset-query effect -/

/-- The world-strength balance query: all account storage is unchanged, the
child emits no logs, and the output is the configured vault's exact WETH
balance. -/
theorem SuccessfulWethWorldProgramRun.balanceOf_effect
    {vault : Adr} {output : Bytes} {initial final : Adr → Stor}
    {initialLogs finalLogs : List Log}
    (run : SuccessfulWethWorldProgramRun vault (balanceOfCalldata vault)
      output initial final initialLogs finalLogs) :
    final = initial ∧ finalLogs = initialLogs ∧
      output = ((initial wethAccount).get vault.toB256).toBytes := by
  rcases run with ⟨childSevm, childPre, rawPost,
    currentTarget, codeAddress, caller, valueZero, dataEq, stackEmpty,
    memoryEmpty, childLogs, initialEq, compiled, rawError, finalEq,
    finalLogsEq, outputEq⟩
  obtain ⟨selectorEq, vaultArg⟩ := balanceOfCalldata_facts dataEq
  have member :
      (selector "balanceOf" [.address], nonpayable balanceOf) ∈
        Blanc.wethFuncs := by
    simp [Blanc.wethFuncs]
  obtain ⟨bodyPre, -, entryState, entryMemory, entryLogs,
      entryOutput, bodyRun⟩ :=
    runCompiled_enters_wethNonpayable compiled selectorEq member
  obtain ⟨bodyOutput, bodyStorage⟩ := balanceOfBody_effect bodyRun
  have bodyLogs : bodyPre.logs = rawPost.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold balanceOf
      func_inv) bodyRun
  have entryStorage : Devm.getStor childPre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have finalInitial : final = initial :=
    finalEq.trans
      (bodyStorage.symm.trans (entryStorage.symm.trans initialEq))
  have rawLogsEmpty : rawPost.logs = [] :=
    bodyLogs.symm.trans (entryLogs.symm.trans childLogs)
  have logsInitial : finalLogs = initialLogs := by
    rw [finalLogsEq, rawLogsEmpty, List.append_nil]
  have bodyInitial : Devm.getStor bodyPre wethAccount =
      initial wethAccount :=
    congrFun (entryStorage.symm.trans initialEq) wethAccount
  change rawPost.output =
      ((Devm.getStor bodyPre childSevm.currentTarget).get
        (Sevm.dataWord childSevm 4)).toBytes at bodyOutput
  rw [currentTarget, vaultArg, bodyInitial] at bodyOutput
  exact ⟨finalInitial, logsInitial, outputEq.symm.trans bodyOutput⟩

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

/-- The exact `Transfer(owner, receiver, assets)` entry the configured WETH
program appends on a successful transfer, delegated or direct. -/
def wethTransferLog (owner receiver : Adr) (assets : B256) : Log :=
  ⟨wethAccount, [Blanc.transferEvent, owner.toB256, receiver.toB256],
    assets.toBytes⟩

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
  obtain ⟨movement, offAddress, -, -, bodyOutput⟩ :=
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

/-- World-strength outbound transfer: the exact successful WETH child for
`transfer(receiver,assets)` moves precisely that balance row out of the calling
vault, leaves every account other than the WETH contract with its exact
storage — the calling vault's own share ledger included — appends exactly one
`Transfer` entry, and returns canonical true.  None of the four is a caller
premise; each is read off the selected WETH body.

This is the mirror of `SuccessfulWethWorldProgramRun.transferFrom_effect`.  The
inbound direction takes its source from an ABI word, while here the debited
account is the executing frame's own caller, so the emitted entry names the
vault without any calldata round trip. -/
theorem SuccessfulWethWorldProgramRun.transfer_effect
    {vault receiver : Adr} {assets : B256} {output : Bytes}
    {initial final : Adr → Stor} {initialLogs finalLogs : List Log}
    (run : SuccessfulWethWorldProgramRun vault
      (transferCalldata receiver assets) output initial final
      initialLogs finalLogs) :
    Transfer (Stor.rest (initial wethAccount)) vault assets receiver
        (Stor.rest (final wethAccount)) ∧
      (∀ account, wethAccount ≠ account → final account = initial account) ∧
      finalLogs = initialLogs ++ [wethTransferLog vault receiver assets] ∧
      output = (1 : B256).toBytes := by
  rcases run with ⟨childSevm, childPre, rawPost,
    currentTarget, codeAddress, caller, valueZero, dataEq, stackEmpty,
    memoryEmpty, childLogs, initialEq, compiled, rawError, finalEq,
    finalLogsEq, outputEq⟩
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
  obtain ⟨movement, -, bodyForeign, bodyEmitted, bodyOutput⟩ :=
    transferBody_exactEffect bodyRun
  have entryStorage : Devm.getStor childPre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have bodyInitial : Devm.getStor bodyPre wethAccount = initial wethAccount :=
    (congrFun entryStorage wethAccount).symm.trans
      (congrFun initialEq wethAccount)
  have bodyFinal : Devm.getStor rawPost wethAccount = final wethAccount :=
    (congrFun finalEq wethAccount).symm
  rw [currentTarget, caller, receiverWord, assetsWord, bodyInitial,
    bodyFinal] at movement
  have foreign : ∀ account, wethAccount ≠ account →
      final account = initial account := by
    intro account accountNe
    rw [congrFun finalEq account]
    rw [bodyForeign account (by rw [currentTarget]; exact accountNe),
      ← congrFun entryStorage account, congrFun initialEq account]
  have entryEq : transferLogEntry childSevm childSevm.caller.toB256
      (Sevm.argWord childSevm 0) (Sevm.argWord childSevm 1) =
      wethTransferLog vault receiver assets := by
    unfold transferLogEntry wethTransferLog
    rw [currentTarget, caller, receiverWord, assetsWord]
  have logged : finalLogs = initialLogs ++
      [wethTransferLog vault receiver assets] := by
    rw [finalLogsEq, bodyEmitted, ← entryLogs, childLogs, List.nil_append,
      entryEq]
  exact ⟨by simpa only [toAdr_toB256] using movement, foreign, logged,
    outputEq.symm.trans bodyOutput⟩

/-! ## Delegated transfer effect -/

/-- World-strength delegated transfer: the exact successful WETH child for
`transferFrom(owner,vault,assets)` moves precisely that balance row, leaves
every account other than the WETH contract with its exact storage — the
calling vault's own ledger included — appends exactly one `Transfer` entry,
and returns canonical true.  None of the four is a caller premise. -/
theorem SuccessfulWethWorldProgramRun.transferFrom_effect
    {vault owner : Adr} {assets : B256} {output : Bytes}
    {initial final : Adr → Stor} {initialLogs finalLogs : List Log}
    (run : SuccessfulWethWorldProgramRun vault
      (transferFromCalldata owner vault assets) output initial final
      initialLogs finalLogs) :
    Transfer (Stor.rest (initial wethAccount)) owner assets vault
        (Stor.rest (final wethAccount)) ∧
      (∀ account, wethAccount ≠ account → final account = initial account) ∧
      finalLogs = initialLogs ++ [wethTransferLog owner vault assets] ∧
      output = (1 : B256).toBytes := by
  rcases run with ⟨childSevm, childPre, rawPost,
    currentTarget, codeAddress, caller, valueZero, dataEq, stackEmpty,
    memoryEmpty, childLogs, initialEq, compiled, rawError, finalEq,
    finalLogsEq, outputEq⟩
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
  obtain ⟨movement, bodyForeign, bodyEmitted, bodyOutput, -⟩ :=
    transferFromBody_exactEffect bodyRun
  have entryStorage : Devm.getStor childPre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have bodyInitial : Devm.getStor bodyPre wethAccount = initial wethAccount :=
    (congrFun entryStorage wethAccount).symm.trans
      (congrFun initialEq wethAccount)
  have bodyFinal : Devm.getStor rawPost wethAccount = final wethAccount :=
    (congrFun finalEq wethAccount).symm
  rw [currentTarget, ownerWord, vaultWord, assetsWord, bodyInitial,
    bodyFinal] at movement
  have foreign : ∀ account, wethAccount ≠ account →
      final account = initial account := by
    intro account accountNe
    rw [congrFun finalEq account]
    rw [bodyForeign account (by rw [currentTarget]; exact accountNe),
      ← congrFun entryStorage account, congrFun initialEq account]
  have entryEq : transferLogEntry childSevm (Sevm.argWord childSevm 0)
      (Sevm.argWord childSevm 1) (Sevm.argWord childSevm 2) =
      wethTransferLog owner vault assets := by
    unfold transferLogEntry wethTransferLog
    rw [currentTarget, ownerWord, vaultWord, assetsWord]
  have logged : finalLogs = initialLogs ++
      [wethTransferLog owner vault assets] := by
    rw [finalLogsEq, bodyEmitted, ← entryLogs, childLogs, List.nil_append,
      entryEq]
  exact ⟨by simpa only [toAdr_toB256] using movement, foreign, logged,
    outputEq.symm.trans bodyOutput⟩

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
  obtain ⟨movement, -, -, bodyOutput, -⟩ := transferFromBody_exactEffect bodyRun
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
