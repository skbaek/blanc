import Blanc.Weth10AllowanceArmsRedeem

/-!
The flash-loan arm of the allowance-region transport.

`flashLoan` is the one dispatched selector whose own attribution record is
placed *after* its descendant stream: the runtime settles the repayment
allowance only once the borrower's callback has returned, and the canonical
repayment pattern grants that allowance inside the callback.  Its counted
contribution is therefore `inner ++ [own]` rather than `own :: inner`, and the
region transport splits at the post-callback settlement state — the
pre-callback prefix together with the borrower subtree carries `inner`, and
the settlement plus its shared burn continuation carries the single own
record.

The semantic heart of the arm is the post-state reconstruction: the committed
post state alone determines which settlement arm the runtime took, because the
burn continuation leaves the tagged repayment cell exactly as settlement wrote
it.  Reading `B256.max` there means the infinite-allowance arm ran and wrote
nothing; any other word `after` means the finite arm reduced an entry
allowance of exactly `after + amount`, the reconstruction `after + amount`
being exact precisely because the finite arm is guarded by
`amount ≤ allowance`.

Three pieces of that transport are established here.

* `flashSettlement_allowanceLedger` /
  `flashSettlement_allowanceRegionEffect` are the settlement segment: from the
  post-callback settlement state to the committed post state, the region moves
  by exactly the frame's own single counted record, read off the committed
  post state by `flashSettlement_reconstruction`.
* `Exec.Frame.attributionInner_eq_callback_of_flashLoan` is the bridge from
  the action-labelled flash chronology to the counted ledger: the whole
  proper-descendant counted stream of an authentic committed `flashLoan` frame
  is the attribution stream of its single retained borrower callback.  Every
  source instruction before that callback is childless and every alternate
  branch arm is a fixed nonreturning reverter, and the post-callback decoder,
  the settlement and the burn continuation likewise cross no recursive child.
* `Exec.Frame.flashCallbackAndSettlement` adds the settlement handoff: the
  settlement phase starts from exactly the storage the callback committed.

What is still open is the pre-callback prefix's own allowance-region
locality, the borrower message's `ProcessMessageTrace` data at the callback
boundary, and the memory image at the settlement entry that pins the hashed
repayment key.  All three need the callback boundary's stack and memory
witnesses, which currently live only inside
`Weth10HolderFlowFlashChronology`'s private compiled-cursor walk.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## The post-callback settlement fork -/

/-- Settlement and its burn continuation move no tagged allowance key other
than the runtime repayment cell: the settlement's only write is at that cell,
and the burn writes address-shaped balance keys and the flash counter. -/
private theorem flashSettlement_region_locality
    {dp : DeployParams} {e : Sevm} {settlePre burnPre post : Devm}
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post)
    {key : B256} (hkey : InRegion .allowance key)
    (hne : flashAllowanceRuntimeKey e ≠ key) :
    (Devm.getStor post e.currentTarget).get key =
      (Devm.getStor settlePre e.currentTarget).get key := by
  rw [flashBurn_storage_get_of_not_valid dp key
    (allowanceRegion_not_valid hkey) (allowanceRegion_ne_flashSlot hkey)
    hburn]
  rcases houtcome.1 with hmax | hfinite
  · rw [hmax.2.1]
  · rcases hfinite with ⟨_allowance, _hnotmax, _hle, _hread, hwrite, _hlogs⟩
    rw [hwrite, Stor.get_set_ne _ hne]

/-! ## Local copies of the compiled flash body

`Weth10HolderFlowFlashChronology` publishes its decomposition of the flash
body, its post-callback decoder, the settlement and the burn continuation,
so this module consumes those directly.  Only the reverter-arm exclusion it
phrases in terms of `Func.revertWith` is local. -/

/-! ## The childless prefix before the borrower callback

Every source instruction the flash body executes before the borrower `CALL`
is childless, and every alternate branch arm is a fixed nonreturning
reverter, so a counted cursor reaches the callback with an exactly empty
counted prefix. -/

/-- Reach the borrower callback from the public `flashLoan` body while
preserving the empty counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.reachFlashLoanSuccessTailCursor`. -/
private theorem Exec.Frame.CountedCursor.reachFlashCallback
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashLoan final) :
    Nonempty (Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      flashLoanSuccessTail final) := by
  rw [flashLoan_shape] at cursor
  unfold flashLoanBodyShape at cursor
  rcases cursor.peelChildlessLine (line := flashTokenLine) (by
      simp [flashTokenLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨tokenBranchCursor, _htoken⟩
  rcases tokenBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revertWith (flashTokenError_lookup dp)) with
    ⟨amountCursor, -⟩
  unfold flashLoanPostAmount at amountCursor
  rcases amountCursor.peelChildlessLine (line := flashAmountLine) (by
      simp [flashAmountLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨amountBranchCursor, _hamount⟩
  rcases amountBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revertWith (individualLimitError_lookup dp)) with
    ⟨counterCursor, -⟩
  unfold flashLoanPostCounter at counterCursor
  rcases counterCursor.peelChildlessLine (line := flashCounterLine) (by
      simp [flashCounterLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalCursor, _hcounter⟩
  rcases totalCursor.peelChildlessLine (line := flashTotalLine) (by
      simp [flashTotalLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalBranchCursor, _htotal⟩
  rcases totalBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revertWith (totalLimitError_lookup dp)) with
    ⟨popCursor, -⟩
  unfold flashLoanPostTotal at popCursor
  rcases popCursor.peelChildlessLine (line := [Ninst.pop])
      (by simp [NinstIsChildless]) with
    ⟨mintCursor, _hpop⟩
  rcases mintCursor.peelChildlessLine (line := flashMintLine) (by
      simp [flashMintLine, addressArg, normalizeAddress, pushAddressMask,
        arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨eventCursor, _hmint⟩
  rcases eventCursor.peelChildlessLine (line := flashEventCheckLine) (by
      simp [flashEventCheckLine, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨codeBranchCursor, _hevent⟩
  rcases codeBranchCursor.selectBranchLeftWithBurn
      (fun _ => not_run_revert) with
    ⟨setupCursor, -⟩
  unfold flashLoanPostCode at setupCursor
  rcases setupCursor.peelChildlessLine (line := flashCallbackSetupLine)
      (by
        simp [flashCallbackSetupLine, storeFlashCallbackHead, mstoreAt,
          pushList, forwardArgTail, arg, cdl, flashCallbackArgsSize,
          NinstIsChildless, Ninst.pushB256]) with
    ⟨callCursor, _hsetup⟩
  exact ⟨callCursor⟩

/-! ## The parent-only suffix after the borrower callback

Everything the frame executes after the callback returns is childless source
code, generated branch glue, internal table jumps, and fixed nonreturning
reverters, so it contributes no counted record. -/

/-- The shared burn continuation crosses no recursive child. -/
private theorem Exec.Frame.CountedCursor.finishFlashBurn
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashBurn final) :
    Exec.attributionInner dp ca frame.run = [] := by
  rw [flashBurn_shape] at cursor
  rcases cursor.peelChildlessLine (line := flashBurnGuardLine) (by
      simp [flashBurnGuardLine, loadArgBalanceAmount, balanceTooSmall,
        addressArg, normalizeAddress, arg, cdl, pushAddressMask,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, _hguard⟩
  rcases branchCursor.selectBranchLeftWithBurn
      (not_run_call_revertWith (burnBalanceError_lookup dp)) with
    ⟨successCursor, -⟩
  rcases successCursor.peelChildlessLine (line := flashBurnSuccessLine) (by
      simp [flashBurnSuccessLine, debitLoadedBalance, addressArg,
        normalizeAddress, pushAddressMask, arg, cdl, emitTransfer,
        Blanc.transferFromLog, mstoreAt, logWith, pushList,
        pushFlashMintedSlot, NinstIsChildless, Ninst.pushB256]) with
    ⟨lastCursor, _hsuccess⟩
  exact lastCursor.finishAttributionInner

/-- Settlement reaches the unique shared burn continuation through either
allowance arm, and neither arm crosses a recursive child. -/
private theorem Exec.Frame.CountedCursor.finishFlashSettle
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashSettle final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    Exec.attributionInner dp ca frame.run = [] := by
  rw [flashSettle_shape] at cursor
  rcases cursor.peelChildlessLine (line := flashSettleKeyLine) (by
      simp [flashSettleKeyLine, addressArg, normalizeAddress,
        pushAddressMask, arg, cdl, mstoreAt, allowanceKeyFromMemory,
        pushList, isMax, NinstIsChildless, Ninst.pushB256]) with
    ⟨allowanceBranchCursor, _hkeyLine⟩
  rcases allowanceBranchCursor.selectBranchSplit with hfinite | hmax
  · rcases hfinite with ⟨finiteCursor⟩
    rcases finiteCursor.peelChildlessLine (line := flashSettleGuardLine) (by
        simp [flashSettleGuardLine, arg, cdl, balanceTooSmall,
          NinstIsChildless, Ninst.pushB256]) with
      ⟨guardBranchCursor, _hguard⟩
    rcases guardBranchCursor.selectBranchLeftWithBurn
        (not_run_call_revertWith (allowanceError_lookup dp)) with
      ⟨successCursor, -⟩
    rcases successCursor.peelChildlessLine
        (line := flashSettleFiniteLine) (by
          simp [flashSettleFiniteLine, emitFlashApproval, arg, cdl,
            mstoreAt, logWith, NinstIsChildless, Ninst.pushB256]) with
      ⟨burnCallCursor, _hfiniteLine⟩
    obtain ⟨body, hget, ⟨burnCursor⟩⟩ := burnCallCursor.enterCall hcode
    have hbody : body = flashBurn := by
      simpa [weth10, weth10Aux, flashBurnSlot] using hget.symm
    subst body
    exact burnCursor.finishFlashBurn
  · rcases hmax with ⟨maxCursor⟩
    rcases maxCursor.peelChildlessLine (line := [Ninst.pop, Ninst.pop])
        (by simp [NinstIsChildless]) with
      ⟨burnCallCursor, _hpops⟩
    obtain ⟨body, hget, ⟨burnCursor⟩⟩ := burnCallCursor.enterCall hcode
    have hbody : body = flashBurn := by
      simpa [weth10, weth10Aux, flashBurnSlot] using hget.symm
    subst body
    exact burnCursor.finishFlashBurn

/-- The successful decoder and repayment suffix after the borrower callback
crosses no further recursive child. -/
private theorem Exec.Frame.CountedCursor.finishFlashLoanAfterCallback
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      flashLoanAfterCallback final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    Exec.attributionInner dp ca frame.run = [] := by
  unfold flashLoanAfterCallback at cursor
  rcases cursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨callbackBranchCursor, _hiszero⟩
  have hbubble : ∀ pre, ¬ Func.Run ((weth10 dp).main :: weth10Aux)
      frame.sevm pre (.call bubbleRevertSlot) final := by
    intro pre run
    rcases of_run_call run with ⟨body, bodyPre, hbody, _hburn, hrun⟩
    have hlookup : ((weth10 dp).main :: weth10Aux)[bubbleRevertSlot]? =
        some bubbleRevert := by
      simp [weth10, weth10Aux, bubbleRevertSlot]
    rw [hlookup] at hbody
    have heq : body = bubbleRevert := Option.some.inj hbody.symm
    subst body
    exact not_run_bubbleRevert hrun
  rcases callbackBranchCursor.selectBranchLeftWithBurn hbubble with
    ⟨decodeCursor, -⟩
  rcases decodeCursor.peelChildlessLine (line := returnDataShorterThan 32)
      (by simp [returnDataShorterThan, NinstIsChildless, Ninst.pushB256]) with
    ⟨lengthBranchCursor, _hlength⟩
  rcases lengthBranchCursor.selectBranchLeftWithBurn
      (fun _ => not_run_revert) with
    ⟨magicCursor, -⟩
  rcases magicCursor.peelChildlessLine
      (line := checkReturnDataHead CALLBACK_SUCCESS 0 ++ [Ninst.iszero]) (by
        simp [checkReturnDataHead, pushList, NinstIsChildless,
          Ninst.pushB256]) with
    ⟨magicBranchCursor, _hmagicLine⟩
  rcases magicBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revertWith (flashFailedError_lookup dp)) with
    ⟨settlePrefixCursor, -⟩
  rcases settlePrefixCursor.peelChildlessLine
      (line := [Ninst.pop, Ninst.pop]) (by simp [NinstIsChildless]) with
    ⟨settleCallCursor, _hpops⟩
  obtain ⟨body, hget, ⟨settleCursor⟩⟩ := settleCallCursor.enterCall hcode
  have hbody : body = flashSettle := by
    simpa [weth10, weth10Aux, flashSettleSlot] using hget.symm
  subst body
  exact settleCursor.finishFlashSettle hcode

/-! ## The counted skeleton of a flash frame -/

/-- Cross the borrower callback `CALL` from a counted cursor at the
successful callback suffix.  The counted prefix reaching that cursor is
exactly empty and the post-callback decoder, settlement and burn
continuation cross no recursive child, so the frame's entire
proper-descendant counted stream is the retained callback child's
attribution stream. -/
private theorem Exec.Frame.CountedCursor.crossFlashCallback
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (callCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      flashLoanSuccessTail frame.post)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    ∃ (callPost : Devm) (pc : Nat) (xl : Xlot) (retained : RetainedXlot xl),
      Ninst.At frame.sevm.code pc Ninst.call ∧
      Xlot.Filled xl ∧
      Ninst.StepRun pc frame.sevm callCursor.pre Ninst.call xl
        (.ok callPost) ∧
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca := by
  have hsub : subcode frame.sevm.code.toList callCursor.pc
      (Func.compile (table 0 ((weth10 dp).main :: weth10Aux)) callCursor.pc
        (Ninst.call ::: flashLoanAfterCallback)) := callCursor.codeSlice
  have hrunShape : Func.RunCompiled ((weth10 dp).main :: weth10Aux)
      frame.sevm callCursor.pre (Ninst.call ::: flashLoanAfterCallback)
      frame.post := callCursor.run
  rcases frame with ⟨fpc, e, fpre, fout, frun, fcommitted⟩
  cases fout with
  | error err => simp [Execution.commits] at fcommitted
  | ok fpost =>
      cases hrunShape with
      | next hcompiled htailCompiled =>
          rename_i midD
          have hat : Ninst.At e.code callCursor.pc Ninst.call :=
            ninstAt_of_subcode_next hsub
          obtain ⟨nextBoundary, nextSub⟩ :=
            Func.noPushBefore_next hsub callCursor.codeBoundary
          rcases callCursor.parentPrefix with ⟨actionsBefore, hbefore⟩
          rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next
              (frame := ⟨fpc, e, fpre, .ok fpost, frun, fcommitted⟩)
              callCursor.current hbefore hat hcompiled with
            ⟨xl, continuation, selected, occurrence, hedge, _hnextPrefix⟩
          rcases hedge.exists_counted with ⟨counted, hcountedEdge⟩
          rcases occurrence with
            ⟨_opc, _ocurrent, _ocont, _obefore, _oselected, _oprefix, _oat,
              ofilled, ostep, _oprec, _oedge⟩
          have hstepAt : Ninst.StepRun callCursor.pc e callCursor.pre
              Ninst.call xl (.ok midD) :=
            Ninst.stepRun_pc_irrel (pc' := callCursor.pc)
              (by simp [Ninst.pcFree]) ostep
          obtain ⟨retained⟩ := exists_retainedXlot_of_filled ofilled
          have htailNil : Exec.attributionInner dp ca continuation = [] := by
            let tailFrame : Exec.Frame :=
              ⟨callCursor.pc + Ninst.call.size, e, midD, .ok fpost,
                continuation, fcommitted⟩
            let tailCursor :
                Blanc.Weth10.Exec.Frame.CountedCursor
                  (frame := tailFrame) dp ca
                  ((weth10 dp).main :: weth10Aux)
                  (table 0 ((weth10 dp).main :: weth10Aux))
                  flashLoanAfterCallback fpost :=
              ⟨callCursor.pc + Ninst.call.size, midD, continuation,
                ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
                Exec.Deriv.ParentPrefixCounted.refl _, htailCompiled,
                nextSub, nextBoundary⟩
            exact tailCursor.finishFlashLoanAfterCallback hcode
          have hprefixSplit := callCursor.countedPrefix.descendantCounted_eq
          change Exec.attributionInner dp ca frun =
            [] ++ Exec.attributionInner dp ca callCursor.current
              at hprefixSplit
          have hedgeSplit := hcountedEdge.descendantCounted_eq
          change Exec.attributionInner dp ca callCursor.current =
            counted ++ Exec.attributionInner dp ca continuation
              at hedgeSplit
          have hcountedEq :=
            Exec.Deriv.ParentStepCounted.selected_eq_retained_of_call
              hat ofilled hstepAt retained hcountedEdge
          refine ⟨midD, callCursor.pc, xl, retained, hat, ofilled,
            hstepAt, ?_⟩
          rw [hprefixSplit, List.nil_append, hedgeSplit, hcountedEq,
            htailNil, List.append_nil]

/-- An authentic committed `flashLoan` frame crosses exactly one recursive
child — the borrower callback — and its entire proper-descendant counted
stream is that child's attribution stream.  This is the bridge from the
action-labelled flash chronology to the counted ledger. -/
theorem Exec.Frame.attributionInner_eq_callback_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ (callPre callPost : Devm) (pc : Nat) (xl : Xlot)
        (retained : RetainedXlot xl),
      Ninst.At frame.sevm.code pc Ninst.call ∧
      Xlot.Filled xl ∧
      Ninst.StepRun pc frame.sevm callPre Ninst.call xl (.ok callPost) ∧
      Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm callPre
        flashLoanSuccessTail frame.post ∧
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca := by
  have hmember :
      (Sevm.selector frame.sevm, nonpayable flashLoan) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [flashLoanSelector, weth10Funcs]
  have hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp) :=
    context.invocation.2.2.2
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCounted (frame := frame) context hnonempty hmember
    with ⟨wrapperCursor⟩
  rcases wrapperCursor.enterNonpayable with ⟨bodyCursor⟩
  rcases bodyCursor.reachFlashCallback with ⟨callCursor⟩
  obtain ⟨callPost, pc, xl, retained, hat, hfilled, hstep, hinner⟩ :=
    callCursor.crossFlashCallback hcode
  exact ⟨callCursor.pre, callPost, pc, xl, retained, hat, hfilled, hstep,
    Func.Run.of_runCompiled callCursor.run, hinner⟩

/-- The counted skeleton together with the settlement handoff: the borrower
callback is the frame's only recursive child, and the post-callback
settlement phase starts from exactly the storage the callback committed.
Neither the stack image at the callback boundary nor any memory invariant is
needed for this step. -/
theorem Exec.Frame.flashCallbackAndSettlement
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ (callPre callPost settlePre : Devm) (pc : Nat) (xl : Xlot)
        (retained : RetainedXlot xl),
      Ninst.At frame.sevm.code pc Ninst.call ∧
      Xlot.Filled xl ∧
      Ninst.StepRun pc frame.sevm callPre Ninst.call xl (.ok callPost) ∧
      Devm.getStor callPost = Devm.getStor settlePre ∧
      Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm settlePre
        flashSettle frame.post ∧
      Exec.attributionInner dp ca frame.run =
        retained.attributionStream dp ca := by
  obtain ⟨callPre, callPost, pc, xl, retained, hat, hfilled, hstep,
      hcallFunc, hinner⟩ :=
    Blanc.Weth10.Exec.Frame.attributionInner_eq_callback_of_flashLoan (frame := frame) context hselector
      hnonempty
  obtain ⟨sf, settlePre, hcall, hsettle, hstor, _hbal⟩ :=
    of_run_flashLoanFromCall dp
      (show Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm callPre
        flashLoanFromCall frame.post from hcallFunc)
  rcases hcall with ⟨xlCall, hfilledCall, pcCall, hstepCall⟩
  have halign := Ninst.StepRun.unique_exec_of_filled hfilled hfilledCall
    hstep hstepCall
  have hpost : callPost = sf := Except.ok.inj halign.2
  subst sf
  exact ⟨callPre, callPost, settlePre, pc, xl, retained, hat, hfilled,
    hstep, hstor, hsettle, hinner⟩

/-! ## The settlement segment

Replaying the frame's own counted record over the post-callback settlement
entry storage is exactly the settlement's effect on the tagged allowance
region. -/

/-- The settlement segment transports the tagged allowance region by exactly
the frame's own counted record: the record's projected key is the runtime
repayment cell, and its reconstructed visit writes precisely the word the
committed post state holds there. -/
theorem flashSettlement_allowanceLedger
    {dp : DeployParams} {e : Sevm} {pre settlePre burnPre post : Devm}
    (hne0 : e.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector e = flashLoanSelector)
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post)
    {record : CountedFrame}
    (hrecord : record.allowance = frameAllowanceEvent e pre post)
    {key : B256} (hkey : InRegion .allowance key) :
    (Devm.getStor post e.currentTarget).get key =
      applyAllowanceLedger (Devm.getStor settlePre e.currentTarget)
        [record] key := by
  have haccept := flashSettlement_reconstruction houtcome hburn
  rw [applyAllowanceLedger_singleton, hrecord]
  by_cases hafter : (Devm.getStor post e.currentTarget).get
      (flashAllowanceRuntimeKey e) = B256.max
  · have hbranch : flashAllowanceBranchFromPost e post =
        .maximum (flashAllowanceRuntimeKey e) := by
      simp [flashAllowanceBranchFromPost, hafter]
    rw [hbranch] at haccept
    obtain ⟨_hkeyEq, hsettleMax⟩ := haccept.2
    have hevent : frameAllowanceEvent e pre post =
        some { owner := normalizedAddressArg e 0
               spender := e.currentTarget.toB256
               caller := e.caller
               depth := e.depth
               visit := .flashMax } := by
      simp [frameAllowanceEvent, hne0, hsel,
        flashLoanSelector_ne_approveSelector,
        flashLoanSelector_ne_approveAndCallSelector,
        flashLoanSelector_ne_permitSelector,
        flashLoanSelector_ne_transferFromSelector,
        flashLoanSelector_ne_withdrawFromSelector, hafter]
    rw [hevent]
    simp only [AllowanceVisit.written?, ite_self]
    by_cases hkeyEq : flashAllowanceRuntimeKey e = key
    · rw [← hkeyEq, hafter, hsettleMax]
    · exact flashSettlement_region_locality houtcome hburn hkey hkeyEq
  · have hevent : frameAllowanceEvent e pre post =
        some { owner := normalizedAddressArg e 0
               spender := e.currentTarget.toB256
               caller := e.caller
               depth := e.depth
               visit := .flashFinite
                 ((Devm.getStor post e.currentTarget).get
                   (flashAllowanceRuntimeKey e) + Sevm.argWord e 2)
                 ((Devm.getStor post e.currentTarget).get
                   (flashAllowanceRuntimeKey e)) } := by
      simp [frameAllowanceEvent, hne0, hsel,
        flashLoanSelector_ne_approveSelector,
        flashLoanSelector_ne_approveAndCallSelector,
        flashLoanSelector_ne_permitSelector,
        flashLoanSelector_ne_transferFromSelector,
        flashLoanSelector_ne_withdrawFromSelector, hafter]
    rw [hevent]
    simp only [AllowanceEvent.key, AllowanceVisit.written?]
    by_cases hkeyEq :
        projectedAllowanceKey (normalizedAddressArg e 0)
          e.currentTarget.toB256 = key
    · rw [if_pos hkeyEq, ← hkeyEq, ← flashAllowanceRuntimeKey_eq_projected]
    · rw [if_neg hkeyEq]
      refine flashSettlement_region_locality houtcome hburn hkey ?_
      rw [flashAllowanceRuntimeKey_eq_projected]
      exact hkeyEq

/-- Carrier-level form of the settlement segment: the post-callback
settlement together with the shared burn continuation transports the tagged
allowance region by the single-record ledger of the frame's own counted
contribution.  The installed-code witness is the settlement chronology's own
`getCode` equality, which the burn continuation already carries. -/
theorem flashSettlement_allowanceRegionEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {pre settlePre burnPre post : Devm}
    (htarget : e.currentTarget = ca)
    (hne0 : e.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector e = flashLoanSelector)
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post)
    (hcode : Devm.getCode settlePre = Devm.getCode post)
    {record : CountedFrame}
    (hrecord : record.allowance = frameAllowanceEvent e pre post) :
    AllowanceRegionEffect ca settlePre post [record] := by
  subst htarget
  exact ⟨fun key hkey =>
    flashSettlement_allowanceLedger hne0 hsel houtcome hburn hrecord hkey,
    congrFun hcode e.currentTarget⟩

/-! ## The borrower subtree segment -/

/-- The parent instruction step retained by a raw flash callback boundary. -/
private theorem RawFlashCallbackStepBoundary.exists_step
    {sevm : Sevm} {self receiver : Adr} {amount inputSize : B256}
    {callbackInput : Bytes} {pre mid : Devm}
    (h : RawFlashCallbackStepBoundary sevm self receiver amount inputSize
      callbackInput pre mid) :
    ∃ (xl : Xlot) (pc : Nat), Xlot.Filled xl ∧
      Ninst.StepRun pc sevm pre Ninst.call xl (.ok mid) := by
  rcases h with
    ⟨_parent, _child, xl, _delegated, _na, _code, _gasWord, _avail, pc,
      hstep, _hdepth, _hstack, _hpref, _hparentState, _hparentMemory,
      _hparentLogs, _hparentOutput, _hdelegation, hfilled, _hprocess,
      _hclean, _hlength, _hmagic, _hresume, _hmidState, _hreturnData,
      _hmidStack, _hmidLogs, _hmidOutput⟩
  exact ⟨xl, pc, hfilled, hstep⟩

/-- The borrower callback transports the tagged allowance region by exactly
its own retained attribution stream, and its resume writes no storage. -/
private theorem RawFlashCallbackStepBoundary.allowanceRegionEffect
    {dp : DeployParams} {ca : Adr} {sevm : Sevm} {receiver : Adr}
    {amount inputSize : B256} {callbackInput : Bytes} {pre mid : Devm}
    {xl : Xlot} {pc : Nat}
    (boundary : RawFlashCallbackStepBoundary sevm sevm.currentTarget
      receiver amount inputSize callbackInput pre mid)
    (retained : RetainedXlot xl)
    (hfilled : Xlot.Filled xl)
    (hstep : Ninst.StepRun pc sevm pre Ninst.call xl (.ok mid))
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt sevm.depth ca (weth10 dp)
      (fun p s d out _ => Exec.CoreAllowanceSound dp ca p s d out)) :
    AllowanceRegionEffect ca pre mid
      (retained.attributionStream dp ca) := by
  rcases boundary with
    ⟨parent, child, xlRaw, delegated, na, code, gasWord, avail, pcRaw,
      hrawStep, hdepth, _hstack, _hpref, hparentState, _hparentMemory,
      _hparentLogs, _hparentOutput, hdelegation, hrawFilled, hprocess,
      _hclean, _hlength, _hmagic, _hresume, hmidState, _hreturnData,
      _hmidStack, _hmidLogs, _hmidOutput⟩
  have halign := Ninst.StepRun.unique_exec_of_filled hfilled hrawFilled
    hstep hrawStep
  cases halign.1
  let msg : Msg :=
    callMsg sevm parent (min gasWord.toNat (except64th avail)) 0
      sevm.currentTarget receiver na true false callbackInput code
      delegated
  have hparent : pre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < sevm.depth := by
    dsimp only [msg, callMsg]
    omega
  have hdelegation' :
      (getDelegatedCodeAddress (pre.getCode receiver) = none ∧
          code = pre.getCode receiver ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (pre.getCode receiver) =
          some delegatedTarget ∧
        code = pre.getCode delegatedTarget ∧ delegated = true) := by
    rcases hdelegation with ⟨hnone, _, hcode, hdel⟩ |
      ⟨delegatedTarget, hsome, _, hcode, hdel⟩
    · exact Or.inl ⟨hnone, hcode, hdel⟩
    · exact Or.inr ⟨delegatedTarget, hsome, hcode, hdel⟩
  have hresolved : receiver = ca → na = ca := by
    intro hreceiver
    have hnone :
        getDelegatedCodeAddress (pre.getCode receiver) = none := by
      rw [hreceiver]
      dsimp only [getDelegatedCodeAddress]
      rw [if_neg (not_delegation_of_compile installed)]
    rcases hdelegation with ⟨_, hna, _, _⟩ | ⟨_, hsome, _, _, _⟩
    · exact hna.trans hreceiver
    · simp [hnone] at hsome
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro hct
    have htargetCa : receiver = ca := by
      simpa only [msg, callMsg] using hct
    exact callbackCode_eq_compiled_of_target_eq installed htargetCa
      hdelegation'
  have htargetDirect :
      msg.currentTarget = ca → msg.codeAddress = some ca := by
    intro hct
    have htargetCa : receiver = ca := by
      simpa only [msg, callMsg] using hct
    simp only [msg, callMsg, hresolved htargetCa]
  have hchild :=
    ProcessMessageTrace.allowanceRegionDelta_of_forallDeeperAt
      (dp := dp) (ca := ca) (depth := sevm.depth) (parent := pre)
      ⟨xl, retained, by simpa only [msg] using hprocess⟩
      hparent hmsgDepth installed htargetCode htargetDirect hdeeper
  have hresumeEffect : AllowanceRegionEffect ca child mid [] :=
    AllowanceRegionEffect.of_getStorCode_eq
      (congrArg (fun state : State => state.getStor ca) hmidState).symm
      (congrArg (fun state : State => state.getCode ca) hmidState).symm
  simpa only [List.append_nil] using hchild.append hresumeEffect

/-! ## The witnessed callback entry

`Weth10HolderFlowFlashChronology` states the effect of the flash body's
childless prefix over the machine states its source lines relate, so the
counted walk consumes exactly the same content the action-labelled walk
does: the callback `CALL` operand stack, the callback memory image, and the
prefix's storage locality away from the minted balance key and the flash
counter. -/

/-- Reach the borrower callback from the public `flashLoan` body with the
callback boundary's stack, memory and prefix-locality witnesses attached,
while preserving the empty counted prefix. -/
private theorem Exec.Frame.CountedCursor.reachFlashCallbackWitnessed
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashLoan frame.post)
    (hwfEntry : Mem.Wf cursor.pre.memory)
    (hreadsEntry : Mem.Reads cursor.pre.memory []) :
    ∃ (gasWord : B256) (callCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        flashLoanSuccessTail frame.post),
      gasWord :: (normalizedAddressArg frame.sevm 0).toAdr.toB256 ::
        (0 : B256) :: callbackArgsOffset ::
        flashCallbackRuntimeSize frame.sevm :: (0 : B256) ::
        (0 : B256) ::
        [Sevm.argWord frame.sevm 2,
          (normalizedAddressArg frame.sevm 0).toAdr.toB256] <<+
        callCursor.pre.stack ∧
      Mem.Wf callCursor.pre.memory ∧
      Mem.Reads callCursor.pre.memory
        (flashCallbackRuntimeImage frame.sevm []) ∧
      Devm.getCode cursor.pre = Devm.getCode callCursor.pre ∧
      ∀ k : B256, ¬ ValidAdr k → k ≠ flashMintedSlot →
        (Devm.getStor callCursor.pre frame.sevm.currentTarget).get k =
          (Devm.getStor cursor.pre frame.sevm.currentTarget).get k := by
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    flashLoanBodyShape frame.post at cursor
  unfold flashLoanBodyShape at cursor
  rcases cursor.peelChildlessLine (line := flashTokenLine) (by
      simp [flashTokenLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨tokenBranchCursor, htoken⟩
  rcases tokenBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revertWith (flashTokenError_lookup dp)) with
    ⟨amountCursor, htokenPop⟩
  unfold flashLoanPostAmount at amountCursor
  rcases amountCursor.peelChildlessLine (line := flashAmountLine) (by
      simp [flashAmountLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨amountBranchCursor, hamount⟩
  rcases amountBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revertWith (individualLimitError_lookup dp)) with
    ⟨counterCursor, hamountPop⟩
  unfold flashLoanPostCounter at counterCursor
  rcases counterCursor.peelChildlessLine (line := flashCounterLine) (by
      simp [flashCounterLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalCursor, hcounter⟩
  rcases totalCursor.peelChildlessLine (line := flashTotalLine) (by
      simp [flashTotalLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalBranchCursor, htotal⟩
  rcases totalBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revertWith (totalLimitError_lookup dp)) with
    ⟨popCursor, htotalPop⟩
  unfold flashLoanPostTotal at popCursor
  rcases popCursor.peelChildlessLine (line := [Ninst.pop])
      (by simp [NinstIsChildless]) with
    ⟨mintCursor, hpop⟩
  rcases mintCursor.peelChildlessLine (line := flashMintLine) (by
      simp [flashMintLine, addressArg, normalizeAddress, pushAddressMask,
        arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨eventCursor, hmint⟩
  rcases eventCursor.peelChildlessLine (line := flashEventCheckLine) (by
      simp [flashEventCheckLine, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨codeBranchCursor, hevent⟩
  rcases codeBranchCursor.selectBranchLeftWithBurn
      (fun _ => not_run_revert) with
    ⟨setupCursor, hcodePop⟩
  unfold flashLoanPostCode at setupCursor
  rcases setupCursor.peelChildlessLine (line := flashCallbackSetupLine)
      (by
        simp [flashCallbackSetupLine, storeFlashCallbackHead, mstoreAt,
          pushList, forwardArgTail, arg, cdl, flashCallbackArgsSize,
          NinstIsChildless, Ninst.pushB256]) with
    ⟨callCursor, hsetup⟩
  obtain ⟨gasWord, hstack, hwfCall, hreadsCall, _hcredit, _hbal, hcodeEq,
      hlocal⟩ :=
    flashLoanCallbackPrefix_effect hwfEntry hreadsEntry htoken htokenPop
      hamount hamountPop hcounter htotal htotalPop hpop hmint hevent
      hcodePop hsetup
  exact ⟨gasWord, callCursor, hstack, hwfCall, hreadsCall, hcodeEq, hlocal⟩

/-! ## The flash-loan arm

The pre-callback prefix moves no tagged allowance key, the borrower subtree
moves the region by exactly its own attribution stream, and the settlement
together with its shared burn continuation moves it by the frame's single
own record.  `flashLoan` is the one dispatched selector whose counted
contribution is `inner ++ [own]`, so those segments compose in that order. -/

/-- `flashLoan` transports the allowance region.  Its committed prefix mints
at one normalized address-shaped balance key and bumps the flash counter, so
every tagged allowance key still holds its entry value when the borrower
callback starts; the callback's subtree carries the whole descendant ledger;
and the post-callback settlement replays the frame's own record, which
follows that subtree precisely because the runtime settles the repayment
allowance only once the borrower has returned. -/
theorem Exec.Frame.allowanceRegionEffect_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ => Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmember :
      (Sevm.selector frame.sevm, nonpayable flashLoan) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [flashLoanSelector, weth10Funcs]
  have hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp) :=
    context.invocation.2.2.2
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  -- reach the borrower callback with all four witnesses
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCountedSilent (frame := frame) context hnonempty
      hmember with ⟨wrapperCursor, hwrapperSilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hbodySilent⟩
  have hentrySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hwrapperSilent.trans hbodySilent
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hentrySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hentrySilent.memory]
    exact context.memory_reads_empty
  obtain ⟨_gasWord, callCursor, hstack, hwfCall, hreadsCall, hcodePrefix,
      hlocalPrefix⟩ :=
    bodyCursor.reachFlashCallbackWitnessed hwfBody hreadsBody
  have hcallRun : Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm
      callCursor.pre flashLoanSuccessTail frame.post :=
    Func.Run.of_runCompiled callCursor.run
  obtain ⟨callPost, settlePre, hboundary, hstorSettle, _hbalSettle,
      hcodeSettle, _hlogsSettle, _houtputSettle, hwfSettle,
      hreadsSettleEx, hsettle⟩ :=
    of_rawFlashLoanSuccessTail_step dp hstack hwfCall hreadsCall rfl
      hcallRun
  -- the counted crossing at the same callback cursor
  obtain ⟨callPost', pcCross, xl, retained, _hat, hfilled, hstep, hinner⟩ :=
    callCursor.crossFlashCallback hcode
  obtain ⟨xlRaw, pcRaw, hrawFilled, hrawStep⟩ := hboundary.exists_step
  have halign := Ninst.StepRun.unique_exec_of_filled hfilled hrawFilled
    hstep hrawStep
  have hpostEq : callPost = callPost' := (Except.ok.inj halign.2).symm
  subst hpostEq
  -- entry-observation transport of the dispatch prefix
  have hentryStor : Devm.getStor frame.pre = Devm.getStor bodyCursor.pre :=
    funext (getStor_eq_of_state_eq hentrySilent.state)
  have hentryCode : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hentrySilent.state)
  have hcodeCall : Devm.getCode frame.pre ca =
      Devm.getCode callCursor.pre ca :=
    (congrFun hentryCode ca).trans (congrFun hcodePrefix ca)
  have hcallCodeAt : some (callCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeCall]
    exact context.installed.1
  have hprefixEffect :
      AllowanceRegionEffect ca frame.pre callCursor.pre [] := by
    refine ⟨fun key hkey => ?_, hcodeCall⟩
    rw [applyAllowanceLedger_nil]
    have hlocal := hlocalPrefix key (allowanceRegion_not_valid hkey)
      (allowanceRegion_ne_flashSlot hkey)
    rw [htarget] at hlocal
    rw [hlocal, ← congrFun hentryStor ca]
  -- the borrower subtree and the settlement handoff
  have hchildEffect :
      AllowanceRegionEffect ca callCursor.pre callPost
        (retained.attributionStream dp ca) :=
    hboundary.allowanceRegionEffect retained hfilled hstep hcallCodeAt
      hdeeper
  have hhandoff : AllowanceRegionEffect ca callPost settlePre [] :=
    AllowanceRegionEffect.of_getStorCode_eq (congrFun hstorSettle ca)
      (congrFun hcodeSettle ca)
  have hsegmentInner :
      AllowanceRegionEffect ca frame.pre settlePre
        (Exec.attributionInner dp ca frame.run) := by
    rw [hinner]
    simpa only [List.nil_append, List.append_nil] using
      hprefixEffect.append (hchildEffect.append hhandoff)
  -- the settlement segment carries the frame's own record
  obtain ⟨settleImg, hreadsSettle⟩ := hreadsSettleEx
  obtain ⟨burnPre, hburn, houtcome, hwfBurn, burnImg, hreadsBurn⟩ :=
    of_flashSettle_allowance dp hwfSettle hreadsSettle hsettle
  obtain ⟨_hdecrease, _hcover, _hflashSlot, _hburnLogs, _htrue, _hbalBurn,
      hcodeBurn⟩ :=
    flashBurn_effect dp hwfBurn hreadsBurn hburn
  have hcodeSettlePost : Devm.getCode settlePre = Devm.getCode frame.post :=
    houtcome.2.2.2.symm.trans hcodeBurn.symm
  have hown : (CountedFrame.ofFrame dp ca frame).allowance =
      frameAllowanceEvent frame.sevm frame.pre frame.post := rfl
  have hsegmentOwn :
      AllowanceRegionEffect ca settlePre frame.post
        [CountedFrame.ofFrame dp ca frame] :=
    flashSettlement_allowanceRegionEffect htarget hnonempty hselector
      houtcome hburn hcodeSettlePost hown
  -- the frame's own record follows its borrower subtree
  have hflash : isFlashInvocation frame.sevm = true := by
    simp [isFlashInvocation, hselector, hnonempty]
  have hframeEq : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      Exec.attributionInner dp ca frame.run ++
        [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframeEq,
      Exec.frameContribution_eq_append_of_flash dp ca frame _
        context.invocation hflash]
  rw [hstream]
  exact hsegmentInner.append hsegmentOwn

/-! ## Read-sound variants

`flashLoan` composes four segments: a silent dispatch prefix, the borrower
subtree, a silent settlement handoff, and the frame's own trailing record.
The three silent segments record nothing, the subtree is read-sound by the
strengthened recursion hypothesis, and the trailing own record is pinned by
`flashSettlement_allowanceEntryRead`.

That last segment is the one place where the recorded read is *not* the
frame's entry word: `frameAllowanceEvent` reconstructs a flash frame's read
from the committed post state rather than observing it at frame entry.  The
placement is what makes that honest.  `Exec.frameContribution` puts a flash
frame's own record after its subtree, so the prefix the entry-read clause
measures that record against is the whole inner stream — and the state that
prefix replays to is exactly the post-callback settlement entry, which is
where the runtime performed the read. -/

/-- Entry-read soundness of the settlement segment: measured against the
post-callback settlement entry storage, the frame's own counted record
records exactly the word that storage holds at the record's projected key.

This is the flash counterpart of `AllowanceEntryReadSound.ofFrame`, stated at
the settlement entry rather than at frame entry because that is where the
record sits in the ledger: `Exec.frameContribution` places it after the
subtree, so `AllowanceEntryReadSound.append` re-bases this segment's clause
over the whole inner stream, whose replay the inner transport identifies with
this very state.

Both settlement arms are pinned by the same post-state reconstruction that
pins the write.  `.flashMax` records `B256.max`, which is exactly what the
infinite arm observed; `.flashFinite (after + amount) after` records
`after + amount`, which `flashSettlement_reconstruction` proves is the exact
word the finite arm read before decrementing — exact because that arm is
guarded by `amount ≤ allowance`. -/
theorem flashSettlement_allowanceEntryRead
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {pre settlePre burnPre post : Devm}
    (htarget : e.currentTarget = ca)
    (hne0 : e.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector e = flashLoanSelector)
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post)
    {record : CountedFrame}
    (hrecord : record.allowance = frameAllowanceEvent e pre post) :
    AllowanceEntryReadSound (Devm.getStor settlePre ca) [record] := by
  subst htarget
  have haccept := flashSettlement_reconstruction houtcome hburn
  refine .singleton (fun event hevent v hread => ?_)
  rw [hrecord] at hevent
  by_cases hafter : (Devm.getStor post e.currentTarget).get
      (flashAllowanceRuntimeKey e) = B256.max
  · have hbranch : flashAllowanceBranchFromPost e post =
        .maximum (flashAllowanceRuntimeKey e) := by
      simp [flashAllowanceBranchFromPost, hafter]
    rw [hbranch] at haccept
    obtain ⟨-, hsettleMax⟩ := haccept.2
    have hextract : frameAllowanceEvent e pre post =
        some { owner := normalizedAddressArg e 0
               spender := e.currentTarget.toB256
               caller := e.caller
               depth := e.depth
               visit := .flashMax } := by
      simp [frameAllowanceEvent, hne0, hsel,
        flashLoanSelector_ne_approveSelector,
        flashLoanSelector_ne_approveAndCallSelector,
        flashLoanSelector_ne_permitSelector,
        flashLoanSelector_ne_transferFromSelector,
        flashLoanSelector_ne_withdrawFromSelector, hafter]
    obtain rfl := Option.some.inj (hextract.symm.trans hevent)
    simp only [AllowanceVisit.read?, Option.some.injEq] at hread
    simp only [AllowanceEvent.key, ← hread,
      ← flashAllowanceRuntimeKey_eq_projected]
    exact hsettleMax.symm
  · have hbranch : flashAllowanceBranchFromPost e post =
        .finite (flashAllowanceRuntimeKey e)
          ((Devm.getStor post e.currentTarget).get
            (flashAllowanceRuntimeKey e) + Sevm.argWord e 2)
          ((Devm.getStor post e.currentTarget).get
            (flashAllowanceRuntimeKey e)) := by
      simp [flashAllowanceBranchFromPost, hafter]
    rw [hbranch] at haccept
    obtain ⟨-, hsettleRead, -, -, -⟩ := haccept.2
    have hextract : frameAllowanceEvent e pre post =
        some { owner := normalizedAddressArg e 0
               spender := e.currentTarget.toB256
               caller := e.caller
               depth := e.depth
               visit := .flashFinite
                 ((Devm.getStor post e.currentTarget).get
                   (flashAllowanceRuntimeKey e) + Sevm.argWord e 2)
                 ((Devm.getStor post e.currentTarget).get
                   (flashAllowanceRuntimeKey e)) } := by
      simp [frameAllowanceEvent, hne0, hsel,
        flashLoanSelector_ne_approveSelector,
        flashLoanSelector_ne_approveAndCallSelector,
        flashLoanSelector_ne_permitSelector,
        flashLoanSelector_ne_transferFromSelector,
        flashLoanSelector_ne_withdrawFromSelector, hafter]
    obtain rfl := Option.some.inj (hextract.symm.trans hevent)
    simp only [AllowanceVisit.read?, Option.some.injEq] at hread
    simp only [AllowanceEvent.key, ← hread,
      ← flashAllowanceRuntimeKey_eq_projected]
    exact hsettleRead.symm

/-- The borrower callback transports the tagged allowance region by exactly
its own retained attribution stream, and its resume writes no storage. -/
private theorem RawFlashCallbackStepBoundary.allowanceRegionEffectSound
    {dp : DeployParams} {ca : Adr} {sevm : Sevm} {receiver : Adr}
    {amount inputSize : B256} {callbackInput : Bytes} {pre mid : Devm}
    {xl : Xlot} {pc : Nat}
    (boundary : RawFlashCallbackStepBoundary sevm sevm.currentTarget
      receiver amount inputSize callbackInput pre mid)
    (retained : RetainedXlot xl)
    (hfilled : Xlot.Filled xl)
    (hstep : Ninst.StepRun pc sevm pre Ninst.call xl (.ok mid))
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt sevm.depth ca (weth10 dp)
      (fun p s d out _ => Exec.CoreAllowanceReadSound dp ca p s d out)) :
    AllowanceRegionEffectSound ca pre mid
      (retained.attributionStream dp ca) := by
  rcases boundary with
    ⟨parent, child, xlRaw, delegated, na, code, gasWord, avail, pcRaw,
      hrawStep, hdepth, _hstack, _hpref, hparentState, _hparentMemory,
      _hparentLogs, _hparentOutput, hdelegation, hrawFilled, hprocess,
      _hclean, _hlength, _hmagic, _hresume, hmidState, _hreturnData,
      _hmidStack, _hmidLogs, _hmidOutput⟩
  have halign := Ninst.StepRun.unique_exec_of_filled hfilled hrawFilled
    hstep hrawStep
  cases halign.1
  let msg : Msg :=
    callMsg sevm parent (min gasWord.toNat (except64th avail)) 0
      sevm.currentTarget receiver na true false callbackInput code
      delegated
  have hparent : pre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < sevm.depth := by
    dsimp only [msg, callMsg]
    omega
  have hdelegation' :
      (getDelegatedCodeAddress (pre.getCode receiver) = none ∧
          code = pre.getCode receiver ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (pre.getCode receiver) =
          some delegatedTarget ∧
        code = pre.getCode delegatedTarget ∧ delegated = true) := by
    rcases hdelegation with ⟨hnone, _, hcode, hdel⟩ |
      ⟨delegatedTarget, hsome, _, hcode, hdel⟩
    · exact Or.inl ⟨hnone, hcode, hdel⟩
    · exact Or.inr ⟨delegatedTarget, hsome, hcode, hdel⟩
  have hresolved : receiver = ca → na = ca := by
    intro hreceiver
    have hnone :
        getDelegatedCodeAddress (pre.getCode receiver) = none := by
      rw [hreceiver]
      dsimp only [getDelegatedCodeAddress]
      rw [if_neg (not_delegation_of_compile installed)]
    rcases hdelegation with ⟨_, hna, _, _⟩ | ⟨_, hsome, _, _, _⟩
    · exact hna.trans hreceiver
    · simp [hnone] at hsome
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro hct
    have htargetCa : receiver = ca := by
      simpa only [msg, callMsg] using hct
    exact callbackCode_eq_compiled_of_target_eq installed htargetCa
      hdelegation'
  have htargetDirect :
      msg.currentTarget = ca → msg.codeAddress = some ca := by
    intro hct
    have htargetCa : receiver = ca := by
      simpa only [msg, callMsg] using hct
    simp only [msg, callMsg, hresolved htargetCa]
  have hchild :=
    ProcessMessageTrace.allowanceRegionDeltaSound_of_forallDeeperAt
      (dp := dp) (ca := ca) (depth := sevm.depth) (parent := pre)
      ⟨xl, retained, by simpa only [msg] using hprocess⟩
      hparent hmsgDepth installed htargetCode htargetDirect hdeeper
  have hresumeEffect : AllowanceRegionEffectSound ca child mid [] :=
    AllowanceRegionEffectSound.of_getStorCode_eq
      (congrArg (fun state : State => state.getStor ca) hmidState).symm
      (congrArg (fun state : State => state.getCode ca) hmidState).symm
  simpa only [List.append_nil] using hchild.append hresumeEffect

/-- `flashLoan` transports the allowance region.  Its committed prefix mints
at one normalized address-shaped balance key and bumps the flash counter, so
every tagged allowance key still holds its entry value when the borrower
callback starts; the callback's subtree carries the whole descendant ledger;
and the post-callback settlement replays the frame's own record, which
follows that subtree precisely because the runtime settles the repayment
allowance only once the borrower has returned. -/
theorem Exec.Frame.allowanceRegionEffectSound_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ => Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    AllowanceRegionEffectSound ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmember :
      (Sevm.selector frame.sevm, nonpayable flashLoan) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [flashLoanSelector, weth10Funcs]
  have hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp) :=
    context.invocation.2.2.2
  have htarget : frame.sevm.currentTarget = ca := context.invocation.2.1
  -- reach the borrower callback with all four witnesses
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCountedSilent (frame := frame) context hnonempty
      hmember with ⟨wrapperCursor, hwrapperSilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hbodySilent⟩
  have hentrySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hwrapperSilent.trans hbodySilent
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hentrySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hentrySilent.memory]
    exact context.memory_reads_empty
  obtain ⟨_gasWord, callCursor, hstack, hwfCall, hreadsCall, hcodePrefix,
      hlocalPrefix⟩ :=
    bodyCursor.reachFlashCallbackWitnessed hwfBody hreadsBody
  have hcallRun : Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm
      callCursor.pre flashLoanSuccessTail frame.post :=
    Func.Run.of_runCompiled callCursor.run
  obtain ⟨callPost, settlePre, hboundary, hstorSettle, _hbalSettle,
      hcodeSettle, _hlogsSettle, _houtputSettle, hwfSettle,
      hreadsSettleEx, hsettle⟩ :=
    of_rawFlashLoanSuccessTail_step dp hstack hwfCall hreadsCall rfl
      hcallRun
  -- the counted crossing at the same callback cursor
  obtain ⟨callPost', pcCross, xl, retained, _hat, hfilled, hstep, hinner⟩ :=
    callCursor.crossFlashCallback hcode
  obtain ⟨xlRaw, pcRaw, hrawFilled, hrawStep⟩ := hboundary.exists_step
  have halign := Ninst.StepRun.unique_exec_of_filled hfilled hrawFilled
    hstep hrawStep
  have hpostEq : callPost = callPost' := (Except.ok.inj halign.2).symm
  subst hpostEq
  -- entry-observation transport of the dispatch prefix
  have hentryStor : Devm.getStor frame.pre = Devm.getStor bodyCursor.pre :=
    funext (getStor_eq_of_state_eq hentrySilent.state)
  have hentryCode : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hentrySilent.state)
  have hcodeCall : Devm.getCode frame.pre ca =
      Devm.getCode callCursor.pre ca :=
    (congrFun hentryCode ca).trans (congrFun hcodePrefix ca)
  have hcallCodeAt : some (callCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← hcodeCall]
    exact context.installed.1
  have hprefixEffect :
      AllowanceRegionEffect ca frame.pre callCursor.pre [] := by
    refine ⟨fun key hkey => ?_, hcodeCall⟩
    rw [applyAllowanceLedger_nil]
    have hlocal := hlocalPrefix key (allowanceRegion_not_valid hkey)
      (allowanceRegion_ne_flashSlot hkey)
    rw [htarget] at hlocal
    rw [hlocal, ← congrFun hentryStor ca]
  -- the borrower subtree and the settlement handoff
  have hchildEffect :
      AllowanceRegionEffectSound ca callCursor.pre callPost
        (retained.attributionStream dp ca) :=
    hboundary.allowanceRegionEffectSound retained hfilled hstep hcallCodeAt
      hdeeper
  have hhandoff : AllowanceRegionEffect ca callPost settlePre [] :=
    AllowanceRegionEffect.of_getStorCode_eq (congrFun hstorSettle ca)
      (congrFun hcodeSettle ca)
  have hsegmentInner :
      AllowanceRegionEffectSound ca frame.pre settlePre
        (Exec.attributionInner dp ca frame.run) := by
    rw [hinner]
    simpa only [List.nil_append, List.append_nil] using
      (AllowanceRegionEffectSound.of_nilLedger hprefixEffect).append
        (hchildEffect.append
          (AllowanceRegionEffectSound.of_nilLedger hhandoff))
  -- the settlement segment carries the frame's own record
  obtain ⟨settleImg, hreadsSettle⟩ := hreadsSettleEx
  obtain ⟨burnPre, hburn, houtcome, hwfBurn, burnImg, hreadsBurn⟩ :=
    of_flashSettle_allowance dp hwfSettle hreadsSettle hsettle
  obtain ⟨_hdecrease, _hcover, _hflashSlot, _hburnLogs, _htrue, _hbalBurn,
      hcodeBurn⟩ :=
    flashBurn_effect dp hwfBurn hreadsBurn hburn
  have hcodeSettlePost : Devm.getCode settlePre = Devm.getCode frame.post :=
    houtcome.2.2.2.symm.trans hcodeBurn.symm
  have hown : (CountedFrame.ofFrame dp ca frame).allowance =
      frameAllowanceEvent frame.sevm frame.pre frame.post := rfl
  have hsegmentOwn :
      AllowanceRegionEffect ca settlePre frame.post
        [CountedFrame.ofFrame dp ca frame] :=
    flashSettlement_allowanceRegionEffect htarget hnonempty hselector
      houtcome hburn hcodeSettlePost hown
  -- the frame's own record follows its borrower subtree
  have hflash : isFlashInvocation frame.sevm = true := by
    simp [isFlashInvocation, hselector, hnonempty]
  have hframeEq : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      Exec.attributionInner dp ca frame.run ++
        [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframeEq,
      Exec.frameContribution_eq_append_of_flash dp ca frame _
        context.invocation hflash]
  rw [hstream]
  have hsegmentOwnSound :
      AllowanceRegionEffectSound ca settlePre frame.post
        [CountedFrame.ofFrame dp ca frame] :=
    { hsegmentOwn with
      entryRead :=
        flashSettlement_allowanceEntryRead htarget hnonempty hselector
          houtcome hburn hown }
  exact hsegmentInner.append hsegmentOwnSound

end Weth10

end Blanc
