import Blanc.Weth10HolderFlowCompiled

/-!
Proof-indexed chronology for the successful WETH10 flash-loan callback.

The functional flash theorem retains the exact borrower `CALL` step, but its
compatibility boundary existentially hides the recursive slot.  This module
keeps those indices explicit, aligns them with the original compiled-frame
cursor, and records the callback, settlement, and repayment in one chronology.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- The raw flash callback boundary with its parent, child, recursive slot,
and parent program counter exposed as indices. -/
def RawFlashCallbackIndexedStepBoundary
    (sevm : Sevm) (self receiver : Adr) (amount inputSize : B256)
    (callbackInput : Bytes) (pre mid parent child : Devm)
    (xl : Xlot) (pc : Nat) : Prop :=
  ∃ (delegated : Bool) (code : ByteArray) (gasWord : B256) (avail : Nat),
    Ninst.StepRun pc sevm pre Ninst.call xl (.ok mid) ∧
    0 < sevm.depth ∧
    pre.stack =
      gasWord :: receiver.toB256 :: (0 : B256) :: callbackArgsOffset ::
        inputSize :: (0 : B256) :: (0 : B256) :: parent.stack ∧
    [amount, receiver.toB256] <<+ parent.stack ∧
    parent.state = pre.state ∧
    parent.memory = pre.memory.extends
      [(callbackArgsOffset.toNat, inputSize.toNat), (0, 0)] ∧
    parent.logs = pre.logs ∧
    parent.output = pre.output ∧
    ((getDelegatedCodeAddress (pre.getCode receiver) = none ∧
        code = pre.getCode receiver ∧ delegated = false) ∨
      (∃ target,
        getDelegatedCodeAddress (pre.getCode receiver) = some target ∧
        code = pre.getCode target ∧ delegated = true)) ∧
    Xlot.Filled xl ∧
    ProcessMessage
      (callMsg sevm parent (min gasWord.toNat (except64th avail)) 0
        self receiver receiver true false callbackInput code delegated)
      xl (.ok child) ∧
    child.error.isSome = false ∧
    32 ≤ child.output.length ∧
    Bytes.toB256 (child.output.sliceD 0 32 0) = CALLBACK_SUCCESS ∧
    (Resume.call parent 0 0).run (.ok child) = .ok mid ∧
    mid.state = child.state ∧
    mid.returnData = child.output ∧
    mid.stack = (1 : B256) :: parent.stack ∧
    mid.logs = pre.logs ++ child.logs ∧
    mid.output = pre.output

/-- Forget only the exposed indices of an indexed flash callback boundary. -/
theorem RawFlashCallbackIndexedStepBoundary.toStepBoundary
    {sevm : Sevm} {self receiver : Adr} {amount inputSize : B256}
    {callbackInput : Bytes} {pre mid parent child : Devm}
    {xl : Xlot} {pc : Nat}
    (h : RawFlashCallbackIndexedStepBoundary sevm self receiver amount
      inputSize callbackInput pre mid parent child xl pc) :
    RawFlashCallbackStepBoundary sevm self receiver amount inputSize
      callbackInput pre mid := by
  rcases h with
    ⟨delegated, code, gasWord, avail, hstep, hdepth, hstack, hpref,
      hstate, hmemory, hlogs, houtput, hdelegation, hfilled, hprocess,
      hclean, hlength, hmagic, hresume, hmidState, hreturndata,
      hmidStack, hmidLogs, hmidOutput⟩
  exact ⟨parent, child, xl, delegated, code, gasWord, avail, pc, hstep,
    hdepth, hstack, hpref, hstate, hmemory, hlogs, houtput, hdelegation,
    hfilled, hprocess, hclean, hlength, hmagic, hresume, hmidState,
    hreturndata, hmidStack, hmidLogs, hmidOutput⟩

/-- A source-level internal jump cannot return when its selected auxiliary
body cannot return. -/
private theorem Func.not_run_call_of
    {fs : List Func} {sevm : Sevm} {slot : Nat} {body : Func}
    (hget : fs[slot]? = some body)
    (hbody : ∀ {pre post}, ¬ Func.Run fs sevm pre body post) :
    ∀ {pre post}, ¬ Func.Run fs sevm pre (.call slot) post := by
  intro pre post run
  cases run with
  | call selected _ bodyRun =>
      rw [hget] at selected
      cases Option.some.inj selected.symm
      exact hbody bodyRun

private def flashBurnGuardLine : Line :=
  loadArgBalanceAmount 0 2 ++ balanceTooSmall

private def flashBurnSuccessLine : Line :=
  debitLoadedBalance ++
    addressArg 0 ++ arg 2 ++ [Ninst.pushB256 0] ++ emitTransfer ++
    [Ninst.pop, Ninst.pop] ++
    pushFlashMintedSlot ++ [Ninst.sload] ++ arg 2 ++
    [Ninst.swap 0, Ninst.sub] ++ pushFlashMintedSlot ++ [Ninst.sstore] ++
    [Ninst.pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

private theorem flashBurn_shape :
    flashBurn = flashBurnGuardLine +++
      ((.call burnBalanceErrorSlot) <?>
        (flashBurnSuccessLine +++ Func.ret)) := by
  rfl

/-- The repayment continuation has no external child after its entry.  Its
only branch alternative is the fixed balance-error reverter. -/
private theorem Exec.Frame.CompiledCursor.finishFlashBurn
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashBurn final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    frame.descendantFlowActions dp ca = cursor.actions := by
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (flashBurnGuardLine +++
      ((.call burnBalanceErrorSlot) <?>
        (flashBurnSuccessLine +++ Func.ret))) final at cursor
  rcases cursor.peelChildlessLine (line := flashBurnGuardLine) (by
      simp [flashBurnGuardLine, loadArgBalanceAmount, balanceTooSmall,
        addressArg, normalizeAddress, arg, cdl, pushAddressMask,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, _hguard, hguardActions⟩
  rcases branchCursor.selectBranchWithActions with hsuccess | herror
  · rcases hsuccess with ⟨successCursor, hsuccessActions⟩
    have hdesc := successCursor.finishTerminalChildlessLine (by
      simp [flashBurnSuccessLine, debitLoadedBalance, addressArg,
        normalizeAddress, pushAddressMask, arg, cdl, emitTransfer,
        Blanc.transferFromLog,
        mstoreAt, logWith, pushList, pushFlashMintedSlot,
        NinstIsChildless, Ninst.pushB256])
    exact hdesc.trans (hsuccessActions.trans hguardActions)
  · rcases herror with ⟨errorCursor, _herrorActions⟩
    rcases errorCursor.enterCall hcode with
      ⟨body, hget, bodyCursor, _hbodyActions⟩
    have hbody : body = burnBalanceError := by
      simpa [weth10, weth10Aux, burnBalanceErrorSlot] using hget.symm
    subst body
    exact (Func.not_run_revWith
      (Func.Run.of_runCompiled bodyCursor.run)).elim

private def flashSettleKeyLine : Line :=
  addressArg 0 ++ mstoreAt 0 ++ [Ninst.address] ++ mstoreAt 1 ++
    allowanceKeyFromMemory ++ [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++
    isMax

private def flashSettleGuardLine : Line :=
  arg 2 ++ [Ninst.swap 0] ++ balanceTooSmall

private def flashSettleFiniteLine : Line :=
  [Ninst.sub, Ninst.dup 0, Ninst.swap 1, Ninst.sstore] ++
    emitFlashApproval

private theorem flashSettle_shape :
    flashSettle = flashSettleKeyLine +++
      (([Ninst.pop, Ninst.pop] +++ .call flashBurnSlot) <?>
        (flashSettleGuardLine +++
          ((.call allowanceErrorSlot) <?>
            (flashSettleFiniteLine +++ .call flashBurnSlot)))) := by
  rfl

/-- Settlement reaches the unique shared `flashBurn` body through either
allowance arm, and neither arm crosses an external child. -/
private theorem Exec.Frame.CompiledCursor.finishFlashSettle
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashSettle final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    frame.descendantFlowActions dp ca = cursor.actions := by
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (flashSettleKeyLine +++
      (([Ninst.pop, Ninst.pop] +++ .call flashBurnSlot) <?>
        (flashSettleGuardLine +++
          ((.call allowanceErrorSlot) <?>
            (flashSettleFiniteLine +++ .call flashBurnSlot)))))
      final at cursor
  rcases cursor.peelChildlessLine (line := flashSettleKeyLine) (by
      simp [flashSettleKeyLine, addressArg, normalizeAddress,
        pushAddressMask, arg, cdl, mstoreAt, allowanceKeyFromMemory,
        pushList, isMax, NinstIsChildless, Ninst.pushB256]) with
    ⟨allowanceBranchCursor, _hkey, hkeyActions⟩
  rcases allowanceBranchCursor.selectBranchWithActions with
      hfinite | hmax
  · rcases hfinite with ⟨finiteCursor, hfiniteActions⟩
    rcases finiteCursor.peelChildlessLine (line := flashSettleGuardLine)
        (by
          simp [flashSettleGuardLine, arg, cdl, balanceTooSmall,
            NinstIsChildless, Ninst.pushB256]) with
      ⟨guardBranchCursor, _hguard, hguardActions⟩
    rcases guardBranchCursor.selectBranchWithActions with
        hsuccess | herror
    · rcases hsuccess with ⟨successCursor, hsuccessActions⟩
      rcases successCursor.peelChildlessLine
          (line := flashSettleFiniteLine) (by
            simp [flashSettleFiniteLine, emitFlashApproval, arg, cdl,
              mstoreAt, logWith, NinstIsChildless, Ninst.pushB256]) with
        ⟨burnCallCursor, _hfiniteLine, hfiniteLineActions⟩
      rcases burnCallCursor.enterCall hcode with
        ⟨body, hget, burnCursor, hburnActions⟩
      have hbody : body = flashBurn := by
        simpa [weth10, weth10Aux, flashBurnSlot] using hget.symm
      subst body
      have hdesc := burnCursor.finishFlashBurn hcode
      exact hdesc.trans (hburnActions.trans
        (hfiniteLineActions.trans (hsuccessActions.trans
          (hguardActions.trans (hfiniteActions.trans hkeyActions)))))
    · rcases herror with ⟨errorCursor, _herrorActions⟩
      rcases errorCursor.enterCall hcode with
        ⟨body, hget, bodyCursor, _hbodyActions⟩
      have hbody : body = allowanceError := by
        simpa [weth10, weth10Aux, allowanceErrorSlot] using hget.symm
      subst body
      exact (Func.not_run_revWith
        (Func.Run.of_runCompiled bodyCursor.run)).elim
  · rcases hmax with ⟨maxCursor, hmaxActions⟩
    rcases maxCursor.peelChildlessLine (line := [Ninst.pop, Ninst.pop])
        (by simp [NinstIsChildless]) with
      ⟨burnCallCursor, _hpops, hpopsActions⟩
    rcases burnCallCursor.enterCall hcode with
      ⟨body, hget, burnCursor, hburnActions⟩
    have hbody : body = flashBurn := by
      simpa [weth10, weth10Aux, flashBurnSlot] using hget.symm
    subst body
    have hdesc := burnCursor.finishFlashBurn hcode
    exact hdesc.trans (hburnActions.trans
      (hpopsActions.trans (hmaxActions.trans hkeyActions)))

private def flashLoanAfterCallback : Func :=
  Ninst.iszero :::
    (.call bubbleRevertSlot) <?>
    (retdataShorterThan 32 +++
      Func.rev <?>
      (checkRetdataHead CALLBACK_SUCCESS 0 +++ Ninst.iszero :::
        (.call flashFailedErrorSlot) <?>
        ([Ninst.pop, Ninst.pop] +++ .call flashSettleSlot)))

private theorem flashLoanSuccessTail_shape :
    flashLoanSuccessTail = Ninst.call ::: flashLoanAfterCallback := by
  rfl

/-- The callback's successful decoder and repayment suffix cross no further
external child.  All failure alternatives are fixed nonreturning bodies. -/
private theorem Exec.Frame.CompiledCursor.finishFlashLoanAfterCallback
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {final : Devm}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      flashLoanAfterCallback final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    frame.descendantFlowActions dp ca = cursor.actions := by
  unfold flashLoanAfterCallback at cursor
  rcases cursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨callbackBranchCursor, _, _hiszero, _, hiszeroActions⟩
  rcases callbackBranchCursor.selectBranchWithActions with
      hdecode | hbubble
  · rcases hdecode with ⟨decodeCursor, hdecodeActions⟩
    rcases decodeCursor.peelChildlessLine (line := retdataShorterThan 32)
        (by
          simp [retdataShorterThan, NinstIsChildless,
            Ninst.pushB256]) with
      ⟨lengthBranchCursor, _hlength, hlengthActions⟩
    rcases lengthBranchCursor.selectBranchWithActions with
        hmagic | hshort
    · rcases hmagic with ⟨magicCursor, hmagicActions⟩
      rcases magicCursor.peelChildlessLine
          (line := checkRetdataHead CALLBACK_SUCCESS 0 ++
            [Ninst.iszero]) (by
            simp [checkRetdataHead, pushList, NinstIsChildless,
              Ninst.pushB256]) with
        ⟨magicBranchCursor, _hmagicLine, hmagicLineActions⟩
      rcases magicBranchCursor.selectBranchWithActions with
          hsettle | hfailed
      · rcases hsettle with ⟨settlePrefixCursor, hsettleActions⟩
        rcases settlePrefixCursor.peelChildlessLine
            (line := [Ninst.pop, Ninst.pop])
            (by simp [NinstIsChildless]) with
          ⟨settleCallCursor, _hpops, hpopsActions⟩
        rcases settleCallCursor.enterCall hcode with
          ⟨body, hget, settleCursor, hbodyActions⟩
        have hbody : body = flashSettle := by
          simpa [weth10, weth10Aux, flashSettleSlot] using hget.symm
        subst body
        have hdesc := settleCursor.finishFlashSettle hcode
        exact hdesc.trans (hbodyActions.trans
          (hpopsActions.trans (hsettleActions.trans
            (hmagicLineActions.trans (hmagicActions.trans
              (hlengthActions.trans
                (hdecodeActions.trans hiszeroActions)))))))
      · rcases hfailed with ⟨failedCursor, _hfailedActions⟩
        rcases failedCursor.enterCall hcode with
          ⟨body, hget, bodyCursor, _hbodyActions⟩
        have hbody : body = flashFailedError := by
          simpa [weth10, weth10Aux, flashFailedErrorSlot] using hget.symm
        subst body
        exact (Func.not_run_revWith
          (Func.Run.of_runCompiled bodyCursor.run)).elim
    · rcases hshort with ⟨shortCursor, _hshortActions⟩
      exact absurd (Func.Run.of_runCompiled shortCursor.run) not_run_rev
  · rcases hbubble with ⟨bubbleCursor, _hbubbleActions⟩
    rcases bubbleCursor.enterCall hcode with
      ⟨body, hget, bodyCursor, _hbodyActions⟩
    have hbody : body = bubbleRevert := by
      simpa [weth10, weth10Aux, bubbleRevertSlot] using hget.symm
    subst body
    exact (not_run_bubbleRevert
      (Func.Run.of_runCompiled bodyCursor.run)).elim

private def flashTokenLine : Line :=
  arg 1 ++ [Ninst.address, Ninst.eq, Ninst.iszero]

private def flashAmountLine : Line :=
  arg 2 ++ [Ninst.dup 0, Ninst.pushB256 maxUint112, Ninst.lt]

private def flashCounterLine : Line :=
  pushFlashMintedSlot ++ [Ninst.sload, Ninst.dup 1, Ninst.add] ++
    pushFlashMintedSlot ++ [Ninst.sstore]

private def flashTotalLine : Line :=
  pushFlashMintedSlot ++
    [Ninst.sload, Ninst.dup 0, Ninst.pushB256 maxUint112, Ninst.lt]

private def flashMintLine : Line :=
  addressArg 0 ++
    [Ninst.dup 0, Ninst.sload, Ninst.dup 2, Ninst.add,
      Ninst.dup 1, Ninst.sstore, Ninst.swap 0]

private def flashEventCheckLine : Line :=
  [Ninst.dup 0] ++ mstoreAt 0 ++
    [Ninst.dup 1, Ninst.pushB256 0, Ninst.pushB256 Blanc.transferEvent] ++
    logWith 2 0 1 ++ [Ninst.dup 1, Ninst.extcodesize, Ninst.iszero]

private def flashCallbackSetupLine : Line :=
  [Ninst.dup 0] ++ storeFlashCallbackHead ++ pushList [0, 0] ++
    forwardArgTail 3 6 ++ flashCallbackArgsSize ++
    [Ninst.pushB256 callbackArgsOffset, Ninst.pushB256 0,
      Ninst.dup 6, Ninst.gas]

private def flashLoanPostCode : Func :=
  flashCallbackSetupLine +++ flashLoanSuccessTail

private def flashLoanPostTotal : Func :=
  [Ninst.pop] +++ flashMintLine +++ flashEventCheckLine +++
    (Func.rev <?> flashLoanPostCode)

private def flashLoanPostCounter : Func :=
  flashCounterLine +++ flashTotalLine +++
    ((.call totalLimitErrorSlot) <?> flashLoanPostTotal)

private def flashLoanPostAmount : Func :=
  flashAmountLine +++
    ((.call individualLimitErrorSlot) <?> flashLoanPostCounter)

private def flashLoanBodyShape : Func :=
  flashTokenLine +++
    ((.call flashTokenErrorSlot) <?> flashLoanPostAmount)

private theorem flashLoan_shape : flashLoan = flashLoanBodyShape := by
  rfl

/-- Reach the exact successful callback suffix of the public `flashLoan`
body.  Every earlier instruction is childless and every alternate branch is a
fixed reverter, so the returned cursor has crossed no recursive child. -/
private theorem Exec.Frame.CompiledCursor.reachFlashLoanSuccessTailCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashLoan frame.post)
    (hwfEntry : Mem.Wf cursor.pre.memory)
    (hreadsEntry : Mem.Reads cursor.pre.memory [])
    :
    ∃ (gasWord : B256) (callCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        flashLoanSuccessTail frame.post),
      callCursor.actions = cursor.actions ∧
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
      Increase (normalizedAddressArg frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2)
        (Stor.rest
          (Devm.getStor cursor.pre frame.sevm.currentTarget))
        (Stor.rest
          (Devm.getStor callCursor.pre frame.sevm.currentTarget)) ∧
      Devm.getBal cursor.pre = Devm.getBal callCursor.pre ∧
      Devm.getCode cursor.pre = Devm.getCode callCursor.pre := by
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    flashLoanBodyShape frame.post at cursor
  unfold flashLoanBodyShape at cursor
  rcases cursor.peelChildlessLine (line := flashTokenLine) (by
      simp [flashTokenLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨tokenBranchCursor, htoken, htokenActions⟩
  have hpTokenFlag :
      ((frame.sevm.currentTarget.toB256 =?
          Sevm.argWord frame.sevm 1) =? 0) :: [] <<+
        tokenBranchCursor.pre.stack := by
    unfold flashTokenLine at htoken
    rcases of_run_append (arg 1) htoken with
      ⟨afterArg, harg, htoken⟩
    have hpArg : Sevm.argWord frame.sevm 1 :: [] <<+
        afterArg.stack := prefix_of_arg nil_pref harg
    rcases Line.of_run_cons htoken with
      ⟨afterAddress, haddress, htoken⟩
    have hpAddress : frame.sevm.currentTarget.toB256 ::
        Sevm.argWord frame.sevm 1 :: [] <<+ afterAddress.stack :=
      prefix_of_push (of_run_address haddress) hpArg
    rcases Line.of_run_cons htoken with ⟨afterEq, heq, htoken⟩
    have hpEq := prefix_of_eq heq hpAddress
    rcases Line.of_run_cons htoken with ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero hpEq
  have htokenLookup :
      ((weth10 dp).main :: weth10Aux)[flashTokenErrorSlot]? =
        some flashTokenError := by
    simp [weth10, weth10Aux, flashTokenErrorSlot]
  have hnoToken : ∀ {pre post},
      ¬ Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm pre
        (.call flashTokenErrorSlot) post :=
    Func.not_run_call_of htokenLookup (fun {_ _} run =>
      Func.not_run_revWith run)
  rcases tokenBranchCursor.selectBranchLeftWithBurn
      (fun _ => hnoToken) with
    ⟨amountCursor, htokenPop, htokenBranchActions⟩
  have hpAmountEntry : [] <<+ amountCursor.pre.stack :=
    (popBurn_pref (Devm.PopBurn.of_popBurnBy htokenPop) hpTokenFlag).2
  unfold flashLoanPostAmount at amountCursor
  rcases amountCursor.peelChildlessLine (line := flashAmountLine) (by
      simp [flashAmountLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨amountBranchCursor, hamount, hamountActions⟩
  have hpAmountFlag :
      (maxUint112 <? Sevm.argWord frame.sevm 2) ::
        Sevm.argWord frame.sevm 2 :: [] <<+
        amountBranchCursor.pre.stack := by
    unfold flashAmountLine at hamount
    rcases of_run_append (arg 2) hamount with
      ⟨afterArg, harg, hamount⟩
    have hpArg : Sevm.argWord frame.sevm 2 :: [] <<+ afterArg.stack :=
      prefix_of_arg hpAmountEntry harg
    rcases Line.of_run_cons hamount with
      ⟨afterDup, hdup, hamount⟩
    have hpDup : Sevm.argWord frame.sevm 2 ::
        Sevm.argWord frame.sevm 2 :: [] <<+ afterDup.stack :=
      prefix_of_dup_val hdup (by show_nth) hpArg
    rcases Line.of_run_cons hamount with
      ⟨afterMax, hmax, hamount⟩
    have hpMax : maxUint112 :: Sevm.argWord frame.sevm 2 ::
        Sevm.argWord frame.sevm 2 :: [] <<+ afterMax.stack :=
      prefix_of_push (of_run_pushB256 hmax) hpDup
    rcases Line.of_run_cons hamount with ⟨afterLt, hlt, hnil⟩
    cases hnil
    exact prefix_of_lt hlt hpMax
  have hamountLookup :
      ((weth10 dp).main :: weth10Aux)[individualLimitErrorSlot]? =
        some individualLimitError := by
    simp [weth10, weth10Aux, individualLimitErrorSlot]
  have hnoAmount : ∀ {pre post},
      ¬ Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm pre
        (.call individualLimitErrorSlot) post :=
    Func.not_run_call_of hamountLookup (fun {_ _} run =>
      Func.not_run_revWith run)
  rcases amountBranchCursor.selectBranchLeftWithBurn
      (fun _ => hnoAmount) with
    ⟨counterCursor, hamountPop, hamountBranchActions⟩
  have hpAmount : [Sevm.argWord frame.sevm 2] <<+
      counterCursor.pre.stack :=
    (popBurn_pref (Devm.PopBurn.of_popBurnBy hamountPop)
      hpAmountFlag).2
  unfold flashLoanPostCounter at counterCursor
  rcases counterCursor.peelChildlessLine (line := flashCounterLine) (by
      simp [flashCounterLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalCursor, hcounter, hcounterActions⟩
  have hpCounter : [Sevm.argWord frame.sevm 2] <<+
      totalCursor.pre.stack := by
    unfold flashCounterLine at hcounter
    rcases of_run_append pushFlashMintedSlot hcounter with
      ⟨afterSlot, hslot, hcounter⟩
    have hpSlot : flashMintedSlot :: Sevm.argWord frame.sevm 2 :: [] <<+
        afterSlot.stack := prefix_of_pushFlashMintedSlot hpAmount hslot
    rcases Line.of_run_cons hcounter with
      ⟨afterLoad, hload, hcounter⟩
    rcases prefix_of_sload hload hpSlot with ⟨stored, hpLoad, _⟩
    rcases Line.of_run_cons hcounter with
      ⟨afterDup, hdup, hcounter⟩
    have hpDup : Sevm.argWord frame.sevm 2 :: stored ::
        Sevm.argWord frame.sevm 2 :: [] <<+ afterDup.stack :=
      prefix_of_dup_val hdup (by show_nth) hpLoad
    rcases Line.of_run_cons hcounter with
      ⟨afterAdd, hadd, hcounter⟩
    have hpAdd := prefix_of_add hadd hpDup
    rcases of_run_append pushFlashMintedSlot hcounter with
      ⟨afterSlot2, hslot2, hcounter⟩
    have hpSlot2 : flashMintedSlot ::
        (Sevm.argWord frame.sevm 2 + stored) ::
        Sevm.argWord frame.sevm 2 :: [] <<+ afterSlot2.stack :=
      prefix_of_pushFlashMintedSlot hpAdd hslot2
    rcases Line.of_run_cons hcounter with
      ⟨afterStore, hstore, hnil⟩
    cases hnil
    exact prefix_of_sstore hstore hpSlot2
  rcases totalCursor.peelChildlessLine (line := flashTotalLine) (by
      simp [flashTotalLine, pushFlashMintedSlot, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨totalBranchCursor, htotal, htotalActions⟩
  obtain ⟨total, hpTotal⟩ : ∃ total,
      (maxUint112 <? total) :: total ::
        Sevm.argWord frame.sevm 2 :: [] <<+
        totalBranchCursor.pre.stack := by
    unfold flashTotalLine at htotal
    rcases of_run_append pushFlashMintedSlot htotal with
      ⟨afterSlot, hslot, htotal⟩
    have hpSlot : flashMintedSlot :: Sevm.argWord frame.sevm 2 :: [] <<+
        afterSlot.stack := prefix_of_pushFlashMintedSlot hpCounter hslot
    rcases Line.of_run_cons htotal with
      ⟨afterLoad, hload, htotal⟩
    rcases prefix_of_sload hload hpSlot with ⟨total, hpLoad, _⟩
    rcases Line.of_run_cons htotal with
      ⟨afterDup, hdup, htotal⟩
    have hpDup : total :: total :: Sevm.argWord frame.sevm 2 :: [] <<+
        afterDup.stack := prefix_of_dup_val hdup (by show_nth) hpLoad
    rcases Line.of_run_cons htotal with
      ⟨afterMax, hmax, htotal⟩
    have hpMax : maxUint112 :: total :: total ::
        Sevm.argWord frame.sevm 2 :: [] <<+ afterMax.stack :=
      prefix_of_push (of_run_pushB256 hmax) hpDup
    rcases Line.of_run_cons htotal with ⟨afterLt, hlt, hnil⟩
    cases hnil
    exact ⟨total, prefix_of_lt hlt hpMax⟩
  have htotalLookup :
      ((weth10 dp).main :: weth10Aux)[totalLimitErrorSlot]? =
        some totalLimitError := by
    simp [weth10, weth10Aux, totalLimitErrorSlot]
  have hnoTotal : ∀ {pre post},
      ¬ Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm pre
        (.call totalLimitErrorSlot) post :=
    Func.not_run_call_of htotalLookup (fun {_ _} run =>
      Func.not_run_revWith run)
  rcases totalBranchCursor.selectBranchLeftWithBurn
      (fun _ => hnoTotal) with
    ⟨popCursor, htotalPop, htotalBranchActions⟩
  have hpBeforePop : total :: Sevm.argWord frame.sevm 2 :: [] <<+
      popCursor.pre.stack :=
    (popBurn_pref (Devm.PopBurn.of_popBurnBy htotalPop) hpTotal).2
  unfold flashLoanPostTotal at popCursor
  rcases popCursor.peelChildlessLine (line := [Ninst.pop])
      (by simp [NinstIsChildless]) with
    ⟨mintCursor, hpop, hpopActions⟩
  have hpMintEntry : [Sevm.argWord frame.sevm 2] <<+
      mintCursor.pre.stack :=
    prefix_of_pop (of_run_pop (of_run_singleton hpop)) hpBeforePop
  rcases mintCursor.peelChildlessLine (line := flashMintLine) (by
      simp [flashMintLine, addressArg, normalizeAddress, pushAddressMask,
        arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨eventCursor, hmint, hmintActions⟩
  let key := (~~~ addressMask) &&& Sevm.argWord frame.sevm 0
  have hpMint : [Sevm.argWord frame.sevm 2, key] <<+
      eventCursor.pre.stack := by
    unfold flashMintLine at hmint
    rcases of_run_append (addressArg 0) hmint with
      ⟨afterKey, hkey, hmint⟩
    have hpKey : key :: Sevm.argWord frame.sevm 2 :: [] <<+
        afterKey.stack := by
      simpa only [key] using prefix_of_addressArg hpMintEntry hkey
    rcases Line.of_run_cons hmint with
      ⟨afterDupKey, hdupKey, hmint⟩
    have hpDupKey : key :: key :: Sevm.argWord frame.sevm 2 :: [] <<+
        afterDupKey.stack :=
      prefix_of_dup_val hdupKey (by show_nth) hpKey
    rcases Line.of_run_cons hmint with
      ⟨afterLoad, hload, hmint⟩
    rcases prefix_of_sload hload hpDupKey with
      ⟨oldBalance, hpLoad, holdBalance⟩
    rcases Line.of_run_cons hmint with
      ⟨afterDupAmount, hdupAmount, hmint⟩
    have hpDupAmount : Sevm.argWord frame.sevm 2 :: oldBalance :: key ::
        Sevm.argWord frame.sevm 2 :: [] <<+ afterDupAmount.stack :=
      prefix_of_dup_val hdupAmount (by show_nth) hpLoad
    rcases Line.of_run_cons hmint with
      ⟨afterAdd, hadd, hmint⟩
    have hpAdd := prefix_of_add hadd hpDupAmount
    rcases Line.of_run_cons hmint with
      ⟨afterDupKey2, hdupKey2, hmint⟩
    have hpDupKey2 : key :: (Sevm.argWord frame.sevm 2 + oldBalance) ::
        key :: Sevm.argWord frame.sevm 2 :: [] <<+ afterDupKey2.stack :=
      prefix_of_dup_val hdupKey2 (by show_nth) hpAdd
    rcases Line.of_run_cons hmint with
      ⟨afterStore, hstore, hmint⟩
    have hstoreBalance :
        Devm.getStor afterStore frame.sevm.currentTarget =
          (Devm.getStor afterDupKey2 frame.sevm.currentTarget).set key
            (Sevm.argWord frame.sevm 2 + oldBalance) :=
      sstore_getStor_set hstore hpDupKey2
    have hpStore : key :: Sevm.argWord frame.sevm 2 :: [] <<+
        afterStore.stack := prefix_of_sstore hstore hpDupKey2
    rcases Line.of_run_cons hmint with
      ⟨afterSwap, hswap, hnil⟩
    cases hnil
    have hswapCore : Stack.Swap (0 : Fin 16).val
        [key, Sevm.argWord frame.sevm 2]
        [Sevm.argWord frame.sevm 2, key] := Stack.swapCore_zero
    exact Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpStore
  rcases eventCursor.peelChildlessLine (line := flashEventCheckLine) (by
      simp [flashEventCheckLine, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨codeBranchCursor, hevent, heventActions⟩
  obtain ⟨codeSize, hpCodeFlag⟩ : ∃ codeSize,
      (codeSize =? 0) :: Sevm.argWord frame.sevm 2 :: key :: [] <<+
        codeBranchCursor.pre.stack := by
    unfold flashEventCheckLine at hevent
    rcases Line.of_run_cons hevent with
      ⟨afterDupAmount, hdupAmount, hevent⟩
    have hpDupAmount : Sevm.argWord frame.sevm 2 ::
        Sevm.argWord frame.sevm 2 :: key :: [] <<+
        afterDupAmount.stack :=
      prefix_of_dup_val hdupAmount (by show_nth) hpMint
    rcases of_run_append (mstoreAt 0) hevent with
      ⟨afterStore, hstore, hevent⟩
    rcases of_run_mstoreAt_val hstore hpDupAmount with
      ⟨hpStore, _hmemory⟩
    rcases Line.of_run_cons hevent with
      ⟨afterDupKey, hdupKey, hevent⟩
    have hpDupKey : key :: Sevm.argWord frame.sevm 2 :: key :: [] <<+
        afterDupKey.stack :=
      prefix_of_dup_val hdupKey (by show_nth) hpStore
    rcases Line.of_run_cons hevent with
      ⟨afterZero, hzero, hevent⟩
    have hpZero : (0 : B256) :: key :: Sevm.argWord frame.sevm 2 ::
        key :: [] <<+ afterZero.stack :=
      prefix_of_push (of_run_pushB256 hzero) hpDupKey
    rcases Line.of_run_cons hevent with
      ⟨afterTopic, htopic, hevent⟩
    have hpTopic : Blanc.transferEvent :: (0 : B256) :: key ::
        Sevm.argWord frame.sevm 2 :: key :: [] <<+ afterTopic.stack :=
      prefix_of_push (of_run_pushB256 htopic) hpZero
    rcases of_run_append (logWith 2 0 1) hevent with
      ⟨afterLog, hlog, hevent⟩
    rcases of_logWith201_val hpTopic hlog with ⟨hpLog, _⟩
    rcases Line.of_run_cons hevent with
      ⟨afterDupKey2, hdupKey2, hevent⟩
    have hpDupKey2 : key :: Sevm.argWord frame.sevm 2 :: key :: [] <<+
        afterDupKey2.stack :=
      prefix_of_dup_val hdupKey2 (by show_nth) hpLog
    rcases Line.of_run_cons hevent with
      ⟨afterCodeSize, hcodeSize, hevent⟩
    rcases prefix_of_extcodesize hpDupKey2 hcodeSize with
      ⟨codeSize, hpCodeSize⟩
    rcases Line.of_run_cons hevent with
      ⟨afterZeroCheck, hzeroCheck, hnil⟩
    cases hnil
    exact ⟨codeSize, prefix_of_iszero hzeroCheck hpCodeSize⟩
  rcases codeBranchCursor.selectBranchLeftWithBurn
      (fun _ => not_run_rev) with
    ⟨setupCursor, hcodePop, hcodeBranchActions⟩
  have hpSetup : [Sevm.argWord frame.sevm 2, key] <<+
      setupCursor.pre.stack :=
    (popBurn_pref (Devm.PopBurn.of_popBurnBy hcodePop) hpCodeFlag).2
  unfold flashLoanPostCode at setupCursor
  rcases setupCursor.peelChildlessLine (line := flashCallbackSetupLine)
      (by
        simp [flashCallbackSetupLine, storeFlashCallbackHead, mstoreAt,
          pushList, forwardArgTail, arg, cdl, flashCallbackArgsSize,
          NinstIsChildless, Ninst.pushB256]) with
    ⟨callCursor, hsetup, hsetupActions⟩
  obtain ⟨gasWord, hpCall⟩ : ∃ gasWord,
      gasWord :: key :: (0 : B256) :: callbackArgsOffset ::
        flashCallbackRuntimeSize frame.sevm :: (0 : B256) ::
        (0 : B256) :: [Sevm.argWord frame.sevm 2, key] <<+
        callCursor.pre.stack := by
    unfold flashCallbackSetupLine at hsetup
    rcases Line.of_run_cons hsetup with
      ⟨afterDup, hdup, hsetup⟩
    have hpDup : Sevm.argWord frame.sevm 2 ::
        Sevm.argWord frame.sevm 2 :: key :: [] <<+ afterDup.stack :=
      prefix_of_dup_val hdup (by show_nth) hpSetup
    rcases of_run_append storeFlashCallbackHead hsetup with
      ⟨afterHead, hhead, hsetup⟩
    have hpHead := prefix_of_storeFlashCallbackHead hpDup hhead
    rcases of_run_append (pushList [0, 0]) hsetup with
      ⟨afterZeros, hzeros, hsetup⟩
    unfold pushList at hzeros
    simp only [List.map] at hzeros
    rcases Line.of_run_cons hzeros with
      ⟨afterZero1, hzero1, hzeros⟩
    have hpZero1 : (0 : B256) :: Sevm.argWord frame.sevm 2 :: key ::
        [] <<+ afterZero1.stack :=
      prefix_of_push (of_run_pushB256 hzero1) hpHead
    rcases Line.of_run_cons hzeros with
      ⟨afterZero2, hzero2, hnilZeros⟩
    cases hnilZeros
    have hpZeros : (0 : B256) :: (0 : B256) ::
        Sevm.argWord frame.sevm 2 :: key :: [] <<+ afterZeros.stack :=
      prefix_of_push (of_run_pushB256 hzero2) hpZero1
    rcases of_run_append (forwardArgTail 3 6) hsetup with
      ⟨afterTail, htail, hsetup⟩
    rcases of_forwardArgTail_val hpZeros htail with ⟨hpTail, _⟩
    rcases of_run_append flashCallbackArgsSize hsetup with
      ⟨afterSize, hsize, hsetup⟩
    have hpSize : flashCallbackRuntimeSize frame.sevm ::
        (0 : B256) :: (0 : B256) :: Sevm.argWord frame.sevm 2 ::
        key :: [] <<+ afterSize.stack := by
      simpa only [flashCallbackRuntimeSize] using
        prefix_of_flashCallbackArgsSize_exact hpTail hsize
    rcases Line.of_run_cons hsetup with
      ⟨afterOffset, hoffset, hsetup⟩
    have hpOffset : callbackArgsOffset ::
        flashCallbackRuntimeSize frame.sevm :: (0 : B256) ::
        (0 : B256) :: Sevm.argWord frame.sevm 2 :: key :: [] <<+
        afterOffset.stack :=
      prefix_of_push (of_run_pushB256 hoffset) hpSize
    rcases Line.of_run_cons hsetup with
      ⟨afterOutSize, houtSize, hsetup⟩
    have hpOutSize : (0 : B256) :: callbackArgsOffset ::
        flashCallbackRuntimeSize frame.sevm :: (0 : B256) ::
        (0 : B256) :: Sevm.argWord frame.sevm 2 :: key :: [] <<+
        afterOutSize.stack :=
      prefix_of_push (of_run_pushB256 houtSize) hpOffset
    rcases Line.of_run_cons hsetup with
      ⟨afterReceiver, hreceiver, hsetup⟩
    have hpReceiver : key :: (0 : B256) :: callbackArgsOffset ::
        flashCallbackRuntimeSize frame.sevm :: (0 : B256) ::
        (0 : B256) :: Sevm.argWord frame.sevm 2 :: key :: [] <<+
        afterReceiver.stack :=
      prefix_of_dup_val hreceiver (by show_nth) hpOutSize
    rcases Line.of_run_cons hsetup with
      ⟨afterGas, hgas, hnil⟩
    cases hnil
    rcases of_run_gas hgas with ⟨gasWord, hgasPush⟩
    exact ⟨gasWord, prefix_of_push hgasPush hpReceiver⟩
  have hkeyValid : ValidAdr key := by
    simpa only [key] using
      normalizedAddress_valid (Sevm.argWord frame.sevm 0)
  have hkey : key.toAdr.toB256 = key := toB256_toAdr hkeyValid

  have hcounterEffect := hcounter
  unfold flashCounterLine at hcounterEffect
  rcases of_run_append pushFlashMintedSlot hcounterEffect with
    ⟨counterSlot, hcounterSlot, hcounterEffect⟩
  rcases Line.of_run_cons hcounterEffect with
    ⟨counterLoad, hcounterLoad, hcounterEffect⟩
  rcases Line.of_run_cons hcounterEffect with
    ⟨counterDup, hcounterDup, hcounterEffect⟩
  rcases Line.of_run_cons hcounterEffect with
    ⟨counterAdd, hcounterAdd, hcounterEffect⟩
  rcases of_run_append pushFlashMintedSlot hcounterEffect with
    ⟨counterSlot2, hcounterSlot2, hcounterEffect⟩
  rcases Line.of_run_cons hcounterEffect with
    ⟨counterStore, hcounterStore, hcounterDone⟩
  cases hcounterDone
  have hpCounterSlot : flashMintedSlot ::
      Sevm.argWord frame.sevm 2 :: [] <<+ counterSlot.stack :=
    prefix_of_pushFlashMintedSlot hpAmount hcounterSlot
  rcases prefix_of_sload hcounterLoad hpCounterSlot with
    ⟨counterBefore, hpCounterLoad, _hcounterRead⟩
  have hpCounterDup : Sevm.argWord frame.sevm 2 :: counterBefore ::
      Sevm.argWord frame.sevm 2 :: [] <<+ counterDup.stack :=
    prefix_of_dup_val hcounterDup (by show_nth) hpCounterLoad
  have hpCounterAdd := prefix_of_add hcounterAdd hpCounterDup
  have hpCounterSlot2 : flashMintedSlot ::
      (Sevm.argWord frame.sevm 2 + counterBefore) ::
      Sevm.argWord frame.sevm 2 :: [] <<+ counterSlot2.stack :=
    prefix_of_pushFlashMintedSlot hpCounterAdd hcounterSlot2
  have hcounterSet :
      Devm.getStor totalCursor.pre frame.sevm.currentTarget =
        (Devm.getStor counterSlot2 frame.sevm.currentTarget).set
          flashMintedSlot
          (Sevm.argWord frame.sevm 2 + counterBefore) :=
    sstore_getStor_set hcounterStore hpCounterSlot2
  have hstorEntryCounterSlot2 :
      Devm.getStor cursor.pre = Devm.getStor counterSlot2 := by
    calc
      Devm.getStor cursor.pre = Devm.getStor tokenBranchCursor.pre :=
        Line.of_inv Devm.getStor (by
          unfold flashTokenLine arg cdl
          line_inv) htoken
      _ = Devm.getStor amountCursor.pre :=
        funext (getStor_eq_of_state_eq htokenPop.state)
      _ = Devm.getStor amountBranchCursor.pre :=
        Line.of_inv Devm.getStor (by
          unfold flashAmountLine arg cdl
          line_inv) hamount
      _ = Devm.getStor counterCursor.pre :=
        funext (getStor_eq_of_state_eq hamountPop.state)
      _ = Devm.getStor counterSlot :=
        Line.of_inv Devm.getStor (by
          unfold pushFlashMintedSlot
          line_inv) hcounterSlot
      _ = Devm.getStor counterLoad :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hcounterLoad Line.Run.nil)
      _ = Devm.getStor counterDup :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hcounterDup Line.Run.nil)
      _ = Devm.getStor counterAdd :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hcounterAdd Line.Run.nil)
      _ = Devm.getStor counterSlot2 :=
        Line.of_inv Devm.getStor (by
          unfold pushFlashMintedSlot
          line_inv) hcounterSlot2
  have hstorTotalMint :
      Devm.getStor totalCursor.pre = Devm.getStor mintCursor.pre := by
    calc
      Devm.getStor totalCursor.pre =
          Devm.getStor totalBranchCursor.pre :=
        Line.of_inv Devm.getStor (by
          unfold flashTotalLine pushFlashMintedSlot
          line_inv) htotal
      _ = Devm.getStor popCursor.pre :=
        funext (getStor_eq_of_state_eq htotalPop.state)
      _ = Devm.getStor mintCursor.pre :=
        Line.of_inv Devm.getStor (by line_inv) hpop
  have hrestEntryMint :
      Stor.rest (Devm.getStor cursor.pre frame.sevm.currentTarget) =
        Stor.rest
          (Devm.getStor mintCursor.pre frame.sevm.currentTarget) := by
    calc
      Stor.rest (Devm.getStor cursor.pre frame.sevm.currentTarget) =
          Stor.rest
            (Devm.getStor counterSlot2 frame.sevm.currentTarget) :=
        congrArg Stor.rest
          (congrFun hstorEntryCounterSlot2 frame.sevm.currentTarget)
      _ = Stor.rest
          ((Devm.getStor counterSlot2 frame.sevm.currentTarget).set
            flashMintedSlot
            (Sevm.argWord frame.sevm 2 + counterBefore)) :=
        (rest_set_flashMintedSlot _ _).symm
      _ = Stor.rest
          (Devm.getStor totalCursor.pre frame.sevm.currentTarget) :=
        congrArg Stor.rest hcounterSet.symm
      _ = Stor.rest
          (Devm.getStor mintCursor.pre frame.sevm.currentTarget) :=
        congrArg Stor.rest
          (congrFun hstorTotalMint frame.sevm.currentTarget)

  have hmintEffect := hmint
  unfold flashMintLine at hmintEffect
  rcases of_run_append (addressArg 0) hmintEffect with
    ⟨mintKey, hmintKey, hmintEffect⟩
  rcases Line.of_run_cons hmintEffect with
    ⟨mintDupKey, hmintDupKey, hmintEffect⟩
  rcases Line.of_run_cons hmintEffect with
    ⟨mintLoad, hmintLoad, hmintEffect⟩
  rcases Line.of_run_cons hmintEffect with
    ⟨mintDupAmount, hmintDupAmount, hmintEffect⟩
  rcases Line.of_run_cons hmintEffect with
    ⟨mintAdd, hmintAdd, hmintEffect⟩
  rcases Line.of_run_cons hmintEffect with
    ⟨mintDupKey2, hmintDupKey2, hmintEffect⟩
  rcases Line.of_run_cons hmintEffect with
    ⟨mintStore, hmintStore, hmintEffect⟩
  rcases Line.of_run_cons hmintEffect with
    ⟨mintSwap, hmintSwap, hmintDone⟩
  cases hmintDone
  have hpMintKey : key :: Sevm.argWord frame.sevm 2 :: [] <<+
      mintKey.stack := by
    simpa only [key] using prefix_of_addressArg hpMintEntry hmintKey
  have hpMintDupKey : key :: key :: Sevm.argWord frame.sevm 2 :: [] <<+
      mintDupKey.stack :=
    prefix_of_dup_val hmintDupKey (by show_nth) hpMintKey
  rcases prefix_of_sload hmintLoad hpMintDupKey with
    ⟨oldBalance, hpMintLoad, holdBalance⟩
  have hpMintDupAmount : Sevm.argWord frame.sevm 2 :: oldBalance :: key ::
      Sevm.argWord frame.sevm 2 :: [] <<+ mintDupAmount.stack :=
    prefix_of_dup_val hmintDupAmount (by show_nth) hpMintLoad
  have hpMintAdd := prefix_of_add hmintAdd hpMintDupAmount
  have hpMintDupKey2 : key ::
      (Sevm.argWord frame.sevm 2 + oldBalance) :: key ::
      Sevm.argWord frame.sevm 2 :: [] <<+ mintDupKey2.stack :=
    prefix_of_dup_val hmintDupKey2 (by show_nth) hpMintAdd
  have hmintSet :
      Devm.getStor mintStore frame.sevm.currentTarget =
        (Devm.getStor mintDupKey2 frame.sevm.currentTarget).set key
          (Sevm.argWord frame.sevm 2 + oldBalance) :=
    sstore_getStor_set hmintStore hpMintDupKey2
  have hstorMintDupKey2 :
      Devm.getStor mintCursor.pre = Devm.getStor mintDupKey2 := by
    calc
      Devm.getStor mintCursor.pre = Devm.getStor mintKey :=
        Line.of_inv Devm.getStor (by
          unfold addressArg normalizeAddress pushAddressMask arg cdl
          line_inv) hmintKey
      _ = Devm.getStor mintDupKey :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hmintDupKey Line.Run.nil)
      _ = Devm.getStor mintLoad :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hmintLoad Line.Run.nil)
      _ = Devm.getStor mintDupAmount :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hmintDupAmount Line.Run.nil)
      _ = Devm.getStor mintAdd :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hmintAdd Line.Run.nil)
      _ = Devm.getStor mintDupKey2 :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hmintDupKey2 Line.Run.nil)
  have hstorMintStoreCall :
      Devm.getStor mintStore = Devm.getStor callCursor.pre := by
    calc
      Devm.getStor mintStore = Devm.getStor eventCursor.pre :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hmintSwap Line.Run.nil)
      _ = Devm.getStor codeBranchCursor.pre :=
        Line.of_inv Devm.getStor (by
          unfold flashEventCheckLine mstoreAt logWith
          line_inv) hevent
      _ = Devm.getStor setupCursor.pre :=
        funext (getStor_eq_of_state_eq hcodePop.state)
      _ = Devm.getStor callCursor.pre :=
        Line.of_inv Devm.getStor (by
          unfold flashCallbackSetupLine storeFlashCallbackHead mstoreAt
            pushList forwardArgTail arg cdl flashCallbackArgsSize
          line_inv) hsetup
  have hkeyNeFlash : key ≠ flashMintedSlot := by
    rw [← hkey]
    exact balanceKey_ne_flashMintedSlot key.toAdr
  have hOldBalance : oldBalance =
      (Devm.getStor mintCursor.pre frame.sevm.currentTarget).get key := by
    rw [holdBalance]
    change (Devm.getStor mintDupKey frame.sevm.currentTarget).get key = _
    rw [← congrFun (Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hmintDupKey Line.Run.nil))
        frame.sevm.currentTarget,
      ← congrFun (Line.of_inv Devm.getStor (by
          unfold addressArg normalizeAddress pushAddressMask arg cdl
          line_inv) hmintKey) frame.sevm.currentTarget]
  have hmintIncrease : Increase key.toAdr
      (Sevm.argWord frame.sevm 2)
      (Stor.rest
        (Devm.getStor mintCursor.pre frame.sevm.currentTarget))
      (Stor.rest
        (Devm.getStor callCursor.pre frame.sevm.currentTarget)) := by
    intro a
    constructor
    · intro ha
      subst a
      simp only [Stor.rest, Function.comp_apply]
      rw [← congrFun hstorMintStoreCall frame.sevm.currentTarget,
        hmintSet, ← congrFun hstorMintDupKey2 frame.sevm.currentTarget,
        hkey, Stor.get_set_self, hOldBalance, B256.add_comm]
    · intro hne
      simp only [Stor.rest, Function.comp_apply]
      rw [← congrFun hstorMintStoreCall frame.sevm.currentTarget,
        hmintSet, ← congrFun hstorMintDupKey2 frame.sevm.currentTarget]
      rw [← hkey]
      exact (Stor.get_set_ne _
        (fun he => hne (Adr.toB256_inj he)) _).symm
  have hcredit : Increase
      (normalizedAddressArg frame.sevm 0).toAdr
      (Sevm.argWord frame.sevm 2)
      (Stor.rest (Devm.getStor cursor.pre frame.sevm.currentTarget))
      (Stor.rest
        (Devm.getStor callCursor.pre frame.sevm.currentTarget)) := by
    rw [hrestEntryMint]
    simpa only [key, normalizedAddressArg] using hmintIncrease

  have hprefixBal :
      Devm.getBal cursor.pre = Devm.getBal callCursor.pre := by
    calc
      Devm.getBal cursor.pre = Devm.getBal tokenBranchCursor.pre :=
        Line.of_inv Devm.getBal (by
          unfold flashTokenLine arg cdl
          line_inv) htoken
      _ = Devm.getBal amountCursor.pre :=
        funext (getBal_eq_of_state_eq htokenPop.state)
      _ = Devm.getBal amountBranchCursor.pre :=
        Line.of_inv Devm.getBal (by
          unfold flashAmountLine arg cdl
          line_inv) hamount
      _ = Devm.getBal counterCursor.pre :=
        funext (getBal_eq_of_state_eq hamountPop.state)
      _ = Devm.getBal totalCursor.pre :=
        Line.of_inv Devm.getBal (by
          unfold flashCounterLine pushFlashMintedSlot
          line_inv) hcounter
      _ = Devm.getBal totalBranchCursor.pre :=
        Line.of_inv Devm.getBal (by
          unfold flashTotalLine pushFlashMintedSlot
          line_inv) htotal
      _ = Devm.getBal popCursor.pre :=
        funext (getBal_eq_of_state_eq htotalPop.state)
      _ = Devm.getBal mintCursor.pre :=
        Line.of_inv Devm.getBal (by line_inv) hpop
      _ = Devm.getBal eventCursor.pre :=
        Line.of_inv Devm.getBal (by
          unfold flashMintLine addressArg normalizeAddress
            pushAddressMask arg cdl
          line_inv) hmint
      _ = Devm.getBal codeBranchCursor.pre :=
        Line.of_inv Devm.getBal (by
          unfold flashEventCheckLine mstoreAt logWith
          line_inv) hevent
      _ = Devm.getBal setupCursor.pre :=
        funext (getBal_eq_of_state_eq hcodePop.state)
      _ = Devm.getBal callCursor.pre :=
        Line.of_inv Devm.getBal (by
          unfold flashCallbackSetupLine storeFlashCallbackHead mstoreAt
            pushList forwardArgTail arg cdl flashCallbackArgsSize
          line_inv) hsetup
  have hprefixCode :
      Devm.getCode cursor.pre = Devm.getCode callCursor.pre := by
    calc
      Devm.getCode cursor.pre = Devm.getCode tokenBranchCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold flashTokenLine arg cdl
          line_inv) htoken
      _ = Devm.getCode amountCursor.pre :=
        funext (getCode_eq_of_state_eq htokenPop.state)
      _ = Devm.getCode amountBranchCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold flashAmountLine arg cdl
          line_inv) hamount
      _ = Devm.getCode counterCursor.pre :=
        funext (getCode_eq_of_state_eq hamountPop.state)
      _ = Devm.getCode totalCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold flashCounterLine pushFlashMintedSlot
          line_inv) hcounter
      _ = Devm.getCode totalBranchCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold flashTotalLine pushFlashMintedSlot
          line_inv) htotal
      _ = Devm.getCode popCursor.pre :=
        funext (getCode_eq_of_state_eq htotalPop.state)
      _ = Devm.getCode mintCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hpop
      _ = Devm.getCode eventCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold flashMintLine addressArg normalizeAddress
            pushAddressMask arg cdl
          line_inv) hmint
      _ = Devm.getCode codeBranchCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold flashEventCheckLine mstoreAt logWith
          line_inv) hevent
      _ = Devm.getCode setupCursor.pre :=
        funext (getCode_eq_of_state_eq hcodePop.state)
      _ = Devm.getCode callCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold flashCallbackSetupLine storeFlashCallbackHead mstoreAt
            pushList forwardArgTail arg cdl flashCallbackArgsSize
          line_inv) hsetup

  have hmemToEvent : cursor.pre.memory = eventCursor.pre.memory := by
    calc
      cursor.pre.memory = tokenBranchCursor.pre.memory :=
        Line.of_inv Devm.memory (by
          unfold flashTokenLine arg cdl
          line_inv) htoken
      _ = amountCursor.pre.memory := htokenPop.memory
      _ = amountBranchCursor.pre.memory :=
        Line.of_inv Devm.memory (by
          unfold flashAmountLine arg cdl
          line_inv) hamount
      _ = counterCursor.pre.memory := hamountPop.memory
      _ = totalCursor.pre.memory :=
        Line.of_inv Devm.memory (by
          unfold flashCounterLine pushFlashMintedSlot
          line_inv) hcounter
      _ = totalBranchCursor.pre.memory :=
        Line.of_inv Devm.memory (by
          unfold flashTotalLine pushFlashMintedSlot
          line_inv) htotal
      _ = popCursor.pre.memory := htotalPop.memory
      _ = mintCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hpop
      _ = eventCursor.pre.memory :=
        Line.of_inv Devm.memory (by
          unfold flashMintLine addressArg normalizeAddress
            pushAddressMask arg cdl
          line_inv) hmint

  have heventMemory := hevent
  unfold flashEventCheckLine at heventMemory
  rcases Line.of_run_cons heventMemory with
    ⟨eventDup, hdupEvent, heventMemory⟩
  have hpEventDup : Sevm.argWord frame.sevm 2 ::
      Sevm.argWord frame.sevm 2 :: key :: [] <<+ eventDup.stack :=
    prefix_of_dup_val hdupEvent (by show_nth) hpMint
  rcases of_run_append (mstoreAt 0) heventMemory with
    ⟨eventStore, hstoreEvent, heventMemory⟩
  rcases of_run_mstoreAt_val hstoreEvent hpEventDup with
    ⟨hpEventStore, hmemEventStore⟩
  rcases Line.of_run_cons heventMemory with
    ⟨eventDupKey, hdupEventKey, heventMemory⟩
  have hpEventDupKey : key :: Sevm.argWord frame.sevm 2 :: key :: [] <<+
      eventDupKey.stack :=
    prefix_of_dup_val hdupEventKey (by show_nth) hpEventStore
  rcases Line.of_run_cons heventMemory with
    ⟨eventZero, hzeroEvent, heventMemory⟩
  have hpEventZero : (0 : B256) :: key :: Sevm.argWord frame.sevm 2 ::
      key :: [] <<+ eventZero.stack :=
    prefix_of_push (of_run_pushB256 hzeroEvent) hpEventDupKey
  rcases Line.of_run_cons heventMemory with
    ⟨eventTopic, htopicEvent, heventMemory⟩
  have hpEventTopic : Blanc.transferEvent :: (0 : B256) :: key ::
      Sevm.argWord frame.sevm 2 :: key :: [] <<+ eventTopic.stack :=
    prefix_of_push (of_run_pushB256 htopicEvent) hpEventZero
  rcases of_run_append (logWith 2 0 1) heventMemory with
    ⟨eventLog, hlogEvent, heventMemory⟩
  rcases of_logWith201_val hpEventTopic hlogEvent with
    ⟨hpEventLog, _hlogsEvent⟩
  have hmemEventLog := of_logWith201_mem hpEventTopic hlogEvent
  rcases Line.of_run_cons heventMemory with
    ⟨eventDupKey2, hdupEventKey2, heventMemory⟩
  have hpEventDupKey2 : key :: Sevm.argWord frame.sevm 2 :: key :: [] <<+
      eventDupKey2.stack :=
    prefix_of_dup_val hdupEventKey2 (by show_nth) hpEventLog
  rcases Line.of_run_cons heventMemory with
    ⟨eventCodeSize, hcodeSizeEvent, heventMemory⟩
  rcases of_extcodesize_frame hpEventDupKey2 hcodeSizeEvent with
    ⟨_eventSize, _hpEventCodeSize, hmemCodeSizeEvent⟩
  rcases Line.of_run_cons heventMemory with
    ⟨eventDone, hzeroCodeEvent, hnilEvent⟩
  cases hnilEvent
  have hmemEventDup : eventCursor.pre.memory = eventDup.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hdupEvent Line.Run.nil)
  have hmemStoreToTopic : eventStore.memory = eventTopic.memory :=
    (Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hdupEventKey Line.Run.nil)).trans
      ((Line.of_inv Devm.memory (by line_inv)
        (Line.Run.cons hzeroEvent Line.Run.nil)).trans
        (Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons htopicEvent Line.Run.nil)))
  have hmemLogToDone : eventLog.memory = codeBranchCursor.pre.memory :=
    (Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hdupEventKey2 Line.Run.nil)).trans
      (hmemCodeSizeEvent.trans
        (Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hzeroCodeEvent Line.Run.nil)))
  have hwfEvent : Mem.Wf eventCursor.pre.memory := by
    rw [← hmemToEvent]
    exact hwfEntry
  have hreadsEvent : Mem.Reads eventCursor.pre.memory [] := by
    rw [← hmemToEvent]
    exact hreadsEntry
  have hwfEventDup : Mem.Wf eventDup.memory := by
    rw [← hmemEventDup]
    exact hwfEvent
  have hreadsEventDup : Mem.Reads eventDup.memory [] := by
    rw [← hmemEventDup]
    exact hreadsEvent
  let eventImage := Bytes.writeAt [] 0
    (Sevm.argWord frame.sevm 2).toBytes
  have hwfEventStore : Mem.Wf eventStore.memory := by
    rw [hmemEventStore]
    exact hwfEventDup.write 0 _
  have hreadsEventStore : Mem.Reads eventStore.memory eventImage := by
    rw [hmemEventStore]
    exact Mem.Reads.write hwfEventDup hreadsEventDup 0 _
  have hwfEventTopic : Mem.Wf eventTopic.memory := by
    rw [← hmemStoreToTopic]
    exact hwfEventStore
  have hreadsEventTopic : Mem.Reads eventTopic.memory eventImage := by
    rw [← hmemStoreToTopic]
    exact hreadsEventStore
  have hwfEventLog : Mem.Wf eventLog.memory := by
    rw [hmemEventLog]
    exact hwfEventTopic.extend 0 32
  have hreadsEventLog : Mem.Reads eventLog.memory eventImage := by
    rw [hmemEventLog]
    exact hreadsEventTopic.extend 0 32
  have hwfSetup : Mem.Wf setupCursor.pre.memory := by
    rw [← hcodePop.memory, ← hmemLogToDone]
    exact hwfEventLog
  have hreadsSetup : Mem.Reads setupCursor.pre.memory eventImage := by
    rw [← hcodePop.memory, ← hmemLogToDone]
    exact hreadsEventLog

  have hsetupMemory := hsetup
  unfold flashCallbackSetupLine at hsetupMemory
  rcases Line.of_run_cons hsetupMemory with
    ⟨setupDup, hdupSetup, hsetupMemory⟩
  have hpSetupDup : Sevm.argWord frame.sevm 2 ::
      Sevm.argWord frame.sevm 2 :: key :: [] <<+ setupDup.stack :=
    prefix_of_dup_val hdupSetup (by show_nth) hpSetup
  rcases of_run_append storeFlashCallbackHead hsetupMemory with
    ⟨setupHead, hheadSetup, hsetupMemory⟩
  rcases of_storeFlashCallbackHead_frame hpSetupDup hheadSetup with
    ⟨hpSetupHead, hmemSetupHead⟩
  rcases of_run_append (pushList [0, 0]) hsetupMemory with
    ⟨setupZeros, hzerosSetup, hsetupMemory⟩
  have hmemHeadZeros : setupHead.memory = setupZeros.memory :=
    Line.of_inv Devm.memory (by line_inv) hzerosSetup
  rcases of_run_append (forwardArgTail 3 6) hsetupMemory with
    ⟨setupTail, htailSetup, hsetupMemory⟩
  have hpSetupZeros : (0 : B256) :: (0 : B256) ::
      Sevm.argWord frame.sevm 2 :: key :: [] <<+ setupZeros.stack := by
    unfold pushList at hzerosSetup
    simp only [List.map] at hzerosSetup
    rcases Line.of_run_cons hzerosSetup with
      ⟨afterZero1, hzero1, hzerosSetup⟩
    have hpZero1 : (0 : B256) :: Sevm.argWord frame.sevm 2 :: key ::
        [] <<+ afterZero1.stack :=
      prefix_of_push (of_run_pushB256 hzero1) hpSetupHead
    rcases Line.of_run_cons hzerosSetup with
      ⟨afterZero2, hzero2, hnilZeros⟩
    cases hnilZeros
    exact prefix_of_push (of_run_pushB256 hzero2) hpZero1
  rcases of_forwardArgTail_val hpSetupZeros htailSetup with
    ⟨_hpSetupTail, hmemSetupTail⟩
  rcases of_run_append flashCallbackArgsSize hsetupMemory with
    ⟨setupSize, hsizeSetup, hsetupMemory⟩
  rcases Line.of_run_cons hsetupMemory with
    ⟨setupOffset, hoffsetSetup, hsetupMemory⟩
  rcases Line.of_run_cons hsetupMemory with
    ⟨setupOutSize, houtSizeSetup, hsetupMemory⟩
  rcases Line.of_run_cons hsetupMemory with
    ⟨setupReceiver, hreceiverSetup, hsetupMemory⟩
  rcases Line.of_run_cons hsetupMemory with
    ⟨setupGas, hgasSetup, hnilSetup⟩
  cases hnilSetup
  have hmemSetupDup : setupCursor.pre.memory = setupDup.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hdupSetup Line.Run.nil)
  have hmemTailToCall : setupTail.memory = callCursor.pre.memory :=
    (Line.of_inv Devm.memory (by line_inv) hsizeSetup).trans
      ((Line.of_inv Devm.memory (by line_inv)
        (Line.Run.cons hoffsetSetup Line.Run.nil)).trans
        ((Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons houtSizeSetup Line.Run.nil)).trans
          ((Line.of_inv Devm.memory (by line_inv)
            (Line.Run.cons hreceiverSetup Line.Run.nil)).trans
            (Line.of_inv Devm.memory (by line_inv)
              (Line.Run.cons hgasSetup Line.Run.nil)))))
  have hwfSetupDup : Mem.Wf setupDup.memory := by
    rw [← hmemSetupDup]
    exact hwfSetup
  have hreadsSetupDup : Mem.Reads setupDup.memory eventImage := by
    rw [← hmemSetupDup]
    exact hreadsSetup
  let image1 := Bytes.writeAt eventImage 0 onFlashLoanSelector.toBytes
  let image2 := Bytes.writeAt image1 32 frame.sevm.caller.toB256.toBytes
  let image3 := Bytes.writeAt image2 64
    frame.sevm.currentTarget.toB256.toBytes
  let image4 := Bytes.writeAt image3 96
    (Sevm.argWord frame.sevm 2).toBytes
  let image5 := Bytes.writeAt image4 128 (0 : B256).toBytes
  let image6 := Bytes.writeAt image5 160 (0xa0 : B256).toBytes
  have wf1 := hwfSetupDup.write 0 onFlashLoanSelector.toBytes
  have rd1 : Mem.Reads
      (setupDup.memory.write 0 onFlashLoanSelector.toBytes) image1 :=
    Mem.Reads.write hwfSetupDup hreadsSetupDup 0 _
  have wf2 := wf1.write 32 frame.sevm.caller.toB256.toBytes
  have rd2 : Mem.Reads
      ((setupDup.memory.write 0 onFlashLoanSelector.toBytes).write
        32 frame.sevm.caller.toB256.toBytes) image2 :=
    Mem.Reads.write wf1 rd1 32 _
  have wf3 := wf2.write 64 frame.sevm.currentTarget.toB256.toBytes
  have rd3 : Mem.Reads
      (((setupDup.memory.write 0 onFlashLoanSelector.toBytes).write
        32 frame.sevm.caller.toB256.toBytes).write
        64 frame.sevm.currentTarget.toB256.toBytes) image3 :=
    Mem.Reads.write wf2 rd2 64 _
  have wf4 := wf3.write 96 (Sevm.argWord frame.sevm 2).toBytes
  have rd4 : Mem.Reads
      ((((setupDup.memory.write 0 onFlashLoanSelector.toBytes).write
        32 frame.sevm.caller.toB256.toBytes).write
        64 frame.sevm.currentTarget.toB256.toBytes).write
        96 (Sevm.argWord frame.sevm 2).toBytes) image4 :=
    Mem.Reads.write wf3 rd3 96 _
  have wf5 := wf4.write 128 (0 : B256).toBytes
  have rd5 : Mem.Reads
      (((((setupDup.memory.write 0 onFlashLoanSelector.toBytes).write
        32 frame.sevm.caller.toB256.toBytes).write
        64 frame.sevm.currentTarget.toB256.toBytes).write
        96 (Sevm.argWord frame.sevm 2).toBytes).write
        128 (0 : B256).toBytes) image5 :=
    Mem.Reads.write wf4 rd4 128 _
  have wf6 := wf5.write 160 (0xa0 : B256).toBytes
  have rd6 : Mem.Reads
      ((((((setupDup.memory.write 0 onFlashLoanSelector.toBytes).write
        32 frame.sevm.caller.toB256.toBytes).write
        64 frame.sevm.currentTarget.toB256.toBytes).write
        96 (Sevm.argWord frame.sevm 2).toBytes).write
        128 (0 : B256).toBytes).write
        160 (0xa0 : B256).toBytes) image6 :=
    Mem.Reads.write wf5 rd5 160 _
  have hwfHead : Mem.Wf setupHead.memory := by
    rw [hmemSetupHead]
    exact wf6
  have hreadsHead : Mem.Reads setupHead.memory image6 := by
    rw [hmemSetupHead]
    exact rd6
  have hwfZeros : Mem.Wf setupZeros.memory := by
    rw [← hmemHeadZeros]
    exact hwfHead
  have hreadsZeros : Mem.Reads setupZeros.memory image6 := by
    rw [← hmemHeadZeros]
    exact hreadsHead
  let image7 := Bytes.writeAt image6 192
    (Sevm.tailLen frame.sevm 3).toBytes
  let image8 := Bytes.writeAt image7 224 (Sevm.tailBytes frame.sevm 3)
  have wf7 := hwfZeros.write 192 (Sevm.tailLen frame.sevm 3).toBytes
  have rd7 : Mem.Reads
      (setupZeros.memory.write 192
        (Sevm.tailLen frame.sevm 3).toBytes) image7 :=
    Mem.Reads.write hwfZeros hreadsZeros 192 _
  have wf8 := wf7.write 224 (Sevm.tailBytes frame.sevm 3)
  have rd8 : Mem.Reads
      ((setupZeros.memory.write 192
        (Sevm.tailLen frame.sevm 3).toBytes).write
        224 (Sevm.tailBytes frame.sevm 3)) image8 :=
    Mem.Reads.write wf7 rd7 224 _
  have hwfTail : Mem.Wf setupTail.memory := by
    rw [hmemSetupTail]
    exact wf8
  have hreadsTail : Mem.Reads setupTail.memory image8 := by
    rw [hmemSetupTail]
    exact rd8
  have hwfCall : Mem.Wf callCursor.pre.memory := by
    rw [← hmemTailToCall]
    exact hwfTail
  have hreadsCall : Mem.Reads callCursor.pre.memory
      (flashCallbackRuntimeImage frame.sevm []) := by
    rw [← hmemTailToCall]
    simpa only [flashCallbackRuntimeImage, eventImage, image1, image2,
      image3, image4, image5, image6, image7, image8] using hreadsTail

  refine ⟨gasWord, callCursor, ?_, ?_, hwfCall, hreadsCall,
    hcredit, hprefixBal, hprefixCode⟩
  · exact hsetupActions.trans (hcodeBranchActions.trans
      (heventActions.trans (hmintActions.trans (hpopActions.trans
        (htotalBranchActions.trans (htotalActions.trans
          (hcounterActions.trans (hamountBranchActions.trans
            (hamountActions.trans
              (htokenBranchActions.trans htokenActions))))))))))
  · rw [← hkey] at hpCall
    simpa only [key, normalizedAddressArg] using hpCall

/-- Full exact chronology of one successful compiled flash-loan body.  The
borrower callback is the original retained child occurrence, its settlement
is followed to the unique `flashBurn` continuation, and no descendant action
is hidden before or after that child. -/
def Exec.Frame.CompiledFlashLoanChronology
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (receiver : Adr) (amount : B256) (prefixActions : List FlowAction) : Prop :=
  ∃ (callbackPre callbackPost settlePre burnPre parent child : Devm)
      (xl : Xlot) (pc : Nat) (retained : RetainedXlot xl),
    RawFlashCallbackIndexedStepBoundary frame.sevm
      frame.sevm.currentTarget receiver amount
      (flashCallbackRuntimeSize frame.sevm)
      (flashCallbackRuntimeInput frame.sevm)
      callbackPre callbackPost parent child xl pc ∧
    retained.RawCommits ∧
    frame.NinstOccurrence dp ca Ninst.call callbackPre callbackPost xl ∧
    Increase receiver amount
      (Stor.rest (Devm.getStor frame.pre ca))
      (Stor.rest (Devm.getStor callbackPre ca)) ∧
    Devm.getBal frame.pre = Devm.getBal callbackPre ∧
    Devm.getCode frame.pre = Devm.getCode callbackPre ∧
    Devm.getStor callbackPost = Devm.getStor settlePre ∧
    Devm.getBal callbackPost = Devm.getBal settlePre ∧
    Devm.getCode callbackPost = Devm.getCode settlePre ∧
    settlePre.logs = callbackPost.logs ∧
    settlePre.output = callbackPost.output ∧
    Mem.Wf settlePre.memory ∧
    (∃ settleImg, Mem.Reads settlePre.memory settleImg) ∧
    Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm settlePre
      flashSettle frame.post ∧
    Stor.Weth10Silent (Devm.getStor settlePre ca)
      (Devm.getStor burnPre ca) ∧
    amount ≤ Stor.rest (Devm.getStor burnPre ca) receiver ∧
    Decrease receiver amount
      (Stor.rest (Devm.getStor burnPre ca))
      (Stor.rest (Devm.getStor frame.post ca)) ∧
    Devm.getBal settlePre = Devm.getBal frame.post ∧
    Devm.getCode settlePre = Devm.getCode frame.post ∧
    Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm burnPre
      flashBurn frame.post ∧
    frame.descendantFlowActions dp ca =
      prefixActions ++ retained.flowActions dp ca

/-- The allowance fork touches only the tagged allowance key (or nothing),
so it is invisible to both holder balances and the temporary flash slot. -/
private theorem flashAllowanceOutcome_weth10Silent_exact
    {e : Sevm} {settle burn : Devm}
    (h : FlashAllowanceOutcome e settle burn) :
    Stor.Weth10Silent (Devm.getStor settle e.currentTarget)
      (Devm.getStor burn e.currentTarget) := by
  rcases h.1 with hmax | hfinite
  · exact Stor.Weth10Silent.of_eq hmax.2.1.symm
  · rcases hfinite with
      ⟨allowance, _hnotmax, _hle, _hget, hstor, _hlogs⟩
    rw [hstor]
    exact Stor.Weth10Silent.set
      (runtimeAllowanceKey_not_valid _)
      (runtimeAllowanceKey_ne_flash _)

/-- Align the raw functional flash suffix with its exact source `CALL` on an
original-frame compiled cursor. -/
theorem Exec.Frame.CompiledCursor.compiledFlashLoanChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {receiver : Adr} {amount gasWord : B256} {img : Bytes}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      flashLoanSuccessTail frame.post)
    (hstack :
      gasWord :: receiver.toB256 :: (0 : B256) :: callbackArgsOffset ::
        flashCallbackRuntimeSize frame.sevm :: (0 : B256) ::
        (0 : B256) :: [amount, receiver.toB256] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hwindow :
      img.sliceD callbackArgsOffset.toNat
          (flashCallbackRuntimeSize frame.sevm).toNat 0 =
        flashCallbackRuntimeInput frame.sevm)
    (htarget : frame.sevm.currentTarget = ca)
    (hreceiver : receiver =
      (normalizedAddressArg frame.sevm 0).toAdr)
    (hamount : amount = Sevm.argWord frame.sevm 2)
    (hcredit : Increase receiver amount
      (Stor.rest (Devm.getStor frame.pre ca))
      (Stor.rest (Devm.getStor cursor.pre ca)))
    (hprefixBal : Devm.getBal frame.pre = Devm.getBal cursor.pre)
    (hprefixCode : Devm.getCode frame.pre = Devm.getCode cursor.pre)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    frame.CompiledFlashLoanChronology dp ca receiver amount
      cursor.actions := by
  have hrun : Func.Run ((weth10 dp).main :: weth10Aux) frame.sevm
      cursor.pre flashLoanSuccessTail frame.post :=
    Func.Run.of_runCompiled cursor.run
  obtain ⟨callbackPost, settlePre, hcallback, hstor, hbal, hcodeEq,
      hlogs, houtput, hwfSettle, hreadsSettleEx, hsettle⟩ :=
    of_rawFlashLoanSuccessTail_step dp hstack hwf hreads hwindow hrun
  rcases hcallback with
    ⟨parent, child, xl, delegated, code, callbackGas, avail, pc, hstep,
      hdepth, hcallbackStack, hparentStack, hparentState,
      hparentMemory, hparentLogs, hparentOutput, hdelegation, hfilled,
      hprocess, hclean, hlength, hmagic, hresume, hmidState,
      hreturnData, hmidStack, hmidLogs, hmidOutput⟩
  let indexed : RawFlashCallbackIndexedStepBoundary frame.sevm
      frame.sevm.currentTarget receiver amount
      (flashCallbackRuntimeSize frame.sevm)
      (flashCallbackRuntimeInput frame.sevm)
      cursor.pre callbackPost parent child xl pc :=
    ⟨delegated, code, callbackGas, avail, hstep, hdepth,
      hcallbackStack, hparentStack, hparentState, hparentMemory,
      hparentLogs, hparentOutput, hdelegation, hfilled, hprocess, hclean,
      hlength, hmagic, hresume, hmidState, hreturnData, hmidStack,
      hmidLogs, hmidOutput⟩
  obtain ⟨retained⟩ := exists_retainedXlot_of_filled hfilled
  have hcommits : retained.RawCommits := by
    cases retained with
    | none => trivial
    | some retainedRun =>
        exact Frame.raw_commits_of_settlementCommits
          (ProcessMessage.settlementCommits_of_some_ok_clean
            hprocess hclean)
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (Ninst.call ::: flashLoanAfterCallback) frame.post at cursor
  rcases cursor.alignCommittedCallStep hfilled hstep retained hcommits with
    ⟨tailCursor, _htailPre, occurrence, htailActions⟩
  have hdesc := tailCursor.finishFlashLoanAfterCallback hcode
  obtain ⟨settleImg, hreadsSettle⟩ := hreadsSettleEx
  obtain ⟨burnPre, hburn, hallowance, hwfBurn, burnImg,
      hreadsBurn⟩ :=
    of_flashSettle_allowance dp hwfSettle hreadsSettle hsettle
  obtain ⟨hdecrease, hcover, _hflashBurn, _hburnLogs, _htrue,
      hbalBurn, hcodeBurn⟩ :=
    flashBurn_effect dp hwfBurn hreadsBurn hburn
  have hsilent := flashAllowanceOutcome_weth10Silent_exact hallowance
  rw [htarget] at hsilent
  have hcover' : amount ≤
      Stor.rest (Devm.getStor burnPre ca) receiver := by
    simpa only [hreceiver, hamount, htarget] using hcover
  have hdecrease' : Decrease receiver amount
      (Stor.rest (Devm.getStor burnPre ca))
      (Stor.rest (Devm.getStor frame.post ca)) := by
    simpa only [hreceiver, hamount, htarget] using hdecrease
  have hsettlePostBal :
      Devm.getBal settlePre = Devm.getBal frame.post :=
    hallowance.2.2.1.symm.trans hbalBurn.symm
  have hsettlePostCode :
      Devm.getCode settlePre = Devm.getCode frame.post :=
    hallowance.2.2.2.symm.trans hcodeBurn.symm
  refine ⟨cursor.pre, callbackPost, settlePre, burnPre, parent, child,
    xl, pc, retained, indexed, hcommits, occurrence, hcredit,
    hprefixBal, hprefixCode, hstor, hbal, hcodeEq, hlogs, houtput,
    hwfSettle, ⟨settleImg, hreadsSettle⟩, hsettle, hsilent, hcover',
    hdecrease', hsettlePostBal, hsettlePostCode, hburn, ?_⟩
  calc
    frame.descendantFlowActions dp ca = tailCursor.actions := hdesc
    _ = cursor.actions ++ retained.flowActions dp ca := htailActions

/-- Exact selector-level flash chronology for an authentic committed WETH10
frame.  Dispatch and the nonpayable wrapper are observation-silent; the
borrower callback is therefore the sole retained descendant action segment. -/
theorem Exec.Frame.compiledFlashLoanChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledFlashLoanChronology dp ca
      (normalizedAddressArg frame.sevm 0).toAdr
      (Sevm.argWord frame.sevm 2) [] := by
  have hmember :
      (Sevm.selector frame.sevm, nonpayable flashLoan) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [flashLoanSelector, weth10Funcs]
  rcases frame.compiledSelectorBodyCursorSilent context hnonempty hmember with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hwrapperSilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, _hbodyStack, hbodyActions, hbodySilent⟩
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hbodySilent.memory, ← hwrapperSilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hbodySilent.memory, ← hwrapperSilent.memory]
    exact context.memory_reads_empty
  obtain ⟨gasWord, callCursor, hcallActions, hstack, hwfCall,
      hreadsCall, hcreditBody, hbalBody, hcodeBody⟩ :=
    bodyCursor.reachFlashLoanSuccessTailCursor hwfBody hreadsBody
  have hentryState : frame.pre.state = bodyCursor.pre.state :=
    hwrapperSilent.state.trans hbodySilent.state
  have hentryStor : Devm.getStor frame.pre ca =
      Devm.getStor bodyCursor.pre ca :=
    congrArg (fun state : State => state.getStor ca) hentryState
  have hentryBal : Devm.getBal frame.pre = Devm.getBal bodyCursor.pre :=
    funext (getBal_eq_of_state_eq hentryState)
  have hentryCode : Devm.getCode frame.pre =
      Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hentryState)
  rw [context.invocation.2.1] at hcreditBody
  have hcredit : Increase
      (normalizedAddressArg frame.sevm 0).toAdr
      (Sevm.argWord frame.sevm 2)
      (Stor.rest (Devm.getStor frame.pre ca))
      (Stor.rest (Devm.getStor callCursor.pre ca)) := by
    rw [hentryStor]
    exact hcreditBody
  have hprefixBal :
      Devm.getBal frame.pre = Devm.getBal callCursor.pre :=
    hentryBal.trans hbalBody
  have hprefixCode :
      Devm.getCode frame.pre = Devm.getCode callCursor.pre :=
    hentryCode.trans hcodeBody
  have chronology := callCursor.compiledFlashLoanChronology
    (gasWord := gasWord) hstack hwfCall hreadsCall (by rfl)
      context.invocation.2.1 rfl rfl hcredit hprefixBal hprefixCode
      context.invocation.2.2.2
  have hzero : callCursor.actions = [] :=
    hcallActions.trans (hbodyActions.trans hwrapperActions)
  simpa only [hzero] using chronology

end Weth10

end Blanc
