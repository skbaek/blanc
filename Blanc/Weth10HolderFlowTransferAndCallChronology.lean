import Blanc.Weth10HolderFlowCompiled

/-!
Proof-indexed chronology for successful WETH10 `transferAndCall` frames.

The raw recipient word selects the transfer arm.  The nonzero arm first
performs the ordinary booked-balance transfer and then crosses exactly the
retained zero-value token callback.  The zero arm first crosses the retained
accepted-value redemption child and then the retained token callback.  Both
children are indexed by occurrences in the original compiled execution, so
the descendant ledger records their actual order rather than merely matching
detached endpoint facts.
-/

namespace Blanc

open Jaune
open scoped LogOutputHinv

namespace Weth10

/-- Exact raw-zero `transferAndCall` chronology.  The accepted value child is
the chronological prefix of the later token callback child. -/
def Exec.Frame.CompiledTransferAndCallZeroChronology
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop :=
  Sevm.argWord frame.sevm 0 = 0 ∧
  ∃ (callPre callbackPre : Devm)
      (trace : AcceptedValueCallTrace frame.sevm
        frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 1)
        callPre callbackPre),
    BurnCallPrefix frame.sevm frame.pre callPre callbackPre
      frame.sevm.caller (Sevm.argWord frame.sevm 1)
      frame.sevm.caller.toB256 ∧
    trace.slot = trace.retained.slot ∧
    Blanc.Weth10.RetainedXlot.RawCommits trace.retained.retained ∧
    Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame Ninst.call callPre trace.callPost
      trace.retained.slot ∧
    Blanc.Weth10.Exec.Frame.CompiledTokenCallbackChronology dp ca frame
      onTokenTransferSelector 0 2 (Sevm.argWord frame.sevm 1)
      callbackPre frame.post
      (Blanc.Weth10.RetainedXlot.flowActions dp ca
        trace.retained.retained)

/-- Exact raw-nonzero `transferAndCall` chronology.  The recipient remains
the normalized low-160-bit address, while the callback keeps the unmodified
raw ABI word. -/
def Exec.Frame.CompiledTransferAndCallNonzeroChronology
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop :=
  Sevm.argWord frame.sevm 0 ≠ 0 ∧
  ∃ (recipient : Adr) (callbackPre : Devm),
    recipient.toB256 = normalizedAddressArg frame.sevm 0 ∧
    Transfer
      (Stor.rest (Devm.getStor frame.pre frame.sevm.currentTarget))
      frame.sevm.caller (Sevm.argWord frame.sevm 1) recipient
      (Stor.rest (Devm.getStor callbackPre frame.sevm.currentTarget)) ∧
    (Devm.getStor callbackPre frame.sevm.currentTarget).get
        flashMintedSlot =
      (Devm.getStor frame.pre frame.sevm.currentTarget).get
        flashMintedSlot ∧
    callbackPre.logs = frame.pre.logs ++
      [ordinaryTransferLog frame.sevm frame.sevm.caller.toB256
        (normalizedAddressArg frame.sevm 0)
        (Sevm.argWord frame.sevm 1)] ∧
    Devm.getBal callbackPre = Devm.getBal frame.pre ∧
    Devm.getCode callbackPre = Devm.getCode frame.pre ∧
    callbackPre.output = frame.pre.output ∧
    Blanc.Weth10.Exec.Frame.CompiledTokenCallbackChronology dp ca frame
      onTokenTransferSelector 0 2 (Sevm.argWord frame.sevm 1)
      callbackPre frame.post []

/-- Exact selector-level chronology, split by the unmodified raw recipient
word rather than by its normalized address. -/
def Exec.Frame.CompiledTransferAndCallChronology
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop :=
  Blanc.Weth10.Exec.Frame.CompiledTransferAndCallZeroChronology dp ca frame ∨
    Blanc.Weth10.Exec.Frame.CompiledTransferAndCallNonzeroChronology dp ca frame

private def transferAndCallCallback : Func :=
  callBoolCallback onTokenTransferSelector 0 2 (arg 1)

private def transferSelectLine : Line := arg 0 ++ [Ninst.iszero]

private def transferNonzeroGuardLine : Line :=
  loadCallerBalanceAmount 1 ++ balanceTooSmall

private def transferNonzeroCreditLine : Line :=
  addressArg 0 ++ [Ninst.dup 0, Ninst.sload] ++ arg 1 ++
    [Ninst.add, Ninst.swap 0, Ninst.sstore]

private def transferNonzeroEventPrep : Line :=
  [Ninst.caller] ++ arg 1 ++ addressArg 0

private theorem dispatchSilent_of_popBurnBy
    {words : List B256} {cost : Nat} {pre post : Devm}
    (h : Devm.PopBurnBy words cost pre post) :
    Devm.DispatchSilent pre post :=
  ⟨h.state, h.memory, h.logs, h.output⟩

private theorem dispatchSilent_trans
    {pre mid post : Devm}
    (left : Devm.DispatchSilent pre mid)
    (right : Devm.DispatchSilent mid post) :
    Devm.DispatchSilent pre post :=
  ⟨left.state.trans right.state, left.memory.trans right.memory,
    left.logs.trans right.logs, left.output.trans right.output⟩

private theorem calldataload_state
    {e : Sevm} {pre post : Devm}
    (run : Ninst.Run e pre Ninst.calldataload post) :
    pre.state = post.state := by
  rcases of_run_reg run with ⟨_pc, core⟩
  simp only [Rinst.run, Rinst.runCore] at core
  rcases Except.bind_eq_ok core with
    ⟨⟨_offset, popped⟩, hpop, loadTail⟩
  rcases Except.bind_eq_ok loadTail with
    ⟨burned, hburn, hpush⟩
  exact (Devm.pop_of_pop hpop).state.trans
    ((Devm.burn_of_chargeGas hburn).state.trans
      (Devm.push_of_push hpush).state)

private theorem dispatchSilent_of_transferSelectLine
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre transferSelectLine post) :
    Devm.DispatchSilent pre post := by
  unfold transferSelectLine arg cdl at run
  rcases Line.of_run_cons run with ⟨afterPush, hpush, run⟩
  rcases Line.of_run_cons run with ⟨afterLoad, hload, run⟩
  rcases Line.of_run_cons run with ⟨last, hzero, hnil⟩
  cases hnil
  exact ⟨(of_run_pushB256 hpush).state.trans
      ((calldataload_state hload).trans
        (Ninst.Hinv.inv (f := Devm.state) hzero)),
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons hpush
        (Line.Run.cons hload (Line.Run.cons hzero Line.Run.nil))),
    (of_run_pushB256 hpush).logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) hload).trans
        (Ninst.Hinv.inv (f := Devm.logs) hzero)),
    (of_run_pushB256 hpush).output.trans
      ((Ninst.Hinv.inv (f := Devm.output) hload).trans
        (Ninst.Hinv.inv (f := Devm.output) hzero))⟩

/-- Local branch selector retaining exactly the observation silence hidden by
the compiler's branch scaffold.  This is intentionally symbolic in the two
arms; it never normalizes the closed WETH10 program. -/
private theorem Exec.Frame.CompiledCursor.selectZeroArmSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final)
    (hstack : (0 : B256) :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final,
      stack <<+ arm.pre.stack ∧ arm.actions = cursor.actions ∧
      Devm.DispatchSilent cursor.pre arm.pre := by
  have compiled := cursor.run
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      _hjumpdest, _hjumpable, _hsubRight, _hboundRight⟩
  cases compiled with
  | zero hroom hpop hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨armExec, hpArm⟩
      let arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final :=
        ⟨cursor.pc + 4, _, armExec, cursor.actions, hpArm,
          hleft, hsubLeft, hboundLeft⟩
      exact ⟨arm, hw.2, rfl, dispatchSilent_of_popBurnBy hpop⟩
  | succ hne _hroom hpop _hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hne hw.1).elim

/-- The matching nonzero selector, again exposing only the compiler
scaffold's observation silence. -/
private theorem Exec.Frame.CompiledCursor.selectNonzeroArmSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {flag : B256} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final)
    (hflag : flag ≠ 0)
    (hstack : flag :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final,
      stack <<+ arm.pre.stack ∧ arm.actions = cursor.actions ∧
      Devm.DispatchSilent cursor.pre arm.pre := by
  have compiled := cursor.run
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, _hsubLeft, _hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  cases compiled with
  | zero _hroom hpop _hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hflag hw.1.symm).elim
  | succ hne hroom hpop hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨afterJump, hpJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterJump hpJump hstepJumpdest with
        ⟨armExec, hpArm⟩
      let arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final :=
        ⟨loc + 1, _, armExec, cursor.actions, hpArm,
          hright, hsubRight, hboundRight⟩
      exact ⟨arm, hw.2, rfl, dispatchSilent_of_popBurnBy hpop⟩

/-- Follow the raw target test on the original cursor.  The returned arm and
the raw-word fact are selected together; normalization plays no role in this
branch decision. -/
private theorem Exec.Frame.CompiledCursor.selectTransferArm
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {next : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (transferThen next) final) :
    (Sevm.argWord frame.sevm 0 = 0 ∧
      ∃ zeroCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (transferZeroThen next) final,
        zeroCursor.actions = cursor.actions ∧
        Devm.DispatchSilent cursor.pre zeroCursor.pre) ∨
    (Sevm.argWord frame.sevm 0 ≠ 0 ∧
      ∃ nonzeroCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (transferNonzeroThen next) final,
        nonzeroCursor.actions = cursor.actions ∧
        Devm.DispatchSilent cursor.pre nonzeroCursor.pre) := by
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferSelectLine +++
      (.branch (transferNonzeroThen next) (transferZeroThen next)))
    final at cursor
  rcases cursor.peelChildlessLine
      (by simp [transferSelectLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨branchCursor, hselect, hselectActions⟩
  have hflagPrefix :
      [Sevm.argWord frame.sevm 0 =? 0] <<+
        branchCursor.pre.stack := by
    unfold transferSelectLine at hselect
    rcases of_run_append (arg 0) hselect with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero (prefix_of_arg nil_pref harg)
  have hlineSilent : Devm.DispatchSilent cursor.pre branchCursor.pre :=
    dispatchSilent_of_transferSelectLine hselect
  by_cases hraw : Sevm.argWord frame.sevm 0 = 0
  · have hcheck : (Sevm.argWord frame.sevm 0 =? 0) = 1 := by
      simp [B256.eqCheck, hraw]
    rw [hcheck] at hflagPrefix
    rcases branchCursor.selectNonzeroArmSilent (flag := (1 : B256))
        (by decide) hflagPrefix with
      ⟨zeroCursor, _hstack, hzeroActions, hbranchSilent⟩
    exact Or.inl ⟨hraw, zeroCursor,
      hzeroActions.trans hselectActions,
      dispatchSilent_trans hlineSilent hbranchSilent⟩
  · have hcheck : (Sevm.argWord frame.sevm 0 =? 0) = 0 := by
      simp [B256.eqCheck, hraw]
    rw [hcheck] at hflagPrefix
    rcases branchCursor.selectZeroArmSilent hflagPrefix with
      ⟨nonzeroCursor, _hstack, hnonzeroActions, hbranchSilent⟩
    exact Or.inr ⟨hraw, nonzeroCursor,
      hnonzeroActions.trans hselectActions,
      dispatchSilent_trans hlineSilent hbranchSilent⟩

private theorem debitLoadedBalance_logOutput
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre debitLoadedBalance post) :
    pre.logs = post.logs ∧ pre.output = post.output := by
  unfold debitLoadedBalance at run
  rcases Line.of_run_cons run with ⟨afterSub, hsub, run⟩
  rcases Line.of_run_cons run with ⟨afterSwap, hswap, run⟩
  rcases Line.of_run_cons run with ⟨last, hstore, hnil⟩
  cases hnil
  have hsubLogs : pre.logs = afterSub.logs := by
    rcases of_run_reg hsub with ⟨_pc, core⟩
    simp only [Rinst.run, Rinst.runCore] at core
    exact (Devm.diffBurn_of_applyBinary core).choose_spec.choose_spec.logs
  have hsubOutput : pre.output = afterSub.output := by
    rcases of_run_reg hsub with ⟨_pc, core⟩
    simp only [Rinst.run, Rinst.runCore] at core
    exact (Devm.diffBurn_of_applyBinary core).choose_spec.choose_spec.output
  exact ⟨hsubLogs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) hswap).trans
        (Ninst.Hinv.inv (f := Devm.logs) hstore)),
    hsubOutput.trans
      ((Ninst.Hinv.inv (f := Devm.output) hswap).trans
        (Ninst.Hinv.inv (f := Devm.output) hstore))⟩

/-- Reach the typed callback after the raw-nonzero transfer prefix.  All local
storage and log facts are proved at the returned cursor's literal `pre`, and
every crossed source instruction is childless. -/
private theorem Exec.Frame.CompiledCursor.reachTransferNonzeroCallback
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {next : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (transferNonzeroThen next) final)
    (h_wf : Mem.Wf cursor.pre.memory)
    (h_reads : Mem.Reads cursor.pre.memory []) :
    ∃ (recipient : Adr)
        (callbackCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux)) next final),
      recipient.toB256 = normalizedAddressArg frame.sevm 0 ∧
      Transfer
        (Stor.rest (Devm.getStor cursor.pre frame.sevm.currentTarget))
        frame.sevm.caller (Sevm.argWord frame.sevm 1) recipient
        (Stor.rest
          (Devm.getStor callbackCursor.pre frame.sevm.currentTarget)) ∧
      (Devm.getStor callbackCursor.pre frame.sevm.currentTarget).get
          flashMintedSlot =
        (Devm.getStor cursor.pre frame.sevm.currentTarget).get
          flashMintedSlot ∧
      callbackCursor.pre.logs = cursor.pre.logs ++
        [ordinaryTransferLog frame.sevm frame.sevm.caller.toB256
          (normalizedAddressArg frame.sevm 0)
          (Sevm.argWord frame.sevm 1)] ∧
      Devm.getBal callbackCursor.pre = Devm.getBal cursor.pre ∧
      Devm.getCode callbackCursor.pre = Devm.getCode cursor.pre ∧
      callbackCursor.pre.output = cursor.pre.output ∧
      Mem.Wf callbackCursor.pre.memory ∧
      Mem.Reads callbackCursor.pre.memory
        (Sevm.argWord frame.sevm 1).toBytes ∧
      callbackCursor.actions = cursor.actions := by
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferNonzeroGuardLine +++
      (.branch
        (debitLoadedBalance +++ transferNonzeroCreditLine +++
          transferNonzeroEventPrep +++ emitTransfer +++ next)
        (.call transferBalanceErrorSlot))) final at cursor
  rcases cursor.peelChildlessLine
      (by simp [transferNonzeroGuardLine, loadCallerBalanceAmount,
        balanceTooSmall, arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨guardCursor, hguard, hguardActions⟩
  rcases of_run_append (loadCallerBalanceAmount 1) hguard with
    ⟨afterLoad, hload, hsmall⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref hload with
    ⟨balance, hbalance, hloadPrefix⟩
  have hguardPrefix :
      (balance <? Sevm.argWord frame.sevm 1) :: balance ::
        Sevm.argWord frame.sevm 1 :: frame.sevm.caller.toB256 :: [] <<+
          guardCursor.pre.stack :=
    prefix_of_balanceTooSmall hloadPrefix hsmall
  rcases guardCursor.selectBranchLeftWithBurn
      (fun pre run => by
        rcases of_run_call run with
          ⟨body, bodyPre, hbody, _hburn, hrun⟩
        rw [transferBalanceError_lookup dp] at hbody
        have heq : body =
            Func.revWith "WETH: transfer amount exceeds balance" :=
          Option.some.inj hbody.symm
        subst body
        exact Func.not_run_revWith hrun) with
    ⟨successCursor, hsuccessPopBy, hsuccessActions⟩
  have hsuccessPop := Devm.PopBurn.of_popBurnBy hsuccessPopBy
  have hpopStack := hsuccessPop.stack
  simp only [Stack.Pop, Split, List.nil_append,
    List.cons_append] at hpopStack
  rw [hpopStack] at hguardPrefix
  have hflag : (balance <? Sevm.argWord frame.sevm 1) = 0 :=
    pref_head_unique hguardPrefix
      (pref_append [(0 : B256)] successCursor.pre.stack)
  have hcover : Sevm.argWord frame.sevm 1 ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at hflag
    exact B256.zero_ne_one hflag.symm
  rw [hflag] at hguardPrefix
  have hsuccessPrefix :
      balance :: Sevm.argWord frame.sevm 1 ::
        frame.sevm.caller.toB256 :: [] <<+ successCursor.pre.stack :=
    cons_pref_cons_inv hguardPrefix
  have hstorCursorSuccess :
      Devm.getStor cursor.pre = Devm.getStor successCursor.pre :=
    (Line.of_inv Devm.getStor (by line_inv) hload).trans
      ((Line.of_inv Devm.getStor (by line_inv) hsmall).trans
        (PopBurn.Inv.inv hsuccessPop))
  have hbalanceSuccess : balance =
      (Devm.getStor successCursor.pre frame.sevm.currentTarget).get
        frame.sevm.caller.toB256 := by
    rw [hbalance,
      congrFun hstorCursorSuccess frame.sevm.currentTarget]
  rcases successCursor.peelChildlessLine
      (by simp [debitLoadedBalance, NinstIsChildless]) with
    ⟨creditCursor, hdebit, hdebitActions⟩
  obtain ⟨hdecrease, hcovered, hflashDebit⟩ :=
    debitLoadedBalance_storage (validAdr_toB256 frame.sevm.caller)
      hbalanceSuccess hcover hsuccessPrefix hdebit
  rcases creditCursor.peelChildlessLine
      (by simp [transferNonzeroCreditLine, addressArg, normalizeAddress,
        pushAddressMask, arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨eventCursor, hcredit, hcreditActions⟩
  obtain ⟨recipient, hrecipient, hincrease, hflashCredit⟩ :=
    creditAddressArg_storage_at 0 1 hcredit
  have htransfer : Transfer
      (Stor.rest
        (Devm.getStor successCursor.pre frame.sevm.currentTarget))
      frame.sevm.caller (Sevm.argWord frame.sevm 1) recipient
      (Stor.rest (Devm.getStor eventCursor.pre
        frame.sevm.currentTarget)) :=
    ⟨by simpa only [toAdr_toB256] using hcovered,
      Stor.rest
        (Devm.getStor creditCursor.pre frame.sevm.currentTarget),
      by simpa only [toAdr_toB256] using hdecrease,
      hincrease⟩
  rcases eventCursor.peelChildlessLine
      (by simp [transferNonzeroEventPrep, addressArg, normalizeAddress,
        pushAddressMask, arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨emitCursor, hevent, heventActions⟩
  have heventRun := hevent
  unfold transferNonzeroEventPrep at hevent
  rcases Line.of_run_cons hevent with
    ⟨afterCaller, hcaller, hevent⟩
  have hpCaller : frame.sevm.caller.toB256 :: [] <<+
      afterCaller.stack :=
    prefix_of_push (of_run_caller hcaller) nil_pref
  rcases of_run_append (arg 1) hevent with
    ⟨afterAmount, hamount, haddress⟩
  have hpAmount : Sevm.argWord frame.sevm 1 ::
      frame.sevm.caller.toB256 :: [] <<+ afterAmount.stack :=
    prefix_of_arg hpCaller hamount
  have hpEvent : normalizedAddressArg frame.sevm 0 ::
      Sevm.argWord frame.sevm 1 :: frame.sevm.caller.toB256 :: [] <<+
        emitCursor.pre.stack := by
    simpa only [normalizedAddressArg] using
      prefix_of_addressArg hpAmount haddress
  rcases emitCursor.peelChildlessLine
      (by simp [emitTransfer, Blanc.transferFromLog, mstoreAt, logWith,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨callbackCursor, hemit, hemitActions⟩
  have hmemCursorEmit : cursor.pre.memory = emitCursor.pre.memory := by
    calc
      cursor.pre.memory = afterLoad.memory :=
        Line.of_inv Devm.memory (by line_inv) hload
      _ = guardCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hsmall
      _ = successCursor.pre.memory := hsuccessPop.memory
      _ = creditCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hdebit
      _ = eventCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hcredit
      _ = emitCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) heventRun
  have hwfEmit : Mem.Wf emitCursor.pre.memory := by
    rw [← hmemCursorEmit]
    exact h_wf
  have hreadsEmit : Mem.Reads emitCursor.pre.memory [] := by
    rw [← hmemCursorEmit]
    exact h_reads
  obtain ⟨_hpNext, hemitLogs, hemitStor, hemitBal, hemitCode,
      hemitOutput, hwfCallback, hreadsCallback⟩ :=
    emitTransfer_effect_frame hpEvent hwfEmit hreadsEmit hemit
  have hstorEventCallback :
      Devm.getStor eventCursor.pre = Devm.getStor callbackCursor.pre :=
    (Line.of_inv Devm.getStor (by line_inv)
      heventRun).trans
      hemitStor.symm
  have hlogsCursorEmit : cursor.pre.logs = emitCursor.pre.logs := by
    calc
      cursor.pre.logs = afterLoad.logs :=
        Line.of_inv Devm.logs (by line_inv) hload
      _ = guardCursor.pre.logs :=
        Line.of_inv Devm.logs (by line_inv) hsmall
      _ = successCursor.pre.logs := hsuccessPop.logs
      _ = creditCursor.pre.logs := (debitLoadedBalance_logOutput hdebit).1
      _ = eventCursor.pre.logs :=
        Line.of_inv Devm.logs (by line_inv) hcredit
      _ = emitCursor.pre.logs :=
        Line.of_inv Devm.logs (by line_inv) heventRun
  have hbalCursorCallback :
      Devm.getBal cursor.pre = Devm.getBal callbackCursor.pre := by
    calc
      Devm.getBal cursor.pre = Devm.getBal afterLoad :=
        Line.of_inv Devm.getBal (by line_inv) hload
      _ = Devm.getBal guardCursor.pre :=
        Line.of_inv Devm.getBal (by line_inv) hsmall
      _ = Devm.getBal successCursor.pre := PopBurn.Inv.inv hsuccessPop
      _ = Devm.getBal creditCursor.pre :=
        Line.of_inv Devm.getBal (by line_inv) hdebit
      _ = Devm.getBal eventCursor.pre :=
        Line.of_inv Devm.getBal (by line_inv) hcredit
      _ = Devm.getBal emitCursor.pre :=
        Line.of_inv Devm.getBal (by line_inv) heventRun
      _ = Devm.getBal callbackCursor.pre := hemitBal.symm
  have hcodeCursorCallback :
      Devm.getCode cursor.pre = Devm.getCode callbackCursor.pre := by
    calc
      Devm.getCode cursor.pre = Devm.getCode afterLoad :=
        Line.of_inv Devm.getCode (by line_inv) hload
      _ = Devm.getCode guardCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hsmall
      _ = Devm.getCode successCursor.pre :=
        funext (getCode_eq_of_state_eq hsuccessPop.state)
      _ = Devm.getCode creditCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hdebit
      _ = Devm.getCode eventCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hcredit
      _ = Devm.getCode emitCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) heventRun
      _ = Devm.getCode callbackCursor.pre := hemitCode.symm
  have houtputCursorCallback :
      cursor.pre.output = callbackCursor.pre.output := by
    calc
      cursor.pre.output = afterLoad.output :=
        Line.of_inv Devm.output (by line_inv) hload
      _ = guardCursor.pre.output :=
        Line.of_inv Devm.output (by line_inv) hsmall
      _ = successCursor.pre.output := hsuccessPop.output
      _ = creditCursor.pre.output := (debitLoadedBalance_logOutput hdebit).2
      _ = eventCursor.pre.output :=
        Line.of_inv Devm.output (by line_inv) hcredit
      _ = emitCursor.pre.output :=
        Line.of_inv Devm.output (by line_inv) heventRun
      _ = callbackCursor.pre.output := hemitOutput.symm
  have hwrite : Bytes.writeAt [] 0
      (Sevm.argWord frame.sevm 1).toBytes =
      (Sevm.argWord frame.sevm 1).toBytes :=
    Bytes.writeAt_zero_of_le (Nat.zero_le _)
  rw [hwrite] at hreadsCallback
  refine ⟨recipient, callbackCursor, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hwfCallback, hreadsCallback, ?_⟩
  · simpa only [normalizedAddressArg] using hrecipient
  · simpa only [congrFun hstorCursorSuccess frame.sevm.currentTarget,
      congrFun hstorEventCallback frame.sevm.currentTarget] using htransfer
  · rw [← congrFun hstorEventCallback frame.sevm.currentTarget,
      hflashCredit, hflashDebit,
      ← congrFun hstorCursorSuccess frame.sevm.currentTarget]
  · rw [hemitLogs, ← hlogsCursorEmit]
  · exact hbalCursorCallback.symm
  · exact hcodeCursorCallback.symm
  · exact houtputCursorCallback.symm
  · calc
      callbackCursor.actions = emitCursor.actions := hemitActions
      _ = eventCursor.actions := heventActions
      _ = creditCursor.actions := hcreditActions
      _ = successCursor.actions := hdebitActions
      _ = guardCursor.actions := hsuccessActions
      _ = cursor.actions := hguardActions

/-- Selector-level raw-nonzero arm.  The ordinary transfer endpoint is the
literal entry cursor of the indexed token callback. -/
theorem Exec.Frame.compiledTransferAndCallNonzeroChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hraw : Sevm.argWord frame.sevm 0 ≠ 0) :
    Blanc.Weth10.Exec.Frame.CompiledTransferAndCallNonzeroChronology dp ca frame := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable transferAndCall) ∈
        weth10Funcs dp := by
    rw [hselector]
    simp [transferAndCallSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame)
      context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, _hbodyStack, hbodyActions, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    dispatchSilent_trans hentrySilent hnonpayableSilent
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferThen transferAndCallCallback) frame.post at bodyCursor
  rcases bodyCursor.selectTransferArm with hzero | hnonzero
  · exact (hraw hzero.1).elim
  · rcases hnonzero with
      ⟨_hraw, nonzeroCursor, hnonzeroActions, hselectSilent⟩
    have hownSilent : Devm.DispatchSilent frame.pre nonzeroCursor.pre :=
      dispatchSilent_trans hbodySilent hselectSilent
    have hwfNonzero : Mem.Wf nonzeroCursor.pre.memory := by
      rw [← hownSilent.memory]
      exact context.memory_wf
    have hreadsNonzero : Mem.Reads nonzeroCursor.pre.memory [] := by
      rw [← hownSilent.memory]
      exact context.memory_reads_empty
    rcases nonzeroCursor.reachTransferNonzeroCallback
        hwfNonzero hreadsNonzero with
      ⟨recipient, callbackCursor, hrecipient, htransfer, hflash,
        hlogs, hbal, hcode, houtput, hwfCallback, hreadsCallback,
        hcallbackActions⟩
    have hchron := callbackCursor.compiledTokenCallbackChronology
      (sel := onTokenTransferSelector) (targetArg := 0) (dataArg := 2)
      (valueWord := Sevm.argWord frame.sevm 1) (value := arg 1)
      (img := (Sevm.argWord frame.sevm 1).toBytes)
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256])
      (by
        intro a b xs hp hline
        exact prefix_of_arg hp hline)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      hwfCallback hreadsCallback context.invocation.2.2.2
    have hcallbackActionsNil : callbackCursor.actions = [] := by
      calc
        callbackCursor.actions = nonzeroCursor.actions := hcallbackActions
        _ = bodyCursor.actions := hnonzeroActions
        _ = wrapperCursor.actions := hbodyActions
        _ = [] := hwrapperActions
    have hchron' : Blanc.Weth10.Exec.Frame.CompiledTokenCallbackChronology dp ca frame
        onTokenTransferSelector 0 2 (Sevm.argWord frame.sevm 1)
        callbackCursor.pre frame.post [] := by
      simpa only [hcallbackActionsNil] using hchron
    have hstorOwn : Devm.getStor frame.pre =
        Devm.getStor nonzeroCursor.pre :=
      funext (getStor_eq_of_state_eq hownSilent.state)
    have hbalOwn : Devm.getBal frame.pre =
        Devm.getBal nonzeroCursor.pre :=
      funext (getBal_eq_of_state_eq hownSilent.state)
    have hcodeOwn : Devm.getCode frame.pre =
        Devm.getCode nonzeroCursor.pre :=
      funext (getCode_eq_of_state_eq hownSilent.state)
    unfold Exec.Frame.CompiledTransferAndCallNonzeroChronology
    refine ⟨hraw, recipient, callbackCursor.pre, hrecipient, ?_, ?_,
      ?_, ?_, ?_, ?_, hchron'⟩
    · simpa only [congrFun hstorOwn frame.sevm.currentTarget] using htransfer
    · rw [hflash, ← congrFun hstorOwn frame.sevm.currentTarget]
    · rw [hlogs, ← hownSilent.logs]
    · exact hbal.trans hbalOwn.symm
    · exact hcode.trans hcodeOwn.symm
    · exact houtput.trans hownSilent.output.symm

/-- Selector-level raw-zero arm.  The accepted value child is crossed first;
its retained action list is then used as the literal prefix of the indexed
token callback chronology. -/
theorem Exec.Frame.compiledTransferAndCallZeroChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hraw : Sevm.argWord frame.sevm 0 = 0) :
    Blanc.Weth10.Exec.Frame.CompiledTransferAndCallZeroChronology dp ca frame := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable transferAndCall) ∈
        weth10Funcs dp := by
    rw [hselector]
    simp [transferAndCallSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame)
      context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, _hbodyStack, hbodyActions, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    dispatchSilent_trans hentrySilent hnonpayableSilent
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferThen transferAndCallCallback) frame.post at bodyCursor
  rcases bodyCursor.selectTransferArm with hzero | hnonzero
  · rcases hzero with
      ⟨_hraw, zeroCursor, hzeroActions, hselectSilent⟩
    have hownSilent : Devm.DispatchSilent frame.pre zeroCursor.pre :=
      dispatchSilent_trans hbodySilent hselectSilent
    have hwfZero : Mem.Wf zeroCursor.pre.memory := by
      rw [← hownSilent.memory]
      exact context.memory_wf
    have hreadsZero : Mem.Reads zeroCursor.pre.memory [] := by
      rw [← hownSilent.memory]
      exact context.memory_reads_empty
    rcases zeroCursor.enterTransferZeroThen (img := []) nil_pref
        hwfZero hreadsZero with
      ⟨callPre, guardPost, trace, callbackCursor, burn, htraceSlot,
        hcommits, occurrence, hcallbackPre, hcallbackActions,
        hwfCallback, hreadsCallback⟩
    subst guardPost
    have hwrite : Bytes.writeAt [] 0
        (Sevm.argWord frame.sevm 1).toBytes =
        (Sevm.argWord frame.sevm 1).toBytes :=
      Bytes.writeAt_zero_of_le (Nat.zero_le _)
    rw [hwrite] at hreadsCallback
    have hchron := callbackCursor.compiledTokenCallbackChronology
      (sel := onTokenTransferSelector) (targetArg := 0) (dataArg := 2)
      (valueWord := Sevm.argWord frame.sevm 1) (value := arg 1)
      (img := (Sevm.argWord frame.sevm 1).toBytes)
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256])
      (by
        intro a b xs hp hline
        exact prefix_of_arg hp hline)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      (by unfold arg cdl; line_inv)
      hwfCallback hreadsCallback context.invocation.2.2.2
    have hzeroActionsNil : zeroCursor.actions = [] := by
      calc
        zeroCursor.actions = bodyCursor.actions := hzeroActions
        _ = wrapperCursor.actions := hbodyActions
        _ = [] := hwrapperActions
    have hcallbackActionsExact : callbackCursor.actions =
        Blanc.Weth10.RetainedXlot.flowActions dp ca
          trace.retained.retained := by
      calc
        callbackCursor.actions = zeroCursor.actions ++
            Blanc.Weth10.RetainedXlot.flowActions dp ca
              trace.retained.retained := hcallbackActions
        _ = Blanc.Weth10.RetainedXlot.flowActions dp ca
              trace.retained.retained := by
          rw [hzeroActionsNil, List.nil_append]
    have hchron' : Blanc.Weth10.Exec.Frame.CompiledTokenCallbackChronology dp ca frame
        onTokenTransferSelector 0 2 (Sevm.argWord frame.sevm 1)
        callbackCursor.pre frame.post
        (Blanc.Weth10.RetainedXlot.flowActions dp ca
          trace.retained.retained) := by
      simpa only [hcallbackActionsExact] using hchron
    have hstorOwn : Devm.getStor frame.pre =
        Devm.getStor zeroCursor.pre :=
      funext (getStor_eq_of_state_eq hownSilent.state)
    have hbalOwn : Devm.getBal frame.pre =
        Devm.getBal zeroCursor.pre :=
      funext (getBal_eq_of_state_eq hownSilent.state)
    have hcodeOwn : Devm.getCode frame.pre =
        Devm.getCode zeroCursor.pre :=
      funext (getCode_eq_of_state_eq hownSilent.state)
    have burn' : BurnCallPrefix frame.sevm frame.pre callPre
        callbackCursor.pre frame.sevm.caller
        (Sevm.argWord frame.sevm 1) frame.sevm.caller.toB256 :=
      BurnCallPrefix.of_entry_eq hstorOwn hbalOwn hcodeOwn
        hownSilent.logs hownSilent.output burn
    unfold Exec.Frame.CompiledTransferAndCallZeroChronology
    exact ⟨hraw, callPre, callbackCursor.pre, trace, burn',
      htraceSlot, hcommits, occurrence, hchron'⟩
  · exact (hnonzero.1 hraw).elim

/-- Every successful authentic `transferAndCall` frame has the exact
proof-indexed chronology selected by its unmodified raw recipient word. -/
theorem Exec.Frame.compiledTransferAndCallChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.CompiledTransferAndCallChronology dp ca frame := by
  by_cases hraw : Sevm.argWord frame.sevm 0 = 0
  · exact Or.inl (Blanc.Weth10.Exec.Frame.compiledTransferAndCallZeroChronology (frame := frame)
      context hselector hnonempty hraw)
  · exact Or.inr (Blanc.Weth10.Exec.Frame.compiledTransferAndCallNonzeroChronology (frame := frame)
      context hselector hnonempty hraw)

end Weth10

end Blanc
